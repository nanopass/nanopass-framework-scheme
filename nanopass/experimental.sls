(library (nanopass experimental)
  (export
    datum? dots? maybe? syntax? exact-integer?
    Lnp-source unparse-Lnp-source
    parse-np-source
    Lcomplete unparse-Lcomplete
    language-information make-language-information
    language-information-language language-information-annotated-language
    handle-language-extension
    Llanguage unparse-Llanguage
    meta-variable-suffix-checker
    check-and-finish-language
    Lannotated unparse-Lannotated
    annotate-language
    star? modifier?
    Lpass unparse-Lpass
    lookup-language)
  (import (rnrs) (nanopass) (nanopass helpers) (nanopass prefix-matcher) (only (chezscheme) box box? set-box! unbox make-parameter record-constructor-descriptor?))

  (define-nanopass-record)

  (define (datum? x) #t)
  (define (dots? x) (eq? (syntax->datum x) '...))
  (define (maybe? x) (eq? (syntax->datum x) 'maybe))
  (define (syntax? x) #t) ;; could be slightly more perscriptive, and check for raw symbols
  (define (exact-integer? x) (and (integer? x) (exact? x)))

  (define-language Lnp-source
    (terminals
      (syntax (stx))
      (identifier (id))
      (datum (handler))
      (dots (dots))
      (null (null)))
    (Defn (def)
      (define-language id cl* ...))
    (Clause (cl)
      (extends id)
      (entry id)
      (nongenerative-id id)
      (terminals term* ...)
      (id (id* ...) prod prod* ...))
    (Terminal (term)
      base-term
      (+ base-term* ...)
      (- base-term* ...))
    (BaseTerminal (base-term)
      simple-term
      (=> (=> simple-term handler)
          (=> simple-term handler)))
    (SimpleTerminal (simple-term)
      (id (id* ...)))
    (Production (prod)
      stx))

  (define-pass parse-np-source : * (stx who) -> Lnp-source ()
    (definitions
      (define (parse-terminals stx)
        (let f ([stx stx])
          (syntax-case stx ()
            [() '()]
            [_ (let-values ([(t stx) (Terminal stx #t)])
                 (cons t (f stx)))])))
      (define (parse-base-terminals stx)
        (let f ([stx stx])
          (syntax-case stx ()
            [() '()]
            [_ (let-values ([(t stx) (Terminal stx #f)])
                 (cons t (f stx)))]))))
    (Defn : * (stx) -> Defn ()
      (syntax-case stx ()
        [(_ ?id ?cl ...)
         (identifier? #'?id)
         `(define-language ,#'?id ,(map Clause #'(?cl ...)) ...)]
        [_ (syntax-violation who "invalid syntax" stx)]))
    (Clause : * (stx) -> Clause ()
      (syntax-case stx (extends entry terminals nongenerative-id)
        [(extends ?id) (identifier? #'?id) `(extends ,#'?id)]
        [(entry ?id) (identifier? #'?id) `(entry ,#'?id)]
        [(nongenerative-id ?id) (identifier? #'?id) `(nongenerative-id ,#'?id)]
        [(terminals ?term* ...) `(terminals ,(parse-terminals #'(?term* ...)) ...)]
        [(?id (?id* ...) ?prod ?prod* ...)
         (and (identifier? #'?id) (for-all identifier? #'(?id* ...)))
         `(,#'?id (,#'(?id* ...) ...) ,#'?prod ,#'(?prod* ...) ...)]
        [x (syntax-violation who "unrecognized language clause" stx #'x)]))
    (Terminal : * (stx ext-okay?) -> Terminal (stx)
      (syntax-case stx ()
        [((=> (?id (?id* ...)) ?handler) . ?rest)
         (and (double-arrow? #'=>) (identifier? #'?id) (for-all identifier? #'(?id* ...)))
         (values `(=> (,#'?id (,#'(?id* ...) ...)) ,#'?handler) #'?rest)]
        [((?id (?id* ...)) => ?handler . ?rest)
         (and (double-arrow? #'=>) (identifier? #'?id) (for-all identifier? #'(?id* ...)))
         (values `(=> (,#'?id (,#'(?id* ...) ...)) ,#'?handler) #'?rest)]
        [((?id (?id* ...)) . ?rest)
         (and (identifier? #'?id) (for-all identifier? #'(?id* ...)))
         (values `(,#'?id (,#'(?id* ...) ...)) #'?rest)]
        [((+ ?term* ...) . ?rest)
         (and ext-okay? (plus? #'+))
         (values `(+ ,(parse-base-terminals #'(?term* ...)) ...) #'?rest)]
        [((- ?term* ...) . ?rest)
         (and ext-okay? (minus? #'-))
         (values `(- ,(parse-base-terminals #'(?term* ...)) ...) #'?rest)]
        [x (syntax-violation who "unrecognized terminal clause" stx #'x)]))
    (Defn stx))

  (define-language Lcomplete
    (extends Lnp-source)
    (Clause (cl)
      (- (extends id)
         (id (id* ...) prod prod* ...))
      (+ (id (id* ...) prod* ...))) ;; really the requirement remains, but is enforced in pass
    (Terminal (term)
      (- base-term
         (+ base-term* ...)
         (- base-term* ...))
      (+ simple-term
         (=> (=> simple-term handler)
             (=> simple-term handler))))
    (BaseTerminal (base-term)
      (- simple-term
         (=> (=> simple-term handler)
             (=> simple-term handler))))
    (Production (prod)
      (- stx)
      (+ pattern
         (=> (=> pattern0 pattern1)
             (=> pattern0 pattern1))
         (=> (-> pattern handler)
             (-> pattern handler))))
    (Pattern (pattern)
      (+ id
         (maybe id)
         (pattern dots)
         (pattern0 dots pattern1 ... . pattern2)
         (pattern0 . pattern1)
         null)))

  (define-record-type language-information
    (nongenerative)
    (fields language annotated-language))

  (define-pass handle-language-extension : Lnp-source (lang who rho) -> Lcomplete ()
    (definitions
      (define (language-extension? cl*)
        (fold-left (lambda (ext? cl)
                     (nanopass-case (Lnp-source Clause) cl
                       [(extends ,id) id]
                       [else ext?]))
          #f cl*))
      (define parse-productions
        (case-lambda
          [(stx) (parse-productions stx '())]
          [(stx prod*)
           (let f ([stx stx])
             (syntax-case stx ()
               [() prod*]
               [_ (let-values ([(prod stx) (FinishProd stx)])
                    (cons prod (f stx)))]))]))
      (define (lookup-language rho base-lang-id)
        (let ([lang-info (rho base-lang-id)])
          (unless lang-info (errorf who "could not find language ~s" (syntax->datum base-lang-id)))
          (language-information-annotated-language lang-info)))
      (define (extend-clauses cl* base-lang)
        (nanopass-case (Lannotated Defn) base-lang
          [(define-language ,id ,ref ,id? ,rtd ,rcd ,tag-mask (,term* ...) ,nt* ...)
           (fold-right (lambda (cl cl*) (ExtendClause cl term* nt* cl*)) '() cl*)]))
      (define-pass rewrite-annotated-term : (Lannotated Terminal) (ir) -> (Lcomplete Terminal) ()
        (Terminal : Terminal (ir) -> Terminal ()
          [(,id (,id* ...) ,handler? ,pred)
           (if handler?
               `(=> (,id (,id* ...)) ,handler?)
               `(,id (,id* ...)))]))
      (define-pass rewrite-production : (Lannotated Production) (ir) -> (Lcomplete Production) ()
        (Production : Production (ir) -> Production ()
          (definitions
            (define (finish-prod pattern pretty-prod?)
              (if pretty-prod?
                  (nanopass-case (Lannotated PrettyProduction) pretty-prod?
                    [(procedure ,handler) `(-> ,pattern ,handler)]
                    [(pretty ,pattern0) `(=> ,pattern ,(Pattern pattern0))])
                  pattern)))
          [(production ,[pattern] ,pretty-prod? ,rtd ,tag ,pred ,maker ,field* ...)
           (finish-prod pattern pretty-prod?)]
          [(terminal ,[pattern] ,pretty-prod?)
           (finish-prod pattern pretty-prod?)]
          [(nonterminal ,[pattern] ,pretty-prod?)
           (finish-prod pattern pretty-prod?)]
          [else (errorf who "unexpected Production ~s" (unparse-Lannotated ir))])
        (Reference : Reference (ir) -> Pattern ()
          [(reference ,id0 ,id1 ,b) id0])
        (Pattern : Pattern (ir) -> Pattern ()
          [,id id]
          [,ref (Reference ref)]
          [(maybe ,[pattern]) `(maybe ,pattern)]
          [(,[pattern] ,dots) `(,pattern ,dots)]
          [(,[pattern0] ,dots ,[pattern1] ... . ,[pattern2])
           `(,pattern0 ,dots ,pattern1 ... . ,pattern2)]
          [(,[pattern0] . ,[pattern1]) `(,pattern0 . ,pattern1)]
          [,null null]))
      (define (extend-terminals term* old-term*)
        (let loop ([term* term*] [old-term* old-term*] [new-term* '()])
          (if (null? term*)
              (fold-left
                (lambda (term* old-term)
                  (cons (rewrite-annotated-term old-term) term*))
                new-term* old-term*)
              (let-values ([(new-term* old-term*) (ExtendTerminal (car term*) new-term* old-term*)])
                (loop (cdr term*) old-term* new-term*)))))
      (define (extend-productions stx* old-prod*)
        (with-values
          (let f ([stx* stx*])
            (if (null? stx*)
                (values '() old-prod*)
                (let-values ([(new-prod* old-prod*) (f (cdr stx*))])
                  (ExtendProd (car stx*) new-prod* old-prod*))))
          (lambda (prod* old-prod*)
            (fold-left
              (lambda (prod* old-prod)
                (cons (rewrite-production old-prod) prod*))
              prod* old-prod*))))
      (define (remove-productions stx old-prod*)
        (let loop ([stx stx] [old-prod* old-prod*])
          (syntax-case stx ()
            [() old-prod*]
            [_ (with-values (RemoveProd stx old-prod*) loop)])))
      (define (remove-terminal id0 id0* old-term*)
        (let f ([old-term* old-term*])
          (if (null? old-term*)
              (errorf who "could not find terminal matching (~s ~s)" (syntax->datum id0) (map syntax->datum id0*))
              (let ([old-term (car old-term*)] [old-term* (cdr old-term*)])
                (nanopass-case (Lannotated Terminal) old-term
                  [(,id (,id* ...) ,handler? ,pred)
                   (if (and (eq? (syntax->datum id) (syntax->datum id0))
                            (equal? (syntax->datum id*) (syntax->datum id0*)))
                       old-term*
                       (cons old-term (f old-term*)))])))))
      (define-pass syntax-matches? : (Lannotated Production) (pat stx) -> * (boolean?)
        (Production : Production (ir stx) -> * (boolean?)
          [(production ,[b?] ,pretty-prod? ,rtd ,tag ,pred ,maker ,field* ...) b?]
          [(terminal ,[b?] ,pretty-prod?) b?]
          [(nonterminal ,[b?] ,pretty-prod?) b?])
        (Reference : Reference (ir stx) -> * (boolean?)
          [(reference ,id0 ,id1 ,b)
           (and (identifier? stx)
                (eq? (syntax->datum id0) (syntax->datum stx)))])
        (Pattern : Pattern (pat stx) -> * (boolean?)
          [,id (and (identifier? stx) (eq? (syntax->datum id) (syntax->datum stx)))]
          [,ref (Reference ref stx)]
          [(maybe ,[b?]) b?]
          [(,pattern ,dots)
           (syntax-case stx ()
             [(stx dots) (dots? #'dots) (Pattern pattern #'stx)]
             [_ #f])]
          [(,pattern0 ,dots ,pattern1 ... . ,pattern2)
           (syntax-case stx ()
             [(p0 dots p1 ... . p2) (dots? #'dots)
              (and (Pattern pattern0 #'p0) (for-all Pattern pattern1 #'(p1 ...)) (Pattern pattern2 #'p2))]
             [_ #f])]
          [(,pattern0 . ,pattern1)
           (syntax-case stx ()
             [(p0 . p1) (and (Pattern pattern0 #'p0) (Pattern pattern1 #'p1))]
             [_ #f])]
          [,null
            (syntax-case stx ()
              [() #t]
              [_ #f])])
        (Production pat stx))
      (define (remove-prod stx old-prod*)
        (let f ([old-prod* old-prod*])
          (if (null? old-prod*)
              (syntax-violation who "unable to find matching old production" stx)
              (let ([old-prod (car old-prod*)] [old-prod* (cdr old-prod*)])
                (if (syntax-matches? old-prod stx)
                    old-prod*
                    (cons old-prod (f old-prod*)))))))
      (define (find-matching-nt id old-nt*)
        (let loop ([old-nt* old-nt*])
          (if (null? old-nt*)
              '()
              (nanopass-case (Lannotated Nonterminal) (car old-nt*)
                [(,id0 (,id* ...) ,rtd ,rcd ,tag ,pred ,all-pred ,all-term-pred ,prod* ...)
                 (if (eq? (syntax->datum id0) (syntax->datum id))
                     prod*
                     (loop (cdr old-nt*)))]))))
      )
    (Defn : Defn (def) -> Defn ()
      [(define-language ,id ,cl* ...)
       `(define-language ,id 
          ,(cond
             [(language-extension? cl*) =>
              (lambda (base-lang-id) (extend-clauses cl* (lookup-language rho base-lang-id)))]
             [else (map FinishClause cl*)])
          ...)])
    (FinishClause : Clause (cl) -> Clause ()
      [(terminals ,[FinishTerminal : term* -> term*] ...) `(terminals ,term* ...)]
      [(,id (,id* ...) ,prod ,prod* ...)
       `(,id (,id* ...) ,(parse-productions (cons prod prod*)) ...)])
    (FinishTerminal : Terminal (term) -> Terminal ()
      [(+ ,base-term* ...) (errorf who "unexpected terminal extension clause ~s" (unparse-Lnp-source term))]
      [(- ,base-term* ...) (errorf who "unexpected terminal extension clause ~s" (unparse-Lnp-source term))])
    (FinishProd : syntax (stx) -> Production (stx)
      (syntax-case stx ()
        [(?pattern => ?handler . ?rest)
         (double-arrow? #'=>)
         (values `(=> ,(Pattern #'?pattern) ,#'?handler) #'?rest)]
        [((=> ?pattern ?handler) . ?rest)
         (double-arrow? #'=>)
         (values `(=> ,(Pattern #'?pattern) ,#'?handler) #'?rest)]
        [(?pattern -> ?pretty . ?rest)
         (arrow? #'->)
         (values `(-> ,(Pattern #'?pattern) ,(Pattern #'?pretty)) #'?rest)]
        [((-> ?pattern ?pretty) . ?rest)
         (arrow? #'->)
         (values `(-> ,(Pattern #'?pattern) ,(Pattern #'?pretty)) #'?rest)]
        [(?x . ?rest) (values (Pattern #'?x) #'?rest)]
        [_ (syntax-violation who "unrecognized productions list" stx)]))
    (ExtendClause : Clause (cl old-term* old-nt* cl*) -> * (cl*)
      [(terminals ,term* ...)
       (cons
         (in-context Clause
           `(terminals ,(extend-terminals term* old-term*)))
         cl*)]
      [(,id (,id* ...) ,prod ,prod* ...)
       (let ([prod* (extend-productions (cons prod prod*) (find-matching-nt id old-nt*))])
         (if (null? prod*)
             cl*
             (cons
               (in-context Clause
                 `(,id (,id* ...) ,prod* ...))
               cl*)))]
      [(extends ,id) cl*]
      [(entry ,id) (cons (in-context Clause `(entry ,id)) cl*)]
      [(nongenerative-id ,id)
       (cons (in-context Clause `(nongenerative-id ,id)) cl*)])
    (ExtendTerminal : Terminal (term new-term* old-term*) -> * (new-term* old-term*)
      [(+ ,base-term* ...)
       (values (append base-term* new-term*) old-term*)]
      [(- ,base-term* ...)
       (values
         new-term*
         (fold-left
           (lambda (old-term* base-term) (RemoveTerminal base-term old-term*))
           old-term* base-term*))]
      [,base-term (errorf who "unexpected non-extension terminal in extended language ~s" (unparse-Lnp-source base-term))])
    (RemoveTerminal : BaseTerminal (ir old-term*) -> * (old-term*)
      [(,id (,id* ...)) (remove-terminal id id* old-term*)]
      [(=> (,id (,id* ...)) ,handler) (remove-terminal id id* old-term*)]
      [else (errorf who "unexpected base terminal ~s" (unparse-Lnp-source ir))])
    (ExtendProd : syntax (stx new-prod* old-prod*) -> * (new-prod* old-prod*)
      (syntax-case stx ()
        [(+ ?prod* ...)
         (plus? #'+)
         (values (parse-productions #'(?prod* ...) new-prod*) old-prod*)]
        [(- ?prod* ...)
         (minus? #'-)
         (values new-prod* (remove-productions #'(?prod* ...) old-prod*))]
        [_ (syntax-violation who "unexpected production extension syntax" stx)]))
    (RemoveProd : syntax (stx old-prod*) -> * (stx old-prod*)
      (let-values ([(pattern rest)
                    (syntax-case stx ()
                      [(?pattern => ?handler . ?rest) (double-arrow? #'=>) (values #'?pattern #'?rest)]
                      [((=> ?pattern ?handler) . ?rest) (double-arrow? #'=>) (values #'?pattern #'?rest)]
                      [(?pattern -> ?pretty . ?rest) (arrow? #'->) (values #'?pattern #'?rest)]
                      [((-> ?pattern ?pretty) . ?rest) (arrow? #'->) (values #'?pattern #'?rest)]
                      [(?pattern . ?rest) (values #'?pattern #'?rest)]
                      [_ (syntax-violation who "unrecognized productions list" stx)])])
        (values rest (remove-prod pattern old-prod*))))
    (Pattern : * (stx) -> Pattern ()
      (syntax-case stx ()
        [?id (identifier? #'?id) #'?id]
        [(maybe ?id)
         (and (maybe? #'maybe) (identifier? #'?id))
         `(maybe ,#'?id)]
        [(?pattern dots)
         (ellipsis? #'dots)
         `(,(Pattern #'?pattern) ,#'dots)]
        [(?pattern0 dots ?pattern1 . ?pattern2)
         (ellipsis? #'dots)
         `(,(Pattern #'?pattern0) ,#'dots ,(Pattern #'?pattern1) . ,(Pattern #'?pattern2))]
        [(?pattern0 . ?pattern1)
         `(,(Pattern #'?pattern0) . ,(Pattern #'?pattern1))]
        [() '()])))

  (define-language Llanguage
    (extends Lcomplete)
    (terminals
      (+ (box (b))))
    (Clause (cl)
      (- (entry id))
      (+ (entry ref)))
    (Reference (ref)
      (+ (reference id0 id1 b)))
    (Pattern (pattern)
      (- (maybe id))
      (+ ref
         (maybe ref))))

  (define meta-variable-suffix-checker
    (make-parameter
      (lambda (str)
        (let f ([i (string-length str)])
          (or (fx=? i 0)
              (let* ([i (fx- i 1)]
                     [c (string-ref str i)])
                (cond
                  [(or (char=? c #\*) (char=? c #\^) (char=? c #\?)) (f i)]
                  [(char-numeric? c)
                   (let f ([i i])
                     (or (fx=? i 0)
                         (let ([i (fx- i 1)])
                           (and (char-numeric? (string-ref str i)) (f i)))))]
                  [else #f])))))
      (lambda (x)
        (unless (procedure? x) (errorf 'meta-variable-suffix-checker "expected procedure, but got ~s" x))
        x)))

  (define-pass check-and-finish-language : Lcomplete (ir) -> Llanguage ()
    (definitions
      (define (build-and-check-maps cl*)
        (let ([ht (make-eq-hashtable)])
          (let ([pt (fold-left (lambda (pt cl) (ExtendMapsClause cl pt ht)) (empty-prefix-tree) cl*)])
            (values pt ht))))
      (define (extract-all-terminals cl* pt ht)
        (let f ([cl* cl*])
          (if (null? cl*)
              (values '() '())
              (let ([cl (car cl*)])
                (let-values ([(term-out* cl-out*) (f (cdr cl*))])
                  (nanopass-case (Lcomplete Clause) cl
                    [(terminals ,term* ...)
                     (values
                       (fold-right
                         (lambda (term term-out*) (cons (Terminal term ht) term-out*))
                         term-out*
                         term*)
                       cl-out*)]
                    [else (values term-out* (cons cl cl-out*))]))))))
      (define (extract-all-nonterminals cl* pt ht)
        (let f ([cl* cl*])
          (if (null? cl*)
              (values '() '())
              (let-values ([(nt* cl-out*) (f (cdr cl*))])
                (let ([cl (car cl*)])
                  (nanopass-case (Lcomplete Clause) cl
                    [(,id (,id* ...) ,prod* ...)
                     (values (cons (Clause cl pt ht) nt*) cl-out*)]
                    [else (values nt* (cons cl cl-out*))]))))))
      (define (check-and-rewrite-clauses cl* pt ht)
        (let*-values ([(term* cl*) (extract-all-terminals cl* pt ht)]
                      [(nt* cl*) (extract-all-nonterminals cl* pt ht)])
          (fold-left
            (lambda (cl* cl) (cons (Clause cl pt ht) cl*))
            (with-output-language (Llanguage Clause)
              (cons `(terminals ,term* ...) nt*))
            cl*)))
      (define (build-ref mv id b)
        (with-output-language (Llanguage Reference)
          `(reference ,mv ,id ,b)))
      (define (set-ref! ht id x)
        (let* ([sym (syntax->datum id)]
               [val (hashtable-ref ht sym #f)])
          (cond
            [(eq? val #f) (syntax-violation who "unexpected terminal or nonterminal id" id)]
            [(box? val) (syntax-violation who "terminal or nonterminal listed more than once" id)]
            [(null? val) (hashtable-set! ht sym (box x))]
            [else (for-each (lambda (b) (set-box! b x)) val) (hashtable-set! ht sym (car val))])))
      (define ref
        (case-lambda
          [(ht id)
           (let* ([sym (syntax->datum id)]
                  [val (hashtable-ref ht sym #f)])
             (cond
               [(eq? val #f) (syntax-violation who "unexpected terminal or nonterminal id" id)]
               [(box? val) val]
               [else (let ([b (box #f)]) (hashtable-set! ht sym (cons b val)) b)]))]
          [(pt ht id)
           (let* ([str (symbol->string (syntax->datum id))]
                  [raw-id (match-prefix pt str (meta-variable-suffix-checker))])
             (unless raw-id (syntax-violation who "unable to find matching metavariable" id))
             (build-ref id raw-id (ref ht raw-id)))]))
      (define (maybe-ref pt ht id)
        (let* ([str (symbol->string (syntax->datum id))]
               [raw-id (match-prefix pt str (meta-variable-suffix-checker))])
          (if raw-id
              (build-ref id raw-id (ref ht raw-id))
              id))))
    (Defn : Defn (ir) -> Defn ()
      [(define-language ,id ,cl* ...)
       (let-values ([(pt ht) (build-and-check-maps cl*)])
         (let ([cl* (check-and-rewrite-clauses cl* pt ht)])
           `(define-language ,id ,cl* ...)))])
    (ExtendMapsClause : Clause (cl pt ht) -> * (pt)
      [(terminals ,term* ...) (fold-left (lambda (pt term) (ExtendMapsTerminal term pt ht)) pt term*)]
      [(,id (,id* ...) ,prod* ...)
       ;; should we be using an identifier hashtable? or symbol hashtable?
       (eq-hashtable-set! ht (syntax->datum id) '())
       (fold-left (lambda (pt mv-id) (insert-prefix pt (symbol->string (syntax->datum mv-id)) id)) pt id*)]
      [else pt])
    (ExtendMapsTerminal : Terminal (term pt ht) -> * (pt)
      [,simple-term (ExtendMapsSimpleTerminal simple-term pt ht)]
      [(=> ,simple-term ,handler) (ExtendMapsSimpleTerminal simple-term pt ht)])
    (ExtendMapsSimpleTerminal : SimpleTerminal (simple-term pt ht) -> * (pt)
      [(,id (,id* ...))
       (eq-hashtable-set! ht (syntax->datum id) '())
       (fold-left (lambda (pt mv-id) (insert-prefix pt (symbol->string (syntax->datum mv-id)) id)) pt id*)])
    (Terminal : Terminal (term ht) -> Terminal ()
      [(,id (,id* ...)) (let ([term `(,id (,id* ...))]) (set-ref! ht id term) term)]
      [(=> (,id (,id* ...)) ,handler) (let ([term `(=> (,id (,id* ...)) ,handler)]) (set-ref! ht id term) term)]
      [,simple-term (errorf who "unreachable match ,simple-term, reached!")]
      [(=> ,simple-term ,handler) (errorf who "unreachable match (=> ,simple-term ,handler), reached!")])
    (Clause : Clause (cl pt ht) -> Clause ()
      [(entry ,id) `(entry ,(ref ht id))]
      [(nongenerative-id ,id) `(nongenerative-id ,id)]
      [(terminals ,term* ...) (errorf who "unexpected terminal clause after terminals were filtered")]
      [(,id (,id* ...) ,prod* ...)
       (let* ([prod* (map (lambda (prod) (Production prod pt ht)) prod*)]
              [cl `(,id (,id* ...) ,prod* ...)])
         (set-ref! ht id cl)
         cl)])
    (Production : Production (prod pt ht) -> Production ()
      [,pattern (Pattern pattern pt ht)]
      [(=> ,[pattern0] ,[pattern1 (empty-prefix-tree) ht -> pattern1]) `(=> ,pattern0 ,pattern1)]
      [(-> ,[pattern] ,handler) `(-> ,pattern ,handler)])
    (Pattern : Pattern (pattern pt ht) -> Pattern ()
      [,id (maybe-ref pt ht id)]
      [(maybe ,id) (ref pt ht id)]
      [(,[pattern] ,dots) `(,pattern ,dots)]
      [(,[pattern0] ,dots ,[pattern1] ... . ,[pattern2]) `(,pattern0 ,dots ,pattern1 ... . ,pattern2)]
      [(,[pattern0] . ,[pattern1]) `(,pattern0 . ,pattern1)]
      [,null null])
    )

  (define-language Lannotated
    (extends Llanguage)
    (terminals
      (- (datum (handler)))
      (+ (datum (handler record-name pred all-pred all-term-pred accessor maker))
         (exact-integer (tag level tag-mask))
         (record-type-descriptor (rtd))
         (record-constructor-descriptor (rcd))))
    (Defn (def)
      (- (define-language id cl* ...))
      (+ (define-language
           id          ;; language name
           ref         ;; reference to entry ntspec
           (maybe id0) ;; nongenerative-id
           rtd
           rcd
           tag-mask
           (term* ...)
           nt* ...)))
    (Clause (cl)
      (- (entry ref)
         (nongenerative-id id)
         (terminals term* ...)
         (id (id* ...) prod* ...)))
    (Nonterminal (nt)
      (+ (id (id* ...) rtd rcd tag pred all-pred all-term-pred prod* ...)))
    (PrettyProduction (pretty-prod)
      (+ (procedure handler)
         (pretty pattern)))
    (Production (prod)
      (- pattern
         (=> (=> pattern0 pattern1)
             (=> pattern0 pattern1))
         (=> (-> pattern handler)
             (-> pattern handler)))
      (+ (production pattern (maybe pretty-prod) rtd tag pred maker field* ...)
         (terminal ref (maybe pretty-prod))
         (nonterminal ref (maybe pretty-prod))))
    (Field (field)
      (+ (ref level accessor)
         (optional ref level accessor)))
    (Terminal (term)
      (- simple-term
         (=> (=> simple-term handler)
             (=> simple-term handler)))
      (+ (id (id* ...) (maybe handler) pred)))
    (SimpleTerminal (simple-term)
      (- (id (id* ...)))))

  ;; TODO: fix the entry for language extenions
  (define-pass annotate-language : Llanguage (lang) -> Lannotated ()
    (definitions
      (define (add-reference! references id b)
        (hashtable-update! references (syntax->datum id) (lambda (v) (cons b v)) '()))
      (define (update-references! references id x)
        (let ([ls (hashtable-ref references (syntax->datum id) '())])
          (for-each (lambda (b) (set-box! b x)) ls)
          (hashtable-delete! references (syntax->datum id))
          x))
      (define-pass build-ref : (Llanguage Clause) (cl references) -> (Llanguage Reference) ()
        (build-ref : Clause (cl) -> Reference ()
          [(,id (,id* ...) ,prod* ...) (let ([b (box cl)]) (add-reference! references id b) `(reference ,id ,id ,b))]
          [else (errorf who "unexpected clause ~s" (unparse-Llanguage cl))]))
      (define (separate-clauses cl*)
        (let ([references (make-eq-hashtable)])
          (let loop ([cl* cl*] [entry #f] [first-nt #f] [nongen-id #f] [rterm* '()] [rnt* '()])
            (if (null? cl*)
                (values references (or entry (build-ref first-nt references)) nongen-id (reverse rterm*) (reverse rnt*))
                (with-values
                  (BinClause (car cl*) references entry first-nt nongen-id rterm* rnt*)
                  (lambda (entry first-nt nongen-id rterm* rnt*)
                    (loop (cdr cl*) entry first-nt nongen-id rterm* rnt*)))))))
      (define (annotate-terminals term* references) (map (lambda (t) (Terminal t references)) term*))
      (define (annotate-nonterminals nt* references lang-name lang-rtd lang-rcd nongen-id)
        (let ([bits (fxlength (length nt*))])
          (let f ([nt* nt*] [tag 0])
            (if (null? nt*)
                '()
                (cons
                  (Nonterminal (car nt*) references lang-name lang-rtd lang-rcd bits tag nongen-id)
                  (f (cdr nt*) (fx+ tag 1)))))))
      (define (build-production pattern nt-rtd lang-name nt-name tag pretty nongen-id)
        (let* ([prod-name (nanopass-case (Llanguage Pattern) pattern
                            [,id id]
                            [(,id ,dots) id]
                            [(,id0 ,dots ,pattern1 ... . ,pattern2) id0]
                            [(,id0 . ,pattern1) id0]
                            [((reference ,id0 ,id1 ,b)  ,dots) id0]
                            [((reference ,id0 ,id1 ,b) ,dots ,pattern1 ... . ,pattern2) id0]
                            [((reference ,id0 ,id1 ,b) . ,pattern1) id0]
                            [(maybe (reference ,id0 ,id1 ,b)) id0]
                            [((maybe (reference ,id0 ,id1 ,b)) ,dots) id0]
                            [((maybe (reference ,id0 ,id1 ,b)) ,dots ,pattern1 ... . ,pattern2) id0]
                            [((maybe (reference ,id0 ,id1 ,b)) . ,pattern1) id0]
                            [else (construct-id #'* "anonymous")])]
               [base-name (unique-name lang-name nt-name prod-name)])
          (let-values ([(pattern field* field-name*) (Pattern pattern base-name 0 '() '())])
            (let* ([rtd (make-record-type-descriptor (string->symbol base-name) nt-rtd
                          (if nongen-id
                              (regensym nongen-id
                                (format ":~s:~s" (syntax->datum nt-name) (syntax->datum prod-name))
                                (format "-~s" tag))
                              (gensym base-name))
                          #t #f
                          (list->vector (map (lambda (fn) `(immutable ,(syntax->datum fn))) field-name*)))]
               [pred (construct-id #'* base-name "?")]
               [maker (construct-id #'* "make-" base-name)])
            (with-output-language (Lannotated Production)
              `(production ,pattern ,pretty ,rtd ,tag ,pred ,maker ,field* ...))))))
      (define (build-accessor record-name id) (construct-id #'* record-name id))
      (define (Pattern* pattern* record-name level flds fns)
        (let f ([pattern* pattern*])
          (if (null? pattern*)
              (values '() flds fns)
              (let*-values ([(p* flds fns) (f (cdr pattern*))]
                            [(p flds fns) (Pattern (car pattern*) record-name level flds fns)])
                (values (cons p p*) flds fns)))))
      (with-output-language (Lannotated PrettyProduction)
        (define (pretty-pattern pattern)
          `(pretty ,(RewritePattern pattern)))
        (define (pretty-procedure handler)
          `(procedure ,handler)))
      )
    (Defn : Defn (def) -> Defn ()
      [(define-language ,id ,cl* ...)
       (let-values ([(references entry nongen-id term* nt*) (separate-clauses cl*)])
         (let* ([rtd (make-record-type-descriptor (syntax->datum id)
                       (record-type-descriptor nanopass-record)
                       (if nongen-id (syntax->datum nongen-id) (gensym (unique-name id)))
                       #f #f (vector))]
                [rcd (make-record-constructor-descriptor rtd
                       (record-constructor-descriptor nanopass-record) #f)]
                [tag-mask (fx- (fxarithmetic-shift-left 1 (fxlength (length nt*))) 1)]
                [term* (annotate-terminals term* references)]
                [nt* (annotate-nonterminals nt* references id rtd rcd nongen-id)])
           (let-values ([(ref ref-id) (Reference entry)]) 
             `(define-language ,id ,ref ,nongen-id ,rtd ,rcd ,tag-mask (,term* ...) ,nt* ...))))])
    (BinClause : Clause (cl references entry first-nt nongen-id rterm* rnt*) -> * (entry first-nt nongen-id rterm* rnt*)
      [(entry ,[RecordRef : ref references ->])
       (when entry (errorf who "found more than one entry"))
       (values ref first-nt nongen-id rterm* rnt*)]
      [(nongenerative-id ,id)
       (when nongen-id (syntax-violation who "found more than one nongenerative-id" id))
       (values entry first-nt id rterm* rnt*)]
      [(terminals ,term* ...)
       (values entry first-nt nongen-id (append term* rterm*) rnt*)]
      [(,id (,id* ...) ,[RecordProd : prod* references ->] ...)
       (values entry (or first-nt cl) nongen-id rterm* (cons cl rnt*))])
    (RecordProd : Production (prod references) -> * ()
      [,pattern (RecordPattern pattern references)]
      [(=> ,[RecordPattern : pattern0 references ->] ,pattern1) (values)]
      [(-> ,[RecordPattern : pattern references ->] ,handler) (values)])
    (RecordPattern : Pattern (pattern references) -> * ()
      [,id (values)]
      [,ref (RecordRef ref references)]
      [(maybe ,[RecordRef : ref references ->]) (values)]
      [(,[RecordPattern : pattern references ->] ,dots) (values)]
      [(,[RecordPattern : pattern0 references ->] ,dots
        ,[RecordPattern : pattern1 references ->] ... .
        ,[RecordPattern : pattern2 references ->])
       (values)]
      [(,[RecordPattern : pattern0 references ->] . ,[RecordPattern : pattern1 references ->])
       (values)]
      [,null (values)])
    (RecordRef : Reference (ref references) -> * ()
      [(reference ,id0 ,id1 ,b) (add-reference! references id1 b) (values)])
    (Terminal : Terminal (term references) -> Terminal ()
      [(,id (,id* ...))
       (update-references! references id `(,id (,id* ...) #f ,(construct-id id id "?")))]
      [(=> (,id (,id* ...)) ,handler)
       (update-references! references id `(,id (,id* ...) ,handler ,(construct-id id id "?")))]
      [else (errorf who "unexpected terminal ~s" (unparse-Llanguage term))])
    (Nonterminal : Clause (cl references lang-name lang-rtd lang-rcd bits tag nongen-id) -> Nonterminal ()
      [(,id (,id* ...) ,prod* ...)
       (let* ([record-name (unique-name lang-name id)]
              [rtd (make-record-type-descriptor
                     (string->symbol record-name)
                     lang-rtd
                     (if nongen-id
                         (regensym nongen-id
                           (format ":~s" (syntax->datum id))
                           (format "-~d" tag))
                         (gensym record-name))
                     #f #f (vector))]
              [rcd (make-record-constructor-descriptor rtd lang-rcd #f)]
              [pred (construct-id #'* record-name "?")]
              [all-pred (construct-id lang-name lang-name "-" id "?")]
              [all-term-pred (construct-id #'* lang-name "-" id "-terminal?")])
         (let loop ([prod* prod*] [next 1] [rprod* '()])
           (if (null? prod*)
               (update-references! references id
                 `(,id (,id* ...) ,rtd ,rcd ,tag ,pred ,all-pred ,all-term-pred ,(reverse rprod*) ...))
               (let ([prod-tag (fx+ (fxarithmetic-shift-left next bits) tag)])
                 (loop
                   (cdr prod*)
                   (fx+ next 1)
                   (cons (Production (car prod*) rtd lang-name id prod-tag nongen-id) rprod*))))))]
      [else (errorf who "unexpected clause in Nonterminal ~s" (unparse-Llanguage cl))])
    (Production : Production (prod nt-rtd lang-name nt-name prod-tag nongen-id) -> Production ()
      [,ref (BaseReference ref #f)]
      [(=> ,ref ,pattern1) (BaseReference ref (pretty-pattern pattern1))]
      [(-> ,ref ,handler) (BaseReference ref (pretty-procedure handler))]
      [,pattern (build-production pattern nt-rtd lang-name nt-name prod-tag #f nongen-id)]
      [(=> ,pattern0 ,pattern1) (build-production pattern0 nt-rtd lang-name nt-name prod-tag (pretty-pattern pattern1) nongen-id)]
      [(-> ,pattern ,handler) (build-production pattern nt-rtd lang-name nt-name prod-tag (pretty-procedure handler) nongen-id)])
    (BaseReference : Reference (ref maybe-pretty) -> Production ()
      [(reference ,id0 ,id1 ,b)
       (let ([x (unbox b)])
         (if (or (Llanguage-Terminal? x)
                 (Lannotated-Terminal? x))
             `(terminal (reference ,id0 ,id1 ,b) ,maybe-pretty)
             `(nonterminal (reference ,id0 ,id1 ,b) ,maybe-pretty)))])
    (RewritePattern : Pattern (pattern) -> Pattern ())
    (Pattern : Pattern (pattern record-name level flds fns) -> Pattern (flds fns)
      [,id (values id flds fns)]
      [,ref
       (let-values ([(ref meta-var) (Reference ref)])
         (values
           ref
           (cons
             (in-context Field
               `(,ref ,level ,(build-accessor record-name meta-var)))
             flds)
           (cons meta-var fns)))]
      [(maybe ,ref)
       (let-values ([(ref meta-var) (Reference ref)])
         (values
           `(maybe ,ref)
           (cons
             (in-context Field
               `(optional ,ref ,level ,(build-accessor record-name meta-var)))
             flds)
           (cons meta-var fns)))]
      [(,pattern ,dots)
       (let-values ([(pattern flds fns) (Pattern pattern record-name (fx+ level 1) flds fns)])
         (values `(,pattern ,dots) flds fns))]
      [(,pattern0 ,dots ,pattern1 ... . ,pattern2)
       (let*-values ([(pattern2 flds fns) (Pattern pattern2 record-name level flds fns)]
                     [(pattern1 flds fns) (Pattern* pattern1 record-name level flds fns)]
                     [(pattern0 flds fns) (Pattern pattern0 record-name (fx+ level 1) flds fns)])
         (values `(,pattern0 ,dots ,pattern1 ... . ,pattern2) flds fns))]
      [(,pattern0 . ,pattern1)
       (let*-values ([(pattern1 flds fns) (Pattern pattern1 record-name level flds fns)]
                     [(pattern0 flds fns) (Pattern pattern0 record-name level flds fns)])
         (values `(,pattern0 . ,pattern1) flds fns))]
      [,null (values null flds fns)])
    (Reference : Reference (ref) -> Reference (id)
      [(reference ,id0 ,id1 ,b) (values `(reference ,id0 ,id1 ,b) id0)])
    )

  (define (star? x)
    (or (eq? x '*)
        (eq? (syntax->datum x) '*)))

  (define (modifier? x)
    (memq (syntax->datum x) '(echo trace)))

  (define-language Lpass
    (terminals
      (identifier (id))
      (colon (:))
      (arrow (->))
      (star (*))
      (syntax (stx))
      (modifier (modifier))
      (null (null))
      (dots (dots))
      (unquote (unquote)))
    (Program (prog)
      (echo-define-pass id : lname0 (id* ...) -> lname1 (out* ...) defns proc* ... stx)
      (echo-define-pass id : lname0 (id* ...) -> lname1 (out* ...) proc* ... stx)
      (trace-define-pass id : lname0 (id* ...) -> lname1 (out* ...) defns proc* ... stx)
      (trace-define-pass id : lname0 (id* ...) -> lname1 (out* ...) proc* ... stx)
      (define-pass id : lname0 (id* ...) -> lname1 (out* ...) defns proc* ... stx)
      (define-pass id : lname0 (id* ...) -> lname1 (out* ...) proc* ... stx))
    (LanguageName (lname)
      *
      id
      (id0 id1))
    (Definitions (defns)
      (definitions stx* ...))
    (Processor (proc)
      (id : id0 (in* ...) -> id1 (out* ...) defns cl* ...)
      (id : id0 (in* ...) -> id1 (out* ...) cl* ...)
      (modifier id : id0 (in* ...) -> id1 (out* ...) defns cl* ...)
      (modifier id : id0 (in* ...) -> id1 (out* ...) cl* ...))
    (InputArgument (in)
      id
      [id stx])
    (OutputExpression (out)
      id
      stx)
    (Clause (cl)
      [pattern stx* ... stx])
    (Pattern (pattern)
      id
      (unquote hole)
      (pattern dots)
      (pattern0 dots pattern1 ... . pattern2)
      (pattern0 . pattern1)
      null)
    (Hole (hole)
      id
      cata)
    (Catamorphism (cata)
      (stx : . cata-remainder)
      cata-remainder)
    (CatamorphismRemainder (cata-remainder)
      (id* ... -> . cata-out)
      cata-out)
    (CatamorphismOutputVariables (cata-out)
      (id* ...)))

  (define lookup-language
    (lambda (rho name)
      (let ([lang (rho name)])
        (unless (language-information? lang)
          (errorf 'with-language "unable to find language information for ~s" (syntax->datum name)))
        lang)))
  )
