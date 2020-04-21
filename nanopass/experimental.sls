(library (nanopass experimental)
  (export
    experimental-language
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
    Lannotated unparse-Lannotated Lannotated? Lannotated-Defn? Lannotated-Terminal? Lannotated-Nonterminal?
    annotate-language
    star? modifier?
    Lpass-src unparse-Lpass-src
    lookup-language
    prune-lang
    diff-langs
    build-lang-node-counter
    build-unparser
    build-parser
    parse-pass
    Lpass unparse-Lpass)
  (import (rnrs) (nanopass) (nanopass helpers) (nanopass prefix-matcher)
    (only (chezscheme) box box? set-box! unbox make-parameter
      record-constructor-descriptor? eq-hashtable-update!))

  (define-syntax experimental-language
    (lambda (x) (syntax-violation 'experimental-language "misplaced aux keyword" x)))

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
          [(,id (,id* ...) ,b ,handler? ,pred)
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
                  [(,id (,id* ...) ,b ,handler? ,pred)
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
                [(,id0 (,id* ...) ,b ,rtd ,rcd ,tag ,pred ,all-pred ,all-term-pred ,prod* ...)
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
      (- (entry id)
         (id (id* ...) prod* ...))
      (+ (entry ref)
         (id (id* ...) b prod* ...)))
    (Reference (ref)
      (+ (reference id0 id1 b)))
    (SimpleTerminal (simple-term)
      (- (id (id* ...)))
      (+ (id (id* ...) b)))
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
      (define ref
        (case-lambda
          [(ht id)
           (let ([sym (syntax->datum id)])
             (or (eq-hashtable-ref ht sym #f)
                 (let ([b (box #f)])
                   (eq-hashtable-set! ht sym b)
                   b)))]
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
       (eq-hashtable-set! ht (syntax->datum id) (box #f))
       (fold-left (lambda (pt mv-id) (insert-prefix pt (symbol->string (syntax->datum mv-id)) id)) pt id*)]
      [else pt])
    (ExtendMapsTerminal : Terminal (term pt ht) -> * (pt)
      [,simple-term (ExtendMapsSimpleTerminal simple-term pt ht)]
      [(=> ,simple-term ,handler) (ExtendMapsSimpleTerminal simple-term pt ht)])
    (ExtendMapsSimpleTerminal : SimpleTerminal (simple-term pt ht) -> * (pt)
      [(,id (,id* ...))
       (eq-hashtable-set! ht (syntax->datum id) (box #f))
       (fold-left (lambda (pt mv-id) (insert-prefix pt (symbol->string (syntax->datum mv-id)) id)) pt id*)])
    (Terminal : Terminal (term ht) -> Terminal ()
      [(,id (,id* ...))
       (let* ([b (ref ht id)]
              [term `(,id (,id* ...) ,b)])
         (set-box! b term)
         term)]
      [(=> (,id (,id* ...)) ,handler)
       (let* ([b (ref ht id)]
             [term `(=> (,id (,id* ...) ,b) ,handler)])
         (set-box! b term)
         term)]
      [,simple-term (errorf who "unreachable match ,simple-term, reached!")]
      [(=> ,simple-term ,handler) (errorf who "unreachable match (=> ,simple-term ,handler), reached!")])
    (Clause : Clause (cl pt ht) -> Clause ()
      [(entry ,id) `(entry (reference ,id ,id ,(ref ht id)))]
      [(nongenerative-id ,id) `(nongenerative-id ,id)]
      [(terminals ,term* ...) (errorf who "unexpected terminal clause after terminals were filtered")]
      [(,id (,id* ...) ,prod* ...)
       (let* ([b (ref ht id)]
              [prod* (map (lambda (prod) (Production prod pt ht)) prod*)]
              [cl `(,id (,id* ...) ,b ,prod* ...)])
         (set-box! b cl)
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
         (id (id* ...) b prod* ...)))
    (Nonterminal (nt)
      (+ (id (id* ...) b rtd rcd tag pred all-pred all-term-pred prod* ...)))
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
      (+ (id (id* ...) b (maybe handler) pred)))
    (SimpleTerminal (simple-term)
      (- (id (id* ...) b))))

  ;; TODO: fix the entry for language extenions
  (define-pass annotate-language : Llanguage (lang) -> Lannotated ()
    (definitions
      (define-pass build-ref : (Llanguage Clause) (cl) -> (Llanguage Reference) ()
        (build-ref : Clause (cl) -> Reference ()
          [(,id (,id* ...) ,b ,prod* ...) `(reference ,id ,id ,b)]
          [else (errorf who "unexpected clause ~s" (unparse-Llanguage cl))]))
      (define (separate-clauses cl*)
        (let loop ([cl* cl*] [entry #f] [first-nt #f] [nongen-id #f] [rterm* '()] [rnt* '()])
          (if (null? cl*)
              (values (or entry (build-ref first-nt)) nongen-id (reverse rterm*) (reverse rnt*))
              (with-values
                (BinClause (car cl*) entry first-nt nongen-id rterm* rnt*)
                (lambda (entry first-nt nongen-id rterm* rnt*)
                  (loop (cdr cl*) entry first-nt nongen-id rterm* rnt*))))))
      (define (annotate-terminals term*) (map Terminal term*))
      (define (annotate-nonterminals nt* lang-name lang-rtd lang-rcd nongen-id)
        (let ([bits (fxlength (length nt*))])
          (let f ([nt* nt*] [tag 0])
            (if (null? nt*)
                '()
                (cons
                  (Nonterminal (car nt*) lang-name lang-rtd lang-rcd bits tag nongen-id)
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
       (let-values ([(entry nongen-id term* nt*) (separate-clauses cl*)])
         (let* ([rtd (make-record-type-descriptor (syntax->datum id)
                       (record-type-descriptor nanopass-record)
                       (if nongen-id (syntax->datum nongen-id) (gensym (unique-name id)))
                       #f #f (vector))]
                [rcd (make-record-constructor-descriptor rtd
                       (record-constructor-descriptor nanopass-record) #f)]
                [tag-mask (fx- (fxarithmetic-shift-left 1 (fxlength (length nt*))) 1)]
                [term* (annotate-terminals term*)]
                [nt* (annotate-nonterminals nt* id rtd rcd nongen-id)])
           (let-values ([(ref ref-id) (Reference entry)]) 
             `(define-language ,id ,ref ,nongen-id ,rtd ,rcd ,tag-mask (,term* ...) ,nt* ...))))])
    (BinClause : Clause (cl entry first-nt nongen-id rterm* rnt*) -> * (entry first-nt nongen-id rterm* rnt*)
      [(entry ,ref)
       (when entry (errorf who "found more than one entry"))
       (values ref first-nt nongen-id rterm* rnt*)]
      [(nongenerative-id ,id)
       (when nongen-id (syntax-violation who "found more than one nongenerative-id" id))
       (values entry first-nt id rterm* rnt*)]
      [(terminals ,term* ...)
       (values entry first-nt nongen-id (append term* rterm*) rnt*)]
      [(,id (,id* ...) ,b ,prod* ...)
       (values entry (or first-nt cl) nongen-id rterm* (cons cl rnt*))])
    (Terminal : Terminal (term ) -> Terminal ()
      [(,id (,id* ...) ,b)
       (let ([term `(,id (,id* ...) ,b #f ,(construct-id id id "?"))])
         (set-box! b term)
         term)]
      [(=> (,id (,id* ...) ,b) ,handler)
       (let ([term `(,id (,id* ...) ,b ,handler ,(construct-id id id "?"))])
         (set-box! b term)
         term)]
      [else (errorf who "unexpected terminal ~s" (unparse-Llanguage term))])
    (Nonterminal : Clause (cl lang-name lang-rtd lang-rcd bits tag nongen-id) -> Nonterminal ()
      [(,id (,id* ...) ,b ,prod* ...)
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
               (let ([nt `(,id (,id* ...) ,b ,rtd ,rcd ,tag ,pred ,all-pred ,all-term-pred ,(reverse rprod*) ...)])
                 (set-box! b nt)
                 nt)
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

  (define-pass prune-lang : Lannotated (ir caller-who maybe-name) -> * (stx)
    (Defn : Defn (ir) -> * (stx)
      [(define-language ,id ,ref ,id0? ,rtd ,rcd ,tag-mask (,term* ...) ,nt* ...)
       (let ([ht (make-eq-hashtable)])
         (let-values ([(entry-id ts nts) (FollowReference ref ht '() '())])
           (with-syntax ([define-language-exp (datum->syntax id 'define-language-exp)])
             (with-implicit (id entry terminals nongenerative-id)
               #`(define-language-exp #,(or maybe-name id)
                   (entry #,entry-id)
                   #,@(if id0? #`((nongenerative-id #,id0?)) #'())
                   (terminals #,@ts)
                   #,@nts)))))])
    (FollowReference : Reference (ir ht ts nts) -> * (id ts nts)
      [(reference ,id0 ,id1 ,b)
       (let ([ir (unbox b)])
         (cond
           [(eq-hashtable-ref ht ir #f) (values id0 ts nts)]
           [(Lannotated-Terminal? ir)
            (eq-hashtable-set! ht ir #t)
            (FollowTerminal ir ts nts id0)]
           [(Lannotated-Nonterminal? ir)
            (eq-hashtable-set! ht ir #t)
            (FollowNonterminal ir ht ts nts id0)]
           [else (errorf caller-who "unrecognized box contents for ~s" (syntax->datum id0))]))])
    (FollowTerminal : Terminal (ir ts nts id0) -> * (id0 ts nts)
      [(,id (,id* ...) ,b ,handler? ,pred)
       (values
         id0 
         (cons 
           (if handler?
               #`(=> (#,id #,id*) #,handler?)
               #`(#,id #,id*))
           ts)
         nts)])
    (FollowNonterminal : Nonterminal (ir ht ts nts id0) -> * (id0 ts nts)
      [(,id (,id* ...) ,b ,rtd ,rcd ,tag ,pred ,all-pred ,all-term-pred ,prod* ...)
       (let loop ([prod* prod*] [ts ts] [nts nts] [rprod* '()])
         (if (null? prod*)
             (values id0 ts (cons #`(#,id #,id* . #,rprod*) nts))
             (let-values ([(prod ts nts) (Production (car prod*) ht ts nts)])
               (loop (cdr prod*) ts nts (cons prod rprod*)))))])
    (Production : Production (ir ht ts nts) -> * (stx ts nts)
      (definitions (define (maybe-wrap pp? stx) (if pp? (PrettyProduction pp? stx) stx)))
      [(production ,[stx] ,pretty-prod? ,rtd ,tag ,pred ,maker ,field* ...)
       (let loop ([field* field*] [ts ts] [nts nts])
         (if (null? field*)
             (values (maybe-wrap pretty-prod? stx) ts nts)
             (let-values ([(ts nts) (FollowField (car field*) ht ts nts)])
               (loop (cdr field*) ts nts))))]
      [(terminal ,ref ,pretty-prod?)
       (let-values ([(id0 ts nts) (FollowReference ref ht ts nts)])
         (values (maybe-wrap pretty-prod? id0) ts nts))]
      [(nonterminal ,ref ,pretty-prod?)
       (let-values ([(id0 ts nts) (FollowReference ref ht ts nts)])
         (values (maybe-wrap pretty-prod? id0) ts nts))])
    (FollowField : Field  (field ht ts nts) -> * (ts nts)
      [(,[id0 ts nts] ,level ,accessor) (values ts nts)]
      [(optional ,[id0 ts nts] ,level ,accessor) (values ts nts)])
    (PrettyProduction : PrettyProduction (ir stx) -> * (stx)
      [(procedure ,handler) #`(-> #,stx #,handler)]
      [(pretty ,[pattern]) #`(=> #,stx #,pattern)])
    (Pattern : Pattern (ir) -> * (stx)
      [,id id]
      [,ref (Reference ref)]
      [,null #'()]
      [(maybe ,[id]) #`(maybe #,id)]
      [(,[pattern] ,dots) #`(#,pattern (... ...))]
      [(,[pattern0] ,dots ,[pattern1] ... . ,[pattern2])
       #`(#,pattern0 (... ...) #,@pattern1 . #,pattern2)]
      [(,[pattern0] . ,[pattern1]) #`(#,pattern0 . #,pattern1)])
    (Reference : Reference (ir) -> * (id)
      [(reference ,id0 ,id1 ,b) id0])
    (Defn ir))

  (define-pass diff-langs : Llanguage (ir-out ir-base) -> * (stx)
    (definitions
      (define (separate-clauses cl*)
        (let loop ([cl* cl*] [rcl* '()] [term* '()] [nt* '()])
          (if (null? cl*)
              (values rcl* term* nt*)
              (let-values ([(rcl* term* nt*) (BinClause (car cl*) rcl* term* nt*)])
                (loop (cdr cl*) rcl* term* nt*)))))
      (define (find-matching-terminal id term1*)
        (let f ([term1* term1*])
          (if (null? term1*)
              (values #f '())
              (let ([term (car term1*)])
                (nanopass-case (Llanguage Terminal) term
                  [(,id1 (,id1* ...) ,b)
                   (if (eq? (syntax->datum id)
                            (syntax->datum id1))
                       (values #t (cdr term1*))
                       (let-values ([(found? term1*) (f (cdr term1*))])
                         (values found? (cons term term1*))))]
                  [(=> (,id1 (,id1* ...) ,b) ,handler)
                   (if (eq? (syntax->datum id)
                            (syntax->datum id1))
                       (values #t (cdr term1*))
                       (let-values ([(found? term1*) (f (cdr term1*))])
                         (values found? (cons term term1*))))])))))
      (define (find-matching-nonterminal id nt1*)
        (let f ([nt1* nt1*])
          (if (null? nt1*)
              (values '() '())
              (let ([nt (car nt1*)])
                (nanopass-case (Llanguage Clause) nt
                  [(,id1 (,id1* ...) ,b ,prod* ...)
                   (if (eq? (syntax->datum id)
                            (syntax->datum id1))
                       (values prod* (cdr nt1*))
                       (let-values ([(prod* nt1*) (f (cdr nt1*))])
                         (values prod* (cons nt nt1*))))]
                  [else (errorf who "unexpected clause in nonterminal ~s" (unparse-Llanguage nt))])))))
      (define (add-terms-clause type term* cl*)
        (if (null? term*)
            cl*
            (cons #`(#,type . #,term*) cl*)))
      (define (Terminal* term0* term1*)
        (let loop ([term0* term0*] [term1* term1*] [add-term* '()])
          (if (null? term0*)
              (add-terms-clause #'- (map RewriteTerminal term1*)
                (add-terms-clause #'+ add-term* '()))
              (let-values ([(term1* add-term*) (Terminal (car term0*) term1* add-term*)])
                (loop (cdr term0*) term1* add-term*)))))
      (define (Nonterminal* nt0* nt1*)
        (let loop ([nt0* nt0*] [nt1* nt1*] [rnt* '()])
          (if (null? nt0*)
              (reverse
                (fold-left
                  (lambda (rnt* nt)
                    (nanopass-case (Llanguage Clause) nt
                      [(,id (,id* ...) ,b ,prod* ...)
                       #`(#,id #,id* (- . #,(map RewriteProduction prod*)))]
                      [else (errorf who "unexpected clause in nonterminal ~s" (unparse-Llanguage nt))]))
                  rnt* nt1*))
              (let-values ([(rnt* nt1*) (Nonterminal (car nt0*) nt1* rnt*)])
                (loop (cdr nt0*) nt1* rnt*)))))
      (define (add-productions type prod* cl*)
        (if (null? prod*)
            cl*
            (cons
              #`(#,type . #,(fold-left
                              (lambda (out* prod)
                                (cons (RewriteProduction prod) out*))
                              '() prod*))
              cl*)))
      (define (Production* prod0* prod1*)
        (let loop ([prod0* prod0*] [prod1* prod1*] [add-prod* '()])
          (if (null? prod0*)
              (add-productions #'- prod1*
                (add-productions #'+ add-prod* '()))
              (let-values ([(prod1* add-prod*)
                            (Production (car prod0*) prod1* add-prod*)])
                (loop (cdr prod0*) prod1* add-prod*)))))
      (define (find-matching-pattern pattern prod1*)
        (let f ([prod1* prod1*])
          (if (null? prod1*)
              (values #f '())
              (let* ([prod1 (car prod1*)]
                     [pattern1 (ProductionPattern prod1)])
                (if (Pattern=? pattern pattern1)
                    (values #t (cdr prod1*))
                    (let-values ([(found? prod1*) (f (cdr prod1*))])
                      (values found? (cons prod1 prod1*))))))))
      )
    (Defn : Defn (ir-out ir-base) -> * (stx)
      [(define-language ,id0 ,cl0* ...)
       (let-values ([(base-cl* term0* nt0*) (separate-clauses cl0*)])
         (nanopass-case (Llanguage Defn) ir-base
           [(define-language ,id1 ,cl1* ...)
            (let-values ([(_ term1* nt1*) (separate-clauses cl1*)])
              (let ([term* (Terminal* term0* term1*)]
                    [nt* (Nonterminal* nt0* nt1*)])
                (if (null? term*)
                    #`(define-language #,id0 #,@base-cl* . #,nt*)
                    #`(define-language #,id0 #,@base-cl* (terminals . #,term*) . #,nt*))))]))])
    (BinClause : Clause (ir cl* all-term* nt*) -> * (cl* all-term* nt*)
      [(entry ,[id]) (values (cons #`(entry #,id) cl*) all-term* nt*)]
      [(nongenerative-id ,id) (values (cons #`(nongenerative-id #,id) cl*) all-term* nt*)]
      [(terminals ,term* ...) (values cl* (append term* all-term*) nt*)]
      [(,id (,id* ...) ,b ,prod* ...) (values cl* all-term* (cons ir nt*))])
    (Terminal : Terminal (term0 term1* add-term*) -> * (term1* add-term*)
      [(=> (,id (,id* ...) ,b) ,handler)
       (let-values ([(found? term1*) (find-matching-terminal id term1*)])
         (if found?
             (values term1* add-term*)
             (values
               term1*
               (cons #`(=> (#,id #,id*) #,handler) add-term*))))]
      [(,id (,id* ...) ,b)
       (let-values ([(found? term1*) (find-matching-terminal id term1*)])
         (if found?
             (values term1* add-term*)
             (values
               term1*
               (cons #`(#,id #,id*) add-term*))))]
      [else (errorf who "unreachable clause in Terminal")])
    (Nonterminal : Clause (nt0 nt1* rnt*) -> * (rnt* nt1*)
      [(,id (,id* ...) ,b ,prod* ...)
       (let*-values ([(prod1* nt1*) (find-matching-nonterminal id nt1*)])
         (let ([prod* (Production* prod* prod1*)])
           (if (null? prod*)
               (values rnt* nt1*)
               (values (cons #`(#,id #,id* . #,prod*) rnt*) nt1*))))]
      [else (errorf who "unexpected clause ~s" (unparse-Llanguage nt0))])
    (Production : Production (prod prod1* add-prod*) -> * (prod1* add-prod*)
      [,pattern
       (let-values ([(found? prod1*) (find-matching-pattern pattern prod1*)])
         (if found?
             (values prod1* add-prod*)
             (values prod1* (cons prod add-prod*))))]
      [(=> ,pattern0 ,pattern1)
       (let-values ([(found? prod1*) (find-matching-pattern pattern0 prod1*)])
         (if found?
             (values prod1* add-prod*)
             (values prod1* (cons prod add-prod*))))]
      [(-> ,pattern ,handler)
       (let-values ([(found? prod1*) (find-matching-pattern pattern prod1*)])
         (if found?
             (values prod1* add-prod*)
             (values prod1* (cons prod add-prod*))))])
    (Pattern=? : Pattern (pattern0 pattern1) -> * (bool?)
      [,id0 (nanopass-case (Llanguage Pattern) pattern1
              [,id1 (eq? (syntax->datum id0) (syntax->datum id1))]
              [else #f])]
      [,ref0 (nanopass-case (Llanguage Pattern) pattern1
               [,ref1 (Reference=? ref0 ref1)]
               [else #f])]
      [,null0 (nanopass-case (Llanguage Pattern) pattern1
                [,null1 #t]
                [else #f])]
      [(maybe ,ref0)
       (nanopass-case (Llanguage Pattern) pattern1
         [(maybe ,ref1) (Reference=? ref0 ref1)]
         [else #f])]
      [(,pattern0 ,dots)
       (nanopass-case (Llanguage Pattern) pattern1
         [(,pattern1 ,dots) (Pattern=? pattern0 pattern1)]
         [else #f])]
      [(,pattern00 ,dots ,pattern10 ... . ,pattern20)
       (nanopass-case (Llanguage Pattern) pattern1
         [(,pattern01 ,dots ,pattern11 ... . ,pattern21)
          (and (Pattern=? pattern00 pattern01)
               (for-all Pattern=? pattern10 pattern11)
               (Pattern=? pattern20 pattern21))]
         [else #f])]
      [(,pattern00 . ,pattern10)
       (nanopass-case (Llanguage Pattern) pattern1
         [(,pattern01 . ,pattern11)
          (and (Pattern=? pattern00 pattern01)
               (Pattern=? pattern10 pattern11))]
         [else #f])])
    (Reference=? : Reference (ref0 ref1) -> * (bool?)
      [(reference ,id00 ,id10 ,b0)
       (nanopass-case (Llanguage Pattern) ref1
         [(reference ,id01 ,id11 ,b1)
          (eq? (syntax->datum id00)
               (syntax->datum id01))]
         [else #f])])
    (ProductionPattern : Production (ir) -> * (stx)
      [,pattern pattern]
      [(=> ,pattern0 ,pattern1) pattern0]
      [(-> ,pattern ,handler) pattern])
    (RewriteTerminal : Terminal (ir) -> * (stx)
      [(,id (,id* ...) ,b) #`(#,id #,id*)]
      [(=> (,id (,id* ...) ,b) ,handler)
       #`(=> (#,id #,id*) ,handler)]
      [else (errorf who "unexpected terminal ~s" (unparse-Llanguage ir))])
    (RewriteProduction : Production (ir) -> * (stx)
      [,pattern (RewritePattern pattern)]
      [(=> ,[stx0] ,[stx1]) #`(=> #,stx0 #,stx1)]
      [(-> ,[stx0] ,handler) #`(-> #,stx0 ,handler)])
    (RewritePattern : Pattern (ir) -> * (stx)
      [,id id]
      [,ref (RewriteReference ref)]
      [,null #'()]
      [(maybe ,[id]) #`(maybe #,id)]
      [(,[stx] ,dots) #`(#,stx (... ...))]
      [(,[stx0] ,dots ,[stx1] ... . ,[stx2])
       #`(#,stx0 (... ...) #,@stx1 . #,stx2)]
      [(,[stx0] . ,[stx1]) #`(#,stx0 . #,stx1)])
    (RewriteReference : Reference (ir) -> * (stx)
      [(reference ,id0 ,id1 ,b) id0])
    (Defn ir-out ir-base))

  (define-pass build-lang-node-counter : Lannotated (ir name) -> * (stx)
    (Defn : Defn (ir) -> * (stx)
      [(define-language ,id ,[id1] ,id0? ,rtd ,rcd ,tag-mask (,term* ...) ,[procs] ...)
       #`(define-pass #,name : #,id (ir) -> * (cnt)
           #,@procs
           (#,id1 ir))])
    (Nonterminal : Nonterminal (ir) -> * (stx)
      [(,id (,id* ...) ,b ,rtd ,rcd ,tag ,pred ,all-pred ,all-term-pred ,[cl*] ...)
       #`(#,id : #,id (ir) -> * (cnt) . #,cl*)])
    (Production : Production (ir) -> * (stx)
      [(production ,[pattern] ,pretty-prod? ,rtd ,tag ,pred ,maker ,[recur] ...)
       #`[#,pattern (+ 1 . #,recur)]]
      [(terminal (reference ,id0 ,id1 ,b) ,pretty-prod?)
       #`[,#,id0 0]]
      [(nonterminal (reference ,id0 ,id1 ,b) ,pretty-prod?)
       #`[,#,id0 (#,id1 #,id0)]]
      [else (errorf who "unrecognized production ~s" (unparse-Lannotated ir))])
    (Pattern : Pattern (ir) -> * (stx)
      [,id id]
      [,ref #`,#,(Reference ref)]
      [,null #'()]
      [(maybe ,[id]) #`,#,id]
      [(,[pattern] ,dots)
       #`(#,pattern (... ...))]
      [(,[pattern0] ,dots ,[pattern1] ... . ,[pattern2])
       #`(#,pattern0 (... ...) #,@pattern1 . #,pattern2)]
      [(,[pattern0] . ,[pattern1])
       #`(#,pattern0 . #,pattern1)])
    (Field : Field (ir) -> * (stx)
      (definitions
        (define (build-recur recur level)
          (let f ([level level])
            (if (fx=? level 0)
                recur
                #`(lambda (x)
                    (fold-left
                      (lambda (c x) (+ c (#,(f (fx- level 1)) x)))
                      0 x))))))
      [((reference ,id0 ,id1 ,b) ,level ,accessor)
       (if (Lannotated-Terminal? (unbox b))
           #'0  ;; possibly should be length?
           #`(#,(build-recur id1 level) #,id0))]
      [(optional (reference ,id0 ,id1 ,b) ,level ,accessor)
       (if (Lannotated-Terminal? (unbox b))
           #'0  ;; possibly should be length?
           #`(#,(build-recur #`(lambda (x) (if x (#,id1 x) 0)) level) #,id0))]
      [else (errorf who "unrecognized field ~s" (unparse-Lannotated ir))])
    (Reference : Reference (ir) -> * (id)
      [(reference ,id0 ,id1 ,b) id0])
    (Defn ir))

  (define-pass build-unparser : Lannotated (ir name) -> * (stx)
    (definitions
      (define (build-mv-refs pat flds)
        (if flds
            (map Field flds)
            (let-values ([(mv up) (Reference pat)]) (list mv)))))
    (Defn : Defn (ir) -> * (stx)
      [(define-language ,id ,[mv upname] ,id? ,rtd ,rcd ,tag-mask (,[tup* tpred* tn*] ...) ,[up* pred* n*] ...)
       (with-syntax ([(tup* ...) tup*]
                     [(tpred* ...) tpred*]
                     [(tn* ...) tn*]
                     [(up* ...) up*]
                     [(pred* ...) pred*]
                     [(n* ...) n*]
                     [who (datum->syntax name 'who)])
         ;; NOTE: entry is #f when not specified to preserve the current
         ;; behavior, but could be specified to be the entry instead.
         #`(define #,name
             (let ()
               (define-pass #,name : #,id (lf entry raw?) -> * (sexp)
                 tup* ...
                 up* ...
                 (case entry
                   [(n*) (n* lf)] ...
                   [(tn*) (tn* lf)] ...
                   [else (cond
                           [(pred* lf) (n* lf)] ...
                           [(tpred* lf) (tn* lf)] ...
                           [else (errorf who "Unrecognized input ~s" lf)])]))
               (case-lambda
                 [(lf) (#,name lf #f #f)]
                 [(lf entry/raw?)
                  (if (symbol? entry/raw?)
                      (#,name lf entry/raw? #f)
                      (#,name lf #f entry/raw?))]
                 [(lf entry raw?) (#,name lf entry raw?)]))))])
    (Terminal : Terminal (ir) -> * (tup tpred tn)
      [(,id (,id* ...) ,b ,handler? ,pred)
       (values
         (if handler?
             #`(#,id : #,id (lf) -> * (sexp) (if raw? lf (#,handler? lf)))
             #`(#,id : #,id (lf) -> * (sexp) lf))
         pred
         id)])
    (Nonterminal : Nonterminal (ir) -> * (up pred n)
      [(,id (,id* ...) ,b ,rtd ,rcd ,tag ,pred ,all-pred ,all-term-pred ,[cl*] ...)
       (values
         #`(#,id : #,id (lf) -> * (sexp) . #,cl*)
         all-pred
         id)])
    (Production : Production (ir) -> * (cl)
      (definitions
        (define (build-sexp pretty-prod? raw-pattern mv*)
          (if pretty-prod?
              (PrettyProduction pretty-prod? raw-pattern mv*)
              #`(with-extended-quasiquote (quasiquote #,raw-pattern)))))
      [(production ,[pattern] ,pretty-prod? ,rtd ,tag ,pred ,maker ,[mv* up*] ...)
       (with-syntax ([sexp-builder (build-sexp pretty-prod? pattern mv*)]
                     [(mv* ...) mv*]
                     [(up* ...) up*])
         #`[#,pattern (let ([mv* (up* mv*)] ...) sexp-builder)])]
      [(terminal ,[ref -> mv upname] ,pretty-prod?)
       (with-syntax ([sexp-builder (build-sexp pretty-prod? #`,#,mv (list mv))])
         #`[,#,mv (let ([#,mv (#,upname #,mv)]) sexp-builder)])]
      [(nonterminal ,[ref -> mv upname] ,pretty-prod?)
       (with-syntax ([sexp-builder (build-sexp pretty-prod? #`,#,mv (list mv))])
         #`[,#,mv (let ([#,mv (#,upname #,mv)]) sexp-builder)])])
    (Pattern : Pattern (ir) -> * (stx)
      [,id id]
      [,ref (let-values ([(mv up) (Reference ref)]) #`,#,mv)]
      [,null #'()]
      [(maybe ,[mv up]) #`,#,mv]
      [(,[pattern] ,dots) #`(#,pattern (... ...))]
      [(,[pattern0] ,dots ,[pattern1] ... .  ,[pattern2])
       #`(#,pattern0 (... ...) #,@pattern1 . #,pattern2)]
      [(,[pattern0] . ,[pattern1]) #`(#,pattern0 . #,pattern1)])
    (PrettyProduction : PrettyProduction (ir raw-pattern mv*) -> * (stx)
      [(procedure ,handler)
       #`(if raw?
             (with-extended-quasiquote (quasiquote #,raw-pattern))
             (#,handler #,name . #,mv*))]
      [(pretty ,pattern)
       (with-syntax ([pretty-builder (Pattern pattern)])
         #`(if raw?
               (with-extended-quasiquote (quasiquote #,raw-pattern))
               (with-extended-quasiquote (quasiquote pretty-builder))))])
    (Field : Field (ir) -> * (mv up)
      (definitions
        (define (build-unparser-for-level up level)
          (let f ([level level])
            (if (fx=? level 0)
                up
                #`(lambda (x) (map #,(f (fx- level 1)) x))))))
      [(,[mv up] ,level ,accessor)
       (values mv (build-unparser-for-level up level))]
      [(optional ,[mv up] ,level ,accessor)
       (values mv
         (build-unparser-for-level
           #`(lambda (x) (and x (#,up x)))
           level))])
    (Reference : Reference (ir) -> * (mv up)
      [(reference ,id0 ,id1 ,b) (values id0 id1)])
    (Defn ir))

  (define-pass build-parser : Lannotated (ir name) -> * (stx)
    (definitions
      (define-pass extract-bindings : (Lannotated Pattern) (ir) -> * (id*)
        (definitions
          (define (Pattern* pattern* id*)
            (let f ([pattern* pattern*])
              (if (null? pattern*)
                  id*
                  (Pattern (car pattern*) (f (cdr pattern*)))))))
        (Pattern : Pattern (ir id*) -> * (id*)
          [,id id*]
          [,ref (Reference ref id*)]
          [(maybe ,[id*]) id*]
          [,null id*]
          [(,[id*] ,dots) id*]
          [(,pattern0 . ,[id*]) (Pattern pattern0 id*)]
          [(,pattern0 ,dots ,pattern1 ... . ,[id*])
           (Pattern pattern0 (Pattern* pattern1 id*))])
        (Reference : Reference (ir id*) -> * (id*)
          [(reference ,id0 ,id1 ,b) (cons id0 id*)])
        (Pattern ir '()))
      (define (build-body id prod*)
        (let f ([prod* prod*])
          (if (null? prod*)
              #'fk
              (with-syntax ([(fk) (generate-temporaries '(fk))])
                (Production (car prod*) id #'fk
                  #`(lambda () #,(f (cdr prod*))))))))
      (define (Pattern* pattern* pattern sexp-id body fk)
        (let f ([pattern* pattern*] [sexp-id sexp-id])
          (if (null? pattern*)
              (Pattern pattern sexp-id body fk)
              (with-syntax ([(a d) (generate-temporaries '(a d))])
                #`(if (pair? #,sexp-id)
                      (let ([a (car #,sexp-id)] [d (cdr #,sexp-id)])
                        #,(Pattern (car pattern*) #'a (f (cdr pattern*) #'d) #'fk))
                      (#,fk)))))))
    (Defn : Defn (ir) -> * (stx)
      [(define-language ,id ,[mv pname pred term?] ,id? ,rtd ,rcd ,tag-mask (,term* ...) ,[p* n*] ...)
       (with-syntax ([(p* ...) p*]
                     [(n* ...) n*]
                     [who (datum->syntax name 'who)])
         #`(define #,name
             (let ()
               (define-pass #,name : * (sexp entry) -> #,id ()
                 (definitions
                   (define (squawk) (errorf who "unrecognized syntax ~s" sexp)))
                 p* ...
                 (case entry
                   [(n*) (n* sexp squawk)] ...
                   [else (errorf who "Unexpected entry name ~s" entry)]))
               (case-lambda
                 [(sexp) (#,name sexp '#,pname)]
                 [(sexp entry) (#,name sexp entry)]))))])
    (Nonterminal : Nonterminal (ir) -> * (stx n)
      [(,id (,id* ...) ,b ,rtd ,rcd ,tag ,pred ,all-pred ,all-term-pred ,prod* ...)
       (values #`(#,id : * (sexp fk) -> #,id () #,(build-body id prod*)) id)])
    (Production : Production (ir id fk-id fk) -> * (stx)
      [(production ,[pattern -> build-rec] ,pretty-prod? ,rtd ,tag ,pred ,maker ,field* ...)
       (with-syntax ([quasiquote (datum->syntax id 'quasiquote)])
         #`(let ([#,fk-id #,fk]) #,(Pattern pattern #'sexp #`(quasiquote #,build-rec) fk-id)))]
      [(terminal ,[mv p pred term?] ,pretty-prod?)
       #`(let ([#,fk-id #,fk]) (if (#,pred sexp) sexp (#,fk-id)))]
      [(nonterminal ,[mv p pred term?] ,pretty-prod?)
       #`(let ([#,fk-id #,fk]) (#,p sexp #,fk-id))])
    (Pattern : Pattern (ir sexp-id body fk) -> * (stx)
      [,id #`(if (eq? #,sexp-id '#,id) #,body (#,fk))]
      [,ref (let-values ([(mv p pred term?) (Reference ref)])
              (if term?
                  #`(if (#,pred #,sexp-id)
                        (let ([#,mv #,sexp-id]) #,body)
                        (#,fk))
                  #`(let ([#,mv (#,p #,sexp-id #,fk)]) #,body)))]
      [,null #`(if (null? #,sexp-id) #,body (#,fk))]
      [(maybe ,[mv p pred term?])
       (if term?
           #`(if (or (eq? #,sexp-id #f)
                     (#,pred #,sexp-id))
                 (let ([#,mv #,sexp-id]) #,body)
                 (#,fk))
           #`(let ([#,mv (and #,sexp-id (#,p #,sexp-id #,fk))]) #,body))]
      [(,pattern ,dots)
       (let ([binding* (extract-bindings pattern)])
         (with-syntax ([(t0 t1 loop) (generate-temporaries '(t0 t1 loop))]
                       [(tbinding ...) (generate-temporaries binding*)]
                       [(binding ...) binding*])
           #`(let loop ([t0 #,sexp-id] [tbinding '()] ...)
               (cond
                 [(pair? t0)
                  (let ([t1 (car t0)] [t0 (cdr t0)])
                    #,(Pattern pattern #'t1 #'(loop t0 (cons binding tbinding) ...) fk))]
                 [(null? t0)
                  (let ([binding (reverse tbinding)] ...)
                    #,body)]
                 [else (#,fk)]))))]
      [(,pattern0 . ,pattern1)
       (with-syntax ([(a d) (generate-temporaries '(a d))])
         #`(if (pair? #,sexp-id)
               (let ([a (car #,sexp-id)] [d (cdr #,sexp-id)])
                 #,(Pattern pattern0 #'a
                     (Pattern pattern1 #'d body fk)
                     fk))
               (#,fk)))]
      [(,pattern0 ,dots ,pattern1 ... . ,pattern2)
       (let ([binding* (extract-bindings pattern0)])
         (with-syntax ([(binding ...) binding*]
                       [(tbinding ...) (generate-temporaries binding*)]
                       [(t0 t1 new-k loop) (generate-temporaries '(t0 t1 new-fk loop))])
           #`(let loop ([t0 #,sexp-id] [tbinding '()] ...)
               (let ([new-fk (lambda ()
                               (if (pair? t0)
                                   (let ([t1 (car t0)] [t0 (cdr t0)])
                                     #,(Pattern pattern0 #'t1
                                         #'(loop t0 (cons binding tbinding) ...)
                                         fk))
                                   (#,fk)))])
                 #,(Pattern* pattern1 pattern2 #'t0
                     #`(let ([binding (reverse tbinding)] ...)
                         #,body)
                     #'new-fk)))))])
    (BuildPattern : Pattern (ir) -> * (stx)
      [,id id]
      [,ref (let-values ([(mv up pred term?) (Reference ref)]) #`,#,mv)]
      [,null #'()]
      [(maybe ,[mv up pred term?]) #`,#,mv]
      [(,[pattern] ,dots) #`(#,pattern (... ...))]
      [(,[pattern0] ,dots ,[pattern1] ... .  ,[pattern2])
       #`(#,pattern0 (... ...) #,@pattern1 . #,pattern2)]
      [(,[pattern0] . ,[pattern1]) #`(#,pattern0 . #,pattern1)]) 
    (Reference : Reference (ir) -> * (mv pname pred term?)
      [(reference ,id0 ,id1 ,b)
       (let ([r (unbox b)])
         (values id0 id1
           (if (Lannotated-Terminal? r)
               (nanopass-case (Lannotated Terminal) r
                 [(,id (,id* ...) ,b ,handler? ,pred) pred])
               #f)
           (Lannotated-Terminal? r)))])
    (Defn ir))

  (define (star? x)
    (or (eq? x '*)
        (eq? (syntax->datum x) '*)))

  (define (modifier? x)
    (memq (syntax->datum x) '(echo trace)))

  (define (definitions? x)
    (or (eq? x 'definitions)
        (eq? (syntax->datum x) 'defintions)))

  (define (options? x)
    (or (eq? x 'options)
        (eq? (syntax->datum x) 'options)))

  (define-language Lpass-src
    (terminals
      (identifier (id))
      (colon (:))
      (arrow (->))
      (star (*))
      (definitions (definitions))
      (options (options))
      (syntax (stx))
      (modifier (modifier))
      (null (null))
      (dots (dots))
      (unquote (unquote))
      (boolean (b)))
    (Program (prog)
      (define-pass id : lname0 (id* ...) -> lname1 (out* ...)
        (options opt* ...)
        (definitions stx* ...)
        proc* ...
        (maybe stx)))
    (LanguageName (lname)
      *
      id
      (id0 id1))
    (Processor (proc)
      (id : id0 (in* ...) -> id1 (out* ...)
        (options opt* ...)
        (definitions stx* ...)
        cl* ...))
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
      (binding hole)
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
      (stx* ... -> . cata-out)
      cata-out)
    (CatamorphismOutputVariables (cata-out)
      (id* ...))
    (Option (opt)
      (trace b)
      (echo b)
      (generate-transformers b)))

  (define-pass parse-pass : * (stx who) -> Lpass-src ()
    (definitions
      (define (has-language? lang)
        (nanopass-case (Lpass-src LanguageName) lang
          [,* #f]
          [else #t])))
    (Program : * (stx) -> Program ()
      (syntax-case stx ()
        [(_ pass-name ?colon iname  (fml ...) ?arrow oname (xval ...) . rest)
         (let ([squawk (lambda (msg what) (syntax-violation who msg stx what))])
           (unless (identifier? #'pass-name) (squawk "invalid pass name" #'pass-name))
           (unless (eq? (datum ?colon) ':) (squawk "expected colon" #'?colon))
           (let ([ilang (LanguageName #'iname squawk)] [fml* #'(fml ...)])
             (unless (for-all identifier? #'(fml ...)) (squawk "expected list of identifiers" fml*))
             (when (and (has-language? ilang) (null? fml*)) (squawk "expected non-empty list of formals" fml*))
             (unless (eq? (datum ?arrow) '->) (squawk "expected arrow" #'?arrow))
             (let ([olang (LanguageName #'oname squawk)])
               (define (looks-like-processor? x)
                 (let loop ([x x] [mcount 0])
                   (syntax-case x ()
                     [(pname ?colon itype (fml ...) ?arrow otype (xval ...) . more)
                      (and (eq? (datum ?colon) ':)
                           (eq? (datum ?arrow) '->)
                           (identifier? #'itype)
                           (identifier? #'otype)
                           (for-all (lambda (fml)
                                      (or (identifier? fml)
                                          (syntax-case fml ()
                                            [[fml exp-value] (identifier? #'fml)])))
                                    #'(fml ...)))
                      #t]
                     [(?modifier ?not-colon . more)
                      (and (memq (datum ?modifier) '(trace echo))
                           (not (eq? (datum ?not-colon) ':))
                           (< mcount 2))
                      (loop #'(?not-colon . more) (fx+ mcount 1))]
                     [_ #f])))
               (define (s0 rest defn* pass-options)
                 (syntax-case rest ()
                   [((definitions defn* ...) . rest)
                    (eq? (datum definitions) 'definitions)
                    (s0 #'rest #'(defn* ...) pass-options)]
                   [((pass-options options ...) . rest)
                    (eq? (datum pass-options) 'pass-options)
                    (s0 #'rest defn* (map Option #'(options ...)))]
                   [_ (s1 rest defn* pass-options '())]))
               (define (s1 rest defn* pass-options processor*)
                 (syntax-case rest ()
                   [(a . rest)
                    (looks-like-processor? #'a)
                    (s1 #'rest defn* pass-options (cons (Processor #'a squawk) processor*))]
                   [_ (s2 rest defn* pass-options processor*)]))
               (define (s2 rest defn* pass-options processor*)
                 `(define-pass ,#'pass-name ,#'?colon ,ilang (,fml* ...) ,#'?arrow ,olang (,#'(xval ...) ...)
                    (options ,(or pass-options '()) ...)
                    (definitions ,defn* ...)
                    ,processor* ...
                    ,(syntax-case rest ()
                       [() #f]
                       [oth #`(begin . oth)])))
               (s0 #'rest '() #f))))]))
    (LanguageName : * (stx squawk) -> LanguageName ()
      (syntax-case stx ()
        [* (eq? (datum #'*) '*) #'*]
        [id (identifier? #'id) #'id]
        [(id0 id1)
         (and (identifier? #'id0) (identifier? #'id1))
         `(,#'id0 ,#'id1)]
        [_ (squawk "invalid language specifier" stx)]))
    (Option : * (stx squawk) -> Option ()
      (syntax-case stx ()
        [trace (eq? (datum #'trace) 'trace) `(trace #t)]
        [echo (eq? (datum #'echo) 'echo) `(echo #t)]
        [generate-transformers (eq? (datum #'generate-transforms) 'generate-transforms) `(generate-transformers #t)]
        [_ (squawk "unexpected option" stx)]))
    (Processor : * (stx squawk) -> Processor ()
      (let s0 ([stx stx] [modifier* '()])
        (syntax-case stx ()
          [(pname ?colon itype (fml ...) ?arrow otype (xval ...) . more)
           (and (eq? (datum ?colon) ':)
                (eq? (datum ?arrow) '->)
                (identifier? #'itype)
                (identifier? #'otype)
                (for-all (lambda (fml)
                           (or (identifier? fml)
                               (syntax-case fml ()
                                 [[fml exp-value] (identifier? #'fml)])))
                         #'(fml ...)))
           (syntax-case #'more ()
             [((definitions defn ...) cl ...)
              (eq? (datum definitions) 'definitions)
              (let ([cl* (map Clause #'(cl ...))]
                    [in* (map InputArgument #'(fml ...))])
                `(,#'id ,#'?colon ,#'itype (,in* ...) ,#'?arrow ,#'otype (,#'(xval ...) ...)
                   (options ,modifier* ...)
                   (definitions ,#'(defn ...) ...)
                   ,cl* ...))]
             [(cl ...)
              (let ([cl* (map Clause #'(cl ...))]
                    [in* (map InputArgument #'(fml ...))])
                `(,#'id ,#'?colon ,#'itype (,in* ...) ,#'?arrow ,#'otype (,#'(xval ...) ...)
                   (options ,modifier* ...)
                   (definitions)
                   ,cl* ...))])]
          [(?modifier ?not-colon . more)
           (s0 #'(?not-colon . more) (cons (Option #'?modifier squawk) modifier*))])))
    (InputArgument : * (stx) -> InputArgument ()
      (syntax-case stx ()
        [id (identifier? #'id) #'id]
        [[id stx] (identifier? #'id) `(,#'id ,#'stx)]))
    (Clause : * (stx) -> Clause ()
      (syntax-case stx ()
        [(pattern stx* ... stx)
         (let ([pattern (Pattern #'pattern)])
           `(,pattern ,#'(stx* ...) ... ,#'stx))]))
    (Pattern : * (stx) -> Pattern ()
      (syntax-case stx ()
        [id (identifier? #'id) #'id]
        [(unq hole) (eq? (datum unq) 'unquote) `(binding ,(Hole #'hole))]
        [(pattern dots) (eq? (datum dots) '...) `(,(Pattern #'pattern) ,#'dots)]
        [(pattern0 dots pattern1 ... . pattern2)
         (eq? (datum dots) '...)
         `(,(Pattern #'pattern0) ,#'dots ,(map Pattern #'(pattern1 ...)) . ,(Pattern #'pattern2))]
        [(pattern0 . pattern1) `(,(Pattern #'pattern0) . ,(Pattern #'pattern1))]
        [null '()]))
    (Hole : * (stx) -> Hole ()
      (syntax-case stx ()
        [id (identifier? #'id) #'id]
        [_ (Catamorphism stx)]))
    (Catamorphism : * (stx) -> Catamorphism ()
      (let ()
        (define (s0 stx)
          (syntax-case stx ()
            [(: . stx) (colon? #':) (s2 #f #'stx)]
            [(-> . stx) (arrow? #'->) (s4 #f #f '() #'stx)]
            [(e . stx) (s1 #'e #'stx)]
            [() (in-context CatamorphismOutputVariables `(,'() ...))]))
        (define (s1 e stx)
          (syntax-case stx ()
            [(: . stx) (colon? #':) (s2 e #'stx)]
            [(-> . stx)
             (and (arrow? #'->) (identifier? e))
             (s4 #f (list e) '() #'stx)]
            [(expr . stx)
             (identifier? e)
             (s3 #f (list #'expr e) #'stx)]
            [() (identifier? e) (in-context CatamorphismOutputVariables `(,e))]))
        (define (s2 f stx)
          (syntax-case stx ()
            [(-> . stx)
             (arrow? #'->)
             (s4 f #f '() #'stx)]
            [(id . stx)
             (identifier? #'id)
             (s3 f (list #'id) #'stx)]))
        (define (s3 f e* stx)
          (syntax-case stx ()
            [(-> . stx)
             (arrow? #'->)
             (s4 f (reverse e*) '() #'stx)]
            [(e . stx)
             (s3 f (cons #'e e*) #'stx)]
            [()
             (for-all identifier? e*)
             `(,f : -> ,e* ...)]))
        (define (s4 f maybe-inid* routid* stx)
          (syntax-case stx ()
            [(id . stx)
             (identifier? #'id)
             (s4 f maybe-inid* (cons #'id routid*) #'stx)]
            [() `(,f : ,(or maybe-inid* '()) ... -> ,(reverse routid*) ...)]))
        (s0 stx)))
    (Program stx))

  (define-language Lpass
    (extends Lpass-src)
    (terminals
      (+ (Lannotated (np-lang))))
    (Program (prog)
      (- (define-pass id : lname0 (id* ...) -> lname1 (out* ...)
           (options opt* ...)
           (definitions stx* ...)
           proc* ...
           (maybe stx)))
      (+ (define-pass id : lang0 (id* ...) -> lang1 (stx0* ...)
           (options opt* ...)
           (definitions stx1* ...)
           proc* ...
           stx)))
    (LanguageName (lname)
      (- *
         id
         (id0 id1)))
    (Language (lang)
      (+ (none)
         np-lang
         (np-lang id)))
    (Clause (cl)
      (- (pattern stx* ... stx))
      (+ (pattern stx)))
    (Catamorphism (cata)
      (- (stx : . cata-remainder)
         cata-remainder)
      (+ (stx : (stx* ...) -> id* ...)))
    (CatamorphismRemainder (cata-remainder)
      (- (stx* ... -> . cata-out)
         cata-out))
    (CatamorphismOutputVariables (cata-out)
      (- (id* ...))))

  #|
  (define-pass expand-pass : Lpass-src (ir rho caller-who) -> Lpass ()
    (Defn : Defn (ir) -> Defn ()
      [(define-pass ,id ,: ,[lang0] (,id* ...) ,-> ,[lang1] (,out* ...)
         (,options ,opt* ...)
         (,definitions ,stx* ...)
         ,proc* ...
         ,stx?)
       `(define-pass ,id ,: ,lang0 (,id* ...) ,-> ,lang1 (,out* ...)
          (,options ,opt* ...)
          (,definitons ,stx* ...)
          ,proc* ...
          ,(or stx? (find-entry-processor 
  |#

  (define lookup-language
    (lambda (rho name)
      (let ([lang (rho name #'experimental-language)])
        (unless (language-information? lang)
          (errorf 'with-language "unable to find language information for ~s" (syntax->datum name)))
        lang)))
  )
