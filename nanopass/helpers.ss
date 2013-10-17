;;; Copyright (c) 2000-2013 Dipanwita Sarkar, Andrew W. Keep, R. Kent Dybvig, Oscar Waddell
;;; See the accompanying file Copyright for detatils

(library (nanopass helpers)
  (export combine ellipsis? unquote? unique-symbol construct-id
    #;ensure-no-suffix #;generate-acc partition-syn gentemp bound-id-member?
    bound-id-union #;my-enumerate colon? arrow? #;warning #;syntax-error format
    make-compile-time-value pretty-print trace-define trace-let
    trace-define-syntax trace-lambda printf echo-syntax gensym
    construct-id-call-count construct-id-constructed-identifiers extends
    definitions entry terminals nongenerative-id define-auxiliary-keyword
    define-auxiliary-keywords plus? minus? double-arrow? double-equal? splice?
    list-of? rec with-values meta-var->raw-meta-var warningf errorf
    meta-parser-property #;define-property define-who datum list-head module
    indirect-export syntax->source-info optimize-level
    all-unique-identifiers? regensym make-list iota with-implicit
    eq-hashtable-set! eq-hashtable-ref define-nanopass-record np-parse-fail-token)
  (import (rnrs) (nanopass implementation-helpers))

  (define all-unique-identifiers?
    (lambda (ls)
      (and (for-all identifier? ls)
           (let f ([ls ls])
             (if (null? ls)
                 #t
                 (let ([id (car ls)] [ls (cdr ls)])
                   (and (not (memp (lambda (x) (free-identifier=? x id)) ls))
                        (f ls))))))))

  (define-syntax with-values
    (syntax-rules ()
      [(_ p c) (call-with-values (lambda () p) c)]))

  (define-syntax rec
    (syntax-rules ()
      [(_ name proc) (letrec ([name proc]) name)]
      [(_ (name . arg) body body* ...)
       (letrec ([name (lambda arg body body* ...)]) name)]))

  (define-syntax define-auxiliary-keyword
    (syntax-rules ()
      [(_ name)
       (define-syntax name 
         (lambda (x)
           (syntax-violation 'name "misplaced use of auxiliary keyword" x)))]))
  
  (define-syntax define-auxiliary-keywords
    (syntax-rules ()
      [(_ name* ...)
       (begin
         (define-auxiliary-keyword name*) ...)]))

  (define-auxiliary-keywords extends definitions entry terminals nongenerative-id meta-parser-property)
  
  #;(define-syntax syntax-error
    (syntax-rules ()
      [(_ obj) (syntax-violation #f "invalid syntax (syntax-error)" obj)]
      [(_ obj str) (syntax-violation #f str obj)]
      [(_ obj str1 o2 o3 ...)
       (syntax-violation #f (format str1 o2 o3 ...) obj)]))

  (define-syntax datum
    (syntax-rules ()
      [(_ id) (syntax->datum #'id)]))

  (define-syntax define-who
    (lambda (x)
      (syntax-case x ()
        [(k name expr)
         (with-implicit (k who)
           #'(define name (let () (define who 'name) expr)))]
        [(k (name . fmls) expr exprs ...)
         #'(define-who name (lambda (fmls) expr exprs ...))])))

  ;;; moved from meta-syntax-dispatch.ss and nano-syntax-dispatch.ss
  (define combine
    (lambda (r* r)
      (if (null? (car r*))
          r
          (cons (map car r*) (combine (map cdr r*) r))))) 
  
  ;;; moved from meta-syntax-dispatch.ss and syntaxconvert.ss
  (define ellipsis?
    (lambda (x)
      (and (identifier? x) (free-identifier=? x (syntax (... ...)))))) 

  (define unquote?
    (lambda (x)
      (and (identifier? x) (free-identifier=? x (syntax unquote)))))

  (define plus?
    (lambda (x)
      (and (identifier? x)
           (or (free-identifier=? x #'+)
               (eq? (syntax->datum x) '+)))))

  (define minus?
    (lambda (x)
      (and (identifier? x)
           (or (free-identifier=? x #'-)
               (eq? (syntax->datum x) '-)))))

  (define double-arrow?
    (lambda (x)
      (and (identifier? x)
           (or (free-identifier=? x #'=>)
               (eq? (syntax->datum x) '=>)))))

  (define double-equal?
    (lambda (x)
      (and (identifier? x)
           (or (free-identifier=? x #'==)
               (eq? (syntax->datum x) '==)))))

  (define colon?
    (lambda (x)
      (and (identifier? x)
           (or (free-identifier=? x #':)
               (eq? (syntax->datum x) ':)))))

  (define arrow?
    (lambda (x)
      (and (identifier? x)
           (or (free-identifier=? x #'->)
               (eq? (syntax->datum x) '->)))))

  (define splice?
    (lambda (x)
      (and (identifier? x)
           (or (free-identifier=? x #'splice)
               (eq? (syntax->datum x) 'splice)))))

  (define list-of? 
    (lambda (x)
      (and (identifier? x)
           (or (free-identifier=? x #'list-of)
               (eq? (syntax->datum x) 'list-of)))))

  ;;; unique-symbol produces a unique name derived the input name by
  ;;; adding a unique suffix of the form .<digit>+.  creating a unique
  ;;; name from a unique name has the effect of replacing the old
  ;;; unique suffix with a new one.
  
  (define unique-suffix
    (let ((count 0))
      (lambda ()
        (set! count (+ count 1))
        (number->string count))))
  
  (define unique-symbol
    (lambda (id . id*)
      (string->symbol
        (string-append
          (fold-right
            (lambda (id str) (string-append str ":" (symbol->string (syntax->datum id))))
            (symbol->string (syntax->datum id)) id*)
          "."
          (unique-suffix)))))

  ;; This is a macro that shows what the language name identifier is
  ;; bound to in the expansion time environment 
  (define-syntax show
    (lambda (x)
      (syntax-case x ()
        [(k id)
         (lambda (r)
           (with-syntax ((x (datum->syntax #'k (r #'id))))
             #''x))]))) 
  
  ; TODO: at some point we may want this to be a little bit more
  ; sophisticated, or we may want to have something like a regular
  ; expression style engine where we bail as soon as we can identify
  ; what the meta-var corresponds to.
  (define meta-var->raw-meta-var
    (lambda (sym)
      (let ([s (symbol->string sym)])
        (let f ([i (fx- (string-length s) 1)])
          (cond
            [(fx=? i -1) sym]
            [(or 
               (char=? #\* (string-ref s i))
               (char=? #\^ (string-ref s i))
               (char=? #\? (string-ref s i)))
             (f (fx- i 1))]
            [else (let f ([i i])
                    (cond
                      [(fx=? i -1) sym]
                      [(char-numeric? (string-ref s i)) (f (fx- i 1))]
                      [else (string->symbol (substring s 0 (fx+ i 1)))]))])))))

  (define lookup
    (lambda (id extract ls)
      (and (identifier? id)
           (exists (lambda (x) 
                     (and (free-identifier=? 
                            (datum->syntax #'mars (syntax->datum id))
                            (datum->syntax #'mars (syntax->datum (extract x))))
                          x)) ls)))) 
  
  (define construct-id-call-count
    (let ([count 0])
      (case-lambda
        [() count]
        [(n) (set! count n)])))

  (define construct-id-constructed-identifiers
    (let ([ht (make-eq-hashtable)])
      (case-lambda
        [() (map (lambda (key) (cons key (hashtable-ref ht key #f)))
                 (vector->list (hashtable-keys ht)))]
        [(id) (hashtable-set! ht id (+ (hashtable-ref ht id 0) 1)) id])))

  ;; This concatenates two identifiers with a string inbetween like "-"
  (define construct-id
    (lambda (tid x . x*)
      (define ->str
        (lambda (x)
          (cond
            [(string? x) x]
            [(identifier? x) (symbol->string (syntax->datum x))]
            [(symbol? x) (symbol->string x)]
            [else (error 'construct-id "invalid input ~s" x)])))
        (unless (identifier? tid)
          (error 'construct-id "template argument ~s is not an identifier" tid))
        #;(construct-id-call-count (+ (construct-id-call-count) 1))
        (datum->syntax 
          tid 
          (string->symbol (apply string-append (->str x) (map ->str x*)))
          #;(construct-id-constructed-identifiers
            (string->symbol (apply string-append (->str x) (map ->str x*)))))))

  #;(define ensure-no-suffix
    (lambda (id)
      (let ([s (symbol->string (syntax->datum id))])
        (let ([n (string-length s)])
          (when (and (> n 0) (char-numeric? (string-ref s (- n 1))))
            (syntax-violation 'ensure-no-suffix 
                              "invalid numeric suffix in metavariable" id)))))) 
  
  #;(define generate-acc
    (lambda (n x)
      (letrec ([helper
                 (lambda (n)
                   (if (= n 2)
                       (list #'cdr x)
                       (list #'cdr (helper (- n 1)))))])
        (cond
          [(= n 0) x]
          [(= n 1) (list #'car x)]
          [else (list #'car (helper n))])))) 
  
  (define find-decls
    (lambda (decl decls)
      (cond
        [(null? decls) #f]
        [(eq? decl (caar decls)) (car decls)]
        [else (find-decls decl (cdr decls))]))) 
  
  (define-syntax partition-syn
    (lambda (x)
      (syntax-case x ()
        [(_ ls-expr () e0 e1 ...) #'(begin ls-expr e0 e1 ...)]
        [(_ ls-expr ([set pred] ...) e0 e1 ...)
         (with-syntax ([(pred ...) 
                        (let f ([preds #'(pred ...)])
                          (if (null? (cdr preds))
                              (if (free-identifier=? (car preds) #'otherwise)
                                  (list #'(lambda (x) #t))
                                  preds)
                              (cons (car preds) (f (cdr preds)))))])
           #'(let-values ([(set ...)
                           (let f ([ls ls-expr])
                             (if (null? ls)
                                 (let ([set '()] ...) (values set ...))
                                 (let-values ([(set ...) (f (cdr ls))])
                                   (cond
                                     [(pred (car ls))
                                      (let ([set (cons (car ls) set)])
                                        (values set ...))]
                                     ...
                                     [else (error 'partition-syn 
                                                  "no home for ~s"
                                                  (car ls))]))))])
               e0 e1 ...))])))
  
  (define gentemp
    (lambda ()
      (car (generate-temporaries '(#'t))))) 
  
  (define bound-id-member? 
    (lambda (id id*)
      (and (not (null? id*))
           (or (bound-identifier=? id (car id*))
               (bound-id-member? id (cdr id*)))))) 
  
  (define bound-id-union ; seems to be unneeded
    (lambda (ls1 ls2)
      (cond
        [(null? ls1) ls2]
        [(bound-id-member? (car ls1) ls2) (bound-id-union (cdr ls1) ls2)]
        [else (cons (car ls1) (bound-id-union (cdr ls1) ls2))]))) 
  
  #;(define my-enumerate
    (lambda (n ctr)
      (if (= n ctr) '() (cons ctr (my-enumerate n (+ ctr 1)))))) 
  
  ;;; Higher order stuff
  (define compose
    (case-lambda
      [() (lambda (x) x)]
      [(f) f]
      [(f . g*) (lambda (x) (f ((apply compose g*) x)))])) 
  
  (define disjoin
    (case-lambda
      [() (lambda (x) #f)]
      [(p?) p?]
      [(p? . q?*) (lambda (x) (or (p? x) ((apply disjoin q?*) x)))])) 
  
  #;(define-syntax warning
    (syntax-rules ()
      [(_ who fmt obj ...)
       (raise-continuable
         (condition
           (make-warning)
           (make-who-condition who)
           (make-message-condition (format fmt obj ...))))]))
  
  (define echo-syntax
    (lambda (x)
      (pretty-print (syntax->datum x))
      x))
  
  (define syntax->source-info
    (lambda (stx)
      (let ([si (syntax->source-information stx)])
        (and si
             (cond
               [(and (source-information-position-line si)
                     (source-information-position-column si))
                (format "~s line ~s, char ~s of ~a"
                  (source-information-type si)
                  (source-information-position-line si)
                  (source-information-position-column si)
                  (source-information-source-file si))]
               [(source-information-byte-offset-start si)
                (format "~s byte position ~s of ~a"
                  (source-information-type si)
                  (source-information-byte-offset-start si)
                  (source-information-source-file si))]
               [(source-information-char-offset-start si)
                (format "~s character position ~s of ~a"
                  (source-information-type si)
                  (source-information-char-offset-start si)
                  (source-information-source-file si))]
               [else (format "in ~a" (source-information-source-file si))]))))))
