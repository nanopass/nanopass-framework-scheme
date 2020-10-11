;;; Copyright (c) 2000-2020 Dipanwita Sarkar, Andrew W. Keep, R. Kent Dybvig, Oscar Waddell
;;; See the accompanying file Copyright for details

(library (nanopass nano-syntax-dispatch)
  (export nano-syntax-dispatch)
  (import (rnrs) (nanopass helpers))

  (define-syntax match-each
    (syntax-rules ()
      [(_ ?e p)
       (let f ([e ?e])
         (cond
           [(pair? e) (match (car e) p (f (cdr e)))]
           [(null? e) '()]
           [else #f]))]))

  (define-syntax match-remainder
    (syntax-rules ()
      [(_ ?e () z-pat ?r)
       (let loop ([e ?e] [re* '()])
         (if (pair? e)
             (loop (cdr e) (cons (car e) re*))
             (values re* (match e z-pat ?r))))]
      [(_ ?e (y-pat . y-pat-rest) z-pat ?r)
       (let-values ([(re* r) (match-remainder ?e y-pat-rest z-pat ?r)])
         (if r
             (if (null? re*)
                 (values #f #f)
                 (values (cdr re*) (match (car re*) y-pat r)))
             (values #f #f)))]))

  (define-syntax match-each+
    (syntax-rules ()
      [(_ e x-pat y-pat z-pat ?r)
       (let-values ([(re* r) (match-remainder e y-pat z-pat ?r)])
         (if r
             (let loop ([re* re*] [xr* '()])
               (if (null? re*)
                   (values xr* r)
                   (let ([xr (match (car re*) x-pat '())])
                     (if xr
                         (loop (cdr re*) (cons xr xr*))
                         (values #f #f)))))
             (values #f #f)))]))

  (define-syntax match-each-any
    (syntax-rules ()
      [(_ ?e)
       (let f ([e ?e])
         (cond
           [(pair? e)
            (let ([l (f (cdr e))])
              (and l (cons (car e) l)))]
           [(null? e) '()]
           [else #f]))]))

  (define-syntax match-empty
    (lambda (x)
      (syntax-case x (any each-any each each+)
        [(_ () r) #'r]
        [(_ any r) #'(cons '() r)]
        [(_ (a . d) r) #'(match-empty a (match-empty d r))]
        [(_ each-any r) #'(cons '() r)]
        [(_ #(each p1) r) #'(match-empty p1 r)]
        [(_ #(each+ p1 (p2 ...) p3) r)
         (with-syntax ([(rp2 ...) (reverse #'(p2 ...))])
           #'(match-empty p1 (match-empty (rp2 ...) (match-empty p3 r))))])))

  (define-syntax match
    (syntax-rules (any)
      [(_ e any r) (and r (cons e r))]
      [(_ e p r) (and r (match* e p r))]))

  (define-syntax match*
    (syntax-rules (any each-any each each+)
      [(_ e () r) (and (null? e) r)]
      [(_ e (a . d) r) (and (pair? e) (match (car e) a (match (cdr e) d r)))]
      [(_ e each-any r) (let ([l (match-each-any e)]) (and l (cons l r)))]
      [(_ e #(each p1) ?r)
       (if (null? e)
           (match-empty p1 ?r)
           (let ([r* (match-each e p1)])
             (and r* (let combine ([r* r*] [r ?r])
                       (if (null? (car r*))
                           r
                           (cons (map car r*) (combine (map cdr r*) r)))))))]
      [(_ e #(each+ p1 p2 p3) ?r)
       (let-values ([(xr* r) (match-each+ e p1 p2 p3 ?r)])
         (and r (if (null? xr*)
                    (match-empty p1 r)
                    (let combine ([r* xr*] [r r])
                      (if (null? (car r*))
                          r
                          (cons (map car r*) (combine (map cdr r*) r)))))))]))

  (define-syntax nano-syntax-dispatch
    (syntax-rules (any)
      [(_ e any) (list e)]
      [(_ e p) (match* e p '())])))
