;;; Copyright (c) 2000-2015 Dipanwita Sarkar, Andrew W. Keep, R. Kent Dybvig, Oscar Waddell
;;; See the accompanying file Copyright for details

(library (nanopass unparser)
  (export make-unparser)
  (import (rnrs)
          (nanopass helpers)
          (nanopass records)
          (nanopass syntaxconvert)) 
  
  (define make-unparser
    (lambda (desc)
      (let* ([lang-name (language-name desc)]
             [ntspecs (language-ntspecs desc)]
             [tspecs (language-tspecs desc)])
        (with-syntax ([(proc-name ...) (map ntspec-unparse-name ntspecs)]
                      [(ntspec? ...) (map ntspec-pred ntspecs)]
                      [(tspec? ...) (map tspec-pred tspecs)]
                      [(tspec-body ...) (map make-unparse-term-clause-body tspecs)])
          (with-syntax ([(proc ...)
                         (map (lambda (ntspec procname)
                                (make-unparse-proc
                                  tspecs ntspecs ntspec procname))
                              ntspecs #'(proc-name ...))])
            #`(rec f (case-lambda
                       [(ir) (f ir #f)]
                       [(ir raw?)
                        (define proc-name proc) ...
                        (cond
                          [(ntspec? ir) (proc-name ir)] ...
                          ; TODO: should be calling the prettify function on these potentially
                          [(tspec? ir) tspec-body] ...
                          [else (error '#,lang-name
                                  "unrecognized language record"
                                  ir)])])))))))

  (define make-unparse-term-clause-body
    (lambda (tspec)
      (let ([h (tspec-handler tspec)])
        (if h
            #`(if raw? ir (#,h ir))
            #'ir))))
  
  (define make-unparse-proc
    (lambda (tspecs ntspecs ntspec procname)
      ;; handles alts of the form: LambdaExpr where LambdaExpr is another
      ;; non-terminal specifier with no surrounding markers.
      (define make-nonterm-clause
        (lambda (alt)
          (let ([ntspec (nonterminal-alt-ntspec alt)])
            (let ([nonterm-proc (ntspec-unparse-name ntspec)]
                   [nonterm-pred? (ntspec-all-pred ntspec)])
              (list #`((#,nonterm-pred? ir) (#,nonterm-proc ir)))))))

      ;; handles alts of the form: x, c where x and c are meta-variables
      ;; that refer to terminals, and have no surrounding marker.
      (define-who make-term-clause ;; only atom alt cases
        (lambda (alt)
          (let ([tspec (terminal-alt-tspec alt)])
            (with-syntax ([pred? (tspec-pred tspec)]
                           [tspec-body (make-unparse-term-clause-body tspec)])
              #'((pred? ir) tspec-body)))))

      (define strip-maybe
        (lambda (tmpl)
          (syntax-case tmpl (maybe)
            [(maybe x) (and (identifier? #'x) (eq? (datum maybe) 'maybe)) #'x]
            [(a . d) (with-syntax ([a (strip-maybe #'a)] [d (strip-maybe #'d)]) #'(a . d))]
            [() tmpl]
            [oth tmpl])))

      (define build-accessor-expr
        (lambda (acc level maybe?)
          (let loop ([level level] [f #`(lambda (t) 
                                          #,(if maybe?
                                                #'(and t (f t raw?))
                                                #'(f t raw?)))])
            (if (fx=? level 0)
                #`(#,f (#,acc ir))
                (loop (fx- level 1) #`(lambda (t) (map #,f t)))))))

      (define build-template-wrapper
        (lambda (tmpl alt)
          (with-syntax ([(e ...) (map build-accessor-expr
                                   (pair-alt-accessors alt)
                                   (pair-alt-field-levels alt)
                                   (pair-alt-field-maybes alt))]
                        [(fld ...) (pair-alt-field-names alt)]
                        [tmpl tmpl])
            #'(let ([fld e] ...)
                (with-extended-quasiquote
                  (with-auto-unquote (fld ...)
                    `tmpl))))))

      (define make-pair-clause
        (lambda (alt)
          (with-syntax ([pred? (pair-alt-pred alt)]
                        [raw-body (build-template-wrapper (strip-maybe (alt-syn alt)) alt)])
            #`((pred? ir)
                #,(let ([pretty (alt-pretty alt)])
                    (if pretty
                        #`(if raw?
                              raw-body
                              #,(if (alt-pretty-procedure? alt)
                                    (with-syntax ([(acc ...) (pair-alt-accessors alt)])
                                      #`(#,pretty f (acc ir) ...))
                                    (build-template-wrapper pretty alt)))
                        #'raw-body))))))

      ;; When one nonterminalA alternative is another nonterminalB, we
      ;; expand all the alternatives of nonterminalB with the alternatives
      ;; of nonterminalA However, nonterminalA and nonterminalB cannot
      ;; (both) have an implicit case, by design.
      (partition-syn (ntspec-alts ntspec)
        ([term-alt* terminal-alt?] [nonterm-alt* nonterminal-alt?] [pair-alt* otherwise])
        (partition-syn nonterm-alt*
          ([nonterm-imp-alt* (lambda (alt)
                               (has-implicit-alt?
                                 (nonterminal-alt-ntspec alt)))]
            [nonterm-nonimp-alt* otherwise])
          #`(lambda (ir)
              (cond
                #,@(map make-term-clause term-alt*)
                #,@(map make-pair-clause pair-alt*)
                ;; note: the following two can potentially be combined
                #,@(apply append (map make-nonterm-clause nonterm-nonimp-alt*))
                #,@(apply append (map make-nonterm-clause nonterm-imp-alt*))
                [else (error '#,procname "invalid record" ir)])))))))
