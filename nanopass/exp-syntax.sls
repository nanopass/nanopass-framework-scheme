(library (nanopass exp-syntax)
  (export
    define-language-exp
    inspect-language lookup-language
    Llanguage unparse-Llanguage
    Lannotated unparse-Lannotated)
  (import (rnrs) (nanopass) (nanopass experimental) (only (chezscheme) make-compile-time-value trace-define-syntax))

  (define-syntax define-language-exp
    (lambda (x)
      (lambda (rho)
        (let* ([lang (parse-np-source x 'define-language-exp)]
               [lang (handle-language-extension lang 'define-language-exp rho)]
               [lang (check-and-finish-language lang)]
               [lang-annotated (annotate-language lang)])
          (nanopass-case (Llanguage Defn) lang
            [(define-language ,id ,cl* ...)
             #`(define-syntax #,id
                 (make-compile-time-value
                   (make-language-information '#,lang '#,lang-annotated)))])))))

  (define-syntax inspect-language
    (lambda (x)
      (lambda (rho)
        (syntax-case x ()
          [(_ name)
           (let ([lang (rho #'name)])
             (if lang
                 (let ([l (language-information-language lang)]
                       [a (language-information-annotated-language lang)])
                   #`(list
                       '#,l
                       '#,(datum->syntax #'* (unparse-Llanguage l))
                       '#,a
                       '#,(datum->syntax #'* (unparse-Lannotated a))))
                 (syntax-violation 'inspect-language "no language found" #'name)))]))))

  )
