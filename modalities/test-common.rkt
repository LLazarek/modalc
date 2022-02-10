#lang at-exp racket

(provide test-no-exn
         test-blamed)

(require ruinit)

(define-test-syntax (test-no-exn e)
  #'(with-handlers ([exn? (λ (exn) (fail @~a{raised exception: @~e[exn]}))])
      e
      #t))

(define (blame-responsible blame)
  (blame-positive blame))
(define ((make-test-blamed-equal? check-party) an-exn)
  (cond [(exn:fail:contract:blame? an-exn)
         (define blamed (blame-responsible (exn:fail:contract:blame-object an-exn)))
         (extend-test-message (check-party blamed)
                              @~a{blamed party: @~s[blamed]})]
        [else
         (test-fail "exn ~s is not a blame error" an-exn)]))
(define-test-syntax (test-blamed e blamed-party-pattern)
  #'(with-handlers ([exn:fail? (make-test-blamed-equal?
                                (match-lambda [blamed-party-pattern #t]
                                              [_ #f]))])
      e
      (fail "No blame")))
