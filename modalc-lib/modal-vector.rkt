#lang racket

(require modalc
         syntax/parse/define)

(define (modal-vector/c should-apply-ctc? . inner-ctc)
  (define inner-ctc-proj
    (map contract-late-neg-projection inner-ctc))
  (make-contract
   #:name `(modal-vector/c ,(map contract-name inner-ctc-proj))
   #:late-neg-projection
   (λ (blame)
     (define inner-ctc-proj/blame (map (λ (p) (p (blame-swap blame))) inner-ctc-proj))
     (λ (val neg-party)
       (impersonate-vector val
                           (λ (vec index value)
                             (cond [(should-apply-ctc? (list index value))
                                    (printf "ref call: ~s\n" (list index value))
                                    (for/list ([arg (in-vector vec)]
                                               [proj (in-list inner-ctc-proj/blame)])
                                      (proj arg neg-party))
                                    value]
                                   [else (printf "no ref ~s\n" (list index value))
                                         value]))
                           (λ (vec index value)
                             (cond [(should-apply-ctc? (list index value))
                                    (printf "set call: ~s\n" (list index value))
                                    (for/list ([arg (in-vector vec)]
                                               [proj (in-list inner-ctc-proj/blame)])
                                      (proj arg neg-party))
                                    (vector-set! vec index value)
                                    value]
                                   [else (printf "no set ~s\n" (list index value))
                                         value])))))))

(define-simple-macro (modal-vector/c* mode
                                 {~and inner-ctc {~not _:keyword}} ...
                                 {~seq kw:keyword ctc} ...)
  (make-modal-vector/c* mode
                   (list inner-ctc ...)
                   (list (list 'kw ctc) ...)))

(define (make-modal-vector/c* should-apply-ctc? inner-ctc kwds)
  (define ref-ctc? should-apply-ctc?)
  (define set-ctc? should-apply-ctc?)
  (for ([kw kwds])
    (cond [(equal? '#:ref (car kw))
           (set! ref-ctc? (car (cdr kw)))]
          [(equal? '#:set (car kw))
           (set! set-ctc? (car (cdr kw)))]))
  (define inner-ctc-proj
    (map contract-late-neg-projection inner-ctc))
  (make-contract
   #:name `(modal-vector/c ,(map contract-name inner-ctc-proj))
   #:late-neg-projection
   (λ (blame)
     (define inner-ctc-proj/blame (map (λ (p) (p (blame-swap blame))) inner-ctc-proj))
     (λ (val neg-party)
       (impersonate-vector val
                           (λ (vec index value)
                             (cond [(ref-ctc? (list index value))
                                    (printf "ref call: ~s\n" (list index value))
                                    (for/list ([arg (in-vector vec)]
                                               [proj (in-list inner-ctc-proj/blame)])
                                      (proj arg neg-party))
                                    value]
                                   [else (printf "no ref ~s\n" (list index value))
                                         value]))
                           (λ (vec index value)
                             (cond [(set-ctc? (list index value))
                                    (printf "set call: ~s\n" (list index value))
                                    (for/list ([arg (in-vector vec)]
                                               [proj (in-list inner-ctc-proj/blame)])
                                      (proj arg neg-party))
                                    (vector-set! vec index value)
                                    value]
                                   [else (printf "no set ~s\n" (list index value))
                                         value])))))))

(module+ test
  (require ruinit
           "test-common.rkt")
  
  
  (define/contract simple-vec
    (modal-vector/c mode:always integer? integer?)
    (vector 1 2))
  (define/contract every-other
    (modal-vector/c* (mode:once-every 2) integer? integer? (and/c positive? integer?) #:ref mode:always #:set (mode:first 2))
    (vector 4 5 6))

  #;(test-begin
    #:name simple-test
    (test-equal? simple-vec (vector 1 2))
    (test-equal? (vector-ref simple-vec 1) 2)
    (vector-set! simple-vec 1 0)
    (test-equal? (vector-ref simple-vec 1) 0)
    (vector-set! simple-vec 0 'bad)
    (test-exn exn:fail:contract:blame? (vector-ref simple-vec 0))
    (test-exn exn:fail:contract:blame? (vector-set! simple-vec 1 #f))
    (test-exn exn:fail:contract:blame? (vector-ref simple-vec 1))
    (test-exn exn:fail:contract:blame? (vector-set! simple-vec 0 -10))
    (test-exn exn:fail:contract:blame? (vector-set! simple-vec 1 15)))
  (test-begin
   #:name every-other-test
   #;(test-equal? every-other (vector 4 5 6))
   (println "next")
   (test-equal? (vector-ref every-other 0) 4)
   (test-equal? (vector-ref every-other 1) 5)
   (vector-set! every-other 1 -2)
   (vector-set! every-other 2 2)
   (vector-set! every-other 0 12)
   ;(test-equal? (vector-ref every-other 2) 6)
   ;(test-equal? (vector-ref every-other 1) -2)
   ;(vector-set! every-other 2 0)
   #;(test-equal? every-other (vector 4 -2 6))
   #;(test-exn exn:fail:contract:blame? (vector-ref every-other 2))))

