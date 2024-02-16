#lang racket

(require modalc)

(define (modal-vector/c should-apply-ctc? . inner-ctc)
  (define vector-contract (apply vector/c inner-ctc))
  (define inner-ctc-proj
    (contract-late-neg-projection vector-contract))
  (make-contract
   #:name `(modal-vector/c ,(contract-name vector-contract))
   #:late-neg-projection
   (λ (blame)
     (define inner-ctc-proj/blame (inner-ctc-proj blame))
     (λ (val neg-party)
       (impersonate-vector val
                           (λ (vec index ret)
                             (if (should-apply-ctc? val)
                                 (vector-ref (inner-ctc-proj/blame val neg-party) index)
                                 ret))
                           (λ (vec index ret)
                             (if (should-apply-ctc? val)
                                 (begin (inner-ctc-proj/blame val neg-party)
                                        ret)
                                 ret)))))))

(define/contract vec
  (modal-vector/c (mode:first 5) integer? integer? (and/c integer? positive?))
  (vector 1 2 1))

(define (f v)
  (println "start")
  (println (vector-ref v 0))
  (println (vector-ref v 1))
  (println (vector-ref v 2))
  (vector-set! v 2 -5)
  (println "vector-set")
  (println (vector-ref v 0))
  (println (vector-ref v 1))
  (println (vector-ref v 2))
  (println v)
  (println "end")
  (if (vector? v)
      (println "is a vector")
      (println "wrong")))
(f vec)
