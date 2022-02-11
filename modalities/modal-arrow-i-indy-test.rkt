#lang racket

(require ruinit
         "modal.rkt"
         "test-common.rkt")

(module indy-test-submod racket
  (require "modal.rkt")
  (provide (contract-out [rename f-indy f-indy-blame-ctc (modal->i mode:always ([g (-> number? number?)]
                                                                  [x {g} (=/c (g "not a number"))])
                                                     [result any/c])]
                         [rename f-indy f-indy-blame-self (modal->i mode:always ([g (-> number? number?)]
                                                                   [x {g} (=/c (g 5))])
                                                                    [result string?])]

                         [rename f-indy baseline-blame-ctc (->i ([g (-> number? number?)]
                                                                 [x {g} (=/c (g "not a number"))])
                                                                [result any/c])]
                         [rename f-indy baseline-blame-self (->i ([g (-> number? number?)]
                                                                  [x {g} (=/c (g 5))])
                                                                 [result string?])]
                         ))
  (define (f-indy g x) x))

(require 'indy-test-submod)


(define/contract (def/c/baseline-blame-ctc g x)
  (->i ([g (-> number? number?)]
        [x {g} (=/c (g "not a number"))])
       [result any/c])
  x)
(define/contract (def/c/baseline-blame-self g x)
  (->i ([g (-> number? number?)]
        [x {g} (=/c (g 5))])
       [result string?])
  x)

(define/contract (def/c/f-indy-blame-ctc g x)
  (modal->i mode:always ([g (-> number? number?)]
                         [x {g} (=/c (g "not a number"))])
            [result any/c])
  x)
(define/contract (def/c/f-indy-blame-self g x)
  (modal->i mode:always ([g (-> number? number?)]
                         [x {g} (=/c (g 5))])
            [result string?])
  x)

(define/contract (def/c/baseline-blame-ctc-ret g x)
  (->i ([g (-> number? number?)]
        [x {g} (=/c (g 5))])
       [result {g} (g "not a number")])
  x)
(define/contract (def/c/f-indy-blame-ctc-ret g x)
  (modal->i mode:always ([g (-> number? number?)]
                         [x {g} (=/c (g 5))])
            [result {g} (g "not a number")])
  x)

(test-begin
  #:name modal->i-indy-blame
  (test-blamed (baseline-blame-ctc (λ (x) x) 5)
               (list (? path-string?) 'indy-test-submod))
  (test-blamed (f-indy-blame-ctc (λ (x) x) 5)
               (list (? path-string?) 'indy-test-submod))

  (test-blamed (baseline-blame-self (λ (x) x) 5)
               (list (? path-string?) 'indy-test-submod))
  (test-blamed (f-indy-blame-self (λ (x) x) 5)
               (list (? path-string?) 'indy-test-submod))


  (test-blamed (def/c/baseline-blame-ctc (λ (x) x) 5)
               (? path-string?))
  (test-blamed (def/c/f-indy-blame-ctc (λ (x) x) 5)
               (? path-string?))

  (test-blamed (def/c/baseline-blame-self (λ (x) x) 5)
               '(function def/c/baseline-blame-self))
  (test-blamed (def/c/f-indy-blame-self (λ (x) x) 5)
               '(function def/c/f-indy-blame-self))

  (test-blamed (def/c/baseline-blame-ctc-ret (λ (x) x) 5)
               (? path-string?))
  (test-blamed (def/c/f-indy-blame-ctc-ret (λ (x) x) 5)
               (? path-string?)))

