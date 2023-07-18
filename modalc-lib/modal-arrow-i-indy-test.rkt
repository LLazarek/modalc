#lang racket

(require ruinit
         "modal.rkt"
         "modes.rkt"
         "test-common.rkt"
         "modal-arrow-i.rkt")

(module basics racket
  (require ruinit
           "modal.rkt"
           "modes.rkt"
           "test-common.rkt"
           "modal-arrow-i.rkt")
  (test-begin
    #:name modal->i-emulates-->i
    (ignore (define/contract (f-n-any x)
              (modal->i mode:always
                        ([x number?])
                        any)
              x)
            (define/contract (f-n-str x)
              (modal->i mode:always ([x number?]) [result string?])
              x)
            (define/contract (f-n-= x)
              (modal->i mode:always ([x number?]) [result {x} (=/c x)])
              x)
            (define/contract (f-n->-= x y)
              (modal->i mode:always ([x number?] [y {x} (>/c x)]) [result {y} (=/c y)])
              x)
            (define/contract (f-n->-=/kw x #:y y)
              (modal->i mode:always
                        ([x number?]
                         #:y [y {x} (>/c x)])
                        [result {y} (=/c y)])
              x))
    (test-equal? (f-n-any 5) 5)
    (test-blamed (f-n-any 'hi)
                 (list (? path-string?) 'basics))
    (test-blamed (f-n-str 5)
                 '(function f-n-str))
    (test-equal? (f-n-= 5) 5)
    (test-blamed (f-n->-= 5 6)
                 '(function f-n->-=))
    (test-blamed (f-n->-= 5 3)
                 (list (? path-string?) 'basics))
    (test-blamed (f-n->-=/kw 5 #:y 3)
                 (list (? path-string?) 'basics)))

  (test-begin
    #:name modal->i-modes
    (ignore (define/contract (f-modal-> x)
              (modal->i (mode:once-every 2)
                        ([x number?])
                        [result {x} (and/c number?
                                           (=/c x))])
              x)
            (define/contract (g-modal-> x)
              (modal->i (mode:once-every 2)
                        ([x number?])
                        [result {x} (and/c number?
                                           (=/c x))])
              (add1 x)))
    (test-equal? (f-modal-> 2) 2)
    (test-equal? (f-modal-> 2) 2)
    (test-exn exn:fail:contract:blame?
              (f-modal-> "hi"))
    (test-equal? (f-modal-> "hi") "hi")
    (test-exn exn:fail:contract:blame?
              (f-modal-> "hi"))
    (test-equal? (f-modal-> "hi") "hi")

    (test-exn exn:fail:contract:blame?
              (g-modal-> 2))
    (test-equal? (g-modal-> 2) 3))

  (test-begin
    #:name modal->i-post
    (ignore (define/contract (f-modal-> x)
              (modal->i (mode:once-every 2)
                        ([x number?])
                        [result {x} (and/c number?
                                           (=/c x))]
                        #:post {x result} (> result x))
              x))
    (test-exn exn:fail:contract:blame?
              (f-modal-> 2))
    (test-equal? (f-modal-> 2) 2)))
(require 'basics)

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

(define/contract (def/c/baseline-blame-ctc-post g x)
  (->i ([g (-> number? number?)]
        [x {g} (=/c (g 5))])
       [result any/c]
       #:post {g} (g "not a number"))
  x)
(define/contract (def/c/f-indy-blame-ctc-post g x)
  (modal->i mode:always ([g (-> number? number?)]
                         [x {g} (=/c (g 5))])
            [result any/c]
            #:post {g} (g "not a number"))
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
               (? path-string?))

  (test-blamed (def/c/baseline-blame-ctc-post (λ (x) x) 5)
               (? path-string?))
  (test-blamed (def/c/f-indy-blame-ctc-post (λ (x) x) 5)
               (? path-string?)))

