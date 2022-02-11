#lang at-exp racket

(provide modal/c
         modal->
         modal->i
         (all-from-out "modes.rkt"))

;; todo: new mode idea: decreasing ctc strength over time

(require racket/contract
         syntax/parse/define
         "modes.rkt"
         "modal-arrow-i.rkt")

;; mode/c : (any/c -> boolean?)
;;   where the argument is the value to potentially be contracted

;; modal/c : mode/c contract?
(define (modal/c should-apply-ctc? inner-ctc)
  (define inner-ctc-proj
    (contract-late-neg-projection inner-ctc))
  (make-contract
   #:name 'modal/c
   #:late-neg-projection
   (λ (blame)
     (define inner-ctc-proj/blame (inner-ctc-proj blame))
     (λ (val neg-party)
       (if (should-apply-ctc? val)
           (inner-ctc-proj/blame val neg-party)
           val)))))

(begin-for-syntax
  (define-syntax-class ->range
    #:commit
    #:attributes [(ctc 1)]
    [pattern ({~datum values} ctc ...)]
    [pattern {~datum any}
             #:with [ctc ...] #'[]]
    [pattern lone-ctc
             #:with [ctc ...] #'[lone-ctc]]))

;; modal-> : mode/c contract? ... (or/c contract? (values contract? ...))
(define-simple-macro (modal-> mode dom-ctc ... rng:->range)
  (make-modal-> mode (list dom-ctc ...) (list rng.ctc ...)))

(define (make-modal-> should-apply-ctc? dom-ctcs rng-ctcs)
  (define chaperone-or-impersonate-procedure
    (if (andmap chaperone-contract? (append dom-ctcs rng-ctcs))
        chaperone-procedure
        impersonate-procedure))
  (define dom-projs (map contract-late-neg-projection dom-ctcs))
  (define rng-projs (map contract-late-neg-projection rng-ctcs))
  (make-contract
   #:name (list* 'modal->
                 (append (map contract-name dom-ctcs)
                         (list (list* 'values (map contract-name rng-ctcs)))))
   #:late-neg-projection
   (λ (blame)
     (define dom-projs/blame (map (λ (p) (p (blame-swap blame))) dom-projs))
     (define rng-projs/blame (map (λ (p) (p blame)) rng-projs))
     (λ (f neg-party)
       (chaperone-or-impersonate-procedure
        f
        (λ args
          (cond [(should-apply-ctc? args)
                 (define contracted-args
                   (map (λ (v proj) (proj v neg-party))
                        args
                        dom-projs/blame))
                 (if (empty? rng-projs) ;; i.e. `any` range
                     (apply values
                            contracted-args)
                     (apply values
                            (λ results
                              (apply values
                                     (map (λ (v proj) (proj v neg-party))
                                          results
                                          rng-projs/blame)))
                            contracted-args))]
                [else
                 (apply values args)])))))))

(module+ test
  (require ruinit
           "test-common.rkt")

  (define/contract (f-normal x)
    (-> number? number?)
    x)
  (define/contract (f-modal-parts x)
    (-> (modal/c (mode:once-every 2) number?)
        (modal/c (mode:once-every 2) number?))
    x)
  (define/contract (f-modal-> x)
    (modal-> (mode:once-every 2)
             number? number?)
    x)
  (define/contract (g-modal-> x)
    (modal-> (mode:once-every 2)
             number? string?)
    x)
  (define/contract (h-exponential-backoff x)
    (modal-> (mode:exponential-backoff 2)
             number? number?)
    x)
  (define check-ctcs? (make-parameter #t))
  (define/contract (m-modal->any x)
    (modal-> (mode:parameter check-ctcs?)
             number? any)
    x)
  (define/contract (p-check-arg-once x)
    (-> (modal/c (mode:first 1) number?)
        any)
    x)

  (test-begin
    #:name checks

    (test-equal? (f-modal-parts 2) 2)
    (test-equal? (f-modal-parts 2) 2)

    ; blame caller (dom: check, rng: check) -> (dom: skip, rng: check)
    (test-exn exn:fail:contract:blame?
              (f-modal-parts "hi"))
    ; blame f-modal-parts (dom: skip, rng: check) -> (dom: check, rng: skip)
    (test-exn exn:fail:contract:blame?
              (f-modal-parts "hi"))
    ; blame caller (dom: check, rng: skip) -> (dom: skip, rng: skip)
    (test-exn exn:fail:contract:blame?
              (f-modal-parts "hi"))
    ; no check! (dom: skip, rng: skip) -> (dom: check, rng: check)
    (test-equal? (f-modal-parts "hi") "hi")

    (test-equal? (f-modal-> 2) 2)
    (test-equal? (f-modal-> 2) 2)
    (test-exn exn:fail:contract:blame?
              (f-modal-> "hi"))
    (test-equal? (f-modal-> "hi") "hi")

    (test-exn exn:fail:contract:blame?
              (g-modal-> 2))
    (test-equal? (g-modal-> 2) 2)
    (test-exn exn:fail:contract:blame?
              (g-modal-> "hi"))
    (test-equal? (g-modal-> "hi") "hi")

    (test-no-exn (m-modal->any 5))
    (test-exn exn:fail:contract:blame?
              (m-modal->any "not a number"))
    (parameterize ([check-ctcs? #f])
      (test-no-exn (m-modal->any "not a number")))

    (test-exn exn:fail:contract:blame?
              (p-check-arg-once "not a number"))
    (test-no-exn (p-check-arg-once "not a number"))
    (test-no-exn (p-check-arg-once "not a number")))

  (test-begin
    #:name exponential-backoff
    (test-exn exn:fail:contract:blame?
              (h-exponential-backoff "hi"))
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-exn exn:fail:contract:blame?
              (h-exponential-backoff "hi"))
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-equal? (h-exponential-backoff "hi") "hi")
    (test-exn exn:fail:contract:blame?
              (h-exponential-backoff "hi")))

  (test-begin
    #:name blame

    ;; modal parts make blame rotate as above comments
    (test-blamed (f-modal-parts "hi")
                 (list (? path-string?) 'test))
    (test-blamed (f-modal-parts "hi")
                 '(function f-modal-parts))
    (test-blamed (f-modal-parts "hi")
                 (list (? path-string?) 'test))
    (ignore (f-modal-parts "hi"))

    ;; `modal->` always blames according to the part of the ctc violated
    (test-blamed (f-modal-> "hi")
                 (list (? path-string?) 'test))
    (ignore (f-modal-> "hi"))
    (test-blamed (f-modal-> "hi")
                 (list (? path-string?) 'test))

    (test-blamed (g-modal-> "hi")
                 (list (? path-string?) 'test))
    (ignore (g-modal-> "hi"))
    (test-blamed (g-modal-> 2)
                 '(function g-modal->))))
