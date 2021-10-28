#lang at-exp racket

(provide modal/c
         mode:once-every
         mode:once-per-category
         mode:exponential-backoff
         modal->)

(require racket/contract
         syntax/parse/define)

;; modal/c : contract? (any/c -> boolean?)
(define (modal/c inner-ctc should-apply-ctc?)
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

;; mode:once-every : natural? -> (any/c -> boolean?)
(define (mode:once-every n)
  (define count (box 0))
  (λ _
    (define current-count (unbox count))
    (cond [(zero? (remainder current-count n))
           ;; (displayln @~a{Checking on call @count / @n})
           (set-box! count 1)
           #t]
          [else
           ;; (displayln @~a{Deciding not to check on call @count / @n})
           (set-box! count (add1 current-count))
           #f])))

;; mode:once-every : (any/c -> any/c) -> (any/c -> boolean?)
(define (mode:once-per-category categorize)
  (define seen-categories (make-hash))
  (λ (v)
    (define category (categorize v))
    (cond [(hash-has-key? seen-categories category)
           #f]
          [else
           (hash-set! seen-categories category #t)
           #f])))

(define (mode:exponential-backoff exponent)
  (define count (box 0))
  (define limit (box 2))
  (λ _
    (define current-count (unbox count))
    (define current-limit (unbox limit))
    (cond [(zero? (remainder current-count current-limit))
           (set-box! limit (expt current-limit exponent))
           (set-box! count 1)
           #t]
          [else
           (set-box! count (add1 current-count))
           #f])))

(begin-for-syntax
  (require syntax/parse/define)
  (define-syntax-class ->range
    #:commit
    #:attributes [(ctc 1)]
    [pattern ({~datum values} ctc ...)]
    [pattern lone-ctc
             #:with [ctc ...] #'[lone-ctc]]))
(define-simple-macro (modal-> mode dom-ctc ... rng:->range)
  (make-modal-> mode (list dom-ctc ...) (list rng.ctc ...)))

;; `any` range not supported
(define (make-modal-> should-apply-ctc? dom-ctcs rng-ctcs)
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
       (chaperone-procedure
        f
        (λ args
          (cond [(should-apply-ctc? args)
                 (define contracted-args
                   (map (λ (v proj) (proj v neg-party))
                        args
                        dom-projs/blame))
                 (apply values
                        (λ results
                          (apply values
                                 (map (λ (v proj) (proj v neg-party))
                                      results
                                      rng-projs/blame)))
                        contracted-args)]
                [else
                 (apply values args)])))))))

(module+ test
  (require ruinit)

  (define/contract (f-normal x)
    (-> number? number?)
    x)
  (define/contract (f-modal-parts x)
    (-> (modal/c number? (mode:once-every 2))
        (modal/c number? (mode:once-every 2)))
    x)
  (define/contract (f-modal-> x)
    (modal-> (mode:once-every 2)
             number? number?)
    x)
  (define/contract (g-modal-> x)
    (modal-> (mode:once-every 2)
             number? string?)
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
    (test-equal? (g-modal-> "hi") "hi"))

  (define (blame-responsible blame)
    (blame-positive blame))
  (define ((make-test-blamed-equal? check-party) an-exn)
    (unless (exn:fail:contract:blame? an-exn)
      (test-fail "exn ~s is not a blame error" an-exn))
    (define blamed (blame-responsible (exn:fail:contract:blame-object an-exn)))
    (extend-test-message (check-party blamed)
                         @~a{blamed party: @~s[blamed]}))
  (define-test-syntax (test-blamed e blamed-party-pattern)
    #'(with-handlers ([exn:fail? (make-test-blamed-equal?
                                  (match-lambda [blamed-party-pattern #t]
                                                [_ #f]))])
        e
        (fail "No blame")))

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
