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
   #:name `(modal/c ,(contract-name inner-ctc))
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

(define (modal-arrow-projection should-apply-ctc?
                                mandatory-positional-dom-ctcs
                                mandatory-kw-dom-ctc-pairs
                                optional-positional-dom-ctcs
                                optional-kw-dom-ctc-pairs
                                result-ctcs)
  (define mandatory-positional-dom-projs (map contract-late-neg-projection mandatory-positional-dom-ctcs))
  (define mandatory-kw-dom-projs (map contract-late-neg-projection (map second mandatory-kw-dom-ctc-pairs)))
  (define optional-positional-dom-projs (map contract-late-neg-projection optional-positional-dom-ctcs))
  (define optional-kw-dom-projs (map contract-late-neg-projection (map second optional-kw-dom-ctc-pairs)))
  (define rng-projs (map contract-late-neg-projection result-ctcs))
  (define chaperone-or-impersonate-procedure
    (if (andmap chaperone-contract? (append mandatory-positional-dom-ctcs
                                            (map second mandatory-kw-dom-ctc-pairs)
                                            optional-positional-dom-ctcs
                                            (map second optional-kw-dom-ctc-pairs)
                                            result-ctcs))
        chaperone-procedure
        impersonate-procedure))
  (λ (blame)
    (define mandatory-positional-dom-projs/blame (map (λ (p) (p (blame-swap blame))) mandatory-positional-dom-projs))
    (define mandatory-kw-dom-projs/blame (map (λ (p) (p (blame-swap blame))) mandatory-kw-dom-projs))
    (define optional-positional-dom-projs/blame (map (λ (p) (p (blame-swap blame))) optional-positional-dom-projs))
    (define optional-kw-dom-projs/blame (map (λ (p) (p (blame-swap blame))) optional-kw-dom-projs))
    (define kw-dom-proj/blame-map
      (for/hash ([kw (in-list (append (map first mandatory-kw-dom-ctc-pairs)
                                      (map first optional-kw-dom-ctc-pairs)))]
                 [proj/blame (in-list (append mandatory-kw-dom-projs/blame
                                              optional-kw-dom-projs/blame))])
        (values kw proj/blame)))
    (define rng-projs/blame (map (λ (p) (p blame)) rng-projs))
    (λ (f neg-party)
      (chaperone-or-impersonate-procedure
       f
       (make-keyword-procedure
        (λ (kws kw-args . args)
          (cond [(should-apply-ctc? (list kws kw-args args))
                 (define contracted-args
                   (for/list ([v (in-list args)]
                              [proj (in-list (append mandatory-positional-dom-projs/blame
                                                     optional-positional-dom-projs/blame))])
                     (proj v neg-party)))
                 (define contracted-kw-args
                   (for/list ([kw (in-list kws)]
                              [kw-arg (in-list kw-args)])
                     (define proj (hash-ref kw-dom-proj/blame-map
                                            kw))
                     (proj kw-arg neg-party)))
                 (define chaperone-arg-results
                   (if (empty? kw-args)
                       contracted-args
                       (append (list contracted-kw-args) contracted-args)))
                 (if (empty? rng-projs) ;; i.e. `any` range
                     (apply values
                            chaperone-arg-results)
                     (apply values
                            (λ results
                              (apply values
                                     (map (λ (v proj) (proj v neg-party))
                                          results
                                          rng-projs/blame)))
                            chaperone-arg-results))]
                [else
                 (apply values
                        (if (empty? kw-args)
                            args
                            (append (list kw-args) args)))])))))))

;; modal-> : mode/c contract? ... (or/c contract? (values contract? ...))
;; To simplify parsing, requires that kws come after all positional args.
(define-simple-macro (modal-> mode
                              {~and dom-ctc {~not _:keyword}} ...
                              {~seq kw:keyword dom-kw-ctc} ...
                              rng:->range)
  (make-modal-> mode
                (list dom-ctc ...)
                (list (list 'kw dom-kw-ctc) ...)
                (list rng.ctc ...)))

(define (make-modal-> should-apply-ctc? positional-dom-ctcs kw-dom-ctc-pairs rng-ctcs)
  (make-contract
   #:name (list* 'modal->
                 (append (map contract-name positional-dom-ctcs)
                         (list (list* 'values (map contract-name rng-ctcs)))))
   #:late-neg-projection
   (modal-arrow-projection should-apply-ctc?
                           positional-dom-ctcs
                           kw-dom-ctc-pairs
                           empty
                           empty
                           rng-ctcs)))

(define-simple-macro (modal->* mode
                               ({~and mandatory-dom-ctc {~not _:keyword}}
                                ...
                                {~seq mandatory-kw:keyword mandatory-dom-kw-ctc}
                                ...)
                               ({~and optional-dom-ctc {~not _:keyword}}
                                ...
                                {~seq optional-kw:keyword optional-dom-kw-ctc}
                                ...)
                               rng:->range)
  (make-modal->* mode
                 (list mandatory-dom-ctc ...)
                 (list (list 'mandatory-kw mandatory-dom-kw-ctc) ...)
                 (list optional-dom-ctc ...)
                 (list (list 'optional-kw optional-dom-kw-ctc) ...)
                 (list rng.ctc ...)))

(define (make-modal->* should-apply-ctc?
                       dom-ctcs
                       dom-kw-ctc-pairs
                       optional-dom-ctcs
                       optional-dom-kw-ctc-pairs
                       rng-ctcs)
  (make-contract
   #:name (list* 'modal->*
                 (append (map contract-name dom-ctcs)
                         (list (list* 'values (map contract-name rng-ctcs)))))
   #:late-neg-projection
   (modal-arrow-projection should-apply-ctc?
                           dom-ctcs
                           dom-kw-ctc-pairs
                           optional-dom-ctcs
                           optional-dom-kw-ctc-pairs
                           rng-ctcs)))

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
  (define/contract (g-modal->/kw x #:y y)
    (modal-> (mode:once-every 2)
             number?
             #:y string?
             string?)
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
  (define/contract (a->* x [y 42])
    (modal->* (mode:once-every 2)
              {number?}
              {number?}
              string?)
    x)
  (define/contract (a->*/kw x [y 42] #:z [z 50])
    (modal->* (mode:once-every 2)
              {number?}
              {number?
               #:z number?}
              string?)
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
    (test-exn exn:fail:contract:blame?
              (g-modal->/kw 42 #:y 42))
    (test-equal? (g-modal->/kw "hi" #:y 42) "hi")

    (test-no-exn (m-modal->any 5))
    (test-exn exn:fail:contract:blame?
              (m-modal->any "not a number"))
    (parameterize ([check-ctcs? #f])
      (test-no-exn (m-modal->any "not a number")))

    (test-exn exn:fail:contract:blame?
              (p-check-arg-once "not a number"))
    (test-no-exn (p-check-arg-once "not a number"))
    (test-no-exn (p-check-arg-once "not a number"))
    (test-exn exn:fail:contract:blame?
              (a->* 1 "not a number"))
    (test-no-exn (a->* 1 "not a number"))
    (test-exn exn:fail:contract:blame?
              (a->*/kw 1 2 #:z "not a number"))
    (test-no-exn (a->*/kw 1 2 #:z "not a number"))
    (test-exn exn:fail:contract:blame? ;; but blaming a->*
              (a->* 1))
    (test-equal? (a->* 1) 1)
    (test-exn exn:fail:contract:blame? ;; but blaming a->*/kw
              (a->*/kw 1 2))
    (test-equal? (a->*/kw 1) 1))

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
