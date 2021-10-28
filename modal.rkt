#lang racket

(provide modal/c
         mode:once-every
         mode:once-per-category)

(require racket/contract
         syntax/parse/define)

(define (contract/late-neg ctc v blame neg-party)
  ;; lltodo: this is breaking some kind of name inference
  (contract ctc
            v
            (if (blame-swapped? blame)
                neg-party
                (blame-positive blame))
            (if (blame-swapped? blame)
                (blame-positive blame)
                neg-party)))

;; modal/c : contract? (any/c -> boolean?)
(define (modal/c inner-ctc should-apply-ctc?)
  (make-contract
   #:name 'modal/c
   #:late-neg-projection
   (λ (blame)
     (λ (val neg-party)
       (if (should-apply-ctc? val)
           (contract/late-neg inner-ctc
                              val
                              blame
                              neg-party)
           val)))))

;; mode:once-every : natural? -> (any/c -> boolean?)
(define (mode:once-every n)
  (define count (box 0))
  (λ _
    (define current-count (unbox count))
    (cond [(zero? (remainder current-count n))
           (set-box! count 1)
           #t]
          [else
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

(define-simple-macro (modal-> mode dom-ctc ... rng-ctc)
  (make-modal-> mode (-> dom-ctc ... rng-ctc)))

(define (make-modal-> should-apply-ctc? arrow-ctc)
  (make-contract
   #:name 'modal->
   #:late-neg-projection
   (λ (blame)
     (λ (f neg-party)
       #;(chaperone-procedure
        f
        (λ args
          (cond [(should-apply-ctc? args)
                 (define args+ctcs)]
                [else
                 (apply values args)])))
       ;; lltodo: this doesn't quite work seemingly to fix the name, e.g. compare g and f below
       (define f+c (procedure-rename
                    (contract arrow-ctc f (blame-positive blame) neg-party)
                    (object-name f)))
       (λ args
          (cond [(should-apply-ctc? args)
                 (apply f+c args)]
                [else
                 (apply f args)]))))))

(module+ testmod
  (define/contract (f-normal x)
    (-> number? number?)
    x)
  (define/contract (f x)
    (-> (modal/c number? (mode:once-every 2))
        (modal/c number? (mode:once-every 2)))
    x)
  (define/contract (g x)
    (-> integer? integer?)
    x))
