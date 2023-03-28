#lang at-exp racket

(provide mode:always
         mode:never
         mode:first
         mode:once-every
         mode:once-per-category
         mode:exponential-backoff
         mode:parameter)

;; mode/c : (any/c -> boolean?)
;;   where the argument is the value to potentially be contracted

;; mode:always , mode:never : mode/c
(define mode:always (const #t))
(define mode:never (const #f))

;; mode:first : natural? -> mode/c
(define (mode:first n)
  (define remaining-checks (box n))
  (λ _
    (define remaining (unbox remaining-checks))
    (cond [(zero? remaining)
           #f]
          [else
           (set-box! remaining-checks (sub1 remaining))
           #t])))

;; mode:once-every : natural? -> mode/c
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

;; mode:once-every : (any/c -> any/c) -> mode/c
(define (mode:once-per-category categorize)
  (define seen-categories (make-hash))
  (λ (v)
    (define category (categorize v))
    (cond [(hash-has-key? seen-categories category)
           #f]
          [else
           (hash-set! seen-categories category #t)
           #f])))

;; mode:exponential-backoff : natural? -> mode/c
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

;; mode:parameter : (parameter/c any/c) -> mode/c
(define (mode:parameter p)
  (λ _ (not (false? (p)))))

