#lang at-exp racket

(provide modal->i)

(require racket/contract
         syntax/parse/define)

(begin-for-syntax
  (require racket
           syntax/parse)
  (struct static-un/dep (name stx deps))
  (define (static-undep name stx)
    (static-un/dep name stx empty))
  (define (static-dep name deps stx)
    (static-un/dep name stx deps))
  (define-syntax-class dep-spec
    #:commit
    #:attributes [dep/undep-ctc]
    [pattern [name {~optional ()} ctc]
             #:attr dep/undep-ctc (static-undep #'name #'ctc)]
    [pattern [name (dep-name:id ...) ctc]
             #:attr dep/undep-ctc (static-dep #'name
                                              (attribute dep-name)
                                              #'ctc)])

  ;; (listof static-un/dep?) -> (hash/c index? (listof index?))
  (define (static-deps->graph-hash deps)
    (define name-indices
      (for/hash ([dep (in-list deps)]
                 [i (in-naturals)])
        (values (syntax->datum (static-un/dep-name dep)) i)))
    (define (index-of-dep id)
      (hash-ref name-indices (syntax->datum id) #f))
    (for/hash ([dep (in-list deps)]
               [i (in-naturals)])
      (values i (filter-map index-of-dep (static-un/dep-deps dep))))))

(define (toposort unnorm-graph-dict)
  (define graph-dict
    ;; unnorm-graph-dict may contain vertices that don't have keys; just ignore them
    (let ([keys (dict-keys unnorm-graph-dict)])
      (for/hash ([{key dependencies} (in-dict unnorm-graph-dict)])
        (values key (set-intersect dependencies keys)))))
  (define ((all-dependencies-in? some-vertices) a-vertex)
    (subset? (hash-ref graph-dict a-vertex) some-vertices))

  (let loop ([order-so-far empty]
             [remaining (dict-keys graph-dict)])
    (cond [(empty? remaining)
           order-so-far]
          [else
           (define feasible-vertices
             (filter (all-dependencies-in? order-so-far)
                     remaining))
           (when (empty? feasible-vertices)
             (error 'toposort
                    "Cycle found in ~e"
                    graph-dict))
           (loop (append order-so-far feasible-vertices)
                 (set-subtract remaining feasible-vertices))])))

;; (listof any/c)
;; (listof (any/c ... -> contract?))
;; (hash/c index? (listof index?))
;; (any/c contract? -> any/c)
;; ->
;; (listof any/c)
;;
;; Apply dependent contracts produced by `contract-makers` to `plain-values` using `apply-contract`.
;; `dependencies` is the dependency graph between the contracts/values, in terms of their indices.
;; Each `contract-maker` expects the contracted values that the contract it creates depends on,
;; and returns that contract.
(define (dep-apply plain-values
                   contract-makers
                   dependencies
                   apply-contract)
  (define (make-indexer l) (let ([v (list->vector l)])
                             (λ (i) (vector-ref v i))))

  (define plain-value (make-indexer plain-values))
  (define contract-maker (make-indexer contract-makers))

  (define sorted-indices (toposort dependencies))
  (for/fold ([contracted-values (make-vector (length plain-values))]
             #:result (vector->list contracted-values))
            ([index (in-list sorted-indices)])
    (define plain-v (plain-value index))
    (define ctc-maker (contract-maker index))
    (define ctced-deps (for/list ([dep-i (in-list (hash-ref dependencies index))])
                         (vector-ref contracted-values dep-i)))
    (define ctc (apply ctc-maker ctced-deps))
    (define v+ctc (apply-contract plain-v ctc))
    (vector-set! contracted-values index v+ctc)
    contracted-values))

;; (listof ((listof any/c) -> contract?))
;; (hash/c index? (listof index?))
;; ->
;; (blame? neg-party? -> ((listof any/c) -> (listof any/c)))
(define (make-arg-contracter contract-makers
                             dependencies
                             [swap-blame? #t])
  (λ (blame neg-party)
    (λ (plain-args)
      (dep-apply plain-args
                 contract-makers
                 dependencies
                 (λ (v ctc)
                   (define proj (contract-late-neg-projection ctc))
                   (define proj/blame (proj (if swap-blame? (blame-swap blame) blame)))
                   (proj/blame v neg-party))))))

;; same contract as -arg-
(define (make-result-contracter make-contract-makers
                                dependencies)
  (λ (contract-maker-maker-arguments)
    (define contract-makers (apply make-contract-makers contract-maker-maker-arguments))
    (make-arg-contracter contract-makers
                         dependencies
                         #f)))

;; lltodo the blame is wrong here, this is picky
(define-simple-macro (modal->i mode
                               (mandatory-arg:dep-spec ...)
                               ;; {~optional (optional-arg:dep-spec ...)}
                               {~or single-result:dep-spec
                                    ({~datum values} results:dep-spec ...)
                                    {~and any-kw {~datum any}}})
  #:with unquoted-name this-syntax
  #:do [(define (->syntax v) (datum->syntax this-syntax v) #;v)]
  #:do [(define arg-names (map static-un/dep-name (attribute mandatory-arg.dep/undep-ctc)))]
  #:do [(define is-any? (and (attribute any-kw) #t))]
  #:with is-any-stx (->syntax is-any?)
  #:with arg-contract-makers-stx (->syntax
                                  (cons
                                   #'list
                                   (for/list ([arg (in-list (attribute mandatory-arg.dep/undep-ctc))])
                                     #`(λ #,(static-un/dep-deps arg)
                                         #,(static-un/dep-stx arg)))))
  #:with arg-dependencies-hash-stx (->syntax (static-deps->graph-hash
                                              (attribute mandatory-arg.dep/undep-ctc)))
  #:do [(define result-dep/undep-ctcs (if (attribute single-result.dep/undep-ctc)
                                          (list (attribute
                                                 single-result.dep/undep-ctc))
                                          (attribute results.dep/undep-ctc)))]
  #:with result-contract-makers-stx
  (->syntax
   (or is-any?
       #`(λ #,arg-names
           #,(cons
              #'list
              (for/list ([result (in-list result-dep/undep-ctcs)])
                (define result-dep-names (remove* arg-names
                                                  (static-un/dep-deps result)
                                                  free-identifier=?))
                #`(λ #,result-dep-names
                    #,(static-un/dep-stx result)))))))
  #:with result-dependencies-hash-stx (->syntax (or is-any?
                                                    (static-deps->graph-hash
                                                     result-dep/undep-ctcs)))
  (make-modal->i mode
                 'unquoted-name
                 (make-arg-contracter arg-contract-makers-stx
                                      arg-dependencies-hash-stx)
                 is-any-stx
                 (make-result-contracter result-contract-makers-stx
                                         result-dependencies-hash-stx)))

(define (make-modal->i should-apply-ctc?
                       name
                       contract-the-args
                       no-results?
                       contract-the-results)
  (make-contract
   #:name name
   #:late-neg-projection
   (λ (blame)
     (λ (f neg-party)
       (chaperone-procedure
        f
        (λ args
          (cond [(should-apply-ctc? args)
                 (define contracted-args
                   ((contract-the-args blame neg-party) args))
                 (if no-results? ;; i.e. `any` range
                     (apply values
                            contracted-args)
                     (apply values
                            (λ results
                              (apply values
                                     (((contract-the-results contracted-args)
                                       blame neg-party)
                                      results)))
                            contracted-args))]
                [else
                 (apply values args)])))))))

(module+ test
  (require ruinit
           "test-common.rkt")
  (test-begin
    #:name toposort
    (test-equal? (toposort (hash 'A '()
                                 'B '(A)
                                 'C '(B)))
                 '(A B C))
    (test-equal? (toposort (hash))
                 '())
    (test-equal? (toposort (hash 'A '(D)
                                 'B '(A)
                                 'C '(B)
                                 'D '()))
                 '(D A B C))
    (test-equal? (toposort (hash 'A '(D)
                                 'B '(A also-not-here!)
                                 'C '(B)
                                 'D '(not-in-here!)))
                 '(D A B C))
    (test-equal? (toposort (hash 'A '(something-else)))
                 '(A)))
  (define mode:always (const #t))
  (test-begin
    #:name modal->i
    (ignore (define/contract (f-n-any x)
              (modal->i mode:always ([x number?]) any)
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
            (define/contract (f-indy g x)
              (modal->i mode:always ([g (-> number? number?)]
                                     [x {g} (=/c (g "not a number"))])
                        [result any/c])
              x))
    (test-equal? (f-n-any 5) 5)
    (test-blamed (f-n-any 'hi)
                 (list (? path-string?) 'test))
    (test-blamed (f-n-str 5)
                 '(function f-n-str))
    (test-equal? (f-n-= 5) 5)
    (test-blamed (f-n->-= 5 6)
                 '(function f-n->-=))
    (test-blamed (f-n->-= 5 3)
                 (list (? path-string?) 'test))
    (test-blamed (f-indy (λ (x) x) 5)
                 '?)))
