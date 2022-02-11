#lang at-exp racket

(provide modal->i)

(require racket/contract
         syntax/parse/define
         syntax/location)

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
      (values i (filter-map index-of-dep (static-un/dep-deps dep)))))
  ;; (listof static-un/dep?) -> (listof index?)
  ;; Return the indexes of `names` to which `deps` contains references.
  ;;
  ;; E.g.
  #;(static-deps->external-refs
     (list (static-un/dep #'x _ (#'y #'z))
           (static-un/dep #'y _ (#'a #'k)))
     (#'a #'b #'z)) ; => '(0 2)
  (define (static-deps->external-refs deps names)
    (remove-duplicates
     (for*/list ([static-ud (in-list deps)]
                 [dep-name (in-list (static-un/dep-deps static-ud))]
                 [i (in-value (index-of names dep-name free-identifier=?))]
                 #:when i)
       i))))

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
;; (listof index?)
;; (any/c contract? boolean? -> any/c)
;; ->
;; (values (listof any/c) (listof (or/c #f any/c)))
;;
;; Apply dependent contracts produced by `contract-makers` to `plain-values` using `apply-contract`.
;; `dependencies` is the dependency graph between the contracts/values, in terms of their indices.
;; Each `contract-maker` expects the contracted values that the contract it creates depends on,
;; and returns that contract.
(define (dep-apply plain-values
                   contract-makers
                   dependencies
                   extra-internal-ctcs
                   apply-contract)
  (define sorted-indices (toposort dependencies))

  (define (make-indexer l) (let ([v (list->vector l)])
                             (λ (i) (vector-ref v i))))
  (define plain-value (make-indexer plain-values))
  (define contract-maker (make-indexer contract-makers))
  (define needs-internal-ctc?
    (make-indexer (for/list ([i (in-range (length plain-values))])
                    (for/or ([{other-i other-i-deps} (in-hash (hash-set dependencies
                                                                        -1
                                                                        extra-internal-ctcs))]
                             #:when (not (= i other-i))
                             [other-i-dep (in-list other-i-deps)])
                      (= other-i-dep i)))))

  (define internal-contracted-values (make-vector (length plain-values)))
  (for/fold ([external-contracted-values empty]
             #:result (values (reverse external-contracted-values)
                              (vector->list internal-contracted-values)))
            ([index (in-list sorted-indices)])
    (define plain-v (plain-value index))
    (define ctc-maker (contract-maker index))
    (define ctced-deps (for/list ([dep-i (in-list (hash-ref dependencies index))])
                         (vector-ref internal-contracted-values dep-i)))
    (define ctc (apply ctc-maker ctced-deps))

    (when (needs-internal-ctc? index)
      (define v+internal-ctc (apply-contract plain-v ctc #t))
      (vector-set! internal-contracted-values index v+internal-ctc))

    (define v+external-ctc (apply-contract plain-v ctc #f))
    (cons v+external-ctc external-contracted-values)))

;; (listof ((listof any/c) -> contract?))
;; (hash/c index? (listof index?))
;; [boolean?]
;; #:contract-location any/c
;; ->
;; (blame? neg-party? -> ((listof any/c) -> (listof any/c)))
(define (make-arg-contracter contract-makers
                             dependencies
                             [swap-blame? #t]
                             #:contract-location ctc-location
                             #:extra-internal-ctcs [extra-internal-ctcs empty])
  (λ (blame neg-party)
    (λ (plain-args)
      (dep-apply plain-args
                 contract-makers
                 dependencies
                 extra-internal-ctcs
                 (λ (v ctc internal-to-ctc?)
                   (define proj (contract-late-neg-projection ctc))
                   (define maybe-replace-negative
                     (if internal-to-ctc?
                         (λ (b) (blame-replace-negative b ctc-location))
                         values))
                   (define proj/blame
                     (proj (maybe-replace-negative (if swap-blame?
                                                       (blame-swap blame)
                                                       blame))))
                   (proj/blame v neg-party))))))

;; almost same contract as -arg-, less `swap-blame?`, but `make-contract-makers` is curried
;; one level, accepting `any/c ...` to produce the contract makers.
;; Those values are meant to be the internally-contracted arguments.
(define (make-result-contracter make-contract-makers
                                dependencies
                                #:contract-location ctc-location)
  (λ (contract-maker-maker-arguments)
    (define contract-makers (apply make-contract-makers contract-maker-maker-arguments))
    (make-arg-contracter contract-makers
                         dependencies
                         #f
                         #:contract-location ctc-location)))

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
  #:with here (syntax/loc this-syntax (quote-module-name))
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
  #:with args-needed-by-result-dependencies-stx (->syntax
                                                 (cons
                                                  #'list
                                                  (if is-any?
                                                      '()
                                                      (static-deps->external-refs result-dep/undep-ctcs
                                                                                  arg-names))))
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
                                      arg-dependencies-hash-stx
                                      #:contract-location here
                                      #:extra-internal-ctcs args-needed-by-result-dependencies-stx)
                 is-any-stx
                 (make-result-contracter result-contract-makers-stx
                                         result-dependencies-hash-stx
                                         #:contract-location here)))

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
                 (define-values {externally-contracted-args internally-contracted-args}
                   ((contract-the-args blame neg-party) args))
                 (if no-results? ;; i.e. `any` range
                     (apply values
                            externally-contracted-args)
                     (apply values
                            (λ results
                              (define-values {contracted-results _ignored}
                                (((contract-the-results internally-contracted-args)
                                  blame neg-party)
                                 results))
                              (apply values contracted-results))
                            externally-contracted-args))]
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
                 (list (? path-string?) 'test))))
