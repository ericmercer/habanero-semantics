#lang racket
(require redex/reduction-semantics
         "rpp.rkt")

(define random-term
  (generate-term rpp P 10))

; -----------------------------------------------------
; ------------------ REWRITE TESTS --------------------
; -----------------------------------------------------

(define-syntax-rule (test-->* red st mt ...)
  (test-predicate (-test-->* red mt ...) st))

(define ((-test-->* red . mts) st)
  (define not-seen (make-hash))
  (for ([mt (in-list mts)])
    (hash-set! not-seen mt #t))
  (let loop ([t st])
    (hash-remove! not-seen t)
    (or (zero? (hash-count not-seen))
        (let ([ts (apply-reduction-relation red t)])
          (ormap loop ts)))))

(define ex
  (reduction-relation
   rpp
   [--> 1 2] [--> 2 3] [--> 3 4] [--> 4 5] [--> 5 1]))

(test-->* ex 1
          2 4)

; variable access
(local [(define h-simple
          (term (((mt [1 -> 0]) 
                 [2 -> 3])[3 -> 4])))
        (define η-simple
          (term ((mt [x -> 1]) [y -> 3])))] 
  (test--> expr-reductions
         (term (() ,h-simple ,η-simple x ret))
         (term (() ,h-simple ,η-simple 0 ret)))
  (test--> expr-reductions
           (term (() ,h-simple ,η-simple y ret))
           (term (() ,h-simple ,η-simple 4 ret))))

; method invocation - arg0 eval
(test--> expr-reductions
         (term (() mt mt 
                   (m (x y)) ret))
         (term (() mt mt 
                   x (m () * (y) -> ret))))

; method invocation - argi eval
(test--> expr-reductions
         (term (() mt mt 
                   1 (who (1 0) * (y) -> ret)))
         (term (() mt mt 
                   y (who (1 0 1) * () -> ret))))

; method invocation - no args
(test--> expr-reductions
         (term (() mt mt (m ()) ret))
         (term (() mt mt (raw m ()) ret)))

; raw method invocation
(local [(define μ-test
          (term ((m (x y z) (begin 1)) (n (i j k) (begin 0)) ))) 
        (define h-test
          (term (h-extend* mt [1 -> 1])))
        (define η-test
          (term mt))]
  
  (test-predicate (redex-match rpp μ) 
                  μ-test)

  (test-predicate (redex-match rpp (μ h η (raw m (v_x ...)) k))
                  (term (,μ-test 
                         ,h-test 
                         ,η-test 
                         (raw m (1 2 3)) ret)))
  
  (test--> expr-reductions
           (term (,μ-test 
                  ,h-test 
                  ,η-test 
                  (raw m (1 2 3)) ret))
           (term (,μ-test 
                  ,h-test         
                  (η-extend* ,η-test [x -> 1] [y -> 2] [z -> 3])
                  (begin 1) 
                  (pop ,η-test ret)))))

; method invocation general
(local [(define μ-test
          (term ((m (x y z) (begin 1)) (n (i j k) (begin 0)) )))
        (define h-test
          (term (h-extend* mt [1 -> 1] [2 -> 2] [3 -> 3])))
        (define η-test
          (term (η-extend* mt [i -> 1] [j -> 2] [k -> 3])))]
  
  (test--> expr-reductions
           (term (,μ-test ,h-test ,η-test (raw m (1 2 3)) ret))
           (term (,μ-test 
                  ,h-test 
                  (η-extend* ,η-test [x -> 1] [y -> 2] [z -> 3]) 
                  (begin 1) (pop ,η-test ret))))
  
  (test-->* expr-reductions
           (term (,μ-test ,h-test ,η-test (m (i j k)) ret))
           (term (,μ-test ,h-test ,η-test i (m () * (j k) -> ret)))
           (term (,μ-test ,h-test ,η-test j (m (1) * (k) -> ret)))
           (term (,μ-test ,h-test ,η-test k (m (1 2) * () -> ret)))
           (term (,μ-test ,h-test ,η-test (raw m (1 2 3)) ret))
           (term (,μ-test 
                  ,h-test 
                  (η-extend* ,η-test [x -> 1] [y -> 2] [z -> 3]) 
                  (begin 1) (pop ,η-test ret)))))

;; equals '=='
;(local [(define h-test
;          (term (h-extend* mt [0 -> true] [1 -> true] [2 -> false])))
;        (define η-test
;          (term (η-extend* mt [x -> 0] [y -> 1] [z -> 2])))]
;  
;  (test-->* expr-reductions
;           (term (() ,h-test ,η-test (x == x) ret))
;           (term (() ,h-test ,η-test true ret)))
;  (test-->* expr-reductions
;           (term (() ,h-test ,η-test (y == y) ret))
;           (term (() ,h-test ,η-test true ret)))
;  (test-->* expr-reductions
;           (term (() ,h-test ,η-test (y == z) ret))
;           (term (() ,h-test ,η-test false ret))))
;
;; typecast (C e)
;(local [(define h-test
;          (term (h-extend* mt [0 -> ((Object) (C0) (C1 [f 0]) (C2))] [1 -> (addr 0 C1)])))
;        (define η-test
;          (term (η-extend* mt [x -> 1])))]
;  
;  (test-->* expr-reductions
;            (term (() ,h-test ,η-test (C2 x) ret))
;            (term (() ,h-test ,η-test (addr 0 C2) ret)))
;  (test-->* expr-reductions
;            (term (() ,h-test ,η-test (Object x) ret))
;            (term (() ,h-test ,η-test (addr 0 Object) ret))))
;
;; instanceof  
;(test-->* expr-reductions
;          (term (() ((mt [0 -> ((Object) (C))])[1 -> (addr 0 C)]) (mt [x -> 1]) (x instanceof C) ret))
;          (term (() ((mt [0 -> ((Object) (C))])[1 -> (addr 0 C)]) (mt [x -> 1]) x (* instanceof C -> ret)))
;          (term (() ((mt [0 -> ((Object) (C))])[1 -> (addr 0 C)]) (mt [x -> 1]) true ret)))
;
;(test-->* expr-reductions
;          (term (() ((mt [0 -> ((Object) (C))])[1 -> (addr 0 C)]) (mt [x -> 1]) (x instanceof D) ret))
;          (term (() ((mt [0 -> ((Object) (C))])[1 -> (addr 0 C)]) (mt [x -> 1]) x (* instanceof D -> ret)))
;          (term (() ((mt [0 -> ((Object) (C))])[1 -> (addr 0 C)]) (mt [x -> 1]) false ret)))
;
;(test--> expr-reductions
;         (term (() (mt (0 -> ((Object) (C)))) mt (addr 0 C) (* instanceof C -> ret)))
;         (term (() (mt [0 -> ((Object) (C))]) mt true ret)))
;
;(test-predicate (redex-match javalite (μ h η v (* instanceof C -> k))) 
;                (term (() (mt (0 -> ((Object) (C)))) mt (addr 0 C) (* instanceof C -> ret))))
;
;; assign
;(test-->* expr-reductions
;          (term (() (mt [0 -> true]) (mt [x -> 0]) (x := false) ret))
;          (term (() (mt [0 -> true]) (mt [x -> 0]) false (x := * -> ret)))
;          (term (() (mt [0 -> false]) (mt [x -> 0]) false ret)))
;
;; field assign
;(local [(define h_0
;          (term ((((mt [0 -> ((Object) (C [f 1]))]) [1 -> true]) [2 -> false])[3 -> (addr 0 C)])))]
;  
;  (test-predicate (redex-match javalite h) h_0)
;  (test-term-equal (h-lookup ,h_0 (η-lookup ((mt [x -> 3])[y -> 2]) x))
;                   (addr 0 C))
;  
;  (test-->* expr-reductions
;           (term (() ,h_0 ((mt [x -> 3]) [y -> 2]) (x $ f := y) ret))
;           (term (() ,h_0 ((mt [x -> 3]) [y -> 2]) false (x $ f := * -> ret)))
;           (term (() (h-extend* ,h_0 [1 -> false]) ((mt [x -> 3]) [y -> 2]) false ret))))      
;
;; if-the-else
;(test-->* expr-reductions
;          (term (() (mt [0 -> true]) (mt [x -> 0]) (if x true else false ) ret))
;          (term (() (mt [0 -> true]) (mt [x -> 0]) x (if * true else false -> ret)))
;          (term (() (mt [0 -> true]) (mt [x -> 0]) true ret)))
;
;(test-->> expr-reductions
;          (term (() (mt [0 -> false]) (mt [x -> 0]) (if x true else false ) ret))
;          (term (() (mt [0 -> false]) (mt [x -> 0]) false ret)))
;
;; variable declaration
;(test-->* expr-reductions
;          (term (() (mt [0 -> null]) (mt [y -> 0]) (var bool x := false in x) ret))
;          (term (() (mt [0 -> null]) (mt [y -> 0]) false (var bool x := * in x -> ret)))
;          (term (() ((mt [0 -> null]) [1 -> false]) ((mt [x -> 1]) [y -> 0]) x (pop (mt [y -> 0]) ret)))
;          (term (() ((mt [0 -> null]) [1 -> false]) ((mt [x -> 1]) [y -> 0]) false (pop (mt [y -> 0]) ret)))
;          (term (() ((mt [0 -> null]) [1 -> false]) (mt [y -> 0]) false ret)))
;
;; begin
;(test--> expr-reductions
;         (term (() mt mt (begin) ret))
;         (term (() mt mt unit ret)))
;
;(local [(define h_0
;          (term ((((mt [0 -> unit]) [1 -> null]) [2 -> true]) [3 -> false])))
;        (define η_0
;          (term ((((mt [w -> 0]) [x -> 1]) [y -> 2]) [z -> 3])))]
;        
;        (test-->* expr-reductions
;                  (term (() ,h_0 ,η_0 (begin w x y z) ret))
;                  (term (() ,h_0 ,η_0 w (begin * (x y z) -> ret)))
;                  (term (() ,h_0 ,η_0 unit (begin * (x y z) -> ret)))
;                  (term (() ,h_0 ,η_0 x (begin * (y z) -> ret)))
;                  (term (() ,h_0 ,η_0 y (begin * (z) -> ret)))
;                  (term (() ,h_0 ,η_0 z (begin * () -> ret)))
;                  (term (() ,h_0 ,η_0 false ret))))
;         
;; pop η
;(test--> expr-reductions
;         (term (() mt (mt [x -> 2]) true (pop (mt [x -> 3]) ret)))
;         (term (() mt (mt [x -> 3]) true ret)))
;
;; -----------------------------------------------------
;; -------------- HELPER FUNCTIONS TESTS ---------------
;; -----------------------------------------------------
;(define-syntax-rule (test-term-equal lhs rhs)
;  (test-equal (term lhs) (term rhs)))
;
;(test-predicate (redex-match javalite object) 
;                (term ((Object) (C2 [x 0] [y 10] [z 3]))))
;
;; default-value
;(test-term-equal (default-value unit) unit)
;(test-term-equal (default-value bool) false)
;(test-term-equal (default-value C) null)
;(test-term-equal (default-value Object) null)
;
;; default-value*
;(test-term-equal (default-value* (unit)) (unit))
;(test-term-equal (default-value* (bool C unit)) (false null unit))
;(test-term-equal (default-value* ()) ())
;
;; h-max
;(test-term-equal (h-max mt) -1)
;(test-term-equal (h-max (mt [0 -> ((Object) (C2 [x 0] [y 10] [z 3]))])) 0)
;(test-term-equal (h-max (mt [3 -> unit])) 3)
;(test-term-equal (h-max ((mt [4 -> true]) [3 -> unit])) 4)
;
;; h-malloc
;(test-term-equal (h-malloc mt) 0)
;(test-term-equal (h-malloc (mt [0 -> true])) 1)
;(test-term-equal (h-malloc (mt [3 -> false])) 4)
;(test-term-equal (h-malloc ((mt [4 -> true]) 
;                            [3 -> ((Object) (C2 [x 0] [y 10] [z 3]))])) 
;                 5)
;
;; h-malloc-n
;(test-term-equal (h-malloc-n mt 5) (0 1 2 3 4))
;(test-term-equal (h-malloc-n (mt [3 -> true]) 1) (4))
;(test-term-equal (h-malloc-n (mt [3 -> true]) 0) ())
;(test-term-equal (h-malloc-n (mt [3 -> true]) 3) (4 5 6))
;
;; h-malloc-n*
;(test-term-equal (h-malloc-n* mt 0 1 2 3) (() (0) (1 2) (3 4 5)))
;(test-term-equal (h-malloc-n* mt 2)((0 1)))
;(test-term-equal (h-malloc-n* (mt [3 -> true]) 2) ((4 5)))
;(test-term-equal (h-malloc-n* (mt [3 -> true]) 2 0 3) ((4 5) () (6 7 8)))
;
;; storelike-lookup
;(test-term-equal (storelike-lookup (mt [a -> 1]) a) 1)
;(test-term-equal (storelike-lookup ((mt [a -> 1]) [a -> 2]) a) 2)
;(test-term-equal (storelike-lookup ((mt [a -> 1]) [b -> 2]) a) 1)
;
;; h-lookup
;(test-term-equal (h-lookup (mt [1 -> true]) 1) 
;                 true)
;(test-term-equal (h-lookup ((mt [1 -> true]) [1 -> true]) 1) 
;                 true)
;(test-term-equal (h-lookup ((mt [1 -> false]) [2 -> ((foo))]) 1) 
;                 false)
;(test-term-equal (h-lookup ((mt [1 -> ((doo [f 0] [y 10] [whoo 3]))]) 
;                            [2 -> ((foo))]) 1) 
;                 ((doo [f 0] [y 10] [whoo 3])))
;
;; field lookup
;(test-term-equal (field-lookup ((Obj) (C1 [x 1] [y 2]) (C2 [x 3])) x C2)
;                 3)
;(test-term-equal (field-lookup ((Obj) (C1 [x 1] [y 2]) (C2 [x 3])) x C1)
;                 1)
;(test-term-equal (field-lookup ((Obj) (C1 [x 1] [y 2]) (C2 [x 3])) y C2)
;                 2)
;(test-term-equal (field-lookup ((Obj) (C1 [y 1] [y 2]) (C2 [x 3])) y C2)
;                 2)
;
;(define μ-simple
;  (term ((class C1 extends Object ()((T M1 ([T x] [T y] [T z]) (begin true)))) (class C2 extends C1 () ()) )))
;
;(test-predicate (redex-match javalite μ) μ-simple)
;
;; class-parrents+self
;(test-term-equal (class-parents+self ,μ-simple Object)
;                 (Object))
;(test-term-equal (class-parents+self ,fig1-CL Object)
;                 (Object))
;(test-term-equal (class-list-extend (Object C1) C2)
;                 (Object C1 C2))
;(test-term-equal (class-parents+self ,μ-simple C2)
;                 (Object C1 C2))
;(test-term-equal (class-parents+self ,fig1-CL Node)
;                 (Object Node))
;(test-term-equal (class-parents+self ,fig1-CL XNode)
;                 (Object Node XNode))
;(test-term-equal (class-parents+self ,fig1-CL YNode)
;                 (Object Node YNode))
;(test-term-equal (class-parents+self ,fig1-CL Main)
;                 (Object Main))
;
;; fields-list-extend
;(test-term-equal (field-lists-extend () ())
;                 (()))
;
;; fields-parents+self
;(local [(define μ_0
;         (term ((class C1 extends Object ([C1 x] [C1 y])()) (class C2 extends C1 ([C1 z]) ()) (class C3 extends C2 () ()))))]
;  
;  (test-term-equal (fields-parents+self ,μ_0 Object)
;                   (()))
;  (test-term-equal (fields-parents+self ,μ_0 C1)
;                   (() ([C1 x] [C1 y])))
;  (test-term-equal (fields-parents+self ,μ_0 C2)
;                   (() ([C1 x] [C1 y]) ([C1 z])))
;  (test-term-equal (fields-parents+self ,μ_0 C3)
;                   (() ([C1 x] [C1 y]) ([C1 z]) ())))
;                  
;; method-lookcup
;(test-term-equal (method-lookup (class-lookup ,μ-simple C1) m)
;                 error)
;(test-term-equal (method-lookup (class-lookup ,fig1-CL Node) m)
;                 error)
;(test-term-equal (method-lookup (class-lookup ,fig1-CL Node) check)
;                 (Node () (begin true)))
;(test-term-equal (method-lookup (class-lookup ,μ-simple C1) M1)
;                 (C1 (x y z) (begin true)))
;(test-predicate (redex-match javalite CL) (term (class C0 extends Object ((bool x) (bool y)) ((bool m () (begin (x := true) (y := true)))))))
;(test-term-equal (method-lookup (class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true))))) m)
;                 (C0 () (begin (x := true) (y := true))))
;
;(test-predicate (redex-match javalite object) (term  ((Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))))
;(test-predicate (redex-match javalite h) (term (mt [0 -> ((Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))])))
;
;(test--> expr-reductions
;         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
;                 (class C1 extends C0 ([bool y]) ((bool n () true)))
;                 (class C2 extends C1 ([bool z]) ((bool m () false))))
;                (mt [0 -> ((Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) 
;                mt (raw (addr 0 C0) @ m ()) ret))
;         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
;                 (class C1 extends C0 ([bool y]) ((bool n () true)))
;                 (class C2 extends C1 ([bool z]) ((bool m () false))))
;                ((mt [0 -> ((Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) [1 -> (addr 0 C2)])
;                (mt [this -> 1])
;                false (pop mt ret))))       
;
;(test--> expr-reductions
;         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
;                 (class C1 extends C0 ([bool y]) ((bool m () true)))
;                 (class C2 extends C1 ([bool z]) ((bool n () false))))
;                (mt [0 -> ((Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) 
;                mt (raw (addr 0 C0) @ m ()) ret))
;         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
;                 (class C1 extends C0 ([bool y]) ((bool m () true)))
;                 (class C2 extends C1 ([bool z]) ((bool n () false))))
;                ((mt [0 -> ((Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) [1 -> (addr 0 C1)])
;                (mt [this -> 1])
;                true (pop mt ret))))
;
;(test--> expr-reductions
;         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
;                 (class C1 extends C0 ([bool y]) ((bool m () true)))
;                 (class C2 extends C1 ([bool z]) ((bool n () false))))
;                (mt [0 -> ((Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) 
;                mt (raw (addr 0 C2) @ m ()) ret))
;         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
;                 (class C1 extends C0 ([bool y]) ((bool m () true)))
;                 (class C2 extends C1 ([bool z]) ((bool n () false))))
;                ((mt [0 -> ((Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) [1 -> (addr 0 C1)])
;                (mt [this -> 1])
;                true (pop mt ret))))
;
;(test--> expr-reductions
;         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
;                 (class C1 extends C0 ([bool y]) ((bool o () true)))
;                 (class C2 extends C1 ([bool z]) ((bool n () false))))
;                (mt [0 -> ((Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) 
;                mt (raw (addr 0 C0) @ m ()) ret))
;         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
;                 (class C1 extends C0 ([bool y]) ((bool o () true)))
;                 (class C2 extends C1 ([bool z]) ((bool n () false))))
;                ((mt [0 -> ((Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) [1 -> (addr 0 C0)])
;                (mt [this -> 1])
;                (begin (x := true) (y := true)) (pop mt ret))))
;
;;; cast?
;(test-equal (cast? (term ((Object) (C))) (term Object)) '#t)
;(test-equal (cast? (term ((Object) (C))) (term C1)) '#f)
;(test-equal (cast? (term ((Obj) (C1 [x 1] [y 2]) (C2 [x 3]))) (term C2)) #t)
;(test-equal (cast? (term ((Obj) (C1 [x 1] [y 2]) (C2 [x 3]))) (term C1)) #t)
;(test-equal (cast? (term ((Obj) (C1 [x 1] [y 2]) (C2 [x 3]))) (term Obj)) #t)
;(test-equal (cast? (term ((Obj) (C1 [x 1] [y 2]) (C2 [x 3]))) (term x)) #f)
;
;; instanceof*
;(test-term-equal (instanceof* ((Object) (C)) C)
;                 true)
;(test-term-equal (instanceof* ((Object) (C) (D)) Object)
;                 true)
;(test-term-equal (instanceof* ((Object) (C)) D)
;                 false)
;(test-term-equal (instanceof* ((Object)) D)
;                 false)

(test-results)