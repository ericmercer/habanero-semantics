#lang racket
(require redex/reduction-semantics)

(provide (all-defined-out))

; Recursively Parrallel Programs
; Ahmed Bouajjani and Michael Emmi 
; POPL 2012

; Habanero-Java: the New Adventures of Old X10
; Vincent Cave, Jisheng Zhao, Jun Shirako, Vivek Sarkar
; PPPJ 2011
;
; 1. DRF(p) /\ HF(p) \subseteq {async, finish, future get} -> DLF(p) /\
;    DRF(p) /\ DET(p) /\ SER(p)
; 2. DRF(p) /\ HF(p) \subseteq {async, finish, future get, phaser new,
;    phaser next, phaser signal} -> DLF(p) /\ DRF(p) /\ DET(p)
; 3. DRF(p) /\ HF(p) \subseteq {async, finish, future get, phaser new,
;    phaser next, phaser signal, phaser wait, DDF} -> DRF(p) /\ DET(p)
; 4. DRF(p) /\ HF(p) \subseteq {async, finish, future get, phaser new,
;    phaser next, phaser signal, isolated} -> DLF(p) /\ DRF(p)
; 5. DRF(p) /\ HF(p) \subseteq {async, finish, future get, phaser new,
;    phaser next, phaser signal, phaser wait, DDF, isolated} -> DRF(p)
;    [trivial]
; 6. no theorem
; 7. no theorem

; -----------------------------------------------------
; -------------------- SYNTAX -------------------------
; -----------------------------------------------------

(define-language rpp-surface
  (P (μ m))
  (μ (M ...))
  (M (m (x ...) e))
  (e (begin e ...)
     (x := e)
     (if e e else e)
     (while e do e)
     (m (e ...))
     x
     v
     (e binop e)
     (var x := e in e)
     )
  (binop ==
         <=
         >=
         >
         <
         +
         -
         *
         /)
  (v number)
  (x id)
  (m id)
  (id variable-not-otherwise-mentioned)
  )

(define-extended-language rpp rpp-surface
  (e ....
     (raw m (v ...)))
  ;; eval syntax
  (h mt
     (h [v -> v]))
  (η mt
     (η [x -> v]))
  (state (μ h η e k))
  (k ret
     (m (v ...) * (e ...) -> k)
     (* binop e -> k)
     (v binop * -> k)
     (x := * -> k)
     (if * e else e -> k)
     (while * do e -> k)
     (var x := * in e -> k)
     (begin * (e ...) -> k)
     (pop η k))
  )

; -----------------------------------------------------
; ------------- EXPRESSION REDUCTIONS -----------------
; -----------------------------------------------------

(define expr-reductions
  (reduction-relation
   rpp
   #:domain state
   
   ; begin
   (--> (μ h η (begin) k)
        (μ h η 0 k)
        "begin -- empty expression list")
   (--> (μ h η (begin e_0 e_1 ...) k)
        (μ h η e_0 (begin * (e_1 ...) -> k))
        "begin -- e_0 evaluation")
   (--> (μ h η v (begin * (e_i e_i+1 ...) -> k))
        (μ h η e_i (begin * (e_i+1 ...) -> k))
        "begin -- e_i evaluation")
   (--> (μ h η v (begin * () -> k))
        (μ h η v k)
        "begin -- complete")

   ; assign
   (--> (μ h η (x := e) k)
        (μ h η e (x := * -> k))
        "assign -- object eval")
   (--> (μ h η v (x := * -> k))
        (μ h_0 η v k)
        "assign"
        (where v_0 (η-lookup η x))
        (where h_0 (h-extend* h [v_0 -> v])))

   ; if-then-else
   (--> (μ h η (if e_p e_t else e_f) k)
        (μ h η e_p (if * e_t else e_f -> k))
        "if-then-else -- eval")
   (--> (μ h η v (if * e_t else e_f -> k))
        (μ h η ,(if (equal? (term v) (term 0)) (term e_f) (term e_t)) k)
        "if-then-else")

    ; method invocation
   (--> (μ h η (m (e_0 e_1 ...)) k)
        (μ h η e_0 (m () * (e_1 ...) -> k))
        "method invocation - arg0 eval")
   (--> (μ h η v_i (m (v_a ...) * (e_0 e_1 ...) -> k))
        (μ h η e_0 (m (v_a ... v_i) * (e_1 ...) -> k))
        "method invocation - argi eval")
   (--> (μ h η (m ()) k)
        (μ h η (raw m ()) k)
        "method invocation - no args")
   (--> (μ h η v_1 (m (v_0 ...) * () -> k))
        (μ h η (raw m (v_0 ... v_1)) k)
        "method invocation - args")
   (--> (μ h η (raw m (v_x ...)) k)
        (μ h η_0 e_m (pop η k))
        "raw method invocation"
        (where ((x_m ...) e_m) (method-lookup μ m))
        (where η_0 (η-extend* η [x_m -> v_x] ...)))
  
   ; variable access
   (--> (μ h η x k)
        (μ h η v k)
        "Variable access"
        (where v (h-lookup h (η-lookup η x))))  
      
   ; varriable declaration
   (--> (μ h η (var x := e_0 in e_1) k)
        (μ h η e_0 (var x := * in e_1 -> k))
        "variable declaration -- object eval")
   (--> (μ h η v (var x := * in e_1 -> k))
        (μ h_0 η_0 e_1 (pop η k))
        "variable declaration"
        (where v_x (h-malloc h))
        (where h_0 (h-extend* h [v_x -> v]))
        (where η_0 (η-extend* η [x -> v_x])))
   
   ; binop 
   (--> (μ h η (e_0 binop e) k)
        (μ h η e_0 (* binop e -> k))
        "equals - l-operand eval")
   (--> (μ h η v (* binop e -> k))
        (μ h η e (v binop * -> k))
        "equals - r-operand eval")
   (--> (μ h η v_0 (v_1 == * -> k))
        (μ h η v_res k)
        "equals"
        (where v_res ,(->bool (equal? (term v_0) (term v_1))))) 
   ; Add all the other operators...
   
   ; Pop η (close scope)
   (--> (μ h η v (pop η_0 k))
        (μ h η_0 v k)
        "pop η")
   ))

; -----------------------------------------------------
; ------------------ HELPER FUNCTIONS -----------------
; -----------------------------------------------------

(define-metafunction rpp
  get-length : (any ...) -> number
  [(get-length (any_0 ...))
   ,(length (term (any_0 ...)))])
  
(define-metafunction rpp
  h-max : h -> number
  [(h-max mt) -1]
  [(h-max (h [v_x -> v]))
   ,(max (term v_x) (term (h-max h)))])

(define-metafunction rpp
  h-malloc : h -> number
  [(h-malloc h)
   ,(add1 (term (h-max h)))])

(define-metafunction rpp
  h-malloc-n-helper : number number -> (v ...)
  [(h-malloc-n-helper number_b number_c)
   ,(let ([z (term number_b)]) (build-list (term number_c) (lambda (y) (+ y z))))])

(define-metafunction rpp
  h-malloc-n : h number -> (v ...)
  [(h-malloc-n h number)
   (h-malloc-n-helper (h-max h) number)])

(define-metafunction rpp
  storelike-lookup : any any -> any
  [(storelike-lookup mt any_0)
   ,(error 'storelike-loopup "~e not found in ~e" (term any_0) (term mt))]
  [(storelike-lookup (any_0 [any_t -> any_ans]) any_t)
   any_ans]
  [(storelike-lookup (any_0 [any_k -> any_v]) any_t)
   (storelike-lookup any_0 any_t)
   (side-condition (not (equal? (term any_k) (term any_t))))])

(define (id-<= a b)
  (string<=? (symbol->string a) (symbol->string b)))
(define (storelike-extend <= storelike k hv)
  (match storelike
    ['mt `(mt [,k -> ,hv])]
    [`(,storelike [,ki -> ,hvi])
     (cond
       [(equal? k ki)
        `(,storelike [,ki -> ,hv])]
       [(<= k ki)
        `(,(storelike-extend <= storelike k hv) [,ki -> ,hvi])]
       [else
        `((,storelike [,ki -> ,hvi]) [,k -> ,hv])])]))     
  
(define (storelike-extend* <= storelike extend*)
  (match extend*
    ['() storelike]
    [`([,k -> ,hv] . ,extend*)
     (storelike-extend* <= (storelike-extend <= storelike k hv) extend*)]))

(define-metafunction rpp
  h-lookup : h v -> v
  [(h-lookup h v)
   (storelike-lookup h v)])

(define-metafunction rpp
  h-extend* : h [v -> v] ... -> h
  [(h-extend* h [v_0 -> v_1] ...)
   ,(storelike-extend* <= (term h) (term ([v_1 -> v_1] ...)))])

(define-metafunction rpp
  η-lookup : η x -> v
  [(η-lookup η x)
   (storelike-lookup η x)])

(define-metafunction rpp
  η-extend* : η [x -> v] ... -> η
  [(η-extend* η [x -> v] ...)
   ,(storelike-extend* id-<= (term η) (term ([x -> v] ...)))])

(define-metafunction rpp
  method-name : M -> m
  [(method-name (m (x ...) e))
   m])

(define-metafunction rpp
  method-expression : M -> e
  [(method-expression (m (x ...) e))
   e])

(define-metafunction rpp
  method-args : M -> (x ...)
  [(method-args (m (x ...) e))
   (x ...)])

(define-metafunction rpp
  method-lookup : μ m -> any
  [(method-lookup (M_0 ... M_t M_1 ...) m)
   ((method-args M_t) (method-expression M_t))
   (side-condition (equal? (term (method-name M_t)) (term m)))]
  [(method-lookup (M ...) m)
   error
   (side-condition (equal? (findf (λ (i) (equal? (term (method-name ,i)) (term m)))
                                   (term (M ...))) #f))])

(define (->bool v)
    (if v
        '0
        '1))

(define-metafunction rpp
  inject : P -> state
  [(inject (μ (C m)))
   (μ mt mt ((new C) @ m ()) ret)])

(define-metafunction rpp
  inject/with-state : state m -> state
  [(inject/with-state (μ h η e k) m)
   (μ h η (e @ m ()) ret)])
   
