#lang plait

(module+ test
  (print-only-errors #t))

;; abstract syntax -------------------------------

(define-type Exp
  (numE [n : Number])
  (ifE [b : Exp] [l : Exp] [r : Exp])
  (varE [x : Symbol])
  (letE [x : Symbol] [e1 : Exp] [e2 : Exp])
  (lamE [args : (Listof Symbol)] [e : Exp]) ; lamE w pierwszym polu przechowuje listę symboli
  (appE [e : Exp] [args : (Listof Exp)]))   ; appE w drugim polu przechowuje listę wyrażeń

;; parse ----------------------------------------

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s)
     (numE (s-exp->number s))]
    [(s-exp-match? `{lambda {SYMBOL ...} ANY} s)
     (lamE (map s-exp->symbol (s-exp->list (second (s-exp->list s)))) ; Zwracamy listę sparsowanych symboli
           (parse (third (s-exp->list s))))]
    [(s-exp-match? `{if ANY ANY ANY} s)
     (ifE (parse (second (s-exp->list s)))
          (parse (third (s-exp->list s)))
          (parse (fourth (s-exp->list s))))]
    [(s-exp-match? `SYMBOL s)
     (varE (s-exp->symbol s))]
    [(s-exp-match? `{let SYMBOL ANY ANY} s)
     (letE (s-exp->symbol (second (s-exp->list s)))
           (parse (third (s-exp->list s)))
           (parse (fourth (s-exp->list s))))]
    [(s-exp-match? `{SYMBOL ANY ANY} s)
     (appE (appE (varE (parse-op (s-exp->symbol (first (s-exp->list s)))))
                 (list (parse (second (s-exp->list s)))))
           (list (parse (third (s-exp->list s)))))] ; Wylistowujemy sparsowane wyrażenia typu ANY
    [(s-exp-match? `{ANY ANY ...} s)
     (appE (parse (first (s-exp->list s)))      
           (map parse (rest (s-exp->list s))))] ; Zwracamy listę sparsowanych wyrażeń
    [else (error 'parse "invalid input")]))

(define prim-ops '(+ - * / = <=))

(define (parse-op [op : Symbol]) : Symbol
  (if (member op prim-ops)
      op 
      (error 'parse "unknown operator")))

(module+ test
  (test (parse `2)
        (numE 2))
  (test (parse `{+ 2 1})
        (appE (appE (varE '+) (list (numE 2))) (list (numE 1))))  ; Wprowadzamy odpowiednie
  (test (parse `{* 3 4})                                          ; modyfikacje w testach
        (appE (appE (varE '*) (list (numE 3))) (list (numE 4)))))


;; eval --------------------------------------

;; values

(define-type Value
  (numV [n : Number])
  (boolV [b : Boolean])
  (funV [xs : (Listof Symbol)] [e : Exp] [env : Env]) ; funV w pierwszym polu przechowuje listę symboli
  (primopV [f : (Value -> Value)]))

(define-type Binding
  (bind [name : Symbol]
        [val : Value]))

;; environments

(define-type-alias Env (Listof Binding))

(define mt-env empty)
(define (extend-env [env : Env] [x : Symbol] [v : Value]) : Env
  (cons (bind x v) env))
(define (extend-env-with-list [env : Env] [xs : (Listof Symbol)] [vs : (Listof Value)]) : Env 
  (type-case (Listof Symbol) xs
    [(cons x xs)
     (type-case (Listof Value) vs
       [(cons v vs)
        (extend-env-with-list (cons (bind x v) env) xs vs)]
       [else
        (error 'apply "Syntax error")])]
    [else
     (type-case (Listof Value) vs
       [(cons v vs)
        (error 'apply "Syntax error")]
       [else
        env])])) ; Funkcja extend-env-with-list dorzuca do środowiska listę zmiennych z przypisaną wartością
(define (lookup-env [n : Symbol] [env : Env]) : Value
  (type-case (Listof Binding) env
    [empty (error 'lookup "unbound variable")]
    [(cons b rst-env) (cond
                        [(eq? n (bind-name b))
                         (bind-val b)]
                        [else (lookup-env n rst-env)])]))

;; primitive operations and the initial environment

(define (op-num-num->value [f : (Number Number -> Number)]) : Value 
  (primopV
   (λ (v1)
     (type-case Value v1
       [(numV n1)
        (primopV
         (λ (v2)
           (type-case Value v2
             [(numV n2)
              (numV (f n1 n2))]
             [else
              (error 'eval "type error")])))]
       [else
        (error 'eval "type error")]))))

(define (op-num-bool->value [f : (Number Number -> Boolean)]) : Value 
  (primopV
   (λ (v1)
     (type-case Value v1
       [(numV n1)
        (primopV
         (λ (v2)
           (type-case Value v2
             [(numV n2)
              (boolV (f n1 n2))]
             [else
              (error 'eval "type error")])))]
       [else
        (error 'eval "type error")]))))

(define init-env 
  (foldr (λ (b env) (extend-env env (fst b) (snd b)))
         mt-env 
         (list (pair '+ (op-num-num->value +))
               (pair '- (op-num-num->value -))
               (pair '* (op-num-num->value *))
               (pair '/ (op-num-num->value /))
               (pair '= (op-num-bool->value =))
               (pair '<= (op-num-bool->value <=)))))

;; evaluation function (eval/apply)

(define (eval [e : Exp] [env : Env]) : Value
  (type-case Exp e
    [(numE n) (numV n)]
    [(ifE b l r)
     (type-case Value (eval b env)
       [(boolV v)
        (if v (eval l env) (eval r env))]
       [else
        (error 'eval "type error")])]
    [(varE x)
     (lookup-env x env)]
    [(letE x e1 e2)
     (let ([v1 (eval e1 env)])
       (eval e2 (extend-env env x v1)))]
    [(lamE args b)
     (funV args b env)] ; Do pierwszego pola funV przekazujemy listę symboli
    [(appE e1 e2)
     (apply (eval e1 env) (map (lambda (x) (eval x env)) e2))])) ; Do drugiego argumentu funkcji apply
                                                                 ; przekazujemy listę wyewaluowanych wyrażeń

(define (apply [v1 : Value] [v2 : (Listof Value)]) : Value ; Drugi argument funkcji apply
  (type-case Value v1                                      ; przyjmuję listę wyrażeń Value
    [(funV args b env)
     (eval b (extend-env-with-list env args v2))] ; Środowisko aktualizujemy za pomocą funckji extend-env-with-list
    [(primopV f)           ; W przypadku wystąpienia konstruktora primopV sprawdzamy,                            
     (if (= 1 (length v2)) ; czy ilość argumentów jest równa jeden
         (f (first v2))    
         (error 'apply "Syntax error"))]
    [else (error 'apply "not a function")]))

(define (run [e : S-Exp]) : Value
  (eval (parse e) init-env))

(module+ test
  (test (run `2)
        (numV 2))
  (test (run `{+ 2 1})
        (numV 3))
  (test (run `{* 2 1})
        (numV 2))
  (test (run `{+ {* 2 3} {+ 5 8}})
        (numV 19))
  (test (run `{= 0 1})
        (boolV #f))
  (test (run `{if {= 0 1} {* 3 4} 8})
        (numV 8))
  (test (run `{let x 1 {+ x 1}})
        (numV 2))
  (test (run `{let x 1 {+ x {let y 2 {* x y}}}})
        (numV 3))
  (test (run `{let x 1
                {+ x {let x {+ x 1}
                       {* x 3}}}})
        (numV 7))
  (test (run `{{lambda {x} {+ x 1}} 5})
        (numV 6))
  (test (run `{lambda {x} {lambda {y} {+ x y}}})
        (funV '(x)
              (lamE '(y) (appE (appE (varE '+)         ; Wprowadzamy odpowiednie
                                     (list (varE 'x))) ; modyfikacje w testach
                               (list (varE 'y))))      
              init-env))
  (test (run `{{lambda {} {+ 7 7}} })
        (numV 14)) ; Test na zerową ilość argumentów aplikacji
  (test (run `{{lambda {x y z} {+ x {+ y z}}} 5 5 4})
        (numV 14)) ; Test na większą ilość argumentów aplikacji
  (test (run `{let a 1
                {let p {lambda {x} {+ x a}}
                  {let a 10
                    {p 0}}}})
        (numV 1)))


;; printer ———————————————————————————————————-

(define (value->string [v : Value]) : String
  (type-case Value v
    [(numV n) (to-string n)]
    [(boolV b) (if b "true" "false")]
    [(funV x e env) "#<procedure>"]
    [(primopV f) "#<primop>"]))

(define (print-value [v : Value]) : Void
  (display (value->string v)))

(define (main [e : S-Exp]) : Void
  (print-value (eval (parse e) init-env)))
