/-
  Exercise 1.
    Define the function Do_Twice, as described in Section 2.4.
  Exercise 2.
    Define the functions curry and uncurry, as described in Section 2.4.
-/

def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)
def double (x : ℕ) : ℕ := x * 2
def quadruple (x : ℕ) : ℕ := do_twice double x
def octuple (x : ℕ) : ℕ := double (do_twice double x)
def Do_Twice (g : (ℕ → ℕ) → ℕ → ℕ) (f : ℕ → ℕ) : ℕ → ℕ := g (g f)

#reduce double 2
#reduce do_twice double 2
#reduce quadruple 2
#reduce octuple 2
#reduce Do_Twice do_twice double 2

#check do_twice
#check Do_Twice
#check Do_Twice do_twice double

-- curry : (α × β) → γ → α → β → γ
-- uncurry : α → β → γ → (α × β) → γ
def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := λ (a : α) (b : β), f (a, b)
def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := λ (ab : α × β), f ab.1 ab.2

#check curry
#check uncurry



/-
  ...try to understand why the definition of foo below type checks, but 
  the definition of bar does not.
-/

def foo := let a := nat  in λ x : a, x + 2
/-
  def bar := (λ a, (λ x : a, x + 2)) nat
    this does not type check because at check time, 
    Lean does not know that the operation '+' is valid 
    for type 'a', even though 'a' is later resolved to 'nat'.
-/
def bar2 := (λ a, (λ x : a, x)) nat -- to illustrate, this is ok.
#check foo
#check bar2
-- this means that let bindings are evaluated before type checks.



/-
  Exercise 3.
    Above, we used the example vec α n for vectors of elements of type α of length n. 
    Declare a constant vec_add that could represent a function that adds two vectors 
    of natural numbers of the same length, and a constant vec_reverse that can represent 
    a function that reverses its argument. Use implicit arguments for parameters 
    that can be inferred. Declare some variables and check some expressions involving 
    the constants that you have declared.
-/

universe u
variable α : Type u
variables m n o : ℕ

constant vec : Type u → ℕ → Type u
constant vec_add : Π {n}, vec ℕ n → vec ℕ n → vec ℕ n
constant vec_reverse : Π {n}, vec ℕ n → vec ℕ n

variable v2 : vec ℕ 2
variable v3 : vec ℕ 3

#check vec_add v2 v2
#check vec_add v3 v3
-- #check vec_add v2 v3 -- error

#check vec_reverse v2
#check vec_reverse v3



/-
  Exercise 4.
    Similarly, declare a constant matrix so that matrix α m n could represent 
    the type of m by n matrices. Declare some constants to represent functions on 
    this type, such as matrix addition and multiplication, and (using vec) multiplication 
    of a matrix by a vector. Once again, declare some variables and check some expressions 
    involving the constants that you have declared.
-/

constant matrix : Type u → ℕ → ℕ → Type u
constant mat_add : Π {α m n}, matrix α m n → matrix α m n → matrix α m n
constant mat_mul : Π {α m n o}, matrix α m n → matrix α n o → matrix α m o
constant mat_vec_mul : Π {α m n}, matrix α m n → vec α n → vec α m

variable m35 : matrix ℕ 3 5
variable m57 : matrix ℕ 5 7
variable v5 : vec ℕ 5
variable v7 : vec ℕ 7

#check mat_add m35 m35
-- #check mat_add m35 m57 -- error
#check mat_mul m35 m57
-- #check mat_mul m35 m35 -- error
#check mat_vec_mul m35 v5
-- #check mat_vec_mul m35 v7 -- error
