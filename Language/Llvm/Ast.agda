module Language.Llvm.Ast where

open import Algebra.FunctionProperties.Core using (Op₂)
open import Data.Bool
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length)
module L where
     open import Data.List.All using (All) public
     open import Data.List.Any using (Any; here; there) public
     open import Data.List using (all) public
open L
open import Data.List.NonEmpty using (List⁺)
import Data.List.NonEmpty as L⁺
open import Data.Maybe as May
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.String
open import Data.Sum
open import Data.Unit
open import Data.Vec as V
open import Function
open import Level
open import Relation.Binary.PropositionalEquality as PropEq

data Name : Set where
    name : String → Name
    unName : ℕ → Name

data AddrSpace : Set where
    addrSpace : ℕ → AddrSpace

data Type : Set where
    int : ℕ → Type
    ptr : Type → AddrSpace → Type
    float : ℕ → Type
    func : (return : Type) → (arguments : List Type) → (variadic : Bool) → Type
    vec : (n : ℕ) → Type → Type
    struct : (packed : Bool) → List Type → Type
    array : ℕ → Type → Type
    named-ref : Name → Type
    metadata : Type

data IntegerPredicate : Set where
    eq ne ugt uge ult ule sgt sge slt sle : IntegerPredicate

data FloatPredicate : Set where
    false oeq ogt oge olt ole one ord ueq ugt uge ult ule une uno true : FloatPredicate

private vec' : Maybe ℕ → Type → Type
vec' = maybe vec id

private Op₂' : ∀ {ℓ ℓ'} {A : Set ℓ} → Op₂ (A → Set ℓ')
Op₂' P Q a = P a → Q a → Q a

data ElSpecType : Set where gep greg : ElSpecType

data ElSpec (P : Type → Set) : ElSpecType → Type → Set where
    ptr   : ∀ {a s n}     → P (int n) → Maybe (ElSpec P gep a) → ElSpec P gep (ptr a s)
    vec   : ∀ {l a n}     → P (int n) → Maybe (ElSpec P gep a) → ElSpec P gep (vec l a)
    array : ∀ {l a n est} → P (int n) → Maybe (ElSpec P est a) → ElSpec P est (array l a)
    struct : ∀ {as p est} → L.Any (Maybe ∘ ElSpec P est) as → ElSpec P est (struct p as)

elSpecType : ∀ {P a est} → ElSpec P est a → Type
elSpecType {_} {ptr a _}   (ptr   _ gs) = maybe elSpecType a gs
elSpecType {_} {vec _ a}   (vec   _ gs) = maybe elSpecType a gs
elSpecType {_} {array _ a} (array _ gs) = maybe elSpecType a gs
elSpecType {_} {struct p []} (struct ())
elSpecType {_} {struct p (a ∷ as)} (struct gsAny) with gsAny
... | here gs = maybe elSpecType (struct p (a ∷ as)) gs
... | there gsAny' = elSpecType {_} {struct p as} (struct gsAny')

data Op P : Type → Set where
    add sub mul shl     : ∀ {l n} (nsw nuw : Bool) → Op₂' P (Op P) (vec' l (int n))
    uDiv sDiv lShr aShr : ∀ {l n} (exact : Bool)   → Op₂' P (Op P) (vec' l (int n))
    and or xor          : ∀ {l n}                  → Op₂' P (Op P) (vec' l (int n))
    fAdd fSub fMul fDiv fRem : ∀ {l n} → Op₂' P (Op P) (vec' l (float n))
    trunc     : ∀ {l m n} → m > n → P (vec' l (int m)) → Op P (vec' l (int n))
    zExt sExt : ∀ {l m n} → m < n → P (vec' l (int m)) → Op P (vec' l (int n))
    fpTrunc : ∀ {l m n} → m > n → P (vec' l (float m)) → Op P (vec' l (float n))
    fpExt   : ∀ {l m n} → m < n → P (vec' l (float m)) → Op P (vec' l (float n))
    ptrToInt : ∀ {l a s n} → P (vec' l (ptr a s)) → Op P (vec' l (int n))
    intToPtr : ∀ {l a s n} → P (vec' l (int n)) → Op P (vec' l (ptr a s))
    bitcast : ∀ {a b} → P a → Op P b -- XXX equal size
    addrSpaceCast : ∀ {l a s t} → P (vec' l (ptr a s)) → Op P (vec' l (ptr a t))
    iCmp : ∀ {l n} → IntegerPredicate
                   → P (vec' l (int n)) → P (vec' l (int n)) → Op P (vec' l (int 1))
    fCmp : ∀ {l n} → FloatPredicate
                   → P (vec' l (float n)) → P (vec' l (float n)) → Op P (vec' l (int 1))
    select : ∀ {l a} → P (vec' l (int 1)) → Op₂' P (Op P) (vec' l a)
    gep : ∀ {l a s} → (inBounds : Bool)
                    → P (vec' l (ptr a s))
                    → (g : ElSpec (P ∘ vec' l) gep (ptr a s))
                    → Op P (vec' l (elSpecType g))
    extractElement : ∀ {l a n} → P (vec l a) → P (int n) → Op P a
    insertElement  : ∀ {l a n} → P (vec l a) → P a → P (int n) → Op P (vec l a)
    shuffleVector  : ∀ {m n a} → P (vec m a) → P (vec m a) → P (vec n (int 32)) → Op P (vec n a)
    extractValue : ∀ {a} → (elSpec : ElSpec P greg a) → P a → Op P (elSpecType elSpec)
    insertValue  : ∀ {a} → (elSpec : ElSpec P greg a) → P a → P (elSpecType elSpec) → Op P a

data Constant : Type → Set where
    undef : ∀ {a} → Constant a
    int : ∀ {n} → Vec Bool n → Constant (int n)
    null : ∀ {a s} → Constant (ptr a s)
    struct : ∀ {as} → Maybe Name → (packed : Bool) → L.All Constant as → Constant (struct packed as)
    array : ∀ {a} → (xs : List (Constant a)) → Constant (array (length xs) a)
    vec : ∀ {a} → (xs : List⁺ (Constant a)) → Constant (vec (L⁺.length xs) a)
    --blockAddress : (fn blk : Name) → Constant _
    globalRef : ∀ {a s} → Name → Constant (ptr a s)
    op : ∀ {a} → Op Constant a → Constant a

data Operand (as : List (Maybe Type)) : Type → Set where
    localRef : ∀ {a} → just a ⟨ L.Any ∘ _≡_ ⟩ as → Operand as a
    constant : ∀ {a} → Constant a    → Operand as a

data Instruction (as : List (Maybe Type)) : Maybe Type → Set where
    op : ∀ {a} → Op (Operand as) a → Instruction as (just a)

data Terminator : Maybe Type → List (Maybe Type) → ℕ → Set where
    ret : ∀ {as} → (xs : Maybe (∃ (Operand as))) → Terminator (May.map proj₁ xs) as 0
    switch : ∀ {as am n} → (s : ∃ (Operand as ∘ int)) → (f : Vec Bool (proj₁ s) → Fin n) → Terminator am as n
    unreachable : ∀ {as am} → Terminator am as 0
