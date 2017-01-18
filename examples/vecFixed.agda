module vecFixed where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

data Vec (A : Set) : ℕ -> Set where
  vnil : Vec A 0
  vcons : A -> {n : ℕ} -> (v : Vec A n) -> Vec A (suc n)


data ℕ_R : ℕ -> ℕ -> Set where
  O_R : ℕ_R 0 0
  suc_R : {n1 n2 : ℕ} -> (n_R : ℕ_R n1 n2) -> ℕ_R (suc n1) (suc n2)

data True : Set where
  I : True

data False : Set where

ℕ_RD : ℕ -> ℕ -> Set
ℕ_RD 0 0 = True
ℕ_RD (suc n1) (suc n2) = ℕ_RD n1 n2
ℕ_RD _ _ = False


O_RD : ℕ_RD 0 0
O_RD = I

suc_RD : {n1 n2 : ℕ} -> (n_R : ℕ_RD n1 n2) -> ℕ_RD (suc n1) (suc n2)
suc_RD n_R = n_R

--ℕ_R n1 n2 = n1 ≡ n2



-- deductive style, nat is inductive
-- it seems that Agda interprets it as strucutrally recursive on N_R
Vec_R : {A1 A2 : Set} -> (A_R : A1 -> A2 -> Set) -> {n1 n2 : ℕ} -> (n_R : ℕ_R n1 n2) -> (v1 : Vec A1 n1) -> (v2 : Vec A2 n2) -> Set
Vec_R A_R O_R (vnil) (vnil) = True
Vec_R A_R (suc_R n_R) (vcons a1 v1) (vcons a2 v2) = False

--
Vec_RND : {A1 A2 : Set} -> (A_R : A1 -> A2 -> Set) -> {n1 n2 : ℕ} -> (n_R : ℕ_RD n1 n2) -> (v1 : Vec A1 n1) -> (v2 : Vec A2 n2) -> Set
Vec_RND A_R O_RD (vnil) (vnil) = True
Vec_RND A_R _ (vcons a1 v1) (vcons a2 v2) = True
Vec_RND A_R _ _ _ = False

-- Vec_RND A_R (suc_RD n_R) (vcons a1 v1) (vcons a2 v2) = False


-- Vec-RDed : {nat1 : Set} {nat2 : Set} (natR : nat1 -> nat2 -> Set)
--             {O1 : nat1} {O2 : nat2} (OR : natR O1 O2)
--             {n1 : nat1} -> {n2 : nat2} -> natR n1 n2 ->
--             Vec nat1 O1 n1 -> Vec nat2 O2 n2 -> Set

-- Vec-RDed nat1 nat 2 natR O1 O2 OR O1 O2 OR vnil vnil = ⊤
--Repeated variables in pattern: O1 O2 OR

--Vec-RDed natR OR OR' vnil vnil = OR ≡ OR'

