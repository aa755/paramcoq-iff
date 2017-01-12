module PFF where

open import Data.Unit
open import Relation.Binary.PropositionalEquality

data Vec (nat : Set) (O : nat) : nat -> Set where
  vnil : Vec nat O O

data Vec-RInd {nat1 : Set} {nat2 : Set} (natR : nat1 -> nat2 -> Set)
             {O1 : nat1} {O2 : nat2} (OR : natR O1 O2) :
             {n1 : nat1} -> {n2 : nat2} -> natR n1 n2 ->
             Vec nat1 O1 n1 -> Vec nat2 O2 n2 -> Set where
  vnil_R : Vec-RInd natR OR OR vnil vnil

Vec-RDed : {nat1 : Set} {nat2 : Set} (natR : nat1 -> nat2 -> Set)
             {O1 : nat1} {O2 : nat2} (OR : natR O1 O2)
             {n1 : nat1} -> {n2 : nat2} -> natR n1 n2 ->
             Vec nat1 O1 n1 -> Vec nat2 O2 n2 -> Set

Vec-RDed nat1 nat 2 natR O1 O2 OR O1 O2 OR vnil vnil = ⊤
--Repeated variables in pattern: O1 O2 OR

--Vec-RDed natR OR OR' vnil vnil = OR ≡ OR'

