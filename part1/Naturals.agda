module plfa.part1.Naturals where

import Relation.Binary.PropositionalEquality as Eq

-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)

open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- 'refl' - the name for evidence that two terms are equal

-- Agda uses underbars to indicate where terms appear in
-- infix or mixfix operators:
--
-- * _≡_ and _≡⟨⟩_ -- infix
-- * begin_        -- prefix
-- * _∎            -- postfix

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- The following pragma tells Agda that ℕ corresponds to the
-- natural numbers, and hence one is permitted to type 0 as
-- shorthand for 'zero,' 1 as shorthand for 'suc zero'. It also
-- enables a more efficient internal representation of naturals
-- using the Haskell type for arbitrary-precision integers.

{-# BUILTIN NATURAL ℕ #-}

-- Operations on naturals are recursive functions

-- The empty braces are called a hole,
-- and 0 is a number used for referring to the hole

-------------------------------------------------------------
-- Workflow & hotkeys:
-------------------------------------------------------------
-- C-c C-l   - load the current file
-- C-c C-f   - moves to the next hole
-- C-c C-b   - moves to the previous hole
-- C-c C-,   - displays information on the required
--             type of the hole and available free vars
-- C-c C-c   - case split on a variable
-- C-c C-SPC - give to the hole at point an expression in it
-- C-c C-r   - solve the case trivially (refine)
-- gd        - go to definition (custom key binding)
-------------------------------------------------------------

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

-- It works because addition of larger numbers is defined in
-- terms of addition of smaller numbers. Such a definition is
-- called well founded.

-- 0       + n  ≡  n
-- (1 + m) + n  ≡  1 + (m + n)

-- We write '=' for definitions, while we write '≡' for
-- assertions that two already defined things are the same.

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

-- In fact, both proofs are longer than need be, and Agda is
-- satisfied with the following:

_ : 2 + 3 ≡ 5
_ = refl

-- Agda knows how to compute the value of 2 + 3, and so can
-- immediately check it is the same as 5. A binary relation is
-- said to be reflexive if every value relates to itself.
-- Evidence that a value is equal to itself is written 'refl'.

-- ^ 'refl' is defined almost the
-- same way as 'eq_relf' in Coq

-- Excercise:

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    7
  ∎

-- Multiplication

_*_ : ℕ → ℕ → ℕ
zero    * n = zero
(suc m) * n = n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

-- Exercise:

_^_ : ℕ → ℕ → ℕ
m ^ zero    = suc zero
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
   3 * (3 ^ 3)
  ≡⟨⟩
   3 * (3 * (3 ^ 2))
  ≡⟨⟩
   3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
   81
  ∎

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

-- Precedence

infixl 6  _+_  _∸_
infixl 7  _*_

-- Application binds more tightly than
-- (or has precedence over) any operator

-- Currying _

-- ℕ → ℕ → ℕ stands for ℕ → (ℕ → ℕ)

-- and

-- _+_ 2 3 stands for (_+_ 2) 3.

-- Writing definitions interactively

_+₁_ : ℕ → ℕ → ℕ
zero +₁ n = n
suc m +₁ n = suc (m +₁ n)

-- Exercise

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ O
inc (x O) = x I
inc (x I) = inc x O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = {!!}

to : ℕ → Bin
to zero    = ⟨⟩ O
to (suc m) = (to m) I


_ : to 12 ≡ ⟨⟩ I O I I
_ = {!!}

from : Bin → ℕ
from ⟨⟩    = 0
from (x O) = from x
from (x I) = suc (from x)

_ : from (⟨⟩ I O I I) ≡ 12
_ = {!!}
