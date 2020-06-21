module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)

  -- A relation is said to be a congruence for
  -- a given function if it is preserved by applying that function

  -- If e is evidence that x ≡ y,
  -- then cong f e is evidence that f x ≡ f y,
  -- for any function f

  -- The correspondence between proof by induction and
  -- definition by recursion is one of the most appealing
  -- aspects of Agda

  -- cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
  --           ^- suc               ^- (m + n) + p ≡ m + (n + p)
  -- ----------------------------------------------------------- (=> implies)
  -- suc ((m + n) + p) ≡ suc (m + (n + p))

  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))

  -- cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
  -- cong f refl = refl

  ≡⟨⟩
    suc m + (n + p)
  ∎

+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    2 + (n + p)
  ∎
  where
  +-assoc-1 : ∀ (n p : ℕ) -> (1 + n) + p ≡ 1 + (n + p)
  +-assoc-1 n p =
    begin
      (1 + n) + p
    ≡⟨⟩
      suc (0 + n) + p
    ≡⟨⟩
      suc ((0 + n) + p)
    ≡⟨ cong suc (+-assoc-0 n p) ⟩
      suc (0 + (n + p))
    ≡⟨⟩
      1 + (n + p)
    ∎
    where
      +-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
      +-assoc-0 n p =
        begin
          (0 + n) + p
        ≡⟨⟩
          n + p
        ≡⟨⟩
          0 + (n + p)
        ∎

+-identityᴿ : ∀ (m : ℕ) → m + zero ≡ m
+-identityᴿ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityᴿ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityᴿ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityᴿ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- Rearranging

-- We can apply associativity to
-- rearrange parentheses however we like

+-rearrange
  : ∀ (m n p q : ℕ)
  → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))

  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)

  -- +-assoc : (m + n) + p ≡ m + (n + p)
  -- sym (+-assoc) : m + (n + p) ≡ (m + n) + p

  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

-- Associativity with rewrite

-- Rewriting avoids not only chains of
-- equations but also the need to invoke cong

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p                           = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

+-identity' : ∀ (n : ℕ) → n + zero ≡ n
+-identity' zero = refl
+-identity' (suc n) rewrite +-identity' n = refl

+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-identity' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl

-- Building proofs interactively

+-assoc'' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc'' zero n p = refl
+-assoc'' (suc m) n p rewrite +-assoc'' m n p = refl

-- Exercise

-- Note:
-- sym -- rewrites the left side of the Goal

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p rewrite
    +-assoc'' m n p
  | +-suc n (m + p)
  | +-swap m n p
  = refl

-- (suc m + n) * p ≡ suc m * p + n * p
-- p + (m * p + n * p) ≡ p + m * p + n * p

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite
    *-distrib-+ m n p
  | sym (+-assoc p (m * p) (n * p))
  = refl

-- (n + m * n) * p ≡ n * p + m * (n * p)

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite
    *-distrib-+ n (m * n) p
  | *-assoc m n p
  = refl
