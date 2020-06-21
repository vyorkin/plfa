module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- z≤n, s≤s       - constructor names (with no spaces)
-- zero ≤ n       - types (with spaces) indexed by
-- suc m ≤ suc n  - 2 naturals: m and n
-- "-----------"  - is just a comment (to make it look
--                  like math notation for inference rule)

data _≤_ : ℕ → ℕ → Set where

  -- base case
  z≤n : ∀ {n : ℕ}
        -------------
      → zero ≤ n

  -- inductive case
  s≤s : ∀ {m n : ℕ}
      → m ≤ n
        -------------
      → suc m ≤ suc n

-- Base case: for all naturals n, the constructor
-- z≤n produces evidence that zero ≤ n holds.

-- Inductive case: for all naturals m and n,
-- the constructor s≤s takes evidence that m ≤ n
-- holds into evidence that suc m ≤ suc n holds.

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

--   z≤n -----
--       0 ≤ 2
--  s≤s -------
--       1 ≤ 3
-- s≤s ---------
--       2 ≤ 4
