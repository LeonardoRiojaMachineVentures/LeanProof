import data.nat.prime
-- import the theorems you want to use
import tactic.linarith
-- import the previous line to use tactics you want

open nat
-- use natural numbers


theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, prime p :=
--for any natural number n you pick, there exists a natural number p, which is prime
begin
  intro N,
-- assume the N exist

  let M := fact N + 1,
  let p := min_fac M,
-- M and P are are not necessary to be strict
-- min_fac is the lowest factor of M
-- fact is factorial


  have pp : prime p :=
-- pp is the statement that p is prime

  begin
-- all proof are between begin and end
    refine min_fac_prime _,
    have : fact N > 0 := fact_pos N,
    linarith,
	-- use tactic called from linarith
  end,
  use p,
	
  split,
	-- split says you will prove this in steps
	-- first step is "by_contradiction" and "exact"
	
  { by_contradiction,
    have h₁ : p ∣ fact N + 1 := min_fac_dvd M,
    have h₂ : p ∣ fact N := (prime.dvd_fact pp).mpr (le_of_not_ge a),
    have h : p ∣ 1 := (nat.dvd_add_right h₂).mp h₁,
    exact prime.not_dvd_one pp h, },
  { exact pp, },
end
