import Mathlib

/-
# IMO 1998 Q3

For any positive integer `n`, let `d(n)` denote the number of positive divisors
of `n` (including `1` and `n` itself). Determine all positive integers `k` such that
`d(n^2)/d(n) = k` for some `n`.

The answer to this problem is every odd number, so to formalize this in Lean,
we must prove that if a `k` satisfies `d(n^2)/d(n) = k` for some `n`, then
`k` is odd, and also if `k` is odd, then it satisfies `d(n^2)/d(n) = k` for some `n`.
-/

namespace Imo1998Q3

-- Define `d(n)`, the function counting the number of positive divisors of `n`.
def d (n : ℕ) : ℕ := (Nat.divisors n).card

-- `dComputed` takes in `n` and produces the product of `n`'s
-- factorization's powers plus one.
-- We want to argue later that `dComputed(n) = d(n)`.
def dComputed (n : ℕ) : ℕ :=
  if n = 0 then 0
  else n.factorization.prod (fun _ k ↦ k + 1)

-- Proof that `d` is multiplicative.
lemma d_multiplicative (m n : ℕ) (h : Nat.Coprime m n) :
    d (m * n) = d m * d n := by
  exact Nat.Coprime.card_divisors_mul h

-- Proof that `d(pᵏ) = k + 1` for `p` prime.
lemma prime_power_divisors {p k : ℕ} (hp : p.Prime) :
    d (p ^ k) = k + 1 := by
  simp [d]
  rw [Nat.divisors_prime_pow hp]
  rw [Finset.card_map]
  simp

-- Proof that `dComputed n = d n`, using the fact that `d` is multiplicative
-- and `d(pᵏ) = k + 1` for `p` prime.
lemma d_eq_dComputed (n : ℕ) : d n = dComputed n := by
  rcases eq_or_ne n 0 with rfl | hn
  { simp [d, dComputed] }
  { rw [dComputed, if_neg hn]
    rw [Nat.multiplicative_factorization d d_multiplicative (by simp [d]) hn]
    refine Finset.prod_congr ?_ ?_
    { rfl }
    { intro p hp
      have hpprime : p.Prime := by
        apply Nat.prime_of_mem_primeFactors
        exact hp
      exact prime_power_divisors hpprime } }

-- Proof that `d(n²) = ∏ᵢ(2kᵢ + 1)` for `n = ∏ᵢpᵢᵏᵢ` (prime factorization).
lemma d_n2 (n : ℕ) (hn : n ≠ 0) : d (n ^ 2) =
          n.factorization.prod (fun _ k ↦ 2 * k + 1) := by
  rw [d_eq_dComputed, dComputed]
  rw [if_neg (pow_ne_zero 2 hn)]
  rw [Nat.factorization_pow]
  refine Finset.prod_congr ?_ ?_
  { aesop }
  { aesop }

-- Proof that if every number in a list is odd, the product of the list is odd.
lemma list_prod_odd : ∀ (l : List ℕ), (∀ x ∈ l, Odd x) → Odd l.prod := by
  intro l
  induction l with
  | nil => simp
  | cons head tail ih =>
      intro hallodd2
      rw [List.prod_cons]
      refine Odd.mul ?_ ?_
      { apply hallodd2
        exact @List.mem_cons_self _ head tail }
      { apply ih
        intro x hx
        apply hallodd2
        exact List.mem_cons_of_mem head hx }

-- We begin by first proving that every value of `k` must be an odd number.
theorem k_is_odd (k : ℕ)
                 (h : ∃ n : ℕ, n ≠ 0 ∧ d (n ^ 2) = k * d n) :
                 (k % 2 = 1) := by
  obtain ⟨n, hn⟩ := h
  let nfac := n.factorization
  have hprime : ∀ p ∈ nfac.support, Nat.Prime p := by aesop
  have hnfac := Nat.eq_factorization_iff hn.left hprime
  have hneqnfac : (nfac.prod fun x1 x2 ↦ x1 ^ x2) = n := hnfac.mp (by rfl)
  have hdn2odd : (d (n ^ 2)) % 2 = 1 := by
    have hn2eqnfac : (nfac.prod fun p k ↦ p ^ (2 * k)) = n ^ 2 := calc
      (nfac.prod fun p k ↦ p ^ (2 * k))
      _ = (nfac.prod fun p k ↦ (p ^ k) ^ 2) := by
          apply Finset.prod_congr rfl
          intro p _
          simp
          rw [pow_mul']
      _ = (nfac.prod fun p k ↦ p ^ k) ^ 2 := by
          unfold Finsupp.prod
          simp
          rw [Finset.prod_pow]
      _ = n ^ 2 := by
          rw [hneqnfac]
    have hd : d (n ^ 2) = (nfac.prod fun _ x2 ↦ ((2 * x2) + 1)) := by
      exact d_n2 n hn.left
    let powers := nfac.support.toList.map (fun x ↦ 2 * nfac x + 1)
    have hallodd : (∀ i ∈ powers, Odd i) := by
      intro i hi
      rw [Nat.odd_iff]
      rw [List.mem_map] at hi
      obtain ⟨p, _, rfl⟩ := hi
      simp
    have hoddmul : (Odd (nfac.prod fun _ x2 ↦ ((2 * x2) + 1))) := by
      have h_eq : (nfac.prod fun _ x2 ↦ ((2 * x2) + 1)) = powers.prod := by
        dsimp [powers]
        rw [Finsupp.prod]
        rw [Finset.prod_eq_multiset_prod]
        aesop
      rw [h_eq]
      exact list_prod_odd powers hallodd
    rw [hd]
    exact Nat.odd_iff.mp hoddmul
  rw [hn.right] at hdn2odd
  have hodd : Odd (k * (d n)) := by grind
  have hkodd : Odd k := (Nat.odd_mul.mp hodd).left
  exact Nat.odd_iff.mp hkodd

lemma exists_distinct_primes (t n : ℕ)
                             (primes : List ℕ)
                             (hallprime : ∀ p ∈ primes, Nat.Prime p) :
                             (∃ l : List ℕ,
                                (∀ i ∈ l, Nat.Prime i ∧
                                         i ∉ primes ∧
                                         Nat.Coprime i n) ∧
                                         List.length l = t ∧
                                         List.Nodup l) := by
  sorry

lemma telescoping_product_identity (t j : ℕ) (hj : j ≠ 0) :
                              let num (i : ℕ) := (2 * (2^i * j - 1) + 1 : ℚ)
                              let den (i : ℕ) := ((2^i * j - 1) + 1 : ℚ)
                              (List.range t).map (fun i ↦ num i / den i) |>.prod =
                              (2^t * j - 1 : ℚ) / j := by
  sorry

lemma repeated_multiplicity_of_d : ∀ (l : List ℕ)
                    (_hcoprime : l.Pairwise Nat.Coprime),
                    d (l.prod) = (List.map (fun i ↦ d i) l).prod := by
  intro l
  induction l with
  | nil => simp [d]
  | cons head tail ih =>
      intro hcoprime
      rw [List.pairwise_cons] at hcoprime
      obtain ⟨hhead, htail⟩ := hcoprime
      simp only [List.prod_cons, List.map_cons]
      rw [d_multiplicative]
      { rw [ih]
        exact htail }
      { apply Nat.coprime_list_prod_right_iff.mpr
        intro n hnintail
        exact hhead n hnintail }

-- We then prove that every odd number satisifies the equation.
theorem odd_k_satisfies (k : ℕ)
                        (hkodd : k % 2 = 1) :
                        (∃ n : ℕ, n ≠ 0 ∧ d (n ^ 2) = k * d n) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with (_ | k_minus_1)
      { contradiction }
      { by_cases hk1 : k_minus_1 = 0
        { simp
          use 0
          rw [hk1]
          simp }
        { let kk := k_minus_1 + 1
          let t := (kk + 1).factorization 2
          let j := (kk + 1) / (2 ^ t)
          have h_div : 2 ^ t ∣ (kk + 1) := by
            exact Nat.ordProj_dvd (kk + 1) 2
          have hjodd : Odd j := by
            have hordcompl : j = ordCompl[2] (kk + 1) := by
              rfl
            have htwondvd := @Nat.not_dvd_ordCompl
                              (kk + 1) _ (Nat.prime_two) (by grind)
            have htwondvdj : ¬ 2 ∣ j := by
              rw [hordcompl]
              exact htwondvd
            exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp htwondvdj)
          have hjltkk : j < kk := by
            have hkkge2 : kk ≥ 2 := by grind
            have h2le2t : 2 ≤ 2 ^ t := by
              have htpos : 0 < t := by
                exact Nat.Prime.factorization_pos_of_dvd (by decide) (by simp) (by grind)
              refine Nat.le_self_pow ?_ 2
              linarith
            have hkkeqjt : kk + 1 = j * 2 ^ t := by
              exact Nat.eq_mul_of_div_eq_left h_div rfl
            have hbound : kk + 1 ≥ 2 * j := calc
              kk + 1 = j * 2^t := hkkeqjt
              _      ≥ j * 2   := Nat.mul_le_mul_left j h2le2t
              _      = 2 * j   := mul_comm _ _
            omega
          have hjworks := ih j hjltkk (Nat.odd_iff.mp hjodd)
          obtain ⟨nⱼ, hnⱼ⟩ := hjworks
          let kfac := kk.factorization
          obtain ⟨ps, hps⟩ := exists_distinct_primes t nⱼ kfac.support.toList (by aesop)
          let exps := (List.range t).map (fun i ↦ 2^i * j - 1)
          let x := ((ps.zip exps).map (fun (p, e) ↦ p ^ e)).prod
          have hxnⱼcoprime : Nat.Coprime x nⱼ := by
            sorry
          have hxneq0 : x ≠ 0 := by
            dsimp only [x]
            apply List.prod_ne_zero
            apply mt List.mem_map.mp
            simp only [not_exists, not_and]
            intro (p, k) hpk
            apply pow_ne_zero
            apply Nat.Prime.ne_zero
            exact (hps.left (p, k).1 (List.of_mem_zip hpk).left).left
          have hneqdx : d x = ((List.range t).map (fun i ↦ (2 ^ i) * j)).prod := by
            dsimp only [x]
            rw [repeated_multiplicity_of_d (List.map (fun x ↦ x.1 ^ x.2) (ps.zip exps))]
            { apply congr_arg List.prod
              apply List.ext_get
              { rw [List.length_map, List.length_map, List.length_map]
                rw [List.length_zip, min_eq_left]
                { rw [hps.right.left]
                  simp }
                { rw [hps.right.left]
                  dsimp [exps]
                  simp } }
              { intro n hind1 hind2
                have hnltexpslen : n < exps.length := by
                  dsimp [exps]
                  have hleneq : exps.length =
                            (List.map (fun i ↦ 2 ^ i * j) (List.range t)).length := by
                    rw [List.length_map, List.length_map]
                  rw [hleneq]
                  exact hind2
                simp
                have hexpsn : exps[n]'hnltexpslen = 2 ^ n * j - 1 := by
                  grind
                rw [hexpsn]
                have hnltpslen : n < ps.length := by
                  have hleneq2 :
                    (List.map (fun i ↦ d i) (List.map (fun x ↦ x.1 ^ x.2) (ps.zip exps))).length
                     = ps.length := by
                    rw [List.length_map, List.length_map]
                    rw [List.length_zip, min_eq_left]
                    rw [hps.right.left]
                    dsimp [exps]
                    simp
                  rw [hleneq2.symm]
                  exact hind1
                have hpsnprime : Nat.Prime (ps[n]'hnltpslen) := by
                  have hpsninps : ps[n] ∈ ps := by
                    exact List.get_mem ps ⟨n, hnltpslen⟩
                  exact (hps.left ps[n] hpsninps).left
                have hclose := @prime_power_divisors ps[n] (2 ^ n * j - 1) hpsnprime
                rw [hclose]
                rw [Nat.sub_add_cancel]
                apply one_le_mul_of_one_le_of_one_le
                { exact Nat.one_le_two_pow }
                { exact hjodd.pos } } }
            { apply List.Nodup.pairwise_of_forall_ne
              { sorry }
              { intro a ha b hb haneqb
                rw [List.mem_map] at ha
                obtain ⟨⟨p₁, k₁⟩, ha'⟩ := ha
                rw [List.mem_map] at hb
                obtain ⟨⟨p₂, k₂⟩, hb'⟩ := hb
                simp at ha' hb'
                have hp₁inps : p₁ ∈ ps := by
                    exact (List.of_mem_zip ha'.left).left
                have hp₁prime : Nat.Prime p₁ := by
                  exact ((hps.left p₁) hp₁inps).left
                have hp₂inps : p₂ ∈ ps := by
                    exact (List.of_mem_zip hb'.left).left
                have hp₂prime : Nat.Prime p₂ := by
                  exact ((hps.left p₂) hp₂inps).left
                rw [ha'.right.symm, hb'.right.symm]
                apply Nat.coprime_pow_primes k₁ k₂ hp₁prime hp₂prime
                have hpowsneq : p₁ ^ k₁ ≠ p₂ ^ k₂ := by
                  rw [ha'.right, hb'.right]
                  exact haneqb
                intro hcon
                have hp₁k₁zip : (p₁, k₁) ∈ ps.zip exps := ha'.left
                have hp₂k₂zip : (p₂, k₂) ∈ ps.zip exps := hb'.left
                have h_k_eq : k₁ = k₂ := by
                  have h_nodup : ps.Nodup := hps.right.right
                  have h_lookup1 : List.lookup p₁ (ps.zip exps) = some k₁ := by
                    sorry
                  have h_lookup2 : List.lookup p₂ (ps.zip exps) = some k₂ := by
                    sorry
                  rw [hcon] at h_lookup1
                  rw [h_lookup1] at h_lookup2
                  injection h_lookup2
                subst hcon h_k_eq
                contradiction }
               }
          have hneqdx2 : d (x ^ 2) = ((List.range t).map (fun i ↦ (2 ^ (i + 1) * j - 1))).prod := by
            dsimp only [x]
            sorry
          have hdvd : d (x ^ 2) / d x = ((2 ^ t) * j - 1) / j := calc
                d (x ^ 2) / d x
                _ = (((List.range t).map (fun i ↦ (2 ^ (i + 1)) * j - 1)).prod) /
                    ((List.range t).map (fun i ↦ (2 ^ i) * j)).prod := by
                  rw [hneqdx2, hneqdx]
                _ = ((List.range t).map (fun i ↦ ((2 ^ (i + 1)) * j - 1)
                                                / ((2 ^ i) * j))).prod := by
                  sorry
                _ = ((2 ^ t) * j - 1) / j := by
                  sorry
          use nⱼ * x
          have hdx2 : d ((nⱼ * x) ^ 2) = (d (nⱼ ^ 2)) * (d (x ^ 2)) := by
            sorry
          have hdx : d (nⱼ * x) = (d nⱼ) * (d x) := by
            sorry
          rw [hdx2, hdx]
          have hkj : k_minus_1 + 1 = (2 ^ t) * j - 1 := by
            simp [j, kk]
            have hkj2 : 2 ^ t * ((k_minus_1 + 2) / 2 ^ t) =
                          (k_minus_1 + 1 + 1) := by
              apply Nat.mul_div_cancel'
              exact h_div
            rw [hkj2]
            simp
          rw [hkj]
          have hnⱼprodxneq0 : nⱼ * x ≠ 0 := by
            rw [mul_ne_zero_iff]
            exact And.intro hnⱼ.left hxneq0
          refine ⟨hnⱼprodxneq0, ?_⟩
          have halmost : d (x ^ 2) * j = (2 ^ t * j - 1) * (d x) := by
            sorry
          sorry
        }
      }

-- Finally, we put it all together.
theorem imo1998_q3 (k : ℕ) :
                   (k % 2 = 1 ↔ ∃ n : ℕ, n ≠ 0 ∧ d (n ^ 2) = k * d n) := by
  exact Iff.intro (odd_k_satisfies k) (k_is_odd k)

end Imo1998Q3
