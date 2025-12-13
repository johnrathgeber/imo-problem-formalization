import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors

/-
# IMO 1998 Q3

For any positive integer `n`, let `d(n)` denote the number of positive divisors
of `n`. Determine all positive integers `k` such that
`d(n^2)/d(n) = k` for some `n`.

The answer to this problem is every odd number, so to formalize this,
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
  { exact Finsupp.support_smul_eq two_ne_zero }
  { simp }

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
  have hprime : ∀ p ∈ nfac.support, Nat.Prime p := by
    intro p hp
    dsimp [nfac] at hp
    exact Nat.prime_of_mem_primeFactors hp
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
        simp
      rw [h_eq]
      exact list_prod_odd powers hallodd
    rw [hd]
    exact Nat.odd_iff.mp hoddmul
  rw [hn.right] at hdn2odd
  have hodd : Odd (k * (d n)) := Nat.odd_iff.mpr hdn2odd
  have hkodd : Odd k := (Nat.odd_mul.mp hodd).left
  exact Nat.odd_iff.mp hkodd

-- Proof that we can pick `t` new and distinct primes given a list of `t` primes.
lemma exists_distinct_primes (t n : ℕ)
                             (hnneq0 : n ≠ 0)
                             (primes : List ℕ) :
                             (∃ l : List ℕ,
                                (∀ i ∈ l, Nat.Prime i ∧
                                         i ∉ primes ∧
                                         Nat.Coprime i n) ∧
                                         List.length l = t ∧
                                         List.Nodup l) := by
  induction t with
  | zero =>
      use []
      simp
  | succ t ih =>
      obtain ⟨l, props⟩ := ih
      let existing_numbers := (primes ++ l ++ [n])
      have he : existing_numbers ≠ [] := by
        dsimp [existing_numbers]
        simp
      let bound := existing_numbers.max he
      have hexists := Nat.exists_infinite_primes (bound + 1)
      obtain ⟨new, hnew⟩ := hexists
      have hnewgtbound : new > bound := Nat.add_one_le_iff.mp hnew.left
      have hnewprime : Nat.Prime new := hnew.right
      use l ++ [new]
      apply And.intro
      { intro i hiinlist
        simp at hiinlist
        cases hiinlist with
        | inl h => exact props.left i h
        | inr h =>
            rw [h]
            have hnewnotinprimes : new ∉ primes := by
              intro hin
              have hnewlebound : new ≤ bound := by
                have hnewinexisting : new ∈ existing_numbers := by
                  apply List.mem_append_left
                  apply List.mem_append_left
                  exact hin
                have hnewlemax := List.le_max_of_mem
                                (l := existing_numbers) hnewinexisting
                simp [bound]
                exact hnewlemax
              linarith [hnewlebound, hnewgtbound]
            have hnewcoprimen : new.Coprime n := by
              refine Nat.coprime_of_lt_prime hnneq0 ?_ hnewprime
              have hnleqbound : n ≤ bound := by
                simp [bound]
                have hninexisting : n ∈ existing_numbers := by
                  apply List.mem_append_right
                  exact List.mem_singleton_self n
                exact List.le_max_of_mem hninexisting
              linarith
            exact And.intro hnewprime (And.intro hnewnotinprimes hnewcoprimen) }
      { apply And.intro
        { rw [List.length_append]
          rw [props.right.left, List.length_singleton] }
        { have halmost : (new :: l).Nodup := by
            refine List.nodup_cons.mpr (And.intro ?_ props.right.right)
            intro hnewinl
            have hnewinexisting : new ∈ existing_numbers := by
              simp [existing_numbers]
              right
              left
              exact hnewinl
            have hle : new ≤ bound := by
              simp [bound]
              exact List.le_max_of_mem hnewinexisting
            linarith
          rw [List.singleton_append.symm] at halmost
          exact List.nodup_append_comm.mp halmost } }

-- Proof that `d(∏ᵢxᵢ) = ∏ᵢd(xᵢ)` for coprime `xᵢ`'s (repeated mulitiplicity).
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

-- Proof that `d(∏ᵢpᵢᵏᵢ) = ∏ᵢ(kᵢ + 1)`. Intuitively, we know `ps` and `exps` form
-- a factorization of `x`, but Lean doesn't know this, so we have to give this lemma
-- all the properties of `x`'s factorization without explicitly saying so.
lemma d_of_factorization (t : ℕ) : ∀ (ps : List ℕ) (exps : List ℕ),
    ps.length = exps.length → exps.length = t → (∀ i ∈ ps, Nat.Prime i)
    → List.Nodup ps → List.Nodup exps
    → d ((ps.zip exps).map (fun (p, e) ↦ p ^ e)).prod =
          (List.map (fun i ↦ i + 1) exps).prod := by
    intro ps exps hlen hlent hallprime hpsnodups hexpsnodups
    rw [repeated_multiplicity_of_d (List.map (fun x ↦ x.1 ^ x.2) (ps.zip exps))]
    { apply congr_arg List.prod
      apply List.ext_get
      { rw [List.length_map, List.length_map, List.length_map]
        rw [List.length_zip, min_eq_left]
        { exact hlen }
        { simp [hlen] } }
      { intro n hind1 hind2
        have hnltexpslen : n < exps.length := by
          rw [List.length_map] at hind2
          exact hind2
        simp
        have hnltpslen : n < ps.length := by
          rw [List.length_map, List.length_map] at hind1
          exact List.lt_length_left_of_zip hind1
        have hpsnprime : Nat.Prime (ps[n]'hnltpslen) := by
          have hpsninps : ps[n] ∈ ps := by
            exact List.get_mem ps ⟨n, hnltpslen⟩
          exact hallprime ps[n] hpsninps
        exact @prime_power_divisors ps[n] exps[n] hpsnprime } }
    { apply List.Nodup.pairwise_of_forall_ne
      { rw [List.nodup_iff_pairwise_ne]
        rw [List.pairwise_map]
        refine List.Pairwise.imp_of_mem (R := Ne) (fun {a b} ha hb hneq => ?_) ?_
        { intro hpoweq
          obtain ⟨p₁, k₁⟩ := a
          obtain ⟨p₂, k₂⟩ := b
          dsimp at hpoweq hneq
          have hexistsidx1 := List.mem_iff_getElem?.mp ha
          have hexistsidx2 := List.mem_iff_getElem?.mp hb
          obtain ⟨i₁, hi₁⟩ := hexistsidx1
          obtain ⟨i₂, hi₂⟩ := hexistsidx2
          rw [List.getElem?_eq_some_iff] at hi₁ hi₂
          obtain ⟨h1, h11⟩ := hi₁
          obtain ⟨h2, h22⟩ := hi₂
          rw [List.getElem_zip] at h11
          rw [List.getElem_zip] at h22
          have hi₁valid : i₁ < ps.length := by
            exact List.lt_length_left_of_zip h1
          have hi₂valid : i₂ < ps.length := by
            exact List.lt_length_left_of_zip h2
          have hi₁valide : i₁ < exps.length := by
            exact List.lt_length_right_of_zip h1
          have hi₂valide : i₂ < exps.length := by
            exact List.lt_length_right_of_zip h2
          have hp₁prime : Nat.Prime p₁ := by
            refine ((hallprime p₁) ?_)
            apply List.mem_of_getElem
            exact (congrArg Prod.fst h11)
          have hp₂prime : Nat.Prime p₂ := by
            refine ((hallprime p₂) ?_)
            apply List.mem_of_getElem
            exact (congrArg Prod.fst h22)
          have hpsi₁eqp₁ : ps[i₁] = p₁ := (Prod.mk_inj.mp h11).left
          have hpsi₂eqp₂ : ps[i₂] = p₂ := (Prod.mk_inj.mp h22).left
          have hexpsi₁eqk₁ : exps[i₁] = k₁ := (Prod.mk_inj.mp h11).right
          have hexpsi₂eqk₂ : exps[i₂] = k₂ := (Prod.mk_inj.mp h22).right
          have hp₁eqp₂ : p₁ = p₂ := by
            by_contra hcon
            have hcoprime := Nat.coprime_pow_primes k₁ k₂ hp₁prime hp₂prime hcon
            rw [hpoweq] at hcoprime
            have hvalone : p₂ ^ k₂ = 1 := (Nat.coprime_self (p₂ ^ k₂)).mp hcoprime
            have hk₂zero : k₂ = 0 := by
              have hor := Nat.pow_eq_one.mp hvalone
              cases hor with
              | inl h =>
                  have h1np := Nat.not_prime_one
                  rw [h.symm] at h1np
                  contradiction
              | inr h => exact h
            have hcoprime2 := Nat.coprime_pow_primes k₁ k₂ hp₁prime hp₂prime hcon
            rw [hpoweq.symm] at hcoprime2
            have hvalone2 : p₁ ^ k₁ = 1 := (Nat.coprime_self (p₁ ^ k₁)).mp hcoprime2
            have hk₁zero : k₁ = 0 := by
              have hor := Nat.pow_eq_one.mp hvalone2
              cases hor with
              | inl h =>
                  have h1np := Nat.not_prime_one
                  rw [h.symm] at h1np
                  contradiction
              | inr h => exact h
            have hiseq : i₁ = i₂ := by
              rw [hexpsi₁eqk₁.symm] at hk₁zero
              rw [hexpsi₂eqk₂.symm] at hk₂zero
              have heq_vals : exps[i₁] = exps[i₂] := by rw [hk₁zero, hk₂zero]
              apply (List.Nodup.getElem_inj_iff hexpsnodups).mp heq_vals
            have hcontra : p₁ = p₂ := by
              rw [hpsi₁eqp₁.symm, hpsi₂eqp₂.symm]
              subst hiseq
              rfl
            contradiction
          rw [hpsi₁eqp₁.symm, hpsi₂eqp₂.symm] at hp₁eqp₂
          have hi₁eqi₂ : i₁ = i₂ := by
            exact (List.Nodup.getElem_inj_iff hpsnodups).mp hp₁eqp₂
          have hk₁eqk₂ : k₁ = k₂ := by
            rw [hexpsi₁eqk₁.symm, hexpsi₂eqk₂.symm]
            subst hi₁eqi₂
            rfl
          rw [hpsi₁eqp₁, hpsi₂eqp₂] at hp₁eqp₂
          have hcontra : (p₁, k₁) = (p₂, k₂) :=
            Prod.mk_inj.mpr (And.intro hp₁eqp₂ hk₁eqk₂)
          contradiction }
        { refine List.nodup_iff_pairwise_ne.mp ?_
          apply List.Nodup.of_map Prod.fst
          rw [List.map_fst_zip]
          { exact hpsnodups }
          { simp [hlent, hlen] } } }
      { intro a ha b hb haneqb
        rw [List.mem_map] at ha
        obtain ⟨⟨p₁, k₁⟩, ha'⟩ := ha
        rw [List.mem_map] at hb
        obtain ⟨⟨p₂, k₂⟩, hb'⟩ := hb
        simp at ha' hb'
        have hp₁inps : p₁ ∈ ps := by
            exact (List.of_mem_zip ha'.left).left
        have hp₁prime : Nat.Prime p₁ := by
          exact (hallprime p₁) hp₁inps
        have hp₂inps : p₂ ∈ ps := by
            exact (List.of_mem_zip hb'.left).left
        have hp₂prime : Nat.Prime p₂ := by
          exact (hallprime p₂) hp₂inps
        rw [ha'.right.symm, hb'.right.symm]
        apply Nat.coprime_pow_primes k₁ k₂ hp₁prime hp₂prime
        have hpowsneq : p₁ ^ k₁ ≠ p₂ ^ k₂ := by
          rw [ha'.right, hb'.right]
          exact haneqb
        intro hcon
        have hp₁k₁zip : (p₁, k₁) ∈ ps.zip exps := ha'.left
        have hp₂k₂zip : (p₂, k₂) ∈ ps.zip exps := hb'.left
        have hexistsidx1 := List.mem_iff_getElem?.mp hp₁k₁zip
        have hexistsidx2 := List.mem_iff_getElem?.mp hp₂k₂zip
        obtain ⟨i₁, hi₁⟩ := hexistsidx1
        obtain ⟨i₂, hi₂⟩ := hexistsidx2
        rw [List.getElem?_eq_some_iff] at hi₁ hi₂
        obtain ⟨h3, h33⟩ := hi₁
        obtain ⟨h4, h44⟩ := hi₂
        have hp1idx := List.mem_iff_getElem?.mp hp₁inps
        have hp2idx := List.mem_iff_getElem?.mp hp₂inps
        obtain ⟨j₁, hj₁⟩ := hp1idx
        obtain ⟨j₂, hj₂⟩ := hp2idx
        rw [List.getElem?_eq_some_iff] at hj₁ hj₂
        obtain ⟨h1, h11⟩ := hj₁
        obtain ⟨h2, h22⟩ := hj₂
        have hjeqj : j₁ = j₂ := by
          apply (List.Nodup.getElem_inj_iff hpsnodups).mp
          rw [h11, h22]
          exact hcon
        have hi₁valid : i₁ < ps.length := List.lt_length_left_of_zip h3
        have hi₂valid : i₂ < ps.length := List.lt_length_left_of_zip h4
        have hi₁valid2 : i₁ < exps.length := List.lt_length_right_of_zip h3
        have hi₂valid2 : i₂ < exps.length := List.lt_length_right_of_zip h4
        have hieqi : i₁ = i₂ := by
          have hpsi₁ : ps[i₁]'hi₁valid = p₁ := by
            rw [List.getElem_zip] at h33
            exact (congrArg Prod.fst h33)
          have hpsi₂ : ps[i₂]'hi₂valid = p₂ := by
            rw [List.getElem_zip] at h44
            exact (congrArg Prod.fst h44)
          rw [h11.symm] at hpsi₁
          rw [h22.symm] at hpsi₂
          have hi₁eqj₁ : i₁ = j₁ := by
            exact (List.Nodup.getElem_inj_iff hpsnodups).mp hpsi₁
          have hi₂eqj₂ : i₂ = j₂ := by
            exact (List.Nodup.getElem_inj_iff hpsnodups).mp hpsi₂
          rw [hi₁eqj₁, hi₂eqj₂]
          exact hjeqj
        rw [List.getElem_zip] at h33 h44
        have hei₁eqk₁ : exps[i₁]'hi₁valid2 = k₁ := by
          exact (congrArg Prod.snd h33)
        have hei₂eqk₂ : exps[i₂]'hi₂valid2 = k₂ := by
          exact (congrArg Prod.snd h44)
        have hkeqk : k₁ = k₂ := by
          rw [hei₁eqk₁.symm, hei₂eqk₂.symm]
          subst hieqi
          rfl
        have hcontra : p₁ ^ k₁ = p₂ ^ k₂ := by
          subst hcon
          subst hkeqk
          rfl
        contradiction } }

-- We now prove that every odd number satisifies the equation.
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
          have htpos : 0 < t := by
            apply Nat.Prime.factorization_pos_of_dvd Nat.prime_two
            { simp }
            { dsimp [kk]
              omega }
          let j := (kk + 1) / (2 ^ t)
          have h_div : 2 ^ t ∣ (kk + 1) := Nat.ordProj_dvd (kk + 1) 2
          have hjodd : Odd j := by
            have hordcompl : j = ordCompl[2] (kk + 1) := by
              rfl
            have htwondvd := @Nat.not_dvd_ordCompl
                      (kk + 1) _ Nat.prime_two (Nat.succ_ne_zero kk)
            have htwondvdj : ¬ 2 ∣ j := by
              rw [hordcompl]
              exact htwondvd
            exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp htwondvdj)
          have hkkeqjt : kk + 1 = j * 2 ^ t :=
            Nat.eq_mul_of_div_eq_left h_div rfl
          have hjltkk : j < kk := by
            have hkkge2 : kk ≥ 2 := by
              dsimp [kk]
              have hpos : 0 < k_minus_1 := Nat.pos_of_ne_zero hk1
              linarith
            have h2le2t : 2 ≤ 2 ^ t := by
              refine Nat.le_self_pow ?_ 2
              linarith
            have hbound : kk + 1 ≥ 2 * j := calc
              kk + 1 = j * 2^t := hkkeqjt
              _      ≥ j * 2   := Nat.mul_le_mul_left j h2le2t
              _      = 2 * j   := mul_comm _ _
            omega
          have hjworks := ih j hjltkk (Nat.odd_iff.mp hjodd)
          obtain ⟨nⱼ, hnⱼ⟩ := hjworks
          let kfac := kk.factorization
          obtain ⟨ps, hps⟩ := exists_distinct_primes t nⱼ hnⱼ.left kfac.support.toList
          let C := j * (2^t - 1) - 1
          have hCpos : C > 0 := by
            have ht : t > 0 := htpos
            have hj : j > 0 := hjodd.pos
            dsimp [C]
            rw [Nat.mul_sub_left_distrib, Nat.mul_one]
            rw [Nat.sub_sub]
            rw [←hkkeqjt]
            rw [Nat.add_sub_add_right]
            apply Nat.sub_pos_of_lt
            exact hjltkk
          let exps := (List.range t).map (fun i ↦ C * 2^i)
          let x := ((ps.zip exps).map (fun (p, e) ↦ p ^ e)).prod
          have hxnⱼcoprime : Nat.Coprime x nⱼ := by
            dsimp only [x]
            apply Nat.coprime_list_prod_left_iff.mpr
            intro n hnin
            simp at hnin
            obtain ⟨p, k, hpk⟩ := hnin
            have hpinps : p ∈ ps := (List.of_mem_zip hpk.left).left
            have hpcoprime : Nat.Coprime p nⱼ := (hps.left p hpinps).right.right
            rw [←hpk.right]
            apply Nat.Coprime.pow_left
            exact hpcoprime
          have hxneq0 : x ≠ 0 := by
            dsimp only [x]
            apply List.prod_ne_zero
            apply mt List.mem_map.mp
            simp only [not_exists, not_and]
            intro (p, k) hpk
            apply pow_ne_zero
            apply Nat.Prime.ne_zero
            exact (hps.left (p, k).1 (List.of_mem_zip hpk).left).left
          have hallp : ∀ i ∈ ps, Nat.Prime i := by
              intro i hi
              exact (hps.left i hi).left
          have hneqdx : d x = ((List.range t).map
            (fun i ↦ (2 ^ (t + i)) * j - 2 ^ i * (j + 1) + 1)).prod := by
            dsimp only [x]
            have hexpsnodups : exps.Nodup := by
              dsimp [exps]
              refine (List.nodup_map_iff ?_).mpr ?_
              { intro a b hab
                simp at hab
                cases hab with
                | inl h => exact h
                | inr h => linarith [hCpos] }
              { exact List.nodup_range }
            have hlent : exps.length = t := by
              dsimp [exps]
              rw [List.length_map, List.length_range]
            have hlen : ps.length = exps.length := by
              rw [hps.right.left]
              exact hlent.symm
            have h := d_of_factorization
                t ps exps hlen hlent hallp hps.right.right hexpsnodups
            rw [h]
            dsimp [exps]
            rw [List.map_map]
            apply congrArg List.prod
            apply List.map_congr_left
            intro i hi
            simp
            dsimp [C]
            rw [Nat.mul_sub_right_distrib, Nat.mul_sub_left_distrib, Nat.mul_one]
            rw [Nat.mul_sub_right_distrib, mul_assoc j, ←pow_add]
            rw [Nat.mul_add, Nat.mul_one]
            rw [mul_comm (2^i) j]
            grind
          have hneqdx2 : d (x ^ 2) = ((List.range t).map
            (fun i ↦ (2 ^ (t + i + 1) * j - 2 ^ (i + 1) * (j + 1) + 1))).prod := by
            dsimp only [x]
            have hsqdistr : (List.map (fun x ↦ x.1 ^ x.2) (ps.zip exps)).prod ^ 2
                        = (List.map (fun x ↦ x.1 ^ (2 * x.2)) (ps.zip exps)).prod := by
              induction (ps.zip exps) with
              | nil => simp
              | cons head tail ih =>
                simp
                rw [Nat.mul_pow, ih, mul_comm 2 head.2, pow_mul]
            rw [hsqdistr]
            have hexp2 : (List.map (fun x ↦ x.1 ^ (2 * x.2)) (ps.zip exps)) =
                    (List.map (fun x ↦ x.1 ^ x.2)
                      (ps.zip ((List.map (fun y ↦ 2 * y) exps)))) := by
              nth_rw 2 [List.zip_map_right]
              rw [List.map_map]
              simp
            rw [hexp2]
            have hexpsnodups : (List.map (fun y ↦ 2 * y) exps).Nodup := by
              dsimp [exps]
              rw [List.map_map]
              refine (List.nodup_map_iff ?_).mpr ?_
              { intro a b hab
                simp at hab
                cases hab with
                | inl h => exact h
                | inr h => linarith [hCpos] }
              { exact List.nodup_range }
            have hlent : (List.map (fun y ↦ 2 * y) exps).length = t := by
              dsimp [exps]
              rw [List.length_map, List.length_map, List.length_range]
            have hlen : ps.length = (List.map (fun y ↦ 2 * y) exps).length := by
              rw [hps.right.left]
              exact hlent.symm
            have h := d_of_factorization t ps (List.map (fun y ↦ 2 * y) exps)
                hlen hlent hallp hps.right.right hexpsnodups
            rw [h]
            dsimp [exps]
            rw [List.map_map, List.map_map]
            apply congrArg List.prod
            apply List.map_congr_left
            intro i hi
            simp
            dsimp [C]
            rw [mul_comm 2, mul_assoc, mul_comm (2 ^ i) 2, (pow_succ' 2 i).symm]
            rw [Nat.mul_sub_right_distrib, Nat.mul_sub_left_distrib, Nat.mul_one]
            rw [Nat.mul_sub_right_distrib, mul_assoc j, ←pow_add]
            grind
          have htelescopes : d (x ^ 2) * j = d x * (2 ^ t * j - 1) := by
            have h : d (x ^ 2) * (2 ^ t * j - (j + 1) + 1) =
              d x * (2 ^ (2 * t) * j - 2 ^ t * (j + 1) + 1) := by
              let f := fun i ↦ 2 ^ (t + i) * j - 2 ^ i * (j + 1) + 1
              have h1 : (List.map (f ∘ Nat.succ) (List.range t)).prod * f 0 =
                    d (x ^ 2) * (2 ^ t * j - (j + 1) + 1) := by
                    simp [f, hneqdx2]
                    apply congrArg List.prod
                    apply List.map_congr_left
                    intro i hi
                    simp
                    rfl
              have h2 : (List.map f (List.range t)).prod * f t =
                    d x * (2 ^ (2 * t) * j - 2 ^ t * (j + 1) + 1) := by
                    simp [f, hneqdx]
                    rw [two_mul]
              rw [h1.symm, h2.symm]
              rw [mul_comm _ (f 0)]
              rw [←List.prod_cons]
              have hlhs : f 0 :: List.map (f ∘ Nat.succ) (List.range t) =
                        List.map f (List.range (t + 1)) := by
                rw [List.range_succ_eq_map]
                rw [List.map_cons]
                rw [List.map_map]
              have hrhs : (List.map f (List.range t)).prod * f t =
                        (List.map f (List.range (t + 1))).prod := by
                rw [List.range_succ]
                rw [List.map_append]
                rw [List.prod_append]
                simp
              rw [hlhs, hrhs]
            have hfactor : (2 ^ (2 * t) * j - 2 ^ t * (j + 1) + 1) =
              (2 ^ t * j - 1) * (2 ^ t - 1) := by
              have h1 : 1 ≤ 2^t := by
                apply Nat.succ_le_of_lt
                apply Nat.lt_of_succ_lt
                apply Nat.one_lt_two_pow
                exact Nat.ne_of_gt htpos
              have h2 : 1 ≤ 2^t * j := by
                linarith [h1, hjodd.pos]
              have h3 : 2 ^ t * (j + 1) ≤ 2 ^ (2 * t) * j := by
                rw [Nat.mul_add, two_mul, pow_add, (Nat.mul_add (2 ^ t) j 1).symm]
                rw [mul_assoc (2 ^ t)]
                apply Nat.mul_le_mul_left
                calc j + 1 ≤ 2 * j     := by linarith [hjodd.pos]
                     _     ≤ 2 ^ t * j := by
                            apply Nat.mul_le_mul_right j
                            apply Nat.succ_le_of_lt
                            apply Nat.one_lt_two_pow
                            exact Nat.ne_of_gt htpos
              zify
              rw [Nat.cast_sub h3]
              zify [h1, h2]
              ring
            have hden : 2 ^ t * j - (j + 1) + 1 = j * (2 ^ t - 1) := by
              grind
            rw [hfactor, hden] at h
            rw [←mul_assoc, ←mul_assoc] at h
            apply Nat.eq_of_mul_eq_mul_right _
            { exact h }
            { apply Nat.sub_pos_of_lt
              apply Nat.one_lt_two_pow
              exact Nat.ne_of_gt htpos }
          use nⱼ * x
          have hnⱼprodxneq0 : nⱼ * x ≠ 0 := by
            rw [mul_ne_zero_iff]
            exact And.intro hnⱼ.left hxneq0
          refine ⟨hnⱼprodxneq0, ?_⟩
          have hdx2 : d ((nⱼ * x) ^ 2) = (d (nⱼ ^ 2)) * (d (x ^ 2)) := by
            have hmulexp : (nⱼ * x) ^ 2 = nⱼ ^ 2 * x ^ 2 := by
              exact Nat.mul_pow nⱼ x 2
            rw [hmulexp]
            apply d_multiplicative (nⱼ ^ 2) (x ^ 2)
            exact Nat.Coprime.pow 2 2 hxnⱼcoprime.symm
          have hdx : d (nⱼ * x) = (d nⱼ) * (d x) := by
            apply d_multiplicative nⱼ x
            exact hxnⱼcoprime.symm
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
          rw [mul_comm (2 ^ t * j - 1), mul_assoc, mul_comm (d nⱼ)]
          rw [htelescopes.symm]
          rw [hnⱼ.right, mul_comm, mul_assoc]
        } }

-- Finally, we put it all together.
theorem imo1998_q3 (k : ℕ) :
                   (k % 2 = 1 ↔ ∃ n : ℕ, n ≠ 0 ∧ d (n ^ 2) = k * d n) :=
  Iff.intro (odd_k_satisfies k) (k_is_odd k)

end Imo1998Q3
