module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# `HeadCert7`, part 2: computable series coefficients of a local type

Helper of `HeadCert7.lean` (notes: `notes/HeadCert7.md`).  Truncated power series are lists of
coefficients (`HC7.cf`, `HC7.tmul`, `HC7.tprod`, `HC7.bserL`).  For a local type `τ`:
* `HC7.coeff_rSer`: `coeff n (rSer τ) = cf (rSerL M τ) n` (`n < M`);
* `HC7.coeff_taylorAt`: `coeff n (taylorAt τ wk) = cf (tayL M τ wk) n` (`n < M`);
* `HC7.coeff_gSer`: `coeff n (gSer τ wk we) = cf (gL M τ wk we) n` (`n < M`);
* `HC7.coeff_ASer`: `coeff m (ASer τ) = ASerC τ m`.
The Boolean checks `HC7.levChk` / `HC7.poleChk` (evaluated by `decide +kernel`) imply `LevGe` /
`PoleLevGe` (`HC7.levChk_sound`, `HC7.poleChk_sound`).

The generated `HeadCert7Lev*.lean` evaluate `levChk` in small pieces: the bad pairs are grouped by
pole (`HC7.grp`), each pole's Taylor series is computed once for its group (`HC7.grpC`,
`HC7.ASerC_eq_grp`), a piece is the contribution `HC7.grpR τ lo hi m` of the groups `lo ≤ k < hi`
(or `HC7.grpT τ lo m` of the groups `k ≥ lo`) to `[y^m] ASer τ`, and `HC7.LevJob.ok_of_vals1` …
`ok_of_vals4` combine the values of the pieces with the check `HC7.levChkV` of the rest of `levChk`.
-/

set_option linter.style.longLine false

open PowerSeries

namespace Zeta2.Z7

namespace HC7

/-! ## Truncated series as lists -/

/-- The coefficient `n` of a truncated series (`0` beyond its length). -/
def cf (a : List ℚ) (n : ℕ) : ℚ := a.getD n 0

/-- `∑_{i ≤ n} a_i b_{n-i}`. -/
def conv (a b : List ℚ) (n : ℕ) : ℚ :=
  ((List.range (n + 1)).map fun i => cf a i * cf b (n - i)).sum

/-- The product truncated to `M` coefficients. -/
def tmul (M : ℕ) (a b : List ℚ) : List ℚ := (List.range M).map (conv a b)

/-- The series `1` truncated to `M` coefficients. -/
def tone (M : ℕ) : List ℚ := (List.range M).map fun i => if i = 0 then 1 else 0

/-- The truncated product of a list of truncated series. -/
def tprod (M : ℕ) : List (List ℚ) → List ℚ
  | [] => tone M
  | a :: l => tmul M a (tprod M l)

/-- The generalised binomial coefficient, computably. -/
def gch (e : ℤ) : ℕ → ℚ
  | 0 => 1
  | i + 1 => gch e i * ((e : ℚ) - i) / (i + 1)

/-- `(1 + c X)^e` truncated to `M` coefficients. -/
def bserL (M : ℕ) (c : ℚ) (e : ℤ) : List ℚ := (List.range M).map fun i => gch e i * c ^ i

/-- Scalar multiple. -/
def smul (k : ℚ) (a : List ℚ) : List ℚ := a.map fun v => k * v

lemma cf_map_range (M : ℕ) (f : ℕ → ℚ) (n : ℕ) (hn : n < M) :
    cf ((List.range M).map f) n = f n := by
  unfold cf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn]
  rfl

lemma cf_smul (k : ℚ) (a : List ℚ) (n : ℕ) : cf (smul k a) n = k * cf a n := by
  unfold cf smul
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases a[n]? <;> simp

lemma cf_tmul {M n : ℕ} (a b : List ℚ) (hn : n < M) : cf (tmul M a b) n = conv a b n :=
  cf_map_range M _ n hn

lemma sum_range_list (n : ℕ) (f : ℕ → ℚ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

lemma gch_eq (e : ℤ) (i : ℕ) : gch e i = gchoose e i := by
  induction i with
  | zero => simp [gch, gchoose]
  | succ i ih =>
    rw [gch, ih]
    unfold gchoose
    rw [Finset.prod_range_succ, Nat.factorial_succ]
    push_cast
    field_simp

lemma coeff_bser' (c : ℚ) (e : ℤ) (i : ℕ) : coeff i (bser c e) = gchoose e i * c ^ i := by
  simp [bser, coeff_mk]

lemma coeff_bser_cf (M : ℕ) (c : ℚ) (e : ℤ) (n : ℕ) (hn : n < M) :
    coeff n (bser c e) = cf (bserL M c e) n := by
  rw [coeff_bser', bserL, cf_map_range M _ n hn, gch_eq]

lemma coeff_mul_eq_conv (φ ψ : PowerSeries ℚ) (a b : List ℚ) (n : ℕ)
    (ha : ∀ i ≤ n, coeff i φ = cf a i) (hb : ∀ i ≤ n, coeff i ψ = cf b i) :
    coeff n (φ * ψ) = conv a b n := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, conv, ← sum_range_list]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
  rw [ha i hi', hb (n - i) (Nat.sub_le n i)]

/-- Coefficients of a product of series with known truncations. -/
lemma coeff_prod_map {α : Type*} (M : ℕ) (P : α → PowerSeries ℚ) (Q : α → List ℚ) :
    ∀ L : List α, (∀ x ∈ L, ∀ n < M, coeff n (P x) = cf (Q x) n) →
      ∀ n < M, coeff n (L.map P).prod = cf (tprod M (L.map Q)) n
  | [], _, n, hn => by
    simp only [List.map_nil, List.prod_nil, tprod, tone]
    rw [cf_map_range M _ n hn, coeff_one]
  | x :: L, h, n, hn => by
    simp only [List.map_cons, List.prod_cons, tprod]
    rw [cf_tmul _ _ hn]
    apply coeff_mul_eq_conv
    · intro i hi
      exact h x List.mem_cons_self i (by omega)
    · intro i hi
      exact coeff_prod_map M P Q L (fun y hy => h y (List.mem_cons_of_mem _ hy)) i (by omega)

/-! ## `rSer`, `taylorAt`, `gSer`, `ASer` -/

/-- `rSer τ` truncated to `M` coefficients. -/
def rSerL (M : ℕ) (τ : LocalType) : List ℚ :=
  tprod M (τ.items.map fun p => bserL M (-(p.1 : ℚ) / 2) p.2)

lemma coeff_rSer (M : ℕ) (τ : LocalType) (n : ℕ) (hn : n < M) :
    coeff n (rSer τ) = cf (rSerL M τ) n :=
  coeff_prod_map M (fun p : ℤ × ℤ => bser (-(p.1 : ℚ) / 2) p.2)
    (fun p : ℤ × ℤ => bserL M (-(p.1 : ℚ) / 2) p.2) τ.items
    (fun _ _ n hn => coeff_bser_cf M _ _ n hn) n hn

/-- `taylorAt τ wk` truncated to `M` coefficients. -/
def tayL (M : ℕ) (τ : LocalType) (wk : ℤ) : List ℚ :=
  tprod M ((τ.items.filter fun p => p.1 ≠ wk).map fun p =>
    smul (((wk - p.1 : ℚ) / 2) ^ p.2) (bserL M (2 / (wk - p.1 : ℚ)) p.2))

lemma coeff_taylorAt (M : ℕ) (τ : LocalType) (wk : ℤ) (n : ℕ) (hn : n < M) :
    coeff n (taylorAt τ wk) = cf (tayL M τ wk) n := by
  unfold taylorAt tayL
  refine coeff_prod_map M
    (fun p : ℤ × ℤ => C (((wk - p.1 : ℚ) / 2) ^ p.2) * bser (2 / (wk - p.1 : ℚ)) p.2)
    (fun p : ℤ × ℤ => smul (((wk - p.1 : ℚ) / 2) ^ p.2) (bserL M (2 / (wk - p.1 : ℚ)) p.2))
    _ (fun p _ n hn => ?_) n hn
  rw [coeff_C_mul, cf_smul, coeff_bser_cf M _ _ n hn]

/-- `gSer τ wk we` truncated to `M` coefficients. -/
def gL (M : ℕ) (τ : LocalType) (wk we : ℤ) : List ℚ :=
  tmul M (tayL M τ wk)
    (smul (((we - wk : ℚ) / 2) ^ (-5 : ℤ)) (bserL M (-2 / (we - wk : ℚ)) (-5)))

lemma coeff_gSer (M : ℕ) (τ : LocalType) (wk we : ℤ) (n : ℕ) (hn : n < M) :
    coeff n (gSer τ wk we) = cf (gL M τ wk we) n := by
  unfold gSer gL
  rw [cf_tmul _ _ hn]
  apply coeff_mul_eq_conv
  · intro i hi
    exact coeff_taylorAt M τ wk i (by omega)
  · intro i hi
    rw [coeff_C_mul, cf_smul, coeff_bser_cf M _ _ i (by omega)]

lemma sum_Icc_one {R : Type*} [AddCommMonoid R] (a : ℕ) (f : ℕ → R) :
    ∑ i ∈ Finset.Icc 1 a, f i = ∑ i ∈ Finset.range a, f (i + 1) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- The contribution of a bad pair to `[y^m] ASer τ`. -/
def pairC (τ : LocalType) (pr : ℤ × ℤ × ℤ) (m : ℕ) : ℚ :=
  (pr.2.2 : ℚ) * ((List.range (-(τ.netE pr.1)).toNat).map fun i' =>
    if i' + 1 ≤ m then
      cf (gL (-(τ.netE pr.1)).toNat τ pr.1 pr.2.1) ((-(τ.netE pr.1)).toNat - (i' + 1)) *
        (gch (-((i' + 1 : ℕ) : ℤ)) (m - (i' + 1)) * (-(pr.1 : ℚ) / 2) ^ (m - (i' + 1)))
    else 0).sum

/-- `[y^m] ASer τ`, computably. -/
def ASerC (τ : LocalType) (m : ℕ) : ℚ := (τ.pairs.map fun pr => pairC τ pr m).sum

lemma coeff_pair (τ : LocalType) (pr : ℤ × ℤ × ℤ) (m : ℕ) :
    coeff m (C (pr.2.2 : ℚ) * ∑ i ∈ Finset.Icc 1 (-(τ.netE pr.1)).toNat,
      C (coeff ((-(τ.netE pr.1)).toNat - i) (gSer τ pr.1 pr.2.1)) * X ^ i *
        bser (-(pr.1 : ℚ) / 2) (-(i : ℤ))) = pairC τ pr m := by
  unfold pairC
  set a := (-(τ.netE pr.1)).toNat with ha
  rw [coeff_C_mul, map_sum]
  congr 1
  have e : ∑ i ∈ Finset.Icc 1 a, coeff m (C (coeff (a - i) (gSer τ pr.1 pr.2.1)) * X ^ i *
      bser (-(pr.1 : ℚ) / 2) (-(i : ℤ))) =
      ∑ i' ∈ Finset.range a, coeff m (C (coeff (a - (i' + 1)) (gSer τ pr.1 pr.2.1)) *
        X ^ (i' + 1) * bser (-(pr.1 : ℚ) / 2) (-((i' + 1 : ℕ) : ℤ))) := by
    exact sum_Icc_one a _
  rw [e, sum_range_list]
  congr 1
  apply List.map_congr_left
  intro i' hi'
  have hi'a : i' < a := List.mem_range.1 hi'
  rw [mul_assoc, coeff_C_mul, PowerSeries.coeff_X_pow_mul', coeff_gSer a τ pr.1 pr.2.1 _ (by omega)]
  split_ifs with h
  · rw [coeff_bser', gch_eq]
  · simp

lemma coeff_ASer (τ : LocalType) (m : ℕ) : coeff m (ASer τ) = ASerC τ m := by
  unfold ASer ASerC
  rw [map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro pr _
  exact coeff_pair τ pr m

/-! ## The level checks -/

/-- `coeffZ` of a coefficient function. -/
def czf (f : ℕ → ℚ) (z : ℤ) : ℚ := if 0 ≤ z then f z.toNat else 0

/-- The Boolean check of `LevGe τ c0 j c P`. -/
def levChk (τ : LocalType) (c0 : ℚ) (j : ℕ) (c : ℚ) (P : ℤ) : Bool :=
  (List.range (P - τ.E - 1).toNat).all fun i =>
    decide (ASerC τ (i + 1) - c0 * czf (cf (rSerL P.toNat τ)) (τ.E + 1 + i) -
      c * czf (cf (rSerL P.toNat τ)) (τ.E + 1 + i - j) = 0)

lemma coeffZ_rSer (τ : LocalType) (P z : ℤ) (hz : z < P) :
    coeffZ (rSer τ) z = czf (cf (rSerL P.toNat τ)) z := by
  unfold coeffZ czf
  split_ifs with h
  · exact coeff_rSer P.toNat τ z.toNat (by omega)
  · rfl

theorem levChk_sound (τ : LocalType) (c0 : ℚ) (j : ℕ) (c : ℚ) (P : ℤ)
    (h : levChk τ c0 j c P = true) : LevGe τ c0 j c P := by
  intro p hp1 hp2
  unfold levChk at h
  rw [List.all_eq_true] at h
  have hi := h (p - τ.E - 1).toNat (List.mem_range.2 (by omega))
  rw [decide_eq_true_eq] at hi
  have e1 : τ.E + 1 + ((p - τ.E - 1).toNat : ℤ) = p := by omega
  rw [e1] at hi
  unfold coeffD
  have hA : coeffZ (ASer τ) (p - τ.E) = ASerC τ ((p - τ.E - 1).toNat + 1) := by
    unfold coeffZ
    rw [ite_eq_left (by omega), coeff_ASer]
    congr 1
    omega
  rw [hA, coeffZ_rSer τ P p hp2, coeffZ_rSer τ P (p - j) (by omega)]
  exact hi

/-- `LevGe` for the trivial kernel on a type without bad pairs. -/
theorem LevGe_zero_of_nopairs (τ : LocalType) (j : ℕ) (P : ℤ) (h : τ.pairs = []) :
    LevGe τ 0 j 0 P := by
  intro p _ _
  unfold coeffD coeffZ ASer
  rw [h]
  simp

/-- The Boolean check of `PoleLevGe τ T`. -/
def poleChk (τ : LocalType) (T : ℤ) : Bool :=
  τ.items.all fun p =>
    (List.range (-τ.netE p.1).toNat).all fun l =>
      !(decide (τ.E - τ.netE p.1 - T < l)) ||
        decide (cf (tayL (-τ.netE p.1).toNat τ p.1) l = 0)

theorem poleChk_sound (τ : LocalType) (T : ℤ) (h : poleChk τ T = true) : PoleLevGe τ T := by
  intro p hp l hl1 hl2
  unfold poleChk at h
  rw [List.all_eq_true] at h
  have h1 := h p hp
  rw [List.all_eq_true] at h1
  have h2 := h1 l (List.mem_range.2 (by omega))
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h2
  rcases h2 with h2 | h2
  · exact absurd hl2 h2
  · rw [coeff_taylorAt (-τ.netE p.1).toNat τ p.1 l (by omega)]
    exact h2

/-! ## The level check by pole groups -/

/-- The bad pairs grouped by pole: maximal runs of consecutive pairs with the same pole
(`decP` lists the pairs of a pole consecutively). -/
def grp : List (ℤ × ℤ × ℤ) → List (ℤ × List (ℤ × ℤ × ℤ))
  | [] => []
  | pr :: l =>
    match grp l with
    | (w, g) :: rest => if pr.1 = w then (w, pr :: g) :: rest else (pr.1, [pr]) :: (w, g) :: rest
    | [] => [(pr.1, [pr])]

lemma grp_flatten : ∀ l : List (ℤ × ℤ × ℤ), ((grp l).map Prod.snd).flatten = l
  | [] => rfl
  | pr :: l => by
    have ih := grp_flatten l
    simp only [grp]
    split
    · next w g rest h =>
      rw [h] at ih
      split_ifs <;> simp_all
    · next h =>
      rw [h] at ih
      simp_all

lemma grp_fst : ∀ (l : List (ℤ × ℤ × ℤ)), ∀ wg ∈ grp l, ∀ pr ∈ wg.2, pr.1 = wg.1
  | [] => by simp [grp]
  | pr :: l => by
    have ih := grp_fst l
    simp only [grp]
    split
    · next w g rest h =>
      rw [h] at ih
      split_ifs with hw
      · intro wg hwg pr' hpr'
        simp only [List.mem_cons] at hwg
        rcases hwg with rfl | hwg
        · simp only [List.mem_cons] at hpr'
          rcases hpr' with rfl | hpr'
          · exact hw
          · exact ih (w, g) List.mem_cons_self pr' hpr'
        · exact ih wg (List.mem_cons_of_mem _ hwg) pr' hpr'
      · intro wg hwg pr' hpr'
        simp only [List.mem_cons] at hwg
        rcases hwg with rfl | hwg
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr'
          rw [hpr']
        · exact ih wg (List.mem_cons.2 hwg) pr' hpr'
    · next h =>
      intro wg hwg pr' hpr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwg
      subst hwg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr'
      rw [hpr']

/-- `pairC` with the truncated Taylor series `A` (of length `a`) of the pair's pole given. -/
def pairCA (A : List ℚ) (a : ℕ) (pr : ℤ × ℤ × ℤ) (m : ℕ) : ℚ :=
  (pr.2.2 : ℚ) * ((List.range a).map fun i' =>
    if i' + 1 ≤ m then
      conv A (smul (((pr.2.1 - pr.1 : ℚ) / 2) ^ (-5 : ℤ)) (bserL a (-2 / (pr.2.1 - pr.1 : ℚ)) (-5)))
          (a - (i' + 1)) *
        (gch (-((i' + 1 : ℕ) : ℤ)) (m - (i' + 1)) * (-(pr.1 : ℚ) / 2) ^ (m - (i' + 1)))
    else 0).sum

lemma pairCA_eq (τ : LocalType) (pr : ℤ × ℤ × ℤ) (m : ℕ) :
    pairCA (tayL (-(τ.netE pr.1)).toNat τ pr.1) (-(τ.netE pr.1)).toNat pr m = pairC τ pr m := by
  unfold pairCA pairC
  congr 2
  apply List.map_congr_left
  intro i' hi'
  have hi'a := List.mem_range.1 hi'
  split_ifs
  · rw [gL, cf_tmul _ _ (by omega)]
  · rfl

/-- The contribution of the bad pairs `wg.2` at the pole `wg.1` to `[y^m] ASer τ`: the pole's
Taylor series is computed once for all of them. -/
def grpC (τ : LocalType) (wg : ℤ × List (ℤ × ℤ × ℤ)) (m : ℕ) : ℚ :=
  (wg.2.map fun pr => pairCA (tayL (-(τ.netE wg.1)).toNat τ wg.1) (-(τ.netE wg.1)).toNat pr m).sum

lemma grpC_eq (τ : LocalType) (wg : ℤ × List (ℤ × ℤ × ℤ)) (h : ∀ pr ∈ wg.2, pr.1 = wg.1)
    (m : ℕ) : grpC τ wg m = (wg.2.map fun pr => pairC τ pr m).sum := by
  unfold grpC
  congr 1
  apply List.map_congr_left
  intro pr hpr
  rw [← pairCA_eq τ pr m, h pr hpr]

lemma sum_map_flatten_snd {β : Type*} (L : List (ℤ × List β)) (f : β → ℚ) :
    (((L.map Prod.snd).flatten).map f).sum = (L.map fun x => (x.2.map f).sum).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.sum_append, List.sum_cons, ih]

lemma ASerC_eq_grp (τ : LocalType) (m : ℕ) :
    ASerC τ m = ((grp τ.pairs).map fun wg => grpC τ wg m).sum := by
  unfold ASerC
  conv_lhs => rw [← grp_flatten τ.pairs]
  rw [sum_map_flatten_snd]
  congr 1
  apply List.map_congr_left
  intro wg hwg
  rw [grpC_eq τ wg (grp_fst τ.pairs wg hwg) m]

/-- The contribution of the pole groups `k ≥ lo` of `τ` to `[y^m] ASer τ`. -/
def grpT (τ : LocalType) (lo m : ℕ) : ℚ :=
  (((grp τ.pairs).drop lo).map fun wg => grpC τ wg m).sum

/-- The contribution of the pole groups `lo ≤ k < hi` of `τ` to `[y^m] ASer τ`. -/
def grpR (τ : LocalType) (lo hi m : ℕ) : ℚ :=
  ((((grp τ.pairs).drop lo).take (hi - lo)).map fun wg => grpC τ wg m).sum

lemma ASerC_eq_grpT (τ : LocalType) (m : ℕ) : ASerC τ m = grpT τ 0 m := by
  rw [ASerC_eq_grp, grpT, List.drop_zero]

lemma grpT_split (τ : LocalType) (lo hi m : ℕ) (h : lo ≤ hi) :
    grpT τ lo m = grpR τ lo hi m + grpT τ hi m := by
  unfold grpT grpR
  rw [← List.sum_append, ← List.map_append]
  congr 2
  conv_lhs => rw [← List.take_append_drop (hi - lo) ((grp τ.pairs).drop lo)]
  rw [List.drop_drop]
  congr 2
  omega

/-- `levChk` with the values `V[i]` of `[y^(i+1)] ASer τ` given. -/
def levChkV (τ : LocalType) (V : List ℚ) (c0 : ℚ) (j : ℕ) (c : ℚ) (P : ℤ) : Bool :=
  decide ((P - τ.E - 1).toNat ≤ V.length) &&
    (List.range (P - τ.E - 1).toNat).all fun i =>
      decide (V.getD i 0 - c0 * czf (cf (rSerL P.toNat τ)) (τ.E + 1 + i) -
        c * czf (cf (rSerL P.toNat τ)) (τ.E + 1 + i - j) = 0)

lemma levChk_of_V (τ : LocalType) (V : List ℚ) (c0 : ℚ) (j : ℕ) (c : ℚ) (P : ℤ)
    (hV : ∀ i < V.length, ASerC τ (i + 1) = V.getD i 0) (h : levChkV τ V c0 j c P = true) :
    levChk τ c0 j c P = true := by
  unfold levChkV at h
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  unfold levChk
  rw [List.all_eq_true]
  intro i hi
  rw [hV i (by have := List.mem_range.1 hi; omega)]
  exact h.2 i hi

/-! ## Compact encoding of local types -/

/-- Decode `[w₁, e₁, w₂, e₂, …]` into items. -/
def decI : List ℤ → List (ℤ × ℤ)
  | a :: b :: l => (a, b) :: decI l
  | _ => []

/-- Decode run-length pairs `[w₁, s₁, n₁, …]`: the bad pairs `(w, w + s (2t+1), s)`, `t < n`. -/
def decP : List ℤ → List (ℤ × ℤ × ℤ)
  | w :: s :: n :: l => (List.range n.toNat).map (fun t : ℕ => (w, w + s * (2 * (t : ℤ) + 1), s)) ++ decP l
  | _ => []

/-- A local type from its compact encoding. -/
def mkT (I P : List ℤ) : LocalType := ⟨decI I, decP P⟩

/-! ## Jobs of the certificate table -/

/-- A `LevGe` job: the type, the kernel `c0 + c y^j` and the level parameter `P`. -/
structure LevJob where
  /-- the local type -/
  τ : LocalType
  /-- kernel constant term -/
  c0 : ℚ
  /-- kernel pole order -/
  j : ℕ
  /-- kernel coefficient -/
  c : ℚ
  /-- level parameter (`5 - f`) -/
  P : ℤ

/-- A `PoleLevGe` job. -/
structure PoleJob where
  /-- the local type -/
  τ : LocalType
  /-- the per-pole level (`-f`) -/
  T : ℤ

/-- The check of a `LevGe` job. -/
def LevJob.ok (e : LevJob) : Bool := levChk e.τ e.c0 e.j e.c e.P

/-- The check of a `PoleLevGe` job. -/
def PoleJob.ok (e : PoleJob) : Bool := poleChk e.τ e.T

/-! The check of a `LevGe` job from the values `vₘ` of `[y^m] ASer τ`, `m = 1, …, P - E - 1`
(`HeadCert7Lev*.lean`: the values are sums of pieces `grpR` / `grpT`). -/

theorem LevJob.ok_of_vals1 (e : LevJob) (v1 : ℚ) (h1 : ASerC e.τ 1 = v1)
    (h : levChkV e.τ [v1] e.c0 e.j e.c e.P = true) : e.ok = true := by
  refine levChk_of_V _ _ _ _ _ _ (fun i hi => ?_) h
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i
  simpa using h1

theorem LevJob.ok_of_vals2 (e : LevJob) (v1 v2 : ℚ) (h1 : ASerC e.τ 1 = v1)
    (h2 : ASerC e.τ 2 = v2) (h : levChkV e.τ [v1, v2] e.c0 e.j e.c e.P = true) : e.ok = true := by
  refine levChk_of_V _ _ _ _ _ _ (fun i hi => ?_) h
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i
  · simpa using h1
  · simpa using h2

theorem LevJob.ok_of_vals3 (e : LevJob) (v1 v2 v3 : ℚ) (h1 : ASerC e.τ 1 = v1)
    (h2 : ASerC e.τ 2 = v2) (h3 : ASerC e.τ 3 = v3)
    (h : levChkV e.τ [v1, v2, v3] e.c0 e.j e.c e.P = true) : e.ok = true := by
  refine levChk_of_V _ _ _ _ _ _ (fun i hi => ?_) h
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i
  · simpa using h1
  · simpa using h2
  · simpa using h3

theorem LevJob.ok_of_vals4 (e : LevJob) (v1 v2 v3 v4 : ℚ) (h1 : ASerC e.τ 1 = v1)
    (h2 : ASerC e.τ 2 = v2) (h3 : ASerC e.τ 3 = v3) (h4 : ASerC e.τ 4 = v4)
    (h : levChkV e.τ [v1, v2, v3, v4] e.c0 e.j e.c e.P = true) : e.ok = true := by
  refine levChk_of_V _ _ _ _ _ _ (fun i hi => ?_) h
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · simpa using h4

end HC7

end Zeta2.Z7
