module

public import Zeta2Lean.Z7.Proofs.HeadCert7Dict
public import Zeta2Lean.Z7.Proofs.HeadCert7Tab

@[expose] public section

/-!
# `HeadCert7`, part 3: the row certificates and their soundness

Helper of `HeadCert7.lean` (notes: `notes/HeadCert7.md`).  A row certificate `HC7.HRow` is the row
of `headRows7`, a sweep certificate of the 23-line system `HC7.sysH` on the row's interval and
`X = ⌊a⌋`.  `HC7.rowOK` (evaluated by `decide +kernel` in the generated `HeadCert7Data*.lean`)
checks the certificate and, for every consistent prefix state `p` (the identical lines `1, 2` and
`7, 8` drop together), with `F = stF sysH cert p`:
* `levOK`: `5 - f ≤ EF F + 1` (vacuous), or `κ = 0` and `cmodF X F` has no bad pairs, or
  `(cmodF X F, κ, 5 - f)` is a job of the table `HC7.levJobs`;
* `poleOK`: `-f ≤ EF F + 1` (vacuous), or `(cmodF X F, -f)` is a job of `HC7.poleJobs`.
`HC7.rowOK_sound`: then every class of every prime `q > 40`, `q ∤ u` with `n/q` in the row
satisfies the row certificate (sweep → state `p`; dictionary `localModel = cmodF X F`;
`E = EF F`).
-/

set_option linter.style.longLine false

namespace Zeta2.Z7

namespace HC7

/-- Equality test of local types. -/
def ltEq (a b : LocalType) : Bool := decide (a.items = b.items) && decide (a.pairs = b.pairs)

lemma ltEq_sound {a b : LocalType} (h : ltEq a b = true) : a = b := by
  obtain ⟨ai, ap⟩ := a
  obtain ⟨bi, bp⟩ := b
  simp only [ltEq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1
  subst h2
  rfl

/-- The certificate of a head row. -/
structure HRow where
  /-- the row of `headRows7` -/
  row : DenRow
  /-- the sweep certificate of `sysH` (`sig` unused) -/
  cert : ECert7
  /-- `⌊a⌋` -/
  X : ℕ

/-- The identical lines `1, 2` and `7, 8` are together in the prefix. -/
def consistent (c : ECert7) (p : ℕ) : Bool :=
  (decide (1 ∈ c.ord.take p) == decide (2 ∈ c.ord.take p)) &&
    (decide (7 ∈ c.ord.take p) == decide (8 ∈ c.ord.take p))

/-- The `LevGe` part of the check of a state. -/
def levOK (row : DenRow) (X : ℕ) (F : ℕ → ℤ) : Bool :=
  decide (5 - (row.f : ℤ) ≤ EF F + 1) ||
    (decide (row.c0 = 0) && decide (row.c = 0) && (cmodF X F).pairs.isEmpty) ||
    levJobs.any (fun e => ltEq e.τ (cmodF X F) && decide (e.c0 = row.c0) && decide (e.j = row.j) &&
      decide (e.c = row.c) && decide (e.P = 5 - (row.f : ℤ)))

/-- The `PoleLevGe` part of the check of a state. -/
def poleOK (row : DenRow) (X : ℕ) (F : ℕ → ℤ) : Bool :=
  decide (-(row.f : ℤ) ≤ EF F + 1) ||
    poleJobs.any (fun e => ltEq e.τ (cmodF X F) && decide (e.T = -(row.f : ℤ)))

/-- The check of a row certificate. -/
def rowOK (h : HRow) : Bool :=
  okS sysH h.cert && decide (h.cert.pa = h.row.an) && decide (h.cert.qa = h.row.ad) &&
    decide (h.cert.pb = h.row.bn) && decide (h.cert.qb = h.row.bd) &&
    decide ((h.X : ℤ) * h.row.ad ≤ h.row.an) && decide ((h.row.bn : ℤ) ≤ ((h.X : ℤ) + 1) * h.row.bd) &&
    (List.range 24).all fun p => !(consistent h.cert p) ||
      (levOK h.row h.X (stF sysH h.cert p) && poleOK h.row h.X (stF sysH h.cert p))

lemma ite_iff {P Q : Prop} [Decidable P] [Decidable Q]
    (h : (if P then (1 : ℤ) else 0) = (if Q then 1 else 0)) : P ↔ Q := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp_all

/-- The actual state is consistent: identical lines have equal floor values. -/
lemma consistent_of {c : ECert7} {p u q k₀ : ℕ}
    (hF' : ∀ j < 23, hF u q k₀ j = stF sysH c p j) : consistent c p = true := by
  have h12 : stF sysH c p 1 = stF sysH c p 2 := by
    rw [← hF' 1 (by norm_num), ← hF' 2 (by norm_num)]
    rfl
  have h78 : stF sysH c p 7 = stF sysH c p 8 := by
    rw [← hF' 7 (by norm_num), ← hF' 8 (by norm_num)]
    rfl
  have hN12 : c.N sysH 1 = c.N sysH 2 := rfl
  have hN78 : c.N sysH 7 = c.N sysH 8 := rfl
  have hc1 : sysH.lc 1 = false := rfl
  have hc2 : sysH.lc 2 = false := rfl
  have hc7 : sysH.lc 7 = false := rfl
  have hc8 : sysH.lc 8 = false := rfl
  unfold stF at h12 h78
  rw [hN12, hc1, hc2] at h12
  rw [hN78, hc7, hc8] at h78
  have e12 : (if 1 ∈ c.ord.take p then (1 : ℤ) else 0) = (if 2 ∈ c.ord.take p then 1 else 0) := by
    linarith
  have e78 : (if 7 ∈ c.ord.take p then (1 : ℤ) else 0) = (if 8 ∈ c.ord.take p then 1 else 0) := by
    linarith
  clear hF' h12 h78
  unfold consistent
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_decide]
  exact ⟨ite_iff e12, ite_iff e78⟩

/-- `40u/q = X` when `X ≤ a ≤ 40u/q < b ≤ X + 1`. -/
lemma div_eq_X {u q X : ℕ} (hq : 0 < q) (hlo : (X : ℚ) ≤ ((40 * u : ℕ) : ℚ) / q)
    (hhi : ((40 * u : ℕ) : ℚ) / q < X + 1) : 40 * u / q = X := by
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  rw [le_div_iff₀ hq'] at hlo
  rw [div_lt_iff₀ hq'] at hhi
  have h1 : X * q ≤ 40 * u := by exact_mod_cast hlo
  have h2 : 40 * u < (X + 1) * q := by exact_mod_cast hhi
  exact Nat.div_eq_of_lt_le h1 h2

/-- **Soundness of a row certificate.** -/
theorem rowOK_sound (h : HRow) (hok : rowOK h = true) (u q : ℕ) (hq : q.Prime) (h40 : 40 < q)
    (hqu : ¬ q ∣ u) (ha : h.row.a ≤ ((40 * u : ℕ) : ℚ) / q)
    (hb : ((40 * u : ℕ) : ℚ) / q < h.row.b) (k₀ : ℕ) (hk : k₀ < q) :
    LevGe (localModel u q k₀) h.row.c0 h.row.j h.row.c (5 - h.row.f) ∧
      PoleLevGe (localModel u q k₀) (-(h.row.f : ℤ)) := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hS, hpa⟩, hqa⟩, hpb⟩, hqb⟩, hXa⟩, hXb⟩, hall⟩ := hok
  have hS' := hS
  simp only [okS, Bool.and_eq_true, decide_eq_true_eq] at hS'
  have hqa0 : 0 < h.cert.qa := hS'.1.1.1.1.1.1
  have hqb0 : 0 < h.cert.qb := hS'.1.1.1.1.1.2
  have hodd : Odd q := hq.odd_of_ne_two (by omega)
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  have hxa : (h.cert.pa : ℚ) / h.cert.qa ≤ ((40 * u : ℕ) : ℚ) / q := by
    rw [hpa, hqa]
    push_cast
    simpa [DenRow.a] using ha
  have hxb : ((40 * u : ℕ) : ℚ) / q < (h.cert.pb : ℚ) / h.cert.qb := by
    rw [hpb, hqb]
    push_cast
    simpa [DenRow.b] using hb
  have hy0 : (0 : ℚ) ≤ (k₀ : ℚ) / q := by positivity
  have hy1 : (k₀ : ℚ) / q < 1 := by
    rw [div_lt_one hq0]
    exact_mod_cast hk
  obtain ⟨p, hp, hFl⟩ := sweep sysH h.cert hS _ _ hxa hxb hy0 hy1 (sysH_real_disc u q k₀ hq h40 hqu)
  have hF' : ∀ j < 23, hF u q k₀ j = stF sysH h.cert p j := fun j hj =>
    (hF_spec hodd j hj).trans (hFl j (by rw [sysH_n]; exact hj))
  -- `40u/q = X`
  have hX : 40 * u / q = h.X := by
    apply div_eq_X hq.pos
    · have had : (0 : ℚ) < h.row.ad := by
        have : (0 : ℤ) < h.row.ad := by rw [← hqa]; exact hqa0
        exact_mod_cast this
      have h1 : (h.X : ℚ) ≤ h.row.a := by
        rw [DenRow.a, le_div_iff₀ had]
        exact_mod_cast hXa
      exact h1.trans ha
    · have hbd : (0 : ℚ) < h.row.bd := by
        have : (0 : ℤ) < h.row.bd := by rw [← hqb]; exact hqb0
        exact_mod_cast this
      have h1 : h.row.b ≤ (h.X : ℚ) + 1 := by
        rw [DenRow.b, div_le_iff₀ hbd]
        exact_mod_cast hXb
      exact hb.trans_le h1
  have hloc : localModel u q k₀ = cmodF h.X (stF sysH h.cert p) := by
    rw [localModel_eq_cmodF hodd, hX]
    exact cmodF_congr _ _ _ hF'
  have hE : (localModel u q k₀).E = EF (stF sysH h.cert p) := by
    rw [localModel_E_eq_EF hodd hk]
    exact EF_congr _ _ hF'
  have hcons : consistent h.cert p = true := consistent_of hF'
  have hst := List.all_eq_true.1 hall p (List.mem_range.2 (by rw [sysH_n] at hp; omega))
  rw [hcons] at hst
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hst
  obtain ⟨hlev, hpole⟩ := hst
  constructor
  · simp only [levOK, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, List.any_eq_true,
      List.isEmpty_iff] at hlev
    rcases hlev with (h1 | ⟨⟨h1, h2⟩, h3⟩) | ⟨e, he, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩
    · exact RC7.LevGe_of_E _ _ _ _ _ (by rw [hE]; exact h1)
    · rw [h1, h2, hloc]
      exact LevGe_zero_of_nopairs _ _ _ h3
    · rw [hloc, ← ltEq_sound h1, ← h2, ← h3, ← h4, ← h5]
      exact levJobs_sound e he
  · simp only [poleOK, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      List.any_eq_true] at hpole
    rcases hpole with h1 | ⟨e, he, h1, h2⟩
    · exact RC7.PoleLevGe_of_E _ _ (by rw [hE]; exact h1)
    · rw [hloc, ← ltEq_sound h1, ← h2]
      exact poleJobs_sound e he

/-! ## Alignment with `headRows7` -/

/-- Equality test of table rows. -/
def denRowEq (r s : DenRow) : Bool :=
  decide (r.an = s.an) && decide (r.ad = s.ad) && decide (r.bn = s.bn) && decide (r.bd = s.bd) &&
    decide (r.f = s.f) && decide (r.c0 = s.c0) && decide (r.j = s.j) && decide (r.c = s.c)

lemma denRowEq_sound {r s : DenRow} (h : denRowEq r s = true) : r = s := by
  obtain ⟨an, ad, bn, bd, f, c0, j, c⟩ := r
  obtain ⟨an', ad', bn', bd', f', c0', j', c'⟩ := s
  simp only [denRowEq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8
  rfl

/-- The certificates are those of the rows, in order. -/
def aligned : List DenRow → List HRow → Bool
  | [], _ => true
  | r :: rs, h :: hs => denRowEq h.row r && aligned rs hs
  | _ :: _, [] => false

lemma aligned_sound : ∀ (L : List DenRow) (H : List HRow), aligned L H = true →
    ∀ r ∈ L, ∃ h ∈ H, h.row = r
  | [], _, _, r, hr => by simp at hr
  | _ :: _, [], hal, _, _ => by simp [aligned] at hal
  | r :: rs, h :: hs, hal, r', hr' => by
    simp only [aligned, Bool.and_eq_true] at hal
    rcases List.mem_cons.1 hr' with rfl | hr''
    · exact ⟨h, List.mem_cons_self, denRowEq_sound hal.1⟩
    · obtain ⟨h', hh', he⟩ := aligned_sound rs hs hal.2 r' hr''
      exact ⟨h', List.mem_cons_of_mem _ hh', he⟩

end HC7

end Zeta2.Z7
