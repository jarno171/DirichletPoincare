import DirichletPoincare.Definitions
import DirichletPoincare.Section2.Starlike

/-!
# Poincaré inequality on piecewise starlike regions (thesis Section 2.5)
-/

open MeasureTheory Metric
open scoped ENNReal

namespace DirichletPoincare

/-- Adding a null set `E` to the domain of an integral does not change it. -/
private lemma lintegral_union_null {E U : Set ℂ} (hE : volume E = 0) (F : ℂ → ℝ≥0∞) :
    ∫⁻ z in E ∪ U, F z = ∫⁻ z in U, F z :=
  le_antisymm
    ((lintegral_union_le F E U).trans_eq (by rw [setLIntegral_measure_zero E F hE, zero_add]))
    (lintegral_mono_set Set.subset_union_right)

/-- Subtracting a constant does not change the Dirichlet energy (the derivative is unchanged). -/
private lemma dirichletEnergy_sub_const (S : Set ℂ) (g : ℂ → ℂ) (c : ℂ) :
    dirichletEnergy S (fun z => g z - c) = dirichletEnergy S g := by
  unfold dirichletEnergy
  simp only [deriv_sub_const]

/-- **Lemma 2.20** (thesis p. 17). For a piecewise decomposition `G = E ∪ G₁ ∪ … ∪ Gₙ`, the
function `f - f(z₀)` lies in `D(G)` if and only if `f - f(zᵢ)` lies in `D(Gᵢ)` for every `i`.
Here `z₀ ∈ G` and `zᵢ ∈ Gᵢ` are the basepoints. -/
theorem dirichlet_iff_on_pieces {G E : Set ℂ} {n : ℕ} {Gs : Fin n → Set ℂ}
    (hdec : IsPiecewiseDecomposition G n Gs E) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f G)
    {z₀ : ℂ} (_hz₀ : z₀ ∈ G) {zs : Fin n → ℂ} (_hzs : ∀ i, zs i ∈ Gs i) :
    IsInDirichletSpace G z₀ (fun z => f z - f z₀) ↔
      ∀ i, IsInDirichletSpace (Gs i) (zs i) (fun z => f z - f (zs i)) := by
  have hE0 : volume E = 0 := hdec.2.2.2.1
  have hG : G = E ∪ ⋃ i, Gs i := hdec.2.2.2.2
  have hopen : ∀ i, IsOpen (Gs i) := fun i => (hdec.1 i).1.1
  have hsub : ∀ i, Gs i ⊆ G := fun i => by
    rw [hG]
    exact Set.subset_union_of_subset_right (Set.subset_iUnion Gs i) E
  -- The energy over `G` is the sum of the energies over the pieces, since `E` is null.
  have hsplit : ∀ S : ℂ → ℂ, dirichletEnergy G S = ∑ i, dirichletEnergy (Gs i) S := by
    intro S
    unfold dirichletEnergy
    rw [hG, lintegral_union_null hE0, lintegral_iUnion (fun i => (hopen i).measurableSet)
      hdec.2.1, tsum_fintype]
  have hdiff : ∀ i, DifferentiableOn ℂ (fun z => f z - f (zs i)) (Gs i) :=
    fun i => (hf.mono (hsub i)).sub_const _
  unfold IsInDirichletSpace
  constructor
  · rintro ⟨-, -, hE⟩ i
    refine ⟨hdiff i, sub_self _, ?_⟩
    rw [dirichletEnergy_sub_const, hsplit] at hE
    rw [dirichletEnergy_sub_const]
    exact (Finset.single_le_sum (f := fun j => dirichletEnergy (Gs j) f)
      (fun j _ => (zero_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ i)).trans_lt hE
  · intro h
    refine ⟨hf.sub_const _, sub_self _, ?_⟩
    rw [dirichletEnergy_sub_const, hsplit]
    refine ENNReal.sum_lt_top.2 fun i _ => ?_
    have := (h i).2.2
    rwa [dirichletEnergy_sub_const] at this

/-- Two points are *energy controlled* on `G` if `‖f x - f y‖²` is bounded by a constant times the
Dirichlet energy, uniformly over holomorphic `f` of finite energy. -/
def EnergyControlled (G : Set ℂ) (x y : ℂ) : Prop :=
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f G → dirichletEnergy G f < ⊤ →
    ENNReal.ofReal (‖f x - f y‖ ^ 2) ≤ C * dirichletEnergy G f

private lemma ofReal_sq_norm_sub_le (a b c : ℂ) :
    ENNReal.ofReal (‖a - c‖ ^ 2) ≤
      2 * ENNReal.ofReal (‖a - b‖ ^ 2) + 2 * ENNReal.ofReal (‖b - c‖ ^ 2) := by
  have h1 := norm_add_le (a - b) (b - c)
  rw [sub_add_sub_cancel] at h1
  have h2 : ‖a - c‖ ^ 2 ≤ (‖a - b‖ + ‖b - c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : ‖a - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a - b‖ - ‖b - c‖)]
  calc ENNReal.ofReal (‖a - c‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖a - b‖ ^ 2 + 2 * ‖b - c‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal h3
    _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        simp

namespace EnergyControlled

theorem refl (G : Set ℂ) (x : ℂ) : EnergyControlled G x x :=
  ⟨0, by simp, fun f _ _ => by simp⟩

theorem symm {G : Set ℂ} {x y : ℂ} (h : EnergyControlled G x y) : EnergyControlled G y x := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun f hf hE => by rw [norm_sub_rev]; exact h f hf hE⟩

theorem trans {G : Set ℂ} {x y z : ℂ} (h₁ : EnergyControlled G x y)
    (h₂ : EnergyControlled G y z) : EnergyControlled G x z := by
  obtain ⟨C₁, hC₁, h₁⟩ := h₁
  obtain ⟨C₂, hC₂, h₂⟩ := h₂
  refine ⟨2 * C₁ + 2 * C₂, ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top (by simp) hC₁, ENNReal.mul_lt_top (by simp) hC₂⟩, fun f hf hE => ?_⟩
  have e₁ := h₁ f hf hE
  have e₂ := h₂ f hf hE
  calc ENNReal.ofReal (‖f x - f z‖ ^ 2)
      ≤ 2 * ENNReal.ofReal (‖f x - f y‖ ^ 2) + 2 * ENNReal.ofReal (‖f y - f z‖ ^ 2) :=
        ofReal_sq_norm_sub_le _ _ _
    _ ≤ 2 * (C₁ * dirichletEnergy G f) + 2 * (C₂ * dirichletEnergy G f) := by gcongr
    _ = _ := by ring

end EnergyControlled

private lemma aemeasurable_sq_norm_sub {G S : Set ℂ} {f : ℂ → ℂ} (hS : MeasurableSet S)
    (hSG : S ⊆ G) (hf : DifferentiableOn ℂ f G) (c : ℂ) :
    AEMeasurable (fun x => ENNReal.ofReal (‖f x - c‖ ^ 2)) (volume.restrict S) :=
  (ENNReal.continuous_ofReal.comp_continuousOn
    (((hf.continuousOn.mono hSG).sub continuousOn_const).norm.pow 2)).aemeasurable hS

/-- If a disc `D ⊂ G` meets a starlike piece `Gᵢ ⊂ G` in a set of positive measure, then the
basepoint `zᵢ` of the piece is energy controlled against the centre of the disc. -/
theorem energyControlled_disc {G Gi : Set ℂ} (hbdd : Bornology.IsBounded G)
    (hGi : IsStarlikeRegion Gi) (hGiG : Gi ⊆ G) {zi : ℂ} (hzi : zi ∈ Gi) {p : ℂ} {r : ℝ}
    (hD : ball p r ⊆ G) (hm : 0 < volume (ball p r ∩ Gi)) :
    EnergyControlled G zi p := by
  have hr : 0 < r := by
    by_contra h
    rw [not_lt] at h
    rw [Metric.ball_eq_empty.2 h, Set.empty_inter, measure_empty] at hm
    exact lt_irrefl _ hm
  obtain ⟨Ki, hKi, hPi⟩ := poincare_of_starlike (hbdd.subset hGiG) hGi hzi
  have hball : IsStarlikeRegion (ball p r) :=
    ⟨⟨isOpen_ball, (convex_ball p r).isConnected (nonempty_ball.2 hr)⟩, p, mem_ball_self hr,
      fun z hz => (convex_ball p r).segment_subset (mem_ball_self hr) hz⟩
  obtain ⟨KD, hKD, hPD⟩ := poincare_of_starlike Metric.isBounded_ball hball (mem_ball_self hr)
  have hSm : MeasurableSet (ball p r ∩ Gi) :=
    isOpen_ball.measurableSet.inter hGi.1.1.measurableSet
  have hm0 : volume (ball p r ∩ Gi) ≠ 0 := hm.ne'
  have hmtop : volume (ball p r ∩ Gi) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt measure_ball_lt_top).ne
  refine ⟨(2 * Ki + 2 * KD) * (volume (ball p r ∩ Gi))⁻¹, ?_, fun f hf hE => ?_⟩
  · exact ENNReal.mul_lt_top (ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top (by simp) hKi, ENNReal.mul_lt_top (by simp) hKD⟩)
      (ENNReal.inv_lt_top.2 hm)
  · set E := dirichletEnergy G f with hEdef
    have hGiD : IsInDirichletSpace Gi zi (fun z => f z - f zi) := by
      refine ⟨(hf.mono hGiG).sub_const _, sub_self _, ?_⟩
      rw [dirichletEnergy_sub_const]
      exact (lintegral_mono_set hGiG).trans_lt hE
    have hDD : IsInDirichletSpace (ball p r) p (fun z => f z - f p) := by
      refine ⟨(hf.mono hD).sub_const _, sub_self _, ?_⟩
      rw [dirichletEnergy_sub_const]
      exact (lintegral_mono_set hD).trans_lt hE
    have hbi := hPi _ hGiD
    have hbD := hPD _ hDD
    unfold bergmanNormSq at hbi hbD
    rw [dirichletEnergy_sub_const] at hbi hbD
    have hi1 : ∫⁻ x in ball p r ∩ Gi, ENNReal.ofReal (‖f x - f zi‖ ^ 2) ≤ Ki * E :=
      (lintegral_mono_set Set.inter_subset_right).trans
        (hbi.trans (mul_le_mul' le_rfl (lintegral_mono_set hGiG)))
    have hi2 : ∫⁻ x in ball p r ∩ Gi, ENNReal.ofReal (‖f x - f p‖ ^ 2) ≤ KD * E :=
      (lintegral_mono_set Set.inter_subset_left).trans
        (hbD.trans (mul_le_mul' le_rfl (lintegral_mono_set hD)))
    have key : ENNReal.ofReal (‖f zi - f p‖ ^ 2) * volume (ball p r ∩ Gi) ≤
        (2 * Ki + 2 * KD) * E := by
      calc ENNReal.ofReal (‖f zi - f p‖ ^ 2) * volume (ball p r ∩ Gi)
          = ∫⁻ _ in ball p r ∩ Gi, ENNReal.ofReal (‖f zi - f p‖ ^ 2) :=
            (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in ball p r ∩ Gi, (2 * ENNReal.ofReal (‖f x - f zi‖ ^ 2) +
              2 * ENNReal.ofReal (‖f x - f p‖ ^ 2)) := by
            refine lintegral_mono fun x => ?_
            refine (ofReal_sq_norm_sub_le (f zi) (f x) (f p)).trans_eq ?_
            rw [norm_sub_rev (f zi) (f x)]
        _ = 2 * (∫⁻ x in ball p r ∩ Gi, ENNReal.ofReal (‖f x - f zi‖ ^ 2)) +
              2 * ∫⁻ x in ball p r ∩ Gi, ENNReal.ofReal (‖f x - f p‖ ^ 2) := by
            rw [lintegral_add_left'
              ((aemeasurable_sq_norm_sub hSm (Set.inter_subset_right.trans hGiG) hf _).const_mul 2),
              lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
        _ ≤ 2 * (Ki * E) + 2 * (KD * E) := by gcongr
        _ = _ := by ring
    calc ENNReal.ofReal (‖f zi - f p‖ ^ 2)
        ≤ (2 * Ki + 2 * KD) * E / volume (ball p r ∩ Gi) :=
          (ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)).2 key
      _ = _ := by
          rw [div_eq_mul_inv]
          ring

/-- A disc `D ⊆ G` of positive measure meets some piece in a set of positive measure. -/
theorem exists_piece_meets {G E : Set ℂ} {n : ℕ} {Gs : Fin n → Set ℂ}
    (hdec : IsPiecewiseDecomposition G n Gs E) {D : Set ℂ} (hDG : D ⊆ G)
    (hD : 0 < volume D) : ∃ i, 0 < volume (D ∩ Gs i) := by
  by_contra h
  have h0 : ∀ i, volume (D ∩ Gs i) = 0 := fun i => by
    by_contra hne
    exact h ⟨i, pos_iff_ne_zero.2 hne⟩
  have hsub : D ⊆ E ∪ ⋃ i, (D ∩ Gs i) := by
    intro x hx
    have hxG : x ∈ E ∪ ⋃ i, Gs i := by
      rw [← hdec.2.2.2.2]
      exact hDG hx
    rcases hxG with hxE | hxU
    · exact Or.inl hxE
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hxU
      exact Or.inr (Set.mem_iUnion.2 ⟨i, hx, hi⟩)
  exact hD.ne' (measure_mono_null hsub
    (measure_union_null hdec.2.2.2.1 (measure_iUnion_null h0)))

/-- Chaining the pieces: a class of pieces that contains one piece and is closed under adjacency
(two pieces meeting a common disc of `G` in positive measure) contains every piece, because `G`
is connected. -/
theorem piece_class_eq_univ {G E : Set ℂ} {n : ℕ} {Gs : Fin n → Set ℂ}
    (hdec : IsPiecewiseDecomposition G n Gs E) (hR : IsRegion G) (A : Set (Fin n))
    (hA : ∀ i j, i ∈ A → (∃ (p : ℂ) (r : ℝ), ball p r ⊆ G ∧ 0 < volume (ball p r ∩ Gs i) ∧
      0 < volume (ball p r ∩ Gs j)) → j ∈ A)
    {i₀ : Fin n} (hi₀ : i₀ ∈ A) : ∀ j, j ∈ A := by
  have hGopen : ∀ i, IsOpen (Gs i) := fun i => (hdec.1 i).1.1
  have hsub : ∀ i, Gs i ⊆ G := fun i => by
    rw [hdec.2.2.2.2]
    exact Set.subset_union_of_subset_right (Set.subset_iUnion Gs i) E
  let U : Set (Fin n) → Set ℂ := fun B => {x | ∃ (p : ℂ) (r : ℝ), x ∈ ball p r ∧ ball p r ⊆ G ∧
    ∃ i ∈ B, 0 < volume (ball p r ∩ Gs i)}
  have hUopen : ∀ B, IsOpen (U B) := fun B => by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨p, r, hx, hG', hB⟩
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact ⟨p, r, hy, hG', hB⟩
  have hcover : G ⊆ U A ∪ U Aᶜ := by
    intro x hx
    obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.1 hR.1 x hx
    obtain ⟨i, hi⟩ := exists_piece_meets hdec hεG (measure_ball_pos volume x hε)
    by_cases hiA : i ∈ A
    · exact Or.inl ⟨x, ε, mem_ball_self hε, hεG, i, hiA, hi⟩
    · exact Or.inr ⟨x, ε, mem_ball_self hε, hεG, i, hiA, hi⟩
  have hdisj : Disjoint (U A) (U Aᶜ) := by
    rw [Set.disjoint_left]
    rintro x ⟨p₁, r₁, hx₁, hG₁, i, hiA, hi⟩ ⟨p₂, r₂, hx₂, hG₂, j, hjA, hj⟩
    have hpos : 0 < volume (ball p₁ r₁ ∩ ball p₂ r₂) :=
      (isOpen_ball.inter isOpen_ball).measure_pos volume ⟨x, hx₁, hx₂⟩
    obtain ⟨k, hk⟩ := exists_piece_meets hdec (Set.inter_subset_left.trans hG₁) hpos
    have hk₁ : 0 < volume (ball p₁ r₁ ∩ Gs k) :=
      hk.trans_le (measure_mono fun y hy => ⟨hy.1.1, hy.2⟩)
    have hk₂ : 0 < volume (ball p₂ r₂ ∩ Gs k) :=
      hk.trans_le (measure_mono fun y hy => ⟨hy.1.2, hy.2⟩)
    have hkA : k ∈ A := hA i k hiA ⟨p₁, r₁, hG₁, hi, hk₁⟩
    exact hjA (hA k j hkA ⟨p₂, r₂, hG₂, hk₂, hj⟩)
  have hpiece : ∀ j B, j ∈ B → ∃ w ∈ G, w ∈ U B := by
    intro j B hj
    obtain ⟨-, w, hw, -⟩ := hdec.1 j
    obtain ⟨ε, hε, hεj⟩ := Metric.isOpen_iff.1 (hGopen j) w hw
    refine ⟨w, hsub j hw, w, ε, mem_ball_self hε, hεj.trans (hsub j), j, hj, ?_⟩
    rw [Set.inter_eq_left.2 hεj]
    exact measure_ball_pos volume w hε
  rcases hR.2.isPreconnected.subset_or_subset (hUopen A) (hUopen Aᶜ) hdisj hcover with h | h
  · intro j
    by_contra hj
    obtain ⟨w, hwG, hwU⟩ := hpiece j Aᶜ hj
    exact Set.disjoint_left.1 hdisj (h hwG) hwU
  · obtain ⟨w, hwG, hwU⟩ := hpiece i₀ A hi₀
    exact (Set.disjoint_left.1 hdisj hwU (h hwG)).elim

/-- **Theorem 2.22** (thesis p. 17). Every bounded, piecewise starlike region satisfies the
analytic Poincaré (2,2) inequality. -/
theorem poincare_of_piecewise_starlike {G : Set ℂ} (hbdd : Bornology.IsBounded G)
    (hR : IsRegion G) (hpw : IsPiecewiseStarlike G) {z₀ : ℂ} (hz₀ : z₀ ∈ G) :
    PoincareInequality G z₀ := by
  obtain ⟨n, Gs, E, hdec⟩ := hpw
  have hopen : ∀ i, IsOpen (Gs i) := fun i => (hdec.1 i).1.1
  have hsub : ∀ i, Gs i ⊆ G := fun i => by
    rw [hdec.2.2.2.2]
    exact Set.subset_union_of_subset_right (Set.subset_iUnion Gs i) E
  have hzs : ∀ i, ∃ z, z ∈ Gs i := fun i => by
    obtain ⟨-, w, hw, -⟩ := hdec.1 i
    exact ⟨w, hw⟩
  choose zs hzs using hzs
  have hdisc : ∀ i p r, ball p r ⊆ G → 0 < volume (ball p r ∩ Gs i) →
      EnergyControlled G (zs i) p := fun i p r hD hm =>
    energyControlled_disc hbdd (hdec.1 i) (hsub i) (hzs i) hD hm
  have hctrl : ∀ i, EnergyControlled G (zs i) z₀ := by
    obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.1 hR.1 z₀ hz₀
    obtain ⟨k, hk⟩ := exists_piece_meets hdec hεG (measure_ball_pos volume z₀ hε)
    refine piece_class_eq_univ hdec hR {i | EnergyControlled G (zs i) z₀} ?_
      (i₀ := k) (hdisc k z₀ ε hεG hk)
    rintro i j hi ⟨p, r, hD, hm₁, hm₂⟩
    exact (hdisc j p r hD hm₂).trans ((hdisc i p r hD hm₁).symm.trans hi)
  have hctrl' : ∀ i, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f G →
      dirichletEnergy G f < ⊤ → ENNReal.ofReal (‖f (zs i) - f z₀‖ ^ 2) ≤ C * dirichletEnergy G f :=
    hctrl
  choose C hCtop hC using hctrl'
  have hP : ∀ i, ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ f : ℂ → ℂ, IsInDirichletSpace (Gs i) (zs i) f →
      bergmanNormSq (Gs i) f ≤ K * dirichletEnergy (Gs i) f := fun i =>
    poincare_of_starlike (hbdd.subset (hsub i)) (hdec.1 i) (hzs i)
  choose K hKtop hK using hP
  have h2 : (2 : ℝ≥0∞) < ⊤ := by simp
  refine ⟨∑ i, (2 * K i + 2 * volume (Gs i) * C i), ?_, ?_⟩
  · refine ENNReal.sum_lt_top.2 fun i _ => ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top h2 (hKtop i), ENNReal.mul_lt_top
      (ENNReal.mul_lt_top h2 (hbdd.subset (hsub i)).measure_lt_top) (hCtop i)⟩
  · rintro f ⟨hf, hz, hE⟩
    have hsplit : bergmanNormSq G f = ∑ i, ∫⁻ z in Gs i, ENNReal.ofReal (‖f z‖ ^ 2) := by
      unfold bergmanNormSq
      rw [hdec.2.2.2.2, lintegral_union_null hdec.2.2.2.1,
        lintegral_iUnion (fun i => (hopen i).measurableSet) hdec.2.1, tsum_fintype]
    rw [hsplit, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hfi : IsInDirichletSpace (Gs i) (zs i) (fun z => f z - f (zs i)) := by
      refine ⟨(hf.mono (hsub i)).sub_const _, sub_self _, ?_⟩
      rw [dirichletEnergy_sub_const]
      exact (lintegral_mono_set (hsub i)).trans_lt hE
    have h1 : ∫⁻ z in Gs i, ENNReal.ofReal (‖f z - f (zs i)‖ ^ 2) ≤ K i * dirichletEnergy G f := by
      have := hK i _ hfi
      unfold bergmanNormSq at this
      rw [dirichletEnergy_sub_const] at this
      exact this.trans (mul_le_mul' le_rfl (lintegral_mono_set (hsub i)))
    have h3 : ENNReal.ofReal (‖f (zs i)‖ ^ 2) ≤ C i * dirichletEnergy G f := by
      have := hC i f hf hE
      rwa [hz, sub_zero] at this
    have hpt : ∀ z, ENNReal.ofReal (‖f z‖ ^ 2) ≤
        2 * ENNReal.ofReal (‖f z - f (zs i)‖ ^ 2) + 2 * ENNReal.ofReal (‖f (zs i)‖ ^ 2) := by
      intro z
      simpa using ofReal_sq_norm_sub_le (f z) (f (zs i)) 0
    calc ∫⁻ z in Gs i, ENNReal.ofReal (‖f z‖ ^ 2)
        ≤ ∫⁻ z in Gs i, (2 * ENNReal.ofReal (‖f z - f (zs i)‖ ^ 2) +
            2 * ENNReal.ofReal (‖f (zs i)‖ ^ 2)) := lintegral_mono hpt
      _ = 2 * (∫⁻ z in Gs i, ENNReal.ofReal (‖f z - f (zs i)‖ ^ 2)) +
            2 * ENNReal.ofReal (‖f (zs i)‖ ^ 2) * volume (Gs i) := by
          rw [lintegral_add_right' _ aemeasurable_const,
            lintegral_const_mul' _ _ (by simp), setLIntegral_const]
      _ ≤ 2 * (K i * dirichletEnergy G f) + 2 * (C i * dirichletEnergy G f) * volume (Gs i) := by
          gcongr
      _ = _ := by ring

end DirichletPoincare
