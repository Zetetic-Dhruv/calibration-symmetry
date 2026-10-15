/-
# Calibration as symmetry: what a brain–computer interface can decode

A session records a subject whose latent state `θ` is unknown, through a device/session
configuration `s` that is also unknown (gains, placement, coupling, drift). Calibration items are
recordings made in the same session whose latent is a known function of the subject's latent:
a physical phantom (constant), a cued trial, or a known intervention on the subject.

§1  General measure-theoretic statements for any family of session laws.
§2  Calibration groups acting on recordings: phantoms, stabilizers, the identifiability floor.
§3  A worked optical instance: flow + volume channels on a two-element Windkessel.
-/
import Mathlib

open MeasureTheory ComplexConjugate

namespace BCIMetrology

/-! ## §1 General statements -/

section General

variable {Θ S ι X Y : Type*} [MeasurableSpace X]

/-- A target is a function of an observation exactly when it is constant on the observation's
fibers. -/
theorem exists_decoder_iff {P Z : Type*} [Nonempty Y] (O : P → Z) (f : P → Y) :
    (∃ h : Z → Y, ∀ x, h (O x) = f x) ↔ ∀ x y, O x = O y → f x = f y := by
  classical
  constructor
  · rintro ⟨h, hh⟩ x y e
    rw [← hh x, ← hh y, e]
  · intro hc
    refine ⟨fun z => if hz : ∃ x, O x = z then f hz.choose else Classical.arbitrary Y,
      fun x => ?_⟩
    have hz : ∃ y, O y = O x := ⟨x, rfl⟩
    show (if hz : ∃ y, O y = O x then f hz.choose else Classical.arbitrary Y) = f x
    rw [dif_pos hz]
    exact hc _ _ hz.choose_spec

/-- What a session reveals: the law of the subject's recording and the law of each calibration
item's recording. `M s θ` is the law of a recording of latent `θ` in session `s`; item `i` has
latent `p i θ`. -/
noncomputable def reveal (M : S → Θ → Measure X) (p : ι → Θ → Θ) (s : S) (θ : Θ) :
    Measure X × (ι → Measure X) :=
  (M s θ, fun i => M s (p i θ))

/-- `φ` is decodable when a single decoder, fed what a session reveals, returns `φ θ` for every
latent `θ` and every admissible session `s`. -/
def Decodable (M : S → Θ → Measure X) (p : ι → Θ → Θ) (φ : Θ → Y) : Prop :=
  ∃ h : Measure X × (ι → Measure X) → Y, ∀ s θ, h (reveal M p s θ) = φ θ

/-- **Decodability.** A target is decodable iff any two (session, latent) pairs that reveal the
same laws carry the same target. -/
theorem decodable_iff [Nonempty Y] {M : S → Θ → Measure X} {p : ι → Θ → Θ} {φ : Θ → Y} :
    Decodable M p φ ↔ ∀ s s' θ θ', reveal M p s θ = reveal M p s' θ' → φ θ = φ θ' := by
  constructor
  · rintro ⟨h, hh⟩ s s' θ θ' e
    rw [← hh s θ, ← hh s' θ', e]
  · intro H
    obtain ⟨h, hh⟩ := (exists_decoder_iff (fun x : S × Θ => reveal M p x.1 x.2)
      (fun x => φ x.2)).2 fun x y e => H x.1 y.1 x.2 y.2 e
    exact ⟨h, fun s θ => hh (s, θ)⟩

/-- More calibration items never lose a decodable target. -/
theorem Decodable.add_items {κ : Type*} {M : S → Θ → Measure X} {p : ι → Θ → Θ}
    {q : κ → Θ → Θ} {φ : Θ → Y} (h : Decodable M p φ) : Decodable M (Sum.elim p q) φ := by
  obtain ⟨dec, hdec⟩ := h
  exact ⟨fun d => dec (d.1, fun i => d.2 (Sum.inl i)), fun s θ => hdec s θ⟩

/-- Two hypotheses that induce the same data law cannot both be recognised: for any measurable
decoder, the two success probabilities sum to at most one. -/
theorem chance_bound {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (P : Measure Ω) [IsProbabilityMeasure P] {T : Ω → Y}
    (hT : Measurable T) {a b : Y} (hab : a ≠ b) :
    P (T ⁻¹' {a}) + P (T ⁻¹' {b}) ≤ 1 := by
  rw [← measure_union ((Set.disjoint_singleton.2 hab).preimage T)
    (hT (measurableSet_singleton b))]
  exact prob_le_one

/-- Metric form: the two expected errors sum to at least the gap between the targets. -/
theorem two_point {Ω : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (P : Measure Ω) [IsProbabilityMeasure P] {T : Ω → Y}
    (hT : Measurable T) (a b : Y) :
    edist a b ≤ ∫⁻ x, edist (T x) a ∂P + ∫⁻ x, edist (T x) b ∂P := by
  have hm : Measurable fun x => edist (T x) a :=
    (continuous_id.edist continuous_const).measurable.comp hT
  rw [← lintegral_add_left hm]
  calc edist a b = ∫⁻ _, edist a b ∂P := by simp
    _ ≤ ∫⁻ x, edist (T x) a + edist (T x) b ∂P := lintegral_mono fun x => by
        rw [edist_comm (T x) a]
        exact edist_triangle a (T x) b

/-- **Impossibility.** If a target is not decodable, there are two sessions and two latents with
different targets on which every decoder, using every recording the sessions produce, succeeds
with probabilities summing to at most one. `J` builds the law of all session data from what
the session reveals (for independent recordings, a product). -/
theorem not_decodable_chance [Nonempty Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    {Ω : Type*} [MeasurableSpace Ω] {M : S → Θ → Measure X} {p : ι → Θ → Θ} {φ : Θ → Y}
    (J : Measure X × (ι → Measure X) → Measure Ω)
    (hJ : ∀ s θ, IsProbabilityMeasure (J (reveal M p s θ))) (hnd : ¬ Decodable M p φ) :
    ∃ s s' θ θ', φ θ ≠ φ θ' ∧ ∀ T : Ω → Y, Measurable T →
      J (reveal M p s θ) (T ⁻¹' {φ θ}) + J (reveal M p s' θ') (T ⁻¹' {φ θ'}) ≤ 1 := by
  rw [decodable_iff] at hnd
  simp only [not_forall] at hnd
  obtain ⟨s, s', θ, θ', e, hne⟩ := hnd
  refine ⟨s, s', θ, θ', hne, fun T hT => ?_⟩
  rw [← e]
  haveI := hJ s θ
  exact chance_bound _ hT hne

/-- **Impossibility, metric form.** For a metric target, the two expected errors of any decoder
sum to at least the distance between the two targets. -/
theorem not_decodable_two_point [Nonempty Y] [PseudoEMetricSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {Ω : Type*} [MeasurableSpace Ω] {M : S → Θ → Measure X}
    {p : ι → Θ → Θ} {φ : Θ → Y} (J : Measure X × (ι → Measure X) → Measure Ω)
    (hJ : ∀ s θ, IsProbabilityMeasure (J (reveal M p s θ))) (hnd : ¬ Decodable M p φ) :
    ∃ s s' θ θ', φ θ ≠ φ θ' ∧ ∀ T : Ω → Y, Measurable T →
      edist (φ θ) (φ θ') ≤ ∫⁻ x, edist (T x) (φ θ) ∂J (reveal M p s θ)
        + ∫⁻ x, edist (T x) (φ θ') ∂J (reveal M p s' θ') := by
  rw [decodable_iff] at hnd
  simp only [not_forall] at hnd
  obtain ⟨s, s', θ, θ', e, hne⟩ := hnd
  refine ⟨s, s', θ, θ', hne, fun T hT => ?_⟩
  rw [← e]
  haveI := hJ s θ
  exact two_point _ hT _ _

end General

/-! ## §2 Calibration groups -/

section Group

variable {Θ ι X Y G : Type*} [MeasurableSpace X] [Group G] [MulAction G X]

/-- Session laws when the session applies an unknown calibration `g ∈ Γ` to every recording. -/
noncomputable def calLaw (μ : Θ → Measure X) (Γ : Subgroup G) : Γ → Θ → Measure X :=
  fun g θ => (μ θ).map ((g : G) • ·)

lemma map_smul_smul (hmeas : ∀ g : G, Measurable fun x : X => g • x) (ν : Measure X)
    (g h : G) : (ν.map (g • ·)).map (h • ·) = ν.map ((h * g) • ·) := by
  rw [Measure.map_map (hmeas h) (hmeas g)]
  congr 1
  funext x
  simp [mul_smul]

lemma map_one_smul (ν : Measure X) : ν.map ((1 : G) • ·) = ν := by
  simp

/-- **Group form.** With a calibration group, a target is decodable iff it agrees on any two
latents related by a calibration `g ∈ Γ` that also maps each item's law to its counterpart. -/
theorem decodable_group_iff [Nonempty Y] (hmeas : ∀ g : G, Measurable fun x : X => g • x)
    {μ : Θ → Measure X} {Γ : Subgroup G} {p : ι → Θ → Θ} {φ : Θ → Y} :
    Decodable (calLaw μ Γ) p φ ↔
      ∀ θ θ', ∀ g ∈ Γ, (∀ i, (μ (p i θ)).map (g • ·) = μ (p i θ')) →
        (μ θ).map (g • ·) = μ θ' → φ θ = φ θ' := by
  rw [decodable_iff]
  constructor
  · intro H θ θ' g hg hp hθ
    apply H ⟨g, hg⟩ 1 θ θ'
    simp only [reveal, calLaw, OneMemClass.coe_one, map_one_smul, Prod.mk.injEq]
    exact ⟨hθ, funext hp⟩
  · intro H s s' θ θ' e
    simp only [reveal, calLaw, Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    have key : ∀ ν ν' : Measure X, ν.map ((s : G) • ·) = ν'.map ((s' : G) • ·) →
        ν.map (((s' : G)⁻¹ * s) • ·) = ν' := by
      intro ν ν' h
      have := congrArg (fun m : Measure X => m.map (((s' : G)⁻¹) • ·)) h
      simpa [map_smul_smul hmeas] using this
    exact H θ θ' ((s' : G)⁻¹ * s) (Γ.mul_mem (Γ.inv_mem s'.2) s.2)
      (fun i => key _ _ (congrFun e2 i)) (key _ _ e1)

/-- **Floor.** Physical phantoms (items whose latent does not depend on the subject) never make
a non-identifiable target decodable. -/
theorem Decodable.identifiable (hmeas : ∀ g : G, Measurable fun x : X => g • x)
    {μ : Θ → Measure X} {Γ : Subgroup G} {s : ι → Θ} {φ : Θ → Y} [Nonempty Y]
    (h : Decodable (calLaw μ Γ) (fun i _ => s i) φ) :
    ∀ θ θ', μ θ = μ θ' → φ θ = φ θ' := fun θ θ' e =>
  (decodable_group_iff hmeas).1 h θ θ' 1 Γ.one_mem (fun _ => by simp) (by simp [e])

/-- **Base.** Phantoms whose joint stabilizer in `Γ` acts trivially on every law make every
identifiable target decodable. -/
theorem decodable_of_base (hmeas : ∀ g : G, Measurable fun x : X => g • x)
    {μ : Θ → Measure X} {Γ : Subgroup G} {s : ι → Θ} {φ : Θ → Y} [Nonempty Y]
    (hbase : ∀ g ∈ Γ, (∀ i, (μ (s i)).map (g • ·) = μ (s i)) → ∀ θ, (μ θ).map (g • ·) = μ θ)
    (hid : ∀ θ θ', μ θ = μ θ' → φ θ = φ θ') : Decodable (calLaw μ Γ) (fun i _ => s i) φ :=
  (decodable_group_iff hmeas).2 fun θ θ' g hg hp hθ =>
    hid θ θ' ((hbase g hg hp θ).symm.trans hθ)

/-- A target decodable under a calibration group stays decodable under any subgroup. -/
theorem Decodable.mono_group {μ : Θ → Measure X} {Γ Γ' : Subgroup G} (hle : Γ ≤ Γ')
    {p : ι → Θ → Θ} {φ : Θ → Y} (h : Decodable (calLaw μ Γ') p φ) :
    Decodable (calLaw μ Γ) p φ := by
  obtain ⟨dec, hdec⟩ := h
  exact ⟨dec, fun g θ => hdec ⟨g, hle g.2⟩ θ⟩

end Group

/-! ## §3 Optical instance: flow and volume channels on a two-element Windkessel -/

namespace Windkessel

/-- Calibration of a (flow, volume) phasor pair at one cardiac harmonic: complex gains `a, b` on
the two channels and a leak `β` of the volume signal into the flow channel. -/
@[ext] structure Cal where
  a : ℂˣ
  b : ℂˣ
  β : ℂ

namespace Cal

instance : One Cal := ⟨⟨1, 1, 0⟩⟩
instance : Mul Cal := ⟨fun g h => ⟨g.a * h.a, g.b * h.b, (g.a : ℂ) * h.β + g.β * h.b⟩⟩
instance : Inv Cal :=
  ⟨fun g => ⟨g.a⁻¹, g.b⁻¹, -(((g.a⁻¹ : ℂˣ) : ℂ) * g.β * ((g.b⁻¹ : ℂˣ) : ℂ))⟩⟩

@[simp] lemma one_a : (1 : Cal).a = 1 := rfl
@[simp] lemma one_b : (1 : Cal).b = 1 := rfl
@[simp] lemma one_β : (1 : Cal).β = 0 := rfl
@[simp] lemma mul_a (g h : Cal) : (g * h).a = g.a * h.a := rfl
@[simp] lemma mul_b (g h : Cal) : (g * h).b = g.b * h.b := rfl
@[simp] lemma mul_β (g h : Cal) : (g * h).β = (g.a : ℂ) * h.β + g.β * h.b := rfl
@[simp] lemma inv_a (g : Cal) : g⁻¹.a = g.a⁻¹ := rfl
@[simp] lemma inv_b (g : Cal) : g⁻¹.b = g.b⁻¹ := rfl
@[simp] lemma inv_β (g : Cal) :
    g⁻¹.β = -(((g.a⁻¹ : ℂˣ) : ℂ) * g.β * ((g.b⁻¹ : ℂˣ) : ℂ)) := rfl

instance : Group Cal where
  mul_assoc g h k := Cal.ext (mul_assoc _ _ _) (mul_assoc _ _ _) (by
    simp only [mul_β, mul_a, mul_b, Units.val_mul]
    ring)
  one_mul g := Cal.ext (one_mul _) (one_mul _) (by simp)
  mul_one g := Cal.ext (mul_one _) (mul_one _) (by simp)
  inv_mul_cancel g := Cal.ext (inv_mul_cancel _) (inv_mul_cancel _) (by
    have hb : ((g.b⁻¹ : ℂˣ) : ℂ) * g.b = 1 := Units.inv_mul g.b
    simp only [mul_β, inv_a, inv_β, one_β]
    linear_combination (-(((g.a⁻¹ : ℂˣ) : ℂ) * g.β)) * hb)

instance : SMul Cal (ℂ × ℂ) := ⟨fun g x => ((g.a : ℂ) * x.1 + g.β * x.2, (g.b : ℂ) * x.2)⟩

lemma smul_def (g : Cal) (x : ℂ × ℂ) :
    g • x = ((g.a : ℂ) * x.1 + g.β * x.2, (g.b : ℂ) * x.2) := rfl

instance : MulAction Cal (ℂ × ℂ) where
  one_smul x := by
    rw [smul_def]
    exact Prod.ext (by simp) (by simp)
  mul_smul g h x := by
    simp only [smul_def, mul_a, mul_b, mul_β, Units.val_mul]
    exact Prod.ext (by ring) (by ring)

lemma measurable_smul (g : Cal) : Measurable fun x : ℂ × ℂ => g • x := by
  simp only [smul_def]
  fun_prop

/-- Real channel gains and no leak: both channels read from the same frames of one sensor. -/
def gainR : Subgroup Cal where
  carrier := {g | g.β = 0 ∧ (g.a : ℂ).im = 0 ∧ (g.b : ℂ).im = 0}
  mul_mem' := by
    rintro g h ⟨hgβ, hga, hgb⟩ ⟨hhβ, hha, hhb⟩
    exact ⟨by simp [hgβ, hhβ], by simp [Complex.mul_im, hga, hha],
      by simp [Complex.mul_im, hgb, hhb]⟩
  one_mem' := ⟨rfl, by simp, by simp⟩
  inv_mem' := by
    rintro g ⟨hβ, ha, hb⟩
    exact ⟨by simp [hβ], by simp [Complex.inv_im, ha], by simp [Complex.inv_im, hb]⟩

/-- Complex channel gains and no leak: separate sensors with a relative delay. -/
def gainC : Subgroup Cal where
  carrier := {g | g.β = 0}
  mul_mem' := by
    rintro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    simp [hg, hh]
  one_mem' := rfl
  inv_mem' := by
    rintro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    simp [hg]

/-- Real gains with a real leak of volume into the flow channel (speckle contrast that also
responds to blood volume). -/
def leakR : Subgroup Cal where
  carrier := {g | g.β.im = 0 ∧ (g.a : ℂ).im = 0 ∧ (g.b : ℂ).im = 0}
  mul_mem' := by
    rintro g h ⟨hgβ, hga, hgb⟩ ⟨hhβ, hha, hhb⟩
    exact ⟨by simp [Complex.mul_im, hgβ, hhβ, hga, hhb], by simp [Complex.mul_im, hga, hha],
      by simp [Complex.mul_im, hgb, hhb]⟩
  one_mem' := ⟨by simp, by simp, by simp⟩
  inv_mem' := by
    rintro g ⟨hβ, ha, hb⟩
    exact ⟨by simp [Complex.mul_im, Complex.inv_im, hβ, ha, hb], by simp [Complex.inv_im, ha],
      by simp [Complex.inv_im, hb]⟩

lemma mem_gainR {g : Cal} : g ∈ gainR ↔ g.β = 0 ∧ (g.a : ℂ).im = 0 ∧ (g.b : ℂ).im = 0 :=
  Iff.rfl
lemma mem_gainC {g : Cal} : g ∈ gainC ↔ g.β = 0 := Iff.rfl
lemma mem_leakR {g : Cal} : g ∈ leakR ↔ g.β.im = 0 ∧ (g.a : ℂ).im = 0 ∧ (g.b : ℂ).im = 0 :=
  Iff.rfl

end Cal

open Cal

/-- Latent state of the vascular bed at one cardiac harmonic: resistance, compliance, and the law
of the inflow phasor. -/
structure Latent where
  R : ℝ
  C : ℝ
  hR : 0 < R
  hC : 0 < C
  ρ : Measure ℂ
  prob : IsProbabilityMeasure ρ
  power : 0 < ∫ q, Complex.normSq q ∂ρ

/-- The Windkessel time constant. -/
def tau (θ : Latent) : ℝ := θ.R * θ.C

variable (ω : ℝ)

/-- Volume phasor per unit flow phasor: `Q = C dP/dt + P/R` and `V = C P` give
`V = Q / (iω + 1/(RC))`. -/
noncomputable def transfer (θ : Latent) : ℂ :=
  (Complex.I * ω + (((θ.R * θ.C)⁻¹ : ℝ) : ℂ))⁻¹

/-- Ideal-device law of the (flow, volume) phasor pair. -/
noncomputable def law (θ : Latent) : Measure (ℂ × ℂ) :=
  θ.ρ.map fun q => (q, transfer ω θ * q)

/-- Cross-moment of volume against flow over flow power: the volume-per-flow slope of a law. -/
noncomputable def slope (ν : Measure (ℂ × ℂ)) : ℂ :=
  (∫ x, x.2 * conj x.1 ∂ν) / ∫ x, x.1 * conj x.1 ∂ν

/-- The decoder: `tan arg` of the inverse slope, over `ω`. -/
noncomputable def tauHat (z : ℂ) : ℝ := (z⁻¹).im / (ω * (z⁻¹).re)

lemma den_ne (θ : Latent) : Complex.I * ω + (((θ.R * θ.C)⁻¹ : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
    Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, zero_add, Complex.zero_re] at this
  exact (inv_pos.2 (mul_pos θ.hR θ.hC)).ne' this

lemma transfer_ne (θ : Latent) : transfer ω θ ≠ 0 := inv_ne_zero (den_ne ω θ)

lemma transfer_im_ne (hω : ω ≠ 0) (θ : Latent) : (transfer ω θ).im ≠ 0 := by
  have hpos : 0 < Complex.normSq (Complex.I * ω + (((θ.R * θ.C)⁻¹ : ℝ) : ℂ)) :=
    Complex.normSq_pos.2 (den_ne ω θ)
  rw [transfer, Complex.inv_im]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im, zero_mul,
    Complex.I_im, Complex.ofReal_re, one_mul, zero_add, add_zero]
  exact div_ne_zero (neg_ne_zero.2 hω) hpos.ne'

lemma tau_eq_of_transfer_eq {θ θ' : Latent} (h : transfer ω θ = transfer ω θ') :
    tau θ = tau θ' := by
  have h1 := congrArg Complex.re (inv_injective h)
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
    Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, zero_add] at h1
  exact inv_injective h1

lemma tauHat_real_mul (hω : ω ≠ 0) (θ : Latent) {r : ℝ} (hr : r ≠ 0) :
    tauHat ω ((r : ℂ) * transfer ω θ) = tau θ := by
  have hτ : θ.R * θ.C ≠ 0 := (mul_pos θ.hR θ.hC).ne'
  have e : ((r : ℂ) * transfer ω θ)⁻¹
      = ((r⁻¹ : ℝ) : ℂ) * (Complex.I * ω + (((θ.R * θ.C)⁻¹ : ℝ) : ℂ)) := by
    rw [transfer, mul_inv, inv_inv]
    simp only [Complex.ofReal_inv]
  rw [tauHat, e, Complex.re_ofReal_mul, Complex.im_ofReal_mul, tau]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
    Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, zero_add, Complex.add_im,
    Complex.mul_im, one_mul, add_zero]
  field_simp

/-- The slope of a law that scales a common input by `u` and `w` is `w / u`. -/
lemma slope_map (ρ : Measure ℂ) (hρ : 0 < ∫ q, Complex.normSq q ∂ρ) {u w : ℂ} (hu : u ≠ 0) :
    slope (ρ.map fun q => (u * q, w * q)) = w / u := by
  have hF : Measurable fun q : ℂ => (u * q, w * q) := by fun_prop
  have hS : (((∫ q, Complex.normSq q ∂ρ : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hcu : conj u ≠ 0 := (map_ne_zero _).2 hu
  have hI : ∫ q, ((Complex.normSq q : ℝ) : ℂ) ∂ρ = ((∫ q, Complex.normSq q ∂ρ : ℝ) : ℂ) :=
    integral_ofReal
  have hN : ∫ x, x.2 * conj x.1 ∂(ρ.map fun q => (u * q, w * q))
      = (w * conj u) * ((∫ q, Complex.normSq q ∂ρ : ℝ) : ℂ) := by
    rw [integral_map hF.aemeasurable (by fun_prop), ← hI, ← integral_const_mul]
    congr 1
    funext q
    dsimp only
    rw [map_mul, ← Complex.mul_conj]
    ring
  have hD : ∫ x, x.1 * conj x.1 ∂(ρ.map fun q => (u * q, w * q))
      = (u * conj u) * ((∫ q, Complex.normSq q ∂ρ : ℝ) : ℂ) := by
    rw [integral_map hF.aemeasurable (by fun_prop), ← hI, ← integral_const_mul]
    congr 1
    funext q
    dsimp only
    rw [map_mul, ← Complex.mul_conj]
    ring
  rw [slope, hN, hD]
  field_simp

lemma slope_law (θ : Latent) : slope (law ω θ) = transfer ω θ := by
  have e : law ω θ = θ.ρ.map fun q => ((1 : ℂ) * q, transfer ω θ * q) := by simp [law]
  rw [e, slope_map θ.ρ θ.power one_ne_zero, div_one]

/-- A session law is again a scaled copy of the inflow. -/
lemma session_eq (θ : Latent) (g : Cal) :
    (law ω θ).map (g • ·) = θ.ρ.map fun q =>
      (((g.a : ℂ) + g.β * transfer ω θ) * q, ((g.b : ℂ) * transfer ω θ) * q) := by
  rw [law, Measure.map_map (measurable_smul g) (by fun_prop)]
  congr 1
  funext q
  simp only [Function.comp, smul_def]
  exact Prod.ext (by ring) (by ring)

lemma slope_session (θ : Latent) (g : Cal) (hd : (g.a : ℂ) + g.β * transfer ω θ ≠ 0) :
    slope ((law ω θ).map (g • ·)) = (g.b : ℂ) * transfer ω θ / ((g.a : ℂ) + g.β * transfer ω θ) := by
  rw [session_eq, slope_map θ.ρ θ.power hd]

lemma slope_map_zero (ρ : Measure ℂ) (w : ℂ) :
    slope (ρ.map fun q => ((0 : ℂ) * q, w * q)) = 0 := by
  have hF : Measurable fun q : ℂ => ((0 : ℂ) * q, w * q) := by fun_prop
  rw [slope, integral_map hF.aemeasurable (by fun_prop)]
  simp

/-- The slope of a session law, with no condition on the flow-channel factor. -/
lemma slope_session' (θ : Latent) (g : Cal) :
    slope ((law ω θ).map (g • ·)) = (g.b : ℂ) * transfer ω θ / ((g.a : ℂ) + g.β * transfer ω θ) := by
  by_cases hd : (g.a : ℂ) + g.β * transfer ω θ = 0
  · rw [session_eq, hd, div_zero]
    exact slope_map_zero _ _
  · exact slope_session ω θ g hd

/-- A calibration that preserves a latent's law fixes its slope: `b = a + β c`. -/
lemma stab_slope {θs : Latent} {g : Cal} (h : (law ω θs).map (g • ·) = law ω θs) :
    (g.b : ℂ) = g.a + g.β * transfer ω θs := by
  have hs := congrArg slope h
  rw [slope_session', slope_law] at hs
  have hd : (g.a : ℂ) + g.β * transfer ω θs ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hs
    exact transfer_ne ω θs hs.symm
  rw [div_eq_iff hd] at hs
  exact mul_right_cancel₀ (transfer_ne ω θs) (by rw [hs]; ring)

lemma ofReal_re_of_im_eq_zero {z : ℂ} (h : z.im = 0) : ((z.re : ℝ) : ℂ) = z :=
  Complex.ext (by simp) (by simp [h])

/-- Under real gains without leak, the decoder returns `τ` from any session law. -/
lemma tauHat_session_gainR (hω : ω ≠ 0) {g : Cal} (hg : g ∈ gainR) (θ : Latent) :
    tauHat ω (slope ((law ω θ).map (g • ·))) = tau θ := by
  obtain ⟨hβ, ha, hb⟩ := mem_gainR.1 hg
  have ha0 : (g.a : ℂ) ≠ 0 := Units.ne_zero _
  have har : (((g.a : ℂ).re : ℝ) : ℂ) = g.a := ofReal_re_of_im_eq_zero ha
  have hbr : (((g.b : ℂ).re : ℝ) : ℂ) = g.b := ofReal_re_of_im_eq_zero hb
  have hd : (g.a : ℂ) + g.β * transfer ω θ ≠ 0 := by simp [hβ]
  have hare : (g.a : ℂ).re ≠ 0 := by
    intro h0; apply ha0; rw [← har, h0, Complex.ofReal_zero]
  have hbre : (g.b : ℂ).re ≠ 0 := by
    intro h0; apply Units.ne_zero g.b; rw [← hbr, h0, Complex.ofReal_zero]
  rw [slope_session ω θ g hd, hβ, zero_mul, add_zero, ← har, ← hbr]
  have : (((g.b : ℂ).re : ℝ) : ℂ) * transfer ω θ / (((g.a : ℂ).re : ℝ) : ℂ)
      = ((((g.b : ℂ).re / (g.a : ℂ).re) : ℝ) : ℂ) * transfer ω θ := by
    push_cast
    field_simp
  rw [this]
  exact tauHat_real_mul ω hω θ (div_ne_zero hbre hare)

/-- **Zero calibration.** When both channels come from the same frames (real gains, no leak), the
Windkessel time constant `τ = RC` is decoded with no calibration at all. -/
theorem tau_zero_calibration (hω : ω ≠ 0) :
    Decodable (calLaw (law ω) gainR) (fun i : Empty => i.elim) tau :=
  ⟨fun d => tauHat ω (slope d.1), fun g θ => tauHat_session_gainR ω hω g.2 θ⟩

/-- A latent with a deterministic inflow phasor `z`. -/
noncomputable def Latent.det (R C : ℝ) (hR : 0 < R) (hC : 0 < C) (z : ℂ) (hz : z ≠ 0) :
    Latent where
  R := R
  C := C
  hR := hR
  hC := hC
  ρ := Measure.dirac z
  prob := inferInstance
  power := by rw [integral_dirac]; exact Complex.normSq_pos.2 hz

lemma law_det (R C : ℝ) (hR : 0 < R) (hC : 0 < C) (z : ℂ) (hz : z ≠ 0) :
    law ω (Latent.det R C hR hC z hz)
      = Measure.dirac (z, transfer ω (Latent.det R C hR hC z hz) * z) := by
  simp [law, Latent.det]

/-- **Delay breaks zero calibration.** With complex gains (separate sensors, relative delay),
`τ` is not decodable without calibration. -/
theorem tau_not_zero_calibration_delay :
    ¬ Decodable (calLaw (law ω) gainC) (fun i : Empty => i.elim) tau := by
  rw [decodable_group_iff measurable_smul]
  intro H
  have hc := transfer_ne ω (Latent.det 1 1 one_pos one_pos 1 one_ne_zero)
  have hk : transfer ω (Latent.det 2 1 two_pos one_pos 1 one_ne_zero)
      / transfer ω (Latent.det 1 1 one_pos one_pos 1 one_ne_zero) ≠ 0 :=
    div_ne_zero (transfer_ne ω _) hc
  have hg : (⟨1, Units.mk0 _ hk, 0⟩ : Cal) ∈ gainC := rfl
  have := H (Latent.det 1 1 one_pos one_pos 1 one_ne_zero)
    (Latent.det 2 1 two_pos one_pos 1 one_ne_zero) _ hg (fun i => i.elim) (by
      rw [law_det, law_det, Measure.map_dirac' (measurable_smul _), smul_def]
      congr 1
      refine Prod.ext (by simp) ?_
      simp only [Units.val_mk0, mul_one]
      exact div_mul_cancel₀ _ hc)
  norm_num [tau, Latent.det] at this

/-- **One phantom suffices against delay.** -/
theorem tau_one_phantom_delay (θs : Latent) :
    Decodable (calLaw (law ω) gainC) (fun (_ : Unit) _ => θs) tau := by
  rw [decodable_group_iff measurable_smul]
  intro θ θ' g hg hp hθ
  have hβ : g.β = 0 := mem_gainC.1 hg
  have ha0 : (g.a : ℂ) ≠ 0 := Units.ne_zero _
  have hd : ∀ θ₀ : Latent, (g.a : ℂ) + g.β * transfer ω θ₀ ≠ 0 := fun _ => by simp [hβ]
  have hs := congrArg slope (hp ())
  rw [slope_session ω θs g (hd θs), slope_law] at hs
  have hab : (g.b : ℂ) = g.a := by
    rw [hβ, zero_mul, add_zero, div_eq_iff ha0] at hs
    exact mul_right_cancel₀ (transfer_ne ω θs) (by rw [hs]; ring)
  have hc := congrArg slope hθ
  rw [slope_session ω θ g (hd θ), slope_law, hβ, zero_mul, add_zero, hab,
    mul_div_cancel_left₀ _ ha0] at hc
  exact tau_eq_of_transfer_eq ω hc

lemma leak_den_ne {g : Cal} (hg : g ∈ leakR) {c : ℂ} (hc : c.im ≠ 0) :
    (g.a : ℂ) + g.β * c ≠ 0 := by
  obtain ⟨hβ, ha, _⟩ := mem_leakR.1 hg
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, ha, hβ, zero_mul, add_zero, zero_add,
    Complex.zero_im] at him
  have hβre : g.β.re = 0 := (mul_eq_zero.1 him).resolve_right hc
  have hβ0 : g.β = 0 := Complex.ext hβre hβ
  rw [hβ0, zero_mul, add_zero] at h
  exact Units.ne_zero _ h

/-- **Leak breaks zero calibration.** If speckle contrast also responds to blood volume, `τ` is not
decodable without calibration. -/
theorem tau_not_zero_calibration_leak :
    ¬ Decodable (calLaw (law ω) leakR) (fun i : Empty => i.elim) tau := by
  rw [decodable_group_iff measurable_smul]
  intro H
  have hd1 : Complex.I * ω + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hd2 : Complex.I * ω + 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hc1 : transfer ω (Latent.det 1 1 one_pos one_pos 1 one_ne_zero)
      = (Complex.I * ω + 1)⁻¹ := by
    norm_num [transfer, Latent.det]
  have e1 : (1 : ℂ) + (Complex.I * ω + 1)⁻¹ = (Complex.I * ω + 2) / (Complex.I * ω + 1) := by
    field_simp
    ring
  have h1c : (1 : ℂ) + (Complex.I * ω + 1)⁻¹ ≠ 0 := by
    rw [e1]
    exact div_ne_zero hd2 hd1
  have hc2 : transfer ω (Latent.det (1 / 2) 1 (by norm_num) one_pos _ h1c)
      = (Complex.I * ω + 2)⁻¹ := by
    norm_num [transfer, Latent.det]
  have hg : (⟨1, 1, 1⟩ : Cal) ∈ leakR := ⟨by simp, by simp, by simp⟩
  have := H (Latent.det 1 1 one_pos one_pos 1 one_ne_zero)
    (Latent.det (1 / 2) 1 (by norm_num) one_pos _ h1c) _ hg (fun i => i.elim) (by
      rw [law_det, law_det, Measure.map_dirac' (measurable_smul _), smul_def, hc1, hc2]
      congr 1
      refine Prod.ext (by simp) ?_
      simp only [Units.val_one, one_mul, mul_one]
      rw [e1]
      field_simp)
  norm_num [tau, Latent.det] at this

/-- **One phantom suffices against leak.** A single phantom of known latent, recorded in the same
session, restores decodability of `τ`. -/
theorem tau_one_phantom_leak (hω : ω ≠ 0) (θs : Latent) :
    Decodable (calLaw (law ω) leakR) (fun (_ : Unit) _ => θs) tau := by
  rw [decodable_group_iff measurable_smul]
  intro θ θ' g hg hp hθ
  obtain ⟨hβi, ha, hb⟩ := mem_leakR.1 hg
  have hcs := transfer_im_ne ω hω θs
  have hs := congrArg slope (hp ())
  rw [slope_session ω θs g (leak_den_ne hg hcs), slope_law,
    div_eq_iff (leak_den_ne hg hcs)] at hs
  -- `b cs = cs (a + β cs)` forces `b = a + β cs`, whose imaginary part forces `β = 0`.
  have hb' : (g.b : ℂ) = g.a + g.β * transfer ω θs :=
    mul_right_cancel₀ (transfer_ne ω θs) (by rw [hs]; ring)
  have him := congrArg Complex.im hb'
  simp only [Complex.add_im, Complex.mul_im, ha, hb, hβi, zero_mul, add_zero, zero_add] at him
  have hβre : g.β.re = 0 := (mul_eq_zero.1 him.symm).resolve_right hcs
  have hβ0 : g.β = 0 := Complex.ext hβre hβi
  have hab : (g.b : ℂ) = g.a := by rw [hb', hβ0, zero_mul, add_zero]
  have hc := congrArg slope hθ
  rw [slope_session ω θ g (leak_den_ne hg (transfer_im_ne ω hω θ)), slope_law, hβ0, zero_mul,
    add_zero, hab, mul_div_cancel_left₀ _ (Units.ne_zero _)] at hc
  exact tau_eq_of_transfer_eq ω hc

/-- **Pressure scale.** Compliance is not decodable under any calibration group with any set of
physical phantoms: `(R, C)` and `(2R, C/2)` produce the same law. -/
theorem compliance_not_decodable (Γ : Subgroup Cal) {ι : Type*} (s : ι → Latent) :
    ¬ Decodable (calLaw (law ω) Γ) (fun i _ => s i) Latent.C := by
  intro h
  have hid := Decodable.identifiable measurable_smul h
  have e : law ω (Latent.det 1 1 one_pos one_pos 1 one_ne_zero)
      = law ω (Latent.det 2 (1 / 2) two_pos (by norm_num) 1 one_ne_zero) := by
    rw [law_det, law_det]
    norm_num [transfer, Latent.det]
  have := hid _ _ e
  norm_num [Latent.det] at this

/-- Chance form of the pressure-scale impossibility: in any session, any measurable decoder of
compliance succeeds on `C = 1` and on `C = 1/2` with probabilities summing to at most one. -/
theorem compliance_chance (g : Cal) {T : ℂ × ℂ → ℝ} (hT : Measurable T) :
    ((law ω (Latent.det 1 1 one_pos one_pos 1 one_ne_zero)).map (g • ·)) (T ⁻¹' {1})
      + ((law ω (Latent.det 2 (1 / 2) two_pos (by norm_num) 1 one_ne_zero)).map (g • ·))
          (T ⁻¹' {1 / 2}) ≤ 1 := by
  have e : law ω (Latent.det 1 1 one_pos one_pos 1 one_ne_zero)
      = law ω (Latent.det 2 (1 / 2) two_pos (by norm_num) 1 one_ne_zero) := by
    rw [law_det, law_det]
    norm_num [transfer, Latent.det]
  rw [e, law_det, Measure.map_dirac' (measurable_smul g)]
  exact chance_bound _ hT (by norm_num)

/-- **An intervention moves the floor.** A recording after a known change of resistance
(`R ↦ R + Δ`), in the same session, makes compliance decodable with zero calibration. -/
theorem compliance_decodable_with_intervention (hω : ω ≠ 0) {Δ : ℝ} (hΔ : 0 < Δ) :
    Decodable (calLaw (law ω) gainR)
      (fun (_ : Unit) θ => { θ with R := θ.R + Δ, hR := add_pos θ.hR hΔ }) Latent.C := by
  refine ⟨fun d => (tauHat ω (slope (d.2 ())) - tauHat ω (slope d.1)) / Δ, fun g θ => ?_⟩
  show (tauHat ω (slope ((law ω _).map ((g : Cal) • ·)))
      - tauHat ω (slope ((law ω θ).map ((g : Cal) • ·)))) / Δ = θ.C
  rw [tauHat_session_gainR ω hω g.2, tauHat_session_gainR ω hω g.2, tau, tau]
  field_simp
  ring

/-! ### Delay and leak together: the inverse slope moves by a complex affine map

Under `g = (a, b, β)` the inverse slope `z = 1/κ` moves by `z ↦ (a/b) z + β/b`, a complex affine
map. One phantom pins one point and leaves the maps fixing it; two phantoms of distinct `τ` pin
two points, which fixes the map: the two-point calibration of a gain and an offset, in `ℂ`. -/

/-- **Two phantoms suffice for any calibration.** Phantoms of distinct time constants recorded in
the same session make `τ` decodable with complex gains (delay) and a complex leak together. -/
theorem tau_two_phantoms (θ₁ θ₂ : Latent) (h12 : tau θ₁ ≠ tau θ₂) :
    Decodable (calLaw (law ω) (⊤ : Subgroup Cal)) (fun (i : Bool) _ => if i then θ₁ else θ₂)
      tau := by
  rw [decodable_group_iff measurable_smul]
  intro θ θ' g _ hp hθ
  have hc12 : transfer ω θ₁ ≠ transfer ω θ₂ := fun h => h12 (tau_eq_of_transfer_eq ω h)
  have h1 := stab_slope ω (θs := θ₁) (by simpa using hp true)
  have h2 := stab_slope ω (θs := θ₂) (by simpa using hp false)
  have hβ : g.β = 0 := by
    have : g.β * (transfer ω θ₁ - transfer ω θ₂) = 0 := by linear_combination h2 - h1
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hc12)
  have hab : (g.b : ℂ) = g.a := by rw [h1, hβ, zero_mul, add_zero]
  have hc := congrArg slope hθ
  rw [slope_session', slope_law, hβ, zero_mul, add_zero, hab,
    mul_div_cancel_left₀ _ (Units.ne_zero _)] at hc
  exact tau_eq_of_transfer_eq ω hc

/-- **One phantom does not suffice for delay and leak together.** Whatever single phantom is
recorded, some calibration fixes its law exactly and still maps a subject with one time
constant onto a subject with another. -/
theorem tau_not_one_phantom (θs : Latent) :
    ¬ Decodable (calLaw (law ω) (⊤ : Subgroup Cal)) (fun (_ : Unit) _ => θs) tau := by
  rw [decodable_group_iff measurable_smul]
  intro H
  set x : ℝ := (θs.R * θs.C)⁻¹ with hxdef
  have hx : 0 < x := inv_pos.2 (mul_pos θs.hR θs.hC)
  set zs : ℂ := Complex.I * ω + (x : ℂ) with hzs
  have hzs_ne : zs ≠ 0 := den_ne ω θs
  have hcs : transfer ω θs = zs⁻¹ := rfl
  have hden : ∀ t : ℝ, 0 < t → Complex.I * ω + (t : ℂ) ≠ 0 := by
    intro t ht h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, zero_add, Complex.zero_re] at this
    linarith
  have h1 : Complex.I * ω + ((x + 1 : ℝ) : ℂ) ≠ 0 := hden _ (by linarith)
  have h2 : Complex.I * ω + ((x + 2 : ℝ) : ℂ) ≠ 0 := hden _ (by linarith)
  -- subject latents with `1/τ = x + 1` and `1/τ' = x + 2`
  have hR1 : 0 < 1 / (x + 1) := by positivity
  have hR2 : 0 < 1 / (x + 2) := by positivity
  set θ := Latent.det (1 / (x + 1)) 1 hR1 one_pos 1 one_ne_zero
  have hc : transfer ω θ = (Complex.I * ω + ((x + 1 : ℝ) : ℂ))⁻¹ := by
    simp only [θ, transfer, Latent.det, mul_one, one_div, inv_inv]
  set z1 : ℂ := 2 - zs * transfer ω θ with hz1
  have hz1' : z1 = (Complex.I * ω + ((x + 2 : ℝ) : ℂ)) / (Complex.I * ω + ((x + 1 : ℝ) : ℂ)) := by
    rw [hz1, hc, hzs]
    field_simp
    push_cast
    ring
  have hz1_ne : z1 ≠ 0 := by rw [hz1']; exact div_ne_zero h2 h1
  set θ' := Latent.det (1 / (x + 2)) 1 hR2 one_pos z1 hz1_ne
  have hc' : transfer ω θ' = (Complex.I * ω + ((x + 2 : ℝ) : ℂ))⁻¹ := by
    simp only [θ', transfer, Latent.det, mul_one, one_div, inv_inv]
  -- the calibration `a = 2, b = 1, β = -zs`
  have h2u : (2 : ℂ) ≠ 0 := two_ne_zero
  let g : Cal := ⟨Units.mk0 2 h2u, 1, -zs⟩
  have hfix : (law ω θs).map (g • ·) = law ω θs := by
    rw [law, Measure.map_map (measurable_smul g) (by fun_prop)]
    congr 1
    funext q
    simp only [Function.comp, smul_def, g, Units.val_mk0, Units.val_one, one_mul]
    refine Prod.ext ?_ rfl
    simp only
    rw [hcs]
    field_simp
    ring
  have hmove : (law ω θ).map (g • ·) = law ω θ' := by
    rw [law_det, law_det, Measure.map_dirac' (measurable_smul g)]
    congr 1
    simp only [smul_def, g, Units.val_mk0, Units.val_one, one_mul, mul_one]
    refine Prod.ext ?_ ?_
    · simp only [hz1]
      ring
    · rw [hc', hz1', hc]
      field_simp
  have := H θ θ' g trivial (fun _ => hfix) hmove
  simp only [tau, θ, θ', Latent.det, mul_one] at this
  have hx12 : (1 : ℝ) / (x + 1) ≠ 1 / (x + 2) := by
    rw [Ne, div_eq_div_iff (by linarith) (by linarith)]
    linarith
  exact hx12 this

/-- **Delay with leak, zero calibration.** With no items `τ` is not decodable once delay is
possible; restricting the group cannot repair it. -/
theorem tau_not_zero_calibration_full :
    ¬ Decodable (calLaw (law ω) (⊤ : Subgroup Cal)) (fun i : Empty => i.elim) tau :=
  fun h => tau_not_zero_calibration_delay ω (h.mono_group le_top)

end Windkessel

end BCIMetrology
