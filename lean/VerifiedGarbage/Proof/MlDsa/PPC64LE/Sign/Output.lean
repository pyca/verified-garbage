module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.LoopCT
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.LoopCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA signing on PPC64LE: the signature

As on 32-bit ARM (`Proof/MlDsa/Arm/Sign/PhaseO.lean`). Once an iteration
passed: `c̃`, then `BitPack(z[r], γ₁ - 1, γ₁)` for each `r` (in range, as `z`
passed its norm check: `zrange_of_norm`), then `HintBitPack(h)` (with at
most `ω` 1s) to `sig`, which then holds `sigEncode(c̃, z mod± q, h)`
(`output_ok`). Two runs that agree on the hint leak the same (`output_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of polyIs_keepW bytes_keepW
  copyS)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Impl.MlDsa.PPC64LE.KeyGen (callAt seqR)
open VG.Impl.MlKem.PPC64LE (copy)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (sigOf)
open VG.Spec.Sha3 (bytesAt)

/-! ## `z` in range -/

theorem coeff_val {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = f[i].val := by
  have e := congrArg (·[i]) h.2
  simp only [polyAt, Vector.getElem_ofFn] at e
  rw [← e, Fin.val_ofNat, Nat.mod_eq_of_lt (h.1 i hi)]

theorem zrange_of_norm {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {B γ : Nat}
    (hn : normRq [f] < B) (hB : B ≤ γ) :
    ∀ i < n, -((γ - 1 : Nat) : Int) ≤ modPm (coeffAt m a i).toNat q ∧ modPm (coeffAt m a i).toNat q ≤ (γ : Int) := by
  intro i hi
  have := (VG.Proof.MlDsa.Round.normRq_lt f B).mp hn i hi
  rw [getElem!_pos f i hi] at this
  rw [coeff_val h hi]
  simp only [normZq] at this
  omega_arith

/-! ## The hint -/

theorem hintAt_of {m : Mem} {a : Addr} {k : Nat} {f : Nat → Vector Bool n}
    (h : ∀ i < k, HintIs m (a + BitVec.ofNat 64 (1024 * i)) 1 [f i]) :
    hintAt m a k = (List.range k).map f := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  apply Vector.ext
  intro j hj
  have hn : n = 256 := rfl
  have e := (h i hi).2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
  have ea : coeffAt m a (256 * i + j) = coeffAt m (a + BitVec.ofNat 64 (1024 * i)) j := by
    simp only [coeffAt]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega_arith]
  rw [Vector.getElem_ofFn, ea, e, getElem!_pos (f i) j hj]
  cases (f i)[j] <;> decide

theorem hintOnes_map (k : Nat) (f : Nat → Vector Bool n) :
    hintOnes ((List.range k).map f) = onesSum f k := by
  simp only [hintOnes, onesSum, List.map_map]
  rfl

theorem SL_hint (p : Params) (STK : Nat) (σ : State) (i : Nat) :
    SL p STK σ (5 + i) = SL p STK σ 5 + BitVec.ofNat 64 (1024 * i) := by
  simp only [SL, Lay.A, oP, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega_arith

/-! ## The signature -/

/-- The encodings of the first `r` polynomials of `z`. -/
abbrev zEnc (p : Params) (σ : State) (κ r : Nat) : List Byte :=
  (List.range r).flatMap fun j => bitPack ((Zv p σ κ j).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁

/-- `sigEncode` of what the passing iteration returns. -/
abbrev sigV (p : Params) (σ : State) (κ : Nat) : List Byte :=
  sigOf p (CTv p σ κ, (List.range p.ℓ).map (Zv p σ κ), (List.range p.k).map (Hv p σ κ))

/-- An iteration with counter `κ` passed: `c̃`, `z` and `h`. -/
structure OI (p : Params) (STK : Nat) (σ : State) (κ : Nat) (s : State) : Prop where
  k : IK p STK σ s
  z : ∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ κ r)
  h : ∀ i < p.k, HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ κ i]
  pass : PassV p σ κ
  r24 : s.gpr .r24 = 1

/-- `c̃` and the first `r` polynomials of `z` in `sig`. -/
structure OS (p : Params) (STK : Nat) (σ : State) (κ r : Nat) (s : State) : Prop where
  o : OI p STK σ κ s
  sig : bytesAt s.mem ((slay2 p STK σ).A 4 0) (cLen p + zLen p * r) = CTv p σ κ ++ zEnc p σ κ r

/-- A part that writes `W` keeps `OI`. -/
def oiChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  ikChk p STK W && sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (yBase p + 0), 1024 * (p.ℓ - 0)) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (5 + 0), 1024 * (p.k - 0)) W

theorem OI.keep {p : Params} {STK : Nat} {σ : State} {κ : Nat} {s s' : State} (h : OI p STK σ κ s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((slay2 p STK σ).RL W) s s') (hc : oiChk p STK W = true) :
    OI p STK σ κ s' := by
  simp only [oiChk, Bool.and_eq_true] at hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := hc
  have hL := h.k.sc.site.ok
  have h0 : 0 ∈ sWb2 := by decide
  exact ⟨h.k.keep hk c1, fun r hr => famR_keep hL h0 hk.frame c2 (fun j _ hj => h.z j hj) r (Nat.zero_le _) hr,
    fun i hi => hintIs_keepW hL hk.frame (sepAll_sub c3 (by unfold oP; omega_arith) (by unfold oP; omega_arith)) h0 (h.h i hi),
    h.pass, (hk.cs .r24 (by decide)).trans h.r24⟩

/-- `ssep`, with the checks of the signature. -/
syntax "osep " term:max : tactic
macro_rules
  | `(tactic| osep $hF) => `(tactic| ssep $hF [oiChk, ikChk, sc2Chk, yBase, s1Base, nSec])

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem outCopy_ok {σ : State} {κ : Nat} {s : State} (h : OI p STK σ κ s)
    (hct : bytesAt s.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = CTv p σ κ) :
    WP isa (copy .r31 oCT .r28 0 (cLen p)) s (OS p STK σ κ 0) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hsh : sigH p = cLen p + zLen p * p.ℓ := rfl
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega_arith) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hc : 0 < cLen p ∧ cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  refine WP.mono (copyS h.k.sc.site (sb := .r31) (so := oCT) (db := .r28) (dO := 0) (len := cLen p)
    ⟨sptr_ok rfl (by decide), by osep hF⟩ ⟨sptr_ok rfl (by decide), by osep hF⟩ (show ix Reg.r28 ∈ sWb2 by decide)
    (by decide) (by decide) (by omega_arith) hc.1 (by osep hF)) fun s1 ⟨k1, b1⟩ => ⟨h.keep k1 (by osep hF), ?_⟩
  rw [Nat.mul_zero, Nat.add_zero]
  show bytesAt s1.mem (lpa (slay2 p STK σ) (.r28, 0)) (cLen p) = _
  have e : bytesAt s.mem (lpa (slay2 p STK σ) (.r31, oCT)) (cLen p) = CTv p σ κ := hct
  rw [b1, e]
  simp [zEnc]

theorem packZ_ok {σ : State} {κ r : Nat} (hr : r < p.ℓ) {s : State} (h : OS p STK σ κ r s) :
    WP isa (packZ P p r) s (OS p STK σ κ (r + 1)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hsh : sigH p = cLen p + zLen p * p.ℓ := rfl
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega_arith) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hz := hF.lz; have hsg := hF.sig
  have hzr := h.o.z r hr
  have hm : zLen p * r + zLen p ≤ zLen p * p.ℓ := by
    have := Nat.mul_le_mul_left (zLen p) (show r + 1 ≤ p.ℓ from hr); rwa [Nat.mul_succ] at this
  have m : KeyGen.BpOk (slay2 p STK σ) sWb2 (yP p r) (p.γ₁ - 1) p.γ₁ (.r28, sigZ p r) (zLen p) :=
    ⟨⟨sptr_ok rfl (by clt hF), by osep hF⟩, ⟨sptr_ok rfl (by clt hF), by osep hF⟩,
      show ix Reg.r28 ∈ sWb2 by decide, by osep hF, hF.zbp, hF.zl⟩
  have hpz : normRq [Zv p σ κ r] < p.γ₁ - p.β := h.o.pass.1 r hr
  unfold packZ bitPackAt
  refine KeyGen.bp_ok hP.bitPack h.o.k.sc.site hS m
    hzr.1 (zrange_of_norm hzr hpz (Nat.sub_le _ _)) fun s' k' hb' => ?_
  refine ⟨h.o.keep k' (by osep hF), ?_⟩
  have e0 := bytes_keepW h.o.k.sc.site.ok k'.frame (i := 4) (o := 0) (l := cLen p + zLen p * r) (by osep hF)
    (by decide) (by omega_arith)
  have e1 : polyAt s.mem (lpa (slay2 p STK σ) (yP p r)) = Zv p σ κ r := hzr.2
  rw [e1] at hb'
  have b2 : bytesAt s'.mem ((slay2 p STK σ).A 4 0 + BitVec.ofNat 64 (cLen p + zLen p * r)) (zLen p) =
      bitPack ((Zv p σ κ r).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁ := by
    simp only [lpa, Lay.A, ix, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.zero_add] at hb' ⊢; exact hb'
  rw [Nat.mul_succ, ← Nat.add_assoc, Proof.MlKem.bytesAt_add, e0, h.sig, b2, zEnc, zEnc, List.range_succ,
    List.flatMap_append, List.flatMap_singleton, List.append_assoc]

omit hP hF hS in
theorem hones_ok {σ : State} {κ : Nat} {s : State} (h : OI p STK σ κ s) :
    hintOnes (hintAt s.mem (SL p STK σ 5) p.k) ≤ p.ω := by
  rw [hintAt_of (f := Hv p σ κ) fun i hi => by have := h.h i hi; rwa [SL_hint] at this, hintOnes_map]
  exact h.pass.2.2.2

omit hP hS in
theorem hbp_m {σ : State} : KeyGen.HbpOk (slay2 p STK σ) sWb2 (pS 5) (256 * p.k) p.ω (.r28, sigH p) (p.ω + p.k) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hsh : sigH p = cLen p + zLen p * p.ℓ := rfl
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega_arith) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hz := hF.lz; have hsg := hF.sig; have hom := hF.om
  exact ⟨⟨sptr_ok rfl (by decide), by osep hF⟩, ⟨sptr_ok rfl (by clt hF), by osep hF⟩,
    show ix Reg.r28 ∈ sWb2 by decide, by osep hF, by rw [Nat.add_sub_cancel_left]; exact hF.hip, by omega_arith,
    by rw [Nat.add_sub_cancel_left], ⟨by omega_arith, by clt hF, by omega_arith, by omega_arith, by omega_arith⟩⟩

theorem hpack_ok {σ : State} {κ : Nat} {s : State} (h : OS p STK σ κ p.ℓ s) :
    WP isa (hintBitPackAt P (Impl.MlDsa.PPC64LE.Sign.hP 0) (256 * p.k) p.ω (.r28, sigH p) (p.ω + p.k)) s fun s' =>
      IK p STK σ s' ∧ bytesAt s'.mem ((slay2 p STK σ).A 4 0) p.sigLen = sigV p σ κ ∧ s'.gpr .r24 = 1 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hsh : sigH p = cLen p + zLen p * p.ℓ := rfl
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega_arith) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hz := hF.lz; have hsg := hF.sig; have hom := hF.om
  unfold hintBitPackAt
  refine KeyGen.hbp_ok hP.hintBitPack h.o.k.sc.site hS (hbp_m hF)
    (by rw [Nat.add_sub_cancel_left]; exact hones_ok h.o) fun s' k' hb' =>
    ⟨h.o.k.keep k' (by osep hF), ?_, (k'.cs .r24 (by decide)).trans h.o.r24⟩
  have e0 := bytes_keepW h.o.k.sc.site.ok k'.frame (i := 4) (o := 0) (l := cLen p + zLen p * p.ℓ) (by osep hF)
    (by decide) (by omega_arith)
  rw [Nat.add_sub_cancel_left, hintAt_of (f := Hv p σ κ) fun i hi => by
    have := h.o.h i hi; rwa [SL_hint] at this] at hb'
  have b2 : bytesAt s'.mem ((slay2 p STK σ).A 4 0 + BitVec.ofNat 64 (cLen p + zLen p * p.ℓ)) (p.ω + p.k) =
      hintBitPack p.ω p.k ((List.range p.k).map (Hv p σ κ)) := by
    simp only [lpa, Lay.A, ix, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.zero_add] at hb' ⊢; exact hb'
  rw [hF.sig, show sigH p = cLen p + zLen p * p.ℓ from rfl, Proof.MlKem.bytesAt_add, e0, h.sig, b2]
  simp only [sigV, sigOf, sigEncode, zEnc, List.map_map, List.flatMap_map]
  rfl

theorem output_ok {σ : State} {κ : Nat} {s : State} (h : OI p STK σ κ s)
    (hct : bytesAt s.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = CTv p σ κ) :
    WP isa (output P p) s fun s' => IK p STK σ s' ∧ bytesAt s'.mem ((slay2 p STK σ).A 4 0) p.sigLen = sigV p σ κ ∧
      s'.gpr .r24 = 1 := by
  unfold output
  refine WP.seq (WP.mono (outCopy_ok hF h hct) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (wp_seqR (I := fun r => OS p STK σ κ r) p.ℓ 0
    (fun r _ hr s h => packZ_ok hP hF hS (by omega_arith) h) s1 h1) fun s2 h2 => ?_)
  rw [Nat.zero_add] at h2
  exact hpack_ok hP hF hS h2

end

/-! ## Two runs -/

/-- A relational step from each run's correctness and the leaks' equality. -/
theorem liftG {P Q₀ Q : State → State → Prop} {c : Prog isa}
    (hw : ∀ x y, P x y → ∃ A B : State → Prop, WP isa c x A ∧ WP isa c y B ∧ ∀ x' y', A x' → B y' → Q₀ x' y' → Q x' y')
    (ht : RelCT isa P c Q₀) : RelCT isa P c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨A, B, ⟨_, u₁, f₁, a₁⟩, ⟨_, u₂, f₂, b₂⟩, hQ⟩ := hw _ _ hr
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', hQ _ _ a₁ b₂ hq⟩

theorem coeff_hint {m : Mem} {a : Addr} {i j : Nat} :
    coeffAt m a (256 * i + j) = coeffAt m (a + BitVec.ofNat 64 (1024 * i)) j := by
  simp only [coeffAt]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega_arith]

/-- Two memories holding the same hint have the same coefficients. -/
theorem coeffs_eq {mx my : Mem} {a : Addr} {k : Nat} {F : Nat → Vector Bool n}
    (hx : ∀ i < k, HintIs mx (a + BitVec.ofNat 64 (1024 * i)) 1 [F i])
    (hy : ∀ i < k, HintIs my (a + BitVec.ofNat 64 (1024 * i)) 1 [F i]) :
    (List.range (256 * k)).map (fun c => (coeffAt mx a c).toNat) =
      (List.range (256 * k)).map (fun c => (coeffAt my a c).toNat) := by
  refine List.map_congr_left fun c hc => ?_
  rw [List.mem_range] at hc
  have hi : c / 256 < k := by omega_arith
  have hj : c % 256 < 256 := Nat.mod_lt _ (by decide)
  have e : c = 256 * (c / 256) + c % 256 := (Nat.div_add_mod c 256).symm
  rw [e, coeff_hint, coeff_hint]
  have ex := (hx _ hi).2 0 (by decide) _ hj
  have ey := (hy _ hi).2 0 (by decide) _ hj
  simp only [Nat.mul_zero, Nat.zero_add] at ex ey
  rw [ex, ey]

/-- Two runs that passed, agreeing on the hint. -/
def OR (p : Params) (STK : Nat) (r : Nat) (x y : State) : Prop :=
  ∃ σ₁ σ₂ κ₁ κ₂, SPre p STK σ₁ ∧ SPre p STK σ₂ ∧ sPub p σ₁ σ₂ ∧ OS p STK σ₁ κ₁ r x ∧ OS p STK σ₂ κ₂ r y ∧
    ∀ i < p.k, Hv p σ₁ κ₁ i = Hv p σ₂ κ₂ i

/-- The taint check of the copy of `c̃` to `sig` does not depend on `λ`. -/
theorem copyCt_taint (l : Nat) : (VG.PPC64LE.taint.check (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (copy .r31 oCT .r28 0 l)
    (VG.Taint.hintOf VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31]) (copy .r31 oCT .r28 0 32))).isSome =
      true := rfl

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem outCopy_tr :
    RelCT isa (fun x y => ∃ σ₁ σ₂ κ₁ κ₂, SPre p STK σ₁ ∧ SPre p STK σ₂ ∧ sPub p σ₁ σ₂ ∧
      (OI p STK σ₁ κ₁ x ∧ bytesAt x.mem ((slay2 p STK σ₁).A 0 oCT) (cLen p) = CTv p σ₁ κ₁) ∧
      (OI p STK σ₂ κ₂ y ∧ bytesAt y.mem ((slay2 p STK σ₂).A 0 oCT) (cLen p) = CTv p σ₂ κ₂) ∧
      ∀ i < p.k, Hv p σ₁ κ₁ i = Hv p σ₂ κ₂ i) (copy .r31 oCT .r28 0 (cLen p)) (OR p STK 0) := by
  refine liftG (Q₀ := fun _ _ => True) (fun x y ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, h₁, h₂, he⟩ => ⟨_, _, outCopy_ok hF h₁.1 h₁.2,
    outCopy_ok hF h₂.1 h₂.2, fun x' y' a b _ => ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, a, b, he⟩⟩) ?_
  exact RelCT.mono (srel2p (I := fun σ s => ∃ κ, OI p STK σ κ s) (fun σ s ⟨_, h⟩ => h.k.sc)
    (copyCt_taint (cLen p))) (fun x y ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, h₁, h₂, _⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, pub, ⟨κ₁, h₁.1⟩, ⟨κ₂, h₂.1⟩⟩) fun _ _ h => h

theorem packZ_tr {r : Nat} (hr : r < p.ℓ) : RelCT isa (OR p STK r) (packZ P p r) (OR p STK (r + 1)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hsh : sigH p = cLen p + zLen p * p.ℓ := rfl
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega_arith) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hz := hF.lz; have hsg := hF.sig
  have m : ∀ σ, KeyGen.BpOk (slay2 p STK σ) sWb2 (yP p r) (p.γ₁ - 1) p.γ₁ (.r28, sigZ p r) (zLen p) := fun σ =>
    have hm : zLen p * r + zLen p ≤ zLen p * p.ℓ := by
      have := Nat.mul_le_mul_left (zLen p) (show r + 1 ≤ p.ℓ from hr); rwa [Nat.mul_succ] at this
    ⟨⟨sptr_ok rfl (by clt hF), by osep hF⟩, ⟨sptr_ok rfl (by clt hF), by osep hF⟩,
      show ix Reg.r28 ∈ sWb2 by decide, by osep hF, hF.zbp, hF.zl⟩
  have hrng : ∀ {σ κ x}, OS p STK σ κ r x → Reduced x.mem (lpa (slay2 p STK σ) (yP p r)) ∧
      ∀ i < n, -((p.γ₁ - 1 : Nat) : Int) ≤ modPm (coeffAt x.mem (lpa (slay2 p STK σ) (yP p r)) i).toNat q ∧
        modPm (coeffAt x.mem (lpa (slay2 p STK σ) (yP p r)) i).toNat q ≤ (p.γ₁ : Int) := fun h =>
    ⟨(h.o.z r hr).1, zrange_of_norm (h.o.z r hr) (h.o.pass.1 r hr) (Nat.sub_le _ _)⟩
  refine liftG (Q₀ := fun _ _ => True) (fun x y ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, h₁, h₂, he⟩ => ⟨_, _, packZ_ok hP hF hS hr h₁,
    packZ_ok hP hF hS hr h₂, fun x' y' a b _ => ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, a, b, he⟩⟩) ?_
  unfold packZ bitPackAt
  refine RelCT.mono (RelCT.exists_ fun σ => KeyGen.bp_tr hP.bitPack hS (m σ)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧
      (Reduced x.mem (lpa (slay2 p STK σ) (yP p r)) ∧
        ∀ i < n, -((p.γ₁ - 1 : Nat) : Int) ≤ modPm (coeffAt x.mem (lpa (slay2 p STK σ) (yP p r)) i).toNat q ∧
          modPm (coeffAt x.mem (lpa (slay2 p STK σ) (yP p r)) i).toNat q ≤ (p.γ₁ : Int)) ∧
      (Reduced y.mem (lpa (slay2 p STK σ) (yP p r)) ∧
        ∀ i < n, -((p.γ₁ - 1 : Nat) : Int) ≤ modPm (coeffAt y.mem (lpa (slay2 p STK σ) (yP p r)) i).toNat q ∧
          modPm (coeffAt y.mem (lpa (slay2 p STK σ) (yP p r)) i).toNat q ≤ (p.γ₁ : Int)))
    fun x y ⟨T, hx, hy⟩ => ⟨T.1, T.2.1, T.2.2, hx.1, hy.1, hx.2, hy.2⟩)
    (fun x y ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, h₁, h₂, _⟩ => ⟨σ₁, sc2_twoL pub h₁.o.k.sc h₂.o.k.sc, hrng h₁,
      by rw [slay2_pub pub]; exact hrng h₂⟩) fun _ _ h => h


theorem hpack_tr :
    RelCT isa (OR p STK p.ℓ) (hintBitPackAt P (Impl.MlDsa.PPC64LE.Sign.hP 0) (256 * p.k) p.ω (.r28, sigH p) (p.ω + p.k))
      fun _ _ => True := by
  unfold hintBitPackAt
  refine RelCT.mono (RelCT.exists_ fun σ => KeyGen.hbp_tr hP.hintBitPack hS (hbp_m hF (σ := σ))
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧
      hintOnes (hintAt x.mem (SL p STK σ 5) p.k) ≤ p.ω ∧ hintOnes (hintAt y.mem (SL p STK σ 5) p.k) ≤ p.ω ∧
      (List.range (256 * p.k)).map (fun c => (coeffAt x.mem (SL p STK σ 5) c).toNat) =
        (List.range (256 * p.k)).map (fun c => (coeffAt y.mem (SL p STK σ 5) c).toNat))
    fun x y ⟨T, ox, oy, e⟩ => ⟨T.1, T.2.1, T.2.2, by rw [Nat.add_sub_cancel_left]; exact ox,
      by rw [Nat.add_sub_cancel_left]; exact oy, e⟩) ?_ fun _ _ h => h
  rintro x y ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, h₁, h₂, he⟩
  refine ⟨σ₁, sc2_twoL pub h₁.o.k.sc h₂.o.k.sc, hones_ok h₁.o, by rw [SL_pub pub]; exact hones_ok h₂.o,
    coeffs_eq (F := Hv p σ₁ κ₁) (fun i hi => by have := h₁.o.h i hi; rwa [SL_hint] at this) fun i hi => ?_⟩
  have := h₂.o.h i hi
  rw [SL_hint, ← SL_pub pub, ← he i hi] at this
  exact this

/-- Two runs that passed, and agree on the hint, leak the same. -/
theorem output_tr :
    RelCT isa (fun x y => ∃ σ₁ σ₂ κ₁ κ₂, SPre p STK σ₁ ∧ SPre p STK σ₂ ∧ sPub p σ₁ σ₂ ∧
      (OI p STK σ₁ κ₁ x ∧ bytesAt x.mem ((slay2 p STK σ₁).A 0 oCT) (cLen p) = CTv p σ₁ κ₁) ∧
      (OI p STK σ₂ κ₂ y ∧ bytesAt y.mem ((slay2 p STK σ₂).A 0 oCT) (cLen p) = CTv p σ₂ κ₂) ∧
      ∀ i < p.k, Hv p σ₁ κ₁ i = Hv p σ₂ κ₂ i) (output P p) fun _ _ => True := by
  unfold output
  refine RelCT.seq (outCopy_tr hF) (RelCT.seq ?_ (hpack_tr hP hF hS))
  simpa using rr_seqR (R := fun r => OR p STK r) p.ℓ 0 fun r _ hr => packZ_tr hP hF hS (by omega_arith)
end

end VG.Proof.MlDsa.PPC64LE.Sign
