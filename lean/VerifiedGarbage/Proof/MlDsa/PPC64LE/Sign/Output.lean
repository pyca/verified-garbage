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
  omega

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
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega]
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
  omega

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
    fun i hi => hintIs_keepW hL hk.frame (sepAll_sub c3 (by unfold oP; omega) (by unfold oP; omega)) h0 (h.h i hi),
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
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega
  have hc : 0 < cLen p ∧ cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega
  refine WP.mono (copyS h.k.sc.site (sb := .r31) (so := oCT) (db := .r28) (dO := 0) (len := cLen p)
    ⟨sptr_ok rfl (by decide), by osep hF⟩ ⟨sptr_ok rfl (by decide), by osep hF⟩ (show ix Reg.r28 ∈ sWb2 by decide)
    (by decide) (by decide) (by omega) hc.1 (by osep hF)) fun s1 ⟨k1, b1⟩ => ⟨h.keep k1 (by osep hF), ?_⟩
  rw [Nat.mul_zero, Nat.add_zero]
  show bytesAt s1.mem (lpa (slay2 p STK σ) (.r28, 0)) (cLen p) = _
  have e : bytesAt s.mem (lpa (slay2 p STK σ) (.r31, oCT)) (cLen p) = CTv p σ κ := hct
  rw [b1, e]
  simp [zEnc]

theorem packZ_ok {σ : State} {κ r : Nat} (hr : r < p.ℓ) {s : State} (h : OS p STK σ κ r s) :
    WP isa (packZ P p r) s (OS p STK σ κ (r + 1)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hsh : sigH p = cLen p + zLen p * p.ℓ := rfl
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega
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
    (by decide) (by omega)
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
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega
  have hz := hF.lz; have hsg := hF.sig; have hom := hF.om
  exact ⟨⟨sptr_ok rfl (by decide), by osep hF⟩, ⟨sptr_ok rfl (by clt hF), by osep hF⟩,
    show ix Reg.r28 ∈ sWb2 by decide, by osep hF, by rw [Nat.add_sub_cancel_left]; exact hF.hip, by omega,
    by rw [Nat.add_sub_cancel_left], ⟨by omega, by clt hF, by omega, by omega, by omega⟩⟩

theorem hpack_ok {σ : State} {κ : Nat} {s : State} (h : OS p STK σ κ p.ℓ s) :
    WP isa (hintBitPackAt P (Impl.MlDsa.PPC64LE.Sign.hP 0) (256 * p.k) p.ω (.r28, sigH p) (p.ω + p.k)) s fun s' =>
      IK p STK σ s' ∧ bytesAt s'.mem ((slay2 p STK σ).A 4 0) p.sigLen = sigV p σ κ ∧ s'.gpr .r24 = 1 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hsh : sigH p = cLen p + zLen p * p.ℓ := rfl
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega
  have hz := hF.lz; have hsg := hF.sig; have hom := hF.om
  unfold hintBitPackAt
  refine KeyGen.hbp_ok hP.hintBitPack h.o.k.sc.site hS (hbp_m hF)
    (by rw [Nat.add_sub_cancel_left]; exact hones_ok h.o) fun s' k' hb' =>
    ⟨h.o.k.keep k' (by osep hF), ?_, (k'.cs .r24 (by decide)).trans h.o.r24⟩
  have e0 := bytes_keepW h.o.k.sc.site.ok k'.frame (i := 4) (o := 0) (l := cLen p + zLen p * p.ℓ) (by osep hF)
    (by decide) (by omega)
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
    (fun r _ hr s h => packZ_ok hP hF hS (by omega) h) s1 h1) fun s2 h2 => ?_)
  rw [Nat.zero_add] at h2
  exact hpack_ok hP hF hS h2

end

end VG.Proof.MlDsa.PPC64LE.Sign
