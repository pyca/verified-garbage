module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Hint
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Steps
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Hint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Steps
meta import VerifiedGarbage.Proof.MlDsa.Verify.Mem
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Site
public import VerifiedGarbage.Proof.MlDsa.Contract

/-!
# ML-DSA verification on PPC64LE: `z`

As on 32-bit ARM (`Proof/MlDsa/Arm/Verify/Z.lean`): each `z[i]`, unpacked
from the signature to polynomial `8 + i`, and `r24 ← r24 ∧ (‖z[i]‖∞ < γ₁ - β)`
(`zOne_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Verify

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee BuOk bu_ok
  bu_tr nl_ok nl_tr polyIs_keepW keepD zx and24_ok)
open VG.Impl.MlDsa.PPC64LE.Verify
open VG.Impl.MlDsa.PPC64LE.KeyGen (and24)
open VG.Spec.MlDsa (Params toRq normRq)
open VG.Proof.MlDsa (HintIs PolyIs polyAt Reduced)
open VG.Proof.MlDsa.Verify (vZ)
open VG.Spec.Sha3 (bytesAt)

/-- `‖z[i]‖∞ < γ₁ - β` for every `i < j`. -/
abbrev zOk (p : Params) (σ : State) (j : Nat) : Bool :=
  decide (∀ i < j, normRq [toRq (vZ p (sgOf p σ) i)] < p.γ₁ - p.β)

/-- A hint kept by a part that writes apart from it. -/
theorem hintIs_keepW {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
    (hf : Frame (L.RL W) m m') {i o k : Nat} (h : sepAll L.sizes (i, o, 1024 * k) W = true) (hw : i ∈ Wb)
    (hk : 1024 * k ≤ 2 ^ 64) {hh : List (Vector Bool Spec.MlDsa.n)} (hi : HintIs m (L.A i o) k hh) :
    HintIs m' (L.A i o) k hh :=
  Proof.MlDsa.Verify.hintIs_frame hf hk (keepD hL h hw) hi

/-- After the hint and the first `j` of `z`. -/
structure V2 (p : Params) (STK : Nat) (j : Nat) (σ s : State) : Prop where
  vc : VC p STK σ s
  hint : ∃ h, hintOf p σ = some h ∧ HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h
  z : ∀ i < j, PolyIs s.mem ((vlay p STK σ).A 0 (oP (8 + i))) (toRq (vZ p (sgOf p σ) i))
  r24 : s.gpr .r24 = flag (zOk p σ j)

theorem V2.keep {p : Params} (hF : VFacts p) {STK j : Nat} {σ s s' : State} (h : V2 p STK j σ s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((vlay p STK σ).RL W) s s') (hc : vcChk p STK W = true)
    (hh : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 0, 1024 * p.k) W = true)
    (hz : ∀ i < j, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (8 + i), 1024) W = true) :
    V2 p STK j σ s' := by
  have hL := h.vc.site.ok
  obtain ⟨hh', e, hi⟩ := h.hint
  exact ⟨h.vc.keep hk hc, ⟨hh', e, hintIs_keepW hL hk.frame hh (by decide) (by have := hF.k; omega_arith) hi⟩,
    fun i hi' => polyIs_keepW hL hk.frame (hz i hi') (by decide) rfl (h.z i hi'),
    by rw [hk.cs _ (by decide)]; exact h.r24⟩

theorem flag_and (a b : Bool) : flag a &&& flag b = flag (a && b) := by
  cases a <;> cases b <;> decide

theorem zOk_succ (p : Params) (σ : State) (j : Nat) :
    zOk p σ (j + 1) = (zOk p σ j && decide (normRq [toRq (vZ p (sgOf p σ) j)] < p.γ₁ - p.β)) := by
  simp only [zOk]
  rw [← Bool.decide_and]
  refine decide_eq_decide.mpr (Iff.intro (fun h => ⟨fun i hi => h i (by omega_arith), h j (by omega_arith)⟩) fun h i hi => ?_)
  rcases (by omega_arith : i < j ∨ i = j) with hi | rfl
  exacts [h.1 i hi, h.2]

/-! ## One `z[i]` -/

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem bu_m {σ : State} {j : Nat} (hj : j < p.ℓ) :
    BuOk (vlay p STK σ) vWb (.r28, p.ctildeLen + lenZ p * j) (lenZ p) (p.γ₁ - 1) p.γ₁ (pZ j) := by
  have hl := hF.l
  obtain ⟨hb, hlz, hg⟩ := hF.bu
  refine ⟨⟨vptr_ok rfl ?_, ?_⟩, ⟨vptr_ok rfl (by unfold oP; omega_arith), by vsep hF⟩, show ix Reg.r31 ∈ vWb by decide,
    ?_, hb, hlz, ?_⟩
  · rcases hF.ct with e | e | e <;> rcases hF.lz with e' | e' <;> rw [e, e'] <;> omega_arith
  · rcases hF.lz with e | e <;> vsep hF [hF.sig, hF.hint, e]
  · rcases hF.lz with e | e <;> vsep hF [hF.sig, hF.hint, e]
  · rcases hF.lz with e | e <;> rw [e] <;> omega_arith

/-- After `z[j]` is unpacked. -/
abbrev Z1 (p : Params) (STK j : Nat) (σ s : State) : Prop :=
  V2 p STK j σ s ∧ PolyIs s.mem ((vlay p STK σ).A 0 (oP (8 + j))) (toRq (vZ p (sgOf p σ) j))

theorem bu_piece {j : Nat} (hj : j < p.ℓ) :
    VPiece p STK (V2 p STK j) (Z1 p STK j)
      (bitUnpackAt P (.r28, p.ctildeLen + lenZ p * j) (lenZ p) (p.γ₁ - 1) p.γ₁ (pZ j)) := by
  have hl := hF.l
  refine ⟨fun σ s _ h => ?_, ?_⟩
  · unfold bitUnpackAt
    refine bu_ok hP.bitUnpack h.vc.site hS (bu_m hF hj) fun s' k' hz => ⟨h.keep hF k' ?_ ?_ ?_, ?_⟩
    · rcases hF.lz with e | e <;> vsep hF [vcChk, hF.sig, hF.hint, e]
    · vsep hF
    · intro i hi; vsep hF
    · have e : bytesAt s.mem (lpa (vlay p STK σ) (.r28, p.ctildeLen + lenZ p * j)) (lenZ p) =
          ((sgOf p σ).drop (p.ctildeLen + lenZ p * j)).take (lenZ p) :=
        sig_slice h.vc (by rw [hF.sig, hF.hint]; rcases hF.lz with e | e <;> rw [e] <;> omega_arith)
      rw [e] at hz
      exact hz
  · unfold bitUnpackAt
    exact rel_of (RelCT.exists_ fun σ => bu_tr hP.bitUnpack hS (bu_m hF hj) fun x y h => h)
      fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩

/-- After the norm of `z[j]`. -/
abbrev Z2 (p : Params) (STK j : Nat) (σ s : State) : Prop :=
  Z1 p STK j σ s ∧ zx (s.gpr .r3) = flag (decide (normRq [toRq (vZ p (sgOf p σ) j)] < p.γ₁ - p.β))

theorem nl_piece {j : Nat} (hj : j < p.ℓ) :
    VPiece p STK (Z1 p STK j) (Z2 p STK j) (normLtAt P (pZ j) (p.γ₁ - p.β)) := by
  have hl := hF.l
  have pf : ∀ σ, PtrIn (vlay p STK σ) (pZ j) 1024 := fun σ => ⟨vptr_ok rfl (by unfold oP; omega_arith), by vsep hF⟩
  refine ⟨fun σ s _ h => ?_, ?_⟩
  · unfold normLtAt
    have hr0 : Reduced s.mem (lpa (vlay p STK σ) (pZ j)) := h.2.1
    have hb : p.γ₁ - p.β < 2 ^ 31 := hF.nb.1
    refine nl_ok hP.normLt h.1.vc.site hS (bd := p.γ₁ - p.β) (pf σ) hb hr0 fun s' k' hr => ⟨⟨h.1.keep hF k'
      (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF),
      polyIs_keepW h.1.vc.site.ok k'.frame (by vsep hF) (by decide) rfl h.2⟩, ?_⟩
    rw [show polyAt s.mem (lpa (vlay p STK σ) (pZ j)) = _ from h.2.2] at hr
    exact zx_of (by rw [hr]; simp only [decide_eq_true_eq])
  · unfold normLtAt
    refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      Reduced x.mem (lpa (vlay p STK σ) (pZ j)) ∧ Reduced y.mem (lpa (vlay p STK σ) (pZ j)))
      (RelCT.exists_ fun σ => nl_tr hP.normLt hS (bd := p.γ₁ - p.β) (pf σ) hF.nb.1
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub h₁ h₂ => ?_
    have r₂ : Reduced _ (lpa (vlay p STK _) (pZ j)) := h₂.2.1
    rw [← vlay_pub pub] at r₂
    exact ⟨σ₁, vc_twoL pub h₁.1.vc h₂.1.vc, h₁.2.1, r₂⟩

omit hP hF hS in
theorem and24z_piece {j : Nat} : VPiece p STK (Z2 p STK j) (V2 p STK (j + 1)) (.block and24) := by
  refine ⟨fun σ s _ h => WP.mono (and24_ok s) fun s' ⟨_, e24, hr⟩ => ?_,
    vrel31 (fun _ _ h => h.1.1.vc) (by taint_decide)⟩
  obtain ⟨hh, e, hi⟩ := h.1.1.hint
  refine ⟨h.1.1.vc.regs2 hr, ⟨hh, e, by rw [hr.mem]; exact hi⟩, fun i hi' => ?_, ?_⟩
  · rw [hr.mem]
    rcases (by omega_arith : i < j ∨ i = j) with hi' | rfl
    exacts [h.1.1.z i hi', h.1.2]
  · rw [e24, h.1.1.r24, h.2, flag_and, zOk_succ]

theorem zOne_piece {j : Nat} (hj : j < p.ℓ) : VPiece p STK (V2 p STK j) (V2 p STK (j + 1)) (zOne P p j) :=
  (bu_piece hP hF hS hj).seq ((nl_piece hP hF hS hj).seq and24z_piece)

end

end VG.Proof.MlDsa.PPC64LE.Verify
