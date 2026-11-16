module

import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Cmp
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Compute
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp4
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Cmp
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Compute
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp4
meta import VerifiedGarbage.Proof.MlDsa.Verify.Final
meta import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-DSA verification on AArch64: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

The checks and the taint analyses of `c̃′ = H(μ ‖ w1Encode(w′₁))`
(`hash_chk`, `hash_taint`) and of its comparison with `c̃` (`cmp_taint`), and
the epilogue (`epi_vpiece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt Bounds minBounds rejNTTPoly sampleInBall simpleBitPack verifyMu normRq normR)
open VG.Proof.MlDsa (polyAt Reduced PolyIs HintIs)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Proof.MlDsa.Verify (w1Row aSeed)

/-- `verifyMu` of the inputs of a run from `σ`, with the bounds `b`. -/
abbrev vv (p : Params) (σ : State) (b : Bounds) : Option Bool := verifyMu p b (vPk p σ) (vMu σ) (vSig p σ)

/-- At the end, before the epilogue: the result in `x24`. -/
def VFin (p : Params) (σ s : State) : Prop :=
  VC p σ s ∧ ((s.gpr .x24 = 1 ∧ ∃ b, vv p σ b = some true) ∨ (s.gpr .x24 = 0 ∧ vv p σ minBounds ≠ some true))

theorem false_ne {p : Params} {σ : State} {b : Bounds} (h : vv p σ b = some false) : vv p σ minBounds ≠ some true :=
  fun hm => by
    have e₁ := Proof.MlDsa.Verify.verifyMu_mono (Proof.MlDsa.Verify.bmax_left b minBounds).rejNTT
      (Proof.MlDsa.Verify.bmax_left b minBounds).ball h
    have e₂ := Proof.MlDsa.Verify.verifyMu_mono (Proof.MlDsa.Verify.bmax_right b minBounds).rejNTT
      (Proof.MlDsa.Verify.bmax_right b minBounds).ball hm
    rw [e₁] at e₂
    cases e₂

/-! ## The hash -/

/-- `w1Encode(w′₁)`. -/
abbrev w1Enc (p : Params) (σ : State) (h : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → Poly) (c0 : Poly) :
    List Byte :=
  (List.range p.k).flatMap fun r => simpleBitPack (w1Row p (vPk p σ) (vSig p σ) A' (ntt c0) h r) (w1Max p)

/-- The input pieces of the hash. -/
abbrev hIns (p : Params) : List Impl.MlKem.AArch64.Piece :=
  [⟨.x26, 0, 64⟩, ⟨.x28, oP (p.k * p.ℓ + 0), p.k * w1Len p⟩]

theorem hash_chk {p : Params} (hF : VFacts p) : hashChk (vR p) (vW p) (hIns p) ⟨.x28, oCT, p.ctildeLen⟩ = true := by
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; have := hF.ct.2; have := hF.w1
  unfold hashChk pieceChk; vlayd

theorem hash_taint {p : Params} (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∀ {P : State → State → Prop}, (∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ bases, x.gpr r = y.gpr r) →
      RelCT isa P ((shake256With keccak.callee) (hIns p) [⟨.x28, oCT, p.ctildeLen⟩]) fun _ _ => True := by
  intro P hr
  obtain ⟨hint, hh⟩ := keccak.mldsaVerifyHashTaint p hp
  exact VectorTaint.relRegs bases hr hh

theorem cmp_taint {p : Params} (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∀ {P : State → State → Prop}, (∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ bases, x.gpr r = y.gpr r) →
      RelCT isa P (cmpAnd (sc oCT) (.x27, 0) p.ctildeLen) fun _ _ => True := by
  intro P hr
  rcases hp with rfl | rfl | rfl
  · exact taintRel bases hr (by taint_decide)
  · exact taintRel bases hr (by taint_decide)
  · exact taintRel bases hr (by taint_decide)

theorem flatMap_congr' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-! ## The function -/

theorem normOk_zero (p : Params) (σ : State) : normOk p σ 0 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem epi_vpiece {S : Nat} {p : Params} (hF : VFacts p) :
    VPiece p S (VFin p) (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.verifyContract p AArch64.abi S).post σ s)
      (.block epi) := by
  refine ⟨fun σ s hp ⟨hv, hr⟩ => ?_, vrel_of (Q := VTwo p S) (taintRel [.x28] (fun x y h => h.x28)
    (by taint_decide)) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => vc_two hF p₁ p₂ pub h₁.1 h₂.1⟩
  have L := hv.lay hF hp
  have hin : InRegions (s.rd ++ s.wr) (σ.gpr .x3 + BitVec.ofNat 64 SV) 48 := by
    have := L.inR (p := svP) (l := 48) (by have := hF.scr; have := hF.k; vlayd)
    rwa [pa, hv.top.x28] at this
  refine WP.mono (epi_ok hv.top hin) fun s' ⟨ha, hx, _⟩ => ⟨ha, ?_⟩
  sig_post [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs]
  rcases hr with ⟨e, hb⟩ | ⟨e, hb⟩
  · exact .inl ⟨by rw [hx, e]; rfl, hb⟩
  · exact .inr ⟨by rw [hx, e]; rfl, hb⟩

end VG.Proof.MlDsa.AArch64.Verify
