module
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Base

public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Top
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlDsa.DecideAt

/-!
# ML-DSA verification on x86 (32-bit): the contract

`vg_mldsa*_verify_core` of the parameter sets of Table 1 meets
`verifyCoreContract` with 96 bytes of stack (`verify_verified`), for any
verified implementations of the primitives it calls (`PrimsOk`): the body,
as a leaf, from the contract's precondition and public data (`pre_of`,
`pub_of`, `t1Ok_of`), to its postcondition (`VFin`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params)

/-- The contract's precondition on `t1`, as the proof's. -/
theorem t1Ok_of {p : Params} (hF : VFacts p) {s₀ : State} (hp : TPre (YV p) s₀)
    (h : T1In p s₀.mem ((arg s₀ 4).setWidth 64) (Spec.Sha3.bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen)) :
    T1Ok p s₀ := fun r hr => by
  have e := h r hr
  rw [PreparedKey.public_poly p _ hr] at e
  rw [Buf.addr_eq hp (b := tB r) (by lvd)]
  simp only [vPk, addr0]
  exact e

/-- `vg_mldsa{44,65,87}_verify_core` of the parameter sets of Table 1 meets
`verifyCoreContract` with 96 bytes of stack (given that its precondition can
hold, which a run of `vg_mldsa*_prepare_verifying_key` shows). -/
theorem verify_verified {P : Prims} (hP : PrimsOk P) (p : Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : ∃ s, (verifyCoreContract p X86.abi 96).pre s) :
    Verified X86.target (verify P p) (verifyCoreContract p X86.abi 96) := by
  have hF := vfacts hp
  have hb : Piece (fun s => TPre (YV p) s ∧ T1Ok p s) (TPub (YV p) (lkV p)) (fun s₀ s => s = P0 s₀)
      (fun s₀ s => Ctx (YV p) s₀ s ∧ Done p s₀ s) (body P p) :=
    { wp := fun s₀ s h₀ ha => ((body_piece hP hF).wp s₀ s h₀.1 ⟨ha, h₀.2⟩).mono fun _ h => ⟨h.1.1.1, h.1⟩
      ct := fun s₀ s₀' h₀ h₀' hq => ((body_piece hP hF).ct s₀ s₀' h₀.1 h₀'.1 hq).mono
        (fun _ _ ⟨a, a'⟩ => ⟨⟨a, h₀.2⟩, ⟨a', h₀'.2⟩⟩) fun _ _ h => h }
  have hl := Piece.leaf (W (YV p)) (body_nosp hP p) (fun _ hp => ⟨hp.1.E0_big, by have := hp.1.sp'; omega⟩)
    (fun _ hp => hp.1.hW) (fun _ _ _ _ hq => hq.1) (hb.mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h.2⟩)
  refine Piece.verified ((hl.pre_mono (fun _ h => ⟨(pre_of h).1, t1Ok_of hF (pre_of h).1 (pre_of h).2⟩)
    fun _ _ _ _ h => pub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) hsat
  obtain ⟨habi, -, -, s, ⟨⟨-, hd⟩, hax⟩, hm, hax'⟩ := hq
  refine ⟨habi, ?_⟩
  sig_post [verifyCoreContract, verifyCoreSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  rw [sw_app, hax', hax]
  simp only [vPk, vMu, vSig, addr0] at hd
  exact hd

end VG.Proof.MlDsa.X86.Verify
