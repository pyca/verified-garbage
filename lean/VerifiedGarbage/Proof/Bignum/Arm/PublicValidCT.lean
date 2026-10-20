module
public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrepare
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.PublicPrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.PublicApplyCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # Modulus precomputation and the public RSA arithmetic path share a public trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem publicValid_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicValidInput base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicValidInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.valid (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  have countFit := (pc_dimensions h.1.buffers.minLength h.1.buffers.maxLength h.1.buffers.space).2.2.2.2
  let P := fun (s t : State) => PublicPrepared base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicPrepared base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  have wp (s : State) {xb : List Byte} (h : PublicPrepared base dst np ep xp len k eLen nb eb xb s) :
      WP isa precompute s (PublicArithmetic base dst np ep xp len k eLen nb eb xb) :=
    WP.mono (publicPrecompute_ok s h) (fun _ h => h.1)
  have ready := (relCT_keep_sp ((precompute_ct countFit).mono (P' := P)
    (fun _ _ h => ⟨h.1.input, h.2.1.input, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have applyCT := publicApply_ct.mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PublicArithmetic base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicArithmetic base dst np ep xp len k eLen nb eb xb2 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)
  exact (publicPrepare_ct.seq (ready.seq applyCT)) s t tr1 tr2 u v h e1 e2

end VG.Proof.Bignum.Arm
