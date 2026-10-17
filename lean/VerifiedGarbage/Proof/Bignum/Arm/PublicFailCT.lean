module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicFail
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
public import VerifiedGarbage.Proof.Bignum.Arm.PublicArgsCT
meta import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Invalid-key output clearing has a public trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem publicFail_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicBodyInput base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicBodyInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.fail (fun _ _ => True) := by
  have zero : RelCT isa (fun _ _ => True) (.block [.mov .r2 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have args : RelCT isa (fun s t => s.sp = t.sp) (.block PublicFn.failArgs) (fun _ _ => True) :=
    RelCT.block_append (M := isa) (l₁ := [.ldrSp .r0 4, .ldrSp .lr 12]) (l₂ := [.mov .r2 (.imm 0)])
      ((stackLoads_ct [(.r0, 4), (.lr, 12)]).seq (zero.mono (fun _ _ _ => trivial) (fun _ _ h => h)))
  let P := fun (s t : State) => PublicBodyInput base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicBodyInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  let Q := fun s : State => s.gpr .r0 = dst ∧ s.gpr .lr = BitVec.ofNat 32 k
  have ready := (args.mono (P' := P) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (F₁ := Q) (F₂ := Q) (fun s t h => ⟨
      WP.mono (publicFailArgs_ok s h.1.stack) (fun _ j => ⟨j.1, j.2.1⟩),
      WP.mono (publicFailArgs_ok t h.2.1.stack) (fun _ j => ⟨j.1, j.2.1⟩)⟩)
  have loop : RelCT isa (fun s t => True ∧ Q s ∧ Q t) maskBytes (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨maskBytes_ct s t tr1 tr2 u v trivial trivial
      ⟨h.2.1.1.trans h.2.2.1.symm, h.2.1.2.trans h.2.2.2.symm⟩ e1 e2, trivial⟩
  have ret : RelCT isa (fun _ _ => True) (.block [.mov .r0 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact ready.seq (loop.seq ret)

end VG.Proof.Bignum.Arm
