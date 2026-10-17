module

public import VerifiedGarbage.Proof.Bignum.Arm.PcFailArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ZeroCT
public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Impl.Bignum.Arm.PcFn
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # RSA rejection zeroing depends only on public buffer dimensions -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pcFail_ct {base dst src : BitVec 32} {len k : Nat} (hk : k ≤ 1024) :
    RelCT isa (fun s t => PcStack base dst src len k s ∧ PcStack base dst src len k t ∧
      s.gpr .r6 = BitVec.ofNat 32 k ∧ t.gpr .r6 = BitVec.ofNat 32 k ∧ s.sp = t.sp)
      PcFn.fail (fun _ _ => True) := by
  let P := fun (s t : State) => PcStack base dst src len k s ∧ PcStack base dst src len k t ∧
    s.gpr .r6 = BitVec.ofNat 32 k ∧ t.gpr .r6 = BitVec.ofNat 32 k ∧ s.sp = t.sp
  have arithmetic : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.dp .add .lr .r6 (.imm 7), .mov .lr (.shifted .lr .lsr 3),
        .mov .lr (.shifted .lr .lsl 2)]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h)
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have last : RelCT isa (fun s t => s.sp = t.sp) (.block [.mov .r3 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have args : RelCT isa P (.block PcFn.failArgs) (fun _ _ => True) :=
    (RelCT.block_append (arithmetic.seq (RelCT.block_append ((loadStack_ct .r0 4).seq last)))).mono
      (fun _ _ h => h.2.2.2.2) (fun _ _ h => h)
  let Q := fun t : State => t.gpr .r0 = dst ∧ t.gpr .lr = BitVec.ofNat 32 (4 * Spec.Rsa.modulusWords k)
  have wp (s : State) (stack : PcStack base dst src len k s) (count : s.gpr .r6 = BitVec.ofNat 32 k) :
      WP isa (.block PcFn.failArgs) s Q :=
    WP.mono (pcFailArgs_ok s stack hk count) (fun _ h => ⟨h.1, h.2.1⟩)
  have ready := args.wp (fun s t h => ⟨wp s h.1 h.2.2.1, wp t h.2.1 h.2.2.2.1⟩)
  have zeroing : RelCT isa (fun s t => s.gpr .r0 = dst ∧ t.gpr .r0 = dst ∧
      s.gpr .lr = BitVec.ofNat 32 (4 * Spec.Rsa.modulusWords k) ∧
      t.gpr .lr = BitVec.ofNat 32 (4 * Spec.Rsa.modulusWords k)) zero (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨zero_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.trans h.2.1.symm, h.2.2.1.trans h.2.2.2.symm⟩ e1 e2, trivial⟩
  have finish : RelCT isa (fun _ _ => True) (.block [.mov .r0 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact (ready.mono (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩)).seq (zeroing.seq finish)

end VG.Proof.Bignum.Arm
