module

public import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
public import VerifiedGarbage.Proof.Bignum.Arm.StageCT
public import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
meta import VerifiedGarbage.Impl.Bignum.Arm.MontFinish
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Final reduction leaks only its count and pointers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

structure FinishReady (base : BitVec 32) (size tmp out acc mod n : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp
  count : s.mem.readW (off (State.addr base) tmp) 32 = BitVec.ofNat 32 n
  outPtr : s.mem.readW (off (State.addr base) (tmp + 24)) 32 = base + BitVec.ofNat 32 out
  accPtr : s.mem.readW (off (State.addr base) (tmp + 28)) 32 = base + BitVec.ofNat 32 acc
  mPtr : s.mem.readW (off (State.addr base) (tmp + 8)) 32 = base + BitVec.ofNat 32 mod

theorem montFinish_ct {base : BitVec 32} {size tmp out acc mod n : Nat} (ht : tmp + 32 ≤ size) :
    RelCT isa (fun s t => FinishReady base size tmp out acc mod n s ∧
      FinishReady base size tmp out acc mod n t) montFinish (fun _ _ => True) := by
  let P := FinishReady base size tmp out acc mod n
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 tmp ∧
    s.gpr .r7 = BitVec.ofNat 32 n ∧ s.gpr .r9 = base + BitVec.ofNat 32 out ∧
    s.gpr .r10 = base + BitVec.ofNat 32 acc ∧ s.gpr .r12 = base + BitVec.ofNat 32 mod ∧
    s.gpr .lr = BitVec.ofNat 32 n
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block finishArgs) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    simpa only [List.mem_singleton, forall_eq] using h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block finishArgs) s Q := by
    refine WP.mono (finishArgs_ok s h.workspace ht h.ptr h.count h.outPtr h.accPtr h.mPtr) ?_
    rintro t ⟨p0, p9, p10, p12, count, lr, _⟩
    exact ⟨p0, count, p9, p10, p12, lr⟩
  unfold montFinish
  refine (pair_posts ct wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  refine ⟨csub_ct s t tr1 tr2 u v trivial trivial ?_ e1 e2, trivial⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases h with ⟨⟨s0, s7, s9, s10, s12, slr⟩, ⟨t0, t7, t9, t10, t12, tlr⟩⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact s0.trans t0.symm
  · exact s7.trans t7.symm
  · exact s9.trans t9.symm
  · exact s10.trans t10.symm
  · exact s12.trans t12.symm
  · exact slr.trans tlr.symm

end VG.Proof.Bignum.Arm
