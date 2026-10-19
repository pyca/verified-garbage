module
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Lay

import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
import VerifiedGarbage.Proof.MlKem.Arm.CallsCT
meta import VerifiedGarbage.Proof.MlKem.Arm.CallsCT
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.BlockTr
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Hash
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Top
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlKem.Arm.HashCT
import VerifiedGarbage.Proof.MlKem.Arm.Loops
import VerifiedGarbage.Proof.MlKem.Arm.NttInv
import VerifiedGarbage.Proof.MlKem.Arm.RowSum
import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze
meta import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sign.BlockTr
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Hash
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Top
meta import VerifiedGarbage.Proof.MlDsa.Round.Decompose
meta import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Sign.Mem
meta import VerifiedGarbage.Proof.MlDsa.Sign.Setup
meta import VerifiedGarbage.Proof.MlKem.Arm.HashCT
meta import VerifiedGarbage.Proof.MlKem.Arm.Loops
meta import VerifiedGarbage.Proof.MlKem.Arm.NttInv
meta import VerifiedGarbage.Proof.MlKem.Arm.RowSum
meta import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze

/-!
# ML-DSA signing on ARMv7: copies leak only their addresses

The setup of a copy accesses no memory, and its loop leaks only the pointers
and the count in `r0`–`r2` (by the taint analysis), so two runs of a copy
between the same addresses leak the same (`copy_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign

theorem copySetup_nomem (dst src : Ptr) (n : Nat) :
    ∀ i ∈ lea .r0 src ++ lea .r1 dst ++ movi .r2 n, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [lea, movi, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Two runs of a copy from the same addresses leak the same. -/
theorem copy_tr {dst src : Ptr} {n : Nat} (b1 : src.1 ∈ bases) (b2 : dst.1 ∈ bases) {P : State → State → Prop}
    (hP : ∀ x y, P x y → x.gpr dst.1 = y.gpr dst.1 ∧ x.gpr src.1 = y.gpr src.1) :
    RelCT isa P (copy dst src n) fun _ _ => True := by
  unfold copy
  refine RelCT.seq (R := fun (x y : State) => ∀ r ∈ [Reg.r0, .r1, .r2], x.gpr r = y.gpr r)
    (postDep (block_nomem_tr (copySetup_nomem dst src n))
      (fun x y _ => ⟨copySetup_ok b1 b2 x, copySetup_ok b1 b2 y⟩)
      fun x y x' y' hp ⟨a0, a1, a2, _⟩ ⟨c0, c1, c2, _⟩ => ?_)
    (VG.Proof.MlKem.Arm.taint_prog [.r0, .r1, .r2] (fun _ _ h => h) (by native_taint_decide))
  obtain ⟨e1, e2⟩ := hP x y hp
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a0, c0, e2]
  · rw [a1, c1, e1]
  · rw [a2, c2]

end VG.Proof.MlDsa.Arm.Sign
