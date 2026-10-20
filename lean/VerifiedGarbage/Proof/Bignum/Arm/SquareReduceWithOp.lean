module

public import VerifiedGarbage.Impl.Bignum.Arm.SquareReduceWith
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Spec.Rsa.Mont
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Bignum.Arm.RowKernel
import VerifiedGarbage.Proof.Bignum.Arm.SquareReduceWithBody
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Framework.Block

/-! # The UMAAL diagonal square preserves the shared arithmetic contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem squareBodyReduceWith_ok (K : RowKernel) (s : State) {base : BitVec 32} {len o a : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (ho : Operand o) (ha : Operand a)
    (ptr : s.gpr .r0 = base) (po : s.gpr .r2 = BitVec.ofNat 32 o)
    (pa : s.gpr .r3 = BitVec.ofNat 32 a) (pb : s.gpr .r12 = BitVec.ofNat 32 a)
    (inverse : ((word s.mem (State.addr base) (arrAt (wOf s.mem (State.addr base)) 0)).toNat *
      (wordAt s.mem (State.addr base) Spec.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0)
    (operand : numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) a <
      numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) 0)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa (squareBodyReduceWith K.code) s fun t =>
      let w := wOf s.mem (State.addr base)
      let M := numAt s.mem (State.addr base) w 0
      numAt t.mem (State.addr base) w o < M ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % M =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w a % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let w := wOf s.mem (State.addr base)
  have hw : 2 ≤ w := layout.1
  have fits : arrAt w 8 ≤ 8 * len := layout.2.2.1
  have header := nativeHeader_of_layout s.mem base ws.nowrap (Nat.le_refl _) layout
  have bound : 128 ≤ 8 * len := by
    simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits
    omega
  rw [squareBodyReduceWith, WP.seq_iff]
  refine WP.mono (bases_ok s ws bound header ho.1 ha.1 ha.1 ptr po pa pb) ?_
  rintro u ⟨regs, mem, keep⟩
  have envU := sqEnv_of_layout s u ws layout ho ha header
    (native_inverse s.mem (State.addr base) (by omega) inverse) operand stackRead stackSep saved mem keep
  refine WP.mono (sqBodyReduceWith_ok K u envU regs.accPtr regs.count regs.aPtr regs.outPtr) ?_
  rintro t ⟨lt, value, outside, rest⟩
  rw [mem] at lt value outside
  refine ⟨?_, ?_, keeps_of_square ws.nowrap outside, frame_of_square ho.1 fits outside, keep.trans rest⟩
  · simpa only [numAt_native] using lt
  · rw [numAt_native, numAt_native, numAt_native, Nat.mul_comm _ (2 ^ (64 * w))]
    simpa only [radix32] using value

theorem squareBodyReduceWith_stack (K : RowKernel) :
    FrameStack.armStack (squareBodyReduceWith K.code) = 0 := by
  have hInit : FrameStack.armStack sqInit = 0 := rfl
  have hCross : FrameStack.armStack crossRows = 0 := rfl
  have hDouble : FrameStack.armStack sqDouble = 0 := rfl
  have hDiag : FrameStack.armStack sqDiagU = 0 := rfl
  have hAnchor : FrameStack.armStack sqAnchor = 0 := rfl
  have hFinish : FrameStack.armStack sqFinish = 0 := rfl
  simp [squareBodyReduceWith, sqBodyReduceWith, sqReduceWith, redRoundsWith, redRoundWith,
    FrameStack.armStack, K.stackZero, hInit, hCross, hDouble, hDiag, hAnchor, hFinish]


end VG.Proof.Bignum.Arm
