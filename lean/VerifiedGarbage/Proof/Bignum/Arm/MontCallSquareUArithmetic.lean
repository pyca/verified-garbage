module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallSquareU
public import VerifiedGarbage.Impl.Bignum.Arm.MontCallWith
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallArithmetic

import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithLaw
import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.SquareState
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Impl.Bignum.Arm.SquareUmaal
import VerifiedGarbage.Proof.Bignum.Arm.SquareUmaalDiag
import VerifiedGarbage.Proof.Bignum.Arm.SquareBody
import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
/-! Public operand equality selects one verified UMAAL diagonal square. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/SquareUmaalBody.lean`, which only this module imported.
section

/-! The specialized UMAAL diagonal preserves the shared square invariant. -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem sqBodyU_ok (s : State) (h : SqEnv s.mem base size out a mod M n inv s)
    (p6 : s.gpr .r6 = base + BitVec.ofNat 32 M) (p7 : s.gpr .r7 = BitVec.ofNat 32 n)
    (p8 : s.gpr .r8 = base + BitVec.ofNat 32 a) (p10 : s.gpr .r10 = base + BitVec.ofNat 32 out) :
    WP isa sqBodyU s fun t =>
      val32 t.mem (State.addr base) out n < val32 s.mem (State.addr base) mod n ∧
      2 ^ (32 * n) * val32 t.mem (State.addr base) out n % val32 s.mem (State.addr base) mod n =
        val32 s.mem (State.addr base) a n * val32 s.mem (State.addr base) a n %
          val32 s.mem (State.addr base) mod n ∧
      Outs (State.addr base) [(M, 4 * (2 * n + 8)), (out, 4 * n)] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [sqBodyU, WP.seq_iff]
  refine WP.mono (sqInit_ok s h p6 p7 p8 p10) ?_
  rintro s1 ⟨h1, r1⟩
  rw [WP.seq_iff]
  refine WP.mono (crossRows_ok s1 h1) ?_
  rintro s2 ⟨h2, r2⟩
  rw [WP.seq_iff]
  refine WP.mono (sqDouble_ok s2 h2) ?_
  rintro s3 ⟨h3, r3⟩
  rw [WP.seq_iff]
  refine WP.mono (sqDiagPhaseU_ok s3 h3) ?_
  rintro s4 ⟨h4, r4⟩
  rw [WP.seq_iff]
  refine WP.mono (sqReduce_ok s4 h4) ?_
  rintro s5 ⟨h5, r5⟩
  refine WP.mono (sqFinish_ok s5 h5) ?_
  rintro t ⟨lt, value, outs, r6⟩
  refine ⟨lt, value, ?_, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))⟩
  exact (h5.env.frame.mono (by simp)).trans outs

end

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/SquareUmaalOp.lean`, which only this module imported.
section

/-! # The UMAAL diagonal square preserves the shared arithmetic contract -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem squareBodyU_ok (s : State) {base : BitVec 32} {len o a : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (ho : Operand o) (ha : Operand a)
    (ptr : s.gpr .r0 = base) (po : s.gpr .r2 = BitVec.ofNat 32 o)
    (pa : s.gpr .r3 = BitVec.ofNat 32 a) (pb : s.gpr .r12 = BitVec.ofNat 32 a)
    (inverse : ((word s.mem (State.addr base) (arrAt (wOf s.mem (State.addr base)) 0)).toNat *
      (wordAt s.mem (State.addr base) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0)
    (operand : numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) a <
      numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) 0)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa squareBodyU s fun t =>
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
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega
  rw [squareBodyU, WP.seq_iff]
  refine WP.mono (bases_ok s ws bound header ho.1 ha.1 ha.1 ptr po pa pb) ?_
  rintro u ⟨regs, mem, keep⟩
  have envU := sqEnv_of_layout s u ws layout ho ha header
    (native_inverse s.mem (State.addr base) (by omega) inverse) operand stackRead stackSep saved mem keep
  refine WP.mono (sqBodyU_ok u envU regs.accPtr regs.count regs.aPtr regs.outPtr) ?_
  rintro t ⟨lt, value, outside, rest⟩
  rw [mem] at lt value outside
  refine ⟨?_, ?_, keeps_of_square ws.nowrap outside, frame_of_square ho.1 fits outside, keep.trans rest⟩
  · simpa only [numAt_native] using lt
  · rw [numAt_native, numAt_native, numAt_native, Nat.mul_comm _ (2 ^ (64 * w))]
    simpa only [radix32] using value

theorem squareBodyU_stack : FrameStack.armStack squareBodyU = 0 := by rfl

end VG.Proof.Bignum.Arm
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest wp_cmp op2_reg)

theorem montCallSquareUArithmetic_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : CallBodyReady base len w o a b s)
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    WP isa MontCallSquareU.arithmetic s fun t =>
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [MontCallSquareU.arithmetic, MontCallWith.dispatch, WP.seq_iff]
  refine wp_cmp (op2_reg s .r12) fun u flags eq => WP.block_nil ?_
  have mem := flags.mem
  have rest := flags.rest []
  have ready := h.of_mem mem rest
  refine WP.ite u.z rfl ?_ ?_
  · intro same
    have indices : a = b := by
      have eq' : BitVec.ofNat 32 a = BitVec.ofNat 32 b := by
        rw [← h.input.aIndex, ← h.input.bIndex]
        have hz : s.gpr .r3 - s.gpr .r12 = 0 := by
          simpa only [eq, beq_iff_eq] using same
        calc
          s.gpr .r3 = (s.gpr .r3 - s.gpr .r12) + s.gpr .r12 := (BitVec.sub_add_cancel _ _).symm
          _ = s.gpr .r12 := by rw [hz]; exact BitVec.zero_add _
      have aw : a < 2 ^ 32 := by have := ha.1; omega
      have bw : b < 2 ^ 32 := by have := hb.1; omega
      have natEq := congrArg BitVec.toNat eq'
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt aw, Nat.mod_eq_of_lt bw] using natEq
    subst b
    have body := squareBodyU_ok u ready.input.workspace ready.input.layout ho ha ready.input.ptr
      ready.input.outIndex ready.input.aIndex ready.input.bIndex
      (by rw [ready.input.width]; exact ready.input.inverse)
      (by rw [ready.input.width]; exact ready.input.operand)
      ready.stackRead ready.stackSep ready.saved
    simp only [ready.input.width] at body
    refine WP.mono body ?_
    rintro t ⟨lt, value, keeps, frame, rt⟩
    rw [mem] at lt value keeps frame
    exact ⟨lt, value, keeps, frame, (rest.mono (by decide)).trans rt⟩
  · intro _
    have body := montFnBody_ok u ready.input.workspace ready.input.layout ho ha hb ready.input.ptr
      ready.input.outIndex ready.input.aIndex ready.input.bIndex
      (by rw [ready.input.width]; exact ready.input.inverse)
      (by rw [ready.input.width]; exact ready.input.operand)
    simp only [ready.input.width] at body
    refine WP.mono body ?_
    rintro t ⟨lt, value, keeps, frame, rt⟩
    rw [mem] at lt value keeps frame
    exact ⟨lt, value, keeps, frame, (rest.mono (by decide)).trans rt⟩

end VG.Proof.Bignum.Arm
