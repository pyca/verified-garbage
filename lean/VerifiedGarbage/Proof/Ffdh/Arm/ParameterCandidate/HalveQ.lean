module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBytes
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.HalveOctets
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.HalveResult
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete candidate halving, including native argument loads and q's parity. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.ParameterCandidate (halfOctets)

private theorem halveHead_ok {s : State} {dst : BitVec 32} {n : Nat}
    (frame : SavedFrame (readValues dst n) [4, 12] s) :
    WP isa (.block [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)]) s fun t =>
      (t.gpr .r0 = dst ∧ t.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .r2 = 0 ∧ t.mem = s.mem) ∧
        Rest [.r0, .r2, .lr] s t := by
  have out : s.mem.readW (State.addr (s.sp + 4#32)) 32 = dst := frame.saved 4 (by simp)
  have width : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 n := frame.saved 12 (by simp)
  refine withRest_all [.r0, .r2, .lr] ?_ (by rfl) (by rfl)
  ffrun [BitVec.add_zero, frame.read (d := 4) (by decide), frame.read (d := 12) (by decide), out, width]

private theorem andOne (x : BitVec 32) : x &&& 1 = BitVec.ofNat 32 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x.toNat % 2 < 2 ^ 32)]
  change x.toNat &&& (2 ^ 1 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem halveTail_ok (s : State) :
    WP isa (.block [.dp .and .r1 .r1 (.imm 1), .cmp .r1 (.imm 0)]) s fun t =>
      (t.z = decide ((s.gpr .r1).toNat % 2 = 0) ∧ t.mem = s.mem) ∧ Rest [.r1] s t := by
  have zero : ((s.gpr .r1 &&& 1) - (0 : BitVec 32) == (0 : BitVec 32)) =
      decide ((s.gpr .r1).toNat % 2 = 0) := by
    change ((s.gpr .r1 &&& 1) - 0#32 == 0#32) = _
    rw [BitVec.sub_zero, andOne]
    exact ofNat_beq_zero (by omega)
  refine withRest_all [.r1] ?_ (by rfl) (by rfl)
  ffrun [zero]

theorem halveQ_ok {s : State} {dst : BitVec 32} {bs : List Byte}
    (frame : SavedFrame (readValues dst bs.length) [4, 12] s)
    (ctx : MaskCtx s dst bs.length) (positive : 0 < bs.length)
    (fits : dst.toNat + bs.length ≤ 2 ^ 32)
    (bytes : ∀ j < bs.length, s.mem (State.addr (dst + BitVec.ofNat 32 j)) = bs[j]?.getD 0) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) bs.length = halfOctets 0 bs ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr dst) bs.length) = Spec.Rsa.os2ip bs / 2 ∧
      t.z = decide ((Spec.Rsa.os2ip bs / 2) % 2 = 0) ∧
      Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (halveHead_ok frame) ?_)
  rintro u ⟨⟨ptr, count, carry, memory⟩, rest⟩
  have ctxU : MaskCtx u dst bs.length := ⟨ctx.countFits,
    by intro i hi; rw [rest.rd, rest.wr]; exact ctx.readable i hi,
    by intro i hi; rw [rest.wr]; exact ctx.writable i hi, ctx.distinct⟩
  refine WP.seq (WP.mono (halveLoop_ok u ctxU positive
    (by intro j hj; rw [memory]; exact bytes j hj) ptr count carry) ?_)
  intro v inv
  refine WP.seq (WP.mono (halveTail_ok v) ?_)
  rintro t ⟨⟨flagT, memoryT⟩, restT⟩
  have changed := inv.frame fits
  rw [memory] at changed
  refine WP.block_nil ⟨?_, ?_, ?_, ?_,
    ((rest.mono (by simp)).trans inv.rest).trans (restT.mono (by simp))⟩
  · rw [memoryT]
    exact inv.encoding fits
  · rw [memoryT]
    exact inv.value fits
  · rw [flagT, inv.parity positive fits]
  · rwa [memoryT]

end VG.Proof.Ffdh.Arm.ParameterCandidate
