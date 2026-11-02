module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytes
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.HalveOctets
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.HalveResult
import VerifiedGarbage.Proof.Ffdh.Arm.Block
/-! Divide the shaped p into q in place without disturbing the RSA sieve table. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/HalveQ.lean`, which only this module imported.
section

/-! Complete candidate halving, including native argument loads and q's parity. -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (arrAt)

private theorem table_after_output {s t : State} {p : CandidateParams}
    (table : TableData p.base p.length s.mem) (changed : Frame [⟨State.addr p.out, p.length⟩] s.mem t.mem) :
    TableData p.base p.length t.mem := by
  intro i hi
  have fit : arrAt ((p.length + 7) / 8) 34 + 4096 ≤ 8 * p.capacity := p.table_fits
  have equal := changed.readW (a := off (State.addr p.base) (arrAt ((p.length + 7) / 8) 34 + 4 * i)) (w := 32)
    (r := ⟨State.addr p.base, 8 * p.capacity⟩)
    (Offset.contains_base _ (by omega) (by have := p.scratchFits; omega)) (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact p.outputScratch.symm) (by decide)
  exact (congrArg BitVec.toNat equal).trans (table i hi)

theorem candidateHalveValue_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ s fun t =>
      CandidateContext p consumed t ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length) = (p.candidate - 1) / 2 ∧
      t.z = decide (((p.candidate - 1) / 2) % 2 = 0) ∧
      Frame [⟨State.addr p.out, p.length⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let bs := Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length
  have size : bs.length = p.length := by simp [bs, Spec.Rsa.bytesAt]
  have saved : SavedFrame (readValues p.out bs.length) [4, 12] s := by rw [size]; exact h.read_context.frame
  have mask : MaskCtx s p.out bs.length := by rw [size]; exact h.mask
  have bytes : ∀ j < bs.length, s.mem (State.addr (p.out + BitVec.ofNat 32 j)) = bs[j]?.getD 0 := by
    intro j hj
    have bound : j < p.length := by rwa [size] at hj
    rw [VG.Arm.addr_add (by have fit : p.out.toNat + p.length ≤ 2 ^ 32 := p.outputFits; omega)]
    simp only [bs, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range bound, Option.map_some, Option.getD_some]
  refine WP.mono (halveQ_ok saved mask (by rw [size]; have := p.length_bounds; omega)
    (by rw [size]; exact p.outputFits) bytes) ?_
  rintro t ⟨_, value, zero, changed, rest⟩
  rw [size] at value changed
  have source : Spec.Rsa.os2ip bs = p.candidate := number
  have half : p.candidate / 2 = (p.candidate - 1) / 2 := by have := p.candidate_odd; omega
  rw [source, half] at value zero
  exact ⟨h.after_output changed rest, value, zero, changed,
    rest.mono (by simp [roundClobbers])⟩


theorem candidateHalve_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (table : TableData p.base p.length s.mem)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ s fun t =>
      CandidateContext p consumed t ∧ TableData p.base p.length t.mem ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length) = (p.candidate - 1) / 2 ∧
      t.z = decide (((p.candidate - 1) / 2) % 2 = 0) ∧
      Frame [⟨State.addr p.out, p.length⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (candidateHalveValue_ok h number) ?_
  rintro t ⟨context, value, zero, changed, rest⟩
  exact ⟨context, table_after_output table changed, value, zero, changed, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
