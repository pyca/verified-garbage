module
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Rsa.Arm.PrivChecked
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseBuffer
import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseArgs
import VerifiedGarbage.Proof.Rsa.Arm.PrivMask
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Fault status, branchless release, and temporary erasure as one verified stage -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

structure ReleaseInput (dst tmp : BitVec 32) (k : Nat) (s : State) : Prop where
  positive : 0 < k
  countFit : k < 2 ^ 32
  stackFit : s.sp.toNat + 76 ≤ 2 ^ 32
  outRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) oOut) 4
  countRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) oK) 4
  output : s.mem.readW (off (State.addr s.sp) oOut) 32 = dst
  count : s.mem.readW (off (State.addr s.sp) oK) 32 = BitVec.ofNat 32 k
  temp : s.sp + BitVec.ofNat 32 oM = tmp
  tempFit : tmp.toNat + k ≤ 2 ^ 32
  outputFit : dst.toNat + k ≤ 2 ^ 32
  tempWrite : InRegions s.wr (State.addr tmp) k
  outputWrite : InRegions s.wr (State.addr dst) k
  separate : Region.Disjoint ⟨State.addr tmp, k⟩ ⟨State.addr dst, k⟩

theorem ReleaseInput.of_mem {s t : State} {dst tmp : BitVec 32} {k : Nat} {rs : List Reg}
    (h : ReleaseInput dst tmp k s) (mem : t.mem = s.mem) (rest : Rest rs s t) : ReleaseInput dst tmp k t :=
  ⟨h.positive, h.countFit, by rw [rest.sp]; exact h.stackFit,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.outRead,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.countRead,
    by rw [mem, rest.sp]; exact h.output, by rw [mem, rest.sp]; exact h.count,
    by rw [rest.sp]; exact h.temp, h.tempFit, h.outputFit,
    by rw [rest.wr]; exact h.tempWrite, by rw [rest.wr]; exact h.outputWrite, h.separate⟩

theorem releaseTail_ok (s : State) {dst tmp : BitVec 32} {k : Nat} {accepted equal : Bool}
    (h : ReleaseInput dst tmp k s) (good : s.gpr .r4 = BitVec.ofNat 32 accepted.toNat)
    (eq : (s.gpr .r2 = 0) ↔ equal = true) :
    WP isa releaseTail s fun t =>
      t.gpr .r0 = (if accepted then if equal then 1 else 2 else 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if accepted && equal then Spec.Rsa.bytesAt s.mem (State.addr tmp) k else List.replicate k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr tmp) k = List.replicate k 0 ∧
      Frame [⟨State.addr dst, k⟩, ⟨State.addr tmp, k⟩] s.mem t.mem ∧
      Rest [.r0, .r1, .r2, .r3, .r4, .r12, .lr] s t := by
  rw [releaseTail, WP.seq_iff]
  refine WP.mono (maskCore_ok s good eq) ?_
  rintro u ⟨mask, status, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (releaseArgs_ok u (by rw [restU.sp]; exact h.stackFit)
    (by rw [restU.rd, restU.wr, restU.sp]; exact h.outRead)
    (by rw [restU.rd, restU.wr, restU.sp]; exact h.countRead)) ?_
  rintro v ⟨output, temp, count, zero, memV, restV⟩
  have outV : v.gpr .r0 = dst := by rw [output, memU, restU.sp]; exact h.output
  have tmpV : v.gpr .r1 = tmp := by rw [temp, restU.sp]; exact h.temp
  have countV : v.gpr .lr = BitVec.ofNat 32 k := by rw [count, memU, restU.sp]; exact h.count
  rw [WP.seq_iff]
  refine WP.mono (releaseBuffer_ok v h.positive h.countFit h.tempFit h.outputFit
    (by rw [restV.wr, restU.wr]; exact h.tempWrite)
    (by rw [restV.wr, restU.wr]; exact h.outputWrite) h.separate tmpV outV countV
    ((restV.gpr .r2 (by simp)).trans mask) zero) ?_
  rintro z ⟨bytes, cleared, frame, restZ⟩
  refine wp_mov (op2_reg _ _) fun t moved => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [moved.gpr, restZ.gpr .r4 (by simp), restV.gpr .r4 (by simp), status]
  · rw [moved.mem, bytes, memV, memU]
  · rw [moved.mem]; exact cleared
  · rw [moved.mem]
    rw [memV, memU] at frame
    exact frame
  · exact (restU.mono (by simp)).trans ((restV.mono (by simp)).trans
      ((restZ.mono (by simp)).trans (moved.rest (by simp))))
end VG.Proof.Rsa.Arm
