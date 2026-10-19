module

import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseBuffer
public import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseArgs
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.X86.PrivMasks
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Fault status, branchless release, and temporary erasure as one verified stage -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.X86.Wp VG.Impl.Rsa.X86.PrivChecked VG.Proof.Mont.X86 VG.Proof.Bignum.X86

structure ReleaseInput (dst tmp : BitVec 32) (k : Nat) (s : State) : Prop where
  positive : 0 < k
  countFit : k < 2 ^ 32
  outRead : InRegions (s.rd ++ s.wr) (incomingAddress s 0) 4
  countRead : InRegions (s.rd ++ s.wr) (incomingAddress s 3) 4
  output : s.mem.readW (incomingAddress s 0) 32 = dst
  count : s.mem.readW (incomingAddress s 3) 32 = BitVec.ofNat 32 k
  temp : s.gpr .esp + BitVec.ofNat 32 candidateOffset = tmp
  tempFit : tmp.toNat + k ≤ 2 ^ 32
  outputFit : dst.toNat + k ≤ 2 ^ 32
  tempWrite : InRegions s.wr (byteAddr tmp) k
  outputWrite : InRegions s.wr (byteAddr dst) k
  separate : Region.Disjoint ⟨byteAddr tmp, k⟩ ⟨byteAddr dst, k⟩

theorem ReleaseInput.of_mem {s t : State} {dst tmp : BitVec 32} {k : Nat} {rs : List Reg}
    (h : ReleaseInput dst tmp k s) (mem : t.mem = s.mem) (rest : Keeps rs s t) (sp : t.gpr .esp = s.gpr .esp) : ReleaseInput dst tmp k t :=
  ⟨h.positive, h.countFit,
    by simp only [incomingAddress, rest.2.1, rest.2.2, sp]; exact h.outRead,
    by simp only [incomingAddress, rest.2.1, rest.2.2, sp]; exact h.countRead,
    by simp only [incomingAddress, mem, sp]; exact h.output,
    by simp only [incomingAddress, mem, sp]; exact h.count,
    by rw [sp]; exact h.temp, h.tempFit, h.outputFit,
    by rw [rest.2.2]; exact h.tempWrite, by rw [rest.2.2]; exact h.outputWrite, h.separate⟩

theorem releaseTail_ok (s : State) {dst tmp : BitVec 32} {k : Nat} {accepted equal : Bool}
    (h : ReleaseInput dst tmp k s) (good : s.gpr .ebx = BitVec.ofNat 32 accepted.toNat)
    (eq : (s.gpr .ebp = 0) ↔ equal = true) :
    WP isa release s fun t =>
      t.gpr .eax = (if accepted then if equal then 1 else 2 else 0) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr dst) k =
        (if accepted && equal then Spec.Rsa.bytesAt s.mem (byteAddr tmp) k else List.replicate k 0) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr tmp) k = List.replicate k 0 ∧
      Frame [⟨byteAddr dst, k⟩, ⟨byteAddr tmp, k⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  rw [release, WP.seq_iff]
  refine WP.mono (masks_ok s accepted equal good eq) ?_
  rintro u ⟨mask, status, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (releaseArgs_ok u
    (by simp only [incomingAddress, restU.2.1, restU.2.2, restU.1 .esp (by decide)]; exact h.outRead)
    (by simp only [incomingAddress, restU.2.1, restU.2.2, restU.1 .esp (by decide)]; exact h.countRead)) ?_
  rintro v ⟨output, temp, count, memV, restV⟩
  have outV : v.gpr .edi = dst := by simp only [output, incomingAddress, memU, restU.1 .esp (by decide)]; exact h.output
  have tmpV : v.gpr .esi = tmp := by rw [temp, restU.1 .esp (by decide)]; exact h.temp
  have countV : v.gpr .ecx = BitVec.ofNat 32 k := by simp only [count, incomingAddress, memU, restU.1 .esp (by decide)]; exact h.count
  rw [WP.seq_iff]
  refine WP.mono (releaseBuffer_ok v h.positive h.countFit h.tempFit h.outputFit
    (by rw [restV.2.2, restU.2.2]; exact h.tempWrite)
    (by rw [restV.2.2, restU.2.2]; exact h.outputWrite) h.separate tmpV outV countV
    ((restV.1 .edx (by decide)).trans mask)) ?_
  rintro z ⟨bytes, cleared, frame, restZ⟩
  refine wp_mov fun t moved => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [moved.gpr, restZ.1 .ebx (by decide), restV.1 .ebx (by decide), status]
  · rw [moved.mem, bytes, memV, memU]
  · rw [moved.mem]; exact cleared
  · rw [moved.mem]
    rw [memV, memU] at frame
    exact frame
  · exact (restU.mono (by simp)).trans ((restV.mono (by simp)).trans
      ((restZ.mono (by simp)).trans (moved.keeps.mono (by decide))))
end VG.Proof.Rsa.X86.PrivChecked
