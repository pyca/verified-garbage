module

public import VerifiedGarbage.Proof.Rsa.X86.PrivCompareArgs
public import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTail
public import VerifiedGarbage.Proof.Rsa.X86.PrivCompareBuffer

/-! # Compare the public re-exponentiation before releasing any private bytes -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

structure TailInput (dst tmp xp : BitVec 32) (k : Nat) (s : State) : Prop where
  release : ReleaseInput dst tmp k s
  args : CompareArgsInput s
  input : s.mem.readW (incomingAddress s 6) 32 = xp
  inputFit : xp.toNat + k ≤ 2 ^ 32
  inputRead : InRegions (s.rd ++ s.wr) (byteAddr xp) k

theorem TailInput.of_mem {s t : State} {dst tmp xp : BitVec 32} {k : Nat} {rs : List Reg}
    (h : TailInput dst tmp xp k s) (mem : t.mem = s.mem) (rest : Keeps rs s t)
    (sp : t.gpr .esp = s.gpr .esp) : TailInput dst tmp xp k t := by
  refine ⟨h.release.of_mem mem rest sp, ?_, ?_, h.inputFit, ?_⟩
  · rcases h.args with ⟨A, B, C, D, E⟩
    exact ⟨by rw [rest.2.1, rest.2.2, sp]; exact A,
      by rw [rest.2.1, rest.2.2, sp]; exact B,
      by simp only [incomingAddress, rest.2.1, rest.2.2, sp]; exact C,
      by simp only [incomingAddress, rest.2.1, rest.2.2, sp]; exact D,
      by simp only [incomingAddress, rest.2.1, rest.2.2, sp]; exact E⟩
  · simp only [incomingAddress, mem, sp]; exact h.input
  · rw [rest.2.1, rest.2.2]; exact h.inputRead

def tailAccepted (s : State) : Bool := decide (successBits (s.gpr .eax)
  (s.mem.readW (addr (s.gpr .esp) crtStatusOffset) 32) (s.mem.readW (addr (s.gpr .esp) precomputeStatusOffset) 32) = 1)
def tailEqual (s : State) (dst xp : BitVec 32) (k : Nat) : Bool :=
  decide (Spec.Rsa.bytesAt s.mem (byteAddr dst) k = Spec.Rsa.bytesAt s.mem (byteAddr xp) k)

theorem tail_ok (s : State) {dst tmp xp : BitVec 32} {k : Nat} (h : TailInput dst tmp xp k s) :
    WP isa tail s fun t =>
      t.gpr .eax = (if tailAccepted s then if tailEqual s dst xp k then 1 else 2 else 0) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr dst) k =
        (if tailAccepted s && tailEqual s dst xp k then Spec.Rsa.bytesAt s.mem (byteAddr tmp) k else List.replicate k 0) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr tmp) k = List.replicate k 0 ∧
      Frame [⟨byteAddr dst, k⟩, ⟨byteAddr tmp, k⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  rw [tail, WP.seq_iff]
  refine WP.mono (compareArgs_ok s h.args) ?_
  rintro u ⟨output, input, count, zero, good, memU, restU⟩
  have outRead : InRegions (s.rd ++ s.wr) (byteAddr dst) k := by
    obtain ⟨r, hr, hc⟩ := h.release.outputWrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [WP.seq_iff]
  refine WP.mono (compareBuffer_ok u h.release.positive h.release.countFit h.release.outputFit h.inputFit
    (by rw [restU.2.1, restU.2.2]; exact outRead) (by rw [restU.2.1, restU.2.2]; exact h.inputRead)
    (output.trans h.release.output) (input.trans h.input) (count.trans h.release.count) zero) ?_
  rintro v ⟨equal, memV, restV⟩
  have goodV : v.gpr .ebx = BitVec.ofNat 32 (tailAccepted s).toNat := by
    rw [restV.1 .ebx (by decide), good]
    unfold tailAccepted
    rcases successBits_cases (s.gpr .eax) (s.mem.readW (addr (s.gpr .esp) crtStatusOffset) 32)
      (s.mem.readW (addr (s.gpr .esp) precomputeStatusOffset) 32) with hz | ho
    · rw [hz]; rfl
    · rw [ho]; rfl
  have eqV : (v.gpr .ebp = 0) ↔ tailEqual s dst xp k = true := by
    rw [equal, memU]
    simp only [tailEqual, decide_eq_true_eq]
  have inputV := (h.release.of_mem memU restU (restU.1 .esp (by decide))).of_mem memV restV (restV.1 .esp (by decide))
  refine WP.mono (releaseTail_ok v inputV goodV eqV) ?_
  rintro t ⟨status, bytes, cleared, frame, rest⟩
  rw [memV, memU] at bytes frame
  exact ⟨status, bytes, cleared, frame,
    (restU.mono (by simp)).trans ((restV.mono (by simp)).trans rest)⟩
end VG.Proof.Rsa.X86.PrivChecked
