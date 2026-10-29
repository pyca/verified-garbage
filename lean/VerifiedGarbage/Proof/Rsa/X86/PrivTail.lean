module

public import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTail
public import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseArgs
public import VerifiedGarbage.Proof.Rsa.SuccessBits32

import VerifiedGarbage.Proof.Rsa.X86.PrivCompareBuffer
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # Compare the public re-exponentiation before releasing any private bytes -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/PrivCompareArgs.lean`, which only this module imported.
section

/-! # Accumulating call status and preparing the full public-result comparison -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.X86.Wp VG.Impl.Rsa.X86.PrivChecked VG.Proof.Mont.X86

structure CompareArgsInput (s : State) : Prop where
  crtRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) crtStatusOffset) 4
  preRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) precomputeStatusOffset) 4
  outRead : InRegions (s.rd ++ s.wr) (incomingAddress s 0) 4
  inputRead : InRegions (s.rd ++ s.wr) (incomingAddress s 6) 4
  countRead : InRegions (s.rd ++ s.wr) (incomingAddress s 3) 4

theorem compareArgs_ok (s : State) (h : CompareArgsInput s) :
    WP isa (.block compareArgs) s fun t =>
      t.gpr .esi = s.mem.readW (incomingAddress s 0) 32 ∧
      t.gpr .edi = s.mem.readW (incomingAddress s 6) 32 ∧
      t.gpr .ecx = s.mem.readW (incomingAddress s 3) 32 ∧ t.gpr .ebp = 0 ∧
      t.gpr .ebx = successBits (s.gpr .eax)
        (s.mem.readW (addr (s.gpr .esp) crtStatusOffset) 32)
        (s.mem.readW (addr (s.gpr .esp) precomputeStatusOffset) 32) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .esi, .edi, .ecx, .ebp] s t := by
  unfold compareArgs incoming stackAt
  refine wp_logicS (.inl rfl) (readSrc_mem rfl h.crtRead) fun a A => ?_
  refine wp_logicS (.inl rfl) (readSrc_mem (A.other .esp (by decide))
    (by rw [A.rd, A.wr]; exact h.preRead)) fun b B => ?_
  refine wp_logicS (.inl rfl) rfl fun c C => ?_
  refine wp_movS rfl fun d D _ => ?_
  have K : Keeps [.eax, .ebx] s d :=
    (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans
      ((C.keeps.mono (by decide)).trans (D.keeps.mono (by decide))))
  have M : d.mem = s.mem := D.mem.trans (C.mem.trans (B.mem.trans A.mem))
  have status : d.gpr .ebx = successBits (s.gpr .eax)
      (s.mem.readW (addr (s.gpr .esp) crtStatusOffset) 32)
      (s.mem.readW (addr (s.gpr .esp) precomputeStatusOffset) 32) := by
    rw [D.gpr, C.gpr, B.gpr, A.gpr, A.mem]
    simp only [ite_true, successBits]
    rw [BitVec.and_comm (s.gpr .eax)]
  refine wp_ldm (K.1 .esp (by decide)) (by rw [K.2.1, K.2.2]; exact h.outRead) fun e E => ?_
  refine wp_ldm (B := s.gpr .esp)
    (by rw [E.other .esp (by decide), K.1 .esp (by decide)])
    (by rw [E.rd, E.wr, K.2.1, K.2.2]; exact h.inputRead) fun f F => ?_
  refine wp_ldm (B := s.gpr .esp)
    (by rw [F.other .esp (by decide), E.other .esp (by decide), K.1 .esp (by decide)])
    (by rw [F.rd, F.wr, E.rd, E.wr, K.2.1, K.2.2]; exact h.countRead) fun g G => ?_
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, T.gpr, ?_, T.mem.trans (G.mem.trans (F.mem.trans (E.mem.trans M))), ?_⟩
  · rw [T.other .esi (by decide), G.other .esi (by decide), F.other .esi (by decide), E.gpr, M]; rfl
  · rw [T.other .edi (by decide), G.other .edi (by decide), F.gpr, E.mem, M]; rfl
  · rw [T.other .ecx (by decide), G.gpr, F.mem, E.mem, M]; rfl
  · rw [T.other .ebx (by decide), G.other .ebx (by decide), F.other .ebx (by decide), E.other .ebx (by decide), status]
  · exact (K.mono (by decide)).trans ((E.keeps.mono (by decide)).trans
      ((F.keeps.mono (by decide)).trans ((G.keeps.mono (by decide)).trans (T.keeps.mono (by decide)))))

end VG.Proof.Rsa.X86.PrivChecked
end

end

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
