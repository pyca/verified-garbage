module

public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Stack-relative pointers and count for releasing the checked candidate -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.X86.Wp VG.Impl.Rsa.X86.PrivChecked VG.Proof.Mont.X86

def incomingAddress (s : State) (i : Nat) : Addr :=
  addr (s.gpr .esp) (frameBytes + 20 + 4 * i)

theorem releaseArgs_ok (s : State)
    (outRead : InRegions (s.rd ++ s.wr) (incomingAddress s 0) 4)
    (countRead : InRegions (s.rd ++ s.wr) (incomingAddress s 3) 4) :
    WP isa (.block releaseArgs) s fun t =>
      t.gpr .edi = s.mem.readW (incomingAddress s 0) 32 ∧
      t.gpr .esi = s.gpr .esp + BitVec.ofNat 32 candidateOffset ∧
      t.gpr .ecx = s.mem.readW (incomingAddress s 3) 32 ∧
      t.mem = s.mem ∧ Keeps [.edi, .esi, .ecx] s t := by
  unfold releaseArgs incoming stackAt
  refine wp_ldm rfl outRead fun a A => ?_
  refine wp_movS rfl fun b B _ => ?_
  refine wp_addS rfl fun c C _ => ?_
  refine wp_ldm (B := s.gpr .esp)
    (by rw [C.other .esp (by decide), B.other .esp (by decide), A.other .esp (by decide)])
    (by rw [C.rd, C.wr, B.rd, B.wr, A.rd, A.wr]; exact countRead) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, T.mem.trans (C.mem.trans (B.mem.trans A.mem)), ?_⟩
  · rw [T.other .edi (by decide), C.other .edi (by decide), B.other .edi (by decide), A.gpr]; rfl
  · rw [T.other .esi (by decide), C.gpr, B.gpr, A.other .esp (by decide)]
  · rw [T.gpr, C.mem, B.mem, A.mem]; rfl
  · exact (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans
      ((C.keeps.mono (by decide)).trans (T.keeps.mono (by decide))))

end VG.Proof.Rsa.X86.PrivChecked
