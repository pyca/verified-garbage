module

public import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseArgs
public import VerifiedGarbage.Proof.Rsa.SuccessBits32

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
