module
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Sign
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Weierstrass

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseArgs
import VerifiedGarbage.Proof.Rsa.X86.PrivRestore

/-! # Restoring the three registers above the final pop -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.X86.Wp VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Mont.X86

theorem restore_ok (s : State)
    (read4 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (read8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    (read0 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 0) 4) :
    WP isa (.block restore) s fun t =>
      t.gpr .edi = s.mem.readW (addr (s.gpr .esp) 0) 32 ∧
      t.gpr .ebp = s.mem.readW (addr (s.gpr .esp) 8) 32 ∧
      t.gpr .esi = s.mem.readW (addr (s.gpr .esp) 4) 32 ∧
      t.mem = s.mem ∧ Keeps [.edi, .ebp, .esi] s t := by
  unfold restore stackAt
  refine wp_ldm rfl read0 fun a A => ?_
  refine wp_ldm (B := s.gpr .esp) (A.other .esp (by decide))
    (by rw [A.rd, A.wr]; exact read8) fun b B => ?_
  refine wp_ldm (B := s.gpr .esp)
    (by rw [B.other .esp (by decide), A.other .esp (by decide)])
    (by rw [B.rd, B.wr, A.rd, A.wr]; exact read4) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, T.mem.trans (B.mem.trans A.mem), ?_⟩
  · rw [T.other .edi (by decide), B.other .edi (by decide), A.gpr]
  · rw [T.other .ebp (by decide), B.gpr, A.mem]
  · rw [T.gpr, B.mem, A.mem]
  · exact (A.keeps.mono (by decide)).trans
      ((B.keeps.mono (by decide)).trans (T.keeps.mono (by decide)))
end VG.Proof.RsaPkcs1Sig.X86.Sgn
