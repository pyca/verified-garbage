module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialStep

/-! # Trial-reduction pointer control is independent of candidate arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Trial

theorem wordStep_control (s : State) (endOffset : Nat) (endPtr : BitVec 32)
    (candidateRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) 0) 4)
    (endRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) endOffset) 4)
    (endValue : s.mem.readW (addr (s.gpr .esp) endOffset) 32 = endPtr) :
    WP isa (.block (wordStep endOffset)) s fun t => t.mem = s.mem ∧
      Keeps [.eax, .edx, .ecx, .ebp, .edi] s t ∧ t.gpr .edi = s.gpr .edi + 4 ∧
      t.zf = some (s.gpr .edi + 4 - endPtr == 0) := by
  unfold wordStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_movS (readSrc_mem rfl candidateRead) fun a A _ => WP.block_nil ?_
  refine WP.mono (redc32_code a) fun b ⟨M, K, _⟩ => ?_
  have Kb : Keeps [.eax, .edx, .ecx, .ebp] s b := (A.keeps.mono (by decide)).trans K
  have Mb : b.mem = s.mem := M.trans A.mem
  refine wp_addS rfl fun c C _ => ?_
  have Kc : Keeps [.eax, .edx, .ecx, .ebp, .edi] s c := (Kb.mono (by decide)).trans (C.keeps.mono (by decide))
  have Mc : c.mem = s.mem := C.mem.trans Mb
  have read : readSrc c (.mem ⟨.esp, endOffset⟩) = some endPtr := by
    have ptr := Kc.1 .esp (by decide)
    have readable : InRegions (c.rd ++ c.wr) (addr (c.gpr .esp) endOffset) 4 := by
      rw [Kc.2.1, Kc.2.2, ptr]
      exact endRead
    have raw := readSrc_mem rfl readable
    rw [Mc, ptr, endValue] at raw
    exact raw
  refine wp_cmpS read fun t T Z => WP.block_nil ?_
  have Kt : Keeps [.eax, .edx, .ecx, .ebp, .edi] s t := Kc.trans (T.keeps _)
  have ptr : c.gpr .edi = s.gpr .edi + 4 := by rw [C.gpr, Kb.1 .edi (by decide)]
  refine ⟨T.mem.trans Mc, Kt, (congrFun T.gpr .edi).trans ptr, ?_⟩
  rw [ptr] at Z
  exact Z

end VG.Proof.RsaKeyGen.X86.Trial
