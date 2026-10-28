module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSizedTiming
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.TCB.X86.State

/-! # Public width comparisons retain the candidate's input relation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem ClearedPair.keepMem {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : ClearedPair E eBytes pBytes qBytes rBytes sBytes s t)
    (MU : u.mem = s.mem) (MZ : z.mem = t.mem) {regs : List Reg} (KU : Keeps regs s u) (KZ : Keeps regs t z)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) (SU : u.syms = s.syms) (SZ : z.syms = t.syms) :
    ClearedPair E eBytes pBytes qBytes rBytes sBytes u z := by
  refine ⟨⟨P.left.keepMem v MU KU base sp SU, P.right.keepMem v MZ KZ base sp SZ⟩, ?_, ?_⟩
  · rw [MU]; exact P.zerosLeft
  · rw [MZ]; exact P.zerosRight

theorem ClearedPair.keepFlags {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : ClearedPair E eBytes pBytes qBytes rBytes sBytes s t) (U : Fupd s u) (Z : Fupd t z) :
    ClearedPair E eBytes pBytes qBytes rBytes sBytes u z :=
  P.keepMem v U.mem Z.mem (U.keeps []) (Z.keeps []) (by decide) (by decide) U.syms Z.syms

end VG.Proof.RsaKeyGen.X86.Candidate
