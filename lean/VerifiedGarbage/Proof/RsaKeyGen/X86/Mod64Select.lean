module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # One mask selects both native words of the reduced remainder -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem select_ok (s : State) (choose : Bool)
    (mask : s.gpr .ebp = if choose then BitVec.allOnes 32 else 0) :
    WP isa (.block select) s fun t =>
      t.gpr .ecx = (if choose then s.gpr .eax else s.gpr .ecx) ∧
      t.gpr .ebx = (if choose then s.gpr .edx else s.gpr .ebx) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx] s t := by
  unfold select
  refine wp_xor fun a A => wp_and fun b B => wp_xor fun c C =>
    wp_xor fun d D => wp_and fun e E => wp_xor fun t T => WP.block_nil ?_
  have Kc : Keeps [.eax, .ecx] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  refine ⟨?_, ?_, ?_, (((Kc.mono (by decide)).widen D.keeps).widen E.keeps).widen T.keeps⟩
  · rw [T.other .ecx (by decide), E.other .ecx (by decide), D.other .ecx (by decide), C.gpr,
      B.other .ecx (by decide), A.other .ecx (by decide), B.gpr, A.gpr,
      A.other .ebp (by decide), mask, select_val]
  · rw [T.gpr, E.other .ebx (by decide), D.other .ebx (by decide), Kc.1 .ebx (by decide),
      E.gpr, D.gpr, Kc.1 .edx (by decide), Kc.1 .ebx (by decide),
      D.other .ebp (by decide), Kc.1 .ebp (by decide), mask, select_val]
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.Mod64
