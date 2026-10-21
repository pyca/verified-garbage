module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowBit
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.NegPair
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Native subtraction and masking isolate the paired word's lowest set bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowBit
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowBit

theorem code_ok (s : State) :
    WP isa (.block code) s fun t =>
      t.gpr .edx ++ t.gpr .eax = (s.gpr .esi ++ s.gpr .ebx) &&& -(s.gpr .esi ++ s.gpr .ebx) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx] s t := by
  unfold code
  refine wp_movS rfl fun a A _ => wp_subS rfl fun b B cfB => wp_movS rfl fun c C cfC => ?_
  refine wp_sbbS rfl (cfC.trans cfB) fun d D _ => wp_and fun e E => wp_and fun t T => WP.block_nil ?_
  have low : t.gpr .eax = (0#32 - s.gpr .ebx) &&& s.gpr .ebx := by
    rw [T.other .eax (by decide), E.gpr, D.other .eax (by decide), C.other .eax (by decide),
      B.gpr, A.gpr, A.other .ebx (by decide), D.other .ebx (by decide), C.other .ebx (by decide),
      B.other .ebx (by decide), A.other .ebx (by decide)]
    rfl
  have high : t.gpr .edx = (0#32 - s.gpr .esi - (BitVec.ofBool (decide (0 < (s.gpr .ebx).toNat))).setWidth 32)
      &&& s.gpr .esi := by
    rw [T.gpr, E.other .edx (by decide), D.gpr, C.gpr, C.other .esi (by decide), B.other .esi (by decide),
      A.other .esi (by decide), A.gpr, A.other .ebx (by decide),
      E.other .esi (by decide), D.other .esi (by decide), C.other .esi (by decide), B.other .esi (by decide),
      A.other .esi (by decide)]
    rfl
  refine ⟨?_, ?_, (((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps).widen T.keeps⟩
  · rw [low, high, ← BitVec.and_append, neg_pair, BitVec.and_comm]
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.LowBit
