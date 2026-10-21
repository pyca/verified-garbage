module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Near
public import VerifiedGarbage.Proof.RsaKeyGen.X86.NearScalar
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The scalar separation comparison executes without branches -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Near
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Near

theorem finish_ok (s : State) (bound : (s.gpr .ecx).toNat < 16) :
    WP isa (.block finish) s fun t =>
      t.gpr .eax = bit (decide ((s.gpr .ecx).toNat + (decide ((s.gpr .ebx).toNat ≠ 0)).toNat ≤ 1) &&
        decide ((s.gpr .edx).toNat = 0)) ∧ t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t := by
  unfold finish
  refine wp_movS rfl fun a A _ => wp_subS rfl fun b B cfB => wp_sbbS rfl cfB fun c C _ => ?_
  have Kc : Keeps [.eax, .ebx] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have delta : c.gpr .eax = bit (decide ((s.gpr .ebx).toNat ≠ 0)) := by
    rw [C.gpr, B.other .eax (by decide), A.gpr, A.other .ebx (by decide)]
    exact nonzero_bit _
  refine wp_addS rfl fun d D _ => ?_
  have sum : (d.gpr .ecx).toNat = (s.gpr .ecx).toNat + (decide ((s.gpr .ebx).toNat ≠ 0)).toNat := by
    rw [D.gpr, delta, Kc.1 .ecx (by decide)]
    exact nibble_sum _ _ bound
  refine wp_movS rfl fun e E _ => wp_subS rfl fun f F cfF => wp_adcS rfl cfF fun h H _ => ?_
  have flag : h.gpr .eax = bit (decide ((s.gpr .ecx).toNat + (decide ((s.gpr .ebx).toNat ≠ 0)).toNat ≤ 1)) := by
    rw [H.gpr, F.other .eax (by decide), E.gpr]
    change 0#32 + 0#32 + _ = _
    rw [BitVec.zero_add, BitVec.zero_add, carry_bit, E.other .ecx (by decide), sum]
    congr 1
  have Kh : Keeps [.eax, .ebx, .ecx] s h :=
    ((((Kc.mono (by decide)).widen D.keeps).widen E.keeps).widen F.keeps).widen H.keeps
  refine wp_movS rfl fun i I _ => wp_subS rfl fun j J cfJ => wp_adcS rfl cfJ fun k K _ => ?_
  have high : k.gpr .ecx = bit (decide ((s.gpr .edx).toNat = 0)) := by
    rw [K.gpr, J.other .ecx (by decide), I.gpr]
    change 0#32 + 0#32 + _ = _
    rw [BitVec.zero_add, BitVec.zero_add, carry_bit, I.other .edx (by decide), Kh.1 .edx (by decide)]
    apply congrArg bit
    apply decide_eq_decide.mpr
    change (s.gpr .edx).toNat < 1 ↔ (s.gpr .edx).toNat = 0
    omega
  refine wp_and fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, (((Kh.mono (by decide)).widen I.keeps).widen J.keeps).widen K.keeps |>.widen T.keeps⟩
  · rw [T.gpr, high, K.other .eax (by decide), J.other .eax (by decide), I.other .eax (by decide), flag, bit_and]
  · rw [T.mem, K.mem, J.mem, I.mem, H.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.Near
