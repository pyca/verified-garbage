module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SampleWitness
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleLayout
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleLoad
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory

/-! # Load and classify the draw without changing its source buffer -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Proof.Ecdsa.X86

theorem sampleHead_ok {s : State} {base : Addr} {size n m len : Nat}
    (C : Context n m base size s) (width : n ≤ 48) (room : primeIsUniform + 4 ≤ size)
    (one : wordsVal s.mem base (slot n 3) n = 1) (ndef : n = (len + 7) / 8)
    (h4 : 4 ≤ len) (hw4 : len % 4 = 0) (fit : (s.gpr .esi).toNat + len ≤ 2 ^ 32)
    (read4 : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) (off ((s.gpr .esi).setWidth 64) d) 4)
    (apart : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, len⟩ ⟨base, size⟩) :
    WP isa (sampleHead len) s fun t =>
      let x := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) len)
      Context n m base size t ∧ wordsVal t.mem base (slot n 5) n = x ∧
      t.mem.readW (off base primeIsUniform) 32 = mask32 (2 ≤ x ∧ x < m - 1) ∧
      t.zf = some (decide (¬ (2 ≤ x ∧ x < m - 1))) ∧
      Spec.Rsa.bytesAt t.mem ((s.gpr .esi).setWidth 64) len = Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) len ∧
      Frame ((sampleArithmeticWrites n).map fun r => ⟨off base r.1, r.2⟩) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold sampleHead
  dsimp only
  rw [← ndef]
  refine WP.seq (WP.mono (sampleLoad_ok C h4 (by omega) hw4 fit read4 apart) fun a ⟨Ca, value, Oa, Ka⟩ => ?_)
  have onea : wordsVal a.mem base (slot n 3) n = 1 := by
    rw [Oa.wordsVal (by simp only [slot, stride]; omega) (by have := C.scr.nowrap; have := C.size_le; simp only [contextBytes, slot, stride] at *; omega), one]
  refine WP.mono (sampleTest_ok Ca width room onea) fun t ⟨Ct, flag, zf, vt, Ot, Kt⟩ => ?_
  rw [value] at flag zf
  have O : Outs base (sampleArithmeticWrites n) s.mem t.mem :=
    (Outs.of_outside Oa (by simp [sampleArithmeticWrites])).trans
      (Ot.mono (by intro r hr; exact List.mem_cons_of_mem _ hr))
  have F := sampleOuts_frame O (fun r hr => by have := sampleArithmetic_bound width room r hr; have := C.scr.nowrap; omega)
  refine ⟨Ct, vt.trans value, flag, zf, ?_, F, (Ka.mono (by decide)).trans Kt⟩
  apply drawFrame_bytes F ?_ (by omega)
  intro r hr
  obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hr
  exact apart.sub_right (Offset.sub_base _ (sampleArithmetic_bound width room item hi))
end VG.Proof.Dsa.X86.Generation
