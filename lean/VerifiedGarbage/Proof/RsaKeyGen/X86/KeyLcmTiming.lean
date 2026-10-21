module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyLcm
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import VerifiedGarbage.Proof.Rsa.X86.CvHelperTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstantTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrimesTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionTiming

/-! # Native LCM arithmetic reveals neither factor nor any intermediate bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86.Key

theorem evenFlag_public (n input : Nat) : KeyPublic (.block (evenFlag n input)) := by
  let reference : Prog isa := .block [
    .mov .eax (.mem (VG.Impl.Mont.X86.sc 0)), .alu .and .eax (.imm 0),
    .alu .xor .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax]
  let hint := VG.Taint.hintOf taint (workspaceTaint true) reference
  refine ⟨hint, workspaceTaint true, ?_, rfl⟩
  exact (check_of_erase_eq (.block (evenFlag n input)) reference
    (workspaceTaint true) hint rfl rfl rfl).trans (by rfl)

theorem oddFlag_public (n input : Nat) : KeyPublic (.block (oddFlag n input)) := by
  let reference : Prog isa := .block [
    .mov .eax (.imm 0), .alu .sub .eax (.reg .ebx),
    .alu .and .eax (.mem (VG.Impl.Mont.X86.sc 0)), .alu .and .eax (.imm 0),
    .store (VG.Impl.Mont.X86.sc 0) .eax]
  let hint := VG.Taint.hintOf taint (workspaceTaint true) reference
  refine ⟨hint, workspaceTaint true, ?_, rfl⟩
  exact (check_of_erase_eq (.block (oddFlag n input)) reference
    (workspaceTaint true) hint rfl rfl rfl).trans (by rfl)

theorem oddSecond_public (n : Nat) : KeyPublic (oddSecond n) := by
  unfold oddSecond
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact evenFlag_public ..
  · exact copy_public ..
  · exact sel_public ..
  · exact sel_public ..

theorem oddModulus_public (n input out : Nat) : KeyPublic (oddModulus n input out) := by
  unfold oddModulus
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact constArray_public ..
  · exact sub3_public ..
  · exact oddFlag_public ..
  · exact sel_public ..

theorem widenCopy_public (n k out src : Nat) : KeyPublic (widenCopy n k out src) := by
  have clear : KeyPublic (VG.Impl.Mont.X86.Dynamic.zerosW (VG.Impl.Rsa.X86.Keys.slot n out) (n + 2)) :=
    ⟨zerosHint true, zerosTaint true, zeros_check true _ _, rfl⟩
  exact clear.seq (copyWords_public ..)

theorem gcdFrom_public (n : Nat) : KeyPublic (gcdFrom n) := by
  unfold gcdFrom
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact inverseFrom_public ..
  · exact widenCopy_public ..
  · exact sel_public ..

theorem gcdPart_public (n : Nat) : KeyPublic (gcdPart n) := by
  unfold gcdPart
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact oddSecond_public _
  · exact oddModulus_public ..
  · exact gcdFrom_public _

theorem lcmPart_public (n : Nat) : KeyPublic (lcmPart n) := by
  unfold lcmPart
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact twos_public _
  · exact gcdPart_public _
  · exact divisionFrom_public ..

theorem lcmPart_constantTime (n : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint true)) (lcmPart n) := by
  obtain ⟨hint, out, checked, _⟩ := lcmPart_public n
  exact VG.Taint.constantTime (A := taint) (workspaceTaint true) (fun _ _ _ _ H => H)
    (hc := hint) (by rw [checked]; rfl)

end VG.Proof.RsaKeyGen.X86.Key
