module

public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Taint summaries for the RSA inverse workspace operations -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic

/-- A workspace operation keeps its base and the outer counter public. -/
def KeyPublic (c : Prog isa) : Prop := ∃ hint out,
  VG.Taint.check taint (workspaceTaint true) c hint = some out ∧
  taint.le (workspaceTaint true) out = true

theorem KeyPublic.seq {a b : Prog isa} (ha : KeyPublic a) (hb : KeyPublic b) : KeyPublic (.seq a b) := by
  obtain ⟨ah, ao, ac, al⟩ := ha
  obtain ⟨bh, bo, bc, bl⟩ := hb
  exact ⟨.seq (workspaceTaint true) ah bh, bo, exponent_check_seq taint ac al bc, bl⟩

theorem KeyPublic.seqs {cs : List (Prog isa)} (h : ∀ c ∈ cs, KeyPublic c) : KeyPublic (seqs cs) := by
  induction cs with
  | nil => exact ⟨.block [], workspaceTaint true, rfl, rfl⟩
  | cons c cs ih =>
    cases cs with
    | nil => exact h c (by simp)
    | cons d ds =>
      exact (h c (by simp)).seq (ih (fun x hx => h x (by simp [hx])))

theorem sub3_public (n o a b : Nat) : KeyPublic (sub3 n o a b) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (sub3 1 0 1 2))),
      { regs := .ofList [.edi, .ebp, .edx, .esi], flags := false }, ?_, ?_⟩
  · rw [check_of_erase_eq (sub3 n o a b) (sub3 1 0 1 2) (workspaceTaint true)
      (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (sub3 1 0 1 2))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)]
    rfl
  · rfl

theorem sel_public (n o a b sl : Nat) : KeyPublic (sel n o a b sl) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (sel 1 0 1 2 100))), rowTaint true, ?_, ?_⟩
  · rw [check_of_erase_eq (sel n o a b sl) (sel 1 0 1 2 100) (workspaceTaint true)
      (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (sel 1 0 1 2 100))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)]
    rfl
  · rfl

theorem half_public (n j : Nat) : KeyPublic (half n j) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (half 1 0))),
      { regs := .ofList [.edi, .ebp, .eax, .esi], flags := false }, ?_, by rfl⟩
  exact (check_of_erase_eq (half n j) (half 1 0) (workspaceTaint true)
      (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (half 1 0))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)

theorem bitOf_public (n sl j : Nat) : KeyPublic (.block (bitOf n sl j)) := by
  refine ⟨.block [], workspaceTaint true, ?_, rfl⟩
  change taint.checkBlock (workspaceTaint true) (bitOf n sl j) = _
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
  change taint.checkBlock (workspaceTaint true)
    [.mov .eax (.mem (VG.Impl.Mont.X86.sc 0)), .alu .and .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax] = _
  rfl

theorem store_public (sl : Nat) : KeyPublic (.block [.store (VG.Impl.Mont.X86.sc sl) .ebx]) := by
  refine ⟨.block [], workspaceTaint true, ?_, rfl⟩
  change taint.checkBlock (workspaceTaint true) [_] = _
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
  change taint.checkBlock (workspaceTaint true) [.store (VG.Impl.Mont.X86.sc 0) .ebx] = _
  rfl

theorem masks_public : KeyPublic (.block (([.store (VG.Impl.Mont.X86.sc sB) .ebx] : List Instr) ++ andS sC sOdd sB)) := by
  exact ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem zeroCarry_public : KeyPublic (.block [.mov .ebx (.imm 0)]) := by
  exact ⟨.block [], { regs := .ofList [.edi, .esi, .ebx], flags := false }, rfl, rfl⟩

theorem xorCarry_public : KeyPublic (.block [.alu .xor .ebx (.mem (VG.Impl.Mont.X86.sc sB))]) := by
  exact ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem subModP_public (n o a b : Nat) : KeyPublic (seqs (subModP n o a b)) := by
  apply KeyPublic.seqs
  intro c hc
  simp only [subModP, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact sub3_public ..
  · exact store_public _
  · exact sel_public ..
  · exact sub3_public ..

end VG.Proof.Rsa.X86.Keys
