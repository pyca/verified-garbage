module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyPrimes
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import VerifiedGarbage.Proof.Rsa.X86.CvHelperTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductTiming
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Factor preparation keeps values and choices secret on i686 -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.Rsa.X86.Keys VG.Impl.RsaKeyGen.X86.Key

theorem primeProduct_public (n out a b : Nat) : KeyPublic (primeProduct n out a b) := by
  exact ⟨Product.productHint true, Product.productEndTaint true,
    Product.product_check true _ _ _ _ _ _, rfl⟩

theorem order_public (n : Nat) : KeyPublic (order n) := by
  unfold order
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact sub3_public ..
  · exact store_public _
  · exact copy_public ..
  · exact sel_public ..
  · exact sel_public ..

theorem decTo_public (n out a : Nat) : KeyPublic (decTo n out a) := by
  unfold decTo
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact eqS_public ..
  · exact sel_public ..
  · exact sub3_public ..

theorem primes_public (n : Nat) : KeyPublic (primes n) := by
  unfold primes
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact order_public _
  · exact decTo_public ..
  · exact decTo_public ..
  · exact primeProduct_public ..

theorem halfIf_public (n j : Nat) : KeyPublic (halfIf n j) := by
  unfold halfIf
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact copy_public ..
  · exact zeroCarry_public
  · exact half_public ..
  · exact sel_public ..

theorem bothEven_public (n : Nat) : KeyPublic (.block (bothEven n)) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (.block [ .mov .eax (.mem (VG.Impl.Mont.X86.sc 0)),
      .alu .or .eax (.mem (VG.Impl.Mont.X86.sc 0)), .alu .and .eax (.imm 0), .alu .xor .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax] : Prog isa)), workspaceTaint true, ?_, rfl⟩
  exact (check_of_erase_eq (.block (bothEven n)) (.block [ .mov .eax (.mem (VG.Impl.Mont.X86.sc 0)), .alu .or .eax (.mem (VG.Impl.Mont.X86.sc 0)), .alu .and .eax (.imm 0), .alu .xor .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax] : Prog isa)
    (workspaceTaint true) (VG.Taint.hintOf taint (workspaceTaint true) (.block [ .mov .eax (.mem (VG.Impl.Mont.X86.sc 0)), .alu .or .eax (.mem (VG.Impl.Mont.X86.sc 0)), .alu .and .eax (.imm 0), .alu .xor .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax] : Prog isa)) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)

theorem halveStep_public (n : Nat) : KeyPublic (halveStep n) := by
  unfold halveStep
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact bothEven_public _
  · exact halfIf_public ..
  · exact halfIf_public ..
  · exact halfIf_public ..

theorem twos_loop_public (n : Nat) : KeyPublic (.loop (twoStep n) .ne) := by
  obtain ⟨hint, out, checked, preserves⟩ := halveStep_public n
  have body : VG.Taint.check taint (workspaceTaint true) (twoStep n) (.seq (workspaceTaint true) hint (.block []) : VG.Taint.Hint VG.X86.Taint.T) = some counterEndTaint :=
    exponent_check_seq taint checked preserves (by kernel_rfl)
  refine ⟨.loop (workspaceTaint true) (.seq (workspaceTaint true) hint (.block []) : VG.Taint.Hint VG.X86.Taint.T), counterEndTaint, ?_, rfl⟩
  change (if taint.le (workspaceTaint true) (workspaceTaint true) then
    (VG.Taint.check taint (workspaceTaint true) _ (.seq (workspaceTaint true) hint (.block []) : VG.Taint.Hint VG.X86.Taint.T)).bind
      (fun t => if taint.le (workspaceTaint true) t && taint.condPub t .ne then some t else none)
    else none) = _
  rw [body]
  rfl

theorem twos_public (n : Nat) : KeyPublic (twos n) := by
  unfold twos
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact copy_public ..
  · exact copy_public ..
  · exact ⟨.block [], workspaceTaint true, rfl, rfl⟩
  · exact twos_loop_public _

end VG.Proof.RsaKeyGen.X86.Key
