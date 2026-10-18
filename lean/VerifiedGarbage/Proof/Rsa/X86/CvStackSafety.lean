module

public import VerifiedGarbage.Impl.Rsa.X86.CrtValues
public import VerifiedGarbage.Proof.Bignum.X86.CrtStackSafety

/-! # Compositional stack-pointer safety for all CRT dispatch widths -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.CrtValues
open VG.Impl.Bignum.X86 VG.Impl.Mont.X86
open VG.Proof.Bignum.X86.Crt (stackSafe shiftExponent_sp)

theorem seqs_sp (cs : List (Prog isa)) (h : ∀ c ∈ cs, c.all stackSafe = true) :
    (seqs cs).all stackSafe = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => exact h c (by simp)
    | cons d ds =>
      change c.all stackSafe && (seqs (d :: ds)).all stackSafe = true
      rw [h c (by simp), ih (fun x hx => h x (by simp [hx]))]
      rfl

theorem invStep_sp (n a b : Nat) : (invStep n a b).all stackSafe = true := by
  unfold invStep
  apply seqs_sp
  intro c hc
  simp only [subModP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [sub3, sel, half, Dynamic.chainW, Dynamic.selectsW, Dynamic.wordLoop,
    Code.all, List.all_append, shiftExponent_sp]
  all_goals rfl

theorem sized_sp (n : Nat) : (sized n).all stackSafe = true := by
  simp only [sized, loads, load, core, firstDiv, checks, invSetup, divQ, stores, store, seqs,
    List.cons_append, List.nil_append, eqS, copy, sub3, sel, inverse,
    VG.Impl.Rsa.X86.CrtValues.div, VG.Impl.Rsa.X86.Div.code, VG.Impl.Rsa.X86.Div.step,
    VG.Impl.Rsa.X86.Div.shiftArrays, VG.Impl.Rsa.X86.Div.shift, VG.Impl.Rsa.X86.Div.copyWords,
    VG.Impl.Rsa.X86.Div.reduce, loadBE, storeBE, reverseBytes,
    Dynamic.zerosW, Dynamic.chainW, Dynamic.selectsW, Dynamic.wordLoop, Code.all, List.all_append]
  rw [invStep_sp, invStep_sp]
  rfl

theorem dispatch_sp (widths : List Nat) : (dispatch widths).all stackSafe = true := by
  induction widths with
  | nil => rfl
  | cons w rest ih =>
    change true && ((sized w).all stackSafe && (dispatch rest).all stackSafe) = true
    rw [sized_sp, ih]
    rfl

theorem code_sp : code.all (fun i => !isa.writesSp i) = true := by
  change code.all stackSafe = true
  unfold code body valid
  simp only [Code.all]
  rw [dispatch_sp]
  rfl

end VG.Proof.Rsa.X86.CrtValues
