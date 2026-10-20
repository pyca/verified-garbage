module

public import VerifiedGarbage.Impl.Rsa.X86.CrtValues
public import VerifiedGarbage.Proof.Bignum.X86.CrtStackSafety

/-! # Stack-pointer safety of the inverse's steps, shared by the key checks and prime recovery -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.CrtValues
open VG.Impl.Bignum.X86 VG.Impl.Mont.X86
open VG.Proof.Bignum.X86.Crt (stackSafe)

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
    Code.all, List.all_append, Dynamic.shiftDown]
  all_goals rfl

end VG.Proof.Rsa.X86.CrtValues
