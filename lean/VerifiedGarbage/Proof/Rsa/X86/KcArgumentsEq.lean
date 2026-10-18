module

public import VerifiedGarbage.Proof.Rsa.X86.KcPair

/-! # Only the declared cdecl arguments matter to key-check caller geometry -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Bignum.X86

theorem Inputs.argsEq {g : CallGeometry} {s : State} {args : Nat → BitVec 32} (h : Inputs g s)
    (eq : ∀ i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full + 2, args i = g.args i) : Inputs {g with args := args} s := by
  have buffers (i : Nat) (hi : i + 1 < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full + 2) :
      ({g with args := args} : CallGeometry).buffer i = g.buffer i := by
    simp only [CallGeometry.buffer, eq i (by omega), eq (i + 1) hi]
  have writes : ({g with args := args} : CallGeometry).writes = g.writes := rfl
  refine ⟨h.ws, h.lower, h.upper, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    change CallArgument s g.base g.size i (args i)
    rw [eq i hi]
    exact h.arguments i hi
  · intro i hi r hr
    rw [writes] at hr
    exact h.stackApart i hi r hr
  · intro i hi; change 2 * i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full at hi; rw [buffers _ (by omega)]; exact h.inputPositive i hi
  · intro i hi; change 2 * i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full at hi; rw [buffers _ (by omega)]; exact h.inputBound i hi
  · intro i hi
    change 2 * i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full at hi
    rw [buffers _ (by omega)]
    change (args (2 * i)).toNat + _ ≤ _
    rw [eq (2 * i) (by omega)]
    exact h.inputFit i hi
  · intro i hi; change 2 * i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full at hi; rw [buffers _ (by omega)]; exact h.inputRead i hi
  · intro i hi r hr; change 2 * i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full at hi; rw [writes] at hr; rw [buffers _ (by omega)]; exact h.inputApart i hi r hr

end VG.Proof.Rsa.X86.KeyCheck
