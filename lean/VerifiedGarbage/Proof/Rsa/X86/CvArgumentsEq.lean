module
import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.CvInputs
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Rsa.X86.CvBuffers
public import Init.Prelude
public import VerifiedGarbage.TCB.X86.State


/-! # Only the sixteen cdecl arguments matter to CRT caller geometry -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Bignum.X86

theorem Inputs.argsEq {g : CallGeometry} {s : State} {args : Nat → BitVec 32} (h : Inputs g s)
    (eq : ∀ i < 16, args i = g.args i) : Inputs {g with args := args} s := by
  have buffers (i : Nat) (hi : i + 1 < 16) :
      ({g with args := args} : CallGeometry).buffer i = g.buffer i := by
    simp only [CallGeometry.buffer, eq i (by omega), eq (i + 1) hi]
  have writes : ({g with args := args} : CallGeometry).writes = g.writes := by
    unfold CallGeometry.writes
    rw [buffers 0 (by decide), buffers 2 (by decide), buffers 4 (by decide)]
  refine ⟨h.ws, h.lower, h.upper, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.room⟩
  · intro i hi
    change CallArgument s g.base g.size i (args i)
    rw [eq i hi]
    exact h.arguments i hi
  · intro i hi r hr
    rw [writes] at hr
    exact h.stackApart i hi r hr
  · intro i; rw [buffers _ (by omega)]; exact h.inputPositive i
  · intro i; rw [buffers _ (by omega)]; exact h.inputBound i
  · intro i
    rw [buffers _ (by omega)]
    change (args (6 + 2 * i.val)).toNat + _ ≤ _
    rw [eq (6 + 2 * i.val) (by omega)]
    exact h.inputFit i
  · intro i; rw [buffers _ (by omega)]; exact h.inputRead i
  · intro i r hr; rw [writes] at hr; rw [buffers _ (by omega)]; exact h.inputApart i r hr
  · intro i; rw [buffers _ (by omega)]; exact h.outputPositive i
  · intro i; rw [buffers _ (by omega)]; exact h.outputBound i
  · intro i
    rw [buffers _ (by omega)]
    change (args (2 * i.val)).toNat + _ ≤ _
    rw [eq (2 * i.val) (by omega)]
    exact h.outputFit i
  · intro i; rw [buffers _ (by omega)]; exact h.outputWrite i
  · intro i; rw [buffers _ (by omega)]; exact h.outputScratch i
  · intro i j ne; rw [buffers _ (by omega), buffers _ (by omega)]; exact h.outputSeparate i j ne

end VG.Proof.Rsa.X86.CrtValues
