module
import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.RvInputs
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Rsa.X86.RvBuffers
public import Init.Prelude
public import VerifiedGarbage.TCB.X86.State


/-! # Only the twelve cdecl arguments matter to CRT caller geometry -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Bignum.X86

theorem Inputs.argsEq {g : CallGeometry} {s : State} {args : Nat → BitVec 32} (h : Inputs g s)
    (eq : ∀ i < 12, args i = g.args i) : Inputs {g with args := args} s := by
  have buffers (i : Nat) (hi : i + 1 < 12) :
      ({g with args := args} : CallGeometry).buffer i = g.buffer i := by
    simp only [CallGeometry.buffer, eq i (by omega), eq (i + 1) hi]
  have writes : ({g with args := args} : CallGeometry).writes = g.writes := by
    unfold CallGeometry.writes
    rw [buffers 0 (by decide), buffers 2 (by decide)]
  refine ⟨h.ws, h.lower, h.upper, h.esp, h.room, h.top, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.wrEq⟩
  · intro i hi
    change CallArgument s g.B g.Z i (args i)
    rw [eq i hi]
    exact h.arguments i hi
  · intro i hi r hr
    rw [writes] at hr
    exact h.stackApart i hi r hr
  · intro i; rw [buffers _ (by omega)]; exact h.inputPositive i
  · intro i; rw [buffers _ (by omega)]; exact h.inputBound i
  · intro i
    rw [buffers _ (by omega)]
    change (args (4 + 2 * i.val)).toNat + _ ≤ _
    rw [eq (4 + 2 * i.val) (by omega)]
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

/-- The inputs over a geometry that agrees on the arguments' values and the rest. -/
theorem Inputs.geoEq {g g' : CallGeometry} {s : State} (h : Inputs g s) (hB : g'.B = g.B) (hZ : g'.Z = g.Z)
    (hn : g'.n = g.n) (hsp : g'.sp = g.sp) (hwr : g'.wr = g.wr) (eq : ∀ i < 12, g'.args i = g.args i) :
    Inputs g' s := by
  obtain ⟨⟨B, Z, n, sp, a, wr⟩⟩ := g'
  dsimp only at hB hZ hn hsp hwr eq
  subst hB hZ hn hsp hwr
  exact h.argsEq eq

end VG.Proof.Rsa.X86.Recover
