module
public import VerifiedGarbage.Impl.Rsa.X86.CrtValues
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes

import VerifiedGarbage.Proof.Bignum.X86.ArgumentFrame

/-! # Buffer and argument geometry for CRT parameter calculation -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

structure CallGeometry where
  base : Addr
  size : Nat
  n : Nat
  args : Nat → BitVec 32

def CallGeometry.buffer (g : CallGeometry) (i : Nat) : Region :=
  ⟨byteAddr (g.args i), (g.args (i + 1)).toNat⟩

def CallGeometry.writes (g : CallGeometry) : List Region :=
  [⟨g.base, g.size⟩, g.buffer 0, g.buffer 2, g.buffer 4]

/-- What the body writes: the working space but its saved registers, and the outputs. -/
def bodyWrites (g : CallGeometry) : List Region :=
  [⟨off g.base 16, g.size - 16⟩, g.buffer 0, g.buffer 2, g.buffer 4]

structure Inputs (g : CallGeometry) (s : State) : Prop where
  ws : Ws s g.base g.size (2 * g.n) nArr
  lower : 8 ≤ g.n
  upper : g.n ≤ 128
  arguments : ∀ i, i < 16 → CallArgument s g.base g.size i (g.args i)
  stackApart : ∀ i, i < 16 → ∀ r ∈ g.writes, Region.Disjoint ⟨stackAddress s i, 4⟩ r
  inputPositive : ∀ j : Fin 4, 0 < (g.buffer (6 + 2 * j.val)).len
  inputBound : ∀ j : Fin 4, (g.buffer (6 + 2 * j.val)).len ≤ 8 * g.n
  inputFit : ∀ j : Fin 4, (g.args (6 + 2 * j.val)).toNat + (g.buffer (6 + 2 * j.val)).len ≤ 2 ^ 32
  inputRead : ∀ j : Fin 4, InRegions (s.rd ++ s.wr) (g.buffer (6 + 2 * j.val)).base (g.buffer (6 + 2 * j.val)).len
  inputApart : ∀ j : Fin 4, ∀ r ∈ g.writes, (g.buffer (6 + 2 * j.val)).Disjoint r
  outputPositive : ∀ j : Fin 3, 0 < (g.buffer (2 * j.val)).len
  outputBound : ∀ j : Fin 3, (g.buffer (2 * j.val)).len ≤ 8 * g.n
  outputFit : ∀ j : Fin 3, (g.args (2 * j.val)).toNat + (g.buffer (2 * j.val)).len ≤ 2 ^ 32
  outputWrite : ∀ j : Fin 3, InRegions s.wr (g.buffer (2 * j.val)).base (g.buffer (2 * j.val)).len
  outputScratch : ∀ j : Fin 3, (g.buffer (2 * j.val)).Disjoint ⟨g.base, g.size⟩
  outputSeparate : ∀ i j : Fin 3, i ≠ j → (g.buffer (2 * i.val)).Disjoint (g.buffer (2 * j.val))

theorem Inputs.after {g : CallGeometry} {s t : State} {regs : List Reg} (h : Inputs g s)
    (rest : Keeps regs s t) (di : .edi ∉ regs) (sp : .esp ∉ regs) (frame : Frame g.writes s.mem t.mem) :
    Inputs g t := by
  refine ⟨h.ws.rest rest di sp, h.lower, h.upper, ?_, ?_, h.inputPositive, h.inputBound,
    h.inputFit, ?_, h.inputApart, h.outputPositive, h.outputBound, h.outputFit, ?_, h.outputScratch,
    h.outputSeparate⟩
  · exact fun i hi => (h.arguments i hi).frame rest sp frame (h.stackApart i hi)
  · intro i hi r hr
    rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, rest.1 _ sp]]
    exact h.stackApart i hi r hr
  · intro j; rw [rest.2.1, rest.2.2]; exact h.inputRead j
  · intro j; rw [rest.2.2]; exact h.outputWrite j

end VG.Proof.Rsa.X86.CrtValues
