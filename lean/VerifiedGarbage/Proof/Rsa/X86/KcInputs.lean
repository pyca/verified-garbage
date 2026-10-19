module

public import VerifiedGarbage.Proof.Rsa.X86.KcBody
public import VerifiedGarbage.Proof.Bignum.X86.ArgumentFrame
public import VerifiedGarbage.Proof.Bignum.X86.LoadBE

/-! # Buffer and argument geometry for CRT parameter calculation -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys

structure CallGeometry where
  full : Bool
  base : Addr
  size : Nat
  n : Nat
  args : Nat → BitVec 32

def CallGeometry.buffer (g : CallGeometry) (i : Nat) : Region :=
  ⟨byteAddr (g.args i), (g.args (i + 1)).toNat⟩

def CallGeometry.writes (g : CallGeometry) : List Region :=
  [⟨g.base, g.size⟩]

structure Inputs (g : CallGeometry) (s : State) : Prop where
  ws : Ws s g.base g.size (2 * g.n) nArr
  lower : 8 ≤ g.n
  upper : g.n ≤ 128
  arguments : ∀ i, i < scratchArg g.full + 2 → CallArgument s g.base g.size i (g.args i)
  stackApart : ∀ i, i < scratchArg g.full + 2 → ∀ r ∈ g.writes, Region.Disjoint ⟨stackAddress s i, 4⟩ r
  inputPositive : ∀ j : Nat, 2 * j < scratchArg g.full → 0 < (g.buffer (2 * j)).len
  inputBound : ∀ j : Nat, 2 * j < scratchArg g.full → (g.buffer (2 * j)).len ≤ 8 * g.n
  inputFit : ∀ j : Nat, 2 * j < scratchArg g.full → (g.args (2 * j)).toNat + (g.buffer (2 * j)).len ≤ 2 ^ 32
  inputRead : ∀ j : Nat, 2 * j < scratchArg g.full → InRegions (s.rd ++ s.wr) (g.buffer (2 * j)).base (g.buffer (2 * j)).len
  inputApart : ∀ j : Nat, 2 * j < scratchArg g.full → ∀ r ∈ g.writes, (g.buffer (2 * j)).Disjoint r

theorem Inputs.after {g : CallGeometry} {s t : State} {regs : List Reg} (h : Inputs g s)
    (rest : Keeps regs s t) (di : .edi ∉ regs) (sp : .esp ∉ regs) (frame : Frame g.writes s.mem t.mem) :
    Inputs g t := by
  refine ⟨h.ws.rest rest di sp, h.lower, h.upper, ?_, ?_, h.inputPositive, h.inputBound,
    h.inputFit, ?_, h.inputApart⟩
  · exact fun i hi => (h.arguments i hi).frame rest sp frame (h.stackApart i hi)
  · intro i hi r hr
    rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, rest.1 _ sp]]
    exact h.stackApart i hi r hr
  · intro j hj; rw [rest.2.1, rest.2.2]; exact h.inputRead j hj

end VG.Proof.Rsa.X86.KeyCheck
