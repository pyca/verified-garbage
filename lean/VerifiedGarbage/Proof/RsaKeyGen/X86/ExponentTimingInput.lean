module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentFilterContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentFastTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64FramedTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.Framework.Offset

/-! # Both exponent paths derive public native geometry from the same candidate input -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

def fastGeometry (workspace p : BitVec 32) (w : Nat) : Sieve.Geometry :=
  ⟨p - 20#32, workspace + BitVec.ofNat 32 (slot w 5), 0, w, 0⟩

def modGeometry (workspace p : BitVec 32) (size w : Nat) : Mod64.ArrayGeometry :=
  ⟨p - 20#32, workspace, size, 2 * w, slot w 5, 128⟩

structure TimingInput (workspace p : BitVec 32) (size w candidate exponent : Nat) (s : State) : Prop where
  input : Input (workspace.setWidth 64) size w candidate exponent s
  stack : s.gpr .esp = p

theorem TimingInput.workspace {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : TimingInput workspace p size w candidate exponent s) : s.gpr .edi = workspace := by
  apply BitVec.eq_of_toNat_eq
  rw [S.input.scratch.edi_toNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans workspace.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem TimingInput.keepReadonly {workspace p : BitVec 32} {size w candidate exponent : Nat} {s t : State}
    (S : TimingInput workspace p size w candidate exponent s) (M : t.mem = s.mem) (K : Keeps [.eax] s t) :
    TimingInput workspace p size w candidate exponent t :=
  ⟨S.input.keepReadonly M K, (K.1 .esp (by decide)).trans S.stack⟩

theorem TimingInput.fastAddress {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : TimingInput workspace p size w candidate exponent s) :
    (workspace + BitVec.ofNat 32 (slot w 5)).setWidth 64 = off (workspace.setWidth 64) (slot w 5) := by
  conv_lhs => rw [← S.workspace]
  exact S.input.scratch.ea (d := slot w 5) (by have := S.input.space; have := S.input.width; omega)

theorem TimingInput.fastFit {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : TimingInput workspace p size w candidate exponent s) :
    (fastGeometry workspace p w).candidate.toNat + 8 * w ≤ 2 ^ 32 := by
  have fit := S.input.scratch.nowrap
  have space := S.input.space
  have positive := S.input.width
  have baseNat : (workspace.setWidth 64).toNat = workspace.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans workspace.isLt (by decide))]
  change (workspace + BitVec.ofNat 32 (slot w 5)).toNat + 8 * w ≤ 2 ^ 32
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := slot w 5) (by omega), Nat.mod_eq_of_lt (by rw [baseNat] at fit; omega)]
  rw [baseNat] at fit
  omega

theorem TimingInput.fastEntry {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : TimingInput workspace p size w candidate exponent s) : FastEntry (fastGeometry workspace p w) workspace s := by
  refine ⟨by have := S.input.fit; omega, by rw [S.stack]; rfl, S.workspace, ?_⟩
  intro i index
  change i < 2 * w at index
  change InRegions (s.rd ++ s.wr) (off ((workspace + BitVec.ofNat 32 (slot w 5)).setWidth 64) (4 * i)) 4
  rw [S.fastAddress]
  have read := S.input.scratch.read (d := slot w 5 + 4 * i) (n := 4) (by have := S.input.space; omega)
  simpa only [off, BitVec.add_assoc, ← BitVec.ofNat_add] using read

theorem TimingInput.modValid {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : TimingInput workspace p size w candidate exponent s) : (modGeometry workspace p size w).Valid := by
  refine ⟨by change 0 < 2 * w; have := S.input.width; omega, ?_, ?_, ?_⟩
  · change slot w 5 + 4 * (2 * w) ≤ size
    have := S.input.space; omega
  · change 128 + 8 ≤ size
    have := S.input.header; omega
  · change (⟨workspace.setWidth 64, size⟩ : Region).Disjoint ⟨(p - 20#32).setWidth 64, 20⟩
    rw [← S.stack]
    exact FilterStack.allocated_apart (by have := S.input.fit; omega) S.input.scratch.nowrap
      (by have := S.input.separate; rcases this with h | h; exact Or.inl h; exact Or.inr (by omega))

theorem TimingInput.modInput {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : TimingInput workspace p size w candidate exponent s) :
    Mod64.FramedInput (modGeometry workspace p size w) (candidate - 1) exponent s := by
  refine ⟨by have := S.input.fit; omega, ?_⟩
  refine ⟨FilterStack.allocated_scratch S.input.scratch S.input.fit S.input.separate, ?_, S.input.saved, S.input.exponentEq⟩
  change Sieve.StackContext (p - 20#32) (allocFrame 20 s)
  rw [← S.stack]
  exact FilterStack.allocated_context (by have := S.input.fit; omega)

end VG.Proof.RsaKeyGen.X86.ExponentFilter
