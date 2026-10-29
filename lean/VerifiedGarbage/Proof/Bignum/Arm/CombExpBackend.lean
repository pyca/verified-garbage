module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpShared
public import VerifiedGarbage.Proof.Bignum.Arm.CombTableState
public import VerifiedGarbage.Proof.Bignum.Arm.CombDigitLoad
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Framework.Offset
/-! Every callable RSA Montgomery backend supports the same immutable comb context. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombExpReadOnly.lean`, which only this module imported.
section

/-! The immutable exponent and table lie outside every arithmetic write region. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure ReadOnly (source table : BitVec 32) (w M g N : Nat) (bs : List Byte)
    (regions : List Region) (s : State) : Prop where
  exponent : CombDigit.Source source bs s
  entries : CombTable table w M g N s
  sourceSeparate : ∀ r∈regions, (⟨State.addr source,bs.length⟩:Region).Disjoint r
  tableSeparate : ∀ r∈regions, (⟨State.addr table,32*(8*w)⟩:Region).Disjoint r

theorem ReadOnly.after_frame {source table : BitVec 32} {w M g N : Nat} {bs : List Byte}
    {regions : List Region} {s t : State} {rs : List Reg}
    (h : ReadOnly source table w M g N bs regions s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t) :
    ReadOnly source table w M g N bs regions t := by
  have entryFits (digit : Nat) (hd : digit<32) (j : Nat) (hj : j<2*w) :
      8*w*digit+4*j+4≤32*(8*w) := by
    have last := Nat.mul_le_mul_left (8*w) (show digit+1≤32 by omega)
    have limb := Nat.mul_le_mul_left 4 (show j+1≤2*w by omega)
    rw [Nat.mul_add,Nat.mul_one] at last
    omega
  refine ⟨⟨h.exponent.fits,?_,?_⟩,⟨h.entries.positive,h.entries.fits,?_,?_⟩,
    h.sourceSeparate,h.tableSeparate⟩
  · rw [rest.rd,rest.wr]; exact h.exponent.readable
  · intro j hj
    exact (frame.bytes h.sourceSeparate (by change bs.length≤2^64; have := h.exponent.fits; omega) hj).trans (h.exponent.bytes j hj)
  · rw [rest.rd,rest.wr]; exact h.entries.readable
  · intro digit hd
    rw [←h.entries.values digit hd]
    apply val32_congr
    intro j hj
    apply congrArg BitVec.toNat
    apply frame.readW (r:=⟨State.addr table,32*(8*w)⟩) _ h.tableSeparate (by decide)
    exact Offset.contains_base _ (entryFits digit hd j hj) (by
      have := entryFits digit hd j hj
      have := h.entries.fits
      omega)

end VG.Proof.Bignum.Arm.CombExp
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Arm.FrameStack

def writeRegions (base sp : BitVec 32) (len : Nat) : List Region :=
  [⟨State.addr base,8*len⟩,belowA sp 48]

abbrev Persistent (base source table sp : BitVec 32) (len w M g N : Nat) (bs : List Byte) (s : State) : Prop :=
  TwoExp.CallReady base sp len s ∧ ReadOnly source table w M g N bs (writeRegions base sp len) s

def arithmetic (backend : MontBackend) (base source table sp : BitVec 32)
    (len w M g N : Nat) (bs : List Byte) :
    TwoExp.Montgomery base len w (Persistent base source table sp len w M g N bs)
      (writeRegions base sp len) :=
  withInvariant (TwoExp.sharedMontgomery base sp len w backend.name backend.mul
    (fun _ _ _ ho ha hb s h=>backend.correct s h ho ha hb) backend.stackOk)
    (ReadOnly source table w M g N bs (writeRegions base sp len))
    (by intro s t frame rest h; exact h.after_frame frame rest)

end VG.Proof.Bignum.Arm.CombExp
