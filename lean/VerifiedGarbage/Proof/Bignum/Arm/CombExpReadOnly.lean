module

public import VerifiedGarbage.Proof.Bignum.Arm.CombTableState
public import VerifiedGarbage.Proof.Bignum.Arm.CombDigitLoad
import VerifiedGarbage.Proof.Bignum.Arm.CombExpShared
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.Arm.Instr

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
