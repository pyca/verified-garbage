module

public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset

/-! The modulus arguments are copied to the slots RSA's helpers consume. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem prepareArgs_store (s : State) {p : Inputs} {slots : List Nat} (slot : Nat)
    (h : Context p slots s) (hs : slot ∈ slots) (hk : 32 ∈ slots) (fit : slot + 4 ≤ 72) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs slot)) s fun t =>
      (t.gpr .r4 = p.slotValue slot ∧ t.gpr .r6 = BitVec.ofNat 32 p.k ∧ t.gpr .r12 = s.sp ∧
      t.mem = (s.mem.writeW (off (State.addr s.sp) 8) (p.slotValue slot)).writeW
        (off (State.addr s.sp) 12) (BitVec.ofNat 32 p.k)) ∧ Rest [.r4, .r6, .r12] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have src := h.saved slot hs
  have count := h.saved 32 hk
  change s.mem.readW (off (State.addr s.sp) 32) 32 = BitVec.ofNat 32 p.k at count
  have slotBound : slot < 4096 := by omega
  have readS := h.locals.read fit
  have readK := h.locals.read (d := 32) (by decide)
  have write8 := h.locals.space.write (off := 8) (by decide)
  have write12 := h.locals.space.write (off := 12) (by decide)
  refine withRest [.r4, .r6, .r12] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs slot) : Prog isa)).all (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have flag := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.prepareArgs VG.Impl.Ffdh.Arm.Domain.st
  ffrun [slotBound, addr slot fit, addr 32 (by decide), addr 8 (by decide), addr 12 (by decide),
    src, count, readS, readK, write8, write12, BitVec.add_zero, off]

end VG.Proof.Ffdh.Arm
