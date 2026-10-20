module

public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Bases and exponents have separate public pointer/count slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem powerArgs_ok (s : State) {p : Inputs} {slots : List Nat} (bs es ec : Nat)
    (h : Context p slots s) (stable : stableSlots slots = true)
    (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs bs es ec)) s fun t =>
      (t.gpr .r4 = p.slotValue bs ∧ t.gpr .r6 = BitVec.ofNat 32 p.k ∧
        t.gpr .r1 = p.slotValue es ∧ t.gpr .r2 = p.slotValue ec ∧ t.mem = s.mem) ∧
      Rest [.r1, .r2, .r4, .r6] s t := by
  have bounds (d : Nat) (hd : d ∈ slots) := (stableSlots_at stable hd).1
  have small (d : Nat) (hd : d ∈ slots) : d < 4096 := by have := bounds d hd; omega
  have addr (d : Nat) (hd : d ∈ slots) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := bounds d hd; have := h.locals.space.nowrap; omega)
  have rb := h.locals.read (bounds bs hb)
  have re := h.locals.read (bounds es he)
  have rc := h.locals.read (bounds ec hc)
  have rk := h.locals.read (bounds 32 hk)
  have vb := h.saved bs hb
  have ve := h.saved es he
  have vc := h.saved ec hc
  have vk := h.saved 32 hk
  change s.mem.readW (off (State.addr s.sp) 32) 32 = BitVec.ofNat 32 p.k at vk
  refine withRest [.r1, .r2, .r4, .r6] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs bs es ec) : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have flag := List.all_eq_true.mp checked i hi
    cases hi' : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.powerArgs
  ffrun [small bs hb, small es he, small ec hc, addr bs hb, addr es he, addr ec hc, addr 32 hk,
    rb, re, rc, rk, vb, ve, vc, vk, off]

end VG.Proof.Ffdh.Arm
