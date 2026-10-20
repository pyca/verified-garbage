module

public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! Whether the public domain contains a subgroup order. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem qTest_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa VG.Impl.Ffdh.Arm.Domain.qTest s fun t =>
      (t.z = !p.hasQ ∧ t.mem = s.mem) ∧ Rest [.r3, .r4] s t := by
  have addr (d : Nat) (hd : d ≤ 68) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have r28 := h.locals.read (d := 28) (by decide)
  have r32 := h.locals.read (d := 32) (by decide)
  have v28 := h.saved 28 h28
  have v32 := h.saved 32 h32
  change s.mem.readW (off (State.addr s.sp) 28) 32 = BitVec.ofNat 32 p.dom.length at v28
  change s.mem.readW (off (State.addr s.sp) 32) 32 = BitVec.ofNat 32 p.k at v32
  refine withRest [.r3, .r4] ?_ (by
    intro r hr i hi
    have checked : (instrs VG.Impl.Ffdh.Arm.Domain.qTest).all (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have flag := List.all_eq_true.mp checked i hi
    cases hi' : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.qTest
  ffrun [addr 28 (by decide), addr 32 (by decide), r28, r32, v28, v32, off]
  change ((BitVec.ofNat 32 p.dom.length - BitVec.ofNat 32 p.k - BitVec.ofNat 32 p.k) - 0#32 == 0#32) = !p.hasQ
  rw [BitVec.sub_zero]
  have length := p.domainLength
  have positive : (BitVec.ofNat 32 p.k) ≠ 0#32 := by
    intro zero
    have natZero := congrArg BitVec.toNat zero
    simp only [BitVec.toNat_ofNat, show (0#32).toNat = 0 from rfl,
      Nat.mod_eq_of_lt (by have := p.maxLength; omega : p.k < 2 ^ 32)] at natZero
    have := p.minLength
    omega
  cases hasQ : p.hasQ
  · rw [hasQ] at length
    simp at length
    rw [length, show 2 * p.k = p.k + p.k by omega, BitVec.ofNat_add,
      BitVec.add_sub_cancel, BitVec.sub_self]
    rfl
  · rw [hasQ] at length
    simp at length
    rw [length, show 3 * p.k = (p.k + p.k) + p.k by omega,
      BitVec.ofNat_add, BitVec.ofNat_add, BitVec.add_sub_cancel,
      BitVec.add_sub_cancel]
    simpa only [Bool.not_true, beq_eq_false_iff_ne] using positive

end VG.Proof.Ffdh.Arm
