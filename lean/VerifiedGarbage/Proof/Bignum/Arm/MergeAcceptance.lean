module

public import VerifiedGarbage.Impl.Bignum.Arm.MergeAcceptance
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Exact conjunction of independent secret validation bits -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str op2_reg dpVal)

theorem mergeAcceptance_ok (s : State) (fit : s.sp.toNat + 52 ≤ 2 ^ 32)
    (write : InRegions s.wr (off (State.addr s.sp) 48) 4) :
    WP isa (.block mergeAcceptance) s fun t =>
      t.gpr .r11 = s.gpr .r11 &&& s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      t.mem = s.mem.writeW (off (State.addr s.sp) 48)
        (s.gpr .r11 &&& s.mem.readW (off (State.addr s.sp) 48) 32) ∧
      Frame [⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem ∧ Rest [.r1, .r11, .r12] s t := by
  have read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4 := by
    obtain ⟨R, hr, sub⟩ := write
    exact ⟨R, List.mem_append_right _ hr, sub⟩
  unfold mergeAcceptance
  refine wp_stackAddr (by decide) fun u a => ?_
  have addr : State.addr (u.gpr .r12 + 0#32) = off (State.addr s.sp) 48 := by
    rw [a.gpr, BitVec.add_zero]; exact addr_add (by omega)
  refine wp_ldr (a := off (State.addr s.sp) 48) (by decide) addr
    (by rw [a.rd, a.wr]; exact read) fun v b => ?_
  refine wp_dp (op2_reg _ _) fun z c => ?_
  refine wp_str (a := off (State.addr s.sp) 48) (by decide)
    (by rw [c.other .r12 (by decide), b.other .r12 (by decide)]; exact addr)
    (by rw [c.wr, b.wr, a.wr]; exact write) fun t d => WP.block_nil ?_
  have value : z.gpr .r11 = s.gpr .r11 &&& s.mem.readW (off (State.addr s.sp) 48) 32 := by
    rw [c.gpr, dpVal, b.other .r11 (by decide), a.other .r11 (by decide), b.gpr, a.mem]
  have mem : t.mem = s.mem.writeW (off (State.addr s.sp) 48)
      (s.gpr .r11 &&& s.mem.readW (off (State.addr s.sp) 48) 32) := by
    rw [d.mem, value, c.mem, b.mem, a.mem]
  have restD : Rest [] z t := d.rest []
  refine ⟨(restD.gpr .r11 (by simp)).trans value, mem, ?_,
    (a.rest (by simp)).trans ((b.rest (by simp)).trans ((c.rest (by simp)).trans (restD.mono (by simp))))⟩
  rw [mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem validation_bits_and (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P then 1 else 0) : BitVec 32) &&& (if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp only [hp, hq, ↓reduceIte] <;> decide

end VG.Proof.Bignum.Arm
