module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# PPC64LE: register reads through carrying writes

Untrusted: everything here is checked by Lean. The lemmas symbolic
execution reads registers and CA with after `State.writeCarry` (the
carrying adds and subtracts), without unfolding the write, as
`RegUpd.lean` does for `State.write`; and `toNat_add_ca`, the value of a
result and its carry together.
-/

@[expose] public section

namespace VG.PPC64LE.RegUpd

variable (s : State)

theorem ca_write (r : Reg) (v : BitVec 64) : (s.write r v).ca = s.ca := rfl

theorem gpr_writeCarry (r : Reg) (v : Nat) (r' : Reg) :
    (s.writeCarry r v).gpr r' = if r' = r then BitVec.ofNat 64 v else s.gpr r' := rfl

theorem gpr_writeCarry_self (r : Reg) (v : Nat) : (s.writeCarry r v).gpr r = BitVec.ofNat 64 v := by
  simp [State.writeCarry, State.write]

theorem gpr_writeCarry_of_ne {r r' : Reg} (v : Nat) (h : ¬r' = r) :
    (s.writeCarry r v).gpr r' = s.gpr r' := by
  simp [State.writeCarry, State.write, h]

theorem ca_writeCarry (r : Reg) (v : Nat) : (s.writeCarry r v).ca = decide (2 ^ 64 ≤ v) := rfl
theorem mem_writeCarry (r : Reg) (v : Nat) : (s.writeCarry r v).mem = s.mem := rfl
theorem rd_writeCarry (r : Reg) (v : Nat) : (s.writeCarry r v).rd = s.rd := rfl
theorem wr_writeCarry (r : Reg) (v : Nat) : (s.writeCarry r v).wr = s.wr := rfl
theorem sp_writeCarry (r : Reg) (v : Nat) : (s.writeCarry r v).sp = s.sp := rfl
theorem lr_writeCarry (r : Reg) (v : Nat) : (s.writeCarry r v).lr = s.lr := rfl

/-- A carrying write of a sum below `2⁶⁵` keeps all of it: the register's
value plus `2⁶⁴` times the carry. -/
theorem toNat_add_ca {r : Reg} {v : Nat} (h : v < 2 ^ 65) :
    ((s.writeCarry r v).gpr r).toNat + 2 ^ 64 * (s.writeCarry r v).ca.toNat = v := by
  rw [gpr_writeCarry_self, ca_writeCarry, BitVec.toNat_ofNat]
  by_cases hv : 2 ^ 64 ≤ v
  · simp only [hv, decide_true, Bool.toNat_true]
    rw [Nat.mod_eq_sub_mod hv, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [hv, decide_false, Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

end VG.PPC64LE.RegUpd
