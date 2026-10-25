module

public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Montgomery arithmetic on PPC64LE: carrying writes

What a carrying write (`State.writeCarry`: `addc`, `adde`, `addze`, `subfc`,
`subfe`) keeps, as `Words.lean` has it for `State.write`, and a sum split
into its low word and its carry (`ca_split`).
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont

theorem writeCarry_gpr (s : State) (d : Reg) (v : Nat) (r : Reg) :
    (s.writeCarry d v).gpr r = if r = d then BitVec.ofNat 64 v else s.gpr r := rfl

theorem Kp.writeCarry (s : State) {d : Reg} (v : Nat) {rs : List Reg} (hd : d ∈ rs) :
    Kp rs s (s.writeCarry d v) :=
  ⟨fun r hr => by
    have : r ≠ d := fun h => hr (h ▸ hd)
    rw [writeCarry_gpr, ite_eq_right_iff.mpr (fun h => absurd h this)], rfl, rfl, rfl, rfl⟩

theorem At.writeCarry {s : State} {base : Addr} {r : Reg} {K : Nat} (h : At s base r K) {d : Reg}
    (v : Nat) (hd : r ≠ d := by decide) : At (s.writeCarry d v) base r K := by
  rw [At, writeCarry_gpr, ite_eq_right_iff.mpr (fun e => absurd e hd)]; exact h

theorem Ws.writeCarry {s : State} {base : Addr} {size : Nat} (h : Ws s base size) (d : Reg) (v : Nat) :
    Ws (s.writeCarry d v) base size := h.of_wr rfl

/-- A sum below `2⁶⁵`: its low word and its carry. -/
theorem ca_split {v : Nat} (h : v < 2 ^ 65) :
    v % 2 ^ 64 + 2 ^ 64 * (decide (2 ^ 64 ≤ v)).toNat = v ∧ (decide (2 ^ 64 ≤ v)).toNat ≤ 1 := by
  by_cases hv : 2 ^ 64 ≤ v
  · simp only [hv, decide_true, Bool.toNat_true]; omega
  · simp only [hv, decide_false, Bool.toNat_false]; omega

end VG.Proof.Mont.PPC64LE
