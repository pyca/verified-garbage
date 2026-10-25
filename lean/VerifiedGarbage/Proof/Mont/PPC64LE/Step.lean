module

public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
public import VerifiedGarbage.Impl.Mont.PPC64LE
import VerifiedGarbage.Proof.Mont.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Montgomery arithmetic on PPC64LE: a multiply-accumulate step

`macStep rs src rd dst j` adds `r9 · y_j` and the carry word `r0` to the
word `t_j` at `[r3 + rd + 8j]`, for word `j` of the number at `[rs + src]`,
stores the low word of the sum at `[r3 + dst + 8j]`, and leaves its high
word in `r0` (`macStep_ok`): `x y + t + c ≤ (2⁶⁴ - 1)² + 2 (2⁶⁴ - 1) < 2¹²⁸`,
and neither `addze` into the product's high word, at most `2⁶⁴ - 2`, nor
the last one, carries.
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont.PPC64LE VG.Proof.Mont

theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem w32_lt (m : Mem) (base : Addr) (d : Nat) : w32 m base d < 2 ^ 32 := BitVec.isLt _

/-- One instruction, then the rest. -/
theorem wp_step {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop} (h : exec i s = some s')
    (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

/-- A step's sum is below `2¹²⁸`. -/
theorem mac_lt {x y t c : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (ht : t < 2 ^ 64) (hc : c < 2 ^ 64) :
    x * y + t + c < 2 ^ 128 := by
  have : x * y ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- The arithmetic of a step: the carrying adds keep the whole sum. -/
theorem mac_arith {P t c : Nat} (hP : P ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (ht : t < 2 ^ 64) (hc : c < 2 ^ 64) :
    ((P % 2 ^ 64 + t) % 2 ^ 64 + c) % 2 ^ 64 + 2 ^ 64 * (((P / 2 ^ 64 % 2 ^ 64 +
      (decide (2 ^ 64 ≤ P % 2 ^ 64 + t)).toNat) % 2 ^ 64 +
      (decide (2 ^ 64 ≤ (P % 2 ^ 64 + t) % 2 ^ 64 + c)).toNat) % 2 ^ 64) = P + t + c := by
  obtain ⟨e1, c1⟩ := ca_split (v := P % 2 ^ 64 + t) (by omega)
  obtain ⟨e3, c3⟩ := ca_split (v := (P % 2 ^ 64 + t) % 2 ^ 64 + c) (by omega)
  generalize (decide (2 ^ 64 ≤ P % 2 ^ 64 + t)).toNat = a at *
  generalize (decide (2 ^ 64 ≤ (P % 2 ^ 64 + t) % 2 ^ 64 + c)).toNat = b at *
  omega

/-- `[r3 + dst + 8j] = r9 · [rs + src + 8j] + r0 + [r3 + rd + 8j]`, the
high word to `r0`. -/
theorem macStep_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {rs : Reg} {K src rd dst j : Nat}
    (hb : At s base rs K) (h3 : At s base .r3 0) (hrs : rs ∉ [.r0, .r10, .r11] := by decide)
    (hsrc4 : src % 4 = 0) (hrd4 : rd % 4 = 0) (hdst4 : dst % 4 = 0)
    (hbd : K + (src + 8 * j) + 8 ≤ size) (hrd : rd + 8 * j + 8 ≤ size) (hdst : dst + 8 * j + 8 ≤ size) :
    WP isa (.block (macStep rs src rd dst j)) s fun u =>
      ∃ lo : BitVec 64, u.mem = s.mem.writeW (off base (dst + 8 * j)) lo ∧
      lo.toNat + 2 ^ 64 * (u.gpr .r0).toNat = (s.gpr .r9).toNat * (word s.mem base (K + (src + 8 * j))).toNat +
          (word s.mem base (rd + 8 * j)).toNat + (s.gpr .r0).toNat ∧
      Kp [.r0, .r10, .r11] s u := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrs
  obtain ⟨h0, h10, h11⟩ := hrs
  have hs15 := hs.small
  simp only [macStep]
  refine wp_step (ld_ok hs hb h0 (by omega) hbd) ?_
  refine wp_step exec_mulhu ?_
  refine wp_step exec_mul ?_
  refine wp_step exec_addc ?_
  refine wp_step exec_addze ?_
  refine wp_step (ld0_ok (((((hs.write _ _).write _ _).write _ _).writeCarry _ _).writeCarry _ _)
    (((((h3.write _).write _).write _).writeCarry _).writeCarry _) (by decide) (by omega) hrd) ?_
  refine wp_step exec_addc ?_
  refine wp_step exec_addze ?_
  refine wp_step (std_ok ((((((((hs.write _ _).write _ _).write _ _).writeCarry _ _).writeCarry _ _).write _ _).writeCarry
    _ _).writeCarry _ _) ((((((((h3.write _).write _).write _).writeCarry _).writeCarry _).write _).writeCarry _).writeCarry _)
    (by decide) (by omega) (d := dst + 8 * j) (by omega)) (WP.block_nil ?_)
  simp only [write_gpr, writeCarry_gpr, write_mem, RegUpd.mem_writeCarry, RegUpd.ca_writeCarry, reduceCtorEq, ite_false, ite_true, Nat.zero_add]
  refine ⟨_, rfl, ?_, ?_⟩
  · generalize hx : s.gpr .r9 = x
    generalize hy : word s.mem base (K + (src + 8 * j)) = y
    generalize ht : word s.mem base (rd + 8 * j) = t
    generalize hc : s.gpr .r0 = c
    have hP : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by have := x.isLt; omega) (by have := y.isLt; omega)
    have := mac_arith hP c.isLt t.isLt
    simp only [BitVec.toNat_ofNat, BitVec.toNat_mul] at this ⊢
    omega
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, writeCarry_gpr, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.Mont.PPC64LE
