module

public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
public import VerifiedGarbage.Impl.Mont.PPC64LE
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Montgomery arithmetic on PPC64LE: a multiply-accumulate step

`mulStep rs src j` adds `r9 · b_j` and the carry `r10` to the digit of the
window at `[r7 + 4j]`, for digit `j` of the number at `[rs + src]`, and
leaves the carry in `r10` (`mulStep_ok`): with every operand below `2³²`,
`x = u b + t + c` is below `2⁶⁴`; its low half is stored and its high half
is the carry.
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont.PPC64LE VG.Proof.Mont

/-- A step's sum is below `2⁶⁴`. -/
theorem step_lt {u d t c : Nat} (hu : u < 2 ^ 32) (hd : d < 2 ^ 32) (ht : t < 2 ^ 32) (hc : c < 2 ^ 32) :
    u * d + t + c < 2 ^ 64 := by
  have : u * d ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem w32_lt (m : Mem) (base : Addr) (d : Nat) : w32 m base d < 2 ^ 32 := BitVec.isLt _

/-- One instruction, then the rest. -/
theorem wp_step {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop} (h : exec i s = some s')
    (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

/-- `[r7 + 4j] += r9 · [rs + src + 4j] + r10`, the carry to `r10`. -/
theorem mulStep_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {rs : Reg} {K src j w : Nat}
    (hb : At s base rs K) (h7 : At s base .r7 w) (hrs : rs ∉ [.r0, .r10, .r11, .r12, .r7] := by decide)
    (hbd : K + (src + 4 * j) + 4 ≤ size) (hwd : w + 4 * j + 4 ≤ size)
    (hu : (s.gpr .r9).toNat < 2 ^ 32) (hc : (s.gpr .r10).toNat < 2 ^ 32)
    (ht : w32 s.mem base (w + 4 * j) < 2 ^ 32 := w32_lt _ _ _) :
    WP isa (.block (mulStep rs src j)) s fun u =>
      u.mem = s.mem.writeW (off base (w + 4 * j)) (BitVec.ofNat 32
        ((s.gpr .r9).toNat * w32 s.mem base (K + (src + 4 * j)) + w32 s.mem base (w + 4 * j) +
          (s.gpr .r10).toNat)) ∧
      (u.gpr .r10).toNat = ((s.gpr .r9).toNat * w32 s.mem base (K + (src + 4 * j)) +
          w32 s.mem base (w + 4 * j) + (s.gpr .r10).toNat) / 2 ^ 32 ∧
      Kp [.r10, .r11, .r12] s u := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrs
  obtain ⟨h0, h10, h11, h12, h7'⟩ := hrs
  have hx := step_lt hu (w32_lt s.mem base (K + (src + 4 * j))) ht hc
  simp only [mulStep]
  refine wp_step (lwz_ok hs hb h0 hbd) ?_
  refine wp_step (lwz_ok (hs.write _ _) (h7.write _) (by decide) hwd) ?_
  refine wp_step exec_mul ?_
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  refine wp_step (stw_ok (((((hs.write _ _).write _ _).write _ _).write _ _).write _ _)
    ((((((h7.write _).write _).write _).write _).write _)) (by decide) hwd) ?_
  refine wp_step (exec_lsr_d (by decide)) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true]
  have e : (BitVec.ofNat 64 (w32 s.mem base (w + 4 * j)) + s.gpr .r9 *
      BitVec.ofNat 64 (w32 s.mem base (K + (src + 4 * j))) + s.gpr .r10).toNat =
      (s.gpr .r9).toNat * w32 s.mem base (K + (src + 4 * j)) + w32 s.mem base (w + 4 * j) +
        (s.gpr .r10).toNat := by
    have hb32 := w32_lt s.mem base (K + (src + 4 * j))
    have hm : (s.gpr .r9).toNat * w32 s.mem base (K + (src + 4 * j)) < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, toNat_ofNat_lt (by omega),
      toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨by rw [e], by rw [BitVec.toNat_ushiftRight, e, Nat.shiftRight_eq_div_pow], ?_⟩
  exact ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false], rfl, rfl, rfl, rfl⟩

end VG.Proof.Mont.PPC64LE
