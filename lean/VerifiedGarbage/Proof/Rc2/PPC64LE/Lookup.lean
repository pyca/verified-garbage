module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Scan
public import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Rc2.PPC64LE.Lookup
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-!
# RC2 on PPC64LE: the lookups

`keyLookup_run`: the schedule's scan leaves key word `idx` in `r11`, for
`q = 2 idx` in `r10`. `entry_byte`: a byte table's scan leaves its byte.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

/-- The chunks' region facts, from the table's. -/
theorem chunks_in {R : List Region} {T : Addr} {len : Nat}
    (hr : ∀ o n, o + n ≤ len → InRegions R (T + BitVec.ofNat 64 o) n) {i : Nat} (hi : 32 * i + 32 ≤ len) :
    InRegions R (ch T i) 16 ∧ InRegions R (ch T i + 16#64) 16 := by
  rw [ch_eq, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]
  exact ⟨hr _ _ (by omega), hr _ _ (by omega)⟩

/-- Key word `idx` of the schedule at `T`, from its two bytes. -/
theorem entry_word (m : Mem) (T : Addr) {idx : Nat} (hidx : idx < 64) :
    (m (T + BitVec.ofNat 64 (2 * idx))).setWidth 64 ||| (m (T + BitVec.ofNat 64 (2 * idx) + 1#64)).setWidth 64 <<< 8 =
      ((Spec.Rc2.scheduleAt m T).getD idx 0).setWidth 64 := by
  rw [Spec.Rc2.scheduleAt, Proof.Rc2.getD_ofFn _ _ hidx, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
    Offset.add_add]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.truncate_eq_setWidth]
  by_cases h8 : i < 8
  · simp [h8, show i < 16 by omega, hi]
  · by_cases h16 : i < 16
    · simp [h8, h16, hi, BitVec.getLsbD_of_ge (m (T + BitVec.ofNat 64 (2 * idx))) i (by omega),
        show i - 8 < 16 by omega, show i - 8 < 64 by omega]
    · simp [h16, BitVec.getLsbD_of_ge (m (T + BitVec.ofNat 64 (2 * idx))) i (by omega),
        BitVec.getLsbD_of_ge (m (T + BitVec.ofNat 64 (2 * idx + 1))) (i - 8) (by omega)]

/-- The scan of the schedule at `r3`. -/
theorem keyLookup_run (s : State) {T : Addr} (hT : s.gpr .r3 = T) {idx : Nat} (hidx : idx < 64)
    (hq : s.gpr .r10 = BitVec.ofNat 64 (2 * idx))
    (hr : ∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 o) n) :
    WP isa keyLookup s fun t =>
      t.gpr .r11 = ((Spec.Rc2.scheduleAt s.mem T).getD idx 0).setWidth 64 ∧
      Keep [.r0, .r11, .r12, .r5] s t ∧ t.mem = s.mem := by
  have h2 : (BitVec.ofNat 64 (2 * idx)).toNat = 2 * idx := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (WP.keep [.r0, .r11, .r12, .r5] (keyScan_run s hT (by rw [hq, h2]; omega) (by rw [hq, h2]; omega)
    (fun i hi => chunks_in hr (by omega))) (by decide) rfl) fun t ⟨⟨t11, tm⟩, tk⟩ => ⟨?_, tk, tm⟩
  rw [t11, hq, entry_word _ _ hidx]

end VG.Proof.Rc2.PPC64LE
