module

public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X448 on AArch64: initializing coefficient arrays

Zeroing a bounded range of words preserves all other memory and the registers.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem store_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) (hd8 : d % 8 = 0) (r : Reg) :
    WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ Keeps [] s t := by
  have enc : d % 8 = 0 ∧ d < 32768 := ⟨hd8, by omega⟩
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    enc, and_self, hs.x3, State.store, State.read, BitVec.setWidth_eq,
    hs.write hd, ite_true, Option.bind_some, write8_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl⟩

theorem zeroX4_ok (s : State) :
    WP isa (.block [.movz .x .x4 0 0]) s fun t =>
      t.gpr .x4 = 0 ∧ t.mem = s.mem ∧ Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem fill_ok {s : State} {base : Addr} (hs : Scr s base) {o n : Nat} (ho : o + 8 * n ≤ 8192) (ho8 : o % 8 = 0)
    (hz : s.gpr .x4 = 0) :
    WP isa (.block ((List.range n).map (fun i => st .x4 (o + 8 * i)))) s fun t =>
      (∀ i < n, limbs t.mem base o i = 0) ∧ Outside base o (8 * n) s.mem t.mem ∧ Keeps [] s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, limbs t.mem base o i = 0) ∧ Outside base o (8 * n) s.mem t.mem ∧ Keeps [] s t
  have step : ∀ k t, k < n → inv k t →
      WP isa (.block [st .x4 (o + 8 * k)]) t (inv (k + 1)) := by
    intro k t hk ⟨tf, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (store_ok ts (by omega) (by omega) .x4) fun u ⟨um, uk⟩ => ?_
    rw [tk.1 .x4 (by decide), hz] at um
    have out : Outside base (o + 8 * k) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (o + 8 * i)).toNat = _
    rw [um, word_write t.mem base (by omega) (by omega)]
    by_cases h : i = k
    · rw [ite_eq_left h]; rfl
    · rw [ite_eq_right h]; exact tf i (by omega)
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) (N := n) inv step n (by omega) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64
