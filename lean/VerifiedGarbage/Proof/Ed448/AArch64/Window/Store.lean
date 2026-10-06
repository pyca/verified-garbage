import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.MOp
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow

/-!
# Ed448 verification on AArch64: storing a table entry

Untrusted: everything here is checked by Lean. `tabStore`, for `x19 = e < 16`,
points `x8` at `base + 192 e` and copies the 24 words of slots 0–2 to entry
`e` of the table at `TAB` (`tabStore_ok`): only those 192 bytes change.
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot)
open VG.Proof.X448.AArch64 (Scr Keeps off word Outside)

theorem off_add' (base : Addr) (d e : Nat) : off base d + BitVec.ofNat 64 e = off base (d + e) := by
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- A store of `r` at `x8 + d`, for `x8` pointing at byte `p` of the working space. -/
theorem strAt_ok {s : State} {base : Addr} (hs : Scr s base) {p d : Nat} (hp : s.gpr .x8 = off base p)
    (hd : p + d + 8 ≤ 8192) (hd8 : d % 8 = 0) (hd' : d < 32768) (r : Reg) :
    WP isa (.block [.str .x r .x8 d]) s fun t =>
      t.mem = s.mem.writeW (off base (p + d)) (s.gpr r) ∧ Keeps [] s t := by
  have enc : d % 8 = 0 ∧ d < 32768 := ⟨hd8, hd'⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    enc, and_self, hp, off_add', State.store, State.read, BitVec.setWidth_eq,
    hs.write hd, ite_true, Option.bind_some, VG.Proof.X448.AArch64.write8_eq, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl⟩

private theorem addr_fact : ∀ e < 16,
    (BitVec.ofNat 64 e <<< 7) + (BitVec.ofNat 64 e <<< 6) = BitVec.ofNat 64 (192 * e) := by
  decide +kernel

/-- `x8 = base + 192 e`. -/
theorem tabAddr_ok {s : State} {base : Addr} (hs : Scr s base) {e : Nat} (he : e < 16)
    (hc : s.gpr .x19 = BitVec.ofNat 64 e) :
    WP isa (.block ([.lsl .x .x8 .x19 7, .lsl .x .x9 .x19 6, .add .x .x8 .x8 .x9, .add .x .x8 .x8 .x3] :
        List Instr)) s fun t =>
      t.gpr .x8 = off base (192 * e) ∧ Keeps [.x8, .x9] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (7 : Nat) < 64 from by decide, show (6 : Nat) < 64 from by decide, ite_true,
    RegUpd.gpr_write, BitVec.setWidth_eq, hc, hs.x3, ite_false, reduceCtorEq, addr_fact e he,
    Option.some.injEq, exists_eq_left']
  refine ⟨BitVec.add_comm _ _, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- Where word `w` of slots 0–2 is. -/
def src (w : Nat) : Nat := slot (w / 8) + 8 * (w % 8)

theorem src_bounds {w : Nat} (hw : w < 24) : 64 ≤ src w ∧ src w + 8 ≤ 448 ∧ src w % 8 = 0 := by
  simp only [src, slot]; omega

theorem tabStore_eq : tabStore =
    ([.lsl .x .x8 .x19 7, .lsl .x .x9 .x19 6, .add .x .x8 .x8 .x9, .add .x .x8 .x8 .x3] : List Instr) ++
    (List.range 24).flatMap fun w => [ld .x4 (src w), .str .x .x4 .x8 (TAB + 8 * w)] := rfl

/-- **Slots 0–2 to entry `e`** of the table. -/
theorem tabStore_ok {s : State} {base : Addr} (hs : Scr s base) {e : Nat} (he : e < 16)
    (hc : s.gpr .x19 = BitVec.ofNat 64 e) :
    WP isa (.block tabStore) s fun t =>
      (∀ w < 24, word t.mem base (TAB + 192 * e + 8 * w) = word s.mem base (src w)) ∧
      Outside base (TAB + 192 * e) 192 s.mem t.mem ∧ Keeps [.x8, .x9, .x4] s t := by
  rw [tabStore_eq, WP.block_append_iff]
  refine WP.mono (tabAddr_ok hs he hc) fun a ⟨a8, ka, ma⟩ => ?_
  have hsa : Scr a base := hs.of_keeps ka (by decide)
  suffices h : ∀ k ≤ 24, WP isa (.block ((List.range k).flatMap fun w =>
      [ld .x4 (src w), .str .x .x4 .x8 (TAB + 8 * w)])) a fun t =>
      (∀ w < k, word t.mem base (TAB + 192 * e + 8 * w) = word s.mem base (src w)) ∧
      Outside base (TAB + 192 * e) 192 s.mem t.mem ∧ Keeps [.x4] a t from
    WP.mono (h 24 (Nat.le_refl _)) fun t ⟨t1, t2, t3⟩ =>
      ⟨t1, t2, (ka.mono (by decide)).trans (t3.mono (by decide))⟩
  intro k hk
  induction k with
  | zero => exact WP.block_nil ⟨fun w hw => absurd hw (Nat.not_lt_zero _),
      by rw [ma]; exact Outside.refl _ _ _ _, Keeps.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨t1, t2, kt⟩ => ?_
    have ht : Scr t base := hsa.of_keeps kt (by decide)
    obtain ⟨s1, s2, s3⟩ := src_bounds (show k < 24 by omega)
    rw [show ([ld .x4 (src k), .str .x .x4 .x8 (TAB + 8 * k)] : List Instr) =
      [ld .x4 (src k)] ++ [.str .x .x4 .x8 (TAB + 8 * k)] from rfl, WP.block_append_iff]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.ld_ok ht .x4 s3 (by omega)) fun u ⟨u4, mu, ku⟩ => ?_
    have hsu : Scr u base := ht.of_keeps ku (by decide)
    have u8 : u.gpr .x8 = off base (192 * e) := by rw [ku.1 _ (by decide), kt.1 _ (by decide), a8]
    refine WP.mono (strAt_ok hsu u8 (d := TAB + 8 * k) (by simp only [TAB]; omega) (by simp only [TAB]; omega)
      (by simp only [TAB]; omega) .x4) fun v ⟨mv, kv⟩ => ⟨fun w hw => ?_, ?_, ?_⟩
    · have hsrc : word t.mem base (src k) = word s.mem base (src k) := by
        rw [t2.word (Or.inl (by simp only [TAB]; omega)) (by omega)]
      rw [mv, VG.Proof.X448.AArch64.word_write_aligned _ _ (by simp only [TAB]; omega)
        (by simp only [TAB]; omega) (by simp only [TAB]; omega) (by simp only [TAB]; omega), u4, mu]
      by_cases hwk : w = k
      · subst hwk; rw [ite_eq_left (by omega), hsrc]
      · rw [ite_eq_right (by omega)]; exact t1 w (by omega)
    · rw [mv, mu]
      exact t2.trans ((VG.Proof.X448.AArch64.writeW_outside _ _ _ (by simp only [TAB]; omega)).mono
        (by omega) (by omega))
    · exact (kt.trans (ku.mono (by decide))).trans (kv.mono (by decide))

end VG.Proof.Ed448.AArch64.Window
