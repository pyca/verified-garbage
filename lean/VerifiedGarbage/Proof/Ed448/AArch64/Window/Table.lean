module

import VerifiedGarbage.Proof.Curve448.AArch64.Fast.MOp
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Select
public import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Dbl
import VerifiedGarbage.Proof.X448.AArch64.Fast.Weave
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.X448.BaseAdd
public import VerifiedGarbage.Impl.X448.AArch64.Common
public import VerifiedGarbage.Proof.Framework.AArch64.Footprint

/-! ### `Ed448.AArch64.Window.Store`, which only this module used -/

section

/-!
# Ed448 verification on AArch64: storing a table entry

Untrusted: everything here is checked by Lean. `tabStore`, for `x19 = e < 16`,
points `x8` at `base + 192 e` and copies the 24 words of slots 3–5 to entry
`e` of the table at `TAB` (`tabStore_ok`): only those 192 bytes change.
-/

@[expose] public section

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

/-- Where word `w` of slots 3–5 is. -/
def src (w : Nat) : Nat := slot (3 + w / 8) + 8 * (w % 8)

theorem src_bounds {w : Nat} (hw : w < 24) : 448 ≤ src w ∧ src w + 8 ≤ 832 ∧ src w % 8 = 0 := by
  simp only [src, slot]; omega_using [hw]

theorem tabStore_eq : tabStore =
    ([.lsl .x .x8 .x19 7, .lsl .x .x9 .x19 6, .add .x .x8 .x8 .x9, .add .x .x8 .x8 .x3] : List Instr) ++
    (List.range 24).flatMap fun w => [ld .x4 (src w), .str .x .x4 .x8 (TAB + 8 * w)] := rfl

/-- **Slots 3–5 to entry `e`** of the table. -/
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
    refine WP.mono (ih (by omega_using [hk])) fun t ⟨t1, t2, kt⟩ => ?_
    have ht : Scr t base := hsa.of_keeps kt (by decide)
    obtain ⟨s1, s2, s3⟩ := src_bounds (show k < 24 by omega_using [hk])
    rw [show ([ld .x4 (src k), .str .x .x4 .x8 (TAB + 8 * k)] : List Instr) =
      [ld .x4 (src k)] ++ [.str .x .x4 .x8 (TAB + 8 * k)] from rfl, WP.block_append_iff]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.ld_ok ht .x4 s3 (by omega_using [s2])) fun u ⟨u4, mu, ku⟩ => ?_
    have hsu : Scr u base := ht.of_keeps ku (by decide)
    have u8 : u.gpr .x8 = off base (192 * e) := by rw [ku.1 _ (by decide), kt.1 _ (by decide), a8]
    refine WP.mono (strAt_ok hsu u8 (d := TAB + 8 * k) (by simp only [TAB]; omega_using [he, hk]) (by simp only [TAB]; omega_using [])
      (by simp only [TAB]; omega_using [hk]) .x4) fun v ⟨mv, kv⟩ => ⟨fun w hw => ?_, ?_, ?_⟩
    · have hsrc : word t.mem base (src k) = word s.mem base (src k) := by
        rw [t2.word (Or.inl (by simp only [TAB]; omega_using [s2])) (by omega_using [s2])]
      rw [mv, VG.Proof.X448.AArch64.word_write_aligned _ _ (by simp only [TAB]; omega_using [he, hk])
        (by simp only [TAB]; omega_using [he, hk, hw]) (by simp only [TAB]; omega_using []) (by simp only [TAB]; omega_using []), u4, mu]
      by_cases hwk : w = k
      · subst hwk; rw [ite_eq_left (by omega_using []), hsrc]
      · rw [ite_eq_right (by omega_using [hwk])]; exact t1 w (by omega_using [hw, hwk])
    · rw [mv, mu]
      exact t2.trans ((VG.Proof.X448.AArch64.writeW_outside _ _ _ (by simp only [TAB]; omega_using [he, hk])).mono
        (by omega_using []) (by omega_using [hk]))
    · exact (kt.trans (ku.mono (by decide))).trans (kv.mono (by decide))

end VG.Proof.Ed448.AArch64.Window

end

end


/-!
# Ed448 verification on AArch64: the table of `[n](-A)`

Untrusted: everything here is checked by Lean. Entry `e` of the table as a
point (`TPt`) and its words' bounds (`TBnd`); a store of slots 3–5 to an
entry (`tabStore_pt`, `tabStore_bnd`), which keeps the other entries
(`TPt_outside`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same block_codeOf)
open VG.Impl.X448.AArch64.Fast (codeOf)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt genEnv genPt temps addOps_ok zero_env next_ok)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

/-! ## The entries -/

/-- Entry `e` of the table, as a point. -/
def TPt (m : Mem) (base : Addr) (e : Nat) : Point :=
  ⟨FV m base (TAB + 192 * e), FV m base (TAB + 192 * e + 64), FV m base (TAB + 192 * e + 128)⟩

/-- Entry `e`'s words below `Ib`. -/
def TBnd (m : Mem) (base : Addr) (e : Nat) : Prop := ∀ w < 24, (tw m base e w).toNat < Ib

/-- Coordinate `c` of entry `e` from the words `8c`, …, `8c + 7` of the entry. -/
theorem FV_entry (m m' : Mem) (base : Addr) {e c o : Nat} (ho : o = TAB + 192 * e + 64 * c)
    {o' : Nat} (h : ∀ i < 8, tw m base e (8 * c + i) = word m' base (o' + 8 * i)) :
    FV m base o = FV m' base o' := by
  simp only [VG.Proof.X448.AArch64.Weak.F]
  refine congrArg _ (VG.Proof.X448.Wide.valN_congr fun i hi => ?_)
  simp only [limbs]
  rw [← h i hi, tw]
  congr 2
  omega_arith

/-- After `tabStore` from slots 3–5 of `s`, entry `e` is their point, with their bounds. -/
theorem tabStore_pt {s t : State} {base : Addr} {e : Nat}
    (h : ∀ w < 24, word t.mem base (TAB + 192 * e + 8 * w) = word s.mem base (src w)) :
    TPt t.mem base e = pt (EV s.mem base) 3 4 5 := by
  have hs : ∀ c < 3, ∀ i < 8, tw t.mem base e (8 * c + i) = word s.mem base (slot (3 + c) + 8 * i) :=
    fun c hc i hi => by
      rw [tw, h _ (by omega_arith), src]
      congr 2
      all_goals (try simp only [slot])
      all_goals omega_arith
  simp only [TPt, pt]
  refine Point.mk.injEq _ _ _ _ _ _ |>.mpr ⟨?_, ?_, ?_⟩
  · exact FV_entry _ _ _ (e := e) (c := 0) (o := TAB + 192 * e) (by omega_arith) (hs 0 (by decide))
  · exact FV_entry _ _ _ (e := e) (c := 1) rfl (hs 1 (by decide))
  · exact FV_entry _ _ _ (e := e) (c := 2) rfl (hs 2 (by decide))

theorem tabStore_bnd {s t : State} {base : Addr} {e : Nat} (hb : BEnv s.mem base)
    (h : ∀ w < 24, word t.mem base (TAB + 192 * e + 8 * w) = word s.mem base (src w)) : TBnd t.mem base e := by
  intro w hw
  rw [tw, h w hw]
  have := hb ⟨3 + w / 8, by omega_arith⟩ (w % 8) (Nat.mod_lt _ (by decide))
  exact this

/-- Entries other than `e` are kept by a store to entry `e`. -/
theorem tw_outside {m m' : Mem} {base : Addr} {e : Nat} (h : Outside base (TAB + 192 * e) 192 m m')
    {e' w : Nat} (he : e' ≠ e) (he' : e' < 16) (hw : w < 24) :
    tw m' base e' w = tw m base e' w := by
  unfold tw
  refine h.word ?_ (by simp only [TAB]; omega_arith)
  rcases Nat.lt_or_gt_of_ne he with h1 | h1 <;> [left; right] <;> omega_arith

/-- An entry is its words. -/
theorem TPt_of_tw {m m' : Mem} {base : Addr} {e : Nat} (h : ∀ w < 24, tw m' base e w = tw m base e w) :
    TPt m' base e = TPt m base e := by
  have hc : ∀ c < 3, ∀ i < 8, tw m' base e (8 * c + i) = word m base (TAB + 192 * e + 64 * c + 8 * i) :=
    fun c hc i hi => by
      rw [h _ (by omega_arith)]
      unfold tw
      rw [show TAB + 192 * e + 8 * (8 * c + i) = TAB + 192 * e + 64 * c + 8 * i by omega_arith]
  unfold TPt
  rw [FV_entry m' m base (e := e) (c := 0) (o := TAB + 192 * e) (o' := TAB + 192 * e) (by omega_arith)
      (fun i hi => by rw [hc 0 (by decide) i hi, show TAB + 192 * e + 64 * 0 = TAB + 192 * e by omega_arith]),
    FV_entry m' m base (e := e) (c := 1) (o' := TAB + 192 * e + 64) rfl (fun i hi => hc 1 (by decide) i hi),
    FV_entry m' m base (e := e) (c := 2) (o' := TAB + 192 * e + 128) rfl (fun i hi => hc 2 (by decide) i hi)]

theorem TPt_outside {m m' : Mem} {base : Addr} {e : Nat} (h : Outside base (TAB + 192 * e) 192 m m')
    {e' : Nat} (he : e' ≠ e) (he' : e' < 16) : TPt m' base e' = TPt m base e' :=
  TPt_of_tw fun _ hw => tw_outside h he he' hw

end VG.Proof.Ed448.AArch64.Window
