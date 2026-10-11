import VerifiedGarbage.Proof.Ed448.AArch64.Point56.AsFn
import VerifiedGarbage.Proof.X448.AArch64.Base.Step
import VerifiedGarbage.Proof.X448.AArch64.Base.Setup
import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.Framework.AArch64.StoreFrame
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.Ed448.AArch64.CombBase
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Conv
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.X448.AArch64.Base.Comb
import VerifiedGarbage.Proof.X448.AArch64.Base.Erase
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Ed448's fixed-base comb on AArch64, as a function

Untrusted: everything here is checked by Lean. One module, so that few others import the AdvSIMD
products' algebra (`ci/check_lean_speed.py`).

* `combBaseFn_ok`: `vg_ed448_r56_comb_base` (`combBaseFn`) saves `x21`–`x28` in the upper halves
  of `v8`–`v15`, those at `CSAVE` (`stqs_ok`), and `x19` and the return address at `XSAVE`; sets
  both accumulators at `[G] B` for `n` (`init_ok`), which takes `StepInv` to step 0; runs the `n`
  steps (`loop_ok`), with `n` in `x30`; and loads the registers back (`ldqs_ok`). The steps store
  only to the slots up to 18 and the products' bytes but `CSAVE` (`loopStores`,
  `WP.storeFrame`), so the saved registers survive them.
* `call_ok`: a call of it (`CombBase.call n`), from what the comb needs (`CombPre`) and `Frame`,
  keeps `Frame` and leaves the comb's sums, as the inlined comb does. The call runs on the working
  space and the tables (`WP.callV`, with the function's own proof as its contract, `combK`), and
  the return address is kept in a lane of `v8`, whose low half the function restores.
* `combBaseFn_verified`: the function meets `combBaseContract` of `Spec/Ed448/Comb56.lean`, with
  no stack, under the calling convention with the comb's tables (`Abi.withConsts combConsts`).
  The bits the contract reads are those of the scalar `bitsAt` (`bits_of_isBits`); the comb's
  sums, `G + Σ_j d_{2j+1} 256^j` and `G + Σ_j d_{2j} 256^j`, are its odd and even nibbles' sums
  (`odd_eq`, `even_eq`); and the points the function leaves represent their multiples of `B`, as
  `pointMul` does (`pointMul_rep`), so they are `pointEqual` to them (`pointEqual_rep`). Constant
  time by taint tracking: only the pointer and `n` are public, every address is `ws` or the
  static plus a constant or the counter, and the branches are on `n` and the counter.
-/

/-! # The function -/

namespace VG.Proof.Ed448.AArch64.CombBase

open VG VG.AArch64 VG.Impl.Ed448.AArch64 VG.Impl.Ed448.AArch64.CombBase
open VG.Impl.X448.AArch64 (slot ACC BITS st ld)
open VG.Impl.X448.AArch64.Base (combSym AX AY AZ BX BY BZ limb)
open VG.Impl.Curve448.AArch64.Neon (V ldq stq)
open VG.Proof.Curve448.AArch64.Neon (exec_ldq exec_stq off_add st_outside read16_write setMem setMem_mem
  V_ne)
open VG.Proof.X448.AArch64 (Scr Keeps off limbs word Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd fclob)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt StepInv Bits TblAt)
open VG.Proof.X448 (combG oddSumZ evenSumZ)
open VG.Proof.Ed448 (Rep baseAff)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-! ## The saves -/

theorem stqs_ok {s : State} {base : Addr} (hs : Scr s base) {O : Nat} (hO : O % 16 = 0) (hO' : O + 128 ≤ 8192) :
    WP isa (.block ((List.range 8).map fun k => stq (8 + k) (O + 16 * k))) s fun t =>
      (∀ k < 8, t.mem.read (off base (O + 16 * k)) 16 = s.v (V (8 + k))) ∧
      Outside base O 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  have e : ((List.range 8).map fun k => stq (8 + k) (O + 16 * k)) =
      (List.range 8).flatMap fun k => [stq (8 + k) (O + 16 * k)] := rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, t.mem.read (off base (O + 16 * k)) 16 = s.v (V (8 + k))) ∧
    Outside base O 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv
    (fun n t hn ⟨tv, tO, tg, tvv, tr, tw, tsp⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl, rfl, rfl, rfl⟩)
    fun t ⟨tv, tO, tg, tvv, tr, tw, tsp⟩ => ⟨fun k hk => by rw [tv k hk], tO, tg, tvv, tr, tw, tsp⟩
  have ts : Scr t base := VG.Proof.Curve448.AArch64.Neon.scr_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_stq ts (8 + n) (d := O + 16 * n) (by omega) (by omega),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, tO.trans ((st_outside _ _ _ (by omega)).mono (by omega) (by omega)),
      tg, tvv, tr, tw, tsp⟩⟩
  simp only [setMem_mem]
  by_cases h : k = n
  · subst h; rw [read16_write, tvv]
  · rw [((st_outside t.mem base (t.v (V (8 + n))) (d := O + 16 * n) (by omega))).read16 (by omega)
      (by omega)]
    exact tv k (by omega)

theorem ldqs_ok {s : State} {base : Addr} (hs : Scr s base) {O : Nat} (hO : O % 16 = 0) (hO' : O + 128 ≤ 8192) :
    WP isa (.block ((List.range 8).map fun k => ldq (8 + k) (O + 16 * k))) s fun t =>
      (∀ k < 8, t.v (V (8 + k)) = s.mem.read (off base (O + 16 * k)) 16) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have e : ((List.range 8).map fun k => ldq (8 + k) (O + 16 * k)) =
      (List.range 8).flatMap fun k => [ldq (8 + k) (O + 16 * k)] := rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, t.v (V (8 + k)) = s.mem.read (off base (O + 16 * k)) 16) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tg, tr, tw, tsp⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl, rfl⟩
  have ts : Scr t base := VG.Proof.Curve448.AArch64.Neon.scr_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq ts (8 + n) (d := O + 16 * n) (by omega) (by omega),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, by rw [RegUpd.mem_setV, tm], by rw [RegUpd.gpr_setV, tg],
      by rw [RegUpd.rd_setV, tr], by rw [RegUpd.wr_setV, tw], by rw [RegUpd.sp_setV, tsp]⟩⟩
  by_cases h : k = n
  · subst h; rw [RegUpd.v_setV_self, tm]
  · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) (by omega))]
    exact tv k (by omega)


/-- The lanes the function keeps `x21`–`x28` in. -/
abbrev cks : List (Reg × VReg × Nat) :=
  [(.x21, .v8, 1), (.x22, .v9, 1), (.x23, .v10, 1), (.x24, .v11, 1), (.x25, .v12, 1), (.x26, .v13, 1),
    (.x27, .v14, 1), (.x28, .v15, 1)]

theorem save_eq : save = ((([.addImm .x .x3 .x0 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] :
    List Instr) ++ insOf cks) ++ (List.range 8).map (fun k => stq (8 + k) (CSAVE + 16 * k))) ++
    (([st .x19 XSAVE] : List Instr) ++ (([st .x30 (XSAVE + 8)] : List Instr) ++
      ([.addImm .x .x30 .x1 0] : List Instr))) := rfl

theorem restore_eq : restore ++ ([ld .x19 XSAVE, ld .x30 (XSAVE + 8)] : List Instr) =
    ((List.range 8).map (fun k => ldq (8 + k) (CSAVE + 16 * k)) ++ umovOf cks) ++
      (([ld .x19 XSAVE] : List Instr) ++ ([ld .x30 (XSAVE + 8)] : List Instr)) := rfl

theorem preservedV_V : ∀ r ∈ preservedV, ∃ k < 8, r = V (8 + k) := by decide

/-- `x30 := x1`. -/
theorem mov30_ok (s : State) :
    WP isa (.block [.addImm .x .x30 .x1 0]) s fun t =>
      t.gpr .x30 = s.gpr .x1 ∧ t.mem = s.mem ∧ Keeps [.x30] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq,
    BitVec.add_zero, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩

/-- `x9 = n - 56`: nonzero exactly for 57. -/
theorem sub56_ok (s : State) {n : Nat} (hn : n = 56 ∨ n = 57) (h : s.gpr .x30 = BitVec.ofNat 64 n) :
    WP isa (.block [.subImm .x .x9 .x30 56]) s fun t =>
      (t.gpr .x9 != 0) = decide (n = 57) ∧ t.mem = s.mem ∧ Keeps [.x9] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (56 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, h,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩
  rcases hn with rfl | rfl <;> decide

theorem WP.ite_of {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop} {b : Bool}
    (hc : isa.eval c s = some b) (ht : b = true → WP isa th s Q) (he : b = false → WP isa el s Q) :
    WP isa (.ite c th el) s Q := by
  cases b
  · obtain ⟨t, s', e, q⟩ := he rfl; exact ⟨_, _, Exec.iteF hc e, q⟩
  · obtain ⟨t, s', e, q⟩ := ht rfl; exact ⟨_, _, Exec.iteT hc e, q⟩

/-- `[G] B` for `n` tables. -/
def gOf (n : Nat) : Spec.X448.Fe × Spec.X448.Fe := if n = 57 then Impl.X448.baseG57 else Impl.X448.baseG

theorem gOf_ok {n : Nat} (hn : n = 56 ∨ n = 57) :
    Rep (VG.Proof.X448.basePt (gOf n)) (((combG n : ℤ) + 0) • baseAff) := by
  rcases hn with rfl | rfl
  · rw [show gOf 56 = Impl.X448.baseG from rfl, VG.Proof.X448.combG_56, add_zero, natCast_zsmul]
    exact VG.Proof.X448.baseG_ok
  · rw [show gOf 57 = Impl.X448.baseG57 from rfl, VG.Proof.X448.combG_57, add_zero, natCast_zsmul]
    exact VG.Proof.X448.baseG57_ok

/-- Both accumulators at `[G] B` for `n = x30`, and the counter at 0. -/
theorem init_ok {s : State} {base : Addr} {n : Nat} (hs : Scr s base) (hn : n = 56 ∨ n = 57)
    (h30 : s.gpr .x30 = BitVec.ofNat 64 n) :
    WP isa init s fun t =>
      (∀ w < 8, word t.mem base (AX + 8 * w) = limb (gOf n).1 w ∧
        word t.mem base (AY + 8 * w) = limb (gOf n).2 w ∧ word t.mem base (AZ + 8 * w) = limb 1 w ∧
        word t.mem base (BX + 8 * w) = limb (gOf n).1 w ∧
        word t.mem base (BY + 8 * w) = limb (gOf n).2 w ∧ word t.mem base (BZ + 8 * w) = limb 1 w) ∧
      Outside base 64 768 s.mem t.mem ∧ Keeps [.x9, .x4, .x19] s t ∧ t.gpr .x19 = 0 := by
  unfold init
  refine WP.seq (WP.mono (sub56_ok s hn h30) fun t1 ⟨z1, m1, k1⟩ => ?_)
  have hs1 := hs.of_keeps k1 (by decide)
  refine WP.ite_of (b := decide (n = 57)) (by simp only [eval, State.read, BitVec.setWidth_eq, z1]) ?_ ?_
  · intro hb
    have e : gOf n = Impl.X448.baseG57 := by simp only [decide_eq_true_eq] at hb; simp [gOf, hb]
    refine WP.mono (VG.Proof.X448.AArch64.Base.consts_ok hs1 _) fun t ⟨tv, tOut, kt, tc⟩ =>
      ⟨by rw [e]; exact tv, by rw [← m1]; exact tOut, (k1.then kt).mono (by decide), tc⟩
  · intro hb
    have e : gOf n = Impl.X448.baseG := by
      simp only [decide_eq_false_iff_not] at hb; simp [gOf, hb]
    refine WP.mono (VG.Proof.X448.AArch64.Base.consts_ok hs1 _) fun t ⟨tv, tOut, kt, tc⟩ =>
      ⟨by rw [e]; exact tv, by rw [← m1]; exact tOut, (k1.then kt).mono (by decide), tc⟩

/-! ## The steps' stores -/

/-- Where the accumulators' setting and the steps store: the slots up to 18, and the products'
bytes but `CSAVE`. -/
def loopOk (d : Nat) : Bool :=
  (64 ≤ d && d + 8 ≤ 2496) || (3584 ≤ d && d + 8 ≤ 3968) || (4096 ≤ d && d + 8 ≤ 4736)

theorem loopStores :
    ∀ i ∈ instrs (.seq init (.loop Impl.X448.AArch64.Base.stepR (.nonzero .x .x9)) : Prog isa),
      storesAt loopOk i = true := by
  rw [← List.all_eq_true, ← Code.allInstrs_eq]; decide +kernel

/-- The bytes the function saves registers at are in no store of the steps. -/
theorem save_unstored (base : Addr) {i : Nat}
    (hi : CSAVE ≤ i ∧ i < CSAVE + 128 ∨ XSAVE ≤ i ∧ i < XSAVE + 16) :
    Unstored loopOk base (off base i) := by
  intro d hd hlt
  simp only [loopOk, CSAVE, XSAVE, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd hi
  rw [off, Offset.add_sub_add_left] at hlt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hlt
  omega

theorem cks_V : ∀ k < 8, (cks.getD k (.x21, .v8, 1)).2.1 = V (8 + k) ∧
    (cks.getD k (.x21, .v8, 1)).1 = Impl.X448.AArch64.Fast.saved k ∧
    (cks.getD k (.x21, .v8, 1)).2.2 = 1 ∧ (cks.getD k (.x21, .v8, 1)) ∈ cks := by
  decide

/-! ## The function -/

/-- What the function needs: `ws` (`base`) in `x0`, `n` in `x1`, the working space writable, every
slot's limbs below `Ib`, slot 19 zero, the bits of `k` at `BITS`, and the tables. -/
structure CombIn (n : Nat) (base : Addr) (k : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = base
  x1 : s.gpr .x1 = BitVec.ofNat 64 n
  hn : n = 56 ∨ n = 57
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 8192 ≤ 2 ^ 64
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  bits : Bits n base k s.mem
  tbl : TblAt s base (s.syms combSym)

/-- What the saves leave. -/
structure Saved (n : Nat) (base : Addr) (s t : State) : Prop where
  scr : Scr t base
  x30 : t.gpr .x30 = BitVec.ofNat 64 n
  regs : ∀ r, r ≠ .x3 → r ≠ .x12 → r ≠ .x30 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside2 base XSAVE 16 CSAVE 128 s.mem t.mem
  x19s : word t.mem base XSAVE = s.gpr .x19
  x30s : word t.mem base (XSAVE + 8) = s.gpr .x30
  lane1 : ∀ k < 8, (t.mem.read (off base (CSAVE + 16 * k)) 16).extractLsb' 64 64 =
    s.gpr (Impl.X448.AArch64.Fast.saved k)
  lane0 : ∀ k < 8, (t.mem.read (off base (CSAVE + 16 * k)) 16).extractLsb' 0 64 =
    (s.v (V (8 + k))).extractLsb' 0 64

theorem save_ok {n k : Nat} {base : Addr} {s : State} (h : CombIn n base k s) :
    WP isa (.block save) s (Saved n base s) := by
  have hnw := h.nowrap
  rw [save_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Point56.regs_ok s) fun s₀ ⟨g3, g12, gk, gm, gr, gw, gsp, gv⟩ => ?_
  refine WP.mono (insOf_ok cks s₀ (by decide) (by decide)) fun s₁ ⟨hg, hm, hr, hw, hsp, hls, hlo⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨by rw [hg, g3, h.x0], by rw [hg, g12], by rw [hw, gw]; exact h.wr, hnw⟩
  refine WP.mono (stqs_ok hs₁ (O := CSAVE) (by decide) (by decide)) fun s₂ ⟨sv₂, o₂, g₂, v₂, r₂, w₂, sp₂⟩ => ?_
  have hs₂ : Scr s₂ base := VG.Proof.Curve448.AArch64.Neon.scr_of hs₁ g₂ w₂
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.store_ok hs₂ (d := XSAVE) (by decide) (by decide) .x19)
    fun s₃ ⟨m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.store_ok hs₃ (d := XSAVE + 8) (by decide) (by decide) .x30)
    fun s₄ ⟨m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (mov30_ok s₄) fun s₅ ⟨g20, m₅, k₅⟩ => ?_
  have gs : ∀ r, r ≠ .x3 → r ≠ .x12 → s₂.gpr r = s.gpr r := fun r h3 h12 => by rw [g₂, hg, gk r h3 h12]
  have g34 : ∀ r, s₄.gpr r = s₂.gpr r := fun r => by rw [k₄.1 r (by simp), k₃.1 r (by simp)]
  have w4 : ∀ x, (ofs base x < XSAVE ∨ XSAVE + 16 ≤ ofs base x) → s₄.mem x = s₂.mem x := fun x hx => by
    rw [m₄, VG.Proof.X448.AArch64.writeW_outside _ _ _ (by decide) x (by simp only [XSAVE] at hx ⊢; omega), m₃,
      VG.Proof.X448.AArch64.writeW_outside _ _ _ (by decide) x (by simp only [XSAVE] at hx ⊢; omega)]
  have csv : ∀ k < 8, s₅.mem.read (off base (CSAVE + 16 * k)) 16 = s₁.v (V (8 + k)) := fun k hk => by
    rw [← sv₂ k hk, m₅]
    exact Mem.read_congr fun i hi => by
      rw [off_add]
      exact w4 _ (by
        rw [VG.Proof.X448.AArch64.Base.ofs_off0 base (by simp only [CSAVE]; omega)]; simp only [CSAVE, XSAVE]; omega)
  have x19w : word s₄.mem base XSAVE = s₂.gpr .x19 := by
    rw [m₄, VG.Proof.X448.AArch64.Base.word_store (d := XSAVE + 8) (e := XSAVE) (by decide) (by decide)
      (by decide) (by decide) _ (by decide), m₃, VG.Proof.X448.AArch64.Base.word_store_self (by decide) (by decide)]
  have x20w : word s₄.mem base (XSAVE + 8) = s₂.gpr .x30 := by
    rw [m₄, VG.Proof.X448.AArch64.Base.word_store_self (by decide) (by decide), k₃.1 _ (by simp)]
  refine ⟨hs₄.of_keeps k₅ (by decide), ?_, fun r h3 h12 h20 => ?_, ?_, ?_, fun x h1 h2 => ?_,
    by rw [m₅, x19w, gs _ (by decide) (by decide)], by rw [m₅, x20w, gs _ (by decide) (by decide)],
    fun k hk => ?_, fun k hk => ?_⟩
  · rw [g20, g34, gs _ (by decide) (by decide), h.x1]
  · rw [k₅.1 r (by simpa using h20), g34, gs r h3 h12]
  · rw [k₅.2.1, k₄.2.1, k₃.2.1, r₂, hr, gr]
  · rw [k₅.2.2, k₄.2.2, k₃.2.2, w₂, hw, gw]
  · rw [m₅, w4 x h1, o₂ x h2, hm, gm]
  · obtain ⟨hv, hs', hl, hm'⟩ := cks_V k hk
    have n3 := (show ∀ k < 8, Impl.X448.AArch64.Fast.saved k ≠ .x3 ∧ Impl.X448.AArch64.Fast.saved k ≠ .x12 by
      decide) k hk
    rw [csv k hk, ← gk _ n3.1 n3.2, ← hs', ← hls _ hm']
    simp only [laneOf, hv, hl]
  · rw [csv k hk]
    have h0 := hlo (V (8 + k)) 0 (by decide) (by revert k; decide)
    simp only [laneOf, Nat.mul_zero] at h0
    rw [h0, gv]

/-- What the function leaves, from `s`: every register outside `x1` and `fclob` restored, and
`x21`–`x28`, but `x3` (`ws`) and `x12` (the mask), the low halves of `v8`–`v15`, and the comb's
sums, `[G + Σ_j d_{2j+1} 256^j] B` in slots 0–2 and `[G + Σ_j d_{2j} 256^j] B` in slots 3–5. -/
structure CombOut (n : Nat) (base : Addr) (k : Nat) (s u : State) : Prop where
  regs : ∀ r, (r ∉ .x1 :: fclob ∨ r ∈ cks.map Prod.fst) → r ≠ .x3 → r ≠ .x12 → u.gpr r = s.gpr r
  x3 : u.gpr .x3 = base
  mask : u.gpr .x12 = 0x0fffffff
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  env : BEnv u.mem base
  zero : ∀ w < 8, limbs u.mem base (slot (19 : Index).val) w = 0
  mem : Outside2 base 64 2816 ACC 1152 s.mem u.mem
  odd : Rep (pt (EV u.mem base) 0 1 2) (((combG n : ℤ) + oddSumZ k n) • baseAff)
  even : Rep (pt (EV u.mem base) 3 4 5) (((combG n : ℤ) + evenSumZ k n) • baseAff)

/-- **The comb, as a function**. -/
theorem combBaseFn_ok {n k : Nat} {base : Addr} {s : State} (h : CombIn n base k s) :
    WP isa combBaseFn s (CombOut n base k s) := by
  have hn57 : n ≤ 57 := by rcases h.hn with rfl | rfl <;> decide
  have hnw := h.nowrap
  unfold combBaseFn
  refine WP.seq (WP.mono_syms (save_ok h) fun s₅ hS sy5 => ?_)
  have hs₅ := hS.scr
  -- The memory after the saves.
  have wS : ∀ {d : Nat}, d + 8 ≤ XSAVE → word s₅.mem base d = word s.mem base d := fun hd =>
    hS.mem.word (Or.inl hd) (Or.inl (by simp only [XSAVE, CSAVE] at hd ⊢; omega))
      (by simp only [XSAVE] at hd; omega)
  have bS : BEnv s₅.mem base := fun i j hj => by
    have := i.isLt
    show (word s₅.mem base (slot i.val + 8 * j)).toNat < Ib
    rw [wS (by simp only [slot, XSAVE]; omega)]; exact h.env i j hj
  have zS : ∀ w < 8, limbs s₅.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    show (word s₅.mem base (slot (19 : Index).val + 8 * w)).toNat = 0
    rw [wS (by simp only [slot, XSAVE]; omega)]; exact h.zero w hw
  have bitsS : Bits n base k s₅.mem := fun q hq => by
    have e := VG.Proof.X448.AArch64.Base.ofs_off0 base (d := BITS + q) (by simp only [BITS]; omega)
    rw [hS.mem _ (by rw [e]; simp only [BITS, XSAVE]; omega) (by rw [e]; simp only [BITS, CSAVE]; omega)]
    exact h.bits q hq
  have tblS : TblAt s₅ base (s₅.syms combSym) := by
    rw [sy5]
    exact h.tbl.of_far (by rw [hS.rd, hS.wr]) fun x hx =>
      hS.mem x (.inr (by simp only [XSAVE]; omega)) (.inr (by simp only [CSAVE]; omega))
  -- The accumulators' setting and the steps, which keep the saved registers.
  refine WP.assoc ?_
  refine WP.seq (WP.mono (WP.storeFrame (Q := StepInv n s₅ base k n) loopStores (WP.seq (WP.mono_syms (init_ok hs₅ h.hn hS.x30)
    fun t ⟨tv, tOut, kt, tc⟩ syt => ?_))) fun tL ⟨hL, x3L, fL⟩ => ?_)
  · have hst : Scr t base := hs₅.of_keeps kt (by decide)
    have ev : ∀ (i : Index) (v : Spec.X448.Fe), (∀ w < 8, word t.mem base (slot i.val + 8 * w) = limb v w) →
        EV t.mem base i = v := fun i v hv => VG.Proof.X448.AArch64.Base.F_of_words hv
    have pA : pt (EV t.mem base) 0 1 2 = VG.Proof.X448.basePt (gOf n) := by
      simp only [pt, VG.Proof.X448.basePt]
      rw [ev 0 _ fun w hw => (tv w hw).1, ev 1 _ fun w hw => (tv w hw).2.1, ev 2 _ fun w hw => (tv w hw).2.2.1]
    have pB : pt (EV t.mem base) 3 4 5 = VG.Proof.X448.basePt (gOf n) := by
      simp only [pt, VG.Proof.X448.basePt]
      rw [ev 3 _ fun w hw => (tv w hw).2.2.2.1, ev 4 _ fun w hw => (tv w hw).2.2.2.2.1,
        ev 5 _ fun w hw => (tv w hw).2.2.2.2.2]
    have wt : ∀ (i : Index), 6 ≤ i.val → ∀ w < 8, word t.mem base (slot i.val + 8 * w) =
        word s₅.mem base (slot i.val + 8 * w) := fun i hi w hw => by
      have := i.isLt
      exact tOut.word (Or.inr (by simp only [slot]; omega)) (by simp only [slot]; omega)
    have inv : StepInv n s₅ base k 0 t := by
      refine ⟨Nat.zero_le _, hst, fun i w hw => ?_, fun w hw => ?_, by rw [tc]; rfl, fun q hq => ?_,
        by rw [pA]; exact gOf_ok h.hn, by rw [pB]; exact gOf_ok h.hn, kt.1 _ (by decide), kt.1 _ (by decide),
        kt.2.1, kt.2.2, fun x h1 _ => tOut x (by omega),
        tblS.of_far (by rw [kt.2.1, kt.2.2]) fun x hx => tOut x (.inr (by omega)),
        fun r hr => kt.1 r (VG.Proof.X448.AArch64.Base.notin_keep (by decide) hr)⟩
      · by_cases hi : i.val < 6
        · have hi6 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
            rcases i with ⟨i, hlt⟩; simp only [Fin.ext_iff] at hi ⊢; omega
          rcases hi6 with rfl | rfl | rfl | rfl | rfl | rfl
          · exact VG.Proof.X448.AArch64.Base.bnd_of_words (fun w hw => (tv w hw).1) w hw
          · exact VG.Proof.X448.AArch64.Base.bnd_of_words (fun w hw => (tv w hw).2.1) w hw
          · exact VG.Proof.X448.AArch64.Base.bnd_of_words (fun w hw => (tv w hw).2.2.1) w hw
          · exact VG.Proof.X448.AArch64.Base.bnd_of_words (fun w hw => (tv w hw).2.2.2.1) w hw
          · exact VG.Proof.X448.AArch64.Base.bnd_of_words (fun w hw => (tv w hw).2.2.2.2.1) w hw
          · exact VG.Proof.X448.AArch64.Base.bnd_of_words (fun w hw => (tv w hw).2.2.2.2.2) w hw
        · show (word t.mem base (slot i.val + 8 * w)).toNat < Ib
          rw [wt i (by omega) w hw]; exact bS i w hw
      · show (word t.mem base (slot (19 : Index).val + 8 * w)).toNat = 0
        rw [wt 19 (by decide) w hw]; exact zS w hw
      · have e := VG.Proof.X448.AArch64.Base.ofs_off0 base (d := BITS + q) (by simp only [BITS]; omega)
        rw [tOut _ (by rw [e]; simp only [BITS]; omega)]
        exact bitsS q hq
    have := VG.Proof.X448.AArch64.Base.loop_ok hn57 hS.x30 n t (by rcases h.hn with rfl | rfl <;> decide)
      le_rfl (by rw [Nat.sub_self]; exact inv) (by rw [syt])
    exact this
  -- The registers loaded back.
  rw [hs₅.x3] at fL
  have hsL := hL.scr
  rw [restore_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldqs_ok hsL (O := CSAVE) (by decide) (by decide)) fun s₆ ⟨v₆, m₆, g₆, r₆, w₆, sp₆⟩ => ?_
  have hs₆ : Scr s₆ base := VG.Proof.Curve448.AArch64.Neon.scr_of hsL g₆ w₆
  refine WP.mono (WP.preservedV (umovOf_ok cks s₆ (by decide) (by decide)) (by lit_decide))
    fun s₇ ⟨⟨m₇, r₇, w₇, sp₇, l₇, o₇⟩, vv₇⟩ => ?_
  have hs₇ : Scr s₇ base := ⟨by rw [o₇ _ (by decide)]; exact hs₆.x3, by rw [o₇ _ (by decide)]; exact hs₆.mask,
    by rw [w₇]; exact hs₆.wr, hnw⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.preservedV (VG.Proof.Curve448.AArch64.Fast.ld_ok hs₇ .x19 (d := XSAVE) (by decide)
    (by decide)) (by lit_decide)) fun s₈ ⟨⟨x8, m₈, k₈⟩, vv₈⟩ => ?_
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  refine WP.mono (WP.preservedV (VG.Proof.Curve448.AArch64.Fast.ld_ok hs₈ .x30 (d := XSAVE + 8) (by decide)
    (by decide)) (by lit_decide)) fun u ⟨⟨xu, mu, ku⟩, vvu⟩ => ?_
  -- The saved bytes, as the saves left them.
  have mL : ∀ i, CSAVE ≤ i ∧ i < CSAVE + 128 ∨ XSAVE ≤ i ∧ i < XSAVE + 16 →
      tL.mem (off base i) = s₅.mem (off base i) := fun i hi => fL _ (save_unstored base hi)
  have rdL : ∀ k < 8, tL.mem.read (off base (CSAVE + 16 * k)) 16 = s₅.mem.read (off base (CSAVE + 16 * k)) 16 :=
    fun k hk => Mem.read_congr fun i hi => by
      rw [off_add]; exact mL _ (.inl (by simp only [CSAVE]; omega))
  have wL : ∀ d, XSAVE ≤ d → d + 8 ≤ XSAVE + 16 → word tL.mem base d = word s₅.mem base d :=
    fun d h1 h2 => Mem.readW_congr fun i hi => by
      rw [off_add]; exact mL _ (.inr (by simp only [XSAVE] at h1 h2 ⊢; omega))
  have mu' : u.mem = tL.mem := by rw [mu, m₈, m₇, m₆]
  have v6 : ∀ k < 8, s₆.v (V (8 + k)) = s₅.mem.read (off base (CSAVE + 16 * k)) 16 := fun k hk => by
    rw [v₆ k hk, rdL k hk]
  have gu : ∀ r, r ≠ .x19 → r ≠ .x30 → u.gpr r = s₇.gpr r := fun r h19 h20 => by
    rw [ku.1 r (by simpa using h20), k₈.1 r (by simpa using h19)]
  refine ⟨fun r hr h3 h12 => ?_, by rw [gu _ (by decide) (by decide), o₇ _ (by decide), g₆]; exact hsL.x3,
    by rw [gu _ (by decide) (by decide), o₇ _ (by decide), g₆]; exact hsL.mask,
    by rw [ku.2.1, k₈.2.1, r₇, r₆, hL.rd, hS.rd], by rw [ku.2.2, k₈.2.2, w₇, w₆, hL.wr, hS.wr],
    fun r hr => ?_, by rw [mu']; exact hL.env, by rw [mu']; exact hL.zero, fun x h1 h2 => ?_,
    by rw [mu']; exact hL.odd, by rw [mu']; exact hL.even⟩
  · by_cases e19 : r = .x19
    · subst e19
      rw [ku.1 _ (by decide), x8, m₇, m₆, wL _ le_rfl (by decide), hS.x19s]
    by_cases e20 : r = .x30
    · subst e20
      rw [xu, m₈, m₇, m₆, wL _ (by decide) le_rfl, hS.x30s]
    by_cases hk : r ∈ cks.map Prod.fst
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      obtain ⟨k, hk8, hkx⟩ : ∃ k < 8, cks.getD k (.x21, .v8, 1) = x := by
        revert x; decide
      obtain ⟨hv, hs', hl, -⟩ := cks_V k hk8
      rw [gu _ e19 e20, l₇ x hx, ← hkx, laneOf, hv, hl, v6 k hk8, hs']
      exact hS.lane1 k hk8
    · have hf : r ∉ .x1 :: fclob := hr.resolve_right hk
      rw [gu r e19 e20, o₇ r hk, g₆, hL.keep r (by simp only [List.mem_cons, not_or] at hf ⊢; exact ⟨hf.1, e19, hf.2⟩),
        hS.regs r h3 h12 e20]
  · obtain ⟨k, hk8, rfl⟩ := preservedV_V r hr
    rw [vvu _ hr, vv₈ _ hr, vv₇ _ hr, v6 k hk8]
    exact hS.lane0 k hk8
  · rw [mu', hL.mem x h1 h2]
    have hA : ACC = 3584 := rfl
    exact hS.mem x (by simp only [XSAVE]; omega) (by simp only [CSAVE]; omega)

end VG.Proof.Ed448.AArch64.CombBase

/-! # Calls -/

namespace VG.Proof.Ed448.AArch64.CombBase

open VG VG.AArch64 VG.Impl.Ed448.AArch64 VG.Impl.Ed448.AArch64.CombBase
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.X448.AArch64.Base (combSym)
open VG.Proof.X448.AArch64 (Scr Keeps limbs Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv fclob)
open VG.Proof.X448.AArch64.Base (pt Bits TblAt CombPre)
open VG.Proof.X448 (combG oddSumZ evenSumZ)
open VG.Proof.Ed448 (Rep baseAff)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "BFrame" => VG.Proof.X448.AArch64.Base.Frame

/-- The tables' bytes. -/
abbrev tblLen : Nat := 8 * (57 * 128)

/-- The function's proof, as the contract of a call on the working space at `base` and the tables
at `T`. -/
def combK (n : Nat) (base : Addr) (k : Nat) (T : Addr) : Contract isa where
  pre t := t.rd = [⟨T, tblLen⟩] ∧ t.wr = [⟨base, 8192⟩] ∧ t.gpr .x0 = base ∧
    t.gpr .x1 = BitVec.ofNat 64 n ∧ (n = 56 ∨ n = 57) ∧ base.toNat + 8192 ≤ 2 ^ 64 ∧ BEnv t.mem base ∧
    (∀ w < 8, limbs t.mem base (slot (19 : Index).val) w = 0) ∧ Bits n base k t.mem ∧
    TblAt t base T ∧ t.syms combSym = T
  post t u := CombOut n base k t u
  pub _ _ := True

theorem preserved_ok : ∀ r ∈ preserved, (r ∉ .x1 :: fclob ∨ r ∈ cks.map Prod.fst) ∧ r ≠ .x3 ∧ r ≠ .x12 := by
  decide

theorem combK_ok {n k : Nat} {base T : Addr} :
    ∀ s, (combK n base k T).pre s →
      ∃ t s', Exec isa combBaseFn s t s' ∧ abiPreserved s s' ∧ (combK n base k T).post s s' := by
  intro s ⟨_, hwr, h0, h1, hn, hnw, hb, hz, hbits, htbl, hsym⟩
  have hin : CombIn n base k s :=
    ⟨h0, h1, hn, by rw [hwr]; exact List.mem_singleton_self _, hnw, hb, hz, hbits, by rw [hsym]; exact htbl⟩
  obtain ⟨t, u, he, hout⟩ := combBaseFn_ok hin
  exact ⟨t, u, he, ⟨fun r hr => hout.regs r (preserved_ok r hr).1 (preserved_ok r hr).2.1 (preserved_ok r hr).2.2,
    Exec.sp he, hout.v⟩, hout⟩

theorem movz1_ok (s : State) {n : Nat} (hn : n = 56 ∨ n = 57) :
    WP isa (.block [.movz .x .x1 n 0]) s fun t => t.gpr .x1 = BitVec.ofNat 64 n ∧ t.mem = s.mem ∧
      Keeps [.x1] s t ∧ t.v = s.v := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl⟩
  rw [RegUpd.gpr_write_self]
  rcases hn with rfl | rfl <;> decide

/-- **A call of `vg_ed448_r56_comb_base`** for `n` tables: from `Frame` and what the comb needs,
`Frame` and the comb's sums. -/
theorem call_ok {n k : Nat} {s₀ s : State} {base : Addr} (hn : n = 56 ∨ n = 57) (hf : BFrame s₀ base s)
    (hp : CombPre n base k s) :
    WP isa (call n) s fun t => BFrame s₀ base t ∧
      Rep (pt (EV t.mem base) 0 1 2) (((combG n : ℤ) + oddSumZ k n) • baseAff) ∧
      Rep (pt (EV t.mem base) 3 4 5) (((combG n : ℤ) + evenSumZ k n) • baseAff) := by
  have hs := hf.scr
  have hnw := hs.nowrap
  unfold VG.Impl.Ed448.AArch64.CombBase.call
  rw [WP.seq_iff, show ([.vop (.ins .d2 .v8 0 .x30), .movz .x .x1 n 0] : List Instr) =
    insOf [(.x30, .v8, 0)] ++ ([.movz .x .x1 n 0] : List Instr) from rfl, WP.block_append_iff]
  refine WP.mono_syms (insOf_ok [(.x30, .v8, 0)] s (by decide) (by decide))
    fun t₁ ⟨g₁, m₁, r₁, w₁, sp₁, l₁, o₁⟩ sy₁ => ?_
  refine WP.mono_syms (movz1_ok t₁ hn) fun t₂ ⟨x1₂, m₂, k₂, v₂⟩ sy₂ => ?_
  unfold fnCall
  rw [WP.seq_iff, WP.seq_iff]
  refine WP.of_runBlock ⟨t₂.write .x .x0 (t₂.gpr .x3 + BitVec.ofNat 64 0), ?_, ?_⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
      show (0 : Nat) < 4096 from by decide, ite_true, BitVec.setWidth_eq]
  generalize ht₃ : t₂.write .x .x0 (t₂.gpr .x3 + BitVec.ofNat 64 0) = t₃
  have g₂ : ∀ r, r ≠ .x1 → t₂.gpr r = s.gpr r := fun r h => by rw [k₂.1 r (by simpa using h), g₁]
  have g0 : t₃.gpr .x0 = base := by
    rw [← ht₃, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero, g₂ _ (by decide), hs.x3]
  have gk : ∀ r, r ≠ .x0 → t₃.gpr r = t₂.gpr r := fun r hr => by rw [← ht₃, RegUpd.gpr_write_of_ne _ _ _ hr]
  have m₃ : t₃.mem = s.mem := by rw [← ht₃]; exact m₂.trans m₁
  have r₃ : t₃.rd = s.rd := by rw [← ht₃]; exact k₂.2.1.trans r₁
  have w₃ : t₃.wr = s.wr := by rw [← ht₃]; exact k₂.2.2.trans w₁
  have v₃ : t₃.v = t₁.v := by rw [← ht₃, ← v₂]; rfl
  have sy₃ : t₃.syms = s.syms := by rw [← ht₃, ← sy₁, ← sy₂]; rfl
  have htb : TblAt t₃ base (s.syms combSym) :=
    hp.tbl.of_far (by rw [r₃, w₃]) fun x _ => by rw [m₃]
  have hcov : Covers ([⟨s.syms combSym, tblLen⟩] ++ [⟨base, 8192⟩]) (t₃.rd ++ t₃.wr) :=
    Covers.append_left (Covers.one htb.rd)
      (Covers.right (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, w₃]; exact hs.wr))
  have hcw : Covers [⟨base, 8192⟩] t₃.wr :=
    Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, w₃]; exact hs.wr
  refine WP.callV (k := combK n base k (s.syms combSym)) (rd := [⟨s.syms combSym, tblLen⟩])
    (wr := [⟨base, 8192⟩]) combK_ok ⟨rfl, rfl, ?_, ?_, hn, hnw, ?_, ?_, ?_, ?_, ?_⟩ hcov hcw ?_
  · rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0]
  · rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), gk _ (by decide), x1₂]
  · rw [State.withRegions_mem, State.callEntry_mem, m₃]; exact hp.env
  · rw [State.withRegions_mem, State.callEntry_mem, m₃]; exact hp.zero
  · rw [State.withRegions_mem, State.callEntry_mem, m₃]; exact hp.bits
  · exact ⟨⟨⟨s.syms combSym, tblLen⟩, List.mem_append_left _ (List.mem_singleton_self _), by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, le_refl]⟩,
      htb.far, by rw [State.withRegions_mem, State.callEntry_mem]; exact htb.val⟩
  · show t₃.syms combSym = s.syms combSym
    rw [sy₃]
  intro t' hrd hwr hsp _ hpres _ hv hpost
  have hm : Outside2 base 64 2816 ACC 1152 s.mem t'.mem := by
    have := hpost.mem
    simp only [State.withRegions_mem, State.callEntry_mem, m₃] at this
    exact this
  refine WP.mono (umovOf_ok [(.x30, .v8, 0)] t' (by decide) (by decide)) fun u ⟨um, ur, uw, usp, ul, uo⟩ => ?_
  have gu : ∀ r, r ≠ .x30 → u.gpr r = t'.gpr r := fun r h => uo r (by simpa using h)
  have l30 : u.gpr .x30 = s₀.gpr .x30 := by
    rw [ul _ List.mem_cons_self]
    show (t'.v .v8).extractLsb' (64 * 0) 64 = _
    rw [hv .v8 (by decide), v₃]
    exact (l₁ _ List.mem_cons_self).trans hf.lr
  have x3u : u.gpr .x3 = base := by rw [gu _ (by decide)]; exact hpost.x3
  refine ⟨⟨⟨x3u, by rw [gu _ (by decide)]; exact hpost.mask, by rw [uw, hwr, w₃]; exact hs.wr, hnw⟩,
    by rw [um]; exact hpost.env, by rw [um]; exact hpost.zero, l30, ?_, by rw [ur, hrd, r₃, hf.rd],
    by rw [uw, hwr, w₃, hf.wr], ?_⟩, by rw [um]; exact hpost.odd, by rw [um]; exact hpost.even⟩
  · rw [gu _ (by decide), hpres .x20 (by decide) (by decide), gk _ (by decide), g₂ _ (by decide)]
    exact hf.out
  · rw [um]
    exact hf.mem.trans hm

end VG.Proof.Ed448.AArch64.CombBase

/-! # The shared contract -/

namespace VG.Proof.Ed448.AArch64.CombBase

open VG VG.AArch64 VG.Impl.Ed448.AArch64 VG.Impl.Ed448.AArch64.CombBase
open VG.Impl.X448.AArch64 (slot ACC BITS)
open VG.Impl.X448.AArch64.Base (combSym combWords combConsts)
open VG.Proof.X448.AArch64 (Scr limbs Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv)
open VG.Proof.X448.AArch64.Base (pt Bits CombHeld combConsts_eq combWords_length satMem satMem_held)
open VG.Proof.X448 (combG oddSumZ evenSumZ oddSum evenSum)
open VG.Proof.Ed448 (Rep baseAff)
open VG.Spec.Ed448.Comb56 (bitsAt IsBits oddNibbles evenNibbles)
open VG.Spec.X448.Field56 (slotAt elemAt Bounded)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-! ## The scalar's bits, and the comb's sums -/

theorem bitsAt_lt {m : Mem} {ws : Addr} : ∀ {T : Nat}, IsBits m ws T → bitsAt m ws T < 2 ^ T
  | 0, _ => by simp [bitsAt]
  | T + 1, h => by
    have ih := bitsAt_lt (T := T) fun i hi => h i (by omega)
    have hb := h T (by omega)
    simp only [bitsAt, Nat.pow_succ]
    have : 2 ^ T * (m (ws + BitVec.ofNat 64 (Spec.Ed448.Comb56.bitsOff + T))).toNat ≤ 2 ^ T * 1 :=
      Nat.mul_le_mul_left _ (by omega)
    omega

theorem bitsAt_bit {m : Mem} {ws : Addr} : ∀ {T : Nat}, IsBits m ws T → ∀ t < T,
    bitsAt m ws T / 2 ^ t % 2 = (m (ws + BitVec.ofNat 64 (Spec.Ed448.Comb56.bitsOff + t))).toNat
  | 0, _, t, ht => absurd ht (Nat.not_lt_zero _)
  | T + 1, h, t, ht => by
    have hT : IsBits m ws T := fun i hi => h i (by omega)
    have hb := h T (by omega)
    simp only [bitsAt]
    rcases Nat.lt_or_ge t T with htT | htT
    · have e : 2 ^ T = 2 ^ t * (2 * 2 ^ (T - t - 1)) := by
        rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
      rw [e, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos t), Nat.mul_assoc,
        Nat.add_mul_mod_self_left]
      exact bitsAt_bit hT t htT
    · have e : t = T := by omega
      subst e
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos t), Nat.div_eq_of_lt (bitsAt_lt hT), Nat.zero_add]
      exact Nat.mod_eq_of_lt hb

theorem bits_of_isBits {m : Mem} {ws : Addr} {n : Nat} (h : IsBits m ws (8 * n)) :
    Bits n ws (bitsAt m ws (8 * n)) m := fun t ht => by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, VG.Proof.X448.AArch64.Base.bit_eq, bitsAt_bit h t ht]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (h t ht) (by decide))).symm

theorem oddNibbles_eq (k : Nat) : ∀ c, oddNibbles k c = oddSum k c
  | 0 => rfl
  | c + 1 => by simp only [oddNibbles, oddSum, oddNibbles_eq k c]; rfl

theorem evenNibbles_eq (k : Nat) : ∀ c, evenNibbles k c = evenSum k c
  | 0 => rfl
  | c + 1 => by simp only [evenNibbles, evenSum, evenNibbles_eq k c]; rfl

theorem odd_eq (k n : Nat) : (combG n : ℤ) + oddSumZ k n = (oddNibbles k n : Nat) := by
  rw [VG.Proof.X448.oddSumZ_eq, oddNibbles_eq]; simp only [combG]; push_cast; omega

theorem even_eq (k n : Nat) : (combG n : ℤ) + evenSumZ k n = (evenNibbles k n : Nat) := by
  rw [VG.Proof.X448.evenSumZ_eq, evenNibbles_eq]; simp only [combG]; push_cast; omega

/-- A point representing `[s] B` is `pointEqual` to `pointMul s basePoint`. -/
theorem pointEqual_of_rep {p : Spec.Ed448.Point} {s : Nat} (h : Rep p ((s : ℤ) • baseAff)) :
    Spec.Ed448.pointEqual p (Spec.Ed448.pointMul s Spec.Ed448.basePoint) = true := by
  refine (VG.Proof.Ed448.pointEqual_rep h (VG.Proof.Ed448.pointMul_rep s VG.Proof.Ed448.basePoint_rep)).mpr ?_
  rw [natCast_zsmul]

/-! ## The contract -/

theorem pointAt_eqN (m : Mem) (ws : Addr) (n : Nat) (x y z : Index) (hx : x.val = n) (hy : y.val = n + 1)
    (hz : z.val = n + 2) : Spec.Ed448.Point56.pointAt m ws n = pt (EV m ws) x y z := by
  simp only [Spec.Ed448.Point56.pointAt, pt]
  subst hx
  rw [← hy, ← hz, VG.Proof.Ed448.AArch64.Point56.elemAt_eq, VG.Proof.Ed448.AArch64.Point56.elemAt_eq,
    VG.Proof.Ed448.AArch64.Point56.elemAt_eq]

/-- The precondition and postcondition, by name: `ws` in `x0`, `n` in `x1`, the tables readable and
the working space writable. -/
def combL : Contract isa where
  pre s := s.rd = [⟨s.syms combSym, 8 * combWords.length⟩] ∧ s.wr = [⟨s.gpr .x0, 8192⟩] ∧
    (s.gpr .x0).toNat + 8192 ≤ 2 ^ 64 ∧ CombHeld s [⟨s.gpr .x0, 8192⟩] ∧
    ((s.gpr .x1).toNat = 56 ∨ (s.gpr .x1).toNat = 57) ∧ IsBits s.mem (s.gpr .x0) (8 * (s.gpr .x1).toNat) ∧
    Bounded s.mem (s.gpr .x0) ∧
    ∀ i < 8, VG.Spec.X448.Field56.limbAt s.mem (s.gpr .x0) (slotAt 19) i = 0
  post s s' := Bounded s'.mem (s.gpr .x0) ∧ elemAt s'.mem (s.gpr .x0) (slotAt 2) ≠ 0 ∧
    elemAt s'.mem (s.gpr .x0) (slotAt 5) ≠ 0 ∧
    Spec.Ed448.pointEqual (Spec.Ed448.Point56.pointAt s'.mem (s.gpr .x0) 0)
      (Spec.Ed448.pointMul (oddNibbles (bitsAt s.mem (s.gpr .x0) (8 * (s.gpr .x1).toNat)) (s.gpr .x1).toNat)
        Spec.Ed448.basePoint) = true ∧
    Spec.Ed448.pointEqual (Spec.Ed448.Point56.pointAt s'.mem (s.gpr .x0) 3)
      (Spec.Ed448.pointMul (evenNibbles (bitsAt s.mem (s.gpr .x0) (8 * (s.gpr .x1).toNat)) (s.gpr .x1).toNat)
        Spec.Ed448.basePoint) = true ∧
    VG.Spec.X448.Field56.Keeps (s.gpr .x0) Spec.Ed448.Comb56.written s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp ∧
    s₁.syms combSym = s₂.syms combSym

theorem z_ne {m : Mem} {ws : Addr} {i : Index} (h : VG.Proof.Ed448.toZ (EV m ws i) ≠ 0) :
    elemAt m ws (slotAt i.val) ≠ 0 := fun e => h (by
  rw [← VG.Proof.Ed448.AArch64.Point56.elemAt_eq, e, VG.Proof.Ed448.toZ_zero])

theorem comb_arm (s : State) (hs : combL.pre s) :
    ∃ t s', Exec isa combBaseFn s t s' ∧ abiPreserved s s' ∧ combL.post s s' := by
  obtain ⟨hrd, hwr, hnw, hheld, hn, hbits, hb, hz⟩ := hs
  have hx1 : s.gpr .x1 = BitVec.ofNat 64 (s.gpr .x1).toNat := BitVec.eq_of_toNat_eq (by simp)
  have hin : CombIn (s.gpr .x1).toNat (s.gpr .x0) (bitsAt s.mem (s.gpr .x0) (8 * (s.gpr .x1).toNat)) s :=
    ⟨rfl, hx1, hn, by rw [hwr]; exact List.mem_singleton_self _, hnw,
      (VG.Proof.Ed448.AArch64.Point56.bounded_iff _ _).mp hb, fun w hw => hz w hw, bits_of_isBits hbits,
      hheld.tblAt (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
        (List.mem_singleton_self _)⟩
  obtain ⟨t, u, he, ho⟩ := combBaseFn_ok hin
  refine ⟨t, u, he, ⟨fun r hr => ho.regs r (preserved_ok r hr).1 (preserved_ok r hr).2.1 (preserved_ok r hr).2.2,
    Exec.sp he, ho.v⟩, (VG.Proof.Ed448.AArch64.Point56.bounded_iff _ _).mpr ho.env, z_ne (i := 2) ho.odd.z,
    z_ne (i := 5) ho.even.z, ?_, ?_, fun i hi hr => ?_⟩
  · rw [pointAt_eqN _ _ 0 0 1 2 rfl rfl rfl]
    exact pointEqual_of_rep (by rw [← odd_eq]; exact ho.odd)
  · rw [pointAt_eqN _ _ 3 3 4 5 rfl rfl rfl]
    exact pointEqual_of_rep (by rw [← even_eq]; exact ho.even)
  · simp only [Spec.Ed448.Comb56.written, VG.Spec.X448.Field56.own, slotAt, VG.Spec.X448.Field56.slots,
      VG.Spec.X448.Field56.accAt, VG.Spec.X448.Field56.accEnd, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hr
    simp only [VG.Spec.X448.Field56.wsBytes] at hi
    have e := VG.Proof.X448.AArch64.Base.ofs_off0 (s.gpr .x0) (d := i) (by omega)
    have hA : ACC = 3584 := rfl
    exact ho.mem _ (by rw [e]; omega) (by rw [e]; omega)

theorem comb_check :
    ∃ h, ((taintS [combSym]).check (Taint.ofRegs [.x0, .x1]) combBaseFn h).isSome = true := by
  apply exists_isSome_of_eraseT
  refine Split.exists_isSome (c' := ?c') ?s ⟨?h, ?g⟩
  case s =>
    simp only [combBaseFn, Code.eraseT]
    exact .seq (.refl _) (.seq (.refl _) (.seq (.loop _ VG.AArch64.stepR_split) (.refl _)))
  case g => taint_decide

theorem comb_ct : ConstantTime isa combL.pre combL.pub combBaseFn :=
  let ⟨_, hc⟩ := comb_check
  VG.Taint.constantTime (A := taintS [combSym]) (Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h0
      · exact h1⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) hc

/-! ## The shared contract -/

/-- The memory of `satState`: zero below the tables, which are at `0x100000`. -/
def satMem2 : Mem := fun a => if a.toNat < 0x100000 then 0 else satMem a

/-- A state satisfying the precondition: `ws` at `0x1000`, every slot zero, `n = 56` and its bits
zero, and the tables at `0x100000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 56 | _ => 0
  sp := 0x10000
  mem := satMem2
  rd := [⟨0x100000, 58368⟩]
  wr := [⟨0x1000, 8192⟩]
  syms _ := 0x100000

theorem satMem2_held : ∀ i < combWords.length,
    satMem2.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := fun i hi => by
  rw [← satMem_held i hi]
  refine Mem.readW_congr fun j hj => ?_
  have hl := combWords_length
  have : ¬ (0x100000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat < 0x100000 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [hl] at hi
    have e : (1048576 : BitVec 64).toNat = 1048576 := rfl
    rw [e]
    simp only [Nat.reducePow] at *
    omega
  simp only [satMem2, this, ite_false]

theorem sat_bounded : Bounded satMem2 0x1000 := by
  unfold Bounded; decide +kernel

theorem sat_bits : IsBits satMem2 0x1000 (8 * 56) := by
  unfold IsBits; decide +kernel

theorem sat_zero : ∀ i < 8, VG.Spec.X448.Field56.limbAt satMem2 0x1000 (slotAt 19) i = 0 := by
  decide +kernel

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State} (hrd : s.rd = [⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 8192⟩]) (hnw : (s.gpr .x0).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .x0, 8192⟩]) (hn : (s.gpr .x1).toNat = 56 ∨ (s.gpr .x1).toNat = 57)
    (hbits : IsBits s.mem (s.gpr .x0) (8 * (s.gpr .x1).toNat)) (hb : Bounded s.mem (s.gpr .x0))
    (hz : ∀ i < 8, VG.Spec.X448.Field56.limbAt s.mem (s.gpr .x0) (slotAt 19) i = 0) :
    (Spec.Ed448.Comb56.combBaseContract (AArch64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.Ed448.Comb56.combBaseContract, Spec.Ed448.Comb56.sig, AArch64.abi, AArch64.argRegs,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, by rw [hrd]; rfl, hw, hnw, hn, hbits, hb, hz⟩

theorem implies : combL.Implies (Spec.Ed448.Comb56.combBaseContract (AArch64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.Ed448.Comb56.combBaseContract, Spec.Ed448.Comb56.sig, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, ht, hw, hnw, hn, hbits, hb, hz⟩ := h
    refine ⟨?_, hw, hnw, ⟨hheld, hfit, by rw [hw] at hdw; exact hdw⟩, hn, hbits, hb, hz⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.Ed448.Comb56.combBaseContract, Spec.Ed448.Comb56.sig, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ed448.Comb56.combBaseContract, Spec.Ed448.Comb56.sig, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1⟩ := h
    exact ⟨h0, h1, hsp, hsy⟩
  sat := ⟨satState, by
    have hl := combWords_length
    refine spec_pre (by rw [hl]; rfl) rfl (by decide) ⟨satMem2_held, by rw [hl]; decide, ?_⟩ (.inl rfl)
      sat_bits sat_bounded sat_zero
    simp only [List.mem_singleton]
    rintro r rfl
    rw [hl]
    exact Region.disjoint_of_sep (by decide)⟩

theorem combBaseFn_verified :
    Verified AArch64.target combBaseFn
      (Spec.Ed448.Comb56.combBaseContract (AArch64.abi.withConsts combConsts)) :=
  Verified.of_correct comb_arm comb_ct implies

end VG.Proof.Ed448.AArch64.CombBase
