module

public import VerifiedGarbage.Proof.Camellia.AArch64.Group
import Mathlib.Tactic.SplitIfs

/-!
# Camellia ECB on AArch64: the whole function

`ecb_wp`: with the working space as an argument (`ecbAArch64`), `ecb dir`
saves the callee-saved registers, sets the masks, builds the table of
subkeys for 18 or 24 rounds in the order `dir` uses them, transforms the
blocks a group at a time (`dataGroup_wp`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 kp movR ldS stS)

/-- The specification's direction. -/
def specDir : Dir → Spec.Camellia.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on AArch64 with its working space at `x4`. -/
def ecbAArch64 (dir : Dir) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 272⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * slots⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧
      (s.gpr .x0).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 16 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + 8 * slots ≤ 2 ^ 64 ∧ ((s.gpr .x1).toNat = 18 ∨ (s.gpr .x1).toNat = 24)
  post s s' :=
    Spec.Camellia.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      Spec.Camellia.ecb (Spec.Camellia.subkeysAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) (specDir dir)
        (Spec.Camellia.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- The order of the subkeys in the table, for each direction. -/
def permOf (dir : Dir) : Nat → Nat → Nat := Proof.Camellia.dirPerm (specDir dir)

/-- The subkeys the loop bitslices, for `g` groups. -/
def cntOf : Dir → Nat → Nat
  | .encrypt, g => 8 * g + 2
  | .decrypt, g => 8 * g - 2

/-- How far `groupConsts` moves `x0`. -/
def x0Of : Dir → Nat → Nat
  | .encrypt, _ => 0
  | .decrypt, g => 64 * g

theorem groupConsts_ok (dir : Dir) {g : Nat} (hg : g = 3 ∨ g = 4) (s : State) :
    ∃ s', runBlock isa (groupConsts dir g) s = some s' ∧
      s'.gpr .x4 = s.gpr sb + BitVec.ofNat 64 (8 * keySlot + 512 * g) ∧
      s'.gpr t1 = BitVec.ofNat 64 (cntOf dir g) ∧ s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 (x0Of dir g) ∧
      (∀ r, r ≠ .x4 → r ≠ t1 → r ≠ .x0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .x4 sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₁ .x4 .x4 (imm := 8 * keySlot + 512 * g)
    (by rw [keySlot_eq]; omega)
  have e₁₂ : runBlock isa (endAddr g) s = some s₂ := by
    rw [endAddr, show ([movR .x4 sb, .addImm .x .x4 .x4 (8 * keySlot + 512 * g)] :
      List Instr) = [movR .x4 sb] ++ [.addImm .x .x4 .x4 (8 * keySlot + 512 * g)] from rfl,
      runBlock_append', e₁, Option.bind_some, e₂]
  have x4₂ : s₂.gpr .x4 = s.gpr sb + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by rw [r₂, r₁]
  have o₁₂ : ∀ r, r ≠ .x4 → s₂.gpr r = s.gpr r := fun r h => by rw [o₂ r h, o₁ r h]
  cases dir
  · obtain ⟨s₃, e₃, t₃, o₃, m₃, rd₃, wr₃⟩ := movz_ok s₂ t1 (v := 8 * g + 2) (by omega)
    refine ⟨s₃, by rw [groupConsts, runBlock_append', e₁₂, Option.bind_some, e₃],
      by rw [o₃ _ (by decide), x4₂], t₃, by rw [o₃ _ (by decide), o₁₂ _ (by decide)]; simp [x0Of],
      fun r h1 h2 _ => by rw [o₃ r h2, o₁₂ r h1], by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩
  · obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := addI_ok s₂ .x0 .x0 (imm := 64 * g) (by omega)
    obtain ⟨s₄, e₄, t₄, o₄, m₄, rd₄, wr₄⟩ := movz_ok s₃ t1 (v := 8 * g - 2) (by omega)
    refine ⟨s₄, by
      rw [groupConsts, runBlock_append', e₁₂, Option.bind_some,
        show ([Instr.addImm .x .x0 .x0 (64 * g), .movz .x t1 (BitVec.ofNat 16 (8 * g - 2)) 0] : List Instr) =
          [.addImm .x .x0 .x0 (64 * g)] ++ [.movz .x t1 (BitVec.ofNat 16 (8 * g - 2)) 0] from rfl,
        runBlock_append', e₃, Option.bind_some, e₄],
      by rw [o₄ _ (by decide), o₃ _ (by decide), x4₂], t₄,
      by rw [o₄ _ (by decide), r₃, o₁₂ _ (by decide)]; rfl,
      fun r h1 h2 h3 => by rw [o₄ r h2, o₃ r h3, o₁₂ r h1], by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁],
      by rw [wr₄, wr₃, wr₂, wr₁]⟩

/-- `KeysPost` from the state after `groupConsts`, which wrote only `x4`, `t1` and `x0`. -/
theorem KeysPost.of_consts {s₀ s₁ s : State} {b sched : Addr} {g : Nat} {perm : Nat → Nat}
    (h : KeysPost s₁ b sched g perm s) (hm : s₁.mem = s₀.mem) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (ho : ∀ r, r ≠ .x4 → r ≠ t1 → r ≠ .x0 → s₁.gpr r = s₀.gpr r) : KeysPost s₀ b sched g perm s :=
  ⟨h.pre, fun i hi => hm ▸ h.ent i hi, h.masks, hm ▸ h.frame,
    fun r h1 h2 h3 h4 => by rw [h.regs r h1 h2 h3 h4, ho r h4 (fun h => h1 (by subst h; decide)) h3],
    h.rd.trans hrd, h.wr.trans hwr⟩

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : Addr} {g : Nat} (hg : g = 3 ∨ g = 4)
    (hz : isa.eval (.zero .x t0) s₀ = some (decide (g = 3)))
    (hk : KeyPre s₀ b sched) (hx0 : s₀.gpr .x0 = sched) (hm : MasksOk s₀) :
    WP isa (keys dir) s₀ fun s => KeysPost s₀ b sched g (permOf dir g) s ∧
      s.gpr .x4 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
  unfold keys
  refine WP.seq (WP.mono (M := isa) (Q := fun s₁ =>
      s₁.gpr .x4 = s₀.gpr sb + BitVec.ofNat 64 (8 * keySlot + 512 * g) ∧
      s₁.gpr t1 = BitVec.ofNat 64 (cntOf dir g) ∧ s₁.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (x0Of dir g) ∧
      (∀ r, r ≠ .x4 → r ≠ t1 → r ≠ .x0 → s₁.gpr r = s₀.gpr r) ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧
      s₁.wr = s₀.wr)
    (WP.ite (decide (g = 3)) hz (fun h => ?_) (fun h => ?_)) fun s₁ h₁ => ?_)
  · obtain rfl : g = 3 := by simpa using h
    obtain ⟨s', e', h'⟩ := groupConsts_ok dir hg s₀
    exact WP.of_runBlock ⟨s', e', h'⟩
  · obtain rfl : g = 4 := by simp at h; omega
    obtain ⟨s', e', h'⟩ := groupConsts_ok dir hg s₀
    exact WP.of_runBlock ⟨s', e', h'⟩
  obtain ⟨x4₁, t₁, x0₁, o₁, m₁, rd₁, wr₁⟩ := h₁
  have hk₁ : KeyPre s₁ b sched := hk.congr (o₁ _ (by decide) (by decide) (by decide)) rd₁ wr₁
  have hm₁ : MasksOk s₁ := fun kv hkv => by
    show s₁.mem.readW (wordAddr (s₁.gpr sb) kv.1) 64 = kv.2
    rw [m₁, o₁ _ (by decide) (by decide) (by decide)]; exact hm kv hkv
  have x4 : s₁.gpr .x4 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by rw [x4₁, hk.base]
  cases dir
  · exact WP.mono (encKeys_wp hg hk₁ (by rw [x0₁, hx0]; simp [x0Of]) t₁ hm₁) fun s ⟨h, h4⟩ =>
      ⟨h.of_consts m₁ rd₁ wr₁ o₁, h4.trans x4⟩
  · exact WP.mono (decKeys_wp hg hk₁ (by rw [x0₁, hx0]; simp only [x0Of]; congr 2; omega) t₁ hm₁)
      fun s ⟨h, h4⟩ => ⟨h.of_consts m₁ rd₁ wr₁ o₁, h4.trans x4⟩

theorem dataLoop_wp {s₀ : State} {b D : Addr} {n g : Nat} {E : Nat → BitVec 64} (hp : GPre s₀ b D n g)
    {s : State} (hi : GInv s₀ b D n g E 0 s) :
    WP isa (.loop Impl.Camellia.AArch64.group (.nonzero .x .x3)) s (GDone s₀ b D n g E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 8 * k ∧ GInv s₀ b D n g E k s) (fun m s hs => ?_) n s
    ⟨0, by omega, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_nonzero s' .x3).trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_nonzero s' .x3).trans (by rw [beq_false_of_ne z]; rfl), n - 8 * (k + 1),
      by have := d.lt; have := hk.lt; omega, k + 1, rfl, d⟩

theorem sreg_ne (i : Nat) (hi : i < 10) : sreg i ≠ sb := by
  revert i; decide

theorem prologue_ok {s₀ : State} {a : Reg} {b : Addr} (hb : s₀.gpr a = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr) :
    ∃ s, runBlock isa (([movR sb a] : List Instr) ++ saveRegs ++ setSlots layerMasks ++
        ([.subImm .x t0 .x1 18] : List Instr)) s₀ = some s ∧
      s.gpr sb = b ∧ (∀ r, r ≠ sb → r ≠ t0 → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧ s.gpr t0 = s₀.gpr .x1 - BitVec.ofNat 64 18 ∧
      Frame [⟨b, 8 * keySlot⟩, savedRegion b] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb a
  have hb₁ : s₁.gpr sb = b := by rw [r₁, hb]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁]; exact hw) hb₁
  obtain ⟨s₃, e₃, v₃, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) (by rw [wr₂, wr₁]; exact hw) (by rw [g₂, hb₁])
  obtain ⟨s₄, e₄, t₄, o₄, m₄, rd₄, wr₄⟩ := subI_ok s₃ t0 .x1 (imm := 18) (by decide)
  have hfit : ∀ i < 10, savedSlot + i < 2 ^ 58 := fun i hi => by rw [savedSlot_eq]; omega
  refine ⟨s₄, by
    rw [runBlock_append', runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some,
      e₃, Option.bind_some, e₄],
    by rw [o₄ _ (by decide), g₃ _ (by decide), g₂, hb₁],
    fun r h1 h2 => by rw [o₄ r h2, g₃ r h2, g₂, o₁ r h1], fun i hi => ?_, fun kv hkv => ?_,
    by rw [t₄, g₃ _ (by decide), g₂, o₁ _ (by decide)], ?_,
    by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [m₄, ← o₁ _ (sreg_ne i hi), ← sv₂ i hi]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [keySlot_eq, savedSlot_eq]; omega)
      (by rw [savedSlot_eq]; omega)
  · show s₄.mem.readW (wordAddr (s₄.gpr sb) kv.1) 64 = kv.2
    rw [m₄, o₄ _ (by decide)]; exact v₃ kv hkv
  · rw [m₄, ← m₁]
    refine (f₂.mono fun r hr => ?_).trans (f₃.mono fun r hr => ?_) <;>
      (simp only [List.mem_singleton] at hr; subst hr; simp)

/-! ## The specification -/

/-! ## The whole function -/

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbAArch64 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (ecbAArch64 dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, fitK, fitD, fitB, hR⟩ := hp
  let b := s₀.gpr .x4
  let D := s₀.gpr .x2
  let n := (s₀.gpr .x3).toNat
  let sched := s₀.gpr .x0
  let R := (s₀.gpr .x1).toNat
  have hg : R / 6 = 3 ∨ R / 6 = 4 := by omega
  have hg4 : R / 6 ≤ 4 := by omega
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨sched, 272⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, m₁, t₁, f₁, rd₁, wr₁⟩ := prologue_ok (b := b) rfl hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : KeyPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, fitB, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  have x0₁ : s₁.gpr .x0 = sched := g₁ _ (by decide) (by decide)
  have hz₁ : (s₁.gpr t0 == 0) = decide (R = 18) := by
    rw [t₁, show s₀.gpr .x1 = BitVec.ofNat 64 R by simp only [R, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  -- The table.
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  rw [hgR] at hg hg4
  refine WP.seq (WP.mono (keys_wp dir hg ((eval_zero s₁ t0).trans (by
    rw [hz₁]; exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩)))
    hk₁ x0₁ m₁) fun s₂ ⟨k₂, x4₂⟩ => ?_)
  -- The scratch buffer and the data before the groups.
  let E : Nat → BitVec 64 := fun i => (schedWords s₀.mem sched R).getD (permOf dir g i) 0
  have hfitB := fitB
  rw [slots_eq] at hfitB
  have f₀₂ : Frame [⟨b, 8 * slots⟩] s₀.mem s₂.mem := by
    refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Region.sub_prefix (by simp only [slots_eq, keySlot_eq]; omega)
      · exact VG.Offset.sub_base b (by simp only [slots_eq, savedSlot_eq]; omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by simp only [slots_eq, endSlot_eq]; omega)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  have hE : ∀ i < 8 * g + 2,
      Spec.Camellia.wordAt s₁.mem (sched + BitVec.ofNat 64 (8 * permOf dir g i)) = E i := fun i hi => by
    have hp : permOf dir g i < 8 * g + 2 := dirPerm_lt (specDir dir) hi
    rw [show E i = _ from schedWords_getD s₀.mem sched (R := R) (by simp only [Spec.Camellia.scheduleLength]; omega)]
    refine wordAt_frame f₁ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dSS.sub_left (VG.Offset.sub_base sched (by omega))).sub_right (Region.sub_prefix (by
        rw [slots_eq, keySlot_eq]; omega))
    · exact (dSS.sub_left (VG.Offset.sub_base sched (by omega))).sub_right (VG.Offset.sub_base b (by
        rw [slots_eq, savedSlot_eq]; omega))
  have sc₂ : ScrOk s₀ b g E s₂.mem := by
    refine ⟨k₂.masks.at base₂, fun i hi => hE i hi ▸ k₂.ent i hi, fun i hi => ?_⟩
    rw [← sv₁ i hi]
    refine k₂.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [endSlot_eq, savedSlot_eq]; omega)
      (by rw [savedSlot_eq]; omega)
  have data₂ : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₀₂.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS)
      (by simp only; omega) hi
  have fr₂ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₂.mem :=
    f₀₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have x3₂ : s₂.gpr .x3 = s₀.gpr .x3 := by
    rw [k₂.regs _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
  have x2₂ : s₂.gpr .x2 = D := by
    rw [k₂.regs _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
  have rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  -- Any blocks?
  have hz₃ : (s₂.gpr .x3 == 0) = decide (n = 0) := by
    rw [x3₂, show s₀.gpr .x3 = BitVec.ofNat 64 n by simp only [n, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n g E)
    (WP.ite (decide (n = 0)) ((eval_zero s₂ .x3).trans (by rw [hz₃])) (fun h0 => ?_) (fun h0 => ?_))
    fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₂, sc₂, fun i hi => by omega, fr₂, rd₂, wr₂⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitB, fitD, hg⟩ ⟨base₂, by rw [x2₂]; simp,
      by rw [x3₂, Nat.mul_zero, Nat.sub_zero]; simp [n], by omega, x4₂, sc₂, fun i hi => ?_, fr₂, rd₂, wr₂⟩
    rw [data₂ i hi, ite_eq_right (by omega)]
  -- The epilogue.
  obtain ⟨s₅, e₅, rg₅, -, m₅, -, -⟩ := restore_ok (by rw [d₄.wr]; exact hwS) d₄.base d₄.scr.saved
  refine WP.of_runBlock ⟨s₅, e₅, rg₅, ?_⟩
  have hd₅ : DInv s₀.mem s₅.mem D n n (outF s₀.mem D g E) := fun i hi => by
    rw [m₅]; exact d₄.data i hi
  show Spec.Camellia.blocksAt s₅.mem D n = _
  rw [blocksAt_of_dinv hd₅, ecb_eq]
  simp only [Spec.Camellia.blocksAt, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  subst hgR
  exact outF_spec (specDir dir) s₀.mem sched D hR j

end VG.Proof.Camellia.AArch64
