module

public import VerifiedGarbage.Proof.Rc4.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rc4.AArch64.Lookup
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd

/-! ### `Rc4.AArch64.Rotate`, which this module and modules that import it used -/

section

/-!
# The rotation after a group

`rotate_ok`: the table registers move down by one (byte `k` becomes the old
byte `k + 16`, around the table), `j` and `-B` move back by 16, and the base
in `x8` advances by 16.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

def movs (n : Nat) : List Instr := (List.range n).map fun r => .vop (.mov (treg r) (treg (r + 1)))

theorem movs_succ (n : Nat) :
    movs (n + 1) = movs n ++ ([.vop (.mov (treg n) (treg (n + 1)))] : List Instr) := by
  simp only [movs, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem movs_run (s : State) {n : Nat} (hn : n ≤ 15) :
    ∃ t, runBlock isa (movs n) s = some t ∧ (∀ r < 16, t.v (treg r) =
      if r < n then s.v (treg (r + 1)) else s.v (treg r)) ∧ Only (treg 0 :: (List.range 15).map treg) s t := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun r _ => by simp, Only.refl _ _⟩
  | succ n ih =>
    obtain ⟨t, run, v, o⟩ := ih (by omega_using [hn])
    let t' := t.setV (treg n) (t.v (treg (n + 1)))
    refine ⟨t', ?_, fun r hr => ?_, o.trans (Only.setV _ (by
      simp only [List.mem_cons, List.mem_map, List.mem_range]
      exact .inr ⟨n, by omega_using [hn], rfl⟩) _)⟩
    · rw [movs_succ]
      exact runBlock_cat_some run (by rw [runBlock_cons]; exact rfl)
    · by_cases h : r = n
      · subst h
        simp only [t', v_setV_self, v (r + 1) (by omega_using [hn]), show ¬ r + 1 < r by omega_using [], ite_false,
          show r < r + 1 by omega_using [], ite_true]
      · rw [v_setV_of_ne _ _ (fun e => h (treg_inj _ hr _ (by omega_using [hn]) e)), v r hr]
        exact ite_iff ⟨fun h' => by omega_using [h'], fun h' => by omega_using [h, h']⟩ _ _

theorem lanes_diff : VArr.b16.map2 (fun _ x y => x - y) (laneNums 1) (laneNums 0) = bc 16 :=
  vbyte_ext fun e he => by
    rw [vbyte_map2 _ _ _ he, laneNums, laneNums, vbyte_ofVBytes _ he, vbyte_ofVBytes _ he,
      vbyte_bc _ he]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (16 : BitVec 8).toNat = 16 from rfl]
    omega_using []

theorem rotate_eq (prga : Bool) : rotate prga =
    ([.vop (.sub .b16 .v7 (lanes 1) (lanes 0)), .vop (.sub .b16 (dq 0) (dq 0) .v7)] : List Instr) ++
      ((if prga then [.vop (.sub .b16 negBase negBase .v7)] else []) ++
        (([.vop (.mov .v7 (treg 0))] : List Instr) ++ (movs 15 ++
          ([.vop (.mov (treg 15) .v7), .addImm .x .x8 .x8 16] : List Instr)))) := by
  simp only [rotate, movs, List.append_assoc]

/-- The vector registers a rotation changes. -/
def rotRegs : List VReg := .v7 :: dq 0 :: negBase :: (List.range 16).map treg

theorem rotate_ok (prga : Bool) {s : State} (hk : Consts s) {J NB : BitVec 8}
    (hj : s.v (dq 0) = bc J) (hn : prga = true → s.v negBase = bc NB) :
    WP isa (.block (rotate prga)) s fun t =>
      (∀ k < 256, tbyte t.v k = tbyte s.v ((k + 16) % 256)) ∧ t.v (dq 0) = bc (J - 16) ∧
      t.v negBase = (if prga then bc (NB - 16) else s.v negBase) ∧
      t.gpr .x8 = s.gpr .x8 + 16 ∧ (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧
      (∀ r, r ∉ rotRegs → t.v r = s.v r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let s₁ := s.setV .v7 (VArr.b16.map2 (fun _ x y => x - y) (s.v (lanes 1)) (s.v (lanes 0)))
  have v₁ : s₁.v .v7 = bc 16 := by
    rw [v_setV_self, hk.lns 1 (by decide), hk.lns 0 (by decide), lanes_diff]
  let s₂ := s₁.setV (dq 0) (VArr.b16.map2 (fun _ x y => x - y) (s₁.v (dq 0)) (s₁.v .v7))
  have j₂ : s₂.v (dq 0) = bc (J - 16) := by
    rw [v_setV_self, v₁, v_setV_of_ne _ _ (by decide), hj, sub_bc]
  obtain ⟨s₃, run₃, n₃, o₃⟩ : ∃ s₃, runBlock isa
      ((if prga then [.vop (.sub .b16 negBase negBase .v7)] else []) : List Instr) s₂ = some s₃ ∧
      s₃.v negBase = (if prga then bc (NB - 16) else s.v negBase) ∧ Only [negBase] s₂ s₃ := by
    cases prga
    · refine ⟨s₂, by simp only [Bool.false_eq_true, ite_false]; exact runBlock_nil, ?_, Only.refl _ _⟩
      simp only [Bool.false_eq_true, ite_false]
      rw [v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide)]
    · refine ⟨s₂.setV negBase (VArr.b16.map2 (fun _ x y => x - y) (s₂.v negBase) (s₂.v .v7)),
        by simp only [ite_true]; rw [runBlock_cons]; rfl, ?_, Only.setV _ (by simp) _⟩
      simp only [ite_true]
      rw [v_setV_self, v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide), hn rfl,
        v_setV_of_ne _ _ (by decide), v₁, sub_bc]
  let s₄ := s₃.setV .v7 (s₃.v (treg 0))
  obtain ⟨s₅, run₅, v₅, o₅⟩ := movs_run s₄ (n := 15) (Nat.le_refl _)
  let s₆ := s₅.setV (treg 15) (s₅.v .v7)
  let s₇ := s₆.write .x .x8 (s₆.read .x .x8 + BitVec.ofNat _ 16)
  have run : runBlock isa (rotate prga) s = some s₇ := by
    rw [rotate_eq]
    refine runBlock_cat_some (s₁ := s₂) (by
      rw [runBlock_cons, show exec (.vop (.sub .b16 .v7 (lanes 1) (lanes 0))) s = some s₁ from rfl,
        runStep_some, runBlock_cons, show exec (.vop (.sub .b16 (dq 0) (dq 0) .v7)) s₁ = some s₂ from rfl,
        runStep_some, runBlock_nil]) ?_
    refine runBlock_cat_some run₃ ?_
    rw [List.singleton_append, runBlock_cons, show exec (.vop (.mov .v7 (treg 0))) s₃ = some s₄ from rfl,
      runStep_some]
    refine runBlock_cat_some run₅ ?_
    rw [runBlock_cons, show exec (.vop (.mov (treg 15) .v7)) s₅ = some s₆ from rfl, runStep_some,
      runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₇, run, ?_⟩
  have v₇ : s₇.v = s₆.v := rfl
  have movsRegs : ∀ r, r ∉ (treg 0 :: (List.range 15).map treg) → r ∉ (List.range 16).map treg →
      True := fun _ _ _ => trivial
  -- what the moves leave alone
  have keep₅ : ∀ r, NotTable r → s₅.v r = s₄.v r := fun r hr => o₅.2 r (by
    simp only [List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists, not_and]
    exact ⟨fun h => hr.ne 0 h.symm, fun a _ h => hr.ne a h⟩)
  have keep₂ : ∀ r, NotTable r → r ≠ .v7 → r ≠ dq 0 → r ≠ negBase → s₃.v r = s.v r := by
    intro r _ h7 hd hn
    rw [o₃.2 r (by simp [hn]), v_setV_of_ne _ _ hd, v_setV_of_ne _ _ h7]
  have tab₃ : ∀ a < 16, s₃.v (treg a) = s.v (treg a) := by
    intro a ha
    rw [o₃.2 _ (by simp; exact fun h => absurd h (by revert a; decide)),
      v_setV_of_ne _ _ (by revert a; decide), v_setV_of_ne _ _ (by revert a; decide)]
  have g₆ : s₆.gpr = s.gpr := by
    show s₅.gpr = s.gpr; rw [o₅.gpr]; show s₃.gpr = s.gpr; rw [o₃.gpr]; rfl
  have m₇ : s₇.mem = s.mem := by
    show s₅.mem = s.mem; rw [o₅.mem]; show s₃.mem = s.mem; rw [o₃.mem]; rfl
  have rd₇ : s₇.rd = s.rd := by
    show s₅.rd = s.rd; rw [o₅.rd]; show s₃.rd = s.rd; rw [o₃.rd]; rfl
  have wr₇ : s₇.wr = s.wr := by
    show s₅.wr = s.wr; rw [o₅.wr]; show s₃.wr = s.wr; rw [o₃.wr]; rfl
  have sp₇ : s₇.sp = s.sp := by
    show s₅.sp = s.sp; rw [o₅.sp]; show s₃.sp = s.sp; rw [o₃.sp]; rfl
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_, m₇, rd₇, wr₇, sp₇⟩
  · simp only [tbyte, v₇]
    by_cases h15 : k / 16 = 15
    · rw [h15, show s₆.v (treg 15) = s₅.v .v7 from v_setV_self _ _ _,
        keep₅ _ (by decide), v_setV_self, tab₃ 0 (by decide),
        show (k + 16) % 256 / 16 = 0 by omega_using [h15], show (k + 16) % 256 % 16 = k % 16 by omega_using []]
    · rw [v_setV_of_ne _ _ (fun e => h15 (treg_inj _ (by omega_using [hk]) _ (by decide) e)),
        v₅ _ (by omega_using [hk]), ite_eq_left (show k / 16 < 15 by omega_using [hk, h15]),
        v_setV_of_ne _ _ ((show NotTable .v7 by decide).ne _), tab₃ _ (by omega_using [hk, h15]),
        show (k + 16) % 256 / 16 = k / 16 + 1 by omega_using [hk, h15], show (k + 16) % 256 % 16 = k % 16 by omega_using []]
  · rw [v₇, v_setV_of_ne _ _ ((show NotTable (dq 0) by decide).ne _ |>.symm),
      keep₅ _ (by decide), v_setV_of_ne _ _ (by decide), o₃.2 _ (by decide), j₂]
  · rw [v₇, v_setV_of_ne _ _ ((show NotTable negBase by decide).ne _ |>.symm),
      keep₅ _ (by decide), v_setV_of_ne _ _ (by decide), n₃]
  · simp only [s₇, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [g₆]; rfl
  · simp only [s₇, State.write, BitVec.setWidth_eq, hr, ite_false]
    rw [g₆]
  · simp only [rotRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists,
      not_and] at hr
    obtain ⟨h7, hd, hn, ht⟩ := hr
    rw [v₇, v_setV_of_ne _ _ (fun e => ht 15 (by decide) e.symm), keep₅ r (fun a ha e => ht a (by omega_using [ha]) e),
      v_setV_of_ne _ _ h7, o₃.2 r (by simp [hn]), v_setV_of_ne _ _ hd, v_setV_of_ne _ _ h7]

end VG.Proof.Rc4.AArch64

end

end

/-!
# The groups

`group_ok`: sixteen lanes and the rotation take a group with base `B` that
starts after `p` bytes to the next group, with base `B + 16`, after
`min N (p + 16 - sk)` bytes and no lanes to skip. `loop_ok`: the groups run
until the data has ended.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem lanesFrom_ok (g : Glob) (hg : DataOk g) {B p sk : Nat} (hsk : sk ≤ 15) {n : Nat} (hn : n ≤ 16)
    {s : State} (h : LaneInv g B p sk 0 s) : WP isa (lanesFrom n) s (LaneInv g B p sk n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    exact WP.seq (WP.mono (ih (by omega_using [hn])) fun t ht => lane_ok g hg hsk (by omega_using [hn]) ht)

theorem ofNat_wrap (B k : Nat) : BitVec.ofNat 8 (B + (k + 16) % 256) = BitVec.ofNat 8 (B + 16 + k) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega_using []

theorem byte_shift (x : BitVec 8) (B : Nat) : x - bB B - 16 = x - bB (B + 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (16 : BitVec 8).toNat = 16 from rfl]
  omega_using []

theorem treg_step : ∀ a < 16, treg a ∈ stepRegs := by decide

theorem group_ok (g : Glob) (hg : DataOk g) {B p sk : Nat} (hsk : sk ≤ 15) {s : State}
    (h : LaneInv g B p sk 0 s) :
    WP isa group s (LaneInv g (B + 16) (doneAt g p sk 16) 0 0) := by
  apply WP.seq (WP.mono (lanesFrom_ok g hg hsk (Nat.le_refl 16) h) fun s₁ h₁ => ?_)
  refine WP.mono (rotate_ok true h₁.prga.consts h₁.prga.j fun _ => h₁.prga.nb) fun t ⟨tab, j, nb, x8, gg, vv, m, rd, wr, sp⟩ => ?_
  have hd0 : doneAt g (doneAt g p sk 16) 0 0 = doneAt g p sk 16 := by
    have := h₁.data.le; simp only [doneAt] at this ⊢; omega_using []
  let q := doneAt g p sk 16
  have notRot : ∀ r, r ∉ rotRegs → r ∉ stepRegs ∨ r = negBase → True := fun _ _ _ => trivial
  exact {
    prga := by
      rw [hd0]
      refine ⟨fun k hk => ?_, ?_, ?_, ?_⟩
      · rw [tab k hk, h₁.prga.table _ (by omega_using []), ofNat_wrap]
      · rw [j, byte_shift]
      · simp only [ite_true] at nb; rw [nb, byte_shift]
      · exact h₁.prga.consts.congr fun r hr => vv r (by
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    data := by
      rw [hd0]
      exact ⟨h₁.data.le, by rw [gg _ (by decide), h₁.data.x1], by rw [gg _ (by decide), h₁.data.x2],
        fun k hk => by rw [m]; exact h₁.data.bytes k hk, by rw [m]; exact h₁.data.frame⟩
    x5 := by rw [gg _ (by decide), h₁.x5]; congr 1; omega_using [hsk]
    x8 := by
      rw [x8, h₁.x8, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
    next := by
      rw [hd0]
      intro hlt
      obtain ⟨hi, hsi⟩ := h₁.next hlt
      rw [show max 16 sk = 16 by omega_using [hsk]] at hi hsi
      refine ⟨by rw [hi]; simp, ?_⟩
      rw [vv _ (by decide), hsi, show max 0 0 = 0 from rfl, tab 0 (by decide)]
    kept := ⟨fun r a b c d e f => by rw [gg r f, h₁.kept.gpr r a b c d e f], rd.trans h₁.kept.rd,
      wr.trans h₁.kept.wr, sp.trans h₁.kept.sp⟩
    vkept := fun r hr hn => by
      rw [vv r (by
        simp only [rotRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists, not_and]
        refine ⟨fun e => hr (by rw [e]; decide), fun e => hr (by rw [e]; decide), hn,
          fun a ha e => hr (e ▸ treg_step a ha)⟩), h₁.vkept r hr hn] }

/-- A group about to start, `m` bytes before the end. -/
def LoopInv (g : Glob) (m : Nat) (s : State) : Prop :=
  ∃ B p sk, B % 16 = 0 ∧ m = g.N - p ∧ p < g.N ∧ sk ≤ 15 ∧ LaneInv g B p sk 0 s

/-- The data has ended. -/
def LoopDone (g : Glob) (s : State) : Prop := ∃ B sk, B % 16 = 0 ∧ LaneInv g B g.N sk 0 s

theorem loop_ok (g : Glob) (hg : DataOk g) (m : Nat) {s : State} (h : LoopInv g m s) :
    WP isa (.loop group (.nonzero .x .x2)) s (LoopDone g) := by
  refine WP.loop (M := isa) (LoopInv g) ?_ m s h
  intro m s ⟨B, p, sk, hB, hm, hp, hsk, h⟩
  refine WP.mono (group_ok g hg hsk h) fun t ht => ?_
  have hfit := hg.fit
  let q := doneAt g p sk 16
  have hd0 : doneAt g q 0 0 = q := by
    have := ht.data.le; simp only [doneAt, q] at this ⊢; omega_using []
  have hq : q ≤ g.N := by have := ht.data.le; rw [hd0] at this; exact this
  have x2 : t.gpr .x2 = BitVec.ofNat 64 (g.N - q) := by rw [ht.data.x2, hd0]
  have flag := eval_nonzero' t .x2 x2 (by omega_using [hfit])
  by_cases hend : q = g.N
  · left
    exact ⟨by rw [flag]; simp [hend], B + 16, 0, by omega_using [hB], hend ▸ ht⟩
  · right
    exact ⟨by rw [flag]; simp; omega_using [hq, hend], g.N - q, by simp only [doneAt, q] at hend ⊢; omega_using [hm, hp, hsk],
      B + 16, q, 0, by omega_using [hB], rfl, by omega_using [hq, hend], by decide, ht⟩

end VG.Proof.Rc4.AArch64
