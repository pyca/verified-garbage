module

public import VerifiedGarbage.Proof.Camellia.Arm.Group
import VerifiedGarbage.Proof.Camellia.Arm.Copy
import VerifiedGarbage.Proof.Camellia.Arm.Crypt8
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Camellia ECB on ARMv7: the whole function

`ecb_wp`: with the working space as a stack argument (`ecbArm`), `ecb dir`
saves the callee-saved registers, builds the table of subkeys for 18 or 24
rounds in the order `dir` uses them, transforms the blocks a group at a
time (`dataGroup_wp`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Proof.Camellia (DInv outF blocksAt_of_dinv ecb_eq outF_spec schedWords_getD dirPerm dirPerm_lt
  wordAt_frame)
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS)

/-- The specification's direction. -/
def specDir : Dir → Spec.Camellia.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on ARMv7 with its working space at the first stack argument. -/
def ecbArm (dir : Dir) : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 272⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 16 * (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 4 * slots⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧ args.Disjoint data ∧ args.Disjoint scratch ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      (s.gpr .r0).toNat + 272 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 4 * slots ≤ 2 ^ 32 ∧ ((s.gpr .r1).toNat = 18 ∨ (s.gpr .r1).toNat = 24)
  post s s' :=
    Spec.Camellia.blocksAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Camellia.ecb (Spec.Camellia.subkeysAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (specDir dir)
        (Spec.Camellia.blocksAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- The order of the subkeys in the table, for each direction. -/
def permOf (dir : Dir) : Nat → Nat → Nat := dirPerm (specDir dir)

theorem exec_movR (s : State) (d n : Reg) : exec (movR d n) s = some (s.setReg d (s.gpr n)) := by
  simp [movR, exec, Op2.eval]

/-- The subkeys the loop bitslices, for `g` groups. -/
def cntOf : Dir → Nat → Nat
  | .encrypt, g => 8 * g + 2
  | .decrypt, g => 8 * g - 2

/-- How far `groupConsts` moves `r12`. -/
def r12Of : Dir → Nat → Nat
  | .encrypt, _ => 0
  | .decrypt, g => 64 * g

theorem groupConsts_ok (dir : Dir) {g : Nat} (hg : g = 3 ∨ g = 4) (s : State) :
    ∃ s', runBlock isa (groupConsts dir g) s = some s' ∧ s'.gpr .lr = BitVec.ofNat 32 (cntOf dir g) ∧
      s'.gpr u7 = s.gpr u7 + BitVec.ofNat 32 (r12Of dir g) ∧
      (∀ r, r ≠ .lr → r ≠ u7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  cases dir
  · refine ⟨s.setReg .lr (BitVec.ofNat 32 (8 * g + 2)), ?_, RegUpd.gpr_setReg_self _ _ _, ?_,
      fun r h1 _ => RegUpd.gpr_setReg_of_ne _ _ h1, rfl, rfl, rfl, rfl⟩
    · rw [groupConsts, runBlock_cons, exec_movImm (by rcases hg with rfl | rfl <;> decide), runStep_some,
        runBlock_nil]
    · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; simp [r12Of]
  · let s₁ := s.setReg .r12 (s.gpr .r12 + BitVec.ofNat 32 (64 * g))
    refine ⟨s₁.setReg .lr (BitVec.ofNat 32 (8 * g - 2)), ?_, RegUpd.gpr_setReg_self _ _ _, ?_,
      fun r h1 h2 => by rw [RegUpd.gpr_setReg_of_ne _ _ h1]; exact RegUpd.gpr_setReg_of_ne _ _ h2, rfl, rfl, rfl,
      rfl⟩
    · rw [groupConsts, runBlock_cons, exec_addImm (by rcases hg with rfl | rfl <;> decide), runStep_some,
        runBlock_cons, exec_movImm (by rcases hg with rfl | rfl <;> decide), runStep_some, runBlock_nil]
    · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), show u7 = Reg.r12 from rfl, RegUpd.gpr_setReg_self]; rfl

/-- `KeysPost` from the state after `groupConsts`, which wrote only `lr` and `r12`. -/
theorem KeysPost.of_consts {s₀ s₁ s : State} {b sched : BitVec 32} {g : Nat} {perm : Nat → Nat}
    (h : KeysPost s₁ b sched g perm s) (hm : s₁.mem = s₀.mem) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (ho : ∀ r, r ≠ .lr → r ≠ u7 → s₁.gpr r = s₀.gpr r) : KeysPost s₀ b sched g perm s :=
  ⟨h.pre, fun i hi => hm ▸ h.ent i hi, hm ▸ h.frame,
    fun r h1 h2 => by
      rw [h.regs r h1 h2, ho r (fun h => h1 (by subst h; decide)) (fun h => h1 (by subst h; decide))],
    h.rd.trans hrd, h.wr.trans hwr, h.kpos⟩

/-- The postwhitening's address, to `lr`. -/
theorem endAddr_ok {s : State} {b : BitVec 32} {g : Nat} (hk : AtEntry s b (8 * g + 2)) :
    ∃ s', runBlock isa endAddr s = some s' ∧ s'.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) ∧
      s'.mem = s.mem ∧ (∀ r, r ≠ .lr → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨s.setReg .lr (s.gpr kp - 128), ?_, ?_, rfl, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl⟩
  · simp only [endAddr, runBlock_cons, exec, Op2.eval, show encodable 128 = true by decide, ↓reduceIte,
      Option.map_some, runStep_some, runBlock_nil]
  · rw [RegUpd.gpr_setReg_self, hk, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, ← BitVec.sub_eq_add_neg, VG.Offset.ofNat_sub_ofNat (by rw [keySlot_eq]; omega_arith),
      show 4 * keySlot + 64 * (8 * g + 2) - 128 = 4 * keySlot + 512 * g by rw [keySlot_eq]; omega_arith]

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : BitVec 32} {g : Nat} (hg : g = 3 ∨ g = 4)
    (hz : isa.eval .eq s₀ = some (decide (g = 3))) (hk : KeyPre s₀ b sched) (hr : s₀.gpr u7 = sched) :
    WP isa (keys dir) s₀ fun s => ∃ s₁, KeysPost s₀ b sched g (permOf dir g) s₁ ∧
      s.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) ∧ s.mem = s₁.mem ∧
      (∀ r, r ≠ .lr → s.gpr r = s₁.gpr r) ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₀.sp := by
  unfold keys
  refine WP.seq (WP.mono (M := isa) (Q := fun s₁ => s₁.gpr .lr = BitVec.ofNat 32 (cntOf dir g) ∧
      s₁.gpr u7 = s₀.gpr u7 + BitVec.ofNat 32 (r12Of dir g) ∧
      (∀ r, r ≠ .lr → r ≠ u7 → s₁.gpr r = s₀.gpr r) ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.sp = s₀.sp)
    (WP.ite (decide (g = 3)) hz (fun h => ?_) (fun h => ?_)) fun s₁ h₁ => ?_)
  · obtain rfl : g = 3 := by simpa using h
    obtain ⟨s', e', h'⟩ := groupConsts_ok dir hg s₀
    exact WP.of_runBlock ⟨s', e', h'⟩
  · obtain rfl : g = 4 := by simp at h; omega_arith
    obtain ⟨s', e', h'⟩ := groupConsts_ok dir hg s₀
    exact WP.of_runBlock ⟨s', e', h'⟩
  obtain ⟨l₁, r₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := h₁
  have hk₁ : KeyPre s₁ b sched := hk.congr (o₁ _ (by decide) (by decide)) rd₁ wr₁
  have post : ∀ s₂, KeysPost s₁ b sched g (permOf dir g) s₂ → s₂.sp = s₁.sp →
      WP isa (.block endAddr) s₂ fun s => ∃ s₂, KeysPost s₀ b sched g (permOf dir g) s₂ ∧
        s.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) ∧ s.mem = s₂.mem ∧
        (∀ r, r ≠ .lr → s.gpr r = s₂.gpr r) ∧ s.rd = s₂.rd ∧ s.wr = s₂.wr ∧ s.sp = s₀.sp := by
    intro s₂ h sp₂
    obtain ⟨s', e', l', m', g', rd', wr', sp'⟩ := endAddr_ok h.kpos
    exact WP.of_runBlock ⟨s', e', s₂, h.of_consts m₁ rd₁ wr₁ o₁, l', m', g', rd', wr', sp'.trans (sp₂.trans sp₁)⟩
  cases dir
  · exact WP.seq (WP.mono (WP.sp (encKeys_wp hg hk₁ (by rw [r₁, hr]; simp [r12Of]) l₁)) fun s h => post s h.1 h.2)
  · exact WP.seq (WP.mono (WP.sp (decKeys_wp hg hk₁ (by rw [r₁, hr]; simp only [r12Of]; congr 2; omega_arith) l₁))
      fun s h => post s h.1 h.2)

theorem dataLoop_wp {s₀ : State} {b D : BitVec 32} {n g : Nat} {E : Nat → BitVec 64} (hp : GPre s₀ b D n)
    (hg : g = 3 ∨ g = 4) {s : State} (hi : GInv s₀ b D n g E 0 s) :
    WP isa (.loop Impl.Camellia.Arm.group .ne) s (GDone s₀ b D n g E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 8 * k ∧ GInv s₀ b D n g E k s) (fun m s hs => ?_) n s
    ⟨0, by omega_arith, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hg hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_ne s').trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_ne s').trans (by rw [z]; rfl), n - 8 * (k + 1),
      by have := d.lt; have := hk.lt; omega_arith, k + 1, rfl, d⟩

/-- The prologue: the scratch buffer's address from the stack to `sb`, the
registers saved, the schedule's pointer in `r12`, `rounds` compared with 18,
the data pointer in `r1` and `n` in `r2`. -/
theorem prologue_ok {s₀ : State} {b : BitVec 32} (hb : stackArg s₀ 0 = b) (hw : ScrIn s₀.wr b)
    (ha : (⟨stackArgAddr s₀ 0, 4⟩ : Region) ∈ s₀.rd) :
    ∃ s, runBlock isa (([.ldrSp .r12 0] : List Instr) ++ saveRegs .r12 ++
        ([movR sb .r12, movR .r12 .r0, .cmp .r1 (.imm 18), movR .r1 .r2, movR .r2 .r3] : List Instr)) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .r12 = s₀.gpr .r0 ∧ s.gpr .r1 = s₀.gpr .r2 ∧ s.gpr .r2 = s₀.gpr .r3 ∧
      s.z = (s₀.gpr .r1 - 18 == 0) ∧ Saved s₀ b s.mem ∧ Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s.mem ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  have hin : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 0)) 4 :=
    ⟨_, List.mem_append_left _ ha, Region.contains_self _ _⟩
  let u := s₀.setReg .r12 b
  have e₀ : exec (.ldrSp .r12 0) s₀ = some u := by
    subst hb
    simp only [exec, show (0 : Nat) < 4096 by decide, ↓reduceIte, State.load32, hin, Option.map_some]
    rfl
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, sp₂, f₂, -⟩ := save_ok (s := u) (base := .r12) hw
    (RegUpd.gpr_setReg_self _ _ _)
  let s₃ := s₂.setReg sb (s₂.gpr .r12)
  let s₄ := s₃.setReg .r12 (s₃.gpr .r0)
  let s₅ := subFlags s₄ (s₄.gpr .r1) 18
  let s₆ := s₅.setReg .r1 (s₅.gpr .r2)
  let s₇ := s₆.setReg .r2 (s₆.gpr .r3)
  have e₅ : exec (.cmp .r1 (.imm 18)) s₄ = some s₅ := by
    simp only [exec, Op2.eval, show encodable (18 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
    rfl
  have hu : ∀ r, r ≠ .r12 → u.gpr r = s₀.gpr r := fun r h => RegUpd.gpr_setReg_of_ne _ _ h
  refine ⟨s₇, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
  · rw [runBlock_app, runBlock_app, runBlock_cons, e₀, runStep_some, runBlock_nil, Option.bind_some, e₂,
      Option.bind_some, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR, runStep_some,
      runBlock_cons, e₅, runStep_some, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR,
      runStep_some, runBlock_nil]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide), subFlags_gpr,
      RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self, g₂, RegUpd.gpr_setReg_self]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide), subFlags_gpr,
      RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂, hu _ (by decide)]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self, subFlags_gpr,
      RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂, hu _ (by decide)]
  · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide), subFlags_gpr,
      RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂, hu _ (by decide)]
  · rw [RegUpd.z_setReg, RegUpd.z_setReg, subFlags_z, RegUpd.gpr_setReg_of_ne _ _ (by decide),
      RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂, hu _ (by decide)]
  · show s₂.mem.readW _ 32 = _
    rw [sv₂ i hi, hu _ (sreg_ne_r12 i hi)]
  · exact f₂
  · exact rd₂
  · exact wr₂
  · exact sp₂

/-! ## The whole function -/

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbArm dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (ecbArm dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, -, -, -, fitK, fitD, fitB, hR⟩ := hp
  generalize hb : stackArg s₀ 0 = b at hwr dSS dDS fitB
  let D := s₀.gpr .r2
  let n := (s₀.gpr .r3).toNat
  let sched := s₀.gpr .r0
  let R := (s₀.gpr .r1).toNat
  have hwS : ScrIn s₀.wr b := ⟨by rw [hwr]; simp, fitB⟩
  have hwD : (⟨State.addr D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨State.addr sched, 272⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  have hrA : (⟨stackArgAddr s₀ 0, 4⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have hfitB := fitB
  rw [slots_eq] at hfitB
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r12₁, r1₁, r2₁, z₁, sv₁, f₁, rd₁, wr₁, sp₁⟩ := prologue_ok hb hwS hrA
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : KeyPre s₁ b sched :=
    ⟨b₁, ⟨by rw [wr₁]; exact hwS.mem, fitB⟩, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  have hz₁ : s₁.z = decide (R = 18) := by
    rw [z₁, show s₀.gpr .r1 = BitVec.ofNat 32 R by simp [R],
      show (18 : BitVec 32) = BitVec.ofNat 32 18 from rfl, ofNat32_sub_beq (by omega_arith) (by decide)]
  -- The table.
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega_arith
  let KQ : State → Prop := fun s => ∃ s', KeysPost s₁ b sched g (permOf dir g) s' ∧
      s.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) ∧ s.mem = s'.mem ∧
      (∀ r, r ≠ .lr → s.gpr r = s'.gpr r) ∧ s.rd = s'.rd ∧ s.wr = s'.wr ∧ s.sp = s₁.sp
  refine WP.seq (WP.mono (M := isa) (Q := KQ) (keys_wp dir hg ((eval_eq s₁).trans (by
      rw [hz₁]; exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩))) hk₁ r12₁)
    fun s₂ ⟨s₂', k₂, lr₂, m₂, g₂, rd₂', wr₂', sp₂⟩ => ?_)
  -- The scratch buffer and the data before the groups.
  let E : Nat → BitVec 64 := fun i => (schedWords s₀.mem (State.addr sched) R).getD (permOf dir g i) 0
  have f₀₂ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₂.mem := by
    rw [m₂]
    exact f₁.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact table_sub_scr fitB⟩)
  have base₂ : s₂.gpr sb = b := by rw [g₂ _ (by decide)]; exact k₂.pre.base
  have hE : ∀ i < 8 * g + 2,
      Spec.Camellia.wordAt s₁.mem (State.addr sched + BitVec.ofNat 64 (8 * permOf dir g i)) = E i :=
    fun i hi => by
      have hp : permOf dir g i < 8 * g + 2 := dirPerm_lt (specDir dir) hi
      rw [show E i = _ from schedWords_getD s₀.mem (State.addr sched) (R := R)
        (by simp only [Spec.Camellia.scheduleLength]; omega_arith)]
      exact hk₁.wordAt_eq f₁ (by omega_arith)
  have sc₂ : ScrOk s₀ b g E s₂.mem := by
    refine ⟨fun i hi => by rw [m₂]; exact hE i hi ▸ k₂.ent i hi, fun i hi => ?_⟩
    rw [← sv₁ i hi, m₂]
    refine slot_keep fitB (lo := savedSlot) (hi := slots) (Nat.le_refl _) k₂.frame (fun r hr => ?_)
      (Nat.le_add_right _ _) (by rw [savedSlot_eq, slots_eq]; omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    simp only [tableRegion]
    rw [VG.Arm.addr_add (by rw [keySlot_eq]; omega_arith)]
    exact VG.Offset.disjoint _ (by rw [savedSlot_eq, keySlot_eq]; omega_arith) (by rw [savedSlot_eq, slots_eq]; omega_arith)
      (by rw [keySlot_eq]; omega_arith)
  have data₂ : ∀ i < 16 * n, s₂.mem (State.addr D + BitVec.ofNat 64 i) = s₀.mem (State.addr D + BitVec.ofNat 64 i) :=
    fun i hi => f₀₂.bytes (R := ⟨State.addr D, 16 * n⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS) (by simp only; omega_arith) hi
  have fr₂ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s₂.mem :=
    f₀₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have rd₂ : s₂.rd = s₀.rd := by rw [rd₂', k₂.rd, rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [wr₂', k₂.wr, wr₁]
  have sp₂' : s₂.sp = s₀.sp := by rw [sp₂, sp₁]
  have r1₂ : s₂.gpr .r1 = D := by
    rw [g₂ _ (by decide), k₂.regs _ (by decide) (by decide), r1₁]
  have r2₂ : s₂.gpr .r2 = BitVec.ofNat 32 n := by
    rw [g₂ _ (by decide), k₂.regs _ (by decide) (by decide), r2₁]; simp [n]
  -- Any blocks?
  let s₄ := subFlags s₂ (s₂.gpr .r2) 0
  have e₄ : runBlock isa [.cmp .r2 (.imm 0)] s₂ = some s₄ := by
    rw [runBlock_cons, show exec (.cmp .r2 (.imm 0)) s₂ = some s₄ by
      simp only [exec, Op2.eval, show encodable (0 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
      rfl,
      runStep_some, runBlock_nil]
  have hz₄ : s₄.z = decide (n = 0) := by
    show (s₂.gpr .r2 - 0 == 0) = _
    rw [r2₂, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    have : n < 2 ^ 32 := (s₀.gpr .r3).isLt
    bv_omega
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have base₄ : s₄.gpr sb = b := base₂
  have mem₄ : s₄.mem = s₂.mem := rfl
  have rd₄ : s₄.rd = s₀.rd := rd₂
  have wr₄ : s₄.wr = s₀.wr := wr₂
  have sp₄ : s₄.sp = s₀.sp := sp₂'
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n g E)
    (WP.ite (decide (n = 0)) ((eval_eq s₄).trans (by rw [hz₄])) (fun h0 => ?_) (fun h0 => ?_))
    fun s₅ d₅ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₄, mem₄ ▸ sc₂, fun i hi => by omega_arith, mem₄ ▸ fr₂, rd₄, wr₄, sp₄⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitD⟩ hg ⟨base₄, by show s₂.gpr .r1 = _; rw [r1₂]; simp,
      by show s₂.gpr .r2 = _; rw [r2₂, Nat.mul_zero, Nat.sub_zero], by omega_arith, lr₂,
      mem₄ ▸ sc₂, fun i hi => ?_, mem₄ ▸ fr₂, rd₄, wr₄, sp₄⟩
    rw [mem₄, data₂ i hi, ite_eq_right (by omega_arith)]
  -- The epilogue.
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := movR_ok s₅ .r12 sb
  obtain ⟨s₇, e₇, rg₇, -, m₇, -, -, -⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [wr₆, d₅.wr]; exact hwS)
    (by rw [r₆, d₅.base]) (by rw [m₆]; exact d₅.scr.saved)
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_app, e₆, Option.bind_some, e₇], rg₇, ?_⟩
  have hd₇ : DInv s₀.mem s₇.mem (State.addr D) n n (outF s₀.mem (State.addr D) g E) := fun i hi => by
    rw [m₇, m₆]; exact d₅.data i hi
  show Spec.Camellia.blocksAt s₇.mem (State.addr D) n = _
  rw [blocksAt_of_dinv hd₇, ecb_eq]
  simp only [Spec.Camellia.blocksAt, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  subst hgR
  exact outF_spec (specDir dir) s₀.mem (State.addr sched) (State.addr D) hR j

end VG.Proof.Camellia.Arm
