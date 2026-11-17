module

public import VerifiedGarbage.Proof.Camellia.Arm.Ecb
public import VerifiedGarbage.Proof.Camellia.Arm.Verified
public import VerifiedGarbage.Proof.Camellia.Arm.ModeCore
public import VerifiedGarbage.Proof.Modes.Arm.SeqKeyed
public import VerifiedGarbage.Impl.Camellia.Arm.Keyed
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Camellia.Arm.Ecb
meta import VerifiedGarbage.Proof.Camellia.Arm.Verified
meta import VerifiedGarbage.Proof.Camellia.Arm.ModeCore
meta import VerifiedGarbage.Proof.Modes.Arm.SeqKeyed
meta import VerifiedGarbage.Impl.Camellia.Arm.Keyed
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Camellia ECB on ARMv7 from a table built once

`ecbKeys dir` and `ecbKeyed` (`Impl/Camellia/Arm/Keyed.lean`) are the two
halves of `ecb dir`, and so are their proofs of `ecb_wp`'s
(`Proof/Camellia/Arm/Ecb.lean`): `ecbKeys_wp` is its table (`keys_wp`),
which leaves `KeysIn dir`, the subkeys of the schedule's bytes in the
entries of the table in the order `dir` uses them; and `ecbKeyed_wp` its
data loop (`dataLoop_wp`), from `KeysIn dir`, which it keeps: the contract
`ecbKeyedArm dir` is `ecbArm dir` with `KeysIn dir` before and after. Both
are constant time by the taint analysis, as `ecb dir` is
(`Proof/Camellia/Arm/Verified.lean`).

`scrSpec dir` is what the modes need of `ecb dir` with its working space as a
stack argument (`Proof.Modes.Arm.CoreSpec`), and `keyedSpec dir` what they
need of the two functions that split it (`Proof.Modes.Arm.KeyedSpec`,
`Proof/Modes/Arm/SeqKeyed.lean`).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Proof.Camellia (DInv outF blocksAt_of_dinv ecb_eq outF_spec schedWords schedWords_getD dirPerm_lt
  wordAt_frame)
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS)
open VG.Impl.Modes.Arm (Core)
open VG.Proof.Modes.Arm (CoreSpec KeyedSpec EcbPreS KeysPre)
open VG.Proof.Modes (blocksOf)

/-! ## The table in the working space -/

/-- The table of `dir` for `R` rounds of the schedule at `sched`, in the
scratch buffer at `b`: entry `e` holds the subkey `dir` uses there. -/
def KeysIn (dir : Dir) (m : Mem) (b sched : BitVec 32) (R : Nat) : Prop :=
  ∀ e < 8 * (R / 6) + 2,
    EntryOk m b e ((schedWords m (State.addr sched) R).getD (permOf dir (R / 6) e) 0)

/-- A subkey of the schedule, outside a frame. -/
theorem schedWord_frame {rs : List Region} {m m' : Mem} {sched : BitVec 32} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨State.addr sched, 272⟩ r) {R : Nat} (hR : R = 18 ∨ R = 24) {i : Nat}
    (hi : i < 8 * (R / 6) + 2) :
    (schedWords m' (State.addr sched) R).getD i 0 = (schedWords m (State.addr sched) R).getD i 0 := by
  rw [schedWords_getD _ _ (by simp only [Spec.Camellia.scheduleLength]; exact hi),
    schedWords_getD _ _ (by simp only [Spec.Camellia.scheduleLength]; exact hi)]
  refine wordAt_frame hf fun r hr => (hd r hr).sub_left (VG.Offset.sub_base _ ?_)
  rcases hR with rfl | rfl <;> omega_arith

/-- The table and the schedule, outside a frame. -/
theorem KeysIn.frame {dir : Dir} {rs : List Region} {m m' : Mem} {b sched : BitVec 32} {R : Nat}
    (h : KeysIn dir m b sched R) (hR : R = 18 ∨ R = 24) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    (hf : Frame rs m m') (hk : ∀ r ∈ rs, Region.Disjoint ⟨State.addr sched, 272⟩ r)
    (hs : ∀ r ∈ rs, Region.Disjoint ⟨State.addr b, 4 * slots⟩ r) : KeysIn dir m' b sched R := by
  intro e he
  rw [schedWord_frame hf hk hR (i := permOf dir (R / 6) e) (dirPerm_lt (specDir dir) he)]
  refine (h e he).congr fun j hj => ?_
  refine slot_keep hfit (lo := 0) (hi := slots) (Nat.le_refl _) hf (fun r hr => ?_) (Nat.zero_le _)
    (by rw [keySlot_eq, slots_eq]; rcases hR with rfl | rfl <;> omega_arith)
  rw [show slotsRegion b 0 slots = ⟨State.addr b, 4 * slots⟩ by
    rw [slotsRegion, Nat.mul_zero, Nat.sub_zero]; exact congrArg (Region.mk · _) (BitVec.add_zero _)]
  exact hs r hr

/-! ## `ecbKeys` -/

/-- `ecbKeys dir` on `(schedule = r0, rounds = r1, scratch = r2)`: the table
of `dir` in the scratch buffer. -/
def ecbKeysArm (dir : Dir) : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 272⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 4 * slots⟩
    s.rd = [sched] ∧ s.wr = [scratch] ∧ sched.Disjoint scratch ∧ (s.gpr .r0).toNat + 272 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 4 * slots ≤ 2 ^ 32 ∧ ((s.gpr .r1).toNat = 18 ∨ (s.gpr .r1).toNat = 24)
  post s s' := KeysIn dir s'.mem (s.gpr .r2) (s.gpr .r0) (s.gpr .r1).toNat
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

/-- The prologue of `ecbKeys`: the scratch buffer's address to `sb`, the
registers saved, the schedule's pointer in `r12`, `rounds` compared with 18. -/
theorem keysPrologue_ok {s₀ : State} {b : BitVec 32} (hb : s₀.gpr .r2 = b) (hw : ScrIn s₀.wr b) :
    ∃ s, runBlock isa (([movR .r12 .r2] : List Instr) ++ saveRegs .r12 ++
        ([movR sb .r12, movR .r12 .r0, .cmp .r1 (.imm 18)] : List Instr)) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .r12 = s₀.gpr .r0 ∧ s.z = (s₀.gpr .r1 - 18 == 0) ∧ Saved s₀ b s.mem ∧
      Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  let u := s₀.setReg .r12 (s₀.gpr .r2)
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, sp₂, f₂, -⟩ := save_ok (s := u) (base := .r12) hw
    ((RegUpd.gpr_setReg_self _ _ _).trans hb)
  let s₃ := s₂.setReg sb (s₂.gpr .r12)
  let s₄ := s₃.setReg .r12 (s₃.gpr .r0)
  let s₅ := subFlags s₄ (s₄.gpr .r1) 18
  obtain e₅ : exec (.cmp .r1 (.imm 18)) s₄ = some s₅ := by
    simp only [exec, Op2.eval, show encodable (18 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
    rfl
  obtain hu : ∀ r, r ≠ .r12 → u.gpr r = s₀.gpr r := fun r h => RegUpd.gpr_setReg_of_ne _ _ h
  refine ⟨s₅, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
  · rw [runBlock_app, runBlock_app, runBlock_cons, exec_movR, runStep_some, runBlock_nil, Option.bind_some, e₂,
      Option.bind_some, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR, runStep_some,
      runBlock_cons, e₅, runStep_some, runBlock_nil]
  · rw [subFlags_gpr, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self, g₂,
      RegUpd.gpr_setReg_self, hb]
  · rw [subFlags_gpr, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂, hu _ (by decide)]
  · rw [subFlags_z, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂,
      hu _ (by decide)]
  · show s₂.mem.readW _ 32 = _
    rw [sv₂ i hi, hu _ (sreg_ne_r12 i hi)]
  · exact f₂
  · exact rd₂
  · exact wr₂
  · exact sp₂

/-- The saved registers' slots are outside the table. -/
theorem saved_table {s₀ : State} {b : BitVec 32} {m m' : Mem} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    (hf : Frame [tableRegion b] m m') (h : Saved s₀ b m) : Saved s₀ b m' := by
  intro i hi
  have hfitB := hfit
  rw [slots_eq] at hfitB
  rw [← h i hi]
  refine slot_keep hfit (lo := savedSlot) (hi := slots) (Nat.le_refl _) hf (fun r hr => ?_)
    (Nat.le_add_right _ _) (by rw [savedSlot_eq, slots_eq]; omega_arith)
  simp only [List.mem_singleton] at hr; subst hr
  simp only [tableRegion]
  rw [VG.Arm.addr_add (by rw [keySlot_eq]; omega_arith)]
  exact VG.Offset.disjoint _ (by rw [savedSlot_eq, keySlot_eq]; omega_arith) (by rw [savedSlot_eq, slots_eq]; omega_arith)
    (by rw [keySlot_eq]; omega_arith)

theorem ecbKeys_wp (dir : Dir) {s₀ : State} (hp : (ecbKeysArm dir).pre s₀) :
    WP isa (ecbKeys dir) s₀ fun s' =>
      (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (ecbKeysArm dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dSS, fitK, fitB, hR⟩ := hp
  generalize hb : s₀.gpr .r2 = b at hwr dSS fitB
  let sched := s₀.gpr .r0
  let R := (s₀.gpr .r1).toNat
  obtain hwS : ScrIn s₀.wr b := ⟨by rw [hwr]; simp, fitB⟩
  obtain hrK : (⟨State.addr sched, 272⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  unfold ecbKeys
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r12₁, z₁, sv₁, f₁, rd₁, wr₁, sp₁⟩ := keysPrologue_ok hb hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain hk₁ : KeyPre s₁ b sched :=
    ⟨b₁, ⟨by rw [wr₁]; exact hwS.mem, fitB⟩, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  obtain hz₁ : s₁.z = decide (R = 18) := by
    rw [z₁, show s₀.gpr .r1 = BitVec.ofNat 32 R by simp [R],
      show (18 : BitVec 32) = BitVec.ofNat 32 18 from rfl, ofNat32_sub_beq (by omega_arith) (by decide)]
  -- The table.
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  obtain hg : g = 3 ∨ g = 4 := by omega_arith
  refine WP.seq (WP.mono (keys_wp dir hg ((eval_eq s₁).trans (by
      rw [hz₁]; exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩))) hk₁ r12₁)
    fun s₂ ⟨s₂', k₂, _, m₂, g₂, _, wr₂', _⟩ => ?_)
  -- The epilogue.
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := movR_ok s₂ .r12 sb
  obtain ⟨s₇, e₇, rg₇, -, m₇, -, -, -⟩ := restore_ok (s₀ := s₀) (b := b)
    (by rw [wr₆, wr₂', k₂.wr, wr₁]; exact hwS)
    (by rw [r₆, g₂ _ (by decide)]; exact k₂.pre.base)
    (by rw [m₆, m₂]; exact saved_table fitB k₂.frame sv₁)
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_app, e₆, Option.bind_some, e₇], rg₇, ?_⟩
  show KeysIn dir s₇.mem (s₀.gpr .r2) sched R
  rw [hb]
  intro e he
  rw [hgR] at he ⊢
  obtain hpm : permOf dir g e < 8 * g + 2 := dirPerm_lt (specDir dir) he
  rw [schedWords_getD _ _ (by simp only [Spec.Camellia.scheduleLength]; omega_arith), m₇, m₆, m₂,
    hk₁.wordAt_eq (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact table_sub_scr fitB⟩) (by omega_arith)]
  exact k₂.ent e he

/-! ## `ecbKeyed` -/

/-- `ecbKeyed` on `ecb dir`'s arguments, with the table of `dir` in the
working space: `ecbArm dir`, with the table before and after. -/
def ecbKeyedArm (dir : Dir) : Contract isa where
  pre s := (ecbArm dir).pre s ∧ KeysIn dir s.mem (stackArg s 0) (s.gpr .r0) (s.gpr .r1).toNat
  post s s' := (ecbArm dir).post s s' ∧ KeysIn dir s'.mem (stackArg s 0) (s.gpr .r0) (s.gpr .r1).toNat
  pub := (ecbArm dir).pub

/-- The prologue of `ecbKeyed`: the scratch buffer's address from the stack
to `sb`, the registers saved, `rounds` compared with 18, the data pointer in
`r1` and `n` in `r2`; the slots below the saved registers' are as they were. -/
theorem keyedPrologue_ok {s₀ : State} {b : BitVec 32} (hb : stackArg s₀ 0 = b) (hw : ScrIn s₀.wr b)
    (ha : (⟨stackArgAddr s₀ 0, 4⟩ : Region) ∈ s₀.rd) :
    ∃ s, runBlock isa (([.ldrSp .r12 0] : List Instr) ++ saveRegs .r12 ++
        ([movR sb .r12, .cmp .r1 (.imm 18), movR .r1 .r2, movR .r2 .r3] : List Instr)) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .r1 = s₀.gpr .r2 ∧ s.gpr .r2 = s₀.gpr .r3 ∧
      s.z = (s₀.gpr .r1 - 18 == 0) ∧ Saved s₀ b s.mem ∧ Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s.mem ∧
      (∀ k, k < savedSlot → s.mem.readW (wordAddr b k) 32 = s₀.mem.readW (wordAddr b k) 32) ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  obtain hin : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 0)) 4 :=
    ⟨_, List.mem_append_left _ ha, Region.contains_self _ _⟩
  let u := s₀.setReg .r12 b
  obtain e₀ : exec (.ldrSp .r12 0) s₀ = some u := by
    subst hb
    simp only [exec, show (0 : Nat) < 4096 by decide, ↓reduceIte, State.load32, hin, Option.map_some]
    rfl
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, sp₂, f₂, lo₂⟩ := save_ok (s := u) (base := .r12) hw
    (RegUpd.gpr_setReg_self _ _ _)
  let s₃ := s₂.setReg sb (s₂.gpr .r12)
  let s₅ := subFlags s₃ (s₃.gpr .r1) 18
  let s₆ := s₅.setReg .r1 (s₅.gpr .r2)
  let s₇ := s₆.setReg .r2 (s₆.gpr .r3)
  obtain e₅ : exec (.cmp .r1 (.imm 18)) s₃ = some s₅ := by
    simp only [exec, Op2.eval, show encodable (18 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
    rfl
  obtain hu : ∀ r, r ≠ .r12 → u.gpr r = s₀.gpr r := fun r h => RegUpd.gpr_setReg_of_ne _ _ h
  refine ⟨s₇, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [runBlock_app, runBlock_app, runBlock_cons, e₀, runStep_some, runBlock_nil, Option.bind_some, e₂,
      Option.bind_some, runBlock_cons, exec_movR, runStep_some, runBlock_cons, e₅, runStep_some,
      runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR, runStep_some, runBlock_nil]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide), subFlags_gpr,
      RegUpd.gpr_setReg_self, g₂, RegUpd.gpr_setReg_self]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self, subFlags_gpr,
      RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂, hu _ (by decide)]
  · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide), subFlags_gpr,
      RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂, hu _ (by decide)]
  · rw [RegUpd.z_setReg, RegUpd.z_setReg, subFlags_z, RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂,
      hu _ (by decide)]
  · show s₂.mem.readW _ 32 = _
    rw [sv₂ i hi, hu _ (sreg_ne_r12 i hi)]
  · exact f₂
  · exact lo₂
  · exact rd₂
  · exact wr₂
  · exact sp₂

/-- The postwhitening's address, to `lr`. -/
theorem endOf_ok {s : State} {b : BitVec 32} (hb : s.gpr sb = b) {g : Nat} (hg : g = 3 ∨ g = 4) :
    ∃ s', runBlock isa (endOf g) s = some s' ∧ s'.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) ∧
      (∀ r, r ≠ .lr → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s', e', l', o', m', rd', wr', sp'⟩ := addImm_ok s .lr sb (BitVec.ofNat 32 (4 * keySlot + 512 * g))
    (by rcases hg with rfl | rfl <;> decide)
  exact ⟨s', e', by rw [l', hb], o', m', rd', wr', sp'⟩

theorem ecbKeyed_wp (dir : Dir) {s₀ : State} (hp : (ecbKeyedArm dir).pre s₀) :
    WP isa ecbKeyed s₀ fun s' =>
      (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (ecbKeyedArm dir).post s₀ s' := by
  obtain ⟨⟨hrd, hwr, dSD, dSS, dDS, -, -, -, fitK, fitD, fitB, hR⟩, hK⟩ := hp
  generalize hb : stackArg s₀ 0 = b at hwr dSS dDS fitB hK
  let D := s₀.gpr .r2
  let n := (s₀.gpr .r3).toNat
  let sched := s₀.gpr .r0
  let R := (s₀.gpr .r1).toNat
  obtain hwS : ScrIn s₀.wr b := ⟨by rw [hwr]; simp, fitB⟩
  obtain hwD : (⟨State.addr D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  obtain hrA : (⟨stackArgAddr s₀ 0, 4⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have hfitB := fitB
  rw [slots_eq] at hfitB
  unfold ecbKeyed
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r1₁, r2₁, z₁, sv₁, f₁, lo₁, rd₁, wr₁, sp₁⟩ := keyedPrologue_ok hb hwS hrA
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain hz₁ : s₁.z = decide (R = 18) := by
    rw [z₁, show s₀.gpr .r1 = BitVec.ofNat 32 R by simp [R],
      show (18 : BitVec 32) = BitVec.ofNat 32 18 from rfl, ofNat32_sub_beq (by omega_arith) (by decide)]
  -- The postwhitening's address.
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  obtain hg : g = 3 ∨ g = 4 := by omega_arith
  let LQ : State → Prop := fun s => s.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) ∧
    (∀ r, r ≠ .lr → s.gpr r = s₁.gpr r) ∧ s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp
  refine WP.seq (WP.mono (M := isa) (Q := LQ)
    (WP.ite (decide (g = 3)) ((eval_eq s₁).trans (by
      rw [hz₁]; exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩)))
      (fun h => ?_) (fun h => ?_)) fun s₂ ⟨lr₂, g₂, m₂, rd₂', wr₂', sp₂⟩ => ?_)
  · obtain rfl : g = 3 := by simpa using h
    exact WP.of_runBlock (endOf_ok b₁ hg)
  · obtain rfl : g = 4 := by simp at h; omega_arith
    exact WP.of_runBlock (endOf_ok b₁ hg)
  -- The scratch buffer and the data before the groups.
  let E : Nat → BitVec 64 := fun i => (schedWords s₀.mem (State.addr sched) R).getD (permOf dir g i) 0
  obtain f₀₂ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₂.mem := by rw [m₂]; exact f₁
  obtain base₂ : s₂.gpr sb = b := by rw [g₂ _ (by decide)]; exact b₁
  obtain hK' : ∀ i < 8 * g + 2, EntryOk s₀.mem b i (E i) := fun i hi => by
    have h : EntryOk s₀.mem b i ((schedWords s₀.mem (State.addr sched) R).getD (permOf dir (R / 6) i) 0) :=
      hK i (by show i < 8 * (R / 6) + 2; rw [hgR]; exact hi)
    rw [hgR] at h
    exact h
  obtain sc₂ : ScrOk s₀ b g E s₂.mem := by
    refine ⟨fun i hi => (hK' i hi).congr fun j hj => ?_, by rw [m₂]; exact sv₁⟩
    rw [m₂]
    exact lo₁ _ (by rw [keySlot_eq, savedSlot_eq]; omega_arith)
  obtain data₂ : ∀ i < 16 * n, s₂.mem (State.addr D + BitVec.ofNat 64 i) = s₀.mem (State.addr D + BitVec.ofNat 64 i) :=
    fun i hi => f₀₂.bytes (R := ⟨State.addr D, 16 * n⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS) (by simp only; omega_arith) hi
  obtain fr₂ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s₂.mem :=
    f₀₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  obtain rd₂ : s₂.rd = s₀.rd := by rw [rd₂', rd₁]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [wr₂', wr₁]
  obtain sp₂' : s₂.sp = s₀.sp := by rw [sp₂, sp₁]
  obtain r1₂ : s₂.gpr .r1 = D := by rw [g₂ _ (by decide), r1₁]
  obtain r2₂ : s₂.gpr .r2 = BitVec.ofNat 32 n := by rw [g₂ _ (by decide), r2₁]; simp [n]
  -- Any blocks?
  let s₄ := subFlags s₂ (s₂.gpr .r2) 0
  obtain e₄ : runBlock isa [.cmp .r2 (.imm 0)] s₂ = some s₄ := by
    rw [runBlock_cons, show exec (.cmp .r2 (.imm 0)) s₂ = some s₄ by
      simp only [exec, Op2.eval, show encodable (0 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
      rfl,
      runStep_some, runBlock_nil]
  obtain hz₄ : s₄.z = decide (n = 0) := by
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
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_app, e₆, Option.bind_some, e₇], rg₇, ?_, ?_⟩
  · obtain hd₇ : DInv s₀.mem s₇.mem (State.addr D) n n (outF s₀.mem (State.addr D) g E) := fun i hi => by
      rw [m₇, m₆]; exact d₅.data i hi
    show Spec.Camellia.blocksAt s₇.mem (State.addr D) n = _
    rw [blocksAt_of_dinv hd₇, ecb_eq]
    simp only [Spec.Camellia.blocksAt, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    subst hgR
    exact outF_spec (specDir dir) s₀.mem (State.addr sched) (State.addr D) hR j
  · show KeysIn dir s₇.mem (stackArg s₀ 0) sched R
    rw [hb]
    intro e he
    rw [m₇, m₆, schedWord_frame (R := R) (d₅.frame) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dSS
        · exact dSD) hR (i := permOf dir (R / 6) e) (dirPerm_lt (specDir dir) he)]
    rw [hgR] at he ⊢
    exact d₅.scr.keys e he

/-! ## Correct, and constant time -/

theorem saved_abi {s s' : State} (h₁ : ∀ i < 9, s'.gpr (sreg i) = s.gpr (sreg i)) :
    ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega_using [])
  · exact h₁ 1 (by omega_using [])
  · exact h₁ 2 (by omega_using [])
  · exact h₁ 3 (by omega_using [])
  · exact h₁ 4 (by omega_using [])
  · exact h₁ 5 (by omega_using [])
  · exact h₁ 6 (by omega_using [])
  · exact h₁ 7 (by omega_using [])
  · exact h₁ 8 (by omega_using [])

theorem ecbKeys_correct (dir : Dir) (s : State) (hs : (ecbKeysArm dir).pre s) :
    ∃ t s', Exec isa (ecbKeys dir) s t s' ∧ abiPreserved s s' ∧ (ecbKeysArm dir).post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := ecbKeys_wp dir hs
  exact ⟨t, s', he, ⟨saved_abi h₁, VG.Arm.Exec.sp he⟩, h₂⟩

theorem ecbKeyed_correct (dir : Dir) (s : State) (hs : (ecbKeyedArm dir).pre s) :
    ∃ t s', Exec isa ecbKeyed s t s' ∧ abiPreserved s s' ∧ (ecbKeyedArm dir).post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := ecbKeyed_wp dir hs
  exact ⟨t, s', he, ⟨saved_abi h₁, VG.Arm.Exec.sp he⟩, h₂⟩

/-- The initial taint of `ecbKeys`: the arguments are public, and `r2` is
the base of the scratch buffer, the writable region. -/
def ecbKeysTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [4 * slots], bases := [(.r2, 0)] }

theorem ecbKeysTaint_wf (dir : Dir) {s : State} (h : (ecbKeysArm dir).pre s) :
    VG.Arm.Taint.Wf ecbKeysTaint s := by
  obtain ⟨-, hwr, -, -, fitB, -⟩ := h
  refine ⟨fun _ => ⟨by simp [hwr, ecbKeysTaint], ?_, ?_⟩, fun p hp => ?_, fun h => by simp [ecbKeysTaint] at h,
    fun p hp => by simp [ecbKeysTaint] at hp⟩
  · simp only [hwr, List.pairwise_cons, List.not_mem_nil, List.Pairwise.nil]
    exact ⟨fun _ h => h.elim, trivial⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    simp only [addr_toNat]; omega_arith
  · simp only [ecbKeysTaint, List.mem_singleton] at hp; subst hp
    simp [VG.Arm.Taint.region, hwr]

theorem ecbKeysTaint_agree (dir : Dir) (s₁ s₂ : State) (h₁ : (ecbKeysArm dir).pre s₁)
    (h₂ : (ecbKeysArm dir).pre s₂) (hp : (ecbKeysArm dir).pub s₁ s₂) :
    VG.Arm.Taint.Agree ecbKeysTaint s₁ s₂ := by
  obtain ⟨p0, p1, p2⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbKeysTaint_wf dir h₁, ecbKeysTaint_wf dir h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => by simp [ecbKeysTaint] at h, fun k hk => by simp [ecbKeysTaint] at hk⟩
  · simp only [ecbKeysTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p2]

theorem ecbKeys_ct (dir : Dir) : ConstantTime isa (ecbKeysArm dir).pre (ecbKeysArm dir).pub (ecbKeys dir) := by
  cases dir
  · exact VG.Taint.constantTime (A := VG.Arm.taint) ecbKeysTaint (ecbKeysTaint_agree .encrypt)
      (by native_taint_decide)
  · exact VG.Taint.constantTime (A := VG.Arm.taint) ecbKeysTaint (ecbKeysTaint_agree .decrypt)
      (by native_taint_decide)

/-- `ecbKeyed` is constant time from the taint `ecb dir` is: its code is
`ecb dir`'s without the table's construction. -/
theorem ecbKeyed_ct (dir : Dir) : ConstantTime isa (ecbKeyedArm dir).pre (ecbKeyedArm dir).pub ecbKeyed :=
  VG.Taint.constantTime (A := VG.Arm.taint) ecbTaint
    (fun s₁ s₂ h₁ h₂ hp => ecbTaint_agree dir s₁ s₂ h₁.1 h₂.1 hp) (by native_taint_decide)

/-! ## As the modes see them -/

theorem scr_dReg (dir : Dir) : (scrCore dir).dReg = .r2 := rfl
theorem scr_nReg (dir : Dir) : (scrCore dir).nReg = .r3 := rfl
theorem scr_bs (dir : Dir) : (scrCore dir).bs = 16 := rfl
theorem scr_scratch (dir : Dir) : (scrCore dir).stackScratch = 4 * slots := rfl

theorem rsel_or (R : BitVec 32) : rsel R = 18 ∨ rsel R = 24 := by
  unfold rsel; split
  · exact .inl rfl
  · exact .inr rfl

theorem ecb_noStack (dir : Dir) : VG.Arm.FrameStack.armStack (ecb dir) = 0 := by cases dir <;> decide +kernel
theorem ecbKeys_noStack (dir : Dir) : VG.Arm.FrameStack.armStack (ecbKeys dir) = 0 := by
  cases dir <;> decide +kernel
theorem ecbKeyed_noStack : VG.Arm.FrameStack.armStack ecbKeyed = 0 := by decide +kernel

/-- `ecb dir`'s precondition, in the state a mode enters it in. -/
theorem ecbArm_pre_of (dir : Dir) {s : State}
    (h : EcbPreS (scrCore dir) 272 8 (fun R => R.toNat = 18 ∨ R.toNat = 24) [] s) : (ecbArm dir).pre s := by
  obtain ⟨-, spF, rd, wr, kd, ks, ds, da, sa, -, -, -, -, fK, fD, fS, rr, -, -, -, -⟩ := h
  have rr := rr rfl
  simp only [scr_dReg, scr_nReg, scr_bs, scr_scratch, Nat.mul_comm _ 16] at wr kd ks ds da sa fD fS
  exact And.intro rd (And.intro wr ⟨kd, ks, ds, da.symm, sa.symm, spF, fK, fD, fS, rr⟩)

/-- What `ecb dir`'s postcondition makes of the blocks. -/
theorem ecbArm_post_of (dir : Dir) {s s' : State} (hR : (s.gpr .r1).toNat = 18 ∨ (s.gpr .r1).toNat = 24)
    (h : (ecbArm dir).post s s') :
    blocksOf (scrCore dir).bs s'.mem (State.addr (s.gpr (scrCore dir).dReg)) (s.gpr (scrCore dir).nReg).toNat =
      (blocksOf (scrCore dir).bs s.mem (State.addr (s.gpr (scrCore dir).dReg))
        (s.gpr (scrCore dir).nReg).toNat).map
        (dirCipher dir (Spec.Camellia.subkeysAt s.mem (State.addr (s.gpr .r0)) (rsel (s.gpr .r1)))) := by
  show blocksOf 16 _ _ _ = (blocksOf 16 _ _ _).map _
  rw [scr_dReg, scr_nReg, rsel_eq hR, blocksOf_eq, blocksOf_eq,
    show Spec.Camellia.blocksAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat = _ from h, ecb_dir,
    List.map_map, List.map_map]
  exact List.map_congr_left fun v _ => (dirCipher_toList dir _ v).symm

/-- `ecb dir`, with its working space as a stack argument, as the modes'
core: the cipher of `ecbSpec dir`. -/
def scrSpec (dir : Dir) : CoreSpec (scrCore dir) where
  keyLen := 272
  stack := 8
  rok R := R.toNat = 18 ∨ R.toNat = 24
  ciphAt m K R := dirCipher dir (Spec.Camellia.subkeysAt m K (rsel R))
  contract := ecbArm dir
  correct := ecb_correct dir
  ct := ecb_ct dir
  depth := by show VG.Arm.FrameStack.armStack (ecb dir) ≤ 8; rw [ecb_noStack]; decide
  pre_of h := absurd h (by rw [scr_scratch]; decide)
  post_of h := absurd h (by rw [scr_scratch]; decide)
  pub_of h := absurd h (by rw [scr_scratch]; decide)
  ciphAt_congr {_ _ _ R} h := congrArg (dirCipher dir) (Proof.Camellia.subkeysAt_congr (R := rsel R)
    (by unfold rsel; split <;> decide) h)
  ciphAt_R h := by cases dir <;> simp [scrCore] at h
  cipher_len m K _ b _ := by cases dir <;> (simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher]; rfl)
  bw_pos := by cases dir <;> decide
  bw_le := by cases dir <;> decide
  bs_enc := by cases dir <;> decide
  consts_plain _ := rfl
  pre_ofS _ _ h := ecbArm_pre_of dir h
  post_ofS _ _ _ hp h := ecbArm_post_of dir (hp.rr rfl) h
  pub_ofS _ _ _ h0 h1 h2 h3 h4 h5 _ := ⟨h1, h2, h3, h4 rfl, h0, h5⟩
  depthS _ := by show VG.Arm.FrameStack.armStack (ecb dir) + 8 ≤ 8; rw [ecb_noStack]
  cs_enc _ := by cases dir <;> decide

/-- The two functions that split `ecb dir`, as the modes need them: the
keys are the table of `dir`. -/
def keyedSpec (dir : Dir) : KeyedSpec (scrCore dir) (scrSpec dir) (keyed dir) where
  keysIn m K R C := KeysIn dir m C K (rsel R)
  keysIn_frame {_ _ _ _ R _} hf hk hc _ fC _ h := h.frame (rsel_or R) fC hf hk hc
  keysIn_R h := by cases dir <;> simp [scrCore] at h
  scr := by rw [scr_scratch]; decide
  keysContract := ecbKeysArm dir
  keysCorrect := ecbKeys_correct dir
  keysCt := ecbKeys_ct dir
  keysDepth := by show VG.Arm.FrameStack.armStack (ecbKeys dir) ≤ 8; rw [ecbKeys_noStack]; decide
  keysPre _ h := And.intro h.rd (And.intro h.wr ⟨h.ks, h.fK, h.fS, h.rr rfl⟩)
  keysPost s s' hp h := by
    show KeysIn dir s'.mem (s.gpr .r2) (s.gpr .r0) (rsel (s.gpr .r1))
    rw [rsel_eq (hp.rr rfl)]; exact h
  keysPub _ _ h0 h1 h2 := ⟨h0, h1, h2 rfl⟩
  contract := ecbKeyedArm dir
  correct := ecbKeyed_correct dir
  ct := ecbKeyed_ct dir
  depth := by show VG.Arm.FrameStack.armStack ecbKeyed + 8 ≤ 8; rw [ecbKeyed_noStack]
  pre_of s h hj := ⟨ecbArm_pre_of dir h, by rw [← rsel_eq (h.rr rfl)]; exact hj⟩
  post_of s s' h _ hpost := ⟨ecbArm_post_of dir (h.rr rfl) hpost.1, by
    show KeysIn dir s'.mem (stackArg s 0) (s.gpr .r0) (rsel (s.gpr .r1))
    rw [rsel_eq (h.rr rfl)]; exact hpost.2⟩
  pub_of _ _ h0 h1 h2 h3 h4 h5 _ := ⟨h1, h2, h3, h4 rfl, h0, h5⟩

end VG.Proof.Camellia.Arm
