import VerifiedGarbage.Proof.Seed.Arm.Group
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SEED ECB on ARMv7: the whole function

`ecb_wp`: with the working space as an argument (`ecbArm`), `ecb d` saves
the callee-saved registers, copies the round keys to the table in the order
the rounds of `d` use them (`keyTable_ok`), transforms the blocks a group at
a time (`dataGroup_wp`) and restores the registers.
-/

namespace VG.Proof.Seed

open VG VG.Arm VG.Impl.Seed.Arm

/-- ECB on ARMv7 with its working space at `r3`. -/
def ecbArm (d : Spec.Seed.Direction) : Contract Arm.isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 16 * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 4 * slots⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 16 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 4 * slots ≤ 2 ^ 32
  post s s' :=
    Spec.Seed.blocksAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (State.addr (s.gpr .r0))) d
        (Spec.Seed.blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

end VG.Proof.Seed

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Seed.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR ldS stS)
open VG.Proof.Seed (ecbArm crypt_congr)

/-! ## The table of round keys -/

/-- `ldr t0, [r0, #4 a]; str t0, [sb, #4 d]` for each `(a, d)`. -/
def loadsCode (L : List (Nat × Nat)) : List Instr :=
  L.flatMap fun p => [.ldr t0 .r0 (4 * p.1), stS p.2 t0]

/-- The schedule at `sched` and the scratch buffer at `b`. -/
structure SchedPre (s : State) (b sched : BitVec 32) : Prop where
  base : s.gpr sb = b
  scr : ScrIn s.wr b
  r0 : s.gpr .r0 = sched
  sch : (⟨State.addr sched, 128⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr sched, 128⟩ ⟨State.addr b, 4 * slots⟩

/-- Word `i` of the schedule. -/
def schW (m : Mem) (sched : BitVec 32) (i : Nat) : BitVec 32 := m.readW (State.addr (sched + BitVec.ofNat 32 (4 * i))) 32

theorem loads_ok {b sched : BitVec 32} :
    ∀ (L : List (Nat × Nat)) (s : State), SchedPre s b sched → (∀ p ∈ L, p.1 < 32 ∧ p.2 < slots) →
      (L.map (·.2)).Nodup →
      ∃ s', runBlock isa (loadsCode L) s = some s' ∧
        (∀ p ∈ L, s'.mem.readW (wordAddr b p.2) 32 = schW s.mem sched p.1) ∧
        (∀ j < slots, j ∉ L.map (·.2) → s'.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32) ∧
        (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, runBlock_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | p :: L, s, hs, hL, hnd => by
    have hp := hL p List.mem_cons_self
    have hfK := hs.schFit
    have hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * p.1))) 4 := by
      rw [hs.r0]; exact in_off hs.sch hfK (by omega) (by omega)
    let v := schW s.mem sched p.1
    have ev : s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * p.1))) 32 = v := by rw [hs.r0]; rfl
    let s₁ := s.setReg t0 v
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, sp₂, -, f₂⟩ := stSlot_ok s₁ t0 sb (k := p.2)
      (by rw [show s₁.gpr sb = s.gpr sb from RegUpd.gpr_setReg_of_ne _ _ (by decide), hs.base]) hp.2
      (by rw [show s₁.wr = s.wr from rfl]; exact hs.scr)
    have e₁ : runBlock isa [.ldr t0 .r0 (4 * p.1), stS p.2 t0] s = some s₂ := by
      rw [runBlock_cons, exec_ldr (by omega) hin, ev, runStep_some]; exact e₂
    have hs₂ : SchedPre s₂ b sched :=
      ⟨by rw [g₂, show s₁.gpr sb = s.gpr sb from RegUpd.gpr_setReg_of_ne _ _ (by decide), hs.base],
        by rw [wr₂]; exact hs.scr,
        by rw [g₂, show s₁.gpr .r0 = s.gpr .r0 from RegUpd.gpr_setReg_of_ne _ _ (by decide), hs.r0],
        by rw [rd₂, wr₂]; exact hs.sch, hfK, hs.sep⟩
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', g', rd', wr', sp', f'⟩ := loads_ok L s₂ hs₂
      (fun q hq => hL q (List.mem_cons_of_mem _ hq)) hnd.2
    have hfit := hs.scr.fit
    have hsch : ∀ i < 32, schW s₂.mem sched i = schW s.mem sched i := by
      intro i hi
      simp only [schW]
      rw [addr_add (by omega)]
      refine f₂.readW (r := ⟨State.addr sched, 128⟩) (Offset.contains_base _ (by omega) (by omega))
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.sep.sub_right (slot_sub hfit hp.2)
    have m₂' : s₂.mem = s.mem.writeW (wordAddr b p.2) v := by
      rw [m₂, show s₁.mem = s.mem from rfl, show s₁.gpr t0 = v from RegUpd.gpr_setReg_self _ _ _]
    refine ⟨s', ?_, fun q hq => ?_, fun j hj hjL => ?_, fun r hr => ?_, by rw [rd', rd₂]; rfl,
      by rw [wr', wr₂]; rfl, by rw [sp', sp₂]; rfl, ?_⟩
    · rw [loadsCode, List.flatMap_cons, runBlock_append, e₁, Option.bind_some]; exact e'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o' _ hp.2 hnd.1, m₂', readW_slot_write hfit _ hp.2 hp.2, ite_eq_left rfl]
      · rw [v' q hq, hsch _ (hL q (List.mem_cons_of_mem _ hq)).1]
    · simp only [List.map_cons, List.mem_cons, not_or] at hjL
      rw [o' j hj hjL.2, m₂', readW_slot_write hfit _ hj hp.2, ite_eq_right hjL.1]
    · rw [g' r hr, g₂, RegUpd.gpr_setReg_of_ne _ _ hr]
    · exact (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hp.2⟩).trans f'

def tableMoves (d : Spec.Seed.Direction) : List (Nat × Nat) := (List.range 32).map fun i => (keySrc d i, tableSlot + i)

theorem keyTable_eq (d : Spec.Seed.Direction) : keyTable d = loadsCode (tableMoves d) := by
  cases d <;> decide +kernel

theorem keySrc_lt (d : Spec.Seed.Direction) {i : Nat} (hi : i < 32) : keySrc d i < 32 := by
  cases d <;> simp [keySrc] <;> omega

/-- The table: word `i` is the schedule's word `keySrc d i`. -/
theorem keyTable_ok (d : Spec.Seed.Direction) {s : State} {b sched : BitVec 32} (hs : SchedPre s b sched) :
    ∃ s', runBlock isa (keyTable d) s = some s' ∧
      (∀ i < 32, s'.mem.readW (wordAddr b (tableSlot + i)) 32 = schW s.mem sched (keySrc d i)) ∧
      (∀ j < slots, (j < tableSlot ∨ tableEnd ≤ j) →
        s'.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem := by
  obtain ⟨s', e', v', o', g', rd', wr', sp', f'⟩ := loads_ok (tableMoves d) s hs
    (by intro p hp
        simp only [tableMoves, List.mem_map, List.mem_range] at hp
        obtain ⟨i, hi, rfl⟩ := hp
        exact ⟨keySrc_lt d hi, by rw [slots_eq, tableSlot_eq]; omega⟩)
    (by cases d <;> decide +kernel)
  refine ⟨s', by rw [keyTable_eq]; exact e', fun i hi => v' (keySrc d i, tableSlot + i) ?_,
    fun j hj hj' => o' j hj ?_, g', rd', wr', sp', f'⟩
  · simp only [tableMoves, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩
  · simp only [tableMoves, List.map_map, List.mem_map, List.mem_range, Function.comp, not_exists, not_and]
    intro i hi he; rw [tableSlot_eq, tableEnd_eq] at *; omega

/-! ## The whole function -/

theorem dataLoop_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Seed.Word} (hp : GPre s₀ b D n)
    {s : State} (hi : GInv s₀ b D n E 0 s) :
    WP isa (.loop group .ne) s (GDone s₀ b D n E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 8 * k ∧ GInv s₀ b D n E k s) (fun m s hs => ?_) n s
    ⟨0, by omega, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_ne s').trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_ne s').trans (by rw [z]; rfl), n - 8 * (k + 1),
      by have := d.lt; have := hk.lt; omega, k + 1, rfl, d⟩

/-- The block function of each direction. -/
def blockFn (sch : Spec.Seed.Schedule) : Spec.Seed.Direction → Spec.Seed.Block → Spec.Seed.Block
  | .encrypt => Spec.Seed.encryptBlock sch
  | .decrypt => Spec.Seed.decryptBlock sch

theorem ecb_eq (sch : Spec.Seed.Schedule) (d : Spec.Seed.Direction) (l : List Spec.Seed.Block) :
    Spec.Seed.ecb sch d l = l.map (blockFn sch d) := by
  cases d <;> rfl

/-- The table's round keys are the schedule's, in the order of `d`. -/
theorem keyPairs_eq (d : Spec.Seed.Direction) (m : Mem) {sched : BitVec 32} (hfit : sched.toNat + 128 ≤ 2 ^ 32)
    {j : Nat} (hj : j < 16) :
    keyPairs (fun i => schW m sched (keySrc d i)) j =
      Spec.Seed.roundKey (Spec.Seed.scheduleAt m (State.addr sched))
        (match d with | .encrypt => j | .decrypt => 15 - j) := by
  have hw : ∀ i < 32, schW m sched i = m.readW (State.addr sched + BitVec.ofNat 64 (4 * i)) 32 := fun i hi => by
    simp only [schW]; rw [addr_add (by omega)]
  cases d
  · rw [Proof.Seed.roundKey_readW _ _ hj]
    simp only [keyPairs, keySrc]
    rw [hw _ (by omega), hw _ (by omega), show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add,
      show 4 * (2 * j) = 8 * j by omega, show 4 * (2 * j + 1) = 8 * j + 4 by omega]
  · show keyPairs _ j = Spec.Seed.roundKey _ (15 - j)
    rw [Proof.Seed.roundKey_readW _ _ (by omega)]
    simp only [keyPairs, keySrc]
    rw [hw _ (by omega), hw _ (by omega), show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add,
      show 4 * (2 * (15 - 2 * j / 2) + 2 * j % 2) = 8 * (15 - j) by omega,
      show 4 * (2 * (15 - (2 * j + 1) / 2) + (2 * j + 1) % 2) = 8 * (15 - j) + 4 by omega]

theorem outF_spec (d : Spec.Seed.Direction) (m : Mem) {sched : BitVec 32} (hfit : sched.toNat + 128 ≤ 2 ^ 32)
    (D : Addr) (j : Nat) :
    outF m D (fun i => schW m sched (keySrc d i)) j =
      blockFn (Spec.Seed.scheduleAt m (State.addr sched)) d
        (Spec.Seed.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  simp only [outF]
  cases d
  · exact crypt_congr (fun i hi => keyPairs_eq .encrypt m hfit hi) _
  · exact crypt_congr (fun i hi => keyPairs_eq .decrypt m hfit hi) _

/-- The prologue: the registers saved, the scratch buffer in `sb`. -/
theorem prologue_ok {s₀ : State} {b : BitVec 32} (hb : s₀.gpr .r3 = b) (hw : ScrIn s₀.wr b) :
    ∃ s, runBlock isa (saveRegs .r3 ++ [movR sb .r3]) s₀ = some s ∧
      s.gpr sb = b ∧ (∀ r, r ≠ sb → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      s.sp = s₀.sp := by
  obtain ⟨s₁, e₁, sv₁, g₁, rd₁, wr₁, sp₁, f₁, -⟩ := save_ok hw hb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movR_ok s₁ sb .r3
  refine ⟨s₂, ?_, by rw [r₂, g₁, hb], fun r h1 => by rw [o₂ r h1, g₁], by rw [m₂]; exact sv₁,
    by rw [m₂]; exact f₁, by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁]⟩
  rw [runBlock_append, e₁, Option.bind_some, e₂]

theorem ecb_wp (d : Spec.Seed.Direction) {s₀ : State} (hp : (ecbArm d).pre s₀) :
    WP isa (ecb d) s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (ecbArm d).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, fitK, fitD, fitB⟩ := hp
  let b := s₀.gpr .r3
  let D := s₀.gpr .r1
  let n := (s₀.gpr .r2).toNat
  let sched := s₀.gpr .r0
  have hwS : ScrIn s₀.wr b := ⟨by rw [hwr]; simp [b], fitB⟩
  have hwD : (⟨State.addr D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨State.addr sched, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  have fitK' : sched.toNat + 128 ≤ 2 ^ 32 := fitK
  unfold ecb
  -- The prologue and the table.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, f₁, rd₁, wr₁, sp₁⟩ := prologue_ok (b := b) rfl hwS
  have hk₁ : SchedPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, g₁ _ (by decide), List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK', dSS⟩
  obtain ⟨s₂, e₂, v₂, o₂, g₂, rd₂', wr₂', sp₂', f₂⟩ := keyTable_ok d hk₁
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [runBlock_append, e₁, Option.bind_some, e₂], ?_⟩)
  let E : Nat → Spec.Seed.Word := fun i => schW s₀.mem sched (keySrc d i)
  have hsch : ∀ i < 32, schW s₁.mem sched i = schW s₀.mem sched i := by
    intro i hi
    simp only [schW]
    rw [addr_add (by omega)]
    refine f₁.readW (r := ⟨State.addr sched, 128⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr; exact dSS
  have f₀₂ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₂.mem := f₁.trans f₂
  have base₂ : s₂.gpr sb = b := by rw [g₂ _ (by decide), b₁]
  have sc₂ : ScrOk s₀ b E s₂.mem := by
    refine ⟨fun e he => ?_, fun i hi => ?_⟩
    · rw [v₂ e he, hsch _ (keySrc_lt d he)]
    · rw [o₂ _ (by rw [savedSlot_eq, slots_eq]; omega) (.inr (by rw [savedSlot_eq, tableEnd_eq]; omega))]
      exact sv₁ i hi
  have data₂ : ∀ i < 16 * n, s₂.mem (State.addr D + BitVec.ofNat 64 i) = s₀.mem (State.addr D + BitVec.ofNat 64 i) :=
    fun i hi => f₀₂.bytes (R := ⟨State.addr D, 16 * n⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS) (by simp only; omega) hi
  have fr₂ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s₂.mem :=
    f₀₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have rd₂ : s₂.rd = s₀.rd := by rw [rd₂', rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [wr₂', wr₁]
  have sp₂ : s₂.sp = s₀.sp := by rw [sp₂', sp₁]
  have r1₂ : s₂.gpr .r1 = D := by rw [g₂ _ (by decide), g₁ _ (by decide)]
  have r2₂ : s₂.gpr .r2 = BitVec.ofNat 32 n := by
    rw [g₂ _ (by decide), g₁ _ (by decide)]; simp [n]
  -- Any blocks?
  let s₄ := subFlags s₂ (s₂.gpr .r2) 0
  have e₄ : runBlock isa [.cmp .r2 (.imm 0)] s₂ = some s₄ := by
    rw [runBlock_cons, show exec (.cmp .r2 (.imm 0)) s₂ = some s₄ by simp [exec, Op2.eval, s₄]; decide,
      runStep_some, runBlock_nil]
  have hz₄ : s₄.z = decide (n = 0) := by
    show (s₂.gpr .r2 - 0 == 0) = _
    rw [r2₂, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    have : n < 2 ^ 32 := (s₀.gpr .r2).isLt
    bv_omega
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have base₄ : s₄.gpr sb = b := base₂
  have mem₄ : s₄.mem = s₂.mem := rfl
  have rd₄ : s₄.rd = s₀.rd := rd₂
  have wr₄ : s₄.wr = s₀.wr := wr₂
  have sp₄ : s₄.sp = s₀.sp := sp₂
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) ((eval_eq s₄).trans (by rw [hz₄])) (fun h0 => ?_) (fun h0 => ?_))
    fun s₅ d₅ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₄, mem₄ ▸ sc₂, fun i hi => by omega, mem₄ ▸ fr₂, rd₄, wr₄, sp₄⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitD⟩ ⟨base₄, by show s₂.gpr .r1 = _; rw [r1₂]; simp,
      by show s₂.gpr .r2 = _; rw [r2₂, Nat.mul_zero, Nat.sub_zero], by omega,
      mem₄ ▸ sc₂, fun i hi => ?_, mem₄ ▸ fr₂, rd₄, wr₄, sp₄⟩
    rw [mem₄, data₂ i hi, ite_eq_right (by omega)]
  -- The epilogue.
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := movR_ok s₅ .r12 sb
  obtain ⟨s₇, e₇, rg₇, -, m₇, -, -, -⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [wr₆, d₅.wr]; exact hwS)
    (by rw [r₆, d₅.base]) (by rw [m₆]; exact d₅.scr.saved)
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_append, e₆, Option.bind_some, e₇], rg₇, ?_⟩
  have hd₇ : DInv s₀.mem s₇.mem (State.addr D) n n (outF s₀.mem (State.addr D) E) := fun i hi => by
    rw [m₇, m₆]; exact d₅.data i hi
  show Spec.Seed.blocksAt s₇.mem (State.addr D) n = _
  rw [blocksAt_of_dinv hd₇, ecb_eq]
  simp only [Spec.Seed.blocksAt, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  exact outF_spec d s₀.mem fitK _ j

end VG.Proof.Seed.Arm
