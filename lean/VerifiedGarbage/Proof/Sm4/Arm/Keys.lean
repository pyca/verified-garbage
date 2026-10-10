import VerifiedGarbage.Proof.Sm4.Arm.Crypt8
import VerifiedGarbage.Proof.Aes.Bitsliced

/-!
# The table of bitsliced round keys on ARMv7

`keyOne_step`: `keyOne` bitslices the round key at `r12` into the table's
entry at `kp`, every block's copy of it alike. `keys_wp` builds the table in
the order the rounds use the round keys: `rk₀ … rk₃₁` for encryption,
`rk₃₁ … rk₀` for decryption.
-/

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR lsrOp)
open VG.Proof.Sm4 (getLsbD_scheduleAt)

/-- `ldr r0, [r12]; rev r0, r0`. -/
theorem keyWord_ok (s : State) (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 0)) 4) :
    ∃ s', runBlock isa keyWord s = some s' ∧
      s'.gpr (q 0) = rev (s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 0)) 32) ∧
      (∀ r, r ≠ q 0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let x := s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 0)) 32
  refine ⟨(s.setReg (q 0) x).setReg (q 0) (rev x), ?_, RegUpd.gpr_setReg_self _ _ _,
    fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl, rfl, rfl⟩
  rw [keyWord, runBlock_cons, exec_ldr (by decide) h, runStep_some, runBlock_cons,
    show exec (.rev (q 0) (q 0)) (s.setReg (q 0) x) = some ((s.setReg (q 0) x).setReg (q 0) (rev x)) by
      simp only [exec, RegUpd.gpr_setReg_self],
    runStep_some, runBlock_nil]

/-- The schedule at `sched`, apart from the scratch buffer at `b`. -/
structure SchedPre (s : State) (b sched : BitVec 32) : Prop where
  base : s.gpr sb = b
  scr : (⟨State.addr b, 4 * slots⟩ : Region) ∈ s.wr
  fit : b.toNat + 4 * slots ≤ 2 ^ 32
  sch : (⟨State.addr sched, 128⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr sched, 128⟩ ⟨State.addr b, 4 * slots⟩

theorem SchedPre.congr {s s' : State} {b sched : BitVec 32} (h : SchedPre s b sched)
    (hb : s'.gpr sb = s.gpr sb) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : SchedPre s' b sched :=
  ⟨hb.trans h.base, hwr ▸ h.scr, h.fit, hrd ▸ hwr ▸ h.sch, h.schFit, h.sep⟩

/-- Round key `i` of the schedule at `sched`. -/
theorem SchedPre.keyIn {s : State} {b sched : BitVec 32} (h : SchedPre s b sched) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (State.addr (sched + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4 :=
  ⟨_, h.sch, by
    have := h.schFit
    rw [BitVec.add_zero, addr_add (by omega_arith)]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- The word at round key `i` is round key `i`. -/
theorem key_word (m : Mem) {sched : BitVec 32} (hfit : sched.toNat + 128 ≤ 2 ^ 32) {i : Nat} (hi : i < 32) :
    m.readW (State.addr (sched + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 32 =
      (Spec.Sm4.scheduleAt m (State.addr sched)).getD i 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [VG.Proof.Aes.getD_eq _ hi, show k = 8 * (k / 8) + k % 8 by omega_arith,
    getLsbD_scheduleAt _ _ hi (by omega_arith) (by omega_arith), readW_bit _ _ (by omega_arith) (by omega_arith),
    BitVec.add_zero, addr_add (by omega_arith), BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The table's entry `e` at `b`. -/
theorem entry_addr {b : BitVec 32} {e j : Nat} :
    wordAddr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)) j = wordAddr b (tableSlot + 8 * e + j) := by
  simp only [wordAddr]
  rw [add_ofNat_ofNat, show 4 * tableSlot + 32 * e + 4 * j = 4 * (tableSlot + 8 * e + j) by omega_arith]

/-- The round key at `r12` to the entry at `kp`. -/
theorem keyOne_step {s : State} {b sched : BitVec 32} {e i : Nat} (hp : SchedPre s b sched)
    (hkp : s.gpr kp = b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)) (he : e < 32)
    (hr : s.gpr .r12 = sched + BitVec.ofNat 32 (4 * i)) (hi : i < 32) :
    ∃ s', runBlock isa keyOne s = some s' ∧
      (∀ r, r ≠ q 0 → r ≠ q 3 → r ≠ t1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)), 32⟩] s.mem s'.mem ∧
      W32.WordRel (entryW s'.mem b e) (fun _ => (Spec.Sm4.scheduleAt s.mem (State.addr sched)).getD i 0) := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  -- The word.
  obtain ⟨s₁, e₁, x₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := keyWord_ok s (by rw [hr]; exact hp.keyIn hi)
  rw [hr, key_word _ hp.schFit hi] at x₁
  -- Its planes, to the entry.
  have kp₁ : s₁.gpr kp = s.gpr kp := o₁ _ (by decide)
  have hok : Ok entryCfg s₁ :=
    { slotIn := fun k hk => by
        simp only [entryCfg] at hk ⊢
        rw [wr₁, kp₁, hkp, entry_addr]
        exact slot_in hp.scr hp.fit (by rw [slots_eq, tableSlot_eq]; omega_arith)
      extIn := fun k hk => by simp [entryCfg] at hk
      slots := by
        simp only [entryCfg]; rw [kp₁, hkp, BitVec.toNat_add, BitVec.toNat_ofNat, tableSlot_eq]
        have := b.isLt
        rw [Nat.mod_eq_of_lt (show 384 + 32 * e < 2 ^ 32 by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
      sep := fun k _ j hj => by simp [entryCfg] at hj }
  have hchk := keyPlanes_check
  unfold keyEnv at hchk
  obtain ⟨s₂, e₂, -, hso₂, -, rd₂, wr₂, sp₂, o₂, f₂, -, -⟩ := linG_ok hchk hok (fun _ => s₁.gpr (q 0))
    (fun r i hri => by
      simp only [List.mem_singleton, Prod.mk.injEq] at hri
      obtain ⟨rfl, rfl⟩ := hri
      exact ⟨by decide, rfl⟩)
    (fun j i hji => by simp at hji) (fun kv hkv => by simp at hkv) (fun j hj => by simp [entryCfg] at hj)
  simp only [entryCfg] at hso₂ f₂
  have he₂ : ∀ j < 8, ∀ p < 32, (entryW s₂.mem b e j).getLsbD p = (rev (Vector.getD
      (Spec.Sm4.scheduleAt s.mem (State.addr sched)) i 0)).getLsbD (8 * (p / 8) + j) := fun j hj p hp => by
    have h := hso₂ j (keyBsG j) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) hj p hp
    rw [keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
      show 8 * (p / 8) + j = 32 * 0 + (8 * (p / 8) + j) by omega_arith, bitOf_word _ _ _ (by omega_arith), x₁, kp₁, hkp,
      entry_addr] at h
    rw [entryW, h]
  have hall₂ : ([Reg.r1, .r2, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .lr].all fun r =>
      keyPlanes.all fun i => dstOf i != some r) = true := by decide +kernel
  refine ⟨s₂, ?_, fun r h0 h3 h11 => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁], ?_, ?_⟩
  · rw [keyOne, runBlock_app, e₁, Option.bind_some, e₂]
  · rw [o₂ r (List.all_eq_true.mp hall₂ r (by revert h0 h3 h11; cases r <;> decide)), o₁ r h0]
  · rw [← m₁]
    refine f₂.mono fun r hr => ?_
    simp only [slotRegion, List.mem_singleton] at hr; subst hr
    rw [kp₁, hkp]; exact List.mem_singleton_self _
  · intro b' hb' i' hi' j hj
    rw [he₂ j hj _ (by omega_arith), show (8 * i' + b') / 8 = i' by omega_arith, rev_bit _ hi' hj]

/-! ## The loop -/

/-- The entry of round key `i`: `i` for encryption, `31 - i` for decryption. -/
def entOf : Dir → Nat → Nat
  | .encrypt, i => i
  | .decrypt, i => 31 - i

/-- `kp` before iteration `m`, as an offset in the scratch buffer. -/
def kpAtIter : Dir → Nat → Nat
  | .encrypt, m => 4 * tableSlot + 32 * m
  | .decrypt, m => 4 * tableSlot - 32 + 32 * (32 - m)

/-- The instruction stepping `kp`. -/
def kpStep : Dir → Instr
  | .encrypt => .dp .add kp kp (.imm 32)
  | .decrypt => .dp .sub kp kp (.imm 32)

/-- The loop's body. -/
def tableBody (dir : Dir) : List Instr :=
  keyOne ++ ([.dp .add .r12 .r12 (.imm 4), kpStep dir, .subs .lr .lr (.imm 1)] : List Instr)

theorem keys_eq (dir : Dir) :
    keys dir = .seq (.block [kpAt (match dir with | .encrypt => tableSlot | .decrypt => tableSlot + 8 * 31),
      .mov .lr (.imm 32)]) (.loop (.block (tableBody dir)) .ne) := by
  cases dir <;> rfl

theorem kpAtIter_ent (dir : Dir) {m : Nat} (hm : m < 32) :
    kpAtIter dir m = 4 * tableSlot + 32 * entOf dir m := by
  cases dir <;> simp only [kpAtIter, entOf, tableSlot_eq] <;> omega_arith

theorem entOf_lt (dir : Dir) {i : Nat} (hi : i < 32) : entOf dir i < 32 := by cases dir <;> simp [entOf] <;> omega_arith

theorem entOf_inj (dir : Dir) {i i' : Nat} (hi : i < 32) (hi' : i' < 32) (h : entOf dir i = entOf dir i') :
    i = i' := by cases dir <;> simp [entOf] at h <;> omega_arith

theorem entOf_entOf (dir : Dir) {e : Nat} (he : e < 32) : entOf dir (entOf dir e) = e := by
  cases dir <;> simp [entOf] <;> omega_arith

/-- `kp ± 32`. -/
theorem kpStep_ok (dir : Dir) (s : State) {b : BitVec 32} {m : Nat} (hm : m < 32)
    (hkp : s.gpr kp = b + BitVec.ofNat 32 (kpAtIter dir m)) :
    ∃ s', runBlock isa [kpStep dir] s = some s' ∧ s'.gpr kp = b + BitVec.ofNat 32 (kpAtIter dir (m + 1)) ∧
      (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  cases dir
  · obtain ⟨s', e', r', o', m', rd', wr', sp'⟩ := addImm_ok s kp kp 32 (by decide)
    refine ⟨s', e', ?_, o', m', rd', wr', sp'⟩
    rw [r', hkp, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, add_ofNat_ofNat]
    simp only [kpAtIter]; rw [show 4 * tableSlot + 32 * m + 32 = 4 * tableSlot + 32 * (m + 1) by omega_arith]
  · obtain ⟨s', e', r', o', m', rd', wr', sp'⟩ := subImm_ok s kp kp 32 (by decide)
    refine ⟨s', e', ?_, o', m', rd', wr', sp'⟩
    simp only [kpAtIter] at hkp ⊢
    rw [r', hkp, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl,
      show 4 * tableSlot - 32 + 32 * (32 - m) = (4 * tableSlot - 32 + 32 * (32 - (m + 1))) + 32 by
        rw [tableSlot_eq]; omega_arith, ← add_ofNat_ofNat, BitVec.add_sub_cancel]

/-- `subs d, n, #1`. -/
theorem subs1_ok (s : State) (d : Reg) :
    ∃ s', runBlock isa [.subs d d (.imm 1)] s = some s' ∧ s'.gpr d = s.gpr d - 1 ∧ s'.z = (s.gpr d - 1 == 0) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨(subFlags s (s.gpr d) 1).setReg d (s.gpr d - 1), ?_, RegUpd.gpr_setReg_self _ _ _, by rw [RegUpd.z_setReg]; rfl,
    fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr]; rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.subs d d (.imm 1)) s = some ((subFlags s (s.gpr d) 1).setReg d (s.gpr d - 1)) by
    simp [exec, Op2.eval]; decide, runStep_some, runBlock_nil]

/-- An entry outside a frame keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e i : Nat}
    (hf : Frame [⟨State.addr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)), 32⟩] m m')
    (hi : i < 32) (he : e < 32) (hie : i ≠ e) {j : Nat} (hj : j < 8) : entryW m' b i j = entryW m b i j := by
  rw [slots_eq] at hfit
  have hb := addr_toNat b
  rw [addr_add (by rw [tableSlot_eq]; omega_arith)] at hf
  simp only [entryW]
  rw [slot_addr (by rw [tableSlot_eq]; omega_arith)]
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [tableSlot_eq]
  exact VG.Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The table's entry `e` is inside the table. -/
theorem entry_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e : Nat} (he : e < 32) :
    Region.Sub ⟨State.addr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)), 32⟩ ⟨State.addr b, 4 * tableEnd⟩ := by
  rw [slots_eq] at hfit
  rw [addr_add (by rw [tableSlot_eq]; omega_arith), tableSlot_eq, tableEnd_eq]
  exact VG.Offset.sub_base _ (by omega_arith)

theorem ofNat32_beq_zero {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

/-- What the loop keeps, after `m` of its 32 iterations. -/
structure KInv (s₀ : State) (b sched : BitVec 32) (dir : Dir) (m : Nat) (s : State) : Prop where
  pre : SchedPre s b sched
  kpv : s.gpr kp = b + BitVec.ofNat 32 (kpAtIter dir m)
  ptr : s.gpr .r12 = sched + BitVec.ofNat 32 (4 * m)
  cnt : s.gpr .lr = BitVec.ofNat 32 (32 - m)
  ent : ∀ i < m, W32.WordRel (entryW s.mem b (entOf dir i))
    (fun _ => (Spec.Sm4.scheduleAt s₀.mem (State.addr sched)).getD i 0)
  frame : Frame [⟨State.addr b, 4 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ q 0 → r ≠ q 3 → r ≠ t1 → r ≠ .r12 → r ≠ kp → r ≠ .lr → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The schedule is outside the scratch buffer. -/
theorem SchedPre.sched_eq {s : State} {b sched : BitVec 32} (h : SchedPre s b sched) {m m' : Mem} {n : Nat}
    (hn : n ≤ slots) (hf : Frame [⟨State.addr b, 4 * n⟩] m m') :
    Spec.Sm4.scheduleAt m' (State.addr sched) = Spec.Sm4.scheduleAt m (State.addr sched) := by
  have hb : ∀ k < 128, m' (State.addr sched + BitVec.ofNat 64 k) = m (State.addr sched + BitVec.ofNat 64 k) :=
    fun k hk => hf.bytes (R := ⟨State.addr sched, 128⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.sep.sub_right (Region.sub_prefix (by omega_arith))) (by show 128 ≤ 2 ^ 64; omega_arith) hk
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
  rw [hb (4 * i + 0) (by omega_arith), hb (4 * i + 1) (by omega_arith), hb (4 * i + 2) (by omega_arith), hb (4 * i + 3) (by omega_arith)]

/-- One iteration: round key `m`. -/
theorem keyIter_ok (dir : Dir) {s₀ s : State} {b sched : BitVec 32} {m : Nat} (hm : m < 32)
    (hi : KInv s₀ b sched dir m s) :
    ∃ s', runBlock isa (tableBody dir) s = some s' ∧ KInv s₀ b sched dir (m + 1) s' ∧
      s'.z = decide (m + 1 = 32) := by
  have hpre := hi.pre
  have hfit := hpre.fit
  have he := entOf_lt dir hm
  have hsched : Spec.Sm4.scheduleAt s.mem (State.addr sched) = Spec.Sm4.scheduleAt s₀.mem (State.addr sched) :=
    hpre.sched_eq (by rw [tableEnd_eq, slots_eq]; omega_arith) hi.frame
  obtain ⟨s₁, e₁, o₁, rd₁, wr₁, sp₁, f₁, E₁⟩ := keyOne_step (e := entOf dir m) hpre
    (by rw [hi.kpv, kpAtIter_ent dir hm]) he hi.ptr hm
  rw [hsched] at E₁
  have ko : ∀ r, r ≠ q 0 → r ≠ q 3 → r ≠ t1 → s₁.gpr r = s.gpr r := o₁
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := addImm_ok s₁ .r12 .r12 4 (by decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := kpStep_ok dir s₂ (b := b) hm
    (by rw [o₂ _ (by decide), ko kp (by decide) (by decide) (by decide), hi.kpv])
  obtain ⟨s₄, e₄, c₄, z₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := subs1_ok s₃ .lr
  have hc₃ : s₃.gpr .lr = BitVec.ofNat 32 (32 - m) := by
    rw [o₃ _ (by decide), o₂ _ (by decide), ko .lr (by decide) (by decide) (by decide), hi.cnt]
  have hmem : s₄.mem = s₁.mem := by rw [m₄, m₃, m₂]
  have hb₄ : s₄.gpr sb = s.gpr sb := by
    rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), ko sb (by decide) (by decide) (by decide)]
  have hf₁ : Frame [⟨State.addr b, 4 * tableEnd⟩] s₀.mem s₁.mem :=
    hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact entry_sub hfit he⟩)
  refine ⟨s₄, ?_, ⟨hpre.congr hb₄ (by rw [rd₄, rd₃, rd₂, rd₁]) (by rw [wr₄, wr₃, wr₂, wr₁]),
      by rw [o₄ _ (by decide), r₃], ?_, ?_, fun i hi' => ?_, by rw [hmem]; exact hf₁,
      fun r h0 h3 h11 h12 hk hl => by rw [o₄ r hl, o₃ r hk, o₂ r h12, ko r h0 h3 h11, hi.regs r h0 h3 h11 h12 hk hl],
      by rw [rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₄, wr₃, wr₂, wr₁, hi.wr], by rw [sp₄, sp₃, sp₂, sp₁, hi.sp]⟩, ?_⟩
  · rw [tableBody, runBlock_app, e₁, Option.bind_some,
      show ([.dp .add .r12 .r12 (.imm 4), kpStep dir, .subs .lr .lr (.imm 1)] : List Instr) =
        [.dp .add .r12 .r12 (.imm 4)] ++ ([kpStep dir] ++ [.subs .lr .lr (.imm 1)]) from rfl,
      runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [o₄ _ (by decide), o₃ _ (by decide), r₂, ko .r12 (by decide) (by decide) (by decide), hi.ptr,
      show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_ofNat, show 4 * m + 4 = 4 * (m + 1) by omega_arith]
  · rw [c₄, hc₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
      show 32 - m - 1 = 32 - (m + 1) by omega_arith]
  · rw [hmem]
    rcases (show i < m ∨ i = m by omega_arith) with hlt | rfl
    · exact (hi.ent i hlt).congr fun j hj => entryW_frame hfit f₁ (entOf_lt dir (by omega_arith)) he
        (fun h => by have := entOf_inj dir (by omega_arith) hm h; omega_arith) hj
    · exact E₁
  · rw [z₄, hc₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
      ofNat32_beq_zero (by omega_arith)]
    simp only [decide_eq_decide]; omega_arith

theorem keyLoop_wp (dir : Dir) {s₀ s : State} {b sched : BitVec 32} (hi : KInv s₀ b sched dir 0 s) :
    WP isa (.loop (.block (tableBody dir)) .ne) s (KInv s₀ b sched dir 32) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 32 - m ∧ m < 32 ∧ KInv s₀ b sched dir m s)
    (fun n s hs => ?_) 32 s ⟨0, rfl, by omega_arith, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := keyIter_ok dir hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h32 : m + 1 = 32
  · exact .inl ⟨by rw [eval_ne, z', h32]; rfl, by rw [h32] at hi'; exact hi'⟩
  · exact .inr ⟨by rw [eval_ne, z']; simp [h32], 32 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith, hi'⟩

/-- The round keys in the order the rounds use them. -/
def dirKeys (dir : Dir) (sch : Spec.Sm4.Schedule) (e : Nat) : Spec.Sm4.Word := sch.getD (entOf dir e) 0

/-- What the table's construction leaves. -/
structure KeysPost (s₀ : State) (b sched : BitVec 32) (dir : Dir) (s : State) : Prop where
  pre : SchedPre s b sched
  key : KeyCtx s (dirKeys dir (Spec.Sm4.scheduleAt s₀.mem (State.addr sched)))
  frame : Frame [⟨State.addr b, 4 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ q 0 → r ≠ q 3 → r ≠ t1 → r ≠ .r12 → r ≠ kp → r ≠ .lr → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- `mov d, #v` (`v` encodable). -/
theorem movImm_ok (s : State) (d : Reg) (v : BitVec 32) (hv : encodable v = true) :
    ∃ s', runBlock isa [.mov d (.imm v)] s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d v, by
    rw [runBlock_cons, show exec (.mov d (.imm v)) s = some (s.setReg d v) by simp [exec, Op2.eval, hv],
      runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : BitVec 32} (hp : SchedPre s₀ b sched)
    (hr : s₀.gpr .r12 = sched) :
    WP isa (keys dir) s₀ (KeysPost s₀ b sched dir) := by
  rw [keys_eq]
  let k := match dir with | .encrypt => tableSlot | .decrypt => tableSlot + 8 * 31
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := kpAt_ok s₀ k (by cases dir <;> decide)
  obtain ⟨s₂, e₂, l₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movImm_ok s₁ .lr 32 (by decide)
  have hinv : KInv s₀ b sched dir 0 s₂ := by
    refine ⟨hp.congr (by rw [o₂ _ (by decide), o₁ _ (by decide)]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]),
      by rw [o₂ _ (by decide), k₁, hp.base]; cases dir <;> rfl,
      by rw [o₂ _ (by decide), o₁ _ (by decide), hr]; simp,
      by rw [l₂]; rfl, fun i hi => by omega_arith, by rw [m₂, m₁]; exact Frame.refl _ _,
      fun r _ _ _ _ hk hl => by rw [o₂ r hl, o₁ r hk], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁]⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, ?_, WP.mono (keyLoop_wp dir hinv) fun s h => ?_⟩)
  · rw [show ([kpAt k, .mov .lr (.imm 32)] : List Instr) = [kpAt k] ++ [.mov .lr (.imm 32)] from rfl,
      runBlock_app, e₁, Option.bind_some, e₂]
  · refine ⟨h.pre, ⟨by rw [h.pre.base]; exact h.pre.scr, by rw [h.pre.base]; exact h.pre.fit, fun e he => ?_⟩,
      h.frame, h.regs, h.rd, h.wr, h.sp⟩
    rw [h.pre.base]
    have := h.ent (entOf dir e) (entOf_lt dir he)
    rw [entOf_entOf dir he] at this
    exact this

end VG.Proof.Sm4.Arm
