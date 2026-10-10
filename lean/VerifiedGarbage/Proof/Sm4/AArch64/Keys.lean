import VerifiedGarbage.Proof.Sm4.AArch64.Crypt16

/-!
# The table of bitsliced round keys on AArch64

`keyOne_step`: `keyOne h` bitslices round key `2 m + h`, half `h` of the
64-bit word at `x0`, into the table's entry at `kp`, every block's copy of
it alike. `keys_wp` builds the table in the order the rounds use the round
keys: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption.
-/

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Sm4.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 movR)
open VG.AArch64.Straight (linEnvG linPostG linG_ok)
open VG.Proof.Sm4 (WordRel readW64_bit getLsbD_scheduleAt)

/-- Round key `2 m + h`, half `h` of the 64-bit word `x`. -/
def rkWord (x : BitVec 64) (h : Nat) : Spec.Sm4.Word := (x >>> (32 * h)).setWidth 32

theorem keyStore_eq (h : Nat) : keyOne h = keyLoad h ++ keyStore := rfl

/-- Round key `2 m + h` from the word at `x0` to the entry at `kp`. -/
theorem keyOne_step {s : State} {b : Addr} {e h : Nat} (hh : h = 0 ∨ h = 1)
    (hb : s.gpr sb = b) (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hkp : s.gpr kp = b + BitVec.ofNat 64 (8 * tableSlot + 64 * e)) (he : e < 32)
    (hx0 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .x0) 0) 8)
    (hsep : ∀ k < 64, Mem.Sep (wordAddr b k) 8 (wordAddr (s.gpr .x0) 0) 8)
    (hm : MasksOk s) :
    ∃ s', runBlock isa (keyOne h) s = some s' ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ MasksOk s' ∧
      Frame [⟨b, 8 * 64⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot + 64 * e), 64⟩] s.mem s'.mem ∧
      WordRel (entryW s'.mem b e) (fun _ => rkWord (s.mem.readW (wordAddr (s.gpr .x0) 0) 64) h) := by
  rw [slots_eq] at hscr
  have hok : Ok keyCfg s :=
    { slotIn := fun k hk => ⟨_, hscr, by
        simp only [keyCfg] at hk ⊢
        rw [hb]; exact VG.Offset.contains_base b (by omega) (by omega)⟩
      extIn := fun k hk => by simp only [keyCfg] at hk ⊢; obtain rfl : k = 0 := by omega
                              exact hx0
      slots := by simp [keyCfg]
      sep := fun k hk j hj => by
        simp only [keyCfg] at hk hj ⊢; obtain rfl : j = 0 := by omega
        rw [hb]; exact hsep k hk }
  have hchk : check (lanes 64 7) keyCfg (linExt 0) (keyLoad h) keyEnv
      (linPostG 7 (qOuts (keyBsG h)) [] keyMaskSlots keyEnv) = true := by
    rcases hh with rfl | rfl
    · exact keyLoad0_check
    · exact keyLoad1_check
  unfold keyEnv at hchk
  obtain ⟨s₁, e₁, ho₁, -, hkp₁, rd₁, wr₁, -, o₁, f₁, hb₁, -⟩ := linG_ok hchk hok
    (fun k => s.mem.readW (wordAddr (s.gpr .x0) k) 64)
    (fun r i hri => by simp at hri) (fun j i hji => by simp at hji)
    (fun kv hkv => ⟨by simp only [keyCfg]; exact mask_lt hkv, by simp only [keyCfg]; exact hm kv hkv⟩)
    (fun j hj => ⟨by simp only [keyCfg] at hj; omega, by simp only [keyCfg, Nat.zero_add]⟩)
  simp only [keyCfg] at hb₁ hkp₁ f₁
  have hall₁ : ∀ r, r ∉ layerWrites → ((keyLoad h).all fun i => dstOf i != some r) = true := fun r hr => by
    have : (layerKeep.all fun r => (keyLoad h).all fun i => dstOf i != some r) =
        true := by rcases hh with rfl | rfl <;> decide +kernel
    exact List.all_eq_true.mp this r (not_layerWrites r hr)
  have k₁ : ∀ r, r ∉ layerWrites → s₁.gpr r = s.gpr r := fun r hr => o₁ r (hall₁ r hr)
  -- The planes of the round key.
  have hQ : WordRel (Qs s₁) (fun _ => rkWord (s.mem.readW (wordAddr (s.gpr .x0) 0) 64) h) := by
    intro b' hb' i hi j hj
    have hp : 16 * i + b' < 64 := by omega
    rw [Qs, ho₁ (q j) (keyBsG h j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      _ hp, keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
      show 32 * h + 8 * (3 - (16 * i + b') / 16) + j = 64 * 0 + (32 * h + 8 * (3 - i) + j) by omega,
      bitOf_word _ _ _ (by rcases hh with rfl | rfl <;> omega), rkWord, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight]
    simp only [show 8 * (3 - i) + j < 32 by omega, decide_true, Bool.true_and]
    exact congrArg (BitVec.getLsbD _) (by omega)
  -- The stores.
  have hkp₁' : s₁.gpr kp = s.gpr kp := k₁ kp (by decide)
  have hok₂ : Ok entryCfg s₁ :=
    { slotIn := fun k hk => ⟨_, by rw [wr₁]; exact hscr, by
        simp only [entryCfg] at hk ⊢
        rw [hkp₁', hkp, wordAddr, addr_add, tableSlot_eq]
        exact VG.Offset.contains_base b (by omega) (by omega)⟩
      extIn := fun k hk => by simp [entryCfg] at hk
      slots := by simp [entryCfg]
      sep := fun k _ j hj => by simp [entryCfg] at hj }
  have hchk₂ := keyStore_check
  unfold entryEnv at hchk₂
  obtain ⟨s₂, e₂, -, hso₂, -, rd₂, wr₂, -, o₂, f₂, hb₂, -⟩ := linG_ok hchk₂ hok₂ (Qs s₁)
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega, rfl⟩)
    (fun j i hji => by simp at hji) (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [entryCfg] at hj)
  simp only [entryCfg] at hb₂ hso₂ f₂
  have k₂ : ∀ r, s₂.gpr r = s₁.gpr r := fun r => o₂ r (by simp [keyStore, dstOf])
  have he₂ : ∀ j < 8, entryW s₂.mem b e j = Qs s₁ j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    have h := hso₂ j (fun p => [64 * j + p]) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      hj p hp
    rw [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp] at h
    rw [← h, entryW, wordAddr, hkp₁', hkp, addr_add]
  refine ⟨s₂, ?_, fun r hr => by rw [k₂, k₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun kv hkv => ?_,
    ?_, hQ.congr fun j hj => he₂ j hj⟩
  · rw [keyStore_eq, runBlock_app, e₁, Option.bind_some, e₂]
  · have hk : kv.1 < 64 := mask_lt hkv
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    have h2 : s₂.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = s₁.mem.readW (wordAddr (s.gpr sb) kv.1) 64 := by
      refine f₂.readW (r := ⟨wordAddr (s.gpr sb) kv.1, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [slotRegion, List.mem_singleton] at hr; subst hr
      rw [hkp₁', hkp, hb, wordAddr]
      rw [tableSlot_eq]
      exact VG.Offset.disjoint b (Or.inl (by omega)) (by omega) (by omega)
    rw [k₂, hb₁, h2, hkp₁ kv.1 (List.mem_map_of_mem hkv) hk]
    exact hm kv hkv
  · refine (f₁.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr; simp [hb]
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr
      simp [hkp₁', hkp]

/-! ## Steps of the pointers and the counter -/

theorem addI_ok (s : State) (d n : Reg) {imm : Nat} (h : imm < 4096) :
    ∃ s', runBlock isa [.addImm .x d n imm] s = some s' ∧ s'.gpr d = s.gpr n + BitVec.ofNat 64 imm ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (s.gpr n + BitVec.ofNat 64 imm), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x h, read_x'],
    (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _),
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩

theorem subI_ok (s : State) (d n : Reg) {imm : Nat} (h : imm < 4096) :
    ∃ s', runBlock isa [.subImm .x d n imm] s = some s' ∧ s'.gpr d = s.gpr n - BitVec.ofNat 64 imm ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (s.gpr n - BitVec.ofNat 64 imm), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_subImm_x h, read_x'],
    (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _),
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩

theorem movz_ok (s : State) (d : Reg) {v : Nat} (hv : v < 65536) :
    ∃ s', runBlock isa [.movz .x d (BitVec.ofNat 16 v) 0] s = some s' ∧ s'.gpr d = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x d ((BitVec.ofNat 16 v).setWidth 64 <<< (16 * 0)), ?_, ?_,
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩
  · simp only [runBlock_cons]; rfl
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

/-! ## The loop -/

/-- The entry of round key `i`: `i` for encryption, `31 - i` for decryption. -/
def entOf : Dir → Nat → Nat
  | .encrypt, i => i
  | .decrypt, i => 31 - i

/-- `kp` before iteration `m`, as an offset in the scratch buffer. -/
def rsiAt : Dir → Nat → Nat
  | .encrypt, m => 8 * tableSlot + 128 * m
  | .decrypt, m => 8 * tableSlot - 64 + 64 * (32 - 2 * m)

/-- The instruction stepping `kp`. -/
def kpStep : Dir → Instr
  | .encrypt => .addImm .x kp kp 64
  | .decrypt => .subImm .x kp kp 64

theorem keyBody_eq (dir : Dir) :
    (match dir with | .encrypt => encKeys | .decrypt => decKeys) =
      .seq (.block (slotAddr kp (match dir with | .encrypt => tableSlot | .decrypt => tableSlot + 8 * 31) ++
          ([.movz .x .x3 16 0] : List Instr)))
        (.loop (.block (keyOne 0 ++ ([kpStep dir] : List Instr) ++ keyOne 1 ++
          ([kpStep dir, .addImm .x .x0 .x0 8, .subImm .x .x3 .x3 1] : List Instr))) (.nonzero .x .x3)) := by
  cases dir <;> rfl

/-- `kp` moves from `x` to `y`. -/
def RsiStep : Dir → Nat → Nat → Prop
  | .encrypt, x, y => y = x + 64
  | .decrypt, x, y => x = y + 64

/-- `kp ± 64`. -/
theorem rsiStep_ok (dir : Dir) (s : State) {b : Addr} {x y : Nat} (hxy : RsiStep dir x y)
    (hkp : s.gpr kp = b + BitVec.ofNat 64 x) :
    ∃ s', runBlock isa [kpStep dir] s = some s' ∧
      s'.gpr kp = b + BitVec.ofNat 64 y ∧
      (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases dir
  · obtain ⟨s', e', r', o', m', rd', wr'⟩ := addI_ok s kp kp (imm := 64) (by decide)
    refine ⟨s', e', ?_, o', m', rd', wr'⟩
    rw [r', hkp, addr_add, show y = x + 64 from hxy]
  · obtain ⟨s', e', r', o', m', rd', wr'⟩ := subI_ok s kp kp (imm := 64) (by decide)
    refine ⟨s', e', ?_, o', m', rd', wr'⟩
    have hxy : x = y + 64 := hxy
    rw [r', hkp, VG.Offset.add_ofNat_sub _ (by omega), show x - 64 = y by omega]

/-- The scratch buffer at `b` and the schedule at `sched`, apart. -/
structure SchedPre (s : State) (b sched : Addr) : Prop where
  base : s.gpr sb = b
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  sch : (⟨sched, 128⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 128 ≤ 2 ^ 64
  sep : Region.Disjoint ⟨sched, 128⟩ ⟨b, 8 * slots⟩

theorem SchedPre.congr {s s' : State} {b sched : Addr} (h : SchedPre s b sched) (hb : s'.gpr sb = s.gpr sb)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : SchedPre s' b sched :=
  ⟨hb.trans h.base, hwr ▸ h.scr, h.fit, hrd ▸ hwr ▸ h.sch, h.schFit, h.sep⟩

theorem SchedPre.rdiIn {s : State} {b sched : Addr} (h : SchedPre s b sched) {m : Nat} (hm : m < 16) :
    InRegions (s.rd ++ s.wr) (wordAddr (sched + BitVec.ofNat 64 (8 * m)) 0) 8 :=
  ⟨_, h.sch, by rw [wordAddr, addr_add]; exact VG.Offset.contains_base sched (by omega) (by omega)⟩

theorem SchedPre.rdiSep {s : State} {b sched : Addr} (h : SchedPre s b sched) {m : Nat} (hm : m < 16)
    {k : Nat} (hk : k < 64) : Mem.Sep (wordAddr b k) 8 (wordAddr (sched + BitVec.ofNat 64 (8 * m)) 0) 8 := by
  have hf := h.fit
  rw [slots_eq] at hf
  refine h.sep.symm.sep (VG.Offset.contains_base b (by rw [slots_eq]; omega) (by omega)) ?_
  rw [wordAddr, addr_add]; exact VG.Offset.contains_base sched (by omega) (by omega)

/-- The schedule's round keys `2 m` and `2 m + 1`, as halves of its word `m`. -/
theorem rkWord_eq (mem : Mem) (sched : Addr) {m h : Nat} (hm : m < 16) (hh : h < 2) :
    rkWord (mem.readW (wordAddr (sched + BitVec.ofNat 64 (8 * m)) 0) 64) h =
      (Spec.Sm4.scheduleAt mem sched).getD (2 * m + h) 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi : 2 * m + h < 32 := by omega
  rw [VG.Proof.Aes.getD_eq _ hi, show k = 8 * (k / 8) + k % 8 by omega, VG.Proof.Sm4.getLsbD_scheduleAt _ _ hi (by omega) (by omega),
    rkWord, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  simp only [show 8 * (k / 8) + k % 8 < 32 by omega, decide_true, Bool.true_and]
  rw [show 32 * h + (8 * (k / 8) + k % 8) = 8 * (4 * h + k / 8) + k % 8 by omega,
    readW64_bit _ _ (by omega) (by omega), wordAddr, addr_add, addr_add]
  rw [show 8 * m + (8 * 0 + (4 * h + k / 8)) = 4 * (2 * m + h) + k / 8 by omega]

/-- An entry outside a frame keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : Addr} {e i : Nat}
    (hf : Frame [⟨b, 8 * 64⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot + 64 * e), 64⟩] m m')
    (hi : i < 32) (he : e < 32) (hie : i ≠ e) {j : Nat} (hj : j < 8) : entryW m' b i j = entryW m b i j := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [tableSlot_eq] at *
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base b (by omega) (by omega)
  · exact VG.Offset.disjoint b (by omega) (by omega) (by omega)

/-- What the loop keeps, after `m` of its 16 iterations. -/
structure KInv (s₀ : State) (b sched : Addr) (dir : Dir) (m : Nat) (s : State) : Prop where
  pre : SchedPre s b sched
  rsi : s.gpr kp = b + BitVec.ofNat 64 (rsiAt dir m)
  rdi : s.gpr .x0 = sched + BitVec.ofNat 64 (8 * m)
  cnt : s.gpr .x3 = BitVec.ofNat 64 (16 - m)
  ent : ∀ i < 2 * m, WordRel (entryW s.mem b (entOf dir i))
    (fun _ => (Spec.Sm4.scheduleAt s₀.mem sched).getD i 0)
  masks : MasksOk s
  frame : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ∉ layerWrites → r ≠ kp → r ≠ .x0 → r ≠ .x3 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem entOf_lt (dir : Dir) {i : Nat} (hi : i < 32) : entOf dir i < 32 := by cases dir <;> simp [entOf] <;> omega

theorem entOf_inj (dir : Dir) {i i' : Nat} (hi : i < 32) (hi' : i' < 32) (h : entOf dir i = entOf dir i') :
    i = i' := by cases dir <;> simp [entOf] at h <;> omega

theorem rsiAt_ent (dir : Dir) {m : Nat} (hm : m < 16) :
    rsiAt dir m = 8 * tableSlot + 64 * entOf dir (2 * m) := by
  cases dir <;> simp only [rsiAt, entOf, tableSlot_eq] <;> omega

/-- The schedule is outside the scratch buffer. -/
theorem SchedPre.sched_eq' {s : State} {b sched : Addr} (h : SchedPre s b sched) {m m' : Mem} {n : Nat}
    (hn : n ≤ slots) (hf : Frame [⟨b, 8 * n⟩] m m') :
    Spec.Sm4.scheduleAt m' sched = Spec.Sm4.scheduleAt m sched := by
  have hb : ∀ k < 128, m' (sched + BitVec.ofNat 64 k) = m (sched + BitVec.ofNat 64 k) := fun k hk =>
    hf.bytes (R := ⟨sched, 128⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.sep.sub_right (Region.sub_prefix (by omega))) (by show 128 ≤ 2 ^ 64; omega) hk
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
  rw [hb (4 * i + 0) (by omega), hb (4 * i + 1) (by omega), hb (4 * i + 2) (by omega), hb (4 * i + 3) (by omega)]

theorem SchedPre.sched_eq {s : State} {b sched : Addr} (h : SchedPre s b sched) {m m' : Mem}
    (hf : Frame [⟨b, 8 * tableEnd⟩] m m') :
    Spec.Sm4.scheduleAt m' sched = Spec.Sm4.scheduleAt m sched :=
  h.sched_eq' (by rw [tableEnd_eq, slots_eq]; omega) hf

theorem rsiAt_succ (dir : Dir) {m : Nat} (hm : m < 16) :
    RsiStep dir (rsiAt dir m) (8 * tableSlot + 64 * entOf dir (2 * m + 1)) ∧
    RsiStep dir (8 * tableSlot + 64 * entOf dir (2 * m + 1)) (rsiAt dir (m + 1)) := by
  cases dir <;> simp only [RsiStep, rsiAt, entOf, tableSlot_eq] <;> omega

/-- One iteration: round keys `2 m` and `2 m + 1`. -/
theorem keyIter_ok (dir : Dir) {s₀ s : State} {b sched : Addr} {m : Nat} (hm : m < 16)
    (hi : KInv s₀ b sched dir m s) :
    ∃ s', runBlock isa (keyOne 0 ++ ([kpStep dir] : List Instr) ++ keyOne 1 ++
        ([kpStep dir, .addImm .x .x0 .x0 8, .subImm .x .x3 .x3 1] : List Instr)) s = some s' ∧
      KInv s₀ b sched dir (m + 1) s' ∧ (s'.gpr .x3 == 0) = decide (m + 1 = 16) := by
  have hpre := hi.pre
  have hfit := hpre.fit
  have he0 := entOf_lt dir (show 2 * m < 32 by omega)
  have he1 := entOf_lt dir (show 2 * m + 1 < 32 by omega)
  have hsched : Spec.Sm4.scheduleAt s.mem sched = Spec.Sm4.scheduleAt s₀.mem sched :=
    hpre.sched_eq hi.frame
  -- Round key `2 m`.
  obtain ⟨s₁, e₁, o₁, rd₁, wr₁, m₁, f₁, E₁⟩ := keyOne_step (h := 0) (e := entOf dir (2 * m)) (Or.inl rfl)
    hpre.base hpre.scr (by rw [hi.rsi, rsiAt_ent dir hm]) he0 (by rw [hi.rdi]; exact hpre.rdiIn hm)
    (fun k hk => by rw [hi.rdi]; exact hpre.rdiSep hm hk) hi.masks
  rw [hi.rdi, rkWord_eq _ _ hm (by decide), hsched] at E₁
  obtain ⟨st1, st2⟩ := rsiAt_succ dir hm
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := rsiStep_ok dir s₁ (b := b) (x := rsiAt dir m)
    (y := 8 * tableSlot + 64 * entOf dir (2 * m + 1)) st1
    (by rw [o₁ _ (by decide), hi.rsi])
  have hpre₂ : SchedPre s₂ b sched :=
    hpre.congr (by rw [o₂ _ (by decide), o₁ _ (by decide)]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have hrdi₂ : s₂.gpr .x0 = sched + BitVec.ofNat 64 (8 * m) := by
    rw [o₂ _ (by decide), o₁ _ (by decide), hi.rdi]
  have hm₂ : MasksOk s₂ := fun kv hkv => by
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, o₂ _ (by decide)]; exact m₁ kv hkv
  -- Round key `2 m + 1`.
  obtain ⟨s₃, e₃, o₃, rd₃, wr₃, m₃, f₃, E₃⟩ := keyOne_step (h := 1) (e := entOf dir (2 * m + 1)) (Or.inr rfl)
    hpre₂.base hpre₂.scr r₂ he1 (by rw [hrdi₂]; exact hpre₂.rdiIn hm)
    (fun k hk => by rw [hrdi₂]; exact hpre₂.rdiSep hm hk) hm₂
  have hfr₂ : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s₂.mem := by
    rw [m₂]
    refine hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [tableEnd_eq]
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by omega)
    · rw [tableSlot_eq]; exact VG.Offset.sub_base b (by omega)
  rw [hrdi₂, rkWord_eq _ _ hm (by decide), hpre₂.sched_eq hfr₂] at E₃
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := rsiStep_ok dir s₃ (b := b)
    (x := 8 * tableSlot + 64 * entOf dir (2 * m + 1)) (y := rsiAt dir (m + 1))
    st2 (by rw [o₃ _ (by decide), r₂])
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .x0 .x0 (imm := 8) (by decide)
  obtain ⟨s₆, e₆, c₆, o₆, m₆, rd₆, wr₆⟩ := subI_ok s₅ .x3 .x3 (imm := 1) (by decide)
  have ht₅ : s₅.gpr .x3 = BitVec.ofNat 64 (16 - m) := by
    rw [o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hi.cnt]
  have hmem : s₆.mem = s₃.mem := by rw [m₆, m₅, m₄]
  have hb₆ : s₆.gpr sb = s₃.gpr sb := by rw [o₆ _ (by decide), o₅ _ (by decide), o₄ _ (by decide)]
  have hf₃ : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s₃.mem := by
    refine hfr₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [tableEnd_eq]
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by omega)
    · rw [tableSlot_eq]; exact VG.Offset.sub_base b (by omega)
  refine ⟨s₆, ?_, ⟨hpre₂.congr (by rw [hb₆, o₃ _ (by decide)]) (by rw [rd₆, rd₅, rd₄, rd₃])
      (by rw [wr₆, wr₅, wr₄, wr₃]), by rw [o₆ _ (by decide), o₅ _ (by decide), r₄], ?_, ?_, fun i hi' => ?_,
      fun kv hkv => ?_, by rw [hmem]; exact hf₃, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩, ?_⟩
  · rw [runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃,
      Option.bind_some,
      show ([kpStep dir, .addImm .x .x0 .x0 8, .subImm .x .x3 .x3 1] : List Instr) =
        [kpStep dir] ++ ([.addImm .x .x0 .x0 8] ++ [.subImm .x .x3 .x3 1]) from rfl,
      runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, e₆]
  · rw [o₆ _ (by decide), r₅, o₄ _ (by decide), o₃ _ (by decide), hrdi₂, addr_add,
      show 8 * m + 8 = 8 * (m + 1) by omega]
  · rw [c₆, ht₅, VG.Offset.ofNat_sub_ofNat (by omega), show 16 - m - 1 = 16 - (m + 1) by omega]
  · have hent : ∀ i' < 32, i' ≠ entOf dir (2 * m) → i' ≠ entOf dir (2 * m + 1) → ∀ j < 8,
        entryW s₆.mem b i' j = entryW s.mem b i' j := fun i' hi'' h0 h1 j hj => by
      rw [hmem, entryW_frame f₃ hi'' he1 h1 hj, m₂, entryW_frame f₁ hi'' he0 h0 hj]
    rcases (show i < 2 * m ∨ i = 2 * m ∨ i = 2 * m + 1 by omega) with hlt | rfl | rfl
    · exact (hi.ent i hlt).congr fun j hj => hent _ (entOf_lt dir (by omega))
        (fun h => by have := entOf_inj dir (by omega) (by omega) h; omega)
        (fun h => by have := entOf_inj dir (by omega) (by omega) h; omega) j hj
    · refine E₁.congr fun j hj => ?_
      rw [hmem, entryW_frame f₃ he0 he1 (fun h => by have := entOf_inj dir (by omega) (by omega) h; omega) hj, m₂]
    · exact E₃.congr fun j hj => by rw [hmem]
  · show s₆.mem.readW (wordAddr (s₆.gpr sb) kv.1) 64 = kv.2
    rw [hmem, hb₆]; exact m₃ kv hkv
  · rw [o₆ r h4, o₅ r h3, o₄ r h2, o₃ r h1, o₂ r h2, o₁ r h1, hi.regs r h1 h2 h3 h4]
  · rw [c₆, ht₅, VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    simp only [decide_eq_decide]; omega

theorem entOf_entOf (dir : Dir) {e : Nat} (he : e < 32) : entOf dir (entOf dir e) = e := by
  cases dir <;> simp [entOf] <;> omega

/-- The round keys in the order the rounds use them. -/
def dirKeys (dir : Dir) (sch : Spec.Sm4.Schedule) (e : Nat) : Spec.Sm4.Word := sch.getD (entOf dir e) 0

/-- What the table's construction leaves. -/
structure KeysPost (s₀ : State) (b sched : Addr) (dir : Dir) (s : State) : Prop where
  pre : SchedPre s b sched
  key : KeyCtx s (dirKeys dir (Spec.Sm4.scheduleAt s₀.mem sched))
  masks : MasksOk s
  rdi : s.gpr .x3 = b + BitVec.ofNat 64 (8 * tableEnd)
  frame : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ∉ layerWrites → r ≠ kp → r ≠ .x0 → r ≠ .x3 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The loop's body. -/
def tableBody (dir : Dir) : List Instr :=
  keyOne 0 ++ ([kpStep dir] : List Instr) ++ keyOne 1 ++
    [kpStep dir, .addImm .x .x0 .x0 8, .subImm .x .x3 .x3 1]

theorem keyLoop_wp (dir : Dir) {s₀ s : State} {b sched : Addr} (hi : KInv s₀ b sched dir 0 s) :
    WP isa (.loop (.block (tableBody dir)) (.nonzero .x .x3)) s (KInv s₀ b sched dir 16) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 16 - m ∧ m < 16 ∧ KInv s₀ b sched dir m s)
    (fun n s hs => ?_) 16 s ⟨0, rfl, by omega, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := keyIter_ok dir hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h16 : m + 1 = 16
  · exact .inl ⟨by rw [eval_nonzero, z', h16]; rfl, by rw [h16] at hi'; exact hi'⟩
  · exact .inr ⟨by rw [eval_nonzero, z']; simp [h16], 16 - (m + 1), by omega, m + 1, rfl, by omega, hi'⟩

theorem keysGen_wp (dir : Dir) (k : Nat) (hk : 8 * k = rsiAt dir 0) (hse : 8 * k < 4096)
    {s₀ : State} {b sched : Addr} (hp : SchedPre s₀ b sched) (hrdi : s₀.gpr .x0 = sched) (hm : MasksOk s₀) :
    WP isa (.seq (.seq (.block (slotAddr kp k ++ ([.movz .x .x3 16 0] : List Instr)))
        (.loop (.block (tableBody dir)) (.nonzero .x .x3)))
      (.block (slotAddr .x3 tableEnd))) s₀ (KeysPost s₀ b sched dir) := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s₀ kp k hse
  obtain ⟨s₂, e₂, t₂, o₂, m₂, rd₂, wr₂⟩ := movz_ok s₁ .x3 (v := 16) (by decide)
  have hinv : KInv s₀ b sched dir 0 s₂ := by
    refine ⟨hp.congr (by rw [o₂ _ (by decide), o₁ _ (by decide)]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]),
      by rw [o₂ _ (by decide), r₁, hp.base, hk], by rw [o₂ _ (by decide), o₁ _ (by decide), hrdi]; simp,
      by rw [t₂], fun i hi => by omega, fun kv hkv => ?_, by rw [m₂, m₁]; exact Frame.refl _ _,
      fun r _ h2 _ h4 => by rw [o₂ r h4, o₁ r h2], by rw [rd₂, rd₁],
      by rw [wr₂, wr₁]⟩
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, m₁, o₂ _ (by decide), o₁ _ (by decide)]; exact hm kv hkv
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_app, e₁, Option.bind_some]; exact e₂,
    WP.mono (keyLoop_wp dir hinv) fun s h => ?_⟩))
  have hfit := h.pre.fit
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := slotAddr_ok s .x3 tableEnd (by decide)
  refine WP.of_runBlock ⟨s₃, e₃, h.pre.congr (o₃ _ (by decide)) rd₃ wr₃, ⟨?_, ?_, fun e he => ?_⟩, fun kv hkv => ?_,
    by rw [r₃, h.pre.base], by rw [m₃]; exact h.frame, fun r h1 h2 h3 h4 => by rw [o₃ r h4, h.regs r h1 h2 h3 h4],
    by rw [rd₃, h.rd], by rw [wr₃, h.wr]⟩
  · rw [wr₃, o₃ _ (by decide), h.pre.base]; exact h.pre.scr
  · rw [o₃ _ (by decide), h.pre.base]; exact hfit
  · rw [o₃ _ (by decide), h.pre.base, m₃]
    have := h.ent (entOf dir e) (by have := entOf_lt dir he; omega)
    rw [entOf_entOf dir he] at this
    exact this
  · show s₃.mem.readW (wordAddr (s₃.gpr sb) kv.1) 64 = kv.2
    rw [m₃, o₃ _ (by decide)]; exact h.masks kv hkv

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : Addr} (hp : SchedPre s₀ b sched)
    (hrdi : s₀.gpr .x0 = sched) (hm : MasksOk s₀) :
    WP isa (keys dir) s₀ (KeysPost s₀ b sched dir) := by
  cases dir
  · exact keysGen_wp .encrypt tableSlot (by simp [rsiAt]) (by decide) hp hrdi hm
  · exact keysGen_wp .decrypt (tableSlot + 8 * 31) (by simp [rsiAt, tableSlot_eq]) (by decide) hp hrdi hm

end VG.Proof.Sm4.AArch64
