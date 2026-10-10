import VerifiedGarbage.Proof.Seed.Arm.Prologue

/-!
# A group of blocks of SEED ECB on ARMv7

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(eight, or the last one to seven) to the tail buffer, transforms it
(`crypt8_wp`), copies the blocks back and steps to the next group. The data
pointer and the blocks left live in their slots (`ptrSlot`, `cntSlot`) between
the steps, which use every other register.
-/

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Seed.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR lsrOp ldS stS)

/-! ## Small blocks -/

theorem lsr3_beq {v : Nat} (hv : v < 2 ^ 32) :
    (BitVec.ofNat 32 v >>> 3 - 0 == 0) = decide (v < 8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem movR_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [movR d n] s = some s' ∧ s'.gpr d = s.gpr n ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.gpr n), by
    rw [runBlock_cons, show exec (movR d n) s = some (s.setReg d (s.gpr n)) by simp [movR, exec, Op2.eval],
      runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `r3 := min(r2, 8)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hn : s.gpr .r2 = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa groupCount s fun s' => s'.gpr .r3 = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .r3 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₂ := s.setReg t0 (s.gpr .r2 >>> 3)
  let s₃ := subFlags s₂ (s₂.gpr t0) 0
  have e₂₃ : runBlock isa [.mov t0 (lsrOp .r2 3), .cmp t0 (.imm 0)] s = some s₃ := by
    rw [runBlock_cons, show exec (.mov t0 (lsrOp .r2 3)) s = some s₂ by simp [exec, Op2.eval, lsrOp, s₂],
      runStep_some, runBlock_cons,
      show exec (.cmp t0 (.imm 0)) s₂ = some s₃ by simp [exec, Op2.eval, s₃]; decide,
      runStep_some, runBlock_nil]
  have z₃ : s₃.z = (BitVec.ofNat 32 v >>> 3 - 0 == 0) := by
    show (s₂.gpr t0 - 0 == 0) = _; rw [RegUpd.gpr_setReg_self, hn]
  have o₃ : ∀ r, r ≠ t0 → s₃.gpr r = s.gpr r := fun r hr => by
    show s₂.gpr r = _; rw [RegUpd.gpr_setReg_of_ne _ _ hr]
  have r2₃ : s₃.gpr .r2 = BitVec.ofNat 32 v := by rw [o₃ _ (by decide), hn]
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₃, e₂₃, ?_⟩)
  refine WP.ite (decide (8 ≤ v)) ((eval_ne s₃).trans (by
      rw [z₃, lsr3_beq hv]; by_cases h : v < 8 <;> simp [h] <;> omega)) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movImm_ok s₃ .r3 8 (by decide)
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, Nat.min_eq_right (by simp at h; omega)]; rfl
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movR_ok s₃ .r3 .r2
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, r2₃, Nat.min_eq_left (by simp at h; omega)]

/-- `subs d, n, m`. -/
theorem subsR_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [.subs d n (.reg m)] s = some s' ∧ s'.gpr d = s.gpr n - s.gpr m ∧
      s'.z = (s.gpr n - s.gpr m == 0) ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨(subFlags s (s.gpr n) (s.gpr m)).setReg d (s.gpr n - s.gpr m), ?_, RegUpd.gpr_setReg_self _ _ _,
    by rw [RegUpd.z_setReg]; rfl, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr]; rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.subs d n (.reg m)) s =
    some ((subFlags s (s.gpr n) (s.gpr m)).setReg d (s.gpr n - s.gpr m)) by simp [exec, Op2.eval],
    runStep_some, runBlock_nil]

theorem toNat_add32 (D : BitVec 32) {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).toNat = D.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32), Nat.mod_eq_of_lt h]

/-! ## The scratch buffer's contents -/

/-- The slots `lo … hi - 1` of the scratch buffer at `b`. -/
abbrev slotsRegion (b : BitVec 32) (lo hi : Nat) : Region :=
  ⟨State.addr b + BitVec.ofNat 64 (4 * lo), 4 * (hi - lo)⟩

/-- A slot outside a frame. -/
theorem slot_keep {rs : List Region} {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {lo hi : Nat} (hhi : hi ≤ slots) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b lo hi).Disjoint r)
    {k : Nat} (hk1 : lo ≤ k) (hk2 : k < hi) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [slots_eq] at hfit hhi
  rw [slot_addr (by omega)]
  exact hf.readW (VG.Offset.contains _ (by omega) (by omega) (by omega)) hd (by decide)

/-- What the data loop keeps in the scratch buffer: the table and the saved
registers, in the slots from `tableSlot` to `ptrSlot`. -/
structure ScrOk (s₀ : State) (b : BitVec 32) (E : Nat → Spec.Seed.Word) (m : Mem) : Prop where
  keys : ∀ e < 32, m.readW (wordAddr b (tableSlot + e)) 32 = E e
  saved : Saved s₀ b m

theorem ScrOk.frame {s₀ : State} {b : BitVec 32} {E : Nat → Spec.Seed.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b tableSlot ptrSlot).Disjoint r) : ScrOk s₀ b E m' := by
  refine ⟨fun e he => ?_, fun i hi => ?_⟩
  · rw [← h.keys e he]
    exact slot_keep hfit (by decide) hf hd (by omega) (by rw [ptrSlot_eq, tableSlot_eq]; omega)
  · rw [← h.saved i hi]
    exact slot_keep hfit (by decide) hf hd (by rw [savedSlot_eq, tableSlot_eq]; omega)
      (by rw [savedSlot_eq, ptrSlot_eq]; omega)

/-! ## The data loop -/

/-- Round `j + 1`'s key, from the table's words `E`. -/
def keyPairs (E : Nat → Spec.Seed.Word) (j : Nat) : Spec.Seed.Word × Spec.Seed.Word := (E (2 * j), E (2 * j + 1))

/-- Each block, transformed: `crypt` with the table's round keys `E`. -/
def outF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Seed.Word) (j : Nat) : Spec.Seed.Block :=
  Spec.Seed.crypt (keyPairs E) (Spec.Seed.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))

theorem blockAt_getD (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (Spec.Seed.blockAt m p).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Seed.blockAt, Vector.getD, hi]

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : BitVec 32) (n : Nat) : Prop where
  scr : ScrIn s₀.wr b
  dat : (⟨State.addr D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr b, 4 * slots⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 32

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Seed.Word) (k : Nat) (s : State) :
    Prop where
  base : s.gpr sb = b
  dp : s.gpr .r1 = D + BitVec.ofNat 32 (128 * k)
  np : s.gpr .r2 = BitVec.ofNat 32 (n - 8 * k)
  lt : 8 * k < n
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n (8 * k) (outF s₀.mem (State.addr D) E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Seed.Word) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n n (outF s₀.mem (State.addr D) E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem dataGroup_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Seed.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa group s fun s' => (s'.z = true ∧ GDone s₀ b D n E s') ∨
      (s'.z = false ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  have hb := toNat_addr b
  rw [slots_eq] at hfit
  have hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega
  let v := n - 8 * k
  let c := min v 8
  have hv : v < 2 ^ 32 := by omega
  have hc0 : 0 < c := by omega
  have hc8 : c ≤ 8 := by omega
  have hkc : 128 * k + 16 * c ≤ 16 * n := by omega
  let A := D + BitVec.ofNat 32 (128 * k)
  let T := b + BitVec.ofNat 32 (4 * tailSlot)
  have hA : State.addr A = State.addr D + BitVec.ofNat 64 (128 * k) := addr_add (by omega)
  have hT : State.addr T = State.addr b + BitVec.ofNat 64 (4 * tailSlot) := addr_add (by rw [tailSlot_eq]; omega)
  have hAn : A.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega)]; omega
  have hTn : T.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by rw [tailSlot_eq]; omega), tailSlot_eq]; omega
  have hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  have hwD : (⟨State.addr D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have inT : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (State.addr T + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwS.mem, ?_⟩
    rw [hT, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by rw [slots_eq, tailSlot_eq]; omega) (by rw [tailSlot_eq]; omega)
  have inA : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (State.addr A + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwD, ?_⟩
    rw [hA, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega) (by omega)
  have subA : Region.Sub ⟨State.addr A, 16 * c⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [hA]; exact VG.Offset.sub_base _ (by omega)
  have subT : Region.Sub ⟨State.addr T, 16 * c⟩ ⟨State.addr b, 4 * slots⟩ := by
    rw [hT]; exact VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq]; omega)
  have sepAT : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr T, 16 * c⟩ :=
    (hp.sep.sub_left subA).sub_right subT
  -- The regions the steps write keep the slots from `tableSlot`.
  have dT : (slotsRegion b tableSlot slots).Disjoint ⟨State.addr T, 16 * c⟩ := by
    rw [hT]; exact VG.Offset.disjoint _ (by rw [tableSlot_eq, tailSlot_eq]; omega)
      (by rw [tableSlot_eq, slots_eq]; omega) (by rw [tailSlot_eq]; omega)
  have dA : (slotsRegion b tableSlot slots).Disjoint ⟨State.addr A, 16 * c⟩ :=
    ((hp.sep.sub_left subA).sub_right (VG.Offset.sub_base _ (by rw [tableSlot_eq, slots_eq]))).symm
  have dTab : (slotsRegion b tableSlot slots).Disjoint ⟨State.addr b, 4 * tableSlot⟩ :=
    VG.Offset.disjoint_base _ (by omega) (by rw [tableSlot_eq, slots_eq]; omega)
  have sub_ts : ∀ l u, tableSlot ≤ l → l ≤ u → u ≤ slots →
      (slotsRegion b l u).Sub (slotsRegion b tableSlot slots) :=
    fun l u h1 h2 h3 => VG.Offset.sub _ (by omega) (by rw [slots_eq] at h3 ⊢; omega)
  have subTab : (slotsRegion b tableSlot ptrSlot).Sub (slotsRegion b tableSlot slots) :=
    sub_ts _ _ (Nat.le_refl _) (by decide) (by decide)
  have dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨State.addr b, 4 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨State.addr D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  have r1₀ : s.gpr .r1 = A := hi.dp
  unfold group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.np hv) fun s₁ ⟨r3₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a, sp₂a⟩ := movR_ok s₁ .r0 .r1
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := addImm_ok s₂a .r12 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂a, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂a, wr₁]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₂a, m₁]
  have g₂ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h0 h12 h3 h4 => by rw [o₂ r h12, o₂a r h0, o₁ r h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show ([movR .r0 .r1, tailAddr .r12] : List Instr) = [movR .r0 .r1] ++ [tailAddr .r12] from rfl,
      runBlock_append, e₂a, Option.bind_some]; exact e₂, ?_⟩)
  refine WP.mono (copyBlocks_wp (A := A) (B := T) hc0 hc8 hAn hTn
    (fun t ht h4 => by rw [rd₂', wr₂']; exact inRd (inA t ht h4))
    (fun t ht h4 => by rw [wr₂']; exact inT t ht h4) sepAT
    ⟨by rw [o₂ _ (by decide), r₂a, o₁ _ (by decide) (by decide), r1₀]; simp [A],
      by rw [r₂, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base]; simp [T],
      by rw [o₂ _ (by decide), o₂a _ (by decide), r3₁, Nat.sub_zero], ⟨fun t ht => by omega, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₃ h₃ => ?_
  have f₃ : Frame [⟨State.addr T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.cp.frame
  have g₃ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h0 h12 h3 h4 => by rw [h₃.regs r h0 h12 h3 h4, g₂ r h0 h12 h3 h4]
  have base₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.base]
  have sc₃ : ScrOk s₀ b E s₃.mem := hi.scr.frame hfit' f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dT.sub_left subTab
  have wr₃ : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  have rd₃ : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  have sp₃ : s₃.sp = s.sp := by rw [h₃.sp, sp₂, sp₂a, sp₁]
  have hwS₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hwS
  -- The data pointer and the blocks left to their slots.
  unfold cryptSaved
  obtain ⟨s₄a, e₄a, m₄a, g₄a, rd₄a, wr₄a, sp₄a, -, f₄a⟩ := stSlot_ok s₃ .r1 sb (k := ptrSlot) base₃ (by decide) hwS₃
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, f₄⟩ := stSlot_ok s₄a .r2 sb (k := cntSlot) (by rw [g₄a, base₃])
    (by decide) (by rw [wr₄a]; exact hwS₃)
  have r1₃ : s₃.gpr .r1 = A := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), r1₀]
  have r2₃ : s₃.gpr .r2 = BitVec.ofNat 32 v := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.np]
  have fs : Frame [⟨wordAddr b ptrSlot, 4⟩, ⟨wordAddr b cntSlot, 4⟩] s₃.mem s₄.mem :=
    (f₄a.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f₄.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  have hsub : ∀ r ∈ [(⟨wordAddr b ptrSlot, 4⟩ : Region), ⟨wordAddr b cntSlot, 4⟩],
      Region.Sub r ⟨State.addr b, 4 * slots⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact slot_sub hfit' (by decide)
    · exact slot_sub hfit' (by decide)
  have dsTab : ∀ r ∈ [(⟨wordAddr b ptrSlot, 4⟩ : Region), ⟨wordAddr b cntSlot, 4⟩],
      (slotsRegion b tableSlot ptrSlot).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [ptrSlot_eq, cntSlot_eq]); omega)] <;>
      exact VG.Offset.disjoint _ (by (try simp only [tableSlot_eq, ptrSlot_eq, cntSlot_eq]); omega)
        (by (try simp only [tableSlot_eq, ptrSlot_eq]); omega) (by (try simp only [ptrSlot_eq, cntSlot_eq]); omega)
  have sc₄ : ScrOk s₀ b E s₄.mem := sc₃.frame hfit' fs dsTab
  have base₄ : s₄.gpr sb = b := by rw [g₄, g₄a, base₃]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₄a, wr₃]
  have dp₄ : s₄.mem.readW (wordAddr b ptrSlot) 32 = A := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_right (by decide), m₄a,
      readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, r1₃]
  have np₄ : s₄.mem.readW (wordAddr b cntSlot) 32 = BitVec.ofNat 32 v := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, g₄a, r2₃]
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([stS ptrSlot .r1, stS cntSlot .r2] : List Instr) =
      [.str .r1 sb (4 * ptrSlot)] ++ [.str .r2 sb (4 * cntSlot)] from rfl, runBlock_append, e₄a, Option.bind_some, e₄],
    ?_⟩))
  -- The eight blocks.
  have hR₄ : Room s₄ := ⟨by unfold scratchR; rw [base₄, wr₄']; exact hwS.mem, by rw [base₄]; exact hfit'⟩
  refine WP.seq (WP.mono (crypt8_wp hR₄) fun s₅ ⟨b₅, _, rd₅', wr₅', sp₅', sb₅, sl₅, f₅'⟩ => ?_)
  have base₅ : s₅.gpr sb = b := by rw [sb₅, base₄]
  have f₅ : Frame [⟨State.addr b, 4 * tableSlot⟩] s₄.mem s₅.mem := by rw [base₄] at f₅'; exact f₅'
  have keep₅ : ∀ j, tableSlot ≤ j → j < slots → s₅.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => by have := sl₅ j h1 h2; simp only [slotW, sb₅, base₄] at this; exact this
  have sc₅ : ScrOk s₀ b E s₅.mem := sc₄.frame hfit' f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dTab.sub_left subTab
  have hk₄ : ∀ j < 16, tableKeys s₄ j = keyPairs E j := fun j hj => by
    simp only [tableKeys, keyPairs, slotW, base₄]
    rw [sc₄.keys _ (by omega), show tableSlot + 2 * j + 1 = tableSlot + (2 * j + 1) by omega,
      sc₄.keys _ (by omega)]
  have wr₅ : s₅.wr = s.wr := by rw [wr₅', wr₄']
  have rd₅ : s₅.rd = s.rd := by rw [rd₅', rd₄, rd₄a, rd₃]
  have sp₅ : s₅.sp = s.sp := by rw [sp₅', sp₄, sp₄a, sp₃]
  have hwS₅ : ScrIn s₅.wr b := by rw [wr₅]; exact hwS
  -- The data pointer and the blocks left back.
  obtain ⟨s₆a, e₆a, r₆a, o₆a, m₆a, rd₆a, wr₆a, sp₆a⟩ := ldSlot_ok s₅ .r1 sb (k := ptrSlot) base₅ (by decide) hwS₅
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := ldSlot_ok s₆a .r2 sb (k := cntSlot)
    (by rw [o₆a _ (by decide), base₅]) (by decide) (by rw [wr₆a]; exact hwS₅)
  refine WP.of_runBlock ⟨s₆, by
    rw [show ([ldS .r1 ptrSlot, ldS .r2 cntSlot] : List Instr) =
      [.ldr .r1 sb (4 * ptrSlot)] ++ [.ldr .r2 sb (4 * cntSlot)] from rfl, runBlock_append, e₆a, Option.bind_some, e₆],
    ?_⟩
  have r1₆ : s₆.gpr .r1 = A := by rw [o₆ _ (by decide), r₆a, keep₅ _ (by decide) (by decide), dp₄]
  have r2₆ : s₆.gpr .r2 = BitVec.ofNat 32 v := by rw [r₆, m₆a, keep₅ _ (by decide) (by decide), np₄]
  have base₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₆a _ (by decide), base₅]
  have mem₆ : s₆.mem = s₅.mem := by rw [m₆, m₆a]
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₆a, wr₅]
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₆a, rd₅]
  have sp₆' : s₆.sp = s.sp := by rw [sp₆, sp₆a, sp₅]
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r2₆ hv) fun s₇ ⟨r3₇, o₇, m₇, rd₇, wr₇, sp₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a, sp₈a⟩ := addImm_ok s₇ .r0 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈, sp₈⟩ := movR_ok s₈a .r12 .r1
  have mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈a, m₇, mem₆]
  have g₈ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₈.gpr r = s₆.gpr r :=
    fun r h0 h12 h3 h4 => by rw [o₈ r h12, o₈a r h0, o₇ r h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [show ([tailAddr .r0, movR .r12 .r1] : List Instr) =
      [.dp .add .r0 sb (.imm (BitVec.ofNat 32 (4 * tailSlot)))] ++ [movR .r12 .r1] from rfl,
      runBlock_append, e₈a, Option.bind_some]; exact e₈, ?_⟩)
  have rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈a, rd₇, rd₆']
  have wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈a, wr₇, wr₆']
  refine WP.mono (copyBlocks_wp (A := T) (B := A) hc0 hc8 hTn hAn
    (fun t ht h4 => by rw [rd₈', wr₈']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [wr₈']; exact inA t ht h4) sepAT.symm
    ⟨by rw [o₈ _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₆]; simp [T],
      by rw [r₈, o₈a _ (by decide), o₇ _ (by decide) (by decide), r1₆]; simp [A],
      by rw [o₈ _ (by decide), o₈a _ (by decide), r3₇, Nat.sub_zero], ⟨fun t ht => by omega, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₉ h₉ => ?_
  have f₉ : Frame [⟨State.addr A, 16 * c⟩] s₅.mem s₉.mem := by rw [← mem₈]; exact h₉.cp.frame
  have g₉ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₉.gpr r = s₆.gpr r :=
    fun r h0 h12 h3 h4 => by rw [h₉.regs r h0 h12 h3 h4, g₈ r h0 h12 h3 h4]
  have sc₉ : ScrOk s₀ b E s₉.mem := sc₅.frame hfit' f₉ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dA.sub_left subTab
  have wr₉ : s₉.wr = s.wr := by rw [h₉.wr, wr₈']
  have rd₉ : s₉.rd = s.rd := by rw [h₉.rd, rd₈']
  have sp₉ : s₉.sp = s.sp := by rw [h₉.sp, sp₈, sp₈a, sp₇, sp₆']
  -- The blocks the eight-block code read are the group's, as on entry.
  have hblk : ∀ j < c, tailBlock s₄ j =
      Spec.Seed.blockAt s₀.mem (State.addr D + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Seed.blockAt, Vector.getElem_ofFn]
    have := h₃.cp.copied (16 * j + u) (by omega)
    rw [hT, VG.Offset.add_add, hA, VG.Offset.add_add] at this
    have hout : ∀ r ∈ [(⟨wordAddr b ptrSlot, 4⟩ : Region), ⟨wordAddr b cntSlot, 4⟩],
        ¬ r.Contains (State.addr b + BitVec.ofNat 64 (4 * tailSlot + (16 * j + u))) 1 := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [ptrSlot_eq, cntSlot_eq]); omega)] <;>
        exact not_contains_off _ (by (try simp only [tailSlot_eq, ptrSlot_eq, cntSlot_eq]); omega)
          (by rw [tailSlot_eq]; omega) (by omega) (by (try simp only [ptrSlot_eq, cntSlot_eq]); omega)
    rw [base₄, VG.Offset.add_add, show 4 * tailSlot + 16 * j + u = 4 * tailSlot + (16 * j + u) by omega,
      fs _ hout, this, mem₂, hi.data _ (by omega), ite_eq_right (by omega), VG.Offset.add_add,
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega]
  have hdata : DInv s₀.mem s₉.mem (State.addr D) n (8 * k + c) (outF s₀.mem (State.addr D) E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : State.addr D + BitVec.ofNat 64 i = State.addr A + BitVec.ofNat 64 (i - 128 * k) := by
        rw [hA, VG.Offset.add_add, show 128 * k + (i - 128 * k) = i by omega]
      rw [e1, h₉.cp.copied _ (by omega), mem₈, ite_eq_left (show i < 16 * (8 * k + c) by omega),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega, show i % 16 = (i - 128 * k) % 16 by omega]
      have hj : (i - 128 * k) / 16 < c := by omega
      have eT : State.addr T + BitVec.ofNat 64 (i - 128 * k) =
          State.addr (s₅.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * ((i - 128 * k) / 16)) +
            BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [base₅, hT, VG.Offset.add_add, VG.Offset.add_add,
          show 4 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = 4 * tailSlot + (i - 128 * k) by omega]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega), hblk _ hj, Proof.Seed.crypt_congr hk₄]
      rfl
    · have hout : ∀ r ∈ [(⟨State.addr A, 16 * c⟩ : Region)], ¬ r.Contains (State.addr D + BitVec.ofNat 64 i) 1 :=
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [hA]
          exact not_contains_off _ (by omega) (by omega) (by omega) (by omega)
      rw [f₉ _ hout,
        f₅.bytes (R := ⟨State.addr D, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega)) (by simp only; omega) hin,
        fs.bytes (R := ⟨State.addr D, 16 * n⟩) (dD hsub) (by simp only; omega) hin,
        f₃.bytes (R := ⟨State.addr D, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subT) (by simp only; omega) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega), ite_eq_left (show i < 16 * (8 * k + c) by omega)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega)]
  have fr₉ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s.mem s₉.mem := by
    refine ((f₃.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((fs.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩).trans
      ((f₅.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₉.sub fun r hr => ⟨⟨State.addr D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))))
    · simp only [List.mem_singleton] at hr; subst hr; exact subT
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact subA
  -- On to the next group.
  have r2₉ : s₉.gpr .r2 = BitVec.ofNat 32 v := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), r2₆]
  unfold advance
  refine WP.seq (WP.mono (groupCount_wp r2₉ hv) fun s₁₀ ⟨r3₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀, sp₁₀⟩ => ?_)
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁, sp₁₁⟩ := addImm_ok s₁₀ .r1 .r1 128 (by decide)
  obtain ⟨s₁₂, e₁₂, r₁₂, z₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂, sp₁₂⟩ := subsR_ok s₁₁ .r2 .r2 .r3
  refine WP.of_runBlock ⟨s₁₂, by
    rw [show ([.dp .add .r1 .r1 (.imm 128), .subs .r2 .r2 (.reg .r3)] : List Instr) =
      [.dp .add .r1 .r1 (.imm 128)] ++ [.subs .r2 .r2 (.reg .r3)] from rfl,
      runBlock_append, e₁₁, Option.bind_some, e₁₂], ?_⟩
  have zz : s₁₂.z = decide (v = c) := by
    rw [z₁₂, o₁₁ _ (by decide), o₁₁ _ (by decide), r3₁₀, o₁₀ _ (by decide) (by decide), r2₉,
      ofNat32_sub_beq (by omega) (by omega)]
  have hmem : s₁₂.mem = s₉.mem := by rw [m₁₂, m₁₁, m₁₀]
  have base₁₂ : s₁₂.gpr sb = b := by
    rw [o₁₂ _ (by decide), o₁₁ _ (by decide), o₁₀ _ (by decide) (by decide),
      g₉ _ (by decide) (by decide) (by decide) (by decide), base₆]
  have rd₁₂' : s₁₂.rd = s₀.rd := by rw [rd₁₂, rd₁₁, rd₁₀, rd₉, hi.rd]
  have wr₁₂' : s₁₂.wr = s₀.wr := by rw [wr₁₂, wr₁₁, wr₁₀, wr₉, hi.wr]
  have sp₁₂' : s₁₂.sp = s₀.sp := by rw [sp₁₂, sp₁₁, sp₁₀, sp₉, hi.sp]
  have fr : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s₁₂.mem := by
    rw [hmem]; exact hi.frame.trans fr₉
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega
    refine .inl ⟨by rw [zz]; simp; omega, base₁₂, hmem ▸ sc₉, by have := hmem ▸ hdata; rwa [hn] at this, fr,
      rd₁₂', wr₁₂', sp₁₂'⟩
  · have hc : c = 8 := by omega
    refine .inr ⟨by rw [zz]; simp; omega, base₁₂, ?_, ?_, by omega, hmem ▸ sc₉,
      by rw [hmem, show 8 * (k + 1) = 8 * k + c by omega]; exact hdata, fr, rd₁₂', wr₁₂', sp₁₂'⟩
    · rw [o₁₂ _ (by decide), r₁₁, o₁₀ _ (by decide) (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide),
        r1₆]
      simp only [A]
      rw [show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
        show 128 * k + 128 = 128 * (k + 1) by omega]
    · rw [r₁₂, o₁₁ _ (by decide), o₁₁ _ (by decide), r3₁₀, o₁₀ _ (by decide) (by decide), r2₉,
        VG.Offset.ofNat_sub_ofNat (by omega), show v - c = n - 8 * (k + 1) by omega]

end VG.Proof.Seed.Arm
