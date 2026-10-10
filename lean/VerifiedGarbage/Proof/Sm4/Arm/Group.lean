import VerifiedGarbage.Proof.Sm4.Arm.Prologue

/-!
# A group of blocks of SM4 ECB on ARMv7

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(eight, or the last one to seven) to the tail buffer, transforms it
(`crypt8_wp`), copies the blocks back and steps to the next group. The data
pointer and the blocks left live in their slots (`dSlot`, `nSlot`) between
the steps, which use every other register.
-/

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Proof.Sm4 (DInv quads ofBlock outBlock not_contains_off blockAt_getD)
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

/-- `r2 := n`, `r3 := min(n, 8)`, from the slot of `n`. -/
theorem groupCount_wp {s : State} {b : BitVec 32} {v : Nat} (hb : s.gpr sb = b) (hw : ScrIn s.wr b)
    (hn : s.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa groupCount s fun s' => s'.gpr .r2 = BitVec.ofNat 32 v ∧ s'.gpr .r3 = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s .r2 sb (k := nSlot) hb (by decide) hw
  rw [hn] at v₁
  let s₂ := s₁.setReg t0 (s₁.gpr .r2 >>> 3)
  let s₃ := subFlags s₂ (s₂.gpr t0) 0
  have e₂₃ : runBlock isa [.mov t0 (lsrOp .r2 3), .cmp t0 (.imm 0)] s₁ = some s₃ := by
    rw [runBlock_cons, show exec (.mov t0 (lsrOp .r2 3)) s₁ = some s₂ by simp [exec, Op2.eval, lsrOp, s₂],
      runStep_some, runBlock_cons,
      show exec (.cmp t0 (.imm 0)) s₂ = some s₃ by simp [exec, Op2.eval, s₃]; decide,
      runStep_some, runBlock_nil]
  have t₃ : s₃.gpr t0 = BitVec.ofNat 32 v >>> 3 := by
    show s₂.gpr t0 = _; rw [RegUpd.gpr_setReg_self, v₁]
  have z₃ : s₃.z = (BitVec.ofNat 32 v >>> 3 - 0 == 0) := by
    show (s₂.gpr t0 - 0 == 0) = _; rw [RegUpd.gpr_setReg_self, v₁]
  have o₃ : ∀ r, r ≠ t0 → s₃.gpr r = s₁.gpr r := fun r hr => by
    show s₂.gpr r = _; rw [RegUpd.gpr_setReg_of_ne _ _ hr]
  have r2₃ : s₃.gpr .r2 = BitVec.ofNat 32 v := by rw [o₃ _ (by decide), v₁]
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [show ([ldS .r2 nSlot, .mov t0 (lsrOp .r2 3), .cmp t0 (.imm 0)] : List Instr) =
      [.ldr .r2 sb (4 * nSlot)] ++ [.mov t0 (lsrOp .r2 3), .cmp t0 (.imm 0)] from rfl,
      runBlock_app, e₁, Option.bind_some, e₂₃], ?_⟩)
  have keep : ∀ r, r ≠ .r2 → r ≠ t0 → s₃.gpr r = s.gpr r := fun r h1 h2 => by rw [o₃ r h2, o₁ r h1]
  refine WP.ite (decide (8 ≤ v)) ((eval_ne s₃).trans (by
      rw [z₃, lsr3_beq hv]; by_cases h : v < 8 <;> simp [h] <;> omega)) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movImm_ok s₃ .r3 8 (by decide)
    refine WP.of_runBlock ⟨s₄, e₄, by rw [o₄ _ (by decide), r2₃], ?_,
      fun r h1 h2 h3 => by rw [o₄ r h2, keep r h1 h3], by rw [m₄]; exact m₁, by rw [rd₄]; exact rd₁,
      by rw [wr₄]; exact wr₁, by rw [sp₄]; exact sp₁⟩
    rw [r₄, Nat.min_eq_right (by simp at h; omega)]; rfl
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movR_ok s₃ .r3 .r2
    refine WP.of_runBlock ⟨s₄, e₄, by rw [o₄ _ (by decide), r2₃], ?_,
      fun r h1 h2 h3 => by rw [o₄ r h2, keep r h1 h3], by rw [m₄]; exact m₁, by rw [rd₄]; exact rd₁,
      by rw [wr₄]; exact wr₁, by rw [sp₄]; exact sp₁⟩
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
registers, in the slots from `tableSlot` to `dSlot`. -/
structure ScrOk (s₀ : State) (b : BitVec 32) (E : Nat → Spec.Sm4.Word) (m : Mem) : Prop where
  keys : ∀ e < 32, W32.WordRel (entryW m b e) fun _ => E e
  saved : Saved s₀ b m

theorem ScrOk.frame {s₀ : State} {b : BitVec 32} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b tableSlot dSlot).Disjoint r) : ScrOk s₀ b E m' := by
  refine ⟨fun e he => (h.keys e he).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact slot_keep hfit (by decide) hf hd (by omega) (by rw [dSlot_eq, tableSlot_eq]; omega)
  · rw [← h.saved i hi]
    exact slot_keep hfit (by decide) hf hd (by rw [savedSlot_eq, tableSlot_eq]; omega)
      (by rw [savedSlot_eq, dSlot_eq]; omega)

/-! ## The data loop -/

/-- Each block, transformed: the output of the 32 rounds with the round keys `E`. -/
def outF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Sm4.Word) (j : Nat) : Spec.Sm4.Block :=
  outBlock (quads .enc E 8 (ofBlock (Spec.Sm4.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))))

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : BitVec 32) (n : Nat) : Prop where
  scr : ScrIn s₀.wr b
  dat : (⟨State.addr D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr b, 4 * slots⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 32

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Sm4.Word) (k : Nat) (s : State) :
    Prop where
  base : s.gpr sb = b
  dp : s.mem.readW (wordAddr b dSlot) 32 = D + BitVec.ofNat 32 (128 * k)
  np : s.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 (n - 8 * k)
  lt : 8 * k < n
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n (8 * k) (outF s₀.mem (State.addr D) E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Sm4.Word) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n n (outF s₀.mem (State.addr D) E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem dataGroup_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa group s fun s' => (s'.z = true ∧ GDone s₀ b D n E s') ∨
      (s'.z = false ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  have hb := addr_toNat b
  rw [slots_eq] at hfit
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
  unfold group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.base hwS hi.np hv) fun s₁ ⟨r2₁, r3₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_))
  have b₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide) (by decide) (by decide), hi.base]
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a, sp₂a⟩ :=
    ldSlot_ok s₁ .r0 sb (k := dSlot) b₁ (by decide) (by rw [wr₁]; exact hwS)
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := addImm_ok s₂a .r1 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂a, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂a, wr₁]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₂a, m₁]
  have g₂ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h4 => by rw [o₂ r h1, o₂a r h0, o₁ r h2 h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show ([ldS .r0 dSlot, tailAddr .r1] : List Instr) = [.ldr .r0 sb (4 * dSlot)] ++ [tailAddr .r1] from rfl,
      runBlock_app, e₂a, Option.bind_some]; exact e₂, ?_⟩)
  refine WP.mono (copyBlocks_wp (A := A) (B := T) hc0 hc8 hAn hTn
    (fun t ht h4 => by rw [rd₂', wr₂']; exact inRd (inA t ht h4))
    (fun t ht h4 => by rw [wr₂']; exact inT t ht h4) sepAT
    ⟨by rw [o₂ _ (by decide), r₂a, m₁, hi.dp]; simp [A], by rw [r₂, o₂a _ (by decide), b₁]; simp [T],
      by rw [o₂ _ (by decide), o₂a _ (by decide), r3₁, Nat.sub_zero], ⟨fun t ht => by omega, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₃ h₃ => ?_
  have f₃ : Frame [⟨State.addr T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.cp.frame
  have g₃ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h4 => by rw [h₃.regs r h0 h1 h3 h4, g₂ r h0 h1 h2 h3 h4]
  have base₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.base]
  have keep₃ : ∀ j, tableSlot ≤ j → j < slots → s₃.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => slot_keep (by rw [slots_eq]; omega) (Nat.le_refl _) f₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dT) h1 h2
  have sc₃ : ScrOk s₀ b E s₃.mem := hi.scr.frame (by rw [slots_eq]; omega) f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dT.sub_left (sub_ts _ _ (Nat.le_refl _) (by decide) (by decide))
  have wr₃ : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  have rd₃ : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  have sp₃ : s₃.sp = s.sp := by rw [h₃.sp, sp₂, sp₂a, sp₁]
  -- The eight blocks.
  have hkey : KeyCtx s₃ E :=
    { scr := by rw [base₃, wr₃]; exact hwS.mem
      fit := by rw [base₃, slots_eq]; exact hfit
      keys := fun e he => by rw [base₃]; exact sc₃.keys e he }
  refine WP.seq (WP.mono (crypt8_wp hkey) fun s₅ ⟨c₅, b₅⟩ => ?_)
  have base₅ : s₅.gpr sb = b := by rw [c₅.base, base₃]
  have f₅ : Frame [⟨State.addr b, 4 * tableSlot⟩] s₃.mem s₅.mem := by have := c₅.frame; rw [base₃] at this; exact this
  have keep₅ : ∀ j, tableSlot ≤ j → j < slots → s₅.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => by
      rw [slot_keep (by rw [slots_eq]; omega) (Nat.le_refl _) f₅
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dTab) h1 h2, keep₃ j h1 h2]
  have sc₅ : ScrOk s₀ b E s₅.mem := sc₃.frame (by rw [slots_eq]; omega) f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dTab.sub_left (sub_ts _ _ (Nat.le_refl _) (by decide) (by decide))
  have wr₅ : s₅.wr = s.wr := by rw [c₅.wr, wr₃]
  have rd₅ : s₅.rd = s.rd := by rw [c₅.rd, rd₃]
  have sp₅ : s₅.sp = s.sp := by rw [c₅.sp, sp₃]
  have hwS₅ : ScrIn s₅.wr b := by rw [wr₅]; exact hwS
  have np₅ : s₅.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 v := by
    rw [keep₅ _ (by decide) (by decide), hi.np]
  have dp₅ : s₅.mem.readW (wordAddr b dSlot) 32 = A := by rw [keep₅ _ (by decide) (by decide), hi.dp]
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp base₅ hwS₅ np₅ hv) fun s₇ ⟨r2₇, r3₇, o₇, m₇, rd₇, wr₇, sp₇⟩ => ?_))
  have b₇ : s₇.gpr sb = b := by rw [o₇ _ (by decide) (by decide) (by decide), base₅]
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a, sp₈a⟩ := addImm_ok s₇ .r0 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈, sp₈⟩ :=
    ldSlot_ok s₈a .r1 sb (k := dSlot) (by rw [o₈a _ (by decide), b₇]) (by decide)
      (by rw [wr₈a, wr₇]; exact hwS₅)
  have mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈a, m₇]
  have g₈ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ t0 → s₈.gpr r = s₅.gpr r :=
    fun r h0 h1 h2 h3 h4 => by rw [o₈ r h1, o₈a r h0, o₇ r h2 h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [show ([tailAddr .r0, ldS .r1 dSlot] : List Instr) =
      [.dp .add .r0 sb (.imm (BitVec.ofNat 32 (4 * tailSlot)))] ++ [.ldr .r1 sb (4 * dSlot)] from rfl,
      runBlock_app, e₈a, Option.bind_some]; exact e₈, ?_⟩)
  have rd₈ : s₈.rd = s.rd := by rw [rd₈, rd₈a, rd₇, rd₅]
  have wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈a, wr₇, wr₅]
  refine WP.mono (copyBlocks_wp (A := T) (B := A) hc0 hc8 hTn hAn
    (fun t ht h4 => by rw [rd₈, wr₈']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [wr₈']; exact inA t ht h4) sepAT.symm
    ⟨by rw [o₈ _ (by decide), r₈a, b₇]; simp [T], by rw [r₈, m₈a, m₇, dp₅]; simp [A],
      by rw [o₈ _ (by decide), o₈a _ (by decide), r3₇, Nat.sub_zero], ⟨fun t ht => by omega, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₉ h₉ => ?_
  have f₉ : Frame [⟨State.addr A, 16 * c⟩] s₅.mem s₉.mem := by rw [← mem₈]; exact h₉.cp.frame
  have g₉ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ t0 → s₉.gpr r = s₅.gpr r :=
    fun r h0 h1 h2 h3 h4 => by rw [h₉.regs r h0 h1 h3 h4, g₈ r h0 h1 h2 h3 h4]
  have base₉ : s₉.gpr sb = b := by rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), base₅]
  have keep₉ : ∀ j, tableSlot ≤ j → j < slots → s₉.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => by
      rw [slot_keep (by rw [slots_eq]; omega) (Nat.le_refl _) f₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dA) h1 h2,
        keep₅ j h1 h2]
  have sc₉ : ScrOk s₀ b E s₉.mem := sc₅.frame (by rw [slots_eq]; omega) f₉ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dA.sub_left (sub_ts _ _ (Nat.le_refl _) (by decide) (by decide))
  have wr₉ : s₉.wr = s.wr := by rw [h₉.wr, wr₈']
  have rd₉ : s₉.rd = s.rd := by rw [h₉.rd, rd₈]
  have sp₉ : s₉.sp = s.sp := by rw [h₉.sp, sp₈, sp₈a, sp₇, sp₅]
  have hwS₉ : ScrIn s₉.wr b := by rw [wr₉]; exact hwS
  -- The blocks the eight-block code read are the group's, as on entry.
  have hblk : ∀ j < c, tailBlock s₃ j =
      Spec.Sm4.blockAt s₀.mem (State.addr D + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn]
    have := h₃.cp.copied (16 * j + u) (by omega)
    rw [hT, VG.Offset.add_add, hA, VG.Offset.add_add] at this
    rw [base₃, VG.Offset.add_add, show 4 * tailSlot + 16 * j + u = 4 * tailSlot + (16 * j + u) by omega, this,
      mem₂, hi.data _ (by omega), ite_eq_right (by omega), VG.Offset.add_add,
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega]
  have dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨State.addr b, 4 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨State.addr D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
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
      rw [b₅ _ (by omega), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨State.addr A, 16 * c⟩ : Region)], ¬ r.Contains (State.addr D + BitVec.ofNat 64 i) 1 :=
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [hA]
          exact not_contains_off _ (by omega) (by omega) (by omega) (by omega)
      rw [f₉ _ hout,
        f₅.bytes (R := ⟨State.addr D, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega)) (by simp only; omega) hin,
        f₃.bytes (R := ⟨State.addr D, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subT) (by simp only; omega) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega), ite_eq_left (show i < 16 * (8 * k + c) by omega)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega)]
  have fr₉ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s.mem s₉.mem := by
    refine ((f₃.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₅.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₉.sub fun r hr => ⟨⟨State.addr D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr; exact subT
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact subA
  -- On to the next group.
  have np₉ : s₉.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 v := by
    rw [keep₉ _ (by decide) (by decide), hi.np]
  have dp₉ : s₉.mem.readW (wordAddr b dSlot) 32 = A := by rw [keep₉ _ (by decide) (by decide), hi.dp]
  unfold advance
  refine WP.seq (WP.mono (groupCount_wp base₉ hwS₉ np₉ hv) fun s₁₀ ⟨r2₁₀, r3₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀, sp₁₀⟩ => ?_)
  have b₁₀ : s₁₀.gpr sb = b := by rw [o₁₀ _ (by decide) (by decide) (by decide), base₉]
  have hwS₁₀ : ScrIn s₁₀.wr b := by rw [wr₁₀]; exact hwS₉
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁, sp₁₁⟩ := ldSlot_ok s₁₀ .r1 sb (k := dSlot) b₁₀ (by decide) hwS₁₀
  obtain ⟨s₁₂, e₁₂, r₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂, sp₁₂⟩ := addImm_ok s₁₁ .r1 .r1 128 (by decide)
  obtain ⟨s₁₃, e₁₃, m₁₃, g₁₃, rd₁₃, wr₁₃, sp₁₃, -, f₁₃⟩ := stSlot_ok s₁₂ .r1 sb (k := dSlot)
    (by rw [o₁₂ _ (by decide), o₁₁ _ (by decide), b₁₀]) (by decide) (by rw [wr₁₂, wr₁₁]; exact hwS₁₀)
  obtain ⟨s₁₄, e₁₄, r₁₄, z₁₄, o₁₄, m₁₄, rd₁₄, wr₁₄, sp₁₄⟩ := subsR_ok s₁₃ .r2 .r2 .r3
  obtain ⟨s₁₅, e₁₅, m₁₅, g₁₅, rd₁₅, wr₁₅, sp₁₅, z₁₅, f₁₅⟩ := stSlot_ok s₁₄ .r2 sb (k := nSlot)
    (by rw [o₁₄ _ (by decide), g₁₃, o₁₂ _ (by decide), o₁₁ _ (by decide), b₁₀]) (by decide)
    (by rw [wr₁₄, wr₁₃, wr₁₂, wr₁₁]; exact hwS₁₀)
  refine WP.of_runBlock ⟨s₁₅, by
    rw [show ([ldS .r1 dSlot, .dp .add .r1 .r1 (.imm 128), stS dSlot .r1, .subs .r2 .r2 (.reg .r3),
        stS nSlot .r2] : List Instr) =
      [.ldr .r1 sb (4 * dSlot)] ++ ([.dp .add .r1 .r1 (.imm 128)] ++ ([.str .r1 sb (4 * dSlot)] ++
        ([.subs .r2 .r2 (.reg .r3)] ++ [.str .r2 sb (4 * nSlot)]))) from rfl,
      runBlock_app, e₁₁, Option.bind_some, runBlock_app, e₁₂, Option.bind_some, runBlock_app, e₁₃,
      Option.bind_some, runBlock_app, e₁₄, Option.bind_some, e₁₅], ?_⟩
  have r1₁₂ : s₁₂.gpr .r1 = A + BitVec.ofNat 32 128 := by rw [r₁₂, r₁₁, m₁₀, dp₉]; rfl
  have r2₁₄ : s₁₄.gpr .r2 = BitVec.ofNat 32 (v - c) := by
    rw [r₁₄, g₁₃, o₁₂ _ (by decide), o₁₁ _ (by decide), r2₁₀, o₁₂ _ (by decide), o₁₁ _ (by decide), r3₁₀,
      VG.Offset.ofNat_sub_ofNat (by omega)]
  have zz : s₁₅.z = decide (v = c) := by
    rw [z₁₅, z₁₄, g₁₃, o₁₂ _ (by decide), o₁₁ _ (by decide), r2₁₀, o₁₂ _ (by decide), o₁₁ _ (by decide), r3₁₀,
      ofNat32_sub_beq (by omega) (by omega)]
  have m₁₂' : s₁₂.mem = s₉.mem := by rw [m₁₂, m₁₁, m₁₀]
  have hmem : s₁₅.mem = (s₉.mem.writeW (wordAddr b dSlot) (A + BitVec.ofNat 32 128)).writeW (wordAddr b nSlot)
      (BitVec.ofNat 32 (v - c)) := by
    rw [m₁₅, m₁₄, m₁₃, m₁₂', r1₁₂, r2₁₄]
  have fs : Frame [⟨wordAddr b dSlot, 4⟩, ⟨wordAddr b nSlot, 4⟩] s₉.mem s₁₅.mem := by
    rw [← m₁₂']
    refine (f₁₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans ?_
    rw [← m₁₄]
    exact f₁₅.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hsub : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      Region.Sub r ⟨State.addr b, 4 * slots⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact slot_sub (by rw [slots_eq]; omega) (by decide)
    · exact slot_sub (by rw [slots_eq]; omega) (by decide)
  have sc₁₅ : ScrOk s₀ b E s₁₅.mem := sc₉.frame (by rw [slots_eq]; omega) fs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [dSlot_eq, nSlot_eq]); omega)] <;>
      exact VG.Offset.disjoint _ (by (try simp only [tableSlot_eq, dSlot_eq, nSlot_eq]); omega)
        (by (try simp only [tableSlot_eq, dSlot_eq]); omega) (by (try simp only [dSlot_eq, nSlot_eq]); omega)
  have data₁₅ : DInv s₀.mem s₁₅.mem (State.addr D) n (8 * k + c) (outF s₀.mem (State.addr D) E) := fun i hin => by
    rw [fs.bytes (R := ⟨State.addr D, 16 * n⟩) (dD hsub) (by simp only; omega) hin]
    exact hdata i hin
  have fr₁₅ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s₁₅.mem :=
    hi.frame.trans (fr₉.trans (fs.sub fun r hr => ⟨_, List.mem_cons_self, hsub r hr⟩))
  have base₁₅ : s₁₅.gpr sb = b := by rw [g₁₅, o₁₄ _ (by decide), g₁₃, o₁₂ _ (by decide), o₁₁ _ (by decide), b₁₀]
  have rd₁₅' : s₁₅.rd = s₀.rd := by rw [rd₁₅, rd₁₄, rd₁₃, rd₁₂, rd₁₁, rd₁₀, rd₉, hi.rd]
  have wr₁₅' : s₁₅.wr = s₀.wr := by rw [wr₁₅, wr₁₄, wr₁₃, wr₁₂, wr₁₁, wr₁₀, wr₉, hi.wr]
  have sp₁₅' : s₁₅.sp = s₀.sp := by rw [sp₁₅, sp₁₄, sp₁₃, sp₁₂, sp₁₁, sp₁₀, sp₉, hi.sp]
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega
    refine .inl ⟨by rw [zz]; simp; omega, base₁₅, sc₁₅, by have := data₁₅; rwa [hn] at this, fr₁₅, rd₁₅', wr₁₅', sp₁₅'⟩
  · have hc : c = 8 := by omega
    have hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega
    refine .inr ⟨by rw [zz]; simp; omega, base₁₅, ?_, ?_, by omega, sc₁₅,
      by rw [show 8 * (k + 1) = 8 * k + c by omega]; exact data₁₅, fr₁₅, rd₁₅', wr₁₅', sp₁₅'⟩
    · rw [hmem, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_right (by decide),
        readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl]
      simp only [A]
      rw [VG.Offset.add_add, show 128 * k + 128 = 128 * (k + 1) by omega]
    · rw [hmem, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl,
        show v - c = n - 8 * (k + 1) by omega]

end VG.Proof.Sm4.Arm
