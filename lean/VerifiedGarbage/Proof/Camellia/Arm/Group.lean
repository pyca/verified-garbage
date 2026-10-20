module

public import VerifiedGarbage.Proof.Camellia.Arm.Prologue
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Camellia.Arm.Keys
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Camellia.Arm.Copy
import VerifiedGarbage.Proof.Camellia.Arm.Crypt8
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# A group of blocks of Camellia ECB on ARMv7

As SM4's (`Proof/Sm4/Arm/Group.lean`): `dataGroup_wp`, one iteration of the
data loop, copies the group's blocks (eight, or the last one to seven) to
the tail buffer, transforms it (`crypt8_ok`), copies the blocks back and
steps to the next group. The data pointer and the blocks left live in their
slots (`dSlot`, `nSlot`) between the steps, which use every other register.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Proof.Camellia (DInv outF not_contains_off blockAt_getD cryptWords)
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR lsrOp ldS stS)

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
  rw [slot_addr (by omega_arith)]
  exact hf.readW (VG.Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)) hd (by decide)

/-- What the data loop keeps in the scratch buffer: the table and the saved
registers. -/
structure ScrOk (s₀ : State) (b : BitVec 32) (g : Nat) (E : Nat → BitVec 64) (m : Mem) : Prop where
  keys : ∀ e < 8 * g + 2, EntryOk m b e (E e)
  saved : Saved s₀ b m

/-- The slots `ScrOk` reads are outside the regions. -/
def KeepOut (b : BitVec 32) (rs : List Region) : Prop :=
  ∀ r ∈ rs, (slotsRegion b keySlot grpSlot).Disjoint r ∧ (slotsRegion b savedSlot dSlot).Disjoint r

theorem ScrOk.frame {s₀ : State} {b : BitVec 32} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hg : g = 3 ∨ g = 4) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {rs : List Region}
    (hf : Frame rs m m') (hd : KeepOut b rs) : ScrOk s₀ b g E m' := by
  refine ⟨fun e he => (h.keys e he).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact slot_keep hfit (by decide) hf (fun r hr => (hd r hr).1) (by omega_arith)
      (by rw [grpSlot_eq, keySlot_eq]; rcases hg with rfl | rfl <;> omega_arith)
  · rw [← h.saved i hi]
    exact slot_keep hfit (by decide) hf (fun r hr => (hd r hr).2) (by omega_arith)
      (by rw [savedSlot_eq, dSlot_eq]; omega_arith)

/-! ## The data loop -/

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : BitVec 32) (n : Nat) : Prop where
  scr : ScrIn s₀.wr b
  dat : (⟨State.addr D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr b, 4 * slots⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 32

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : BitVec 32) (n : Nat) (g : Nat) (E : Nat → BitVec 64) (k : Nat) (s : State) :
    Prop where
  base : s.gpr sb = b
  dp : s.gpr .r1 = D + BitVec.ofNat 32 (128 * k)
  np : s.gpr .r2 = BitVec.ofNat 32 (n - 8 * k)
  lt : 8 * k < n
  lr : s.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g)
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n (8 * k) (outF s₀.mem (State.addr D) g E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : BitVec 32) (n : Nat) (g : Nat) (E : Nat → BitVec 64) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n n (outF s₀.mem (State.addr D) g E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem KeepOut.cons {b : BitVec 32} {r : Region} {rs : List Region} (h₁ : KeepOut b [r]) (h₂ : KeepOut b rs) :
    KeepOut b (r :: rs) := fun x hx => by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁ _ List.mem_cons_self
  · exact h₂ x hx

theorem KeepOut.nil (b : BitVec 32) : KeepOut b [] := fun _ h => absurd h List.not_mem_nil

/-- A region at an offset of the scratch buffer, outside what `ScrOk` reads. -/
theorem keepOut_off (b : BitVec 32) {e n : Nat} (hn : e + n ≤ 4 * slots)
    (h1 : e + n ≤ 4 * keySlot ∨ 4 * grpSlot ≤ e) (h2 : e + n ≤ 4 * savedSlot ∨ 4 * dSlot ≤ e) :
    KeepOut b [⟨State.addr b + BitVec.ofNat 64 e, n⟩] := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [slots_eq] at hn
  rw [keySlot_eq, grpSlot_eq] at h1
  rw [savedSlot_eq, dSlot_eq] at h2
  exact ⟨VG.Offset.disjoint _ (by rw [keySlot_eq, grpSlot_eq]; omega_arith) (by rw [keySlot_eq, grpSlot_eq]; omega_arith)
      (by omega_arith),
    VG.Offset.disjoint _ (by rw [savedSlot_eq, dSlot_eq]; omega_arith) (by rw [savedSlot_eq, dSlot_eq]; omega_arith) (by omega_arith)⟩

/-- A region outside the scratch buffer. -/
theorem keepOut_out (b : BitVec 32) {R : Region}
    (h : Region.Disjoint R ⟨State.addr b, 4 * slots⟩) : KeepOut b [R] := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨(h.sub_right (VG.Offset.sub_base _ (by rw [slots_eq, keySlot_eq, grpSlot_eq]; omega_arith))).symm,
    (h.sub_right (VG.Offset.sub_base _ (by rw [slots_eq, savedSlot_eq, dSlot_eq]; omega_arith))).symm⟩

theorem keepOut_ctx {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) : KeepOut b (ctxRegions b) := by
  have hb := addr_toNat b
  have h2 := hfit
  rw [slots_eq] at h2
  refine KeepOut.cons ?_ (KeepOut.cons ?_ (KeepOut.cons ?_ (KeepOut.nil b)))
  · have := keepOut_off b (e := 0) (n := 4 * keySlot) (by rw [slots_eq, keySlot_eq] <;> omega_arith)
      (.inl (by omega_arith)) (.inl (by rw [keySlot_eq, savedSlot_eq] <;> omega_arith))
    simpa using this
  · rw [VG.Arm.addr_add (by rw [grpSlot_eq] <;> omega_arith)]
    exact keepOut_off b (by rw [grpSlot_eq, slots_eq] <;> omega_arith) (.inr (Nat.le_refl _))
      (.inl (by rw [grpSlot_eq, savedSlot_eq] <;> omega_arith))
  · rw [VG.Arm.addr_add (by rw [tailSlot_eq] <;> omega_arith)]
    exact keepOut_off b (by rw [tailSlot_eq, slots_eq] <;> omega_arith) (.inr (by rw [tailSlot_eq, grpSlot_eq] <;> omega_arith))
      (.inr (by rw [tailSlot_eq, dSlot_eq] <;> omega_arith))

theorem dataGroup_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {g : Nat} {E : Nat → BitVec 64} (hp : GPre s₀ b D n)
    (hg : g = 3 ∨ g = 4) {k : Nat} {s : State} (hi : GInv s₀ b D n g E k s) :
    WP isa Impl.Camellia.Arm.group s fun s' => (s'.z = true ∧ GDone s₀ b D n g E s') ∨
      (s'.z = false ∧ GInv s₀ b D n g E (k + 1) s') := by
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  have hb := addr_toNat b
  rw [slots_eq] at hfit
  have hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega_arith
  let v := n - 8 * k
  let c := min v 8
  have hv : v < 2 ^ 32 := by omega_arith
  have hc0 : 0 < c := by omega_arith
  have hc8 : c ≤ 8 := by omega_arith
  have hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 32 (128 * k)
  let T := b + BitVec.ofNat 32 (4 * tailSlot)
  have hA : State.addr A = State.addr D + BitVec.ofNat 64 (128 * k) := VG.Arm.addr_add (by omega_arith)
  have hT : State.addr T = State.addr b + BitVec.ofNat 64 (4 * tailSlot) := VG.Arm.addr_add (by rw [tailSlot_eq]; omega_arith)
  have hAn : A.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega_arith)]; omega_arith
  have hTn : T.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by rw [tailSlot_eq]; omega_arith), tailSlot_eq]; omega_arith
  have hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  have hwD : (⟨State.addr D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have inT : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (State.addr T + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwS.mem, ?_⟩
    rw [hT, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  have inA : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (State.addr A + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwD, ?_⟩
    rw [hA, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  have subA : Region.Sub ⟨State.addr A, 16 * c⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [hA]; exact VG.Offset.sub_base _ (by omega_arith)
  have subT : Region.Sub ⟨State.addr T, 16 * c⟩ ⟨State.addr b, 4 * slots⟩ := by
    rw [hT]; exact VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith)
  have sepAT : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr T, 16 * c⟩ :=
    (hp.sep.sub_left subA).sub_right subT
  have dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨State.addr b, 4 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨State.addr D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  have koT : KeepOut b [⟨State.addr T, 16 * c⟩] := by
    rw [hT]; exact keepOut_off b (by rw [slots_eq, tailSlot_eq]; omega_arith)
      (.inr (by rw [tailSlot_eq, grpSlot_eq]; omega_arith)) (.inr (by rw [tailSlot_eq, dSlot_eq]; omega_arith))
  have koA : KeepOut b [⟨State.addr A, 16 * c⟩] := keepOut_out b (hp.sep.sub_left subA)
  have r1₀ : s.gpr .r1 = A := hi.dp
  unfold Impl.Camellia.Arm.group copyIn
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
    rw [show ([movR .r0 .r1, slotAddr .r12 tailSlot] : List Instr) = [movR .r0 .r1] ++ [slotAddr .r12 tailSlot] from rfl,
      runBlock_app, e₂a, Option.bind_some]; exact e₂, ?_⟩)
  refine WP.mono (copyBlocks_wp (A := A) (B := T) hc0 hc8 hAn hTn
    (fun t ht h4 => by rw [rd₂', wr₂']; exact inRd (inA t ht h4))
    (fun t ht h4 => by rw [wr₂']; exact inT t ht h4) sepAT
    ⟨by rw [o₂ _ (by decide), r₂a, o₁ _ (by decide) (by decide), r1₀]; simp [A],
      by rw [r₂, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base]; simp [T],
      by rw [o₂ _ (by decide), o₂a _ (by decide), r3₁, Nat.sub_zero], ⟨fun t ht => by omega_arith, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₃ h₃ => ?_
  have f₃ : Frame [⟨State.addr T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.cp.frame
  have g₃ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h0 h12 h3 h4 => by rw [h₃.regs r h0 h12 h3 h4, g₂ r h0 h12 h3 h4]
  have base₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.base]
  have sc₃ : ScrOk s₀ b g E s₃.mem := hi.scr.frame hg hfit' f₃ koT
  have wr₃ : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  have rd₃ : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  have sp₃ : s₃.sp = s.sp := by rw [h₃.sp, sp₂, sp₂a, sp₁]
  have hwS₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hwS
  -- The data pointer, the blocks left and the postwhitening's address to their slots.
  unfold cryptSaved
  obtain ⟨s₄a, e₄a, m₄a, g₄a, rd₄a, wr₄a, sp₄a, -, f₄a⟩ := stSlot_ok s₃ .r1 sb (k := dSlot) base₃ (by decide) hwS₃
  obtain ⟨s₄b, e₄b, m₄b, g₄b, rd₄b, wr₄b, sp₄b, -, f₄b⟩ := stSlot_ok s₄a .r2 sb (k := nSlot)
    (by rw [g₄a, base₃]) (by decide) (by rw [wr₄a]; exact hwS₃)
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, f₄⟩ := stSlot_ok s₄b .lr sb (k := endSlot)
    (by rw [g₄b, g₄a, base₃]) (by decide) (by rw [wr₄b, wr₄a]; exact hwS₃)
  have r1₃ : s₃.gpr .r1 = A := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), r1₀]
  have r2₃ : s₃.gpr .r2 = BitVec.ofNat 32 v := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.np]
  have lr₃ : s₃.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.lr]
  have fs : Frame [⟨wordAddr b dSlot, 4⟩, ⟨wordAddr b nSlot, 4⟩, ⟨wordAddr b endSlot, 4⟩] s₃.mem s₄.mem :=
    (f₄a.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      ((f₄b.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
        (f₄.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩))
  have hsub : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩, ⟨wordAddr b endSlot, 4⟩],
      Region.Sub r ⟨State.addr b, 4 * slots⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact slot_sub hfit' (by decide)
    · exact slot_sub hfit' (by decide)
    · exact slot_sub hfit' (by decide)
  have dsTab : KeepOut b [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩, ⟨wordAddr b endSlot, 4⟩] := by
    refine KeepOut.cons ?_ (KeepOut.cons ?_ (KeepOut.cons ?_ (KeepOut.nil b)))
    · rw [slot_addr (by rw [dSlot_eq]; omega_arith)]
      exact keepOut_off b (by rw [dSlot_eq, slots_eq]; omega_arith) (.inr (by rw [dSlot_eq, grpSlot_eq]; omega_arith))
        (.inr (Nat.le_refl _))
    · rw [slot_addr (by rw [nSlot_eq]; omega_arith)]
      exact keepOut_off b (by rw [nSlot_eq, slots_eq]; omega_arith) (.inr (by rw [nSlot_eq, grpSlot_eq]; omega_arith))
        (.inr (by rw [nSlot_eq, dSlot_eq]; omega_arith))
    · rw [slot_addr (by rw [endSlot_eq]; omega_arith)]
      exact keepOut_off b (by rw [endSlot_eq, slots_eq]; omega_arith) (.inr (by rw [endSlot_eq, grpSlot_eq]; omega_arith))
        (.inl (by rw [endSlot_eq, savedSlot_eq]))
  have sc₄ : ScrOk s₀ b g E s₄.mem := sc₃.frame hg hfit' fs dsTab
  have base₄ : s₄.gpr sb = b := by rw [g₄, g₄b, g₄a, base₃]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₄b, wr₄a, wr₃]
  have dp₄ : s₄.mem.readW (wordAddr b dSlot) 32 = A := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_right (by decide), m₄b,
      readW_slot_write hfit' _ (by decide) (by decide), ite_eq_right (by decide), m₄a,
      readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, r1₃]
  have np₄ : s₄.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 v := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_right (by decide), m₄b,
      readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, g₄a, r2₃]
  have ep₄ : s₄.mem.readW (wordAddr b endSlot) 32 = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, g₄b, g₄a, lr₃]
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([stS dSlot .r1, stS nSlot .r2, stS endSlot .lr] : List Instr) =
      [.str .r1 sb (4 * dSlot)] ++ ([.str .r2 sb (4 * nSlot)] ++ [.str .lr sb (4 * endSlot)]) from rfl,
      runBlock_app, e₄a, Option.bind_some, runBlock_app, e₄b, Option.bind_some, e₄],
    ?_⟩))
  -- The eight blocks.
  have hcore : CorePre s₄ g E :=
    { scr := ⟨by rw [base₄, wr₄']; exact hwS.mem, by rw [base₄]; exact hfit'⟩
      nk34 := by rcases hg with rfl | rfl <;> decide
      keys := fun e he => by rw [base₄]; exact sc₄.keys e he
      hg := hg
      bound := by rw [slotW, base₄]; exact ep₄ }
  refine WP.seq (WP.mono (WP.sp (crypt8_ok hcore)) fun s₅ ⟨⟨c₅, b₅⟩, sp₅'⟩ => ?_)
  have base₅ : s₅.gpr sb = b := by rw [c₅.base, base₄]
  have f₅ : Frame (ctxRegions b) s₄.mem s₅.mem := by have := c₅.frame; rw [base₄] at this; exact this
  have keep₅ : ∀ j, j = dSlot ∨ j = nSlot ∨ j = endSlot →
      s₅.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32 :=
    fun j hj => by
      have := c₅.slot (k := j) (by rw [base₄]; exact hfit') (by rcases hj with rfl | rfl | rfl <;> decide)
        (by rcases hj with rfl | rfl | rfl <;> decide) (by rcases hj with rfl | rfl | rfl <;> decide)
        (.inl (by rcases hj with rfl | rfl | rfl <;> decide))
      simp only [slotW, base₅, base₄] at this; exact this
  have sc₅ : ScrOk s₀ b g E s₅.mem := sc₄.frame hg hfit' f₅ (keepOut_ctx hfit')
  have wr₅ : s₅.wr = s.wr := by rw [c₅.wr, wr₄']
  have rd₅ : s₅.rd = s.rd := by rw [c₅.rd, rd₄, rd₄b, rd₄a, rd₃]
  have sp₅ : s₅.sp = s.sp := by rw [sp₅', sp₄, sp₄b, sp₄a, sp₃]
  have hwS₅ : ScrIn s₅.wr b := by rw [wr₅]; exact hwS
  -- The data pointer, the blocks left and the postwhitening's address back.
  obtain ⟨s₆a, e₆a, r₆a, o₆a, m₆a, rd₆a, wr₆a, sp₆a⟩ := ldSlot_ok s₅ .r1 sb (k := dSlot) base₅ (by decide) hwS₅
  obtain ⟨s₆b, e₆b, r₆b, o₆b, m₆b, rd₆b, wr₆b, sp₆b⟩ := ldSlot_ok s₆a .r2 sb (k := nSlot)
    (by rw [o₆a _ (by decide), base₅]) (by decide) (by rw [wr₆a]; exact hwS₅)
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := ldSlot_ok s₆b .lr sb (k := endSlot)
    (by rw [o₆b _ (by decide), o₆a _ (by decide), base₅]) (by decide) (by rw [wr₆b, wr₆a]; exact hwS₅)
  refine WP.of_runBlock ⟨s₆, by
    rw [show ([ldS .r1 dSlot, ldS .r2 nSlot, ldS .lr endSlot] : List Instr) =
      [.ldr .r1 sb (4 * dSlot)] ++ ([.ldr .r2 sb (4 * nSlot)] ++ [.ldr .lr sb (4 * endSlot)]) from rfl,
      runBlock_app, e₆a, Option.bind_some, runBlock_app, e₆b, Option.bind_some, e₆],
    ?_⟩
  have r1₆ : s₆.gpr .r1 = A := by rw [o₆ _ (by decide), o₆b _ (by decide), r₆a, keep₅ _ (by decide), dp₄]
  have r2₆ : s₆.gpr .r2 = BitVec.ofNat 32 v := by
    rw [o₆ _ (by decide), r₆b, m₆a, keep₅ _ (by decide), np₄]
  have lr₆ : s₆.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) := by
    rw [r₆, m₆b, m₆a, keep₅ _ (by decide), ep₄]
  have base₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₆b _ (by decide), o₆a _ (by decide), base₅]
  have mem₆ : s₆.mem = s₅.mem := by rw [m₆, m₆b, m₆a]
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₆b, wr₆a, wr₅]
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₆b, rd₆a, rd₅]
  have sp₆' : s₆.sp = s.sp := by rw [sp₆, sp₆b, sp₆a, sp₅]
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r2₆ hv) fun s₇ ⟨r3₇, o₇, m₇, rd₇, wr₇, sp₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a, sp₈a⟩ := addImm_ok s₇ .r0 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈, sp₈⟩ := movR_ok s₈a .r12 .r1
  have mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈a, m₇, mem₆]
  have g₈ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₈.gpr r = s₆.gpr r :=
    fun r h0 h12 h3 h4 => by rw [o₈ r h12, o₈a r h0, o₇ r h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [show ([slotAddr .r0 tailSlot, movR .r12 .r1] : List Instr) =
      [.dp .add .r0 sb (.imm (BitVec.ofNat 32 (4 * tailSlot)))] ++ [movR .r12 .r1] from rfl,
      runBlock_app, e₈a, Option.bind_some]; exact e₈, ?_⟩)
  have rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈a, rd₇, rd₆']
  have wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈a, wr₇, wr₆']
  refine WP.mono (copyBlocks_wp (A := T) (B := A) hc0 hc8 hTn hAn
    (fun t ht h4 => by rw [rd₈', wr₈']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [wr₈']; exact inA t ht h4) sepAT.symm
    ⟨by rw [o₈ _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₆]; simp [T],
      by rw [r₈, o₈a _ (by decide), o₇ _ (by decide) (by decide), r1₆]; simp [A],
      by rw [o₈ _ (by decide), o₈a _ (by decide), r3₇, Nat.sub_zero], ⟨fun t ht => by omega_arith, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₉ h₉ => ?_
  have f₉ : Frame [⟨State.addr A, 16 * c⟩] s₅.mem s₉.mem := by rw [← mem₈]; exact h₉.cp.frame
  have g₉ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₉.gpr r = s₆.gpr r :=
    fun r h0 h12 h3 h4 => by rw [h₉.regs r h0 h12 h3 h4, g₈ r h0 h12 h3 h4]
  have sc₉ : ScrOk s₀ b g E s₉.mem := sc₅.frame hg hfit' f₉ koA
  have wr₉ : s₉.wr = s.wr := by rw [h₉.wr, wr₈']
  have rd₉ : s₉.rd = s.rd := by rw [h₉.rd, rd₈']
  have sp₉ : s₉.sp = s.sp := by rw [h₉.sp, sp₈, sp₈a, sp₇, sp₆']
  -- The blocks the eight-block code read are the group's, as on entry.
  have hblk : ∀ j < c, blk s₄ j =
      Spec.Camellia.blockAt s₀.mem (State.addr D + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [blk, Spec.Camellia.blockAt, Vector.getElem_ofFn]
    have := h₃.cp.copied (16 * j + u) (by omega_arith)
    rw [hT, VG.Offset.add_add, hA, VG.Offset.add_add] at this
    have hout : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩, ⟨wordAddr b endSlot, 4⟩],
        ¬ r.Contains (State.addr b + BitVec.ofNat 64 (4 * tailSlot + (16 * j + u))) 1 := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        rw [slot_addr (by (try simp only [dSlot_eq, nSlot_eq, endSlot_eq]); omega_arith)] <;>
        exact not_contains_off _ (by (try simp only [tailSlot_eq, dSlot_eq, nSlot_eq, endSlot_eq]); omega_arith)
          (by rw [tailSlot_eq]; omega_arith) (by omega_arith) (by (try simp only [dSlot_eq, nSlot_eq, endSlot_eq]); omega_arith)
    rw [base₄, VG.Offset.add_add, show 4 * tailSlot + 16 * j + u = 4 * tailSlot + (16 * j + u) by omega_arith,
      fs _ hout, this, mem₂, hi.data _ (by omega_arith), ite_eq_right (by omega_arith), VG.Offset.add_add,
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith]
  have hdata : DInv s₀.mem s₉.mem (State.addr D) n (8 * k + c) (outF s₀.mem (State.addr D) g E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : State.addr D + BitVec.ofNat 64 i = State.addr A + BitVec.ofNat 64 (i - 128 * k) := by
        rw [hA, VG.Offset.add_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, h₉.cp.copied _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      have hj : (i - 128 * k) / 16 < c := by omega_arith
      have eT : State.addr T + BitVec.ofNat 64 (i - 128 * k) =
          State.addr (s₅.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * ((i - 128 * k) / 16)) +
            BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [base₅, hT, VG.Offset.add_add, VG.Offset.add_add,
          show 4 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = 4 * tailSlot + (i - 128 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (blk s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨State.addr A, 16 * c⟩ : Region)], ¬ r.Contains (State.addr D + BitVec.ofNat 64 i) 1 :=
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [hA]
          exact not_contains_off _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      rw [f₉ _ hout,
        f₅.bytes (R := ⟨State.addr D, 16 * n⟩) (dD (ctx_sub_scr hfit')) (by simp only; omega_arith) hin,
        fs.bytes (R := ⟨State.addr D, 16 * n⟩) (dD hsub) (by simp only; omega_arith) hin,
        f₃.bytes (R := ⟨State.addr D, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subT) (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  have fr₉ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s.mem s₉.mem := by
    refine ((f₃.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((fs.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩).trans
      ((f₅.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ctx_sub_scr hfit' r hr⟩).trans
      (f₉.sub fun r hr => ⟨⟨State.addr D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))))
    · simp only [List.mem_singleton] at hr; subst hr; exact subT
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
      runBlock_app, e₁₁, Option.bind_some, e₁₂], ?_⟩
  have zz : s₁₂.z = decide (v = c) := by
    rw [z₁₂, o₁₁ _ (by decide), o₁₁ _ (by decide), r3₁₀, o₁₀ _ (by decide) (by decide), r2₉,
      ofNat32_sub_beq (by omega_arith) (by omega_arith)]
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
  · have hn : 8 * k + c = n := by omega_arith
    refine .inl ⟨by rw [zz]; simp; omega_arith, base₁₂, hmem ▸ sc₉, by have := hmem ▸ hdata; rwa [hn] at this, fr,
      rd₁₂', wr₁₂', sp₁₂'⟩
  · have hc : c = 8 := by omega_arith
    refine .inr ⟨by rw [zz]; simp; omega_arith, base₁₂, ?_, ?_, by omega_arith, ?_, hmem ▸ sc₉,
      by rw [hmem, show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata, fr, rd₁₂', wr₁₂', sp₁₂'⟩
    · rw [o₁₂ _ (by decide), r₁₁, o₁₀ _ (by decide) (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide),
        r1₆]
      simp only [A]
      rw [show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
        show 128 * k + 128 = 128 * (k + 1) by omega_arith]
    · rw [r₁₂, o₁₁ _ (by decide), o₁₁ _ (by decide), r3₁₀, o₁₀ _ (by decide) (by decide), r2₉,
        VG.Offset.ofNat_sub_ofNat (by omega_arith), show v - c = n - 8 * (k + 1) by omega_arith]
    · rw [o₁₂ _ (by decide), o₁₁ _ (by decide), o₁₀ _ (by decide) (by decide),
        g₉ _ (by decide) (by decide) (by decide) (by decide), lr₆]

end VG.Proof.Camellia.Arm
