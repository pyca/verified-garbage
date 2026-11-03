module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Batch
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.TripleDes.Schedule

/-!
# Bitsliced Triple DES ECB on RISC-V

`ecb_wp`: in a frame of 1056 bytes below the stack pointer, the caller's
`s1`–`s11`, `ra` and `s0` saved, the schedules copied and the masks stored
(`setup_ok`), the batches (`loop_ok`), the frame zeroed below the saved
registers and the registers restored (`finish_ok`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Bitsliced

open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64.Bitslice VG.Spec.TripleDes VG.Impl.Words.RISCV64
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame)
open VG.RISCV64.Straight (wordAddr)

/-! ## The masks -/

def maskCode (k : Nat) : List Instr :=
  li64 .t0 .t1 (swapMask (maskShifts.getD k 1)) ++ ([.store .d .t0 base (maskOff + 8 * k)] : List Instr)

theorem storeMasks_eq : storeMasks = (List.range 6).flatMap maskCode := rfl

/-- The mask words. -/
def maskR (s : State) : Region := ⟨wordAddr (s.gpr .s0) 112, 48⟩

theorem maskCode_ok {s : State} (h : Room s) {k : Nat} (hk : k < 6) :
    WP isa (.block (maskCode k)) s fun s' =>
      s'.mem = s.mem.writeW (wordAddr (s.gpr .s0) (112 + k)) (swapMask (maskShifts.getD k 1)) ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) ∧ s'.wr = s.wr := by
  unfold maskCode
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.li64_ok (s := s) (by decide) _) fun s₁ e => ?_
  subst e
  let s₁ := (s.write .t1 (sext32 ((swapMask (maskShifts.getD k 1)).setWidth 32))).write .t0
    (swapMask (maskShifts.getD k 1))
  have b₁ : s₁.gpr .s0 = s.gpr .s0 := by simp [s₁, RegUpd.gpr_write]
  have t0₁ : s₁.gpr .t0 = swapMask (maskShifts.getD k 1) := by simp [s₁, RegUpd.gpr_write]
  have ea : s₁.gpr base + BitVec.ofNat 64 (maskOff + 8 * k) = wordAddr (s.gpr .s0) (112 + k) := by
    rw [show base = .s0 from rfl, b₁, wordAddr, show maskOff + 8 * k = 8 * (112 + k) by unfold maskOff; omega]
  have e := exec_store_d (s := s₁) (t := .t0) (n := base) (off := maskOff + 8 * k)
    (by unfold maskOff; omega) (by rw [ea]; exact Straight.wordAddr_al h.al _ (by omega))
    (by rw [ea]; exact slot_in h (by omega))
  let A := wordAddr (s.gpr .s0) (112 + k)
  let v := swapMask (maskShifts.getD k 1)
  refine WP.of_runBlock ⟨{ s₁ with mem := s₁.mem.writeW A v }, by rw [runBlock_cons, e, runStep_some, runBlock_nil, ea, t0₁], rfl,
    fun r a b => ?_, rfl⟩
  show s₁.gpr r = s.gpr r
  simp only [s₁, RegUpd.gpr_write, a, b, ite_false]

theorem masks_ok {s : State} (h : Room s) : ∀ n ≤ 6,
    WP isa (.block ((List.range n).flatMap maskCode)) s fun s' =>
      (∀ k < n, s'.mem.readW (wordAddr (s.gpr .s0) (112 + k)) 64 = swapMask (maskShifts.getD k 1)) ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) ∧ s'.wr = s.wr ∧ Frame [maskR s] s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun k hk => absurd hk (by omega), fun _ _ _ => rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (masks_ok h n (by omega)) fun s₁ ⟨m₁, g₁, w₁, f₁⟩ => ?_
    have b₁ : s₁.gpr .s0 = s.gpr .s0 := g₁ _ (by decide) (by decide)
    have h₁ : Room s₁ := h.congr b₁ w₁
    refine WP.mono (maskCode_ok h₁ (k := n) (by omega)) fun s₂ ⟨m₂, g₂, w₂⟩ =>
      ⟨fun k hk => ?_, fun r a b => (g₂ r a b).trans (g₁ r a b), w₂.trans w₁, ?_⟩
    · rw [m₂, b₁]
      by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (by
          simp only [wordAddr]
          exact Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact m₁ k (by omega)
    · rw [m₂, b₁]
      exact f₁.writeW (List.mem_singleton_self _) _ (by
        simp only [maskR, wordAddr]
        rw [show 8 * (112 + n) = 8 * 112 + 8 * n by omega, ← Offset.add_add]
        exact Offset.contains_base _ (by omega) (by omega))

theorem masksAt_of {s s' : State} (hb : s'.gpr .s0 = s.gpr .s0)
    (h : ∀ k < 6, s'.mem.readW (wordAddr (s.gpr .s0) (112 + k)) 64 = swapMask (maskShifts.getD k 1)) :
    MasksAt s' := fun k hk => by rw [hb]; exact h k hk

/-! ## The setup -/

/-- The saved registers' slots, from the frame's base. -/
def savedL : List (Reg × Nat) := saved.map fun (r, o) => (r, savedOff + o)

theorem savedL_fits : Spill.Fits savedL := by decide

theorem savedL_le : ∀ p ∈ savedL, 944 ≤ p.2 ∧ p.2 + 8 ≤ 1048 := by decide

/-- A schedule from its bytes. -/
theorem scheduleAt_of_bytes {m m' : Mem} {p p' : Addr}
    (h : ∀ i < 384, m' (p' + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    scheduleAt m' p' = scheduleAt m p := by
  apply Vector.ext
  intro i hi
  rw [VG.Proof.TripleDes.scheduleAt_readW m' p' i hi, VG.Proof.TripleDes.scheduleAt_readW m p i hi]
  refine readW_of_bytes fun j hj => ?_
  rw [Offset.add_add, Offset.add_add, h _ (by omega)]

/-- What the setup needs: the frame at the stack pointer, writable, aligned
and apart from the schedules, which are readable. -/
structure SetupPre (u : State) : Prop where
  wr : (⟨u.sp, 1056⟩ : Region) ∈ u.wr
  al : u.sp.toNat % 8 = 0
  fit : u.sp.toNat + 1056 ≤ 2 ^ 64
  key : ∀ i < 384, InRegions (u.rd ++ u.wr) (u.gpr .a0 + BitVec.ofNat 64 i) 1
  sep : (⟨u.sp, 1056⟩ : Region).Disjoint ⟨u.gpr .a0, 384⟩

structure SetupPost (u v : State) : Prop where
  room : Room v
  s0 : v.gpr .s0 = u.sp
  masks : MasksAt v
  sched : scheduleAt v.mem (schedA v) = scheduleAt u.mem (u.gpr .a0)
  saved : Spill.Saved u.sp u.gpr savedL v.mem
  a1 : v.gpr .a1 = u.gpr .a1
  a2 : v.gpr .a2 = u.gpr .a2
  wr : v.wr = u.wr
  frame : Frame [⟨u.sp, 1056⟩] u.mem v.mem

theorem setup_ok {u : State} (h : SetupPre u) : WP isa setup u (SetupPost u) := by
  have fit := h.fit
  unfold setup
  apply WP.seq
  have hb : ([.addSp .t0 0] ++ saved.map (fun (r, o) => Instr.store .d r .t0 (savedOff + o)) ++
      [.addi base .t0 0, .addi .t3 base schedOff, .addi .t2 .a0 0, .li .t4 384] : List Instr) =
      .addSp .t0 0 :: (Spill.saveCode .t0 savedL ++
        [.addi base .t0 0, .addi .t3 base schedOff, .addi .t2 .a0 0, .li .t4 384]) := rfl
  rw [hb]
  let u₀ := u.write .t0 (u.sp + BitVec.ofNat 64 0)
  have t0₀ : u₀.gpr .t0 = u.sp := by simp [u₀, RegUpd.gpr_write]
  refine WP.block_cons_iff.mpr ⟨u₀, exec_addSp (s := u) (d := .t0) (imm := 0) (by decide), ?_⟩
  refine Spill.save_ok (by rw [t0₀]; exact h.al) savedL_fits.1 (fun p hp => ?_) ?_
  · rw [t0₀]
    exact ⟨_, h.wr, Offset.contains_base _ (by have := (savedL_le p hp).2; omega) (by have := (savedL_le p hp).2; omega)⟩
  let u₁ : State := { u₀ with mem := Spill.saveMem u₀.mem (u₀.gpr .t0) u₀.gpr savedL }
  have e₂ := exec_addi (s := u₁) (d := .s0) (n := .t0) (imm := 0) (by decide)
  let u₂ := u₁.write .s0 (u₁.gpr .t0 + BitVec.ofInt 64 0)
  have e₃ := exec_addi (s := u₂) (d := .t3) (n := .s0) (imm := (schedOff : Int)) (by decide)
  let u₃ := u₂.write .t3 (u₂.gpr .s0 + BitVec.ofInt 64 (schedOff : Int))
  have e₄ := exec_addi (s := u₃) (d := .t2) (n := .a0) (imm := 0) (by decide)
  let u₄ := u₃.write .t2 (u₃.gpr .a0 + BitVec.ofInt 64 0)
  have e₅ := exec_li (s := u₄) (d := .t4) (imm := 384) (by decide)
  let u₅ := u₄.write .t4 (BitVec.ofInt 64 384)
  have s0₅ : u₅.gpr .s0 = u.sp := by
    simp [u₅, u₄, u₃, u₂, u₁, RegUpd.gpr_write, t0₀]
  have t3₅ : u₅.gpr .t3 = u.sp + BitVec.ofNat 64 schedOff := by
    simp [u₅, u₄, u₃, u₂, u₁, RegUpd.gpr_write, t0₀]
  have t2₅ : u₅.gpr .t2 = u.gpr .a0 := by
    simp [u₅, u₄, u₃, u₂, u₁, u₀, RegUpd.gpr_write]
  have t4₅ : u₅.gpr .t4 = BitVec.ofNat 64 384 := by
    simp [u₅, RegUpd.gpr_write]
  have g₅ : ∀ r, r ≠ .t0 → r ≠ .s0 → r ≠ .t3 → r ≠ .t2 → r ≠ .t4 → u₅.gpr r = u.gpr r := by
    intro r a b c d e
    simp [u₅, u₄, u₃, u₂, u₁, u₀, RegUpd.gpr_write, a, b, c, d, e]
  have m₅ : u₅.mem = Spill.saveMem u.mem u.sp u₀.gpr savedL := by
    show Spill.saveMem u₀.mem (u₀.gpr .t0) u₀.gpr savedL = _
    rw [t0₀]; rfl
  have f₅ : Frame [⟨u.sp, 1056⟩] u.mem u₅.mem := by
    rw [m₅]
    have := Spill.saveMem_frame (lo := 0) (n := 1056) (fun p hp => ⟨Nat.zero_le _, by have := (savedL_le p hp).2; omega⟩)
      (by decide) u.mem u.sp u₀.gpr
    simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using this
  have hkey₅ : (⟨u.sp + BitVec.ofNat 64 schedOff, 384⟩ : Region).Disjoint ⟨u.gpr .a0, 384⟩ :=
    h.sep.sub_left (Offset.sub_base _ (by unfold schedOff; omega))
  refine WP.block_cons_iff.mpr ⟨u₂, e₂, WP.block_cons_iff.mpr ⟨u₃, e₃, WP.block_cons_iff.mpr ⟨u₄, e₄,
    WP.block_cons_iff.mpr ⟨u₅, e₅, WP.block_nil ?_⟩⟩⟩⟩
  -- the schedules copied
  apply WP.seq
  refine WP.mono (copyLoop_ok (tmp := .t1) (src := .t2) (dst := .t3) (cnt := .t4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) u₅ (N := 384) (by decide) (by decide) t4₅
    (fun i hi => by rw [t2₅]; exact h.key i hi)
    (fun i hi => by
      rw [t3₅]
      exact ⟨_, h.wr, by rw [Offset.add_add]; exact Offset.contains_base _ (by unfold schedOff; omega) (by unfold schedOff; omega)⟩)
    (by rw [t2₅, t3₅]; exact sep_of_disjoint hkey₅)) fun u₆ ⟨c₆, f₆, k₆⟩ => ?_
  have s0₆ : u₆.gpr .s0 = u.sp := (k₆.1 _ (by decide)).trans s0₅
  have wr₆ : u₆.wr = u.wr := k₆.2.2
  have h₆ : Room u₆ :=
    ⟨by simp only [frameR, s0₆, wr₆, frameBytes]; exact h.wr, by rw [s0₆]; exact h.al,
      by rw [s0₆]; unfold frameBytes; omega⟩
  -- the masks
  rw [storeMasks_eq]
  refine WP.mono (masks_ok h₆ 6 (Nat.le_refl _)) fun v ⟨m₇, g₇, w₇, f₇⟩ => ?_
  have s0₇ : v.gpr .s0 = u.sp := (g₇ _ (by decide) (by decide)).trans s0₆
  have hm₇ : maskR u₆ = ⟨u.sp + BitVec.ofNat 64 896, 48⟩ := by simp only [maskR, s0₆]
  rw [hm₇] at f₇
  have f₆' : Frame [⟨u.sp + BitVec.ofNat 64 schedOff, 384⟩] u₅.mem u₆.mem := by rw [← t3₅]; exact f₆
  refine ⟨h₆.congr (s0₇.trans s0₆.symm) w₇, s0₇, masksAt_of (s := u₆) (g₇ _ (by decide) (by decide)) m₇, ?_, ?_,
    (g₇ _ (by decide) (by decide)).trans ((k₆.1 _ (by decide)).trans (g₅ _ (by decide) (by decide)
      (by decide) (by decide) (by decide))),
    (g₇ _ (by decide) (by decide)).trans ((k₆.1 _ (by decide)).trans (g₅ _ (by decide) (by decide)
      (by decide) (by decide) (by decide))), w₇.trans wr₆, ?_⟩
  · -- the schedule
    rw [show schedA v = u.sp + BitVec.ofNat 64 schedOff by simp only [schedA, s0₇]]
    rw [VG.Proof.TripleDes.scheduleAt_eq_of_frame _ f₇ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by unfold schedOff; omega)) (by unfold schedOff; omega) (by omega)]
    refine scheduleAt_of_bytes fun i hi => ?_
    have e := c₆ i hi
    rw [t3₅, t2₅] at e
    rw [e, m₅]
    refine Spill.saveMem_frame (lo := 0) (n := 1056) (fun p hp => ⟨Nat.zero_le _, by have := (savedL_le p hp).2; omega⟩)
      (by decide) u.mem u.sp u₀.gpr _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rw [BitVec.add_zero] at hc
    exact h.sep _ hc (Offset.contains_base _ (by omega) (by omega))
  · -- the saved registers
    have sv₅ : Spill.Saved u.sp u.gpr savedL u₅.mem := by
      rw [m₅]
      intro p hp
      rw [Spill.saveMem_saved savedL_fits u.mem u.sp u₀.gpr p hp]
      have hne : p.1 ≠ .t0 := by revert p; decide
      simp [u₀, RegUpd.gpr_write, hne]
    have dj : ∀ (lo n : Nat), lo + n ≤ 944 → (⟨u.sp + BitVec.ofNat 64 944, 104⟩ : Region).Disjoint
        ⟨u.sp + BitVec.ofNat 64 lo, n⟩ := fun lo n hl =>
      Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    exact (sv₅.frame_in (lo := 944) (n := 104) (fun p hp => ⟨(savedL_le p hp).1, (savedL_le p hp).2⟩) f₆' fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dj _ _ (by unfold schedOff; omega)).frame_in
      (lo := 944) (n := 104) (fun p hp => ⟨(savedL_le p hp).1, (savedL_le p hp).2⟩) f₇
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dj _ _ (by omega)
  · -- the frame
    have sub : ∀ (lo n : Nat), lo + n ≤ 1056 → ∀ r ∈ [(⟨u.sp + BitVec.ofNat 64 lo, n⟩ : Region)],
        ∃ r' ∈ [(⟨u.sp, 1056⟩ : Region)], Region.Sub r r' := fun lo n hl r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ hl⟩
    exact (f₅.trans (f₆'.sub (sub _ _ (by unfold schedOff; omega)))).trans (f₇.sub (sub _ _ (by omega)))

/-! ## The batches -/

/-- What stays true of the data and the frame through the batches. -/
structure LoopEnv (B D : Addr) (n : Nat) (W : List Region) : Prop where
  data : ∀ i < 8 * n, InRegions W (D + BitVec.ofNat 64 i) 1
  fit : D.toNat + 8 * n ≤ 2 ^ 64
  sep : (⟨D, 8 * n⟩ : Region).Disjoint ⟨B, 1056⟩

/-- After the first `p` blocks. -/
structure LoopInv (d : Direction) (s : State) (B D : Addr) (n : Nat) (K : Schedule) (g : Reg → BitVec 64)
    (W : List Region) (p : Nat) (v : State) : Prop where
  le : p ≤ n
  room : Room v
  s0 : v.gpr .s0 = B
  masks : MasksAt v
  sched : scheduleAt v.mem (schedA v) = K
  a1 : v.gpr .a1 = wAt D p
  a2 : v.gpr .a2 = BitVec.ofNat 64 (n - p)
  wr : v.wr = W
  done : ∀ b < p, blockAt v.mem (wAt D b) = blockOut K d (blockAt s.mem (wAt D b))
  rest : ∀ b, p ≤ b → b < n → blockAt v.mem (wAt D b) = blockAt s.mem (wAt D b)
  saved : Spill.Saved B g savedL v.mem

theorem batch_step {d : Direction} {s : State} {B D : Addr} {n : Nat} {K : Schedule} {g : Reg → BitVec 64}
    {W : List Region} (E : LoopEnv B D n W) {p : Nat} (hp : p < n) {v : State}
    (I : LoopInv d s B D n K g W p v) :
    WP isa (batch d) v fun v' => LoopInv d s B D n K g W (p + min (n - p) 64) v' := by
  have fit := E.fit
  have hrem : (v.gpr .a2).toNat = n - p := by rw [I.a2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hkv : kOf v = min (n - p) 64 := by rw [kOf, hrem]
  have hDp : (wAt D p).toNat = D.toNat + 8 * p := by
    rw [wAt, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * p) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have pre : BatchPre v := by
    refine ⟨I.room, I.masks, by omega, ⟨fun i hi => ?_, by rw [hrem, I.a1, hDp]; omega, ?_⟩⟩
    · rw [I.wr, I.a1, wAt, Offset.add_add]; exact E.data _ (by rw [hrem] at hi; omega)
    · simp only [frameR, I.a1, I.s0, hrem, frameBytes]
      exact E.sep.sub_left (Offset.sub_base _ (by omega))
  refine WP.mono (batch_ok d pre) fun v' q => ?_
  obtain ⟨qs0, qa1, qa2, qwr, qout, qframe⟩ := q
  rw [hkv] at qa1 qa2 qout qframe
  generalize hk : min (n - p) 64 = k at qa1 qa2 qout qframe
  have hk1 : 1 ≤ k := by omega
  have hkn : k ≤ n - p := by omega
  have hst : stR v = ⟨B, 512⟩ := by simp only [stR, I.s0]
  have a1v : v.gpr .a1 = wAt D p := I.a1
  rw [hst, a1v] at qframe
  rw [a1v] at qa1 qout
  -- regions written by the batch, apart from the frame's other words and the other blocks
  have dataSub : Region.Sub ⟨wAt D p, 8 * k⟩ ⟨D, 8 * n⟩ := Offset.sub_base _ (by omega)
  have offB : ∀ (lo m : Nat), 512 ≤ lo → lo + m ≤ 1056 →
      ∀ r ∈ [(⟨B, 512⟩ : Region), ⟨wAt D p, 8 * k⟩], Region.Disjoint ⟨B + BitVec.ofNat 64 lo, m⟩ r :=
    fun lo m h1 h2 r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ h1 (by have := I.room.fit; rw [I.s0] at this; unfold frameBytes at this; omega)
      · exact (E.sep.sub_left dataSub).symm.sub_left (Offset.sub_base _ h2)
  have blk : ∀ b, (b < p ∨ p + k ≤ b) → b < n →
      ∀ r ∈ [(⟨B, 512⟩ : Region), ⟨wAt D p, 8 * k⟩], Region.Disjoint ⟨wAt D b, 8⟩ r := fun b hb hbn r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (E.sep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))
    · simp only [wAt]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have s0' : v'.gpr .s0 = B := qs0.trans I.s0
  refine ⟨by omega, I.room.congr qs0 qwr, s0', ?_, ?_, by rw [qa1, wAt_wAt], ?_, qwr.trans I.wr,
    fun b hb => ?_, fun b hb hbn => ?_, ?_⟩
  · -- the masks
    intro j hj
    rw [s0', ← I.s0, ← I.masks j hj, I.s0]
    exact qframe.readW (Region.contains_self _ 8) (by
      intro r hr
      have := offB (896 + 8 * j) 8 (by omega) (by omega) r hr
      simp only [wordAddr]; rw [show 8 * (112 + j) = 896 + 8 * j by omega]; exact this) (by decide)
  · -- the schedules
    rw [show schedA v' = schedA v by simp only [schedA, s0', I.s0], ← I.sched]
    refine VG.Proof.TripleDes.scheduleAt_eq_of_frame _ qframe fun r hr => ?_
    simp only [schedA, I.s0]
    exact offB 512 384 (by omega) (by omega) r hr
  · rw [qa2, I.a2, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hkn]; congr 1; omega
  · -- the blocks done
    by_cases e : b < p
    · rw [blockAt_frame qframe (blk b (.inl e) (by omega)), I.done b e]
    · have hb' : b - p < k := by omega
      have := qout (b - p) hb'
      rw [wAt_wAt, show p + (b - p) = b by omega, I.sched, I.rest b (by omega) (by omega)] at this
      exact this
  · rw [blockAt_frame qframe (blk b (.inr hb) hbn), I.rest b (by omega) hbn]
  · exact I.saved.frame_in (lo := 944) (n := 104) (fun p hp => ⟨(savedL_le p hp).1, (savedL_le p hp).2⟩)
      qframe fun r hr => offB 944 104 (by omega) (by omega) r hr

theorem loop_ok {d : Direction} {s : State} {B D : Addr} {n : Nat} {K : Schedule} {g : Reg → BitVec 64}
    {W : List Region} (E : LoopEnv B D n W) (hn : 0 < n) {v : State} (I : LoopInv d s B D n K g W 0 v) :
    WP isa (.loop (batch d) (.nonzero .a2)) v (LoopInv d s B D n K g W n) := by
  have fit := E.fit
  refine WP.loop (M := isa) (fun m v => ∃ p, p < n ∧ m = n - p ∧ LoopInv d s B D n K g W p v) ?_ n v
    ⟨0, hn, rfl, I⟩
  rintro m v ⟨p, hp, rfl, J⟩
  refine WP.mono (batch_step E hp J) fun v' J' => ?_
  rw [Steps.eval_nonzero_ofNat _ _ (by omega) J'.a2]
  by_cases e : n - (p + min (n - p) 64) = 0
  · left
    refine ⟨by simp [e], ?_⟩
    rwa [show p + min (n - p) 64 = n by omega] at J'
  · right
    exact ⟨by simp [e], _, by omega, _, by omega, rfl, J'⟩

/-! ## The end -/

theorem restores_eq : (saved.map fun (r, o) => Instr.load .d r base (savedOff + o)) =
    Spill.restoreCode .s0 savedL := rfl

theorem finish_ok {d : Direction} {s : State} {B D : Addr} {n : Nat} {K : Schedule} {g : Reg → BitVec 64}
    {W : List Region} (E : LoopEnv B D n W) {v : State} (I : LoopInv d s B D n K g W n v) :
    WP isa finish v fun y => (∀ r ∈ savedL.map Prod.fst, y.gpr r = g r) ∧
      ∀ b < n, blockAt y.mem (wAt D b) = blockOut K d (blockAt s.mem (wAt D b)) := by
  have fit := E.fit
  have al : B.toNat % 8 = 0 := by rw [← I.s0]; exact I.room.al
  have bfit : B.toNat + 1056 ≤ 2 ^ 64 := by rw [← I.s0]; exact I.room.fit
  have inF : ∀ o m, o + m ≤ 1056 → InRegions v.wr (B + BitVec.ofNat 64 o) m := fun o m hm =>
    ⟨_, by have := I.room.frame; rwa [frameR, I.s0] at this, Offset.contains_base _ (by unfold frameBytes; omega)
      (by omega)⟩
  unfold finish
  have e₁ := exec_li (s := v) (d := .t1) (imm := 0) (by decide)
  let w₁ := v.write .t1 (BitVec.ofInt 64 0)
  have e₂ := exec_addi (s := w₁) (d := .t0) (n := base) (imm := 0) (by decide)
  let w₂ := w₁.write .t0 (w₁.gpr base + BitVec.ofInt 64 0)
  have e₃ := exec_li (s := w₂) (d := .t4) (imm := ((savedOff / 8 : Nat) : Int)) (by decide)
  let w₃ := w₂.write .t4 (BitVec.ofInt 64 ((savedOff / 8 : Nat) : Int))
  apply WP.seq
  refine WP.of_runBlock ⟨w₃, by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some,
      runBlock_nil], ?_⟩
  have t0₃ : w₃.gpr .t0 = B := by simp [w₃, w₂, w₁, RegUpd.gpr_write, base, I.s0]
  have s0₃ : w₃.gpr .s0 = B := by simp [w₃, w₂, w₁, RegUpd.gpr_write, I.s0]
  have t4₃ : w₃.gpr .t4 = BitVec.ofNat 64 118 := by simp [w₃, RegUpd.gpr_write]; rfl
  apply WP.seq
  refine WP.mono (fillLoop_ok (v := .t1) (ptr := .t0) (cnt := .t4) (by decide) (by decide) (by decide) w₃
    (N := 118) (by decide) (by decide) t4₃ (by rw [t0₃]; exact al)
    (fun i hi => by rw [t0₃]; exact inF _ _ (by omega))) fun x ⟨_, fx, kx⟩ => ?_
  have s0x : x.gpr .s0 = B := (kx.1 _ (by decide)).trans s0₃
  rw [t0₃] at fx
  rw [restores_eq]
  have sv : Spill.Saved B g savedL x.mem :=
    I.saved.frame_in (lo := 944) (n := 104) (fun p hp => ⟨(savedL_le p hp).1, (savedL_le p hp).2⟩) fx
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega) (by omega)
  refine WP.mono (Spill.restore_wp (b := .s0) al s0x savedL_fits.1 (by decide) (fun p hp => ?_) sv)
    fun y r => ⟨fun q hq => r.gpr_of (.inl hq), fun b hb => ?_⟩
  · rw [kx.2.2]
    obtain ⟨R, hR, hc⟩ := inF p.2 8 (by have := (savedL_le p hp).2; omega)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  · rw [r.mem, blockAt_frame fx fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (E.sep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))]
    exact I.done b hb

/-! ## The function -/

theorem preserved_saved : ∀ r ∈ preserved, r ∈ savedL.map Prod.fst := by decide

/-- What ECB may assume: the schedule readable, the `n` blocks writable,
apart from each other and from the 1056 bytes below the stack pointer, the
blocks not wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 384⟩]
  wr : s.wr = [⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩]
  keyData : (⟨s.gpr .a0, 384⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
  fit : (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64
  al : s.sp.toNat % 16 = 0
  sp : 1056 ≤ s.sp.toNat
  stackKey : (⟨s.sp - 1056, 1056⟩ : Region).Disjoint ⟨s.gpr .a0, 384⟩
  stackData : (⟨s.sp - 1056, 1056⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩

theorem ecb_wp (d : Direction) {s : State} (h : EcbPre s) :
    WP isa (Impl.TripleDes.RISCV64.Bitslice.ecb d) s fun s' => abiPreserved s s' ∧ ∀ b < (s.gpr .a2).toNat,
      blockAt s'.mem (wAt (s.gpr .a1) b) =
        blockOut (scheduleAt s.mem (s.gpr .a0)) d (blockAt s.mem (wAt (s.gpr .a1) b)) := by
  have fit := h.fit
  have hsp := h.sp
  have hal := h.al
  let D := s.gpr .a1
  let n := (s.gpr .a2).toNat
  let K := scheduleAt s.mem (s.gpr .a0)
  unfold Impl.TripleDes.RISCV64.Bitslice.ecb
  refine WP.ite (s.gpr .a2 == 0) (by rw [Steps.eval_zero]) (fun hz => ?_) (fun hz => ?_)
  · have hn : (s.gpr .a2).toNat = 0 := by simp only [beq_iff_eq] at hz; simp [hz]
    exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, fun b hb => absurd hb (by omega)⟩
  have hn : 0 < n := by
    have : s.gpr .a2 ≠ 0 := by simpa using hz
    have : (s.gpr .a2).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
    omega
  refine WP.alloc (n := frameBytes) ⟨by decide, by decide, by decide⟩ h.sp ?_
  let u := allocd frameBytes s
  have usp : u.sp = s.sp - 1056 := rfl
  have uspN : u.sp.toNat = s.sp.toNat - 1056 := by
    rw [usp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; show 1056 ≤ s.sp.toNat; omega)]; rfl
  have stackU : (⟨u.sp, 1056⟩ : Region) ∈ u.wr := List.mem_cons_self
  have pre : SetupPre u :=
    ⟨stackU, by rw [uspN]; omega, by rw [uspN]; omega,
      fun i hi => ⟨_, List.mem_append_left _ (by show _ ∈ s.rd; rw [h.rd]; exact List.mem_singleton_self _),
        Offset.contains_base _ (by omega) (by omega)⟩, h.stackKey⟩
  have body : WP isa (.seq setup (.seq (.loop (batch d) (.nonzero .a2)) finish)) u fun y =>
      (∀ r ∈ savedL.map Prod.fst, y.gpr r = u.gpr r) ∧
      ∀ b < n, blockAt y.mem (wAt D b) = blockOut K d (blockAt s.mem (wAt D b)) := by
    apply WP.seq
    refine WP.mono (setup_ok pre) fun v q => ?_
    have E : LoopEnv u.sp D n u.wr :=
      ⟨fun i hi => ⟨_, List.mem_cons_of_mem _ (by rw [h.wr]; exact List.mem_singleton_self _),
          Offset.contains_base _ (by omega) (by omega)⟩, fit, h.stackData.symm⟩
    have I0 : LoopInv d s u.sp D n K u.gpr u.wr 0 v :=
      ⟨Nat.zero_le _, q.room, q.s0, q.masks, q.sched, by rw [q.a1]; exact (BitVec.add_zero _).symm,
        by rw [q.a2, Nat.sub_zero]; exact ((BitVec.ofNat_toNat 64 (s.gpr .a2)).trans (BitVec.setWidth_eq _)).symm, q.wr, fun b hb => absurd hb (by omega),
        fun b _ hbn => blockAt_frame q.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (h.stackData.symm.sub_left (Offset.sub_base _ (by omega))),
        q.saved⟩
    apply WP.seq
    refine WP.mono (loop_ok E hn I0) fun w J => ?_
    exact finish_ok E J
  refine WP.mono (WP.rdwr body) fun y ⟨⟨gy, by_⟩, _, _, spy⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun b hb => ?_⟩
  · show y.gpr r = s.gpr r
    exact gy r (preserved_saved r hr)
  · show y.sp + BitVec.ofNat 64 frameBytes = s.sp
    rw [spy, usp]; exact BitVec.sub_add_cancel s.sp _
  · show y.gpr .ra = s.gpr .ra
    exact gy .ra (by decide)
  · have e : (freed frameBytes y).mem = y.mem := by simp only [freed]
    rw [e]; exact by_ b hb

end VG.Proof.TripleDes.RISCV64.Bitsliced
