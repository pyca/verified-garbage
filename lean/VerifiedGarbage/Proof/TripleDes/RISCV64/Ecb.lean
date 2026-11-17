module

public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.RISCV64.BigFrame
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModeCore
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Ecb
public import VerifiedGarbage.Proof.Modes.RISCV64.Core

/-! ### `TripleDes.RISCV64.EcbLoop`, which this module and modules that import it used -/

section

/-!
# ECB's loop

`loop_ok`: the loop of ECB's blocks, each encrypted (or decrypted) in place
by the block function under the schedules' copy in the frame, the data
pointer in `s2` and the blocks left in `s3`.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Ecb

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.TripleDes.RISCV64 VG.Impl.TripleDes.RISCV64.Ecb
open VG.Proof.Modes.RISCV64 (slotA kept)
open VG.Spec.TripleDes (Direction Schedule)
open VG.Proof.TripleDes (blockAt_eq_of_frame scheduleAt_eq_of_frame)

/-- The block `b` of the data at `D`. -/
abbrev wAt (D : Addr) (b : Nat) : Addr := D + BitVec.ofNat 64 (8 * b)

/-- The loop's fixed facts: the frame at `B`, writable as one region, the
`n` blocks at `D`, writable and apart from it. -/
structure Env (B D : Addr) (n : Nat) (ws : List Region) : Prop where
  al : B.toNat % 16 = 0
  fit : B.toNat + 944 ≤ 2 ^ 64
  frame : (⟨B, 944⟩ : Region) ∈ ws
  data : (⟨D, 8 * n⟩ : Region) ∈ ws
  dataFit : D.toNat + 8 * n ≤ 2 ^ 64
  sep : (⟨D, 8 * n⟩ : Region).Disjoint ⟨B, 944⟩

/-- After `j` blocks, from `s₀`, before the loop. -/
structure EInv (k : Schedule) (d : Direction) (B D : Addr) (n : Nat) (s₀ : State) (j : Nat)
    (u : State) : Prop where
  le : j ≤ n
  ptr : u.gpr .s2 = wAt D j
  cnt : u.gpr .s3 = BitVec.ofNat 64 (n - j)
  b : u.gpr sb = B
  keys : Spec.TripleDes.scheduleAt u.mem (B + BitVec.ofNat 64 keyOff) = k
  keep : ∀ r ∈ kept, r ≠ .s2 → r ≠ .s3 → u.gpr r = s₀.gpr r
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  sp : u.sp = s₀.sp
  saved : ∀ i < 4, u.mem.readW (slotA B i) 64 = s₀.mem.readW (slotA B i) 64
  done : ∀ b < j, Spec.TripleDes.blockAt u.mem (wAt D b) =
    blockResult k d (Spec.TripleDes.blockAt s₀.mem (wAt D b))
  rest : ∀ b, j ≤ b → b < n → Spec.TripleDes.blockAt u.mem (wAt D b) =
    Spec.TripleDes.blockAt s₀.mem (wAt D b)

theorem step_ok {k : Schedule} {d : Direction} {B D : Addr} {n : Nat} {s₀ : State}
    (E : Env B D n s₀.wr) {j : Nat} (hj : j < n) {u : State} (I : EInv k d B D n s₀ j u) :
    WP isa (.seq (block d .s2 0) (.block advance)) u fun u' =>
      EInv k d B D n s₀ (j + 1) u' ∧ u'.gpr .s3 = BitVec.ofNat 64 (n - (j + 1)) := by
  have fit := E.dataFit
  have hsub : Region.Sub ⟨wAt D j, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hj])
  have hpre : BlockPre k .s2 0 u := by
    refine ⟨by decide, by decide, by rw [I.b]; have := E.al; omega_using [this], fun o ho => ?_,
      by rw [I.b]; exact I.keys, ?_, ?_⟩
    · rw [I.wr, I.b]; exact ⟨_, E.frame, Offset.contains_base _ (by omega_using [ho]) (by have := E.fit; omega_using [ho])⟩
    · rw [I.wr, I.ptr, BitVec.add_zero]
      exact ⟨_, E.data, Offset.contains_base D (by omega_using [hj]) (by omega_using [hj, fit])⟩
    · simp only [workRegion, I.ptr, I.b, BitVec.add_zero]
      exact (E.sep.sub_left hsub).sub_right (Offset.sub_base _ (by decide))
  apply WP.seq
  refine WP.mono (block_ok k d .s2 0 u hpre) fun u₁ h₁ => ?_
  have ptr₁ : u₁.gpr .s2 = wAt D j := (h₁.regs .s2 (by decide)).trans I.ptr
  refine wp_addi (by decide) fun u₂ h₂ => wp_subi (by decide) fun u₃ h₃ => WP.block_nil ?_
  have hb₁ : u₁.gpr sb = B := (h₁.regs sb (by decide)).trans I.b
  have hfr : Frame [⟨wAt D j, 8⟩, ⟨B + BitVec.ofNat 64 56, 504⟩] u.mem u₁.mem := by
    have h := h₁.frame
    simp only [I.ptr, BitVec.add_zero, workRegion, I.b] at h
    exact h
  have m₃ : u₃.mem = u₁.mem := by rw [h₃.mem, h₂.mem]
  have frameOut : ∀ {R : Region}, Region.Sub R ⟨D, 8 * n⟩ → R.Disjoint ⟨wAt D j, 8⟩ →
      ∀ r ∈ [(⟨wAt D j, 8⟩ : Region), ⟨B + BitVec.ofNat 64 56, 504⟩], R.Disjoint r :=
    fun hR hj r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hj
      · exact (E.sep.sub_left hR).sub_right (Offset.sub_base _ (by decide))
  have slotOut : ∀ i < 4, ∀ r ∈ [(⟨wAt D j, 8⟩ : Region), ⟨B + BitVec.ofNat 64 56, 504⟩],
      Region.Disjoint ⟨slotA B i, 8⟩ r := fun i hi r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((E.sep.sub_left hsub).sub_right
        (Offset.sub_base B (d := 8 * i) (n := 8) (k := 944) (by omega_using [hi]))).symm
    · exact Offset.disjoint _ (.inl (by omega_using [hi])) (by omega_using [hi]) (by decide)
  refine ⟨⟨by omega_using [hj], ?_, ?_, ?_, ?_, fun r hr h2 h3 => ?_, ?_, ?_, ?_, fun i hi => ?_,
    fun b hb => ?_, fun b h1 h2 => ?_⟩, ?_⟩
  · rw [h₃.other _ (by decide), h₂.gpr, ptr₁]
    show D + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 = D + BitVec.ofNat 64 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat, show 8 * j + 8 = 8 * (j + 1) by omega_using []]
  · rw [h₃.gpr, h₂.other _ (by decide), h₁.regs .s3 (by decide), I.cnt]
    apply BitVec.eq_of_toNat_eq; simp; omega_using [hj]
  · rw [h₃.other _ (by decide), h₂.other _ (by decide), hb₁]
  · rw [m₃, scheduleAt_eq_of_frame _ hfr fun r hr => ?_, I.keys]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((E.sep.sub_left hsub).sub_right (Offset.sub_base _ (by decide))).symm
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  · rw [h₃.other r h3, h₂.other r h2, h₁.regs r (Mode.kept_sub r hr), I.keep r hr h2 h3]
  · rw [h₃.rd, h₂.rd, h₁.rd, I.rd]
  · rw [h₃.wr, h₂.wr, h₁.wr, I.wr]
  · rw [h₃.sp, h₂.sp, h₁.sp, I.sp]
  · rw [m₃, ← I.saved i hi]
    exact hfr.readW (Region.contains_self _ _) (slotOut i hi) (by decide)
  · rw [m₃]
    by_cases hbj : b = j
    · subst hbj
      have hr := h₁.result
      rw [I.ptr, BitVec.add_zero] at hr
      rw [hr, I.rest b (by omega_using []) hj]
    · rw [blockAt_eq_of_frame _ hfr (frameOut (Offset.sub_base D (by omega_using [hj, hb]))
        (Offset.disjoint D (by omega_using [hbj]) (by omega_using [hj, fit, hb]) (by omega_using [hj, fit])))]
      exact I.done b (by omega_using [hb, hbj])
  · rw [m₃, blockAt_eq_of_frame _ hfr (frameOut (Offset.sub_base D (by omega_using [h2]))
      (Offset.disjoint D (by omega_using [h1]) (by omega_using [fit, h2]) (by omega_using [hj, fit])))]
    exact I.rest b (by omega_using [h1]) h2
  · rw [h₃.gpr, h₂.other _ (by decide), h₁.regs .s3 (by decide), I.cnt]
    apply BitVec.eq_of_toNat_eq; simp; omega_using [hj]

theorem loop_ok {k : Schedule} {d : Direction} {B D : Addr} {n : Nat} {s₀ : State}
    (E : Env B D n s₀.wr) (hn : 0 < n) (I : EInv k d B D n s₀ 0 s₀) :
    WP isa (.loop (.seq (block d .s2 0) (.block advance)) (.nonzero .s3)) s₀
      (EInv k d B D n s₀ n) := by
  refine WP.loop (M := isa) (Q := EInv k d B D n s₀ n)
    (fun m v => ∃ j, j < n ∧ m = n - j ∧ EInv k d B D n s₀ j v) ?_ n s₀ ⟨0, hn, rfl, I⟩
  intro m v ⟨j, hj, hm, J⟩
  refine WP.mono (step_ok E hj J) fun v' ⟨J', hz⟩ => ?_
  have hn64 : n < 2 ^ 64 := by have := E.dataFit; omega_using [this]
  rw [eval_nonzero, hz, ofNat_bne_zero' (by omega_using [hn64])]
  by_cases e : j + 1 = n
  · left
    exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp; omega_using [hj, e], n - (j + 1), by omega_using [hj, hm], j + 1, by omega_using [hj, e], rfl, J'⟩

end VG.Proof.TripleDes.RISCV64.Ecb

end

end

/-!
# Triple DES ECB on RISC-V

`ecb_wp`: in the modes' frame of 118 slots below the stack pointer, the
caller's `s1`–`s4` saved (`saves_wp`), the schedules copied
(`Mode.prepare_wp`), the blocks (`loop_ok`), the registers restored
(`restore_wp`) and the frame zeroed (`wipe_wp`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Ecb

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.TripleDes.RISCV64 VG.Impl.TripleDes.RISCV64.Ecb
open VG.Proof.Modes.RISCV64 (slotA kept Fb Saves saves_wp scrIn_of' restore_wp wipe_wp coreRegion
  ScrIn)
open VG.Impl.Modes.RISCV64 (Core)
open VG.Spec.TripleDes (Direction Schedule)
open VG.Proof.TripleDes (blockAt_eq_of_frame scheduleAt_eq_of_frame)

/-- What ECB may assume: the schedule readable, the `n` blocks writable,
apart from each other and from the 944 bytes below the stack pointer, the
blocks not wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 384⟩]
  wr : s.wr = [⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩]
  keyData : (⟨s.gpr .a0, 384⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
  fit : (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64
  al : s.sp.toNat % 16 = 0
  sp : 944 ≤ s.sp.toNat
  stackKey : (⟨s.sp - 944, 944⟩ : Region).Disjoint ⟨s.gpr .a0, 384⟩
  stackData : (⟨s.sp - 944, 944⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩

theorem ecb_wp (d : Direction) {s : State} (h : EcbPre s) :
    WP isa (Ecb.ecb d) s fun s' => abiPreserved s s' ∧ ∀ b < (s.gpr .a2).toNat,
      Spec.TripleDes.blockAt s'.mem (wAt (s.gpr .a1) b) =
        blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .a0)) d
          (Spec.TripleDes.blockAt s.mem (wAt (s.gpr .a1) b)) := by
  have fit := h.fit
  let c := dirCore d
  let D := s.gpr .a1
  let n := (s.gpr .a2).toNat
  let k := Spec.TripleDes.scheduleAt s.mem (s.gpr .a0)
  obtain hL := Mode.layout d
  have htot : c.total = 118 := rfl
  have hB : Fb s c = s.sp - 944 := rfl
  unfold Ecb.ecb
  refine WP.ite (s.gpr .a2 == 0) (by rw [eval_zero]) (fun hz => ?_) (fun hz => ?_)
  · have hn : (s.gpr .a2).toNat = 0 := by simp only [beq_iff_eq] at hz; simp [hz]
    exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, fun b hb => absurd hb (by omega_using [hn])⟩
  obtain hn : 0 < n := by
    have : s.gpr .a2 ≠ 0 := by simpa using hz
    have : (s.gpr .a2).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
    omega
  obtain hBnat : (Fb s c).toNat = s.sp.toNat - 944 := Proof.Modes.RISCV64.fb_toNat' (c := c) h.sp
  refine bigFrame_wp (n := 8 * c.total) (by rw [htot]) (by rw [htot]; exact h.sp) fun t ht hw => ?_
  obtain hS : ScrIn t (Fb s c) c.total := scrIn_of' h.al h.sp hL ht hw
  obtain ⟨ws, hws⟩ := ht.wr
  obtain hframeR : (⟨Fb s c, 944⟩ : Region) ∈ t.wr := hS.whole (by rw [htot]; decide)
  obtain hdataR : (⟨D, 8 * n⟩ : Region) ∈ t.wr := by rw [hws, h.wr]; simp [D, n]
  obtain sepDF : (⟨D, 8 * n⟩ : Region).Disjoint ⟨Fb s c, 944⟩ := by rw [hB]; exact h.stackData.symm
  -- The entry.
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (saves_wp hL hS ht) fun s₁ h₁ => wp_mv fun s₂ u₂ => WP.block_nil ?_
  obtain b₂ : s₂.gpr sb = Fb s c := by rw [u₂.other _ (by decide)]; exact h₁.b
  obtain a0₂ : s₂.gpr .a0 = s.gpr .a0 :=
    by rw [u₂.other _ (by decide), h₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  obtain s2₂ : s₂.gpr .s2 = D := by rw [u₂.other _ (by decide), h₁.s2]
  obtain s3₂ : s₂.gpr .s3 = s.gpr .a2 := by
    rw [u₂.gpr, h₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  obtain keep₂ : ∀ r ∈ kept, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s₂.gpr r = s.gpr r :=
    fun r hr h1 h2 h3 h4 => by
      rw [u₂.other r h3, h₁.other r (Proof.Modes.RISCV64.kept_ne_entry r hr).1 h1 h2 h3 h4]
  obtain rd₂ : s₂.rd = s.rd := by rw [u₂.rd, h₁.rd]
  obtain wr₂ : s₂.wr = t.wr := by rw [u₂.wr, h₁.wr]
  have m₂ : s₂.mem = s₁.mem := u₂.mem
  -- The schedules copied.
  let rs : List Region := [⟨Fb s c, 8 * c.total⟩, ⟨D, 8 * n⟩]
  obtain hk : Mode.KeyArgs s₂ rs k := by
    refine ⟨?_, by simp only [Mode.keyR, rd₂, a0₂, h.rd]; simp, fun r hr => ?_⟩
    · rw [a0₂, m₂, scheduleAt_eq_of_frame _ h₁.frame fun r hr => ?_]
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stackKey.symm.sub_right (Region.sub_prefix (by decide)))
    · simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Mode.keyR, a0₂, htot, hB]; exact h.stackKey.symm
      · simp only [Mode.keyR, a0₂]; exact h.keyData
  apply WP.seq
  refine WP.mono (Mode.prepare_wp d b₂ (hS.congr wr₂) List.mem_cons_self hk)
    fun s₃ ⟨⟨ready₃, _⟩, b₃, kept₃, f₃, rd₃, wr₃⟩ => ?_
  obtain sv₃ : ∀ i < 4, s₃.mem.readW (slotA (Fb s c) i) 64 = s.gpr (Core.savedRegs.getD i .s1) := by
    intro i hi
    obtain e := h₁.saved i hi
    rw [← m₂] at e
    rw [← e]
    exact f₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by simp only [Impl.Modes.RISCV64.coreSlot]; omega_using [hi])) (by omega_using [hi])
        (by cases d <;> decide)) (by decide)
  obtain data₃ : ∀ b < n, Spec.TripleDes.blockAt s₃.mem (wAt D b) = Spec.TripleDes.blockAt s.mem (wAt D b) := by
    intro b hb
    obtain hsub : Region.Sub ⟨wAt D b, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hb])
    rw [blockAt_eq_of_frame _ f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (sepDF.sub_left hsub).sub_right (Offset.sub_base _ (by cases d <;> decide)),
      m₂, blockAt_eq_of_frame _ h₁.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (sepDF.sub_left hsub).sub_right (Region.sub_prefix (by decide))]
  -- The blocks.
  obtain E : Env (Fb s c) D n s₃.wr :=
    ⟨hS.al, by have := hS.fit; simpa [htot] using this, by rw [wr₃, wr₂]; exact hframeR,
      by rw [wr₃, wr₂]; exact hdataR, fit, sepDF⟩
  obtain p₃ : s₃.gpr .s2 = wAt D 0 := by
    rw [kept₃ _ (by decide), s2₂]; exact (BitVec.add_zero _).symm
  obtain c₃ : s₃.gpr .s3 = BitVec.ofNat 64 (n - 0) := by
    rw [kept₃ _ (by decide), s3₂]; simp [n]
  obtain I0 : EInv k d (Fb s c) D n s₃ 0 s₃ :=
    ⟨by omega_using [], p₃, c₃, b₃, ready₃, fun _ _ _ _ => rfl, rfl, rfl, rfl,
      fun _ _ => rfl, fun b hb => absurd hb (by omega_using []), fun _ _ _ => rfl⟩
  apply WP.seq
  refine WP.mono (loop_ok E hn I0) fun s₄ I => ?_
  -- The registers restored and the frame zeroed.
  obtain sv₄ : ∀ i < 4, s₄.mem.readW (slotA (Fb s c) (Core.savedSlot i)) 64 =
      s.gpr (Core.savedRegs.getD i .s1) := fun i hi => (I.saved i hi).trans (sv₃ i hi)
  obtain hS₄ : ScrIn s₄ (Fb s c) c.total := hS.congr (by rw [I.wr, wr₃, wr₂])
  apply WP.seq
  rw [← List.append_nil Core.restore]
  refine restore_wp hL hS₄ I.b sv₄ fun u g1 g2 g3 g4 g3' g mu rdu wru => WP.block_nil ?_
  refine WP.mono (wipe_wp hL (hS₄.congr wru) g3') fun s' ⟨_, f', g', _, _⟩ => ⟨?_, fun b hb => ?_⟩
  · refine ⟨fun r hr => ?_, rfl, ?_⟩
    · show s'.gpr r = s.gpr r
      obtain h0 : r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 := by revert hr; decide +revert
      rw [g' r h0.1 h0.2.1 h0.2.2.1]
      by_cases e1 : r = .s1
      · subst e1; exact g1
      by_cases e2 : r = .s2
      · subst e2; exact g2
      by_cases e3 : r = .s3
      · subst e3; exact g3
      by_cases e4 : r = .s4
      · subst e4; exact g4
      obtain hk : r ∈ kept := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
      rw [g r e1 e2 e3 e4 h0.2.2.2, I.keep r hk e2 e3, kept₃ r hk, keep₂ r hk e1 e2 e3 e4]
    · show s'.gpr .ra = s.gpr .ra
      rw [g' _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide) (by decide)
        (by decide), I.keep _ (by decide) (by decide) (by decide), kept₃ _ (by decide),
        keep₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · show Spec.TripleDes.blockAt s'.mem (wAt D b) = _
    obtain hsub : Region.Sub ⟨wAt D b, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hb])
    rw [blockAt_eq_of_frame _ f' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (sepDF.sub_left hsub).sub_right (Region.sub_prefix (by cases d <;> decide)),
      mu, I.done b hb, data₃ b hb]

end VG.Proof.TripleDes.RISCV64.Ecb
