module

public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.RISCV64
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Lit
public import VerifiedGarbage.Proof.TripleDes.RISCV64.FeistelLit
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Key.Verified
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.TripleDes.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.RISCV64.BigFrame
public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModeCore
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Ecb
public import VerifiedGarbage.Proof.Modes.RISCV64.Core
meta import VerifiedGarbage.Proof.Modes.RISCV64.Seq
meta import VerifiedGarbage.Proof.TripleDes.Bytes
meta import VerifiedGarbage.Proof.TripleDes.Schedule
meta import VerifiedGarbage.Proof.Framework.RISCV64.BigFrame
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.ModeCore
meta import VerifiedGarbage.Proof.Framework.RISCV64.Loops
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Modes.RISCV64.Core

/-! ### `CmacTripleDes.Stream.RISCV64.Calls`, which this module and modules that import it used -/

section

/-! ### `TripleDes.RISCV64.EcbVerified`, which only this module used -/

section

/-! ### `TripleDes.RISCV64.Ecb`, which only this module used -/

section

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
  refine WP.mono (wipe_wp hL (hS₄.congr wru) g3') fun s' ⟨_, f', g', _, _⟩ mL _ fl => ⟨?_, fun b hb => ?_⟩
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
  · show Spec.TripleDes.blockAt mL (wAt D b) = _
    obtain hsub : Region.Sub ⟨wAt D b, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hb])
    -- The `free` loses the frame's bytes, which lie apart from the data.
    have fl' : Frame [⟨Fb s c, 944⟩] s'.mem mL := by
      have e : 8 * c.total = 944 := by rw [htot]
      rw [← e]; exact fl
    rw [blockAt_eq_of_frame _ fl' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sepDF.sub_left hsub,
      blockAt_eq_of_frame _ f' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (sepDF.sub_left hsub).sub_right (Region.sub_prefix (by cases d <;> decide)),
      mu, I.done b hb, data₃ b hb]

end VG.Proof.TripleDes.RISCV64.Ecb

end

end

/-!
# Serial Triple DES ECB encryption on RISC-V meets its contract

`ecbC` states the frame of 944 bytes below the stack pointer. Streaming
TDEA-CMAC calls this code on one block at a time
(`vg_triple_des_ecb_encrypt_serial`), by `ecb_ok` and `encrypt_ct`; the
artifacts `vg_triple_des_ecb_encrypt` and `_decrypt` are bitsliced
(`Bitsliced/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Ecb

open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64
open VG.Spec.TripleDes (Direction)

/-- The ECB contract as the code sees it. -/
def ecbC (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 384⟩
    let data : Region := ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
    let stack : Region := ⟨s.sp - 944, 944⟩
    s.rd = [key] ∧ s.wr = [data] ∧ key.Disjoint data ∧
      (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ 944 ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint data
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .a0)) d
        (Spec.TripleDes.blocksAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

theorem ecb_blocks (K : Spec.TripleDes.Schedule) (d : Direction) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, Spec.TripleDes.blockAt m' (wAt D b) = blockResult K d (Spec.TripleDes.blockAt m (wAt D b))) :
    Spec.TripleDes.blocksAt m' D n = Spec.TripleDes.ecb K d (Spec.TripleDes.blocksAt m D n) := by
  simp only [Spec.TripleDes.blocksAt, Spec.TripleDes.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases d <;> rfl

theorem ecb_ok (d : Direction) (s : State) (hs : (ecbC d).pre s) :
    ∃ t s', Exec isa (Ecb.ecb d) s t s' ∧ abiPreserved s s' ∧ (ecbC d).post s s' := by
  obtain ⟨rd, wr, kd, fit, al, sp, sk, sd⟩ := hs
  obtain ⟨t, s', he, hp, hb⟩ := ecb_wp d ⟨rd, wr, kd, fit, al, sp, sk, sd⟩
  exact ⟨t, s', he, hp, ecb_blocks _ _ _ _ _ _ hb⟩

theorem ecb_agree (d : Direction) : ∀ s₁ s₂, (ecbC d).pre s₁ → (ecbC d).pre s₂ → (ecbC d).pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

theorem encrypt_ct : ConstantTime isa (ecbC .encrypt).pre (ecbC .encrypt).pub Ecb.encrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) (ecb_agree .encrypt)
    (by taint_decide)

end VG.Proof.TripleDes.RISCV64.Ecb

end

end

/-!
# Streaming TDEA-CMAC on RISC-V: the calls

The calls of the verified key expansion (`keyCall`, by `Key.contract`,
with `WP.call`: it uses no stack) and serial ECB encryption (`ecbCall`, of
`vg_triple_des_ecb_encrypt_serial`, by `Ecb.ecbC`, with `WP.callAny`: it
uses the 944 bytes below the stack pointer, `ecb_sdepth`), as the streaming functions make them: the key
expansion writes the schedule at the start of the state `S`, and ECB
enciphers the block at `S + off` in place, a block of the state past the
schedule, with the state as the schedule. What each needs (`KArgs`,
`EArgs`), what it leaves (`KPost`, `EPost`, in terms of the memory before
the call), and that two calls with the same arguments leak the same
(`key_rel`, `ecb_rel`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64

theorem expandKey_noFrames : Impl.TripleDes.RISCV64.Key.expandKey.noFrames = true := by lit_decide

/-- ECB's frame uses the 944 bytes of stack its contract reserves. -/
theorem ecb_sdepth : sdepth (Impl.TripleDes.RISCV64.Ecb.ecb .encrypt) = 944 := by decide +kernel

theorem toNat_add_lt (p : Addr) {d k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d < k) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h, hd] : d < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega_using [h, hd])

/-! ## The key expansion -/

/-- What the key expansion's call needs: the key at `K`, of `KL` bytes, and
the state at `S`. -/
structure KArgs (s : State) (K S : Addr) (KL : Nat) : Prop where
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = BitVec.ofNat 64 KL
  a2 : s.gpr .a2 = S
  valid : Spec.TripleDes.validKey KL
  ks : (⟨K, KL⟩ : Region).Disjoint ⟨S, 416⟩
  reads : (⟨K, KL⟩ : Region) ∈ s.rd
  writes : (⟨S, 416⟩ : Region) ∈ s.wr

/-- What the key expansion's call leaves. -/
structure KPost (s : State) (K S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨S, 384⟩] s.mem s'.mem
  out : Spec.TripleDes.scheduleAt s'.mem S =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem K KL)

theorem KArgs.toNat {s : State} {K S : Addr} {KL : Nat} (h : KArgs s K S KL) :
    (BitVec.ofNat 64 KL).toNat = KL := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.valid with h | h <;> omega_using [h])

theorem KArgs.pre {s : State} {K S : Addr} {KL : Nat} (h : KArgs s K S KL) :
    Proof.TripleDes.RISCV64.Key.contract.pre (s.callEntry.withRegions [⟨K, KL⟩] [⟨S, 384⟩]) := by
  simp only [Proof.TripleDes.RISCV64.Key.contract, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.toNat]
  exact ⟨trivial, trivial, h.ks.sub_right (Region.sub_prefix (by decide)), h.valid⟩

theorem KArgs.covers {s : State} {K S : Addr} {KL : Nat} (h : KArgs s K S KL) :
    Covers ([⟨K, KL⟩] ++ [⟨S, 384⟩]) (s.rd ++ s.wr) ∧ Covers [⟨S, 384⟩] s.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_append_left _ h.reads, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ h.writes, 0, by simp, by show 0 + 384 ≤ 416; decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, h.writes, 0, by simp, by show 0 + 384 ≤ 416; decide⟩

theorem key_call {s : State} {K S : Addr} {KL : Nat} (h : KArgs s K S KL) :
    WP isa Impl.CmacTripleDes.Stream.RISCV64.keyCall s (KPost s K S KL) := by
  refine WP.call (k := Proof.TripleDes.RISCV64.Key.contract)
    (Proof.TripleDes.RISCV64.Key.correct (by lit_decide) (by lit_decide)) h.pre h.covers.1 h.covers.2 ?_
    expandKey_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.TripleDes.RISCV64.Key.contract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.toNat] at hpost
  exact hpost

theorem key_rel {K S : Addr} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → KArgs s₁ K S KL ∧ KArgs s₂ K S KL ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacTripleDes.Stream.RISCV64.keyCall fun _ _ => True := by
  refine RelCT.call (Proof.TripleDes.RISCV64.Key.correct (by lit_decide) (by lit_decide))
    Proof.TripleDes.RISCV64.Key.constantTime [⟨K, KL⟩] [⟨S, 384⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.covers.1, h₁.covers.2, h₂.covers.1, h₂.covers.2⟩
  simp only [Proof.TripleDes.RISCV64.Key.contract, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₂.a0, h₂.a1, h₂.a2, hsp]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-! ## ECB on one block of the state -/

/-- What ECB's call on the block at `S + off` of the state `S` needs. -/
structure EArgs (s : State) (S : Addr) (off : Nat) : Prop where
  a0 : s.gpr .a0 = S
  a1 : s.gpr .a1 = S + BitVec.ofNat 64 off
  a2 : s.gpr .a2 = BitVec.ofInt 64 1
  lo : 384 ≤ off
  hi : off + 8 ≤ 416
  fit : S.toNat + 416 ≤ 2 ^ 64
  al : s.sp.toNat % 16 = 0
  sp : 944 ≤ s.sp.toNat
  stk : (⟨s.sp - 944, 944⟩ : Region).Disjoint ⟨S, 416⟩
  writes : (⟨S, 416⟩ : Region) ∈ s.wr

/-- What ECB's call leaves. -/
structure EPost (s : State) (S : Addr) (off : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨S + BitVec.ofNat 64 off, 8⟩, ⟨s.sp - 944, 944⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (S + BitVec.ofNat 64 off) 8 =
    Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt s.mem S) (Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 off) 8)

theorem EArgs.pre {s : State} {S : Addr} {off : Nat} (h : EArgs s S off) :
    (Proof.TripleDes.RISCV64.Ecb.ecbC .encrypt).pre
      (s.callEntry.withRegions [⟨S, 384⟩] [⟨S + BitVec.ofNat 64 off, 8⟩]) := by
  have hl := h.lo
  have hh := h.hi
  have hf := h.fit
  simp only [Proof.TripleDes.RISCV64.Ecb.ecbC, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    h.a0, h.a1, h.a2, show (BitVec.ofInt 64 1).toNat = 1 from rfl, Nat.mul_one]
  refine ⟨trivial, trivial, Offset.base_disjoint _ (by omega_using [hl]) (by omega_using [hh]), ?_, h.al, h.sp,
    h.stk.sub_right (Region.sub_prefix (by decide)), h.stk.sub_right (Offset.sub_base _ (by omega_using [hh]))⟩
  rw [toNat_add_lt S hf (show off < 416 by omega_using [hh])]; omega_using [hh, hf]

theorem EArgs.covers {s : State} {S : Addr} {off : Nat} (h : EArgs s S off) :
    Covers ([⟨S, 384⟩] ++ [⟨S + BitVec.ofNat 64 off, 8⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨S + BitVec.ofNat 64 off, 8⟩] s.wr := by
  have hh := h.hi
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_append_right _ h.writes, 0, by simp, by show 0 + 384 ≤ 416; decide⟩
    · exact ⟨_, List.mem_append_right _ h.writes, off, rfl, by show off + 8 ≤ 416; omega_using [hh]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, h.writes, off, rfl, by show off + 8 ≤ 416; omega_using [hh]⟩

theorem ecb_call {s : State} {S : Addr} {off : Nat} (h : EArgs s S off) :
    WP isa Impl.CmacTripleDes.Stream.RISCV64.ecbCall s (EPost s S off) := by
  refine WP.callAny (k := Proof.TripleDes.RISCV64.Ecb.ecbC .encrypt) (Proof.TripleDes.RISCV64.Ecb.ecb_ok .encrypt)
    h.pre h.covers.1 h.covers.2 ?_ (by rw [ecb_sdepth]; decide)
  intro s' hrd hwr hsp hf hsaved hpost
  rw [ecb_sdepth] at hf
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.TripleDes.RISCV64.Ecb.ecbC, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    h.a0, h.a1, h.a2, show (BitVec.ofInt 64 1).toNat = 1 from rfl] at hpost
  simp only [Spec.TripleDes.blocksAt, List.range_one, List.map_cons, List.map_nil, Spec.TripleDes.ecb,
    Nat.mul_zero, BitVec.add_zero, List.cons.injEq, and_true] at hpost
  rw [Proof.TripleDes.bytesAt_eq, Proof.TripleDes.bytesAt_eq, hpost]
  rw [Spec.Cmac.tdesWith, ← Proof.TripleDes.bytesAt_eq, Proof.TripleDes.ofFn_bytesAt]

theorem ecb_rel {S : Addr} {off : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → EArgs s₁ S off ∧ EArgs s₂ S off ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacTripleDes.Stream.RISCV64.ecbCall fun _ _ => True := by
  refine RelCT.call (Proof.TripleDes.RISCV64.Ecb.ecb_ok .encrypt) Proof.TripleDes.RISCV64.Ecb.encrypt_ct
    [⟨S, 384⟩] [⟨S + BitVec.ofNat 64 off, 8⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.covers.1, h₁.covers.2, h₂.covers.1, h₂.covers.2⟩
  simp only [Proof.TripleDes.RISCV64.Ecb.ecbC, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₂.a0, h₂.a1, h₂.a2, hsp]
  exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacTripleDes.Stream.RISCV64

end

end

/-!
# Streaming TDEA-CMAC on RISC-V: the contracts and what the functions share

The contracts the code is proved against (`initRISCV64`, `absorbRISCV64`,
`finishRISCV64`), which the shared contracts with the working space
appended (`Proof/CmacTripleDes/StreamScratch.lean`, with the 944 bytes of
stack ECB uses) imply (`Verified.lean`). Then where the registers are saved
(`sv S`, the scratch buffer rounded up to a multiple of 8), the number of
bytes held back as `heldCode` computes it from `count` (`heldCode_wp`), and
`copy`, which copies `cnt` bytes from `src` to `dst`, a byte at a time
(none if `cnt` is 0), changing only `tmp`, `src`, `dst` and `cnt`
(`copy_ok`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64

/-! ## The contracts -/

/-- `vg_cmac_triple_des_stream_init(state = a0, key = a1, key_len = a2, scratch = a3)`. -/
def initRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 416⟩
    let key : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let scr : Region := ⟨s.gpr .a3, 640⟩
    let stk : Region := ⟨s.sp - 944, 944⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      stk.Disjoint state ∧ stk.Disjoint key ∧ stk.Disjoint scr ∧
      (s.gpr .a0).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 640 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧ 944 ≤ s.sp.toNat ∧
      Spec.TripleDes.validKey (s.gpr .a2).toNat
  post s s' :=
    Spec.Cmac.tdesRepr s'.mem (s.gpr .a0) (Spec.TripleDes.bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat) []
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_triple_des_absorb(state = a0, count = a1, data = a2, len = a3, scratch = a4)`. -/
def absorbRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 416⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let scr : Region := ⟨s.gpr .a4, 688⟩
    let stk : Region := ⟨s.sp - 944, 944⟩
    s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      stk.Disjoint state ∧ stk.Disjoint data ∧ stk.Disjoint scr ∧
      (s.gpr .a0).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + 688 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧ 944 ≤ s.sp.toNat
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (s.gpr .a0) key msg →
      s.gpr .a1 = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .a3).toNat < 2 ^ 64 →
      Spec.Cmac.tdesRepr s'.mem (s.gpr .a0) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_triple_des_finish(state = a0, count = a1, out = a2, scratch = a3)`. -/
def finishRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 416⟩
    let out : Region := ⟨s.gpr .a2, 8⟩
    let scr : Region := ⟨s.gpr .a3, 640⟩
    let stk : Region := ⟨s.sp - 944, 944⟩
    s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      stk.Disjoint state ∧ stk.Disjoint out ∧ stk.Disjoint scr ∧
      (s.gpr .a0).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 640 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧ 944 ≤ s.sp.toNat
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (s.gpr .a0) key msg →
      s.gpr .a1 = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .a2) 8 = Spec.Cmac.tdesCmac key 8 msg
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-! ## Arithmetic -/

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ x.isLt)])

theorem and7 (x : BitVec 64) : (x &&& BitVec.ofInt 64 7).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 7).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

open VG.Proof.CmacTripleDes.Stream (held held_pos) in
/-- The number of bytes held back for a nonzero `count`, as `addi -1; andi 7; addi 1` computes it. -/
theorem held_bv (c : BitVec 64) (h : c ≠ 0) :
    ((c - BitVec.ofNat 64 1) &&& BitVec.ofInt 64 7) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (held c.toNat) := by
  have hc : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [held_pos (by omega_using [hc])]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and7, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  have := c.isLt
  omega_using [hc]

theorem preserved_ne (r : Reg) (hr : r ∈ preserved) :
    r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 ∧ r ≠ .t5 ∧ r ≠ .t6 ∧ r ≠ .ra ∧ r ≠ .a0 ∧
      r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 ∧ r ≠ .a6 ∧ r ≠ .a7 := by
  revert hr; cases r <;> decide

/-- Code keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.sp he⟩

theorem in_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## The number of bytes held back -/

open VG.Proof.CmacTripleDes.Stream (held) in
/-- `heldCode` computes, from `count = n` in `a1`, the number of bytes held
back for a message of `n` bytes, to `t0`. -/
theorem heldCode_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h1 : s.gpr .a1 = BitVec.ofNat 64 n) :
    WP isa heldCode s fun t => t.gpr .t0 = BitVec.ofNat 64 (held n) ∧
      (∀ r, r ≠ .t0 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have ev := Steps.eval_zero_ofNat s .a1 hn h1
  by_cases h0 : n = 0
  · subst h0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine wp_li (imm := 0) (by decide) fun t u => WP.block_nil ?_
    exact ⟨by rw [u.gpr]; rfl, fun r h => u.other r h, u.mem, u.rd, u.wr, u.sp⟩
  refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
  refine wp_subi (imm := 1) (by decide) fun t₁ u₁ => wp_andi (by decide) fun t₂ u₂ =>
    wp_addi (imm := 1) (by decide) fun t₃ u₃ => WP.block_nil ?_
  refine ⟨?_, fun r h => by rw [u₃.other r h, u₂.other r h, u₁.other r h], by rw [u₃.mem, u₂.mem, u₁.mem],
    by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp]⟩
  have hc : s.gpr .a1 ≠ 0 := by
    rw [h1]; intro e; apply h0; have := congrArg BitVec.toNat e; rwa [toNat_ofNat hn] at this
  rw [u₃.gpr, u₂.gpr, u₁.gpr, held_bv _ hc, h1, toNat_ofNat hn]

/-! ## Saving registers -/

/-- Where the functions save the registers, from the scratch buffer `S`: `S`
rounded up to a multiple of 8. -/
abbrev sv (S : Addr) : Addr := S + BitVec.ofNat 64 (Align.pad S)

/-- `t0 :=` the register `n`'s value rounded up. -/
theorem savePtr_ok {s : State} (n : Reg) :
    WP isa (.block (savePtr n)) s (· = s.write .t0 (sv (s.gpr n))) := by
  apply WP.of_runBlock
  simp only [savePtr, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 7 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write, Option.some.injEq,
    exists_eq_left']
  rw [Align.align_eq]

theorem sv_add (S : Addr) (d : Nat) : sv S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 (Align.pad S + d) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- A slot at `sv S + d`, within the scratch buffer's first 56 bytes. -/
theorem sv_sub (S : Addr) {d n : Nat} (h : d + n ≤ 49) : Region.Sub ⟨sv S + BitVec.ofNat 64 d, n⟩ ⟨S, 56⟩ := by
  have := Align.pad_lt S
  rw [sv_add]; exact Offset.sub_base _ (by omega_using [h, this])

theorem sv_contains (S : Addr) {d n L : Nat} (h : d + n ≤ 49) (hL : 56 ≤ L) :
    (⟨S, L⟩ : Region).Contains (sv S + BitVec.ofNat 64 d) n := by
  have := Align.pad_lt S
  rw [sv_add]; exact Offset.contains_base _ (by omega_using [h, hL, this]) (by omega_using [h, this])

/-! ## Copying bytes -/

open VG.WriteBytes

/-- What `copy` leaves: the bytes copied, and every register but the
copy's. -/
structure Copied (tmp src dst cnt : Reg) (s : State) (C : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem C xs
  other : ∀ r, r ≠ tmp → r ≠ src → r ≠ dst → r ≠ cnt → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- Memory after writing the bytes copied, pointwise, as `writeBytes`. -/
theorem writeBytes_of {m m' : Mem} {C : Addr} {xs : List Byte}
    (hc : ∀ i < xs.length, m' (C + BitVec.ofNat 64 i) = xs.getD i 0) (hf : Frame [⟨C, xs.length⟩] m m') :
    m' = writeBytes m C xs := by
  funext a
  simp only [writeBytes]
  split
  · rename_i h
    have := hc _ h
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at this
  · rename_i h
    exact hf a fun r hr hc' => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains] at hc'; omega_using [h, hc']

theorem copy_ok {tmp src dst cnt : Reg} (h1 : tmp ≠ src) (h2 : tmp ≠ dst) (h3 : tmp ≠ cnt)
    (h4 : src ≠ dst) (h5 : src ≠ cnt) (h6 : dst ≠ cnt) (s : State) {P C : Addr} {L : Nat} (hL : L < 2 ^ 64)
    (hs : s.gpr src = P) (hd : s.gpr dst = C) (hc : s.gpr cnt = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, L⟩) :
    WP isa (copy tmp src dst cnt) s (Copied tmp src dst cnt s C (Spec.Aes.bytesAt s.mem P L)) := by
  have ev := Steps.eval_zero_ofNat s cnt hL hc
  by_cases hL0 : L = 0
  · subst hL0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
  refine WP.mono (copyLoop_ok h1 h2 h3 h4 h5 h6 s (N := L) (by omega_using [hL0]) hL hc (by rw [hs]; exact hr)
    (by rw [hd]; exact hw) (fun x hx₁ hx₂ => ?_)) ?_
  · rw [hd] at hx₁; rw [hs] at hx₂
    exact hdis x (by simp only [Region.Contains]; omega_using [hx₂]) (by simp only [Region.Contains]; omega_using [hx₁])
  rintro t ⟨hcp, hf, hk⟩
  rw [hd, hs] at hcp
  rw [hd] at hf
  refine ⟨writeBytes_of (fun i hi => ?_) (by rw [Proof.Cmac.bytesAt_length]; exact hf),
    fun r a b c d => hk.gpr (by simp [a, b, c, d]), hk.2.1, hk.2.2⟩
  rw [Proof.Cmac.bytesAt_length] at hi
  rw [hcp i hi, Proof.Cmac.getD_bytesAt _ _ hi]

/-! ## Zeroing a block -/

/-- The 8 bytes `storeBytes` stores of zeros, at `C`. -/
theorem zeros_stored {s s' : State} {tmp dst : Reg} {doff : Nat} {C : Addr} (hC : s.gpr dst + BitVec.ofNat 64 doff = C)
    (h : Bytes.StoreI tmp dst doff (List.replicate 8 0) s 8 s') :
    Spec.Aes.bytesAt s'.mem C 8 = Spec.Cmac.zeros 8 ∧ Frame [⟨C, 8⟩] s.mem s'.mem := by
  refine ⟨?_, by have := h.frame; rwa [hC, List.length_replicate] at this⟩
  simp only [Spec.Aes.bytesAt, Spec.Cmac.zeros]
  apply List.ext_getElem (by simp)
  intro j h₁ _
  simp only [List.length_map, List.length_range] at h₁
  have := h.stored j h₁
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  rw [← hC, Offset.add_add, this]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, show j < 8 from h₁, ↓reduceIte,
    Option.getD_some]
  rfl


/-! ## Bytes written and read -/

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega_arith : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, bytesAt_writeBytes_self _ _ (by omega_using [h])]
  refine congrArg (· ++ xs) ?_
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega_using [h])

/-- The bytes past the first `a`. -/
theorem bytesAt_drop (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    (Spec.Aes.bytesAt m p n).drop a = Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) (n - a) := by
  conv => lhs; rw [show n = a + (n - a) by omega_using [h], Proof.Cmac.Stream.bytesAt_append]
  rw [List.drop_append_of_le_length (by simp [Spec.Aes.bytesAt]), List.drop_of_length_le (by simp [Spec.Aes.bytesAt]),
    List.nil_append]

/-- The first `b` bytes past the first `a`. -/
theorem bytesAt_drop_take (m : Mem) (p : Addr) {a b n : Nat} (h : a + b ≤ n) :
    ((Spec.Aes.bytesAt m p n).drop a).take b = Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b := by
  rw [bytesAt_drop m p (by omega_using [h]), show n - a = b + (n - a - b) by omega_using [h], Proof.Cmac.Stream.bytesAt_append,
    List.take_append_of_le_length (by simp [Spec.Aes.bytesAt]), List.take_of_length_le (by simp [Spec.Aes.bytesAt])]

/-- The first `a` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    (Spec.Aes.bytesAt m p n).take a = Spec.Aes.bytesAt m p a := by
  have := bytesAt_drop_take m p (a := 0) (b := a) (n := n) (by omega_using [h])
  rwa [List.drop_zero, BitVec.add_zero] at this

theorem blocksAt_succ (m : Mem) (p : Addr) (k : Nat) :
    Spec.Cmac.blocksAt m p 8 (k + 1) =
      Spec.Cmac.blocksAt m p 8 k ++ [Spec.Aes.bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8] := by
  simp only [Spec.Cmac.blocksAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

end VG.Proof.CmacTripleDes.Stream.RISCV64
