module

import VerifiedGarbage.Proof.TripleDes.RISCV64.ModeCore
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.TripleDes.RISCV64.BlockOk
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Ecb
public import VerifiedGarbage.Proof.Modes.RISCV64.Core
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Block

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
  have hsub : Region.Sub ⟨wAt D j, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
  have hpre : BlockPre k .s2 0 u := by
    refine ⟨by decide, by decide, by rw [I.b]; have := E.al; omega, fun o ho => ?_,
      by rw [I.b]; exact I.keys, ?_, ?_⟩
    · rw [I.wr, I.b]; exact ⟨_, E.frame, Offset.contains_base _ (by omega) (by have := E.fit; omega)⟩
    · rw [I.wr, I.ptr, BitVec.add_zero]
      exact ⟨_, E.data, Offset.contains_base D (by omega) (by omega)⟩
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
        (Offset.sub_base B (d := 8 * i) (n := 8) (k := 944) (by omega))).symm
    · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, fun r hr h2 h3 => ?_, ?_, ?_, ?_, fun i hi => ?_,
    fun b hb => ?_, fun b h1 h2 => ?_⟩, ?_⟩
  · rw [h₃.other _ (by decide), h₂.gpr, ptr₁]
    show D + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 = D + BitVec.ofNat 64 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat, show 8 * j + 8 = 8 * (j + 1) by omega]
  · rw [h₃.gpr, h₂.other _ (by decide), h₁.regs .s3 (by decide), I.cnt]
    apply BitVec.eq_of_toNat_eq; simp; omega
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
      rw [hr, I.rest b (by omega) hj]
    · rw [blockAt_eq_of_frame _ hfr (frameOut (Offset.sub_base D (by omega))
        (Offset.disjoint D (by omega) (by omega) (by omega)))]
      exact I.done b (by omega)
  · rw [m₃, blockAt_eq_of_frame _ hfr (frameOut (Offset.sub_base D (by omega))
      (Offset.disjoint D (by omega) (by omega) (by omega)))]
    exact I.rest b (by omega) h2
  · rw [h₃.gpr, h₂.other _ (by decide), h₁.regs .s3 (by decide), I.cnt]
    apply BitVec.eq_of_toNat_eq; simp; omega

theorem loop_ok {k : Schedule} {d : Direction} {B D : Addr} {n : Nat} {s₀ : State}
    (E : Env B D n s₀.wr) (hn : 0 < n) (I : EInv k d B D n s₀ 0 s₀) :
    WP isa (.loop (.seq (block d .s2 0) (.block advance)) (.nonzero .s3)) s₀
      (EInv k d B D n s₀ n) := by
  refine WP.loop (M := isa) (Q := EInv k d B D n s₀ n)
    (fun m v => ∃ j, j < n ∧ m = n - j ∧ EInv k d B D n s₀ j v) ?_ n s₀ ⟨0, hn, rfl, I⟩
  intro m v ⟨j, hj, hm, J⟩
  refine WP.mono (step_ok E hj J) fun v' ⟨J', hz⟩ => ?_
  have hn64 : n < 2 ^ 64 := by have := E.dataFit; omega
  rw [eval_nonzero, hz, ofNat_bne_zero' (by omega)]
  by_cases e : j + 1 = n
  · left
    exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp; omega, n - (j + 1), by omega, j + 1, by omega, rfl, J'⟩

end VG.Proof.TripleDes.RISCV64.Ecb
