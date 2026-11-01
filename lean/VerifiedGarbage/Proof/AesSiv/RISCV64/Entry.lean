module

public import VerifiedGarbage.Proof.AesSiv.RISCV64.Env
public import VerifiedGarbage.Impl.AesSiv.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES-SIV on RISC-V: the arguments, the entry and the exit

Untrusted: everything here is checked by Lean. `encrypt` and `decrypt` are
given their public values in `a0`–`a7` (`Args`). `entry` saves our caller's
registers and the return address at `W + 128` and keeps the arguments in
`s1`–`s5` and `s9`–`s11` (`entry_wp`); `restore` reloads them, `s1`, the
base, last (`exit_wp`). The pieces write only the parts of `W` in `mutR`
and the data, so the slots stay as the entry left them. As on PPC64LE
(`Proof/AesSiv/PPC64LE/Entry.lean`); the entry saves every callee-saved
register, so none is left for the pieces to keep untouched.
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64
open VG.RISCV64 VG.RISCV64.Steps
open VG.RISCV64.Spill (saveCode saveMem Saved saveMem_saved save_ok restoreCode restore_wp)

/-- What `encrypt` and `decrypt` are given: the public values `c`. -/
structure Args (c : Cx) (s : State) : Prop where
  lay : Lay c
  a0 : s.gpr .a0 = c.C
  a1 : s.gpr .a1 = BitVec.ofNat 64 c.R
  a2 : s.gpr .a2 = c.A
  a3 : s.gpr .a3 = BitVec.ofNat 64 c.N
  a4 : s.gpr .a4 = c.D
  a5 : s.gpr .a5 = BitVec.ofNat 64 c.n
  a6 : s.gpr .a6 = c.V
  a7 : s.gpr .a7 = c.W
  perm : Perm c s

/-! ## What the pieces write -/

/-- What the pieces write: the parts of `W` below the slots and above them,
and the data. -/
abbrev mutR (c : Cx) : List Region := [⟨c.W, 128⟩, ⟨c.W + BitVec.ofNat 64 240, 2336⟩, ⟨c.D, c.n⟩]

theorem sub_lo {c : Cx} {d k : Nat} (h : d + k ≤ 128) :
    ∃ r' ∈ mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨c.W, 128⟩, by simp, Offset.sub_base _ h⟩

theorem sub_hi {c : Cx} {d k : Nat} (h₁ : 240 ≤ d) (h₂ : d + k ≤ 2576) :
    ∃ r' ∈ mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ h₁ (by omega)⟩

theorem sub_data {c : Cx} : ∃ r' ∈ mutR c, Region.Sub ⟨c.D, c.n⟩ r' := ⟨_, by simp, fun _ h => h⟩

/-- A buffer missing `W` and the data misses what the pieces write. -/
theorem buf_mut {c : Cx} {P : Addr} {k : Nat} (hw : (⟨P, k⟩ : Region).Disjoint ⟨c.W, 2576⟩)
    (hd : (⟨P, k⟩ : Region).Disjoint ⟨c.D, c.n⟩) : ∀ r ∈ mutR c, (⟨P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hw.sub_right (Region.sub_prefix (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hd

/-! ## The entry -/

/-- What the entry writes: the saved registers and the return address. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 104⟩

/-- The slots of our caller's registers and of the return address, in the
order the entry saves them. -/
abbrev savedL : List (Reg × Nat) := saved ++ [(.ra, raO)]

theorem savedL_bound : ∀ p ∈ savedL, 128 ≤ p.2 ∧ p.2 + 8 ≤ 128 + 104 := by decide

theorem savedL_fits : Spill.Fits savedL := by decide

theorem savedL_off : ∀ p ∈ savedL, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

/-- The slots are kept by what the pieces write. -/
theorem slots_mut {c : Cx} (L : Lay c) : ∀ r ∈ mutR c, (entryR c.W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (Lay.w0_w (c := c) (n := 128) (d := 128) (k := 104) (Nat.le_refl _) (by decide)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm

/-- Our caller's registers, kept in their slots by writes to `mutR`. -/
theorem saved_mut {c : Cx} (L : Lay c) {g : Reg → BitVec 64} {m m' : Mem} (hf : Frame (mutR c) m m')
    (h : Saved c.W g savedL m) : Saved c.W g savedL m' :=
  h.frame_in savedL_bound hf (slots_mut L)

/-- What the entry leaves. -/
structure Entered (c : Cx) (s s₁ : State) : Prop where
  env : Env c s₁
  s4 : s₁.gpr .s4 = c.A
  s5 : s₁.gpr .s5 = BitVec.ofNat 64 c.N
  saved : Saved c.W s.gpr savedL s₁.mem
  frame : Frame [entryR c.W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp

theorem entry_code : entry = saveCode .a7 savedL ++
    ([Impl.AesCbc.RISCV64.mov .s1 .a7, Impl.AesCbc.RISCV64.mov .s2 .a0, Impl.AesCbc.RISCV64.mov .s3 .a1,
      Impl.AesCbc.RISCV64.mov .s4 .a2, Impl.AesCbc.RISCV64.mov .s5 .a3, Impl.AesCbc.RISCV64.mov .s9 .a4,
      Impl.AesCbc.RISCV64.mov .s10 .a5, Impl.AesCbc.RISCV64.mov .s11 .a6] : List Instr) := rfl

theorem entry_wp {c : Cx} {s : State} (Ar : Args c s) : WP isa (.block entry) s (Entered c s) := by
  have L := Ar.lay
  have hww := L.ww
  rw [entry_code]
  refine save_ok (b := .a7) (by rw [Ar.a7]; exact L.wal) savedL_off (fun p hp => by
    rw [Ar.a7]; exact Ar.perm.wW (by have := savedL_bound p hp; omega)) ?_
  rw [Ar.a7]
  generalize hs₀ : ({ s with mem := saveMem s.mem c.W s.gpr savedL } : State) = s₀
  have g₀ : s₀.gpr = s.gpr := by rw [← hs₀]
  have rd₀ : s₀.rd = s.rd := by rw [← hs₀]
  have wr₀ : s₀.wr = s.wr := by rw [← hs₀]
  have sp₀ : s₀.sp = s.sp := by rw [← hs₀]
  have m₀ : s₀.mem = saveMem s.mem c.W s.gpr savedL := by rw [← hs₀]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  have m₈ : s₈.mem = s₀.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₈ : s₈.rd = s.rd := by
    rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rd₀]
  have wr₈ : s₈.wr = s.wr := by
    rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wr₀]
  -- Each move reads an argument register, which no earlier move writes.
  have g : ∀ r, r ∉ [Reg.s1, .s2, .s3, .s4, .s5, .s9, .s10, .s11] → s₈.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h9, h10, h11⟩ := hr
    rw [u₈.other _ h11, u₇.other _ h10, u₆.other _ h9, u₅.other _ h5, u₄.other _ h4, u₃.other _ h3,
      u₂.other _ h2, u₁.other _ h1, g₀]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, Ar.perm.of_eq rd₈ wr₈⟩, ?_, ?_, ?_, ?_, rd₈, wr₈, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, g₀, Ar.a7]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), g₀, Ar.a0]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), g₀, Ar.a1]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      Ar.a4]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      Ar.a5]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      Ar.a6]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀, Ar.a2]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      Ar.a3]
  · rw [m₈, m₀]; exact saveMem_saved savedL_fits _ _ _
  · rw [m₈, m₀]; exact Spill.saveMem_frame savedL_bound (by omega) _ _ _
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, sp₀]

/-! ## The exit -/

/-- The slots `restore` reloads, in its order. -/
abbrev restoreL : List (Reg × Nat) := (.ra, raO) :: saved

theorem restore_code : restore = restoreCode .s1 restoreL := rfl

theorem restoreL_sub : ∀ p ∈ restoreL, p ∈ savedL := by decide

theorem preserved_restored : ∀ r ∈ preserved, r ∈ restoreL.map Prod.fst := by decide

/-- `restore`: our caller's registers and return address back, for `s₀` the
state at the entry. -/
theorem exit_wp {c : Cx} (L : Lay c) {s₀ s : State} (E : Env c s) (sv : Saved c.W s₀.gpr savedL s.mem)
    (hsp : s.sp = s₀.sp) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .a0 = s.gpr .a0 := by
  rw [restore_code]
  refine WP.mono (restore_wp (b := .s1) (B := c.W) L.wal E.s1 (by decide) (by decide) (fun p hp => by
      have := savedL_bound p (restoreL_sub p hp)
      exact E.perm.wR (by omega)) (sv.sub restoreL_sub)) fun s' R => ?_
  refine ⟨⟨fun r hr => ?_, by rw [R.sp, hsp], R.gpr (.ra, raO) List.mem_cons_self⟩, R.mem,
    R.other _ (by decide)⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (preserved_restored r hr)
  exact R.gpr p hp

end VG.Proof.AesSiv.RISCV64
