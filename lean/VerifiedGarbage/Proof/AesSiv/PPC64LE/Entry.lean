module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Env
public import VerifiedGarbage.Impl.AesSiv.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES-SIV on PPC64LE: the arguments, the entry and the exit

Untrusted: everything here is checked by Lean. `encrypt` and `decrypt` are
given their public values in `r3`–`r10` (`Args`). `entry` saves our
caller's registers and the return address at `W + 128` and keeps the
arguments in `r14`–`r18` and `r22`–`r24` (`entry_wp`); `restore` reloads
them (`exit_wp`). The pieces write only the parts of `W` in `mutR` and the
data, so the slots stay as the entry left them.
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.Impl.AesSiv.PPC64LE
open VG.PPC64LE
open VG.PPC64LE.Spill (saveCode saveMem Saved saveMem_saved save_ok restoreCode restore_wp)
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_ld wp_std wp_mflr wp_mtlr)
open VG.Proof.AesCcm.PPC64LE (wp_mv)

/-- What `encrypt` and `decrypt` are given: the public values `c`. -/
structure Args (c : Cx) (s : State) : Prop where
  lay : Lay c
  r3 : s.gpr .r3 = c.C
  r4 : s.gpr .r4 = BitVec.ofNat 64 c.R
  r5 : s.gpr .r5 = c.A
  r6 : s.gpr .r6 = BitVec.ofNat 64 c.N
  r7 : s.gpr .r7 = c.D
  r8 : s.gpr .r8 = BitVec.ofNat 64 c.n
  r9 : s.gpr .r9 = c.V
  r10 : s.gpr .r10 = c.W
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

/-- Our caller's registers, with the return address in `r0`'s place. -/
abbrev saveG (s : State) : Reg → BitVec 64 := (s.write .r0 s.lr).gpr

/-- The slots of our caller's registers and the return address. -/
abbrev savedL : List (Reg × Nat) := (.r0, lrO) :: saved

/-- Our caller's registers the entry does not save, since nothing writes them. -/
abbrev otherRegs : List Reg := [.r2, .r26, .r27, .r28, .r29, .r30, .r31]

theorem other_keep : ∀ r ∈ otherRegs, r ∈ keepRegs := by decide

theorem saved_bound : ∀ p ∈ saved, 128 ≤ p.2 ∧ p.2 + 8 ≤ 128 + 96 := by decide

theorem savedL_bound : ∀ p ∈ savedL, 128 ≤ p.2 ∧ p.2 + 8 ≤ 128 + 104 := by decide

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
  r17 : s₁.gpr .r17 = c.A
  r18 : s₁.gpr .r18 = BitVec.ofNat 64 c.N
  saved : Saved c.W (saveG s) savedL s₁.mem
  frame : Frame [entryR c.W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp
  lr : s₁.lr = s.lr
  others : ∀ r ∈ otherRegs, s₁.gpr r = s.gpr r

theorem entry_wp {c : Cx} {s : State} (Ar : Args c s) : WP isa (.block entry) s (Entered c s) := by
  have L := Ar.lay
  have hww := L.ww
  unfold entry
  change WP isa (.block ([.mflr .r0] ++ saveCode .r10 saved ++ _)) s _
  simp only [List.cons_append, List.nil_append]
  refine wp_mflr fun s₃ u₃ => ?_
  have W₃ : s₃.gpr .r10 = c.W := by rw [u₃.other _ (by decide), Ar.r10]
  have rd₃ : s₃.rd = s.rd := u₃.rd
  have wr₃ : s₃.wr = s.wr := u₃.wr
  refine save_ok (b := .r10) (by decide) (by decide) (fun p hp => by
    rw [W₃, wr₃]; exact Ar.perm.wW (by have := saved_bound p hp; omega)) ?_
  rw [W₃]
  generalize hmS : saveMem s₃.mem c.W s₃.gpr saved = mS
  have m₃ : s₃.mem = s.mem := u₃.mem
  have fS : Frame [⟨c.W + BitVec.ofNat 64 128, 96⟩] s.mem mS := by
    rw [← hmS, m₃]; exact Spill.saveMem_frame saved_bound (by omega) _ _ _
  have svS : Saved c.W s₃.gpr saved mS := by rw [← hmS]; exact saveMem_saved (by decide) _ _ _
  refine wp_std (a := c.W + BitVec.ofNat 64 224) (by decide) (by decide) (by show s₃.gpr .r10 + _ = _; rw [W₃]; rfl)
    (by show InRegions s₃.wr _ 8; rw [wr₃]; exact Ar.perm.wW (by decide)) fun s₅ u₅ => ?_
  refine wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => wp_mv fun s₉ u₉ => wp_mv fun s₁₀ u₁₀ =>
    wp_mv fun s₁₁ u₁₁ => wp_mv fun s₁₂ u₁₂ => wp_mv fun s₁₃ u₁₃ => WP.block_nil ?_
  have m₁₃ : s₁₃.mem = mS.writeW (c.W + BitVec.ofNat 64 224) s.lr := by
    rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
    show mS.writeW _ (s₃.gpr .r0) = _; rw [u₃.gpr]
  have c224 : (entryR c.W).Contains (c.W + BitVec.ofNat 64 224) (64 / 8) :=
    Offset.contains c.W (by decide) (by decide) (by decide)
  have f₁₃ : Frame [entryR c.W] s.mem s₁₃.mem := by
    rw [m₁₃]
    exact (fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩).writeW (List.mem_singleton_self _) _ c224
  have g₅ : ∀ r, r ≠ .r0 → s₅.gpr r = s.gpr r := fun r h0 => by
    rw [u₅.gpr]; show s₃.gpr r = _; rw [u₃.other _ h0]
  have gF : ∀ r, r ∉ [Reg.r14, .r15, .r16, .r17, .r18, .r22, .r23, .r24] → s₁₃.gpr r = s₅.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h14, h15, h16, h17, h18, h22, h23, h24⟩ := hr
    rw [u₁₃.other _ h24, u₁₂.other _ h23, u₁₁.other _ h22, u₁₀.other _ h18, u₉.other _ h17, u₈.other _ h16,
      u₇.other _ h15, u₆.other _ h14]
  have rd₁₃ : s₁₃.rd = s.rd := by
    rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd]; exact rd₃
  have wr₁₃ : s₁₃.wr = s.wr := by
    rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr]; exact wr₃
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, Ar.perm.of_eq rd₁₃ wr₁₃⟩, ?_, ?_, ?_, f₁₃, rd₁₃, wr₁₃, ?_, ?_, ?_⟩
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅ .r10 (by decide), Ar.r10]
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅ .r3 (by decide), Ar.r3]
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅ .r4 (by decide), Ar.r4]
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅ .r7 (by decide), Ar.r7]
  · rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅ .r8 (by decide), Ar.r8]
  · rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅ .r9 (by decide), Ar.r9]
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), g₅ .r5 (by decide), Ar.r5]
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr,
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅ .r6 (by decide), Ar.r6]
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · show s₁₃.mem.readW (c.W + BitVec.ofNat 64 224) 64 = _
      rw [m₁₃, Mem.readW_writeW_self64]
      simp [saveG, State.write]
    · have hv : mS.readW (c.W + BitVec.ofNat 64 p.2) 64 = s₃.gpr p.1 := svS p hp
      have d224 : Mem.Sep (c.W + BitVec.ofNat 64 p.2) (64 / 8) (c.W + BitVec.ofNat 64 224) (64 / 8) := by
        have := saved_bound p hp
        exact (L.w_w (n := 8) (k := 8) (.inl (by omega)) (by omega) (by decide)).sep (Region.contains_self _ _)
          (Region.contains_self _ _)
      rw [m₁₃, Mem.readW_writeW_sep d224 (by decide), hv]
      have h1 : p.1 ≠ .r0 := (show ∀ q ∈ saved, q.1 ≠ .r0 by decide) p hp
      rw [u₃.other _ h1]
      simp [saveG, State.write, h1]
  · rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp]
    show s₃.sp = _
    rw [u₃.sp]
  · rw [u₁₃.lr, u₁₂.lr, u₁₁.lr, u₁₀.lr, u₉.lr, u₈.lr, u₇.lr, u₆.lr, u₅.lr]
    show s₃.lr = _
    rw [u₃.lr]
  · intro r hr
    simp only [otherRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [gF _ (by decide), g₅ _ (by decide)]

/-! ## The exit -/

theorem saved_sub : ∀ p ∈ saved, p ∈ savedL := fun _ hp => List.mem_cons_of_mem _ hp

theorem other_of_preserved : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r ∈ otherRegs := by decide

theorem saved_ne_r0 : ∀ p ∈ saved, p.1 ≠ .r0 := by decide

/-- `restore`: our caller's registers and return address back, for `s₀` the
state at the entry. -/
theorem exit_wp {c : Cx} {s₀ s : State} (E : Env c s) (sv : Saved c.W (saveG s₀) savedL s.mem)
    (hsp : s.sp = s₀.sp) (ho : ∀ r ∈ otherRegs, s.gpr r = s₀.gpr r) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .r3 = s.gpr .r3 := by
  unfold restore
  simp only [List.cons_append, List.nil_append]
  refine wp_ld (a := c.W + BitVec.ofNat 64 lrO) (by decide) (by decide) (by rw [E.r14])
    (E.perm.wR (by decide)) fun s₁ u₁ => wp_mtlr fun s₂ u₂ => ?_
  change WP isa (.block (restoreCode .r14 saved)) s₂ _
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have g₂ : ∀ r, r ≠ .r0 → s₂.gpr r = s.gpr r := fun r h => by rw [u₂.gpr, u₁.other _ h]
  have sv₂ : Saved c.W (saveG s₀) saved s₂.mem := by rw [m₂]; exact sv.sub saved_sub
  refine WP.mono (restore_wp (b := .r14) (B := c.W) (by decide) (by rw [g₂ _ (by decide), E.r14]) (by decide)
    (by decide) (fun p hp => by
      have := saved_bound p hp
      rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
      exact E.perm.wR (by omega)) sv₂) fun s' R => ?_
  have lr₂ : s₂.lr = s₀.lr := by
    rw [u₂.lr, u₁.gpr, sv (.r0, lrO) List.mem_cons_self]
    simp [saveG, State.write]
  refine ⟨⟨fun r hr => ?_, by rw [R.sp, u₂.sp, u₁.sp, hsp], by rw [R.lr, lr₂]⟩, by rw [R.mem, m₂],
    by rw [R.other _ (by decide), g₂ _ (by decide)]⟩
  by_cases hs : r ∈ saved.map Prod.fst
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
    rw [R.gpr p hp]
    simp [saveG, State.write, saved_ne_r0 p hp]
  · have hr0 : r ≠ .r0 := fun h => by subst h; exact absurd hr (by decide)
    rw [R.other r hs, g₂ r hr0, ho r (other_of_preserved r hr hs)]

end VG.Proof.AesSiv.PPC64LE
