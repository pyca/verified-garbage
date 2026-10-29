module

public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Env
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Contract
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Fn
import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# AES-GCM-SIV on PPC64LE: the arguments, the entry and the exit

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`). `entry` loads `work` from the stack, saves
our caller's registers and the return address at `W + 128` and keeps the
arguments in `r14`–`r22` (`entry_wp`); `restore` reloads them (`exit_wp`).
The pieces write only the parts of `W` in `mutR` and the data, so the slots
stay as the entry left them.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Spec.Aes (bytesAt)
open VG.PPC64LE.Spill (saveCode saveMem Saved saveMem_saved save_ok restoreCode restore_wp)
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_ld wp_std wp_mflr wp_mtlr)
open VG.Proof.ChaCha20Poly1305.PPC64LE.Gather (wp_addSp)
open VG.Proof.AesCcm.PPC64LE (wp_mv)
open VG.Proof.Gather.PPC64LE (covers_off in_off)

/-- The public values of the arguments of `s`. -/
def cxOf (s : State) : Cx where
  K := s.gpr .r3
  W := stackArg s 0
  N := s.gpr .r5
  A := s.gpr .r6
  D := s.gpr .r8
  T := s.gpr .r10
  R := (s.gpr .r4).toNat
  al := (s.gpr .r7).toNat
  n := (s.gpr .r9).toNat

/-- What `seal` and `open` are given: the public values `c`. -/
structure Args (c : Cx) (s : State) : Prop where
  lay : Lay c
  r3 : s.gpr .r3 = c.K
  r4 : s.gpr .r4 = BitVec.ofNat 64 c.R
  r5 : s.gpr .r5 = c.N
  r6 : s.gpr .r6 = c.A
  r7 : s.gpr .r7 = BitVec.ofNat 64 c.al
  r8 : s.gpr .r8 = c.D
  r9 : s.gpr .r9 = BitVec.ofNat 64 c.n
  r10 : s.gpr .r10 = c.T
  w : stackArg s 0 = c.W
  perm : Perm c s
  argsC : Covers [args s] (s.rd ++ s.wr)
  argsW : (args s).Disjoint ⟨c.W, 3824⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem covers_of_mem {r : Region} {rs : List Region} (h : r ∈ rs) : Covers [r] rs := fun _ _ ⟨r', hr', hc⟩ => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact ⟨_, h, hc⟩

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (hk : Covers [⟨s.gpr .r3, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .r5, 12⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .r6, (s.gpr .r7).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [args s] (s.rd ++ s.wr))
    (hT : Covers [⟨s.gpr .r10, 16⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .r8, (s.gpr .r9).toNat⟩] s.wr) (hW : Covers [⟨stackArg s 0, 3824⟩] s.wr) :
    Args (cxOf s) s := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, _, d11, b1, b2, b3, b4, b5, b6, _, hR⟩ := h
  exact {
    lay := ⟨b1, b6, b2, b3, b4, b5, d2, d1, d4, d3, d6, d5, d9, d8, d7, hR, BitVec.isLt _, BitVec.isLt _⟩
    r3 := rfl
    r4 := (ofNat_toNat64 _).symm
    r5 := rfl
    r6 := rfl
    r7 := (ofNat_toNat64 _).symm
    r8 := rfl
    r9 := (ofNat_toNat64 _).symm
    r10 := rfl
    w := rfl
    perm := ⟨hk, hW, hN, hA, hD, hT⟩
    argsC := ha
    argsW := d11.symm }

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) : Args (cxOf s) s ∧ Covers [⟨s.gpr .r10, 16⟩] s.wr := by
  obtain ⟨hrd, hwr, _, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .r3, 240⟩ : Region), ⟨s.gpr .r5, 12⟩, ⟨s.gpr .r6, (s.gpr .r7).toNat⟩, args s],
      Covers [r] (s.rd ++ s.wr) := fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region), ⟨s.gpr .r10, 16⟩, ⟨stackArg s 0, 3824⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (Covers.right (mwr _ (by simp))) (mwr _ (by simp)) (mwr _ (by simp)), mwr _ (by simp)⟩

/-- `open`'s arguments, with the received tag to read. -/
theorem args_of_open {s : State} (h : openPre s) : Args (cxOf s) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .r3, 240⟩ : Region), ⟨s.gpr .r5, 12⟩, ⟨s.gpr .r6, (s.gpr .r7).toNat⟩,
      ⟨s.gpr .r10, 16⟩, args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region), ⟨stackArg s 0, 3824⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (mwr _ (by simp)) (mwr _ (by simp))

/-! ## What the pieces write -/

/-- What the pieces write: the parts of `W` below the slots and above them,
and the data. -/
abbrev mutR (c : Cx) : List Region := [⟨c.W, 128⟩, ⟨c.W + BitVec.ofNat 64 240, 3584⟩, ⟨c.D, c.n⟩]

theorem sub_lo {c : Cx} {d k : Nat} (h : d + k ≤ 128) :
    ∃ r' ∈ mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨c.W, 128⟩, by simp, Offset.sub_base _ h⟩

theorem sub_hi {c : Cx} {d k : Nat} (h₁ : 240 ≤ d) (h₂ : d + k ≤ 3824) :
    ∃ r' ∈ mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨c.W + BitVec.ofNat 64 240, 3584⟩, by simp, Offset.sub _ h₁ (by omega)⟩

theorem sub_data {c : Cx} : ∃ r' ∈ mutR c, Region.Sub ⟨c.D, c.n⟩ r' := ⟨_, by simp, fun _ h => h⟩

/-- A buffer missing `W` and the data misses what the pieces write. -/
theorem buf_mut {c : Cx} {P : Addr} {k : Nat} (hw : (⟨P, k⟩ : Region).Disjoint ⟨c.W, 3824⟩)
    (hd : (⟨P, k⟩ : Region).Disjoint ⟨c.D, c.n⟩) : ∀ r ∈ mutR c, (⟨P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hw.sub_right (Region.sub_prefix (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hd

/-- The key schedule is kept by what the pieces write. -/
theorem ciph_mut {c : Cx} (L : Lay c) {m m' : Mem} (hf : Frame (mutR c) m m') :
    Spec.GcmSiv.ctxCiph m' c.K c.R = Spec.GcmSiv.ctxCiph m c.K c.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (buf_mut L.k_w L.k_d r hr).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega)]

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
  change WP isa (.block ([.addSp .r12 0, .load .d .r11 .r12 96, .mflr .r0] ++ saveCode .r11 saved ++ _)) s _
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  have r12₁ : s₁.gpr .r12 = s.sp := by rw [u₁.gpr, BitVec.add_zero]
  refine wp_ld (a := stackArgAddr s 0) (by decide) (by decide) (by rw [r12₁]; rfl)
    (by rw [u₁.rd, u₁.wr]; simpa using in_off Ar.argsC (d := 0) (n := 8) (by decide) (by decide))
    fun s₂ u₂ => wp_mflr fun s₃ u₃ => ?_
  have W₃ : s₃.gpr .r11 = c.W := by rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, ← Ar.w]; rfl
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  refine save_ok (b := .r11) (by decide) (by decide) (fun p hp => by
    rw [W₃, wr₃]; exact Ar.perm.wW (by have := saved_bound p hp; omega)) ?_
  rw [W₃]
  generalize hmS : saveMem s₃.mem c.W s₃.gpr saved = mS
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have fS : Frame [⟨c.W + BitVec.ofNat 64 128, 96⟩] s.mem mS := by
    rw [← hmS, m₃]; exact Spill.saveMem_frame saved_bound (by omega) _ _ _
  have svS : Saved c.W s₃.gpr saved mS := by rw [← hmS]; exact saveMem_saved (by decide) _ _ _
  refine wp_std (a := c.W + BitVec.ofNat 64 224) (by decide) (by decide) (by show s₃.gpr .r11 + _ = _; rw [W₃]; rfl)
    (by show InRegions s₃.wr _ 8; rw [wr₃]; exact Ar.perm.wW (by decide)) fun s₅ u₅ => ?_
  refine wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => wp_mv fun s₉ u₉ => wp_mv fun s₁₀ u₁₀ =>
    wp_mv fun s₁₁ u₁₁ => wp_mv fun s₁₂ u₁₂ => wp_mv fun s₁₃ u₁₃ => wp_mv fun s₁₄ u₁₄ => WP.block_nil ?_
  have m₁₄ : s₁₄.mem = mS.writeW (c.W + BitVec.ofNat 64 224) s.lr := by
    rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
    show mS.writeW _ (s₃.gpr .r0) = _; rw [u₃.gpr, u₂.lr, u₁.lr]
  have c224 : (entryR c.W).Contains (c.W + BitVec.ofNat 64 224) (64 / 8) :=
    Offset.contains c.W (by decide) (by decide) (by decide)
  have f₁₄ : Frame [entryR c.W] s.mem s₁₄.mem := by
    rw [m₁₄]
    exact (fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩).writeW (List.mem_singleton_self _) _ c224
  have g₅ : ∀ r, r ≠ .r0 → r ≠ .r11 → r ≠ .r12 → s₅.gpr r = s.gpr r := fun r h0 h11 h12 => by
    rw [u₅.gpr]; show s₃.gpr r = _; rw [u₃.other _ h0, u₂.other _ h11, u₁.other _ h12]
  have r14₆ : s₆.gpr .r14 = c.W := by rw [u₆.gpr, u₅.gpr]; exact W₃
  have gF : ∀ r, r ∉ [Reg.r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22] → s₁₄.gpr r = s₆.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h15, h16, h17, h18, h19, h20, h21, h22⟩ := hr
    rw [u₁₄.other _ h22, u₁₃.other _ h21, u₁₂.other _ h20, u₁₁.other _ h19, u₁₀.other _ h18, u₉.other _ h17,
      u₈.other _ h16, u₇.other _ h15]
  have g₆ : ∀ r, r ≠ .r0 → r ≠ .r11 → r ≠ .r12 → r ≠ .r14 → s₆.gpr r = s.gpr r := fun r h0 h11 h12 h14 => by
    rw [u₆.other _ h14, g₅ r h0 h11 h12]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Ar.perm.of_eq ?_ ?_⟩, ?_, f₁₄, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gF _ (by decide), r14₆]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      g₆ .r5 (by decide) (by decide) (by decide) (by decide), Ar.r5]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      g₆ .r3 (by decide) (by decide) (by decide) (by decide), Ar.r3]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      g₆ .r4 (by decide) (by decide) (by decide) (by decide), Ar.r4]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      g₆ .r6 (by decide) (by decide) (by decide) (by decide), Ar.r6]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr,
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      g₆ .r7 (by decide) (by decide) (by decide) (by decide), Ar.r7]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      g₆ .r8 (by decide) (by decide) (by decide) (by decide), Ar.r8]
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      g₆ .r9 (by decide) (by decide) (by decide) (by decide), Ar.r9]
  · rw [u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      g₆ .r10 (by decide) (by decide) (by decide) (by decide), Ar.r10]
  · rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd]; exact rd₃
  · rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr]; exact wr₃
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · show s₁₄.mem.readW (c.W + BitVec.ofNat 64 224) 64 = _
      rw [m₁₄, Mem.readW_writeW_self64]
      simp [saveG, State.write]
    · have hv : mS.readW (c.W + BitVec.ofNat 64 p.2) 64 = s₃.gpr p.1 := svS p hp
      have d224 : Mem.Sep (c.W + BitVec.ofNat 64 p.2) (64 / 8) (c.W + BitVec.ofNat 64 224) (64 / 8) := by
        have := saved_bound p hp
        exact (L.w_w (n := 8) (k := 8) (.inl (by omega)) (by omega) (by decide)).sep (Region.contains_self _ _)
          (Region.contains_self _ _)
      rw [m₁₄, Mem.readW_writeW_sep d224 (by decide), hv]
      have h1 : p.1 ≠ .r0 ∧ p.1 ≠ .r11 ∧ p.1 ≠ .r12 :=
        (show ∀ q ∈ saved, q.1 ≠ .r0 ∧ q.1 ≠ .r11 ∧ q.1 ≠ .r12 by decide) p hp
      rw [u₃.other _ h1.1, u₂.other _ h1.2.1, u₁.other _ h1.2.2]
      simp [saveG, State.write, h1.1]
  · rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd]; exact rd₃
  · rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr]; exact wr₃
  · rw [u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp]
    show s₃.sp = _
    rw [u₃.sp, u₂.sp, u₁.sp]
  · rw [u₁₄.lr, u₁₃.lr, u₁₂.lr, u₁₁.lr, u₁₀.lr, u₉.lr, u₈.lr, u₇.lr, u₆.lr, u₅.lr]
    show s₃.lr = _
    rw [u₃.lr, u₂.lr, u₁.lr]
  · intro r hr
    simp only [otherRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [gF _ (by decide), g₆ _ (by decide) (by decide) (by decide) (by decide)]

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

end VG.Proof.AesGcmSiv.PPC64LE
