module

public import VerifiedGarbage.Proof.Pbkdf2.Stream.PPC64LE.Step
public import VerifiedGarbage.Proof.Pbkdf2.Stream.PPC64LE.Contract
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import all Init.Data.Nat.Bitwise.Basic

/-!
# PBKDF2 over any streaming hash function on PPC64LE: `iterate`

`iterateMain` saves our caller's `r20`–`r25`, zero-extends `n` into `r22`,
copies `U` into `ub`, runs `n` steps (`Iter.step_ok`, `loop_ok`), and
restores the registers (`correctMain`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Stream.PPC64LE.Iter

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Pbkdf2.Stream.PPC64LE.Iter (keep)
open VG.Impl.Pbkdf2.Stream.PPC64LE.Iter (st dig ub bytes)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK untouched untouched_pres Saved saved_keep saveMem saveMem_saved
  saveMem_frame save_ok restore_ok preserved_of)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_li wp_mov wp_addi wp_lsl wp_lsr contains_offset eval_zero
  eval_nonzero ofNat_beq_zero ofNat_pred)
open VG.Proof.Hmac.Stream.PPC64LE.Init (cover_self cover_pre cover_off Regs)
open VG.Proof.Pbkdf2.Stream.PPC64LE.Iter (contains_start)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)
open Spec.Pbkdf2 (xorBytes)

/-- `(x << 32) >> 32` is the low 32 bits of `x`. -/
theorem zext32 (x : BitVec 64) : x <<< 32 >>> 32 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

variable {H : Hash} (hH : HashOK H) {s₀ : State}

section
variable (H) (s₀)

abbrev U0 : List Byte := bytesAt s₀.mem (up s₀) H.D
abbrev T0 : List Byte := bytesAt s₀.mem (tp s₀) H.D
abbrev ubp : Addr := scr s₀ + BitVec.ofNat 64 (ub H)

end

/-- What holds after `j` of `n` steps. -/
structure LInv (n j : Nat) (s : State) : Prop where
  regs : Regs s₀ s
  vars : Vars s₀ s
  r22 : s.gpr .r22 = BitVec.ofNat 64 (n - j)
  frame : Frame (all H s₀) s₀.mem s.mem
  saved : Saved H.W (scr s₀) s₀.gpr s.mem
  bytes : ∀ k0, Hyp hH s₀ k0 → Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) n (U0 H s₀) (T0 H s₀) =
    Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (n - j) (bytesAt s.mem (ubp H s₀) H.D)
      (bytesAt s.mem (tp s₀) H.D)

/-- The loop, from `j < n` steps done. -/
theorem loop_ok (hp : Pre H s₀) {n j : Nat} (hn : n < 2 ^ 32) (hj : j < n) {s : State}
    (h : LInv hH (s₀ := s₀) n j s) :
    WP isa (.loop (VG.Impl.Pbkdf2.Stream.PPC64LE.Iter.step H) (.nonzero .d .r22)) s
      (LInv hH (s₀ := s₀) n n) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ j < n ∧ LInv hH (s₀ := s₀) n j s) ?_ (n - j) s
    ⟨j, rfl, hj, h⟩
  rintro m s ⟨j, rfl, hj, hb⟩
  refine WP.mono (step_ok hH hp hb.regs hb.vars hb.frame hb.saved) fun s' ⟨r', v', h22, f', sv', hby⟩ => ?_
  have h22' : s'.gpr .r22 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [h22, hb.r22, ofNat_pred (by omega), Nat.sub_sub]
  have hb' : LInv hH (s₀ := s₀) n (j + 1) s' := ⟨r', v', h22', f', sv', fun k0 hk => by
    rw [hb.bytes k0 hk, show n - j = (n - (j + 1)) + 1 by omega, (hby k0 hk).1, (hby k0 hk).2]
    rfl⟩
  have hz : isa.eval (.nonzero .d .r22) s' = some (decide (n - (j + 1) ≠ 0)) := by
    show VG.PPC64LE.eval (.nonzero .d .r22) s' = _
    rw [eval_nonzero, h22', bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hl : n - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    have e : n = j + 1 := by omega
    subst e; exact hb'
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, j + 1, rfl, by omega, hb'⟩

/-- The number of steps. -/
abbrev nn (s₀ : State) : Nat := ((s₀.gpr .r5).setWidth 32).toNat

include hH in
/-- `iterate` without its frame: the callee-saved registers are kept. -/
theorem correctMain (hp : Pre H s₀) (h5 : s₀.gpr .r5 = BitVec.ofNat 64 (nn s₀)) :
    WP isa (VG.Impl.Pbkdf2.Stream.PPC64LE.iterateMain H) s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      ∀ k0, Hyp hH s₀ k0 → bytesAt s'.mem (tp s₀) H.D =
        Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (nn s₀) (U0 H s₀) (T0 H s₀) := by
  have hz := sz hH
  have hW : H.W % 8 = 0 ∧ H.W ≤ 1024 := hH.dims.so
  have hD := hH.hD64
  have hDF := hH.hDF
  have hD4 := hH.hD4
  have hDq : 4 * (H.D / 4) = H.D := by omega
  have e0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => by simp
  have hbytes : bytes H = H.W + 48 + H.S + H.FD + H.FD := by simp [bytes, ub, dig, st] <;> omega
  have hbl : bytes H < 2 ^ 64 := by rw [hbytes]; have := hz.S; have := hz.FD; have := hz.W; omega
  have hub : ub H + H.D ≤ bytes H := by simp [bytes, ub, dig, st]; omega
  have hn : nn s₀ < 2 ^ 32 := ((s₀.gpr .r5).setWidth 32).isLt
  have add_off := VG.Proof.Hmac.Stream.PPC64LE.add_off
  have scW : scR H s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  let svR : Region := ⟨scr s₀ + BitVec.ofNat 64 H.W, 48⟩
  unfold VG.Impl.Pbkdf2.Stream.PPC64LE.iterateMain
  -- Save our caller's registers, `n`, our variables, and `U` into `ub`.
  refine WP.seq (save_ok hW (b := .r7) (by decide)
    (fun d hd₁ hd₂ => ⟨scR H s₀, scW, contains_offset
      (show d + 8 ≤ bytes H by have : d + 8 ≤ H.W + 48 := hd₂; rw [hbytes]; omega) (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_)
  refine wp_mov fun s₂ x₂ => wp_mov fun s₃ x₃ => wp_mov fun s₄ x₄ => wp_mov fun s₆ x₆ => ?_
  have r₆ : Regs s₀ s₆ :=
    ⟨by rw [x₆.rd, x₄.rd, x₃.rd, x₂.rd, rd₁], by rw [x₆.wr, x₄.wr, x₃.wr, x₂.wr, wr₁],
      by rw [x₆.sp, x₄.sp, x₃.sp, x₂.sp, sp₁]⟩
  have m₆ : s₆.mem = saveMem H.W s₀.mem (scr s₀) s₀.gpr := by
    rw [x₆.mem, x₄.mem, x₃.mem, x₂.mem, m₁]
  have k₆ : ∀ r, r ≠ .r20 → r ≠ .r21 → r ≠ .r22 → r ≠ .r23 → s₆.gpr r = s₀.gpr r := fun r a b c d => by
    rw [x₆.other r d, x₄.other r c, x₃.other r b, x₂.other r a, g₁]
  have h4 : s₆.gpr .r4 = up s₀ := k₆ _ (by decide) (by decide) (by decide) (by decide)
  have h21 : s₆.gpr .r21 = scr s₀ := by
    rw [x₆.other _ (by decide), x₄.other _ (by decide), x₃.gpr, x₂.other _ (by decide), g₁]
  have h22 : s₆.gpr .r22 = BitVec.ofNat 64 (nn s₀) := by
    rw [x₆.other _ (by decide), x₄.gpr, x₃.other _ (by decide), x₂.other _ (by decide), g₁, h5]
  have v₆ : Vars s₀ s₆ := by
    refine ⟨?_, h21, ?_, fun r hr => k₆ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)⟩
    · rw [x₆.other _ (by decide), x₄.other _ (by decide), x₃.other _ (by decide), x₂.gpr, g₁]
    · rw [x₆.gpr, x₄.other _ (by decide), x₃.other _ (by decide), x₂.other _ (by decide), g₁]
  have uR' : uR H s₀ ∈ s₆.rd ++ s₆.wr := List.mem_append_left _ (by rw [r₆.rd, hp.rd]; simp)
  have scW₆ : scR H s₀ ∈ s₆.wr := by rw [r₆.wr]; exact scW
  have ubS : Region.Sub ⟨ubp H s₀, H.D⟩ (scR H s₀) := ubD_sub hz _
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.PPC64LE.Iter.copyU H)]
  refine (VG.Proof.Hmac.Stream.PPC64LE.copy32_ok (src := .r4) (dst := .r21) (by decide) (by decide)
    (by decide) (by decide) 0 (ub H) (H.D / 4)
    ⟨by omega, by have := hz.W; have := hz.S; have := hz.FD; show H.W + 48 + H.S + H.FD + 4 * (H.D / 4) ≤ 2 ^ 15; omega⟩
    [] s₆ _
    (fun k hk => ⟨uR H s₀, uR', by rw [h4, e0]; exact contains_offset (by omega) (by omega)⟩)
    (fun k hk => ⟨scR H s₀, scW₆, by rw [h21, ← add_off]; exact contains_offset (by omega) (by omega)⟩)
    (by
      rw [h4, h21, e0, hDq]
      exact hp.u_s.sep (contains_start (Nat.le_refl _)) (contains_offset (by omega) (by omega)))
    fun s₇ g₇ rd₇ wr₇ sp₇ m₇ => WP.block_nil ?_)
  rw [h4, h21, e0, hDq] at m₇
  have r₇ : Regs s₀ s₇ := ⟨rd₇.trans r₆.rd, wr₇.trans r₆.wr, sp₇.trans r₆.sp⟩
  have v₇ : Vars s₀ s₇ := v₆.of_keep fun r _ _ _ _ _ h8 _ _ => g₇ r h8
  have fS : Frame [⟨scr s₀, H.W + 48⟩] s₀.mem s₆.mem := by rw [m₆]; exact saveMem_frame hW _ _ _
  have fU : Frame [⟨ubp H s₀, H.D⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [VG.Proof.Hmac.Common.bytesAt_length]; exact contains_start (Nat.le_refl _))
  have l₀ : LInv hH (s₀ := s₀) (nn s₀) 0 s₇ := by
    refine ⟨r₇, v₇, by rw [g₇ _ (by decide), h22, Nat.sub_zero], ?_, ?_, fun k0 _ => ?_⟩
    · exact (fS.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨scR H s₀, by simp [all], Region.sub_prefix (by rw [hbytes]; omega)⟩).trans
        (fU.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR H s₀, by simp [all], ubS⟩)
    · exact saved_keep (by rw [m₆]; exact saveMem_saved hW _ _ _) fU (by
        simp only [List.mem_singleton]; rintro r rfl; exact sv_ub hz _ |>.sub_right (Region.sub_prefix hDF))
    · rw [Nat.sub_zero]
      have hu : bytesAt s₇.mem (ubp H s₀) H.D = U0 H s₀ := by
        rw [m₇]
        have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s₆.mem (ubp H s₀) (bytesAt s₆.mem (up s₀) H.D)
          (by rw [VG.Proof.Hmac.Common.bytesAt_length]; omega)
        rw [VG.Proof.Hmac.Common.bytesAt_length] at this
        rw [this]
        exact keep fS (by
          simp only [List.mem_singleton]; rintro r rfl
          exact hp.u_s.sub_right (Region.sub_prefix (by rw [hbytes]; omega))) (by omega)
      have ht : bytesAt s₇.mem (tp s₀) H.D = T0 H s₀ := by
        rw [keep fU (by simp only [List.mem_singleton]; rintro r rfl; exact hp.t_s.sub_right ubS) (by omega)]
        exact keep fS (by
          simp only [List.mem_singleton]; rintro r rfl
          exact hp.t_s.sub_right (Region.sub_prefix (by rw [hbytes]; omega))) (by omega)
      rw [hu, ht]
  -- The steps.
  have hdone : ∀ s', LInv hH (s₀ := s₀) (nn s₀) (nn s₀) s' →
      WP isa (.block (Hash.restoreAt H.W)) s' fun s'' =>
        (∀ r ∈ preserved, s''.gpr r = s₀.gpr r) ∧ s''.sp = s₀.sp ∧
        ∀ k0, Hyp hH s₀ k0 → bytesAt s''.mem (tp s₀) H.D =
          Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (nn s₀) (U0 H s₀) (T0 H s₀) := by
    intro s' l
    refine restore_ok hW (scr := scr s₀) l.vars.r21
      (fun d hd₁ hd₂ => ⟨scR H s₀, by rw [l.regs.rd, l.regs.wr]; exact List.mem_append_right _ scW,
        contains_offset (show d + 8 ≤ bytes H by have : d + 8 ≤ H.W + 48 := hd₂; rw [hbytes]; omega) (by omega)⟩)
      s₀.gpr l.saved fun s'' hsv ho hmem _ _ hsp => ⟨preserved_of hsv fun r hr => ?_, by rw [hsp, l.regs.sp],
        fun k0 hk => by rw [hmem, l.bytes k0 hk, Nat.sub_self]; rfl⟩
    rw [ho r (by simp only [Hash.savedAt, List.map_cons, List.map_nil]; revert r; decide)]
    exact l.vars.un r hr
  have hc : isa.eval (.zero .d .r22) s₇ = some (decide (nn s₀ = 0)) := by
    show VG.PPC64LE.eval (.zero .d .r22) s₇ = _
    rw [eval_zero, g₇ _ (by decide), h22, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.ite (decide (nn s₀ = 0)) hc (fun hb => WP.block_nil (hdone s₇ ?_))
    (fun hb => WP.mono (loop_ok hH hp hn (j := 0) (Nat.pos_of_ne_zero (by simpa using hb)) l₀) hdone))
  have e : nn s₀ = 0 := by simpa using hb
  rw [e] at l₀ ⊢
  exact l₀

/-! ## The frame -/

include hH in
theorem iterateMain_fdepth : (VG.Impl.Pbkdf2.Stream.PPC64LE.iterateMain H).fdepth ≤ 1 := by
  have := hH.finFd
  have := hH.updFd
  simp only [VG.Impl.Pbkdf2.Stream.PPC64LE.iterateMain, VG.Impl.Pbkdf2.Stream.PPC64LE.Iter.step,
    Hash.callFin, Hash.callUpd, Code.fdepth, Nat.max_le]
  omega

include hH in
theorem iterateMain_pf : pushFrames (VG.Impl.Pbkdf2.Stream.PPC64LE.iterateMain H) = true := by
  simp [VG.Impl.Pbkdf2.Stream.PPC64LE.iterateMain, VG.Impl.Pbkdf2.Stream.PPC64LE.Iter.step, Hash.callFin,
    Hash.callUpd, pushFrames, hH.finPf, hH.updPf]

theorem pre_framed {s : State} (hp : (iterG hH.SH (bytes H) 96).pre s) : Pre H (framed .r0 s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hp
  rw [hH.hS, hH.hD] at *
  have sub : Region.Sub (below (s.sp - 48) 48) (below s.sp 96) := below_body s.sp 48
  exact ⟨h1, h2, h3, h4, h5, h6, h7, by show 48 ≤ (s.sp - 48).toNat; bv_omega, h9.sub_left sub,
    h10.sub_left sub, h11.sub_left sub, h12.sub_left sub⟩

/-- A byte of a region the frame is disjoint from is unchanged by the push. -/
theorem framed_bytes {s : State} {R : Region} (hd : (below s.sp 48).Disjoint R) (hR : R.len < 2 ^ 64) {i : Nat}
    (hi : i < R.len) : (framed .r0 s).mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  Proof.MdStream.PPC64LE.write_frame_bytes hd hR hi

/-- `iterate`, with its frame. -/
theorem correct {s₀ : State} (hp : (iterG hH.SH (bytes H) 96).pre s₀) :
    WP isa (VG.Impl.Pbkdf2.Stream.PPC64LE.iterate H) s₀ fun s' =>
      abiPreserved s₀ s' ∧ (iterG hH.SH (bytes H) 96).post s₀ s' := by
  have hz := sz hH
  have hsub : Region.Sub (below s₀.sp 48) (below s₀.sp 96) := below_sub (by have := hp.2.2.2.2.2.2.2.1; omega)
    (by have := hp.2.2.2.2.2.2.2.1; omega)
  unfold VG.Impl.Pbkdf2.Stream.PPC64LE.iterate VG.Impl.Pbkdf2.Stream.PPC64LE.zextN
    VG.Impl.Pbkdf2.Stream.PPC64LE.iterateBody
  refine WP.seq (Proof.MdStream.PPC64LE.WP.cons exec_mflr (wp_lsl (by decide) fun s₁ x₁ =>
    wp_lsr (by decide) fun s₂ x₂ => WP.block_nil (WP.seq ?_)))
  have q₂ : ∀ r, r ≠ .r0 → r ≠ .r5 → s₂.gpr r = s₀.gpr r := fun r h0 h5 => by
    rw [x₂.other r h5, x₁.other r h5]; simp only [State.write, h0, ite_false]
  have rd₂ : s₂.rd = s₀.rd := by rw [x₂.rd, x₁.rd]; rfl
  have wr₂ : s₂.wr = s₀.wr := by rw [x₂.wr, x₁.wr]; rfl
  have sp₂ : s₂.sp = s₀.sp := by rw [x₂.sp, x₁.sp]; rfl
  have mem₂ : s₂.mem = s₀.mem := by rw [x₂.mem, x₁.mem]; rfl
  have hn₂ : nn (framed .r0 s₂) = nn s₀ := by
    show ((s₂.gpr .r5).setWidth 32).toNat = _
    rw [x₂.gpr, x₁.gpr, show (s₀.write .r0 s₀.lr).gpr .r5 = s₀.gpr .r5 from rfl, zext32, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat]
    have := ((s₀.gpr .r5).setWidth 32).isLt
    show _ = ((s₀.gpr .r5).setWidth 32).toNat
    omega
  have hp₂ : (iterG hH.SH (bytes H) 96).pre s₂ := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hp
    simp only [iterG, rd₂, wr₂, sp₂, q₂ .r3 (by decide) (by decide), q₂ .r4 (by decide) (by decide),
      q₂ .r6 (by decide) (by decide), q₂ .r7 (by decide) (by decide)]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  have hpi := pre_framed hH hp₂
  have h5 : (framed .r0 s₂).gpr .r5 = BitVec.ofNat 64 (nn (framed .r0 s₂)) := by
    rw [hn₂]; show s₂.gpr .r5 = _
    rw [x₂.gpr, x₁.gpr, show (s₀.write .r0 s₀.lr).gpr .r5 = s₀.gpr .r5 from rfl, zext32]
  obtain ⟨h1, h2, _, _, _, _, _, h8, h9, h10, h11, h12⟩ := hp
  refine WP.frameReg (by rw [sp₂]; show 48 ≤ s₀.sp.toNat; omega) (fun R hR => ?_)
    (WP.mono (correctMain hH hpi h5) fun s' ⟨hk, hsp, hpost⟩ => ?_) (by have := iterateMain_fdepth hH; omega)
    (iterateMain_pf hH)
  · rw [wr₂, h2] at hR
    have hf : Region.Sub ⟨s₂.sp - 48 + 32, 16⟩ (below s₀.sp 96) :=
      fun a h => hsub a (by rw [← sp₂]; exact Proof.MdStream.PPC64LE.frame_sub s₂.sp a h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact h11.sub_left hf
    · exact h12.sub_left hf
  · refine Proof.MdStream.PPC64LE.WP.cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, by rw [← sp₂], ?_⟩, ?_⟩)
    · have h0 : r ≠ .r0 := by revert r hr; decide
      simp only [State.write, h0, ite_false]
      rw [hk r hr]
      simp only [framed]
      exact q₂ r h0 (by revert r hr; decide)
    · simp only [State.write]
      rw [x₂.other .r0 (by decide), x₁.other .r0 (by decide)]
      simp [State.write]
    · intro k0 hk0 hI hO
      rw [hH.hD]
      have hS2 : 2 * H.S < 2 ^ 64 := by have := hz.S; omega
      have hDl : H.D < 2 ^ 64 := by have := hH.hD64; omega
      have hsub₂ : Region.Sub (below s₂.sp 48) (below s₀.sp 96) := by rw [sp₂]; exact hsub
      have hu : U0 H (framed .r0 s₂) = bytesAt s₀.mem (s₀.gpr .r4) H.D := by
        show bytesAt (framed .r0 s₂).mem (s₂.gpr .r4) H.D = _
        rw [q₂ .r4 (by decide) (by decide), ← mem₂]
        exact Proof.Sha256.Stream.bytesAt_congr fun i hi =>
          framed_bytes (R := ⟨s₀.gpr .r4, H.D⟩) (by rw [← hH.hD]; exact h10.sub_left hsub₂) hDl hi
      have ht : T0 H (framed .r0 s₂) = bytesAt s₀.mem (s₀.gpr .r6) H.D := by
        show bytesAt (framed .r0 s₂).mem (s₂.gpr .r6) H.D = _
        rw [q₂ .r6 (by decide) (by decide), ← mem₂]
        exact Proof.Sha256.Stream.bytesAt_congr fun i hi =>
          framed_bytes (R := ⟨s₀.gpr .r6, H.D⟩) (by rw [← hH.hD]; exact h11.sub_left hsub₂) hDl hi
      have hI' : hH.SH.Repr (framed .r0 s₂).mem (kp (framed .r0 s₂)) (xorPad k0 ipad) := by
        show hH.SH.Repr (framed .r0 s₂).mem (s₂.gpr .r3) _
        rw [q₂ .r3 (by decide) (by decide)]
        refine hH.congr s₀.mem _ _ _ (fun i hi => ?_) hI
        rw [← mem₂]
        exact framed_bytes (R := ⟨s₀.gpr .r3, 2 * H.S⟩) (by rw [← hH.hS]; exact h9.sub_left hsub₂)
          hS2 (show i < 2 * H.S by omega)
      have hO' : hH.SH.Repr (framed .r0 s₂).mem (kp (framed .r0 s₂) + BitVec.ofNat 64 H.S) (xorPad k0 opad) := by
        show hH.SH.Repr (framed .r0 s₂).mem (s₂.gpr .r3 + BitVec.ofNat 64 H.S) _
        rw [q₂ .r3 (by decide) (by decide)]
        rw [hH.hS] at hO
        refine hH.congr s₀.mem _ _ _ (fun i hi => ?_) hO
        rw [← mem₂]
        have := framed_bytes (s := s₂) (R := ⟨s₀.gpr .r3, 2 * H.S⟩) (by rw [← hH.hS]; exact h9.sub_left hsub₂)
          hS2 (i := H.S + i) (show H.S + i < 2 * H.S by omega)
        rwa [VG.Proof.Hmac.Stream.PPC64LE.add_off] at this
      show bytesAt s'.mem (s₀.gpr .r6) H.D = _
      rw [← q₂ .r6 (by decide) (by decide)]
      refine (hpost k0 ⟨by rw [hk0, hH.hB], hI', hO'⟩).trans ?_
      rw [hu, ht, hn₂, q₂ .r6 (by decide) (by decide)]

end VG.Proof.Pbkdf2.Stream.PPC64LE.Iter
