import VerifiedGarbage.Proof.AesOcb.AArch64.Callee
import VerifiedGarbage.Proof.Framework.AArch64.Spill

/-!
# AES-OCB on AArch64: the entry (`entry`)

Untrusted: everything here is checked by Lean. `entry` reads `W` from the
stack, saves our caller's registers at `W + savO` (`Spill.save_wp`), keeps
the data and its length in `x21` and `x28` and the other arguments in `W`,
computes `L_$` and `L_0` from `L_*` and zeroes the checksum (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxLstar lDollar lAt)
open VG.Proof.AesGcm.AArch64 (in_left in_off)
open VG.Proof.Ocb (blockAtMem_frame)

theorem saved_fits : Spill.Fits saved := by decide

theorem saved_in : ∀ p ∈ saved, 160 ≤ p.2 ∧ p.2 + 8 ≤ 160 + 88 := by decide

theorem save_eq (b : Reg) : save b = Spill.saveCode b saved := rfl

theorem restore_eq : restore = Spill.restoreCode .x19 saved := rfl

/-- The parts of `W` that `entry` writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 32, 256⟩

/-- `ldr x, [sp, #off]` of a stack argument. -/
theorem ldrSp_ok {s : State} {t : Reg} {i : Nat} (hi : i < 4)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * i)) 8) :
    ∃ s', runBlock isa [.ldrSp t (8 * i)] s = some s' ∧ s' = s.write .x t (stackArg s i) := by
  refine ⟨_, ?_, rfl⟩
  have h₁ : (8 * i) % 8 = 0 := by omega
  have h₂ : 8 * i < 32768 := by omega
  simp only [runBlock_cons, runBlock_nil, runStep_some, exec, h₁, h₂, and_self, ite_true, State.load, hsp,
    Option.map_some, stackArg, stackArgAddr, Mem.readW, BitVec.setWidth_eq]

/-- What `entry` leaves. -/
structure EntryPost (K W D : Addr) (R n : Nat) (N A : Addr) (nl al tl : Nat) (s s₁ : State) : Prop where
  env : Env K W D R n s.sp s₁
  slots : Slots W N A nl al tl s₁.mem
  saved : Spill.Saved W s.gpr saved s₁.mem
  ld : blockAtMem s₁.mem (W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem K)
  l0 : blockAtMem s₁.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0
  ck : blockAtMem s₁.mem (W + BitVec.ofNat 64 ckO) = 0
  frame : Frame [entryR W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem readW_writeW_off {m : Mem} {W : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) (by decide)

/-- `entry`. -/
theorem entry_ok {K W : Addr} (L : Lay K W) {s : State} (P : Perm K W s) {R n : Nat} {N A D : Addr}
    {nl al tl : Nat} (hW : stackArg s 0 = W) (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (hargs : Covers [⟨s.sp, 16⟩] (s.rd ++ s.wr)) (hargsW : (⟨s.sp, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa (.block entry) s (EntryPost K W D R n N A nl al tl s) := by
  have a₀ : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 0)) 8 := in_off hargs (by decide) (by decide)
  obtain ⟨_, run₀, rfl⟩ := ldrSp_ok (t := .x9) (s := s) (i := 0) (by decide) a₀
  rw [hW] at run₀
  simp only [Nat.reduceMul] at run₀
  have x9₀ : (s.write .x .x9 W).gpr .x9 = W := by simp [gpr_write]
  have hin : ∀ p ∈ saved, InRegions (s.write .x .x9 W).wr ((s.write .x .x9 W).gpr .x9 + BitVec.ofNat 64 p.2) 8 :=
    fun p hp => by
      rw [x9₀, wr_write]; exact in_off P.w (by have := saved_in p hp; omega) (by decide)
  obtain ⟨g₀, hg₀⟩ : ∃ g, g = (s.write .x .x9 W).gpr := ⟨_, rfl⟩
  obtain ⟨M₁, hM₁⟩ : ∃ M, M = Spill.saveMem s.mem W g₀ saved := ⟨_, rfl⟩
  have hsv₁ : Spill.Saved W s.gpr saved M₁ := by
    have := Spill.saveMem_saved saved_fits s.mem W g₀
    rw [← hM₁] at this
    intro p hp
    rw [this p hp]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hg₀, gpr_write]
  have f₁ : Frame [⟨W + BitVec.ofNat 64 160, 88⟩] s.mem M₁ :=
    hM₁ ▸ Spill.saveMem_frame saved_in (by decide) _ _ _
  rw [entry]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨_, run₀, ?_⟩
  rw [save_eq, WP.block_append_iff]
  refine WP.mono (Spill.save_wp saved_fits.1 hin) fun s₁ St => ?_
  rw [x9₀] at St
  have g₁ : s₁.gpr = g₀ := by rw [St.gpr, hg₀]
  have m₁ : s₁.mem = M₁ := by rw [St.mem, hM₁, hg₀]; rfl
  -- the registers and the arguments kept in `W`
  have ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s₁.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [St.wr, wr_write]; exact in_off P.w h (by decide)
  have w₁ := ww (d := nO) (by decide)
  have w₂ := ww (d := nlO) (by decide)
  have w₃ := ww (d := aadO) (by decide)
  have w₄ := ww (d := alenO) (by decide)
  have w₅ := ww (d := tlO) (by decide)
  simp only [nO, nlO, aadO, alenO, tlO] at w₁ w₂ w₃ w₄ w₅
  have gx : ∀ r, r ≠ .x9 → s₁.gpr r = s.gpr r := fun r hr => by rw [g₁, hg₀, gpr_write_of_ne _ _ _ hr]
  have x9₁ : s₁.gpr .x9 = W := by rw [g₁, hg₀, x9₀]
  obtain ⟨M₂, hM₂⟩ : ∃ M, M = (((M₁.writeW (W + BitVec.ofNat 64 272) N).writeW (W + BitVec.ofNat 64 280)
    (BitVec.ofNat 64 nl)).writeW (W + BitVec.ofNat 64 256) A).writeW (W + BitVec.ofNat 64 264) (BitVec.ofNat 64 al) :=
    ⟨_, rfl⟩
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x22₂, x28₂, g₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [Impl.AesGcm.AArch64.mov .x19 .x9, Impl.AesGcm.AArch64.mov .x20 .x0, Impl.AesGcm.AArch64.mov .x21 .x6,
        Impl.AesGcm.AArch64.mov .x22 .x1, Impl.AesGcm.AArch64.mov .x28 .x7, st .x19 nO .x2, st .x19 nlO .x3,
        st .x19 aadO .x4, st .x19 alenO .x5] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = K ∧ s₂.gpr .x21 = D ∧ s₂.gpr .x22 = BitVec.ofNat 64 R ∧
      s₂.gpr .x28 = BitVec.ofNat 64 n ∧ (∀ r, r ∉ [.x19, .x20, .x21, .x22, .x28] → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = M₂ ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by orun [x9₁, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩ <;>
      try simp only [mem_write, sp_write, rd_write, wr_write]
    · simp [gpr_write, x9₁]
    · simp [gpr_write, gx .x0 (by decide), h0]
    · simp [gpr_write, gx .x6 (by decide), h6]
    · simp [gpr_write, gx .x1 (by decide), h1]
    · simp [gpr_write, gx .x7 (by decide), h7]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, gx .x2 (by decide), gx .x3 (by decide),
        gx .x4 (by decide), gx .x5 (by decide), h2, h3, h4, h5, x9₁, hM₂, m₁]
    · rw [St.sp, sp_write]
    · rw [St.rd, rd_write]
    · rw [St.wr, wr_write]
  have f₂ : Frame [⟨W, 2560⟩] s.mem s₂.mem := by
    rw [m₂, hM₂]
    have c : ∀ {d : Nat}, d + 8 ≤ 2560 → (⟨W, 2560⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun h => Offset.contains_base W h (by omega)
    exact (((((f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (c (by decide))).writeW (List.mem_singleton_self _) _ (c (by decide))).writeW
      (List.mem_singleton_self _) _ (c (by decide))).writeW (List.mem_singleton_self _) _ (c (by decide)))
  have a₁ : InRegions (s₂.rd ++ s₂.wr) (s₂.sp + BitVec.ofNat 64 (8 * 1)) 8 := by
    rw [rd₂, wr₂, sp₂]; exact in_off hargs (by decide) (by decide)
  have tl₂ : stackArg s₂ 1 = BitVec.ofNat 64 tl := by
    rw [← htl]
    simp only [stackArg, stackArgAddr, sp₂]
    refine f₂.readW (r := ⟨s.sp + BitVec.ofNat 64 (8 * 1), 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact hargsW.sub_left (Offset.sub_base _ (by decide))
  obtain ⟨_, run₃, rfl⟩ := ldrSp_ok (t := .x10) (s := s₂) (i := 1) (by decide) a₁
  rw [tl₂] at run₃
  simp only [Nat.reduceMul] at run₃
  rw [show ([Impl.AesGcm.AArch64.mov .x19 .x9, Impl.AesGcm.AArch64.mov .x20 .x0, Impl.AesGcm.AArch64.mov .x21 .x6,
        Impl.AesGcm.AArch64.mov .x22 .x1, Impl.AesGcm.AArch64.mov .x28 .x7, st .x19 nO .x2, st .x19 nlO .x3,
        st .x19 aadO .x4, st .x19 alenO .x5, .ldrSp .x10 8, st .x19 tlO .x10] : List Instr) ++ (lsetup ++ zero16 ckO) =
      [Impl.AesGcm.AArch64.mov .x19 .x9, Impl.AesGcm.AArch64.mov .x20 .x0, Impl.AesGcm.AArch64.mov .x21 .x6,
        Impl.AesGcm.AArch64.mov .x22 .x1, Impl.AesGcm.AArch64.mov .x28 .x7, st .x19 nO .x2, st .x19 nlO .x3,
        st .x19 aadO .x4, st .x19 alenO .x5] ++ ([.ldrSp .x10 8] ++ ([st .x19 tlO .x10] ++ (lsetup ++ zero16 ckO)))
      from rfl, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨_, run₃, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨s₄, run₄, h₄⟩ : ∃ s₄, runBlock isa [st .x19 tlO .x10] (s₂.write .x .x10 (BitVec.ofNat 64 tl)) = some s₄ ∧
      s₄ = { s₂.write .x .x10 (BitVec.ofNat 64 tl) with mem := M₂.writeW (W + BitVec.ofNat 64 248) (BitVec.ofNat 64 tl) } :=
    ⟨_, by orun [x19₂, wr₂, m₂, show InRegions s.wr (W + BitVec.ofNat 64 248) 8 from in_off P.w (by decide) (by decide)],
      rfl⟩
  refine WP.of_runBlock ⟨_, run₄, ?_⟩
  have g₄ : ∀ r, r ≠ .x10 → s₄.gpr r = s₂.gpr r := fun r hr => by rw [h₄]; simp [gpr_write, hr]
  have m₄ : s₄.mem = M₂.writeW (W + BitVec.ofNat 64 248) (BitVec.ofNat 64 tl) := by rw [h₄]
  have sp₄ : s₄.sp = s.sp := by rw [h₄]; exact sp₂
  have rd₄ : s₄.rd = s.rd := by rw [h₄]; exact rd₂
  have wr₄ : s₄.wr = s.wr := by rw [h₄]; exact wr₂
  have E₄ : Env K W D R n s.sp s₄ := ⟨by rw [g₄ _ (by decide), x19₂], by rw [g₄ _ (by decide), x20₂],
    by rw [g₄ _ (by decide), x21₂], by rw [g₄ _ (by decide), x22₂], by rw [g₄ _ (by decide), x28₂], sp₄,
    P.of_eq rd₄ wr₄⟩
  -- `L_$`, `L_0` and the checksum
  obtain ⟨s₅, run₅, B₅⟩ := dbl_ok (s := s₄) (b := .x20) (a := 240) (d := ldO) (by decide) (by decide) E₄.x19 E₄.x20
    (by decide) (E₄.perm.kR (by decide)) (E₄.perm.kR (by decide)) (E₄.perm.wW (by decide)) (E₄.perm.wW (by decide))
  have E₅ := E₄.others B₅.gpr B₅.sp B₅.rd B₅.wr
  obtain ⟨s₆, run₆, B₆⟩ := dbl_ok (s := s₅) (b := .x19) (a := ldO) (d := l0O) (by decide) (by decide) E₅.x19 E₅.x19
    (by decide) (E₅.perm.wR (by decide)) (E₅.perm.wR (by decide)) (E₅.perm.wW (by decide)) (E₅.perm.wW (by decide))
  have E₆ := E₅.others B₆.gpr B₆.sp B₆.rd B₆.wr
  obtain ⟨s₇, run₇, B₇⟩ := zero16_ok (s := s₆) (d := ckO) (by decide) E₆.x19 (E₆.perm.wW (by decide))
    (E₆.perm.wW (by decide))
  refine WP.of_runBlock ⟨s₇, by rw [lsetup, runBlock_append, runBlock_append, run₅, Option.bind_some, run₆,
    Option.bind_some, run₇], ?_⟩
  have fr₇ : Frame [⟨W + BitVec.ofNat 64 32, 64⟩] s₄.mem s₇.mem :=
    ((B₅.frame.sub fun r hr => ?_).trans (B₆.frame.sub fun r hr => ?_)).trans (B₇.frame.sub fun r hr => ?_)
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  have k₇ : ∀ {d : Nat}, 96 ≤ d → d + 8 ≤ 2560 →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ =>
    fr₇.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega)) h₂ (by decide)) (by decide)
  have k₄ : ∀ {d : Nat}, (d + 8 ≤ 248 ∨ 288 ≤ d) → d + 8 ≤ 2560 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = M₁.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [m₄, readW_writeW_off _ (by omega) (by omega) (by decide), hM₂,
      readW_writeW_off _ (by omega) (by omega) (by decide), readW_writeW_off _ (by omega) (by omega) (by decide),
      readW_writeW_off _ (by omega) (by omega) (by decide), readW_writeW_off _ (by omega) (by omega) (by decide)]
  have l₄ : blockAtMem s₄.mem (K + BitVec.ofNat 64 240) = ctxLstar s.mem K := by
    have f₄ : Frame [⟨W, 2560⟩] s.mem s₄.mem := by
      rw [m₄, ← m₂]; exact f₂.writeW (List.mem_singleton_self _) (BitVec.ofNat 64 tl) (Offset.contains_base W (d := 248) (n := 8) (k := 2560) (by decide) (by decide))
    rw [blockAtMem_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_left (Lay.kSub (by decide)))]
    rfl
  refine ⟨E₆.others B₇.gpr B₇.sp B₇.rd B₇.wr, ⟨?_, ?_, ?_, ?_, ?_⟩, fun p hp => ?_, ?_, ?_, B₇.val, ?_,
    by rw [B₇.rd, B₆.rd, B₅.rd, rd₄], by rw [B₇.wr, B₆.wr, B₅.wr, wr₄]⟩
  · rw [k₇ (by decide) (by decide), m₄]; exact Mem.readW_writeW_self64 ..
  · rw [k₇ (by decide) (by decide), m₄, readW_writeW_off _ (by decide) (by decide) (by decide), hM₂,
      readW_writeW_off _ (by decide) (by decide) (by decide)]; exact Mem.readW_writeW_self64 ..
  · rw [k₇ (by decide) (by decide), m₄, readW_writeW_off _ (by decide) (by decide) (by decide), hM₂]
    exact Mem.readW_writeW_self64 ..
  · rw [k₇ (by decide) (by decide), m₄, readW_writeW_off _ (by decide) (by decide) (by decide), hM₂,
      readW_writeW_off _ (by decide) (by decide) (by decide), readW_writeW_off _ (by decide) (by decide) (by decide),
      readW_writeW_off _ (by decide) (by decide) (by decide)]; exact Mem.readW_writeW_self64 ..
  · rw [k₇ (by decide) (by decide), m₄, readW_writeW_off _ (by decide) (by decide) (by decide), hM₂,
      readW_writeW_off _ (by decide) (by decide) (by decide), readW_writeW_off _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 ..
  · have hp' := saved_in p hp
    rw [← hsv₁ p hp, k₇ (by omega) (by omega), k₄ (.inl (by omega)) (by omega)]
  · rw [blockAtMem_frame B₇.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      blockAtMem_frame B₆.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      B₅.val, l₄]
    rfl
  · rw [blockAtMem_frame B₇.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      B₆.val, B₅.val, l₄]
    rfl
  · have c : ∀ {d : Nat}, 32 ≤ d → d + 8 ≤ 288 → (entryR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
    have f₄ : Frame [entryR W] s.mem s₄.mem := by
      rw [m₄, hM₂]
      exact (((((f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub W (by decide) (by decide)⟩).writeW
        (List.mem_singleton_self _) N (c (d := 272) (by decide) (by decide))).writeW (List.mem_singleton_self _)
        (BitVec.ofNat 64 nl) (c (d := 280) (by decide) (by decide))).writeW (List.mem_singleton_self _) A
        (c (d := 256) (by decide) (by decide))).writeW (List.mem_singleton_self _) (BitVec.ofNat 64 al)
        (c (d := 264) (by decide) (by decide))).writeW (List.mem_singleton_self _) (BitVec.ofNat 64 tl)
        (c (d := 248) (by decide) (by decide))
    exact f₄.trans (fr₇.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub W (by decide) (by decide)⟩)

end VG.Proof.AesOcb.AArch64