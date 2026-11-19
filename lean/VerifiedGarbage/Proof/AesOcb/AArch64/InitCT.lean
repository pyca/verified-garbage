module

public import VerifiedGarbage.Proof.AesOcb.AArch64.Args
public import VerifiedGarbage.Proof.AesOcb.AArch64.Env
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesOcb.AArch64.Args
meta import VerifiedGarbage.Proof.AesOcb.AArch64.Env
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Impl.AesOcb.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ocb.Bytes
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Env
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesOcb.AArch64.Body
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Spec.Ocb
public import VerifiedGarbage.Proof.AesOcb.AArch64.LNtz
import VerifiedGarbage.Proof.Ocb.State
public import VerifiedGarbage.Proof.AesOcb.AArch64.Hash
public import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesOcb.AArch64.Body
meta import VerifiedGarbage.Proof.Framework.AArch64.Spill
meta import VerifiedGarbage.Spec.Ocb
meta import VerifiedGarbage.Proof.AesOcb.AArch64.LNtz
meta import VerifiedGarbage.Proof.Ocb.State
meta import VerifiedGarbage.Proof.AesOcb.AArch64.Hash
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `AesOcb.AArch64.Seal`, which this module and modules that import it used -/

section

/-! ### `AesOcb.AArch64.Entry`, which only this module used -/

section

/-!
# AES-OCB on AArch64: the entry (`entry`)

Untrusted: everything here is checked by Lean. `entry` reads `W` from the
stack, saves our caller's registers at `W + savO` (`Spill.save_wp`), keeps
the data and its length in `x21` and `x28` and the other arguments in `W`,
computes `L_$` and `L_0` from `L_*` and zeroes the checksum (`entry_ok`).
-/

@[expose] public section

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
  obtain h₁ : (8 * i) % 8 = 0 := by omega_using []
  obtain h₂ : 8 * i < 32768 := by omega_using [hi]
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
    {nl al tl : Nat} (hW : stackArg s 2 = W) (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (hargs : Covers [⟨s.sp, 24⟩] (s.rd ++ s.wr)) (hargsW : (⟨s.sp, 24⟩ : Region).Disjoint ⟨W, 2560⟩)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa (.block entry) s (EntryPost K W D R n N A nl al tl s) := by
  have a₀ : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 2)) 8 := in_off hargs (by decide) (by decide)
  obtain ⟨_, run₀, rfl⟩ := ldrSp_ok (t := .x9) (s := s) (i := 2) (by decide) a₀
  rw [hW] at run₀
  simp only [Nat.reduceMul] at run₀
  have x9₀ : (s.write .x .x9 W).gpr .x9 = W := by simp [gpr_write]
  have hin : ∀ p ∈ saved, InRegions (s.write .x .x9 W).wr ((s.write .x .x9 W).gpr .x9 + BitVec.ofNat 64 p.2) 8 :=
    fun p hp => by
      rw [x9₀, wr_write]; exact in_off P.w (by have := saved_in p hp; omega_using [this]) (by decide)
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
      fun h => Offset.contains_base W h (by omega_using [h])
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
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega_using [h₁])) h₂ (by decide)) (by decide)
  have k₄ : ∀ {d : Nat}, (d + 8 ≤ 248 ∨ 288 ≤ d) → d + 8 ≤ 2560 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = M₁.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [m₄, readW_writeW_off _ (by omega_using [h₁]) (by omega_using [h₂]) (by decide), hM₂,
      readW_writeW_off _ (by omega_using [h₁]) (by omega_using [h₂]) (by decide), readW_writeW_off _ (by omega_using [h₁]) (by omega_using [h₂]) (by decide),
      readW_writeW_off _ (by omega_using [h₁]) (by omega_using [h₂]) (by decide), readW_writeW_off _ (by omega_using [h₁]) (by omega_using [h₂]) (by decide)]
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
    rw [← hsv₁ p hp, k₇ (by omega_using [hp']) (by omega_using [hp']), k₄ (.inl (by omega_using [hp'])) (by omega_using [hp'])]
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
      fun h₁ h₂ => Offset.contains W h₁ (by omega_using [h₂]) (by decide)
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

end

end


/-!
# AES-OCB on AArch64: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. The preconditions `sealPreA`
and `openPreA` give the facts the proofs use about the arguments (`Args`,
`sealArgs_of`, `openArgs_of`). `seal` is `front`: `entry`, `Offset_0`
(`nonce`), `HASH` (`hash`), the data (`body`) and the tag at `W` (`tag`);
then the copy of the tag to `tag`, whose address is on the stack
(`tagOut`), and `restore` (`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (covers_of_mem covers_left)

/-- What `seal` and `open` are given: the key context at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`) and the
working space at `W`. -/
structure Args (s : State) (K W N A D : Addr) (R nl al n tl : Nat) (T : Addr) : Prop where
  lay : Lay K W
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf W s N nl
  aad : Buf W s A al
  data : DBuf K W s D n
  tag : Buf W s T tl
  nd : (⟨N, nl⟩ : Region).Disjoint ⟨D, n⟩
  td : (⟨T, tl⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  n1 : 1 ≤ nl
  n15 : nl ≤ 15
  t1 : 1 ≤ tl
  t16 : tl ≤ 16
  args : Covers [⟨s.sp, 24⟩] (s.rd ++ s.wr)
  argsW : (⟨s.sp, 24⟩ : Region).Disjoint ⟨W, 2560⟩
  argsD : (⟨s.sp, 24⟩ : Region).Disjoint ⟨D, n⟩

/-- `Args` from the facts both preconditions give, for a state that may
read the key context, the nonce, the associated data, the arguments on the
stack and the tag, and write the data and `W`. -/
theorem args_of {s : State} (h : oneFacts s)
    (mrd : ∀ r ∈ [aCtx s, aNonce s, aAad s, args s 3, aTag s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [aData s, aWork s], Covers [r] s.wr) :
    Args s (s.gpr .x0) (stackArg s 2) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (s.gpr .x1).toNat (s.gpr .x3).toNat
      (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat (stackArg s 0) := by
  sig_split h
  rename_i d3 d4 d5 d6 d7 d8 t1 t2 d9 d10 d11 b12 b13 b14 b15 bt b16 _ hR
  have hv := h
  clear h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  obtain sp0 : stackArgAddr s 0 = s.sp := by simp [stackArgAddr]
  obtain ha := mrd (args s 3) (by simp)
  simp only [args, sp0] at ha d10 d11
  exact {
    lay := ⟨b12, b16, d4⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), BitVec.isLt _, b13, d6⟩
    aad := ⟨mrd _ (by simp), BitVec.isLt _, b14, d8⟩
    data := ⟨⟨covers_left (mwr _ (by simp)), BitVec.isLt _, b15, d9⟩, mwr _ (by simp), d3⟩
    tag := ⟨mrd _ (by simp), BitVec.isLt _, bt, t2⟩
    nd := d5
    ad := d7
    td := t1
    n1 := hn1
    n15 := hn15
    t1 := ht1
    t16 := ht16
    args := ha
    argsW := d11.symm
    argsD := d10.symm }

theorem sealArgs_of {s : State} (h : sealPreA s) :
    Args s (s.gpr .x0) (stackArg s 2) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (s.gpr .x1).toNat (s.gpr .x3).toNat
      (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨hrd, hwr, -, -, -, -, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_of_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_of_mem (by simp))

theorem openArgs_of {s : State} (h : openPreA s) :
    Args s (s.gpr .x0) (stackArg s 2) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (s.gpr .x1).toNat (s.gpr .x3).toNat
      (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨hrd, hwr, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_of_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_of_mem (by simp))

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-! ## Frames -/

/-- A frame within `W`. -/
theorem frameW {W : Addr} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r ⟨W, 2560⟩) : Frame [⟨W, 2560⟩] m m' :=
  h.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩

theorem entryR_W (W : Addr) : ∀ r ∈ [entryR W], Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)

theorem nonceR_W (W : Addr) : ∀ r ∈ nonceR W, Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem hashR_W (W : Addr) : ∀ r ∈ hashR W, Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact Lay.wSub (by decide)

/-- A buffer apart from `W`, after a frame within `W`. -/
theorem bytesAt_W {W P : Addr} {k : Nat} (hP : (⟨P, k⟩ : Region).Disjoint ⟨W, 2560⟩) (hk : k < 2 ^ 64) {m m' : Mem}
    (h : Frame [⟨W, 2560⟩] m m') : bytesAt m' P k = bytesAt m P k :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hP) (by omega_arith)

theorem ctxCiph_W {K W : Addr} (L : Lay K W) {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [bytesAt_W (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega_arith) h]

theorem ctxInv_W {K W : Addr} (L : Lay K W) {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : Spec.Ocb.ctxInv m' K R = Spec.Ocb.ctxInv m K R := by
  unfold Spec.Ocb.ctxInv
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [bytesAt_W (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega_arith) h]

theorem ctxLstar_W {K W : Addr} (L : Lay K W) {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') :
    ctxLstar m' K = ctxLstar m K := by
  show blockAtMem m' (K + BitVec.ofNat 64 240) = blockAtMem m (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_left (Lay.kSub (by decide))

/-- What `tag d` writes, within the parts the pieces write. -/
theorem tagR_mut {W D : Addr} {n d : Nat} (hd : d + 16 ≤ 160) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩] m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA hd
  · exact in_mutB (by decide) (by decide)

/-- The saved registers, after a frame within the parts the pieces write. -/
theorem saved_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {g : Reg → BitVec 64} {m m' : Mem} (h : Spill.Saved W g saved m) (hf : Frame (mutR W D n) m m') :
    Spill.Saved W g saved m' :=
  Spill.Saved.frame_in h saved_in hf (kept_mut L hD (by decide))

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (blockAtMem m p)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega_arith,
    Proof.Ocb.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

/-! ## Before the data -/

/-- What the pieces before the data leave: the offset, the checksum, `L_$`,
`L_0` and `HASH`. -/
structure Pre (K W D : Addr) (R n : Nat) (N A : Addr) (nl al tl : Nat) (s s' : State) : Prop where
  env : Env K W D R n s.sp s'
  frame : Frame [⟨W, 2560⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  slots : Slots W N A nl al tl s'.mem
  saved : Spill.Saved W s.gpr saved s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  ck : blockAtMem s'.mem (W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K)
  l0 : blockAtMem s'.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0
  sum : blockAtMem s'.mem (W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al)

/-- What `HASH` needs, after `entry` and `nonce`. -/
theorem hctx_of {s : State} {K W N A D : Addr} {R nl al n tl : Nat} {T : Addr} (Ar : Args s K W N A D R nl al n tl T)
    {s₁ s₂ : State} (P₁ : EntryPost K W D R n N A nl al tl s s₁) {SP : Addr} {o : Block}
    (P₂ : NonceOk K W D R n SP o s₁ s₂) :
    HCtx K W D n R (ctxCiph s.mem K R) (ctxLstar s.mem K) A (bytesAt s.mem A al) s₂ :=
  have L := Ar.lay
  have F₁ : Frame [⟨W, 2560⟩] s.mem s₁.mem := frameW P₁.frame (entryR_W W)
  have F₂ : Frame [⟨W, 2560⟩] s₁.mem s₂.mem := frameW P₂.frame (nonceR_W W)
  { lay := L, rounds := Ar.rounds
    ciph := by rw [ctxCiph_W L F₂ Ar.rounds, ctxCiph_W L F₁ Ar.rounds]
    lstar := by rw [ctxLstar_W L F₂, ctxLstar_W L F₁]
    buf := by rw [length_bytesAt]; exact Ar.aad.of_eq (P₂.rd.trans P₁.rd) (P₂.wr.trans P₁.wr)
    aad := by rw [length_bytesAt, bytesAt_W Ar.aad.w Ar.aad.lt F₂, bytesAt_W Ar.aad.w Ar.aad.lt F₁]
    ad := by rw [length_bytesAt]; exact Ar.ad
    kd := Ar.data.k, dw := Ar.data.w }

/-- `entry`, `nonce` and `hash`. -/
theorem pre_wp' (v : BlocksImpl) {s : State} {K W N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W N A D R nl al n tl T) (hW : stackArg s 2 = W)
    (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa (.seq (.block entry) (.seq (nonce (callees v)) (hash (callees v)))) s
      (Pre K W D R n N A nl al tl s) := by
  have L := Ar.lay
  refine WP.seq (WP.mono (entry_ok L Ar.perm hW htl Ar.args Ar.argsW h0 h1 h2 h3 h4 h5 h6 h7) fun s₁ P₁ => ?_)
  obtain F₁ : Frame [⟨W, 2560⟩] s.mem s₁.mem := frameW P₁.frame (entryR_W W)
  -- `Offset_0`.
  refine WP.seq (WP.mono (nonce_ok v L P₁.env Ar.rounds P₁.slots.nonce P₁.slots.nlen P₁.slots.tl
    Ar.n1 Ar.n15 (by have := Ar.t16; omega_arith) (Ar.nonce.of_eq P₁.rd P₁.wr) Ar.data.k) fun s₂ P₂ => ?_)
  obtain F₂ : Frame [⟨W, 2560⟩] s₁.mem s₂.mem := frameW P₂.frame (nonceR_W W)
  obtain S₂ := Slots.of_mut L Ar.data.w (nonceR_mut (D := D) (n := n) P₂.frame) P₁.slots
  -- `HASH`.
  obtain C := hctx_of Ar P₁ P₂
  refine WP.mono (hash_ok v C P₂.env S₂.aad (by rw [length_bytesAt]; exact S₂.alen)
    (by rw [P₂.keep (by decide) (by decide), P₁.l0])) fun s₃ ⟨E₃, F₃, sum₃, rd₃, wr₃⟩ => ?_
  obtain F₃' : Frame [⟨W, 2560⟩] s₂.mem s₃.mem := frameW F₃ (hashR_W W)
  obtain k₃ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (160 ≤ d ∧ d + 16 ≤ 384)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (W + BitVec.ofNat 64 d) := fun {d} hd =>
    blockAtMem_frame F₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  refine ⟨E₃, F₁.trans (F₂.trans F₃'), by rw [rd₃, P₂.rd, P₁.rd], by rw [wr₃, P₂.wr, P₁.wr],
    Slots.of_mut L Ar.data.w (hashR_mut F₃) S₂,
    saved_mut L Ar.data.w (saved_mut L Ar.data.w P₁.saved (nonceR_mut P₂.frame)) (hashR_mut F₃), ?_, ?_, ?_, ?_,
    ?_, by rw [sum₃]⟩
  · rw [k₃ (d := ofsO) (by decide), P₂.ofs, ctxCiph_W L F₁ Ar.rounds, bytesAt_W Ar.nonce.w Ar.nonce.lt F₁]
  · rw [k₃ (d := o0O) (by decide), P₂.o0, ctxCiph_W L F₁ Ar.rounds, bytesAt_W Ar.nonce.w Ar.nonce.lt F₁]
  · rw [k₃ (d := ckO) (by decide), P₂.keep (by decide) (by decide), P₁.ck]
  · rw [k₃ (d := ldO) (by decide), P₂.keep (by decide) (by decide), P₁.ld]
  · rw [k₃ (d := l0O) (by decide), P₂.keep (by decide) (by decide), P₁.l0]

/-- `entry`, `nonce` and `hash`, then `k`. -/
theorem pre_wp (v : BlocksImpl) {s : State} {K W N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W N A D R nl al n tl T) (hW : stackArg s 2 = W)
    (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n)
    {k : Prog isa} {Q : State → Prop} (hk : ∀ s', Pre K W D R n N A nl al tl s s' → WP isa k s' Q) :
    WP isa (.seq (.block entry) (.seq (nonce (callees v)) (.seq (hash (callees v)) k))) s Q := by
  exact WP.seq (WP.mono (WP.seq_iff.mp (pre_wp' v Ar hW htl h0 h1 h2 h3 h4 h5 h6 h7)) fun _ h₁ =>
    WP.assoc (WP.seq (WP.mono h₁ hk)))

/-- `body`'s frame misses a block of `W` outside the offset, the checksum and
`[96, 144)`. -/
theorem body_keep {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {m m' : Mem}
    (h : Frame (bodyR W D n) m m') {d : Nat} (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (144 ≤ d ∧ d + 16 ≤ 512)) :
    blockAtMem m' (W + BitVec.ofNat 64 d) = blockAtMem m (W + BitVec.ofNat 64 d) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · exact (hD.sub_right (Lay.wSub (by omega_arith))).symm

/-- `tag d`'s frame misses the data. -/
theorem tag_data {W D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hd : d + 16 ≤ 512) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩],
      (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact hD.sub_right (Lay.wSub (by first | omega_arith | (simp only [tmpO]; omega_arith)))

/-- The registers `restore` restores are our caller's. -/
theorem restore_abi {s t t' : State} (h : Spill.Restored s.gpr saved t t') (hsp : t.sp = s.sp) : GprAbi s t' := by
  refine ⟨fun r hr => ?_, by rw [h.sp, hsp]⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((by decide : ∀ r ∈ preserved, r ∈ saved.map Prod.fst) r hr)
  exact h.gpr p hp

/-- `restore`. -/
theorem restore_wp' {K W D : Addr} {R n : Nat} {SP : Addr} {t : State} (E : Env K W D R n SP t)
    {g : Reg → BitVec 64} (hsv : Spill.Saved W g saved t.mem) :
    WP isa (.block restore) t (Spill.Restored g saved t) := by
  rw [restore_eq]
  exact Spill.restore_wp E.x19 saved_fits.1 (by decide) (fun p hp => E.perm.wR (by have := saved_in p hp; omega_arith))
    hsv

/-- The arguments on the stack, apart from `W` and the data, are kept by a
frame within them. -/
theorem args_kept {W D : Addr} {n : Nat} {SP : Addr} (hW : (⟨SP, 24⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : (⟨SP, 24⟩ : Region).Disjoint ⟨D, n⟩) {m m' : Mem} (h : Frame [⟨W, 2560⟩, ⟨D, n⟩] m m') {i : Nat}
    (hi : i < 3) : m'.readW (SP + BitVec.ofNat 64 (8 * i)) 64 = m.readW (SP + BitVec.ofNat 64 (8 * i)) 64 :=
  h.readW (r := ⟨SP + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hW.sub_left (Offset.sub_base _ (by omega_arith))
    · exact hD.sub_left (Offset.sub_base _ (by omega_arith))) (by decide)

/-- The frame of `front`, from those of its pieces. -/
theorem front_frame {W D : Addr} {n : Nat} {m₀ m₃ m₄ m₅ : Mem} {d : Nat} (hd : d + 16 ≤ 160)
    (P : Frame [⟨W, 2560⟩] m₀ m₃) (B : Frame (bodyR W D n) m₃ m₄)
    (T : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩] m₄ m₅) :
    Frame [⟨W, 2560⟩, ⟨D, n⟩] m₀ m₅ :=
  have M : Frame (mutR W D n) m₃ m₅ := (bodyR_mut B).trans (tagR_mut hd T)
  (P.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans (M.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩)

/-- The first block of `tagOut`: the tag's address from the stack, `W` and
the tag length. -/
theorem tagOutHead_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) {T : Addr}
    {tl : Nat} (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) (hT : stackArg s 0 = T)
    (ha : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 0)) 8) :
    ∃ s₁, runBlock isa [.ldrSp .x11 0, Impl.AesGcm.AArch64.mov .x12 .x19, ld .x13 .x19 tlO] s = some s₁ ∧
      s₁.gpr .x11 = T ∧ s₁.gpr .x12 = W ∧ s₁.gpr .x13 = BitVec.ofNat 64 tl ∧ s₁.mem = s.mem ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  obtain ⟨_, run₀, rfl⟩ := ldrSp_ok (t := .x11) (s := s) (i := 0) (by decide) ha
  simp only [Nat.reduceMul] at run₀
  obtain r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 248) 8 := E.perm.wR (by decide)
  obtain h19 : (s.write .x .x11 (stackArg s 0)).gpr .x19 = W := by simp [gpr_write, E.x19]
  have htl' : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl := htl
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [Impl.AesGcm.AArch64.mov .x12 .x19, ld .x13 .x19 tlO] (s.write .x .x11 (stackArg s 0)) = some s₁ ∧
      s₁.gpr .x11 = stackArg s 0 ∧ s₁.gpr .x12 = W ∧ s₁.gpr .x13 = BitVec.ofNat 64 tl ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [E.x19, r₀, htl'], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, htl']
    · simp only [Proof.AesGcm.AArch64.loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1, hr.2.2.1]
    all_goals rfl
  exact ⟨s₁, by rw [show ([.ldrSp .x11 0, Impl.AesGcm.AArch64.mov .x12 .x19, ld .x13 .x19 tlO] : List Instr) =
    [.ldrSp .x11 0] ++ [Impl.AesGcm.AArch64.mov .x12 .x19, ld .x13 .x19 tlO] from rfl, runBlock_append, run₀,
    Option.bind_some, run₁], by rw [x11₁, hT], x12₁, x13₁, m₁, g₁, sp₁, rd₁, wr₁⟩

/-- The first block of `recv`: `W`, the tag's address from the stack and the
tag length. -/
theorem recvHead_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) {T : Addr}
    {tl : Nat} (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) (hT : stackArg s 0 = T)
    (ha : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 0)) 8) :
    ∃ s₁, runBlock isa [Impl.AesGcm.AArch64.mov .x11 .x19, .ldrSp .x12 0, ld .x13 .x19 tlO] s = some s₁ ∧
      s₁.gpr .x11 = W ∧ s₁.gpr .x12 = T ∧ s₁.gpr .x13 = BitVec.ofNat 64 tl ∧ s₁.mem = s.mem ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  obtain ⟨s₀, run₀, x11₀, g₀, m₀, sp₀, rd₀, wr₀⟩ : ∃ s₀, runBlock isa [Impl.AesGcm.AArch64.mov .x11 .x19] s = some s₀ ∧
      s₀.gpr .x11 = W ∧ (∀ r, r ≠ .x11 → s₀.gpr r = s.gpr r) ∧ s₀.mem = s.mem ∧ s₀.sp = s.sp ∧ s₀.rd = s.rd ∧
      s₀.wr = s.wr := by
    refine ⟨_, by orun [E.x19], ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, E.x19]
    · simp [gpr_write, hr]
    all_goals rfl
  obtain ha₀ : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 (8 * 0)) 8 := by rw [rd₀, wr₀, sp₀]; exact ha
  obtain ⟨_, run₁, rfl⟩ := ldrSp_ok (t := .x12) (s := s₀) (i := 0) (by decide) ha₀
  simp only [Nat.reduceMul] at run₁
  obtain hT₀ : stackArg s₀ 0 = T := by rw [← hT]; simp only [stackArg, stackArgAddr, m₀, sp₀]
  obtain r₀ : InRegions (s₀.rd ++ s₀.wr) (W + BitVec.ofNat 64 248) 8 := by
    rw [rd₀, wr₀]; exact E.perm.wR (by decide)
  obtain h19 : s₀.gpr .x19 = W := by rw [g₀ .x19 (by decide), E.x19]
  obtain htl' : s₀.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl := by rw [m₀]; exact htl
  obtain ⟨s₁, run₂, x11₁, x12₁, x13₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [ld .x13 .x19 tlO]
      (s₀.write .x .x12 (stackArg s₀ 0)) = some s₁ ∧
      s₁.gpr .x11 = W ∧ s₁.gpr .x12 = T ∧ s₁.gpr .x13 = BitVec.ofNat 64 tl ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [h19, r₀, htl'], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, x11₀]
    · simp [gpr_write, hT₀]
    · simp [gpr_write, h19, htl']
    · simp only [Proof.AesGcm.AArch64.loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, g₀ r hr.1]
    · simp [mem_write, m₀]
    · simp [sp_write, sp₀]
    · simp [rd_write, rd₀]
    · simp [wr_write, wr₀]
  exact ⟨s₁, by rw [show ([Impl.AesGcm.AArch64.mov .x11 .x19, .ldrSp .x12 0, ld .x13 .x19 tlO] : List Instr) =
    [Impl.AesGcm.AArch64.mov .x11 .x19] ++ ([.ldrSp .x12 0] ++ [ld .x13 .x19 tlO]) from rfl, runBlock_append,
    run₀, Option.bind_some, runBlock_append, run₁, Option.bind_some, run₂], x11₁, x12₁, x13₁, m₁, g₁, sp₁, rd₁,
    wr₁⟩

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`, which the
state may write. -/
theorem tagOut_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) {T : Addr}
    {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hT : stackArg s 0 = T) (ha : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 0)) 8)
    (hTw : Covers [⟨T, tl⟩] s.wr) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa tagOut s fun t => t.mem = writeBytes s.mem T (bytesAt s.mem W tl) ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := tagOutHead_ok E htl hT ha
  unfold tagOut
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (Proof.AesGcm.AArch64.copyLoop_ok s₁ x12₁ x11₁ x13₁ (by omega_arith)
    ⟨by omega_arith, by
      rw [rd₁, wr₁]
      exact covers_left fun a m ⟨r, hr, hc⟩ => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.perm.w a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_arith⟩,
      by rw [wr₁]; exact hTw,
      (hTW.sub_right (Region.sub_prefix (by omega_arith))).symm⟩)
    fun t ⟨m, _, _, g, sp, rd, wr⟩ => ⟨by rw [m, m₁], fun r hr => by rw [g r hr, g₁ r hr], by rw [sp, sp₁],
      by rw [rd, rd₁], by rw [wr, wr₁]⟩

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' (v : BlocksImpl) {s : State} {K W N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W N A D R nl al n tl T) (hTw : Covers [⟨T, tl⟩] s.wr) (hW : stackArg s 2 = W)
    (hT : stackArg s 0 = T) (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa («seal» (callees v)) s fun s' => GprAbi s s' ∧
      Spec.Ocb.encryptWith (ctxCiph s.mem K R) (ctxLstar s.mem K) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
        (bytesAt s.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem T tl) := by
  have L := Ar.lay
  unfold «seal» front
  refine WP.seq (pre_wp v Ar hW htl h0 h1 h2 h3 h4 h5 h6 h7 fun s₃ P₃ => ?_)
  obtain hD₃ : DBuf K W s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  obtain c₃ : ctxCiph s₃.mem K R = ctxCiph s.mem K R := ctxCiph_W L P₃.frame Ar.rounds
  obtain l₃ : ctxLstar s₃.mem K = ctxLstar s.mem K := ctxLstar_W L P₃.frame
  obtain d₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := bytesAt_W Ar.data.w Ar.data.lt P₃.frame
  refine WP.seq (WP.mono (bodySeal_ok v L P₃.env Ar.rounds hD₃ P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, l₃]))
    fun s₄ B => ?_)
  obtain F₄ : Frame (mutR W D n) s₃.mem s₄.mem := bodyR_mut B.frame
  obtain cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans c₃
  obtain ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  obtain sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag.
  refine WP.mono (tag_ok v L B.env Ar.rounds (.inl rfl)) fun s₅ T₅ => ?_
  obtain F₅ : Frame (mutR W D n) s₄.mem s₅.mem := tagR_mut (by decide) T₅.frame
  obtain S₅ := Slots.of_mut L Ar.data.w (F₄.trans F₅) P₃.slots
  obtain sv₅ := saved_mut L Ar.data.w (saved_mut L Ar.data.w P₃.saved F₄) F₅
  obtain Ff := front_frame (by decide) P₃.frame B.frame T₅.frame
  have sp₅ : s₅.sp = s.sp := T₅.env.sp
  -- The copy of the tag.
  obtain hT₅ : stackArg s₅ 0 = T := by
    rw [← hT]; simp only [stackArg, stackArgAddr, sp₅]
    exact args_kept Ar.argsW Ar.argsD Ff (i := 0) (by decide)
  obtain ha₅ : InRegions (s₅.rd ++ s₅.wr) (s₅.sp + BitVec.ofNat 64 (8 * 0)) 8 := by
    rw [T₅.rd, B.rd, P₃.rd, T₅.wr, B.wr, P₃.wr, sp₅]
    exact Proof.AesGcm.AArch64.in_off Ar.args (by decide) (by decide)
  refine WP.seq (WP.mono (tagOut_ok T₅.env Ar.t1 Ar.t16 S₅.tl hT₅ ha₅
    (by rw [T₅.wr, B.wr, P₃.wr]; exact hTw) Ar.tag.w) fun s₆ ⟨m₆, g₆, sp₆, rd₆, wr₆⟩ => ?_)
  obtain E₆ := T₅.env.others g₆ sp₆ rd₆ wr₆
  obtain F₆ : Frame [⟨T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  obtain sv₆ : Spill.Saved W s.gpr saved s₆.mem :=
    Spill.Saved.frame_in sv₅ saved_in F₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Ar.tag.w.sub_right (Lay.wSub (by decide))).symm
  -- `restore`.
  refine WP.mono (restore_wp' E₆ sv₆) fun s₇ Rs => ⟨restore_abi Rs E₆.sp, ?_⟩
  have hout := B.out
  rw [c₃, l₃, d₃] at hout
  have hofs := B.ofs
  rw [l₃] at hofs
  have hck := B.ck
  rw [d₃] at hck
  have hn := Ar.data.lt
  have ht := Ar.tag.lt
  obtain d₇ : bytesAt s₇.mem D n = bytesAt s₄.mem D n := by
    rw [Rs.mem, Proof.Cmac.bytesAt_frame F₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by omega_arith)]
    exact Proof.Cmac.bytesAt_frame T₅.frame (tag_data Ar.data.w (by decide)) (by omega_arith)
  have tv := T₅.val
  rw [show W + BitVec.ofNat 64 tagO = W from BitVec.add_zero W] at tv
  obtain t₇ : bytesAt s₇.mem T tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem W)).take tl := by
    rw [Rs.mem, m₆, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) ht, length_bytesAt,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, bytesAt_take_block _ _ Ar.t16]
  rw [Proof.Ocb.encryptWith_eq, d₇, hout, t₇, tv, hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega_arith
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega_arith
    simp only [h', hr, ↓reduceIte]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp (v : BlocksImpl) {s : State} (h : sealAArch64.pre s) :
    WP isa («seal» (callees v)) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' :=
  seal_wp' v (sealArgs_of h) (covers_of_mem (by rw [h.2.1]; simp)) rfl rfl (ofNat_toNat64 _).symm rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.AArch64

end

end

/-! ### `AesOcb.AArch64.Init`, which this module and modules that import it used -/

section

/-!
# AES-OCB on AArch64: `vg_aes_ocb_init`

Untrusted: everything here is checked by Lean. `init` saves our caller's
registers in the scratch buffer, expands the key into the key context
(`vg_aes_expand_key_scratch`), enciphers a zero block at byte 240 of it in place,
for `L_*` (`vg_aes_encrypt_blocks`), and restores the registers
(`init_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (covers_of_mem covers_cons covers_prefix covers_off covers_left in_off KeyCall key_call)

/-- The rounds, as `lsr 2; add 6` computes them from the key length. -/
theorem rounds_of_len {L : Nat} (hL : L = 16 ∨ L = 24 ∨ L = 32) :
    BitVec.ofNat 64 L >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) := by
  rcases hL with rfl | rfl | rfl <;> decide

/-- What `vg_aes_ocb_init` is given: the key (`L` bytes at `K`), the key
context at `Ctx` and the scratch buffer at `W`. -/
structure IArgs (s : State) (K Ctx W : Addr) (L : Nat) : Prop where
  rd : s.rd = [⟨K, L⟩]
  wr : s.wr = [⟨Ctx, 256⟩, ⟨W, 2560⟩]
  kc : (⟨K, L⟩ : Region).Disjoint ⟨Ctx, 256⟩
  ks : (⟨K, L⟩ : Region).Disjoint ⟨W, 2560⟩
  cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩
  wc : Ctx.toNat + 256 ≤ 2 ^ 64
  ws : W.toNat + 2560 ≤ 2 ^ 64
  len : L = 16 ∨ L = 24 ∨ L = 32

theorem IArgs.of {s : State} (hp : initAArch64.pre s) :
    IArgs s (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h⟩ := hp
  ⟨a, b, c, d, e, f, g, h⟩

namespace IArgs

variable {s : State} {K Ctx W : Addr} {L : Nat} (Ar : IArgs s K Ctx W L)
include Ar

theorem pW : Covers [⟨W, 2560⟩] s.wr := by rw [Ar.wr]; exact covers_of_mem (by simp)
theorem pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [Ar.wr]; exact covers_of_mem (by simp)
theorem pK : Covers [⟨K, L⟩] (s.rd ++ s.wr) := by rw [Ar.rd]; exact covers_of_mem (by simp)

end IArgs

/-- The registers saved and the arguments of `vg_aes_expand_key_scratch`. -/
theorem init1_ok {s : State} {K Ctx W : Addr} {L : Nat} (Ar : IArgs s K Ctx W L) (h0 : s.gpr .x0 = K)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 L) (h2 : s.gpr .x2 = Ctx) (h3 : s.gpr .x3 = W) :
    WP isa (.block (save .x3 ++ [Impl.AesGcm.AArch64.mov .x19 .x3, Impl.AesGcm.AArch64.mov .x20 .x2,
        .lsr .x .x22 .x1 2, Impl.AesGcm.AArch64.ptr .x22 .x22 6, Impl.AesGcm.AArch64.ptr .x3 .x19 scrO])) s
      fun s₂ => s₂.gpr .x19 = W ∧ s₂.gpr .x20 = Ctx ∧
        s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
        KeyCall s₂ K Ctx (W + BitVec.ofNat 64 512) L ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr ∧
        Spill.Saved W s.gpr saved s₂.mem ∧ Frame [⟨W + BitVec.ofNat 64 160, 88⟩] s.mem s₂.mem := by
  have pW := Ar.pW
  have pC := Ar.pC
  have hin : ∀ p ∈ saved, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 p.2) 8 := fun p hp => by
    rw [h3]; exact in_off pW (by have := saved_in p hp; omega_using [this]) (by decide)
  rw [save_eq]
  refine WP.block_append_iff.mpr (WP.mono (Spill.save_wp saved_fits.1 hin) fun s₁ St => ?_)
  rw [h3] at St
  obtain ⟨s₂, run₂, x19₂, x20₂, x22₂, x3₂, x0₂, x1₂, x2₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [Impl.AesGcm.AArch64.mov .x19 .x3, Impl.AesGcm.AArch64.mov .x20 .x2, .lsr .x .x22 .x1 2,
        Impl.AesGcm.AArch64.ptr .x22 .x22 6, Impl.AesGcm.AArch64.ptr .x3 .x19 scrO] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = Ctx ∧ s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
      s₂.gpr .x3 = W + BitVec.ofNat 64 512 ∧ s₂.gpr .x0 = K ∧ s₂.gpr .x1 = BitVec.ofNat 64 L ∧
      s₂.gpr .x2 = Ctx ∧ s₂.sp = s.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by orun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, St.gpr, h3]
    · simp [gpr_write, St.gpr, h2]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, St.gpr, h1, BitVec.setWidth_eq]
      exact rounds_of_len Ar.len
    · simp [gpr_write, St.gpr, h3]
    · simp [gpr_write, St.gpr, h0]
    · simp [gpr_write, St.gpr, h1]
    · simp [gpr_write, St.gpr, h2]
    · simp only [sp_write]; exact St.sp
    · rfl
    · simp only [rd_write]; exact St.rd
    · simp only [wr_write]; exact St.wr
  refine WP.of_runBlock ⟨s₂, run₂, x19₂, x20₂, x22₂, ?_, sp₂, rd₂, wr₂, ?_, ?_⟩
  · refine ⟨x0₂, x1₂, x2₂, x3₂, Ar.len, Ar.kc.sub_right (Region.sub_prefix (by decide)),
      Ar.ks.sub_right (Lay.wSub (by decide)), (Ar.cs.sub_left (Region.sub_prefix (by decide))).sub_right
        (Lay.wSub (by decide)), ?_, ?_⟩
    · rw [rd₂, wr₂]
      exact covers_cons Ar.pK (covers_left (covers_cons (covers_prefix pC (by decide))
        (covers_off pW (by decide) (by decide))))
    · rw [wr₂]; exact covers_cons (covers_prefix pC (by decide)) (covers_off pW (by decide) (by decide))
  · rw [m₂, St.mem]; exact Spill.saveMem_saved saved_fits _ _ _
  · rw [m₂, St.mem]; exact Spill.saveMem_frame saved_in (by decide) _ _ _

/-- A zero block at byte 240 of the key context, and the arguments of its encipherment. -/
theorem init2_ok {s : State} {K Ctx W : Addr} {L : Nat} (Ar : IArgs s K Ctx W L) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {t : State} (h19 : t.gpr .x19 = W) (h20 : t.gpr .x20 = Ctx)
    (h22 : t.gpr .x22 = BitVec.ofNat 64 R) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    WP isa (.block [Impl.AesGcm.AArch64.imm .x9 0, st .x20 240 .x9, st .x20 248 .x9,
        Impl.AesGcm.AArch64.ptr .x2 .x20 240, Impl.AesGcm.AArch64.imm .x3 1, Impl.AesGcm.AArch64.mov .x0 .x20,
        Impl.AesGcm.AArch64.mov .x1 .x22, Impl.AesGcm.AArch64.ptr .x4 .x19 scrO]) t fun t₄ =>
      BCall t₄ Ctx (Ctx + BitVec.ofNat 64 240) (W + BitVec.ofNat 64 512) R 1 ∧
      (∀ r ∈ preserved, t₄.gpr r = t.gpr r) ∧ t₄.sp = t.sp ∧ t₄.rd = t.rd ∧ t₄.wr = t.wr ∧
      t₄.mem = (t.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
  have pW := Ar.pW
  have pC := Ar.pC
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  rw [← hwr] at w₁ w₂
  obtain ⟨s₄, run₄, m₄, x0₄, x1₄, x2₄, x3₄, x4₄, g₄, sp₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa
      [Impl.AesGcm.AArch64.imm .x9 0, st .x20 240 .x9, st .x20 248 .x9, Impl.AesGcm.AArch64.ptr .x2 .x20 240,
        Impl.AesGcm.AArch64.imm .x3 1, Impl.AesGcm.AArch64.mov .x0 .x20, Impl.AesGcm.AArch64.mov .x1 .x22,
        Impl.AesGcm.AArch64.ptr .x4 .x19 scrO] t = some s₄ ∧
      s₄.mem = (t.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₄.gpr .x0 = Ctx ∧ s₄.gpr .x1 = BitVec.ofNat 64 R ∧ s₄.gpr .x2 = Ctx + BitVec.ofNat 64 240 ∧
      s₄.gpr .x3 = BitVec.ofNat 64 1 ∧ s₄.gpr .x4 = W + BitVec.ofNat 64 512 ∧
      (∀ r ∈ preserved, s₄.gpr r = t.gpr r) ∧ s₄.sp = t.sp ∧ s₄.rd = t.rd ∧ s₄.wr = t.wr := by
    refine ⟨_, by orun [h19, h20, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [mem_write, addr8]; rfl
    · simp [gpr_write, h20]
    · simp [gpr_write, h22]
    · simp [gpr_write, h20]
    · simp [gpr_write]
    · simp [gpr_write, h19]
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
    all_goals rfl
  have rd₄' : s₄.rd = s.rd := rd₄.trans hrd
  have wr₄' : s₄.wr = s.wr := wr₄.trans hwr
  refine WP.of_runBlock ⟨s₄, run₄,
    { x0 := x0₄, x1 := x1₄, x2 := x2₄, x3 := x3₄, x4 := x4₄, rounds := hR
      wrap := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); have := Ar.wc; omega_using [this]
      kd := Offset.base_disjoint Ctx (by decide) (by have := Ar.wc; omega_using [])
      ks := (Ar.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
      ds := (Ar.cs.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (by decide))
      reads := by
        rw [rd₄', wr₄']
        exact covers_cons (covers_left (covers_prefix pC (by decide))) (covers_cons
          (covers_left (covers_off pC (by decide) (by decide))) (covers_left (covers_off pW (by decide) (by decide))))
      writes := by
        rw [wr₄']
        exact covers_cons (covers_off pC (by decide) (by decide)) (covers_off pW (by decide) (by decide)) },
    g₄, sp₄, rd₄, wr₄, m₄⟩

/-- `vg_aes_ocb_init`, for its arguments. -/
theorem init_wp' (v : BlocksImpl) {s : State} {K Ctx W : Addr} {L : Nat} (Ar : IArgs s K Ctx W L)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 L) (h2 : s.gpr .x2 = Ctx) (h3 : s.gpr .x3 = W) :
    WP isa (init (callees v)) s fun s' => GprAbi s s' ∧ Spec.Ocb.KeyRepr s'.mem Ctx (bytesAt s.mem K L) := by
  have pW := Ar.pW
  have hKL : L < 2 ^ 64 := by rcases Ar.len with h | h | h <;> omega_using [h]
  unfold init
  refine WP.seq (WP.mono (init1_ok Ar h0 h1 h2 h3) fun s₂ ⟨x19₂, x20₂, x22₂, kc, sp₂, rd₂, wr₂, sv₂, f₂⟩ => ?_)
  generalize hRd : Spec.Aes.rounds (L / 4) = R at x22₂
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRd]; rcases Ar.len with rfl | rfl | rfl <;> decide
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR' with rfl | rfl | rfl <;> decide
  -- The key schedule.
  refine WP.seq (WP.mono (key_call (keyImpl v) kc) fun s₃ g => ?_)
  have g19 : s₃.gpr .x19 = W := by rw [g.saved .x19 (by decide) (by decide), x19₂]
  have g20 : s₃.gpr .x20 = Ctx := by rw [g.saved .x20 (by decide) (by decide), x20₂]
  have g22 : s₃.gpr .x22 = BitVec.ofNat 64 R := by rw [g.saved .x22 (by decide) (by decide), x22₂]
  refine WP.seq (WP.mono (init2_ok Ar hR' g19 g20 g22 (g.rd.trans rd₂) (g.wr.trans wr₂))
    fun s₄ ⟨bc, g₄, sp₄, rd₄, wr₄, m₄⟩ => ?_)
  have rd₄' : s₄.rd = s.rd := rd₄.trans (g.rd.trans rd₂)
  have wr₄' : s₄.wr = s.wr := wr₄.trans (g.wr.trans wr₂)
  have dK0 : (⟨Ctx, 240⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩ := bc.kd
  refine WP.seq (WP.mono (blk_call v.encOk v.encNoFrames bc) fun s₅ P₅ => ?_)
  -- The saved registers, and `restore`.
  have dSv : ∀ {d k : Nat}, d + k ≤ 256 → (⟨W + BitVec.ofNat 64 160, 88⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 d, k⟩ :=
    fun h => (Ar.cs.sub_left (Offset.sub_base _ h)).sub_right (Lay.wSub (by decide)) |>.symm
  have dSv' : ∀ {d k : Nat}, 512 ≤ d → d + k ≤ 2560 →
      (⟨W + BitVec.ofNat 64 160, 88⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Offset.disjoint W (.inl (by omega_using [h₁])) (by omega_using []) (by have := Ar.ws; omega_using [h₂])
  have f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact Proof.Cmac.frame_store2 _ _ _
  have sv₅ : Spill.Saved W s.gpr saved s₅.mem := by
    have a := Spill.Saved.frame_in sv₂ saved_in (rs := [⟨Ctx, 240⟩, ⟨W + BitVec.ofNat 64 512, 512⟩]) g.frame
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simpa using dSv (d := 0) (k := 240) (by decide)
        · exact dSv' (by decide) (by decide))
    have b := Spill.Saved.frame_in a saved_in f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dSv (by decide))
    exact Spill.Saved.frame_in b saved_in P₅.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dSv (by decide)
      · exact dSv' (by decide) (by decide))
  have c19 : s₅.gpr .x19 = W := by rw [P₅.saved .x19 (by decide) (by decide), g₄ _ (by decide), g19]
  have sp₅ : s₅.sp = s.sp := by rw [P₅.sp, sp₄, g.sp, sp₂]
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp c19 saved_fits.1 (by decide) (fun p hp => by
    rw [P₅.rd, P₅.wr, rd₄', wr₄']; exact covers_left pW _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base W (by have := saved_in p hp; omega_using [this]) (by have := saved_in p hp; have := Ar.ws; omega_arith)⟩)
      sv₅) fun s₆ Rs => ⟨restore_abi Rs sp₅, ?_⟩
  -- The key context.
  have k₃ : bytesAt s₃.mem Ctx (16 * (R + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L) := by
    rw [← hRd, g.out, Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.ks.sub_right (Lay.wSub (by decide)))
        (by omega_using [hKL])]
  have k₅ : bytesAt s₅.mem Ctx (16 * (R + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L) := by
    rw [Proof.Cmac.bytesAt_frame P₅.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dK0.sub_left (Region.sub_prefix hRb)
        · exact (Ar.cs.sub_left (Region.sub_prefix (by omega_using [hR']))).sub_right (Lay.wSub (by decide))) (by omega_using [hR']),
      Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dK0.sub_left (Region.sub_prefix hRb)) (by omega_using [hR']), k₃]
  refine ⟨?_, ?_⟩
  · rw [length_bytesAt, hRd, Rs.mem]; exact k₅
  · show blockAtMem s₆.mem (Ctx + BitVec.ofNat 64 240) = _
    have hz : blockAtMem s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
      rw [m₄, blockAtMem_store2, Proof.Cmac.le8_zero]; rfl
    rw [Rs.mem, P₅.enc0, hz, Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dK0.sub_left (Region.sub_prefix hRb)) (by omega_using [hR']), k₃,
      Spec.Ocb.aes, length_bytesAt, hRd]

/-- `vg_aes_ocb_init`. -/
theorem init_wp (v : BlocksImpl) {s : State} (hp : initAArch64.pre s) :
    WP isa (init (callees v)) s fun s' => GprAbi s s' ∧ initAArch64.post s s' :=
  init_wp' v (IArgs.of hp) rfl (ofNat_toNat64 _).symm rfl rfl

end VG.Proof.AesOcb.AArch64

end

end

/-!
# AES-OCB on AArch64: `vg_aes_ocb_init` is constant time

Untrusted: everything here is checked by Lean. The blocks between the calls
run from public registers (the arguments, then the scratch buffer, the key
context and the rounds), and the calls have the same arguments in both runs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint rel_key ct_of KeyCall key_call)

theorem init_ct (v : BlocksImpl) : ConstantTime isa initAArch64.pre initAArch64.pub (init (callees v)) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, qsp⟩ := hq
  have A₁ := IArgs.of h₁
  have A₂ := IArgs.of h₂
  rw [← q0, ← q1, ← q2, ← q3] at A₂
  have o : ∀ x : BitVec 64, x = BitVec.ofNat 64 x.toNat := fun x => (ofNat_toNat64 x).symm
  have hR' : Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4) = 10 ∨ Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4) = 12 ∨
      Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4) = 14 := by rcases A₁.len with h | h | h <;> rw [h] <;> decide
  unfold init
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3] qsp (by agree_tac [q0, q1, q2, q3]) ⟨_, by taint_decide⟩)
    (init1_ok A₁ rfl (o _) rfl rfl) (init1_ok A₂ q0.symm (by rw [← q1]; exact o _) q2.symm q3.symm)
    fun s₁ s₂ ⟨a19, a20, a22, kc₁, asp, ard, awr, _, _⟩ ⟨b19, b20, b22, kc₂, bsp, brd, bwr, _, _⟩ => ?_
  refine rel_seq (rel_key (keyImpl v) kc₁ kc₂ (by rw [asp, bsp, qsp])) (key_call (keyImpl v) kc₁)
    (key_call (keyImpl v) kc₂) fun t₁ t₂ g₁ g₂ => ?_
  have c19 : t₁.gpr .x19 = σ₁.gpr .x3 := by rw [g₁.saved .x19 (by decide) (by decide), a19]
  have c20 : t₁.gpr .x20 = σ₁.gpr .x2 := by rw [g₁.saved .x20 (by decide) (by decide), a20]
  have c22 : t₁.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4)) := by rw [g₁.saved .x22 (by decide) (by decide), a22]
  have d19 : t₂.gpr .x19 = σ₁.gpr .x3 := by rw [g₂.saved .x19 (by decide) (by decide), b19]
  have d20 : t₂.gpr .x20 = σ₁.gpr .x2 := by rw [g₂.saved .x20 (by decide) (by decide), b20]
  have d22 : t₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4)) := by rw [g₂.saved .x22 (by decide) (by decide), b22]
  refine rel_seq (rel_taint [.x19, .x20, .x22] (by rw [g₁.sp, g₂.sp, asp, bsp, qsp])
      (by agree_tac [c19, c20, c22, d19, d20, d22]) ⟨_, by taint_decide⟩)
    (init2_ok A₁ hR' c19 c20 c22 (by rw [g₁.rd, ard]) (by rw [g₁.wr, awr]))
    (init2_ok A₂ hR' d19 d20 d22 (by rw [g₂.rd, brd]) (by rw [g₂.wr, bwr]))
    fun u₁ u₂ ⟨bc₁, e₁, esp₁, _, _, _⟩ ⟨bc₂, e₂, esp₂, _, _, _⟩ => ?_
  refine rel_seq (blk_rel v.encOk v.encCt fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨_, _, _, _, _, bc₁, bc₂, by rw [esp₁, esp₂, g₁.sp, g₂.sp, asp, bsp, qsp]⟩)
    (blk_call v.encOk v.encNoFrames bc₁) (blk_call v.encOk v.encNoFrames bc₂) fun w₁ w₂ P₁ P₂ => ?_
  exact rel_taint [.x19] (by rw [P₁.sp, P₂.sp, esp₁, esp₂, g₁.sp, g₂.sp, asp, bsp, qsp])
    (by agree_tac [P₁.saved .x19 (by decide) (by decide), P₂.saved .x19 (by decide) (by decide),
      e₁ .x19 (by decide), e₂ .x19 (by decide), c19, d19]) ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64
