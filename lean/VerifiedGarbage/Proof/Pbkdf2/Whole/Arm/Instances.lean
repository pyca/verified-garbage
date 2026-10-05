import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances
import VerifiedGarbage.Proof.Framework.TaintBatch

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Key`. -/
section

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: the prologue and the key

As on x86 (`Proof/Pbkdf2/Whole/X86/Key.lean`): the prologue saves our caller's
registers in `scratch` (`save_ok`, `VG.Proof.Pbkdf2.Stream.Arm.save_ok` for any
amount of working space before the save area that an immediate offset reaches)
and keeps the arguments in registers; then the key is the password, or its
digest if it is longer than a block (`key_ok`): either gives the same `K₀`.
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Pbkdf2.Stream.Arm (Hash scrAt)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK SavedRegs saveR FinArgs init_call fin_frame count saveMem_frameR
  saveMem_read saved_mem saved_pairwise savedRegs)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_ldrSp op2_imm op2_reg saveList_ok contains_offset eval_eq)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey)

variable {F : Fns}

/-- Saving the registers, with `scratch` in `r12`: `VG.Proof.Pbkdf2.Stream.Arm.save_ok`, for any
working space before the save area that an immediate offset reaches. -/
theorem save_ok (H : VG.Impl.Pbkdf2.Stream.Arm.Hash) {s : State} {sc : BitVec 32} {L : Nat} (h12 : s.gpr .r12 = sc)
    (hW : 8 * H.W + 36 ≤ 4096) (hsc : ⟨State.addr sc, L⟩ ∈ s.wr) (hL : 8 * H.W + 36 ≤ L)
    (hfit : sc.toNat + L ≤ 2 ^ 32) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [saveR H sc] s.mem s'.mem → SavedRegs H sc s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  rw [Pbkdf2.Stream.Arm.save_eq]
  refine VG.Arm.Spill.saveList_ok H.saved s Q (fun p hp => ?_) fun s' g rd wr sp m => k s' g rd wr sp ?_ ?_
  · obtain ⟨h₁, h₂⟩ := saved_mem H hp
    rw [h12]
    exact ⟨by omega, by omega, ⟨_, hsc, VG.Proof.MdStream.Arm.contains_offset (by omega) (by omega)⟩⟩
  · rw [m, h12]
    exact saveMem_frameR _ _ _ _ (by omega) _ _ fun p hp => saved_mem H hp
  · intro p hp
    rw [m, h12]
    exact saveMem_read _ _ _ _ (saved_pairwise H) (fun q hq => by have := saved_mem H hq; omega) p hp

theorem zero_append (x : BitVec 32) : (0 : BitVec 32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat]
  have := x.isLt
  simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or]
  omega

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F)
include hp hz

/-! ## The prologue -/

/-- After the prologue: `KR`, and the password in `r8` and `r9`. -/
structure KK (F : Fns) (s₀ s : State) : Prop where
  kr : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s
  r8 : s.gpr .r8 = pw s₀
  r9 : s.gpr .r9 = s₀.gpr .r1

theorem prologue_ok : WP isa (.block F.prologue) s₀ (VG.Proof.Pbkdf2.Whole.Arm.KK F s₀) := by
  have hL := end_le hz; have := layout (F := F); have hr := hz.reach
  have hsc := sc_mem hp
  simp only [Fns.prologue, List.cons_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 3) (by decide) rfl (by
      rw [hp.rd, hp.wr]
      exact ⟨VG.Proof.Pbkdf2.Whole.Arm.argR s₀, by simp, argR_sub hp (i := 3) (by decide) |> fun h => by
        have e : stackArgAddr s₀ 3 = State.addr s₀.sp + BitVec.ofNat 64 12 :=
          addr_add (by have := hp.spf; omega)
        have e0 : stackArgAddr s₀ 0 = State.addr s₀.sp := by simp [stackArgAddr]
        show Region.Contains ⟨stackArgAddr s₀ 0, 16⟩ _ 4
        rw [e, e0]; exact Offset.contains_base _ (by omega) (by omega)⟩) fun s₁ u₁ => ?_
  refine VG.Proof.Pbkdf2.Whole.Arm.save_ok F.L (sc := VG.Proof.Pbkdf2.Whole.Arm.scr s₀) (L := F.L8) u₁.gpr (by simp only [Fns.L]; omega) (by rw [u₁.wr]; exact hsc)
    (by show 8 * F.W + 36 ≤ F.L8; omega) hp.nsc fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      g₂, u₁.gpr]; rfl
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
    exact sv₂.of_eq F.L fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, ← u₁.mem]
    exact f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F, by simp, sv_sub hz⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      e₂ _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)]

/-! ## The stack and `scratch`, while `KR` holds -/

omit hp hz in
theorem below_sub {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) : Region.Sub (Pbkdf2.Stream.Arm.below s) (stkR s₀) := by
  rw [← hk.stkE]; exact below_stk (n := 16) (by decide)

omit hz in
/-- A region of `scratch` is apart from the stack below the stack pointer. -/
theorem b24 {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {R : Region} (hR : Region.Sub R (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F)) : (stk s).Disjoint R := by
  rw [hk.stkE]; exact hp.b_s.sub_right hR

omit hz in
theorem b16 {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {R : Region} (hR : Region.Sub R (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F)) :
    (Pbkdf2.Stream.Arm.below s).Disjoint R :=
  (hp.b_s.sub_left (VG.Proof.Pbkdf2.Whole.Arm.below_sub hk)).sub_right hR

omit hz in
/-- A part of `scratch` is in a region the code may write. -/
theorem cov_part {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {o n : Nat} (h : o + n ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F, by rw [hk.wr]; exact sc_mem hp, o, rfl, h⟩

omit hz in
theorem cov_low {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {k : Nat} (h : k ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (lowR s₀ k).base = r'.base + BitVec.ofNat 64 off ∧ off + (lowR s₀ k).len ≤ r'.len :=
  ⟨VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F, by rw [hk.wr]; exact sc_mem hp, 0, by simp, by simp only [Nat.zero_add]; exact h⟩

omit hz in
theorem cov_pw {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) : Covers [pwR s₀] (s.rd ++ s.wr) :=
  Pbkdf2.Stream.Arm.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))

omit hz in
theorem cov_salt {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) : Covers [saltR s₀] (s.rd ++ s.wr) :=
  Pbkdf2.Stream.Arm.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))

/-! ## Hashing a password longer than a block -/

variable (hH : VG.Proof.Pbkdf2.Stream.Arm.HashOK F.H)
include hH

omit hp hz hH in
/-- `r4 ← scratch + stWO`. -/
theorem hk1_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) (ho : F.stWO < 2 ^ 16) :
    WP isa (.block (scrAt .r4 F.stWO)) s fun t => VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ t ∧ t.gpr .r4 = dO s₀ F.stWO ∧ t.mem = s.mem := by
  rw [← List.append_nil (scrAt .r4 F.stWO)]
  exact scr_ok hk.kr ho fun s₁ u₁ => WP.block_nil ⟨⟨hk.kr.upd12 (by decide) u₁,
    by rw [u₁.other _ (by decide) (by decide), hk.r8], by rw [u₁.other _ (by decide) (by decide), hk.r9]⟩, u₁.gpr, u₁.mem⟩

omit hp hz hH in
/-- `r0 ← r4`, before `init`. -/
theorem hk2a_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) :
    WP isa (.block [.mov .r0 (.reg .r4)]) s fun t => VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ t ∧ t.gpr .r4 = dO s₀ F.stWO ∧
      t.gpr .r0 = dO s₀ F.stWO := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ⟨⟨hk.kr.upd (by decide) u₁, ?_, ?_⟩, ?_, ?_⟩
  · rw [u₁.other _ (by decide), hk.r8]
  · rw [u₁.other _ (by decide), hk.r9]
  · rw [u₁.other _ (by decide), h4]
  · rw [u₁.gpr, h4]

/-- `init` on the working state. -/
theorem hk2b_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) (h0 : s.gpr .r0 = dO s₀ F.stWO) :
    WP isa (.call F.H.initN F.H.initC) s fun t => VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ t ∧ hH.SH.Repr t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.stWO) [] ∧
      t.gpr .r4 = dO s₀ F.stWO := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.reach
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have cw : Covers [⟨State.addr (dO s₀ F.stWO), F.H.S⟩] s.wr := by
    rw [ea]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk.kr (by omega)
  refine init_call hH (st := dO s₀ F.stWO) h0 (by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega)
    cw fun s' a r => ?_
  have a' := After.of_hmac a
  refine ⟨⟨hk.kr.call hp hz a' fun r hr => ?_, ?_, ?_⟩, by rw [← ea]; exact r, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
  · rw [a.cs _ (by decide) (by decide), hk.r8]
  · rw [a.cs _ (by decide) (by decide), hk.r9]
  · rw [a.cs _ (by decide) (by decide), h4]

/-- `init` on the working state. -/
theorem hk2_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) :
    WP isa (F.H.callInit .r4) s fun t => VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ t ∧ hH.SH.Repr t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.stWO) [] ∧
      t.gpr .r4 = dO s₀ F.stWO := by
  unfold Hash.callInit
  exact WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk2a_ok hk h4) fun s₁ ⟨k₁, d₁, a₁⟩ => VG.Proof.Pbkdf2.Whole.Arm.hk2b_ok hp hz hH k₁ d₁ a₁)

omit hp hz hH in
/-- `update`'s arguments: the password. -/
theorem hk3_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) :
    WP isa (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r8), .mov .r7 (.reg .r9), .mov .r10 (.reg .r11),
      .mov .r2 (.imm 0), .mov .r3 (.imm 0)]) s fun t => VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ t ∧ t.gpr .r4 = dO s₀ F.stWO ∧
        t.gpr .r0 = dO s₀ F.stWO ∧ t.gpr .r1 = pw s₀ ∧ t.gpr .r7 = s₀.gpr .r1 ∧ t.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀ ∧
        count t = BitVec.ofNat 64 0 ∧ t.mem = s.mem := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_imm (by decide))
    fun s₆ u₆ => WP.block_nil ?_
  have k₆ := (((((hk.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
    (by decide) u₅).upd (by decide) u₆
  refine ⟨⟨k₆, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hk.r8]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hk.r9]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, h4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), hk.r8]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hk.r9]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hk.kr.r11]
  · simp only [count]; rw [u₆.gpr, u₆.other .r2 (by decide), u₅.gpr]; rfl

theorem hk4_args {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stWO) (h1 : s.gpr .r1 = pw s₀)
    (h7 : s.gpr .r7 = s₀.gpr .r1) (h10 : s.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀) :
    UpdL hH s (dO s₀ F.stWO) (pw s₀) (VG.Proof.Pbkdf2.Whole.Arm.scr s₀) (pwl s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hH.hWb
  have k := hk.kr
  have ea := dO_addr hp (o := F.stWO) (by omega)
  exact
    { r0 := h0
      r1 := h1
      r7 := by rw [h7, VG.Proof.Pbkdf2.Whole.Arm.ofNat_toNat32]
      r10 := h10
      hlen := (s₀.gpr .r1).isLt
      sp16 := by rw [k.sp]; have := hp.sp24; omega
      cd := VG.Proof.Pbkdf2.Whole.Arm.cov_pw hp k
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_part hp k (by omega)
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_low hp k (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega) (by omega)).symm
      d_st := by rw [ea]; exact hp.pw_s.sub_right (part_sub (by omega))
      d_sc := hp.pw_s.sub_right (low_sub (by omega))
      b_st := by rw [ea]; exact VG.Proof.Pbkdf2.Whole.Arm.b16 hp k (part_sub (by omega))
      b_d := hp.b_pw.sub_left (VG.Proof.Pbkdf2.Whole.Arm.below_sub k)
      b_sc := VG.Proof.Pbkdf2.Whole.Arm.b16 hp k (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nd := hp.npw
      nsc := by have := hp.nsc; omega }

theorem hk4_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) (h0 : s.gpr .r0 = dO s₀ F.stWO)
    (h1 : s.gpr .r1 = pw s₀) (h7 : s.gpr .r7 = s₀.gpr .r1) (h10 : s.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀)
    (hc : count s = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.stWO) []) :
    WP isa (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16)) s
      fun t => VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ t ∧ t.gpr .r4 = dO s₀ F.stWO ∧
        hH.SH.Repr t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.stWO) (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  refine upd_frame hH (VG.Proof.Pbkdf2.Whole.Arm.hk4_args hp hz hH hk h0 h1 h7 h10) fun s' a r => ⟨⟨hk.kr.call hp hz (After.of_hmac a)
    fun r hr => ?_, by rw [a.cs _ (by decide) (by decide), hk.r8], by rw [a.cs _ (by decide) (by decide), hk.r9]⟩,
    by rw [a.cs _ (by decide) (by decide), h4], ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · have := r [] (by rw [ea]; exact hr) hc
    rwa [List.nil_append, ea, hk.kr.pwBytes hp] at this

omit hp hz hH in
/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) (ho : F.hkO < 2 ^ 16) :
    WP isa (.block (([.mov .r0 (.reg .r4)] : List Instr) ++ scrAt .r1 F.hkO ++
      ([.mov .r12 (.reg .r11), .mov .r2 (.reg .r9), .mov .r3 (.imm 0)] : List Instr))) s fun t => VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ t ∧ t.gpr .r0 = dO s₀ F.stWO ∧ t.gpr .r1 = dO s₀ F.hkO ∧
        t.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀ ∧ count t = BitVec.ofNat 64 (pwl s₀) ∧ t.mem = s.mem := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have k₁ := hk.kr.upd (by decide) u₁
  refine scr_ok k₁ ho fun s₂ u₂ => ?_
  have k₂ := k₁.upd12 (by decide) u₂
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm (by decide))
    fun s₅ u₅ => WP.block_nil ?_
  have k₅ := ((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅
  have e8 : s₂.gpr .r8 = pw s₀ := by rw [u₂.other _ (by decide) (by decide), u₁.other _ (by decide), hk.r8]
  have e9 : s₂.gpr .r9 = s₀.gpr .r1 := by rw [u₂.other _ (by decide) (by decide), u₁.other _ (by decide), hk.r9]
  refine ⟨⟨k₅, ?_, ?_⟩, ?_, ?_, ?_, ?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e8]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e9]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide) (by decide),
      u₁.gpr, h4]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide) (by decide),
      u₁.other _ (by decide), hk.kr.r11]
  · simp only [count]; rw [u₅.gpr, u₅.other .r2 (by decide), u₄.gpr, u₃.other _ (by decide), e9, VG.Proof.Pbkdf2.Whole.Arm.zero_append]

theorem hk6_args {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stWO) (h1 : s.gpr .r1 = dO s₀ F.hkO)
    (h12 : s.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀) : FinArgs hH s (dO s₀ F.stWO) (dO s₀ F.hkO) (VG.Proof.Pbkdf2.Whole.Arm.scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hH.hWb
  have k := hk.kr
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have eh := dO_addr hp (o := F.hkO) (by omega)
  exact
    { r0 := h0
      r1 := h1
      r12 := h12
      sp16 := by rw [k.sp]; have := hp.sp24; omega
      cw := by
        rw [ea, eh]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_part hp k (by omega)
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_part hp k (by omega)
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_low hp k (by omega)
      st_o := by rw [ea, eh]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega) (by omega)).symm
      o_sc := by rw [eh]; exact (low_disj hz (k := hH.Wb) (by omega) (by omega)).symm
      b_st := by rw [ea]; exact VG.Proof.Pbkdf2.Whole.Arm.b16 hp k (part_sub (by omega))
      b_o := by rw [eh]; exact VG.Proof.Pbkdf2.Whole.Arm.b16 hp k (part_sub (by omega))
      b_sc := VG.Proof.Pbkdf2.Whole.Arm.b16 hp k (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      no := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nsc := by have := hp.nsc; omega }

theorem hk6_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stWO) (h1 : s.gpr .r1 = dO s₀ F.hkO)
    (h12 : s.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀) (hc : count s = BitVec.ofNat 64 (pwl s₀))
    (hr : hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.stWO) (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀))) :
    WP isa (.frame (.push [.r1, .r12]) (.call F.H.finN F.H.finC) (.pop .r1 8)) s
      fun t => VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ t ∧
        bytesAt t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have eh := dO_addr hp (o := F.hkO) (by omega)
  refine fin_frame hH (VG.Proof.Pbkdf2.Whole.Arm.hk6_args hp hz hH hk h0 h1 h12) fun s' a r => ⟨hk.kr.call hp hz (After.of_hmac a)
    fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
    · exact .inr ⟨_, _, by rw [eh], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · rw [bytesAt_take _ _ hz.D.2.1, ← eh]
    exact r _ (by rw [ea]; exact hr) (by rw [bytesAt_length]; exact Nat.lt_trans (s₀.gpr .r1).isLt (by decide))
      (by rw [bytesAt_length]; exact hc)

omit hp hz hH in
theorem hk7_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) (ho : F.hkO < 2 ^ 16) (hD : F.H.D < 2 ^ 16) :
    WP isa (.block (scrAt .r2 F.hkO ++ ([.movw .r3 (BitVec.ofNat 16 F.H.D)] : List Instr))) s
      fun t => VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ t ∧ t.gpr .r2 = dO s₀ F.hkO ∧ t.gpr .r3 = BitVec.ofNat 32 F.H.D ∧ t.mem = s.mem :=
  scr_ok hk ho fun s₁ u₁ => Pbkdf2.Stream.Arm.wp_movw fun s₂ u₂ => WP.block_nil
    ⟨(hk.upd12 (by decide) u₁).upd (by decide) u₂, by rw [u₂.other _ (by decide), u₁.gpr],
      by rw [u₂.gpr, Pbkdf2.Stream.Arm.movw_ofNat hD], by rw [u₂.mem, u₁.mem]⟩

theorem hashKey_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) :
    WP isa F.hashKey s fun t => VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ t ∧ t.gpr .r2 = dO s₀ F.hkO ∧ t.gpr .r3 = BitVec.ofNat 32 F.H.D ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.reach
  unfold Fns.hashKey
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk1_ok hk (by omega)) fun s₁ ⟨k₁, d₁, _⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂, e₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk3_ok k₂ e₂) fun s₃ ⟨k₃, d₃, a₀, a₁, a₇, a₁₀, c₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk4_ok hp hz hH k₃ d₃ a₀ a₁ a₇ a₁₀ c₃ (by rw [m₃]; exact r₂)) fun s₄ ⟨k₄, d₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk5_ok k₄ d₄ (by omega)) fun s₅ ⟨k₅, a₀', a₁', a₁₂, c₅, m₅⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk6_ok hp hz hH k₅ a₀' a₁' a₁₂ c₅ (by rw [m₅]; exact r₄)) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk7_ok k₆ (by omega) (by omega)) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

end

/-! ## The key -/

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F) (hH : VG.Proof.Pbkdf2.Stream.Arm.HashOK F.H)
include hp hz

omit hp in
theorem cmp_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) :
    WP isa (.block F.cmpPw) s fun t => VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ t ∧ t.z = decide (pwl s₀ < F.H.B + 1) ∧ t.mem = s.mem := by
  have := hz.B
  unfold Fns.cmpPw
  rw [← List.append_nil [Instr.subs .r12 .r9 (.imm (BitVec.ofNat 32 (F.H.B + 1))), .mov .r12 (.imm 0),
    .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)]]
  refine wp_lt hz.encB1 fun s' g m rd wr sp z => WP.block_nil ⟨⟨hk.kr.same rd wr sp (fun r hr => g r (by
    simp only [VG.Proof.Pbkdf2.Whole.Arm.kregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) m,
    by rw [g _ (by decide), hk.r8], by rw [g _ (by decide), hk.r9]⟩, ?_, m⟩
  rw [z, hk.r9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := F.H.B + 1) (by omega)]

omit hp hz in
include hH in
theorem hash_len {k : List Byte} {m : Mem} {p : Addr} (h : bytesAt m p F.H.D = hH.SH.H.hash k) :
    (hH.SH.H.hash k).length = F.H.D := by
  rw [← h, bytesAt_length]

omit hp in
include hH in
/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash {k : List Byte} (hk : F.H.B < k.length) (hl : (hH.SH.H.hash k).length = F.H.D) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hB := hH.hB; have := hz.DB
  simp only [blockKey, hB, hl, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ F.H.B < F.H.D by omega))]

end

/-- Where the key is, and its length. -/
abbrev kp (F : Fns) (s₀ : State) : BitVec 32 := if pwl s₀ < F.H.B + 1 then pw s₀ else dO s₀ F.hkO
abbrev kl (F : Fns) (s₀ : State) : Nat := if pwl s₀ < F.H.B + 1 then pwl s₀ else F.H.D

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F) (hH : VG.Proof.Pbkdf2.Stream.Arm.HashOK F.H)
include hp hz hH

theorem key_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) :
    WP isa F.key s fun t => VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ t ∧ t.gpr .r2 = VG.Proof.Pbkdf2.Whole.Arm.kp F s₀ ∧ t.gpr .r3 = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Whole.Arm.kl F s₀) ∧
      blockKey hH.SH.H (bytesAt t.mem (State.addr (VG.Proof.Pbkdf2.Whole.Arm.kp F s₀)) (VG.Proof.Pbkdf2.Whole.Arm.kl F s₀)) =
        blockKey hH.SH.H (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀)) := by
  unfold Fns.key
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.cmp_ok hz hk) fun s₁ ⟨k₁, z₁, _⟩ => ?_)
  refine WP.ite (decide (pwl s₀ < F.H.B + 1)) (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, z₁]) (fun hT => ?_) fun hF => ?_
  · have hlt : pwl s₀ < F.H.B + 1 := of_decide_eq_true hT
    simp only [VG.Proof.Pbkdf2.Whole.Arm.kp, VG.Proof.Pbkdf2.Whole.Arm.kl, hlt, ↓reduceIte]
    refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil
      ⟨(k₁.kr.upd (by decide) u₂).upd (by decide) u₃, ?_, ?_, ?_⟩
    · rw [u₃.other _ (by decide), u₂.gpr, k₁.r8]
    · rw [u₃.gpr, u₂.other _ (by decide), k₁.r9, VG.Proof.Pbkdf2.Whole.Arm.ofNat_toNat32]
    · rw [u₃.mem, u₂.mem, k₁.kr.pwBytes hp]
  · have hlt : ¬ pwl s₀ < F.H.B + 1 := of_decide_eq_false hF
    simp only [VG.Proof.Pbkdf2.Whole.Arm.kp, VG.Proof.Pbkdf2.Whole.Arm.kl, hlt, ↓reduceIte]
    refine WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hashKey_ok hp hz hH k₁) fun t ⟨k, d, c, b⟩ => ⟨k, d, c, ?_⟩
    have := hz.D; have := hz.reach
    rw [dO_addr hp (by have := end_le hz; have := layout (F := F); omega),
      b, VG.Proof.Pbkdf2.Whole.Arm.blockKey_hash hz hH (by rw [bytesAt_length]; omega) (VG.Proof.Pbkdf2.Whole.Arm.hash_len hH b)]

omit hH in
/-- The key's region is the password, or the hashed password in `scratch`. -/
theorem key_cases : (VG.Proof.Pbkdf2.Whole.Arm.kp F s₀ = pw s₀ ∧ VG.Proof.Pbkdf2.Whole.Arm.kl F s₀ = pwl s₀ ∧ pwl s₀ ≤ F.H.B) ∨
    (State.addr (VG.Proof.Pbkdf2.Whole.Arm.kp F s₀) = VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.hkO ∧ VG.Proof.Pbkdf2.Whole.Arm.kl F s₀ = F.H.D) := by
  by_cases h : pwl s₀ < F.H.B + 1
  · exact .inl ⟨by simp [VG.Proof.Pbkdf2.Whole.Arm.kp, h], by simp [VG.Proof.Pbkdf2.Whole.Arm.kl, h], by omega⟩
  · refine .inr ⟨?_, by simp [VG.Proof.Pbkdf2.Whole.Arm.kl, h]⟩
    simp only [VG.Proof.Pbkdf2.Whole.Arm.kp, h, ↓reduceIte]
    exact dO_addr hp (by have := end_le hz; have := layout (F := F); have := hz.D; omega)

omit hH in
theorem kl_le : VG.Proof.Pbkdf2.Whole.Arm.kl F s₀ ≤ F.H.B := by
  have := hz.DB
  rcases VG.Proof.Pbkdf2.Whole.Arm.key_cases hp hz with ⟨-, h, h'⟩ | ⟨-, h⟩ <;> omega

omit hH in
theorem key_toNat : (VG.Proof.Pbkdf2.Whole.Arm.kp F s₀).toNat + VG.Proof.Pbkdf2.Whole.Arm.kl F s₀ ≤ 2 ^ 32 := by
  by_cases h : pwl s₀ < F.H.B + 1
  · simp only [VG.Proof.Pbkdf2.Whole.Arm.kp, VG.Proof.Pbkdf2.Whole.Arm.kl, h, ↓reduceIte]; exact hp.npw
  · simp only [VG.Proof.Pbkdf2.Whole.Arm.kp, VG.Proof.Pbkdf2.Whole.Arm.kl, h, ↓reduceIte]
    have := end_le hz; have := layout (F := F); have := hz.D
    rw [dO_toNat hp (by omega)]
    have := hp.nsc; omega

omit hH in
/-- The key is apart from the parts of `scratch` after the hashed password,
from the working space, and from the stack below the stack pointer. -/
theorem key_disj {R : Region} (hR : Region.Sub R (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F))
    (hd : R.Disjoint (sR s₀ F.hkO F.H.D)) : Region.Disjoint ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.kp F s₀), VG.Proof.Pbkdf2.Whole.Arm.kl F s₀⟩ R := by
  rcases VG.Proof.Pbkdf2.Whole.Arm.key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.pw_s.sub_right hR
  · rw [h, h']; exact hd.symm

omit hH in
theorem key_stk {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) : (stk s).Disjoint ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.kp F s₀), VG.Proof.Pbkdf2.Whole.Arm.kl F s₀⟩ := by
  rw [hk.stkE]
  rcases VG.Proof.Pbkdf2.Whole.Arm.key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.b_pw
  · rw [h, h']; exact hp.b_s.sub_right (part_sub (by have := end_le hz; have := layout (F := F); have := hz.D; omega))

omit hH in
theorem key_cov {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) : Covers [⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.kp F s₀), VG.Proof.Pbkdf2.Whole.Arm.kl F s₀⟩] (s.rd ++ s.wr) := by
  rcases VG.Proof.Pbkdf2.Whole.Arm.key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact VG.Proof.Pbkdf2.Whole.Arm.cov_pw hp hk
  · rw [h, h']
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', off, e, l⟩ := VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk (o := F.hkO) (n := F.H.D)
        (by have := end_le hz; have := layout (F := F); have := hz.D; omega)
      exact ⟨r', List.mem_append_right _ hr', off, e, l⟩

end

end VG.Proof.Pbkdf2.Whole.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Setup`. -/
section

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: HMAC's states for the key, and the salt

As on x86 (`Proof/Pbkdf2/Whole/X86/Setup.lean`): HMAC's `init` makes the key's
inner and outer states; the inner one is copied and absorbs the salt
(`setup_ok`), which gives the three states every block starts from (`States`).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Pbkdf2.Stream.Arm (Hash scrAt copy)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK Copied copy_ok cclob count)
open VG.Proof.MdStream.Arm (Upd wp_mov op2_imm op2_reg)
open VG.Proof.Hmac.Common (bytesAt_length writeBytes_at bytesAt_getD' xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad)

variable {F : Fns}

/-- `K₀`, the password padded (or hashed and padded) to a block. -/
abbrev K0 (hF : FnsOK F) (s₀ : State) : List Byte :=
  blockKey hF.hH.SH.H (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀))

abbrev saltB (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (salt s₀)) (sl s₀)

/-- The key's states, and the inner one after the salt. -/
structure States (hF : FnsOK F) (s₀ : State) (m : Mem) : Prop where
  st0 : hF.hH.SH.Repr m (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad)
  st1 : hF.hH.SH.Repr m (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) opad)
  stS : hF.hH.SH.Repr m (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.stSO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad ++ VG.Proof.Pbkdf2.Whole.Arm.saltB s₀)

/-- The representation is kept by what writes elsewhere. -/
theorem repr_keep (hH : VG.Proof.Pbkdf2.Stream.Arm.HashOK F.H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, F.H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, F.H.S⟩) hd (by show F.H.S ≤ 2 ^ 64; have hH_hSB := hH.hSB; omega) hi) hr

/-- The three states are kept by what writes elsewhere: after them in `scratch`. -/
theorem States.keep {hF : FnsOK F} {s₀ : State} (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F) {m m' : Mem} (h : VG.Proof.Pbkdf2.Whole.Arm.States hF s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ F.st0O (3 * F.H.S)) r) :
    VG.Proof.Pbkdf2.Whole.Arm.States hF s₀ m' := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D
  have sub : ∀ o, F.st0O ≤ o → o + F.H.S ≤ F.st0O + 3 * F.H.S →
      Region.Sub (sR s₀ o F.H.S) (sR s₀ F.st0O (3 * F.H.S)) := fun o h₁ h₂ =>
    Offset.sub _ h₁ h₂
  refine ⟨VG.Proof.Pbkdf2.Whole.Arm.repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega) (by omega))) h.st0,
    VG.Proof.Pbkdf2.Whole.Arm.repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega) (by omega))) h.st1,
    VG.Proof.Pbkdf2.Whole.Arm.repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega) (by omega))) h.stS⟩

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F)
include hp hz

/-- A copy of `n > 0` bytes within `scratch`, after the save area. -/
theorem copy_part_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {a b n : Nat} (hn : 0 < n) (ha : a + n ≤ F.L8)
    (hb : b + n ≤ F.L8) (hb' : 8 * F.W + 36 ≤ b) (hab : a + n ≤ b ∨ b + n ≤ a) :
    WP isa (copy .r11 a .r11 b n) s fun t => VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ t ∧ (∀ r ∉ cclob, t.gpr r = s.gpr r) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ b) (bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ a) n) := by
  have hL := hz.reach; have hp_nsc := hp.nsc; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (copy_ok (src := .r11) (dst := .r11) (by decide) (by decide) (by omega_using [hL, ha, hn]) (by omega_using [hL, hb, hn]) hn (by omega_using [hL, ha])
    (by rw [hk.r11]; omega_using [hp_nsc, ha]) (by rw [hk.r11]; omega_using [hp_nsc, hb])
    (fun j hj => by
      rw [hk.r11]
      exact ⟨VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F, List.mem_append_right _ (by rw [hk.wr]; exact sc_mem hp),
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega_using [hj, hL, ha])⟩)
    (fun j hj => by
      rw [hk.r11]
      exact ⟨VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F, by rw [hk.wr]; exact sc_mem hp,
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega_using [hj, hL, hb])⟩)
    (by rw [hk.r11]; exact part_disj hz hab ha hb)) fun t c => ?_
  rw [hk.r11] at c
  have f : Frame [sR s₀ b n] s.mem t.mem := by
    rw [c.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  exact ⟨hk.write hz c.rd c.wr c.sp (fun r hr => c.other r (by
    simp only [VG.Proof.Pbkdf2.Whole.Arm.kregs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide))
    hb' hb f, c.other, c.mem⟩

omit hp hz in
/-- After such a copy, the bytes at `b` are those at `a`. -/
theorem copied_byte {m : Mem} {a b n : Nat} (hn : n ≤ 2 ^ 32) (i : Nat) (hi : i < n) :
    VG.WriteBytes.writeBytes m (VG.Proof.Pbkdf2.Whole.Arm.A s₀ b) (bytesAt m (VG.Proof.Pbkdf2.Whole.Arm.A s₀ a) n) (VG.Proof.Pbkdf2.Whole.Arm.A s₀ b + BitVec.ofNat 64 i) = m (VG.Proof.Pbkdf2.Whole.Arm.A s₀ a + BitVec.ofNat 64 i) := by
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega), bytesAt_getD' _ _ hi]

end

/-- After the key: where it is, and its `K₀`. -/
structure Keyed (hF : FnsOK F) (s₀ s : State) : Prop where
  kr : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s
  r2 : s.gpr .r2 = VG.Proof.Pbkdf2.Whole.Arm.kp F s₀
  r3 : s.gpr .r3 = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Whole.Arm.kl F s₀)
  k0 : blockKey hF.hH.SH.H (bytesAt s.mem (State.addr (VG.Proof.Pbkdf2.Whole.Arm.kp F s₀)) (VG.Proof.Pbkdf2.Whole.Arm.kl F s₀)) = VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F) (hF : FnsOK F)
include hp hz hF

theorem keyed_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) : WP isa F.key s (VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀) :=
  WP.mono (VG.Proof.Pbkdf2.Whole.Arm.key_ok hp hz hF.hH hk) fun _ ⟨k, d, c, b⟩ => ⟨k, d, c, b⟩

omit hp in
theorem su1_ok {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀ s) :
    WP isa (.block F.initArgs) s
      fun t => VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀ t ∧ t.gpr .r0 = dO s₀ F.st0O ∧ t.gpr .r1 = dO s₀ F.st1O ∧ t.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀ := by
  have hl := layout (F := F); have he := end_le hz; have hz_reach := hz.reach
  unfold Fns.initArgs
  rw [List.append_assoc]
  refine scr_ok h.kr (by omega) fun s₁ u₁ => ?_
  have k₁ := h.kr.upd12 (by decide) u₁
  refine scr_ok k₁ (by omega) fun s₂ u₂ => ?_
  have k₂ := k₁.upd12 (by decide) u₂
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil ⟨⟨k₂.upd (by decide) u₃, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.r2]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.r3]
  · rw [u₃.mem, u₂.mem, u₁.mem]; exact h.k0
  · rw [u₃.other _ (by decide), u₂.other _ (by decide) (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr]
  · rw [u₃.gpr, u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.kr.r11]

theorem su2_args {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀ s) (h0 : s.gpr .r0 = dO s₀ F.st0O)
    (h1 : s.gpr .r1 = dO s₀ F.st1O) (h12 : s.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀) :
    HiArgs hF.hH.SH hF.Wi s (dO s₀ F.st0O) (dO s₀ F.st1O) (VG.Proof.Pbkdf2.Whole.Arm.kp F s₀) (VG.Proof.Pbkdf2.Whole.Arm.scr s₀) (VG.Proof.Pbkdf2.Whole.Arm.kl F s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W; have hz_reach := hz.reach
  have hF_hWi := hF.hWi; have hS := hF.hH.hS
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  have hk := h.kr
  have kd : ∀ o n, o + n ≤ F.hkO → F.st0O ≤ o →
      Region.Disjoint ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.kp F s₀), VG.Proof.Pbkdf2.Whole.Arm.kl F s₀⟩ (sR s₀ o n) := fun o n h₁ h₂ =>
    VG.Proof.Pbkdf2.Whole.Arm.key_disj hp hz (part_sub (by omega_using [h₁, he, hl])) (part_disj hz (Or.inl h₁) (by omega) (by omega))
  have kls : Region.Disjoint ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.kp F s₀), VG.Proof.Pbkdf2.Whole.Arm.kl F s₀⟩ (lowR s₀ (hF.Wi * 8)) :=
    VG.Proof.Pbkdf2.Whole.Arm.key_disj hp hz (low_sub (by omega_using [hF_hWi, he, hl])) (low_disj hz (by omega) (by omega))
  exact
    { r0 := h0
      r1 := h1
      r2 := h.r2
      r3 := h.r3
      r12 := h12
      klB := by rw [hF.hH.hB]; exact VG.Proof.Pbkdf2.Whole.Arm.kl_le hp hz
      kl32 := by have := VG.Proof.Pbkdf2.Whole.Arm.kl_le hp hz; have hz_B := hz.B; omega_using [hz_B, this]
      sp := by rw [hk.sp]; exact hp.sp24
      cr := VG.Proof.Pbkdf2.Whole.Arm.key_cov hp hz hk
      cw := by
        rw [hS, e0, e1]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_low hp hk (by omega)
      i_o := by rw [hS, e0, e1]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      i_k := by rw [hS, e0]; exact (kd _ _ (by omega) (by omega)).symm
      i_s := by rw [hS, e0]; exact (low_disj hz (by omega_using [hF_hWi, hl]) (by omega)).symm
      o_k := by rw [hS, e1]; exact (kd _ _ (by omega) (by omega_using [hl])).symm
      o_s := by rw [hS, e1]; exact (low_disj hz (by omega_using [hF_hWi, hl]) (by omega)).symm
      k_s := kls
      b_i := by rw [hS, e0]; exact VG.Proof.Pbkdf2.Whole.Arm.b24 hp hk (part_sub (by omega))
      b_o := by rw [hS, e1]; exact VG.Proof.Pbkdf2.Whole.Arm.b24 hp hk (part_sub (by omega))
      b_k := VG.Proof.Pbkdf2.Whole.Arm.key_stk hp hz hk
      b_s := VG.Proof.Pbkdf2.Whole.Arm.b24 hp hk (low_sub (by omega))
      ni := by rw [hS, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      no := by rw [hS, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega
      nk := VG.Proof.Pbkdf2.Whole.Arm.key_toNat hp hz
      nsc := by have hp_nsc := hp.nsc; omega }

theorem su2_ok {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀ s) (h0 : s.gpr .r0 = dO s₀ F.st0O)
    (h1 : s.gpr .r1 = dO s₀ F.st1O) (h12 : s.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀) :
    WP isa (.frame (.push [.r12, .lr]) (.call F.hiN F.hiC) (.pop .r12 8)) s fun t => VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) opad) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have hF_hWi := hF.hWi; have hS := hF.hH.hS
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  refine hi_frame hF.hi hF.hiSt (VG.Proof.Pbkdf2.Whole.Arm.su2_args hp hz hF h h0 h1 h12) fun s' a r0 r1 => ⟨?_, ?_, ?_⟩
  · refine h.kr.call hp hz a fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [e0, hS], by omega, by omega⟩
    · exact .inr ⟨_, _, by rw [e1, hS], by omega_using [hl], by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · rw [h.k0, e0] at r0; exact r0
  · rw [h.k0, e1] at r1; exact r1

omit hF in
theorem K0_length (hF : FnsOK F) {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀ s) : (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀).length = F.H.B := by
  have := VG.Proof.Pbkdf2.Whole.Arm.kl_le hp hz
  rw [← h.k0]
  simp only [blockKey, hF.hH.hB, bytesAt_length, show ¬ F.H.B < VG.Proof.Pbkdf2.Whole.Arm.kl F s₀ by omega, ↓reduceIte,
    List.length_append, List.length_replicate]
  omega

/-- The key's inner state, copied for the salt. -/
theorem su3_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) (r0 : hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad))
    (r1 : hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) opad)) :
    WP isa (copy .r11 F.st0O .r11 F.stSO F.H.S) s fun t => VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) opad) ∧
      hF.hH.SH.Repr t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.stSO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hL := hz.reach
  refine WP.mono (VG.Proof.Pbkdf2.Whole.Arm.copy_part_ok hp hz hk hz.S.1 (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨k, _, m⟩ => ?_
  have f : Frame [sR s₀ F.stSO F.H.S] s.mem t.mem := by
    rw [m]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨k, VG.Proof.Pbkdf2.Whole.Arm.repr_keep hF.hH f (fun r hr => ?_) r0, VG.Proof.Pbkdf2.Whole.Arm.repr_keep hF.hH f (fun r hr => ?_) r1, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · refine hF.hH.repr _ _ _ _ _ (fun i hi => ?_) r0
    rw [m]; exact VG.Proof.Pbkdf2.Whole.Arm.copied_byte (by omega) i hi

omit hp hF in
/-- `update`'s arguments: the salt. -/
theorem su4_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) :
    WP isa (.block F.saltArgs) s
      fun t => VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ t ∧ t.gpr .r0 = dO s₀ F.stSO ∧ t.gpr .r1 = salt s₀ ∧ t.gpr .r7 = s₀.gpr .r3 ∧
        t.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀ ∧ count t = BitVec.ofNat 64 F.H.B ∧ t.mem = s.mem := by
  have hl := layout (F := F); have he := end_le hz; have hz_reach := hz.reach; have hz_B := hz.B
  unfold Fns.saltArgs
  refine scr_ok hk (by omega) fun s₁ u₁ => ?_
  have k₁ := hk.upd12 (by decide) u₁
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    Pbkdf2.Stream.Arm.wp_movw fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have k₆ := ((((k₁.upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd
    (by decide) u₆
  refine ⟨k₆, ?_, ?_, ?_, ?_, ?_, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide) (by decide), hk.r5]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide) (by decide), hk.r6]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide) (by decide), hk.r11]
  · simp only [count]
    rw [u₆.gpr, u₆.other .r2 (by decide), u₅.gpr, Pbkdf2.Stream.Arm.movw_ofNat (by omega), VG.Proof.Pbkdf2.Whole.Arm.zero_append,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

omit hF in
/-- The salt is apart from `scratch`, so `B + 4 + salt_len` does not wrap around. -/
theorem salt_fit : F.H.B + 4 + sl s₀ < 2 ^ 32 := by
  have h₁ : (saltR s₀).base.toNat + (saltR s₀).len ≤ 2 ^ 32 := by
    show (State.addr (salt s₀)).toNat + sl s₀ ≤ _; rw [toNat_addr]; exact hp.nsa
  have h₂ : (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F).base.toNat + (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F).len ≤ 2 ^ 32 := by
    show (State.addr (VG.Proof.Pbkdf2.Whole.Arm.scr s₀)).toNat + F.L8 ≤ _; rw [toNat_addr]; exact hp.nsc
  have h : sl s₀ + (F.W + F.H.S) * 8 ≤ 2 ^ 32 := Pbkdf2.Whole.len_add_le hp.sa_s h₁ h₂
  have hz_B := hz.B; have hz_S := hz.S; have hz_BS := hz.BS
  omega

theorem su5_args {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stSO) (h1 : s.gpr .r1 = salt s₀)
    (h7 : s.gpr .r7 = s₀.gpr .r3) (h10 : s.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀) :
    UpdL hF.hH s (dO s₀ F.stSO) (salt s₀) (VG.Proof.Pbkdf2.Whole.Arm.scr s₀) (sl s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W; have hz_reach := hz.reach
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stSO) (by omega)
  exact
    { r0 := h0
      r1 := h1
      r7 := by rw [h7, VG.Proof.Pbkdf2.Whole.Arm.ofNat_toNat32]
      r10 := h10
      hlen := (s₀.gpr .r3).isLt
      sp16 := by rw [hk.sp]; have hp_sp24 := hp.sp24; omega
      cd := VG.Proof.Pbkdf2.Whole.Arm.cov_salt hp hk
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_low hp hk (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hF.hH.Wb) (by omega) (by omega)).symm
      d_st := by rw [ea]; exact hp.sa_s.sub_right (part_sub (by omega))
      d_sc := hp.sa_s.sub_right (low_sub (by omega))
      b_st := by rw [ea]; exact VG.Proof.Pbkdf2.Whole.Arm.b16 hp hk (part_sub (by omega))
      b_d := hp.b_sa.sub_left (VG.Proof.Pbkdf2.Whole.Arm.below_sub hk)
      b_sc := VG.Proof.Pbkdf2.Whole.Arm.b16 hp hk (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega
      nd := hp.nsa
      nsc := by have hp_nsc := hp.nsc; omega }

theorem su5_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stSO) (h1 : s.gpr .r1 = salt s₀)
    (h7 : s.gpr .r7 = s₀.gpr .r3) (h10 : s.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀) (hc : count s = BitVec.ofNat 64 F.H.B)
    (hkl : (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀).length = F.H.B)
    (r0 : hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad))
    (r1 : hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) opad))
    (rS : hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.stSO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad)) :
    WP isa (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16)) s
      fun t => VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ t ∧ VG.Proof.Pbkdf2.Whole.Arm.States hF s₀ t.mem := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W; have hz_reach := hz.reach
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stSO) (by omega_using [he, hl])
  refine upd_frame hF.hH (VG.Proof.Pbkdf2.Whole.Arm.su5_args hp hz hF hk h0 h1 h7 h10) fun s' a r => ⟨hk.call hp hz (After.of_hmac a)
    fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega_using [this, hz_W]⟩
  all_goals have f := a.frame
  all_goals rw [ea] at f
  · refine VG.Proof.Pbkdf2.Whole.Arm.repr_keep hF.hH f (fun r hr => ?_) r0
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact part_disj hz (Or.inl (by omega)) (by omega_using [he, hl]) (by omega)
    · exact low_disj hz (by omega_using [this, hz_W, hl]) (by omega) |>.symm
    · exact (VG.Proof.Pbkdf2.Whole.Arm.b16 hp hk (part_sub (by omega))).symm
  · refine VG.Proof.Pbkdf2.Whole.Arm.repr_keep hF.hH f (fun r hr => ?_) r1
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact part_disj hz (Or.inl (by omega_using [hl])) (by omega) (by omega)
    · exact low_disj hz (by omega) (by omega) |>.symm
    · exact (VG.Proof.Pbkdf2.Whole.Arm.b16 hp hk (part_sub (by omega))).symm
  · have := r (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad) (by rw [ea]; exact rS) (by rw [xorPad_length, hkl, hc])
    rw [ea, hk.saltBytes hp] at this
    exact this

theorem setup_ok {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀ s) :
    WP isa F.setup s fun t => VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ t ∧ VG.Proof.Pbkdf2.Whole.Arm.States hF s₀ t.mem ∧ (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀).length = F.H.B := by
  have hkl := VG.Proof.Pbkdf2.Whole.Arm.K0_length hp hz hF h
  unfold Fns.setup
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.su1_ok hz hF h) fun s₁ ⟨k₁, a₀, a₁, a₁₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.su2_ok hp hz hF k₁ a₀ a₁ a₁₂) fun s₂ ⟨k₂, r0, r1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.su3_ok hp hz hF k₂ r0 r1) fun s₃ ⟨k₃, r0, r1, rS⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.su4_ok hz k₃) fun s₄ ⟨k₄, a₀, a₁, a₇, a₁₀, c₄, m₄⟩ => ?_)
  exact WP.mono (VG.Proof.Pbkdf2.Whole.Arm.su5_ok hp hz hF k₄ a₀ a₁ a₇ a₁₀ c₄ hkl (m₄ ▸ r0) (m₄ ▸ r1) (m₄ ▸ rS))
    fun t ⟨k, st⟩ => ⟨k, st, hkl⟩

end

end VG.Proof.Pbkdf2.Whole.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Block`. -/
section

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: a block of the output, up to `U₁`

As on x86 (`Proof/Pbkdf2/Whole/X86/Block.lean`): after `k` blocks of the
output (`Inv`), `out` holds the first `done k` bytes of `T₁ ‖ … ‖ T_k`, `r4`
is `done k`, and `scratch` holds `INT (k + 1)`, byte-reversed. A step copies
the salted inner state into the working state, absorbs `INT (k + 1)` into it
(`update`) and computes `U₁` with HMAC's `finalize`.
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Pbkdf2.Stream.Arm (Hash scrAt copy)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK cclob count)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_cmp wp_rev wp_str op2_imm op2_reg)
open VG.Proof.Hmac.Generic.Common (bytes_keep)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad hmacBlockKey)

variable {F : Fns}

/-- The pseudorandom function: HMAC keyed with the password. -/
abbrev prf (hF : FnsOK F) (s₀ : State) : List Byte → List Byte := hmacBlockKey hF.hH.SH.H (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀)

/-- `T₁ ‖ … ‖ T_k`, `T_i`, the number of blocks and the bytes written after `k` of them. -/
abbrev Gk (hF : FnsOK F) (s₀ : State) (k : Nat) : List Byte := Whole.G (VG.Proof.Pbkdf2.Whole.Arm.prf hF s₀) (VG.Proof.Pbkdf2.Whole.Arm.saltB s₀) (cc s₀) k
abbrev Tk (hF : FnsOK F) (s₀ : State) (i : Nat) : List Byte := Whole.Tb (VG.Proof.Pbkdf2.Whole.Arm.prf hF s₀) (VG.Proof.Pbkdf2.Whole.Arm.saltB s₀) (cc s₀) i
abbrev nbk (F : Fns) (s₀ : State) : Nat := Whole.nb F.H.D (ol s₀)
abbrev dn (F : Fns) (s₀ : State) (k : Nat) : Nat := Whole.done F.H.D (ol s₀) k

/-- After `k` blocks of the output. -/
structure Inv (hF : FnsOK F) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s
  st : VG.Proof.Pbkdf2.Whole.Arm.States hF s₀ s.mem
  k0l : (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀).length = F.H.B
  r4 : s.gpr .r4 = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Whole.Arm.dn F s₀ k)
  intW : s.mem.readW (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.intO) 32 = byteRev32 (BitVec.ofNat 32 (k + 1))
  glen : (VG.Proof.Pbkdf2.Whole.Arm.Gk hF s₀ k).length = k * F.H.D
  outB : bytesAt s.mem (State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀)) (VG.Proof.Pbkdf2.Whole.Arm.dn F s₀ k) = (VG.Proof.Pbkdf2.Whole.Arm.Gk hF s₀ k).take (VG.Proof.Pbkdf2.Whole.Arm.dn F s₀ k)

/-- The registers `Inv` fixes. -/
abbrev iregs : List Reg := [.r4, .r5, .r6, .r11]

/-- Where a step writes, before it copies `T` out: the working space, or
the parts of `scratch` from the working state up to `INT (i)`. -/
def Wks (F : Fns) (s₀ : State) (r : Region) : Prop :=
  (∃ k, r = lowR s₀ k ∧ k ≤ 8 * F.W) ∨ ∃ o n, r = sR s₀ o n ∧ F.stWO ≤ o ∧ o + n ≤ F.intO

section
variable {hF : FnsOK F} {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F)
include hp hz

omit hp in
theorem Wks.disj {r : Region} (h : VG.Proof.Pbkdf2.Whole.Arm.Wks F s₀ r) :
    (svR F s₀).Disjoint r ∧ Region.Sub r (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F) ∧ (sR s₀ F.st0O (3 * F.H.S)).Disjoint r ∧
      (sR s₀ F.intO 4).Disjoint r := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D
  rcases h with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
  · exact ⟨sv_low hz hk, low_sub (by omega), (low_disj hz (by omega) (by omega)).symm,
      (low_disj hz (by omega) (by omega)).symm⟩
  · exact ⟨sv_disj hz (by omega) (by omega_using [h₂, he]), part_sub (by omega),
      part_disj hz (Or.inl (by omega)) (by omega) (by omega), part_disj hz (Or.inr (by omega)) (by omega) (by omega)⟩

/-- `Inv` survives writes where a step writes, and to the stack below `sp`. -/
theorem Inv.keep {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Whole.Arm.iregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, VG.Proof.Pbkdf2.Whole.Arm.Wks F s₀ r ∨ r = stkR s₀) : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s' := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D
  have hsb : (stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F) := hp.b_s
  refine ⟨h.kr.keep hrd hwr hsp (fun r hr => hg r (by simp only [List.mem_cons] at hr ⊢; grind)) hf
    (fun r hr => ?_) (fun r hr => ?_), h.st.keep hz hf (fun r hr => ?_), h.k0l, by rw [hg _ (by simp), h.r4],
    ?_, h.glen, ?_⟩
  · rcases hw r hr with hw | rfl
    · exact (hw.disj hz).1
    · exact (hsb.sub_right (sv_sub hz)).symm
  · rcases hw r hr with hw | rfl
    · exact ⟨_, by simp, (hw.disj hz).2.1⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rcases hw r hr with hw | rfl
    · exact (hw.disj hz).2.2.1
    · exact (hsb.sub_right (part_sub (by omega))).symm
  · rw [← h.intW]
    refine hf.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases hw r hr with hw | rfl
    · exact (hw.disj hz).2.2.2
    · exact (hsb.sub_right (part_sub (by omega))).symm
  · rw [← h.outB]
    have osub : Region.Sub ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀), VG.Proof.Pbkdf2.Whole.Arm.dn F s₀ k⟩ (VG.Proof.Pbkdf2.Whole.Arm.outR s₀) :=
      Region.sub_prefix (Nat.min_le_right _ _)
    refine bytes_keep hf (fun r hr => ?_) (by
      have h1 : VG.Proof.Pbkdf2.Whole.Arm.dn F s₀ k ≤ ol s₀ := Nat.min_le_right _ _; have hp_no := hp.no; omega_using [hp_no, h1])
    rcases hw r hr with hw | rfl
    · exact (hp.o_s.sub_left osub).sub_right (hw.disj hz).2.1
    · exact hp.b_o.symm.sub_left osub

theorem Inv.same {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Whole.Arm.iregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s' :=
  h.keep hp hz hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp)

theorem Inv.upd {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) {d : Reg} (hd : d ∉ VG.Proof.Pbkdf2.Whole.Arm.iregs) {v : BitVec 32}
    (u : Upd s s' d v) : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s' :=
  h.same hp hz u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

theorem Inv.upd12 {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) {d : Reg} (hd : d ∉ VG.Proof.Pbkdf2.Whole.Arm.iregs) {v : BitVec 32}
    (u : Upd12 s s' d v) : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s' :=
  h.same hp hz u.rd u.wr u.sp (fun r hr => u.other r (fun e => hd (e ▸ hr)) (by
    simp only [VG.Proof.Pbkdf2.Whole.Arm.iregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) u.mem

/-- After a call that writes where a step writes. -/
theorem Inv.after {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, VG.Proof.Pbkdf2.Whole.Arm.Wks F s₀ r) : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s' := by
  have f := ha.frame
  rw [h.kr.stkE] at f
  refine h.keep hp hz ha.rd ha.wr ha.sp (fun r hr => ha.cs r (by
    simp only [VG.Proof.Pbkdf2.Whole.Arm.iregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
    simp only [VG.Proof.Pbkdf2.Whole.Arm.iregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) f fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact .inl (hw r hr)
  · simp only [List.mem_singleton] at hr; exact .inr hr

/-! ## The loop's start -/

omit hp hz in
theorem rev_eq (x : BitVec 32) : rev x = byteRev32 x := rfl

omit hz in
theorem addr_scr {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {o : Nat} (ho : o < F.L8) :
    State.addr (s.gpr .r11 + BitVec.ofNat 32 o) = VG.Proof.Pbkdf2.Whole.Arm.A s₀ o := by
  rw [hk.r11]; exact dO_addr hp ho

omit hp hz in
theorem beq_zero (x : BitVec 32) : (x - 0 == 0) = decide (x.toNat = 0) := by
  have e : x - 0 = x := by apply BitVec.eq_of_toNat_eq; simp
  rw [e]
  rcases Decidable.em (x = 0) with h | h
  · subst h; rfl
  · have h' : x.toNat ≠ 0 := fun t => h (BitVec.eq_of_toNat_eq (by rw [t]; rfl))
    rw [decide_eq_false h']
    exact beq_eq_false_iff_ne.2 h

/-- `INT (1)`, no bytes written, and whether `out_len` is 0. -/
theorem loopInit_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) (hst : VG.Proof.Pbkdf2.Whole.Arm.States hF s₀ s.mem) (hkl : (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀).length = F.H.B) :
    WP isa (.block F.loopInit) s fun t => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ 0 t ∧ t.z = decide (ol s₀ = 0) := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D; have hz_reach := hz.reach
  unfold Fns.loopInit
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_rev fun s₂ u₂ => ?_
  have k₂ := (hk.upd (by decide) u₁).upd (by decide) u₂
  refine wp_str (a := VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.intO) (by omega_using [hz_reach, he]) (VG.Proof.Pbkdf2.Whole.Arm.addr_scr hp k₂ (by omega_using [he]))
    (by rw [u₂.wr, u₁.wr]; exact in_sc hp hz hk.wr (by omega)) fun s₃ m₃ => ?_
  have f₃ : Frame [sR s₀ F.intO 4] s.mem s₃.mem := by
    rw [m₃.mem, u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₃ : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s₃ := hk.write hz (by rw [m₃.rd, u₂.rd, u₁.rd]) (by rw [m₃.wr, u₂.wr, u₁.wr])
    (by rw [m₃.sp, u₂.sp, u₁.sp])
    (fun r hr => by
      simp only [VG.Proof.Pbkdf2.Whole.Arm.kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [m₃.gpr, u₂.other r (by rcases hr with rfl | rfl | rfl <;> decide),
        u₁.other r (by rcases hr with rfl | rfl | rfl <;> decide)])
    (by omega) (by omega) f₃
  refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_arg hp (k₃.upd (by decide) u₄) (i := 2) (by decide)
    fun s₅ u₅ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₆ f₆ z₆ => WP.block_nil ⟨⟨?_, ?_, hkl, ?_, ?_, by simp [VG.Proof.Pbkdf2.Whole.Arm.Gk, Whole.G], ?_⟩, ?_⟩
  · exact ((k₃.upd (by decide) u₄).upd (by decide) u₅).same f₆.rd f₆.wr f₆.sp (fun r _ => by rw [f₆.gpr]) f₆.mem
  · rw [f₆.mem, u₅.mem, u₄.mem]
    exact hst.keep hz f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr]; simp [VG.Proof.Pbkdf2.Whole.Arm.dn, Whole.done]
  · rw [f₆.mem, u₅.mem, u₄.mem, m₃.mem, Mem.readW_writeW_self32, u₂.gpr, u₁.gpr]; rfl
  · simp [VG.Proof.Pbkdf2.Whole.Arm.dn, Whole.done, bytesAt]
  · rw [z₆, u₅.gpr, VG.Proof.Pbkdf2.Whole.Arm.beq_zero]

/-! ## A step: the working state, and `INT (i)` -/

/-- The salted inner state, copied into the working state. -/
theorem b1_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) :
    WP isa (copy .r11 F.stSO .r11 F.stWO F.H.S) s fun t => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad ++ VG.Proof.Pbkdf2.Whole.Arm.saltB s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_reach := hz.reach
  refine WP.mono (VG.Proof.Pbkdf2.Whole.Arm.copy_part_ok hp hz h.kr hz.S.1 (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨kt, g, m⟩ => ⟨?_, ?_⟩
  · have f : Frame [sR s₀ F.stWO F.H.S] s.mem t.mem := by
      rw [m]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    exact h.keep hp hz (kt.rd.trans h.kr.rd.symm) (kt.wr.trans h.kr.wr.symm) (kt.sp.trans h.kr.sp.symm)
      (fun r hr => g r (by
        simp only [VG.Proof.Pbkdf2.Whole.Arm.iregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide))
      f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (.inr ⟨_, _, rfl, Nat.le_refl _, by omega⟩)
  · refine hF.hH.repr _ _ _ _ _ (fun i hi => ?_) h.st.stS
    rw [m]; exact VG.Proof.Pbkdf2.Whole.Arm.copied_byte (by omega) i hi

omit hp hz in
theorem add_ofNat_eq (x : BitVec 32) {n : Nat} (h : x.toNat + n < 2 ^ 32) :
    x + BitVec.ofNat 32 n = BitVec.ofNat 32 (x.toNat + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := h
  omega

omit hz in
/-- The count of bytes absorbed, `B + salt_len + j`. -/
theorem count_salt {j : Nat} (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F) (hj : j ≤ 4) {s : State} (h2 : s.gpr .r2 = s₀.gpr .r3 + BitVec.ofNat 32 (F.H.B + j))
    (h3 : s.gpr .r3 = 0) : count s = BitVec.ofNat 64 (F.H.B + (sl s₀ + j)) := by
  have hsf := VG.Proof.Pbkdf2.Whole.Arm.salt_fit hp hz
  have : sl s₀ = (s₀.gpr .r3).toNat := rfl
  simp only [count]
  rw [h3, h2, VG.Proof.Pbkdf2.Whole.Arm.zero_append, VG.Proof.Pbkdf2.Whole.Arm.add_ofNat_eq _ (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  congr 1; omega

/-- `update`'s arguments: the working state, `INT (i)`, and the bytes absorbed. -/
theorem b2_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) :
    WP isa (.block F.updArgs) s fun t => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k t ∧ t.gpr .r0 = dO s₀ F.stWO ∧
      t.gpr .r1 = dO s₀ F.intO ∧ t.gpr .r7 = BitVec.ofNat 32 4 ∧ t.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀ ∧
      count t = BitVec.ofNat 64 (F.H.B + (sl s₀ + 0)) ∧ t.mem = s.mem := by
  have hl := layout (F := F); have he := end_le hz; have hz_reach := hz.reach
  simp only [Fns.updArgs, List.append_assoc]
  refine scr_ok h.kr (by omega) fun s₁ u₁ => ?_
  have i₁ := h.upd12 hp hz (by decide) u₁
  refine scr_ok i₁.kr (by omega_using [hz_reach, he]) fun s₂ u₂ => ?_
  have i₂ := i₁.upd12 hp hz (by decide) u₂
  refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_add (op2_imm hz.encB) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have i₆ := (((i₂.upd hp hz (by decide) u₃).upd hp hz (by decide) u₄).upd hp hz (by decide) u₅).upd hp hz
    (by decide) u₆
  refine ⟨i₆, ?_, ?_, ?_, ?_, VG.Proof.Pbkdf2.Whole.Arm.count_salt hp hz (by decide) ?_ u₆.gpr, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide) (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]; rfl
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.kr.r11]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.kr.r6]; rfl
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b3_args {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) (h0 : s.gpr .r0 = dO s₀ F.stWO)
    (h1 : s.gpr .r1 = dO s₀ F.intO) (h7 : s.gpr .r7 = BitVec.ofNat 32 4) (h10 : s.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀) :
    UpdL hF.hH s (dO s₀ F.stWO) (dO s₀ F.intO) (VG.Proof.Pbkdf2.Whole.Arm.scr s₀) 4 := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W; have hz_reach := hz.reach
  have := hF.hH.hWb
  have hk := h.kr
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have ei := dO_addr hp (o := F.intO) (by omega_using [he])
  exact
    { r0 := h0
      r1 := h1
      r7 := h7
      r10 := h10
      hlen := by decide
      sp16 := by rw [hk.sp]; have hp_sp24 := hp.sp24; omega
      cd := by
        rw [ei]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          obtain ⟨r', hr', off, e, l⟩ := VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk (o := F.intO) (n := 4) (by omega)
          exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_low hp hk (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hF.hH.Wb) (by omega) (by omega)).symm
      d_st := by rw [ei, ea]; exact part_disj hz (Or.inr (by omega)) (by omega) (by omega)
      d_sc := by rw [ei]; exact (low_disj hz (k := hF.hH.Wb) (by omega) (by omega)).symm
      b_st := by rw [ea]; exact VG.Proof.Pbkdf2.Whole.Arm.b16 hp hk (part_sub (by omega))
      b_d := by rw [ei]; exact VG.Proof.Pbkdf2.Whole.Arm.b16 hp hk (part_sub (by omega))
      b_sc := VG.Proof.Pbkdf2.Whole.Arm.b16 hp hk (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega
      nd := by rw [dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he]
      nsc := by have hp_nsc := hp.nsc; omega }

/-- `update` with `INT (k + 1)`. -/
theorem b3_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) (h0 : s.gpr .r0 = dO s₀ F.stWO)
    (h1 : s.gpr .r1 = dO s₀ F.intO) (h7 : s.gpr .r7 = BitVec.ofNat 32 4) (h10 : s.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀)
    (hc : count s = BitVec.ofNat 64 (F.H.B + (sl s₀ + 0)))
    (hr : hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad ++ VG.Proof.Pbkdf2.Whole.Arm.saltB s₀)) :
    WP isa (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16)) s
      fun t => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k t ∧
        hF.hH.SH.Repr t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad ++ VG.Proof.Pbkdf2.Whole.Arm.saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W; have hz_reach := hz.reach
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have ei := dO_addr hp (o := F.intO) (by omega)
  refine upd_frame hF.hH (VG.Proof.Pbkdf2.Whole.Arm.b3_args hp hz h h0 h1 h7 h10) fun s' a r => ⟨h.after hp hz (After.of_hmac a)
    fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], Nat.le_refl _, by omega⟩
    · exact .inl ⟨_, rfl, by omega_using [this, hz_W]⟩
  · have := r _ (by rw [ea]; exact hr) (by
      rw [hc, List.length_append, xorPad_length, h.k0l, bytesAt_length]; rfl)
    rwa [ea, ei, Whole.bytes_rev_int h.intW] at this

/-! ## A step: `U₁` -/

omit hp hz in
theorem FnsOK.reprOK (hF : FnsOK F) : ReprOK hF.hH.SH := fun m m' p q msg hb =>
  hF.hH.repr m m' p q msg (fun i hi => hb i (by rw [hF.hH.hS]; exact hi))

/-- HMAC's `finalize`'s arguments. -/
theorem b4_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) :
    WP isa (.block F.finArgs) s fun t => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k t ∧ t.gpr .r0 = dO s₀ F.stWO ∧
      t.gpr .r1 = dO s₀ F.st1O ∧ t.gpr .r10 = dO s₀ F.uO ∧ t.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀ ∧
      count t = BitVec.ofNat 64 (F.H.B + (sl s₀ + 4)) ∧ t.mem = s.mem := by
  have hl := layout (F := F); have he := end_le hz; have hz_reach := hz.reach
  simp only [Fns.finArgs, List.append_assoc]
  refine scr_ok h.kr (by omega_using [hz_reach, he, hl]) fun s₁ u₁ => ?_
  have i₁ := h.upd12 hp hz (by decide) u₁
  refine scr_ok i₁.kr (by omega) fun s₂ u₂ => ?_
  have i₂ := i₁.upd12 hp hz (by decide) u₂
  refine scr_ok i₂.kr (by omega) fun s₃ u₃ => ?_
  have i₃ := i₂.upd12 hp hz (by decide) u₃
  refine wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_add (op2_imm hz.encB4) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have i₆ := ((i₃.upd hp hz (by decide) u₄).upd hp hz (by decide) u₅).upd hp hz (by decide) u₆
  refine ⟨i₆, ?_, ?_, ?_, ?_, VG.Proof.Pbkdf2.Whole.Arm.count_salt hp hz (by decide) ?_ u₆.gpr, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide) (by decide),
      u₂.other _ (by decide) (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide) (by decide),
      u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide) (by decide),
      u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.kr.r11]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide) (by decide),
      u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.kr.r6]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b5_args {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) (h0 : s.gpr .r0 = dO s₀ F.stWO)
    (h1 : s.gpr .r1 = dO s₀ F.st1O) (h10 : s.gpr .r10 = dO s₀ F.uO) (h12 : s.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀) :
    HfArgs hF.hH.SH hF.Wf s (dO s₀ F.stWO) (dO s₀ F.st1O) (dO s₀ F.uO) (VG.Proof.Pbkdf2.Whole.Arm.scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W; have hz_reach := hz.reach
  have hF_hWf := hF.hWf; have hS := hF.hH.hS; have hD := hF.hH.hD
  have hk := h.kr
  have ew := dO_addr hp (o := F.stWO) (by omega_using [he, hl])
  have e1 := dO_addr hp (o := F.st1O) (by omega_using [he, hl])
  have eu := dO_addr hp (o := F.uO) (by omega)
  exact
    { r0 := h0
      r1 := h1
      r10 := h10
      r12 := h12
      sp := by rw [hk.sp]; exact hp.sp24
      cr := by
        rw [hS, e1]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          obtain ⟨r', hr', off, e, l⟩ := VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk (o := F.st1O) (n := F.H.S) (by omega_using [he, hl])
          exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [hS, hD, ew, eu]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk (by omega_using [he, hl])
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_low hp hk (by omega_using [hF_hWf, he, hl])
      i_u := by rw [hS, ew, e1]; exact part_disj hz (Or.inr (by omega)) (by omega) (by omega)
      i_o := by rw [hS, hD, ew, eu]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      i_s := by rw [hS, ew]; exact (low_disj hz (by omega_using [hF_hWf, hl]) (by omega)).symm
      u_o := by rw [hS, hD, e1, eu]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      u_s := by rw [hS, e1]; exact (low_disj hz (by omega_using [hF_hWf, hl]) (by omega)).symm
      o_s := by rw [hD, eu]; exact (low_disj hz (by omega_using [hF_hWf, hl]) (by omega)).symm
      b_i := by rw [hS, ew]; exact VG.Proof.Pbkdf2.Whole.Arm.b24 hp hk (part_sub (by omega))
      b_u := by rw [hS, e1]; exact VG.Proof.Pbkdf2.Whole.Arm.b24 hp hk (part_sub (by omega))
      b_o := by rw [hD, eu]; exact VG.Proof.Pbkdf2.Whole.Arm.b24 hp hk (part_sub (by omega))
      b_s := VG.Proof.Pbkdf2.Whole.Arm.b24 hp hk (low_sub (by omega))
      ni := by rw [hS, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nu := by rw [hS, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      no := by rw [hD, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nsc := by have hp_nsc := hp.nsc; omega_using [hp_nsc, hF_hWf, he, hl] }

/-- HMAC's `finalize`: `U₁ = PRF (salt ‖ INT (k + 1))`. -/
theorem b5_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) (h0 : s.gpr .r0 = dO s₀ F.stWO)
    (h1 : s.gpr .r1 = dO s₀ F.st1O) (h10 : s.gpr .r10 = dO s₀ F.uO) (h12 : s.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀)
    (hc : count s = BitVec.ofNat 64 (F.H.B + (sl s₀ + 4)))
    (hr : hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) ipad ++ VG.Proof.Pbkdf2.Whole.Arm.saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.frame (.push [.r10, .r12]) (.call F.hfN F.hfC) (.pop .r12 8)) s fun t => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k t ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.uO) F.H.D = VG.Proof.Pbkdf2.Whole.Arm.prf hF s₀ (VG.Proof.Pbkdf2.Whole.Arm.saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W; have hz_reach := hz.reach
  have hF_hWf := hF.hWf; have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have ew := dO_addr hp (o := F.stWO) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  have eu := dO_addr hp (o := F.uO) (by omega)
  have hsf := VG.Proof.Pbkdf2.Whole.Arm.salt_fit hp hz
  refine hf_frame (FnsOK.reprOK hF) (by rw [hS]; omega_using [hz_S]) hF.hf hF.hfSt (VG.Proof.Pbkdf2.Whole.Arm.b5_args hp hz h h0 h1 h10 h12)
    fun s' a post => ⟨h.after hp hz a fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [ew, hS], Nat.le_refl _, by omega⟩
    · exact .inr ⟨_, _, by rw [eu, hD], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega_using [hF_hWf]⟩
  · have := post (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) (VG.Proof.Pbkdf2.Whole.Arm.saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) (by rw [h.k0l, hB])
      (by rw [h.k0l, List.length_append, bytesAt_length]; simp only [Spec.Pbkdf2.int, List.length_cons,
        List.length_nil]; omega_using [hsf])
      (by rw [ew, ← List.append_assoc]; exact hr)
      (by
        have e : s.gpr .r3 ++ s.gpr .r2 = count s := rfl
        rw [e, hc, List.length_append, bytesAt_length, hB]
        simp only [Spec.Pbkdf2.int, List.length_cons, List.length_nil])
      (by rw [e1]; exact h.st.st1)
    rwa [eu, hD] at this

end

end VG.Proof.Pbkdf2.Whole.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Loop`. -/
section

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: the rest of a block, the loop, and `pbkdf2`

As on x86 (`Proof/Pbkdf2/Whole/X86/Loop.lean`): a step copies `U₁` into `T`,
runs `iterate` for the rest of the chain, copies as much of `T` as the output
still needs (`copyLoop_ok`, `copy`'s loop for a length in `r9`), and moves on
to the next block; after the last one, `out` holds the derived key, and the
caller's registers are restored (`restore_ok`, HMAC's for any working space an
immediate offset reaches).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Pbkdf2.Stream.Arm (Hash scrAt copy)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK cclob count count_loop nm addr3 ofNat_succ32 left_val left_z CopyInv
  SavedRegs savedRegs saved8 saved8_fst saved8_sub saved_mem restoreList_ok restore_eq)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_subs wp_cmp wp_rev wp_ldr wp_str wp_ldrb wp_strb
  op2_imm op2_reg sub_beq sub_ofNat contains_offset eval_eq)
open VG.Proof.Hmac.Generic.Common (bytes_keep writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad hmacBlockKey)

/-! ## `copy`'s loop, for a length in `r9` -/

/-- The loop of `copy`, from `r8 = 0` and `r9 = n > 0`. -/
theorem copyLoop_ok {src dst : Reg} (hs : src ∉ cclob) (hd : dst ∉ cclob)
    {so d n : Nat} (hso : so < 4096) (hdo : d < 4096) (hn : 0 < n) (hn' : n < 2 ^ 32) {s : State}
    (h8 : s.gpr .r8 = 0) (h9 : s.gpr .r9 = BitVec.ofNat 32 n)
    (hsw : (s.gpr src).toNat + so + n ≤ 2 ^ 32) (hdw : (s.gpr dst).toNat + d + n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr src) + BitVec.ofNat 64 so, n⟩
      ⟨State.addr (s.gpr dst) + BitVec.ofNat 64 d, n⟩) :
    WP isa (.loop (.block [.dp .add .r2 src (.reg .r8), .ldrb .r12 .r2 so, .dp .add .r2 dst (.reg .r8),
      .strb .r12 .r2 d, .dp .add .r8 .r8 (.imm 1), .subs .r9 .r9 (.imm 1)]) .ne) s
      (CopyInv s (State.addr (s.gpr src) + BitVec.ofNat 64 so) (State.addr (s.gpr dst) + BitVec.ofNat 64 d) n n) := by
  generalize eA : State.addr (s.gpr src) + BitVec.ofNat 64 so = A at hin hsep ⊢
  generalize eB : State.addr (s.gpr dst) + BitVec.ofNat 64 d = B at hout hsep ⊢
  have i0 : CopyInv s A B n 0 s :=
    ⟨rfl, rfl, rfl, fun _ _ => rfl, h8, h9, by rw [bytesAt, List.range_zero, List.map_nil, VG.WriteBytes.writeBytes_nil]⟩
  refine count_loop hn (CopyInv s A B n) (fun k hk t h => ?_) i0
  refine wp_add (op2_reg _ _) fun t₁ u₁ => ?_
  refine wp_ldrb (a := A + BitVec.ofNat 64 k) hso
    (by rw [u₁.gpr, h.other src hs, h.r8, addr3 (by omega), eA])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₂ u₂ => ?_
  refine wp_add (op2_reg _ _) fun t₃ u₃ => ?_
  refine wp_strb (a := B + BitVec.ofNat 64 k) hdo
    (by rw [u₃.gpr, u₂.other dst (nm hd .r12), u₁.other dst (nm hd .r2), h.other dst hd,
      u₂.other .r8 (by decide), u₁.other .r8 (by decide), h.r8, addr3 (by omega), eB])
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₄ m₄ => ?_
  refine wp_add (op2_imm (by decide)) fun t₅ u₅ => wp_subs (op2_imm (by decide)) fun t₆ u₆ z₆ =>
    WP.block_nil ?_
  have h8' : t₅.gpr .r8 = BitVec.ofNat 32 (k + 1) := by
    rw [u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r8,
      ofNat_succ32]
  have h9' : t₅.gpr .r9 = BitVec.ofNat 32 (n - k) := by
    rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r9]
  refine ⟨⟨by rw [u₆.rd, u₅.rd, m₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, m₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₆.sp, u₅.sp, m₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr => by
      rw [u₆.other r (nm hr .r9), u₅.other r (nm hr .r8), m₄.gpr, u₃.other r (nm hr .r2), u₂.other r (nm hr .r12),
        u₁.other r (nm hr .r2), h.other r hr],
    by rw [u₆.other _ (by decide), h8'], by rw [u₆.gpr, h9', left_val hk], ?_⟩, ?_⟩
  · have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
    have v : (t₃.gpr .r12).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, h.mem]
      simp only [VG.WriteBytes.writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega), ↓reduceIte]
      ext i hi; simp
    have e' := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega_using [hk, hn'])
    rw [hl] at e'
    rw [u₆.mem, u₅.mem, m₄.mem, v, u₃.mem, u₂.mem, u₁.mem, h.mem, bytesAt_snoc', e']
  · rw [z₆, h9', left_z hk hn']

/-! ## Restoring our caller's registers -/

/-- `VG.Proof.Pbkdf2.Stream.Arm.restore_ok`, for any working space before
the save area that an immediate offset reaches. -/
theorem restore_ok (H : VG.Impl.Pbkdf2.Stream.Arm.Hash) {s : State} {scr : BitVec 32} {L : Nat} (h11 : s.gpr .r11 = scr)
    (hW : 8 * H.W + 36 ≤ 4096) {s₀ : State} (hs : SavedRegs H scr s₀ s.mem) (hsc : ⟨State.addr scr, L⟩ ∈ s.wr)
    (hL : 8 * H.W + 36 ≤ L) (hfit : scr.toNat + L ≤ 2 ^ 32) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ {d}, d + 4 ≤ L →
      InRegions (t.rd ++ t.wr) (State.addr scr + BitVec.ofNat 64 d) 4 := fun hr hw d hd => by
    rw [hr, hw]; exact Hmac.Generic.Common.InRegions.right' ⟨_, hsc, VG.Proof.MdStream.Arm.contains_offset hd (by omega_using [hd, hfit])⟩
  rw [restore_eq]
  refine VG.Proof.Pbkdf2.Stream.Arm.restoreList_ok (saved8 H) s _ (by rw [saved8_fst]; decide) (fun p hp => ?_)
    fun s₁ hl ho hm hrd hwr hsp => ?_
  · have := saved_mem H (saved8_sub H hp)
    refine ⟨?_, by omega, by rw [h11]; omega, by rw [h11]; exact io rfl rfl (by omega)⟩
    simp only [saved8, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  have e11 : s₁.gpr .r11 = scr := by
    rw [ho _ (by rw [saved8_fst]; decide), h11]
  refine wp_ldr (by omega) (addr_add (by rw [e11]; omega)) (by rw [e11]; exact io hrd hwr (by omega))
    fun s₂ u => WP.block_nil ⟨by rw [u.mem, hm], by rw [u.rd, hrd], by rw [u.wr, hwr], by rw [u.sp, hsp],
      fun r hr => ?_⟩
  have hv : ∀ p ∈ saved8 H, s₂.gpr p.1 = s₀.gpr p.1 := fun p hp => by
    have h1 : p.1 ≠ .r11 := by
      simp only [saved8, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
    rw [u.other _ h1, hl p hp, h11, hs p (saved8_sub H hp)]
  simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hv (.r4, 8 * H.W) (by simp [saved8])
  · exact hv (.r5, 8 * H.W + 4) (by simp [saved8])
  · exact hv (.r6, 8 * H.W + 8) (by simp [saved8])
  · exact hv (.r7, 8 * H.W + 12) (by simp [saved8])
  · exact hv (.r8, 8 * H.W + 16) (by simp [saved8])
  · exact hv (.r9, 8 * H.W + 20) (by simp [saved8])
  · exact hv (.r10, 8 * H.W + 24) (by simp [saved8])
  · exact hv (.lr, 8 * H.W + 28) (by simp [saved8])
  · rw [u.gpr, e11, hm, hs (.r11, 8 * H.W + 32) (by simp [Hash.saved])]

variable {F : Fns}

section
variable {hF : FnsOK F} {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F)
include hp hz

/-! ## A step: `T`, from `U₁` and `iterate` -/

/-- `T ← U₁`. -/
theorem b6_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) {u : List Byte} (hu : bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.uO) F.H.D = u) :
    WP isa (copy .r11 F.uO .r11 F.tO F.H.D) s fun t => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k t ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.uO) F.H.D = u ∧ bytesAt t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.tO) F.H.D = u := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_reach := hz.reach
  refine WP.mono (VG.Proof.Pbkdf2.Whole.Arm.copy_part_ok hp hz h.kr hz.D.1 (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨kt, g, m⟩ => ?_
  have f : Frame [sR s₀ F.tO F.H.D] s.mem t.mem := by
    rw [m]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨h.keep hp hz (kt.rd.trans h.kr.rd.symm) (kt.wr.trans h.kr.wr.symm) (kt.sp.trans h.kr.sp.symm)
      (fun r hr => g r (by
        simp only [VG.Proof.Pbkdf2.Whole.Arm.iregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide))
      f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (.inr ⟨_, _, rfl, by omega, by omega⟩), ?_, ?_⟩
  · rw [bytes_keep f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega))
      (by omega_using [hz_D])]
    exact hu
  · rw [m, Hmac.Generic.Common.bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hz_D])]
    exact hu

/-- `iterate`'s arguments: the key's states, `U`, `c - 1`, `T` and `scratch`. -/
theorem b7_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) :
    WP isa (.block F.iterArgs) s fun t => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k t ∧ t.gpr .r0 = dO s₀ F.st0O ∧
      t.gpr .r1 = dO s₀ F.uO ∧ t.gpr .r3 = dO s₀ F.tO ∧ t.gpr .r2 = stackArg s₀ 0 - 1 ∧
      t.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀ ∧ t.mem = s.mem := by
  have hl := layout (F := F); have he := end_le hz; have hz_reach := hz.reach
  simp only [Fns.iterArgs, List.append_assoc]
  refine scr_ok h.kr (by omega) fun s₁ u₁ => ?_
  have i₁ := h.upd12 hp hz (by decide) u₁
  refine scr_ok i₁.kr (by omega) fun s₂ u₂ => ?_
  have i₂ := i₁.upd12 hp hz (by decide) u₂
  refine scr_ok i₂.kr (by omega) fun s₃ u₃ => ?_
  have i₃ := i₂.upd12 hp hz (by decide) u₃
  refine wp_arg hp i₃.kr (i := 0) (by decide) fun s₄ u₄ => wp_sub (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  have i₆ := ((i₃.upd hp hz (by decide) u₄).upd hp hz (by decide) u₅).upd hp hz (by decide) u₆
  refine ⟨i₆, ?_, ?_, ?_, ?_, ?_, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide) (by decide),
      u₂.other _ (by decide) (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide) (by decide),
      u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), i₃.kr.r11]

theorem b8_args {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) (h0 : s.gpr .r0 = dO s₀ F.st0O)
    (h1 : s.gpr .r1 = dO s₀ F.uO) (h3 : s.gpr .r3 = dO s₀ F.tO) (h2 : s.gpr .r2 = stackArg s₀ 0 - 1)
    (h12 : s.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀) :
    ItArgs hF.hH.SH hF.Wt s (dO s₀ F.st0O) (dO s₀ F.uO) (stackArg s₀ 0 - 1) (dO s₀ F.tO) (VG.Proof.Pbkdf2.Whole.Arm.scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W; have hz_reach := hz.reach
  have hF_hWt := hF.hWt; have hS := hF.hH.hS; have hD := hF.hH.hD
  have hk := h.kr
  have e0 := dO_addr hp (o := F.st0O) (by omega_using [he, hl])
  have eu := dO_addr hp (o := F.uO) (by omega)
  have et := dO_addr hp (o := F.tO) (by omega)
  exact
    { r0 := h0
      r1 := h1
      r2 := h2
      r3 := h3
      r12 := h12
      sp := by rw [hk.sp]; exact hp.sp24
      cr := by
        rw [hS, hD, e0, eu]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · obtain ⟨r', hr', off, e, l⟩ := VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk (o := F.st0O) (n := 2 * F.H.S) (by omega_using [he, hl])
            exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
          · obtain ⟨r', hr', off, e, l⟩ := VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk (o := F.uO) (n := F.H.D) (by omega)
            exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [hD, et]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.Arm.cov_low hp hk (by omega_using [hF_hWt, he, hl])
      k_t := by rw [hS, hD, e0, et]; exact part_disj hz (Or.inl (by omega_using [hl])) (by omega) (by omega)
      k_s := by rw [hS, e0]; exact (low_disj hz (by omega) (by omega)).symm
      u_t := by rw [hD, eu, et]; exact part_disj hz (Or.inl (by omega_using [hl])) (by omega) (by omega)
      u_s := by rw [hD, eu]; exact (low_disj hz (by omega) (by omega)).symm
      t_s := by rw [hD, et]; exact (low_disj hz (by omega_using [hF_hWt, hl]) (by omega)).symm
      b_k := by rw [hS, e0]; exact VG.Proof.Pbkdf2.Whole.Arm.b24 hp hk (part_sub (by omega))
      b_u := by rw [hD, eu]; exact VG.Proof.Pbkdf2.Whole.Arm.b24 hp hk (part_sub (by omega))
      b_t := by rw [hD, et]; exact VG.Proof.Pbkdf2.Whole.Arm.b24 hp hk (part_sub (by omega))
      b_s := VG.Proof.Pbkdf2.Whole.Arm.b24 hp hk (low_sub (by omega))
      nk := by rw [hS, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nu := by rw [hD, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nt := by rw [hD, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nsc := by have hp_nsc := hp.nsc; omega_using [hp_nsc, hF_hWt, he, hl] }

/-- `iterate`: `T_{k + 1}`. -/
theorem b8_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) (h0 : s.gpr .r0 = dO s₀ F.st0O)
    (h1 : s.gpr .r1 = dO s₀ F.uO) (h3 : s.gpr .r3 = dO s₀ F.tO) (h2 : s.gpr .r2 = stackArg s₀ 0 - 1)
    (h12 : s.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀)
    (hu : bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.uO) F.H.D = VG.Proof.Pbkdf2.Whole.Arm.prf hF s₀ (VG.Proof.Pbkdf2.Whole.Arm.saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (ht : bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.tO) F.H.D = VG.Proof.Pbkdf2.Whole.Arm.prf hF s₀ (VG.Proof.Pbkdf2.Whole.Arm.saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.frame (.push [.r12, .lr]) (.call F.itN F.itC) (.pop .r12 8)) s fun t => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k t ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.tO) F.H.D = VG.Proof.Pbkdf2.Whole.Arm.Tk hF s₀ (k + 1) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W; have hz_reach := hz.reach
  have hF_hWt := hF.hWt; have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have eu := dO_addr hp (o := F.uO) (by omega)
  have et := dO_addr hp (o := F.tO) (by omega)
  refine it_frame (FnsOK.reprOK hF) (by rw [hS]; omega_using [hz_S]) (by rw [hD]; omega_using [hz_D]) hF.it hF.itSt
    (VG.Proof.Pbkdf2.Whole.Arm.b8_args hp hz h h0 h1 h3 h2 h12) fun s' a post => ⟨h.after hp hz a fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [et, hD], by omega_using [hl], by omega⟩
    · exact .inl ⟨_, rfl, by omega_using [hF_hWt]⟩
  · have := post (VG.Proof.Pbkdf2.Whole.Arm.K0 hF s₀) (by rw [h.k0l, hB]) (by rw [e0]; exact h.st.st0)
      (by rw [e0, hS, Hmac.Generic.Common.add_ofNat_add]; exact h.st.st1)
    rw [et, hD, eu, hu, ht] at this
    rw [this]
    have hc := hp.c0
    rw [show (stackArg s₀ 0 - 1).toNat = cc s₀ - 1 by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 1 ≤ (stackArg s₀ 0).toNat; exact hc)]; rfl]
    rfl

/-! ## A step: copying `T` out -/

omit hp hz in
theorem arg_ofNat (i : Nat) : stackArg s₀ i = BitVec.ofNat 32 (stackArg s₀ i).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

omit hp hz in
theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The bytes of `T` the output still needs. -/
theorem outLen_ok {k : Nat} (hk : k * F.H.D < ol s₀) {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) :
    WP isa F.outLen s fun t => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k t ∧
      t.gpr .r9 = BitVec.ofNat 32 (min (ol s₀ - k * F.H.D) F.H.D) ∧ t.mem = s.mem := by
  have hD := hz.D; have hol : ol s₀ < 2 ^ 32 := (stackArg s₀ 2).isLt
  have hdn : VG.Proof.Pbkdf2.Whole.Arm.dn F s₀ k = k * F.H.D := by show min _ _ = _; omega
  unfold Fns.outLen
  refine WP.seq (wp_arg hp h.kr (i := 2) (by decide) fun s₁ u₁ => wp_sub (op2_reg _ _) fun s₂ u₂ =>
    wp_lt hz.encD fun s₃ g₃ m₃ rd₃ wr₃ sp₃ z₃ => WP.block_nil ?_)
  have i₂ := (h.upd hp hz (by decide) u₁).upd hp hz (by decide) u₂
  have i₃ := i₂.same hp hz rd₃ wr₃ sp₃ (fun r hr => g₃ r (by
    simp only [VG.Proof.Pbkdf2.Whole.Arm.iregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) m₃
  have e₂ : s₂.gpr .r9 = BitVec.ofNat 32 (ol s₀ - k * F.H.D) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.r4, hdn, VG.Proof.Pbkdf2.Whole.Arm.arg_ofNat 2,
      sub_ofNat (by have : ol s₀ = (stackArg s₀ 2).toNat := rfl; omega)]
  have e₃ : s₃.gpr .r9 = BitVec.ofNat 32 (ol s₀ - k * F.H.D) := by rw [g₃ _ (by decide), e₂]
  have m₃' : s₃.mem = s.mem := by rw [m₃, u₂.mem, u₁.mem]
  have z : s₃.z = decide (ol s₀ - k * F.H.D < F.H.D) := by
    rw [z₃, e₂, VG.Proof.Pbkdf2.Whole.Arm.toNat_ofNat32 (by omega_using [hol]), VG.Proof.Pbkdf2.Whole.Arm.toNat_ofNat32 (by omega)]
  refine WP.ite (decide (ol s₀ - k * F.H.D < F.H.D)) (by show VG.Arm.eval .eq s₃ = _; rw [eval_eq, z])
    (fun hT => WP.block_nil ?_)
    fun hF' => Pbkdf2.Stream.Arm.wp_movw fun s₄ u₄ => WP.block_nil ⟨i₃.upd hp hz (by decide) u₄, ?_, by rw [u₄.mem, m₃']⟩
  · have : ol s₀ - k * F.H.D < F.H.D := of_decide_eq_true hT
    exact ⟨i₃, by rw [e₃, Nat.min_eq_left (Nat.le_of_lt this)], m₃'⟩
  · have : ¬ ol s₀ - k * F.H.D < F.H.D := of_decide_eq_false hF'
    rw [u₄.gpr, Pbkdf2.Stream.Arm.movw_ofNat (by omega), Nat.min_eq_right (by omega)]

/-- Copying `n` bytes of `T` to `out` after the `k D` written. -/
theorem outLoop_ok {k n : Nat} (hn : 0 < n) (hkn : k * F.H.D + n ≤ ol s₀) (hnD : n ≤ F.H.D) {s : State}
    (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) (h9 : s.gpr .r9 = BitVec.ofNat 32 n) (hkD : k * F.H.D < ol s₀) :
    WP isa F.outLoop s fun t => VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ t ∧ t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r8 = BitVec.ofNat 32 n ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀) + BitVec.ofNat 64 (k * F.H.D))
        (bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.tO) n) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hD := hz.D; have hz_reach := hz.reach
  have hol : ol s₀ < 2 ^ 32 := (stackArg s₀ 2).isLt
  have hdn : VG.Proof.Pbkdf2.Whole.Arm.dn F s₀ k = k * F.H.D := by show min _ _ = _; omega
  have hno := hp.no
  have eO : State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀ + BitVec.ofNat 32 (k * F.H.D)) = State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀) + BitVec.ofNat 64 (k * F.H.D) :=
    addr_add (by have : ol s₀ = (stackArg s₀ 2).toNat := rfl; omega_using [hno, hkn, hn])
  have tO' : (VG.Proof.Pbkdf2.Whole.Arm.out s₀ + BitVec.ofNat 32 (k * F.H.D)).toNat = (VG.Proof.Pbkdf2.Whole.Arm.out s₀).toNat + k * F.H.D := by
    rw [VG.Proof.Pbkdf2.Whole.Arm.add_ofNat_eq _ (by have : ol s₀ = (stackArg s₀ 2).toNat := rfl; omega), VG.Proof.Pbkdf2.Whole.Arm.toNat_ofNat32 (by omega_using [hno, hkn, hn])]
  have osub : Region.Sub ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩ (VG.Proof.Pbkdf2.Whole.Arm.outR s₀) :=
    Offset.sub_base _ hkn
  unfold Fns.outLoop
  refine WP.seq (wp_arg hp h.kr (i := 1) (by decide) fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_)
  have k₃ := ((h.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃
  have e₉ : s₃.gpr .r9 = BitVec.ofNat 32 n := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h9]
  have e₁₀ : s₃.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.out s₀ + BitVec.ofNat 32 (k * F.H.D) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.r4, hdn]
  have e₄ : s₃.gpr .r4 = s.gpr .r4 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (VG.Proof.Pbkdf2.Whole.Arm.copyLoop_ok (src := .r11) (dst := .r10) (so := F.tO) (d := 0) (by decide) (by decide)
    (by omega_using [hz_reach, he, hl]) (by decide) hn (by omega_using [hD, hnD]) u₃.gpr e₉
    (by rw [k₃.r11]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl, hnD]) (by rw [e₁₀, tO']; omega_using [hno, hkn])
    (fun j hj => by
      rw [k₃.r11]
      exact ⟨VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F, List.mem_append_right _ (by rw [k₃.wr]; exact sc_mem hp),
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega_using [hj, hz_reach, he, hl, hnD])⟩)
    (fun j hj => by
      rw [e₁₀, eO, Hmac.Generic.Common.add_ofNat_add, Nat.zero_add]
      exact ⟨VG.Proof.Pbkdf2.Whole.Arm.outR s₀, by rw [k₃.wr, hp.wr]; simp, by
        rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega_using [hj, hkn]) (by omega_using [hj, hol, hkn])⟩)
    (by rw [k₃.r11, e₁₀, eO, Hmac.Generic.Common.add_ofNat_add, Nat.add_zero]
        exact (hp.o_s.sub_left osub).symm.sub_left (part_sub (F := F) (by omega_using [he, hl, hnD])))) fun t c => ?_
  rw [k₃.r11, e₁₀, eO, Hmac.Generic.Common.add_ofNat_add, Nat.add_zero] at c
  have cm : t.mem = VG.WriteBytes.writeBytes s.mem (State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀) + BitVec.ofNat 64 (k * F.H.D))
      (bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.tO) n) := by rw [c.mem, m₃]
  have f : Frame [⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩] s₃.mem t.mem := by
    rw [cm, m₃]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨k₃.keep c.rd c.wr c.sp (fun r hr => c.other r (by
      simp only [VG.Proof.Pbkdf2.Whole.Arm.kregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    (rs := [⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩]) f
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.o_s.sub_left osub).symm.sub_left (sv_sub hz))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, osub⟩),
    by rw [c.other _ (by decide), e₄], by rw [c.r8], cm⟩

/-- The rest of a step: as much of `T` as the output needs, copied out,
`INT (k + 2)`, and whether that was the last block. -/
theorem tail_ok {k : Nat} (hk : k < VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀) {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s)
    (ht : bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.tO) F.H.D = VG.Proof.Pbkdf2.Whole.Arm.Tk hF s₀ (k + 1)) :
    WP isa (.seq F.outLen (.seq F.outLoop (.block F.advance))) s fun t =>
      VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ (k + 1) t ∧ t.z = decide (k + 1 = VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hD := hz.D; have hz_reach := hz.reach
  have hol : ol s₀ < 2 ^ 32 := (stackArg s₀ 2).isLt
  have hno := hp.no
  have hkD : k * F.H.D < ol s₀ := (Whole.lt_nb hD.1).1 hk
  have hdn : VG.Proof.Pbkdf2.Whole.Arm.dn F s₀ k = k * F.H.D := by show min _ _ = _; omega
  generalize en : min (ol s₀ - k * F.H.D) F.H.D = n
  have hn : 0 < n := by omega_using [en, hkD, hD]
  have hkn : k * F.H.D + n ≤ ol s₀ := by omega_using [en, hkD]
  have hnD : n ≤ F.H.D := by omega_using [en]
  have hdn' : VG.Proof.Pbkdf2.Whole.Arm.dn F s₀ (k + 1) = k * F.H.D + n := by show min _ _ = _; rw [Nat.succ_mul]; omega_using [en, hkD]
  have osub : Region.Sub ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩ (VG.Proof.Pbkdf2.Whole.Arm.outR s₀) :=
    Offset.sub_base _ hkn
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.outLen_ok hp hz hkD h) fun s₁ ⟨i₁, c₁, m₁⟩ => ?_)
  rw [en] at c₁
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.outLoop_ok hp hz hn hkn hnD i₁ c₁ hkD) fun s₂ ⟨k₂, b₂, e₂, m₂⟩ => ?_)
  unfold Fns.advance
  refine wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  have k₃ := k₂.upd (by decide) u₃
  refine wp_ldr (a := VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.intO) (by omega_using [hz_reach, he]) (VG.Proof.Pbkdf2.Whole.Arm.addr_scr hp k₃ (by omega_using [he])) (by
      obtain ⟨r, hr, c⟩ := in_sc hp hz k₃.wr (o := F.intO) (n := 4) (by omega)
      exact ⟨r, List.mem_append_right _ hr, c⟩)
    fun s₄ u₄ => wp_rev fun s₅ u₅ => wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_rev fun s₇ u₇ => ?_
  have k₇ := (((k₃.upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆).upd (by decide) u₇
  refine wp_str (a := VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.intO) (by omega) (VG.Proof.Pbkdf2.Whole.Arm.addr_scr hp k₇ (by omega)) (in_sc hp hz k₇.wr (by omega))
    fun s₈ m₈ => ?_
  have fr₈ : Frame [sR s₀ F.intO 4] s₇.mem s₈.mem := by
    rw [m₈.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₈ := k₇.write hz m₈.rd m₈.wr m₈.sp (fun r _ => by rw [m₈.gpr]) (by omega) (by omega) fr₈
  refine wp_arg hp k₈ (i := 2) (by decide) fun s₉ u₉ => wp_cmp (op2_reg _ _) fun s₁₀ f₁₀ z₁₀ => WP.block_nil ?_
  have m₁₀ : s₁₀.mem = s₂.mem.writeW (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.intO) (s₇.gpr .r12) := by
    rw [f₁₀.mem, u₉.mem, m₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have fr₂ : Frame [sR s₀ F.intO 4] s₂.mem s₁₀.mem := by
    rw [m₁₀]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fr₁ : Frame [⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have dI : (sR s₀ F.intO 4).Disjoint ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩ :=
    ((hp.o_s.sub_left osub).sub_right (part_sub (by omega))).symm
  have r₂ : s₂.mem.readW (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.intO) 32 = byteRev32 (BitVec.ofNat 32 (k + 1)) := by
    rw [← i₁.intW]
    exact fr₁.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dI) (by decide)
  have e₇ : s₇.gpr .r12 = byteRev32 (BitVec.ofNat 32 (k + 1 + 1)) := by
    rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.mem, r₂, VG.Proof.Pbkdf2.Whole.Arm.rev_eq, VG.Proof.Pbkdf2.Whole.Arm.rev_eq, Whole.byteRev32_byteRev32, ofNat_succ32]
  have e₉ : s₉.gpr .r4 = BitVec.ofNat 32 (k * F.H.D + n) := by
    rw [u₉.other _ (by decide), m₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, b₂, e₂, i₁.r4, hdn, ← BitVec.ofNat_add]
  have hg : (VG.Proof.Pbkdf2.Whole.Arm.Gk hF s₀ (k + 1)) = VG.Proof.Pbkdf2.Whole.Arm.Gk hF s₀ k ++ VG.Proof.Pbkdf2.Whole.Arm.Tk hF s₀ (k + 1) := Whole.G_succ _ _ _ _
  have tl : (VG.Proof.Pbkdf2.Whole.Arm.Tk hF s₀ (k + 1)).length = F.H.D := by rw [← ht, bytesAt_length]
  refine ⟨⟨(k₈.upd (by decide) u₉).same f₁₀.rd f₁₀.wr f₁₀.sp (fun r _ => by rw [f₁₀.gpr]) f₁₀.mem, ?_, i₁.k0l,
    by rw [f₁₀.gpr, e₉, hdn'], by rw [m₁₀, Mem.readW_writeW_self32, e₇], ?_, ?_⟩, ?_⟩
  · refine i₁.st.keep hz (rs := [⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩, sR s₀ F.intO 4])
      ((fr₁.mono (by simp)).trans (fr₂.mono (by simp))) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.o_s.sub_left osub).sub_right (part_sub (by omega_using [he, hl]))).symm
    · exact part_disj hz (Or.inl (by omega_using [hl])) (by omega) (by omega)
  · rw [hg, List.length_append, i₁.glen, tl, Nat.succ_mul]
  · have osub' : Region.Sub ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀), k * F.H.D + n⟩ (VG.Proof.Pbkdf2.Whole.Arm.outR s₀) := Region.sub_prefix hkn
    rw [hdn', bytes_keep fr₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.o_s.sub_left osub').sub_right (part_sub (by omega))) (by omega_using [en, hkD, hol]), m₂]
    have bw := VG.Proof.Sha256.Stream.bytesAt_writeBytes s₁.mem (State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀)) (k * F.H.D)
      (bytesAt s₁.mem (VG.Proof.Pbkdf2.Whole.Arm.A s₀ F.tO) n) (by rw [bytesAt_length]; omega_using [en, hkD, hol])
    rw [bytesAt_length] at bw
    have ob := i₁.outB
    rw [hdn] at ob
    rw [bw, ob, Hmac.Generic.Common.bytesAt_take _ _ hnD, m₁, ht, hg, List.take_append,
      i₁.glen, Nat.add_sub_cancel_left, List.take_of_length_le (l := VG.Proof.Pbkdf2.Whole.Arm.Gk hF s₀ k) (i := k * F.H.D) (by rw [i₁.glen]),
      List.take_of_length_le (l := VG.Proof.Pbkdf2.Whole.Arm.Gk hF s₀ k) (i := k * F.H.D + n) (by rw [i₁.glen]; omega_using [])]
  · rw [z₁₀, e₉, u₉.gpr, VG.Proof.Pbkdf2.Whole.Arm.arg_ofNat 2, sub_beq (by omega_using [en, hkD, hol]) (by omega)]
    have e1 : k + 1 < VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ ↔ (k + 1) * F.H.D < ol s₀ := Whole.lt_nb hD.1
    rw [Nat.succ_mul] at e1
    have : (stackArg s₀ 2).toNat = ol s₀ := rfl
    refine decide_eq_decide.2 ⟨fun h1 => ?_, fun h1 => ?_⟩
    · by_contra h2
      have := e1.1 (by omega_using [h2, hk])
      omega
    · have : ¬ (k * F.H.D + F.H.D < ol s₀) := fun h' => absurd (e1.2 h') (by omega)
      omega

/-! ## The loop and `pbkdf2` -/

/-- A block of the output. -/
theorem block_ok {k : Nat} (hk : k < VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀) {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) :
    WP isa F.block s fun t => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ (k + 1) t ∧ t.z = decide (k + 1 = VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀) := by
  unfold Fns.block
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b1_ok hp hz h) fun s₁ ⟨i₁, r₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b2_ok hp hz i₁) fun s₂ ⟨i₂, a₀, a₁, a₇, a₁₀, c₂, m₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b3_ok hp hz i₂ a₀ a₁ a₇ a₁₀ c₂ (by rw [m₂]; exact r₁)) fun s₃ ⟨i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b4_ok hp hz i₃) fun s₄ ⟨i₄, a₀, a₁, a₁₀, a₁₂, c₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b5_ok hp hz i₄ a₀ a₁ a₁₀ a₁₂ c₄ (by rw [m₄]; exact r₃)) fun s₅ ⟨i₅, u₅⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b6_ok hp hz i₅ u₅) fun s₆ ⟨i₆, u₆, t₆⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b7_ok hp hz i₆) fun s₇ ⟨i₇, a₀, a₁, a₃, a₂, a₁₂, m₇⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b8_ok hp hz i₇ a₀ a₁ a₃ a₂ a₁₂ (by rw [m₇]; exact u₆) (by rw [m₇]; exact t₆))
    fun s₈ ⟨i₈, t₈⟩ => ?_)
  exact VG.Proof.Pbkdf2.Whole.Arm.tail_ok hp hz hk i₈ t₈

/-- The loop over the blocks of the output, if there are any. -/
theorem loop_ok {s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ 0 s) (hz' : s.z = decide (ol s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.loop F.block .ne)) s (VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ (VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀)) := by
  have hD := hz.D
  have e0 : VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ = 0 ↔ ol s₀ = 0 := Whole.nb_zero hD.1
  refine WP.ite (decide (ol s₀ = 0)) (by show VG.Arm.eval .eq s = _; rw [eval_eq, hz'])
    (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · rw [e0.2 (of_decide_eq_true h0)]; exact h
  · have hpos : 0 < VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ := by
      have := of_decide_eq_false h0; have : VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ ≠ 0 := fun e => this (e0.1 e); omega
    exact count_loop hpos (VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀) (fun k hk t ht => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.block_ok hp hz hk ht) fun t' ⟨i, z⟩ =>
      ⟨i, by rw [z]; exact decide_eq_decide.2 (by omega)⟩) h

/-- What `pbkdf2` leaves: our caller's registers, and the derived key in `out`. -/
theorem correct : WP isa F.pbkdf2 s₀ fun s' => abiPreserved s₀ s' ∧
    Spec.Pbkdf2.pbkdf2Hmac hF.hH.SH (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀)) (VG.Proof.Pbkdf2.Whole.Arm.saltB s₀) (cc s₀) (ol s₀) =
      some (bytesAt s'.mem (State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀)) (ol s₀)) := by
  have hD := hz.D
  unfold Fns.pbkdf2
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.prologue_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.keyed_ok (hF := hF) hp hz k₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.setup_ok hp hz hF h₂) fun s₃ ⟨k₃, st₃, kl₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.loopInit_ok hp hz k₃ st₃ kl₃) fun s₄ ⟨i₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.Arm.loop_ok hp hz i₄ z₄) fun s₅ h₅ => ?_)
  have k₅ := h₅.kr
  have hr := hz.reach; have := end_le hz; have := layout (F := F)
  refine WP.mono (VG.Proof.Pbkdf2.Whole.Arm.restore_ok F.L k₅.r11 (by simp only [Fns.L]; omega) k₅.saved (by rw [k₅.wr]; exact sc_mem hp)
    (show 8 * F.W + 36 ≤ F.L8 by omega) hp.nsc)
    fun s' ⟨hm, _, _, hsp, hg⟩ => ⟨⟨fun r hr => hg r (Pbkdf2.Stream.Arm.preserved_saved r hr), by rw [hsp, k₅.sp]⟩, ?_⟩
  have ob := h₅.outB
  have e : VG.Proof.Pbkdf2.Whole.Arm.dn F s₀ (VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀) = ol s₀ := Whole.done_nb hD.1
  rw [e] at ob
  unfold Spec.Pbkdf2.pbkdf2Hmac
  rw [hF.hH.hD]
  exact Whole.pbkdf2_eq (VG.Proof.Pbkdf2.Whole.Arm.prf hF s₀) (VG.Proof.Pbkdf2.Whole.Arm.saltB s₀) hp.olD (by rw [hm, ob])

end

end VG.Proof.Pbkdf2.Whole.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.CT`. -/
section

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: constant time

As on x86 (`Proof/Pbkdf2/Whole/X86/CT.lean`): the pieces of code between the
calls are checked by the taint analysis (`Checks`, which the kernel evaluates
for each hash function), with the stack arguments and the registers holding
pointers, lengths and, in the loop over the blocks, the bytes written public
(`piece`); the calls are related by their contracts (`init_rel`, `upd_rel`,
`fin_rel`, `hi_rel`, `hf_rel`, `it_rel`), whose public arguments are the same
in two runs with the same public arguments (`PubEq`). The branches (whether
the password is hashed, and the loop over the blocks) depend only on the
lengths.
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Pbkdf2.Stream.Arm (Hash scrAt copy)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK count FinArgs init_rel fin_rel)
open VG.Proof.MdStream.Arm (eval_eq)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad)
open VG.Proof.Hmac.Common (bytesAt_length)

/-- A piece of code the taint analysis accepts with the stack arguments and `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (argTaint rs 16) c hc).isSome = true

/-- The argument registers; the registers public in the key, while hashing
the password, from the key on, and in the loop over the blocks. -/
abbrev inRegs : List Reg := [.r0, .r1, .r2, .r3]
abbrev kkRegs : List Reg := [.r5, .r6, .r8, .r9, .r11]
abbrev hkRegs : List Reg := [.r4, .r5, .r6, .r8, .r9, .r11]
abbrev krRegs : List Reg := [.r5, .r6, .r11]
abbrev lpRegs : List Reg := [.r4, .r5, .r6, .r11]

/-- The taint checks of the pieces of `pbkdf2` between its calls. -/
structure Checks (F : Fns) : Prop where
  pro : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.inRegs (.block F.prologue)
  cmp : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.kkRegs (.block F.cmpPw)
  hk1 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.kkRegs (.block (scrAt .r4 F.stWO))
  hk2 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.hkRegs (.block [.mov .r0 (.reg .r4)])
  hk3 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.hkRegs (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r8), .mov .r7 (.reg .r9), .mov .r10 (.reg .r11),
    .mov .r2 (.imm 0), .mov .r3 (.imm 0)])
  hk5 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.hkRegs (.block ([.mov .r0 (.reg .r4)] ++ scrAt .r1 F.hkO ++ [.mov .r12 (.reg .r11), .mov .r2 (.reg .r9),
    .mov .r3 (.imm 0)]))
  hk7 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.krRegs (.block (scrAt .r2 F.hkO ++ [.movw .r3 (BitVec.ofNat 16 F.H.D)]))
  short : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.kkRegs (.block [.mov .r2 (.reg .r8), .mov .r3 (.reg .r9)])
  su1 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.krRegs (.block F.initArgs)
  su3 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.krRegs (copy .r11 F.st0O .r11 F.stSO F.H.S)
  su4 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.krRegs (.block F.saltArgs)
  init : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.krRegs (.block F.loopInit)
  skip : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.lpRegs (.block [])
  b1 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.lpRegs (copy .r11 F.stSO .r11 F.stWO F.H.S)
  b2 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.lpRegs (.block F.updArgs)
  b4 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.lpRegs (.block F.finArgs)
  b6 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.lpRegs (copy .r11 F.uO .r11 F.tO F.H.D)
  b7 : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.lpRegs (.block F.iterArgs)
  tail : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.lpRegs (.seq F.outLen (.seq F.outLoop (.block F.advance)))
  restore : VG.Proof.Pbkdf2.Whole.Arm.Ck VG.Proof.Pbkdf2.Whole.Arm.krRegs (.block F.L.restore)

/-- The public arguments of two runs are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0
  a1 : stackArg s₀ 1 = stackArg s₀' 1
  a2 : stackArg s₀ 2 = stackArg s₀' 2
  a3 : stackArg s₀ 3 = stackArg s₀' 3

variable {F : Fns}

section
variable {s₀ s₀' : State} (hq : VG.Proof.Pbkdf2.Whole.Arm.PubEq s₀ s₀')
include hq

theorem PubEq.a {i : Nat} (hi : i < 4) : stackArg s₀ i = stackArg s₀' i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · exact hq.a0
  · exact hq.a1
  · exact hq.a2
  · exact hq.a3

/-- `s₀'`'s public values are `s₀`'s. -/
macro "pub_simp" hq:term " at " h:ident : tactic => `(tactic|
  simp only [dO, A, scr, pw, salt, pwl, sl, ol, cc, out, kp, kl, nbk, dn, ← PubEq.r0 $hq, ← PubEq.r1 $hq,
    ← PubEq.r2 $hq, ← PubEq.r3 $hq, ← PubEq.a0 $hq, ← PubEq.a1 $hq, ← PubEq.a2 $hq, ← PubEq.a3 $hq] at $h:ident)

theorem PubEq.scrEq : VG.Proof.Pbkdf2.Whole.Arm.scr s₀' = VG.Proof.Pbkdf2.Whole.Arm.scr s₀ := hq.a3.symm
theorem PubEq.pwlEq : pwl s₀' = pwl s₀ := by show (s₀'.gpr .r1).toNat = _; rw [← hq.r1]
theorem PubEq.olEq : ol s₀' = ol s₀ := by show (stackArg s₀' 2).toNat = _; rw [← hq.a2]
theorem PubEq.nbkEq : VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀' = VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ := by show Whole.nb _ (ol s₀') = _; rw [hq.olEq]
theorem PubEq.dnEq (k : Nat) : VG.Proof.Pbkdf2.Whole.Arm.dn F s₀' k = VG.Proof.Pbkdf2.Whole.Arm.dn F s₀ k := by show Whole.done _ (ol s₀') k = _; rw [hq.olEq]

end

/-- The stack arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Pre F t) {s : State} (hsp : s.sp = t.sp) (hwr : s.wr = t.wr) :
    s.sp.toNat + 16 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 16⟩ r := by
  have e : (⟨State.addr s.sp, 16⟩ : Region) = VG.Proof.Pbkdf2.Whole.Arm.argR t := by simp [stackArgAddr, hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact h.o_a.symm
  · exact h.s_a.symm

section
variable {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hp' : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀') (hq : VG.Proof.Pbkdf2.Whole.Arm.PubEq s₀ s₀')
include hp hp' hq

/-- Two states agree on the taint `argTaint rs 16`. -/
theorem agree {rs : List Reg} {s s' : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) (hk' : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀' s')
    (hag : ∀ r ∈ rs, s.gpr r = s'.gpr r) : VG.Arm.Taint.Agree (argTaint rs 16) s s' :=
  agree_argTaint hag (by rw [hk.sp, hk'.sp, hq.sp]) (VG.Proof.Pbkdf2.Whole.Arm.args_out hp hk.sp hk.wr) (VG.Proof.Pbkdf2.Whole.Arm.args_out hp' hk'.sp hk'.wr)
    (argMem_of (j := 4) (by rw [hk.sp, hk'.sp, hq.sp]) (by rw [hk.sp]; exact hp.spf) fun i hi => by
      rw [hk.stackArg hp hi, hk'.stackArg hp' hi, hq.a hi])

/-- A piece of code the taint analysis accepts, between states that keep `KR`. -/
theorem piece {rs : List Reg} {c : Prog isa} (P G : State → State → Prop)
    (hk : ∀ {t₀ s}, P t₀ s → VG.Proof.Pbkdf2.Whole.Arm.KR F t₀ s)
    (hag : ∀ s s', P s₀ s → P s₀' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : VG.Proof.Pbkdf2.Whole.Arm.Ck rs c) (hw : ∀ {t₀}, VG.Proof.Pbkdf2.Whole.Arm.Pre F t₀ → ∀ s, P t₀ s → WP isa c s (G t₀)) :
    RelCT isa (fun s s' => P s₀ s ∧ P s₀' s') c fun s s' => G s₀ s ∧ G s₀' s' :=
  rel_agree _ (fun s s' h h' => VG.Proof.Pbkdf2.Whole.Arm.agree hp hp' hq (hk h) (hk h') (hag s s' h h')) hc (hw hp) (hw hp')

omit hp hp' in
theorem ag_kr {s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) (h' : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀' s') : ∀ r ∈ VG.Proof.Pbkdf2.Whole.Arm.krRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r5, h'.r5, salt, salt, hq.r2]
  · rw [h.r6, h'.r6, hq.r3]
  · rw [h.r11, h'.r11, hq.scrEq]

omit hp hp' in
theorem ag_kk {s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) (h' : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀' s') : ∀ r ∈ VG.Proof.Pbkdf2.Whole.Arm.kkRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.Pbkdf2.Whole.Arm.ag_kr hq h.kr h'.kr _ (by simp)
  · exact VG.Proof.Pbkdf2.Whole.Arm.ag_kr hq h.kr h'.kr _ (by simp)
  · rw [h.r8, h'.r8, pw, pw, hq.r0]
  · rw [h.r9, h'.r9, hq.r1]
  · exact VG.Proof.Pbkdf2.Whole.Arm.ag_kr hq h.kr h'.kr _ (by simp)

omit hp hp' in
theorem ag_hk {s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s) (h' : VG.Proof.Pbkdf2.Whole.Arm.KK F s₀' s') (h4 : s.gpr .r4 = dO s₀ F.stWO)
    (h4' : s'.gpr .r4 = dO s₀' F.stWO) : ∀ r ∈ VG.Proof.Pbkdf2.Whole.Arm.hkRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [VG.Proof.Pbkdf2.Whole.Arm.hkRegs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · rw [h4, h4', dO, dO, hq.scrEq]
  · exact VG.Proof.Pbkdf2.Whole.Arm.ag_kk hq h h' _ (by simpa using hr)

end

/-! ## The key -/

/-- The password is longer than a block. -/
abbrev Long (F : Fns) (t₀ : State) : Prop := F.H.B + 1 ≤ pwl t₀

/-- The pieces of hashing the password. -/
abbrev Hk1 (F : Fns) (t₀ s : State) : Prop := (VG.Proof.Pbkdf2.Whole.Arm.KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO) ∧ VG.Proof.Pbkdf2.Whole.Arm.Long F t₀
abbrev Hk2a (F : Fns) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.Arm.KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO ∧ s.gpr .r0 = dO t₀ F.stWO) ∧ VG.Proof.Pbkdf2.Whole.Arm.Long F t₀
abbrev Hk2 (hH : VG.Proof.Pbkdf2.Stream.Arm.HashOK F.H) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.Arm.KK F t₀ s ∧ hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.stWO) [] ∧ s.gpr .r4 = dO t₀ F.stWO) ∧ VG.Proof.Pbkdf2.Whole.Arm.Long F t₀
abbrev Hk3 (hH : VG.Proof.Pbkdf2.Stream.Arm.HashOK F.H) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.Arm.KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO ∧ s.gpr .r0 = dO t₀ F.stWO ∧ s.gpr .r1 = pw t₀ ∧
    s.gpr .r7 = t₀.gpr .r1 ∧ s.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.scr t₀ ∧ count s = BitVec.ofNat 64 0 ∧
    hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.stWO) []) ∧ VG.Proof.Pbkdf2.Whole.Arm.Long F t₀
abbrev Hk4 (hH : VG.Proof.Pbkdf2.Stream.Arm.HashOK F.H) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.Arm.KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO ∧
    hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.stWO) (bytesAt t₀.mem (State.addr (pw t₀)) (pwl t₀))) ∧ VG.Proof.Pbkdf2.Whole.Arm.Long F t₀
abbrev Hk5 (hH : VG.Proof.Pbkdf2.Stream.Arm.HashOK F.H) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.Arm.KK F t₀ s ∧ s.gpr .r0 = dO t₀ F.stWO ∧ s.gpr .r1 = dO t₀ F.hkO ∧ s.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr t₀ ∧
    count s = BitVec.ofNat 64 (pwl t₀) ∧
    hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.stWO) (bytesAt t₀.mem (State.addr (pw t₀)) (pwl t₀))) ∧ VG.Proof.Pbkdf2.Whole.Arm.Long F t₀
abbrev Hk6 (hH : VG.Proof.Pbkdf2.Stream.Arm.HashOK F.H) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.Arm.KR F t₀ s ∧ bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt t₀.mem (State.addr (pw t₀)) (pwl t₀))) ∧
    VG.Proof.Pbkdf2.Whole.Arm.Long F t₀

/-- After `cmp`. -/
abbrev Cmp (F : Fns) (t₀ s : State) : Prop := VG.Proof.Pbkdf2.Whole.Arm.KK F t₀ s ∧ s.z = decide (pwl t₀ < F.H.B + 1)

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hp' : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀') (hq : VG.Proof.Pbkdf2.Whole.Arm.PubEq s₀ s₀') (hc : VG.Proof.Pbkdf2.Whole.Arm.Checks F)
include hp hp' hq hc

theorem hashKey_rel :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Long F s₀) ∧ (VG.Proof.Pbkdf2.Whole.Arm.KK F s₀' s' ∧ VG.Proof.Pbkdf2.Whole.Arm.Long F s₀')) F.hashKey
      fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀' s' := by
  have hz := hF.sizes
  have hl := layout (F := F); have he := end_le hz; have := hz.D; have := hz.S; have := hz.reach
  unfold Fns.hashKey Hash.callInit
  have r1 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (fun t₀ s => VG.Proof.Pbkdf2.Whole.Arm.KK F t₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Long F t₀) (VG.Proof.Pbkdf2.Whole.Arm.Hk1 F) (fun h => h.1.kr)
    (fun s s' h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_kk hq h.1 h'.1) hc.hk1
    (fun _ s h => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk1_ok h.1 (by omega)) fun t ⟨k, d, _⟩ => ⟨⟨k, d⟩, h.2⟩)
  have r2a := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Hk1 F) (VG.Proof.Pbkdf2.Whole.Arm.Hk2a F) (fun h => h.1.1.kr)
    (fun s s' h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_hk hq h.1.1 h'.1.1 h.1.2 h'.1.2) hc.hk2
    (fun _ s h => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk2a_ok h.1.1 h.1.2) fun t ⟨k, d, a⟩ => ⟨⟨k, d, a⟩, h.2⟩)
  have cw : ∀ {t₀ : State}, VG.Proof.Pbkdf2.Whole.Arm.Pre F t₀ → ∀ {s : State}, VG.Proof.Pbkdf2.Whole.Arm.KR F t₀ s →
      Covers [⟨State.addr (dO t₀ F.stWO), F.H.S⟩] s.wr := fun {t₀} hp₀ {s} k => by
    rw [dO_addr hp₀ (by omega)]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Whole.Arm.cov_part hp₀ k (by omega)
  have r2 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Hk2a F s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Hk2a F s₀' s') (.call F.H.initN F.H.initC)
      fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Hk2 hF.hH s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Hk2 hF.hH s₀' s' :=
    rel_wp (init_rel hF.hH (st := dO s₀ F.stWO) fun s s' ⟨⟨⟨k, _, a⟩, _⟩, ⟨⟨k', _, a'⟩, _⟩⟩ =>
        ⟨a, by rw [a', dO, dO, hq.scrEq], by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega, cw hp k.kr,
          by have := cw hp' k'.kr; rw [dO, hq.scrEq] at this; exact this⟩)
      (fun s ⟨⟨k, d, a⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk2b_ok hp hz hF.hH k d a) fun t h => ⟨h, l⟩)
      (fun s ⟨⟨k, d, a⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk2b_ok hp' hz hF.hH k d a) fun t h => ⟨h, l⟩)
  have r3 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Hk2 hF.hH) (VG.Proof.Pbkdf2.Whole.Arm.Hk3 hF.hH) (fun h => h.1.1.kr)
    (fun s s' h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_hk hq h.1.1 h'.1.1 h.1.2.2 h'.1.2.2) hc.hk3
    (fun hp₀ s ⟨⟨k, r, d⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk3_ok k d) fun t ⟨k', d', a₀, a₁, a₇, a₁₀, c, m⟩ =>
      ⟨⟨k', d', a₀, a₁, a₇, a₁₀, c, by rw [m]; exact r⟩, l⟩)
  have r4 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Hk3 hF.hH s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Hk3 hF.hH s₀' s')
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16))
      fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Hk4 hF.hH s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Hk4 hF.hH s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := s₀.sp)
        fun s s' ⟨⟨⟨k, _, a₀, a₁, a₇, a₁₀, c, _⟩, _⟩, ⟨⟨k', _, a₀', a₁', a₇', a₁₀', c', _⟩, _⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.Arm.hk4_args hp hz hF.hH k a₀ a₁ a₇ a₁₀,
          by have := VG.Proof.Pbkdf2.Whole.Arm.hk4_args hp' hz hF.hH k' a₀' a₁' a₇' a₁₀'; pub_simp hq at this; exact this,
          by rw [c, c'], k.kr.sp, by rw [k'.kr.sp, hq.sp]⟩)
      (fun s ⟨⟨k, d, a₀, a₁, a₇, a₁₀, c, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk4_ok hp hz hF.hH k d a₀ a₁ a₇ a₁₀ c r) fun t h =>
        ⟨h, l⟩)
      (fun s ⟨⟨k, d, a₀, a₁, a₇, a₁₀, c, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk4_ok hp' hz hF.hH k d a₀ a₁ a₇ a₁₀ c r) fun t h =>
        ⟨h, l⟩)
  have r5 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Hk4 hF.hH) (VG.Proof.Pbkdf2.Whole.Arm.Hk5 hF.hH) (fun h => h.1.1.kr)
    (fun s s' h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_hk hq h.1.1 h'.1.1 h.1.2.1 h'.1.2.1) hc.hk5
    (fun hp₀ s ⟨⟨k, d, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk5_ok k d (by omega)) fun t ⟨k', a₀, a₁, a₁₂, c, m⟩ =>
      ⟨⟨k', a₀, a₁, a₁₂, c, by rw [m]; exact r⟩, l⟩)
  have r6 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Hk5 hF.hH s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Hk5 hF.hH s₀' s')
      (.frame (.push [.r1, .r12]) (.call F.H.finN F.H.finC) (.pop .r1 8))
      fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Hk6 hF.hH s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Hk6 hF.hH s₀' s' :=
    rel_wp (fin_rel hF.hH (sp := s₀.sp) fun s s' ⟨⟨⟨k, a₀, a₁, a₁₂, c, _⟩, _⟩, ⟨⟨k', a₀', a₁', a₁₂', c', _⟩, _⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.Arm.hk6_args hp hz hF.hH k a₀ a₁ a₁₂,
          by have := VG.Proof.Pbkdf2.Whole.Arm.hk6_args hp' hz hF.hH k' a₀' a₁' a₁₂'; pub_simp hq at this; exact this,
          by rw [c, c', hq.pwlEq], k.kr.sp, by rw [k'.kr.sp, hq.sp]⟩)
      (fun s ⟨⟨k, a₀, a₁, a₁₂, c, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk6_ok hp hz hF.hH k a₀ a₁ a₁₂ c r) fun t h => ⟨h, l⟩)
      (fun s ⟨⟨k, a₀, a₁, a₁₂, c, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk6_ok hp' hz hF.hH k a₀ a₁ a₁₂ c r) fun t h => ⟨h, l⟩)
  have r7 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Hk6 hF.hH) (VG.Proof.Pbkdf2.Whole.Arm.Keyed hF) (fun h => h.1.1) (fun s s' h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_kr hq h.1.1 h'.1.1) hc.hk7
    (fun {t₀} hp₀ s ⟨⟨k, b⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.hk7_ok k (by omega) (by omega)) fun t ⟨k', d, c, m⟩ => by
      have hlt : ¬ pwl t₀ < F.H.B + 1 := by omega
      have ekp : VG.Proof.Pbkdf2.Whole.Arm.kp F t₀ = dO t₀ F.hkO := by simp only [VG.Proof.Pbkdf2.Whole.Arm.kp, hlt, ↓reduceIte]
      have ekl : VG.Proof.Pbkdf2.Whole.Arm.kl F t₀ = F.H.D := by simp only [VG.Proof.Pbkdf2.Whole.Arm.kl, hlt, ↓reduceIte]
      refine ⟨k', by rw [ekp]; exact d, by rw [ekl]; exact c, ?_⟩
      rw [ekp, ekl, dO_addr hp₀ (by omega), m, b, VG.Proof.Pbkdf2.Whole.Arm.blockKey_hash hz hF.hH (by rw [bytesAt_length]; omega)
        (VG.Proof.Pbkdf2.Whole.Arm.hash_len hF.hH b)])
  exact (r1.seq ((r2a.seq r2).seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono (fun _ _ h => h) fun _ _ h => h

theorem key_rel :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.Arm.KK F s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.KK F s₀' s') F.key fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀' s' := by
  have hz := hF.sizes
  unfold Fns.key
  have rc := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (fun t₀ s => VG.Proof.Pbkdf2.Whole.Arm.KK F t₀ s) (VG.Proof.Pbkdf2.Whole.Arm.Cmp F) (fun h => h.kr) (fun s s' h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_kk hq h h') hc.cmp
    (fun hp₀ s k => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.cmp_ok hz k) fun t ⟨k', z, _⟩ => ⟨k', z⟩)
  have ev : ∀ {t₀ t : State}, VG.Proof.Pbkdf2.Whole.Arm.Cmp F t₀ t → isa.eval .eq t = some (decide (pwl t₀ < F.H.B + 1)) := by
    intro t₀ t h
    show VG.Arm.eval .eq t = _
    rw [eval_eq, h.2]
  refine rc.seq (RelCT.ite (fun s s' h => by rw [ev h.1, ev h.2, hq.pwlEq]) ?_ ?_)
  · refine (VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (fun t₀ s => VG.Proof.Pbkdf2.Whole.Arm.Cmp F t₀ s ∧ pwl t₀ < F.H.B + 1) (VG.Proof.Pbkdf2.Whole.Arm.Keyed hF) (fun h => h.1.1.kr)
      (fun s s' h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_kk hq h.1.1 h'.1.1) hc.short (fun {t₀} hp₀ s ⟨⟨k, _⟩, hlt⟩ => ?_)).mono
      (fun s s' h => ?_) fun _ _ h => h
    · have ekp : VG.Proof.Pbkdf2.Whole.Arm.kp F t₀ = pw t₀ := by simp only [VG.Proof.Pbkdf2.Whole.Arm.kp, hlt, ↓reduceIte]
      have ekl : VG.Proof.Pbkdf2.Whole.Arm.kl F t₀ = pwl t₀ := by simp only [VG.Proof.Pbkdf2.Whole.Arm.kl, hlt, ↓reduceIte]
      refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₂ u₂ =>
        VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₃ u₃ => WP.block_nil
          ⟨(k.kr.upd (by decide) u₂).upd (by decide) u₃, ?_, ?_, ?_⟩
      · rw [u₃.other _ (by decide), u₂.gpr, k.r8, ekp]
      · rw [u₃.gpr, u₂.other _ (by decide), k.r9, ekl, VG.Proof.Pbkdf2.Whole.Arm.ofNat_toNat32]
      · rw [u₃.mem, u₂.mem, ekp, ekl, k.kr.pwBytes hp₀]
    · have := of_decide_eq_true ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
      exact ⟨⟨h.1.1, this⟩, h.1.2, by rw [hq.pwlEq]; exact this⟩
  · refine (VG.Proof.Pbkdf2.Whole.Arm.hashKey_rel hp hp' hq hc).mono (fun s s' h => ?_) fun _ _ h => h
    have := of_decide_eq_false ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
    exact ⟨⟨h.1.1.1, by omega⟩, h.1.2.1, by show F.H.B + 1 ≤ pwl s₀'; rw [hq.pwlEq]; omega⟩

end

/-! ## HMAC's states for the key, and the salt -/

abbrev Su1 (hF : FnsOK F) (t₀ s : State) : Prop :=
  VG.Proof.Pbkdf2.Whole.Arm.Keyed hF t₀ s ∧ s.gpr .r0 = dO t₀ F.st0O ∧ s.gpr .r1 = dO t₀ F.st1O ∧ s.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr t₀
abbrev Su2 (hF : FnsOK F) (t₀ s : State) : Prop :=
  VG.Proof.Pbkdf2.Whole.Arm.KR F t₀ s ∧ hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀) opad) ∧ (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀).length = F.H.B
abbrev Su3 (hF : FnsOK F) (t₀ s : State) : Prop :=
  VG.Proof.Pbkdf2.Whole.Arm.KR F t₀ s ∧ hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀) opad) ∧
    hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.stSO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀) ipad) ∧ (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀).length = F.H.B
abbrev Su4 (hF : FnsOK F) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.Arm.KR F t₀ s ∧ s.gpr .r0 = dO t₀ F.stSO ∧ s.gpr .r1 = salt t₀ ∧ s.gpr .r7 = t₀.gpr .r3 ∧
    s.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.scr t₀ ∧ count s = BitVec.ofNat 64 F.H.B) ∧
  hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀) opad) ∧
    hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.stSO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀) ipad) ∧ (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀).length = F.H.B
/-- After the setup. -/
abbrev Su5 (hF : FnsOK F) (t₀ s : State) : Prop :=
  VG.Proof.Pbkdf2.Whole.Arm.KR F t₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.States hF t₀ s.mem ∧ (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀).length = F.H.B

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hp' : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀') (hq : VG.Proof.Pbkdf2.Whole.Arm.PubEq s₀ s₀') (hc : VG.Proof.Pbkdf2.Whole.Arm.Checks F)
include hp hp' hq hc

theorem setup_rel :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Keyed hF s₀' s') F.setup fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Su5 hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Su5 hF s₀' s' := by
  have hz := hF.sizes
  unfold Fns.setup
  have r1 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Keyed hF) (VG.Proof.Pbkdf2.Whole.Arm.Su1 hF) (fun h => h.kr) (fun s s' h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_kr hq h.kr h'.kr) hc.su1
    (fun _ s h => VG.Proof.Pbkdf2.Whole.Arm.su1_ok hz hF h)
  have r2 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Su1 hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Su1 hF s₀' s')
      (.frame (.push [.r12, .lr]) (.call F.hiN F.hiC) (.pop .r12 8))
      fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Su2 hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Su2 hF s₀' s' :=
    rel_wp (hi_rel hF.hi (sp := s₀.sp) fun s s' ⟨⟨h, a₀, a₁, a₁₂⟩, ⟨h', a₀', a₁', a₁₂'⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.Arm.su2_args hp hz hF h a₀ a₁ a₁₂,
          by have := VG.Proof.Pbkdf2.Whole.Arm.su2_args hp' hz hF h' a₀' a₁' a₁₂'; pub_simp hq at this; exact this,
          h.kr.sp, by rw [h'.kr.sp, hq.sp]⟩)
      (fun s ⟨h, a₀, a₁, a₁₂⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.su2_ok hp hz hF h a₀ a₁ a₁₂) fun t ⟨k, r0, r1⟩ =>
        ⟨k, r0, r1, VG.Proof.Pbkdf2.Whole.Arm.K0_length hp hz hF h⟩)
      (fun s ⟨h, a₀, a₁, a₁₂⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.su2_ok hp' hz hF h a₀ a₁ a₁₂) fun t ⟨k, r0, r1⟩ =>
        ⟨k, r0, r1, VG.Proof.Pbkdf2.Whole.Arm.K0_length hp' hz hF h⟩)
  have r3 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Su2 hF) (VG.Proof.Pbkdf2.Whole.Arm.Su3 hF) (fun h => h.1) (fun s s' h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_kr hq h.1 h'.1) hc.su3
    (fun hp₀ s ⟨k, r0, r1, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.su3_ok hp₀ hz hF k r0 r1) fun t ⟨k', r0', r1', rS⟩ =>
      ⟨k', r0', r1', rS, l⟩)
  have r4 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Su3 hF) (VG.Proof.Pbkdf2.Whole.Arm.Su4 hF) (fun h => h.1) (fun s s' h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_kr hq h.1 h'.1) hc.su4
    (fun hp₀ s ⟨k, r0, r1, rS, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.su4_ok hz k) fun t ⟨k', a₀, a₁, a₇, a₁₀, c, m⟩ =>
      ⟨⟨k', a₀, a₁, a₇, a₁₀, c⟩, m ▸ r0, m ▸ r1, m ▸ rS, l⟩)
  have r5 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Su4 hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Su4 hF s₀' s')
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16))
      fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Su5 hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Su5 hF s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := s₀.sp) fun s s' ⟨⟨⟨k, a₀, a₁, a₇, a₁₀, c⟩, _⟩, ⟨⟨k', a₀', a₁', a₇', a₁₀', c'⟩, _⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.Arm.su5_args hp hz hF k a₀ a₁ a₇ a₁₀,
          by have := VG.Proof.Pbkdf2.Whole.Arm.su5_args hp' hz hF k' a₀' a₁' a₇' a₁₀'; pub_simp hq at this; exact this,
          by rw [c, c'], k.sp, by rw [k'.sp, hq.sp]⟩)
      (fun s ⟨⟨k, a₀, a₁, a₇, a₁₀, c⟩, r0, r1, rS, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.su5_ok hp hz hF k a₀ a₁ a₇ a₁₀ c l r0 r1 rS)
        fun t ⟨k', st⟩ => ⟨k', st, l⟩)
      (fun s ⟨⟨k, a₀, a₁, a₇, a₁₀, c⟩, r0, r1, rS, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.su5_ok hp' hz hF k a₀ a₁ a₇ a₁₀ c l r0 r1 rS)
        fun t ⟨k', st⟩ => ⟨k', st, l⟩)
  exact r1.seq (r2.seq (r3.seq (r4.seq r5)))

theorem loopInit_rel :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Su5 hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Su5 hF s₀' s') (.block F.loopInit) fun s s' =>
      (VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ 0 s ∧ s.z = decide (ol s₀ = 0)) ∧ (VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀' 0 s' ∧ s'.z = decide (ol s₀' = 0)) :=
  VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Su5 hF) (fun t₀ s => VG.Proof.Pbkdf2.Whole.Arm.Inv hF t₀ 0 s ∧ s.z = decide (ol t₀ = 0)) (fun h => h.1)
    (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_kr hq h.1 h'.1) hc.init
    (fun hp₀ _ ⟨k, st, l⟩ => VG.Proof.Pbkdf2.Whole.Arm.loopInit_ok hp₀ hF.sizes k st l)

end

/-! ## A block of the output -/

/-- The pieces of a block. -/
abbrev Bk (hF : FnsOK F) (k : Nat) (P : State → State → Prop) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.Arm.Inv hF t₀ k s ∧ P t₀ s) ∧ k < VG.Proof.Pbkdf2.Whole.Arm.nbk F t₀
abbrev Bk1 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.Arm.Bk hF k fun t₀ s =>
  hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀) ipad ++ VG.Proof.Pbkdf2.Whole.Arm.saltB t₀)
abbrev Bk2 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.Arm.Bk hF k fun t₀ s =>
  (s.gpr .r0 = dO t₀ F.stWO ∧ s.gpr .r1 = dO t₀ F.intO ∧ s.gpr .r7 = BitVec.ofNat 32 4 ∧ s.gpr .r10 = VG.Proof.Pbkdf2.Whole.Arm.scr t₀ ∧
    count s = BitVec.ofNat 64 (F.H.B + (sl t₀ + 0))) ∧
  hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀) ipad ++ VG.Proof.Pbkdf2.Whole.Arm.saltB t₀)
abbrev Bk3 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.Arm.Bk hF k fun t₀ s =>
  hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀) ipad ++ VG.Proof.Pbkdf2.Whole.Arm.saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk4 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.Arm.Bk hF k fun t₀ s =>
  (s.gpr .r0 = dO t₀ F.stWO ∧ s.gpr .r1 = dO t₀ F.st1O ∧ s.gpr .r10 = dO t₀ F.uO ∧ s.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr t₀ ∧
    count s = BitVec.ofNat 64 (F.H.B + (sl t₀ + 4))) ∧
  hF.hH.SH.Repr s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.Arm.K0 hF t₀) ipad ++ VG.Proof.Pbkdf2.Whole.Arm.saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk5 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.Arm.Bk hF k fun t₀ s =>
  bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.uO) F.H.D = VG.Proof.Pbkdf2.Whole.Arm.prf hF t₀ (VG.Proof.Pbkdf2.Whole.Arm.saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk6 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.Arm.Bk hF k fun t₀ s =>
  bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.uO) F.H.D = VG.Proof.Pbkdf2.Whole.Arm.prf hF t₀ (VG.Proof.Pbkdf2.Whole.Arm.saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.tO) F.H.D = VG.Proof.Pbkdf2.Whole.Arm.prf hF t₀ (VG.Proof.Pbkdf2.Whole.Arm.saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk7 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.Arm.Bk hF k fun t₀ s =>
  (s.gpr .r0 = dO t₀ F.st0O ∧ s.gpr .r1 = dO t₀ F.uO ∧ s.gpr .r3 = dO t₀ F.tO ∧ s.gpr .r2 = stackArg t₀ 0 - 1 ∧
    s.gpr .r12 = VG.Proof.Pbkdf2.Whole.Arm.scr t₀) ∧
  bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.uO) F.H.D = VG.Proof.Pbkdf2.Whole.Arm.prf hF t₀ (VG.Proof.Pbkdf2.Whole.Arm.saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.tO) F.H.D = VG.Proof.Pbkdf2.Whole.Arm.prf hF t₀ (VG.Proof.Pbkdf2.Whole.Arm.saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk8 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.Arm.Bk hF k fun t₀ s => bytesAt s.mem (VG.Proof.Pbkdf2.Whole.Arm.A t₀ F.tO) F.H.D = VG.Proof.Pbkdf2.Whole.Arm.Tk hF t₀ (k + 1)

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hp' : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀') (hq : VG.Proof.Pbkdf2.Whole.Arm.PubEq s₀ s₀') (hc : VG.Proof.Pbkdf2.Whole.Arm.Checks F)
include hp hp' hq hc

omit hp hp' hc in
theorem ag_loop {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s) (h' : VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀' k s') :
    ∀ r ∈ VG.Proof.Pbkdf2.Whole.Arm.lpRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [VG.Proof.Pbkdf2.Whole.Arm.lpRegs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · rw [h.r4, h'.r4, hq.dnEq]
  · exact VG.Proof.Pbkdf2.Whole.Arm.ag_kr hq h.kr h'.kr _ (by simpa using hr)

theorem block_rel (k : Nat) :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s ∧ k < VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀) ∧ (VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀' k s' ∧ k < VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀')) F.block
      fun s s' => (VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ (k + 1) s ∧ s.z = decide (k + 1 = VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀)) ∧
        (VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀' (k + 1) s' ∧ s'.z = decide (k + 1 = VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀')) := by
  have hz := hF.sizes
  unfold Fns.block
  have r1 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (fun t₀ s => VG.Proof.Pbkdf2.Whole.Arm.Inv hF t₀ k s ∧ k < VG.Proof.Pbkdf2.Whole.Arm.nbk F t₀) (VG.Proof.Pbkdf2.Whole.Arm.Bk1 hF k) (fun h => h.1.kr)
    (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_loop hq h.1 h'.1) hc.b1
    (fun hp₀ _ ⟨i, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b1_ok hp₀ hz i) fun _ ⟨i', r⟩ => ⟨⟨i', r⟩, l⟩)
  have r2 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Bk1 hF k) (VG.Proof.Pbkdf2.Whole.Arm.Bk2 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_loop hq h.1.1 h'.1.1) hc.b2
    (fun hp₀ _ ⟨⟨i, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b2_ok hp₀ hz i) fun _ ⟨i', a₀, a₁, a₇, a₁₀, c, m⟩ =>
      ⟨⟨i', ⟨a₀, a₁, a₇, a₁₀, c⟩, by rw [m]; exact r⟩, l⟩)
  have r3 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Bk2 hF k s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Bk2 hF k s₀' s')
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16))
      fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Bk3 hF k s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Bk3 hF k s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := s₀.sp)
        fun s s' ⟨⟨⟨i, ⟨a₀, a₁, a₇, a₁₀, c⟩, _⟩, _⟩, ⟨⟨i', ⟨a₀', a₁', a₇', a₁₀', c'⟩, _⟩, _⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.Arm.b3_args hp hz i a₀ a₁ a₇ a₁₀,
          by have := VG.Proof.Pbkdf2.Whole.Arm.b3_args hp' hz i' a₀' a₁' a₇' a₁₀'; pub_simp hq at this; exact this,
          by rw [c, c', sl, sl, hq.r3], i.kr.sp, by rw [i'.kr.sp, hq.sp]⟩)
      (fun _ ⟨⟨i, ⟨a₀, a₁, a₇, a₁₀, c⟩, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b3_ok hp hz i a₀ a₁ a₇ a₁₀ c r) fun _ h => ⟨h, l⟩)
      (fun _ ⟨⟨i, ⟨a₀, a₁, a₇, a₁₀, c⟩, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b3_ok hp' hz i a₀ a₁ a₇ a₁₀ c r) fun _ h => ⟨h, l⟩)
  have r4 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Bk3 hF k) (VG.Proof.Pbkdf2.Whole.Arm.Bk4 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_loop hq h.1.1 h'.1.1) hc.b4
    (fun hp₀ _ ⟨⟨i, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b4_ok hp₀ hz i) fun _ ⟨i', a₀, a₁, a₁₀, a₁₂, c, m⟩ =>
      ⟨⟨i', ⟨a₀, a₁, a₁₀, a₁₂, c⟩, by rw [m]; exact r⟩, l⟩)
  have r5 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Bk4 hF k s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Bk4 hF k s₀' s')
      (.frame (.push [.r10, .r12]) (.call F.hfN F.hfC) (.pop .r12 8))
      fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Bk5 hF k s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Bk5 hF k s₀' s' :=
    rel_wp (hf_rel hF.hf (sp := s₀.sp)
        fun s s' ⟨⟨⟨i, ⟨a₀, a₁, a₁₀, a₁₂, c⟩, _⟩, _⟩, ⟨⟨i', ⟨a₀', a₁', a₁₀', a₁₂', c'⟩, _⟩, _⟩⟩ => by
        have cc : count s = count s' := by rw [c, c', sl, sl, hq.r3]
        obtain ⟨c3, c2⟩ := BitVec.append_32_inj cc
        exact ⟨VG.Proof.Pbkdf2.Whole.Arm.b5_args hp hz i a₀ a₁ a₁₀ a₁₂,
          by have := VG.Proof.Pbkdf2.Whole.Arm.b5_args hp' hz i' a₀' a₁' a₁₀' a₁₂'; pub_simp hq at this; exact this,
          c2, c3, i.kr.sp, by rw [i'.kr.sp, hq.sp]⟩)
      (fun _ ⟨⟨i, ⟨a₀, a₁, a₁₀, a₁₂, c⟩, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b5_ok hp hz i a₀ a₁ a₁₀ a₁₂ c r) fun _ h => ⟨h, l⟩)
      (fun _ ⟨⟨i, ⟨a₀, a₁, a₁₀, a₁₂, c⟩, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b5_ok hp' hz i a₀ a₁ a₁₀ a₁₂ c r) fun _ h => ⟨h, l⟩)
  have r6 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Bk5 hF k) (VG.Proof.Pbkdf2.Whole.Arm.Bk6 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_loop hq h.1.1 h'.1.1) hc.b6
    (fun hp₀ _ ⟨⟨i, u⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b6_ok hp₀ hz i u) fun _ ⟨i', u', t'⟩ => ⟨⟨i', u', t'⟩, l⟩)
  have r7 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Bk6 hF k) (VG.Proof.Pbkdf2.Whole.Arm.Bk7 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_loop hq h.1.1 h'.1.1) hc.b7
    (fun hp₀ _ ⟨⟨i, u, t⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b7_ok hp₀ hz i) fun _ ⟨i', a₀, a₁, a₃, a₂, a₁₂, m⟩ =>
      ⟨⟨i', ⟨a₀, a₁, a₃, a₂, a₁₂⟩, by rw [m]; exact u, by rw [m]; exact t⟩, l⟩)
  have r8 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Bk7 hF k s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Bk7 hF k s₀' s')
      (.frame (.push [.r12, .lr]) (.call F.itN F.itC) (.pop .r12 8))
      fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Bk8 hF k s₀ s ∧ VG.Proof.Pbkdf2.Whole.Arm.Bk8 hF k s₀' s' :=
    rel_wp (it_rel hF.it (sp := s₀.sp)
        fun s s' ⟨⟨⟨i, ⟨a₀, a₁, a₃, a₂, a₁₂⟩, _⟩, _⟩, ⟨⟨i', ⟨a₀', a₁', a₃', a₂', a₁₂'⟩, _⟩, _⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.Arm.b8_args hp hz i a₀ a₁ a₃ a₂ a₁₂,
          by have := VG.Proof.Pbkdf2.Whole.Arm.b8_args hp' hz i' a₀' a₁' a₃' a₂' a₁₂'; pub_simp hq at this; exact this,
          i.kr.sp, by rw [i'.kr.sp, hq.sp]⟩)
      (fun _ ⟨⟨i, ⟨a₀, a₁, a₃, a₂, a₁₂⟩, u, t⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b8_ok hp hz i a₀ a₁ a₃ a₂ a₁₂ u t) fun _ h => ⟨h, l⟩)
      (fun _ ⟨⟨i, ⟨a₀, a₁, a₃, a₂, a₁₂⟩, u, t⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.b8_ok hp' hz i a₀ a₁ a₃ a₂ a₁₂ u t) fun _ h => ⟨h, l⟩)
  have r9 := VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.Arm.Bk8 hF k) (fun t₀ s => VG.Proof.Pbkdf2.Whole.Arm.Inv hF t₀ (k + 1) s ∧ s.z = decide (k + 1 = VG.Proof.Pbkdf2.Whole.Arm.nbk F t₀))
    (fun h => h.1.1.kr) (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_loop hq h.1.1 h'.1.1) hc.tail
    (fun hp₀ _ ⟨⟨i, t⟩, l⟩ => VG.Proof.Pbkdf2.Whole.Arm.tail_ok hp₀ hz l i t)
  exact (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9)))))))).mono (fun _ _ h => h)
    fun _ _ h => h

/-- The loop's invariant in two runs, with `n` blocks left. -/
abbrev LoopI (hF : FnsOK F) (s₀ s₀' : State) (n : Nat) (s s' : State) : Prop :=
  ∃ k, n = VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ - k ∧ k < VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ ∧ VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ k s ∧ VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀' k s'

theorem step_rel (n : Nat) :
    RelCT isa (VG.Proof.Pbkdf2.Whole.Arm.LoopI hF s₀ s₀' n) F.block fun s s' =>
      isa.eval .ne s = isa.eval .ne s' ∧
      (isa.eval .ne s = some false → VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ (VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀) s ∧ VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀' (VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀') s') ∧
      (isa.eval .ne s = some true → ∃ m < n, VG.Proof.Pbkdf2.Whole.Arm.LoopI hF s₀ s₀' m s s') := by
  rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨k, rfl, hk, i, i'⟩ e₁ e₂
  obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := VG.Proof.Pbkdf2.Whole.Arm.block_rel hp hp' hq hc k _ _ _ _ _ _
    ⟨⟨i, hk⟩, ⟨i', by rw [hq.nbkEq]; exact hk⟩⟩ e₁ e₂
  refine ⟨ht, ?_⟩
  show isa.eval .ne s₁' = isa.eval .ne s₂' ∧ _
  have e : isa.eval .ne s₁' = some (!decide (k + 1 = VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀)) := by
    show some (!s₁'.z) = _; rw [z]
  have e' : isa.eval .ne s₂' = some (!decide (k + 1 = VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀)) := by
    show some (!s₂'.z) = _; rw [z', hq.nbkEq]
  rw [e, e']
  refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
  · have hl : k + 1 = VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ := by simpa using hf
    exact ⟨hl ▸ j, by rw [hq.nbkEq, ← hl]; exact j'⟩
  · have hl : k + 1 ≠ VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ := by simpa using ht
    exact ⟨VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ - (k + 1), by omega, k + 1, rfl, by omega, j, j'⟩

theorem loop_rel :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ 0 s ∧ s.z = decide (ol s₀ = 0)) ∧
        (VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀' 0 s' ∧ s'.z = decide (ol s₀' = 0)))
      (.ite .eq (.block []) (.loop F.block .ne))
      fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ (VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀) s ∧ VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀' (VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀') s' := by
  have hD := hF.sizes.D
  have e0 : VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ = 0 ↔ ol s₀ = 0 := Whole.nb_zero hD.1
  have ev : ∀ {t : State} {o : Nat}, t.z = decide (o = 0) → isa.eval .eq t = some (decide (o = 0)) :=
    fun h => by show VG.Arm.eval .eq _ = _; rw [eval_eq, h]
  refine RelCT.ite (fun s s' h => by rw [ev h.1.2, ev h.2.2, hq.olEq]) ?_ ?_
  · by_cases e : ol s₀ = 0
    · have n0 : VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ = 0 := e0.2 e
      have n0' : VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀' = 0 := by rw [hq.nbkEq]; exact n0
      exact (VG.Proof.Pbkdf2.Whole.Arm.piece hp hp' hq (fun t₀ s => (VG.Proof.Pbkdf2.Whole.Arm.Inv hF t₀ 0 s ∧ s.z = decide (ol t₀ = 0)) ∧ ol t₀ = 0)
        (fun t₀ s => VG.Proof.Pbkdf2.Whole.Arm.Inv hF t₀ (VG.Proof.Pbkdf2.Whole.Arm.nbk F t₀) s) (fun h => h.1.1.kr) (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.Arm.ag_loop hq h.1.1 h'.1.1) hc.skip
        (fun {t₀} _ _ h => WP.block_nil (by
          have : VG.Proof.Pbkdf2.Whole.Arm.nbk F t₀ = 0 := (Whole.nb_zero hD.1).2 h.2
          rw [this]; exact h.1.1))).mono
        (fun _ _ h => ⟨⟨h.1.1, e⟩, h.1.2, by rw [hq.olEq]; exact e⟩) fun _ _ h => h
    · intro _ _ _ _ _ _ h
      have z := h.2
      rw [ev h.1.1.2] at z
      exact absurd (by simpa using z) e
  · refine (RelCT.loop (M := isa) (VG.Proof.Pbkdf2.Whole.Arm.LoopI hF s₀ s₀') (VG.Proof.Pbkdf2.Whole.Arm.step_rel hp hp' hq hc) (VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ - 0)).mono
      (fun s s' h => ?_) fun _ _ h => h
    have z := h.2
    rw [ev h.1.1.2] at z
    have e : ol s₀ ≠ 0 := by simpa using z
    have : VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀ ≠ 0 := fun h => e (e0.1 h)
    exact ⟨0, rfl, by omega, h.1.1.1, h.1.2.1⟩

include hF in
/-- `pbkdf2` in two runs with the same public arguments. -/
theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') F.pbkdf2 fun _ _ => True := by
  have hz := hF.sizes
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.Pbkdf2.Whole.Arm.KK F s₀) (G' := VG.Proof.Pbkdf2.Whole.Arm.KK F s₀')
    (argTaint VG.Proof.Pbkdf2.Whole.Arm.inRegs 16) (fun s s' e e' => by
        subst e e'
        refine agree_argTaint (fun r hr => ?_) hq.sp (VG.Proof.Pbkdf2.Whole.Arm.args_out hp rfl rfl) (VG.Proof.Pbkdf2.Whole.Arm.args_out hp' rfl rfl)
          (argMem_of (j := 4) hq.sp hp.spf fun i hi => hq.a hi)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
    (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Whole.Arm.prologue_ok hp hz) (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Whole.Arm.prologue_ok hp' hz)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀ (VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀) s ∧ VG.Proof.Pbkdf2.Whole.Arm.Inv hF s₀' (VG.Proof.Pbkdf2.Whole.Arm.nbk F s₀') s') (.block F.L.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (argTaint VG.Proof.Pbkdf2.Whole.Arm.krRegs 16)
      (fun s s' h => VG.Proof.Pbkdf2.Whole.Arm.agree hp hp' hq h.1.kr h.2.kr (VG.Proof.Pbkdf2.Whole.Arm.ag_kr hq h.1.kr h.2.kr)) hr
  unfold Fns.pbkdf2
  exact pro.seq ((VG.Proof.Pbkdf2.Whole.Arm.key_rel hp hp' hq hc).seq ((VG.Proof.Pbkdf2.Whole.Arm.setup_rel hp hp' hq hc).seq ((VG.Proof.Pbkdf2.Whole.Arm.loopInit_rel hp hp' hq hc).seq
    ((VG.Proof.Pbkdf2.Whole.Arm.loop_rel hp hp' hq hc).seq restore))))

end

/-- The public arguments of the shared contract. -/
theorem pub_of {S : Spec.Hmac.StreamingHash} {W : Nat} {s₁ s₂ : State}
    (h : (Spec.Pbkdf2.pbkdf2ScratchContract S W Arm.abi 24).pub s₁ s₂) : VG.Proof.Pbkdf2.Whole.Arm.PubEq s₁ s₂ := by
  sig_pub [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- `pbkdf2` is verified against the shared contract, given the taint checks
and a state satisfying it. -/
theorem verified (hF : FnsOK F) (hc : VG.Proof.Pbkdf2.Whole.Arm.Checks F) {S : Spec.Hmac.StreamingHash} {W : Nat} (hS : hF.hH.SH = S)
    (hW : F.W + F.H.S = W) (hsat : ∃ s, (Spec.Pbkdf2.pbkdf2ScratchContract S W Arm.abi 24).pre s) :
    Verified Arm.target F.pbkdf2 (Spec.Pbkdf2.pbkdf2ScratchContract S W Arm.abi 24) := by
  subst hS hW
  refine ⟨fun s hs => WP.mono (VG.Proof.Pbkdf2.Whole.Arm.correct (hF := hF) (VG.Proof.Pbkdf2.Whole.Arm.pre_of hF hs) hF.sizes) fun s' ⟨a, h⟩ => ⟨a, ?_⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ =>
      (VG.Proof.Pbkdf2.Whole.Arm.ct (hF := hF) (VG.Proof.Pbkdf2.Whole.Arm.pre_of hF h₁) (VG.Proof.Pbkdf2.Whole.Arm.pre_of hF h₂) (VG.Proof.Pbkdf2.Whole.Arm.pub_of hpub) hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, hsat⟩
  sig_post [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  exact h

end VG.Proof.Pbkdf2.Whole.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances`. -/
section

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: the instances

The generic proof (`CT.lean`) at each hash function of
`Proof/Pbkdf2/Stream/Arm/Hashes.lean`: the functions it calls are verified by
their own registration files (with 16 bytes of stack, the most their frames
use: `armStack`), the taint checks are evaluated by the kernel, and a state
satisfies the shared contract (`pbkSat`).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Arm.FrameStack
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Proof.Pbkdf2.Stream.Arm (sha1H md5H sha384H sha512H' sha512_224H sha512_256H sha1OK md5OK sha384OK
  sha512OK sha512_224OK sha512_256OK)

/-- The functions `pbkdf2` calls for the hash function `M` of the instance
`I` (`Impl/Pbkdf2/Md/Arm.lean`), with the working space of `I`'s functions,
by the names they are registered with. -/
def fnsOf (I : Spec.Hmac.Instance) (M : Impl.Pbkdf2.Md.Arm.Hash) : Fns where
  H := M.st
  W := I.scratch
  hiN := I.initScratchApi.name
  hiC := M.hmacInit
  hfN := I.finalizeScratchApi.name
  hfC := M.hmacFin
  itN := I.iterateApi.name
  itC := M.iterate

/-- Memory holding the stack arguments `1, 0x1200, 0, 0x2000` of `pbkdf2` at `0x8000`. -/
def pbkMem : Mem := fun a =>
  if a = 0x8000 then 0x01 else if a = 0x8005 then 0x12 else if a = 0x800D then 0x20 else 0

/-- A state satisfying `pbkdf2`'s precondition with `8 W` bytes of scratch
space: an empty password, salt and output, and one iteration. -/
def pbkSat (W : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x1100
    | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := VG.Proof.Pbkdf2.Whole.Arm.pbkMem
  rd := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩, ⟨0x8000, 16⟩]
  wr := [⟨0x1200, 0⟩, ⟨0x2000, W * 8⟩]

/-! ## SHA-1 -/

def sha1F : Fns := VG.Proof.Pbkdf2.Whole.Arm.fnsOf Spec.Hmac.sha1I Md.Arm.sha1Md

theorem sha1_checks : VG.Proof.Pbkdf2.Whole.Arm.Checks VG.Proof.Pbkdf2.Whole.Arm.sha1F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

def sha1OKF : FnsOK VG.Proof.Pbkdf2.Whole.Arm.sha1F := by
  refine {
    hH := sha1OK
    Wi := 56
    Wf := 56
    Wt := 56
    hi := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha1_init
    hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha1_finalize
    it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha1_iterate
    hiSt := ?_
    hfSt := ?_
    itSt := ?_
    hWi := by decide
    hWf := by decide
    hWt := by decide
    hWH := by decide
    hDB := by decide
    hBS := by decide
    fits := by decide
    reach := by decide
    encB1 := by decide
    encB := by decide
    encB4 := by decide
    encD := by decide }
  taint_decide_all

theorem sha1_sat : ∃ s, (Spec.Hmac.sha1I.pbkdf2ScratchContract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using VG.Proof.Pbkdf2.Whole.Arm.pbkSat 140

theorem sha1 : Verified Arm.target sha1F.pbkdf2 (Spec.Hmac.sha1I.pbkdf2ScratchContract Arm.abi 24) :=
  VG.Proof.Pbkdf2.Whole.Arm.verified VG.Proof.Pbkdf2.Whole.Arm.sha1OKF VG.Proof.Pbkdf2.Whole.Arm.sha1_checks rfl rfl VG.Proof.Pbkdf2.Whole.Arm.sha1_sat

/-! ## MD5 -/

def md5F : Fns := VG.Proof.Pbkdf2.Whole.Arm.fnsOf Spec.Hmac.md5I Md.Arm.md5Md

theorem md5_checks : VG.Proof.Pbkdf2.Whole.Arm.Checks VG.Proof.Pbkdf2.Whole.Arm.md5F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

def md5OKF : FnsOK VG.Proof.Pbkdf2.Whole.Arm.md5F := by
  refine {
    hH := md5OK
    Wi := 48
    Wf := 48
    Wt := 48
    hi := .of_verified Proof.Pbkdf2.Md.Arm.Instances.md5_init
    hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.md5_finalize
    it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.md5_iterate
    hiSt := ?_
    hfSt := ?_
    itSt := ?_
    hWi := by decide
    hWf := by decide
    hWt := by decide
    hWH := by decide
    hDB := by decide
    hBS := by decide
    fits := by decide
    reach := by decide
    encB1 := by decide
    encB := by decide
    encB4 := by decide
    encD := by decide }
  taint_decide_all

theorem md5_sat : ∃ s, (Spec.Hmac.md5I.pbkdf2ScratchContract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using VG.Proof.Pbkdf2.Whole.Arm.pbkSat 128

theorem md5 : Verified Arm.target md5F.pbkdf2 (Spec.Hmac.md5I.pbkdf2ScratchContract Arm.abi 24) :=
  VG.Proof.Pbkdf2.Whole.Arm.verified VG.Proof.Pbkdf2.Whole.Arm.md5OKF VG.Proof.Pbkdf2.Whole.Arm.md5_checks rfl rfl VG.Proof.Pbkdf2.Whole.Arm.md5_sat

/-! ## SHA-384 -/

def sha384F : Fns := VG.Proof.Pbkdf2.Whole.Arm.fnsOf Spec.Hmac.sha384I Md.Arm.sha384Md

theorem sha384_checks : VG.Proof.Pbkdf2.Whole.Arm.Checks VG.Proof.Pbkdf2.Whole.Arm.sha384F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

def sha384OKF : FnsOK VG.Proof.Pbkdf2.Whole.Arm.sha384F := by
  refine {
    hH := sha384OK
    Wi := 234
    Wf := 234
    Wt := 234
    hi := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha384_init
    hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha384_finalize
    it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha384_iterate
    hiSt := ?_
    hfSt := ?_
    itSt := ?_
    hWi := by decide
    hWf := by decide
    hWt := by decide
    hWH := by decide
    hDB := by decide
    hBS := by decide
    fits := by decide
    reach := by decide
    encB1 := by decide
    encB := by decide
    encB4 := by decide
    encD := by decide }
  taint_decide_all

theorem sha384_sat : ∃ s, (Spec.Hmac.sha384I.pbkdf2ScratchContract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using VG.Proof.Pbkdf2.Whole.Arm.pbkSat 426

theorem sha384 : Verified Arm.target sha384F.pbkdf2 (Spec.Hmac.sha384I.pbkdf2ScratchContract Arm.abi 24) :=
  VG.Proof.Pbkdf2.Whole.Arm.verified VG.Proof.Pbkdf2.Whole.Arm.sha384OKF VG.Proof.Pbkdf2.Whole.Arm.sha384_checks rfl rfl VG.Proof.Pbkdf2.Whole.Arm.sha384_sat

/-! ## SHA-512 -/

def sha512F : Fns := VG.Proof.Pbkdf2.Whole.Arm.fnsOf Spec.Hmac.sha512I Md.Arm.sha512Md'

theorem sha512_checks : VG.Proof.Pbkdf2.Whole.Arm.Checks VG.Proof.Pbkdf2.Whole.Arm.sha512F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

def sha512OKF : FnsOK VG.Proof.Pbkdf2.Whole.Arm.sha512F := by
  refine {
    hH := sha512OK
    Wi := 234
    Wf := 234
    Wt := 234
    hi := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_init
    hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_finalize
    it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_iterate
    hiSt := ?_
    hfSt := ?_
    itSt := ?_
    hWi := by decide
    hWf := by decide
    hWt := by decide
    hWH := by decide
    hDB := by decide
    hBS := by decide
    fits := by decide
    reach := by decide
    encB1 := by decide
    encB := by decide
    encB4 := by decide
    encD := by decide }
  taint_decide_all

theorem sha512_sat : ∃ s, (Spec.Hmac.sha512I.pbkdf2ScratchContract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using VG.Proof.Pbkdf2.Whole.Arm.pbkSat 426

theorem sha512 : Verified Arm.target sha512F.pbkdf2 (Spec.Hmac.sha512I.pbkdf2ScratchContract Arm.abi 24) :=
  VG.Proof.Pbkdf2.Whole.Arm.verified VG.Proof.Pbkdf2.Whole.Arm.sha512OKF VG.Proof.Pbkdf2.Whole.Arm.sha512_checks rfl rfl VG.Proof.Pbkdf2.Whole.Arm.sha512_sat

/-! ## SHA-512/224 -/

def sha512_224F : Fns := VG.Proof.Pbkdf2.Whole.Arm.fnsOf Spec.Hmac.sha512_224I Md.Arm.sha512_224Md

theorem sha512_224_checks : VG.Proof.Pbkdf2.Whole.Arm.Checks VG.Proof.Pbkdf2.Whole.Arm.sha512_224F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

def sha512_224OKF : FnsOK VG.Proof.Pbkdf2.Whole.Arm.sha512_224F := by
  refine {
    hH := sha512_224OK
    Wi := 234
    Wf := 234
    Wt := 234
    hi := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_224_init
    hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_224_finalize
    it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_224_iterate
    hiSt := ?_
    hfSt := ?_
    itSt := ?_
    hWi := by decide
    hWf := by decide
    hWt := by decide
    hWH := by decide
    hDB := by decide
    hBS := by decide
    fits := by decide
    reach := by decide
    encB1 := by decide
    encB := by decide
    encB4 := by decide
    encD := by decide }
  taint_decide_all

theorem sha512_224_sat : ∃ s, (Spec.Hmac.sha512_224I.pbkdf2ScratchContract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using VG.Proof.Pbkdf2.Whole.Arm.pbkSat 426

theorem sha512_224 : Verified Arm.target sha512_224F.pbkdf2 (Spec.Hmac.sha512_224I.pbkdf2ScratchContract Arm.abi 24) :=
  VG.Proof.Pbkdf2.Whole.Arm.verified VG.Proof.Pbkdf2.Whole.Arm.sha512_224OKF VG.Proof.Pbkdf2.Whole.Arm.sha512_224_checks rfl rfl VG.Proof.Pbkdf2.Whole.Arm.sha512_224_sat

/-! ## SHA-512/256 -/

def sha512_256F : Fns := VG.Proof.Pbkdf2.Whole.Arm.fnsOf Spec.Hmac.sha512_256I Md.Arm.sha512_256Md

theorem sha512_256_checks : VG.Proof.Pbkdf2.Whole.Arm.Checks VG.Proof.Pbkdf2.Whole.Arm.sha512_256F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

def sha512_256OKF : FnsOK VG.Proof.Pbkdf2.Whole.Arm.sha512_256F := by
  refine {
    hH := sha512_256OK
    Wi := 234
    Wf := 234
    Wt := 234
    hi := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_256_init
    hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_256_finalize
    it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_256_iterate
    hiSt := ?_
    hfSt := ?_
    itSt := ?_
    hWi := by decide
    hWf := by decide
    hWt := by decide
    hWH := by decide
    hDB := by decide
    hBS := by decide
    fits := by decide
    reach := by decide
    encB1 := by decide
    encB := by decide
    encB4 := by decide
    encD := by decide }
  taint_decide_all

theorem sha512_256_sat : ∃ s, (Spec.Hmac.sha512_256I.pbkdf2ScratchContract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using VG.Proof.Pbkdf2.Whole.Arm.pbkSat 426

theorem sha512_256 : Verified Arm.target sha512_256F.pbkdf2 (Spec.Hmac.sha512_256I.pbkdf2ScratchContract Arm.abi 24) :=
  VG.Proof.Pbkdf2.Whole.Arm.verified VG.Proof.Pbkdf2.Whole.Arm.sha512_256OKF VG.Proof.Pbkdf2.Whole.Arm.sha512_256_checks rfl rfl VG.Proof.Pbkdf2.Whole.Arm.sha512_256_sat

end VG.Proof.Pbkdf2.Whole.Arm

end
