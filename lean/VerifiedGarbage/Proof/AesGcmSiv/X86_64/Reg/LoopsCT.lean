module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.CT
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.CryptCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Impl.AesGcmSiv.X86_64Reg
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Narrow
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.FnCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Narrow
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.CT
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.CryptCT
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Env
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.AesGcmSiv.X86_64Reg
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM-SIV in registers on x86-64: constant time, with the loops

Untrusted: everything here is checked by Lean. `sealL` and `openL` are
constant time for any loops that meet their contracts (`Stitch.LoopsOk`) and
pass the taint analysis from the registers holding their arguments
(`LoopsCT`), which the two runs agree on by correctness: they are addresses
in `W`, the data's address and a count of its blocks (`HAt`, `CAt`). The
code around the loops passes the analysis from the public slots, as the
other pieces do.
-/

-- separate module: the loops' paths, apart from the pieces'

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64Reg
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Impl.AesGcmSiv.X86_64 (entry recv tagOut restore mask okO bO tagO aadO alenO dataO lenO)
open VG.Impl.AesGcmSiv.X86_64Stitch (Loops)
open VG.Proof.AesGcm.X86_64 (toNat_ofNat_of_lt)
open VG.Proof.AesGcmSiv.X86_64 (eval_b Stitch.LoopsOk Stitch.nb Stitch.yR Stitch.pR Stitch.cR Stitch.dR Stitch.yp
  Stitch.pp Stitch.cp Stitch.dp)

/-- The loops pass the taint analysis from the registers holding their
arguments, in this code's working space. -/
structure LoopsCT (lp : Loops) : Prop where
  decT : ∃ hc, (taint.check (sivT [.rdi, .rsi, .rdx, .rcx, .r8, .r11, .r12, .r9]) lp.dec hc).isSome = true
  hashT : ∃ hc, (taint.check (sivT [.rcx, .r8, .r11, .rdx, .r9]) lp.hash hc).isSome = true
  ctrT : ∃ hc, (taint.check (sivT [.rdi, .rsi, .rdx, .rcx, .r8, .r11, .r12, .r9]) lp.ctr hc).isSome = true

/-! ## The code around the loops, checked -/

theorem nil_check : ∃ hc, (taint.check (sivT []) (.block []) hc).isSome = true := ⟨_, by taint_decide⟩

theorem lenCmp_check : ∃ hc, (taint.check (sivT []) (.block lenCmp) hc).isSome = true := ⟨_, by taint_decide⟩

theorem hashArgs_check : ∃ hc, (taint.check (sivT []) (.block hashArgs) hc).isSome = true := ⟨_, by taint_decide⟩

theorem back_check : ∃ hc, (taint.check (sivT []) (.block back) hc).isSome = true := ⟨_, by taint_decide⟩

theorem ctrArgs_check : ∃ hc, (taint.check (sivT []) (.block ctrArgs) hc).isSome = true := ⟨_, by taint_decide⟩

theorem decArgs_check : ∃ hc, (taint.check (sivT []) (.block (putYH ++ ctrArgs)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ctrTail_check : ∃ hc, (taint.check (sivT []) (.seq (.block ctrBack) cryptRest) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## The loops' paths keep `St` -/

section
variable {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat}

/-- The registers `hash` takes. -/
structure HAt (W D : Addr) (n : Nat) (t : State) : Prop where
  rcx : t.gpr .rcx = W + BitVec.ofNat 64 80
  r8 : t.gpr .r8 = W + BitVec.ofNat 64 64
  r11 : t.gpr .r11 = W + BitVec.ofNat 64 488
  rdx : t.gpr .rdx = D
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 * (n / 256))

/-- The registers `ctr` and `dec` take. -/
structure CAt (W D : Addr) (R n : Nat) (t : State) : Prop where
  rdi : t.gpr .rdi = W + BitVec.ofNat 64 248
  rsi : t.gpr .rsi = BitVec.ofNat 64 R
  rdx : t.gpr .rdx = W + BitVec.ofNat 64 96
  rcx : t.gpr .rcx = W + BitVec.ofNat 64 80
  r8 : t.gpr .r8 = W + BitVec.ofNat 64 64
  r11 : t.gpr .r11 = W + BitVec.ofNat 64 488
  r12 : t.gpr .r12 = D
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 * (n / 256))

theorem mem3 {r : Reg} (hr : r ∈ [Reg.r13, .r15, .rsp]) :
    r ∈ calleeSaved ∧ r ≠ .rax ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 ∧
      r ≠ .rbp := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> decide

theorem putYH_st (F : MulFacts) (L : Lay K W SP) {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (.block putYH) t (St K W SP R N A D al n T) :=
  WP.mono (putYH_ok F L h.bufs.one.env) fun _ ⟨_, _, f₁, rd₁, wr₁, sv₁⟩ =>
    h.frame (h.bufs.one.env.of_saved sv₁ rd₁ wr₁) f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (frA (d := 64) (k := 32) (by decide) f₁) rd₁ wr₁

theorem hashArgs_st (F : MulFacts) (L : Lay K W SP) {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (.block hashArgs) t fun t' => St K W SP R N A D al n T t' ∧ HAt W D n t' := by
  rw [show hashArgs = putYH ++ hashPtrs from rfl, WP.block_append_iff]
  refine WP.mono (putYH_st F L h) fun s₁ h₁ => ?_
  obtain ⟨s₂, run₂, m₂, rcx, r8, r11, rdx, r9, sv₂, rd₂, wr₂⟩ :=
    hashPtrs_run h₁.bufs.one.env h₁.bufs.one.sl h₁.bufs.data.lt
  exact WP.of_runBlock ⟨s₂, run₂, h₁.same m₂ (fun r hr => sv₂ r (mem3 hr).1) rd₂ wr₂, ⟨rcx, r8, r11, rdx, r9⟩⟩

theorem hash_st {lp : Loops} (hlp : Stitch.LoopsOk lp) (L : Lay K W SP) (h256 : 256 ≤ n) {t : State}
    (h : St K W SP R N A D al n T t ∧ HAt W D n t) : WP isa lp.hash t (St K W SP R N A D al n T) := by
  obtain ⟨hs, G⟩ := h
  have hp := hpre_of L hs.bufs.one.env hs.bufs.data h256 G.rcx G.r8 G.r11 G.rdx G.r9
  refine WP.mono (hlp.hash hp) fun t' Hp => ?_
  have Fh : Frame [⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 488, 256⟩] t.mem t'.mem := by
    have h := Hp.frame
    simp only [Stitch.yR, Stitch.pR, Stitch.yp, Stitch.pp, G.rcx, G.r11] at h
    exact h
  refine hs.frame (hs.bufs.one.env.keep (fun r hr => Hp.gpr r (mem3 hr).2.1 (mem3 hr).2.2.1 (mem3 hr).2.2.2.2.2.1)
    Hp.rd Hp.wr) Fh (fun q hq => ?_) (Fh.sub fun q hq => ?_) Hp.rd Hp.wr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩

theorem back_pr (F : MulFacts) {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (.block back) t
      (PR F K W SP R N A D al n T (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256)) :=
  WP.mono (back_ok F h.bufs.one.env h.bufs.one.sl h.bufs.data.lt) fun _ ⟨g, _, r12, rbp, m, rd, wr, gp⟩ =>
    ⟨⟨h.same m gp rd wr, _, g⟩, r12, rbp⟩

theorem hashFront_pr (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (L : Lay K W SP) (h256 : 256 ≤ n)
    {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (hashFront lp) t (PR F K W SP R N A D al n T (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256)) :=
  WP.seq (WP.mono (hashArgs_st F L h) fun _ h₁ => WP.seq (WP.mono (hash_st hlp L h256 h₁) fun _ h₂ => back_pr F h₂))

theorem lenCmp_st {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (.block lenCmp) t fun t' => St K W SP R N A D al n T t' ∧ t'.cf = some (decide (n < 256)) := by
  obtain ⟨t₁, run, cf, gg, _, m, rd, wr⟩ := lenCmp_run h.bufs.one.env h.bufs.one.sl h.bufs.data.lt
  exact WP.of_runBlock ⟨t₁, run, h.same m (fun r hr => gg r (mem3 hr).2.1) rd wr, cf⟩

theorem lenCmp_pr {F : MulFacts} {Q : Addr} {k : Nat} {t : State} (h : PR F K W SP R N A D al n T Q k t) :
    WP isa (.block lenCmp) t fun t' =>
      PR F K W SP R N A D al n T Q k t' ∧ t'.cf = some (decide (n < 256)) := by
  obtain ⟨⟨hs, H, g⟩, r12, rbp⟩ := h
  obtain ⟨t₁, run, cf, gg, x, m, rd, wr⟩ := lenCmp_run hs.bufs.one.env hs.bufs.one.sl hs.bufs.data.lt
  exact WP.of_runBlock ⟨t₁, run, ⟨⟨hs.same m (fun r hr => gg r (mem3 hr).2.1) rd wr, H, by rw [x]; exact g.c,
    by rw [x]; exact g.h⟩, by rw [gg _ (by decide), r12], by rw [gg _ (by decide), rbp]⟩, cf⟩

theorem mid_pr (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (L : Lay K W SP) {t : State}
    (h : PR F K W SP R N A D al n T D n t ∧ t.cf = some (decide (n < 256))) :
    WP isa (.ite .b (.block []) (hashFront lp)) t
      (PR F K W SP R N A D al n T (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256)) := by
  obtain ⟨hpr, hcf⟩ := h
  refine WP.ite (decide (n < 256)) (eval_b hcf) (fun hlt => WP.block_nil ?_)
    (fun hge => hashFront_pr F hlp L (by simpa using hge) hpr.1.1)
  have h' : n < 256 := by simpa using hlt
  refine ⟨hpr.1, ?_, ?_⟩
  · rw [hpr.2.1, Nat.div_eq_of_lt h']; simp
  · rw [hpr.2.2, Nat.mod_eq_of_lt h']

theorem polyvalL_st (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (L : Lay K W SP) {t : State}
    (h : St K W SP R N A D al n T t) : WP isa (polyvalL lp) t (St K W SP R N A D al n T) :=
  WP.seq (WP.mono (polyA_wp (F := F) h) fun _ h₁ => WP.seq (WP.mono (absorb_st false L h₁.1.1.bufs.aad h₁)
    fun _ h₂ => WP.seq (WP.mono (polyD_wp h₂) fun _ h₃ => WP.seq (WP.mono (lenCmp_pr h₃)
      fun _ h₄ => WP.seq (WP.mono (mid_pr F hlp L h₄) fun _ h₅ => WP.seq (WP.mono
        (absorb_st true L (h₅.1.1.bufs.data.slice (a := 256 * (n / 256)) (k := n % 256) (by omega_arith)) h₅)
        fun _ h₆ => lens_st h₆))))))

theorem ctrArgs_st (L : Lay K W SP) (hR : R = 10 ∨ R = 14) {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (.block ctrArgs) t fun t' => St K W SP R N A D al n T t' ∧ CAt W D R n t' := by
  obtain ⟨t₁, run₁, _, _, rdi₁, rsi₁, _, r12₁, _, _, _, m₁, rd₁, wr₁, g₁⟩ :=
    ctrInit_run hR h.bufs.one.env h.bufs.one.sl h.bufs.data.lt
  have h₁ := h.same m₁ g₁ rd₁ wr₁
  obtain ⟨t₂, run₂, m₂, rdx, rcx, r8, r11, r9, g₂, rd₂, wr₂⟩ :=
    ctrPtrs_run h₁.bufs.one.env h₁.bufs.one.sl h₁.bufs.data.lt
  have f₂ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] t₁.mem t₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [show ctrArgs = ctrInit ++ ctrPtrs from rfl, WP.block_append_iff]
  refine WP.of_runBlock ⟨t₁, run₁, WP.of_runBlock ⟨t₂, run₂, h₁.frame (h₁.bufs.one.env.keep (fun r hr =>
    g₂ r (mem3 hr).2.2.1 (mem3 hr).2.2.2.1 (mem3 hr).2.2.2.2.1 (mem3 hr).2.2.2.2.2.2.2.1 (mem3 hr).2.2.2.2.2.1) rd₂ wr₂)
    f₂ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
    (frA (d := 96) (k := 16) (by decide) f₂) rd₂ wr₂,
    ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), rdi₁],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), rsi₁], rdx, rcx, r8, r11,
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), r12₁], r9⟩⟩⟩

theorem decArgs_st (F : MulFacts) (L : Lay K W SP) (hR : R = 10 ∨ R = 14) {t : State}
    (h : St K W SP R N A D al n T t) :
    WP isa (.block (putYH ++ ctrArgs)) t fun t' => St K W SP R N A D al n T t' ∧ CAt W D R n t' := by
  rw [WP.block_append_iff]
  exact WP.mono (putYH_st F L h) fun _ h₁ => ctrArgs_st L hR h₁

theorem ctr_st {lp : Loops} (hlp : Stitch.LoopsOk lp) (L : Lay K W SP) (hR : R = 10 ∨ R = 14) (h256 : 256 ≤ n)
    {t : State} (h : St K W SP R N A D al n T t ∧ CAt W D R n t) : WP isa lp.ctr t (St K W SP R N A D al n T) := by
  obtain ⟨hs, G⟩ := h
  have hn := hs.bufs.data.lt
  have hp := spre_of L hR hs.bufs.one.env hs.bufs.data hs.dw h256 G.rdi G.rsi G.rdx G.rcx G.r8 G.r11 G.r12 G.r9
  obtain hnb : Stitch.nb t = 16 * (n / 256) := by
    show (t.gpr .r9).toNat = _; rw [G.r9, toNat_ofNat_of_lt (by omega_arith)]
  refine WP.mono (hlp.ctr hp (by rw [hnb]; omega_arith)) fun t' Cp => ?_
  have Fd : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨D, 16 * (16 * (n / 256))⟩,
      ⟨W + BitVec.ofNat 64 488, 256⟩] t.mem t'.mem := by
    have h := Cp.frame
    simp only [Stitch.cR, Stitch.dR, Stitch.pR, Stitch.cp, Stitch.dp, Stitch.pp, hnb, G.rdx, G.r12, G.r11] at h
    exact h
  refine hs.frame (hs.bufs.one.env.keep (fun r hr => Cp.gpr r (mem3 hr).2.1 (mem3 hr).2.2.1 (mem3 hr).2.2.2.2.2.1
    (mem3 hr).2.2.2.2.2.2.1) Cp.rd Cp.wr) Fd (fun q hq => ?_) (Fd.sub fun q hq => ?_) Cp.rd Cp.wr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact ((hs.bufs.data.w.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub (by decide))).symm
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩

theorem dec_st {lp : Loops} (hlp : Stitch.LoopsOk lp) (L : Lay K W SP) (hR : R = 10 ∨ R = 14) (h256 : 256 ≤ n)
    {t : State} (h : St K W SP R N A D al n T t ∧ CAt W D R n t) : WP isa lp.dec t (St K W SP R N A D al n T) := by
  obtain ⟨hs, G⟩ := h
  have hn := hs.bufs.data.lt
  have hp := spre_of L hR hs.bufs.one.env hs.bufs.data hs.dw h256 G.rdi G.rsi G.rdx G.rcx G.r8 G.r11 G.r12 G.r9
  obtain hnb : Stitch.nb t = 16 * (n / 256) := by
    show (t.gpr .r9).toNat = _; rw [G.r9, toNat_ofNat_of_lt (by omega_arith)]
  refine WP.mono (hlp.dec hp (by rw [hnb]; omega_arith)) fun t' Dp => ?_
  have Fd : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 80, 16⟩, ⟨D, 16 * (16 * (n / 256))⟩,
      ⟨W + BitVec.ofNat 64 488, 256⟩] t.mem t'.mem := by
    have h := Dp.frame
    simp only [Stitch.cR, Stitch.yR, Stitch.dR, Stitch.pR, Stitch.cp, Stitch.yp, Stitch.dp, Stitch.pp, hnb, G.rdx,
      G.rcx, G.r12, G.r11] at h
    exact h
  refine hs.frame (hs.bufs.one.env.keep (fun r hr => Dp.gpr r (mem3 hr).2.1 (mem3 hr).2.2.1 (mem3 hr).2.2.2.2.2.1
    (mem3 hr).2.2.2.2.2.2.1) Dp.rd Dp.wr) Fd (fun q hq => ?_) (Fd.sub fun q hq => ?_) Dp.rd Dp.wr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact ((hs.bufs.data.w.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub (by decide))).symm
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩

theorem ctrFront_st {lp : Loops} (hlp : Stitch.LoopsOk lp) (L : Lay K W SP) (hR : R = 10 ∨ R = 14) (h256 : 256 ≤ n)
    {t : State} (h : St K W SP R N A D al n T t) : WP isa (ctrFront lp) t (St K W SP R N A D al n T) :=
  WP.mono (ctrLoop_ok hlp L hR h.bufs.one.env h.bufs.one.sl h.bufs.data h.dw h256) fun _ Cr =>
    h.frame Cr.env Cr.frame (slots_lRD L h.bufs.data) (frLD Cr.frame) Cr.rd Cr.wr

theorem decFront_st (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (L : Lay K W SP) (hR : R = 10 ∨ R = 14)
    (h256 : 256 ≤ n) {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (decFront lp) t (St K W SP R N A D al n T) :=
  WP.mono (decFront_ok F hlp L hR h.bufs.one.env h.bufs.one.sl h.bufs.data h.dw h256) fun _ ⟨E, rd, wr, f, _, _⟩ =>
    h.frame E f (slots_lRD L h.bufs.data) (frLD f) rd wr

theorem cryptIte_st {lp : Loops} (hlp : Stitch.LoopsOk lp) (L : Lay K W SP) (hR : R = 10 ∨ R = 14) {t : State}
    (h : St K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256))) :
    WP isa (.ite .b crypt (ctrFront lp)) t (St K W SP R N A D al n T) :=
  WP.ite (decide (n < 256)) (eval_b h.2) (fun _ => crypt_st L hR h.1)
    (fun hge => ctrFront_st hlp L hR (by simpa using hge) h.1)

theorem cryptL_st {lp : Loops} (hlp : Stitch.LoopsOk lp) (L : Lay K W SP) (hR : R = 10 ∨ R = 14) {t : State}
    (h : St K W SP R N A D al n T t) : WP isa (cryptL lp) t (St K W SP R N A D al n T) :=
  WP.seq (WP.mono (lenCmp_st h) fun _ h₁ => cryptIte_st hlp L hR h₁)

theorem decL_st (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (L : Lay K W SP) (hR : R = 10 ∨ R = 14)
    (h256 : 256 ≤ n) {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (decL lp) t (St K W SP R N A D al n T) :=
  WP.seq (WP.mono (polyA_wp (F := F) h) fun _ h₁ => WP.seq (WP.mono (absorb_st false L h₁.1.1.bufs.aad h₁)
    fun _ h₂ => WP.seq (WP.mono (decFront_st F hlp L hR h256 h₂.1) fun _ h₃ => WP.seq (WP.mono (back_pr F h₃)
      fun _ h₄ => WP.seq (WP.mono
        (absorb_st true L (h₄.1.1.bufs.data.slice (a := 256 * (n / 256)) (k := n % 256) (by omega_arith)) h₄)
        fun _ h₅ => lens_st h₅)))))

theorem openIte_st (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (L : Lay K W SP) (hR : R = 10 ∨ R = 14)
    {t : State} (h : St K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256))) :
    WP isa (.ite .b (.seq crypt polyval) (decL lp)) t (St K W SP R N A D al n T) :=
  WP.ite (decide (n < 256)) (eval_b h.2)
    (fun _ => WP.seq (WP.mono (crypt_st L hR h.1) fun _ h₁ => polyval_st F L h₁))
    (fun hge => decL_st F hlp L hR (by simpa using hge) h.1)

/-! ## The loops' paths, in two runs -/

theorem HAt.both {t₁ t₂ : State} (h₁ : St K W SP R N A D al n T t₁ ∧ HAt W D n t₁)
    (h₂ : St K W SP R N A D al n T t₂ ∧ HAt W D n t₂) :
    Both K W SP R N A D al n [.rcx, .r8, .r11, .rdx, .r9] t₁ t₂ :=
  ⟨h₁.1.bufs.one, h₂.1.bufs.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.rcx, h₂.2.rcx]
    · rw [h₁.2.r8, h₂.2.r8]
    · rw [h₁.2.r11, h₂.2.r11]
    · rw [h₁.2.rdx, h₂.2.rdx]
    · rw [h₁.2.r9, h₂.2.r9]⟩

theorem CAt.both {t₁ t₂ : State} (h₁ : St K W SP R N A D al n T t₁ ∧ CAt W D R n t₁)
    (h₂ : St K W SP R N A D al n T t₂ ∧ CAt W D R n t₂) :
    Both K W SP R N A D al n [.rdi, .rsi, .rdx, .rcx, .r8, .r11, .r12, .r9] t₁ t₂ :=
  ⟨h₁.1.bufs.one, h₂.1.bufs.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.rdi, h₂.2.rdi]
    · rw [h₁.2.rsi, h₂.2.rsi]
    · rw [h₁.2.rdx, h₂.2.rdx]
    · rw [h₁.2.rcx, h₂.2.rcx]
    · rw [h₁.2.r8, h₂.2.r8]
    · rw [h₁.2.r11, h₂.2.r11]
    · rw [h₁.2.r12, h₂.2.r12]
    · rw [h₁.2.r9, h₂.2.r9]⟩

variable (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 744⟩) (hn : n ≤ 2 ^ 64)
include hDW hn

theorem hashFront_rel (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (hct : LoopsCT lp) (L : Lay K W SP)
    (h256 : 256 ≤ n) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (hashFront lp) fun _ _ => True := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.bufs.one, (hP _ _ h).2.bufs.one,
      fun _ h => nomatch h⟩) hashArgs_check).wp
    (F₁ := fun (t : State) => St K W SP R N A D al n T t ∧ HAt W D n t)
    (F₂ := fun (t : State) => St K W SP R N A D al n T t ∧ HAt W D n t)
    fun t₁ t₂ h => ⟨hashArgs_st F L (hP _ _ h).1, hashArgs_st F L (hP _ _ h).2⟩
  have r₂ := (rel_taintC [.rcx, .r8, .r11, .rdx, .r9] (P := fun t₁ t₂ => True ∧
      (St K W SP R N A D al n T t₁ ∧ HAt W D n t₁) ∧ (St K W SP R N A D al n T t₂ ∧ HAt W D n t₂))
    hDW hn (fun t₁ t₂ h => HAt.both h.2.1 h.2.2) hct.hashT).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨hash_st hlp L h256 h.2.1, hash_st hlp L h256 h.2.2⟩
  have r₃ := rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) back_check
  exact RelCT.seq r₁ (RelCT.seq r₂ r₃)

theorem polyvalL_rel (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (hct : LoopsCT lp) (L : Lay K W SP)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (polyvalL lp) fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂ := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.bufs.one, (hP _ _ h).2.bufs.one,
      fun _ h => nomatch h⟩) polyA_check).wp
    (F₁ := PR F K W SP R N A D al n T A al) (F₂ := PR F K W SP R N A D al n T A al)
    fun t₁ t₂ h => ⟨polyA_wp (hP _ _ h).1, polyA_wp (hP _ _ h).2⟩
  have r₂ := (rel_taintC [.r12, .rbp] (P := fun t₁ t₂ => True ∧ PR F K W SP R N A D al n T A al t₁ ∧
      PR F K W SP R N A D al n T A al t₂) hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.1.bufs.one, h.2.2.1.1.bufs.one, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1]
        · rw [h.2.1.2.2, h.2.2.2.2]⟩) (absorb_check false)).wp
    (F₁ := PG F K W SP R N A D al n T) (F₂ := PG F K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨absorb_st false L h.2.1.1.1.bufs.aad h.2.1, absorb_st false L h.2.2.1.1.bufs.aad h.2.2⟩
  have r₃ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ PG F K W SP R N A D al n T t₁ ∧ PG F K W SP R N A D al n T t₂)
      hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.bufs.one, h.2.2.1.bufs.one, fun _ h => nomatch h⟩) polyD_check).wp
    (F₁ := PR F K W SP R N A D al n T D n) (F₂ := PR F K W SP R N A D al n T D n)
    fun t₁ t₂ h => ⟨polyD_wp h.2.1, polyD_wp h.2.2⟩
  have r₄ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ PR F K W SP R N A D al n T D n t₁ ∧
      PR F K W SP R N A D al n T D n t₂) hDW hn
      (fun t₁ t₂ h => ⟨h.2.1.1.1.bufs.one, h.2.2.1.1.bufs.one, fun _ h => nomatch h⟩) lenCmp_check).wp
    (F₁ := fun (t : State) => PR F K W SP R N A D al n T D n t ∧ t.cf = some (decide (n < 256)))
    (F₂ := fun (t : State) => PR F K W SP R N A D al n T D n t ∧ t.cf = some (decide (n < 256)))
    fun t₁ t₂ h => ⟨lenCmp_pr h.2.1, lenCmp_pr h.2.2⟩
  have i₅ : RelCT isa (fun t₁ t₂ => True ∧
        (PR F K W SP R N A D al n T D n t₁ ∧ t₁.cf = some (decide (n < 256))) ∧
        (PR F K W SP R N A D al n T D n t₂ ∧ t₂.cf = some (decide (n < 256))))
      (.ite .b (.block []) (hashFront lp)) fun _ _ => True := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [eval_b h.2.1.2, eval_b h.2.2.2]) ?_ ?_
    · exact rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨h.1.2.1.1.1.1.bufs.one, h.1.2.2.1.1.1.bufs.one,
        fun _ h => nomatch h⟩) nil_check
    · by_cases hn256 : 256 ≤ n
      · exact hashFront_rel hDW hn F hlp hct L hn256 fun t₁ t₂ h => ⟨h.1.2.1.1.1.1, h.1.2.2.1.1.1⟩
      · refine RelCT.of_false fun _ _ h => hn256 ?_
        have := h.2; rw [eval_b h.1.2.1.2] at this; simp at this; omega_using [this]
  have r₅ := i₅.wp
    (F₁ := PR F K W SP R N A D al n T (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256))
    (F₂ := PR F K W SP R N A D al n T (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256))
    fun t₁ t₂ h => ⟨mid_pr F hlp L h.2.1, mid_pr F hlp L h.2.2⟩
  have r₆ := (rel_taintC [.r12, .rbp] (P := fun t₁ t₂ => True ∧
      PR F K W SP R N A D al n T (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t₁ ∧
      PR F K W SP R N A D al n T (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t₂) hDW hn
      (fun t₁ t₂ h => ⟨h.2.1.1.1.bufs.one, h.2.2.1.1.bufs.one, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1]
        · rw [h.2.1.2.2, h.2.2.2.2]⟩) (absorb_check true)).wp
    (F₁ := PG F K W SP R N A D al n T) (F₂ := PG F K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨absorb_st true L (h.2.1.1.1.bufs.data.slice (a := 256 * (n / 256)) (k := n % 256)
        (by omega_arith)) h.2.1,
      absorb_st true L (h.2.2.1.1.bufs.data.slice (a := 256 * (n / 256)) (k := n % 256) (by omega_arith)) h.2.2⟩
  have r₇ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ PG F K W SP R N A D al n T t₁ ∧ PG F K W SP R N A D al n T t₂)
      hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.bufs.one, h.2.2.1.bufs.one, fun _ h => nomatch h⟩) lens_check).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨lens_st h.2.1, lens_st h.2.2⟩
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ (RelCT.seq r₆ r₇)))))

theorem ctrFront_rel {lp : Loops} (hlp : Stitch.LoopsOk lp) (hct : LoopsCT lp) (L : Lay K W SP)
    (hR : R = 10 ∨ R = 14) (h256 : 256 ≤ n) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (ctrFront lp) fun _ _ => True := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.bufs.one, (hP _ _ h).2.bufs.one,
      fun _ h => nomatch h⟩) ctrArgs_check).wp
    (F₁ := fun (t : State) => St K W SP R N A D al n T t ∧ CAt W D R n t)
    (F₂ := fun (t : State) => St K W SP R N A D al n T t ∧ CAt W D R n t)
    fun t₁ t₂ h => ⟨ctrArgs_st L hR (hP _ _ h).1, ctrArgs_st L hR (hP _ _ h).2⟩
  have r₂ := (rel_taintC [.rdi, .rsi, .rdx, .rcx, .r8, .r11, .r12, .r9] (P := fun t₁ t₂ => True ∧
      (St K W SP R N A D al n T t₁ ∧ CAt W D R n t₁) ∧ (St K W SP R N A D al n T t₂ ∧ CAt W D R n t₂))
    hDW hn (fun t₁ t₂ h => CAt.both h.2.1 h.2.2) hct.ctrT).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨ctr_st hlp L hR h256 h.2.1, ctr_st hlp L hR h256 h.2.2⟩
  have r₃ := rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) ctrTail_check
  exact RelCT.seq r₁ (RelCT.seq r₂ r₃)

theorem decFront_rel (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (hct : LoopsCT lp) (L : Lay K W SP)
    (hR : R = 10 ∨ R = 14) (h256 : 256 ≤ n) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (decFront lp) fun _ _ => True := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.bufs.one, (hP _ _ h).2.bufs.one,
      fun _ h => nomatch h⟩) decArgs_check).wp
    (F₁ := fun (t : State) => St K W SP R N A D al n T t ∧ CAt W D R n t)
    (F₂ := fun (t : State) => St K W SP R N A D al n T t ∧ CAt W D R n t)
    fun t₁ t₂ h => ⟨decArgs_st F L hR (hP _ _ h).1, decArgs_st F L hR (hP _ _ h).2⟩
  have r₂ := (rel_taintC [.rdi, .rsi, .rdx, .rcx, .r8, .r11, .r12, .r9] (P := fun t₁ t₂ => True ∧
      (St K W SP R N A D al n T t₁ ∧ CAt W D R n t₁) ∧ (St K W SP R N A D al n T t₂ ∧ CAt W D R n t₂))
    hDW hn (fun t₁ t₂ h => CAt.both h.2.1 h.2.2) hct.decT).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨dec_st hlp L hR h256 h.2.1, dec_st hlp L hR h256 h.2.2⟩
  have r₃ := rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) ctrTail_check
  exact RelCT.seq r₁ (RelCT.seq r₂ r₃)

theorem cryptL_rel {lp : Loops} (hlp : Stitch.LoopsOk lp) (hct : LoopsCT lp) (L : Lay K W SP)
    (hR : R = 10 ∨ R = 14) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (cryptL lp) fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂ := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.bufs.one, (hP _ _ h).2.bufs.one,
      fun _ h => nomatch h⟩) lenCmp_check).wp
    (F₁ := fun (t : State) => St K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256)))
    (F₂ := fun (t : State) => St K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256)))
    fun t₁ t₂ h => ⟨lenCmp_st (hP _ _ h).1, lenCmp_st (hP _ _ h).2⟩
  have i₂ : RelCT isa (fun t₁ t₂ => True ∧ (St K W SP R N A D al n T t₁ ∧ t₁.cf = some (decide (n < 256))) ∧
        (St K W SP R N A D al n T t₂ ∧ t₂.cf = some (decide (n < 256))))
      (.ite .b crypt (ctrFront lp)) fun _ _ => True := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [eval_b h.2.1.2, eval_b h.2.2.2]) ?_ ?_
    · exact rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨h.1.2.1.1.bufs.one, h.1.2.2.1.bufs.one, fun _ h => nomatch h⟩)
        crypt_check
    · by_cases hn256 : 256 ≤ n
      · exact ctrFront_rel hDW hn hlp hct L hR hn256 fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
      · refine RelCT.of_false fun _ _ h => hn256 ?_
        have := h.2; rw [eval_b h.1.2.1.2] at this; simp at this; omega_using [this]
  have r₂ := i₂.wp (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨cryptIte_st hlp L hR h.2.1, cryptIte_st hlp L hR h.2.2⟩
  exact RelCT.seq r₁ r₂

theorem decL_rel (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (hct : LoopsCT lp) (L : Lay K W SP)
    (hR : R = 10 ∨ R = 14) (h256 : 256 ≤ n) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (decL lp) fun _ _ => True := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.bufs.one, (hP _ _ h).2.bufs.one,
      fun _ h => nomatch h⟩) polyA_check).wp
    (F₁ := PR F K W SP R N A D al n T A al) (F₂ := PR F K W SP R N A D al n T A al)
    fun t₁ t₂ h => ⟨polyA_wp (hP _ _ h).1, polyA_wp (hP _ _ h).2⟩
  have r₂ := (rel_taintC [.r12, .rbp] (P := fun t₁ t₂ => True ∧ PR F K W SP R N A D al n T A al t₁ ∧
      PR F K W SP R N A D al n T A al t₂) hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.1.bufs.one, h.2.2.1.1.bufs.one, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1]
        · rw [h.2.1.2.2, h.2.2.2.2]⟩) (absorb_check false)).wp
    (F₁ := PG F K W SP R N A D al n T) (F₂ := PG F K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨absorb_st false L h.2.1.1.1.bufs.aad h.2.1, absorb_st false L h.2.2.1.1.bufs.aad h.2.2⟩
  have r₃ := (decFront_rel hDW hn F hlp hct L hR h256 (P := fun t₁ t₂ => True ∧ PG F K W SP R N A D al n T t₁ ∧
      PG F K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨decFront_st F hlp L hR h256 h.2.1.1, decFront_st F hlp L hR h256 h.2.2.1⟩
  have r₄ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂)
      hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) back_check).wp
    (F₁ := PR F K W SP R N A D al n T (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256))
    (F₂ := PR F K W SP R N A D al n T (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256))
    fun t₁ t₂ h => ⟨back_pr F h.2.1, back_pr F h.2.2⟩
  have r₅ := (rel_taintC [.r12, .rbp] (P := fun t₁ t₂ => True ∧
      PR F K W SP R N A D al n T (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t₁ ∧
      PR F K W SP R N A D al n T (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t₂) hDW hn
      (fun t₁ t₂ h => ⟨h.2.1.1.1.bufs.one, h.2.2.1.1.bufs.one, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1]
        · rw [h.2.1.2.2, h.2.2.2.2]⟩) (absorb_check true)).wp
    (F₁ := PG F K W SP R N A D al n T) (F₂ := PG F K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨absorb_st true L (h.2.1.1.1.bufs.data.slice (a := 256 * (n / 256)) (k := n % 256)
        (by omega_arith)) h.2.1,
      absorb_st true L (h.2.2.1.1.bufs.data.slice (a := 256 * (n / 256)) (k := n % 256) (by omega_arith)) h.2.2⟩
  have r₆ := rel_taintC [] (P := fun t₁ t₂ => True ∧ PG F K W SP R N A D al n T t₁ ∧ PG F K W SP R N A D al n T t₂)
      hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.bufs.one, h.2.2.1.bufs.one, fun _ h => nomatch h⟩) lens_check
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ r₆))))

theorem openIte_rel (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (hct : LoopsCT lp) (L : Lay K W SP)
    (hR : R = 10 ∨ R = 14) :
    RelCT isa (fun t₁ t₂ => True ∧ (St K W SP R N A D al n T t₁ ∧ t₁.cf = some (decide (n < 256))) ∧
        (St K W SP R N A D al n T t₂ ∧ t₂.cf = some (decide (n < 256))))
      (.ite .b (.seq crypt polyval) (decL lp))
      fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂ := by
  have i : RelCT isa (fun t₁ t₂ => True ∧ (St K W SP R N A D al n T t₁ ∧ t₁.cf = some (decide (n < 256))) ∧
        (St K W SP R N A D al n T t₂ ∧ t₂.cf = some (decide (n < 256))))
      (.ite .b (.seq crypt polyval) (decL lp)) fun _ _ => True := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [eval_b h.2.1.2, eval_b h.2.2.2]) ?_ ?_
    · exact (RelCT.seq (piece_rel hDW hn crypt_check (fun _ h => crypt_st L hR h)
        fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (polyval_rel hDW hn F L fun _ _ h => h.2)).mono (fun _ _ h => h)
        fun _ _ _ => trivial
    · by_cases hn256 : 256 ≤ n
      · exact decL_rel hDW hn F hlp hct L hR hn256 fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
      · refine RelCT.of_false fun _ _ h => hn256 ?_
        have := h.2; rw [eval_b h.1.2.1.2] at this; simp at this; omega_using [this]
  exact i.wp (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨openIte_st F hlp L hR h.2.1, openIte_st F hlp L hR h.2.2⟩

end

/-! ## The functions -/

/-- `vg_aes_gcm_siv_seal` with the loops, in two runs with the same public
arguments. -/
theorem sealL_rel (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (hct : LoopsCT lp) {s₀ s₀' : State}
    (hp : sealPre s₀) (hp' : sealPre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (sealL lp) fun _ _ => True :=
  seal_relG (fun _ _ _ _ _ _ _ _ _ _ L _ _ h => polyvalL_st F hlp L h)
    (fun _ _ _ _ _ _ _ _ _ _ L hR _ h => cryptL_st hlp L hR h)
    (fun _ _ _ _ _ _ _ _ _ _ hDW hn L _ _ hP => polyvalL_rel hDW hn F hlp hct L hP)
    (fun _ _ _ _ _ _ _ _ _ _ hDW hn L hR _ hP => cryptL_rel hDW hn hlp hct L hR hP)
    hp hp' hq

/-- `vg_aes_gcm_siv_open` with the loops, in two runs with the same public
arguments. -/
theorem openL_rel (F : MulFacts) {lp : Loops} (hlp : Stitch.LoopsOk lp) (hct : LoopsCT lp) {s₀ s₀' : State}
    (hp : openPre s₀) (hp' : openPre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (openL lp) fun _ _ => True := by
  have Ar := (args_of_open hp).1.1
  have hn := Nat.le_of_lt Ar.data.lt
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_open hp').1.1 rfl) (entry_open hp) (entry_open_pub hp' hq)) ?_
  exact openBody_rel Ar.lay Ar.rounds Ar.data.w hn Ar.retW
    ((rel_taintC [] Ar.data.w hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩)
      lenCmp_check).wp fun t₁ t₂ h => ⟨lenCmp_st h.2.1, lenCmp_st h.2.2⟩)
    (openIte_rel Ar.data.w hn F hlp hct Ar.lay Ar.rounds) fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.AesGcmSivReg.X86_64
