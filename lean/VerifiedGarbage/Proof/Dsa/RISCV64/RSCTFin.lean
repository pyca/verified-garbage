module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RSCall
public import VerifiedGarbage.Proof.Dsa.RISCV64.GKCTSample
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Dsa.RISCV64.GKCTSample
import VerifiedGarbage.Proof.Dsa.RISCV64.RSCall
import VerifiedGarbage.Proof.Dsa.RISCV64.RSAttempt
import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSCall
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSAttempt
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# Randomized DSA signing on RISC-V: constant time of the exit

`finish_st`: the exit leaks the same trace in two runs with the same call's
data and status. The taint analysis sees memory secret, so the code that
loads the addresses it then writes through is cut after those loads:
`zeroOut`'s count loop runs from `out`'s address and length (`zblk_ok`),
and the store of the octets consumed from `used`'s address (`usedLd_ok`),
which correctness fixes.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd

/-- Two states of the body with the same call's data agree on its registers. -/
theorem ctx_eq {s₁ s₂ t₁ t₂ : State} (eL : rlOf s₁ = rlOf s₂) (c₁ : Ctx (rlOf s₁) s₁ t₁)
    (c₂ : Ctx (rlOf s₂) s₂ t₂) :
    t₁.sp = t₂.sp ∧ EqRegs t₁ t₂ [.s1, .s2, .s3, .s4] :=
  ⟨by rw [c₁.sp, c₂.sp, eL], by rw [c₁.s1, c₂.s1, eL], by rw [c₁.s2, c₂.s2, eL], by rw [c₁.s3, c₂.s3, eL],
    EqRegs.single (by rw [c₁.s4, c₂.s4, eL])⟩

/-- `zeroOut`'s first block: `out`'s address and length, and 0. -/
theorem zblk_ok {s₀ t : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) :
    WP isa (.block (([.addSp .t3 0, .load .d .t4 .t3 oOut] : List Instr) ++ (lenQ .t5 ++ ([.add .t5 .t5 .t5] : List Instr)) ++ ([.li .a0 0] : List Instr))) t fun t₂ =>
      ((t₂.gpr .a0 = 0 ∧ t₂.gpr .t4 = (rlOf s₀).out ∧ t₂.gpr .t5 = BitVec.ofNat 64 (2 * (rlOf s₀).ql) ∧
        t₂.mem = t.mem) ∧ Keep [.t3, .t4, .t5, .a0, .t2, .t1] t t₂) ∧ t₂.sp = t.sp := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  obtain ⟨i64, l64⟩ := hc.word hL rfl (d := 64) (by decide) (by decide)
  have o64 := hc.out
  simp only [oOut] at o64
  have e1 := lenP_eq (pl := (rlOf s₀).pl) (ql := (rlOf s₀).ql) (by omega) (by omega)
  have e2 := lenQ_eq (pl := (rlOf s₀).pl) (ql := (rlOf s₀).ql) (by omega) (by omega)
  refine wp_sp (WP.keep [.t3, .t4, .t5, .a0, .t2, .t1] ?_ (by decide) (by rfl))
  brun [lenQ, hc.sp, hc.s2, e1, e2, exec_addSp (show 0 < 2048 by decide), BitVec.add_zero, oOut,
    i64, l64, o64, exec_li_zero, ← BitVec.ofNat_add]
  congr 1; omega

/-- `zeroOut`, keeping `Ctx`. -/
theorem zeroOut_ok {s₀ t : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) :
    WP isa (zeroOut (lenQ .t5 ++ ([.add .t5 .t5 .t5] : List Instr))) t fun t' => Ctx (rlOf s₀) s₀ t' := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  obtain ⟨-, hwr⟩ := regions_eq h
  unfold zeroOut
  refine WP.seq (WP.mono (zblk_ok h hc) fun t₂ ⟨⟨⟨b0, b4, b5, m2⟩, k2⟩, sp2⟩ => ?_)
  have ho : ∀ i < 2 * (rlOf s₀).ql, InRegions t₂.wr (off (rlOf s₀).out i) 1 := fun i hi =>
    ⟨(rlOf s₀).outR, by rw [k2.2.2, hc.wr, hwr]; simp,
      VG.Offset.contains_base _ (by omega) (by have := hL.nwOut; omega)⟩
  refine WP.mono (wp_sp (zeroLoopA_ok (by omega) (by omega) ho hL.nwOut
    b0 b4 b5)) fun t₃ ⟨⟨⟨_, o3⟩, k3⟩, sp3⟩ => ?_
  have k23 := k2.trans k3
  refine hc.step hL (sp3.trans sp2) k23.2.1 k23.2.2 (fun r hr => k23.1 r (by revert r hr; decide)) ?_
  rw [← m2]
  intro x hx
  refine o3 x ?_
  by_contra hc'
  exact hx _ (List.mem_cons_self ..) (by simp only [Region.Contains, ofs] at hc' ⊢; omega)

theorem zeroOut_st {s₁ s₂ t₁ t₂ : State} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂)
    (eL : rlOf s₁ = rlOf s₂) (c₁ : Ctx (rlOf s₁) s₁ t₁) (c₂ : Ctx (rlOf s₂) s₂ t₂) :
    SameTrace isa (zeroOut (lenQ .t5 ++ ([.add .t5 .t5 .t5] : List Instr))) t₁ t₂ := by
  have hsp := (ctx_eq eL c₁ c₂).1
  have hr := (ctx_eq eL c₁ c₂).2
  unfold zeroOut
  refine SameTrace.seq (st_taint [.s2] hsp (hr.sub) (by taint_decide)) (zblk_ok h₁ c₁) (zblk_ok h₂ c₂)
    fun u₁ u₂ ⟨⟨⟨_, a4, a5, _⟩, _⟩, sp1⟩ ⟨⟨⟨_, b4, b5, _⟩, _⟩, sp2⟩ => ?_
  exact st_taint [.t4, .t5] (by rw [sp1, sp2, hsp]) ⟨by rw [a4, b4, eL], EqRegs.single (by rw [a5, b5, eL])⟩
    (by taint_decide)

/-- The nonce zeroed and `used`'s address loaded. -/
theorem usedLd_ok {s₀ t : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) :
    WP isa (.block (clearNonce ++ ([.load .d .t4 .t0 oUsed] : List Instr))) t fun u =>
      u.gpr .t4 = (rlOf s₀).used ∧ u.sp = t.sp := by
  have hL := rlOf_ok h
  have hF := hL.fnw
  rw [WP.block_append_iff]
  refine WP.mono (wp_sp (clearNonce_ok t hF hc.sp (scr_nonce hL rfl hc.wr))) fun x ⟨⟨⟨t0, _, o3⟩, k3⟩, sp3⟩ => ?_
  have hc₃ : Ctx (rlOf s₀) s₀ x := hc.step hL sp3 k3.2.1 k3.2.2 (fun r hr => k3.1 r (by revert r hr; decide))
    (outside_frame hL (o := 0) (n := 32) (by decide) o3)
  obtain ⟨i72, l72⟩ := hc₃.word hL rfl (d := 72) (by decide) (by decide)
  have o72 := hc₃.used
  simp only [oUsed] at o72
  refine WP.mono (wp_sp (WP.keep [.t4] (Q := fun u => u.gpr .t4 = (rlOf s₀).used)
    (by brun [t0, oUsed, i72, l72, o72]) (by decide) (by rfl))) fun u ⟨⟨a4, _⟩, spu⟩ => ⟨a4, spu.trans sp3⟩

/-- The exit, from the same call's data and status. -/
theorem finish_st {s₁ s₂ t₁ t₂ : State} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂)
    (eL : rlOf s₁ = rlOf s₂) (c₁ : Ctx (rlOf s₁) s₁ t₁) (c₂ : Ctx (rlOf s₂) s₂ t₂) {st : Nat}
    (a10 : t₁.gpr .s10 = BitVec.ofNat 64 st) (b10 : t₂.gpr .s10 = BitVec.ofNat 64 st) :
    SameTrace isa (finish (lenQ .t5 ++ ([.add .t5 .t5 .t5] : List Instr))) t₁ t₂ := by
  have hL₁ := rlOf_ok h₁
  have hL₂ := rlOf_ok h₂
  have hsp := (ctx_eq eL c₁ c₂).1
  have W : ∀ {y : State}, WP isa (.block [.addi .a0 .s10 (-1)]) y fun z =>
      ((z.mem = y.mem ∧ z.gpr .a0 = y.gpr .s10 - BitVec.ofNat 64 1) ∧ Keep [.a0] y z) ∧ z.sp = y.sp :=
    fun {_} => wp_sp (WP.keep [.a0] (by brun) (by decide) (by rfl))
  unfold finish
  refine SameTrace.seq (st_taint [] hsp trivial (by taint_decide)) W W
    fun u₁ u₂ ⟨⟨⟨m1, a0⟩, k1⟩, sp1⟩ ⟨⟨⟨m2, b0⟩, k2⟩, sp2⟩ => ?_
  have cu₁ : Ctx (rlOf s₁) s₁ u₁ := c₁.step hL₁ sp1 k1.2.1 k1.2.2 (fun r hr => k1.1 r (by revert r hr; decide))
    (by rw [m1]; exact Frame.refl _ _)
  have cu₂ : Ctx (rlOf s₂) s₂ u₂ := c₂.step hL₂ sp2 k2.2.1 k2.2.2 (fun r hr => k2.1 r (by revert r hr; decide))
    (by rw [m2]; exact Frame.refl _ _)
  have I : ∀ {s₀ u : State}, rsContract.pre s₀ → Ctx (rlOf s₀) s₀ u →
      WP isa (.ite (.zero .a0) (.block []) (zeroOut (lenQ .t5 ++ ([.add .t5 .t5 .t5] : List Instr)))) u fun v => Ctx (rlOf s₀) s₀ v := by
    intro s₀ u h hc
    refine WP.ite _ (Steps.eval_zero u .a0) (fun _ => WP.block_nil hc) (fun _ => zeroOut_ok h hc)
  refine SameTrace.seq ?_ (I h₁ cu₁) (I h₂ cu₂) fun v₁ v₂ cv₁ cv₂ => ?_
  · refine SameTrace.ite (by rw [Steps.eval_zero, Steps.eval_zero, a0, b0, a10, b10])
      (fun _ => SameTrace.block_nil) (fun _ => zeroOut_st h₁ h₂ eL cu₁ cu₂)
  have vsp := (ctx_eq eL cv₁ cv₂).1
  rw [show clearNonce ++ [.load .d .t4 .t0 oUsed, .store .d .s5 .t4 0, .addi .a0 .s10 0] ++ restoreRegs =
    (clearNonce ++ [.load .d .t4 .t0 oUsed]) ++ ([.store .d .s5 .t4 0, .addi .a0 .s10 0] ++ restoreRegs) by
      simp only [List.append_assoc, List.cons_append, List.nil_append]]
  refine SameTrace.block_append (SameTrace.seq (st_taint [] vsp trivial (by taint_decide)) (usedLd_ok h₁ cv₁)
    (usedLd_ok h₂ cv₂) fun x₁ x₂ ⟨a4, xs1⟩ ⟨b4, xs2⟩ => ?_)
  exact st_taint [.t4] (by rw [xs1, xs2, vsp]) (EqRegs.single (by rw [a4, b4, eL])) (by taint_decide)

end VG.Proof.Dsa.RISCV64.RS
