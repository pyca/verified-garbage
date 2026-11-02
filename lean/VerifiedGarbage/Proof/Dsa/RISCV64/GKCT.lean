module

public import VerifiedGarbage.Proof.Dsa.RISCV64.GKCTFin
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Dsa.RISCV64.GKCTFin
import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
import VerifiedGarbage.Proof.Dsa.RISCV64.RSAttempt
import VerifiedGarbage.Proof.Dsa.RISCV64.RSSpec
import VerifiedGarbage.Proof.Dsa.RISCV64.RSFinish
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSAttempt
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSSpec
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSFinish
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA key generation on RISC-V: constant time

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/CT.lean`). `generate_ct`: two
runs from states that satisfy `gkContract` and agree on its public data
(the arguments, the domain, and the result's status, octets consumed and
trace) leak the same trace. The runs are followed together
(`SameTrace`), as the correctness proof follows each: the pieces the taint
analysis checks from the registers both runs agree on (`st_taint`), cut
after the loads whose results the code uses as addresses (the scan's
length, `out` and `used`, `GKCTFin.lean`), the calls (`check_st`,
`dcall_st`), and the branches on public data: the domain's validity, q,
the sampling decisions (`sample_st`) and the derivation's success
(`split_marker`), with the callees' `u32` results zero-extended.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.Random (sampleStatus)
open VG.Proof.Dsa.RISCV64.RS (sub1_beq sampleStatus_some nonce_eq zx_beq_zero)

/-! ## The scan of q -/

/-- The first instructions of the scan: q's address and length. -/
theorem qargs_ok {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa (.block (lenP .t3 ++ ([.add .s7 .s1 .t3] : List Instr) ++ lenQ .s8)) t fun t₁ =>
      ((t₁.gpr .s7 = off (glOf s₀).par (glOf s₀).pl ∧ t₁.gpr .s8 = BitVec.ofNat 64 (glOf s₀).ql ∧
        t₁.mem = t.mem) ∧ Keep [.t3, .s7, .s8] t t₁) ∧ t₁.sp = t.sp := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have e1 := lenP_eq (pl := (glOf s₀).pl) (ql := (glOf s₀).ql) (by omega) (by omega)
  have e2 := lenQ_eq (pl := (glOf s₀).pl) (ql := (glOf s₀).ql) (by omega) (by omega)
  exact wp_sp (WP.keep [.t3, .s7, .s8] (by brun [lenP, lenQ, hc.s1, hc.s2, e1, e2]) (by decide) (by rfl))

/-- q's octets, and the one after, are readable. -/
theorem q_in {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    ∀ i ≤ (glOf s₀).ql, InRegions (t.rd ++ t.wr) (off (off (glOf s₀).par (glOf s₀).pl) i) 1 := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have hk := hL.nwPar
  have ekl : (glOf s₀).kl = 2 * (glOf s₀).pl + (glOf s₀).ql := rfl
  obtain ⟨hrd, -⟩ := regions_eq h
  intro i hi
  rw [hc.rd, off_off]
  exact ⟨(glOf s₀).parR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
    VG.Offset.contains_base _ (by omega) (by omega)⟩

theorem prepareQ_st {s₁ s₂ t₁ t₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂)
    (eL : glOf s₁ = glOf s₂) (eq : qbOf (glOf s₁) s₁.mem = qbOf (glOf s₁) s₂.mem)
    (c₁ : Ctx (glOf s₁) s₁ t₁) (c₂ : Ctx (glOf s₂) s₂ t₂) : SameTrace isa prepareQ t₁ t₂ := by
  have hsp := (ctx_eq eL c₁ c₂).1
  have hr := (ctx_eq eL c₁ c₂).2
  have hq₁ := (glOf_ok h₁).ql
  have hq₂ := (glOf_ok h₂).ql
  unfold prepareQ prepare
  refine SameTrace.seq (st_taint [.s1, .s2] hsp hr.sub (by taint_decide)) (qargs_ok h₁ c₁)
    (qargs_ok h₂ c₂) fun u₁ u₂ ⟨⟨⟨a7, a8, m1⟩, k1⟩, sp1⟩ ⟨⟨⟨b7, b8, m2⟩, k2⟩, sp2⟩ => ?_
  have usp : u₁.sp = u₂.sp := by rw [sp1, sp2, hsp]
  have e7 : u₁.gpr .s7 = u₂.gpr .s7 := by rw [a7, b7, eL]
  have e8 : u₁.gpr .s8 = u₂.gpr .s8 := by rw [a8, b8, eL]
  refine SameTrace.seq (st_taint [.s7, .s8] usp ⟨e7, e8⟩ (by taint_decide))
    (wp_sp (sigLen_ok a7 a8 (by omega) (by omega) fun i hi => by
      rw [k1.2.1, k1.2.2]; exact q_in h₁ c₁ i (by omega)))
    (wp_sp (sigLen_ok b7 b8 (by omega) (by omega) fun i hi => by
      rw [k2.2.1, k2.2.2]; exact q_in h₂ c₂ i (by omega)))
    fun v₁ v₂ ⟨⟨⟨x1, _⟩, kv1⟩, spv1⟩ ⟨⟨⟨y1, _⟩, kv2⟩, spv2⟩ => ?_
  rw [m1, c₁.qb (glOf_ok h₁)] at x1
  rw [m2, c₂.qb (glOf_ok h₂), ← eL, ← eq] at y1
  exact st_taint [.s7, .s8, .a1] (by rw [spv1, spv2, usp])
    ⟨by rw [kv1.gpr (by decide), kv2.gpr (by decide), e7], by rw [kv1.gpr (by decide), kv2.gpr (by decide), e8],
      EqRegs.single (by rw [x1, y1])⟩ (by taint_decide)

/-! ## The derivation -/

theorem deriveFinish_st {v₁ v₂ : State} (hsp : v₁.sp = v₂.sp) {st₁ st₂ : Nat}
    (h₁ : ((v₁.gpr .a0).setWidth 32).toNat = st₁) (h₂ : ((v₂.gpr .a0).setWidth 32).toNat = st₂)
    (hs : st₁ = st₂) : SameTrace isa deriveFinish v₁ v₂ := by
  have W : ∀ {y : State}, WP isa (.block zx) y fun z =>
      ((z.mem = y.mem ∧ z.gpr .a0 = (y.gpr .a0 <<< 32) >>> 32) ∧ Keep [.a0] y z) ∧ z.sp = y.sp :=
    fun {_} => wp_sp (WP.keep [.a0] (by brun [zx]) (by decide) (by rfl))
  unfold deriveFinish
  refine SameTrace.seq (st_taint [] hsp trivial (by taint_decide)) W W
    fun u₁ u₂ ⟨⟨⟨_, a0⟩, _⟩, sp1⟩ ⟨⟨⟨_, b0⟩, _⟩, sp2⟩ => ?_
  have usp : u₁.sp = u₂.sp := by rw [sp1, sp2, hsp]
  exact SameTrace.ite (by rw [Steps.eval_zero, Steps.eval_zero, a0, b0, zx_beq_zero h₁, zx_beq_zero h₂, hs])
    (fun _ => by exact st_taint [] usp trivial (by taint_decide))
    (fun _ => by exact st_taint [] usp trivial (by taint_decide))

/-- The derivation's success, by its marker. -/
theorem isSome_eq {s₁ s₂ : State} {x₁ x₂ : Nat} (hx₁ : (drawOf s₁).scalar = some x₁)
    (hx₂ : (drawOf s₂).scalar = some x₂) (emk : mkOf s₁ = mkOf s₂) :
    (dkOf s₁ x₁).isSome = (dkOf s₂ x₂).isSome := by
  simp only [mkOf, hx₁, hx₂, List.cons.injEq, and_true] at emk
  cases a : (dkOf s₁ x₁).isSome <;> cases b : (dkOf s₂ x₂).isSome <;> simp_all

theorem derive_st {s₁ s₂ t₁ t₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂)
    (eL : glOf s₁ = glOf s₂) (ep : parOf s₁ = parOf s₂) (hq₁ : 1 < qOf s₁) (hq₂ : 1 < qOf s₂)
    (c₁ : Ctx (glOf s₁) s₁ t₁) (c₂ : Ctx (glOf s₂) s₂ t₂) (z₁ : NZero s₁ t₁.mem) (z₂ : NZero s₂ t₂.mem)
    (a10 : t₁.gpr .s10 = BitVec.ofNat 64 (sampleStatus (drawOf s₁)))
    (b10 : t₂.gpr .s10 = BitVec.ofNat 64 (sampleStatus (drawOf s₂)))
    (k₁ : ∀ x, (drawOf s₁).scalar = some x → Spec.Dsa.decodeBE (cands (eOf s₁) t₁.mem) = x)
    (k₂ : ∀ x, (drawOf s₂).scalar = some x → Spec.Dsa.decodeBE (cands (eOf s₂) t₂.mem) = x)
    (est : sampleStatus (drawOf s₁) = sampleStatus (drawOf s₂)) (emk : mkOf s₁ = mkOf s₂) :
    SameTrace isa Impl.Dsa.RISCV64.Generate.derive t₁ t₂ := by
  have hL₁ := glOf_ok h₁
  have hL₂ := glOf_ok h₂
  have hE₁ : (eOf s₁).Ok := seOf_ok hL₁ s₁.mem hq₁
  have hE₂ : (eOf s₂).Ok := seOf_ok hL₂ s₂.mem hq₂
  have tsp : t₁.sp = t₂.sp := (ctx_eq eL c₁ c₂).1
  have hs₁ := sampleStatus_le (drawOf s₁)
  have hs₂ := sampleStatus_le (drawOf s₂)
  have W : ∀ {y : State}, WP isa (.block [.addi .a0 .s10 (-1)]) y fun z =>
      ((z.mem = y.mem ∧ z.gpr .a0 = y.gpr .s10 - BitVec.ofNat 64 1) ∧ Keep [.a0] y z) ∧ z.sp = y.sp :=
    fun {_} => wp_sp (WP.keep [.a0] (by brun) (by decide) (by rfl))
  unfold Impl.Dsa.RISCV64.Generate.derive
  refine SameTrace.seq (st_taint [] tsp trivial (by taint_decide)) W W
    fun u₁ u₂ ⟨⟨⟨m1, a3⟩, k1⟩, sp1⟩ ⟨⟨⟨m2, b3⟩, k2⟩, sp2⟩ => ?_
  have usp : u₁.sp = u₂.sp := by rw [sp1, sp2, tsp]
  have ev₁ : isa.eval (.zero .a0) u₁ = some (decide (sampleStatus (drawOf s₁) = 1)) := by
    rw [Steps.eval_zero, a3, a10, sub1_beq _ (by omega)]
  have ev₂ : isa.eval (.zero .a0) u₂ = some (decide (sampleStatus (drawOf s₂) = 1)) := by
    rw [Steps.eval_zero, b3, b10, sub1_beq _ (by omega)]
  refine SameTrace.ite (by rw [ev₁, ev₂, est]) (fun hc => ?_) (fun _ => SameTrace.block_nil)
  rw [ev₁, Option.some.injEq, decide_eq_true_eq] at hc
  obtain ⟨x₁, hx₁⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp hc)
  obtain ⟨x₂, hx₂⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp (est ▸ hc))
  have cz₁ : Ctx (glOf s₁) s₁ u₁ :=
    c₁.step hL₁ sp1 k1.2.1 k1.2.2 (fun r hr => k1.1 r (by revert r hr; decide)) (by rw [m1]; exact Frame.refl _ _)
  have cz₂ : Ctx (glOf s₂) s₂ u₂ :=
    c₂.step hL₂ sp2 k2.2.1 k2.2.2 (fun r hr => k2.1 r (by revert r hr; decide)) (by rw [m2]; exact Frame.refl _ _)
  have nn₁ : Spec.Rsa.bytesAt u₁.mem (off (glOf s₁).F oNonce) (glOf s₁).ql = Spec.Dsa.encodeBE (glOf s₁).ql x₁ := by
    rw [m1]; exact nonce_eq (W := (eOf s₁).W) hE₁.Wq z₁ (k₁ x₁ hx₁)
  have nn₂ : Spec.Rsa.bytesAt u₂.mem (off (glOf s₂).F oNonce) (glOf s₂).ql = Spec.Dsa.encodeBE (glOf s₂).ql x₂ := by
    rw [m2]; exact nonce_eq (W := (eOf s₂).W) hE₂.Wq z₂ (k₂ x₂ hx₂)
  have hr := (ctx_eq eL cz₁ cz₂).2
  refine SameTrace.seq (st_taint [.s1, .s2, .s6] usp hr.sub (by taint_decide))
    (deriveArgs_ok hL₁ rfl cz₁) (deriveArgs_ok hL₂ rfl cz₂) fun w₁ w₂ ⟨⟨A₁, mw₁, _⟩, _⟩ ⟨⟨A₂, mw₂, _⟩, _⟩ => ?_
  have es₁ : dresOf (glOf s₁) w₁.mem = dkOf s₁ x₁ := by
    simp only [dresOf, dkOf, parOf]; rw [mw₁, cz₁.par, nn₁]
  have es₂ : dresOf (glOf s₂) w₂.mem = dkOf s₂ x₂ := by
    simp only [dresOf, dkOf, parOf]; rw [mw₂, cz₂.par, nn₂]
  have hs : Spec.Dsa.signStatus (dresOf (glOf s₁) w₁.mem) = Spec.Dsa.signStatus (dresOf (glOf s₂) w₂.mem) := by
    rw [es₁, es₂]; simp only [Spec.Dsa.signStatus, isSome_eq hx₁ hx₂ emk]
  refine SameTrace.seq (dcall_st h₁ h₂ eL ep A₁ A₂ hs) (derive_ok h₁ A₁) (derive_ok h₂ A₂) fun v₁ v₂ D₁ D₂ => ?_
  exact deriveFinish_st (by rw [D₁.ctx.sp, D₂.ctx.sp, eL]) D₁.a0 D₂.a0 hs

/-! ## A valid domain, and the function -/

/-- After the draw: `Ctx`, and the nonce's leading zeros. -/
theorem after_sample {s₀ t₃ t₄ : State} {S : Spec.Dsa.Random.Sample} (h : gkContract.pre s₀) (hq : 1 < qOf s₀)
    (sc : Scanned (glOf s₀) s₀ t₃) (nz : ∀ j < 32, t₃.mem (off (glOf s₀).F (oNonce + j)) = 0)
    (so : SampleOut (eOf s₀) (randOf (glOf s₀) s₀.mem) 0 S t₃ t₄) :
    Ctx (glOf s₀) s₀ t₄ ∧ NZero s₀ t₄.mem := by
  have hL := glOf_ok h
  have hql := hL.ql
  have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have hW : (eOf s₀).W ≤ (eOf s₀).ql := hE.Wq
  have hql' : (eOf s₀).ql ≤ 32 := hE.ql
  have hF := hL.fnw
  refine ⟨sc.ctx.step hL (so.env.sp.trans sc.ctx.sp.symm) so.keep.2.1 so.keep.2.2
    (fun r hr => so.keep.1 r (by revert r hr; decide))
    (outside_frame hL (o := (eOf s₀).ql - (eOf s₀).W) (n := (eOf s₀).W) (by omega) so.out), fun j hj => ?_⟩
  have e : ofs (eOf s₀).F (off (glOf s₀).F (oNonce + j)) = oNonce + j :=
    Mont.ofs_off0 _ (by simp only [oNonce, frameBytes] at hF ⊢; omega)
  have hj' : oNonce + j < (eOf s₀).o := by
    have e2 : (eOf s₀).ql = (glOf s₀).ql := rfl
    simp only [SE.o]; omega
  rw [so.out _ (.inl (by rw [e]; exact hj'))]
  exact nz j (by omega)

theorem valid_st {s₁ s₂ t₁ t₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂)
    (eL : glOf s₁ = glOf s₂) (ep : parOf s₁ = parOf s₂) (ck₁ : Chk s₁ t₁) (ck₂ : Chk s₂ t₂)
    (c₁ : chkOf s₁ = true) (c₂ : chkOf s₂ = true) (ht : (resOf s₁).trace = (resOf s₂).trace) :
    SameTrace isa valid t₁ t₂ := by
  have eq := qb_eq h₁ eL ep
  obtain ⟨eQ, eE⟩ := same_q eL eq
  have hL₁ := glOf_ok h₁
  have hL₂ := glOf_ok h₂
  unfold valid
  refine SameTrace.seq (prepareQ_st h₁ h₂ eL eq ck₁.ctx ck₂.ctx) (prepareQ_ok h₁ ck₁.ctx) (prepareQ_ok h₂ ck₂.ctx)
    fun u₁ u₂ ⟨⟨sc₁, z₁, m₁, k₁⟩, _⟩ ⟨⟨sc₂, z₂, m₂, k₂⟩, _⟩ => ?_
  have usp := (ctx_eq eL sc₁.ctx sc₂.ctx).1
  have z₂' : u₂.gpr .a0 = 0 ↔ ¬ 1 < qOf s₁ := by rw [← eQ]; exact z₂
  refine SameTrace.ite (by rw [Steps.eval_zero, Steps.eval_zero, beq_of_iff z₁, beq_of_iff z₂'])
    (fun _ => by exact st_taint [] usp trivial (by taint_decide)) (fun hc => ?_)
  rw [Steps.eval_zero, beq_of_iff z₁, Option.some.injEq, decide_eq_false_iff_not, Decidable.not_not] at hc
  have hq₂ : 1 < qOf s₂ := eQ ▸ hc
  have hE₁ : (eOf s₁).Ok := seOf_ok hL₁ s₁.mem hc
  have hE₂ : (eOf s₂).Ok := seOf_ok hL₂ s₂.mem hq₂
  have hQ₁ := seOf_Q (L := glOf s₁) s₁.mem hc
  have hQ₂ := seOf_Q (L := glOf s₂) s₂.mem hq₂
  have env₁ := sc₁.env h₁ hc
  have env₂ := sc₂.env h₂ hq₂
  have env₂' : SEnv (eOf s₁) (randOf (glOf s₂) s₂.mem) u₂ := eE ▸ env₂
  have r₁ : u₁.gpr .s5 = BitVec.ofNat 64 0 := (k₁.gpr (by decide)).trans ck₁.s5
  have r₂ : u₂.gpr .s5 = BitVec.ofNat 64 0 := (k₂.gpr (by decide)).trans ck₂.s5
  obtain ⟨tD, emk⟩ := trace_split c₁ c₂ ht
  have tS : (Spec.Dsa.Random.sample (qOf s₁) 128 (randOf (glOf s₁) s₁.mem)).trace =
      (Spec.Dsa.Random.sample (qOf s₁) 128 (randOf (glOf s₂) s₂.mem)).trace := by
    have e : drawOf s₂ = Spec.Dsa.Random.sample (qOf s₁) 128 (randOf (glOf s₂) s₂.mem) := by
      show Spec.Dsa.Random.sample (qOf s₂) _ _ = _
      rw [eQ]
    rw [← e]; exact tD
  have est : sampleStatus (drawOf s₁) = sampleStatus (drawOf s₂) := by
    have := (VG.Proof.Dsa.Random.sample_trace_agree tS).2.2
    show _ = sampleStatus (Spec.Dsa.Random.sample (qOf s₂) 128 _)
    rw [eQ]; exact this
  have tS' : (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (qbOf (glOf s₁) s₁.mem)) 128
      ((randOf (glOf s₁) s₁.mem).drop 0)).trace = (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (qbOf (glOf s₁) s₁.mem))
      128 ((randOf (glOf s₂) s₂.mem).drop 0)).trace := by
    rw [List.drop_zero, List.drop_zero]; exact tS
  refine SameTrace.seq (sample_st hE₁ hQ₁ env₁ env₂' r₁ r₂ (Nat.zero_le _) tS')
    (sample_ok hE₁ hQ₁ env₁ r₁ (Nat.zero_le _)) (sample_ok hE₂ hQ₂ env₂ r₂ (Nat.zero_le _))
    fun y₁ y₂ so₁ so₂ => ?_
  rw [List.drop_zero] at so₁ so₂
  obtain ⟨cy₁, ny₁⟩ := after_sample h₁ hc sc₁ (fun j hj => by rw [m₁]; exact ck₁.nonce j hj) so₁
  obtain ⟨cy₂, ny₂⟩ := after_sample h₂ hq₂ sc₂ (fun j hj => by rw [m₂]; exact ck₂.nonce j hj) so₂
  exact derive_st h₁ h₂ eL ep hc hq₂ cy₁ cy₂ ny₁ ny₂ so₁.s10 so₂.s10 so₁.cand so₂.cand est emk

theorem generate_ct : ConstantTime isa gkContract.pre gkContract.pub Impl.Dsa.RISCV64.Generate.code := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ hp => ?_
  obtain ⟨eL, ep, est, etr⟩ := pub_facts h₁ h₂ hp
  have hL₁ := glOf_ok h₁
  have hL₂ := glOf_ok h₂
  have hsp : s₁.sp = s₂.sp := hp.1
  unfold Impl.Dsa.RISCV64.Generate.code
  refine st_alloc ?_
  unfold Impl.Dsa.RISCV64.Generate.body
  refine SameTrace.seq (st_taint [] (by simp only [allocd, hsp]) trivial (by taint_decide))
    (entry_ok h₁) (entry_ok h₂) fun t₁ t₂ E₁ E₂ => ?_
  have tsp := (ctx_eq eL E₁.ctx E₂.ctx).1
  have tr := (ctx_eq eL E₁.ctx E₂.ctx).2
  have hck : SameTrace isa (.seq (.block checkArgs)
      (.call "vg_dsa_check_parameters" Impl.Dsa.RISCV64.Params.checkParameters)) t₁ t₂ :=
    SameTrace.seq (st_taint [.s1, .s2, .s6] tsp tr.sub (by taint_decide))
      (checkArgs_ok hL₁ rfl E₁.ctx) (checkArgs_ok hL₂ rfl E₂.ctx)
      fun _ _ ⟨⟨A₁, _, _⟩, _⟩ ⟨⟨A₂, _, _⟩, _⟩ => check_st h₁ h₂ eL ep A₁ A₂
  refine SameTrace.seq hck (checked_ok h₁ E₁) (checked_ok h₂ E₂) fun u₁ u₂ ck₁ ck₂ => ?_
  have usp := (ctx_eq eL ck₁.ctx ck₂.ctx).1
  have ec := chk_eq eL ep
  refine SameTrace.assoc_left (SameTrace.seq (st_taint [] usp trivial (by taint_decide)) (zx_ok hL₁ ck₁.ctx)
    (zx_ok hL₂ ck₂.ctx) fun x₁ x₂ ⟨cx₁, z1, mx1, g1⟩ ⟨cx₂, z2, mx2, g2⟩ => ?_)
  have xsp := (ctx_eq eL cx₁ cx₂).1
  have s5₁ : x₁.gpr .s5 = BitVec.ofNat 64 0 := (g1 _ (by decide)).trans ck₁.s5
  have s5₂ : x₂.gpr .s5 = BitVec.ofNat 64 0 := (g2 _ (by decide)).trans ck₂.s5
  refine SameTrace.seq_ite (by rw [Steps.eval_zero, Steps.eval_zero, z1, z2, zx_beq_zero ck₁.a0,
      zx_beq_zero ck₂.a0, ec]) (fun hc => ?_) (fun hc => ?_)
  · -- An invalid domain.
    refine SameTrace.seq (st_taint [] xsp trivial (by taint_decide)) (li0_ok hL₁ cx₁) (li0_ok hL₂ cx₂)
      fun y₁ y₂ ⟨cy₁, a10, _, _⟩ ⟨cy₂, b10, _, _⟩ => ?_
    exact finish_st h₁ h₂ eL cy₁ cy₂ a10 b10
  · -- A valid domain.
    rw [Steps.eval_zero, z1, zx_beq_zero ck₁.a0, Option.some.injEq, decide_eq_false_iff_not] at hc
    have c₁ : chkOf s₁ = true := by cases hc' : chkOf s₁ <;> simp_all
    have c₂ : chkOf s₂ = true := ec ▸ c₁
    have ck₁' : Chk s₁ x₁ := ⟨cx₁, s5₁, fun j hj => by rw [mx1]; exact ck₁.nonce j hj, by
      rw [z1, BitVec.toNat_setWidth, RS.zx_toNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; exact ck₁.a0⟩
    have ck₂' : Chk s₂ x₂ := ⟨cx₂, s5₂, fun j hj => by rw [mx2]; exact ck₂.nonce j hj, by
      rw [z2, BitVec.toNat_setWidth, RS.zx_toNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; exact ck₂.a0⟩
    refine SameTrace.seq (valid_st h₁ h₂ eL ep ck₁' ck₂' c₁ c₂ etr) (valid_ok h₁ ck₁' c₁) (valid_ok h₂ ck₂' c₂)
      fun v₁ v₂ V₁ V₂ => ?_
    exact finish_st h₁ h₂ eL V₁.ctx V₂.ctx V₁.s10 (V₂.s10.trans (by rw [est]))

end VG.Proof.Dsa.RISCV64.GK
