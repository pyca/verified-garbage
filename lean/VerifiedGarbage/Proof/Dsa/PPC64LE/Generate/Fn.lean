module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Finish
public import VerifiedGarbage.Proof.Dsa.RandomResult
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Range
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Sample
import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Attempt
import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Spec
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.DeriveCall
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generate
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Params
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Check
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Entry
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Sampler
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Prepare
public import VerifiedGarbage.Spec.Dsa.Derive

/-!
# DSA key generation on PPC64LE: the function

`generate_correct`: `vg_dsa_generate_key` meets `gkContract`. In its frame,
the entry (`entry_ok`), the check of the domain (`checked_ok`), then for a
valid domain the scan of q (`prepareQ_ok`), the sampling (`sample_ok`) and
the derivation (`derive_ok`), and the exit (`finish_ok`) follow one
another; the result is `generateKeyBytes`'s (`gkRes_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa.Random (sampleStatus)

/-- q, on entry. -/
abbrev qOf (s₀ : State) : Nat := Spec.Dsa.decodeBE (qbOf (glOf s₀) s₀.mem)

/-- The sampler's data, on entry. -/
abbrev eOf (s₀ : State) : SE := seOf (glOf s₀) (qbOf (glOf s₀) s₀.mem)

/-- The draw of x. -/
abbrev drawOf (s₀ : State) : Spec.Dsa.Random.Sample :=
  Spec.Dsa.Random.sample (qOf s₀) 128 (randOf (glOf s₀) s₀.mem)

/-- The domain, on entry. -/
abbrev parOf (s₀ : State) : List Byte := Spec.Rsa.bytesAt s₀.mem (glOf s₀).par (glOf s₀).kl

/-- The key derived from `x`. -/
abbrev dkOf (s₀ : State) (x : Nat) : Option (List Byte) :=
  Spec.Dsa.deriveKeyBytes (glOf s₀).pl (glOf s₀).ql (parOf s₀) (Spec.Dsa.encodeBE (glOf s₀).ql x)

/-- The result, by the domain's check and the draw. -/
abbrev resOf (s₀ : State) : Spec.Dsa.GenerateKeyResult :=
  if chkOf s₀ then
    match (drawOf s₀).scalar with
    | none => ⟨none, if (drawOf s₀).trace.getLast? == some 2 then 2 else 0, (drawOf s₀).used, (drawOf s₀).trace⟩
    | some x => ⟨dkOf s₀ x, Spec.Dsa.signStatus (dkOf s₀ x), (drawOf s₀).used,
        (drawOf s₀).trace ++ [if (dkOf s₀ x).isSome then 5 else 6]⟩
  else ⟨none, 0, 0, [4]⟩

theorem gkRes_eq {s₀ : State} (h : gkContract.pre s₀) : gkRes s₀ = resOf s₀ := by
  have hL := glOf_ok h
  have hq := hL.ql
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hkl, -⟩ := h
  have e7 : (s₀.gpr .r7).toNat = (glOf s₀).kl := hkl
  have hq' : (Spec.Dsa.paramsBytes (glOf s₀).pl (glOf s₀).ql (parOf s₀)).q = qOf s₀ := by
    rw [VG.Proof.Dsa.paramsBytes_eq]
    show Spec.Dsa.decodeBE _ = Spec.Dsa.decodeBE _
    rw [VG.Proof.Dsa.bytesAt_slice s₀.mem _ (by simp only [GL.kl]; omega)]
  unfold gkRes
  rw [e7]
  show Spec.Dsa.generateKeyBytes (glOf s₀).pl (glOf s₀).ql (parOf s₀) (randOf (glOf s₀) s₀.mem) = _
  rw [VG.Proof.Dsa.generateKeyBytes_eq hL.lv (by rw [VG.Proof.Bignum.bytesAt_length])]
  simp only [hq']
  rfl

theorem resOf_status (s₀ : State) : (resOf s₀).status ≤ 2 := by
  unfold resOf
  split
  · split
    · dsimp only; split <;> omega
    · dsimp only; unfold Spec.Dsa.signStatus; split <;> omega
  · dsimp only; omega

theorem resOf_none {s₀ : State} (hs : (resOf s₀).status ≠ 1) : (resOf s₀).key = none := by
  revert hs
  unfold resOf
  split
  · split
    · intro _; rfl
    · dsimp only
      intro hs
      unfold Spec.Dsa.signStatus at hs
      split at hs
      · exact absurd rfl hs
      · rename_i hn; simpa using hn
  · intro _; rfl

/-- A frame's octet is kept by a call that writes regions apart from the frame. -/
theorem frame_byte {L : GL} (hL : L.Ok) {rs : List Region} (hd : ∀ r ∈ rs, L.frR.Disjoint r) {m m' : Mem}
    (hf : Frame rs m m') {d : Nat} (hdl : d < frameBytes) : m' (off L.F d) = m (off L.F d) := by
  have hF := hL.fnw
  refine hf _ fun r hr hc => ?_
  have hin : L.frR.Contains (off L.F d) 1 :=
    VG.Offset.contains_base _ (by omega) (by simp only [frameBytes] at hdl; omega)
  exact hd r hr _ hin hc

/-- After the check of the domain. -/
structure Chk (s₀ : State) (t : State) : Prop where
  ctx : Ctx (glOf s₀) s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 0
  nonce : ∀ j < 32, t.mem (off (glOf s₀).F (oNonce + j)) = 0
  r3 : ((t.gpr .r3).setWidth 32).toNat = if chkOf s₀ then 1 else 0

theorem checked_ok {s₀ t : State} (h : gkContract.pre s₀) (he : Entered (glOf s₀) s₀ t) :
    WP isa (.seq (.block checkArgs) (.call "vg_dsa_check_parameters" Impl.Dsa.PPC64LE.Params.checkParameters)) t
      (Chk s₀) := by
  have hL := glOf_ok h
  refine WP.seq (WP.mono (checkArgs_ok hL he.ctx) fun t₂ ⟨ca, m2, k2⟩ => WP.mono (check_ok h ca) fun t₃ ck => ?_)
  refine ⟨ck.ctx, (ck.pres _ (by decide)).trans ((k2.gpr _ (by decide)).trans he.r25), fun j hj => ?_, ck.r3⟩
  rw [frame_byte hL (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dFS) ck.frame
    (by simp only [oNonce, frameBytes]; omega), m2]
  exact he.nonce j hj

/-- The nonce's first `q_len − W` octets are zero. -/
abbrev NZero (s₀ : State) (m : Mem) : Prop :=
  ∀ j < (glOf s₀).ql - (eOf s₀).W, m (off (glOf s₀).F (oNonce + j)) = 0

/-- The derivation, from the sampler's result. -/
theorem derive_wp {s₀ t : State} (h : gkContract.pre s₀) (hq : 1 < qOf s₀) (hc : Ctx (glOf s₀) s₀ t)
    (hz : NZero s₀ t.mem) (h25 : t.gpr .r25 = BitVec.ofNat 64 (drawOf s₀).used)
    (h31 : t.gpr .r31 = BitVec.ofNat 64 (sampleStatus (drawOf s₀)))
    (hk : ∀ x, (drawOf s₀).scalar = some x → Spec.Dsa.decodeBE (cands (eOf s₀) t.mem) = x)
    (hchk : chkOf s₀ = true) :
    WP isa Impl.Dsa.PPC64LE.Generate.derive t fun t' =>
      Ctx (glOf s₀) s₀ t' ∧ t'.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used ∧
        t'.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status ∧
        ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t'.mem (glOf s₀).out (glOf s₀).ol =
          (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)) := by
  have hL := glOf_ok h
  have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have hst := sampleStatus_le (drawOf s₀)
  unfold Impl.Dsa.PPC64LE.Generate.derive
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun t₂ => t₂.mem = t.mem ∧
    t₂.gpr .r3 = t.gpr .r31 - BitVec.ofNat 64 1) (by prun) (by decide)) fun t₂ ⟨⟨m2, a3⟩, k2⟩ => ?_)
  have c₂ : Ctx (glOf s₀) s₀ t₂ :=
    hc.step hL k2.sp k2.rd k2.wr (fun r hr => k2.gpr r (ctx_r3 r hr)) (by rw [m2]; exact Frame.refl _ _)
  have b25 : t₂.gpr .r25 = BitVec.ofNat 64 (drawOf s₀).used := (k2.gpr _ (by decide)).trans h25
  refine WP.ite (decide (sampleStatus (drawOf s₀) = 1))
    (by rw [eval_zero, a3, h31, RS.sub1_beq _ (by omega)]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (RS.sampleStatus_some.mp hs)
    have hR : resOf s₀ = ⟨dkOf s₀ x, Spec.Dsa.signStatus (dkOf s₀ x), (drawOf s₀).used,
        (drawOf s₀).trace ++ [if (dkOf s₀ x).isSome then 5 else 6]⟩ := by
      simp only [resOf, hchk, ite_true, hx]
    have hnonce : Spec.Rsa.bytesAt t₂.mem (off (glOf s₀).F oNonce) (glOf s₀).ql =
        Spec.Dsa.encodeBE (glOf s₀).ql x := by
      rw [m2]
      exact RS.nonce_eq (W := (eOf s₀).W) hE.Wq hz (hk x hx)
    refine WP.seq (WP.mono (deriveArgs_ok hL c₂) fun t₃ ⟨da, m3, k3⟩ => ?_)
    refine WP.seq (WP.mono (derive_ok h da) fun t₄ dv => ?_)
    have es : dresOf (glOf s₀) t₃.mem = dkOf s₀ x := by
      simp only [dresOf, dkOf, parOf]; rw [m3, c₂.par, hnonce]
    have hr3 := dv.r3
    rw [es] at hr3
    unfold deriveFinish
    refine WP.ite (decide (Spec.Dsa.signStatus (dkOf s₀ x) = 0))
      (by rw [RS.eval_zero_w, RS.setWidth_beq_zero hr3]) (fun hz' => ?_) (fun hz' => ?_)
    · simp only [decide_eq_true_eq] at hz'
      refine WP.mono (WP.keep (c := .block [.li .r31 0]) [.r31] (Q := fun t₅ => t₅.mem = t₄.mem ∧
        t₅.gpr .r31 = BitVec.ofNat 64 0) (by prun) (by decide)) fun t₅ ⟨⟨m5, a31⟩, k5⟩ => ?_
      refine ⟨dv.ctx.step hL k5.sp k5.rd k5.wr (fun r hr => k5.gpr r (ctx_31 r hr))
        (by rw [m5]; exact Frame.refl _ _), ?_, ?_, fun _ => ?_⟩
      · rw [k5.gpr _ (by decide), dv.pres _ (by decide), k3.gpr _ (by decide), b25, hR]
      · rw [a31, hR]; dsimp only; rw [hz']
      · rw [m5, dv.out, es, hR]
    · simp only [decide_eq_false_iff_not] at hz'
      refine WP.mono (WP.keep (c := .block [.li .r31 1]) [.r31] (Q := fun t₅ => t₅.mem = t₄.mem ∧
        t₅.gpr .r31 = BitVec.ofNat 64 1) (by prun) (by decide)) fun t₅ ⟨⟨m5, a31⟩, k5⟩ => ?_
      refine ⟨dv.ctx.step hL k5.sp k5.rd k5.wr (fun r hr => k5.gpr r (ctx_31 r hr))
        (by rw [m5]; exact Frame.refl _ _), ?_, ?_, fun _ => ?_⟩
      · rw [k5.gpr _ (by decide), dv.pres _ (by decide), k3.gpr _ (by decide), b25, hR]
      · rw [a31, hR]; dsimp only
        unfold Spec.Dsa.signStatus at hz' ⊢
        split at hz' <;> simp_all
      · rw [m5, dv.out, es, hR]
  · simp only [decide_eq_false_iff_not] at hs
    have hx : (drawOf s₀).scalar = none := by
      cases hc' : (drawOf s₀).scalar with
      | none => rfl
      | some k => exact absurd (RS.sampleStatus_some.mpr (by rw [hc']; rfl)) hs
    have hR : resOf s₀ = ⟨none, if (drawOf s₀).trace.getLast? == some 2 then 2 else 0, (drawOf s₀).used,
        (drawOf s₀).trace⟩ := by
      simp only [resOf, hchk, ite_true, hx]
    refine WP.block_nil ⟨c₂, by rw [b25, hR], ?_, fun h1 => ?_⟩
    · rw [(k2.gpr _ (by decide)).trans h31, hR]
      simp only [sampleStatus, hx]
    · rw [hR] at h1 ⊢
      exact absurd h1 (by dsimp only; split <;> decide)

theorem ctx_draw : ∀ r ∈ ctxRegs, r ∉ drawRegs := by decide

theorem ctx_prep : ∀ r ∈ ctxRegs, r ∉ (([.r6, .r12] : List Reg) ++ prepRegs) := by decide

/-- After the steps for a valid domain. -/
structure VOut (s₀ : State) (t : State) : Prop where
  ctx : Ctx (glOf s₀) s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used
  r31 : t.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status
  out : (resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
    (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)

theorem valid_ok {s₀ t₂ : State} (h : gkContract.pre s₀) (ck : Chk s₀ t₂) (hchk : chkOf s₀ = true) :
    WP isa valid t₂ (VOut s₀) := by
  have hL := glOf_ok h
  have hql := hL.ql
  unfold valid
  refine WP.seq (WP.mono (prepareQ_ok h ck.ctx) fun t₃ ⟨sc, h0, m3, k3⟩ => ?_)
  have c25 : t₃.gpr .r25 = BitVec.ofNat 64 0 := (k3.gpr _ (by decide)).trans ck.r25
  refine WP.ite (decide (¬ 1 < qOf s₀)) (by rw [eval_zero]; exact congrArg some (by
    by_cases hq : 1 < qOf s₀
    · simp only [hq, not_true_eq_false, decide_false, beq_eq_false_iff_ne, ne_eq]; exact fun e => (h0.mp e) hq
    · simp only [hq, not_false_eq_true, decide_true, beq_iff_eq]; exact h0.mpr hq)) (fun hq => ?_) (fun hq => ?_)
  · -- q ≤ 1: no draw.
    simp only [decide_eq_true_eq] at hq
    have hd : drawOf s₀ = ⟨none, 0, [4]⟩ := by
      show Spec.Dsa.Random.sample (qOf s₀) (127 + 1) _ = _
      rw [Spec.Dsa.Random.sample, ite_eq_left (show qOf s₀ ≤ 1 by omega)]
    have hR : resOf s₀ = ⟨none, 0, 0, [4]⟩ := by simp only [resOf, hchk, hd]; rfl
    refine WP.mono (WP.keep (c := .block [.li .r31 0]) [.r31] (Q := fun t₄ => t₄.mem = t₃.mem ∧
      t₄.gpr .r31 = BitVec.ofNat 64 0) (by prun) (by decide)) fun t₄ ⟨⟨m4, a31⟩, k4⟩ => ?_
    refine ⟨sc.ctx.step hL k4.sp k4.rd k4.wr (fun r hr => k4.gpr r (ctx_31 r hr))
      (by rw [m4]; exact Frame.refl _ _), ?_, ?_, fun h1 => ?_⟩
    · rw [k4.gpr _ (by decide), c25, hR]
    · rw [a31, hR]
    · rw [hR] at h1; exact absurd h1 (by decide)
  · -- q > 1: the draw and the derivation.
    simp only [decide_eq_false_iff_not, Decidable.not_not] at hq
    have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
    have hQ := seOf_Q (L := glOf s₀) s₀.mem hq
    have hW : (eOf s₀).W ≤ (eOf s₀).ql := hE.Wq
    have hql' : (eOf s₀).ql ≤ 32 := hE.ql
    have hF := hL.fnw
    refine WP.seq (WP.mono (sample_ok hE hQ (sc.env h hq) c25 (Nat.zero_le _)) fun t₄ so => ?_)
    rw [List.drop_zero] at so
    have c₄ : Ctx (glOf s₀) s₀ t₄ := sc.ctx.step hL so.keep.sp so.keep.rd so.keep.wr
      (fun r hr => so.keep.gpr r (ctx_draw r hr))
      (outside_frame hL (o := (eOf s₀).ql - (eOf s₀).W) (n := (eOf s₀).W) (by omega) so.out)
    have nz : NZero s₀ t₄.mem := fun j hj => by
      have e : ofs (eOf s₀).F (off (glOf s₀).F (oNonce + j)) = oNonce + j :=
        Mont.ofs_off0 _ (by simp only [oNonce, frameBytes] at hF ⊢; omega)
      have hj' : oNonce + j < (eOf s₀).o := by
        have e2 : (eOf s₀).ql = (glOf s₀).ql := rfl
        simp only [SE.o]; omega
      rw [so.out _ (.inl (by rw [e]; exact hj')), m3]
      exact ck.nonce j (by omega)
    have r25 : t₄.gpr .r25 = BitVec.ofNat 64 (drawOf s₀).used := by rw [so.r25, Nat.zero_add]
    exact WP.mono (derive_wp h hq c₄ nz r25 so.r31 so.cand hchk) fun t₅ ⟨c, a, b, d⟩ => ⟨c, a, b, d⟩


theorem generate_correct (s₀ : State) (h : gkContract.pre s₀) :
    ∃ tr t, Exec isa Impl.Dsa.PPC64LE.Generate.code s₀ tr t ∧ abiPreserved s₀ t ∧ gkContract.post s₀ t := by
  show WP isa Impl.Dsa.PPC64LE.Generate.code s₀ fun t => abiPreserved s₀ t ∧ gkContract.post s₀ t
  have hL := glOf_ok h
  have hql := hL.ql
  have hfin : ∀ t, Ctx (glOf s₀) s₀ t → t.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used →
      t.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status →
      ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
        (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)) →
      WP isa (finish olen) t fun t' =>
        abiPreserved s₀ (freed frameBytes t') ∧ gkContract.post s₀ (freed frameBytes t') :=
    fun t hc h25 h31 hsig => WP.mono (finish_ok h hc h25 h31 (resOf_status s₀) hsig resOf_none) fun t' hf =>
      fin_post h (by rw [gkRes_eq h]; exact resOf_status s₀) (by rw [gkRes_eq h]; exact hf)
  unfold Impl.Dsa.PPC64LE.Generate.code
  refine WP.alloc (by decide) hL.spF ?_
  unfold Impl.Dsa.PPC64LE.Generate.body
  refine WP.seq (WP.mono (entry_ok h) fun t₁ he => ?_)
  refine WP.seq (WP.mono (checked_ok h he) fun t₂ ck => ?_)
  refine WP.seq (WP.ite (decide ((if chkOf s₀ then 1 else 0) = 0))
    (by rw [RS.eval_zero_w, RS.setWidth_beq_zero ck.r3]) (fun hc => ?_) (fun hc => ?_))
  · -- An invalid domain.
    have hchk : chkOf s₀ = false := by
      cases hc' : chkOf s₀ <;> simp_all
    have hR : resOf s₀ = ⟨none, 0, 0, [4]⟩ := by simp only [resOf, hchk]; rfl
    refine WP.mono (WP.keep (c := .block [.li .r31 0]) [.r31] (Q := fun t₃ => t₃.mem = t₂.mem ∧
      t₃.gpr .r31 = BitVec.ofNat 64 0) (by prun) (by decide)) fun t₃ ⟨⟨m3, a31⟩, k3⟩ => ?_
    refine hfin t₃ (ck.ctx.step hL k3.sp k3.rd k3.wr (fun r hr => k3.gpr r (ctx_31 r hr))
      (by rw [m3]; exact Frame.refl _ _)) ?_ ?_ fun h1 => ?_
    · rw [k3.gpr _ (by decide), ck.r25, hR]
    · rw [a31, hR]
    · rw [hR] at h1; exact absurd h1 (by decide)
  · -- A valid domain.
    have hchk : chkOf s₀ = true := by
      cases hc' : chkOf s₀ <;> simp_all
    exact WP.mono (valid_ok h ck hchk) fun t₄ v => hfin t₄ v.ctx v.r25 v.r31 v.out

end VG.Proof.Dsa.PPC64LE.GK
