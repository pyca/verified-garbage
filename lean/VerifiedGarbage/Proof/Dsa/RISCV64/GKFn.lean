module

public import VerifiedGarbage.Proof.Dsa.RISCV64.GKFinish
public import VerifiedGarbage.Proof.Dsa.RISCV64.GKDerive
public import VerifiedGarbage.Proof.Dsa.RISCV64.RndSample
public import VerifiedGarbage.Proof.Dsa.RandomResult
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.RSAttempt
import VerifiedGarbage.Proof.Dsa.RISCV64.RSSpec
import VerifiedGarbage.Proof.Dsa.RISCV64.RSFinish
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Spec.Dsa.Derive

/-!
# DSA key generation on RISC-V: the function

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Fn.lean`). `generate_correct`:
`vg_dsa_generate_key` meets `gkContract`. In its frame, the entry
(`entry_ok`), the check of the domain (`checked_ok`), then for a valid
domain the scan of q (`prepareQ_ok`), the sampling (`sample_ok`) and the
derivation (`derive_wp`), and the exit (`finish_ok`) follow one another;
the callees' results are zero-extended before they are tested; the result
is `generateKeyBytes`'s (`gkRes_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.Random (sampleStatus)
open VG.Proof.Dsa.RISCV64.RS (sub1_beq sampleStatus_some nonce_eq zx_beq_zero)

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
  have e7 : (s₀.gpr .a4).toNat = (glOf s₀).kl := hkl
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
  s5 : t.gpr .s5 = BitVec.ofNat 64 0
  nonce : ∀ j < 32, t.mem (off (glOf s₀).F (oNonce + j)) = 0
  a0 : ((t.gpr .a0).setWidth 32).toNat = if chkOf s₀ then 1 else 0

theorem checked_ok {s₀ t : State} (h : gkContract.pre s₀) (he : Entered (glOf s₀) s₀ t) :
    WP isa (.seq (.block checkArgs) (.call "vg_dsa_check_parameters" Impl.Dsa.RISCV64.Params.checkParameters)) t
      (Chk s₀) := by
  have hL := glOf_ok h
  refine WP.seq (WP.mono (checkArgs_ok hL rfl he.ctx) fun t₂ ⟨⟨ca, m2, k2⟩, _⟩ =>
    WP.mono (check_ok h ca) fun t₃ ck => ?_)
  refine ⟨ck.ctx, (ck.pres _ (by decide)).trans ((k2.1 _ (by decide)).trans he.s5), fun j hj => ?_, ck.a0⟩
  rw [frame_byte hL (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dFS) ck.frame
    (by simp only [oNonce, frameBytes]; omega), m2]
  exact he.nonce j hj

/-- The nonce's first `q_len − W` octets are zero. -/
abbrev NZero (s₀ : State) (m : Mem) : Prop :=
  ∀ j < (glOf s₀).ql - (eOf s₀).W, m (off (glOf s₀).F (oNonce + j)) = 0

/-- `s10 := 0`. -/
theorem li0_ok {s₀ t : State} (hL : (glOf s₀).Ok) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa (.block [.li .s10 0]) t fun t' =>
      Ctx (glOf s₀) s₀ t' ∧ t'.gpr .s10 = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .s10 → t'.gpr r = t.gpr r) ∧
        t'.mem = t.mem :=
  WP.mono (wp_sp (WP.keep (c := .block [.li .s10 0]) [.s10]
    (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .s10 = BitVec.ofNat 64 0) (by brun [exec_li_zero]; rfl) (by decide)
      (by rfl)))
    fun t' ⟨⟨⟨m', a'⟩, k⟩, sp'⟩ => ⟨hc.step hL sp' k.2.1 k.2.2 (fun r hr => k.1 r (by revert r hr; decide))
      (by rw [m']; exact Frame.refl _ _), a', fun r hr => k.1 r (by simp [hr]), m'⟩

/-- `s10 := 1`. -/
theorem li1_ok {s₀ t : State} (hL : (glOf s₀).Ok) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa (.block [.li .s10 1]) t fun t' =>
      Ctx (glOf s₀) s₀ t' ∧ t'.gpr .s10 = BitVec.ofNat 64 1 ∧ (∀ r, r ≠ .s10 → t'.gpr r = t.gpr r) ∧
        t'.mem = t.mem :=
  WP.mono (wp_sp (WP.keep (c := .block [.li .s10 1]) [.s10]
    (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .s10 = BitVec.ofNat 64 1)
      (by brun [exec_li_lit (show 1 < 2048 by decide)]) (by decide) (by rfl)))
    fun t' ⟨⟨⟨m', a'⟩, k⟩, sp'⟩ => ⟨hc.step hL sp' k.2.1 k.2.2 (fun r hr => k.1 r (by revert r hr; decide))
      (by rw [m']; exact Frame.refl _ _), a', fun r hr => k.1 r (by simp [hr]), m'⟩

/-- `zx`: the low word of `a0`, zero-extended. -/
theorem zx_ok {s₀ t : State} (hL : (glOf s₀).Ok) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa (.block zx) t fun t' =>
      Ctx (glOf s₀) s₀ t' ∧ t'.gpr .a0 = (t.gpr .a0 <<< 32) >>> 32 ∧ t'.mem = t.mem ∧
        ∀ r, r ≠ .a0 → t'.gpr r = t.gpr r :=
  WP.mono (wp_sp (WP.keep (c := .block zx) [.a0]
    (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .a0 = (t.gpr .a0 <<< 32) >>> 32) (by brun [zx]) (by decide)
      (by rfl)))
    fun t' ⟨⟨⟨m', a'⟩, k⟩, sp'⟩ => ⟨hc.step hL sp' k.2.1 k.2.2 (fun r hr => k.1 r (by revert r hr; decide))
      (by rw [m']; exact Frame.refl _ _), a', m', fun r hr => k.1 r (by simp [hr])⟩

/-- The derivation, from the sampler's result. -/
theorem derive_wp {s₀ t : State} (h : gkContract.pre s₀) (hq : 1 < qOf s₀) (hc : Ctx (glOf s₀) s₀ t)
    (hz : NZero s₀ t.mem) (h5 : t.gpr .s5 = BitVec.ofNat 64 (drawOf s₀).used)
    (h10 : t.gpr .s10 = BitVec.ofNat 64 (sampleStatus (drawOf s₀)))
    (hk : ∀ x, (drawOf s₀).scalar = some x → Spec.Dsa.decodeBE (cands (eOf s₀) t.mem) = x)
    (hchk : chkOf s₀ = true) :
    WP isa Impl.Dsa.RISCV64.Generate.derive t fun t' =>
      Ctx (glOf s₀) s₀ t' ∧ t'.gpr .s5 = BitVec.ofNat 64 (resOf s₀).used ∧
        t'.gpr .s10 = BitVec.ofNat 64 (resOf s₀).status ∧
        ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t'.mem (glOf s₀).out (glOf s₀).ol =
          (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)) := by
  have hL := glOf_ok h
  have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have hst := sampleStatus_le (drawOf s₀)
  unfold Impl.Dsa.RISCV64.Generate.derive
  refine WP.seq (WP.mono (wp_sp (WP.keep [.a0] (Q := fun t₂ => t₂.mem = t.mem ∧
    t₂.gpr .a0 = t.gpr .s10 - BitVec.ofNat 64 1) (by brun) (by decide) (by rfl)))
    fun t₂ ⟨⟨⟨m2, a0⟩, k2⟩, sp2⟩ => ?_)
  have c₂ : Ctx (glOf s₀) s₀ t₂ :=
    hc.step hL sp2 k2.2.1 k2.2.2 (fun r hr => k2.1 r (by revert r hr; decide)) (by rw [m2]; exact Frame.refl _ _)
  have b5 : t₂.gpr .s5 = BitVec.ofNat 64 (drawOf s₀).used := (k2.1 _ (by decide)).trans h5
  refine WP.ite (decide (sampleStatus (drawOf s₀) = 1))
    (by rw [Steps.eval_zero, a0, h10, sub1_beq _ (by omega)]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp hs)
    have hR : resOf s₀ = ⟨dkOf s₀ x, Spec.Dsa.signStatus (dkOf s₀ x), (drawOf s₀).used,
        (drawOf s₀).trace ++ [if (dkOf s₀ x).isSome then 5 else 6]⟩ := by
      simp only [resOf, hchk, ite_true, hx]
    have hnonce : Spec.Rsa.bytesAt t₂.mem (off (glOf s₀).F oNonce) (glOf s₀).ql =
        Spec.Dsa.encodeBE (glOf s₀).ql x := by
      rw [m2]
      exact nonce_eq (W := (eOf s₀).W) hE.Wq hz (hk x hx)
    refine WP.seq (WP.mono (deriveArgs_ok hL rfl c₂) fun t₃ ⟨⟨da, m3, k3⟩, _⟩ => ?_)
    refine WP.seq (WP.mono (derive_ok h da) fun t₄ dv => ?_)
    have es : dresOf (glOf s₀) t₃.mem = dkOf s₀ x := by
      simp only [dresOf, dkOf, parOf]; rw [m3, c₂.par, hnonce]
    have hr0 := dv.a0
    rw [es] at hr0
    have b5' : t₄.gpr .s5 = BitVec.ofNat 64 (drawOf s₀).used :=
      (dv.pres _ (by decide)).trans ((k3.1 _ (by decide)).trans b5)
    unfold deriveFinish
    refine WP.seq (WP.mono (zx_ok hL dv.ctx) fun t₅ ⟨c₅, z5, m5, g5⟩ => ?_)
    refine WP.ite (decide (Spec.Dsa.signStatus (dkOf s₀ x) = 0))
      (by rw [Steps.eval_zero, z5, zx_beq_zero hr0]) (fun hz' => ?_) (fun hz' => ?_)
    · simp only [decide_eq_true_eq] at hz'
      refine WP.mono (li0_ok hL c₅) fun t₆ ⟨c₆, a10, g6, m6⟩ => ⟨c₆, ?_, ?_, fun _ => ?_⟩
      · rw [g6 _ (by decide), g5 _ (by decide), b5', hR]
      · rw [a10, hR]; dsimp only; rw [hz']
      · rw [m6, m5, dv.out, es, hR]
    · simp only [decide_eq_false_iff_not] at hz'
      refine WP.mono (li1_ok hL c₅) fun t₆ ⟨c₆, a10, g6, m6⟩ => ⟨c₆, ?_, ?_, fun _ => ?_⟩
      · rw [g6 _ (by decide), g5 _ (by decide), b5', hR]
      · rw [a10, hR]; dsimp only
        unfold Spec.Dsa.signStatus at hz' ⊢
        split at hz' <;> simp_all
      · rw [m6, m5, dv.out, es, hR]
  · simp only [decide_eq_false_iff_not] at hs
    have hx : (drawOf s₀).scalar = none := by
      cases hc' : (drawOf s₀).scalar with
      | none => rfl
      | some k => exact absurd (sampleStatus_some.mpr (by rw [hc']; rfl)) hs
    have hR : resOf s₀ = ⟨none, if (drawOf s₀).trace.getLast? == some 2 then 2 else 0, (drawOf s₀).used,
        (drawOf s₀).trace⟩ := by
      simp only [resOf, hchk, ite_true, hx]
    refine WP.block_nil ⟨c₂, by rw [b5, hR], ?_, fun h1 => ?_⟩
    · rw [(k2.1 _ (by decide)).trans h10, hR]
      simp only [sampleStatus, hx]
    · rw [hR] at h1 ⊢
      exact absurd h1 (by dsimp only; split <;> decide)

/-- After the steps for a valid domain. -/
structure VOut (s₀ : State) (t : State) : Prop where
  ctx : Ctx (glOf s₀) s₀ t
  s5 : t.gpr .s5 = BitVec.ofNat 64 (resOf s₀).used
  s10 : t.gpr .s10 = BitVec.ofNat 64 (resOf s₀).status
  out : (resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
    (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)

theorem valid_ok {s₀ t₂ : State} (h : gkContract.pre s₀) (ck : Chk s₀ t₂) (hchk : chkOf s₀ = true) :
    WP isa valid t₂ (VOut s₀) := by
  have hL := glOf_ok h
  have hql := hL.ql
  unfold valid
  refine WP.seq (WP.mono (prepareQ_ok h ck.ctx) fun t₃ ⟨⟨sc, h0, m3, k3⟩, _⟩ => ?_)
  have c5 : t₃.gpr .s5 = BitVec.ofNat 64 0 := (k3.1 _ (by decide)).trans ck.s5
  refine WP.ite (decide (¬ 1 < qOf s₀)) (by rw [Steps.eval_zero]; exact congrArg some (by
    by_cases hq : 1 < qOf s₀
    · simp only [hq, not_true_eq_false, decide_false, beq_eq_false_iff_ne, ne_eq]; exact fun e => (h0.mp e) hq
    · simp only [hq, not_false_eq_true, decide_true, beq_iff_eq]; exact h0.mpr hq)) (fun hq => ?_) (fun hq => ?_)
  · -- q ≤ 1: no draw.
    simp only [decide_eq_true_eq] at hq
    have hd : drawOf s₀ = ⟨none, 0, [4]⟩ := by
      show Spec.Dsa.Random.sample (qOf s₀) (127 + 1) _ = _
      rw [Spec.Dsa.Random.sample, ite_eq_left (show qOf s₀ ≤ 1 by omega)]
    have hR : resOf s₀ = ⟨none, 0, 0, [4]⟩ := by simp only [resOf, hchk, hd]; rfl
    refine WP.mono (li0_ok hL sc.ctx) fun t₄ ⟨c₄, a10, g4, _⟩ => ⟨c₄, ?_, ?_, fun h1 => ?_⟩
    · rw [g4 _ (by decide), c5, hR]
    · rw [a10, hR]
    · rw [hR] at h1; exact absurd h1 (by decide)
  · -- q > 1: the draw and the derivation.
    simp only [decide_eq_false_iff_not, Decidable.not_not] at hq
    have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
    have hQ := seOf_Q (L := glOf s₀) s₀.mem hq
    have hW : (eOf s₀).W ≤ (eOf s₀).ql := hE.Wq
    have hql' : (eOf s₀).ql ≤ 32 := hE.ql
    have hF := hL.fnw
    refine WP.seq (WP.mono (sample_ok hE hQ (sc.env h hq) c5 (Nat.zero_le _)) fun t₄ so => ?_)
    rw [List.drop_zero] at so
    have c₄ : Ctx (glOf s₀) s₀ t₄ := sc.ctx.step hL (so.env.sp.trans sc.ctx.sp.symm) so.keep.2.1 so.keep.2.2
      (fun r hr => so.keep.1 r (by revert r hr; decide))
      (outside_frame hL (o := (eOf s₀).ql - (eOf s₀).W) (n := (eOf s₀).W) (by omega) so.out)
    have nz : NZero s₀ t₄.mem := fun j hj => by
      have e : ofs (eOf s₀).F (off (glOf s₀).F (oNonce + j)) = oNonce + j :=
        Mont.ofs_off0 _ (by simp only [oNonce, frameBytes] at hF ⊢; omega)
      have hj' : oNonce + j < (eOf s₀).o := by
        have e2 : (eOf s₀).ql = (glOf s₀).ql := rfl
        simp only [SE.o]; omega
      rw [so.out _ (.inl (by rw [e]; exact hj')), m3]
      exact ck.nonce j (by omega)
    have r5 : t₄.gpr .s5 = BitVec.ofNat 64 (drawOf s₀).used := by rw [so.s5, Nat.zero_add]
    exact WP.mono (derive_wp h hq c₄ nz r5 so.s10 so.cand hchk) fun t₅ ⟨c, a, b, d⟩ => ⟨c, a, b, d⟩

theorem generate_correct (s₀ : State) (h : gkContract.pre s₀) :
    ∃ tr t, Exec isa Impl.Dsa.RISCV64.Generate.code s₀ tr t ∧ abiPreserved s₀ t ∧ gkContract.post s₀ t := by
  show WP isa Impl.Dsa.RISCV64.Generate.code s₀ fun t => abiPreserved s₀ t ∧ gkContract.post s₀ t
  have hL := glOf_ok h
  have hql := hL.ql
  have hfin : ∀ t, Ctx (glOf s₀) s₀ t → t.gpr .s5 = BitVec.ofNat 64 (resOf s₀).used →
      t.gpr .s10 = BitVec.ofNat 64 (resOf s₀).status →
      ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
        (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)) →
      WP isa (finish outLen) t fun t' =>
        abiPreserved s₀ (freed frameBytes t') ∧ gkContract.post s₀ (freed frameBytes t') :=
    fun t hc h5 h10 hsig => WP.mono (finish_ok h hc h5 h10 (resOf_status s₀) hsig resOf_none) fun t' hf =>
      fin_post h (by rw [gkRes_eq h]; exact resOf_status s₀) (by rw [gkRes_eq h]; exact hf)
  unfold Impl.Dsa.RISCV64.Generate.code
  refine WP.alloc (by decide) hL.spF ?_
  unfold Impl.Dsa.RISCV64.Generate.body
  refine WP.seq (WP.mono (entry_ok h) fun t₁ he => ?_)
  refine WP.seq (WP.mono (checked_ok h he) fun t₂ ck => ?_)
  refine WP.seq (WP.seq (WP.mono (zx_ok hL ck.ctx) fun t₃ ⟨c₃, z3, m3, g3⟩ => ?_))
  refine WP.ite (decide ((if chkOf s₀ then 1 else 0) = 0))
    (by rw [Steps.eval_zero, z3, zx_beq_zero ck.a0]) (fun hc => ?_) (fun hc => ?_)
  · -- An invalid domain.
    have hchk : chkOf s₀ = false := by
      cases hc' : chkOf s₀ <;> simp_all
    have hR : resOf s₀ = ⟨none, 0, 0, [4]⟩ := by simp only [resOf, hchk]; rfl
    refine WP.mono (li0_ok hL c₃) fun t₄ ⟨c₄, a10, g4, _⟩ => ?_
    refine hfin t₄ c₄ ?_ ?_ fun h1 => ?_
    · rw [g4 _ (by decide), g3 _ (by decide), ck.s5, hR]
    · rw [a10, hR]
    · rw [hR] at h1; exact absurd h1 (by decide)
  · -- A valid domain.
    have hchk : chkOf s₀ = true := by
      cases hc' : chkOf s₀ <;> simp_all
    have ck₃ : Chk s₀ t₃ := ⟨c₃, by rw [g3 _ (by decide)]; exact ck.s5,
      fun j hj => by rw [m3]; exact ck.nonce j hj, by
      rw [z3, BitVec.toNat_setWidth, RS.zx_toNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; exact ck.a0⟩
    exact WP.mono (valid_ok h ck₃ hchk) fun t₄ v => hfin t₄ v.ctx v.s5 v.s10 v.out

end VG.Proof.Dsa.RISCV64.GK
