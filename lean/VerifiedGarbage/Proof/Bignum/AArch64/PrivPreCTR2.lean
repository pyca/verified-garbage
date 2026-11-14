module
-- separate module: the precomputation's constant-time proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.AArch64.PrivPreR2
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.PrivPreR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_private_precompute` on AArch64: `r2X` is constant time

`r2X` in a prime's workspace (`r2X_ct`): every count it runs (the chunks,
the further reductions, the doublings, whether it squares) is a function of
`w` and `w_X`, which both runs share; its multiplications and additions are
constant time for any modulus. Each part is checked by the taint analysis or
by `M.ct`, and what each run satisfies between them follows from
correctness (`PrivPreR2.lean`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.PrivPre

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.PrivPre
open VG.Impl.Bignum.Crt (aXc aChunk aT sLink sSrc sRem)
open VG.Impl.Rsa.AArch64.Crt (copyArr addMod ldw redc)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)
open VG.Proof.Bignum.AArch64 (eval_nz_count)

/-! ## `redc` of `R² mod n`, and `e₀` -/

/-- After `redc`, or a part of the further steps: the prime's workspace. -/
def Q1 (p : XPub) (t : State) : Prop := ∃ minv, SubCtx t p.B p.Z p.o p.w p.wx minv ∧ XF p

/-- After the load of `n`'s base. -/
def Q2 (p : XPub) (t : State) : Prop := Q1 p t ∧ t.gpr .x5 = p.B

/-- The loop `x3 += w_X`'s public data. -/
def gpOf (p : XPub) : GPub := ⟨off p.B p.o, 0, p.w, 0, 0, 0, p.wx⟩

theorem q2_ok {p : XPub} {t : State} (h : Q1 p t) : WP isa (.block [ldh .x5 sLink]) t (Q2 p) := by
  obtain ⟨minv, hc, hf⟩ := h
  exact WP.mono (WP.keep [.x5] (Q := fun t' => t'.gpr .x5 = p.B ∧ t'.mem = t.mem)
    (by brun [hc.x0, hdr_enc (show sLink < 32 by decide), hc.ld' (show sLink < 32 by decide), hc.link'])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h5, hm⟩, k⟩ =>
      ⟨⟨minv, hc.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k.wr (k.gpr .x0 (by decide)), hf⟩, h5⟩

theorem kl_ok {p : XPub} {t : State} (h : Q2 p t) :
    WP isa (.block [ldw .x12 .x5 sW, ldh .x5 sW, movi .x3 0, movi .x7 0, movi .x8 1]) t fun t' =>
      0 < nChunks (gpOf p).w (gpOf p).wx ∧ KL (gpOf p) 0 t' := by
  obtain ⟨⟨minv, hc, hw2, hwx, hw30⟩, h5⟩ := h
  have hK : 0 < nChunks p.w p.wx := (lt_chunks (k := 0) (by omega_using [hw2])).mpr (by omega_using [hw2, hwx])
  refine WP.mono (WP.keep [.x3, .x5, .x7, .x8, .x12] (Q := fun t' => t'.gpr .x5 = BitVec.ofNat 64 p.wx ∧
      t'.gpr .x12 = BitVec.ofNat 64 p.w ∧ t'.gpr .x3 = BitVec.ofNat 64 0 ∧ t'.gpr .x7 = 0 ∧ t'.gpr .x8 = 1)
    (by brun [ldw, hc.x0, h5, hdr_enc (show sW < 32 by decide), hc.ldn (show sW < 32 by decide), hc.nw,
      hc.ld' (show sW < 32 by decide), hc.hw'])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h5', h12, h3, h7, h8⟩, k⟩ =>
      ⟨hK, (k.gpr .x0 (by decide)).trans hc.x0, by rw [h3, Nat.zero_mul], h5', h12, h7, h8, show 1 ≤ p.wx by omega_using [hw2], hwx, hw30⟩

/-- `redc` of `R² mod n`, `r2Load`, the loop `x3 += w_X` and `eInit`. -/
theorem r2A_ct (M : Mont) :
    RelCT isa (Two (RPre aR2)) (seqs (redc M.mm aR2 ++ ([.block r2Load, kLoop, .block eInit] : List (Prog isa)))) fun _ _ => True := by
  refine RelCT.seqs_append (by simp [redc]) (by simp) (RelCT.seq (two_post (Ψ := Q1) (redc_ct_of M (by taint_decide))
    fun p s ⟨minv, X, hc, hv, hw2, hwx, hw30, hX1, _⟩ => WP.mono (redc_ok M hc hv hw2 hwx hw30 hX1 (by decide))
      fun t ⟨hc', _⟩ => ⟨minv, hc', hw2, hwx, hw30⟩) ?_)
  simp only [seqs]
  refine RelCT.seq (RelCT.block_append (l₁ := [ldh .x5 sLink]) (RelCT.seq (two_piece (Ψ := Q2) [.x0]
    (pins_subCtx id fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc⟩) (by taint_decide) fun _ _ h => q2_ok h)
    (two_piece (Ψ := fun p t => 0 < nChunks (gpOf p).w (gpOf p).wx ∧ KL (gpOf p) 0 t) [.x0, .x5]
      (pins_of (fun p r => if r = .x0 then off p.B p.o else p.B) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        obtain ⟨⟨_, hc, _⟩, h5⟩ := h
        rcases hr with rfl | rfl
        · exact hc.x0
        · exact h5) (by taint_decide) fun _ _ h => kl_ok h))) ?_
  exact RelCT.seq (two_map gpOf (fun _ _ h => h) kLoop_ct)
    (two_taint [.x0] (pins_x0B (fun g : GPub => g.B) fun _ _ h => h) (by taint_decide))

/-! ## The further reductions -/

/-- After `j` further reductions. -/
def ZΦ (p : XPub) (j : Nat) (t : State) : Prop :=
  ∃ (s₀ : State) (minv : BitVec 64) (X x : Nat), RzInv s₀ p.B p.Z p.o p.w p.wx minv X x j t ∧ XF p ∧ 1 < X

/-- After `eInit`. -/
def ZA (p : XPub) (t : State) : Prop := ZΦ p 0 t ∧ t.gpr .x4 = if r2E0 p.w p.wx ≤ 2 * p.wx then 0 else 1

theorem zBody_ct (M : Mont) :
    RelCT isa (Two fun (q : XPub × Nat) s => q.2 < r2Z q.1.w q.1.wx ∧ ZΦ q.1 q.2 s) (zBody M.mm) fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := fun q t => Q1 q.1 t) (two_map (fun q : XPub × Nat => q.1.ws)
    (fun _ _ ⟨_, _, minv, _, _, hI, _⟩ => ⟨minv, hI.ctx.good, Nat.le_refl _⟩) (M.ct (by unfold MmUse; decide)))
    fun q s ⟨_, _, minv, X, _, hI, hf, hX1⟩ => ?_)
    (two_taint [.x0] (pins_subCtx (·.1) fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc⟩) (by taint_decide))
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  exact WP.mono (mmOne_ok M hI.ctx hI.xv hw2 (by omega_using [hwx, hw30]) hX1 (d := aXc) (a := aXc) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [redcRanges])) fun t ⟨hc, _⟩ => ⟨minv, hc, hf⟩

theorem zLoop_ct (M : Mont) : RelCT isa (Two ZA) (zLoop M.mm) (Two fun p t => ZΦ p (r2Z p.w p.wx) t) := by
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2]) ?_ ?_
  · refine (two_loop (Φ := ZΦ) (fun p => r2Z p.w p.wx) (zBody_ct M) fun p j s hj ⟨s₀, minv, X, x, hI, hf, hX1⟩ => ?_).mono
      (fun _ _ h => two_mono (fun p s ⟨⟨hZ, h4⟩, hb⟩ => ⟨?_, hZ⟩) h) fun _ _ h => h
    · obtain ⟨hw2, hwx, hw30⟩ := id hf
      exact WP.mono (rzStep_ok M hw2 hwx hw30 hX1 hj hI) fun s' ⟨hI', hz⟩ =>
        ⟨eval_nz_count hj hz, fun _ => ⟨s₀, minv, X, x, hI', hf, hX1⟩, fun he => he ▸ ⟨s₀, minv, X, x, hI', hf, hX1⟩⟩
    · obtain ⟨_, _, _, _, _, ⟨hw2, _, _⟩, _⟩ := hZ
      refine (r2Z_pos (by omega_using [hw2])).mpr ?_
      by_contra hc
      rw [eval_nonzero, h4, ite_eq_left_iff.mpr (fun h => absurd (by omega_using [hc]) h)] at hb
      exact absurd hb (by decide)
  · refine RelCT.block_nil fun s₁ s₂ ⟨p, ⟨⟨hZ₁, h4₁⟩, hb₁⟩, ⟨⟨hZ₂, _⟩, _⟩, hsp⟩ => ⟨p, ?_, ?_, hsp⟩
    all_goals
      have h0 : r2Z p.w p.wx = 0 := by
        obtain ⟨_, _, _, _, _, ⟨hw2, _, _⟩, _⟩ := hZ₁
        have := r2Z_pos (w := p.w) (wx := p.wx) (by omega_using [hw2])
        by_contra hc
        rw [eval_nonzero, h4₁, ite_eq_right_iff.mpr (fun h => absurd h (by omega))] at hb₁
        exact absurd hb₁ (by decide)
      show ZΦ p (r2Z p.w p.wx) _
      rw [h0]
    · exact hZ₁
    · exact hZ₂

/-! ## `Y := A`, the counts and the doublings -/

/-- Whether six squarings follow. -/
abbrev flag (p : XPub) : BitVec 64 := if r2E p.w p.wx ≤ p.wx then (1 : BitVec 64) else 0#64

/-- After `j` doublings. -/
def DΦ (p : XPub) (j : Nat) (t : State) : Prop :=
  ∃ (s₀ : State) (minv : BitVec 64) (X A : Nat), DInv s₀ p.B p.Z p.o p.w p.wx minv (flag p) X A (r2C p.w p.wx) j t ∧
    XF p ∧ 1 < X

/-- After the counts. -/
def DA (p : XPub) (t : State) : Prop := DΦ p 0 t ∧ t.gpr .x3 = BitVec.ofNat 64 (r2C p.w p.wx)

theorem r2B_ct :
    RelCT isa (Two fun p t => ZΦ p (r2Z p.w p.wx) t) (seqs (copyArr aY aXc ++ ([.block cntBlk] : List (Prog isa)))) (Two DA) := by
  refine two_post (RelCT.seqs_append (by simp [copyArr]) (by simp) (RelCT.seq (two_post (Ψ := Q1)
    (two_map XPub.ws (fun _ _ ⟨_, minv, _, _, hI, _⟩ => ⟨minv, hI.ctx.good, Nat.le_refl _⟩)
      (copyArr_ct (by decide) (by decide) (by taint_decide))) fun p s ⟨_, minv, _, _, hI, hf, _⟩ => ?_)
    (two_taint [.x0] (pins_subCtx id fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc⟩) (by taint_decide))))
    fun p s ⟨s₀, minv, X, x, hI, hf, hX1⟩ => ?_
  · obtain ⟨hw2, hwx, hw30⟩ := id hf
    refine WP.mono (copyArr_ok hI.ctx.good (Nat.le_refl _) (by omega_using [hw2]) (by omega_using [hwx, hw30]) (o := aY) (a := aXc) (by decide)
      (by decide) (by decide)) fun t ⟨_, ho, k⟩ => ⟨minv, hI.ctx.of_frm
        (Frm.of_outside (ho.mono (o' := slot p.wx aY) (n' := 8 * (p.wx + 2)) (Nat.le_refl _) (by omega_using []))
          (by simp [r2Ranges])) (r2Ranges_ok p.wx) k.wr (k.gpr .x0 (by decide)), hf⟩
  · obtain ⟨hw2, hwx, hw30⟩ := id hf
    exact WP.mono (r2B_ok hw2 hwx hw30 hI) fun t ⟨hD, h3⟩ => ⟨⟨s₀, minv, X, _, hD, hf, hX1⟩, h3⟩

theorem r2Body_ct :
    RelCT isa (Two fun (q : XPub × Nat) s => q.2 < r2C q.1.w q.1.wx ∧ DΦ q.1 q.2 s) r2Body fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := fun q t => t.gpr .x0 = off q.1.B q.1.o) (two_map (fun q : XPub × Nat => q.1.ws)
    (fun _ _ ⟨_, _, minv, _, _, hI, _⟩ => ⟨minv, hI.ctx.good, Nat.le_refl _⟩)
    (addMod_ct (by decide) (by decide) (by decide) (by taint_decide))) fun q s ⟨hj, _, minv, X, A, hI, hf, hX1⟩ => ?_)
    (two_taint [.x0] (pins_x0B (fun q : XPub × Nat => off q.1.B q.1.o) fun _ _ h => h) (by taint_decide))
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hg := hI.ctx.good
  have hylt : wv s.mem (off q.1.B q.1.o) (slot q.1.wx aY) q.1.wx < wv s.mem (off q.1.B q.1.o) (slot q.1.wx aN) q.1.wx := by
    rw [hI.y, hI.xv.n]; exact Nat.mod_lt _ (by omega_using [hX1])
  exact WP.mono (addMod_ok hg.scr hg.x0 hg.hdr (Nat.le_refl _) hw2 (by omega_using [hwx, hw30]) (o := aY) (a := aY) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hylt hylt)
    fun t ⟨_, _, k⟩ => (k.gpr .x0 (by decide)).trans hg.x0

theorem dLoop_ct : RelCT isa (Two DA) dLoop (Two fun p t => DΦ p (r2C p.w p.wx) t) := by
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2]) ?_ ?_
  · refine (two_loop (Φ := DΦ) (fun p => r2C p.w p.wx) r2Body_ct fun p j s hj ⟨s₀, minv, X, A, hI, hf, hX1⟩ => ?_).mono
      (fun _ _ h => two_mono (fun p s ⟨⟨hD, h3⟩, hb⟩ => ⟨?_, hD⟩) h) fun _ _ h => h
    · obtain ⟨hw2, hwx, hw30⟩ := id hf
      have hC := r2C_le (w := p.w) (wx := p.wx) (by omega_using [hw2]) hwx
      exact WP.mono (dStep_ok hw2 (by omega_using [hwx, hw30]) hX1 (by omega_using [hwx, hw30, hC]) hj hI) fun s' ⟨hI', hz⟩ =>
        ⟨eval_nz_count hj hz, fun _ => ⟨s₀, minv, X, A, hI', hf, hX1⟩, fun he => he ▸ ⟨s₀, minv, X, A, hI', hf, hX1⟩⟩
    · obtain ⟨_, _, _, _, _, ⟨hw2, hwx, hw30⟩, _⟩ := hD
      have hC := r2C_le (w := p.w) (wx := p.wx) (by omega_using [hw2]) hwx
      rw [eval_nz_ofNat' h3 (by omega_using [hwx, hw30, hC])] at hb
      by_contra hc
      exact absurd hb (by simp only [Option.some.injEq, decide_eq_true_eq]; omega)
  · refine RelCT.block_nil fun s₁ s₂ ⟨p, ⟨⟨hD₁, h3₁⟩, hb₁⟩, ⟨⟨hD₂, _⟩, _⟩, hsp⟩ => ⟨p, ?_, ?_, hsp⟩
    all_goals
      have h0 : r2C p.w p.wx = 0 := by
        obtain ⟨_, _, _, _, _, ⟨hw2, hwx, hw30⟩, _⟩ := hD₁
        have hC := r2C_le (w := p.w) (wx := p.wx) (by omega_using [hw2]) hwx
        rw [eval_nz_ofNat' h3₁ (by omega_using [hwx, hw30, hC])] at hb₁
        by_contra hc
        exact absurd hb₁ (by simp only [Option.some.injEq, decide_eq_false_iff_not, Classical.not_not]; exact hc)
      show DΦ p (r2C p.w p.wx) _
      rw [h0]
    · exact hD₁
    · exact hD₂

/-! ## The squarings -/

/-- Between the squarings. -/
def SΦ (p : XPub) (t : State) : Prop :=
  ∃ (s₀ : State) (minv : BitVec 64) (X e : Nat), SInv s₀ p.B p.Z p.o p.w p.wx minv X False e t ∧ XF p ∧ 1 < X

/-- After the flag's load. -/
def SA (p : XPub) (t : State) : Prop := SΦ p t ∧ t.gpr .x3 = flag p

theorem sa_ok {p : XPub} {t : State} (h : DΦ p (r2C p.w p.wx) t) : WP isa (.block [ldh .x3 Crt.sV]) t (SA p) := by
  obtain ⟨s₀, minv, X, A, hD, hf, hX1⟩ := h
  have hfl : word t.mem p.B (p.o + 8 * Crt.sV) = flag p := by rw [← word_off]; exact hD.sv
  refine WP.mono (WP.keep [.x3] (Q := fun u => u.gpr .x3 = flag p ∧ u.mem = t.mem)
    (by brun [hD.ctx.x0, hdr_enc (show Crt.sV < 32 by decide), hD.ctx.ld' (show Crt.sV < 32 by decide), hfl])
    (by decide) (by decide) (by decide +kernel)) fun u ⟨⟨h3, hm⟩, k⟩ => ⟨⟨s₀, minv, X, 0, ⟨?_, ?_, ?_, fun h => h.elim,
      by rw [hm]; exact hD.frm, (hD.keep.trans k).mono (by decide)⟩, hf, hX1⟩, h3⟩
  · exact hD.ctx.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k.wr (k.gpr .x0 (by decide))
  · exact ⟨by rw [hm]; exact hD.xv.n, by rw [hm]; exact hD.xv.inv, by rw [hm]; exact hD.xv.one⟩
  · rw [hm, hD.y]; exact Nat.mod_lt _ (by omega_using [hX1])

theorem sq_ct (M : Mont) : RelCT isa (Two SΦ) (M.mm aY aY aY) (Two SΦ) :=
  two_post (two_map XPub.ws (fun _ _ ⟨_, minv, _, _, hI, _⟩ => ⟨minv, hI.ctx.good, Nat.le_refl _⟩)
    (M.ct (by unfold MmUse; decide))) fun p s ⟨s₀, minv, X, e, hI, hf, hX1⟩ => by
      obtain ⟨hw2, hwx, hw30⟩ := id hf
      exact WP.mono (sqStep_ok M hw2 (by omega_using [hwx, hw30]) (fun h => h.elim) hI) fun t h => ⟨s₀, minv, X, _, h, hf, hX1⟩

theorem r2Tail_ct (M : Mont) :
    RelCT isa (Two fun p t => DΦ p (r2C p.w p.wx) t) (seqs [.block [ldh .x3 Crt.sV], sq6 M.mm]) fun _ _ => True := by
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := SA) [.x0] (pins_subCtx id fun _ _ ⟨_, minv, _, _, hD, _⟩ => ⟨minv, hD.ctx⟩)
    (by taint_decide) fun _ _ h => sa_ok h) ?_
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2]) ?_
    (RelCT.block_nil fun _ _ _ => trivial)
  have h := sq_ct M
  have hm : ∀ {c : Prog isa}, RelCT isa (Two SΦ) c (Two SΦ) →
      RelCT isa (Two fun p s => SA p s ∧ isa.eval (.nonzero .x .x3) s = some true) c (Two SΦ) := fun hc =>
    two_map id (fun _ _ h => h.1.1) hc
  exact RelCT.seq (hm h) (RelCT.seq h (RelCT.seq h (RelCT.seq h (RelCT.seq h (h.mono (fun _ _ h => h)
    fun _ _ _ => trivial)))))

/-! ## `r2X` -/

theorem r2X_ct (M : Mont) : RelCT isa (Two (RPre aR2)) (seqs (r2X M.mm)) fun _ _ => True := by
  rw [r2X_eq]
  refine RelCT.seqs_append (by simp [redc]) (by simp) (RelCT.seq (two_post (Ψ := ZA) (r2A_ct M)
    fun p s ⟨minv, X, hc, hv, hw2, hwx, hw30, hX1, _⟩ => WP.mono (r2A_ok M hc hv hw2 hwx hw30 hX1)
      fun t ⟨hI, h4⟩ => ⟨⟨s, minv, X, _, hI, ⟨hw2, hwx, hw30⟩, hX1⟩, h4⟩) ?_)
  refine RelCT.seqs_append (by simp) (by simp [copyArr]) (RelCT.seq (zLoop_ct M) ?_)
  refine RelCT.seqs_append (by simp [copyArr]) (by simp) (RelCT.seq r2B_ct ?_)
  exact RelCT.seqs_append (by simp) (by simp) (RelCT.seq dLoop_ct (r2Tail_ct M))

end VG.Proof.Bignum.AArch64.PrivPre
