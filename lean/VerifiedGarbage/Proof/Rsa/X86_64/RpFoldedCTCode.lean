module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT8
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTFin
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCode
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT2
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT7
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCode
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT2
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT5
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedMain
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
public import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Rsa.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1

/-! # Folded prime recovery preserves the public leakage contract -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Spec.Rsa (recoverPrimes)

open VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open Rp

theorem rpMain_ct [InvLaw] (M : Mont) : RelCT isa (Two GM) (Folded.main M.mm) fun _ _ => True := by
  rw [rpMain_eq']
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (R := Two GMP) (two_post (prefix_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)
    fun p s ⟨I, e, h, hv⟩ => WP.mono (rpPrefix_ok h hv) fun t ⟨S, hz, vM, vN, hi, hDE⟩ =>
      ⟨s, I, e, h, hv, S, hz, vM, vN, hi, hDE⟩) ?_)
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [gmp_eval h₁, gmp_eval h₂]) ?_ ?_
  · refine failR_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨σ, I, e, hp, hv, S, _⟩, _⟩ =>
      ⟨I, e, S.ws.scr, S.ws.rdi, S.args, S.wr, hp.L, hp.outs⟩) h) fun _ _ h => h
  · refine (rest_ct M).mono (fun _ _ h => two_mono (fun p t ⟨h, hf⟩ => ?_) h) fun _ _ h => h
    have hev := gmp_eval h
    obtain ⟨σ, I, rfl, hp, hv, S, hz, vM, vN, hi, hDE⟩ := h
    rw [hev] at hf
    have hb : I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E := by
      have := cnt_zero hv hp.L; simp only [Option.some.injEq, decide_eq_false_iff_not] at hf
      by_contra hn; exact hf (this.mpr hn)
    have L := hp.L
    have k1 := L.k1
    have k2 := L.k2
    obtain ⟨hNo, hlo⟩ := valid_lo hv
    have hlo' : 2 ^ (64 * (wk I.k - 1)) ≤ I.N := by
      refine Nat.le_trans ?_ hlo
      rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold wk; omega_arith)
    exact ⟨I, σ.mem, rfl, ⟨S, L, hNo, hlo', vN, hi, by rw [vM]; omega_arith, by omega_arith, by omega_arith, by omega_arith,
      ⟨fun i hi => by rw [S.wr, ← hp.wr]; exact hp.oP.wr i hi, hp.oP.sep⟩,
      ⟨fun i hi => by rw [S.wr, ← hp.wr]; exact hp.oQ.wr i hi, hp.oQ.sep⟩, hp.a⟩, hp.outs, hv⟩
theorem rpCode_ct [InvLaw] (M : Mont) : RelCT isa (Two RPRel) (Folded.code M.mm) fun _ _ => True := by
  unfold Folded.code
  refine RelCT.seq (R := Two RP3) (RelCT.block_append (RelCT.seq (R := Two RP2) ?_ ?_)) ?_
  · rw [rpEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := RP1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (congrArg RpP.sp h₁.2).trans (congrArg RpP.sp h₂.2).symm) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := rpCtx_of hs.1
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 40 })] : List Instr) ++
        ((entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
          .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))]))) s (RpHeadPost s) := by
      rw [← rpEntry_split]; exact rpHead_ok' c
    have e4 : s.gpr .rsp + BitVec.ofInt 64 40 = stackArgAddr s 4 := rfl
    have hB' : s.mem.readW (stackArgAddr s 4) 64 = stackArg s 4 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 4)
      (by xrun [State.ea, e4, c.ha 4 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans (congrArg RpP.B hs.2), (k.gpr (by decide)).trans (congrArg RpP.sp hs.2), hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx]
        exact (congrArg RpP.pN c₁.2).trans (congrArg RpP.pN c₂.2).symm
      · rw [h₁.rcx, h₂.rcx]
        exact congrArg (BitVec.ofNat 64) ((congrArg RpP.k c₁.2).trans (congrArg RpP.k c₂.2).symm))
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := rpCtx_of hs.1
    have hnb := c.n.congrK h.inScr h.keep
    have hnl : (rpIn s).nb.length = (s.gpr .r9).toNat := bytesAt_length _ _ _
    refine WP.mono (invalid_ok h.rdx h.rcx c.L.k1 c.L.k2 hnl (fun i hi => hnb.rd i (by rw [hnl]; exact hi))
      (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2]
    rfl
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_
  · exact Rp.failR_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ => by
      have hpre := rpPre_of (rpCtx_of hs.1) h hm k
      exact ⟨rpIn s, hs.2, hpre.scr, hpre.rdi, hpre.args, hpre.wr, hpre.L, hpre.outs⟩) h) fun _ _ h => h
  · exact (rpMain_ct M).mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, z⟩, hf⟩ => by
      refine ⟨rpIn s, hs.2, rpPre_of (rpCtx_of hs.1) h hm k, ?_⟩
      have hz : Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true := by
        simp only [eval, z, Option.map_some, Option.some.injEq] at hf; simpa using hf
      have e : (rpIn s).pub = p := hs.2
      subst e
      exact hz) h) fun _ _ h => h

/-- `vg_rsa_recover_primes` is constant time but for `n`, `e` and the number
of tries. -/
theorem rpCode_constantTime [InvLaw] (M : Mont) : ConstantTime isa rpContract.pre rpContract.pub (Folded.code M.mm) := by
  refine RelCT.constantTime ((rpCode_ct M).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(rpIn s₁).pub, ⟨h₁, rfl⟩, ⟨h₂, ?_⟩⟩)
    fun _ _ h => h)
  obtain ⟨hr, a0, a1, a2, a3, a4, a5, hn, he, hc⟩ := hp
  have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have w₁ := h₁.2.2.1
  have w₂ := h₂.2.2.1
  simp only [RpIn.pub, rpIn, RpP.mk.injEq]
  refine ⟨a4.symm, by rw [a5], by rw [r .r9 (by decide)], by rw [a1], by rw [a3], r .rdi (by decide),
    r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, hn.symm, he.symm, ?_, r .rsp (by decide), hc.symm⟩
  rw [w₁, w₂, r .rdi (by decide), r .rsi (by decide), r .rdx (by decide), r .rcx (by decide), a4, a5]

end VG.Proof.Rsa.X86_64.RecoveryFolded
