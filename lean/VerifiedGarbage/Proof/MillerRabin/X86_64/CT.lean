module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrRound
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Shared Miller–Rabin core: constant time on x86-64

The core reuses the RSA table and window proofs. The callable wrapper will
normalize and restore the unused RSA header fields, so only layout and limb
count need to be public at its boundary. -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MlKem.X86_64

def CorePre (q : RPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i (q.u + 8 * q.p.w)) s ∧
    MrDims q.p.B q.p.Z q.p.w ∧ ∃ (mi : BitVec 64) (c bm b : Nat),
      MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧ ECtx s.mem q.p.B q.p.w c ∧
      wv s.mem q.p.B (slot q.p.w aXm) q.p.w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * q.p.w) % c ∧
      c % 2 = 1 ∧ 1 < c

private def AfterTable (q : RPub) (s : State) : Prop :=
  ExpPre ⟨q.p, q.i, q.u + 8 * q.p.w⟩ s

theorem core_ct (M : Mont) :
    RelCT isa (Two CorePre) (seqs (preparedRound M.mm)) fun _ _ => True := by
  unfold preparedRound
  refine RelCT.seqs_app (by simp [tabBuild]) (by simp [mrExpLoop]) (RelCT.seq (R := Two AfterTable) ?_ ?_)
  · refine two_post ((tabBuild_ct M).mono (fun _ _ h => two_mono (fun _ _ h => ?_) h) (fun _ _ _ => trivial)) ?_
    · obtain ⟨hk, hp, hd, mi, c, bm, b, hc, hE, hX, hodd, hc1⟩ := h
      exact ⟨⟨hk, hp⟩, hd, mi, c, bm, b, hc, hX, hodd, hc1⟩
    · rintro q s ⟨hk, hp, hd, mi, c, bm, b, hc, hE, hX, hodd, hc1⟩
      have hEn : q.p.B.toNat + slot q.p.w aE + 8 * (q.p.w + 1) ≤ 2 ^ 64 := by
        have := hc.good.scr.nowrap
        have := aE_fits hd
        omega_arith
      exact WP.mono (tabBuild_ok M hd hc hodd hc1 hX) fun t ⟨ht, htab, hy, hf, k⟩ =>
        ⟨hk, ⟨ht.good.rdi, k.2.2.trans hp.wr,
          fun e he => hdr_frm hf (vs_tab _ _ _) hp.hdr e he⟩, hd,
          mi, c, _, b, ht, htab,
          hE.of_frm hf (fun r hr => Or.inr (tabRanges_lt q.p.w r hr)) hEn, hodd, hc1, hy⟩
  · exact two_map (fun q : RPub => (⟨q.p, q.i, q.u + 8 * q.p.w⟩ : EPub))
      (fun _ _ h => h) (mrExpLoop_ct M)

end VG.Proof.MillerRabin.X86_64
