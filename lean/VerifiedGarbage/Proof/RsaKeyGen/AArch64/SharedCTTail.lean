module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedCTMain
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTTail
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMr
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KTail
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Bignum.AArch64.PdCTExp

/-! # Constant time of RSA setup, shared Miller–Rabin, and result -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)
open VG.Proof.RsaKeyGen (shapeOf itersOf passS checksW)

theorem sharedLoopEnd_endq {q : FPub} {s : State} (h : SharedLoopEnd q s) : EndQ q s := by
  obtain ⟨-, -, c, r, s₀, res, ⟨⟨bm, hc⟩, h0, h1, hf, k⟩, hS, -, hO, hU, hK, ho⟩ := h
  have hw : ∀ {i : Nat}, (i = kRand ∨ i = kLen ∨ i = kRandLen ∨ i = kChecks ∨ i = kOut ∨ i = kUsedP) →
      word s.mem q.B (8 * i) = word s₀.mem q.B (8 * i) := fun hi =>
    hf.word_eq (sharedRoundRanges_hdr _ hi) (by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨hc.ws, (hw (by simp)).trans hO, (hw (by simp)).trans hK, (hw (by simp)).trans hU, ho.congr k.wr, ?_⟩
  rw [← hS]
  rcases hres : res with _ | ⟨b, rest⟩
  · exact h0 hres
  · exact (h1 b rest hres).1

theorem sharedTail_ct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) :
    RelCT isa (Two TS) (seqs (montSetup M.mm ++ expSetup ++ millerRabinWith M.mm R.run ++ [mrResult])) fun _ _ => True := by
  rw [List.append_assoc, List.append_assoc]
  exact ct_app' (by simp [montSetup]) (by simp [expSetup, lowWord])
    (two_post (two_map FPub.L (fun _ _ h => ts_ms0 h) (montSetup_ct M)) fun _ _ h => ms_mrpre M h)
    (ct_app' (by simp [expSetup, lowWord]) (by simp [millerRabinWith]) expSetup_ct (ct_app' (by simp [millerRabinWith]) (by simp)
      ((sharedMillerRabin_ct M R).mono (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => sharedLoopEnd_endq h) h)
      mrResult_ct))

end VG.Proof.RsaKeyGen.AArch64
