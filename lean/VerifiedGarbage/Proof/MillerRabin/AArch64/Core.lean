module

public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTab
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrLoop
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrTab
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrExp
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp

/-! # Shared Miller–Rabin core: correctness and constant time on AArch64 -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.MlKem.AArch64 (Keep)

def coreRanges (w : Nat) : List (Nat × Nat) :=
  tabRanges w ++ VG.Proof.RsaKeyGen.AArch64.expRanges w

private theorem tab_below_exp (w : Nat) :
    ∀ r ∈ tabRanges w, r.1 + r.2 ≤ slot w aE := by
  intro r hr
  simp only [tabRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [slot, hdrBytes, aT0, aE, aAcc, aTmp, aY, kV, kT0, kBits, kT2, sCnt, sFn]; omega_arith

theorem core_ok (M : Mont) {s : State} {B : Addr} {Z w c bm b : Nat}
    (hw : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hc : MrCtx s B Z w c bm) (hE : ECtx s.mem B w c)
    (hodd : c % 2 = 1) (hc3 : 3 ≤ c) (hfit : mrE c < 16 ^ (16 * w))
    (hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) :
    WP isa (seqs (preparedRound M.mm)) s fun t =>
      MrCtx t B Z w c bm ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      Frm B (coreRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hc1 : 1 < c := by omega_arith
  have hEn : B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64 := by
    have := hc.ws.scr.nowrap
    omega_arith
  unfold preparedRound
  refine wp_seqs_append (by simp [tabBuild]) (by simp [mrExpLoop])
    (WP.mono (tabBuild_ok M hw hEZ hc hodd hc1 hX) fun u ⟨hu, ht, hy, hf, hk⟩ => ?_)
  have hEu : ECtx u.mem B w c := hE.of_frm hf
    (fun r hr => Or.inr (tab_below_exp w r hr)) hEn
  refine WP.mono (mrExpLoop_ok M hw hEZ hu ht hEu hodd hc1 hy) fun t ⟨hc', hE', hp, hf', hk'⟩ =>
    ⟨hc', hE', ?_, ?_, (hk.trans hk').mono (by decide)⟩
  · rw [hp, VG.Proof.Ffdh.window_round_eq b hc3 hodd hfit, ← VG.Proof.Ffdh.rsa_round_eq b hc3 hodd]
    rfl
  · exact (hf.mono (fun r hr => List.mem_append_left _ hr)).trans
      (hf'.mono (fun r hr => List.mem_append_right _ hr))

/-- A prepared input, with only the layout and limb count shared by runs. -/
def CorePre (L : VG.Proof.Bignum.AArch64.Ws) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 128 ∧ slot L.w aE + 8 * (L.w + 2) ≤ L.Z ∧
    ∃ c bm b, MrCtx s L.B L.Z L.w c bm ∧ ECtx s.mem L.B L.w c ∧
      c % 2 = 1 ∧ 1 < c ∧
      wv s.mem L.B (slot L.w aXm) L.w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * L.w) % c

theorem core_ct (M : Mont) :
    RelCT isa (Two CorePre) (seqs (preparedRound M.mm)) fun _ _ => True := by
  unfold preparedRound
  refine ct_app' (by simp [tabBuild]) (by simp [mrExpLoop]) (Ψ := E0) ?_ (mrExpLoop_ct M)
  refine two_post ((tabBuild_ct M).mono (fun _ _ h => two_mono (fun _ _ h => ?_) h) (fun _ _ _ => trivial)) ?_
  · obtain ⟨h4, hw, hEZ, c, bm, b, hc, hE, hodd, hc1, hX⟩ := h
    exact ⟨h4, hw, hEZ, c, bm, b, hc, hodd, hc1, hX⟩
  · rintro L s ⟨h4, hw, hEZ, c, bm, b, hc, hE, hodd, hc1, hX⟩
    have hEn : L.B.toNat + slot L.w aE + 8 * (L.w + 1) ≤ 2 ^ 64 := by
      have := hc.ws.scr.nowrap
      omega_arith
    exact WP.mono (tabBuild_ok M hw hEZ hc hodd hc1 hX) fun t ⟨ht, htab, hy, hf, hk⟩ =>
      ⟨h4, hw, hEZ, c, bm, b, ht, htab,
        hE.of_frm hf (fun r hr => Or.inr (tab_below_exp L.w r hr)) hEn, hodd, hc1, hy⟩

end VG.Proof.MillerRabin.AArch64
