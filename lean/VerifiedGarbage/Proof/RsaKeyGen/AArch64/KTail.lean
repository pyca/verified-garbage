import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Fin
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain

/-!
# A candidate on AArch64: Montgomery setup, Miller–Rabin and the result

`kTail_ok`: `montSetup`, `millerRabin` and `mrResult` end as
`primalityTest c` on the octets after the candidate.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aAcc aTmp aR2 aY aOne sCnt)

/-- Disjointness of a header word from `montSetup`'s ranges, and their bounds. -/
macro "kt_disj" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, msRanges, msTail, slot,
    hdrBytes, aN, aAcc, aTmp, aR2, aY, aOne, aR1, aRm1, sCnt, kChecks, kE, sFn, sMinv, kRand, kLen, Public.sK,
    kRandLen, kUsed, kOut, kUsedP, Public.sMask]
  and_intros <;> omega))

/-- The octets of `out`, past the scratch space, survive changes inside it. -/
theorem outBytes_inScr' {B : Addr} {Z k : Nat} {m m' : Mem} {op : Addr} (hin : InScr B Z m m')
    (hz : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)) : outBytes m' op k = outBytes m op k :=
  List.map_congr_left fun j hj => hin _ (hz j (List.mem_range.mp hj))

/-- `montSetup`, `millerRabin` and `mrResult`, for the candidate `c` in
`aN`, from offset `8 w` of `rand`. -/
theorem kTail_ok (M : Mont) {s : State} {B : Addr} {Z w c : Nat} {op up rp : Addr} {r : List Byte}
    (h : Ws s B Z w) (hw4 : 4 ≤ w) (hw64 : w ≤ 64) (hn : wv s.mem B (slot w aN) w = c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c) (ho : OutUp s B Z op up (8 * w))
    (hO : word s.mem B (8 * kOut) = op) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hU : word s.mem B (8 * kUsedP) = up) (hM : word s.mem B (8 * Public.sMask) = mask true)
    (hrp : word s.mem B (8 * kRand) = rp) (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w)) (hsrc : Src s B Z rp r) (hrl : r.length < 2 ^ 64)
    (hrk : 8 * w ≤ r.length) :
    WP isa (seqs (montSetup M.mm ++ millerRabin M.mm ++ [mrResult])) s fun t =>
      TestEnd s t op up (8 * w) r c (Spec.RsaKeyGen.primalityTest c (r.drop (8 * w))) := by
  have hnw := h.scr.nowrap
  have hZ := h.hZ
  obtain ⟨hodd, hlo, hhi⟩ := hsh
  have htop : 2 ^ (64 * w - 1) ≤ c := by
    have : 2 ^ (64 * w - 1) = 2 ^ (64 * w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    omega
  have hc1 : 1 < c := by
    have : 2 ≤ 2 ^ (64 * w - 1) := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (show 1 ≤ 64 * w - 1 by omega))
    omega
  have hW : ∀ {rs : List (Nat × Nat)} {m m' : Mem}, Frm B rs m m' → ∀ {i : Nat}, i < 32 →
      (∀ r ∈ rs, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i) → word m' B (8 * i) = word m B (8 * i) :=
    fun f _ hi hd => f.word_eq hd (by have := h.h256; omega)
  rw [List.append_assoc]
  refine wp_seqs_append (by simp [montSetup]) (by simp [millerRabin]) ?_
  refine WP.mono (montSetup_ok M h hw4 hw64 hn hodd htop) fun s₁ ⟨h₁, hinv₁, hn₁, hr2₁, hr1₁, hrm₁, hch₁, f₁, k₁⟩ => ?_
  have hc₁ : MrCtx s₁ B Z w c (wv s₁.mem B (slot w aB) w) := ⟨h₁, hinv₁, hn₁, rfl, hr1₁, hrm₁⟩
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := by simpa only [slot, hdrBytes] using hZ
  have hsl₁ : ∀ r ∈ msRanges w, r.1 + r.2 ≤ Z := by kt_disj
  have hin₁ : InScr B Z s.mem s₁.mem := InScr.of_frm f₁ (fun r hr => by
    have := hsl₁ r hr; omega)
  have hsrc₁ := hsrc.congrK hin₁ k₁
  have hres : mrRest c (VG.Proof.RsaKeyGen.checksW w) r 1 0 (8 * w) =
      Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) := by
    rw [VG.Proof.RsaKeyGen.primalityTest_cand (by omega) ⟨hodd, hlo, hhi⟩,
      VG.Proof.RsaKeyGen.checksW_eq w (by omega) hw4]
  refine wp_seqs_append (by simp [millerRabin]) (by simp) ?_
  refine WP.mono (millerRabin_ok M hw4 hw64 hc1 ⟨hodd, hlo, hhi⟩ hrl (by
      unfold VG.Proof.RsaKeyGen.checksW; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
        (try split) <;> decide) hc₁ hr2₁
    ((hW f₁ (by decide) (by kt_disj)).trans hrp)
    ((hW f₁ (by decide) (by kt_disj)).trans hK)
    ((hW f₁ (by decide) (by kt_disj)).trans hrlen) hch₁ hsrc₁
    ((hW f₁ (by decide) (by kt_disj)).trans hus) (Nat.le_refl _) hrk)
    fun s₂ ⟨⟨bm, hc₂⟩, h0, h1, f₂, k₂⟩ => ?_
  rw [hres] at h0 h1
  have hsl₂ : ∀ r ∈ roundRanges w, r.1 + r.2 ≤ Z := fun r hr => by have := roundRanges_le w r hr; omega
  have hin₂ : InScr B Z s.mem s₂.mem := hin₁.trans (InScr.of_frm f₂ hsl₂)
  have k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
  have ho₂ := ho.congr k12.wr
  have hM₂ : word s₂.mem B (8 * Public.sMask) = mask true :=
    (hW f₂ (by decide) (by simp only [Public.sMask]; rd_disj)).trans
      ((hW f₁ (by decide) (by kt_disj)).trans hM)
  refine WP.mono (mrResult_ok (r := r) hc₂.ws hw64 hc₂.n ho₂
    ((hW f₂ (by decide) (roundRanges_hdr w (by simp))).trans
      ((hW f₁ (by decide) (by kt_disj)).trans hO))
    ((hW f₂ (by decide) (roundRanges_hdr w (by simp))).trans
      ((hW f₁ (by decide) (by kt_disj)).trans hK))
    ((hW f₂ (by decide) (roundRanges_hdr w (by simp))).trans
      ((hW f₁ (by decide) (by kt_disj)).trans hU)) hM₂ h0 h1) fun t ht => ?_
  have hout := outBytes_inScr' hin₂ ho.outZ
  have kk : Keep (.x0 :: mmRegs) s s₂ := k12.mono (by decide)
  rcases hp : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with _ | ⟨b, rest⟩
  · rw [hp] at ht; exact KEnd.trans_pre ht hout kk
  · rw [hp] at ht; cases b <;> exact KEnd.trans_pre ht hout kk

end VG.Proof.RsaKeyGen.AArch64
