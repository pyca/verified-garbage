module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Fin
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.Rsa.Ranges

/-!
# A candidate on AArch64: Montgomery setup, Miller–Rabin and the result

`kTail_ok`: `montSetup`, `expSetup`, `millerRabin` and `mrResult` end as
`primalityTest c` on the octets after the candidate.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aAcc aTmp aR2 aY aOne sCnt)

/-- Disjointness of a header word from `montSetup`'s ranges, and their bounds. -/
tactic_template "kt_disj" : tactic => `(tactic| first | hdr_disj | (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, msRanges, msTail,
    List.cons_append, List.nil_append, slot, hdrBytes, aE, aN, aAcc, aTmp, aR2, aY, aOne, aR1, aRm1, sCnt, kChecks, kE, sFn, sMinv, kRand, kLen, Public.sK,
    kRandLen, kUsed, kOut, kUsedP, Public.sMask]
  and_intros <;> omega_arith))

/-- The octets of `out`, past the scratch space, survive changes inside it. -/
theorem outBytes_inScr' {B : Addr} {Z k : Nat} {m m' : Mem} {op : Addr} (hin : InScr B Z m m')
    (hz : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)) : outBytes m' op k = outBytes m op k :=
  List.map_congr_left fun j hj => hin _ (hz j (List.mem_range.mp hj))

/-- `montSetup`, `expSetup`, `millerRabin` and `mrResult`, for the candidate `c` in
`aN`, from offset `8 w` of `rand`. -/
theorem kTail_ok (M : Mont) {s : State} {B : Addr} {Z w c : Nat} {op up rp : Addr} {r : List Byte}
    (h : Ws s B Z w) (hw4 : 4 ≤ w) (hw64 : w ≤ 64) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hn : wv s.mem B (slot w aN) w = c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c) (ho : OutUp s B Z op up (8 * w))
    (hO : word s.mem B (8 * kOut) = op) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hU : word s.mem B (8 * kUsedP) = up) (hM : word s.mem B (8 * Public.sMask) = mask true)
    (hrp : word s.mem B (8 * kRand) = rp) (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w)) (hsrc : Src s B Z rp r) (hrl : r.length < 2 ^ 64)
    (hrk : 8 * w ≤ r.length) :
    WP isa (seqs (montSetup M.mm ++ expSetup ++ millerRabin M.mm ++ [mrResult])) s fun t =>
      TestEnd s t op up (8 * w) r c (Spec.RsaKeyGen.primalityTest c (r.drop (8 * w))) := by
  have hnw := h.scr.nowrap
  have hZ := h.hZ
  obtain ⟨hodd, hlo, hhi⟩ := hsh
  have htop : 2 ^ (64 * w - 1) ≤ c := by
    have : 2 ^ (64 * w - 1) = 2 ^ (64 * w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega_arith
    omega_arith
  have hc1 : 1 < c := by
    have : 2 ≤ 2 ^ (64 * w - 1) := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (show 1 ≤ 64 * w - 1 by omega_arith))
    omega_arith
  have hW : ∀ {rs : List (Nat × Nat)} {m m' : Mem}, Frm B rs m m' → ∀ {i : Nat}, i < 32 →
      (∀ r ∈ rs, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i) → word m' B (8 * i) = word m B (8 * i) :=
    fun f _ hi hd => f.word_eq hd (by have := h.h256; omega_arith)
  rw [List.append_assoc, List.append_assoc]
  refine wp_seqs_append (by simp [montSetup]) (by simp [expSetup, lowWord]) ?_
  refine WP.mono (montSetup_ok M h hw4 hw64 hn hodd htop) fun s₀ ⟨h₀, hinv₀, hn₀, hr2₀, hr1₀, hrm₀, hch₀, f₀, k₀⟩ => ?_
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := by simpa only [slot, hdrBytes] using hZ
  have hsl₀ : ∀ r ∈ msRanges w, r.1 + r.2 ≤ Z := by kt_disj
  refine wp_seqs_append (by simp [expSetup, lowWord]) (by simp [millerRabin]) ?_
  refine WP.mono (expSetup_ok h₀ hEZ hn₀ (by omega_arith) hc1) fun s₁ ⟨hE₁, fE, h₁, kE⟩ => ?_
  have hEw : ∀ r ∈ [(slot w aE, 8 * (w + 1))], ∀ d, d + 8 * w ≤ slot w aE → d + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ d :=
    fun r hr d hd => by simp only [List.mem_singleton] at hr; subst hr; exact Or.inl hd
  have hbel : ∀ {j : Nat}, j < 16 → slot w j + 8 * w ≤ slot w aE := fun {j} hj => by
    have := VG.Proof.Rsa.slot_lt (w := w) (show j < aE by unfold aE; omega); omega_arith
  have hN0 := hbel (show aN < 16 by decide)
  have hR10 := hbel (show aR1 < 16 by decide)
  have hRm0 := hbel (show aRm1 < 16 by decide)
  have hR20 := hbel (show aR2 < 16 by decide)
  have hsm : 8 * sMinv + 8 ≤ 256 := by decide
  have hc₁ : MrCtx s₁ B Z w c (wv s₁.mem B (slot w aB) w) := ⟨h₁,
    by rw [fE.word_eq (d := slot w aN) (fun r hr => by
          have := hEw r hr (slot w aN) (hbel (show aN < 16 by decide)); omega_arith) (by omega_arith),
        fE.word_eq (d := 8 * sMinv) (by kt_disj) (by omega_arith)]; exact hinv₀,
    by rw [fE.wv_eq (hEw · · _ (hbel (show aN < 16 by decide))) (by omega_arith)]; exact hn₀, rfl,
    by rw [fE.wv_eq (hEw · · _ (hbel (show aR1 < 16 by decide))) (by omega_arith)]; exact hr1₀,
    by rw [fE.wv_eq (hEw · · _ (hbel (show aRm1 < 16 by decide))) (by omega_arith)]; exact hrm₀⟩
  have hr2₁ : wv s₁.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c := by
    rw [fE.wv_eq (hEw · · _ (hbel (show aR2 < 16 by decide))) (by omega_arith)]; exact hr2₀
  have hEn : slot w aE + 8 * (w + 1) ≤ Z := by omega_arith
  have f₁ : Frm B (msRanges w ++ [(slot w aE, 8 * (w + 1))]) s.mem s₁.mem :=
    (f₀.mono fun r hr => List.mem_append_left _ hr).trans (fE.mono fun r hr => List.mem_append_right _ hr)
  have hsl₁ : ∀ r ∈ msRanges w ++ [(slot w aE, 8 * (w + 1))], r.1 + r.2 ≤ Z := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hsl₀ r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hEn
  have hin₁ : InScr B Z s.mem s₁.mem := InScr.of_frm f₁ (fun r hr => by
    have := hsl₁ r hr; omega_arith)
  have k₁ : Keep mmRegs s s₁ := (k₀.trans kE).mono (by decide)
  have hch₁ : word s₁.mem B (8 * kChecks) = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w) := by
    exact (hW fE (show kChecks < 32 by decide) (by kt_disj)).trans hch₀
  have hsrc₁ := hsrc.congrK hin₁ k₁
  have hres : mrRest c (VG.Proof.RsaKeyGen.checksW w) r 1 0 (8 * w) =
      Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) := by
    rw [VG.Proof.RsaKeyGen.primalityTest_cand (by omega_arith) ⟨hodd, hlo, hhi⟩,
      VG.Proof.RsaKeyGen.checksW_eq w (by omega_arith) hw4]
  refine wp_seqs_append (by simp [millerRabin]) (by simp) ?_
  refine WP.mono (millerRabin_ok M hw4 (by omega_arith) hEZ hc1 ⟨hodd, hlo, hhi⟩ hrl
    (Nat.lt_of_le_of_lt (VG.Proof.RsaKeyGen.checksW_le w) (by decide)) hc₁ hE₁ hr2₁
    ((hW f₁ (by decide) (by kt_disj)).trans hrp)
    ((hW f₁ (by decide) (by kt_disj)).trans hK)
    ((hW f₁ (by decide) (by kt_disj)).trans hrlen) hch₁ hsrc₁
    ((hW f₁ (by decide) (by kt_disj)).trans hus) (Nat.le_refl _) hrk)
    fun s₂ ⟨⟨bm, hc₂⟩, h0, h1, f₂, k₂⟩ => ?_
  rw [hres] at h0 h1
  have hsl₂ : ∀ r ∈ roundRanges w, r.1 + r.2 ≤ Z := fun r hr => by have := roundRanges_lt w r hr; omega_arith
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
