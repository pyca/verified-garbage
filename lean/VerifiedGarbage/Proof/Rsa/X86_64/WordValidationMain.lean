module

public import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyMain
public import VerifiedGarbage.Proof.Rsa.X86_64.WordValidationGuard
import VerifiedGarbage.Proof.Rsa.X86_64.WordValidationQI
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyPhases
import VerifiedGarbage.Proof.Rsa.CrtKeyParts
import VerifiedGarbage.Proof.Rsa.X86_64.KeyPhases
import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps
import VerifiedGarbage.Proof.Rsa.Octets

/-! # Full CRT-key validation with a word remainder

Only the final inverse-coefficient reduction differs from `crtMain_ok`.
The accumulated acceptance mask supplies `p q = n`, so public dispatch
implies a normalized `p`; the adapter is safe even when the mask is clear.
The final theorem composes the public guard with either implementation.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

theorem crtMainFast_eq : Impl.Rsa.X86_64.CheckCrtKey.mainFast = seqs (([.block VG.Impl.Rsa.X86_64.head, loadBE,
    .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)], setWord aOne .rcx,
    .block [.mov32 .rax (.imm 0), .alu .sub .rax (.imm 1), .store (hdr sMask) .rax]] : List (Prog isa)) ++
    ((loadNum aX sP sPlen ++ loadNum aR sQ sQlen ++ mulXR ++ VG.Impl.Rsa.X86_64.Crt.eqCheck) ++
    (Impl.Rsa.X86_64.CheckCrtKey.modChecks sP sPlen sDP ++ (Impl.Rsa.X86_64.CheckCrtKey.modChecks sQ sQlen sDQ ++
    (([Impl.Rsa.X86_64.WordValidation.qinv]) ++
    ([.block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)] :
      List (Prog isa))))))) := by
  simp only [Impl.Rsa.X86_64.CheckCrtKey.mainFast, List.append_assoc]

/-- `main`: `crtKeyValid` returned as 1 or 0, and the saved registers
restored. -/
theorem crtMainFast_ok {s : State} {B : Addr} {Z k : Nat} {np pp pq pdp pdq pqi : Addr}
    {nb pb qb dpb dqb qib : List Byte} {ev : Nat}
    (hp : MainPre s B Z k np pp pp pq pdp pdq pqi nb pb pb qb dpb dqb qib ev)
    (he : Spec.Rsa.exponentValid ev = true)
    (hg : VG.Proof.Rsa.X86_64.WordDivide.guardVal ((k + 7) / 8) k pb.length qb.length
      (nb[0]'(by rw [hp.nl]; have := hp.k1; omega)) = 0) :
    WP isa Impl.Rsa.X86_64.CheckCrtKey.mainFast s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (Spec.Rsa.crtKeyValid k (Spec.Rsa.os2ip nb) ev
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib)).toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      InScr B Z s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Keep mmRegs s t := by
  have := hp.k1
  have := hp.k2
  have := hp.pl2
  have := hp.ql2
  have hk8 : k ≤ 8 * ((k + 7) / 8) := by omega
  have hev : ev < 2 ^ 33 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he; exact he.2
  rw [crtMainFast_eq]
  refine wsa (by simp) (by simp [loadNum]) (WP.mono (setupK_ok hp)
    fun t₀ ⟨minv, h₀, m₀, hw, in₀, rd₀, wr₀, k₀⟩ => ?_)
  have sr : ∀ {p : Addr} {bs : List Byte}, Src s B Z p bs → Src t₀ B Z p bs := fun h => h.congr in₀ rd₀ wr₀
  have hE : (word t₀.mem B (8 * sEv)).toNat = ev := by rw [hw sEv (by decide) (by decide)]; exact hp.hEv
  refine wsa (by simp [loadNum]) (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum]) (WP.mono (pqN_ok h₀ m₀
    (by rw [hw sP (by decide) (by decide)]; exact hp.hP) (by rw [hw sPlen (by decide) (by decide)]; exact hp.hPl)
    (by rw [hw sQ (by decide) (by decide)]; exact hp.hQ) (by rw [hw sQlen (by decide) (by decide)]; exact hp.hQl)
    (sr hp.srP) (sr hp.srQ) hp.pl1 (by omega) hp.ql1 (by omega)) fun t₂ ⟨h₂, m₂⟩ => ?_)
  refine wsa (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum])
    (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum]) (WP.mono (crtModChecks_ok h₂ m₂
    (sX := sP) (sXlen := sPlen) (sDX := sDP) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hw sP (by decide) (by decide)]; exact hp.hP) (by rw [hw sPlen (by decide) (by decide)]; exact hp.hPl)
    (by rw [hw sDP (by decide) (by decide)]; exact hp.hDP) (sr hp.srP) (sr hp.srDP) hp.dpl hp.pl1
    (by omega) (by rw [hE]; exact hev)) fun t₃ ⟨h₃, Mp, Rp, eMp, eRp, m₃⟩ => ?_)
  refine wsa (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum]) (by simp)
    (WP.mono (crtModChecks_ok h₃ m₃
    (sX := sQ) (sXlen := sQlen) (sDX := sDQ) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hw sQ (by decide) (by decide)]; exact hp.hQ) (by rw [hw sQlen (by decide) (by decide)]; exact hp.hQl)
    (by rw [hw sDQ (by decide) (by decide)]; exact hp.hDQ) (sr hp.srQ) (sr hp.srDQ) hp.dql hp.ql1
    (by omega) (by rw [hE]; exact hev)) fun t₄ ⟨h₄, Mq, Rq, eMq, eRq, m₄⟩ => ?_)
  have pqeq : ((true && decide (Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb)) &&
      decide (Spec.Rsa.os2ip dpb < Mp) && decide (Rp = 1) &&
      decide (Spec.Rsa.os2ip dqb < Mq) && decide (Rq = 1)) = true →
      Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb := by
    intro hb
    simp only [Bool.and_eq_true, Bool.true_and, decide_eq_true_eq] at hb
    exact hb.1.1.1.1
  refine wsa (by simp) (by simp) (WP.mono (crtQInvWord_ok h₄ m₄
    (by omega) (by omega)
    (by have := hp.zk; simp only [VG.Proof.Rsa.X86_64.WordValidation.start,
      VG.Proof.Rsa.X86_64.WordValidation.span, slot, Impl.Bignum.hdrBytes]; omega)
    (by rw [hw sP (by decide) (by decide)]; exact hp.hP) (by rw [hw sPlen (by decide) (by decide)]; exact hp.hPl)
    (by rw [hw sQ (by decide) (by decide)]; exact hp.hQ) (by rw [hw sQlen (by decide) (by decide)]; exact hp.hQl)
    (by rw [hw sQI (by decide) (by decide)]; exact hp.hQI) (sr hp.srP) (sr hp.srQ) (sr hp.srQI) hp.qil
    hp.pl1 (by omega) hp.ql1 (by omega)
    (fun hb => (validationFactors hp hg (pqeq hb)).1)
    (fun hb => pqeq hb)) fun t₅ ⟨h₅, Rpq, eR, m₅⟩ => ?_)
  refine WP.mono (outK_ok h₅.good h₅.hZ m₅) fun t ⟨hax, hsv, hm, kk⟩ =>
    ⟨?_, fun i hi => ?_, ?_, kk.2.1.trans (h₅.rd.trans rd₀), kk.2.2.trans (h₅.wr.trans wr₀),
      ((k₀.trans h₅.keep).trans kk).mono (by decide)⟩
  · rw [hE] at eRp eRq
    rw [hax, Proof.Rsa.crtKeyValid_parts hp.mv he
      (Nat.lt_of_lt_of_le (lt_of_os2ip pb) (Nat.pow_le_pow_right (by decide) (by omega)))
      (Nat.lt_of_lt_of_le (lt_of_os2ip qb) (Nat.pow_le_pow_right (by decide) (by omega)))
      eMp eMq eRp eRq eR]
    rfl
  · rw [hsv i hi, h₅.hdr i (by omega) (by unfold sMask sFn; omega)]
    exact hw i (by omega) (by revert hi; revert i; decide)
  · rw [hm]; exact in₀.trans h₅.ins

theorem crtMainChoice_ok {s : State} {B : Addr} {Z k : Nat} {np pp pq pdp pdq pqi : Addr}
    {nb pb qb dpb dqb qib : List Byte} {ev : Nat}
    (hp : MainPre s B Z k np pp pp pq pdp pdq pqi nb pb pb qb dpb dqb qib ev)
    (he : Spec.Rsa.exponentValid ev = true) :
    WP isa (Impl.Rsa.X86_64.WordValidation.choice Impl.Rsa.X86_64.CheckCrtKey.mainFast
      Impl.Rsa.X86_64.CheckCrtKey.main) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (Spec.Rsa.crtKeyValid k (Spec.Rsa.os2ip nb) ev
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib)).toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      InScr B Z s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Keep mmRegs s t := by
  unfold Impl.Rsa.X86_64.WordValidation.choice
  refine WP.seq (WP.mono (validationGuardHead_ok hp) fun s₁ ⟨h₁, m₁, h12, hdx, k₁⟩ => ?_)
  refine WP.seq (WP.mono (validationGuardTail_ok h₁ h12 hdx) fun s₂ ⟨h₂, m₂, hz, k₂⟩ => ?_)
  have mm := m₂.trans m₁
  refine WP.ite (VG.Proof.Rsa.X86_64.WordDivide.guardVal ((k + 7) / 8) k pb.length qb.length
    (nb[0]'(by rw [hp.nl]; have := hp.k1; omega)) == 0) (by simp only [eval, hz]) (fun hb => ?_) (fun _ => ?_)
  · have hg : VG.Proof.Rsa.X86_64.WordDivide.guardVal ((k + 7) / 8) k pb.length qb.length
      (nb[0]'(by rw [hp.nl]; have := hp.k1; omega)) = 0 := by simpa only [beq_iff_eq] using hb
    exact WP.mono (crtMainFast_ok h₂ he hg) fun t ⟨ha, hs, hi, hr, hw, kk⟩ =>
      ⟨ha, by rw [mm] at hs; exact hs, by rw [mm] at hi; exact hi,
        hr.trans (k₂.2.1.trans k₁.2.1), hw.trans (k₂.2.2.trans k₁.2.2), ((k₁.trans k₂).trans kk).mono (by decide)⟩
  · exact WP.mono (crtMain_ok h₂ he) fun t ⟨ha, hs, hi, hr, hw, kk⟩ =>
      ⟨ha, by rw [mm] at hs; exact hs, by rw [mm] at hi; exact hi,
        hr.trans (k₂.2.1.trans k₁.2.1), hw.trans (k₂.2.2.trans k₁.2.2), ((k₁.trans k₂).trans kk).mono (by decide)⟩

end VG.Proof.Rsa.X86_64.Key
