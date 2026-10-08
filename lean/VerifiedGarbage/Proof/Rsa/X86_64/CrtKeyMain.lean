import VerifiedGarbage.Proof.Rsa.X86_64.KeyMain
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyPhases
import VerifiedGarbage.Proof.Rsa.CrtKeyParts

/-!
# `vg_rsa_check_crt_key` on x86-64: the checks

`main`, from the header its entry leaves (`vg_rsa_check_key`'s, with `p` in
`d`'s slots: `MainPre` with `d = p`), for a valid modulus and exponent: the
workspace (`setupK_ok`), then each check, and'ed into `sMask`; it returns
`crtKeyValid` as 1 or 0 (`crtMain_ok`).
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

theorem crtMain_eq : Impl.Rsa.X86_64.CheckCrtKey.main = seqs (([.block VG.Impl.Rsa.X86_64.head, loadBE,
    .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)], setWord aOne .rcx,
    .block [.mov32 .rax (.imm 0), .alu .sub .rax (.imm 1), .store (hdr sMask) .rax]] : List (Prog isa)) ++
    ((loadNum aX sP sPlen ++ loadNum aR sQ sQlen ++ mulXR ++ VG.Impl.Rsa.X86_64.Crt.eqCheck) ++
    (Impl.Rsa.X86_64.CheckCrtKey.modChecks sP sPlen sDP ++ (Impl.Rsa.X86_64.CheckCrtKey.modChecks sQ sQlen sDQ ++
    ((loadNum aM sP sPlen ++ loadNum aX sQI sPlen ++ ltMask aX aM ++
      loadNum aR sQ sQlen ++ mulXR ++ Impl.Rsa.X86_64.CheckCrtKey.reduceTop sPlen Impl.Rsa.X86_64.CheckCrtKey.topQ ++
      eqOne) ++
    ([.block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)] :
      List (Prog isa))))))) := by
  simp only [Impl.Rsa.X86_64.CheckCrtKey.main, List.append_assoc]

/-- `main`: `crtKeyValid` returned as 1 or 0, and the saved registers
restored. -/
theorem crtMain_ok {s : State} {B : Addr} {Z k : Nat} {np pp pq pdp pdq pqi : Addr}
    {nb pb qb dpb dqb qib : List Byte} {ev : Nat}
    (hp : MainPre s B Z k np pp pp pq pdp pdq pqi nb pb pb qb dpb dqb qib ev)
    (he : Spec.Rsa.exponentValid ev = true) :
    WP isa Impl.Rsa.X86_64.CheckCrtKey.main s fun t =>
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
  rw [crtMain_eq]
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
  refine wsa (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum]) (by simp [loadNum])
    (WP.mono (crtModChecks_ok h₃ m₃
    (sX := sQ) (sXlen := sQlen) (sDX := sDQ) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hw sQ (by decide) (by decide)]; exact hp.hQ) (by rw [hw sQlen (by decide) (by decide)]; exact hp.hQl)
    (by rw [hw sDQ (by decide) (by decide)]; exact hp.hDQ) (sr hp.srQ) (sr hp.srDQ) hp.dql hp.ql1
    (by omega) (by rw [hE]; exact hev)) fun t₄ ⟨h₄, Mq, Rq, eMq, eRq, m₄⟩ => ?_)
  refine wsa (by simp [loadNum]) (by simp) (WP.mono (crtQInv_ok h₄ m₄
    (by rw [hw sP (by decide) (by decide)]; exact hp.hP) (by rw [hw sPlen (by decide) (by decide)]; exact hp.hPl)
    (by rw [hw sQ (by decide) (by decide)]; exact hp.hQ) (by rw [hw sQlen (by decide) (by decide)]; exact hp.hQl)
    (by rw [hw sQI (by decide) (by decide)]; exact hp.hQI) (sr hp.srP) (sr hp.srQ) (sr hp.srQI) hp.qil
    hp.pl1 (by omega) hp.ql1 (by omega)) fun t₅ ⟨h₅, Rpq, eR, m₅⟩ => ?_)
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

end VG.Proof.Rsa.X86_64.Key
