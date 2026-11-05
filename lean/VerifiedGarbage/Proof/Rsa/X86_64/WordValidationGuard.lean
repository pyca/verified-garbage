module

public import VerifiedGarbage.Proof.Rsa.X86_64.KeyMain
public import VerifiedGarbage.Impl.Rsa.X86_64.WordValidation
public import VerifiedGarbage.Proof.Rsa.X86_64.WordGuard
import VerifiedGarbage.Proof.Rsa.WordFactors
import VerifiedGarbage.Proof.Bignum.X86_64.R2

/-! # Public dispatch before setting up CRT-key validation -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- A read-only guard preserves every input assertion of the validation main. -/
theorem MainPre.same {s t : State} {B : Addr} {Z k : Nat} {np pd pp pq pdp pdq pqi : Addr}
    {nb db pb qb dpb dqb qib : List Byte} {ev : Nat} {rs : List Reg}
    (h : MainPre s B Z k np pd pp pq pdp pdq pqi nb db pb qb dpb dqb qib ev)
    (hm : t.mem = s.mem) (hk : Keep rs s t) (hr : .rdi ∉ rs) :
    MainPre t B Z k np pd pp pq pdp pdq pqi nb db pb qb dpb dqb qib ev := by
  have hi : InScr B Z s.mem t.mem := by rw [hm]; exact InScr.refl _ _ _
  exact { h with
    scr := h.scr.congr hk.2.2
    rdi := (hk.gpr hr).trans h.rdi
    hK := by rw [hm]; exact h.hK
    hN := by rw [hm]; exact h.hN
    hD := by rw [hm]; exact h.hD
    hDl := by rw [hm]; exact h.hDl
    hP := by rw [hm]; exact h.hP
    hPl := by rw [hm]; exact h.hPl
    hQ := by rw [hm]; exact h.hQ
    hQl := by rw [hm]; exact h.hQl
    hDP := by rw [hm]; exact h.hDP
    hDQ := by rw [hm]; exact h.hDQ
    hQI := by rw [hm]; exact h.hQI
    hEv := by rw [hm]; exact h.hEv
    srN := h.srN.congrK hi hk
    srD := h.srD.congrK hi hk
    srP := h.srP.congrK hi hk
    srQ := h.srQ.congrK hi hk
    srDP := h.srDP.congrK hi hk
    srDQ := h.srDQ.congrK hi hk
    srQI := h.srQI.congrK hi hk }

theorem validationGuardHead_ok {s : State} {B : Addr} {Z k : Nat} {np pd pp pq pdp pdq pqi : Addr}
    {nb db pb qb dpb dqb qib : List Byte} {ev : Nat}
    (h : MainPre s B Z k np pd pp pq pdp pdq pqi nb db pb qb dpb dqb qib ev) :
    WP isa (.block WordValidation.guardHead) s fun t =>
      MainPre t B Z k np pd pp pq pdp pdq pqi nb db pb qb dpb dqb qib ev ∧ t.mem = s.mem ∧
      t.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.gpr .rdx = np ∧ Keep mmRegs s t := by
  have hz := h.zk
  have hk := h.k1
  have hk' := h.k2
  refine WP.mono (WP.keep [.r12, .rdx] (Q := fun t => t.mem = s.mem ∧
    t.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.gpr .rdx = np) (by
    xrun [WordValidation.guardHead, State.ea, hdr, h.rdi, hdrOff,
      h.scr.ld (d := 8 * sK) (by change 8 * 18 + 8 ≤ Z; omega_using [hz, hk]),
      h.scr.ld (d := 8 * sN) (by change 8 * 17 + 8 ≤ Z; omega_using [hz, hk]),
      h.hK, h.hN, shr3_w k (by omega_using [hk'])]) rfl) fun t ⟨⟨hm, h12, hdx⟩, hkeep⟩ =>
        ⟨h.same hm hkeep (by decide), hm, h12, hdx, hkeep.mono (by decide)⟩

theorem validationGuardTail_ok {s : State} {B : Addr} {Z k : Nat} {np pd pp pq pdp pdq pqi : Addr}
    {nb db pb qb dpb dqb qib : List Byte} {ev : Nat}
    (h : MainPre s B Z k np pd pp pq pdp pdq pqi nb db pb qb dpb dqb qib ev)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8)) (hdx : s.gpr .rdx = np) :
    WP isa (.block WordValidation.guardTail) s fun t =>
      MainPre t B Z k np pd pp pq pdp pdq pqi nb db pb qb dpb dqb qib ev ∧ t.mem = s.mem ∧
      t.zf = some (VG.Proof.Rsa.X86_64.WordDivide.guardVal ((k + 7) / 8) k pb.length qb.length
        (nb[0]'(by rw [h.nl]; have := h.k1; omega)) == 0) ∧ Keep mmRegs s t := by
  have hz := h.zk
  have hk := h.k1
  have hnl : 0 < nb.length := by rw [h.nl]; omega_using [hk]
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = s.mem ∧
    t.zf = some (VG.Proof.Rsa.X86_64.WordDivide.guardVal ((k + 7) / 8) k pb.length qb.length (nb[0]'hnl) == 0)) (by
    xrun [WordValidation.guardTail, State.ea, hdr, h.rdi, h12, hdx, hdrOff,
      h.scr.ld (d := 8 * sK) (by change 8 * 18 + 8 ≤ Z; omega_using [hz, hk]),
      h.scr.ld (d := 8 * CheckKey.sPlen) (by change 8 * 24 + 8 ≤ Z; omega_using [hz, hk]),
      h.scr.ld (d := 8 * CheckKey.sQlen) (by change 8 * 26 + 8 ≤ Z; omega_using [hz, hk]),
      h.hK, h.hPl, h.hQl, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      show InRegions (s.rd ++ s.wr) np 1 by simpa using h.srN.rd 0 hnl,
      show s.mem np = nb[0] from by simpa using h.srN.val 0 hnl,
      VG.Proof.Rsa.X86_64.WordDivide.guardVal]
    rfl) rfl) fun t ⟨⟨hm, hzf⟩, hkeep⟩ => ⟨h.same hm hkeep (by decide), hm, hzf, hkeep.mono (by decide)⟩

/-- Accepted factors selected by the public guard fill their half-width moduli. -/
theorem validationFactors {s : State} {B : Addr} {Z k : Nat} {np pd pp pq pdp pdq pqi : Addr}
    {nb db pb qb dpb dqb qib : List Byte} {ev : Nat}
    (h : MainPre s B Z k np pd pp pq pdp pdq pqi nb db pb qb dpb dqb qib ev)
    (hg : VG.Proof.Rsa.X86_64.WordDivide.guardVal ((k + 7) / 8) k pb.length qb.length
      (nb[0]'(by rw [h.nl]; have := h.k1; omega)) = 0)
    (he : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb) :
    (2 ^ (64 * (((k + 7) / 8) / 2) - 1) ≤ Spec.Rsa.os2ip pb ∧
      Spec.Rsa.os2ip pb < 2 ^ (64 * (((k + 7) / 8) / 2))) ∧
    (2 ^ (64 * (((k + 7) / 8) / 2) - 1) ≤ Spec.Rsa.os2ip qb ∧
      Spec.Rsa.os2ip qb < 2 ^ (64 * (((k + 7) / 8) / 2))) := by
  have hk := h.k2
  have hp := h.pl2
  have hq := h.ql2
  have hw : (k + 7) / 8 < 2 ^ 24 := by omega_using [hk]
  obtain ⟨hw2, hwk, hpk, hpq, hb⟩ := VG.Proof.Rsa.X86_64.WordDivide.guard_zero hw
    (by omega_using [hk]) (by omega_using [hk, hp]) (by omega_using [hk, hq]) hg
  have hbits : 64 * (((k + 7) / 8) / 2) = 32 * ((k + 7) / 8) := by omega_using [hw2]
  have ep : 8 * pb.length = 64 * (((k + 7) / 8) / 2) := by omega_using [hbits, hpk, hwk]
  have eq : 8 * qb.length = 64 * (((k + 7) / 8) / 2) := by omega_using [ep, hpq]
  have pbound := os2ip_lt pb
  have qbound := os2ip_lt qb
  rw [pow256_eq, ep] at pbound
  rw [pow256_eq, eq] at qbound
  have nbnd := VG.Proof.Rsa.os2ip_high (by rw [h.nl]; have := h.k1; omega) hb
  rw [h.nl, show 8 * k - 1 = 2 * (64 * (((k + 7) / 8) / 2)) - 1 by omega_using [hwk, hbits]] at nbnd
  have npos : 1 ≤ 64 * (((k + 7) / 8) / 2) := by have := h.k1; omega_using [this, hwk, hbits]
  have fb := VG.Proof.Rsa.balanced_factor npos pbound qbound nbnd he
  exact ⟨⟨Nat.le_trans fb.1 (Nat.sub_le _ _), pbound⟩, Nat.le_trans fb.2 (Nat.sub_le _ _), qbound⟩

end VG.Proof.Rsa.X86_64.Key
