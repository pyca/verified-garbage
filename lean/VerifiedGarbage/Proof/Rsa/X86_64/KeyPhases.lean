module
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKeyCore
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCtx

import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# `vg_rsa_check_key` on x86-64: `d < n` and `p q = n`

In the checks' context (`KCtx`), these phases of `main` and'ed into `sMask`:
`d < n` (`dLtN_ok`) and `p q = n` (`pqN_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

section
variable {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}

theorem eqCheckK (h : KCtx s t B Z w minv N) :
    WP isa (seqs VG.Impl.Rsa.X86_64.Crt.eqCheck) t fun t' => KCtx s t' B Z w minv N ∧
      word t'.mem B (8 * sMask) = word t.mem B (8 * sMask) &&&
        mask (decide (wv t.mem B (slot w aAcc) (2 * w + 2) = N)) ∧
      Outside B (8 * sMask) 8 t.mem t'.mem :=
  WP.mono (eqCheck_ok h.good h.hZ h.w1 (by have := h.w2; omega_using [this])) fun _ ⟨hv, ho, hk⟩ =>
    ⟨h.msk ho hk, by rw [hv, h.n], ho⟩

/-- `d < n`. -/
theorem dLtN_ok (h : KCtx s t B Z w minv N) {b : Bool} (hm : word t.mem B (8 * sMask) = mask b)
    {pd : Addr} {db : List Byte} (hpd : word s.mem B (8 * sD) = pd)
    (hdl : word s.mem B (8 * sDlen) = BitVec.ofNat 64 db.length) (src : Src s B Z pd db)
    (hd1 : 1 ≤ db.length) (hdk : db.length ≤ 8 * w) :
    WP isa (seqs (loadNum aX sD sDlen ++ ltMask aX aN)) t fun t' => KCtx s t' B Z w minv N ∧
      word t'.mem B (8 * sMask) = mask (b && decide (Spec.Rsa.os2ip db < N)) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  refine wsa (by simp [loadNum]) (by simp [ltMask]) (WP.mono (loadK h (j := aX) (by decide) (by decide)
    (by decide) (show sD < 32 by decide) (show sDlen < 32 by decide) (by decide) (by decide) hpd hdl src hd1 hdk)
    fun t₁ ⟨h₁, v₁, a₁⟩ => ?_)
  refine WP.mono (ltK h₁ (a := aX) (b := aN) (by decide) (by decide)) fun t₂ ⟨h₂, m₂, _⟩ => ⟨h₂, ?_⟩
  rw [m₂, v₁, h₁.n, Arrays.mask_eq a₁ hn hZ, hm, mask_and']

/-- `p q = n`. -/
theorem pqN_ok (h : KCtx s t B Z w minv N) {b : Bool} (hm : word t.mem B (8 * sMask) = mask b)
    {pp pq : Addr} {pb qb : List Byte} (hpp : word s.mem B (8 * sP) = pp)
    (hpl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pb.length) (hpq : word s.mem B (8 * sQ) = pq)
    (hql : word s.mem B (8 * sQlen) = BitVec.ofNat 64 qb.length) (srP : Src s B Z pp pb)
    (srQ : Src s B Z pq qb) (hp1 : 1 ≤ pb.length) (hpk : pb.length ≤ 8 * w) (hq1 : 1 ≤ qb.length)
    (hqk : qb.length ≤ 8 * w) :
    WP isa (seqs (loadNum aX sP sPlen ++ loadNum aR sQ sQlen ++ mulPQ ++ VG.Impl.Rsa.X86_64.Crt.eqCheck)) t fun t' =>
      KCtx s t' B Z w minv N ∧
      word t'.mem B (8 * sMask) = mask (b && decide (Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = N)) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  simp only [List.append_assoc]
  refine wsa (by simp [loadNum]) (by simp [loadNum]) (WP.mono (loadK h (j := aX) (by decide) (by decide)
    (by decide) (show sP < 32 by decide) (show sPlen < 32 by decide) (by decide) (by decide) hpp hpl srP hp1 hpk)
    fun t₁ ⟨h₁, v₁, a₁⟩ => ?_)
  refine wsa (by simp [loadNum]) (by simp [mulPQ]) (WP.mono (loadK h₁ (j := aR) (by decide) (by decide)
    (by decide) (show sQ < 32 by decide) (show sQlen < 32 by decide) (by decide) (by decide) hpq hql srQ hq1 hqk)
    fun t₂ ⟨h₂, v₂, a₂⟩ => ?_)
  rw [← Arrays.wv_other a₂ (by decide) (by decide) hZ hn] at v₁
  -- `p` and `q` are their low `⌈len / 8⌉` words.
  have low : ∀ {bs : List Byte} {j : Nat}, wv t₂.mem B (slot w j) w = Spec.Rsa.os2ip bs → bs.length ≤ 8 * w →
      wv t₂.mem B (slot w j) ((bs.length + 7) / 8) = Spec.Rsa.os2ip bs := fun {bs j} v hk => by
    rw [wv_low_of_lt (v := (bs.length + 7) / 8) (w := w) (by omega_using [hk]) (by
      rw [v]; exact Nat.lt_of_lt_of_le (os2ip_lt bs) (by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega_using []))), v]
  refine wsa (by simp [mulPQ]) (by simp [VG.Impl.Rsa.X86_64.Crt.eqCheck])
    (WP.mono (mulPQK h₂ hpl hql hp1 hq1 hpk hqk) fun t₃ ⟨h₃, v₃, a₃⟩ => ?_)
  refine WP.mono (eqCheckK h₃) fun t₄ ⟨h₄, m₄, _⟩ => ⟨h₄, ?_⟩
  rw [m₄, v₃, low v₁ hpk, low v₂ hqk, Arrays.mask_eq a₃ hn hZ, Arrays.mask_eq a₂ hn hZ, Arrays.mask_eq a₁ hn hZ, hm, mask_and']

end

end VG.Proof.Rsa.X86_64.Key
