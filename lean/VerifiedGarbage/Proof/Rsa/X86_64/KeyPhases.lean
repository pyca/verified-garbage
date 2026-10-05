import VerifiedGarbage.Proof.Rsa.X86_64.KeyMod

/-!
# `vg_rsa_check_key` on x86-64: the checks but those modulo `X - 1`

In the checks' context (`KCtx`), each phase of `main` and'ed into `sMask`:
`d < n` (`dLtN_ok`), `p q = n` (`pqN_ok`), and `qInv < p` and
`qInv q mod p = 1` (`qInv_ok`).
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

section
variable {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}

theorem eqCheckK (h : KCtx s t B Z w minv N) :
    WP isa (seqs VG.Impl.Rsa.X86_64.Crt.eqCheck) t fun t' => KCtx s t' B Z w minv N ∧
      word t'.mem B (8 * sMask) = word t.mem B (8 * sMask) &&&
        mask (decide (wv t.mem B (slot w aAcc) (2 * w + 2) = N)) ∧
      Outside B (8 * sMask) 8 t.mem t'.mem :=
  WP.mono (eqCheck_ok h.good h.hZ h.w1 (by have := h.w2; omega)) fun _ ⟨hv, ho, hk⟩ =>
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
    WP isa (seqs (loadNum aX sP sPlen ++ loadNum aR sQ sQlen ++ mulXR ++ VG.Impl.Rsa.X86_64.Crt.eqCheck)) t fun t' =>
      KCtx s t' B Z w minv N ∧
      word t'.mem B (8 * sMask) = mask (b && decide (Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = N)) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  simp only [List.append_assoc]
  refine wsa (by simp [loadNum]) (by simp [loadNum]) (WP.mono (loadK h (j := aX) (by decide) (by decide)
    (by decide) (show sP < 32 by decide) (show sPlen < 32 by decide) (by decide) (by decide) hpp hpl srP hp1 hpk)
    fun t₁ ⟨h₁, v₁, a₁⟩ => ?_)
  refine wsa (by simp [loadNum]) (by simp [mulXR]) (WP.mono (loadK h₁ (j := aR) (by decide) (by decide)
    (by decide) (show sQ < 32 by decide) (show sQlen < 32 by decide) (by decide) (by decide) hpq hql srQ hq1 hqk)
    fun t₂ ⟨h₂, v₂, a₂⟩ => ?_)
  rw [← Arrays.wv_other a₂ (by decide) (by decide) hZ hn] at v₁
  refine wsa (by simp [mulXR]) (by simp [VG.Impl.Rsa.X86_64.Crt.eqCheck]) (WP.mono (mulXRK h₂) fun t₃ ⟨h₃, v₃, a₃⟩ => ?_)
  refine WP.mono (eqCheckK h₃) fun t₄ ⟨h₄, m₄, _⟩ => ⟨h₄, ?_⟩
  rw [m₄, v₃, v₁, v₂, Arrays.mask_eq a₃ hn hZ, Arrays.mask_eq a₂ hn hZ, Arrays.mask_eq a₁ hn hZ, hm, mask_and']

/-- `qInv < p` and `qInv q mod p = 1`. -/
theorem qInv_ok (h : KCtx s t B Z w minv N) {b : Bool} (hm : word t.mem B (8 * sMask) = mask b)
    {pp pq pqi : Addr} {pb qb qib : List Byte} (hpp : word s.mem B (8 * sP) = pp)
    (hpl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pb.length) (hpq : word s.mem B (8 * sQ) = pq)
    (hql : word s.mem B (8 * sQlen) = BitVec.ofNat 64 qb.length) (hpqi : word s.mem B (8 * sQI) = pqi)
    (srP : Src s B Z pp pb) (srQ : Src s B Z pq qb) (srQI : Src s B Z pqi qib) (hqil : qib.length = pb.length)
    (hp1 : 1 ≤ pb.length) (hpk : pb.length ≤ 8 * w) (hq1 : 1 ≤ qb.length) (hqk : qb.length ≤ 8 * w) :
    WP isa (seqs (loadNum aM sP sPlen ++ loadNum aX sQI sPlen ++ ltMask aX aM ++
        loadNum aR sQ sQlen ++ mulXR ++ reduce cntXR ++ eqOne)) t fun t' =>
      KCtx s t' B Z w minv N ∧ ∃ R : Nat,
        (0 < Spec.Rsa.os2ip pb → R = Spec.Rsa.os2ip qib * Spec.Rsa.os2ip qb % Spec.Rsa.os2ip pb) ∧
        word t'.mem B (8 * sMask) =
          mask (b && decide (Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) && decide (R = 1)) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  simp only [List.append_assoc]
  refine wsa (by simp [loadNum]) (by simp [loadNum]) (WP.mono (loadK h (j := aM) (by decide) (by decide)
    (by decide) (show sP < 32 by decide) (show sPlen < 32 by decide) (by decide) (by decide) hpp hpl srP hp1 hpk)
    fun t₁ ⟨h₁, v₁, a₁⟩ => ?_)
  refine wsa (by simp [loadNum]) (by simp [ltMask]) (WP.mono (loadK h₁ (j := aX) (by decide) (by decide)
    (by decide) (show sQI < 32 by decide) (show sPlen < 32 by decide) (by decide) (by decide) hpqi
    (by rw [hqil]; exact hpl) srQI (by omega) (by omega)) fun t₂ ⟨h₂, v₂, a₂⟩ => ?_)
  rw [← Arrays.wv_other a₂ (by decide) (by decide) hZ hn] at v₁
  refine wsa (by simp [ltMask]) (by simp [loadNum]) (WP.mono (ltK h₂ (a := aX) (b := aM) (by decide) (by decide))
    fun t₃ ⟨h₃, m₃, o₃⟩ => ?_)
  rw [v₁, v₂, Arrays.mask_eq a₂ hn hZ, Arrays.mask_eq a₁ hn hZ, hm, mask_and'] at m₃
  rw [← Outside.wv_arr o₃ (by decide) hZ hn (by omega)] at v₁ v₂
  refine wsa (by simp [loadNum]) (by simp [mulXR]) (WP.mono (loadK h₃ (j := aR) (by decide) (by decide)
    (by decide) (show sQ < 32 by decide) (show sQlen < 32 by decide) (by decide) (by decide) hpq hql srQ hq1 hqk)
    fun t₄ ⟨h₄, v₄, a₄⟩ => ?_)
  rw [← Arrays.wv_other a₄ (by decide) (by decide) hZ hn] at v₁ v₂
  refine wsa (by simp [mulXR]) (by simp [reduce]) (WP.mono (mulXRK h₄) fun t₅ ⟨h₅, v₅, a₅⟩ => ?_)
  rw [← Arrays.wv_other a₅ (by decide) (by decide) hZ hn] at v₁
  refine wsa (by simp [reduce]) (by simp [eqOne]) (WP.mono (reduceXRK h₅) fun t₆ ⟨h₆, v₆, a₆⟩ => ?_)
  refine WP.mono (eqOneK h₆) fun t₇ ⟨h₇, m₇, _⟩ => ⟨h₇, wv t₆.mem B (slot w aR) w,
    fun hp => by rw [v₆ (by rw [v₁]; exact hp), v₅, v₁, v₂, v₄], ?_⟩
  rw [m₇, Arrays.mask_eq a₆ hn hZ, Arrays.mask_eq a₅ hn hZ, Arrays.mask_eq a₄ hn hZ, m₃, mask_and']

end

end VG.Proof.Rsa.X86_64.Key
