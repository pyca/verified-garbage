import VerifiedGarbage.Proof.Rsa.X86_64.KeyPhases
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyReduce
import VerifiedGarbage.Proof.Rsa.Octets

/-!
# `vg_rsa_check_crt_key` on x86-64: the checks with remainders

In the checks' context (`KCtx`), the phases of `vg_rsa_check_crt_key`'s
`main` that compute a remainder by `reduceTop`, and'ed into `sMask`:
`dX < X - 1` and `e dX mod (X - 1) = 1` (`crtModChecks_ok`), and `qInv < p`
and `qInv q mod p = 1` (`crtQInv_ok`). Each remainder is known when the
comparison before it holds, which bounds its quotient.
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

theorem topE_ok (t : State) :
    WP isa (.block Impl.Rsa.X86_64.CheckCrtKey.topE) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 1 ∧
      t'.mem = t.mem ∧ Keep [.r13] t t' := by
  refine WP.mono (WP.keep [.r13] (Q := fun t' => t'.gpr .r13 = BitVec.ofNat 64 1 ∧ t'.mem = t.mem)
    (by xrun [Impl.Rsa.X86_64.CheckCrtKey.topE]) rfl) fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩

theorem topQ_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) {ql : Nat} (hql : word t.mem B (8 * sQlen) = BitVec.ofNat 64 ql) (hq : ql < 2 ^ 32) :
    WP isa (.block Impl.Rsa.X86_64.CheckCrtKey.topQ) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 ((ql + 7) / 8) ∧
      t'.mem = t.mem ∧ Keep [.r13] t t' := by
  have hn := hg.scr.nowrap
  refine WP.mono (WP.keep [.r13] (Q := fun t' => t'.gpr .r13 = BitVec.ofNat 64 ((ql + 7) / 8) ∧ t'.mem = t.mem)
    (by xrun [Impl.Rsa.X86_64.CheckCrtKey.topQ, State.ea, hdr, hg.rdi, hdrOff,
      hg.scr.ld (d := 8 * sQlen) (by have := hdr_lt_slot w 8 (show sQlen < 32 by decide); omega), hql,
      shr3_w ql hq]) rfl) fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩

section
variable {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}

/-- `reduceTop` in the checks' context. -/
theorem reduceTopK (h : KCtx s t B Z w minv N) {sl : Nat} {top : List Instr} {L c Nx : Nat}
    (hsl : sl < 32) (hsl' : sl ≠ sMask) (hLs : word s.mem B (8 * sl) = BitVec.ofNat 64 L) (hL1 : 1 ≤ L)
    (hLw : L ≤ 8 * w)
    (htop : ∀ t' : State, Good t' B Z w minv → (∀ i < 32, word t'.mem B (8 * i) = word t.mem B (8 * i)) →
      WP isa (.block top) t' fun t'' => t''.gpr .r13 = BitVec.ofNat 64 c ∧ t''.mem = t'.mem ∧ Keep [.r13] t' t'')
    (hc : 1 ≤ c) (hcN : c + (L + 7) / 8 ≤ Nx) (hN : Nx ≤ 2 * w + 4) :
    WP isa (seqs (Impl.Rsa.X86_64.CheckCrtKey.reduceTop sl top)) t fun t' => KCtx s t' B Z w minv N ∧
      (wv t.mem B (slot w aM) w < 2 ^ (64 * ((L + 7) / 8)) → 0 < wv t.mem B (slot w aM) w →
        wv t.mem B (slot w aAcc + 8 * c) (Nx - c) < wv t.mem B (slot w aM) w →
        wv t'.mem B (slot w aR) w = wv t.mem B (slot w aAcc) Nx % wv t.mem B (slot w aM) w) ∧
      Arrays B w [aR, aX, aT] t.mem t'.mem :=
  WP.mono (reduceTop_ok h.good h.hZ h.w1 h.w2 hsl (by rw [h.hdr sl hsl hsl']; exact hLs) hL1 hLw htop hc hcN hN)
    fun _ ⟨_, hv, ha, hk⟩ => ⟨h.arr ha (by decide) (by decide) (by decide) hk, hv, ha⟩

/-- A number of `n + 1` words below `2^64 M` has its words from 1 up below
`M`. -/
theorem top_lt {m : Mem} {p : Addr} {d n M : Nat} (h : wv m p d (1 + n) < 2 ^ (64 * 1) * M) :
    wv m p (d + 8 * 1) n < M := by
  rw [wv_add] at h
  rcases Nat.lt_or_ge (wv m p (d + 8 * 1) n) M with h' | h'
  · exact h'
  · have := Nat.mul_le_mul_left (2 ^ (64 * 1)) h'; omega

/-- The words from `c` up of a number below `2^(64 c) M`. -/
theorem top_lt' {m : Mem} {p : Addr} {d c n M : Nat} (h : wv m p d (c + n) < 2 ^ (64 * c) * M) :
    wv m p (d + 8 * c) n < M := by
  rw [wv_add] at h
  rcases Nat.lt_or_ge (wv m p (d + 8 * c) n) M with h' | h'
  · exact h'
  · have := Nat.mul_le_mul_left (2 ^ (64 * c)) h'; omega

theorem pow_len_le (L : Nat) : 256 ^ L ≤ 2 ^ (64 * ((L + 7) / 8)) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The checks modulo `X - 1`: `sMask` and'ed with the masks of `dX < M` and
`R = 1`, for `M = X - 1` and `R = e dX mod M` (when `X > 0` and
`dX < M`). -/
theorem crtModChecks_ok (h : KCtx s t B Z w minv N) {b : Bool} (hm : word t.mem B (8 * sMask) = mask b)
    {sX sXlen sDX : Nat} (hsX : sX < 32) (hsXl : sXlen < 32) (hsDX : sDX < 32)
    (nX : sX ≠ sMask) (nXl : sXlen ≠ sMask) (nDX : sDX ≠ sMask)
    {px pdx : Addr} {xb dxb : List Byte}
    (hpx : word s.mem B (8 * sX) = px) (hxl : word s.mem B (8 * sXlen) = BitVec.ofNat 64 xb.length)
    (hpdx : word s.mem B (8 * sDX) = pdx) (srcX : Src s B Z px xb) (srcDX : Src s B Z pdx dxb)
    (hdxl : dxb.length = xb.length) (hx1 : 1 ≤ xb.length) (hxk : xb.length ≤ 8 * w)
    (hev : (word s.mem B (8 * sEv)).toNat < 2 ^ 33) :
    WP isa (seqs (Impl.Rsa.X86_64.CheckCrtKey.modChecks sX sXlen sDX)) t fun t' => KCtx s t' B Z w minv N ∧
      ∃ M R : Nat, (0 < Spec.Rsa.os2ip xb → M = Spec.Rsa.os2ip xb - 1) ∧
        (0 < Spec.Rsa.os2ip xb → Spec.Rsa.os2ip dxb < M →
          R = (word s.mem B (8 * sEv)).toNat * Spec.Rsa.os2ip dxb % M) ∧
        word t'.mem B (8 * sMask) = mask (b && decide (Spec.Rsa.os2ip dxb < M) && decide (R = 1)) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have := h.w2
  simp only [Impl.Rsa.X86_64.CheckCrtKey.modChecks, List.append_assoc]
  refine wsa (by simp [loadNum]) (by simp [decM]) (WP.mono (loadK h (j := aM) (by decide) (by decide)
    (by decide) hsX hsXl nX nXl hpx hxl srcX hx1 hxk) fun t₁ ⟨h₁, v₁, a₁⟩ => ?_)
  refine wsa (by simp [decM]) (by simp [loadNum]) (WP.mono (decK h₁) fun t₂ ⟨h₂, v₂, a₂⟩ => ?_)
  rw [v₁] at v₂
  refine wsa (by simp [loadNum]) (by simp [ltMask]) (WP.mono (loadK h₂ (j := aX) (by decide) (by decide)
    (by decide) hsDX hsXl nDX nXl hpdx (by rw [hdxl]; exact hxl) srcDX (by omega) (by omega))
    fun t₃ ⟨h₃, v₃, a₃⟩ => ?_)
  have M₃ : wv t₃.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := Arrays.wv_other a₃ (by decide) (by decide) hZ hn
  refine wsa (by simp [ltMask]) (by simp [mulE]) (WP.mono (ltK h₃ (a := aX) (b := aM) (by decide) (by decide))
    fun t₄ ⟨h₄, m₄, o₄⟩ => ?_)
  rw [v₃, M₃, Arrays.mask_eq a₃ hn hZ, Arrays.mask_eq a₂ hn hZ, Arrays.mask_eq a₁ hn hZ, hm, mask_and'] at m₄
  have M₄ : wv t₄.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := by
    rw [Outside.wv_arr o₄ (by decide) hZ hn (by omega), M₃]
  have X₄ : wv t₄.mem B (slot w aX) w = Spec.Rsa.os2ip dxb := by
    rw [Outside.wv_arr o₄ (by decide) hZ hn (by omega), v₃]
  refine wsa (by simp [mulE]) (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop])
    (WP.mono (mulEK h₄) fun t₅ ⟨h₅, v₅, a₅⟩ => ?_)
  rw [X₄] at v₅
  have M₅ : wv t₅.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := by
    rw [Arrays.wv_other a₅ (by decide) (by decide) hZ hn, M₄]
  refine wsa (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop]) (by simp [eqOne])
    (WP.mono (reduceTopK h₅ (sl := sXlen) (top := Impl.Rsa.X86_64.CheckCrtKey.topE) (L := xb.length) (c := 1)
      (Nx := w + 2) hsXl nXl hxl hx1 hxk (fun t' _ _ => topE_ok t') (Nat.le_refl _) (by omega) (by omega))
    fun t₆ ⟨h₆, v₆, a₆⟩ => ?_)
  rw [M₅, v₅] at v₆
  refine WP.mono (eqOneK h₆) fun t₇ ⟨h₇, m₇, _⟩ => ⟨h₇, wv t₂.mem B (slot w aM) w, wv t₆.mem B (slot w aR) w,
    fun hx => by have := v₂ hx; omega, fun hx hlt => ?_, ?_⟩
  · have eM := v₂ hx
    have hM : wv t₂.mem B (slot w aM) w < 2 ^ (64 * ((xb.length + 7) / 8)) := by
      have := Proof.Rsa.lt_of_os2ip xb; have := pow_len_le xb.length; omega
    refine v₆ hM (by omega) (top_lt ?_)
    rw [show 1 + (w + 2 - 1) = w + 2 by omega, v₅]
    calc (word s.mem B (8 * sEv)).toNat * Spec.Rsa.os2ip dxb
        ≤ (word s.mem B (8 * sEv)).toNat * wv t₂.mem B (slot w aM) w := Nat.mul_le_mul_left _ (Nat.le_of_lt hlt)
      _ < 2 ^ (64 * 1) * wv t₂.mem B (slot w aM) w := by
          apply Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  · rw [m₇, Arrays.mask_eq a₆ hn hZ, Arrays.mask_eq a₅ hn hZ, m₄, mask_and']

/-- `qInv < p` and `qInv q mod p = 1`. -/
theorem crtQInv_ok (h : KCtx s t B Z w minv N) {b : Bool} (hm : word t.mem B (8 * sMask) = mask b)
    {pp pq pqi : Addr} {pb qb qib : List Byte} (hpp : word s.mem B (8 * sP) = pp)
    (hpl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pb.length) (hpq : word s.mem B (8 * sQ) = pq)
    (hql : word s.mem B (8 * sQlen) = BitVec.ofNat 64 qb.length) (hpqi : word s.mem B (8 * sQI) = pqi)
    (srP : Src s B Z pp pb) (srQ : Src s B Z pq qb) (srQI : Src s B Z pqi qib) (hqil : qib.length = pb.length)
    (hp1 : 1 ≤ pb.length) (hpk : pb.length ≤ 8 * w) (hq1 : 1 ≤ qb.length) (hqk : qb.length ≤ 8 * w) :
    WP isa (seqs (loadNum aM sP sPlen ++ loadNum aX sQI sPlen ++ ltMask aX aM ++
        loadNum aR sQ sQlen ++ mulXR ++ Impl.Rsa.X86_64.CheckCrtKey.reduceTop sPlen Impl.Rsa.X86_64.CheckCrtKey.topQ ++
        eqOne)) t fun t' =>
      KCtx s t' B Z w minv N ∧ ∃ R : Nat,
        (0 < Spec.Rsa.os2ip pb → Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb →
          R = Spec.Rsa.os2ip qib * Spec.Rsa.os2ip qb % Spec.Rsa.os2ip pb) ∧
        word t'.mem B (8 * sMask) =
          mask (b && decide (Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) && decide (R = 1)) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have := h.w2
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
  refine wsa (by simp [mulXR]) (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop])
    (WP.mono (mulXRK h₄) fun t₅ ⟨h₅, v₅, a₅⟩ => ?_)
  rw [← Arrays.wv_other a₅ (by decide) (by decide) hZ hn] at v₁
  rw [v₂, v₄] at v₅
  have hql' : qb.length < 2 ^ 32 := by omega
  refine wsa (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop]) (by simp [eqOne])
    (WP.mono (reduceTopK h₅ (sl := sPlen) (top := Impl.Rsa.X86_64.CheckCrtKey.topQ) (L := pb.length)
      (c := (qb.length + 7) / 8) (Nx := 2 * w + 2) (by decide) (by decide) hpl hp1 hpk
      (fun t' hg hh => topQ_ok hg hZ (by rw [hh _ (by decide), h₅.hdr _ (by decide) (by decide)]; exact hql) hql')
      (by omega) (by omega) (by omega))
    fun t₆ ⟨h₆, v₆, a₆⟩ => ?_)
  rw [v₁, v₅] at v₆
  refine WP.mono (eqOneK h₆) fun t₇ ⟨h₇, m₇, _⟩ => ⟨h₇, wv t₆.mem B (slot w aR) w, fun hp hlt => ?_, ?_⟩
  · have hM : Spec.Rsa.os2ip pb < 2 ^ (64 * ((pb.length + 7) / 8)) := by
      have := Proof.Rsa.lt_of_os2ip pb; have := pow_len_le pb.length; omega
    refine v₆ hM hp (top_lt' ?_)
    rw [show (qb.length + 7) / 8 + (2 * w + 2 - (qb.length + 7) / 8) = 2 * w + 2 by omega, v₅]
    have hq := Proof.Rsa.lt_of_os2ip qb
    have := pow_len_le qb.length
    calc Spec.Rsa.os2ip qib * Spec.Rsa.os2ip qb
        ≤ Spec.Rsa.os2ip qib * 2 ^ (64 * ((qb.length + 7) / 8)) := Nat.mul_le_mul_left _ (by omega)
      _ < Spec.Rsa.os2ip pb * 2 ^ (64 * ((qb.length + 7) / 8)) :=
          Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
      _ = 2 ^ (64 * ((qb.length + 7) / 8)) * Spec.Rsa.os2ip pb := Nat.mul_comm _ _
  · rw [m₇, Arrays.mask_eq a₆ hn hZ, Arrays.mask_eq a₅ hn hZ, Arrays.mask_eq a₄ hn hZ, m₃, mask_and']

end

end VG.Proof.Rsa.X86_64.Key
