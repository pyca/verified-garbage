import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps

/-!
# `vg_rsa_check_key` on x86-64: the checks modulo `X - 1`

`modChecks sX sXlen sDX` for the prime `X` and its exponent `dX`: `sMask`
and'ed with the masks of `dX < M`, `R₁ = 1` and `R₂ = 1`, for `M = X - 1`
(when `X > 0`) and the remainders `R₁ = e d mod M` and `R₂ = e dX mod M`
(when `M > 0`) (`modChecks_ok`).
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

theorem wsa {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s : State} {Q : State → Prop}
    (h : WP isa (seqs a) s fun t => WP isa (seqs b) t Q) : WP isa (seqs (a ++ b)) s Q :=
  wp_seqs_append ha hb h

theorem modChecks_ok {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (h : KCtx s t B Z w minv N) {b : Bool} (hm : word t.mem B (8 * sMask) = mask b)
    {sX sXlen sDX : Nat} (hsX : sX < 32) (hsXl : sXlen < 32) (hsDX : sDX < 32)
    (nX : sX ≠ sMask) (nXl : sXlen ≠ sMask) (nDX : sDX ≠ sMask)
    {px pdx pd : Addr} {xb dxb db : List Byte}
    (hpx : word s.mem B (8 * sX) = px) (hxl : word s.mem B (8 * sXlen) = BitVec.ofNat 64 xb.length)
    (hpdx : word s.mem B (8 * sDX) = pdx) (hpd : word s.mem B (8 * sD) = pd)
    (hdl : word s.mem B (8 * sDlen) = BitVec.ofNat 64 db.length)
    (srcX : Src s B Z px xb) (srcDX : Src s B Z pdx dxb) (srcD : Src s B Z pd db)
    (hdxl : dxb.length = xb.length) (hx1 : 1 ≤ xb.length) (hxk : xb.length ≤ 8 * w)
    (hd1 : 1 ≤ db.length) (hdk : db.length ≤ 8 * w) :
    WP isa (seqs (modChecks sX sXlen sDX)) t fun t' => KCtx s t' B Z w minv N ∧
      ∃ M R1 R2 : Nat, (0 < Spec.Rsa.os2ip xb → M = Spec.Rsa.os2ip xb - 1) ∧
        (0 < M → R1 = (word s.mem B (8 * sEv)).toNat * Spec.Rsa.os2ip db % M) ∧
        (0 < M → R2 = (word s.mem B (8 * sEv)).toNat * Spec.Rsa.os2ip dxb % M) ∧
        word t'.mem B (8 * sMask) =
          mask (b && decide (Spec.Rsa.os2ip dxb < M) && decide (R1 = 1) && decide (R2 = 1)) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  simp only [modChecks, List.append_assoc]
  refine wsa (by simp [loadNum]) (by simp [decM]) (WP.mono (loadK h (j := aM) (by decide) (by decide)
    (by decide) hsX hsXl nX nXl hpx hxl srcX hx1 hxk) fun t₁ ⟨h₁, v₁, a₁⟩ => ?_)
  refine wsa (by simp [decM]) (by simp [loadNum]) (WP.mono (decK h₁) fun t₂ ⟨h₂, v₂, a₂⟩ => ?_)
  rw [v₁] at v₂
  -- `M`, from here on.
  refine wsa (by simp [loadNum]) (by simp [ltMask]) (WP.mono (loadK h₂ (j := aX) (by decide) (by decide)
    (by decide) hsDX hsXl nDX nXl hpdx (by rw [hdxl]; exact hxl) srcDX (by omega) (by omega))
    fun t₃ ⟨h₃, v₃, a₃⟩ => ?_)
  have M₃ : wv t₃.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := Arrays.wv_other a₃ (by decide) (by decide) hZ hn
  refine wsa (by simp [ltMask]) (by simp [loadNum]) (WP.mono (ltK h₃ (a := aX) (b := aM) (by decide) (by decide))
    fun t₄ ⟨h₄, m₄, o₄⟩ => ?_)
  rw [v₃, M₃, Arrays.mask_eq a₃ hn hZ, Arrays.mask_eq a₂ hn hZ, Arrays.mask_eq a₁ hn hZ, hm, mask_and'] at m₄
  have M₄ : wv t₄.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := by
    rw [Outside.wv_arr o₄ (by decide) hZ hn (by omega), M₃]
  refine wsa (by simp [loadNum]) (by simp [mulE]) (WP.mono (loadK h₄ (j := aX) (by decide) (by decide)
    (by decide) (show sD < 32 by decide) (show sDlen < 32 by decide) (by decide) (by decide) hpd hdl srcD hd1 hdk)
    fun t₅ ⟨h₅, v₅, a₅⟩ => ?_)
  have M₅ : wv t₅.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := by
    rw [Arrays.wv_other a₅ (by decide) (by decide) hZ hn, M₄]
  refine wsa (by simp [mulE]) (by simp [reduce]) (WP.mono (mulEK h₅) fun t₆ ⟨h₆, v₆, a₆⟩ => ?_)
  have M₆ : wv t₆.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := by
    rw [Arrays.wv_other a₆ (by decide) (by decide) hZ hn, M₅]
  refine wsa (by simp [reduce]) (by simp [eqOne]) (WP.mono (reduceEK h₆) fun t₇ ⟨h₇, v₇, a₇⟩ => ?_)
  rw [M₆, v₆, v₅] at v₇
  have M₇ : wv t₇.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := by
    rw [Arrays.wv_other a₇ (by decide) (by decide) hZ hn, M₆]
  refine wsa (by simp [eqOne]) (by simp [loadNum]) (WP.mono (eqOneK h₇) fun t₈ ⟨h₈, m₈, o₈⟩ => ?_)
  rw [Arrays.mask_eq a₇ hn hZ, Arrays.mask_eq a₆ hn hZ, Arrays.mask_eq a₅ hn hZ, m₄, mask_and'] at m₈
  have M₈ : wv t₈.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := by
    rw [Outside.wv_arr o₈ (by decide) hZ hn (by omega), M₇]
  refine wsa (by simp [loadNum]) (by simp [mulE]) (WP.mono (loadK h₈ (j := aX) (by decide) (by decide)
    (by decide) hsDX hsXl nDX nXl hpdx (by rw [hdxl]; exact hxl) srcDX (by omega) (by omega))
    fun t₉ ⟨h₉, v₉, a₉⟩ => ?_)
  have M₉ : wv t₉.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := by
    rw [Arrays.wv_other a₉ (by decide) (by decide) hZ hn, M₈]
  refine wsa (by simp [mulE]) (by simp [reduce]) (WP.mono (mulEK h₉) fun t₁₀ ⟨h₁₀, v₁₀, a₁₀⟩ => ?_)
  have M₁₀ : wv t₁₀.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := by
    rw [Arrays.wv_other a₁₀ (by decide) (by decide) hZ hn, M₉]
  refine wsa (by simp [reduce]) (by simp [eqOne]) (WP.mono (reduceEK h₁₀) fun t₁₁ ⟨h₁₁, v₁₁, a₁₁⟩ => ?_)
  rw [M₁₀, v₁₀, v₉] at v₁₁
  refine WP.mono (eqOneK h₁₁) fun t₁₂ ⟨h₁₂, m₁₂, _⟩ => ⟨h₁₂, wv t₂.mem B (slot w aM) w, wv t₇.mem B (slot w aR) w,
    wv t₁₁.mem B (slot w aR) w, fun hx => by have := v₂ hx; omega, v₇, v₁₁, ?_⟩
  rw [m₁₂, Arrays.mask_eq a₁₁ hn hZ, Arrays.mask_eq a₁₀ hn hZ, Arrays.mask_eq a₉ hn hZ, m₈, mask_and']

end VG.Proof.Rsa.X86_64.Key
