import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-!
# RSA with the CRT on x86-64: `c^d mod X`

In a prime's phase, from `c G mod n` in the modulus' `Y` and `R_X mod X` in
the prime's: `c R_X mod X` by `redc`, then `Y := Y^d` (`powPhase_ok`):
`c^d R_X mod X` if `X` divides `n`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The prime's `-X⁻¹`, `X` and 1 past a change within `crtExpRanges`. -/
theorem XVals.of_exp {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {X : Nat}
    (h : XVals s B o wx mx X) (hf : Frm (off B o) (crtExpRanges wx) s.mem t.mem)
    (hz : (off B o).toNat + slot wx 8 ≤ 2 ^ 64) : XVals t B o wx mx X := by
  have rN := crtExpRanges_arr wx (j := Public.aN) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rO := crtExpRanges_arr wx (j := Public.aOne) (by decide) (by decide) (by decide) (by decide) (by decide)
  have lN := slot_le (w := wx) (show Public.aN < 8 by decide)
  have lO := slot_le (w := wx) (show Public.aOne < 8 by decide)
  exact ⟨by rw [hf.wv_eq (fun r hr => by have := rN r hr; omega) (by omega)]; exact h.n,
    by rw [hf.word_eq (fun r hr => by have := rN r hr; omega) (by omega)]; exact h.inv,
    by rw [hf.wv_eq (fun r hr => by have := rO r hr; omega) (by omega)]; exact h.one⟩

/-- From the modulus' workspace, `c G mod N` in its `Y` and `R_X mod X` in
the prime's: the prime's `Y := c^d R_X mod X` if `X` divides `N`, `d` the
bytes whose pointer and length are in the modulus' header slots `sd` and
`slen`. Ends in the prime's workspace. -/
theorem powPhase_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X C : Nat}
    {sl o wx sd slen : Nat} {ep : Addr} {eb : List Byte}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hsl : sl < 32) (hslv : word s.mem B (8 * sl) = off B o)
    (hws : WsAt s.mem B o wx mx) (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hnY : wv s.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N)
    (hyl : wv s.mem (off B o) (slot wx Public.aY) wx < X)
    (hyc : X ∣ N → wv s.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X)
    (hsd : sd < 32) (hsln : slen < 32) (hep : word s.mem B (8 * sd) = ep)
    (hel : word s.mem B (8 * slen) = BitVec.ofNat 64 eb.length) (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024)
    (he : Src s B Z ep eb) :
    WP isa (seqs (([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ redc M.mm Public.aY ++ Crt.expLoop M.mm sd slen)) s
      fun t => SubCtx t B Z o w wx mx ∧ XVals t B o wx mx X ∧
        wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
        (X ∣ N → wv t.mem (off B o) (slot wx Public.aY) wx % X = C ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
        word t.mem (off B o) (8 * sMaskX) = word s.mem (off B o) (8 * sMaskX) ∧
        Frm B [xRange o wx] s.mem t.mem ∧ Keep (mmRegs ++ ([.rdi] : List Reg)) s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [redc]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl)
    fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ?_
  have hc₁ : SubCtx s₁ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k₁.2.2) (by rw [hm₁]; exact hg.hdr) (by rw [hm₁]; exact hws) hdi₁ hlo hhi
  have hX₁ : XVals s₁ B o wx mx X := ⟨by rw [hm₁]; exact hX.n, by rw [hm₁]; exact hX.inv, by rw [hm₁]; exact hX.one⟩
  refine wp_seqs_append (by simp [redc]) (by simp [Crt.expLoop]) ?_
  refine WP.mono (redc_ok M hc₁ hX₁ hwx2 hwx (by omega) hX1 (j := Public.aY) (by decide))
    fun s₂ ⟨hc₂, hX₂, hlt₂, hv₂, f₂, k₂⟩ => ?_
  have fx₂ : Frm B [xRange o wx] s₁.mem s₂.mem := f₂.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  have hb₂ : ∀ d, d + 8 ≤ o → word s₂.mem B d = word s.mem B d := fun d hd => by
    rw [fx₂.x_below hd ho64, hm₁]
  have hY₂ : wv s₂.mem (off B o) (slot wx Public.aY) wx = wv s.mem (off B o) (slot wx Public.aY) wx := by
    have rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have := slot_le (w := wx) (show Public.aY < 8 by decide)
    have := hc₁.good.scr.nowrap
    rw [f₂.wv_eq (fun r hr => by have := rY r hr; omega) (by omega), hm₁]
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  have hsrc₂ : Src s₂ B Z ep eb := he.congrK (rs := mmRegs ++ [.rdi]) (by
    rw [← hm₁] at *
    exact InScr.of_frm fx₂ fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega)
    ((k₁.trans k₂).mono (by decide))
  -- The exponent's base and the start, in Montgomery form (any, if `X` does not divide `N`).
  obtain ⟨x, y, hxc, hyc', hval⟩ : ∃ x y : Nat,
      wv s₂.mem (off B o) (slot wx aXc) wx % X = x * 2 ^ (64 * wx) % X ∧
      wv s₂.mem (off B o) (slot wx Public.aY) wx % X = y * 2 ^ (64 * wx) % X ∧
      (X ∣ N → x = C ∧ y = 1) := by
    by_cases hd : X ∣ N
    · refine ⟨C, 1, ?_, by rw [hY₂, hyc hd, Nat.one_mul], fun _ => ⟨rfl, rfl⟩⟩
      apply VG.Proof.Bignum.redc_cancel hR
      rw [Nat.pow_mul] at hv₂
      rw [hv₂, hm₁, ← Nat.mod_mod_of_dvd _ hd, hnY, Nat.mod_mod_of_dvd _ hd, ← Nat.pow_mul]
    · obtain ⟨x, hx⟩ := VG.Proof.Bignum.exists_mont hR (by omega) (wv s₂.mem (off B o) (slot wx aXc) wx)
      obtain ⟨y, hy⟩ := VG.Proof.Bignum.exists_mont hR (by omega)
        (wv s₂.mem (off B o) (slot wx Public.aY) wx)
      exact ⟨x, y, hx, hy, fun h => absurd h hd⟩
  refine WP.mono (crtExpLoop_ok M hc₂ hwx2 hwx (by omega) hX₂.n hX₂.inv hXodd hlt₂ hxc
    (by rw [hY₂]; exact hyl) hyc' hsd hsln (by rw [hb₂ _ (by omega)]; exact hep)
    (by rw [hb₂ _ (by omega)]; exact hel) hL1 hL2 hsrc₂) fun t ⟨hc, hlt, hv, f₃, k₃⟩ => ?_
  refine ⟨hc, hX₂.of_exp f₃ (by have := hc₂.good.scr.nowrap; omega), hlt, fun hd => ?_, ?_, ?_,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · obtain ⟨rfl, rfl⟩ := hval hd
    rw [hv, Nat.one_pow, Nat.one_mul]
  · rw [f₃.word_eq (fun r hr => by
      simp only [crtExpRanges, crtBitRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hdr_lt_slot wx Public.aAcc (show 31 < 32 by decide)
      have := hdr_lt_slot wx Public.aTmp (show 31 < 32 by decide)
      have := hdr_lt_slot wx Public.aY (show 31 < 32 by decide)
      have := hdr_lt_slot wx aT (show 31 < 32 by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sMaskX, Crt.sExp, Crt.sExpLen, Crt.sI, Crt.sV, Crt.sBit, sFn] <;> omega)
      (by unfold sMaskX sFn; omega), f₂.word_eq (sMaskX_redc wx) (by unfold sMaskX sFn; omega), hm₁]
  · rw [← hm₁]
    exact fx₂.trans (f₃.to_x (crtExpRanges_ok wx) hoL (List.mem_singleton_self _))

end VG.Proof.Bignum.X86_64
