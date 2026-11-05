module

public import VerifiedGarbage.Proof.Rsa.X86_64.CvCheck
import VerifiedGarbage.Proof.Rsa.WordFactors
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.R2

/-! # Public dispatch for word-based CRT exponent remainders -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The public guard's accumulated mismatches. -/
def guardVal (W k pl ql : Nat) (b : Byte) : BitVec 64 :=
  (((((BitVec.ofNat 64 W &&& 1#64) ||| ((BitVec.ofNat 64 W <<< 3) ^^^ BitVec.ofNat 64 k)) |||
      ((BitVec.ofNat 64 pl <<< 1) ^^^ BitVec.ofNat 64 k)) |||
      (BitVec.ofNat 64 pl ^^^ BitVec.ofNat 64 ql)) ||| ((b.zeroExtend 64 >>> 7) ^^^ 1#64))

/-- The first block loads only public workspace dimensions and `n`'s address. -/
theorem guardHead_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) :
    WP isa (.block wordGuardHead) s fun t =>
      CvS I m₀ t ∧ t.mem = s.mem ∧ t.gpr .r12 = BitVec.ofNat 64 (wk I.k) ∧ t.gpr .rdx = I.pN := by
  have hz := h.ws.h256
  unfold wordGuardHead
  rw [WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₁ ⟨h12, _, m₁, k₁⟩ => ?_
  have hs := h.ws.scr.congr k₁.2.2
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = I.pN ∧ t.mem = s₁.mem) (by
    xrun [State.ea, hdr, (k₁.gpr (by decide) : s₁.gpr .rdi = _), h.ws.rdi, hdrOff,
      hs.ld (d := 8 * Public.sN) (by change 8 * 17 + 8 ≤ I.Z; omega_using [hz]), m₁, h.args.n]) rfl) fun t ⟨⟨hdx, m₂⟩, k₂⟩ => ?_
  have mm := m₂.trans m₁
  exact ⟨h.step (rs := []) (by rw [mm]; exact Frm.refl _ _ _) (by simp) (by simp)
    (k₁.trans k₂) (by decide), mm, (k₂.gpr (by decide)).trans h12, hdx⟩

/-- The tail reads public lengths and the first byte of the public modulus. -/
theorem guardTail_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (wk I.k)) (hdx : s.gpr .rdx = I.pN) :
    WP isa (.block wordGuardTail) s fun t =>
      CvS I m₀ t ∧ t.mem = s.mem ∧ t.zf = some (guardVal (wk I.k) I.k I.pl I.ql (I.nb[0]'(by rw [L.nl]; have := L.k1; omega)) == 0) := by
  have hk := L.k1
  have hn : 0 < I.nb.length := by rw [L.nl]; omega_using [hk]
  have hz := h.ws.h256
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = s.mem ∧
    t.zf = some (guardVal (wk I.k) I.k I.pl I.ql (I.nb[0]'hn) == 0)) (by
    xrun [wordGuardTail, State.ea, hdr, h.ws.rdi, h12, hdx, hdrOff,
      h.ws.scr.ld (d := 8 * Public.sK) (by change 8 * 18 + 8 ≤ I.Z; omega_using [hz]), h.ws.scr.ld (d := 8 * sPl) (by change 8 * 21 + 8 ≤ I.Z; omega_using [hz]),
      h.ws.scr.ld (d := 8 * sQl) (by change 8 * 23 + 8 ≤ I.Z; omega_using [hz]), h.args.k, h.args.pl, h.args.ql,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      show InRegions (s.rd ++ s.wr) I.pN 1 by simpa using h.n.rd 0 hn,
      show s.mem I.pN = I.nb[0] from by simpa using h.n.val 0 hn,
      guardVal]
    rfl) rfl) fun t ⟨⟨hm, hz'⟩, hk'⟩ => ?_
  exact ⟨h.step (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) hk' (by decide), hm, hz'⟩

/-- Zero mismatches imply the public widths used by the fast reduction. -/
theorem guard_zero {W k pl ql : Nat} {b : Byte} (hW : W < 2 ^ 24) (hk : k < 2 ^ 24)
    (hp : pl < 2 ^ 24) (hq : ql < 2 ^ 24) (hg : guardVal W k pl ql b = 0) :
    W % 2 = 0 ∧ 8 * W = k ∧ 2 * pl = k ∧ pl = ql ∧ 128 ≤ b.toNat := by
  change guardVal W k pl ql b = 0#64 at hg
  unfold guardVal at hg
  simp only [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff] at hg
  obtain ⟨⟨⟨⟨he, hwk⟩, hpk⟩, hpq⟩, hb⟩ := hg
  have ew := congrArg BitVec.toNat he
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hW]),
    show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod] at ew
  have ewk := congrArg BitVec.toNat hwk
  have epk := congrArg BitVec.toNat hpk
  have epq := congrArg BitVec.toNat hpq
  have eb := congrArg BitVec.toNat hb
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show W < 2 ^ 64 by omega_using [hW]),
    Nat.mod_eq_of_lt (show pl < 2 ^ 64 by omega_using [hp]),
    Nat.mod_eq_of_lt (show ql < 2 ^ 64 by omega_using [hq]),
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_using [hk]),
    Nat.mod_eq_of_lt (show W * 2 ^ 3 < 2 ^ 64 by omega_using [hW]),
    Nat.mod_eq_of_lt (show pl * 2 ^ 1 < 2 ^ 64 by omega_using [hp])] at ewk epk epq
  simp only [BitVec.toNat_ushiftRight, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 from Nat.lt_trans b.isLt (by decide)), show (1#64).toNat = 1 from rfl] at eb
  exact ⟨ew, by omega_using [ewk], by omega_using [epk], epq, by omega_using [eb]⟩

/-- The public guard ensures that valid factors fit the normalized half width. -/
theorem factors_word {I : CvIn} (L : CvLens I)
    (hg : guardVal (wk I.k) I.k I.pl I.ql (I.nb[0]'(by rw [L.nl]; have := L.k1; omega)) = 0)
    (he : Spec.Rsa.os2ip I.pb * Spec.Rsa.os2ip I.qb = Spec.Rsa.os2ip I.nb) :
    (2 ^ (64 * (wk I.k / 2) - 1) ≤ Spec.Rsa.os2ip I.pb - 1 ∧
      Spec.Rsa.os2ip I.pb < 2 ^ (64 * (wk I.k / 2))) ∧
    (2 ^ (64 * (wk I.k / 2) - 1) ≤ Spec.Rsa.os2ip I.qb - 1 ∧
      Spec.Rsa.os2ip I.qb < 2 ^ (64 * (wk I.k / 2))) := by
  have hk := L.k2
  have hp := L.pl2
  have hq := L.ql2
  have hw : wk I.k < 2 ^ 24 := by unfold wk; omega_using [hk]
  obtain ⟨hw2, hwk, hpk, hpq, hb⟩ := guard_zero hw (by omega_using [hk]) (by omega_using [hk, hp])
    (by omega_using [hk, hq]) hg
  have hbits : 64 * (wk I.k / 2) = 32 * wk I.k := by omega_using [hw2]
  have ep : 8 * I.pl = 64 * (wk I.k / 2) := by omega_using [hbits, hpk, hwk]
  have eq : 8 * I.ql = 64 * (wk I.k / 2) := by omega_using [ep, hpq]
  have pbound := os2ip_lt I.pb
  have qbound := os2ip_lt I.qb
  rw [L.pbl, pow256_eq, ep] at pbound
  rw [L.qbl, pow256_eq, eq] at qbound
  have nb := os2ip_high (by rw [L.nl]; have := L.k1; omega) hb
  rw [L.nl, show 8 * I.k - 1 = 2 * (64 * (wk I.k / 2)) - 1 by omega_using [hwk, hbits]] at nb
  have npos : 1 ≤ 64 * (wk I.k / 2) := by have := L.k1; omega_using [this, hwk, hbits]
  have fb := balanced_factor npos pbound qbound nb he
  exact ⟨⟨fb.1, pbound⟩, fb.2, qbound⟩

end VG.Proof.Rsa.X86_64.WordDivide
