module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcBody

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

structure RedcInv (s : State) (B : Addr) (eQ eN k j : Nat) (inv : Word) (t : State) : Prop where
  value : ((word s.mem B eN).toNat * inv.toNat + 1) % 2 ^ 64 = 0 →
    ∃ q < 2 ^ (64 * (8 * j)), 2 ^ (64 * (8 * j)) *
      (wv t.mem B (eQ + 64 * j) (8 * (2 * k - j)) + 2 ^ (64 * (8 * k)) * (t.gpr .x10).toNat) =
      wv s.mem B eQ (16 * k) + q * wv s.mem B eN (8 * k)
  ptr : t.gpr .x8 = off B (eQ + 64 * j)
  carry : (t.gpr .x10).toNat ≤ 1
  frame : Outside B eQ (128 * k) s.mem t.mem
  keep : Keep rowRegs s t

theorem redcStep_ok {s t : State} {B : Addr} {Z eQ eN k j : Nat} {inv : Word}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0)
    (hHdr : 256 ≤ eQ) (hSize : eQ + 128 * k ≤ Z)
    (hNQ : eN + 64 * k ≤ eQ) (hk : 2 ≤ k) (hk' : 8 * k < 2 ^ 64)
    (hn : word s.mem B (8 * sArr Public.aN) = off B eN)
    (hi : word s.mem B (8 * sMinv) = inv)
    (hw : word s.mem B (8 * sW) = BitVec.ofNat 64 (8 * k))
    (hj : j < k) (hI : RedcInv s B eQ eN k j inv t) :
    WP isa rowBody t fun u => RedcInv s B eQ eN k (j + 1) inv u ∧
      u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1 := by
  have hns := hs.nowrap
  obtain ⟨p, hp⟩ := word_flag (t.gpr .x10) hI.carry
  have hn' := (hI.frame.word (d := 8 * sArr Public.aN)
    (by unfold sArr Public.aN; omega) (by unfold sArr Public.aN; omega)).trans hn
  have hi' := (hI.frame.word (d := 8 * sMinv) (by unfold sMinv; omega)
    (by unfold sMinv; omega)).trans hi
  have hw' := (hI.frame.word (d := 8 * sW) (by unfold sW; omega)
    (by unfold sW; omega)).trans hw
  refine WP.mono (rowBody_ok (hs.congr hI.keep.wr)
    ((hI.keep.gpr .x0 (by decide)).trans h0) hI.ptr
    ((hI.keep.gpr .x7 (by decide)).trans h7) hp (by omega) (by omega)
    (by omega) hk hk' hn' hi' hw') fun u ⟨d, hd, hv, ho, hc, h8, h12, ku⟩ => ?_
  refine ⟨⟨?_, h8.trans (congrArg (off B) (by omega)), hc,
    hI.frame.trans (ho.mono (by omega) (by omega)), (hI.keep.trans ku).mono (by decide)⟩, h12⟩
  intro hInv
  have hN0 := congrArg BitVec.toNat (hI.frame.word (d := eN) (by omega) (by omega))
  have hInvT : ((word t.mem B eN).toNat * inv.toNat + 1) % 2 ^ 64 = 0 :=
    (congrArg (fun n => (n * inv.toNat + 1) % 2 ^ 64) hN0).trans hInv
  have hfull := extend_row_value (n := 2 * k - j) (by omega) (by omega) ho (hv hInvT)
  have hN := hI.frame.wv (d := eN) (k := 8 * k) (by omega) (by omega)
  have hpN : (t.gpr .x10).toNat = p.toNat := by
    have h := congrArg BitVec.toNat hp
    have h' : (BitVec.ofNat 64 p.toNat).toNat = p.toNat := by cases p <;> rfl
    exact h.trans h'
  rewrite [hN, ← hpN,
    show eQ + 64 * j + 64 = eQ + 64 * (j + 1) by omega,
    show 2 * k - j - 1 = 2 * k - (j + 1) by omega] at hfull
  obtain ⟨q, hq, he⟩ := hI.value hInv
  refine ⟨q + 2 ^ (64 * (8 * j)) * d, ?_, ?_⟩
  · rewrite [pow_blocks_succ]
    exact append_digit_bound hq hd
  · have hrow : (2 ^ 64) ^ 8 *
        (wv u.mem B (eQ + 64 * (j + 1)) (8 * (2 * k - (j + 1))) +
          2 ^ (64 * (8 * k)) * (u.gpr .x10).toNat) =
        (wv t.mem B (eQ + 64 * j) (8 * (2 * k - j)) +
          2 ^ (64 * (8 * k)) * (t.gpr .x10).toNat) + d * wv s.mem B eN (8 * k) :=
      hfull.trans (by omega)
    rewrite [pow_blocks_succ]
    exact cancel_step he hrow

/-- Fixed public bounds drive the outer loop even when the inverse is invalid. -/
theorem redcRows_ok {s : State} {B : Addr} {Z eQ eN k : Nat} {inv : Word}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0)
    (h8 : s.gpr .x8 = off B eQ) (h10 : s.gpr .x10 = 0)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 k)
    (hHdr : 256 ≤ eQ) (hSize : eQ + 128 * k ≤ Z)
    (hNQ : eN + 64 * k ≤ eQ) (hk : 2 ≤ k) (hk' : 8 * k < 2 ^ 64)
    (hn : word s.mem B (8 * sArr Public.aN) = off B eN)
    (hi : word s.mem B (8 * sMinv) = inv)
    (hw : word s.mem B (8 * sW) = BitVec.ofNat 64 (8 * k)) :
    WP isa (.loop rowBody (.nonzero .x .x12)) s (RedcInv s B eQ eN k k inv) := by
  have hzc : (s.gpr .x10).toNat = 0 := congrArg BitVec.toNat h10
  have hInit : RedcInv s B eQ eN k 0 inv s := by
    refine ⟨?_, h8, Nat.le_trans (Nat.le_of_eq hzc) (by decide), Outside.refl _ _ _ _, Keep.refl _ _⟩
    intro _
    refine ⟨0, by decide, ?_⟩
    exact outer_initial (congrArg (fun n => wv s.mem B eQ n) (show 8 * (2 * k - 0) = 16 * k by omega)) hzc
  exact wp_countdown (by omega) (by omega) (RedcInv s B eQ eN k · inv)
    (fun j hj t hI _ => redcStep_ok hs h0 h7 hHdr hSize hNQ hk hk' hn hi hw hj hI)
    hInit h12

end VG.Proof.Bignum.AArch64.BlockedRedc
