module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowByte
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (groupBytes groupByte)

/-- Up to five bytes, read at fixed offsets, give their big-endian integer
without changing memory or the source address. -/
theorem groupBytes_ok (n : Nat) {s : State} {src : Addr} {bs : List Byte}
    (hn : n ≤ 5) (hbs : n ≤ bs.length) (h3 : s.gpr .x3 = src) (h4 : s.gpr .x4 = 0#64)
    (hld : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hb : ∀ i (hi : i < n), s.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega)) :
    WP isa (.block (groupBytes n)) s fun t =>
      t.gpr .x4 = BitVec.ofNat 64 (pre bs n) ∧ t.mem = s.mem ∧ Keep [.x4, .x5] s t := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨by simpa [pre, Spec.Rsa.os2ip] using h4, rfl, Keep.refl _ _⟩
  | succ n ih =>
    have he : groupBytes (n + 1) = groupBytes n ++ groupByte n := by
      simp [groupBytes, List.range_succ]
    rw [he, WP.block_append_iff]
    refine WP.mono (ih (by omega) (by omega)
      (fun i hi => hld i (by omega)) (fun i hi => hb i (by omega)))
      fun t ⟨ht4, htm, kt⟩ => ?_
    refine WP.mono (groupByte_ok (by omega) ((kt.gpr .x3 (by decide)).trans h3)
      (by rw [kt.rd, kt.wr]; exact hld n (by omega))) fun u ⟨⟨hu4, hum⟩, ku⟩ =>
        ⟨?_, hum.trans htm, (kt.trans ku).mono (by decide)⟩
    have hnbs : n < bs.length := by omega
    have hp := pre_lt bs (i := n) (by omega)
    have hpow : 256 ^ n ≤ 256 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
    have hv : pre bs n < 2 ^ 56 := by omega
    have hbyte : ((t.mem.read (src + BitVec.ofNat 64 n) 1).setWidth 32).setWidth 64 =
        (bs[n]'hnbs).setWidth 64 := by
      rw [VG.Proof.MlKem.AArch64.read_one, htm, hb n (by omega)]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      have := (bs[n]'hnbs).isLt
      omega
    apply BitVec.eq_of_toNat_eq
    rw [hu4, ht4, hbyte, appendByte_value _ _ hv, BitVec.toNat_ofNat, pre_succ bs hnbs]
    have := (bs[n]'hnbs).isLt
    omega

/-- The complete group uses five fixed byte addresses, with no
exponent-dependent memory access or branch. -/
theorem groupFive_ct :
    RelCT isa (Two fun (src : Addr) s => s.gpr .x3 = src)
      (.block (groupBytes 5)) (fun _ _ => True) := by
  apply two_taint [.x3] (hc := .block [])
  · intro P s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.trans ht.symm
  · rfl

end VG.Proof.Bignum.AArch64.WindowFive
