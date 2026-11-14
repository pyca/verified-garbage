module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Tactic.ToAdditive

/-! ### `Bignum.AArch64.CrtWindowGroup`, which only this module used -/

section

/-! ### `Bignum.AArch64.CrtWindowByte`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- One source byte is appended without changing memory or the source pointer. -/
theorem groupByte_ok {s : State} {src : Addr} {i : Nat} (hi : i < 5)
    (h3 : s.gpr .x3 = src)
    (hld : InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1) :
    WP isa (.block (VG.Impl.Rsa.AArch64.WindowFive.groupByte i)) s fun t =>
      (t.gpr .x4 = (s.gpr .x4 <<< 8) |||
        ((s.mem.read (src + BitVec.ofNat 64 i) 1).setWidth 32).setWidth 64 ∧
        t.mem = s.mem) ∧ Keep [.x4, .x5] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [VG.Impl.Rsa.AArch64.WindowFive.groupByte, h3, hld, show i < 4096 by omega_using [hi]]

/-- The shift-and-OR byte append is ordinary big-endian accumulation;
the bound excludes a discarded high byte. -/
theorem appendByte_value (v : Nat) (b : Byte) (hv : v < 2 ^ 56) :
    ((BitVec.ofNat 64 v <<< 8) ||| b.setWidth 64).toNat = 256 * v + b.toNat := by
  have hb := b.isLt
  have hshift : v * 2 ^ 8 < 2 ^ 64 := by omega_using [hv]
  have hor : v * 2 ^ 8 ||| b.toNat = v * 2 ^ 8 + b.toNat := by
    simpa only [Nat.shiftLeft_eq] using (Nat.shiftLeft_add_eq_or_of_lt hb v).symm
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega_using [hv]), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hshift, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega_using []), hor]
  omega_using []

end VG.Proof.Bignum.AArch64.WindowFive

end

end


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
    (hb : ∀ i (hi : i < n), s.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega_using [hbs, hi])) :
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
    refine WP.mono (ih (by omega_using [hn]) (by omega_using [hbs])
      (fun i hi => hld i (by omega_using [hi])) (fun i hi => hb i (by omega_using [hi])))
      fun t ⟨ht4, htm, kt⟩ => ?_
    refine WP.mono (groupByte_ok (by omega_using [hn]) ((kt.gpr .x3 (by decide)).trans h3)
      (by rw [kt.rd, kt.wr]; exact hld n (by omega_using []))) fun u ⟨⟨hu4, hum⟩, ku⟩ =>
        ⟨?_, hum.trans htm, (kt.trans ku).mono (by decide)⟩
    have hnbs : n < bs.length := by omega_using [hbs]
    have hp := pre_lt bs (i := n) (by omega_using [hbs])
    have hpow : 256 ^ n ≤ 256 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega_using [hn])
    have hv : pre bs n < 2 ^ 56 := by omega_using [hp, hpow]
    have hbyte : ((t.mem.read (src + BitVec.ofNat 64 n) 1).setWidth 32).setWidth 64 =
        (bs[n]'hnbs).setWidth 64 := by
      rw [VG.Proof.MlKem.AArch64.read_one, htm, hb n (by omega_using [])]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      have := (bs[n]'hnbs).isLt
      omega_using []
    apply BitVec.eq_of_toNat_eq
    rw [hu4, ht4, hbyte, appendByte_value _ _ hv, BitVec.toNat_ofNat, pre_succ bs hnbs]
    have := (bs[n]'hnbs).isLt
    omega_using [hv]

end VG.Proof.Bignum.AArch64.WindowFive

end

end


/-! Read five exponent bytes while preserving the complete precomputed table. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (loadGroup groupBytes)

theorem loadGroup_ok {s : State} {P src : Addr} {w i : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) {bs : List Byte} (hbs : 5 ≤ bs.length)
    (hp : word s.mem P (8 * Crt.sExp) = src)
    (hi : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 i)
    (hld : ∀ j < 5, InRegions (s.rd ++ s.wr) ((src + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) 1)
    (hb : ∀ j (hj : j < 5), s.mem ((src + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) = bs[j]'(by omega_using [hbs, hj])) :
    WP isa (.block loadGroup) s fun t =>
      t.mem = s.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (pre bs 5)) ∧
      Keep [.x3,.x4,.x5] s t := by
  unfold loadGroup
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3,.x4] (Q := fun u =>
    u.gpr .x3 = src + BitVec.ofNat 64 i ∧ u.gpr .x4 = 0 ∧ u.mem = s.mem)
    (by brun [hc.good.x0, hdr_enc (show Crt.sExp < 32 by decide),
      hdr_enc (show Crt.sI < 32 by decide), hc.ld (i := Crt.sExp) (by decide),
      hc.ld (i := Crt.sI) (by decide), hp,hi]) rfl rfl rfl) fun u ⟨⟨h3,h4,hm⟩,ku⟩ => ?_
  refine WP.mono (groupBytes_ok 5 (by decide) hbs h3 h4
    (fun j hj => by rw [ku.rd,ku.wr]; exact hld j hj)
    (fun j hj => by rw [hm]; exact hb j hj)) fun a ⟨h4',hm',ka⟩ => ?_
  refine WP.mono (WP.keep [] (Q := fun t =>
    t.mem = a.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (pre bs 5))) ?_ rfl rfl rfl)
    fun t ⟨ht,kt⟩ => ⟨by rw [ht,hm',hm],((ku.trans ka).trans kt).mono (by decide)⟩
  brun [hc.good.x0, hdr_enc (show Crt.sV < 32 by decide),
    (ka.gpr .x0 (by decide)).trans (ku.gpr .x0 (by decide)), h4',
    show InRegions a.wr (off P (8 * Crt.sV)) 8 by rw [ka.wr,ku.wr]; exact hc.st (by decide)]

end VG.Proof.Bignum.AArch64.WindowFive
