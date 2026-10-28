module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroup
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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
    (hb : ∀ j (hj : j < 5), s.mem ((src + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) = bs[j]'(by omega)) :
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
