module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStore
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorScan
import Mathlib.Data.Int.ModEq

/-! A full table scan followed by the four stores of one selected block. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (inner)

theorem scan_store_ok {s : State} {B : Addr} {base stride dst v : Nat}
    (hv : v < 32) (hs : s.gpr .x6 = BitVec.ofNat 64 stride)
    (hc : s.gpr .x14 = BitVec.ofNat 64 32)
    (h0 : ScanInv s (off B base) stride v 0 s)
    (hp : s.gpr .x17 = off B dst) (hd : dst + 64 ≤ 2 ^ 64)
    (hld : ∀ j < 32, ∀ i < 4,
      InRegions (s.rd ++ s.wr) (off B (base + stride * j + 16 * i)) 16)
    (hw : ∀ i < 4, InRegions s.wr (off B (dst + 16 * i)) 16) :
    WP isa (.seq (countLoop .x14 inner) (.block (stores 4))) s fun t =>
      Keep [.x14, .x16] s t ∧ Outside B dst 64 s.mem t.mem ∧
      t.v .v22 = dup2 (BitVec.ofNat 64 v) ∧ t.v .v24 = dup2 1 ∧
      ∀ j < 64, t.mem (off B (dst + j)) =
        s.mem (off B (base + stride * v + j)) := by
  apply WP.seq
  refine WP.mono (scan_ok hv hs hc h0 (fun j hj i hi => by
    simpa only [off, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc] using hld j hj i hi))
    fun u hu => ?_
  refine WP.mono (stores_ok 4 (src := base + stride * v) (by decide)
    (by rw [hu.keep.gpr .x17 (by decide)]; exact hp) hd
    (fun i hi => by
      simp only [hu.value i hi, hv, ite_true, hu.mem]
      simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc])
    (fun i hi => by rw [hu.keep.wr]; exact hw i hi)) fun t ht => ?_
  refine ⟨(hu.keep.trans ht.keep).mono (by decide), ?_, ?_, ?_, ?_⟩
  · simpa only [hu.mem] using ht.frame
  · rw [ht.vectors]; exact hu.digit
  · rw [ht.vectors]; exact hu.one
  · simpa only [hu.mem] using ht.bytes

end VG.Proof.Bignum.AArch64.WindowVector
