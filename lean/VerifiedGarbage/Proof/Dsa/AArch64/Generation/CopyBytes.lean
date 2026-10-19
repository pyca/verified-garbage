module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega

/-! Copy a complete big-endian component with the existing native byte loop. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem copyBytes_ok {s : State} {rp op : Addr} {bs : List Byte}
    (hlen : bs.length < 2 ^ 64)
    (hrp : s.gpr .x12 = rp) (hop : s.gpr .x2 = op)
    (hn : s.gpr .x9 = BitVec.ofNat 64 bs.length)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hbytes : ∀ i < bs.length, s.mem (off rp i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ j < bs.length, off rp i ≠ off op j) :
    WP isa Impl.Dsa.AArch64.Random.copyRest s fun t =>
      Spec.Rsa.bytesAt t.mem op bs.length = bs ∧
      (∀ a, (∀ i < bs.length, a ≠ off op i) → t.mem a = s.mem a) ∧
      Keep [.x0, .x12, .x2, .x9] s t := by
  refine WP.mono (random_copyRest_ok hrp hop hn hlen hrd hwr hsep) fun t ⟨hb, hf, hk⟩ => ?_
  refine ⟨?_, hf, hk⟩
  apply List.ext_getElem
  · exact bytesAt_length _ _ _
  · intro i hi hi'
    have hil : i < bs.length := by simpa only [bytesAt_length] using hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some] using
      (hb i hil).trans (hbytes i hil)

end VG.Proof.Dsa.AArch64.Generation
