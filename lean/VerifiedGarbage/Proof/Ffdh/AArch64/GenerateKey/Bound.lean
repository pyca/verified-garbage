module

public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain

/-!
# `vg_ffdh_generate_key` on AArch64: the bound

The bound's octets (`KeyScalar.bnd`: q's, or p's), the index of their first
nonzero one, and that octet.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Ffdh.KeyScalar (bnd bnd_length)
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The bound's octets. -/
abbrev FD.bb (D : FD) : List Byte := bnd D.k D.dom

/-- Their first nonzero octet's index. -/
abbrev FD.bl (D : FD) : Nat := lead D.bb

/-- That octet. -/
abbrev FD.bc (D : FD) : Byte := D.bb.getD D.bl 0

end VG.Proof.Ffdh.AArch64
