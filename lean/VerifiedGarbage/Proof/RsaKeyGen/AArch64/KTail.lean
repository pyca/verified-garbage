module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Fin
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.Rsa.Ranges

/-!
# A candidate on AArch64: Montgomery setup, Miller–Rabin and the result

Disjointness of a header word from `montSetup`'s ranges (`kt_disj`), and the
octets of `out` past the scratch space (`outBytes_inScr'`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aAcc aTmp aR2 aY aOne sCnt)

/-- Disjointness of a header word from `montSetup`'s ranges, and their bounds. -/
tactic_template "kt_disj" : tactic => `(tactic| first | hdr_disj | (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, msRanges, msTail,
    List.cons_append, List.nil_append, slot, hdrBytes, aE, aN, aAcc, aTmp, aR2, aY, aOne, aR1, aRm1, sCnt, kChecks, kE, sFn, sMinv, kRand, kLen, Public.sK,
    kRandLen, kUsed, kOut, kUsedP, Public.sMask]
  and_intros <;> omega_arith))

/-- The octets of `out`, past the scratch space, survive changes inside it. -/
theorem outBytes_inScr' {B : Addr} {Z k : Nat} {m m' : Mem} {op : Addr} (hin : InScr B Z m m')
    (hz : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)) : outBytes m' op k = outBytes m op k :=
  List.map_congr_left fun j hj => hin _ (hz j (List.mem_range.mp hj))

end VG.Proof.RsaKeyGen.AArch64
