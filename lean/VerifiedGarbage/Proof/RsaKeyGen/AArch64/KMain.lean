module

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KTail
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdE
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Front
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain

/-!
# A candidate on AArch64: once `rand` has the candidate's octets

`CandEnd`: a candidate ends as `afterDraw` of the candidate from the first
`8 w` octets of `rand`: too close to `p` (status 2), obviously composite or
sharing a factor with `e − 1` (3), or Miller–Rabin's result. `MainCtx`: what
`kMainWith` needs.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aY sCnt)

/-- How a candidate ends, from the specification's result. -/
def CandEnd (s t : State) (op up : Addr) (k : Nat) (r : List Byte) :
    Option (Spec.RsaKeyGen.Candidate × List Byte) → Prop
  | none => KEnd s t op up k 0 0 none
  | some (.prime c, rest) => KEnd s t op up k 1 (r.length - rest.length) (some c)
  | some (.close, rest) => KEnd s t op up k 2 (r.length - rest.length) none
  | some (.rejected, rest) => KEnd s t op up k 3 (r.length - rest.length) none

/-- What `kMainWith` needs, for a prime of `w` words. -/
structure MainCtx (s : State) (B : Addr) (Z w : Nat) (op up eP pP rP : Addr) (eB pB r : List Byte) : Prop where
  scr : Scr s B Z
  x0 : s.gpr .x0 = B
  z : 1024 * w ≤ Z
  w4 : 4 ≤ w
  w64 : w ≤ 64
  out : word s.mem B (8 * kOut) = op
  len : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)
  usedP : word s.mem B (8 * kUsedP) = up
  e : word s.mem B (8 * kE) = eP
  elen : word s.mem B (8 * kElen) = BitVec.ofNat 64 eB.length
  p : word s.mem B (8 * kP) = pP
  plen : word s.mem B (8 * kPlen) = BitVec.ofNat 64 pB.length
  rand : word s.mem B (8 * kRand) = rP
  rlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length
  esrc : Src s B Z eP eB
  psrc : Src s B Z pP pB
  rsrc : Src s B Z rP r
  el1 : 1 ≤ eB.length
  el8 : eB.length ≤ 8
  pl : pB.length = 0 ∨ pB.length = 8 * w
  rl : r.length < 2 ^ 64
  rk : 8 * w ≤ r.length
  ou : OutUp s B Z op up (8 * w)

theorem mask_bne (b : Bool) : (mask b != 0) = b := by cases b <;> decide

/-- The octets of `out`, past the scratch space, survive changes inside it. -/
theorem outBytes_inScr {B : Addr} {Z k : Nat} {m m' : Mem} {op : Addr} (hin : InScr B Z m m')
    (hz : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)) : outBytes m' op k = outBytes m op k :=
  List.map_congr_left fun j hj => hin _ (hz j (List.mem_range.mp hj))

/-- `finUsed st` ends a candidate. -/
theorem finUsed_end {s sX : State} {B : Addr} {Z : Nat} {op up : Addr} {k st u : Nat} (hs : Scr sX B Z)
    (h0 : sX.gpr .x0 = B) (h8 : 8 * 32 ≤ Z) (hst : st < 2 ^ 16) (hu : word sX.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hU : word sX.mem B (8 * kUsedP) = up) (ho : OutUp sX B Z op up k) (hin : InScr B Z s.mem sX.mem)
    (kk : Keep mmRegs s sX) :
    WP isa (finUsed st) sX fun t => KEnd s t op up k st u none :=
  WP.mono (finUsed_ok hs h0 h8 hst hu hU ho.upw) fun _ h =>
    (KEnd.of_fin ho h).trans_pre (outBytes_inScr hin ho.outZ) (kk.mono (by decide))

/-- Disjointness of a header word from a list of literal ranges. -/
tactic_template "k_disj" : tactic => `(tactic| first | hdr_disj | (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, loadCRanges, closeRanges,
    gcdRanges, slot, hdrBytes, aN, aX, aAcc, aTmp, aY, aTab, kT0, kG, sCnt, sW, sArr, sStride, Public.sMask, sFn, kOut,
    kLen, Public.sK, kUsedP, kE, kElen, kP, kPlen, kRand, kRandLen, kUsed]
  and_intros <;> omega_arith))

/-- Bounds of a list of literal ranges. -/
tactic_template "k_le" : tactic => `(tactic| first | hdr_disj | (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, loadCRanges, closeRanges,
    gcdRanges, slot, hdrBytes, aN, aX, aAcc, aTmp, aY, aTab, kT0, kG, sCnt, sW, sArr, sStride, Public.sMask, sFn,
    kUsed]
  and_intros <;> omega_arith))

end VG.Proof.RsaKeyGen.AArch64
