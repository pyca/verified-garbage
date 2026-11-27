module
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Frag
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Base

import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Round
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

/-!
# ML-DSA key generation on AArch64: the call of `vg_mldsa_power2round`

What the call needs of the layout (`p2rChk`), and that it then meets the
function's precondition (`p2r_pre`); the norm is in
`Proof/MlDsa/AArch64/Call/Round.lean`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `Power2Round` -/

def p2rChk (rbs wbs : List (Reg × Nat)) (t t1 t0 : Ptr) : Bool :=
  sepB rbs wbs t 1024 t1 1024 && sepB rbs wbs t 1024 t0 1024 && sepB rbs wbs t1 1024 t0 1024 &&
    inB (rbs ++ wbs) t 1024 && inB (rbs ++ wbs) t1 1024 && inB (rbs ++ wbs) t0 1024 && inB wbs t1 1024 &&
    inB wbs t0 1024

abbrev p2rArgs (t t1 t0 : Ptr) : List (Reg × Arg) := [(.x0, .ptr t), (.x1, .ptr t1), (.x2, .ptr t0)]

theorem p2r_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {t t1 t0 : Ptr} (c4 : inB bs t 1024 = true)
    (c5 : inB bs t1 1024 = true) (c6 : inB bs t0 1024 = true) :
    ∀ x ∈ p2rArgs t t1 t0, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨ptr_ok (ptr_kept L c5), by decide⟩, ⟨ptr_ok (ptr_kept L c6), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {t t1 t0 : Ptr}
  (hc : p2rChk rbs wbs t t1 t0 = true)
include L hc

theorem p2r_cov : Covers ([⟨pa s t, 1024⟩] ++ [⟨pa s t1, 1024⟩, ⟨pa s t0, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s t1, 1024⟩, ⟨pa s t0, 1024⟩] s.wr := by
  simp only [p2rChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem p2r_pre (hr : Reduced s.mem (pa s t)) {s1 : State} (h1 : Args (p2rArgs t t1 t0) s s1) :
    (power2RoundContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s t, 1024⟩] [⟨pa s t1, 1024⟩, ⟨pa s t0, 1024⟩]) := by
  simp only [p2rChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [power2RoundContract, power2RoundSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exact hr

end

end VG.Proof.MlDsa.AArch64.KeyGen
