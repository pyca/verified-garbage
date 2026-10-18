module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafTiming
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# ECDSA verification over P-384 on AArch64: what taint tracking checks

Each piece of the verifier whose timing the relational proof
(`pubNafVerify_public_ct`) takes from taint tracking, with the registers it
may branch on or address by: the pointer `x0` for the field arithmetic, and
the loop counters, the digits' and entries' registers and the recoding's
residual elsewhere.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P384

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64

/-- Constant time for the registers `rs`, by taint tracking. -/
macro "reg_ct" rs:term : tactic => `(tactic|
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs $rs) (fun _ _ _ _ h => h) (by taint_decide))

/-- The window method's slots, which the public NAF uses. -/
abbrev Kq := winQ p384

theorem add_checks : AddCChecks Kq Kq.D Kq.E Kq.R := {
    zero := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> reg_ct [.x0]
    copyP := by reg_ct [.x0]
    copyQ := by reg_ct [.x0]
    head := by reg_ct [.x0]
    tail := by reg_ct [.x0]
    double := by reg_ct [.x0]
    infinity := by reg_ct [.x0] }

theorem keep_of {c : Prog isa}
    (h : (instrs c).all (fun i => decide (clobbers i .x19 = false ∧ clobbers i .x20 = false)) = true) :
    ∀ r ∈ [Reg.x19, .x20], ∀ i ∈ instrs c, clobbers i r = false := by
  intro r hr i hi
  have hh := of_decide_eq_true (List.all_eq_true.mp h i hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hh.1
  · exact hh.2

theorem dblu_keep : ∀ r ∈ [Reg.x19, .x20], ∀ i ∈ instrs (fprogB Kq.M (PubNaf.dbluOps Kq)),
    clobbers i r = false :=
  keep_of (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem zaddu_keep : ∀ r ∈ [Reg.x19, .x20], ∀ i ∈ instrs (fprogB Kq.M (PubNaf.zadduOps Kq)),
    clobbers i r = false :=
  keep_of (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem window_checks : PubNaf.WindowChecks Kq where
  table := {
    copyP := by reg_ct [.x0]
    ptr := by reg_ct [.x0]
    store := by reg_ct [.x0, .x20]
    set := by reg_ct [.x0, .x20]
    dblu := by reg_ct [.x0]
    zaddu := by reg_ct [.x0]
    bump := by reg_ct [.x0, .x19, .x20]
    keepD := by
      intro r hr s t tr he
      exact Exec.gpr (dblu_keep r hr) he (Or.inr (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> decide))
    keep := by
      intro r hr s t tr he
      exact Exec.gpr (zaddu_keep r hr) he (Or.inr (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> decide)) }
  cache := by reg_ct [.x0]
  infinity := by reg_ct [.x0]
  counter := by reg_ct [.x0]
  step := {
    dec := by reg_ct [.x0, .x19]
    dbl := by reg_ct [.x0]
    digit := {
      read := by reg_ct [.x0, .x19]
      lookup := by reg_ct [.x0, .x2]
      sign := by reg_ct [.x0, .x19]
      neg := by reg_ct [.x0]
      add := add_checks
      copy := by reg_ct [.x0] } }
  finish := by reg_ct [.x0]

theorem prep_checks : PubNaf.PrepChecks Kq (p384.sl V) where
  init := by reg_ct [.x0]
  step := by reg_ct (PubNaf.prepPublic Kq.M.n)

/-- The public comb's iterations, and the code before and after the multiplications. -/
theorem verify_checks : PubNafVerifyChecks p384 where
  before := by reg_ct [.x0, .x1, .x2, .x3]
  comb := {
    init := by reg_ct [.x0]
    head := by reg_ct [.x0, .x19]
    tail := by reg_ct [.x0, .x19, .x16] }
  save := by reg_ct [.x0]
  prep := prep_checks
  window := window_checks
  tail := by reg_ct [.x0]

end VG.Proof.Ecdsa.Verify.AArch64.P384
