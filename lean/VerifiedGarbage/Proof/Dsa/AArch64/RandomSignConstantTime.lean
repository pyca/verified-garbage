module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInvalidCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignBodyCT

/-! Whole-entry leakage equality against the merged randomized-signing contract. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

theorem random_sign_body_agreement (v : Backend) {s t : State}
    (hs : RandomSignABI v.stack s) (ht : RandomSignABI v.stack t) (hp : RandomSignPublicAgree s t)
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.mul)) (allocated Random.frameBytes s) tsa u)
    (eb : Exec isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.mul)) (allocated Random.frameBytes t) tsb w) : tsa = tsb := by
  by_cases hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)
  · exact random_sign_body_valid_ct v hs ht hp hq htrace hstatus ea eb
  · exact random_sign_body_invalid_ct v hs ht hp hq ea eb

theorem random_sign_alloc {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    isa.push (.alloc Random.frameBytes) s = some (allocated Random.frameBytes s) := by
  have hl := h.stackLower
  simp only [isa, push, allocated]
  exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega⟩

theorem random_sign_constantTime (v : Backend) :
    ConstantTime isa (Spec.Dsa.randomSignContract abi (v.stack + 256)).pre
      (Spec.Dsa.randomSignContract abi (v.stack + 256)).pub
      (RandomSign.code (randomSignerName v) (SignVerify.sign v.mul)) := by
  intro s t tsa tsb u w hs ht hpub ea eb
  have hsa := randomSignABI_of hs
  have hta := randomSignABI_of ht
  obtain ⟨hp, hstatus, _, htrace⟩ := random_sign_public_related hsa hta hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [random_sign_alloc hsa, Option.some.injEq] at hap
      rw [random_sign_alloc hta, Option.some.injEq] at hbp
      subst hap
      subst hbp
      have hh := random_sign_body_agreement v hsa hta hp htrace hstatus hab hbb
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.AArch64
