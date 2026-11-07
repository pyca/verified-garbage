module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallResult
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInvalidCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignBodyCT

/-! Whole-entry leakage equality against the merged randomized-signing contract. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

theorem random_sign_body_agreement (S : Signer) {s t : State}
    (hs : RandomSignABI S.stack s) (ht : RandomSignABI S.stack t) (hp : RandomSignPublicAgree s t)
    (hvs : RandomValid S s) (hvt : RandomValid S t)
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.body S.name S.code) (allocated Random.frameBytes s) tsa u)
    (eb : Exec isa (RandomSign.body S.name S.code) (allocated Random.frameBytes t) tsb w) : tsa = tsb := by
  by_cases hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)
  · exact random_sign_body_valid_ct S hs ht hp hvs hvt hq htrace hstatus ea eb
  · exact random_sign_body_invalid_ct S hs ht hp hq ea eb

theorem random_sign_alloc {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    isa.push (.alloc Random.frameBytes) s = some (allocated Random.frameBytes s) := by
  have hl := h.stackLower
  simp only [isa, push, allocated]
  exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega⟩

theorem random_sign_constantTime (S : Signer) :
    ConstantTime isa (fun s => (Spec.Dsa.randomSignContract abi (S.stack + 256)).pre s ∧ RandomValid S s)
      (Spec.Dsa.randomSignContract abi (S.stack + 256)).pub
      (RandomSign.code S.name S.code) := by
  intro s t tsa tsb u w ⟨hs, hvs⟩ ⟨ht, hvt⟩ hpub ea eb
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
      have hh := random_sign_body_agreement S hsa hta hp hvs hvt htrace hstatus hab hbb
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.AArch64
