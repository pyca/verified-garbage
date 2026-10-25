module

public import VerifiedGarbage.Proof.Dsa.Arm.SigningKey
public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace

/-! # Fixed pointer schedules for the signer's reduced public checks -/

@[expose] public section
namespace VG.Proof.Dsa.Arm
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout

theorem signingSubgroup_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Validate.signingSubgroup pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have ho : 4960 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by omega_arith
  have pt : PtrOk (.local Impl.Dsa.Layout.t) := (by decide : Impl.Dsa.Layout.t < 2 ^ 16)
  unfold Validate.signingSubgroup
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t) (X.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo)
      (X.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X.C₁.inp mg).toReady (X.C₂.inp mg).toReady (X.C₁.inp mq).toReady
      (X.E _ mp) (X.E _ mg) (X.E _ mq)
      (X.C₂.inp mq).toReady q4 qp qw)
    (power_ok (output := Impl.Dsa.Layout.t) X.C₁.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X.C₁.inp mp).toReady
      (X.C₁.inp mg).toReady (X.C₁.inp mq).toReady (X.C₁.inp mp).value D₁.hP D₁.hPo ho.1 (by omega_arith) (by decide))
    (power_ok (output := Impl.Dsa.Layout.t) X.C₂.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X.C₂.inp mp).toReady
      (X.C₂.inp mg).toReady (X.C₂.inp mq).toReady (X.C₂.inp mp).value D₂.hP D₂.hPo ho.1 (by omega_arith) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₁ := X.run (St₁.run (.inr ho)) (St₂.run (.inr ho))
  exact isOne_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega_arith) (by omega_arith) pt
    (ptrEq_local X₁.C₁.S.ws X₁.C₂.S.ws _)

theorem signingKey_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Validate.signingKey pLen qLen) s₁ s₂ :=
  SameTrace.seq (domain_trace X mp mq mg my D₁ D₂)
    (domain_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my) D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (domain_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my) D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun _ _ ⟨_, _, Rn₁⟩ ⟨_, _, Rn₂⟩ => signingSubgroup_trace (X.run Rn₁ Rn₂) mp mq mg D₁ D₂

end VG.Proof.Dsa.Arm
