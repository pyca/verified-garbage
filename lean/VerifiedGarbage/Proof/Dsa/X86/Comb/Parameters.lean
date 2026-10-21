module

public import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.ValidateOne
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.GenerateDomain
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Core
public import VerifiedGarbage.Proof.Dsa.X86.ScheduleFrame

/-! The public check constructs a canonical table while checking g^q = 1. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Ecdsa.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem subgroup_ok {base : Addr} {size pLen qLen p q g : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s)
    (G : CallerBuffer s base size (.input .g) pLen)
    (hg : operandValue s base (.input .g) pLen=g)
    (sizeComb : (layout ((pLen+7)/8) ((qLen+3)/4)).size≤size) :
    WP isa (subgroup pLen qLen) s fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf=flagW base (Layout.field .mask) s &&& mask32 (g^q%p=1) ∧
      canonical ((pLen+7)/8) ((qLen+3)/4) p g base sf.mem ∧ ScheduleFrame base size s sf := by
  have L := M.lengths
  have A := M.aligned
  have np : (pLen+7)/8≤48 := by omega
  unfold subgroup Generate.subgroupWith
  refine WP.seq (WP.mono (stagePower_ok true M (G.ready (M.context np))
    (M.qBuffer.ready (M.context np)) (by decide) sizeComb (fun h => Bool.noConfusion h))
    fun t ⟨Mt,V,C,F,E,_⟩ => ?_)
  have Y : operandValue t base (.local VG.Impl.Dsa.Layout.t) pLen=g^q%p := by
    unfold operandValue
    rw [local_pointer Mt.scr (by omega) (Nat.le_trans (Mt.wideFit (by decide)) Mt.extent),
      V,hg,M.qValue,VG.Proof.Dsa.decodeBE_encodeBE]
    exact Nat.lt_trans (Nat.mod_lt _ (by have := M.pLarge; omega)) M.valueBounds.1
  refine WP.mono (validateOne_ok Mt.scr Mt.saved rfl (by omega) (by omega) A.1
    (Mt.wideReady (by decide) np)) fun sf ⟨Ff,K,O⟩ => ?_
  have R := StageFrame.of_frame K (by decide) O np
  have Ef := R.execution (.inr ⟨rfl,rfl⟩)
  have Ct := C rfl
  rw [hg] at Ct
  exact ⟨Mt.keep Ef.mem Ef.keeps (by decide) (by decide),by unfold operandValue at Y; rw [Ff,F,Y],
    canonical_check (supported_widths M.widths) np Ct O,E.trans (Ef.schedule M.extent)⟩

theorem parameters_ok {base : Addr} {size pLen qLen p q g : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s)
    (G : CallerBuffer s base size (.input .g) pLen)
    (hg : operandValue s base (.input .g) pLen=g)
    (sizeComb : (layout ((pLen+7)/8) ((qLen+3)/4)).size≤size) :
    WP isa (parameters pLen qLen) s fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf=flagW base (Layout.field .mask) s &&&
        mask32 ((1<g ∧ g<p) ∧ (p-1)%q=0 ∧ g^q%p=1) ∧
      canonical ((pLen+7)/8) ((qLen+3)/4) p g base sf.mem ∧ ScheduleFrame base size s sf := by
  unfold parameters
  refine WP.seq (WP.mono (generateDomain_ok M G hg) fun t ⟨Mt,F,E⟩ => ?_)
  refine WP.mono (subgroup_ok Mt (E.buffer G (by decide))
    ((E.value G (by decide) M.extent).trans hg) sizeComb) fun sf ⟨Mf,Ff,C,Ef⟩ => ?_
  refine ⟨Mf,?_,C,(E.schedule M.extent).trans Ef⟩
  rw [Ff,F]
  simp only [BitVec.and_assoc,mask32_and,and_assoc]

end VG.Proof.Dsa.X86.Comb
