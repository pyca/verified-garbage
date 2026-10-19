module
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Pre

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Fwd
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Inv
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Fwd
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Gs
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Inv
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.InvPass1
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Words
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16

def contract (op : Poly → Poly) (symbol : String) (H : List Nat) : Contract isa where
  pre s := Input s symbol H
  post s t := PolyIs t.mem (s.gpr .x0) (op (polyAt s.mem (s.gpr .x0)))
  pub s t := s.sp=t.sp ∧ s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.syms symbol=t.syms symbol

def fwdContract : Contract isa := contract ntt "VG_MLKEM_NTT16_ZETAS" tableHalves
def invContract : Contract isa := contract nttInv "VG_MLKEM_INTT16_ZETAS" invTableHalves

theorem fwd_correct (s : State) (h : fwdContract.pre s) :
    ∃ tr t, Exec isa Impl.MlKem.AArch64.Ntt16.Readonly.fwd s tr t ∧
      abiPreserved s t ∧ fwdContract.post s t := by
  obtain ⟨tr,t,he,_,hf⟩ := fwd_ok s h
  exact ⟨tr,t,he,abi_of rfl (by lit_decide) he (by lit_decide),hf⟩

theorem inv_correct (s : State) (h : invContract.pre s) :
    ∃ tr t, Exec isa Impl.MlKem.AArch64.Ntt16.Readonly.inv s tr t ∧
      abiPreserved s t ∧ invContract.post s t := by
  obtain ⟨tr,t,he,_,hf⟩ := inv_ok s h
  exact ⟨tr,t,he,abi_of rfl (by lit_decide) he (by lit_decide),hf⟩

theorem fwd_ct : ConstantTime isa fwdContract.pre fwdContract.pub
    Impl.MlKem.AArch64.Ntt16.Readonly.fwd := by
  have hp : ∀ s t, fwdContract.pre s → fwdContract.pre t → fwdContract.pub s t →
      VG.AArch64.Taint.AgreeS ["VG_MLKEM_NTT16_ZETAS"] (VG.AArch64.Taint.ofRegs [.x0,.x1]) s t := by
    intro s t _ _ h
    refine ⟨agree_of h.1 ?_,?_⟩
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact h.2.1
      · exact h.2.2.1
    · intro name hn
      rw [List.mem_singleton.mp hn]
      exact h.2.2.2
  exact VG.Taint.constantTime (A:=taintS ["VG_MLKEM_NTT16_ZETAS"])
    (VG.AArch64.Taint.ofRegs [.x0,.x1]) hp (by taint_decide)

theorem inv_ct : ConstantTime isa invContract.pre invContract.pub
    Impl.MlKem.AArch64.Ntt16.Readonly.inv := by
  have hp : ∀ s t, invContract.pre s → invContract.pre t → invContract.pub s t →
      VG.AArch64.Taint.AgreeS ["VG_MLKEM_INTT16_ZETAS"] (VG.AArch64.Taint.ofRegs [.x0,.x1]) s t := by
    intro s t _ _ h
    refine ⟨agree_of h.1 ?_,?_⟩
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact h.2.1
      · exact h.2.2.1
    · intro name hn
      rw [List.mem_singleton.mp hn]
      exact h.2.2.2
  exact VG.Taint.constantTime (A:=taintS ["VG_MLKEM_INTT16_ZETAS"])
    (VG.AArch64.Taint.ofRegs [.x0,.x1]) hp (by taint_decide)

end VG.Proof.MlKem.AArch64.Ntt16.Readonly
