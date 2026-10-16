module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Contract
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem.AArch64

theorem shared_pre {s : State} (op : Poly → Poly) (symbol : String) (H : List Nat)
    (W : List (BitVec 64)) (hl : W.length=64)
    (he : ∀ i<64,W.getD i 0=hw4 H i)
    (h : (inPlaceContract (abi.withConsts [(symbol,W)]) op).pre s) : Input s symbol H := by
  sig_pre [inPlaceContract,inPlaceSig,abi,argRegs,Abi.withConsts,Abi.constRegions,Abi.constsHeld,
    hl,stackBelow] at h
  obtain ⟨hd,held,fit,sep,ht,hw,disj,pfit,wfit,red⟩ := h
  simp only [hl,Nat.reduceMul] at hd held fit sep
  have hrd : s.rd=[⟨s.syms symbol,512⟩] := by
    rw [←List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    rfl
  refine ⟨⟨hw,disj,red⟩,?_,?_,?_,?_⟩
  · intro i hi
    exact (held i hi).trans (he i hi)
  · exact Covers.of_mem (fun r hr => List.mem_append_left _ (hrd ▸ hr))
  · exact (sep (polyRegion (fP s)) (by rw [hw]; exact List.mem_cons_self ..)).symm
  · exact (sep (polyRegion (sP s)) (by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).symm

end VG.Proof.MlKem.AArch64.Ntt16.Readonly
