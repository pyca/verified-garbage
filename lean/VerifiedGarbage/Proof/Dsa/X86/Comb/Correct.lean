module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Body


import VerifiedGarbage.Proof.Dsa.X86.Comb.BodyWide

public import VerifiedGarbage.Proof.Dsa.X86.Comb.ABI
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Lit

/-! Functional correctness of both callable comb helpers against their merged specs. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86.Pow (ws bytes numAt_eq8 numAt_eq4)

theorem scratch_fits {n e : Nat} (h : Supported n e) (prepare : Bool) :
    ∀ r ∈ scratch prepare n, r.1+r.2≤(layout n e).size := by
  cases prepare <;>
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem correct {n e : Nat} (supported : Supported n e) (prepare : Bool)
    (s : State) (h : (contract prepare n e).pre s) :
    ∃ tr t, Exec isa (body prepare n e) s tr t ∧ abiPreserved s t ∧ (contract prepare n e).post s t := by
  obtain ⟨A,Size,H⟩ := abi_of supported prepare h
  have M : wordsVal s.mem (ws s) (slot n 0) n = Proof.Dsa.ModPow.numAt s.mem (ws s) (slot n 0) (8*n) :=
    (numAt_eq8 ..).symm
  obtain ⟨tr,t,E,V,C,O,R,_,_⟩ := body_wide_ok supported prepare A.entry Size M A.gt_one A.odd
    (by simpa only [numAt_eq8] using H)
  have F : Frame [⟨ws s,bytes s⟩] s.mem t.mem := by
    intro x hx
    apply O x
    intro r hr
    have X := hx _ (List.mem_singleton_self _)
    have B := scratch_fits supported prepare r hr
    simp only [Region.Contains,ofs] at X ⊢
    omega
  have K : Proof.Dsa.ModPow.Keeps (ws s) (arg s 1).toNat (scratch prepare n) s.mem t.mem := by
    intro i hi hj
    apply O _
    intro r hr
    have bound := A.bound
    rw [show ofs (ws s) (ws s+BitVec.ofNat 64 i)=i by
      simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by dsimp only [bytes] at bound; omega)]]
    exact hj r hr
  refine ⟨tr,t,E,⟨R,?_⟩,?_⟩
  · exact F.readW (by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact A.retScratch) (by decide)
  · cases prepare
    · sig_post [contract,Proof.Dsa.FixedBaseComb.powerContract,Proof.Dsa.ModPow.sig,
        Proof.Dsa.FixedBaseComb.powerResult,layout,VG.Impl.Dsa.X86.Pow.layout,abi,argSlots,argVal,argBytes]
      refine ⟨?_,?_⟩
      · simpa only [numAt_eq8,numAt_eq4] using V
      · simpa only [scratch,Bool.false_eq_true,ite_false,List.append_nil] using K
    · sig_post [contract,Proof.Dsa.FixedBaseComb.prepareContract,Proof.Dsa.ModPow.sig,
        Proof.Dsa.FixedBaseComb.powerResult,layout,VG.Impl.Dsa.X86.Pow.layout,abi,argSlots,argVal,argBytes]
      refine ⟨?_,?_,?_⟩
      · simpa only [numAt_eq8,numAt_eq4] using V
      · simpa only [canonical,layout,VG.Impl.Dsa.X86.Pow.layout,numAt_eq8] using C rfl
      · have lengths : 8*Proof.Dsa.FixedBaseComb.contextWords (layout n e)=272*n := by
          unfold Proof.Dsa.FixedBaseComb.contextWords Spec.Rsa.FixedBaseComb.entries Spec.Rsa.FixedBaseComb.teeth
          change 8*((2+2^5)*n)=272*n
          omega
        change Proof.Dsa.ModPow.Keeps (ws s) (arg s 1).toNat
          (VG.Impl.Dsa.X86.Pow.scratch n ++ [(context n,8*Proof.Dsa.FixedBaseComb.contextWords (layout n e))]) s.mem t.mem
        rw [lengths]
        exact K

end VG.Proof.Dsa.X86.Comb
