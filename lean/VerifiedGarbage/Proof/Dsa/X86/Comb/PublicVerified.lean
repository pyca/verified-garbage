module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicBodyTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.Satisfiable
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Dsa.X86.Comb.ABI
public import VerifiedGarbage.Proof.Dsa.X86.Comb.BodyWide
import VerifiedGarbage.Proof.Dsa.X86.Comb.Correct
import VerifiedGarbage.Proof.Dsa.X86.Comb.PrivateBodyTiming

/-! The public helper satisfies the merged preparation contract, including timing. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Dsa.X86.Pow (ws bytes numAt_eq8 numAt_eq4)

theorem publicValues {n e : Nat} {s t : State} (H : (contract true n e).pub s t) :
    wordsVal s.mem (ws s) (slot n 0) n=wordsVal t.mem (ws t) (slot n 0) n ∧
    wordsVal s.mem (ws s) (slot n 5) n=wordsVal t.mem (ws t) (slot n 5) n ∧
    val32 s.mem (ws s) (slot n 8) e=val32 t.mem (ws t) (slot n 8) e := by
  sig_pub [contract,Proof.Dsa.FixedBaseComb.prepareContract,Proof.Dsa.ModPow.sig,
    layout,VG.Impl.Dsa.X86.Pow.layout,abi,argSlots,argVal,argBytes] at H
  sig_split H
  simp only [numAt_eq8,numAt_eq4,List.cons.injEq,and_true] at *
  with_reducible assumption

theorem publicNarrowRun {n e m size : Nat} {base : Addr} {s t : State} {tr : List Leak}
    (h : Supported n e) (E : Pow.Entry s base size) (hz : (layout n e).size≤size)
    (hv : wordsVal s.mem base (slot n 0) n=m) (hm : 1<m) (odd : m%2=1)
    (run : Exec isa (body true n e) s tr t) :
    ∃ u, Exec isa (body true n e) (narrowState n e base s) tr u := by
  obtain ⟨En,R,W⟩ := narrowResources E hz
  obtain ⟨trace,u,Run,_⟩ := body_ok h true En hv hm odd (fun eq => Bool.noConfusion eq)
  obtain ⟨rfl,_⟩ := Exec.det run (regionModel.inline Run R W).1
  exact ⟨u,Run⟩

theorem public_constantTime {n e : Nat} (h : Supported n e) :
    ConstantTime isa (contract true n e).pre (contract true n e).pub (body true n e) := by
  intro s t tr ur sf tf hs ht hp E F
  obtain ⟨A,As,_⟩ := abi_of h true hs
  obtain ⟨B,Bs,_⟩ := abi_of h true ht
  obtain ⟨SP,Arg⟩ := publicArgs true hp
  obtain ⟨M,G,X⟩ := publicValues hp
  have Base : ws s=ws t := congrArg (fun v : BitVec 32 => v.setWidth 64) Arg
  have Hm : 1<wordsVal s.mem (ws s) (slot n 0) n := by simpa only [numAt_eq8] using A.gt_one
  have Ho : wordsVal s.mem (ws s) (slot n 0) n%2=1 := by simpa only [numAt_eq8] using A.odd
  have Hmt : 1<wordsVal t.mem (ws t) (slot n 0) n := by simpa only [numAt_eq8] using B.gt_one
  have Hot : wordsVal t.mem (ws t) (slot n 0) n%2=1 := by simpa only [numAt_eq8] using B.odd
  obtain ⟨u,Eu⟩ := publicNarrowRun h A.entry As rfl Hm Ho E
  obtain ⟨v,Ev⟩ := publicNarrowRun h B.entry Bs rfl Hmt Hot F
  have En := (narrowResources A.entry As).1
  have Fn := (narrowResources B.entry Bs).1
  have Ra : readSrc (narrowState n e (ws s) s) (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg s 0) :=
    readSrc_widen (Covers.of_mem (fun _ hr => List.mem_append_left _ hr)) A.readArg
  have Rb : readSrc (narrowState n e (ws t) t) (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg t 0) :=
    readSrc_widen (Covers.of_mem (fun _ hr => List.mem_append_left _ hr)) B.readArg
  rw [←Base] at Fn Ev Rb
  refine (publicBody_relCT h (ws s) (wordsVal s.mem (ws s) (slot n 0) n)
    (wordsVal s.mem (ws s) (slot n 5) n) (val32 s.mem (ws s) (slot n 8) e) Hm Ho _ _ _ _ _ _ ?_ Eu Ev).1
  refine ⟨⟨En,rfl,rfl,rfl⟩,⟨Fn,?_,?_,?_⟩,SP,Arg,Ra,Rb⟩
  · simpa only [narrowState,State.withRegions_mem,Base] using M.symm
  · simpa only [narrowState,State.withRegions_mem,Base] using G.symm
  · simpa only [narrowState,State.withRegions_mem,Base] using X.symm

theorem public_verified {n e : Nat} (h : Supported n e) :
    Verified target (body true n e) (Proof.Dsa.FixedBaseComb.prepareContract (layout n e) abi 20) :=
  ⟨correct h true,public_constantTime h,satisfiable h true⟩

end VG.Proof.Dsa.X86.Comb
