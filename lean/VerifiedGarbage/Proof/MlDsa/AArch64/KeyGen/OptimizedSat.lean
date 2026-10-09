import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedEntry
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSat

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts signRootConsts_eq)
open VG.Proof.MlDsa.AArch64.Optimized

theorem staticRoots_pre {p : Params} {S : Nat} {s : State} (hS : 0<S)
    (hk : kgPre p S s) (hr : StaticRoots S s)
    (hrd : s.rd=[⟨s.gpr .x0,32⟩] ++
      [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩]) :
    (keyGenContract p (abi.withConsts signRootConsts) S).pre s := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hS)
  obtain ⟨hk,_⟩ := hk
  sig_pre [keyGenContract,keyGenSig,abi,argRegs,stackBelow] at hk
  obtain ⟨hsp,hw,d1,d2,d3,d4,d5,d6,k1,k2,k3,k4,n1,n2,n3,n4⟩ := hk
  sig_pre [keyGenContract,keyGenSig,abi,argRegs,Abi.withConsts,signRootConsts_eq,
    nttConsts_eq,Inverse.inverseConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,stackBelow]
  refine ⟨hsp,?_,hr.forward.held,hr.inverse.held,hr.forward.fit,hr.forward.writable,
    hr.forward.stack,hr.inverse.fit,hr.inverse.writable,hr.inverse.stack,?_,hw,
    d1,d2,d3,d4,d5,d6,k1,k2,k3,k4,n1,n2,n3,n4⟩
  · rw [hrd]; rfl
  · rw [hrd]; rfl

def keyGenSatWith (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x4000 | .x2 => 0x5000 | .x3 => 0x10000 | _ => 0
  sp := 0x80000
  mem := m
  syms := fun name => if name="VG_MLDSA_NTT_EXPANDED" then 1048576 else 1052480
  rd := [⟨0x1000,32⟩,⟨1048576,3904⟩,⟨1052480,3904⟩]
  wr := [⟨0x4000,p.pkLen⟩,⟨0x5000,p.skLen⟩,⟨0x10000,scrLen p⟩]

theorem keyGenSatWith_pre {p : Params} (hp : p=mlDsa44∨p=mlDsa65∨p=mlDsa87) (m : Mem)
    (hf : ∀j<488,m.readW (1048576+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀j<488,m.readW (1052480+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0) :
    (keyGenContract p (abi.withConsts signRootConsts) 16).pre (keyGenSatWith p m) := by
  apply staticRoots_pre (by decide)
  · constructor
    · rcases hp with rfl|rfl|rfl
      all_goals sig_pre [keyGenContract,keyGenSig,abi,argRegs,keyGenSatWith]
      all_goals sig_and_intros
      all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide
    · simp only [keyGenSatWith,List.mem_cons]; exact .inl True.intro
  · refine ⟨⟨hf,?_,?_,?_,?_⟩,⟨hi,?_,?_,?_,?_⟩⟩
    · dsimp [keyGenSatWith,Sign.optimizedSignSat,Sign.optimizedSignSatWith]; decide
    · apply Covers.one
      exact ⟨⟨1048576,3904⟩,by simp [keyGenSatWith],Region.contains_self _ _⟩
    · rcases hp with rfl|rfl|rfl
      all_goals dsimp [keyGenSatWith,Sign.optimizedSignSat,Sign.optimizedSignSatWith]
      all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      all_goals sig_and_intros
      all_goals exact Region.disjoint_of_sep (by decide)
    · dsimp [keyGenSatWith,Sign.optimizedSignSat,Sign.optimizedSignSatWith]
      exact Region.disjoint_of_sep (by decide)
    · dsimp [keyGenSatWith,Sign.optimizedSignSat,Sign.optimizedSignSatWith]; decide
    · apply Covers.one
      exact ⟨⟨1052480,3904⟩,by simp [keyGenSatWith],Region.contains_self _ _⟩
    · rcases hp with rfl|rfl|rfl
      all_goals dsimp [keyGenSatWith,Sign.optimizedSignSat,Sign.optimizedSignSatWith]
      all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      all_goals sig_and_intros
      all_goals exact Region.disjoint_of_sep (by decide)
    · dsimp [keyGenSatWith,Sign.optimizedSignSat,Sign.optimizedSignSatWith]
      exact Region.disjoint_of_sep (by decide)
  · rfl

def keyGenSat (p : Params) : State := keyGenSatWith p (Sign.optimizedSignSat p).mem

theorem keyGen_sat {p : Params} (hp : p=mlDsa44∨p=mlDsa65∨p=mlDsa87) :
    (keyGenContract p (abi.withConsts signRootConsts) 16).pre (keyGenSat p) := by
  have roots := (Sign.staticRoots_entry (by decide : 0<Sign.signStack) (Sign.optimizedSign_sat hp)).2
  apply keyGenSatWith_pre hp
  · simpa only [Sign.optimizedSignSat,Sign.optimizedSignSatWith,ite_true] using roots.forward.held
  · simpa only [Sign.optimizedSignSat,Sign.optimizedSignSatWith,
      show ("VG_MLDSA_INV_FOLDED"="VG_MLDSA_NTT_EXPANDED")=False from by decide,ite_false] using roots.inverse.held

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
