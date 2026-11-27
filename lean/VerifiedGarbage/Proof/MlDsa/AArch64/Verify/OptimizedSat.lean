module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSat
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords

/-! ### `MlDsa.AArch64.Message.OptimizedVerifyRoots`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open Message.Optimized (rootRegions)

theorem verify_pre_extend {p : Params} {s : State}
    (h : (verifyContract p abi 16).pre (s.withRegions
      [⟨s.gpr .x0,p.pkLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,p.sigLen⟩] s.wr))
    (hr : StaticRoots 16 s)
    (hd : s.rd=[⟨s.gpr .x0,p.pkLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,p.sigLen⟩]++rootRegions s) :
    (verifyContract p (abi.withConsts signRootConsts) 16).pre s := by
  sig_pre [verifyContract,verifySig,abi,argRegs,List.range,List.range.loop] at h
  sig_pre [verifyContract,verifySig,abi,argRegs,Abi.withConsts,
    VG.Proof.MlDsa.AArch64.Sign.signRootConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,stackBelow,
    List.range,List.range.loop]
  obtain ⟨sp,wr,d1,d2,d3,k1,k2,k3,k4,n1,n2,n3,n4⟩ := h
  exact ⟨sp,by rw [hd]; rfl,hr.forward.held,hr.inverse.held,hr.forward.fit,hr.forward.writable,
    hr.forward.stack,hr.inverse.fit,hr.inverse.writable,hr.inverse.stack,hr.forward.aligned,hr.inverse.aligned,by rw [hd]; rfl,
    wr,d1,d2,d3,k1,k2,k3,k4,n1,n2,n3,n4⟩

end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (Ok3 StaticRoots signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized

def baseSat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 0x3200 | .x3 => 0x10000
    | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000,p.pkLen⟩,⟨0x3000,64⟩,⟨0x3200,p.sigLen⟩]
  wr := [⟨0x10000,KeyGen.scrLen p⟩]

def verifySatWith (p : Params) (m : Mem) : State :=
  { baseSat p with
    mem := m
    syms := fun name=>if name="VG_MLDSA_NTT_EXPANDED" then 1048576 else 1052480
    rd := (baseSat p).rd++[⟨1048576,3904⟩,⟨1052480,3904⟩] }

theorem verifySatWith_roots (p : Params) (hp : Ok3 p) (m : Mem)
    (hf : ∀j<488,m.readW (1048576+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀j<488,m.readW (1052480+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0) :
    StaticRoots 16 (verifySatWith p m) := by
  -- The tables' addresses as numerals first: in a term that holds `p` and `m` the kernel adds
  -- 3904 to an address, and takes its remainder by 64, in unary.
  have ef : (verifySatWith p m).syms "VG_MLDSA_NTT_EXPANDED" = 1048576 := rfl
  have ei : (verifySatWith p m).syms "VG_MLDSA_INV_FOLDED" = 1052480 := rfl
  refine ⟨⟨hf,by rw [ef]; decide,?_,?_,?_,by rw [ef]; decide⟩,
    ⟨hi,by rw [ei]; decide,?_,?_,?_,by rw [ei]; decide⟩⟩
  · apply Covers.one
    exact ⟨⟨1048576,3904⟩,by simp [verifySatWith],Region.contains_self _ _⟩
  · rcases hp with rfl|rfl|rfl
    all_goals dsimp [verifySatWith,baseSat]
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq]
    all_goals exact Region.disjoint_of_sep (by decide +kernel)
  · exact Region.disjoint_of_sep (by dsimp [verifySatWith,baseSat]; decide)
  · apply Covers.one
    exact ⟨⟨1052480,3904⟩,by simp [verifySatWith],Region.contains_self _ _⟩
  · rcases hp with rfl|rfl|rfl
    all_goals dsimp [verifySatWith,baseSat]
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq]
    all_goals exact Region.disjoint_of_sep (by decide +kernel)
  · exact Region.disjoint_of_sep (by dsimp [verifySatWith,baseSat]; decide)

theorem verifySatWith_pre (p : Params) (hp : Ok3 p) (m : Mem)
    (hf : ∀j<488,m.readW (1048576+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀j<488,m.readW (1052480+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0) :
    (verifyContract p (abi.withConsts signRootConsts) 16).pre (verifySatWith p m) := by
  apply Message.OptimizedVerify.verify_pre_extend ?_ (verifySatWith_roots p hp m hf hi) rfl
  have hb : (verifyContract p abi 16).pre (baseSat p) := by
    rcases hp with rfl|rfl|rfl
    all_goals sig_sat_check [verifyContract,verifySig,abi,argRegs,baseSat,List.range,List.range.loop]
  sig_pre [verifyContract,verifySig,abi,argRegs,List.range,List.range.loop] at hb ⊢
  exact hb

end VG.Proof.MlDsa.AArch64.Verify.Optimized
