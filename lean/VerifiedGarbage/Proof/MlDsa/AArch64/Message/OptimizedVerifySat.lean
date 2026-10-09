import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSat

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Sign (Ok3)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized

theorem vPre_spec {p : Params} {s : State} (h : VPre p s) :
    (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre s := by
  sig_pre [verifyMessageContract,verifyMessageSig,abi,argRegs,Abi.withConsts,
    VG.Proof.MlDsa.AArch64.Sign.signRootConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,stackBelow,
    List.range,List.range.loop]
  refine ⟨h.sp,?_,h.roots.forward.held,h.roots.inverse.held,h.roots.forward.fit,
    h.roots.forward.writable,h.roots.forward.stack,h.roots.inverse.fit,
    h.roots.inverse.writable,h.roots.inverse.stack,?_,h.wr,
    h.pkScr,h.msgScr,h.ctxScr,h.sigScr,
    h.stkPk,h.stkMsg,h.stkCtx,h.stkSig,h.stkScr,
    h.nPk,h.nMsg,h.nCtx,h.nSig,h.nScr⟩
  · rw [h.rd]; rfl
  · rw [h.rd]; rfl

private def baseSat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x3 => 0x3100 | .x5 => 0x3200 | .x6 => 0x10000
    | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000,p.pkLen⟩,⟨0x3000,0⟩,⟨0x3100,0⟩,⟨0x3200,p.sigLen⟩]
  wr := [⟨0x10000,mScrLen p⟩]

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
  refine ⟨⟨hf,by dsimp [verifySatWith]; decide,?_,?_,?_⟩,
    ⟨hi,by dsimp [verifySatWith]; decide,?_,?_,?_⟩⟩
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


private theorem baseSat_pre (p : Params) (hp : Ok3 p) :
    (verifyMessageContract p abi 16).pre (baseSat p) := by
  rcases hp with rfl|rfl|rfl
  all_goals sig_sat_check [verifyMessageContract,verifyMessageSig,abi,argRegs,
    baseSat,List.range,List.range.loop]

theorem verifySatWith_state (p : Params) (hp : Ok3 p) (m : Mem)
    (hr : StaticRoots 16 (verifySatWith p m)) : VPre p (verifySatWith p m) := by
  have h := Message.vPre_of (baseSat_pre p hp)
  exact ⟨h.sp,rfl,h.wr,h.pkScr,h.msgScr,h.ctxScr,h.sigScr,h.stkPk,h.stkMsg,h.stkCtx,h.stkSig,h.stkScr,
    h.nPk,h.nMsg,h.nCtx,h.nSig,h.nScr,hr⟩


theorem verifySatWith_pre (p : Params) (hp : Ok3 p) (m : Mem)
    (hf : ∀j<488,m.readW (1048576+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀j<488,m.readW (1052480+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0) :
    (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre (verifySatWith p m) :=
  vPre_spec (verifySatWith_state p hp m (verifySatWith_roots p hp m hf hi))

def verifySat (p : Params) : State := verifySatWith p (Sign.optimizedSignSat mlDsa44).mem

theorem verify_sat {p : Params} (hp : Ok3 p) :
    (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre (verifySat p) := by
  have hr := (Sign.staticRoots_entry (by decide +kernel) (Sign.optimizedSign_sat (.inl rfl))).2
  apply verifySatWith_pre p hp
  · exact hr.forward.held
  · exact hr.inverse.held

end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
