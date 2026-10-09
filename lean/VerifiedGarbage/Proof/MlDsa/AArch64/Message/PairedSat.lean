import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Verified
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedSignSat

namespace VG.Proof.MlDsa.AArch64.Message.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Sign (Ok3)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots PairedRoots pairedSignRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized

theorem sPre_spec {p : Params} {s : State} (h : SPre p s) :
    (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pre s := by
  sig_pre [signMessageContract,signMessageSig,abi,argRegs,Abi.withConsts,
    VG.Proof.MlDsa.AArch64.Sign.pairedSignRootConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,PairedTable.expandedWords_length,stackBelow,
    List.range,List.range.loop]
  refine ⟨h.sp,?_,h.roots.forward.held,h.roots.inverse.held,h.paired.held,h.roots.forward.fit,
    h.roots.forward.writable,h.roots.forward.stack,h.roots.inverse.fit,
    h.roots.inverse.writable,h.roots.inverse.stack,h.paired.fit,h.paired.writable,h.paired.stack,?_,h.wr,
    h.skSig,h.skScr,h.msgSig,h.msgScr,h.ctxSig,h.ctxScr,h.rndSig,h.rndScr,h.sigScr,
    h.stkSk,h.stkMsg,h.stkCtx,h.stkRnd,h.stkSig,h.stkScr,
    h.nSk,h.nMsg,h.nCtx,h.nRnd,h.nSig,h.nScr⟩
  · rw [h.rd]; rfl
  · rw [h.rd]; rfl

def signSatWith (p : Params) (m : Mem) : State :=
  { Message.signSat p with
    mem := m
    syms := fun name=>if name="VG_MLDSA_NTT_EXPANDED" then 1048576 else if name="VG_MLDSA_INV_FOLDED" then 1052480 else 1056384
    rd := (Message.signSat p).rd++[⟨1048576,3904⟩,⟨1052480,3904⟩,⟨1056384,4096⟩] }

theorem signSatWith_roots (p : Params) (hp : Ok3 p) (m : Mem)
    (hf : ∀j<488,m.readW (1048576+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀j<488,m.readW (1052480+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0) :
    StaticRoots 16 (signSatWith p m) := by
  refine ⟨⟨hf,by dsimp [signSatWith]; decide,?_,?_,?_⟩,
    ⟨hi,by dsimp [signSatWith]; decide,?_,?_,?_⟩⟩
  · apply Covers.one
    exact ⟨⟨1048576,3904⟩,by simp [signSatWith],Region.contains_self _ _⟩
  · rcases hp with rfl|rfl|rfl
    all_goals dsimp [signSatWith,Message.signSat]
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    all_goals constructor <;> exact Region.disjoint_of_sep (by decide +kernel)
  · exact Region.disjoint_of_sep (by dsimp [signSatWith,Message.signSat]; decide)
  · apply Covers.one
    exact ⟨⟨1052480,3904⟩,by simp [signSatWith],Region.contains_self _ _⟩
  · rcases hp with rfl|rfl|rfl
    all_goals dsimp [signSatWith,Message.signSat]
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    all_goals constructor <;> exact Region.disjoint_of_sep (by decide +kernel)
  · exact Region.disjoint_of_sep (by dsimp [signSatWith,Message.signSat]; decide)


private theorem baseSat_pre (p : Params) (hp : Ok3 p) :
    (signMessageContract p abi 16).pre (Message.signSat p) := by
  rcases hp with rfl|rfl|rfl
  all_goals sig_sat_check [signMessageContract,signMessageSig,abi,argRegs,
    Message.signSat,List.range,List.range.loop]

theorem signSatWith_state (p : Params) (hp : Ok3 p) (m : Mem)
    (hr : StaticRoots 16 (signSatWith p m)) (rp : PairedRoots 16 (signSatWith p m)) : SPre p (signSatWith p m) := by
  have h := Message.sPre_of (baseSat_pre p hp)
  exact ⟨h.sp,rfl,h.wr,h.skSig,h.skScr,h.msgSig,h.msgScr,h.ctxSig,h.ctxScr,
    h.rndSig,h.rndScr,h.sigScr,h.stkSk,h.stkMsg,h.stkCtx,h.stkRnd,h.stkSig,h.stkScr,
    h.nSk,h.nMsg,h.nCtx,h.nRnd,h.nSig,h.nScr,hr,rp⟩


theorem signSatWith_paired (p : Params) (hp : Ok3 p) (m : Mem)
    (hr : ∀j<512,m.readW (1056384+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Paired.expandedWords.getD j 0) :
    PairedRoots 16 (signSatWith p m) := by
  refine ⟨hr,by dsimp [signSatWith]; decide,?_,?_,?_⟩
  · apply Covers.one
    exact ⟨⟨1056384,4096⟩,by simp [signSatWith],Region.contains_self _ _⟩
  · rcases hp with rfl|rfl|rfl
    all_goals dsimp [signSatWith,Message.signSat]
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    all_goals constructor <;> exact Region.disjoint_of_sep (by decide +kernel)
  · exact Region.disjoint_of_sep (by dsimp [signSatWith,Message.signSat]; decide)

theorem signSatWith_pre (p : Params) (hp : Ok3 p) (m : Mem)
    (hf : ∀j<488,m.readW (1048576+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀j<488,m.readW (1052480+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0)
    (hr : ∀j<512,m.readW (1056384+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Paired.expandedWords.getD j 0) :
    (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pre (signSatWith p m) :=
  sPre_spec (signSatWith_state p hp m (signSatWith_roots p hp m hf hi) (signSatWith_paired p hp m hr))

def signSat (p : Params) : State := signSatWith p (Sign.pairedSignSat mlDsa44).mem

theorem sign_sat {p : Params} (hp : Ok3 p) :
    (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pre (signSat p) := by
  have hr := (Sign.pairedRoots_entry (by decide +kernel) (Sign.pairedSign_sat (.inl rfl))).2
  apply signSatWith_pre p hp
  · exact hr.1.forward.held
  · exact hr.1.inverse.held
  · exact hr.2.held

end VG.Proof.MlDsa.AArch64.Message.Paired
