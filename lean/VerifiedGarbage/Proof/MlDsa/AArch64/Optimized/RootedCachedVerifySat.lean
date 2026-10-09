import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifySat

namespace VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts Ok3)
open VG.Spec.Sha3 (bytesAt)

theorem cachedPre_spec {p : Params} {s : State} (h : CachedPre p s) :
    (verifyMessageCachedContract p (abi.withConsts signRootConsts) 16).pre s := by
  sig_pre [verifyMessageCachedContract,verifyMessageCachedSig,abi,argRegs,Abi.withConsts,
    Sign.signRootConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,stackBelow,
    List.range,List.range.loop]
  refine ⟨h.sp,?_,h.roots.forward.held,h.roots.inverse.held,h.roots.forward.fit,
    h.roots.forward.writable,h.roots.forward.stack,h.roots.inverse.fit,
    h.roots.inverse.writable,h.roots.inverse.stack,?_,h.wr,
    h.pkScr,h.msgScr,h.ctxScr,h.sigScr,h.trScr.symm,
    h.stkPk,h.stkMsg,h.stkCtx,h.stkSig,h.stkScr,h.stkTr,
    h.nPk,h.nMsg,h.nCtx,h.nSig,h.nScr,h.nTr,h.digest⟩
  · rw [h.rd];rfl
  · rw [h.rd];rfl

private def tableMem : Mem := (Sign.optimizedSignSat mlDsa44).mem

def satMem (p : Params) : Mem := fun a=>
  if a.toNat<1048576 then CachedVerify.satMem p a else tableMem a

def verifySat (p : Params) : State :=
  { CachedVerify.verifySat p with
    mem:=satMem p
    syms:=fun nm=>if nm="VG_MLDSA_NTT_EXPANDED" then 1048576 else 1052480
    rd:=(CachedVerify.verifySat p).rd++[⟨1048576,3904⟩,⟨1052480,3904⟩] }

private theorem satMem_low (p : Params) (a : Addr) (n : Nat) (ha : a.toNat+n≤1048576) :
    bytesAt (satMem p) a n=bytesAt (CachedVerify.satMem p) a n := by
  apply Proof.MlKem.bytesAt_congr
  intro i hi
  have e : (a+BitVec.ofNat 64 i).toNat=a.toNat+i := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    have := a.isLt
    omega
  have hh : a.toNat+i<1048576 := by omega
  simp only [satMem,e,hh,ite_true]

private theorem satMem_high (p : Params) (a : Addr) (ha : 1048576≤a.toNat) (hb : a.toNat+8≤2^64) :
    (satMem p).readW a 64=tableMem.readW a 64 := by
  apply Mem.readW_congr
  intro i hi
  have e : (a+BitVec.ofNat 64 i).toNat=a.toNat+i := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  have hh : ¬a.toNat+i<1048576 := by omega
  simp only [satMem,e,hh,ite_false]

private theorem roots (p : Params) (hp : Ok3 p) : StaticRoots 16 (verifySat p) := by
  have src := (Sign.staticRoots_entry (by decide +kernel) (Sign.optimizedSign_sat (.inl rfl))).2
  have heldF : ∀j<488,(satMem p).readW (1048576+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0 := by
    intro j hj
    rw [satMem_high p _ (by bv_omega) (by bv_omega)]
    exact src.forward.held j hj
  have heldI : ∀j<488,(satMem p).readW (1052480+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0 := by
    intro j hj
    rw [satMem_high p _ (by bv_omega) (by bv_omega)]
    exact src.inverse.held j hj
  have h := Message.OptimizedVerify.verifySatWith_roots p hp (satMem p) heldF heldI
  refine ⟨⟨h.forward.held,h.forward.fit,?_,h.forward.writable,h.forward.stack⟩,
    ⟨h.inverse.held,h.inverse.fit,?_,h.inverse.writable,h.inverse.stack⟩⟩
  · apply Covers.one
    exact ⟨⟨1048576,3904⟩,by simp [verifySat],Region.contains_self _ _⟩
  · apply Covers.one
    exact ⟨⟨1052480,3904⟩,by simp [verifySat],Region.contains_self _ _⟩

private theorem base_pre (p : Params) (hp : Ok3 p) :
    (verifyMessageCachedContract p abi 16).pre (CachedVerify.verifySat p) := by
  rcases hp with rfl|rfl|rfl <;>
    sig_pre [verifyMessageCachedContract,verifyMessageCachedSig,abi,argRegs,List.range,List.range.loop] <;> sig_and_intros
  all_goals first
    | exact CachedVerify.satMem_digest (by decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem verify_sat {p : Params} (hp : Ok3 p) :
    (verifyMessageCachedContract p (abi.withConsts signRootConsts) 16).pre (verifySat p) := by
  have h := CachedVerify.cachedPre_of (base_pre p hp)
  apply cachedPre_spec
  refine ⟨h.sp,rfl,h.wr,h.pkScr,h.msgScr,h.ctxScr,h.sigScr,h.stkPk,h.stkMsg,h.stkCtx,
    h.stkSig,h.stkScr,h.nPk,h.nMsg,h.nCtx,h.nSig,h.nScr,h.trScr,h.stkTr,h.nTr,?_,roots p hp⟩
  change bytesAt (satMem p) 0x8000 64=pkTr (bytesAt (satMem p) 0x1000 p.pkLen)
  rw [satMem_low p _ _ (by decide),satMem_low p _ _ (by rcases hp with rfl|rfl|rfl <;> decide)]
  exact h.digest

end VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
