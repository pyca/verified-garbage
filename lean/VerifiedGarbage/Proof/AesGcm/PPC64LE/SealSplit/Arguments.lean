module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Call
public import VerifiedGarbage.Proof.Gcm.SplitBlocksContract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: permissions and non-aliasing for the split helper call.
/-! # Split-seal outgoing call layout -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit.Call
open VG VG.PPC64LE

structure Layout (V : Reg → BitVec 64) (sp S : Addr) (count : Nat) (s : State) : Prop where
  bound : count≤(V .r23).toNat
  source : s.gpr .r7=S
  countReg : s.gpr .r8=BitVec.ofNat 64 count
  reads : Covers [⟨S,count⟩] (s.rd++s.wr)
  fit : S.toNat+count≤2^64
  st : (⟨S,count⟩ : Region).Disjoint ⟨V .r30,80⟩
  data : (⟨S,count⟩ : Region).Disjoint ⟨V .r27,(V .r23).toNat⟩
  work : (⟨S,count⟩ : Region).Disjoint ⟨V .r31,2560⟩
  slotWrite : InRegions s.wr (sp+96) 8
  stackFit : sp.toNat+104≤2^64
  slotFit : (sp+96).toNat+8≤2^64
  slotContext : (⟨sp+96,8⟩ : Region).Disjoint ⟨V .r29,256⟩
  slotState : (⟨sp+96,8⟩ : Region).Disjoint ⟨V .r30,80⟩
  slotData : (⟨sp+96,8⟩ : Region).Disjoint ⟨V .r27,(V .r23).toNat⟩
  slotWork : (⟨sp+96,8⟩ : Region).Disjoint ⟨V .r31,2560⟩
  slotSource : (⟨sp+96,8⟩ : Region).Disjoint ⟨S,count⟩


theorem args_values {V : Reg → BitVec 64} {sp S : Addr} {count : Nat} {s : State}
    (he : Env V sp s) (lay : Layout V sp S count s) :
    (argsState s).gpr .r3=V .r29 ∧ (argsState s).gpr .r4=V .r28 ∧
    (argsState s).gpr .r5=V .r30+48 ∧ (argsState s).gpr .r6=V .r30+16 ∧
    (argsState s).gpr .r7=S ∧ (argsState s).gpr .r8=BitVec.ofNat 64 (count/16) ∧
    (argsState s).gpr .r9=V .r27 ∧ (argsState s).gpr .r10=BitVec.ofNat 64 ((V .r23).toNat/16) ∧
    (argsState s).mem.readW ((argsState s).sp+96) 64=V .r31+448 := by
  have hc : count<2^64 := Nat.lt_of_le_of_lt lay.bound (V .r23).isLt
  have hn : V .r23 >>> 4=BitVec.ofNat 64 ((V .r23).toNat/16) := by
    have hh := shr4 (V .r23).isLt
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using hh
  simp only [argsState,argsRegs,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,
    he.r29,he.r30,he.r31,he.fr .r28 (by decide),he.fr .r27 (by decide),he.fr .r23 (by decide),
    lay.source,lay.countReg,shr4 hc,hn,RegUpd.sp_write,he.sp,Mem.readW_writeW_self64,true_and]


theorem args_pre {V : Reg → BitVec 64} {sp S : Addr} {count R : Nat} {s : State}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (lay : Layout V sp S count s) (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14) :
    (Proof.Gcm.encryptBlocksSplitContract PPC64LE.abi).pre
      ((argsState s).callEntry.withRegions (reads (argsState s)) (writes (argsState s))) := by
  obtain ⟨h3,h4,h5,h6,h7,h8,h9,h10,hw⟩ := args_values he lay
  have hc : count/16<2^64 := by have := lay.bound; have := (V .r23).isLt; omega
  have hn : (V .r23).toNat/16<2^64 := by have := (V .r23).isLt; omega
  have hr : R<2^64 := by rcases hv with h | h | h <;> omega
  sig_eval [Proof.Gcm.encryptBlocksSplitContract,Proof.Gcm.encryptBlocksSplitSig,Proof.Gcm.encryptBlocksSplitPre,
    PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop]
  simp only [reads,writes,argsState,argsRegs,RegUpd.gpr_write,RegUpd.sp_write,reduceCtorEq,ite_false,ite_true,
    Mem.readW_writeW_self64,he.r29,he.r30,he.r31,he.fr .r28 (by decide),he.fr .r27 (by decide),
    he.fr .r23 (by decide),he.sp,lay.source,lay.countReg,shr4 (Nat.lt_of_le_of_lt lay.bound (V .r23).isLt),
    hR,toNat64 hc,toNat64 hr]
  have h23 : (V .r23 >>> 4).toNat=(V .r23).toNat/16 := by
    have hh := shr4 (V .r23).isLt
    rw [BitVec.ofNat_toNat,BitVec.setWidth_eq] at hh
    rw [hh,toNat64 hn]
  have hslt : (s.mem.writeW (sp+96) (V .r31+448)).readW (sp+96#64) 64=V .r31+448 :=
    Mem.readW_writeW_self64 _ _ _
  simp only [h23,hslt]
  have dp := hd.take (k := ((V .r23).toNat/16)*16) (by omega)
  have src := Region.sub_prefix (by omega : count/16*16≤count) (base := S)
  refine ⟨by have := lay.stackFit; omega,rfl,trivial,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,L.cw,?_,?_,?_,dp.ok.fit,?_,hv,by have := lay.bound; omega⟩
  · exact L.cs.sub_right (Lay.stSub (d := 48) (n := 16) (by decide))
  · exact L.cs.sub_right (Lay.stSub (d := 16) (n := 16) (by decide))
  · exact dp.ctx
  · exact L.cw'.sub_right (Lay.wSub (d := 448) (n := 2112) (by decide))
  · exact Lay.st_st (a := 48) (n := 16) (d := 16) (k := 16) (by decide) (by decide) (by decide)
  · exact (lay.st.sub_left src).symm.sub_left (Lay.stSub (d := 48) (n := 16) (by decide))
  · exact dp.ok.st.symm.sub_left (Lay.stSub (d := 48) (n := 16) (by decide))
  · exact L.st_w (a := 48) (n := 16) (d := 448) (k := 2112) (by decide) (.inr ⟨by decide,by decide⟩)
  · exact lay.slotState.symm.sub_left (Lay.stSub (d := 48) (n := 16) (by decide))
  · exact (lay.st.sub_left src).symm.sub_left (Lay.stSub (d := 16) (n := 16) (by decide))
  · exact dp.ok.st.symm.sub_left (Lay.stSub (d := 16) (n := 16) (by decide))
  · exact L.st_w (a := 16) (n := 16) (d := 448) (k := 2112) (by decide) (.inr ⟨by decide,by decide⟩)
  · exact lay.slotState.symm.sub_left (Lay.stSub (d := 16) (n := 16) (by decide))
  · exact (lay.data.sub_left src).sub_right (Region.sub_prefix (by omega))
  · exact (lay.work.sub_left src).sub_right (Lay.wSub (d := 448) (n := 2112) (by decide))
  · exact dp.ok.w.sub_right (Lay.wSub (d := 448) (n := 2112) (by decide))
  · exact lay.slotData.symm.sub_left (Region.sub_prefix (by omega))
  · exact lay.slotWork.symm.sub_left (Lay.wSub (d := 448) (n := 2112) (by decide))
  · exact SealFused.fit_offset _ L.sw (by decide) (off := 48) (n := 16) (by decide)
  · exact SealFused.fit_offset _ L.sw (by decide) (off := 16) (n := 16) (by decide)
  · have := lay.fit; omega
  · exact SealFused.fit_offset _ L.ww (by decide) (off := 448) (n := 2112) (by decide)


theorem args_regions {V : Reg → BitVec 64} {sp S : Addr} {count : Nat} {s : State}
    (he : Env V sp s) (lay : Layout V sp S count s) :
    reads (argsState s)=[⟨V .r29,256⟩,⟨S,count/16*16⟩,⟨sp+96,8⟩] ∧
    writes (argsState s)=[⟨V .r30+48,16⟩,⟨V .r30+16,16⟩,
      ⟨V .r27,(V .r23).toNat/16*16⟩,⟨V .r31+448,2112⟩] := by
  obtain ⟨h3,_,h5,h6,h7,h8,h9,h10,hw⟩ := args_values he lay
  have hc : count/16<2^64 := by have := lay.bound; have := (V .r23).isLt; omega
  have hn : (V .r23).toNat/16<2^64 := by have := (V .r23).isLt; omega
  simp only [reads,writes,h3,h5,h6,h7,h8,h9,h10,hw,toNat64 hc,toNat64 hn]
  exact ⟨by rw [show (argsState s).sp=sp by exact he.sp],trivial⟩


theorem args_env {V : Reg → BitVec 64} {sp S : Addr} {count : Nat} {s : State}
    (he : Env V sp s) (lay : Layout V sp S count s) : Env V sp (argsState s) := by
  have hk := args_keep s (by rw [he.sp]; exact lay.slotWrite)
  exact he.keep (fun r hr => hk.gpr (by
    have hp : ∀ r ∈ frozen, r ∉ registers := by decide
    exact hp r hr)) rfl hk.2.1 hk.2.2


theorem args_config {V : Reg → BitVec 64} {sp S : Addr} {count R : Nat} {s : State}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (lay : Layout V sp S count s) (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14) :
    Config (argsState s) := by
  obtain ⟨hr,hw⟩ := args_regions he lay
  have hk := args_keep s (by rw [he.sp]; exact lay.slotWrite)
  have ww : Covers (writes (argsState s)) (argsState s).wr := by
    rw [hw,hk.2.2]
    have dp := hd.take (k := (V .r23).toNat/16*16) (by omega)
    exact Covers.cons (he.perm.stC (d := 48) (n := 16) (by decide))
      (Covers.cons (he.perm.stC (d := 16) (n := 16) (by decide))
        (Covers.cons dp.wr (he.perm.wC (d := 448) (n := 2112) (by decide))))
  refine ⟨args_pre L he hd lay hR hv,?_,ww⟩
  apply Covers.append_left
  · rw [hr,hk.2.1,hk.2.2]
    exact Covers.cons he.perm.ctx (Covers.cons (covers_prefix lay.reads (by omega))
      (Covers.one (in_left lay.slotWrite)))
  · exact Covers.right ww


end VG.Proof.AesGcm.PPC64LE.SealSplit.Call
