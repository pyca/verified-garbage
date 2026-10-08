import VerifiedGarbage.Impl.Weierstrass.X86.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86.NafTableIO

/-! Store each cached Jacobian entry at addresses derived from the public counter. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem entryAddr_ok {K : JacWinCfg} {s : State} {base : Addr} {size j : Nat} (cache : Bool)
    (hs : Scr s base size) (h1 : 1≤j) (h16 : j≤16)
    (hb : s.gpr .esi=BitVec.ofNat 32 j) (ht : K.tbl+2560≤size) :
    WP isa (.block (K.entryAddr cache)) s fun t =>
      (t.gpr .edx).setWidth 64=
        off base (K.tbl+(if cache then 1536 else 0)+(if cache then 64 else 96)*(j-1)) ∧
      CKeeps [.eax,.ecx,.edx] s t := by
  have hj : BitVec.ofNat 32 j-1=BitVec.ofNat 32 (j-1) :=
    BitVec.ofNat_sub_ofNat_of_le j 1 (by decide) h1
  apply WP.of_runBlock
  simp only [JacWinCfg.entryAddr,runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,
    execAlu,execMul,hb,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags,Option.map_some,Option.bind_some,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left',hj]
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · cases cache <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,BitVec.toNat_ofNat,Nat.add_zero]
    · rw [show (96 : BitVec 32).toNat=96 from rfl,
        Nat.mod_eq_of_lt (show j-1<2^32 by omega),Nat.mul_comm (j-1),Offset.add_add]
      exact hs.ea (by omega)
    · rw [show (64 : BitVec 32).toNat=64 from rfl,
        Nat.mod_eq_of_lt (show j-1<2^32 by omega),Nat.mul_comm (j-1),Offset.add_add]
      exact hs.ea (by omega)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,
      hr.1,hr.2.1,hr.2.2,ite_false]

theorem storePart_ok {K : JacWinCfg} {s : State} {base : Addr} {size j : Nat} (cache : Bool)
    (hs : Scr s base size) (h1 : 1≤j) (h16 : j≤16)
    (hb : s.gpr .esi=BitVec.ofNat 32 j) (ht : K.tbl+2560≤size) (hT : K.T+160≤K.tbl) :
    WP isa (.block (K.storePart cache)) s fun t =>
      (∀ c<(if cache then 2 else 3),
        wordsVal t.mem base
          (K.tbl+(if cache then 1536 else 0)+(if cache then 64 else 96)*(j-1)+32*c) 4=
        wordsVal s.mem base (K.T+(if cache then 96 else 0)+32*c) 4) ∧
      Outside base (K.tbl+(if cache then 1536 else 0)+(if cache then 64 else 96)*(j-1))
        (if cache then 64 else 96) s.mem t.mem ∧ KeepRegs [.eax,.ecx,.edx] s t := by
  rw [JacWinCfg.storePart,WP.block_append_iff]
  refine WP.mono (entryAddr_ok cache hs h1 h16 hb ht) fun u ⟨pu,ku⟩ => ?_
  have hu := hs.of_keeps ku.keeps (by decide)
  refine WP.mono (nafCopyPieces_ok
    (a:=K.T+(if cache then 96 else 0))
    (o:=K.tbl+(if cache then 1536 else 0)+(if cache then 64 else 96)*(j-1))
    (if cache then 4 else 6) u hu
    (by cases cache <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] <;> omega)
    (by cases cache <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] <;> omega)
    (by cases cache <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] <;> omega)
    (fun i hi => hu.ea (by cases cache <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at hi ⊢ <;> omega))
    (fun i hi => nafTable_ea hu pu (by cases cache <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at hi ⊢ <;> omega)))
    fun t ⟨et,ot,gt,rt,wt⟩ => ?_
  refine ⟨fun c hc => ?_,?_,⟨fun r hr => (congrFun gt r).trans (ku.1 r hr),
    rt.trans ku.2.2.1,wt.trans ku.2.2.2⟩⟩
  · rw [nafCopy_field et (by cases cache <;>
      simp only [Bool.false_eq_true,ite_false,ite_true] at hc ⊢ <;> omega),ku.2.1]
  · rw [ku.2.1] at ot
    cases cache <;> exact ot

def storeW (K : JacWinCfg) (m : Nat) : List (Nat × Nat) :=
  [(K.tbl+96*m,96),(K.tbl+1536+64*m,64)]

theorem storeEntry_ok {K : JacWinCfg} {s : State} {base : Addr} {size j : Nat}
    (hs : Scr s base size) (h1 : 1≤j) (h16 : j≤16)
    (hb : s.gpr .esi=BitVec.ofNat 32 j) (ht : K.tbl+2560≤size) (hT : K.T+160≤K.tbl) :
    WP isa (.block K.storeEntry) s fun t =>
      (∀ c<5,wordsVal t.mem base (K.entry (j-1) c) 4=wordsVal s.mem base (K.T+32*c) 4) ∧
      Unch base (storeW K (j-1)) s.mem t.mem ∧ KeepRegs [.eax,.ecx,.edx] s t := by
  rw [JacWinCfg.storeEntry,WP.block_append_iff]
  refine WP.mono (storePart_ok false hs h1 h16 hb ht hT) fun u ⟨eu,ou,ku⟩ => ?_
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at eu ou
  have hu := hs.of_keepRegs ku (by decide)
  refine WP.mono (storePart_ok true hu h1 h16 ((ku.gpr _ (by decide)).trans hb) ht hT)
    fun t ⟨et,ot,kt⟩ => ?_
  simp only [ite_true] at et ot
  have hn := hs.nowrap
  refine ⟨fun c hc => ?_,ou.unch.trans ot.unch,
    ⟨fun r hr => (kt.gpr r hr).trans (ku.gpr r hr),kt.rd.trans ku.rd,kt.wr.trans ku.wr⟩⟩
  by_cases h3 : c<3
  · simp only [JacWinCfg.entry,h3,ite_true]
    rw [ot.wordsVal (by omega) (by omega),eu c h3]
  · have e := et (c-3) (by omega)
    rw [show K.T+96+32*(c-3)=K.T+32*c by omega] at e
    simp only [JacWinCfg.entry,h3,ite_false]
    rw [e,ou.wordsVal (by omega) (by omega)]

end VG.Proof.Weierstrass.X86.JWin
