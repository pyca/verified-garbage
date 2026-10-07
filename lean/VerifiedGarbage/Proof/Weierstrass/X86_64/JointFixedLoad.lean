import VerifiedGarbage.Impl.Weierstrass.X86_64.JointFixed
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafExternalCopy
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem jointFixedAddress_ok {s : State} {n a : Nat} {T : Addr} {tsym : String}
    (ha : 1≤a) (ha' : a≤2^31) (hn : 16*n<2^31)
    (h8 : s.gpr .r8=BitVec.ofNat 64 a) (hT : s.syms tsym=T) :
    WP isa (.block (Joint.fixedAddress n tsym)) s fun t =>
      t.gpr .rdx=off T (16*n*(a-1)) ∧ Keeps [.rax,.rcx,.rdx] s t := by
  subst hT
  unfold Joint.fixedAddress Joint.fixedOffset
  split
  · rename_i hn4
    subst hn4
    crun [h8,List.cons_append,List.nil_append]
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · rw [show (1 : BitVec 32).signExtend 64=BitVec.ofNat 64 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
      rw [Nat.mul_mod,Nat.mod_mod,←Nat.mul_mod]
      congr 1
      omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,
        hr.1,hr.2.2,ite_false]
  · crun [h8,List.cons_append,List.nil_append]
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · rw [show (1 : BitVec 32).signExtend 64=BitVec.ofNat 64 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat,BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (show 16*n<2^32 by omega),Nat.mod_eq_of_lt (show a-1<2^64 by omega)]
      rw [Nat.mod_eq_of_lt (show 16*n<2^64 by omega),Nat.mul_comm]
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,
        hr.1,hr.2.1,hr.2.2,ite_false]

theorem jointFixedLoad_ok {K : WinCfg} {s : State} {base T : Addr} {size a : Nat} {tsym : String}
    (hs : Scr s base size) (ha : 1≤a) (ha' : a≤2^31) (hn : 16*K.M.n<2^31)
    (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    (ht : s.syms tsym=T) (hy : K.E.y=K.E.x+8*K.M.n) (hd : K.E.x+16*K.M.n≤size)
    (hz : K.E.z+8*K.M.n≤size) (hsep : K.E.x+16*K.M.n≤K.E.z ∨ K.E.z+8*K.M.n≤K.E.x)
    (hone : K.one<2^(64*K.M.n))
    (hr : ∀ i<K.M.n,InRegions (s.rd++s.wr) (off (off T (16*K.M.n*(a-1))) (16*i)) 16)
    (hout : ∀ i<K.M.n,∀ b<16,size≤ofs base (off (off T (16*K.M.n*(a-1))) (16*i)+BitVec.ofNat 64 b)) :
    WP isa (.block (Joint.fixedLoad K tsym)) s fun t =>
      wordsVal t.mem base K.E.x K.M.n=wordsVal s.mem (off T (16*K.M.n*(a-1))) 0 K.M.n ∧
      wordsVal t.mem base K.E.y K.M.n=wordsVal s.mem (off T (16*K.M.n*(a-1))) (8*K.M.n) K.M.n ∧
      wordsVal t.mem base K.E.z K.M.n=K.one ∧
      KeepRegs [.rax,.rcx,.rdx] s t ∧
      Unch base [(K.E.x,16*K.M.n),(K.E.z,8*K.M.n)] s.mem t.mem := by
  rw [Joint.fixedLoad,List.append_assoc,WP.block_append_iff]
  refine WP.mono (jointFixedAddress_ok ha ha' hn h8 ht) fun u ⟨eu,ku⟩ => ?_
  have su := hs.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (nafExternalPieces_ok (X:=off T (16*K.M.n*(a-1))) K.M.n u su hd
    (fun i _ => by rw [ea_tblAt,eu])
    (fun i _ => by rw [ea_sc,su.rdi])
    (fun i hi => by rw [ku.2.2.1,ku.2.2.2]; exact hr i hi) hout)
    fun v ⟨ev,ov,gv,rv,wv⟩ => ?_
  have sv : Scr v base size := ⟨by rw [gv]; exact su.rdi,wv ▸ su.wr,su.nowrap⟩
  refine WP.mono (setConst_ok sv hz hone) fun t ⟨zt,kt,ot⟩ => ?_
  refine ⟨?_,?_,zt,?_,?_⟩
  · rw [ot.wordsVal (by omega) (by have:=hs.nowrap; omega)]
    simpa only [Nat.add_zero,ku.2.1] using
      nafExternalCopy_fieldAt (o:=K.E.x) (d:=0) (w:=K.M.n) ev (by decide) (by omega)
  · rw [ot.wordsVal (by omega) (by have:=hs.nowrap; omega)]
    simpa only [hy,ku.2.1] using
      nafExternalCopy_fieldAt (o:=K.E.x) (d:=8*K.M.n) (w:=K.M.n) ev (by omega) (by omega)
  · exact (KeepRegs.mk (fun r h => (congrFun gv r).trans (ku.1 r h))
      (rv.trans ku.2.2.1) (wv.trans ku.2.2.2)).trans (kt.mono (by simp))
  · intro x hx
    rw [ot x (hx (K.E.z,8*K.M.n) (by simp)),ov x (hx (K.E.x,16*K.M.n) (by simp)),ku.2.1]

end VG.Proof.Weierstrass.X86_64
