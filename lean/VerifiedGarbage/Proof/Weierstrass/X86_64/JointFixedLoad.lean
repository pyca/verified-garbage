import VerifiedGarbage.Impl.Weierstrass.X86_64.JointFixed
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafExternalCopy
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem jointFixedAddress_ok {s : State} {a : Nat} {T : Addr} {tsym : String}
    (ha : 1≤a) (h8 : s.gpr .r8=BitVec.ofNat 64 a) (hT : s.syms tsym=T) :
    WP isa (.block (Joint.fixedAddress tsym)) s fun t =>
      t.gpr .rdx=off T (64*(a-1)) ∧ Keeps [.rax,.rdx] s t := by
  subst hT
  crun [Joint.fixedAddress,h8]
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
      hr.1,hr.2,ite_false]

theorem jointFixedLoad_ok {K : WinCfg} {s : State} {base T : Addr} {size a : Nat} {tsym : String}
    (hs : Scr s base size) (ha : 1≤a) (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    (ht : s.syms tsym=T) (hy : K.E.y=K.E.x+32) (hd : K.E.x+64≤size)
    (hz : K.E.z+32≤size) (hsep : K.E.x+64≤K.E.z ∨ K.E.z+32≤K.E.x)
    (hone : K.one<2^256)
    (hr : ∀ i<4,InRegions (s.rd++s.wr) (off (off T (64*(a-1))) (16*i)) 16)
    (hout : ∀ i<4,∀ b<16,size≤ofs base (off (off T (64*(a-1))) (16*i)+BitVec.ofNat 64 b)) :
    WP isa (.block (Joint.fixedLoad K tsym)) s fun t =>
      wordsVal t.mem base K.E.x 4=wordsVal s.mem (off T (64*(a-1))) 0 4 ∧
      wordsVal t.mem base K.E.y 4=wordsVal s.mem (off T (64*(a-1))) 32 4 ∧
      wordsVal t.mem base K.E.z 4=K.one ∧
      KeepRegs [.rax,.rdx] s t ∧ Unch base [(K.E.x,64),(K.E.z,32)] s.mem t.mem := by
  rw [Joint.fixedLoad,List.append_assoc,WP.block_append_iff]
  refine WP.mono (jointFixedAddress_ok ha h8 ht) fun u ⟨eu,ku⟩ => ?_
  have su := hs.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (nafExternalPieces_ok (X:=off T (64*(a-1))) 4 u su hd
    (fun i _ => by rw [ea_tblAt,eu])
    (fun i _ => by rw [ea_sc,su.rdi])
    (fun i hi => by rw [ku.2.2.1,ku.2.2.2]; exact hr i hi) hout)
    fun v ⟨ev,ov,gv,rv,wv⟩ => ?_
  have sv : Scr v base size := ⟨by rw [gv]; exact su.rdi,wv ▸ su.wr,su.nowrap⟩
  refine WP.mono (setConst_ok sv hz hone) fun t ⟨zt,kt,ot⟩ => ?_
  refine ⟨?_,?_,zt,?_,?_⟩
  · rw [ot.wordsVal (by omega) (by have:=hs.nowrap; omega)]
    simpa only [Nat.mul_zero,Nat.add_zero,ku.2.1] using nafExternalCopy_field ev (j:=0) (by decide)
  · rw [ot.wordsVal (by omega) (by have:=hs.nowrap; omega)]
    simpa only [Nat.mul_one,hy,ku.2.1] using nafExternalCopy_field ev (j:=1) (by decide)
  · exact (KeepRegs.mk (fun r h => (congrFun gv r).trans (ku.1 r h))
      (rv.trans ku.2.2.1) (wv.trans ku.2.2.2)).trans (kt.mono (by simp))
  · intro x hx
    rw [ot x (hx (K.E.z,32) (by simp)),ov x (hx (K.E.x,64) (by simp)),ku.2.1]

end VG.Proof.Weierstrass.X86_64
