module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.JointFixed
public import VerifiedGarbage.Proof.Mont.X86_64.Csub
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectPass
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelect
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Mont.X86_64.Words

/-! ### `Weierstrass.X86_64.NafExternalCopy`, which this module and modules that import it used -/

section

/-! Public copies from a read-only table outside the scratch allocation. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

theorem nafExternalPiece_ok {s : State} {base X : Addr} {size o : Nat} {src dst : MemOp}
    (hs : Scr s base size) (ho : o+16≤size)
    (ea : s.ea src=X) (eo : s.ea dst=off base o)
    (hr : InRegions (s.rd++s.wr) X 16) (r : XReg) :
    WP isa (.block [.movdquLoad r src,.movdquStore dst r]) s fun t =>
      t.mem.readW (off base o) 128=s.mem.readW X 128 ∧
      Outside base o 16 s.mem t.mem ∧ t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have hw : InRegions s.wr (off base o) 16 := ⟨_,hs.wr,hs.contains ho (by decide)⟩
  have ed : (s.setXmm r (s.mem.readW X 128)).ea dst=s.ea dst := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.load128,State.store128,
    ea,hr,ite_true,Option.map_some,RegUpd.wr_setXmm,ed,eo,hw,
    RegUpd.xmm_setXmm_self,RegUpd.mem_setXmm,Option.some.injEq,exists_eq_left']
  exact ⟨Mem.readW_writeW_self (n:=16) _ _ _ (by decide),
    writeW128_out s.mem base (s.mem.readW X 128) (by have:=hs.nowrap; omega_using [ho, this]),rfl,rfl,trivial⟩

theorem nafExternalPieces_ok {base X : Addr} {size o : Nat} {src dst : Nat → MemOp} :
    ∀ n (s : State), Scr s base size → o+16*n≤size →
      (∀ i<n,s.ea (src i)=off X (16*i)) →
      (∀ i<n,s.ea (dst i)=off base (o+16*i)) →
      (∀ i<n,InRegions (s.rd++s.wr) (off X (16*i)) 16) →
      (∀ i<n,∀ b<16,size≤ofs base (off X (16*i)+BitVec.ofNat 64 b)) →
    WP isa (.block (Naf.copyPieces n src dst)) s fun t =>
      (∀ i<n,t.mem.readW (off base (o+16*i)) 128=s.mem.readW (off X (16*i)) 128) ∧
      Outside base o (16*n) s.mem t.mem ∧ t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr
  | 0,s,_,_,_,_,_,_ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      Outside.refl _ _ _ _,rfl,rfl,rfl⟩
  | n+1,s,hs,ho,ea,eo,hr,hout => by
    rw [Naf.copyPieces,List.range_succ,List.flatMap_append,List.flatMap_singleton,WP.block_append_iff]
    refine WP.mono (nafExternalPieces_ok n s hs (by omega_using [ho])
      (fun i hi => ea i (by omega_using [hi])) (fun i hi => eo i (by omega_using [hi]))
      (fun i hi => hr i (by omega_using [hi])) (fun i hi => hout i (by omega_using [hi]))) fun u ⟨eu,ou,gu,ru,wu⟩ => ?_
    have su : Scr u base size := ⟨by rw [gu]; exact hs.rdi,wu ▸ hs.wr,hs.nowrap⟩
    have eac (m : MemOp) : u.ea m=s.ea m := by simp only [State.ea,gu]
    refine WP.mono (nafExternalPiece_ok su (X:=off X (16*n)) (src:=src n) (dst:=dst n) (o:=o+16*n) (by omega_using [ho])
      (by rw [eac]; exact ea n (by omega_using [])) (by rw [eac]; exact eo n (by omega_using []))
      (by rw [ru,wu]; exact hr n (by omega_using [])) (selAcc n)) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
    refine ⟨fun i hi => ?_,(ou.mono (Nat.le_refl _) (by omega_using [])).trans (ot.mono (by omega_using []) (by omega_using [])),
      gt.trans gu,rt.trans ru,wt.trans wu⟩
    by_cases he : i=n
    · subst i
      rw [et]
      exact Mem.readW_congr fun b hb => ou _ (Or.inr (by
        have := hout n (by omega_using []) b (by omega_using [hb]); omega_using [ho, this]))
    · rw [ot.read128 (by omega_using [he]) (by have:=hs.nowrap; omega_using [ho, hi, this]),eu i (by omega_using [hi, he])]

theorem nafExternalCopy_words {mem mem' : Mem} {base X : Addr} {n o : Nat}
    (h : ∀ c<n,mem'.readW (off base (o+16*c)) 128=mem.readW (off X (16*c)) 128) :
    ∀ i<2*n,word mem' base (o+8*i)=word mem X (8*i) := by
  intro i hi
  obtain ⟨c,q,hq,rfl⟩ : ∃ c q,q<2 ∧ i=2*c+q :=
    ⟨i/2,i%2,Nat.mod_lt _ (by decide),by omega_using []⟩
  have e := readW_extract mem' (off base (o+16*c)) (w:=128) (k:=8*q) (n:=8) (by omega_using [hq])
  rw [show 8*8=64 from rfl,off,Offset.add_add,
    show o+16*c+8*q=o+8*(2*c+q) from by omega_using []] at e
  rw [VG.Proof.Mont.word,off,←e,h c (by omega_using [hi])]
  have e2 := readW_extract mem (off X (16*c)) (w:=128) (k:=8*q) (n:=8) (by omega_using [hq])
  rw [show 8*8=64 from rfl,off,Offset.add_add] at e2
  rw [e2,VG.Proof.Mont.word,off,show 16*c+8*q=8*(2*c+q) from by omega_using []]

/-- A field of `w` words at an 8-byte-aligned offset `d` of the copied pieces. -/
theorem nafExternalCopy_fieldAt {mem mem' : Mem} {base X : Addr} {n o d w : Nat}
    (h : ∀ c<n,mem'.readW (off base (o+16*c)) 128=mem.readW (off X (16*c)) 128)
    (hd : d%8=0) (hj : d+8*w≤16*n) : wordsVal mem' base (o+d) w=wordsVal mem X d w := by
  apply wordsVal_congr₂
  intro i hi
  rw [show o+d+8*i=o+8*(d/8+i) from by omega_using [hd],show d+8*i=8*(d/8+i) from by omega_using [hd]]
  exact nafExternalCopy_words h _ (by omega_using [hj, hi])

end VG.Proof.Weierstrass.X86_64

end

end

@[expose] public section

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
      omega_using []
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
        Nat.mod_eq_of_lt (show 16*n<2^32 by omega_using [hn]),Nat.mod_eq_of_lt (show a-1<2^64 by omega_using [ha'])]
      rw [Nat.mod_eq_of_lt (show 16*n<2^64 by omega_using [hn]),Nat.mul_comm]
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
  · rw [ot.wordsVal (by omega_using [hsep]) (by have:=hs.nowrap; omega_using [hd, this])]
    simpa only [Nat.add_zero,ku.2.1] using
      nafExternalCopy_fieldAt (o:=K.E.x) (d:=0) (w:=K.M.n) ev (by decide) (by omega_using [])
  · rw [ot.wordsVal (by omega_using [hy, hsep]) (by have:=hs.nowrap; omega_using [hy, hd, this])]
    simpa only [hy,ku.2.1] using
      nafExternalCopy_fieldAt (o:=K.E.x) (d:=8*K.M.n) (w:=K.M.n) ev (by omega_using []) (by omega_using [])
  · exact (KeepRegs.mk (fun r h => (congrFun gv r).trans (ku.1 r h))
      (rv.trans ku.2.2.1) (wv.trans ku.2.2.2)).trans (kt.mono (by regions_sub))
  · intro x hx
    rw [ot x (hx (K.E.z,8*K.M.n) (by simp)),ov x (hx (K.E.x,16*K.M.n) (by simp)),ku.2.1]

end VG.Proof.Weierstrass.X86_64
