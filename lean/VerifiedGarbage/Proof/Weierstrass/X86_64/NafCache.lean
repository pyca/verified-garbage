import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCache
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableIO

/-! Cache lookup addresses and exact copies of both cached field elements. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.X25519.X86_64

theorem nafCacheAddress_ok {s : State} {base : Addr} {tbl a : Nat}
    (hb : s.gpr .rdi=base) (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    (ha : 1≤a) (ha' : a≤15) (hodd : a%2=1) (ht : tbl<2^31) :
    WP isa (.block (Naf.cacheAddress tbl)) s fun t =>
      t.gpr .rdx=off base (tbl+64*((a-1)/2)) ∧ Keeps [.rax,.rdx] s t := by
  apply WP.of_runBlock
  simp only [Naf.cacheAddress,runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,execAlu,
    execShift,imm32_sext ht,h8,hb,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags,Option.map_some,Option.bind_some,ite_true,ite_false,reduceCtorEq,and_self,
    show 1≤5 ∧ 5≤63 from by decide,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · have he : (BitVec.ofNat 64 a-(1 : BitVec 32).signExtend 64)<<<5=
        BitVec.ofNat 64 (64*((a-1)/2)) := by
      rw [show (1 : BitVec 32).signExtend 64=BitVec.ofNat 64 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
      omega
    rw [he,Offset.add_add]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,
      hr.1,hr.2,ite_false]

theorem nafCacheRead_ok {s : State} {base : Addr} {size tbl dst a : Nat}
    (hs : Scr s base size) (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    (ha : 1≤a) (ha' : a≤15) (hodd : a%2=1) (ht : tbl<2^31)
    (hT : tbl+512≤size) (hD : dst+64≤size)
    (hSep : dst+64≤tbl ∨ tbl+512≤dst) :
    WP isa (.block (Naf.cacheRead tbl dst)) s fun t =>
      (∀ j<2,wordsVal t.mem base (dst+32*j) 4=
        wordsVal s.mem base (tbl+64*((a-1)/2)+32*j) 4) ∧
      KeepRegs [.rax,.rdx] s t ∧ Outside base dst 64 s.mem t.mem := by
  have hi : (a-1)/2<8 := by omega
  rw [Naf.cacheRead,WP.block_append_iff]
  refine WP.mono (nafCacheAddress_ok hs.rdi h8 ha ha' hodd ht) fun u ⟨hu,ku⟩ => ?_
  have su := hs.of_keeps ku (by decide)
  refine WP.mono (nafCopyPieces_ok (a:=tbl+64*((a-1)/2)) (o:=dst) 4 u su
    (by omega) (by omega) (by omega)
    (fun i _ => by rw [ea_tblAt,hu]; unfold off; rw [Offset.add_add])
    (fun i _ => by rw [ea_sc,su.rdi])) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
  refine ⟨fun j hj => ?_,⟨fun r hr => ?_,rt.trans ku.2.2.1,wt.trans ku.2.2.2⟩,?_⟩
  · rw [nafCopy_field et (by omega),ku.2.1]
  · rw [gt,ku.1 r hr]
  · rw [ku.2.1] at ot
    exact ot

theorem nafCachedEntry_ok {K : WinCfg} {s : State} {base : Addr} {size tbl dst a : Nat}
    (hs : Scr s base size) (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    (ha : 1≤a) (ha' : a≤15) (hodd : a%2=1)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+768≤size) (hC : tbl+512≤size)
    (hE : K.E.x+96≤size) (hD : dst+64≤size)
    (hEP : K.E.x+96≤K.tbl ∨ K.tbl+768≤K.E.x)
    (hEC : K.E.x+96≤tbl ∨ tbl+512≤K.E.x)
    (hDC : dst+64≤tbl ∨ tbl+512≤dst)
    (hDE : dst+64≤K.E.x ∨ K.E.x+96≤dst) :
    WP isa (.block (Naf.cachedEntry K tbl dst)) s fun t =>
      (∀ j<3,wordsVal t.mem base (K.E.x+32*j) 4=
        wordsVal s.mem base (K.tbl+96*((a-1)/2)+32*j) 4) ∧
      (∀ j<2,wordsVal t.mem base (dst+32*j) 4=
        wordsVal s.mem base (tbl+64*((a-1)/2)+32*j) 4) ∧
      KeepRegs [.rax,.rcx,.rdx] s t ∧
      (∀ x,(ofs base x<K.E.x ∨ K.E.x+96≤ofs base x) →
        (ofs base x<dst ∨ dst+64≤ofs base x) → t.mem x=s.mem x) := by
  have hi : (a-1)/2<8 := by omega
  have hn := hs.nowrap
  rw [Naf.cachedEntry,WP.block_append_iff]
  refine WP.mono (nafPublicEntry_ok hs ha ha' h8 hp hP hE hEP) fun u ⟨eu,ku,ou⟩ => ?_
  have su := hs.of_keepRegs ku (by decide)
  have hu8 : u.gpr .r8=BitVec.ofNat 64 a := (ku.gpr .r8 (by decide)).trans h8
  refine WP.mono (nafCacheRead_ok su hu8 ha ha' hodd hc hC hD hDC) fun t ⟨et,kt,ot⟩ => ?_
  refine ⟨fun j hj => ?_,fun j hj => ?_,ku.trans (kt.mono (by simp)),fun x he hd => ?_⟩
  · rw [ot.wordsVal (by omega) (by omega),eu j hj]
  · rw [et j hj,ou.wordsVal (by omega) (by omega)]
  · rw [ot x hd,ou x he]

end VG.Proof.Weierstrass.X86_64
