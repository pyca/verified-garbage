import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCache
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableIO

/-! Cache lookup addresses and exact copies of both cached field elements. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.X25519.X86_64

theorem nafCacheOffset_ok (s : State) {n a : Nat} (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    (ha : 1≤a) (ha' : a≤15) (hodd : a%2=1) (hn : 8*n<2^31) :
    WP isa (.block (Naf.cacheOffset n)) s fun t =>
      t.gpr .rax=BitVec.ofNat 64 (16*n*((a-1)/2)) ∧ Keeps [.rax,.rcx,.rdx] s t := by
  have hsub : BitVec.ofNat 64 a-(1 : BitVec 32).signExtend 64=BitVec.ofNat 64 (a-1) := by
    rw [show (1 : BitVec 32).signExtend 64=BitVec.ofNat 64 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
  apply WP.of_runBlock
  by_cases h4 : n=4
  · subst h4
    simp only [Naf.cacheOffset,ite_true,runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,
      execAlu,execShift,h8,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,
      Option.map_some,Option.bind_some,ite_true,and_self,
      show 1≤5 ∧ 5≤63 from by decide,Option.some.injEq,exists_eq_left']
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · rw [hsub]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
      omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,hr.1,ite_false]
  · simp only [Naf.cacheOffset,h4,ite_false,runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,
      readSrc32,execAlu,execMul,State.setReg32,h8,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
      RegUpd.gpr_setFlags,Option.map_some,Option.bind_some,ite_true,reduceCtorEq,
      Option.some.injEq,exists_eq_left']
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · rw [hsub]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat,BitVec.toNat_setWidth,Nat.mod_eq_of_lt (show 8*n<2^32 by omega)]
      rw [Nat.mod_eq_of_lt (show a-1<2^64 by omega),Nat.mod_eq_of_lt (show 8*n<2^64 by omega)]
      obtain ⟨k,hk⟩ : ∃ k,a-1=2*k := ⟨(a-1)/2,by omega⟩
      rw [hk,show 2*k/2=k by omega,show 2*k*(8*n)=16*n*k by grind]
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,
        hr.1,hr.2.1,hr.2.2,ite_false]

theorem nafCacheAddress_ok {s : State} {base : Addr} {n tbl a : Nat}
    (hb : s.gpr .rdi=base) (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    (ha : 1≤a) (ha' : a≤15) (hodd : a%2=1) (ht : tbl<2^31) (hn : 8*n<2^31) :
    WP isa (.block (Naf.cacheAddress n tbl)) s fun t =>
      t.gpr .rdx=off base (tbl+16*n*((a-1)/2)) ∧ Keeps [.rax,.rcx,.rdx] s t := by
  rw [Naf.cacheAddress,WP.block_append_iff]
  refine WP.mono (nafCacheOffset_ok s h8 ha ha' hodd hn) fun u ⟨hu,ku⟩ => ?_
  have hb' : u.gpr .rdi=base := (ku.1 .rdi (by decide)).trans hb
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,execAlu,
    imm32_sext ht,hu,hb',RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,Option.map_some,Option.bind_some,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,ku.2.1,ku.2.2.1,ku.2.2.2⟩
  · rw [Offset.add_add]
  · have hr' := hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr'
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr'.2.2,ite_false]
    exact ku.1 r hr

theorem nafCacheRead_ok {s : State} {base : Addr} {size n tbl dst a : Nat}
    (hs : Scr s base size) (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    (ha : 1≤a) (ha' : a≤15) (hodd : a%2=1) (ht : tbl<2^31) (hn : n=4 ∨ n=6 ∨ n=9)
    (hT : tbl+128*n≤size) (hD : dst+16*n≤size)
    (hSep : dst+16*n≤tbl ∨ tbl+128*n≤dst) :
    WP isa (.block (Naf.cacheRead n tbl dst)) s fun t =>
      (∀ j<2,wordsVal t.mem base (dst+8*n*j) n=
        wordsVal s.mem base (tbl+16*n*((a-1)/2)+8*n*j) n) ∧
      KeepRegs [.rax,.rcx,.rdx] s t ∧ Outside base dst (16*n) s.mem t.mem := by
  have hi := entry_end_le (16*n) (show (a-1)/2<8 by omega)
  rw [Naf.cacheRead,WP.block_append_iff]
  refine WP.mono (nafCacheAddress_ok hs.rdi h8 ha ha' hodd ht (by omega)) fun u ⟨hu,ku⟩ => ?_
  have su := hs.of_keeps ku (by decide)
  refine WP.mono (nafCopyPieces_ok (a:=tbl+16*n*((a-1)/2)) (o:=dst) n u su
    (by omega) (by omega) (by omega)
    (fun i _ => by rw [ea_tblAt,hu]; unfold off; rw [Offset.add_add])
    (fun i _ => by rw [ea_sc,su.rdi])) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
  refine ⟨fun j hj => ?_,⟨fun r hr => ?_,rt.trans ku.2.2.1,wt.trans ku.2.2.2⟩,?_⟩
  · obtain rfl|rfl : j=0∨j=1 := by omega
    all_goals rw [nafCopy_fieldAt et (by omega) (by omega),ku.2.1]
  · rw [gt,ku.1 r hr]
  · rw [ku.2.1] at ot
    exact ot

theorem nafCachedEntry_ok {K : WinCfg} {s : State} {base : Addr} {size tbl dst a : Nat}
    (hs : Scr s base size) (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    (ha : 1≤a) (ha' : a≤15) (hodd : a%2=1) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+192*K.M.n≤size) (hC : tbl+128*K.M.n≤size)
    (hE : K.E.x+24*K.M.n≤size) (hD : dst+16*K.M.n≤size)
    (hEP : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    (hEC : K.E.x+24*K.M.n≤tbl ∨ tbl+128*K.M.n≤K.E.x)
    (hDC : dst+16*K.M.n≤tbl ∨ tbl+128*K.M.n≤dst)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst) :
    WP isa (.block (Naf.cachedEntry K tbl dst)) s fun t =>
      (∀ j<3,wordsVal t.mem base (K.E.x+8*K.M.n*j) K.M.n=
        wordsVal s.mem base (K.tbl+24*K.M.n*((a-1)/2)+8*K.M.n*j) K.M.n) ∧
      (∀ j<2,wordsVal t.mem base (dst+8*K.M.n*j) K.M.n=
        wordsVal s.mem base (tbl+16*K.M.n*((a-1)/2)+8*K.M.n*j) K.M.n) ∧
      KeepRegs [.rax,.rcx,.rdx] s t ∧
      (∀ x,(ofs base x<K.E.x ∨ K.E.x+24*K.M.n≤ofs base x) →
        (ofs base x<dst ∨ dst+16*K.M.n≤ofs base x) → t.mem x=s.mem x) := by
  have hn' := hs.nowrap
  have hi := entry_end_le (16*K.M.n) (show (a-1)/2<8 by omega)
  rw [Naf.cachedEntry,WP.block_append_iff]
  refine WP.mono (nafPublicEntry_ok hs ha ha' h8 hn hp hP hE hEP) fun u ⟨eu,ku,ou⟩ => ?_
  have su := hs.of_keepRegs ku (by decide)
  have hu8 : u.gpr .r8=BitVec.ofNat 64 a := (ku.gpr .r8 (by decide)).trans h8
  refine WP.mono (nafCacheRead_ok su hu8 ha ha' hodd hc hn hC hD hDC) fun t ⟨et,kt,ot⟩ => ?_
  refine ⟨fun j hj => ?_,fun j hj => ?_,ku.trans (kt.mono (by simp)),fun x he hd => ?_⟩
  · have := entry_end_le (8*K.M.n) hj
    rw [ot.wordsVal (by omega) (by omega),eu j hj]
  · have := entry_end_le (8*K.M.n) hj
    rw [et j hj,ou.wordsVal (by omega) (by omega)]
  · rw [ot x hd,ou x he]

end VG.Proof.Weierstrass.X86_64
