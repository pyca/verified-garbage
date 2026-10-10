import VerifiedGarbage.Proof.Weierstrass.X86.NafAdjust

/-! Reading and writing public Jacobian table entries, with exact memory frames. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass VG.Impl.Mont.X86
open VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafTable_ea {s : State} {base : Addr} {size a d : Nat}
    (hs : Scr s base size) (hx : (s.gpr .edx).setWidth 64=off base a)
    (hd : a+d<size) : s.ea (TCombCfg.tblAt d)=off base (a+d) := by
  have hn := hs.nowrap
  have ht : (off base a).toNat=base.toNat+a := by
    simp only [off,BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  rw [ea_tblAt hx (by rw [ht]; omega),off,Offset.add_add]

theorem nafPublicEntry_ok {K : WinCfg} {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : 1≤a) (ha' : a≤15) (h8 : s.gpr .ebx=BitVec.ofNat 32 a)
    (hT : K.tbl+768≤size) (hE : K.E.x+96≤size)
    (hSep : K.E.x+96≤K.tbl ∨ K.tbl+768≤K.E.x) :
    WP isa (.block (Naf.publicEntry K)) s fun t =>
      (∀ j<3,wordsVal t.mem base (K.E.x+32*j) 4=
        wordsVal s.mem base (K.tbl+96*((a-1)/2)+32*j) 4) ∧
      KeepRegs [.eax,.ecx,.edx] s t ∧ Outside base K.E.x 96 s.mem t.mem := by
  have hi : (a-1)/2<8 := by omega
  rw [Naf.publicEntry,List.append_assoc,WP.block_append_iff]
  refine WP.mono (nafIndex_ok s ha ha' h8) fun u ⟨iu,ku⟩ => ?_
  have su := hs.of_keeps ku.keeps (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (nafAddress_ok su iu (by omega)) fun v ⟨av,kv⟩ => ?_
  have sv := su.of_keeps kv.keeps (by decide)
  refine WP.mono (nafCopyPieces_ok (a:=K.tbl+96*((a-1)/2)) (o:=K.E.x) 6 v sv
    (by omega) (by omega) (by omega)
    (fun i hi => nafTable_ea sv av (by omega))
    (fun i hi => sv.ea (by omega))) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
  refine ⟨fun j hj => ?_,⟨fun r hr => ?_,rt.trans (kv.2.2.1.trans ku.2.2.1),
    wt.trans (kv.2.2.2.trans ku.2.2.2)⟩,?_⟩
  · rw [nafCopy_coord et hj,kv.2.1,ku.2.1]
  · rw [gt,kv.1 r hr,ku.1 r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; exact fun he => hr (Or.inl he))]
  · rw [kv.2.1,ku.2.1] at ot
    exact ot

theorem nafTableStore_ok {K : WinCfg} {s : State} {base : Addr} {size j : Nat}
    (hs : Scr s base size) (hj : j<8) (hc : s.gpr .esi=BitVec.ofNat 32 j)
    (hT : K.tbl+768≤size) (hR : K.R.x+96≤size)
    (hSep : K.R.x+96≤K.tbl ∨ K.tbl+768≤K.R.x) :
    WP isa (.block (Naf.tableStore K)) s fun t =>
      (∀ i<3,wordsVal t.mem base (K.tbl+96*j+32*i) 4=wordsVal s.mem base (K.R.x+32*i) 4) ∧
      KeepRegs [.eax,.ecx,.edx] s t ∧ Outside base (K.tbl+96*j) 96 s.mem t.mem := by
  rw [Naf.tableStore,List.append_assoc,WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .eax (.reg .esi)]) s (fun u =>
      u.gpr .eax=BitVec.ofNat 32 j ∧ CKeeps [.eax] s u) by
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,Option.map_some,
      RegUpd.gpr_setReg,ite_true,hc,Option.some.injEq,exists_eq_left']
    refine ⟨trivial,fun r hr => ?_,rfl,rfl,rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg,hr,ite_false]) fun u ⟨iu,ku⟩ => ?_
  have su := hs.of_keeps ku.keeps (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (nafAddress_ok su iu (by omega)) fun v ⟨av,kv⟩ => ?_
  have sv := su.of_keeps kv.keeps (by decide)
  refine WP.mono (nafCopyPieces_ok (a:=K.R.x) (o:=K.tbl+96*j) 6 v sv
    (by omega) (by omega) (by omega)
    (fun i hi => sv.ea (by omega))
    (fun i hi => nafTable_ea sv av (by omega))) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
  refine ⟨fun i hi => ?_,⟨fun r hr => ?_,rt.trans (kv.2.2.1.trans ku.2.2.1),
    wt.trans (kv.2.2.2.trans ku.2.2.2)⟩,?_⟩
  · rw [nafCopy_coord et hi,kv.2.1,ku.2.1]
  · rw [gt,kv.1 r hr,ku.1 r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; exact fun he => hr (Or.inl he))]
  · rw [kv.2.1,ku.2.1] at ot
    exact ot

end VG.Proof.Weierstrass.X86
