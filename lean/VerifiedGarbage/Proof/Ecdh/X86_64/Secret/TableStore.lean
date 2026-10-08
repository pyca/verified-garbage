import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableAddress

/-! Table stores preserve both the point coordinates and its cached Z powers. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

theorem tableStore_ok {K : WinCfg} {s : State} {base : Addr} {size j : Nat}
    (hs : Scr s base size) (hj1 : 1≤j) (hj16 : j≤16) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (ht : K.tbl<2^31) (hT : K.tbl+2560≤size) (hR : K.R.x+96≤size) (hE : K.E.x+160≤size)
    (hRT : K.R.x+96≤K.tbl ∨ K.tbl+2560≤K.R.x)
    (hET : K.E.x+160≤K.tbl ∨ K.tbl+2560≤K.E.x+96) :
    WP isa (.block (Impl.Ecdh.X86_64.Window5.tableStore K)) s fun t =>
      (∀ i<3,wordsVal t.mem base (K.tbl+160*(j-1)+32*i) 4=
        wordsVal s.mem base (K.R.x+32*i) 4) ∧
      (∀ i<2,wordsVal t.mem base (K.tbl+160*(j-1)+96+32*i) 4=
        wordsVal s.mem base (K.E.x+96+32*i) 4) ∧
      KeepRegs [.rax,.rcx,.rdx] s t ∧ Outside base (K.tbl+160*(j-1)) 160 s.mem t.mem := by
  rw [Impl.Ecdh.X86_64.Window5.tableStore,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (tableCounter_ok s hc) fun u ⟨hu,ku⟩ => ?_
  have su := hs.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddress_ok u su.rdi hu hj1 ht) fun v ⟨hv,kv⟩ => ?_
  have sv := su.of_keeps kv (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (nafCopyPieces_ok (a:=K.R.x) (o:=K.tbl+160*(j-1)) 6 v sv
    (by omega) (by omega) (by omega)
    (fun i _ => by rw [ea_sc,sv.rdi])
    (fun i _ => by rw [ea_tblAt,hv]; unfold off; rw [Offset.add_add])) fun w ⟨ew,ow,gw,rw',ww⟩ => ?_
  have sw : Scr w base size := ⟨by rw [gw]; exact sv.rdi,ww ▸ sv.wr,sv.nowrap⟩
  have hw : w.gpr .rdx=off base (K.tbl+160*(j-1)) := by rw [gw,hv]
  refine WP.mono (nafCopyPieces_ok (a:=K.E.x+96) (o:=K.tbl+160*(j-1)+96) 4 w sw
    (by omega) (by omega) (by omega)
    (fun i _ => by rw [ea_sc,sw.rdi])
    (fun i _ => by rw [ea_tblAt,hw]; unfold off; rw [Offset.add_add]; simp only [Nat.add_assoc]))
    fun t ⟨et,ot,gt,rt,wt⟩ => ?_
  refine ⟨fun i hi => ?_,fun i hi => ?_,⟨fun r hr => ?_,
    rt.trans (rw'.trans (kv.2.2.1.trans ku.2.2.1)),wt.trans (ww.trans (kv.2.2.2.trans ku.2.2.2))⟩,?_⟩
  · rw [ot.wordsVal (by omega) (by have := hs.nowrap; omega),nafCopy_fieldAt (d:=32*i) ew (by omega) (by omega),kv.2.1,ku.2.1]
  · rw [nafCopy_fieldAt (d:=32*i) et (by omega) (by omega),ow.wordsVal (by omega) (by have := hs.nowrap; omega),kv.2.1,ku.2.1]
  · rw [gt,gw,kv.1 r hr,ku.1 r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      exact fun he => hr (Or.inl he))]
  · have ho : Outside base (K.tbl+160*(j-1)) 160 v.mem t.mem := (ow.mono (Nat.le_refl _) (by omega)).trans (ot.mono (by omega) (by omega))
    rw [kv.2.1,ku.2.1] at ho
    exact ho

end VG.Proof.Ecdh.X86_64.Secret
