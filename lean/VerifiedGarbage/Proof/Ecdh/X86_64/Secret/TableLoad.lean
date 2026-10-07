import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableIndex

/-! The public table-builder load copies the parent point selected by parity. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

theorem tableLoad_ok {K : WinCfg} {s : State} {base : Addr} {size j : Nat}
    (hs : Scr s base size) (h2 : 2≤j) (h16 : j≤16) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (ht : K.tbl<2^31) (hT : K.tbl+2560≤size) (hR : K.R.x+96≤size)
    (hRT : K.R.x+96≤K.tbl ∨ K.tbl+2560≤K.R.x) :
    WP isa (Impl.Ecdh.X86_64.Window5.tableLoad K) s fun t =>
      (∀ i<3,wordsVal t.mem base (K.R.x+32*i) 4=
        wordsVal s.mem base (K.tbl+160*(tableParent j-1)+32*i) 4) ∧
      KeepRegs [.rax,.rcx,.rdx] s t ∧ Outside base K.R.x 96 s.mem t.mem := by
  have hp := tableParent_bounds h2 h16
  rw [Impl.Ecdh.X86_64.Window5.tableLoad]
  apply WP.seq
  refine WP.mono (tableParity_ok s hc h16) fun u ⟨hu,zu,ku⟩ => ?_
  apply WP.seq
  refine WP.mono (tableParent_ok u h2 h16 hu zu) fun v ⟨hv,kv⟩ => ?_
  have kvu := ku.trans kv
  have sv := hs.of_keeps kvu (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddress_ok v sv.rdi hv hp.1 ht) fun w ⟨hw,kw⟩ => ?_
  have sw := sv.of_keeps kw (by decide)
  refine WP.mono (nafCopyPieces_ok (a:=K.tbl+160*(tableParent j-1)) (o:=K.R.x) 6 w sw
    (by omega) (by omega) (by omega)
    (fun i _ => by rw [ea_tblAt,hw]; unfold off; rw [Offset.add_add])
    (fun i _ => by rw [ea_sc,sw.rdi])) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
  refine ⟨fun i hi => ?_,⟨fun r hr => ?_,rt.trans (kw.2.2.1.trans kvu.2.2.1),
    wt.trans (kw.2.2.2.trans kvu.2.2.2)⟩,?_⟩
  · rw [nafCopy_coord et hi,kw.2.1,kvu.2.1]
  · rw [gt,kw.1 r hr,kvu.1 r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      exact fun he => hr (Or.inl he))]
  · rw [kw.2.1,kvu.2.1] at ot
    exact ot

end VG.Proof.Ecdh.X86_64.Secret
