module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.MaskCall
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.WordXor
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.MaskTag
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-! # Compose the short contiguous seal's counter batch and payload XOR -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.WriteBytes VG.Impl.AesGcm.RISCV64
open VG.Spec.Gcm (Block blockAt gctr inc32 toBytes ghashFrom ghash blocks ofBytes zeros padLen)
open VG.Proof.Gcm (padded lensBlock Absorbed)
open VG.Spec.Aes (bytesAt)

abbrev shortXor : Prog isa := .ite (.zero .s5) (.block []) (.seq (.block
  [.addi .a0 .s0 272,mov .a1 .s4,mov .a4 .s8,mov .a2 .s5]) VG.Impl.AesGcm.RISCV64.Contiguous.xorText)

theorem shortXor_wp {V : Reg → BitVec 64} {sp : Addr} {s : State} {X D : Addr} {n : Nat}
    (he : Env V sp s) (L : Lay (V .s2) (V .s1) (V .s0))
    (src : s.gpr .s4=X) (dst : s.gpr .s8=D) (len : s.gpr .s5=BitVec.ofNat 64 n) (small : n≤240)
    (xd : DataOk (V .s1) (V .s0) s X n) (dd : DataW (V .s2) (V .s1) (V .s0) s D n) (alias : Alias true X D n) :
    WP isa shortXor s (TextOut s (V .s0+BitVec.ofNat 64 272) X D n) := by
  apply WP.ite _ (eval_zero len xd.lt)
  · intro z
    obtain rfl : n=0 := by simpa using z
    exact WP.block_nil ⟨by simp [xorBytes,bytesAt,writeBytes_nil],fun _ _ => rfl,⟨rfl,rfl,rfl⟩⟩
  · intro nz
    have pos : 0<n := by have := of_decide_eq_false nz; omega
    apply WP.seq
    refine Steps.wp_addi (imm := 272) (by decide) fun v a => Steps.wp_mv fun u b =>
      Steps.wp_mv fun j c => Steps.wp_mv fun t e => WP.block_nil ?_
    have keep : Keeps s t := ⟨e.mem.trans (c.mem.trans (b.mem.trans a.mem)),e.rd.trans (c.rd.trans (b.rd.trans a.rd)),
      e.wr.trans (c.wr.trans (b.wr.trans a.wr)),e.sp.trans (c.sp.trans (b.sp.trans a.sp))⟩
    have g (r : Reg) (h0 : r≠.a0) (h1 : r≠.a1) (h2 : r≠.a2) (h4 : r≠.a4) :=
      (e.other r h2).trans ((c.other r h4).trans ((b.other r h1).trans (a.other r h0)))
    have pre : XorPre true t (V .s0+BitVec.ofNat 64 272) X D n := by
      refine ⟨?_,?_,?_,?_,pos,xd.lt,?_,?_,?_,?_,alias⟩
      · rw [e.other _ (by decide),c.other _ (by decide),b.other _ (by decide),a.gpr,he.s0]
      · rw [e.other _ (by decide),c.other _ (by decide),b.gpr,a.other _ (by decide),src]
      · change t.gpr .a4=D
        rw [e.other _ (by decide),c.gpr,b.other _ (by decide),a.other _ (by decide),dst]
      · rw [e.gpr,c.other _ (by decide),b.other _ (by decide),a.other _ (by decide),len]
      · rw [keep.rd,keep.wr];exact covers_left (he.perm.wC (by omega))
      · rw [keep.rd,keep.wr];exact xd.rd
      · rw [keep.wr];exact dd.wr
      · exact dd.ok.w.symm.sub_left (Lay.wSub (by omega))
    refine WP.mono (xorText_wp pre (L.wal8 (by decide) (by decide))) fun y out => ⟨by rw [out.mem,keep.mem],?_,
      ⟨out.keeps.rd.trans keep.rd,out.keeps.wr.trans keep.wr,out.keeps.sp.trans keep.sp⟩⟩
    exact fun r hr => (out.saved r hr).trans (g r (by revert r;decide) (by revert r;decide) (by revert r;decide) (by revert r;decide))

theorem maskData_wp {V : Reg → BitVec 64} {sp : Addr} {s : State} {X D : Addr} {n R : Nat}
    (he : Env V sp s) (L : Lay (V .s2) (V .s1) (V .s0))
    (src : s.gpr .s4=X) (dst : s.gpr .s8=D) (len : s.gpr .s5=BitVec.ofNat 64 n) (small : n≤240)
    (xd : DataOk (V .s1) (V .s0) s X n) (dd : DataW (V .s2) (V .s1) (V .s0) s D n) (alias : Alias true X D n)
    (rounds : V .s3=BitVec.ofNat 64 R) (hR : R=10 ∨ R=12 ∨ R=14) (hb : BkIn (V .s7) (V .s2) (V .s1) (V .s0) sp R s.mem X D n s) :
    WP isa (.seq VG.Impl.AesGcm.RISCV64.Contiguous.masks shortXor) s fun t =>
      Env V sp t ∧ Keeps' s t ∧
      Frame (⟨D,n⟩ :: maskFrame (V .s1) (V .s0)) s.mem t.mem ∧
      blockAt t.mem (V .s0+BitVec.ofNat 64 256)=ciphOf s.mem (V .s2) R (blockAt s.mem (V .s1)) ∧
      bytesAt t.mem D n=gctr (ciphOf s.mem (V .s2) R) (inc32 (blockAt s.mem (V .s1))) (bytesAt s.mem X n) := by
  apply WP.seq
  refine WP.mono (masks_wp L he len small rounds hR hb) fun u ⟨eu,gu,ku,fr,ms⟩ => ?_
  have read : bytesAt u.mem X n=bytesAt s.mem X n := bytesAt_frame fr (fun r hr => by
    simp only [maskFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact xd.w.sub_right (Lay.wSub (d := 256) (by decide))
    · exact xd.st.sub_right (Region.sub_prefix (by decide))
    · exact xd.w.sub_right (Lay.wSub (d := 512) (by decide))) (by omega)
  refine WP.mono (shortXor_wp eu L ((gu _ (by decide)).trans src) ((gu _ (by decide)).trans dst) ((gu _ (by decide)).trans len)
    small (xd.of_eq ku.rd ku.wr ku.sp) (dd.of_eq ku.rd ku.wr ku.sp) alias) fun t out => ?_
  have ft : Frame [⟨D,n⟩] u.mem t.mem := by
    rw [out.mem];exact writeBytes_frame _ _ _ (by rw [length_xorBytes];exact Region.contains_self _ _)
  refine ⟨eu.keep (fun r hr => out.saved r (frozen_preserved r hr)) out.keeps.sp out.keeps.rd out.keeps.wr,
    ⟨out.keeps.rd.trans ku.rd,out.keeps.wr.trans ku.wr,out.keeps.sp.trans ku.sp⟩,?_,?_,?_⟩
  · exact (fr.mono (fun r hr => List.mem_cons_of_mem _ hr)).trans (ft.mono (fun r hr => List.mem_cons.mpr (.inl (List.mem_singleton.mp hr))))
  · rw [blockAt_frame ft (fun r hr => by obtain rfl := List.mem_singleton.mp hr;exact dd.ok.w.symm.sub_left (Lay.wSub (d := 256) (by decide)))]
    exact ms.tag
  · rw [out.mem,bytesAt_writeBytes_self' _ _ (length_xorBytes _ _ _ _) (by omega)]
    have e := ms.stream (bytesAt u.mem X n) (by simp [bytesAt])
    rw [length_bytesAt,show (V .s0+256)+16=V .s0+BitVec.ofNat 64 272 from add_ofNat_assoc _ 256 16] at e
    exact e.trans (by rw [read])

abbrev dataFrame (st w D : Addr) (n : Nat) := ⟨D,n⟩ :: maskFrame st w

/-- Authenticate the ciphertext produced by the XOR loop in its final destination, and leave the tag in scratch. -/
theorem shortPayload_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {V : Reg → BitVec 64} {sp : Addr} {s : State} {X D : Addr}
    {R : Nat} {a : List Byte} {H : Block}
    (he : Env V sp s) (L : Lay (V .s2) (V .s1) (V .s0)) (src : s.gpr .s4=X) (dst : s.gpr .s8=D)
    (len : s.gpr .s5=V .s11) (small : (V .s11).toNat≤240)
    (xd : DataOk (V .s1) (V .s0) s X (V .s11).toNat) (dd : DataW (V .s2) (V .s1) (V .s0) s D (V .s11).toNat)
    (alias : Alias true X D (V .s11).toNat) (rounds : V .s3=BitVec.ofNat 64 R) (hR : R=10 ∨ R=12 ∨ R=14)
    (hb : BkIn (V .s7) (V .s2) (V .s1) (V .s0) sp R s.mem X D (V .s11).toNat s)
    (hH : blockAt s.mem (V .s2+BitVec.ofNat 64 240)=H) (hl : (V .s10).toNat=a.length)
    (hab : Absorbed s.mem (V .s1+BitVec.ofNat 64 16) (V .s1+BitVec.ofNat 64 32) H (a++zeros (padLen a.length)))
    (slot : s.mem.readW (V .s0+BitVec.ofNat 64 dataO) 64=D) :
    let n := (V .s11).toNat
    let ciph := ciphOf s.mem (V .s2) R
    let j := blockAt s.mem (V .s1)
    let ct := gctr ciph (inc32 j) (bytesAt s.mem X n)
    WP isa VG.Impl.AesGcm.RISCV64.Contiguous.shortPayload s fun t =>
      Env V sp t ∧ bytesAt t.mem D n=ct ∧
      bytesAt t.mem (V .s0) 16=toBytes (ghashFrom H (ghash H (blocks (padded a ct)))
        [ofBytes (lensBlock a.length n)] ^^^ ciph j) ∧
      Frame (dataFrame (V .s1) (V .s0) D n ++ otFrame (V .s1) (V .s0) 0 sp) s.mem t.mem := by
  dsimp only
  have hw := maskData_wp he L src dst (n := (V .s11).toNat) (by simpa using len) small xd dd alias rounds hR hb
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp hw) fun _ run => WP.seq (WP.mono run fun u ⟨eu,ku,fr,mask,ct⟩ => ?_)
  have apart {r : Region} (rd : r.Disjoint ⟨D,(V .s11).toNat⟩) (rw : r.Disjoint ⟨V .s0+256,256⟩)
      (rs : r.Disjoint ⟨V .s1,16⟩) (rk : r.Disjoint ⟨V .s0+512,2048⟩) :
      ∀ x ∈ dataFrame (V .s1) (V .s0) D (V .s11).toNat, r.Disjoint x := by
    intro x hx
    simp only [dataFrame,maskFrame,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact rd
    · exact rw
    · exact rs
    · exact rk
  have ctx : ∀ r ∈ dataFrame (V .s1) (V .s0) D (V .s11).toNat,(⟨V .s2,256⟩ : Region).Disjoint r :=
    apart dd.ctx (L.cw'.sub_right (Lay.wSub (d := 256) (by decide))) (L.cs.sub_right (Region.sub_prefix (by decide)))
      (L.cw'.sub_right (Lay.wSub (d := 512) (by decide)))
  have H' := (blockAt_frame fr (fun r hr => (ctx r hr).sub_left (Offset.sub_base _ (d := 240) (by decide : 240+16≤256)))).trans hH
  have hashKeep (i : Nat) (hi : i=16 ∨ i=32) : ∀ r ∈ dataFrame (V .s1) (V .s0) D (V .s11).toNat,
      (⟨V .s1+BitVec.ofNat 64 i,16⟩ : Region).Disjoint r := apart
    (dd.ok.st.symm.sub_left (Lay.stSub (by omega))) (L.st_w (by omega) (.inr ⟨by decide,by decide⟩))
    (by simpa using Lay.st_st (st := V .s1) (a := i) (n := 16) (d := 0) (k := 16) (.inr (by omega)) (by omega) (by decide))
    (L.st_w (by omega) (.inr ⟨by decide,by decide⟩))
  have ab : Absorbed u.mem (V .s1+BitVec.ofNat 64 16) (V .s1+BitVec.ofNat 64 32) H (a++zeros (padLen a.length)) :=
    ⟨(blockAt_frame fr (hashKeep 16 (.inl rfl))).trans hab.1,
      (bytesAt_frame fr (fun r hr => (hashKeep 32 (.inr rfl) r hr).sub_left (Region.sub_prefix (by omega))) (by omega)).trans hab.2⟩
  have sl : u.mem.readW (V .s0+BitVec.ofNat 64 dataO) 64=D := by
    rw [fr.readW (r := ⟨_,8⟩) (Region.contains_self _ _) (apart
      (dd.ok.w.symm.sub_left (Lay.wSub (by decide))) (Lay.w_w (.inl (by decide)) (by decide) (by decide))
      (by simpa using (L.st_w (a := 0) (n := 16) (d := dataO) (k := 8) (by decide) (.inr ⟨by decide,by decide⟩)).symm)
      (Lay.w_w (.inl (by decide)) (by decide) (by decide))) (by decide)]
    exact slot
  refine WP.mono (authenticate_wp L eu H' hl ab (dd.ok.of_eq ku.rd ku.wr ku.sp) sl) fun t ⟨et,tag,ft⟩ =>
    ⟨et,?_,by rw [tag,ct,mask],?_⟩
  · rw [bytesAt_frame ft (fun r hr => by
      simp only [otFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact dd.ok.st.sub_right (Region.sub_prefix (by decide))
      · exact dd.ok.w.sub_right (Lay.wSub (by decide))
      · exact dd.ok.w.sub_right (Lay.wSub (by decide))
      · exact dd.ok.w.sub_right (Lay.wSub (by decide))
      · simpa only [he.sp] using dd.ok.sk) (by omega),ct]
  · exact (fr.mono fun r hr => List.mem_append_left _ hr).trans (ft.mono fun r hr => List.mem_append_right _ hr)

end VG.Proof.AesGcm.RISCV64.Contiguous
