module

-- separate module: The GHASH tag and final mask proof does not depend on the plaintext XOR loop.

public import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.Tag
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset

/-! # Finish authentication with the tag mask produced by the first CTR lane -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Gcm (Block blockAt toBytes ghashFrom ofBytes)
open VG.Spec.Aes (bytesAt)

private abbrev word (i : Nat) : List Instr :=
  [.load .d .t0 .s1 (16+i),.load .d .t1 .s0 (256+i),.logic .xor .t0 .t0 .t1,.store .d .t0 .s0 i]

private theorem word_wp {V : Reg → BitVec 64} {sp : Addr} {s : State} {i : Nat} (pos : i=0 ∨ i=8)
    (L : Lay (V .s2) (V .s1) (V .s0)) (he : Env V sp s) :
    WP isa (.block (word i)) s fun t => Env V sp t ∧ t.mem=s.mem.writeW (V .s0+BitVec.ofNat 64 i)
      (s.mem.readW (V .s1+BitVec.ofNat 64 (16+i)) 64 ^^^ s.mem.readW (V .s0+BitVec.ofNat 64 (256+i)) 64) := by
  unfold word
  refine Steps.wp_ld (a := V .s1+BitVec.ofNat 64 (16+i)) (by omega) (by rw [he.s1]) (L.stal (by omega) (by omega))
    (he.perm.stR (by omega)) fun v a => ?_
  refine Steps.wp_ld (a := V .s0+BitVec.ofNat 64 (256+i)) (by omega) (by rw [a.other _ (by decide),he.s0])
    (L.wal8 (by omega) (by omega)) (by rw [a.rd,a.wr];exact he.perm.wR (by omega)) fun u b => ?_
  refine Steps.wp_xor fun z c => Steps.wp_sd (a := V .s0+BitVec.ofNat 64 i) (by omega)
    (by rw [c.other _ (by decide),b.other _ (by decide),a.other _ (by decide),he.s0]) (L.wal8 (by omega) (by omega))
    (by rw [c.wr,b.wr,a.wr];exact he.perm.wW (by omega)) fun t d => WP.block_nil ⟨?_,?_⟩
  · apply he.keep
    · intro r hr
      rw [d.gpr,c.other r (by revert r;decide),b.other r (by revert r;decide),a.other r (by revert r;decide)]
    · rw [d.sp,c.sp,b.sp,a.sp]
    · rw [d.rd,c.rd,b.rd,a.rd]
    · rw [d.wr,c.wr,b.wr,a.wr]
  · rw [d.mem,c.mem,b.mem,a.mem,c.gpr,b.other _ (by decide),a.gpr,b.gpr,a.mem]

private theorem xorBlock (m : Mem) (Y T : Addr) :
    VG.Spec.Cmac.xor (bytesAt m Y 16) (bytesAt m T 16) = toBytes (blockAt m Y ^^^ blockAt m T) := by
  rw [Cmac.bytesAt_blockAt,Cmac.bytesAt_blockAt]
  apply Cmac.ext16 (by simp [Cmac.length_xor,Cmac.toBytes_length]) (Cmac.toBytes_length _)
  intro k hk
  rw [Cmac.getD_xor (by simp [Cmac.toBytes_length]) (by simpa [Cmac.toBytes_length] using hk),Proof.Aes.toBytes_xor _ _ hk]

private theorem tagWords_wp {V : Reg → BitVec 64} {sp : Addr} {s : State}
    (L : Lay (V .s2) (V .s1) (V .s0)) (he : Env V sp s) :
    WP isa (.block (word 0 ++ word 8)) s fun t =>
      Env V sp t ∧ bytesAt t.mem (V .s0) 16 = toBytes (blockAt s.mem (V .s1+BitVec.ofNat 64 16) ^^^ blockAt s.mem (V .s0+BitVec.ofNat 64 256)) ∧
      Frame [⟨V .s0,16⟩] s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (word_wp (.inl rfl) L he) fun u ⟨eu,mu⟩ =>
    WP.mono (word_wp (.inr rfl) L eu) fun t ⟨et,mt⟩ => ⟨et,?_,?_⟩
  all_goals rw [show V .s0+BitVec.ofNat 64 0=V .s0 from BitVec.add_zero _] at mu
  · have dis (a : Addr) (sep : (⟨a,8⟩ : Region).Disjoint ⟨V .s0,8⟩) :
        u.mem.readW a 64=s.mem.readW a 64 := by
      rw [mu]
      exact Mem.readW_writeW_sep (Region.Disjoint.sep sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)
    have dY : (⟨V .s1+BitVec.ofNat 64 24,8⟩ : Region).Disjoint ⟨V .s0,8⟩ := by
      simpa using L.st_w (a := 24) (n := 8) (d := 0) (k := 8) (by decide) (.inl (by decide))
    have dT : (⟨V .s0+BitVec.ofNat 64 264,8⟩ : Region).Disjoint ⟨V .s0,8⟩ := by
      simpa using Lay.w_w (w := V .s0) (a := 264) (n := 8) (d := 0) (k := 8) (.inr (by decide)) (by decide) (by decide)
    rw [mt,dis _ dY,dis _ dT,mu,Cmac.bytesAt_store2,←xorBlock]
    simpa only [add_ofNat_assoc,Nat.reduceAdd] using Cmac.xor_words s.mem (V .s1+BitVec.ofNat 64 16) (V .s0+BitVec.ofNat 64 256)
  · rw [mt,mu];exact Cmac.frame_store2 _ _ _

theorem maskTag_wp {invoke : Prog isa} {V : Reg → BitVec 64} {sp : Addr} {s : State}
    (L : Lay (V .s2) (V .s1) (V .s0)) (he : Env V sp s)
    (exec : FramedHashAction invoke (V .s2+BitVec.ofNat 64 240) [⟨V .s0+BitVec.ofNat 64 96,16⟩] s) :
    WP isa (VG.Impl.AesGcm.RISCV64.Contiguous.maskTagWith invoke) s fun t =>
      Env V sp t ∧ bytesAt t.mem (V .s0) 16 =
        toBytes (ghashFrom (blockAt s.mem (V .s2+BitVec.ofNat 64 240)) (blockAt s.mem (V .s1+BitVec.ofNat 64 16))
          [ofBytes (VG.Proof.Gcm.lensBlock (V .s10).toNat (V .s11).toNat)] ^^^ blockAt s.mem (V .s0+BitVec.ofNat 64 256)) ∧
      Frame (⟨V .s0,16⟩ :: tFrame (V .s1) (V .s0) 16 sp) s.mem t.mem := by
  apply WP.seq
  refine Steps.wp_mv fun v a => Steps.wp_mv fun u b => WP.block_nil ?_
  have g (r : Reg) (x : r≠.s4) (y : r≠.s6) : u.gpr r=s.gpr r := (b.other r y).trans (a.other r x)
  have eu := he.keep (fun r hr => g r (by revert r;decide) (by revert r;decide)) (b.sp.trans a.sp)
    (b.rd.trans a.rd) (b.wr.trans a.wr)
  have um : u.mem=s.mem := b.mem.trans a.mem
  have lenA : u.gpr .s4=V .s10 := (b.other _ (by decide)).trans (a.gpr.trans (he.fr _ (by decide)))
  have lenC : u.gpr .s6=V .s11 := b.gpr.trans ((a.other _ (by decide)).trans (he.fr _ (by decide)))
  apply WP.seq
  refine WP.mono (lens_ok_with L (.inr (by rfl)) eu rfl (FramedHashAction.kept exec ⟨um,b.rd.trans a.rd,b.wr.trans a.wr,b.sp.trans a.sp⟩)) fun z ⟨ez,_,hash,_,frame⟩ =>
    WP.mono (tagWords_wp L ez) fun t ⟨et,tag,ft⟩ => ⟨et,?_,?_⟩
  · rw [tag,hash,lenA,lenC,blockAt_frame frame (fun r hr => by
      simp only [tFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (L.st_w (a := 16) (n := 16) (d := 256) (k := 16) (by decide) (.inr ⟨by decide,by decide⟩)).symm
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact he.stk'.w.sub_left (Lay.wSub (by decide))),um]
  · rw [←um]
    exact (frame.sub (fun r hr => ⟨r,List.mem_cons_of_mem _ hr,fun _ hx => hx⟩)).trans
      (ft.sub (fun r hr => ⟨r,Or.inl (List.mem_singleton.mp hr) |> List.mem_cons.mpr,fun _ hx => hx⟩))

/-- Authenticate the ciphertext in its final destination with the precomputed mask. -/
theorem authenticate_wp {invoke : Prog isa} {V : Reg → BitVec 64} {sp : Addr} {s : State}
    {D : Addr} {a : List Byte} {H : Block}
    (L : Lay (V .s2) (V .s1) (V .s0)) (he : Env V sp s) (hH : blockAt s.mem (V .s2+BitVec.ofNat 64 240)=H)
    (hl : (V .s10).toNat=a.length)
    (hab : VG.Proof.Gcm.Absorbed s.mem (V .s1+BitVec.ofNat 64 16) (V .s1+BitVec.ofNat 64 32) H
      (a++VG.Spec.Gcm.zeros (VG.Spec.Gcm.padLen a.length)))
    (hd : DataOk (V .s1) (V .s0) s D (V .s11).toNat) (slot : s.mem.readW (V .s0+BitVec.ofNat 64 dataO) 64=D)
    (exec : FramedHashAction invoke (V .s2+BitVec.ofNat 64 240) (j0Frame (V .s1) (V .s0) sp) s) :
    WP isa (.seq (.block dataArgs) (.seq (absorbWith invoke 16) (.seq (.block [.logicImm .and .s6 .s11 15])
      (.seq (flushWith invoke 16) (VG.Impl.AesGcm.RISCV64.Contiguous.maskTagWith invoke))))) s fun t => Env V sp t ∧
      bytesAt t.mem (V .s0) 16 = toBytes (ghashFrom H
        (VG.Spec.Gcm.ghash H (VG.Spec.Gcm.blocks (VG.Proof.Gcm.padded a (bytesAt s.mem D (V .s11).toNat))))
        [ofBytes (VG.Proof.Gcm.lensBlock a.length (V .s11).toNat)] ^^^ blockAt s.mem (V .s0+BitVec.ofNat 64 256)) ∧
      Frame (otFrame (V .s1) (V .s0) 0 sp) s.mem t.mem := by
  refine oneTagAbsorb_ok_with L he hH hab hd slot (fun u eu hk hy rd wr fr => ?_) exec
  have ju : Frame (j0Frame (V .s1) (V .s0) sp) s.mem u.mem := fr.sub fun r hr =>
    (List.mem_append.mp hr).elim (abs16_j0 r) (t16_j0 r)
  refine WP.mono (maskTag_wp L eu (FramedHashAction.temp_j0
    (FramedHashAction.after exec ⟨rd,wr,eu.sp.trans he.sp.symm⟩ ju))) fun t ⟨et,tag,ft⟩ => ⟨et,?_,?_⟩
  · have hm : blockAt u.mem (V .s0+BitVec.ofNat 64 256)=blockAt s.mem (V .s0+BitVec.ofNat 64 256) := by
      apply blockAt_frame fr
      intro r hr
      rcases List.mem_append.mp hr with ab | fl
      · simp only [absFrame,List.mem_cons,List.not_mem_nil,or_false] at ab
        rcases ab with rfl | rfl | rfl | rfl
        · exact (L.st_w (by decide) (.inr ⟨by decide,by decide⟩)).symm
        · exact (L.st_w (by decide) (.inr ⟨by decide,by decide⟩)).symm
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact he.stk'.w.sub_left (Lay.wSub (by decide))
      · simp only [tFrame,List.mem_cons,List.not_mem_nil,or_false] at fl
        rcases fl with rfl | rfl | rfl | rfl
        · exact (L.st_w (by decide) (.inr ⟨by decide,by decide⟩)).symm
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact he.stk'.w.sub_left (Lay.wSub (by decide))
    rw [tag,hk,hy,hl,hm]
  · apply Frame.trans (fr.sub (fun r hr => (List.mem_append.mp hr).elim (abs_otSub r) (t_otSub r)))
    apply ft.sub
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨_,by simp [otFrame],fun _ hx => hx⟩
    · exact t_otSub r hr

end VG.Proof.AesGcm.RISCV64.Contiguous
