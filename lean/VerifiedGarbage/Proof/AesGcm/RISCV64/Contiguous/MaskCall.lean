module

-- separate module: Keep bitsliced subroutine permissions and saved-register reasoning apart from byte-level payload composition.

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Masks
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.MaskZero
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Tag
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-! # Call the bitsliced CTR kernel once for the tag mask and short plaintext -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Gcm (blockAt blocksAt aesWith)
open VG.Spec.Aes (bytesAt)

private theorem maskCount {n : Nat} (h : n≤240) :
    (((BitVec.ofNat 64 n+15) >>> 4) + 1) = BitVec.ofNat 64 ((n+15)/16+1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat]
  simp only [Nat.shiftRight_eq_div_pow]
  change ((((n % 2^64+15) % 2^64)/16+1) % 2^64) = ((n+15)/16+1)%2^64
  rw [Nat.mod_eq_of_lt (show n<2^64 by omega), Nat.mod_eq_of_lt (show n+15<2^64 by omega)]

theorem maskArgs_wp {V : Reg → BitVec 64} {sp : Addr} {s : State} {n R : Nat}
    (he : Env V sp s) (hn : s.gpr .s5=BitVec.ofNat 64 n) (h : n≤240) (hR : V .s3=BitVec.ofNat 64 R) :
    WP isa (.block VG.Impl.AesGcm.RISCV64.Contiguous.maskArgs) s fun t =>
      t.gpr .a0=V .s7 ∧ t.gpr .a1=BitVec.ofNat 64 R ∧ t.gpr .a2=V .s1 ∧ t.gpr .a3=V .s0+256 ∧
      t.gpr .a4=BitVec.ofNat 64 ((n+15)/16+1) ∧ t.gpr .a5=V .s0+512 ∧ t.mem=s.mem ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .a4 → r ≠ .a5 → t.gpr r=s.gpr r) ∧ Keeps' s t := by
  have h7 : s.gpr .s7=V .s7 := he.fr _ (by decide)
  unfold VG.Impl.AesGcm.RISCV64.Contiguous.maskArgs
  crun [Int.reduceNatCast',scrO,mov,he.s0,he.s1,he.s3,h7,hR,hn,exec_shift_d (show 4<64 by decide)]
  exact ⟨maskCount h,fun r a b c d e f => by simp [a,b,c,d,e,f],⟨rfl,rfl,rfl⟩⟩

theorem batchCall {V : Reg → BitVec 64} {sp : Addr} {s : State} {R nb : Nat} {S D : Addr} {n : Nat}
    (L : Lay (V .s2) (V .s1) (V .s0)) (he : Env V sp s)
    (h0 : s.gpr .a0 = V .s7) (h1 : s.gpr .a1 = BitVec.ofNat 64 R)
    (h2 : s.gpr .a2 = V .s1) (h3 : s.gpr .a3 = V .s0 + 256)
    (h4 : s.gpr .a4 = BitVec.ofNat 64 nb) (h5 : s.gpr .a5 = V .s0 + 512)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (bound : nb ≤ 16)
    (hb : BkIn (V .s7) (V .s2) (V .s1) (V .s0) sp R s.mem S D n s) :
    CtrBsCall s (V .s7) (V .s2) (V .s1) (V .s0+256) (V .s0+512) R nb := by
  refine ⟨h0,h1,h2,h3,h4,h5,hR,by omega,?_,?_,?_,?_,?_,?_,?_,hb.al,hb.keys,?_,?_⟩
  · exact hb.st.sub_right (Region.sub_prefix (by decide))
  · exact hb.w.sub_right (Lay.wSub (d := 256) (by omega))
  · exact hb.w.sub_right (Lay.wSub (d := 512) (by decide))
  · simpa using L.st_w (a := 0) (n := 16) (d := 256) (k := 16*nb) (by decide) (.inr ⟨by decide,by omega⟩)
  · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide,by decide⟩)
  · exact Lay.w_w (w := V .s0) (a := 256) (n := 16*nb) (d := 512) (k := 2048) (by omega) (by omega) (by decide)
  · have := L.ww
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change (V .s0).toNat+256 < 2^64; omega)]
    change (V .s0).toNat+256+16*nb ≤ 2^64
    omega
  · exact Covers.cons hb.rd (Covers.cons (covers_left (covers_prefix he.perm.st (by decide))) (Covers.cons
      (covers_left (he.perm.wC (d := 256) (by omega))) (Covers.cons (covers_left (he.perm.wC (d := 512) (by decide))) Covers.nil)))
  · exact Covers.cons (covers_prefix he.perm.st (by decide)) (Covers.cons (he.perm.wC (d := 256) (by omega))
      (Covers.cons (he.perm.wC (d := 512) (by decide)) Covers.nil))

theorem batch_masks {s : State} {B K C D W : Addr} {R n : Nat}
    (h : CtrBsCall s B K C D W R ((n+15)/16+1))
    (zero : blocksAt s.mem D ((n+15)/16+1) = List.replicate ((n+15)/16+1) 0) :
    WP isa (ctrCallB true) s fun t =>
      CtrPost s K C D W R ((n+15)/16+1) t ∧
      Masks t.mem D (aesWith R (bytesAt s.mem K (16*(R+1)))) (blockAt s.mem C) n := by
  refine WP.mono (ctrBs_call h) fun t p => ⟨p,masks_of_ctr ?_⟩
  rw [p.out,zero]

/-- The writes of the batch exclude the plaintext, ciphertext and authentication accumulator. -/
abbrev maskFrame (st w : Addr) : List Region := [⟨w+256,256⟩,⟨st,16⟩,⟨w+512,2048⟩]

theorem masks_wp {V : Reg → BitVec 64} {sp : Addr} {s : State} {R n : Nat} {S D : Addr}
    (L : Lay (V .s2) (V .s1) (V .s0)) (he : Env V sp s)
    (hn : s.gpr .s5=BitVec.ofNat 64 n) (small : n≤240) (hr : V .s3=BitVec.ofNat 64 R)
    (hR : R=10 ∨ R=12 ∨ R=14) (hb : BkIn (V .s7) (V .s2) (V .s1) (V .s0) sp R s.mem S D n s) :
    WP isa VG.Impl.AesGcm.RISCV64.Contiguous.masks s fun t =>
      Env V sp t ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ Keeps' s t ∧
      Frame (maskFrame (V .s1) (V .s0)) s.mem t.mem ∧
      Masks t.mem (V .s0+256) (ciphOf s.mem (V .s2) R) (blockAt s.mem (V .s1)) n := by
  unfold VG.Impl.AesGcm.RISCV64.Contiguous.masks
  apply WP.seq
  rw [WP.block_append_iff]
  rw [WP.block_append_iff]
  apply Steps.wp_li (by decide : 0 < 2048)
  intro v li
  apply WP.block_nil
  have ev := he.keep (fun r hr => li.other r (by revert r; decide)) li.sp li.rd li.wr
  refine WP.mono (maskZero_wp li.gpr (ev.s0 ▸ L.wal) (ev.s0 ▸ ev.perm.w) (by decide : 16≤16)) fun u clear => ?_
  have ug : u.gpr=v.gpr := by rw [clear.state]
  have uk : Keeps' s u := by rw [clear.state]; exact ⟨li.rd,li.wr,li.sp⟩
  have eu := he.keep (fun r hr => (congrFun ug r).trans (li.other r (by revert r; decide))) uk.sp uk.rd uk.wr
  refine WP.mono (maskArgs_wp eu ((congrFun ug .s5).trans ((li.other _ (by decide)).trans hn)) small hr) ?_
  intro a args
  obtain ⟨a0,a1,a2,a3,a4,a5,am,ag,ak⟩ := args
  have ea := eu.keep (fun r hr => ag r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) ak.sp ak.rd ak.wr
  have f : Frame [⟨V .s0+256,256⟩] s.mem a.mem := by
    rw [am,←li.mem,←ev.s0]; exact clear.frame
  have disCtx : ∀ r ∈ [⟨V .s0+256,256⟩], (⟨V .s2,256⟩ : Region).Disjoint r := by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; exact L.cw'.sub_right (Lay.wSub (d := 256) (by decide))
  have bk := hb.frame hR f (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hb.w.sub_right (Lay.wSub (d := 256) (by decide)))
    disCtx (ak.rd.trans uk.rd) (ak.wr.trans uk.wr)
  have cnt : (n+15)/16+1 ≤ 16 := by omega
  have call := batchCall L ea a0 a1 a2 a3 a4 a5 hR cnt bk
  have zero := clear.prefix cnt
  rw [ev.s0,←am] at zero
  refine WP.mono (batch_masks call zero) fun t ⟨post,m⟩ => ?_
  refine ⟨ea.keep (fun r hr => post.saved r (frozen_preserved r hr)) post.sp post.rd post.wr,?_,
    ⟨post.rd.trans (ak.rd.trans uk.rd),post.wr.trans (ak.wr.trans uk.wr),post.sp.trans (ak.sp.trans uk.sp)⟩,?_,?_⟩
  · intro r hr
    rw [post.saved r hr,ag r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide),congrFun ug r,li.other r (by revert r; decide)]
  · apply Frame.trans (f.sub (fun r hr => ⟨r,by simp_all [maskFrame],fun _ h => h⟩))
    apply post.frame.sub
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_,by simp [maskFrame],fun _ h => h⟩
    · exact ⟨⟨V .s0+256,256⟩,by simp [maskFrame],Region.sub_prefix (by omega)⟩
    · exact ⟨_,by simp [maskFrame],fun _ h => h⟩
  · change Masks t.mem _ (ciphOf a.mem _ _) _ _ at m
    rw [ciph_frame f disCtx hR,blockAt_frame f (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      simpa using L.st_w (a := 0) (n := 16) (d := 256) (k := 256) (by decide) (.inr ⟨by decide,by decide⟩))] at m
    exact m

end VG.Proof.AesGcm.RISCV64.Contiguous
