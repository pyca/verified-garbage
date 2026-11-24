module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Remainder
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectBatches
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tables
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The prepared eight-block body authenticates the ciphertext produced by
its own stores in either layout, and reloads the original input for the tail. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous
open VG.Proof.Gcm.AArch64.Stitch (BatchArgs BatchMid Gh8Ok kRegsT sealPrepared_ok)
open VG.Proof.AesGcm.AArch64.Stitch (tblR sFrame pre)
open VG.Spec.Gcm (ctxH blockAt)

abbrev outputView (s : State) (O : Addr) := s.write .x .x23 O

theorem batchSlots {wn : Nat} {Ctx St W O : Addr} {n : Nat} (L : Lay wn Ctx St W)
    (ds : (⟨O,n⟩ : Region).Disjoint (workR wn W)) {d : Nat} (hd : 216 ≤ d) (hi : d+8 ≤ 328) :
    ∀ r ∈ sFrame St W O n, (slotR W d).Disjoint r := by
  have lim := L.hWn
  intro r hr; simp only [sFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact (L.st_w (d := d) (by decide) (.inr ⟨by omega,by omega⟩)).symm
  · exact (L.st_w (d := d) (by decide) (.inr ⟨by omega,by omega⟩)).symm
  · exact (ds.symm.sub_left (Offset.sub_base W (by omega))).sub_right (Region.sub_prefix (Nat.mul_div_le n 128))
  · exact Offset.disjoint W (.inl (by change d+8 ≤ 512; omega)) (by omega) (by decide)

theorem batches_ok {wn R n : Nat} {Ctx St W SP D O P : Addr} {s : State}
    (L : Lay wn Ctx St W) (he : Env wn Ctx St W SP s) (gh : Gh8Ok)
    (rounds : R = 10 ∨ R = 12 ∨ R = 14) (x22 : s.gpr .x22 = BitVec.ofNat 64 R)
    (x23 : s.gpr .x23 = D) (x26 : s.gpr .x26 = BitVec.ofNat 64 n)
    (sd : DataOk wn St W s D n) (od : DataW wn Ctx St W s O n) (mode : BufferLayout D O n)
    (hn : 128 ≤ n) (p : GhWCall s Ctx (word St 16) (word W 512) P)
    (pw : s.mem.readW (word s.sp 16) 64 = P) (rp : InRegions (s.rd++s.wr) (word s.sp 16) 8)
    (src : s.mem.readW (word W dataO) 64 = D) (dst : s.mem.readW (word W dstO) 64 = O) :
    WP isa batches s fun t => ∃ z, BatchMid Ctx St W D O R n (outputView s O) z ∧
      Regs [.x23] z t ∧ t.gpr .x23 = D ∧ t.gpr .x26 = BitVec.ofNat 64 n := by
  let b := s.write .x .x9 (s.gpr .x26 >>> 7)
  have nb : b.gpr .x9 = BitVec.ofNat 64 (n/128) := by
    simp only [b,gpr_write,ite_true,Size.bits,BitVec.setWidth_eq,x26,Proof.Gcm.AArch64.Stitch.ushr7 sd.lt]
  have gb (r : Reg) (hr : r ≠ .x9) : b.gpr r = s.gpr r := by simp [b,gpr_write,hr]
  have eb := he.keep (fun r hr => gb _ (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl <;> decide))
    (s' := b) rfl rfl rfl
  unfold batches Impl.AesGcm.AArch64.Stitch.stitched
  rw [WP.seq_iff]; refine WP.of_runBlock ⟨b,by arun [b],?_⟩
  refine WP.ite (decide (n/128 = 0)) (Proof.Aes.AArch64.Aese.eval_zero nb (by have := sd.lt; omega))
    (fun h => False.elim (by have := of_decide_eq_true h; omega)) (fun _ => ?_)
  rw [List.nil_append]
  refine WP.seq ((Stitch.pwTbl_ok (k := 16) (by decide) eb pw rp p.reads p.repr).mono ?_)
  intro u ⟨tok,fr,gr,sp,rd,wr⟩
  have g (r : Reg) (h5 : r ≠ .x5) (h9 : r ≠ .x9) : u.gpr r = s.gpr r := (gr r h5).trans (gb r h9)
  have eu := he.keep (fun r hr => g _ (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl <;> decide)
    (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl <;> decide)) sp rd wr
  have ft : Frame [tblR W] s.mem u.mem := fr
  have oval : u.mem.read (W+320#64) 8 = O := by
    exact (ft.readW (r := slotR W 320) (Region.contains_self _ _)
      (by simpa only [List.mem_singleton,forall_eq] using
        (Offset.disjoint W (d := 320) (n := 8) (e := 512) (k := 192) (.inl (by decide)) (by decide) (by decide))) (by decide)).trans dst
  have ir := eu.perm.wR (d := 320) (n := 8) (by decide)
  let a := (u.write .x .x15 (u.gpr .x23)).write .x .x23 O
  refine WP.seq (WP.of_runBlock ⟨a,by arun [a,eu.x19,dstO,ir,oval,BitVec.add_zero],?_⟩)
  have ga (r : Reg) (h15 : r ≠ .x15) (h23 : r ≠ .x23) : a.gpr r = u.gpr r := by simp [a,gpr_write,h15,h23]
  have ea := eu.keep (fun r hr => ga _ (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl <;> decide)
    (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl <;> decide)) (s' := a) rfl rfl rfl
  have aa : BatchArgs wn Ctx St W SP D O R n a :=
    ⟨ea,rounds,(ga _ (by decide) (by decide)).trans ((g _ (by decide) (by decide)).trans x22),
      by simp [a,gpr_write,g .x23 (by decide) (by decide),x23],by simp [a,gpr_write],
      (ga _ (by decide) (by decide)).trans ((g _ (by decide) (by decide)).trans x26),sd.of_eq rd wr,od.of_eq rd wr,mode⟩
  have hH : blockAt a.mem (word Ctx 240) = ctxH s.mem Ctx :=
    blockAt_frame ft fun r hr => (Stitch.tbl_ctx L r hr).sub_left (Lay.ctxSub (by decide))
  have reg (r : Reg) (_ : r ≠ .x0) (h5 : r ≠ .x5) (hk : r ∉ kRegsT true) : a.gpr r = (outputView s O).gpr r := by
    by_cases r23 : r = .x23
    · subst r; simp [a,outputView,gpr_write]
    · have ne (j : Reg) (mem : j ∈ kRegsT true) : r ≠ j := fun eq => hk (eq ▸ mem)
      simp only [outputView,gpr_write,Size.bits,BitVec.setWidth_eq,r23,ite_false]
      exact (ga r (ne _ (by decide)) r23).trans (g r h5 (ne _ (by decide)))
  refine WP.seq ((sealPrepared_ok (s := outputView s O) (u := a) aa L gh (aa.sealPre L hn (hH ▸ tok)) ft reg sp rd wr).mono ?_)
  intro z hz
  have Wz : z.gpr .x19 = W := (hz.gpr _ (by decide) (by decide) (by decide)).trans he.x19
  have rz : InRegions (z.rd++z.wr) (W+232#64) 8 := by rw [hz.rd,hz.wr]; exact he.perm.wR (by decide)
  have Dz : z.mem.read (W+232#64) 8 = D := (hz.frame.readW (r := slotR W 232) (Region.contains_self _ _)
    (batchSlots L od.ok.w (by decide) (by decide)) (by decide)).trans src
  refine WP.of_runBlock ⟨_,by arun [Wz,dataO,rz,Dz],?_⟩
  exact ⟨z,hz,⟨by others_tac,rfl,rfl,rfl,rfl⟩,by simp [gpr_write],
    by simp [gpr_write,hz.gpr .x26 (by decide) (by decide) (by decide),outputView,x26]⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared
