module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Batches
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tables
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.CT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Prepared

/-! Stitched exact-alias and disjoint records follow the same branch and
access trace whenever their two public input and output addresses agree. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.Contiguous
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)
open VG.Proof.AesGcm.AArch64.Fast (stRegs)

private theorem table_rel {a b : State} {P : Addr} (sp : a.sp = b.sp)
    (reg : ∀ r ∈ stRegs, a.gpr r = b.gpr r)
    (sa : a.mem.readW (word a.sp 16) 64 = P) (sb : b.mem.readW (word b.sp 16) 64 = P)
    (ra : InRegions (a.rd++a.wr) (word a.sp 16) 8) (rb : InRegions (b.rd++b.wr) (word b.sp 16) 8) :
    RelCT isa (Eq2 a b) (.block (Impl.AesGcm.AArch64.Stitch.pwTbl 16)) TT := by
  have cert : ∃ h, (taint.check (Taint.ofRegs (.x5 :: stRegs)) (.seq (.block Fast.pwRest) (.block [])) h).isSome = true :=
    ⟨_,by taint_decide⟩
  have rel := Fast.pwTbl_rel (l := .block []) (k := 16) (by decide) (fun hsp hreg =>
    rel_taint (.x5 :: stRegs) hsp hreg cert) sp reg sa ra sb rb
  intro s t ts tt u v hp ex ey
  simpa only [List.append_nil] using rel s t _ _ u v hp (.seq ex (.block rfl)) (.seq ey (.block rfl))

private theorem batchPtrs {s : State} {W O : Addr} (h19 : s.gpr .x19 = W)
    (read : InRegions (s.rd++s.wr) (word W dstO) 8) (slot : s.mem.readW (word W dstO) 64 = O) :
    WP isa (.block [mov .x15 .x23,.ldr .x .x23 .x19 dstO]) s fun a => a.gpr .x15 = s.gpr .x23 ∧ a.gpr .x23 = O ∧
      Regs [.x15,.x23] s a := by
  change InRegions _ (W+320#64) 8 at read
  change s.mem.read (W+320#64) 8 = O at slot
  exact WP.of_runBlock ⟨(s.write .x .x15 (s.gpr .x23)).write .x .x23 O,by arun [h19,dstO,read,slot,BitVec.add_zero],by simp [gpr_write],by simp [gpr_write],⟨by others_tac,rfl,rfl,rfl,rfl⟩⟩

theorem batches_rel {wn n : Nat} {Ctx St W SP O P : Addr} {a b : State}
    (forward : Bool) (ea : Env wn Ctx St W SP a) (eb : Env wn Ctx St W SP b)
    (reg : ∀ r ∈ stRegs, r ≠ .x9 → a.gpr r = b.gpr r) (an : a.gpr .x26 = BitVec.ofNat 64 n) (hn : n < 2^64)
    (pa : GhWCall a Ctx (word St 16) (word W 512) P) (pb : GhWCall b Ctx (word St 16) (word W 512) P)
    (sa : a.mem.readW (word a.sp 16) 64 = P) (sb : b.mem.readW (word b.sp 16) 64 = P)
    (ra : InRegions (a.rd++a.wr) (word a.sp 16) 8) (rb : InRegions (b.rd++b.wr) (word b.sp 16) 8)
    (da : a.mem.readW (word W dstO) 64 = O) (db : b.mem.readW (word W dstO) 64 = O) :
    RelCT isa (Eq2 a b) (batches forward) TT := by
  refine Fast.stitched_rel (ea.sp.trans eb.sp.symm) reg an hn ?_
  intro u z sp rg gu mu ru wu su gz mz rz wz sz
  have keep {u a : State} (en : Env wn Ctx St W SP a)
      (g : ∀ r, r ≠ .x9 → u.gpr r = a.gpr r) (r : u.rd = a.rd) (w : u.wr = a.wr) (sp : u.sp = a.sp) :
      Env wn Ctx St W SP u := en.keep (fun i hi => g _ (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl|rfl|rfl <;> decide)) sp r w
  have eu := keep ea gu ru wu su
  have ez := keep eb gz rz wz sz
  have pu : u.mem.readW (word u.sp 16) 64 = P := by rw [mu,su]; exact sa
  have pz : z.mem.readW (word z.sp 16) 64 = P := by rw [mz,sz]; exact sb
  have ur : InRegions (u.rd++u.wr) (word u.sp 16) 8 := by rw [ru,wu,su]; exact ra
  have zr : InRegions (z.rd++z.wr) (word z.sp 16) 8 := by rw [rz,wz,sz]; exact rb
  refine rel_seq (table_rel sp rg pu pz ur zr)
    (Stitch.pwTbl_ok (k := 16) (by decide) eu pu ur (by rw [ru,wu]; exact pa.reads) (mu ▸ pa.repr))
    (Stitch.pwTbl_ok (k := 16) (by decide) ez pz zr (by rw [rz,wz]; exact pb.reads) (mz ▸ pb.repr)) ?_
  intro x y ⟨_,fx,gx,sx,rx,wx⟩ ⟨_,fy,gy,sy,ry,wy⟩
  have hx := (gx .x19 (by decide)).trans eu.x19
  have hy := (gy .x19 (by decide)).trans ez.x19
  have eq (i : Reg) (hi : i ∈ stRegs) : x.gpr i = y.gpr i :=
    (gx _ (by intro h; subst i; contradiction)).trans ((rg _ hi).trans (gy _ (by intro h; subst i; contradiction)).symm)
  have mem {x u : State} (f : Frame [Stitch.tblR W] u.mem x.mem) :
      x.mem.readW (word W dstO) 64 = u.mem.readW (word W dstO) 64 :=
    f.readW (r := slotR W dstO) (Region.contains_self _ _) (by intro r hr; obtain rfl := List.mem_singleton.mp hr
                                                               exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide)
  refine rel_seq (rel_taint [.x19] (sx.trans (sp.trans sy.symm)) (by agree_tac [hx,hy]) ⟨_,by taint_decide⟩)
    (batchPtrs hx (by rw [rx,wx]; exact eu.perm.wR (by decide)) ((mem fx).trans (mu ▸ da)))
    (batchPtrs hy (by rw [ry,wy]; exact ez.perm.wR (by decide)) ((mem fy).trans (mz ▸ db))) ?_
  intro i j ⟨i15,i23,ri⟩ ⟨j15,j23,rj⟩
  have lr (q : Reg) (inS : q ∈ stRegs) (ne : q ∉ [Reg.x15,.x23]) := (ri.others q ne).trans ((eq q inS).trans (rj.others q ne).symm)
  exact rel_taint [.x9,.x15,.x19,.x20,.x21,.x22,.x23,.x26] (ri.sp.trans (sx.trans (sp.trans (sy.symm.trans rj.sp.symm))))
    (by agree_tac [i15,j15,i23,j23,eq .x23 (by decide),lr .x9 (by decide) (by decide),
      lr .x19 (by decide) (by decide),lr .x20 (by decide) (by decide),lr .x21 (by decide) (by decide),
      lr .x22 (by decide) (by decide),lr .x26 (by decide) (by decide)]) (by cases forward <;> exact ⟨_,by taint_decide⟩)

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared
