module

meta import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Medium
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FinishCT
public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Medium
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FinishSpec

import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
public import VerifiedGarbage.Proof.Gcm.Clmul.Ops
public import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
import VerifiedGarbage.Proof.Gcm.Short
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesGcm.AArch64.Save
import VerifiedGarbage.Proof.Cmac.Stream

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64.DirectGather VG.Proof.AesGcm.AArch64.Gather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph inc32 j0 gctr blockAt blocksAt ghashFrom padLen zeros toBytes)

theorem mediumLengths_ok {W : Addr} {al n : Nat} (s : State) (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, 752⟩] s.wr)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 al) (h26 : s.gpr .x26 = BitVec.ofNat 64 n)
    (hal' : al < 2 ^ 64) (hn : n < 2 ^ 64) :
    WP isa (.block Medium.lengths) s fun s' =>
      Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 720) 16 = Proof.Gcm.lensBlock al n ∧
      Frame [⟨W + BitVec.ofNat 64 720, 16⟩] s.mem s'.mem ∧
      Others [.x9, .x10] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v :=
  Stitch.lengthsAt_ok (offset := 720) s h19 hr h24 h26 hal' hn (by decide) (by decide) (by decide)


open VG.Proof.Gcm.AArch64.Pmull (ext8 ext8_ext8 rev64b_rev64b rev64b_read blockAt_store exec_rev64b exec_ldrq
  exec_eor exec_strq)

/-- Combine the authenticated polynomial with the encrypted initial counter and
write the resulting tag to the output pointer passed on the caller's stack. -/
theorem mediumTag_ok (s : State) (W T : Addr) (g : Spec.Gcm.Block)
    (hw : s.gpr .x19 = W) (hY : s.v .v16 = VRevOp.eval .rev64b (ext8 g g))
    (hmask : InRegions (s.rd ++ s.wr) (W+224#64) 16)
    (hptr : InRegions (s.rd ++ s.wr) (s.sp + 768#64) 8)
    (ht : s.mem.readW (s.sp + 768#64) 64 = T) (hout : InRegions s.wr T 16) :
    WP isa (.block Medium.tagOut) s fun t =>
      Spec.Gcm.blockAt t.mem T = g ^^^ Spec.Gcm.blockAt s.mem (W+224#64) ∧
      Frame [⟨T,16⟩] s.mem t.mem ∧ t.gpr .x19 = W ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  writeTag_ok (maskOff := 224) (argOff := 768) (by decide) (by decide) (by decide) s W T g hw hY hmask hptr ht hout


open VG.Impl.AesGcm.AArch64 (ptr imm)
open VG.Proof.Gcm.AArch64 (hR dR yR nb)
open VG.Spec.Gcm (blockAt blocksAt ghashFrom)

abbrev Hash16Ok := ∀ (s : State), nb s = 16 →
    Covers ([hR s,Proof.Gcm.AArch64.dR s]++[yR s]) (s.rd++s.wr) → Covers [yR s] s.wr → (yR s).Disjoint (Proof.Gcm.AArch64.dR s) →
    WP isa (.block Medium.hash16) s fun t =>
      let y := ghashFrom (VG.Proof.Gcm.AArch64.H₀ s) (VG.Proof.Gcm.AArch64.Y₀ s)
        (blocksAt s.mem (VG.Proof.Gcm.AArch64.dp s) 16)
      t.v .v16 = VRevOp.eval .rev64b (ext8 y y) ∧ t.mem = s.mem ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .x19 = s.gpr .x19

abbrev Hash16WithOk := ∀ (s : State), nb s = 16 →
    Covers ([hR s,Proof.Gcm.AArch64.dR s,⟨s.gpr .x5,128⟩]++[yR s]) (s.rd++s.wr) → Covers [yR s] s.wr → (yR s).Disjoint (Proof.Gcm.AArch64.dR s) →
    Spec.Gcm.Powers8Repr s.mem (s.gpr .x5) (VG.Proof.Gcm.AArch64.H₀ s) →
    WP isa (.block Medium.hash16With) s fun t =>
      let y := ghashFrom (VG.Proof.Gcm.AArch64.H₀ s) (VG.Proof.Gcm.AArch64.Y₀ s)
        (blocksAt s.mem (VG.Proof.Gcm.AArch64.dp s) 16)
      t.v .v16 = VRevOp.eval .rev64b (ext8 y y) ∧ t.mem = s.mem ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .x19 = s.gpr .x19

abbrev MediumCoreOk (cached : Bool) : Prop := if cached then Hash16WithOk else Hash16Ok

theorem mediumHashWith_ok {cached : Bool} (hash : MediumCoreOk cached) (s : State) (W K : Addr) (h19 : s.gpr .x19 = W)
    (h21 : s.gpr .x21 = K) (hw : Covers [⟨W,752⟩] s.wr)
    (hk : Covers [⟨K+240#64,16⟩] (s.rd ++ s.wr)) (hy : blockAt s.mem (W+736#64) = 0)
    (powers : cached = true → ShortPowers s W K Medium.work) :
    WP isa (.block (Medium.hashArgs ++ Medium.hashCore cached)) s fun t =>
      let y := ghashFrom (blockAt s.mem (K+240#64)) 0 (blocksAt s.mem (W+480#64) 16)
      t.v .v16 = VRevOp.eval .rev64b (ext8 y y) ∧ t.mem = s.mem ∧ t.gpr .x19 = W ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [WP.block_append_iff]
  obtain ⟨u,run,k,d,y,n,mem,reg,x5,sp,rd,wr⟩ : ∃ u, runBlock isa Medium.hashArgs s = some u ∧
      u.gpr .x0 = K+240#64 ∧ u.gpr .x2 = W+480#64 ∧ u.gpr .x1 = W+736#64 ∧
      u.gpr .x3 = 16#64 ∧ u.mem = s.mem ∧ u.gpr .x19 = W ∧ u.gpr .x5 = s.gpr .x5 ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr := by
    refine ⟨_,by arun [Medium.hashArgs,Medium.authO,ptr,imm],?_⟩
    simp [gpr_write,h19,h21,mem_write,sp_write,rd_write,wr_write]
  refine WP.of_runBlock ⟨u,run,?_⟩
  have hn : nb u = 16 := by unfold nb; rw [n]; rfl
  have hr : hR u = ⟨K+240#64,16⟩ := congrArg (fun b => Region.mk b 16) k
  have yr : yR u = ⟨W+736#64,16⟩ := congrArg (fun b => Region.mk b 16) y
  have dr : Proof.Gcm.AArch64.dR u = ⟨W+480#64,256⟩ := by
    change Region.mk _ (16*nb u) = _; rw [hn]; exact congrArg (fun b => Region.mk b 256) d
  have yc : Covers [yR u] u.wr := by rw [yr,wr]; exact covers_off hw (by decide) (by decide)
  have dc : Covers [Proof.Gcm.AArch64.dR u] u.wr := by rw [dr,wr]; exact covers_off hw (by decide) (by decide)
  have hc : Covers [hR u] (u.rd++u.wr) := by rwa [hr,rd,wr]
  have sep : (yR u).Disjoint (Proof.Gcm.AArch64.dR u) := by rw [yr,dr]; exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  have folded : WP isa (.block (Medium.hashCore cached)) u fun t =>
      let val := ghashFrom (VG.Proof.Gcm.AArch64.H₀ u) (VG.Proof.Gcm.AArch64.Y₀ u)
        (blocksAt u.mem (VG.Proof.Gcm.AArch64.dp u) 16)
      t.v .v16 = VRevOp.eval .rev64b (ext8 val val) ∧ t.mem = u.mem ∧
      t.sp = u.sp ∧ t.rd = u.rd ∧ t.wr = u.wr ∧ t.gpr .x19 = u.gpr .x19 := by
    cases cached with
    | false => exact hash u hn (Covers.append_left (Covers.cons hc (Covers.right dc)) (Covers.right yc)) yc sep
    | true =>
      have pc : Covers [⟨u.gpr .x5,128⟩] (u.rd++u.wr) := by rw [x5,rd,wr]; exact (powers rfl).read
      have repr : Spec.Gcm.Powers8Repr u.mem (u.gpr .x5) (VG.Proof.Gcm.AArch64.H₀ u) := by
        change Spec.Gcm.Powers8Repr u.mem (u.gpr .x5) (blockAt u.mem (u.gpr .x0))
        rw [mem,x5,k]; exact (powers rfl).repr
      exact hash u hn (Covers.append_left (Covers.cons hc (Covers.cons (Covers.right dc) pc)) (Covers.right yc)) yc sep repr
  refine folded.mono ?_
  rintro t ⟨val,m,rsp,rr,rw',g⟩
  change t.v .v16 = VRevOp.eval .rev64b (ext8 _ _) at val
  simp only [Proof.Gcm.AArch64.H₀,Proof.Gcm.AArch64.hA,Proof.Gcm.AArch64.Y₀,
    Proof.Gcm.AArch64.yp,Proof.Gcm.AArch64.dp,k,d,y,mem,hy] at val
  exact ⟨val,m.trans mem,g.trans reg,rsp.trans sp,rr.trans rd,rw'.trans wr⟩

structure MediumFinishPre (o s : State) (W : Addr) (lead : Nat) : Prop where
  x19 : s.gpr .x19 = W
  x21 : s.gpr .x21 = K o
  x24 : s.gpr .x24 = BitVec.ofNat 64 (AL o)
  x26 : s.gpr .x26 = BitVec.ofNat 64 (L o)
  sp : s.sp = W
  saved : SavedAt s.mem W o
  work : Covers [⟨W,752⟩] s.wr
  key : Covers [⟨K o+240#64,16⟩] (s.rd ++ s.wr)
  ptr : InRegions (s.rd ++ s.wr) (W+768#64) 8
  tag : InRegions s.wr (Tg o) 16
  tagAddr : s.mem.readW (W+768#64) 64 = Tg o
  keyWork : Region.Disjoint ⟨K o+240#64,16⟩ ⟨W,752⟩
  dstWork : (Gather.dR o).Disjoint ⟨W,752⟩
  tagWork : (tgR o).Disjoint ⟨W,752⟩
  dstTag : (Gather.dR o).Disjoint (tgR o)
  shortAad : AL o ≤ 16
  hashKey : blockAt s.mem (K o+240#64) = ctxH o.mem (K o)
  mask : blockAt s.mem (W+224#64) = shortCipher o (shortJ0 o)
  ct : shortCt o s = gctr (shortCipher o) (inc32 (shortJ0 o)) (pt o (Cnt o))
  auth : bytesAt s.mem (W+480#64) 240 = zeros (16*lead) ++ shortAadBytes o ++ zeros (16-AL o) ++
    shortCt o s ++ zeros (padLen (L o))

  zero : blockAt s.mem (W+736#64) = 0

/-- The end of the medium body meets the public gather postcondition and
restores the registers saved at entry, keeping the medium frame allocated. -/
theorem mediumFinishWith_ok {cached : Bool} (hash : MediumCoreOk cached) (o s : State) (W : Addr) (lead : Nat) (p : MediumFinishPre o s W lead)
    (powers : cached = true → ShortPowers s W (K o) Medium.work) :
    WP isa (.block (Medium.finishUsing cached)) s fun t =>
      gatherPost o t ∧ (∀ r ∈ preserved, t.gpr r = o.gpr r) ∧ t.sp = W ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨W,752⟩, tgR o] s.mem t.mem := by
  unfold Medium.finishUsing
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine (mediumLengths_ok s p.x19 p.work p.x24 p.x26 (o.gpr .x5).isLt (stackArg o 1).isLt).mono ?_
  intro l pl
  obtain ⟨lens, lf, regs, lsp, lrd, lwr, _⟩ := pl
  have lw : Covers [⟨W,752⟩] l.wr := lwr ▸ p.work
  have lh : Covers [⟨K o+240#64,16⟩] (l.rd ++ l.wr) := by rw [lrd,lwr]; exact p.key
  have subL : Region.Sub ⟨W+720#64,16⟩ ⟨W,752⟩ := Offset.sub_base _ (by decide)
  have subY : Region.Sub ⟨W+736#64,16⟩ ⟨W,752⟩ := Offset.sub_base _ (by decide)
  have zero : blockAt l.mem (W+736#64) = 0 := (blockAt_frame lf (by
    simpa only [List.mem_singleton,forall_eq] using Offset.disjoint W (d := 736) (n := 16) (e := 720) (k := 16)
      (.inr (by decide)) (by decide) (by decide))).trans p.zero
  refine (mediumHashWith_ok hash l W (K o) ((regs _ (by decide)).trans p.x19) ((regs _ (by decide)).trans p.x21)
    lw lh zero (fun h => (powers h).frame lf subL (p.keyWork.sub_right subL) (regs _ (by decide)) lrd lwr)).mono ?_
  intro h ⟨hash, hm, hx, hsp, hrd, hwr⟩
  have subWork : Frame [⟨W,752⟩] s.mem h.mem := by
    rw [hm]; exact singletonFrame lf (List.mem_singleton_self _) subL
  have ptrRead : h.mem.readW (W+768#64) 64 = Tg o := by
    rw [subWork.readW (r := ⟨W+768#64,8⟩) (Region.contains_self _ _) (by
      simpa only [List.mem_singleton, forall_eq] using Offset.disjoint_base W (d := 768) (n := 8)
        (k := 752) (by decide) (by decide)) (by decide), p.tagAddr]
  have hspW := hsp.trans (lsp.trans p.sp)
  have mask0 : InRegions (h.rd ++ h.wr) (W+224#64) 16 := by
    rw [hrd,hwr,lrd,lwr]
    exact in_left (rd := s.rd) (in_off (d := 224) (n := 16) p.work (by decide) (by decide))
  refine (mediumTag_ok h W (Tg o) _ hx hash mask0 (by rw [hspW,hrd,hwr,lrd,lwr]; exact p.ptr)
    (by rwa [hspW]) (by rw [hwr,lwr]; exact p.tag)).mono ?_
  intro t tt
  obtain ⟨tag, tf, tx, tsp, trd, twr⟩ := tt
  have sfL := p.saved.frame lf (by simpa only [List.mem_singleton, forall_eq] using Offset.disjoint W (d := 128) (n := 88) (e := 720) (k := 16) (.inl (by decide)) (by decide) (by decide))
  have sfH : SavedAt h.mem W o := hm ▸ sfL
  have sf := sfH.frame tf (by simpa only [List.mem_singleton, forall_eq] using p.tagWork.symm.sub_left (Offset.sub_base W (d := 128) (n := 88) (by decide)))
  refine (exit_ok (s₀ := {o with sp := W}) tx (tsp.trans hspW) (Covers.right (by
    rw [twr,hwr,lwr]; exact p.work)) sf (by decide)).mono ?_
  intro z hz
  obtain ⟨abi, zm, _, zrd, zwr⟩ := hz
  have f : Frame [⟨W,752⟩, tgR o] s.mem z.mem := by
    rw [zm]
    exact (singletonFrame subWork (List.mem_cons_self ..) (fun _ => id)).trans
      (singletonFrame tf (by simp) (fun _ => id))
  have zct : shortCt o z = shortCt o s := bytesAt_frame f (by
    intro r hr; rcases List.mem_cons.mp hr with e | e
    · exact e ▸ p.dstWork
    · exact (List.mem_singleton.mp e) ▸ p.dstTag)
    (Nat.le_of_lt (stackArg o 1).isLt)
  refine ⟨gather_post_of_blocks 16 o z l.mem (W+480#64) lead ?_ (zct.trans p.ct) ?_ ?_, abi.1, abi.2,
    zrd.trans (trd.trans (hrd.trans lrd)), zwr.trans (twr.trans (hwr.trans lwr)), f⟩
  · simpa only [Proof.Cmac.bytesAt_length] using p.shortAad
  · change _ = _ ++ shortAadBytes o ++ _ ++ shortCt o z ++ _ ++ _
    rw [zct, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length,
      show (16*16:Nat) = 240+16 from rfl, Proof.Cmac.Stream.bytesAt_append, Offset.add_add, lens,
      bytesAt_frame lf (by simpa only [List.mem_singleton, forall_eq] using Offset.disjoint W (d := 480) (n := 240) (e := 720) (k := 16) (.inl (by decide)) (by decide) (by decide))
        (by decide), p.auth]
  · have hkey : blockAt l.mem (K o+240#64) = ctxH o.mem (K o) :=
      (blockAt_frame lf (by simpa only [List.mem_singleton, forall_eq] using p.keyWork.sub_right subL)).trans p.hashKey
    have hmask : blockAt h.mem (W+224#64) = shortCipher o (shortJ0 o) := by
      rw [hm,blockAt_frame lf (by simpa only [List.mem_singleton,forall_eq] using Offset.disjoint W (d := 224) (n := 16) (e := 720) (k := 16) (.inl (by decide)) (by decide) (by decide)),p.mask]
    rw [zm, Proof.Cmac.bytesAt_blockAt, tag, hkey, hmask]


open VG.Proof.AesGcm.AArch64 (rel_seq rel_taint Eq2 TT)
private def mediumTagPrefix : List Instr :=
  [.ldrq .v0 .x19 224,.vop (.logic .eor .v16 .v16 .v0),
    .ldrSp .x10 (768)]

private theorem mediumTagPtr_ok (s : State) (W : Addr) (w : s.gpr .x19 = W)
    (read : InRegions (s.rd ++ s.wr) (W+224#64) 16)
    (ptr : InRegions (s.rd ++ s.wr) (s.sp+768#64) 8) :
    WP isa (.block mediumTagPrefix) s fun t => t.gpr .x10 = s.mem.readW (s.sp+768#64) 64 ∧
      t.gpr .x19 = W ∧ t.sp = s.sp := by
  unfold mediumTagPrefix
  rw [WP.block_cons_iff]
  refine ⟨_,exec_ldrq (off := 224) (by decide) (by decide) ?_,?_⟩
  · simpa only [gpr_setV,w,BitVec.add_zero,rd_setV,wr_setV] using read
  rw [WP.block_cons_iff]
  refine ⟨_, exec_eor _ _ _ _,?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_ldrSp (off := 768) (by decide) ptr,WP.block_nil ?_⟩
  simp only [gpr_write,ite_true,reduceCtorEq,ite_false,gpr_setV,sp_setV,sp_write,mem_setV,
    BitVec.setWidth_eq,w,and_self]

private abbrev mediumEndPrefix (cached : Bool) := Medium.lengths ++ (Medium.hashArgs ++ Medium.hashCore cached) ++ mediumTagPrefix
private abbrev mediumEndTail := [Instr.strq .v16 .x10 0] ++ Impl.AesGcm.AArch64.restore

private theorem mediumPrefix_ok {cached : Bool} (hash : MediumCoreOk cached) {o s : State} {W : Addr} {i : Nat} (p : MediumFinishPre o s W i) (powers : cached = true → ShortPowers s W (K o) Medium.work) :
    WP isa (.block (mediumEndPrefix cached)) s fun t => t.gpr .x10 = Tg o ∧ t.gpr .x19 = W ∧ t.sp = W := by
  rw [WP.block_append_iff,WP.block_append_iff]
  refine (mediumLengths_ok s p.x19 p.work p.x24 p.x26 (o.gpr .x5).isLt (stackArg o 1).isLt).mono ?_
  intro l pl
  obtain ⟨_, lf, regs, lsp, lrd, lwr, _⟩ := pl
  have lw : Covers [⟨W,752⟩] l.wr := lwr ▸ p.work
  have lh : Covers [⟨K o+240#64,16⟩] (l.rd ++ l.wr) := by rw [lrd,lwr]; exact p.key
  have zero : blockAt l.mem (W+736#64) = 0 := (blockAt_frame lf (by
    simpa only [List.mem_singleton,forall_eq] using Offset.disjoint W (d := 736) (n := 16) (e := 720) (k := 16)
      (.inr (by decide)) (by decide) (by decide))).trans p.zero
  have subL : Region.Sub ⟨W+720#64,16⟩ ⟨W,752⟩ := Offset.sub_base _ (by decide)
  refine (mediumHashWith_ok hash l W (K o) ((regs _ (by decide)).trans p.x19) ((regs _ (by decide)).trans p.x21)
    lw lh zero (fun h => (powers h).frame lf subL (p.keyWork.sub_right subL) (regs _ (by decide)) lrd lwr)).mono ?_
  intro h ⟨_,hm,hx,hsp,hrd,hwr⟩
  have sp := hsp.trans (lsp.trans p.sp)
  refine (mediumTagPtr_ok h W hx (by rw [hrd,hwr,lrd,lwr]; exact in_left (rd := s.rd) (in_off (d := 224) (n := 16) p.work (by decide) (by decide)))
    (by rw [sp,hrd,hwr,lrd,lwr]; exact p.ptr)).mono ?_
  intro t ⟨tp,tx,ts⟩
  refine ⟨?_,tx,ts.trans sp⟩
  rw [tp,sp,hm,lf.readW (r := ⟨W+768#64,8⟩) (Region.contains_self _ _) (by
    simpa only [List.mem_singleton,forall_eq] using (Offset.disjoint W (d := 768) (n := 8) (e := 720) (k := 16)
      (.inr (by decide)) (by decide) (by decide))) (by decide),p.tagAddr]

theorem mediumFinish_ok (hash : Hash16Ok) (o s : State) (W : Addr) (lead : Nat) (p : MediumFinishPre o s W lead) :
    WP isa (.block Medium.finish) s fun t =>
      gatherPost o t ∧ (∀ r ∈ preserved, t.gpr r = o.gpr r) ∧ t.sp = W ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨W,752⟩, tgR o] s.mem t.mem :=
  mediumFinishWith_ok (cached := false) hash o s W lead p (by intro e; cases e)

theorem mediumFinishWith_rel {cached : Bool} (hash : MediumCoreOk cached) {a b s t : State} {W : Addr} {i j : Nat}
    (p : MediumFinishPre a s W i) (q : MediumFinishPre b t W j) (k : K a = K b) (tag : Tg a = Tg b)
    (pc : cached = true → ShortPowers s W (K a) Medium.work) (qc : cached = true → ShortPowers t W (K b) Medium.work)
    (powerEq : cached = true → s.gpr .x5 = t.gpr .x5) :
    RelCT isa (Eq2 s t) (.block (Medium.finishUsing cached)) TT := by
  unfold Medium.finishUsing
  have eq : Medium.lengths ++ (Medium.hashArgs ++ Medium.hashCore cached) ++ Medium.tagOut ++ Impl.AesGcm.AArch64.restore =
      mediumEndPrefix cached ++ mediumEndTail := by simp only [Medium.tagOut,writeTag,mediumEndPrefix,mediumEndTail,mediumTagPrefix,List.append_assoc,List.cons_append,
        List.nil_append,Medium.keyO,Medium.work]
  rw [eq]
  apply RelCT.block_split
  have pre : RelCT isa (Eq2 s t) (.block (mediumEndPrefix cached)) TT := by
    cases cached with
    | false =>
      exact rel_taint [.x19,.x21] (p.sp.trans q.sp.symm)
        (by agree_tac [p.x19,q.x19,p.x21,q.x21,k]) ⟨_,by taint_decide⟩
    | true =>
      have eq5 := powerEq rfl
      exact rel_taint [.x5,.x19,.x21] (p.sp.trans q.sp.symm)
        (by agree_tac [p.x19,q.x19,p.x21,q.x21,k,eq5]) ⟨_,by taint_decide⟩
  refine rel_seq pre (mediumPrefix_ok hash p pc) (mediumPrefix_ok hash q qc) ?_
  intro u v ⟨u10,u19,us⟩ ⟨v10,v19,vs⟩
  exact rel_taint [.x10,.x19] (us.trans vs.symm) (by agree_tac [u10,v10,u19,v19,tag]) ⟨_,by taint_decide⟩

theorem mediumFinish_rel (hash : Hash16Ok) {a b s t : State} {W : Addr} {i j : Nat}
    (p : MediumFinishPre a s W i) (q : MediumFinishPre b t W j) (k : K a = K b) (tag : Tg a = Tg b) :
    RelCT isa (Eq2 s t) (.block Medium.finish) TT :=
  mediumFinishWith_rel (cached := false) hash p q k tag (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)

end VG.Proof.AesGcm.AArch64.DirectGather
