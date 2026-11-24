module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.MediumDirect
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Short
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumBody
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumFinish
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumLayout
import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FinishCT
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumKeys
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Short
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.MediumDirect

/-! Set up the bounded contiguous frame directly under the caller’s stack arguments. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.MediumDirect
open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather
open VG.Impl.AesGcm.AArch64.DirectGather VG.Proof.AesGcm.AArch64.DirectGather
open Short (len)

theorem enter {o : State} (c : Caller o) (hn : len o ≤ 224) :
    WP isa (.block (shortSetupAt Medium.work)) (allocated Medium.work o) fun t =>
      Mid.Header o t (len o) ∧ t.gpr .x4 = Ad o := by
  let a := allocated Medium.work o
  have ha : Mid.LocalMem o a := ⟨Frame.refl _ _,rfl,rfl⟩
  refine (Mid.setupAt_ok (.inl rfl) a hn ha.scratchWr (BoundedArgs.argRead c ha 0 (by decide))
    (by simpa only [len,a,allocated,Compact.base,Mid.size,Medium.work,Nat.mul_zero,Nat.add_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq] using BoundedArgs.argVal ha 0 (by decide))).mono ?_
  intro t ⟨b,k,r,n,al,l,ceil,other,saved,fr,sp,rd,wr⟩
  have m : Mid.LocalMem o t := ⟨fr.sub (fun q hq => by
    obtain rfl := List.mem_singleton.mp hq
    exact ⟨_,List.mem_singleton_self _, Offset.sub_base (Mid.base o) (by decide)⟩),rd,wr⟩
  exact ⟨⟨m,sp,saved,b,k,r,n,by simpa only [a,allocated,AL,BitVec.ofNat_toNat,BitVec.setWidth_eq] using al,
    ceil,l,other _ (by decide),other _ (by decide)⟩,other _ (by decide)⟩

theorem prefix_ok {o : State} (c : Caller o) (hn : len o ≤ 224) (hal : AL o ≤ 16) :
    WP isa (.seq (.block (shortSetupAt Medium.work)) (.seq (.block Medium.zero) (Medium.aadWith true))) (allocated Medium.work o)
      fun t => Mid.Header o t (len o) ∧ Spec.Aes.bytesAt t.mem (Mid.ghBase o) 256 = Mid.aadLayout o (len o) ∧
        Spec.Aes.bytesAt t.mem (Mid.base o+224) 256 = Spec.Gcm.zeros 256 ∧
        Spec.Aes.bytesAt t.mem (Mid.base o+736) 16 = Spec.Gcm.zeros 16 := by
  refine WP.seq ((enter c hn).mono fun a ⟨h,x4⟩ =>
    Mid.fillMedium true hn hal (BoundedArgs.scratchApart Mid.size _ c _ (by simp [externalRegions])) ?_ h x4)
  exact (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans c.read

end VG.Proof.AesGcm.AArch64.Contiguous.MediumDirect

/-! The bounded CTR call holds the caller's two pointers in callee-saved registers.
The fragment reads the original plaintext and writes identical ciphertext to the
destination and the authentication area for either admitted buffer layout. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.MediumDirect
open VG VG.AArch64 VG.AArch64.RegUpd VG.Proof.AesGcm.AArch64.Gather
open VG.Impl.AesGcm.AArch64.DirectGather VG.Proof.AesGcm.AArch64.DirectGather
open VG.Impl.AesGcm.AArch64 (mov)
open VG.Spec.Gcm (blockAt inc32 gctr)
open VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect (cursors)
open Short (len count out)


theorem pointers_ok {W : Addr} {c : Nat} (hc : c ≤ 14) (s : State)
    (hb : s.gpr .x19 = W) (h25 : s.gpr .x25 = BitVec.ofNat 64 (16*c)) :
    WP isa (.block cursors) s fun t =>
      t.gpr .x1 = W + 240 ∧ t.gpr .x2 = s.gpr .x28 ∧
      t.gpr .x3 = W + BitVec.ofNat 64 (Medium.authO+240-16*c) ∧
      (∀ r, r ∉ [.x1,.x2,.x3] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold cursors
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨_,by arun [Medium.keyO],?_⟩
  let t := (s.write .x .x1 (s.gpr .x19 + 240#64)).write .x .x2 (s.gpr .x28)
  obtain ⟨u,run,out,g,m,_,sp,rd,wr⟩ := Stitch.atP_ok (c := c) .x3 (Medium.authO+128) 1 (by decide)
    (by unfold Medium.authO; omega) t (by simpa [t,gpr_write] using hb) (by simpa [t,gpr_write] using h25) (by decide)
  refine WP.of_runBlock ⟨u,by simpa only [t,BitVec.add_zero] using run,?_,?_,out,fun r h => ?_,m,sp,rd,wr⟩
  · simp [g .x1 (by decide),t,gpr_write,hb]
  · simp [g .x2 (by decide),t,gpr_write]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    simp [g r h.2.2,t,gpr_write,h.1,h.2.1]

abbrev buffers (o : State) : Fragment.Buffers :=
  ⟨o.gpr .x6,Mid.base o+240,o.gpr .x7,Mid.base o+BitVec.ofNat 64 (Medium.authO+240-16*count o),len o⟩

structure Ready (o t : State) : Prop extends Mid.LocalMem o t where
  sp : t.sp = Mid.base o
  saved : SavedAt t.mem (Mid.base o) o
  x19 : t.gpr .x19 = Mid.base o
  x21 : t.gpr .x21 = K o
  x24 : t.gpr .x24 = BitVec.ofNat 64 (AL o)
  x26 : t.gpr .x26 = BitVec.ofNat 64 (len o)
  src : t.gpr .x27 = o.gpr .x6
  key : t.gpr .x1 = (buffers o).key
  dst : t.gpr .x2 = (buffers o).dst
  auth : t.gpr .x3 = (buffers o).auth
  mask : blockAt t.mem (Mid.base o+224) = shortCipher o (shortJ0 o)
  stream : ∀ j < len o, t.mem ((buffers o).key+BitVec.ofNat 64 j) =
    Proof.Gcm.ksByte (shortCipher o) (inc32 (shortJ0 o)) j
  input : Spec.Aes.bytesAt t.mem (Mid.ghBase o) 256 = Mid.aadLayout o (len o)
  zero : blockAt t.mem (Mid.base o+736) = 0

theorem pieceLayout {o s : State} (c : Caller o) (hn : len o ≤ 224) (h : Ready o s) :
    Fragment.Layout (buffers o) s := by
  have hc : count o ≤ 14 := by unfold count; omega
  have text : Medium.authO+240-16*count o+len o ≤ Medium.work := by unfold Medium.authO Medium.work count; omega
  have ks : ((buffers o).reg (buffers o).key).Sub (Mid.scratch o) :=
    Offset.sub_base _ (by change 240+len o ≤ 752; omega)
  have aut : ((buffers o).reg (buffers o).auth).Sub (Mid.scratch o) := Offset.sub_base _ text
  have sSrc := BoundedArgs.scratchApart Mid.size _ c (srcR o) (by simp [externalRegions])
  have sDst := BoundedArgs.scratchApart Mid.size _ c (dstR o) (by simp [externalRegions])
  have rd := c.read.trans h.toLocalMem.read
  have wDst : Covers [dstR o] s.wr :=
    (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans
      (c.write.trans (Covers.of_mem fun r hr => by rw [h.wr]; exact List.mem_cons_of_mem _ hr))
  have wAuth := covers_off h.scratchWr text (by decide)
  refine ⟨(stackArg o 0).isLt,?_,?_,?_,?_,sDst.symm.sub_right aut⟩
  · refine Covers.pair ((Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans rd) ?_
    exact Covers.right (covers_off h.scratchWr (by change 240+len o ≤ 752; omega) (by decide))
  · exact Covers.pair wDst wAuth
  · rcases c.sd with dis|eq
    · right; intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact dis
      · exact List.mem_singleton.mp hr ▸ sSrc.symm.sub_right aut
    · exact .inl eq
  · intro r hr; rcases List.mem_cons.mp hr with rfl|hr
    · exact sDst.sub_left ks
    · obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (.inl (by change 240+len o ≤ 480+240-16*count o; omega))
        (by change 240+len o ≤ 2^64; omega) (by change 480+240-16*count o+len o ≤ 2^64; omega)

/-- Recover the caller's plaintext from the pre-state for both layouts. -/
theorem ciphertext {o s t : State} (c : Caller o) (hn : len o ≤ 224) (h : Ready o s)
    (p : Fragment.Cursor (buffers o) s (len o) (len o) t) :
    Spec.Aes.bytesAt t.mem (o.gpr .x7) (len o) = gctr (shortCipher o) (inc32 (shortJ0 o)) (out o).plain ∧
    Spec.Aes.bytesAt t.mem (buffers o).auth (len o) = gctr (shortCipher o) (inc32 (shortJ0 o)) (out o).plain := by
  have orig (j : Nat) (hj : j < len o) : s.mem (Fragment.off (o.gpr .x6) j) = o.mem (Fragment.off (o.gpr .x6) j) := by
    apply h.frame _; intro q hq hit
    obtain rfl := List.mem_singleton.mp hq
    exact (BoundedArgs.scratchApart Mid.size _ c (srcR o) (by simp [externalRegions])) _ hit
      (Offset.contains_base _ (by change j+1 ≤ len o; omega) (by omega))
  have hl : (out o).plain.length = len o := Proof.Cmac.bytesAt_length ..
  rw [Proof.Gcm.gctr_eq]
  constructor <;>
    refine Proof.Gcm.list_ext (by rw [Proof.Gcm.length_xorKs,hl,Proof.Cmac.bytesAt_length]) fun j hj => ?_ <;>
    rw [Proof.Cmac.bytesAt_length] at hj <;>
    rw [Proof.Gcm.getD_bytesAt' _ _ hj,Proof.Gcm.getD_xorKs _ _ _ _ (hl ▸ hj),Nat.zero_add,
      ← h.stream _ (by omega)] <;>
    change _ = ((Spec.Aes.bytesAt o.mem (o.gpr .x6) (len o)).getD j 0 ^^^ _) <;>
    rw [Proof.Gcm.getD_bytesAt' _ _ hj,← orig j hj]
  · exact p.written.dst j hj
  · exact p.written.auth j hj

theorem cursorFrame {o s t : State} (h : Ready o s) (hn : len o ≤ 224)
    (p : Fragment.Cursor (buffers o) s (len o) (len o) t) :
    Frame [Mid.scratch o,dstR o] o.mem t.mem := by
  let slot : Region := ⟨(buffers o).auth,len o⟩
  have f : Frame [dstR o,slot] s.mem t.mem := p.written.frame
  have slotSub : slot.Sub (Mid.scratch o) := Offset.sub_base _ (by
    change 480+240-16*count o+len o ≤ 752; unfold count; omega)
  have small : Frame [Mid.scratch o,dstR o] s.mem t.mem := f.sub fun r hr => by
    rcases List.mem_cons.mp hr with rfl|hr
    · exact ⟨_,by simp,fun _ => id⟩
    · exact ⟨_,List.mem_cons_self ..,List.mem_singleton.mp hr ▸ slotSub⟩
  exact (h.frame.mono (fun r hr => List.mem_cons.mpr (.inl (List.mem_singleton.mp hr)))).trans small

theorem finishPre {o s t : State} (c : Caller o) (hn : len o ≤ 224) (al : AL o ≤ 16)
    (h : Ready o s) (p : Fragment.Cursor (buffers o) s (len o) (len o) t) :
    MediumFinishPreFor o t (Mid.base o) (14-count o) (out o) 760 := by
  let slot : Region := ⟨(buffers o).auth,len o⟩
  have f : Frame [dstR o,slot] s.mem t.mem := p.written.frame
  have ds := BoundedArgs.scratchApart Mid.size _ c (dstR o) (by simp [externalRegions])
  have ts := BoundedArgs.scratchApart Mid.size _ c (tagR o) (by simp [externalRegions])
  have bk := BoundedArgs.scratchApart Mid.size _ c (kR .plain o) (by simp [externalRegions])
  have whole := cursorFrame h hn p
  have apart {r : Region} (a : (Mid.scratch o).Disjoint r) (b : r.Disjoint (dstR o)) :
      ∀ q ∈ [Mid.scratch o,dstR o], r.Disjoint q := by
    intro q hq; rcases List.mem_cons.mp hq with rfl|hq
    · exact a.symm
    · exact List.mem_singleton.mp hq ▸ b
  have args : t.mem.readW (Mid.base o+760#64) 64 = stackArg o 1 := by
    have arg := Mid.scratchArg o 1
    change Mid.base o+760#64 = stackArgAddr o 1 at arg
    rw [arg]
    exact whole.readW (r := callerArgs o) (stackArg_contains o 1 (by decide))
      (apart (BoundedArgs.argsApart Mid.size o).symm c.dstArgs.symm) (by decide)
  have kc : Covers [kR .plain o] (t.rd ++ t.wr) := by
    rw [p.rd,p.wr]
    exact (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans (c.read.trans h.toLocalMem.read)
  have hk := covers_off kc (by decide : 240+16 ≤ 256) (by decide)
  have hashSub : Region.Sub ⟨K o+240#64,16⟩ (kR .plain o) := Offset.sub_base _ (by decide)
  have hc : count o ≤ 14 := by unfold count; omega
  have ct := ciphertext c hn h p
  refine ⟨(p.gpr _ (by decide)).trans h.x19,(p.gpr _ (by decide)).trans h.x21,
    (p.gpr _ (by decide)).trans h.x24,(p.gpr _ (by decide)).trans h.x26,p.sp.trans h.sp,h.saved.frame f ?_,
    p.wr ▸ h.scratchWr,hk,?_,?_,args,bk.symm.sub_left hashSub,ds.symm,ts.symm,c.dt,al,?_,?_,ct.1,?_,?_⟩
  · intro r hr; rcases List.mem_cons.mp hr with rfl|hr
    · exact ds.sub_left (Offset.sub_base _ (by decide))
    · obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (.inl (by change 128+88 ≤ 480+240-16*count o; omega)) (by decide)
        (by change 480+240-16*count o+len o ≤ 2^64; omega)
  · rw [p.rd,p.wr]; exact BoundedArgs.argRead c h.toLocalMem 1 (by decide)
  · rw [p.wr,h.wr]; obtain ⟨r,hr,hc⟩ := c.write _ _ ⟨tagR o,by simp,Region.contains_self _ _⟩
    exact ⟨r,List.mem_cons_of_mem _ hr,hc⟩
  · apply blockAt_frame whole
    exact fun r hr => (apart bk c.kd r hr).sub_left hashSub
  · rw [blockAt_frame f (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact ds.sub_left (Offset.sub_base _ (by decide))
      · obtain rfl := List.mem_singleton.mp hr
        exact Offset.disjoint _ (.inl (by change 224+16 ≤ 480+240-16*count o; omega)) (by decide)
          (by change 480+240-16*count o+len o ≤ 2^64; omega))]
    exact h.mask
  · exact Mid.authFilledFor ds hn al _ (Proof.Cmac.bytesAt_length ..) f h.input (ct.2.trans ct.1.symm)
  · rw [blockAt_frame f (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact ds.sub_left (Offset.sub_base _ (by decide))
      · obtain rfl := List.mem_singleton.mp hr
        exact Offset.disjoint _ (.inr (by change 480+240-16*count o+len o ≤ 736; unfold count; omega)) (by decide)
          (by change 480+240-16*count o+len o ≤ 2^64; omega))]
    exact h.zero

theorem piece_ok {o s : State} (c : Caller o) (hn : len o ≤ 224) (h : Ready o s) :
    WP isa (shortPieceWith [mov .x0 .x27,mov .x12 .x26]) s (Fragment.Cursor (buffers o) s (len o) (len o)) :=
  Fragment.directPiece_ok (pieceLayout c hn h) h.src h.x26 h.key h.dst h.auth

theorem piece_rel {a b u v : State} (hu : Ready a u) (hv : Ready b v)
    (w : Mid.base a = Mid.base b) (n : len a = len b)
    (q6 : a.gpr .x6 = b.gpr .x6) (q7 : a.gpr .x7 = b.gpr .x7) :
    RelCT isa (Eq2 u v) (shortPieceWith [mov .x0 .x27,mov .x12 .x26]) TT := by
  have ce : count a = count b := by simp only [Short.count,n]
  exact rel_taint [.x1,.x2,.x3,.x27,.x26] (hu.sp.trans (w.trans hv.sp.symm))
    (by agree_tac [hu.key,hv.key,hu.dst,hv.dst,hu.auth,hv.auth,hu.src,hv.src,hu.x26,hv.x26,buffers,q6,q7,ce,w,n])
    ⟨_,by taint_decide⟩

end VG.Proof.AesGcm.AArch64.Contiguous.MediumDirect

/-! Relate the CTR call's output to the contiguous record’s stream and tag mask. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.MediumDirect
open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather
open VG.Impl.AesGcm.AArch64.DirectGather VG.Proof.AesGcm.AArch64.DirectGather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt inc32 zeros)
open Short (len count)
open VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect (cursors)

theorem preKeys {o s : State} (c : Caller o) (iv : NL o=12) (hn : len o ≤ 224)
    (h : Mid.Header o s (len o)) (zero : bytesAt s.mem (Mid.base o+224) 256 = zeros 256) :
    MediumKeysPre (Mid.base o) (K o) (o.gpr .x1).toNat (count o) s :=
  Mid.preKeysAt iv hn h zero c.rounds (by have := c.room; omega)
    (((Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans c.read).trans h.toLocalMem.read)
    (((Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans c.read).trans h.toLocalMem.read)
    (BoundedArgs.scratchApart Mid.size _ c _ (by simp [externalRegions]))

theorem ready {o s : State} (v : GcmImpl) (v0 : v.ctr.scratch = 0) (c : Caller o)
    (iv : NL o = 12) (hn : len o ≤ 224) (h : Mid.Header o s (len o))
    (input : bytesAt s.mem (Mid.ghBase o) 256 = Mid.aadLayout o (len o))
    (zero : bytesAt s.mem (Mid.base o+224) 256 = zeros 256)
    (acc : bytesAt s.mem (Mid.base o+736) 16 = zeros 16) :
    WP isa (.seq (Medium.keys v.callees) (.block cursors)) s (Ready o) := by
  have hc : count o ≤ 14 := by unfold Short.count; omega
  refine WP.seq ((mediumKeys_ok v v0 (preKeys c iv hn h zero)).mono ?_)
  intro k hk
  have localK : Mid.LocalMem o k := ⟨h.frame.trans (hk.frame.sub (by
    intro r hr; refine ⟨Mid.scratch o,List.mem_singleton_self _,?_⟩
    rcases List.mem_cons.mp hr with rfl|hr
    · exact Region.sub_prefix (by decide)
    · obtain rfl := List.mem_singleton.mp hr; exact Offset.sub_base _ (by decide))),
    hk.rd.trans h.rd,hk.wr.trans h.wr⟩
  have sp := hk.sp.trans h.sp
  have k19 := (hk.kept .x19 (by decide)).trans h.x19
  have k25 := (hk.kept .x25 (by decide)).trans h.x25
  have saved := h.saved.frame hk.frame (by
    intro q hq; rcases List.mem_cons.mp hq with rfl|hq
    · exact Offset.disjoint_base _ (by decide) (by decide)
    · obtain rfl := List.mem_singleton.mp hq; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  refine (pointers_ok hc k k19 k25).mono ?_
  intro t ⟨key,dst,auth,g,m,ts,tr,tw⟩
  have reg (r : Reg) (a : r ∉ [.x1,.x2,.x3]) (b : r ∈ medKept) := (g r a).trans (hk.kept r b)
  have kc := Mid.keyCipherAt c.rounds (BoundedArgs.scratchApart Mid.size _ c _ (by simp [externalRegions])) h.toLocalMem
  have ns := Mid.keyNonceAt (BoundedArgs.scratchApart Mid.size _ c _ (by simp [externalRegions])) iv h
  refine ⟨⟨m ▸ localK.frame,tr.trans localK.rd,tw.trans localK.wr⟩,ts.trans sp,m ▸ saved,
    (g _ (by decide)).trans k19,(reg _ (by decide) (by decide)).trans h.x21,
    (reg _ (by decide) (by decide)).trans h.x24,(reg _ (by decide) (by decide)).trans h.x26,
    (g _ (by decide)).trans (hk.desc.trans h.x6),key,dst.trans (hk.count.trans h.x7),auth,
    by simpa only [m,kc,ns,medD,show (224:Addr)=224#64 by decide] using hk.mask,?_,?_,?_⟩
  · intro j hj
    rw [m]; simpa only [kc,ns] using hk.stream j (by unfold Short.count; omega)
  · rw [m,bytesAt_frame hk.frame (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · obtain rfl := List.mem_singleton.mp hr; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)) (by decide), input]
  · rw [m,blockAt,bytesAt_frame hk.frame (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · obtain rfl := List.mem_singleton.mp hr; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)) (by decide),acc,Proof.Gcm.ofBytes_zeros16]

end VG.Proof.AesGcm.AArch64.Contiguous.MediumDirect

/-! Seal a bounded record through the original input and output pointers and return its tag. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.MediumDirect
open VG VG.AArch64 VG.AArch64.RegUpd VG.Proof.AesGcm.AArch64.Gather
open VG.Impl.AesGcm.AArch64.DirectGather VG.Proof.AesGcm.AArch64.DirectGather
open VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect (frame)
open Short (len count out)

/-- Load the publicly addressed table after the fragment has written the destination.
The caller proved it disjoint from both the ciphertext and this frame. -/
theorem loadPowers {o s t : State} (c : Caller o) (key : Prepared.Powers o)
    (hn : len o ≤ 224) (al : AL o ≤ 16) (h : Ready o s)
    (cur : Fragment.Cursor (buffers o) s (len o) (len o) t) :
    WP isa (.block [.ldrSp .x5 (Medium.work+16)]) t fun u =>
      MediumFinishPreFor o u (Mid.base o) (14-count o) (out o) 760 ∧ ShortPowers u (Mid.base o) (K o) Medium.work ∧
      u.gpr .x5 = stackArg o 2 := by
  have p := finishPre c hn al h cur
  have mem := cursorFrame h hn cur
  have slot : Mid.base o + 768#64 = stackArgAddr o 2 := Mid.scratchArg o 2
  have ptr : InRegions (t.rd ++ t.wr) (t.sp+768#64) 8 := by
    rw [p.sp,cur.rd,cur.wr]
    exact BoundedArgs.argRead c h.toLocalMem 2 (by decide)
  have addr : t.mem.readW (t.sp+768#64) 64 = stackArg o 2 := by
    rw [p.sp,slot]
    exact mem.readW (r := callerArgs o) (stackArg_contains o 2 (by decide)) (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact BoundedArgs.argsApart Mid.size o
      · exact List.mem_singleton.mp hr ▸ c.dstArgs.symm) (by decide)
  have sep : (Prepared.powerR o).Disjoint (Mid.scratch o) :=
    key.stack.sub_right (Offset.sub_below _ (by decide) (by decide))
  rw [WP.block_cons_iff]
  refine ⟨_,exec_ldrSp (off := 768) (by decide) ptr,WP.block_nil ?_⟩
  have g : (t.write .x .x5 (t.mem.readW (t.sp+768#64) 64)).gpr .x5 = stackArg o 2 := by
    simpa only [gpr_write,ite_true,BitVec.setWidth_eq] using addr
  refine ⟨{p with}, ⟨?_,?_,?_⟩,g⟩
  · rw [g,rd_write,wr_write,cur.rd,cur.wr]
    exact key.read.trans h.toLocalMem.read
  · rw [g]; exact sep
  · rw [g,mem_write,p.hashKey]
    exact Proof.AesGcm.powers8Repr_congr (fun i hi => mem.bytes (R := Prepared.powerR o)
      (by intro r hr; rcases List.mem_cons.mp hr with rfl|hr
          · exact sep
          · exact List.mem_singleton.mp hr ▸ key.dst)
      (by change (128:Nat) ≤ 2^64; decide) hi) key.repr

theorem frame_ok (v : GcmImpl) (z : v.ctr.scratch=0) (hash : Hash16WithOk) {o : State}
    (c : Caller o) (pw : Prepared.Powers o) (iv : NL o=12) (al : AL o≤16) (hn : len o≤224)
    (keep : (frame v.callees).allInstrs keepsV = true) :
    WP isa (frame v.callees) o fun t => abiPreserved o t ∧ result o t := by
  apply WP.withPreservedV (hc := keep)
  apply WP.alloc (by decide) (by change 752 ≤ o.sp.toNat; have := c.room; omega)
  have front := prefix_ok c hn al
  refine WP.seq ((WP.seq_iff.mp front).mono fun _ w => WP.seq ((WP.seq_iff.mp w).mono fun _ w => WP.seq (w.mono ?_)))
  intro u ⟨header,input,zero,acc⟩
  refine WP.seq ((WP.seq_iff.mp (ready v z c iv hn header input zero acc)).mono fun _ w => WP.seq (w.mono ?_))
  intro s h
  refine WP.seq ((piece_ok c hn h).mono ?_)
  intro t cursor
  refine WP.seq ((loadPowers c pw hn al h cursor).mono ?_)
  intro u ⟨p,pc,_⟩
  refine (mediumFinishWith_ok (cached := true) (.inl rfl) hash o u (Mid.base o) _ p
    (fun _ => pc) (fun _ => ⟨rfl,hn⟩)).mono ?_
  intro t ⟨post,g,sp,_,_,_⟩ _ _ fr
  exact ⟨⟨g,by change t.sp+BitVec.ofNat 64 Medium.work = o.sp; rw [sp]; exact BitVec.sub_add_cancel _ _⟩,
    result_frame c (by decide) post fr⟩

end VG.Proof.AesGcm.AArch64.Contiguous.MediumDirect

/-! Every branch and address of the bounded contiguous record depends only
on the public byte counts, round count, pointers and stack slots. -/

public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.MediumDirect

open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather
open VG.Impl.AesGcm.AArch64.Contiguous VG.Impl.AesGcm.AArch64.DirectGather
open VG.Proof.AesGcm.AArch64.DirectGather
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)

open Short (len count)
open VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect (body frame cursors)

theorem frame_rel (v : GcmImpl) (z : v.ctr.scratch = 0) (hash : Hash16WithOk) {a b : State} (ca : Caller a) (cb : Caller b)
    (ka : Prepared.Powers a) (kb : Prepared.Powers b)
    (ai : NL a = 12) (bi : NL b = 12) (aa : AL a ≤ 16) (ba : AL b ≤ 16)
    (an : len a ≤ 224) (bn : len b ≤ 224) (pub : onePub 3 a b) :
    RelCT isa (Eq2 a b) (frame v.callees) TT := by
  apply RelCT.alloc (R := TT)
  suffices body : RelCT isa (Eq2 (allocated Medium.work a) (allocated Medium.work b)) (body v.callees) TT from
    body.mono (by rintro x y ⟨_,_,⟨rfl,rfl⟩,rfl,rfl⟩; exact ⟨rfl,rfl⟩) (fun _ _ h => h)
  obtain ⟨q0,q1,q2,_,q4,q5,q6,q7,qsp,stk⟩ := pub
  have w : Mid.base a = Mid.base b := by simp only [Mid.base,qsp]
  have n : len a = len b := congrArg BitVec.toNat (stk 0 (by decide))
  have ce : count a = count b := by rw [Short.count,Short.count,n]
  have al : AL a = AL b := congrArg BitVec.toNat q5
  have preRel : RelCT isa (Eq2 (allocated Medium.work a) (allocated Medium.work b))
      (.seq (.block (shortSetupAt Medium.work)) (.seq (.block Medium.zero) (Medium.aadWith true))) TT := by
    refine rel_seq (rel_taint [] w (by agree_tac []) ⟨_,by taint_decide⟩) (enter ca an) (enter cb bn) ?_
    intro u v ⟨p,p4⟩ ⟨q,q4'⟩
    exact rel_taint [.x4,.x19,.x24,.x25] (p.sp.trans (w.trans q.sp.symm))
      (by agree_tac [p4,q4',Ad,q4,p.x19,q.x19,p.x24,q.x24,p.x25,q.x25,al,w,n]) ⟨_,by taint_decide⟩
  unfold Impl.AesGcm.AArch64.Contiguous.MediumDirect.body
  apply VG.RelCT.assoc
  apply VG.RelCT.assoc
  refine rel_seq (Fast.RelCT.assoc' preRel) (VG.WP.assoc' (prefix_ok ca an aa))
    (VG.WP.assoc' (prefix_ok cb bn ba)) ?_
  intro e f ⟨p,pin,pz,pa⟩ ⟨q,qin,qz,qa⟩
  have pk := preKeys ca ai an p pz
  have qk := preKeys cb bi bn q qz
  have ps := p.sp.trans (w.trans q.sp.symm)
  have key : K a=K b := q0
  have same : MediumKeysPre (Mid.base a) (K a) (a.gpr .x1).toNat (count a) f := by
    simpa only [w,key,q1,ce] using qk
  have kr := mediumKeys_rel v z pk same ps (p.x23.trans (q2.trans q.x23.symm))
  have kp : RelCT isa (Eq2 e f) (.seq (Medium.keys v.callees) (.block cursors)) TT := by
    refine rel_seq kr (mediumKeys_ok v z pk) (mediumKeys_ok v z qk) ?_
    intro _ _ ha hb
    exact rel_taint [] (ha.sp.trans (ps.trans hb.sp.symm)) (by agree_tac []) ⟨_,by taint_decide⟩
  apply VG.RelCT.assoc
  refine rel_seq kp (ready v z ca ai an p pin pz pa) (ready v z cb bi bn q qin qz qa) ?_
  intro u t hu ht
  refine rel_seq (piece_rel hu ht w n q6 q7) (piece_ok ca an hu) (piece_ok cb bn ht) ?_
  intro x y hx hy
  have xs := hx.sp.trans hu.sp
  have ys := hy.sp.trans ht.sp
  refine rel_seq (rel_taint [] (xs.trans (w.trans ys.symm)) (by agree_tac []) ⟨_,by taint_decide⟩)
    (loadPowers ca ka an aa hu hx) (loadPowers cb kb bn ba ht hy) ?_
  intro j k ⟨p,pc,p5⟩ ⟨q,qc,q5'⟩
  exact mediumFinishWith_rel (cached := true) (d := Short.out a) (e := Short.out b) (.inl rfl) hash p (w ▸ q) q0 (stk 1 (by decide))
    (fun _ => pc) (fun _ => w ▸ qc) (fun _ => p5.trans ((stk 2 (by decide)).trans q5'.symm))
    (fun _ => ⟨rfl,an⟩) (fun _ => ⟨rfl,bn⟩) (fun _ => n) (fun _ => al)

end VG.Proof.AesGcm.AArch64.Contiguous.MediumDirect
