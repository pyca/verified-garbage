module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Bounded
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.General
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The short contiguous record takes both pointers directly from the caller.
The stack arguments stay readable when encryption writes through the destination. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Short

open VG VG.AArch64 VG.AArch64.RegUpd VG.Proof.AesGcm.AArch64.Gather
open VG.Impl.AesGcm.AArch64.Contiguous VG.Impl.AesGcm.AArch64.DirectGather
open VG.Proof.AesGcm.AArch64.DirectGather

abbrev len (s : State) := (stackArg s 0).toNat
abbrev count (s : State) := (len s + 15)/16
abbrev layout (s : State) :=
  Spec.Gcm.zeros (16*(6-count s)) ++ aadBytes s ++ Spec.Gcm.zeros (16-AL s) ++
  Spec.Gcm.zeros (16*count s) ++ Spec.Gcm.zeros 16

theorem scratchApart (o : State) (c : Caller o) (r : Region) (hr : r ∈ externalRegions o) :
    (scratch o).Disjoint r :=
  (c.stack r hr).sub_left (Offset.sub_below _ (by decide) (by decide))

theorem argsApart (o : State) : (callerArgs o).Disjoint (scratch o) := by
  simpa only [callerArgs,stackArgAddr,scratch,base,shortWork,Nat.mul_zero,BitVec.add_zero] using
    Offset.base_disjoint_below o.sp (by decide : 368+24 ≤ 2^64)

theorem argRead {o t : State} (c : Caller o) (m : LocalMem o t) (i : Nat) (hi : i < 3) :
    InRegions (t.rd ++ t.wr) (base o + BitVec.ofNat 64 (shortWork+8*i)) 8 := by
  rw [scratchArg]
  exact m.read _ _ (c.read _ _ ⟨callerArgs o,by simp,stackArg_contains o i hi⟩)

theorem argVal {o t : State} (m : LocalMem o t) (i : Nat) (hi : i < 3) :
    t.mem.readW (base o + BitVec.ofNat 64 (shortWork+8*i)) 64 = stackArg o i := by
  rw [scratchArg]
  exact m.frame.read (stackArg_contains o i hi)
    (by simpa only [List.mem_singleton,forall_eq] using argsApart o) (by decide)

theorem enter {o : State} (c : Caller o) (hn : len o ≤ 96) :
    WP isa (.block (shortSetupAt shortWork)) (allocated shortWork o) fun t =>
      Header o t (len o) ∧ t.gpr .x4 = Ad o := by
  let a := allocated shortWork o
  have ha : LocalMem o a := ⟨Frame.refl _ _,rfl,rfl⟩
  refine (shortSetupAt_ok (.inl rfl) a hn ha.scratchWr (argRead c ha 0 (by decide))
    (by simpa only [len,a,allocated,base,shortWork,Nat.mul_zero,Nat.add_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq] using argVal ha 0 (by decide))).mono ?_
  intro t ⟨b,k,r,n,al,l,ceil,other,saved,fr,sp,rd,wr⟩
  have m : LocalMem o t := ⟨fr.sub (fun q hq => by
    obtain rfl := List.mem_singleton.mp hq
    exact ⟨_,List.mem_singleton_self _, Offset.sub_base (base o) (by decide)⟩),rd,wr⟩
  exact ⟨⟨m,sp,saved,b,k,r,n,by simpa only [a,allocated,AL,BitVec.ofNat_toNat,BitVec.setWidth_eq] using al,
    ceil,l,other _ (by decide),other _ (by decide)⟩,other _ (by decide)⟩

theorem prefix_ok {o : State} (c : Caller o) (hn : len o ≤ 96) (hal : AL o ≤ 16) :
    WP isa (.seq (.block (shortSetupAt shortWork)) (.seq (.block shortZero) shortAad)) (allocated shortWork o)
      fun t => Header o t (len o) ∧ Spec.Aes.bytesAt t.mem (ghBase o) 128 = layout o := by
  refine WP.seq ((enter c hn).mono fun a ⟨h,x4⟩ =>
    fillShort hn hal (scratchApart _ c _ (by simp [externalRegions])) ?_ h x4)
  exact (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans c.read

theorem pointers_ok {W : Addr} {c : Nat} (hc : c ≤ 6) (s : State)
    (hb : s.gpr .x19 = W) (h25 : s.gpr .x25 = BitVec.ofNat 64 (16*c)) :
    WP isa (.block directPointers) s fun t =>
      t.gpr .x1 = W + 16 ∧ t.gpr .x2 = s.gpr .x7 ∧
      t.gpr .x3 = W + BitVec.ofNat 64 (authO+112-16*c) ∧
      (∀ r, r ∉ [.x1,.x2,.x3] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold directPointers
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨_,by arun [streamO],?_⟩
  let t := (s.write .x .x1 (s.gpr .x19 + 16#64)).write .x .x2 (s.gpr .x7)
  obtain ⟨u,run,out,g,m,_,sp,rd,wr⟩ := Stitch.atP_ok (c := c) .x3 authO 1 (by decide)
    (by unfold authO; omega) t (by simpa [t,gpr_write] using hb) (by simpa [t,gpr_write] using h25) (by decide)
  refine WP.of_runBlock ⟨u,by simpa only [t,BitVec.add_zero] using run,?_,?_,out,fun r h => ?_,m,sp,rd,wr⟩
  · simp [g .x1 (by decide),t,gpr_write,hb]
  · simp [g .x2 (by decide),t,gpr_write]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    simp [g r h.2.2,t,gpr_write,h.1,h.2.1]

abbrev buffers (o : State) : Fragment.Buffers :=
  ⟨o.gpr .x6,base o+16,o.gpr .x7,base o+BitVec.ofNat 64 (authO+112-16*count o),len o⟩

open VG.Spec.Gcm (blockAt inc32 gctr)

structure Ready (o t : State) : Prop extends Header o t (len o) where
  key : t.gpr .x1 = (buffers o).key
  dst : t.gpr .x2 = (buffers o).dst
  auth : t.gpr .x3 = (buffers o).auth
  mask : blockAt t.mem (base o) = shortCipher o (shortJ0 o)
  stream : ∀ j < 96, t.mem ((buffers o).key+BitVec.ofNat 64 j) =
    Proof.Gcm.ksByte (shortCipher o) (inc32 (shortJ0 o)) j
  input : Spec.Aes.bytesAt t.mem (ghBase o) 128 = layout o

theorem ready {o s : State} (c : Caller o) (iv : NL o = 12) (hn : len o ≤ 96)
    (h : Header o s (len o)) (input : Spec.Aes.bytesAt s.mem (ghBase o) 128 = layout o) :
    WP isa (.seq (Impl.Gcm.AArch64.Stitch.byRounds (shortKeys streamO)) (.block directPointers)) s (Ready o) := by
  have hc : count o ≤ 6 := by unfold count; omega
  refine WP.seq ((shortKeysPhaseFor o s c.rounds ?_ ?_ (scratchApart _ c _ (by simp [externalRegions]))
    (scratchApart _ c _ (by simp [externalRegions])) h.toLocalMem iv h.x19 h.x21 h.x22 h.x23).mono ?_)
  · exact (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans c.read
  · exact (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans c.read
  intro k hk
  have sp := hk.sp.trans h.sp
  have k19 := (hk.gpr .x19 (by decide)).trans h.x19
  have k25 := (hk.gpr .x25 (by decide)).trans h.x25
  refine (pointers_ok hc k k19 k25).mono ?_
  intro t ⟨key,dst,auth,g,m,ts,tr,tw⟩
  have reg (r : Reg) (a : r ∉ [.x1,.x2,.x3]) (b : r ∉ [.x9,.x10,.x12,.x13,.x14]) :=
    (g r a).trans (hk.gpr r b)
  have header : Header o t (len o) := ⟨⟨m ▸ hk.mem.frame,tr.trans hk.mem.rd,tw.trans hk.mem.wr⟩,ts.trans sp,
    m ▸ hk.saved h.saved,(g _ (by decide)).trans k19,
    (reg _ (by decide) (by decide)).trans h.x21,(reg _ (by decide) (by decide)).trans h.x22,
    (reg _ (by decide) (by decide)).trans h.x23,(reg _ (by decide) (by decide)).trans h.x24,
    (g _ (by decide)).trans k25,(reg _ (by decide) (by decide)).trans h.x26,
    (reg _ (by decide) (by decide)).trans h.x6,(reg _ (by decide) (by decide)).trans h.x7⟩
  refine ⟨header,key,dst.trans ((hk.gpr .x7 (by decide)).trans h.x7),auth,m ▸ hk.mask,m ▸ hk.stream,?_⟩
  rw [m,bytesAt_frame hk.frame (by simpa only [List.mem_singleton,forall_eq,ghBase,authO] using
    (Offset.disjoint_base (base o) (d := 224) (n := 128) (k := 112) (by decide) (by decide))) (by decide),input]

theorem pieceLayout {o s : State} (c : Caller o) (hn : len o ≤ 96) (h : Ready o s) :
    Fragment.Layout (buffers o) s := by
  have hc : count o ≤ 6 := by unfold count; omega
  have text : authO+112-16*count o+len o ≤ shortWork := by unfold authO shortWork count; omega
  have ks : ((buffers o).reg (buffers o).key).Sub (scratch o) :=
    Offset.sub_base _ (by change 16+len o ≤ 368; omega)
  have aut : ((buffers o).reg (buffers o).auth).Sub (scratch o) := Offset.sub_base _ text
  have sSrc := scratchApart _ c (srcR o) (by simp [externalRegions])
  have sDst := scratchApart _ c (dstR o) (by simp [externalRegions])
  have rd := c.read.trans h.toLocalMem.read
  have wDst : Covers [dstR o] s.wr :=
    (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans
      (c.write.trans (Covers.of_mem fun r hr => by rw [h.wr]; exact List.mem_cons_of_mem _ hr))
  have wAuth := covers_off h.scratchWr text (by decide)
  refine ⟨(stackArg o 0).isLt,?_,?_,?_,?_,sDst.symm.sub_right aut⟩
  · refine Covers.pair ((Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans rd) ?_
    exact Covers.right (covers_off h.scratchWr (by change 16+len o ≤ 368; omega) (by decide))
  · exact Covers.pair wDst wAuth
  · rcases c.sd with dis|eq
    · right; intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact dis
      · exact List.mem_singleton.mp hr ▸ sSrc.symm.sub_right aut
    · exact .inl eq
  · intro r hr; rcases List.mem_cons.mp hr with rfl|hr
    · exact sDst.sub_left ks
    · obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (.inl (by change 16+len o ≤ 224+112-16*count o; omega))
        (by change 16+len o ≤ 2^64; omega) (by change 224+112-16*count o+len o ≤ 2^64; omega)

abbrev out (o : State) : ShortOutput :=
  ⟨o.gpr .x7,stackArg o 0,stackArg o 1,Spec.Aes.bytesAt o.mem (o.gpr .x6) (len o)⟩

/-- Recover the caller's plaintext from the pre-state for both layouts. -/
theorem ciphertext {o s t : State} (c : Caller o) (hn : len o ≤ 96) (h : Ready o s)
    (p : Fragment.Cursor (buffers o) s (len o) (len o) t) :
    Spec.Aes.bytesAt t.mem (o.gpr .x7) (len o) = gctr (shortCipher o) (inc32 (shortJ0 o)) (out o).plain ∧
    Spec.Aes.bytesAt t.mem (buffers o).auth (len o) = gctr (shortCipher o) (inc32 (shortJ0 o)) (out o).plain := by
  have orig (j : Nat) (hj : j < len o) : s.mem (Fragment.off (o.gpr .x6) j) = o.mem (Fragment.off (o.gpr .x6) j) := by
    apply h.frame _; intro q hq hit
    obtain rfl := List.mem_singleton.mp hq
    exact (scratchApart _ c (srcR o) (by simp [externalRegions])) _ hit
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

theorem cursorFrame {o s t : State} (h : Ready o s) (hn : len o ≤ 96)
    (p : Fragment.Cursor (buffers o) s (len o) (len o) t) :
    Frame [scratch o,dstR o] o.mem t.mem := by
  let slot : Region := ⟨(buffers o).auth,len o⟩
  have f : Frame [dstR o,slot] s.mem t.mem := p.written.frame
  have slotSub : slot.Sub (scratch o) := Offset.sub_base _ (by
    change 224+112-16*count o+len o ≤ 368; unfold count; omega)
  have small : Frame [scratch o,dstR o] s.mem t.mem := f.sub fun r hr => by
    rcases List.mem_cons.mp hr with rfl|hr
    · exact ⟨_,by simp,fun _ => id⟩
    · exact ⟨_,List.mem_cons_self ..,List.mem_singleton.mp hr ▸ slotSub⟩
  exact (h.frame.mono (fun r hr => List.mem_cons.mpr (.inl (List.mem_singleton.mp hr)))).trans small

theorem finishPre {o s t : State} (c : Caller o) (hn : len o ≤ 96) (al : AL o ≤ 16)
    (h : Ready o s) (p : Fragment.Cursor (buffers o) s (len o) (len o) t) :
    ShortFinishPreFor o t (base o) (6-count o) (out o) 376 := by
  let slot : Region := ⟨(buffers o).auth,len o⟩
  have f : Frame [dstR o,slot] s.mem t.mem := p.written.frame
  have ds := scratchApart _ c (dstR o) (by simp [externalRegions])
  have ts := scratchApart _ c (tagR o) (by simp [externalRegions])
  have bk := scratchApart _ c (kR .plain o) (by simp [externalRegions])
  have whole := cursorFrame h hn p
  have apart {r : Region} (a : (scratch o).Disjoint r) (b : r.Disjoint (dstR o)) :
      ∀ q ∈ [scratch o,dstR o], r.Disjoint q := by
    intro q hq; rcases List.mem_cons.mp hq with rfl|hq
    · exact a.symm
    · exact List.mem_singleton.mp hq ▸ b
  have args : t.mem.readW (base o+376#64) 64 = stackArg o 1 := by
    have arg := scratchArg o 1
    change base o+376#64 = stackArgAddr o 1 at arg
    rw [arg]
    exact whole.readW (r := callerArgs o) (stackArg_contains o 1 (by decide))
      (apart (argsApart o).symm c.dstArgs.symm) (by decide)
  have kc : Covers [kR .plain o] (t.rd ++ t.wr) := by
    rw [p.rd,p.wr]
    exact (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans (c.read.trans h.toLocalMem.read)
  have hk := covers_off kc (by decide : 240+16 ≤ 256) (by decide)
  have hashSub : Region.Sub ⟨K o+240#64,16⟩ (kR .plain o) := Offset.sub_base _ (by decide)
  have hc : count o ≤ 6 := by unfold count; omega
  have ct := ciphertext c hn h p
  refine ⟨(p.gpr _ (by decide)).trans h.x19,(p.gpr _ (by decide)).trans h.x21,
    (p.gpr _ (by decide)).trans h.x24,(p.gpr _ (by decide)).trans h.x26,p.sp.trans h.sp,h.saved.frame f ?_,
    p.wr ▸ h.scratchWr,hk,?_,?_,args,bk.symm.sub_left hashSub,ds.symm,ts.symm,c.dt,al,?_,?_,ct.1,?_⟩
  · intro r hr; rcases List.mem_cons.mp hr with rfl|hr
    · exact ds.sub_left (Offset.sub_base _ (by decide))
    · obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (.inl (by change 128+88 ≤ 224+112-16*count o; omega)) (by decide)
        (by change 224+112-16*count o+len o ≤ 2^64; omega)
  · rw [p.rd,p.wr]; exact argRead c h.toLocalMem 1 (by decide)
  · rw [p.wr,h.wr]; obtain ⟨r,hr,hc⟩ := c.write _ _ ⟨tagR o,by simp,Region.contains_self _ _⟩
    exact ⟨r,List.mem_cons_of_mem _ hr,hc⟩
  · apply blockAt_frame whole
    exact fun r hr => (apart bk c.kd r hr).sub_left hashSub
  · rw [blockAt_frame f (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact ds.sub_left (by simpa using (Offset.sub_base (base o) (d := 0) (n := 16) (k := shortWork) (by decide)))
      · obtain rfl := List.mem_singleton.mp hr
        exact Offset.base_disjoint (base o) (by change 16 ≤ 224+112-16*count o; omega)
          (by change 224+112-16*count o+len o ≤ 2^64; omega)),h.mask]
  · exact authFilledFor ds hn al _ (Proof.Cmac.bytesAt_length ..) f h.input (ct.2.trans ct.1.symm)

/-- Load the publicly addressed table after the fragment has written the destination.
The caller proved it disjoint from both the ciphertext and this frame. -/
theorem loadPowers {o s t : State} (c : Caller o) (key : Prepared.Powers o)
    (hn : len o ≤ 96) (al : AL o ≤ 16) (h : Ready o s)
    (cur : Fragment.Cursor (buffers o) s (len o) (len o) t) :
    WP isa (.block [.ldrSp .x5 (shortWork+16)]) t fun u =>
      ShortFinishPreFor o u (base o) (6-count o) (out o) 376 ∧ ShortPowers u (base o) (K o) ∧
      u.gpr .x5 = stackArg o 2 := by
  have p := finishPre c hn al h cur
  have mem := cursorFrame h hn cur
  have slot : base o + 384#64 = stackArgAddr o 2 := scratchArg o 2
  have ptr : InRegions (t.rd ++ t.wr) (t.sp+384#64) 8 := by
    rw [p.sp,cur.rd,cur.wr]
    exact argRead c h.toLocalMem 2 (by decide)
  have addr : t.mem.readW (t.sp+384#64) 64 = stackArg o 2 := by
    rw [p.sp,slot]
    exact mem.readW (r := callerArgs o) (stackArg_contains o 2 (by decide)) (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact argsApart o
      · exact List.mem_singleton.mp hr ▸ c.dstArgs.symm) (by decide)
  have sep : (Prepared.powerR o).Disjoint (scratch o) :=
    key.stack.sub_right (Offset.sub_below _ (by decide) (by decide))
  rw [WP.block_cons_iff]
  refine ⟨_,exec_ldrSp (off := 384) (by decide) ptr,WP.block_nil ?_⟩
  have g : (t.write .x .x5 (t.mem.readW (t.sp+384#64) 64)).gpr .x5 = stackArg o 2 := by
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

theorem frame_ok (hash : HashEightWithOk) {o : State} (c : Caller o) (pw : Prepared.Powers o) (iv : NL o = 12) (al : AL o ≤ 16)
    (hn : len o ≤ 96) (keep : shortFrame.allInstrs keepsV = true) :
    WP isa shortFrame o fun t => abiPreserved o t ∧ result o t := by
  apply WP.withPreservedV (hc := keep)
  apply WP.alloc (by decide) (by change 368 ≤ o.sp.toNat; have := c.room; omega)
  have front := prefix_ok c hn al
  refine WP.seq ((WP.seq_iff.mp front).mono fun _ w => WP.seq ((WP.seq_iff.mp w).mono fun _ w => WP.seq (w.mono ?_)))
  intro u ⟨header,input⟩
  refine WP.seq ((WP.seq_iff.mp (ready c iv hn header input)).mono fun _ w => WP.seq (w.mono ?_))
  intro s h
  refine WP.seq ((Fragment.directPiece_ok (pieceLayout c hn h) h.x6 h.x26 h.key h.dst h.auth).mono ?_)
  intro z cursor
  refine WP.seq ((loadPowers c pw hn al h cursor).mono ?_)
  intro u ⟨p,pc,_⟩
  refine (shortFinishUsing_ok (cached := true) (.inl rfl) hash o u (base o) _ p (fun _ => pc)).mono ?_
  intro t ⟨post,g,sp,_,_,_⟩ m v fr
  exact ⟨⟨g,by change t.sp+BitVec.ofNat 64 shortWork = o.sp; rw [sp]; exact BitVec.sub_add_cancel _ _⟩,
    result_frame c (by decide) post fr⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Short
