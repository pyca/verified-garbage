module

public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.StepGeometry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Crypt
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn

@[expose] public section

/-! The frame of one descriptor iteration preserves the authenticated prefix and the caller's saved state. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt)
variable {M : CtxMode} {s t u : State} {pre i : Nat}

abbrev iterFrame (s : State) (pre i : Nat) : List Region :=
  ⟨W s+224#64,48⟩ :: crFrame (W s+16#64) (W s) (SP s) (dPtr s pre i) (sz s pre i)

theorem iter_sub (g : Geometry s pre i) : ∀ r∈iterFrame s pre i,∃ r'∈changed s,Region.Sub r r' := by
  intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩
  · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),Offset.sub_base _ g.total⟩
  · exact ⟨_,List.mem_cons_self ..,fun a ha => Lay.wSub (d:=16) (n:=80) (by decide) a (Lay.stSub (by decide) a ha)⟩
  · exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩
  · exact ⟨below (SP s) 56,by simp [changed],below_sub (by decide) (by decide)⟩

theorem iter_work (h : Layout M s) (g : Geometry s pre i) {d n : Nat}
    (hi : d+n≤224) (cipher : d+n≤64 ∨ 96≤d) :
    ∀ r∈iterFrame s pre i,(⟨W s+BitVec.ofNat 64 d,n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact Offset.disjoint _ (.inl hi) (by omega) (by decide)
  · exact (h.d_w.symm.sub_left (Lay.wSub (by omega))).sub_right (Offset.sub_base _ g.total)
  · rw [show W s+16#64+48#64=W s+BitVec.ofNat 64 64 from BitVec.add_assoc ..]
    exact Offset.disjoint _ cipher (by omega) (by decide)
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  · exact ((h.b_w.sub_left (below_sub (by decide) (by decide))).sub_right (Lay.wSub (by omega))).symm

theorem iter_prefix (h : Layout M s) (g : Geometry s pre i) {k : Nat} (hk : k≤consumed s pre i) :
    ∀ r∈iterFrame s pre i,(⟨Dst s,k⟩ : Region).Disjoint r := by
  have len := g.total
  have q := h.d_w.sub_left (Region.sub_prefix (show k≤L s by omega))
  intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact q.sub_right (Lay.wSub (by decide))
  · have e := Offset.disjoint (Dst s) (d:=0) (n:=k) (e:=consumed s pre i) (k:=sz s pre i) (.inl (by omega))
      (by have : L s < 2^64 := BitVec.isLt _; omega) (by have : L s < 2^64 := BitVec.isLt _; omega)
    simpa using e
  · exact (q.sub_right (Lay.wSub (by decide))).sub_right (Lay.stSub (by decide))
  · exact q.sub_right (Lay.wSub (by decide))
  · exact ((h.b_d.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by omega))).symm

theorem iter_key (h : Layout M s) : ∀ r∈changed s, (⟨K s,256⟩ : Region).Disjoint r := by
  intro r hr; simp only [changed,List.mem_cons,List.not_mem_nil,or_false] at hr
  have k : (⟨K s,256⟩ : Region).Sub (kR M s) := Region.sub_prefix M.ge
  rcases hr with rfl|rfl|rfl
  · exact h.k_w.sub_left k
  · exact h.k_d.sub_left k
  · exact ((h.b_k.sub_left (below_sub (by decide) (by decide))).sub_right k).symm

theorem source_unchanged (h : Layout M s) (f : Frame (changed s) s.mem t.mem) (hi : i<Cnt s)
    (g : Geometry s pre i) : bytesAt t.mem (qPtr s pre i) (sz s pre i) = bytesAt s.mem (qPtr s pre i) (sz s pre i) := by
  have region := slice_mem s hi
  obtain ⟨d,_,w⟩ := h.ls _ region
  have sub : (⟨qPtr s pre i,sz s pre i⟩ : Region).Sub ⟨sb s i,sl s i⟩ :=
    Offset.sub_base _ (by dsimp [sz]; have := g.skipBound; omega)
  apply bytesAt_frame f _ (by have := g.total; have : L s < 2^64 := BitVec.isLt _; omega)
  intro r hr; simp only [changed,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact w.sub_left sub
  · exact d.sub_left sub
  · exact (((h.b_ls _ region).sub_left (below_sub (by decide) (by decide))).sub_right sub).symm

end VG.Proof.AesGcm.X86_64.DirectGather

/-! Convert descriptor registers and memory into the direct counter-mode call interface. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.Gcm (Ctr)
variable {M : CtxMode} {s t u : State} {pre i : Nat}

abbrev LoadedAt (s : State) (pre i : Nat) (t u : State) :=
  Loaded (W s) (dp s i) (sb s i) (Dst s+BitVec.ofNat 64 pre) (sl s i) (skip pre i) (consumed s pre i-pre) t u

theorem loaded_inputs (h : Layout M s) (a : LoopAt M s pre i t) (hi : i<Cnt s) (z : LoadedAt s pre i t u) :
    PieceInput (K s) (W s+16#64) (W s) (SP s) (R s) (qPtr s pre i) (dPtr s pre i) (sz s pre i) u ∧
    u.gpr .rsi=BitVec.ofNat 64 (consumed s pre i%16) ∧
    Ctr u.mem (W s+16#64+48#64) (W s+16#64+64#64) (ciphOf u.mem (K s) (R s)) (icb s) (consumed s pre i) := by
  have g := geometry h a hi
  obtain ⟨src,dst,sep⟩ := geometry_data h a hi
  have f : Frame [⟨W s+224#64,48⟩] t.mem u.mem := by rw [z.mem]; exact loadedMem_frame _ _ _ _
  have small : Frame (iterFrame s pre i) t.mem u.mem := f.sub fun r hr => ⟨r,List.mem_cons.mpr (.inl (List.mem_singleton.mp hr)),fun _ x => x⟩
  have base := small.sub (iter_sub g)
  have key := (ciph_frame base (iter_key h) a.rounds.2).trans a.key
  have prele := g.pref
  have aligned := a.aligned
  have dstreg := z.dst
  rw [add_ofNat_assoc,Nat.add_sub_of_le prele] at dstreg
  have read (d : Nat) (n : Nat) (hi : d+n≤224) : ∀ r∈[(⟨W s+224#64,48⟩ : Region)],(⟨W s+BitVec.ofNat 64 d,n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl hi) (by omega) (by decide)
  refine ⟨⟨a.env.keep z.kept z.rd z.wr,rounds_frame f (read 176 8 (by decide)) a.rounds,src.of_eq z.rd z.wr,
    dst.of_eq z.rd z.wr,sep,z.src,dstreg,z.left⟩,?_,?_⟩
  · rw [z.off]; congr 1; omega
  · rw [key]
    apply a.ctr.congr
    · rw [show W s+16#64+48#64=W s+64#64 from BitVec.add_assoc ..]
      exact blockAt_frame f (read 64 16 (by decide))
    · rw [show W s+16#64+64#64=W s+80#64 from BitVec.add_assoc ..]
      exact blockAt_frame f (read 80 16 (by decide))

end VG.Proof.AesGcm.X86_64.DirectGather

/-! Derive the next gather-loop invariant from the changes made by one fragment. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Ctr xorKs)
open VG.Spec.Gcm (blockAt)
variable {M : CtxMode} {s t u : State} {i pre : Nat}

structure StepResult (s t : State) (pre i : Nat) (u : State) : Prop where
  env : Env (K s) (W s+16#64) (W s) (SP s) u
  rd : u.rd=t.rd
  wr : u.wr=t.wr
  frame : Frame (iterFrame s pre i) t.mem u.mem
  desc : u.mem.readW (W s+256#64) 64=dp s (i+1)
  num : u.mem.readW (W s+224#64) 64=BitVec.ofNat 64 (Cnt s-(i+1))
  span : u.mem.readW (W s+240#64) 64=BitVec.ofNat 64 (consumed s pre i+sz s pre i-pre)
  skipAt : u.mem.readW (W s+264#64) 64=0
  ctr : Ctr u.mem (W s+16#64+48#64) (W s+16#64+64#64) (ciph s) (icb s) (consumed s pre i+sz s pre i)
  out : bytesAt u.mem (dPtr s pre i) (sz s pre i)=xorKs (ciph s) (icb s) (consumed s pre i)
    (bytesAt s.mem (qPtr s pre i) (sz s pre i))

theorem StepResult.next (h : Layout M s) (a : LoopAt M s pre i t) (g : Geometry s pre i)
    (z : StepResult s t pre i u) : LoopAt M s pre (i+1) u := by
  have f := z.frame
  have big := f.sub (iter_sub g)
  have wk (d : Nat) (lo : 96≤d) (hi : d+8≤224) :
      u.mem.readW (W s+BitVec.ofNat 64 d) 64=t.mem.readW (W s+BitVec.ofNat 64 d) 64 :=
    f.readW (Region.contains_self _ _) (iter_work h g hi (.inr lo)) (by decide)
  have k := iter_key h
  have hk := ciph_frame big k a.rounds.2
  have prelen := a.preLen
  have lt : L s<2^64 := BitVec.isLt _
  have cipher0 := bytesAt_frame f (iter_prefix h g g.pref) (by omega)
  have lng := g.total
  have prior := bytesAt_frame f (iter_prefix h g (Nat.le_refl _)) (by omega)
  refine ⟨z.env,z.rd.trans a.rd,z.wr.trans a.wr,a.saved.frame f (iter_work h g (by decide) (.inr (by decide))),
    a.frame.trans big,a.preLen,a.inFirst,a.noFirst,a.aligned,z.desc,z.num,by rw [g.next]; exact z.span,
    by simpa [skip] using z.skipAt,(wk 200 (by decide) (by decide)).trans a.data,
    (wk 208 (by decide) (by decide)).trans a.len,(wk 192 (by decide) (by decide)).trans a.total,
    (wk 184 (by decide) (by decide)).trans a.aad,⟨(wk 176 (by decide) (by decide)).trans a.rounds.1,a.rounds.2⟩,
    hk.trans a.key,?_,?_,?_,by rw [g.next]; exact z.ctr,?_⟩
  · exact (blockAt_frame big fun r hr => (k r hr).sub_left (Lay.ctxSub (by decide))).trans a.hkey
  · exact (blockAt_frame f (iter_work h g (by decide) (.inl (by decide)))).trans a.j0
  · rw [cipher0]
    apply a.auth.congr
    · rw [show W s+16#64+16#64=W s+32#64 from BitVec.add_assoc ..]
      exact blockAt_frame f (iter_work h g (by decide) (.inl (by decide)))
    · rw [show W s+16#64+32#64=W s+48#64 from BitVec.add_assoc ..]
      apply bytesAt_frame f
      · exact iter_work h g (by omega) (.inl (by omega))
      · omega
  · rw [g.next,bytesAt_add,prior,a.out,g.plainNext]
    rw [Gcm.gctr_eq,Gcm.gctr_eq,Gcm.xorKs_append,g.plainLen,Nat.zero_add,z.out]

end VG.Proof.AesGcm.X86_64.DirectGather

/-! Execute one descriptor, including the empty-fragment branch and the public loop count. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.DirectGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.Gcm (Ctr xorKs)
open VG.Spec.Aes (bytesAt)
variable {M : CtxMode} {s t u z : State} {pre i : Nat}
abbrev runFragment (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl) : Prog isa :=
  .ite .e (.block []) (.seq suffix (.seq (whole ⟨c.callee.name,c.callee.code⟩) (cryptTailG v.callees true)))
abbrev iteration (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl) : Prog isa :=
  .seq (.block loadPiece) (.seq (runFragment v c) (.block advance))
abbrev CipherOut (s : State) (pre i : Nat) (u z : State) :=
  PieceOutput (K s) (W s+16#64) (W s) (SP s) (R s) (icb s) (consumed s pre i)
    (qPtr s pre i) (dPtr s pre i) (sz s pre i) u z

theorem runFragment_ok (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl) (h : Layout M s)
    (a : LoopAt M s pre i t) (hi : i<Cnt s) (d : LoadedAt s pre i t u) :
    WP isa (runFragment v c) u (CipherOut s pre i u) := by
  obtain ⟨p,off,ctr⟩ := loaded_inputs h a hi d
  refine WP.ite (decide (sz s pre i=0)) (eval_e d.zero) (fun hz => ?_) (fun hz => ?_)
  · have e : sz s pre i=0 := by simpa using hz
    exact WP.block_nil ⟨p.env,p.rounds,by simpa [e] using ctr,by simp [e,bytesAt,xorKs],Frame.refl _ _⟩
  · have ne : sz s pre i≠0 := by simpa using hz
    exact piece_ok v c (h.oneCtx M.ge).lay p off (by omega) ctr

private theorem ctrSlot (h : Layout M s) (g : Geometry s pre i) (a : CipherOut s pre i u z)
    (d : Nat) (lo : 224≤d) (hi : d+8≤272) :
    z.mem.readW (W s+BitVec.ofNat 64 d) 64=u.mem.readW (W s+BitVec.ofNat 64 d) 64 := by
  apply a.frame.readW (Region.contains_self _ _) _ (by decide)
  intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact (h.d_w.symm.sub_left (Lay.wSub (by omega))).sub_right (Offset.sub_base _ g.total)
  · rw [show W s+16#64+48#64=W s+64#64 from BitVec.add_assoc ..]
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  · exact ((h.b_w.sub_left (below_sub (by decide) (by decide))).sub_right (Lay.wSub (by omega))).symm

private theorem decFrame (m : Mem) (W : Addr) (v : Addr) :
    Frame [⟨W+224#64,48⟩] m (slot m W 224 v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) v (by
    simp only [Region.Contains,BitVec.sub_self,BitVec.toNat_zero,Nat.zero_add]; decide)

theorem iteration_ok (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl) (h : Layout M s)
    (a : LoopAt M s pre i t) (hi : i<Cnt s) :
    WP isa (iteration v c) t fun r => LoopAt M s pre (i+1) r ∧ r.zf=some (decide (Cnt s-(i+1)=0)) := by
  have g := geometry h a hi
  have total := g.total
  have lt : L s<2^64 := BitVec.isLt _
  have countLt : Cnt s<2^64 := BitVec.isLt _
  have it := loadPiece_ok (descriptor_input h a hi) (BitVec.isLt _) g.skipBound
    (show consumed s pre i-pre<2^64 by omega)
  refine WP.seq (it.mono fun u d => ?_)
  refine WP.seq ((WP.with_rdwr (runFragment_ok v c h a hi d)).mono fun z ⟨out,rd,wr⟩ => ?_)
  have f₁ : Frame [⟨W s+224#64,48⟩] t.mem u.mem := by rw [d.mem]; exact loadedMem_frame _ _ _ _
  have lift (m m' : Mem) (f : Frame [⟨W s+224#64,48⟩] m m') :
      Frame (iterFrame s pre i) m m' := f.sub fun r hr => ⟨r,List.mem_cons.mpr (.inl (List.mem_singleton.mp hr)),fun _ hx => hx⟩
  have frameU := a.frame.trans ((lift _ _ f₁).sub (iter_sub g))
  have frameZ := (lift _ _ f₁).trans (out.frame.sub (fun r hr => ⟨r,List.mem_cons_of_mem _ hr,fun _ hx => hx⟩))
  have slots := loadedMem_slots t.mem (W s) (dp s i) ((consumed s pre i-pre)+sz s pre i)
  rw [←d.mem] at slots
  obtain ⟨desc,skipAt,span,num⟩ := slots
  have load (d : Nat) (lo : 224≤d) (hi : d+8≤272) := ctrSlot h g out d lo hi
  have numZ := (load 224 (by decide) (by decide)).trans (num.trans a.num)
  have hw := out.env.perm.wW (show 224+8≤2560 by decide)
  refine (advance_ok out.env.r15 hw numZ (by omega) (by omega)).mono fun r b => ?_
  have same (d : Nat) (lo : 232≤d) (hi : d+8≤272) :
      r.mem.readW (W s+BitVec.ofNat 64 d) 64=z.mem.readW (W s+BitVec.ofNat 64 d) 64 := by
    rw [b.mem]; exact slot_other _ _ _ d 224 (.inr lo) (by omega) (by decide)
  have f₃ : Frame [⟨W s+224#64,48⟩] z.mem r.mem := by rw [b.mem]; exact decFrame _ _ _
  have f := frameZ.trans (lift _ _ f₃)
  have key := ciph_frame frameU (iter_key h) h.rounds
  have cip : ciphOf u.mem (K s) (R s)=ciph s := key
  have extent := g.pref
  have step : StepResult s t pre i r := by
    refine ⟨out.env.keep b.kept b.rd b.wr,b.rd.trans (rd.trans d.rd),b.wr.trans (wr.trans d.wr),f,
      ?_,?_,?_,?_,?_,?_⟩
    · rw [same 256 (by decide) (by decide),load 256 (by decide) (by decide),desc,dp,dp,add_ofNat_assoc]
      congr 2
    · rw [b.mem]; change (z.mem.writeW _ _).readW _ 64=_
      rw [Mem.readW_writeW_self64]; congr 1
    · rw [same 240 (by decide) (by decide),load 240 (by decide) (by decide),span]; congr 1; omega
    · rw [same 264 (by decide) (by decide),load 264 (by decide) (by decide),skipAt]
    · have ctr := out.ctr
      rw [cip] at ctr
      apply ctr.congr
      all_goals
        apply blockAt_frame f₃
        intro q hq; simp only [List.mem_singleton] at hq; subst hq
        rw [BitVec.add_assoc]
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · have cipher := out.out
      rw [cip,source_unchanged h frameU hi g] at cipher
      refine (bytesAt_frame f₃ (fun q hq => ?_) (by omega)).trans cipher
      simp only [List.mem_singleton] at hq; subst hq
      exact (h.d_w.sub_left (Offset.sub_base _ g.total)).sub_right (Lay.wSub (by decide))
  exact ⟨step.next h a g,by simpa only [Nat.sub_sub] using b.zero⟩

end VG.Proof.AesGcm.X86_64.DirectGather
