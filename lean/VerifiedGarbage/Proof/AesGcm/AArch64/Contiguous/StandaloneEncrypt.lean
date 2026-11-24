module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Standalone
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Calls
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Aligned
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericLoop
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.BatchesCT
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Standalone

/-! The contiguous source and destination use the gather kernel's two-pointer ABI
for complete stitched batches and the same counter kernel for the remainder. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.DirectGather (hashO descO batches)
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone
open VG.Proof.Gcm.AArch64.Stitch (BatchIn BatchProgress batchFrame batchTest PendingIn GatherLaws)
open VG.Proof.AesGcm.AArch64.DirectGather.Generic (Encrypted batchDone)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctxH)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Ctr xorKs)
variable {wn R n : Nat} {Ctx St W SP D O : Addr} {icb Y : Block} {s u t : State}

structure EncIn (wn R n : Nat) (Ctx St W SP D O : Addr) (icb Y : Block) (s : State) : Prop where
  env : Env wn Ctx St W SP s
  rr : R=10 ∨ R=12 ∨ R=14
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  src : DataOk wn St W s D n
  dst : DataW wn Ctx St W s O n
  mode : BufferLayout D O n
  dataSlot : s.mem.readW (W+232#64) 64 = D
  lenSlot : s.mem.readW (W+240#64) 64 = BitVec.ofNat 64 n
  outSlot : s.mem.readW (W+336#64) 64 = O
  ctr : Ctr s.mem (St+48#64) (St+64#64) (ciphOf s.mem Ctx R) icb 0
  acc : blockAt s.mem (St+16#64) = Y

abbrev encArgs : List Instr := [.ldr .x .x23 .x19 dataO,.ldr .x .x24 .x19 lenO,
  .ldr .x .x26 .x19 descO,.str .x .x26 .x19 hashO,imm .x25 0]

structure SetUp (W D O : Addr) (n : Nat) (s t : State) : Prop where
  src : t.gpr .x23 = D
  len : t.gpr .x24 = BitVec.ofNat 64 n
  dst : t.gpr .x26 = O
  cursor : t.gpr .x25 = 0
  regs : Others [.x23,.x24,.x26,.x25] s t
  mem : t.mem = s.mem.writeW (W+352#64) O
  sp : t.sp=s.sp
  rd : t.rd=s.rd
  wr : t.wr=s.wr

theorem args_ok (c : EncIn wn R n Ctx St W SP D O icb Y s) :
    WP isa (.block encArgs) s (SetUp W D O n s) := by
  have bounds := c.env.perm.hWn
  have rd (d : Nat) (h : d+8 ≤ 512) : InRegions (s.rd++s.wr) (W+BitVec.ofNat 64 d) 8 := c.env.perm.wR h
  have wr : InRegions s.wr (W+352#64) 8 := in_off c.env.perm.w (by omega) (by omega)
  have a : s.mem.read (W+232#64) 8 = D := c.dataSlot
  have b : s.mem.read (W+240#64) 8 = BitVec.ofNat 64 n := c.lenSlot
  have o : s.mem.read (W+336#64) 8 = O := c.outSlot
  have r0 := rd 232 (by decide)
  have r1 := rd 240 (by decide)
  have r2 := rd 336 (by decide)
  refine WP.of_runBlock ⟨_,by unfold encArgs; arun [c.env.x19,dataO,lenO,descO,hashO,r0,r1,r2,wr,a,b,o],?_⟩
  exact ⟨by simp [gpr_write],by simp [gpr_write],by simp [gpr_write],by simp [gpr_write],
    by others_tac,rfl,rfl,rfl,rfl⟩

theorem SetUp.batch (c : EncIn wn R n Ctx St W SP D O icb Y s) (e : SetUp W D O n s u) :
    BatchIn wn Ctx St W SP D O R n u :=
  ⟨c.env.keep (fun r h => e.regs r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> decide))
    e.sp e.rd e.wr,c.rr,(e.regs _ (by decide)).trans c.x22,e.src,e.len,e.dst,
    c.src.of_eq e.rd e.wr,c.dst.of_eq e.rd e.wr,c.mode⟩

theorem SetUp.pending (c : EncIn wn R n Ctx St W SP D O icb Y s) (e : SetUp W D O n s u) :
    PendingIn wn St W O O 0 u := by
  refine ⟨?_,by simp,(c.dst.ok.take (Nat.zero_le n)).of_eq e.rd e.wr⟩
  rw [e.mem]; exact Mem.readW_writeW_self64 ..

theorem batch_ok (v : GcmImpl) (stitch forward : Bool) (L : Lay wn Ctx St W) (gh : stitch=true → GatherLaws)
    (h : BatchIn wn Ctx St W SP D O R n u) (hp : PendingIn wn St W O O 0 u)
    (ctr : Ctr u.mem (St+48#64) (St+64#64) (ciphOf u.mem Ctx R) icb 0) (acc : blockAt u.mem (St+16#64) = Y) :
    WP isa (if stitch then batches v.callees forward else .block []) u fun t =>
      BatchProgress wn R n 0 Ctx St W SP D O O icb Y u t (batchDone stitch n) (batchDone stitch n / 16) := by
  cases stitch
  · apply WP.block_nil
    simp only [batchDone,Bool.false_and,Bool.false_eq_true,ite_false,Nat.zero_div]
    exact ⟨Nat.zero_le _,⟨0,rfl⟩,by simp,by rfl,ctr,acc,
      by simpa using hp.slot,
      by simpa [batchDone] using h.x23,by simpa [batchDone] using h.x26,h.x24,h.env,
      fun _ _ _ _ _ _ => rfl,Frame.refl _ _,rfl,rfl⟩
  · apply (Proof.Gcm.AArch64.Stitch.batches_ok v h L (gh rfl) (fun _ => hp) forward).mono
    intro t post
    obtain ⟨b,j,e,jval,p⟩ := Proof.Gcm.AArch64.Stitch.batches_progress (B := O) (T := 0) (h := 0) (k := 0)
      h L rfl (by simp) (by simpa using h.dst) acc ctr (by simpa using hp.slot) (by simpa using post)
    have eq : batchDone true n = b := by rw [e]; by_cases z : batchTest n = 0 <;> simp [batchDone,z]
    have count : j = b/16 := by
      rw [jval]; split
      · rename_i zero; simp [e,zero]
      · simp
    rwa [eq,← count]
theorem batch_apart {p : Nat} {q : Region} (lim : 768 ≤ wn) (ho : q.Disjoint ⟨O,p⟩)
    (hs : q.Disjoint ⟨St,80⟩) (hw : q.Disjoint (workR wn W)) :
    ∀ r ∈ batchFrame wn O St W p, q.Disjoint r := by
  intro r hr
  simp only [batchFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact ho
  · exact hs.sub_right (Lay.stSub (by decide))
  · exact hs.sub_right (Lay.stSub (by decide))
  · exact hw.sub_right (Lay.wSub (by change 352+8≤wn; omega))
  · exact hw.sub_right (Lay.wSub (by omega))

theorem SetUp.frame (e : SetUp W D O n s u) :
    Frame [⟨W+352#64,8⟩] s.mem u.mem := by
  rw [e.mem]; exact (Frame.refl _ _).writeW (.head _) _ (Region.contains_self _ _)

theorem SetUp.batchState (L : Lay wn Ctx St W) (c : EncIn wn R n Ctx St W SP D O icb Y s)
    (e : SetUp W D O n s u) :
    Ctr u.mem (St+48#64) (St+64#64) (ciphOf u.mem Ctx R) icb 0 ∧ blockAt u.mem (St+16#64) = Y := by
  have fr := e.frame
  have wc : (⟨Ctx,256⟩ : Region).Disjoint ⟨W+352#64,8⟩ := L.cw'.sub_right (Offset.sub_base W (by change 352+8 ≤ wn; have := L.hWn; omega))
  have key := ciph_frame fr (by simpa only [List.mem_singleton,forall_eq] using wc) c.rr
  rw [key]
  refine ⟨Ctr.frame fr (fun q hq => ?_) c.ctr,?_⟩
  · obtain rfl := List.mem_singleton.mp hq
    exact L.st_w (by decide) (.inr ⟨by decide,by decide⟩)
  · have apart : (⟨St+16#64,16⟩ : Region).Disjoint ⟨W+352#64,8⟩ := L.st_w (by decide) (.inr ⟨by decide,by decide⟩)
    rw [blockAt_frame fr (by simpa only [List.mem_singleton,forall_eq] using apart)]
    exact c.acc

theorem tail_args {p j : Nat} (L : Lay wn Ctx St W) (h : BatchIn wn Ctx St W SP D O R n u)
    (x25 : u.gpr .x25 = 0) (progress : BatchProgress wn R n 0 Ctx St W SP D O O icb Y u t p j) :
    CrInG wn true Ctx St W SP t.gpr R p (D+BitVec.ofNat 64 p) (O+BitVec.ofNat 64 p) (n-p) t ∧
    Ctr t.mem (St+48#64) (St+64#64) (ciphOf t.mem Ctx R) icb p := by
  have hp := progress.le
  have off : p%16=0 := Nat.mod_eq_zero_of_dvd progress.whole
  have keep (r : Reg) (hr : r∈preserved) (a : r≠.x23) (b : r≠.x24) (c : r≠.x26) (d : r≠.x30) :=
    progress.saved r hr a b c d
  have key := ciph_frame progress.frame (batch_apart L.hWn.1 ((h.dst.take hp).ctx) L.cs L.cw') h.rounds
  refine ⟨⟨progress.env,fun _ _ => rfl,(keep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x22,
    h.rounds,progress.src,progress.rest,?_,(h.src.drop hp).of_eq progress.rd progress.wr,
    (h.dst.drop hp).of_eq progress.rd progress.wr,h.apart.sub (by omega),?_⟩,?_⟩
  · rw [off,keep _ (by decide) (by decide) (by decide) (by decide) (by decide),x25];rfl
  · simpa only [BitVec.add_zero] using progress.dst
  · rw [key]; simpa only [Nat.zero_add] using progress.ctr

theorem guardedTail_ok (L : Lay wn Ctx St W) (v : GcmImpl) {p : Nat}
    (input : CrInG wn true Ctx St W SP t.gpr R p D O n t) (hp : p%16=0)
    (ctr : Ctr t.mem (St+48#64) (St+64#64) (ciphOf t.mem Ctx R) icb p) (hv : v.ctr.scratch ≤ wn-512) :
    WP isa (.ite (.zero .x .x24) (.block []) (Impl.AesGcm.AArch64.Contiguous.Tail.aligned v.callees)) t
      (Encrypted wn Ctx St W SP t.gpr R icb p D O n t.mem) := by
  have lt := input.data.lt
  have ev : AArch64.eval (.zero .x .x24) t = some (decide (n=0)) := by
    exact Proof.Aes.AArch64.Aese.eval_zero input.x24 lt
  apply WP.ite (decide (n=0)) ev
  · intro h
    obtain rfl := of_decide_eq_true h
    refine WP.block_nil ⟨input.env,fun _ _ => rfl,by simpa using input.x23,?_,input.x24,by simpa using input.x25,
      by simpa using ctr,by rfl,Frame.refl _ _⟩
    simpa using input.outAt.2.2
  · intro _; exact Tail.aligned_ok L v input hp ctr hv

theorem tail_apart {p : Nat} {q : Region} (lim : 768 ≤ wn) (ho : q.Disjoint ⟨O,p⟩)
    (hs : q.Disjoint ⟨St,80⟩) (hw : q.Disjoint (workR wn W)) :
    ∀ r ∈ crFrame wn St W O p, q.Disjoint r := by
  intro r hr
  simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact ho
  · exact hs.sub_right (Lay.stSub (by decide))
  · exact hw.sub_right (Lay.wSub (by omega))

structure EncOut (wn R n : Nat) (Ctx St W SP D O : Addr) (icb Y : Block) (s t : State) : Prop where
  env : Env wn Ctx St W SP t
  x22 : t.gpr .x22 = s.gpr .x22
  x26 : t.gpr .x26 = O+BitVec.ofNat 64 n
  x28 : t.gpr .x28 = s.gpr .x28
  cipher : bytesAt t.mem O n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n)
  auth : ∃ j, 16*j ≤ n ∧ t.mem.readW (W+352#64) 64 = O+BitVec.ofNat 64 (16*j) ∧
    blockAt t.mem (St+16#64) = ghashFrom (ctxH s.mem Ctx) Y (blocksAt t.mem O j)
  frame : Frame (batchFrame wn O St W n) s.mem t.mem
  rd : t.rd=s.rd
  wr : t.wr=s.wr

theorem join {p j : Nat} {z : State} (L : Lay wn Ctx St W) (h : BatchIn wn Ctx St W SP D O R n u)
    (q : BatchProgress wn R n 0 Ctx St W SP D O O icb Y u t p j)
    (tail : Encrypted wn Ctx St W SP t.gpr R icb p (D+BitVec.ofNat 64 p) (O+BitVec.ofNat 64 p) (n-p) t.mem z)
    (rd : z.rd=t.rd) (wr : z.wr=t.wr) : EncOut wn R n Ctx St W SP D O icb Y u z ∧
      z.mem.readW (W+352#64) 64 = O+BitVec.ofNat 64 (16*j) := by
  have hp := q.le
  have hj : 16*j ≤ p := by simpa only [Nat.zero_add] using q.hashed
  have hn := h.src.lt
  have lim := L.hWn.1
  have cp := h.dst.take hp
  have split := split_disj (D := O) hp hn
  have kept := bytesAt_frame tail.frame (tail_apart lim split cp.ok.st cp.ok.w) (by omega)
  have data := h.src.drop hp
  have dis : (⟨D+BitVec.ofNat 64 p,n-p⟩ : Region).Disjoint ⟨O,p⟩ := by
    rcases h.apart with same|d
    · rw [← same]; exact split.symm
    · exact (d.sub_left (Offset.sub_base D (by omega))).sub_right (Region.sub_prefix hp)
  have source := bytesAt_frame q.frame (batch_apart lim dis data.st data.w) (by omega)
  have key := ciph_frame q.frame (batch_apart lim cp.ctx L.cs L.cw') h.rounds
  have rem := tail.out
  rw [source,key] at rem
  have whole := done_append (j := p) (l := n-p) (kept.trans q.data) (by simpa only [Nat.zero_add] using rem)
  have total : O+BitVec.ofNat 64 p+BitVec.ofNat 64 (n-p) = O+BitVec.ofNat 64 n := by
    rw [BitVec.add_assoc,← BitVec.ofNat_add,Nat.add_sub_cancel' hp]
  have keep (r : Reg) (a : r ∈ [Reg.x22,.x28]) : z.gpr r = u.gpr r := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at a
    rcases a with rfl|rfl <;> exact (tail.kept _ (by decide)).trans (q.saved _ (by decide) (by decide) (by decide) (by decide) (by decide))
  have hashApart : ∀ r ∈ crFrame wn St W (O+BitVec.ofNat 64 p) (n-p), (⟨W+352#64,8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ((h.dst.drop hp).ok.w.sub_right (Offset.sub_base W (by change 352+8≤wn; omega))).symm
    · exact (L.st_wn (by decide) (.inr ⟨by decide,by omega⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by have := L.hWn;omega)
  have cursor := (tail.frame.readW (r := ⟨W+352#64,8⟩) (Region.contains_self _ _) hashApart (by decide : 64/8<2^64)).trans q.hashPtr
  refine ⟨?_,cursor⟩
  refine ⟨tail.env,keep _ (by decide),tail.dst.trans total,keep _ (by decide),by simpa only [Nat.add_sub_cancel' hp] using whole,?_,?_,rd.trans q.rd,wr.trans q.wr⟩
  · refine ⟨j,by omega,?_,?_⟩
    · exact cursor
    · have yApart : ∀ r ∈ crFrame wn St W (O+BitVec.ofNat 64 p) (n-p), (⟨St+16#64,16⟩ : Region).Disjoint r := by
        intro r hr
        simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl
        · exact ((h.dst.drop hp).ok.st.sub_right (Lay.stSub (by decide))).symm
        · exact Offset.disjoint St (.inl (by decide)) (by decide) (by decide)
        · exact L.st_wn (by decide) (.inr ⟨by decide,by omega⟩)
      have aligned := h.dst.take (Nat.le_trans hj hp)
      have blocks := blocksAt_frame tail.frame (tail_apart lim (split.sub_left (Region.sub_prefix hj)) aligned.ok.st aligned.ok.w) (by omega)
      rw [blockAt_frame tail.frame yApart,q.y,blocks]
  · apply Frame.trans (q.frame.sub (fun r hr => ?_)) (tail.frame.sub (fun r hr => ?_))
    · simp only [batchFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl
      · exact ⟨_,.head _,Region.sub_prefix hp⟩
      all_goals exact ⟨_,by simp [batchFrame],fun _ h => h⟩
    · simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact ⟨⟨O,n⟩,.head _,Offset.sub_base _ (by omega)⟩
      all_goals exact ⟨_,by simp [batchFrame],fun _ h => h⟩


theorem SetUp.liftOut {z : State} (L : Lay wn Ctx St W) (c : EncIn wn R n Ctx St W SP D O icb Y s)
    (e : SetUp W D O n s u) (h : EncOut wn R n Ctx St W SP D O icb Y u z) :
    EncOut wn R n Ctx St W SP D O icb Y s z := by
  have sub : (⟨W+352#64,8⟩ : Region).Sub (workR wn W) := Offset.sub_base W (by change 352+8≤wn; have := L.hWn; omega)
  have apart {r : Region} (d : r.Disjoint (workR wn W)) : ∀ q ∈ [⟨W+352#64,8⟩], r.Disjoint q :=
    by simpa only [List.mem_singleton,forall_eq] using d.sub_right sub
  have key := ciph_frame e.frame (apart L.cw') c.rr
  have hash := blockAt_frame e.frame (apart (L.cw'.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))))
  change ctxH u.mem Ctx = ctxH s.mem Ctx at hash
  refine ⟨h.env,h.x22.trans (e.regs _ (by decide)),h.x26,h.x28.trans (e.regs _ (by decide)),?_,?_,?_,h.rd.trans e.rd,h.wr.trans e.wr⟩
  · simpa only [key,bytesAt_frame e.frame (apart c.src.w) (Nat.le_of_lt c.src.lt)] using h.cipher
  · simpa only [hash] using h.auth
  · apply Frame.trans (e.frame.sub ?_) h.frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,by simp [batchFrame,hashO],fun _ h => h⟩

theorem encrypt_ok (v : GcmImpl) (L : Lay wn Ctx St W) (c : EncIn wn R n Ctx St W SP D O icb Y s)
    (gh : v.calls.pmull=true → GatherLaws) (hv : v.ctr.scratch ≤ wn-512) :
    WP isa (encrypt v.calls) s fun t => EncOut wn R n Ctx St W SP D O icb Y s t ∧
      t.mem.readW (W+352#64) 64 = O+BitVec.ofNat 64 (batchDone v.calls.pmull n) := by
  refine WP.seq ((args_ok c).mono ?_)
  intro u e
  have h := SetUp.batch c e
  obtain ⟨ctr,acc⟩ := SetUp.batchState L c e
  refine WP.seq ((batch_ok v _ (!v.calls.stitch) L gh h (SetUp.pending c e) ctr acc).mono ?_)
  intro t q
  obtain ⟨input,count⟩ := tail_args L h e.cursor q
  refine (WP.with_rdwr (guardedTail_ok L v input (Nat.mod_eq_zero_of_dvd q.whole) count hv)).mono ?_
  intro z ⟨tail,rd,wr⟩
  obtain ⟨out,cursor⟩ := join L h q tail rd wr
  exact ⟨SetUp.liftOut L c e out,by simpa only [Nat.mul_div_cancel' q.whole] using cursor⟩

theorem encrypt_rel {ivA ivB yA yB : Block} (v : GcmImpl) (L : Lay wn Ctx St W)
    (a : EncIn wn R n Ctx St W SP D O ivA yA s) (b : EncIn wn R n Ctx St W SP D O ivB yB t)
    (gh : v.calls.pmull=true → GatherLaws) (hv : v.ctr.scratch ≤ wn-512) :
    RelCT isa (Eq2 s t) (encrypt v.calls) TT := by
  refine rel_seq (rel_taint [.x19] (a.env.sp.trans b.env.sp.symm) (by agree_tac [a.env.x19,b.env.x19])
    ⟨_,by taint_decide⟩) (args_ok a) (args_ok b) ?_
  intro u u' ea eb
  have ha := SetUp.batch a ea
  have hb := SetUp.batch b eb
  have ba := SetUp.pending a ea
  have bb := SetUp.pending b eb
  obtain ⟨ca,ya⟩ := SetUp.batchState L a ea
  obtain ⟨cb,yb⟩ := SetUp.batchState L b eb
  have batchRel : RelCT isa (Eq2 u u') (if v.calls.pmull then batches v.callees (!v.calls.stitch) else .block []) TT := by
    cases flag : v.calls.pmull
    · change RelCT isa _ (.block []) TT
      exact rel_taint [] (ha.env.sp.trans hb.env.sp.symm) (by agree_tac []) ⟨.block [] 256,by decide⟩
    · exact DirectGather.Generic.batches_rel v ha hb L (gh flag) (fun _ => ba) (fun _ => bb) (!v.calls.stitch)
  refine rel_seq batchRel (batch_ok v _ (!v.calls.stitch) L gh ha ba ca ya) (batch_ok v _ (!v.calls.stitch) L gh hb bb cb yb) ?_
  intro t₁ t₂ qa qb
  obtain ⟨ra,_⟩ := tail_args L ha ea.cursor qa
  obtain ⟨rb,_⟩ := tail_args L hb eb.cursor qb
  refine rel_ite (Proof.Aes.AArch64.Aese.eval_zero ra.x24 ra.data.lt)
    (Proof.Aes.AArch64.Aese.eval_zero rb.x24 rb.data.lt) ?_ ?_
  · intro _; exact rel_taint [] (ra.env.sp.trans rb.env.sp.symm) (by agree_tac []) ⟨.block [] 256,by decide⟩
  · intro _; exact Tail.aligned_rel L v ra rb (Nat.mod_eq_zero_of_dvd qa.whole) hv

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
