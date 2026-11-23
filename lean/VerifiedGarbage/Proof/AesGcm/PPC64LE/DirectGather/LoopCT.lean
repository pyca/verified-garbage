module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.DirectGather
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.DirectGather
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Bulk
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.CT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Loop

/-! # Public addresses and loop bounds for direct POWER8 fragment encryption -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.DirectGather
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_taint)

def piecePublic : List Reg := [.r21,.r24,.r25,.r27,.r28,.r29,.r30,.r31]

theorem piece_certificate : ∃ h, (vectorTaint.check (Taint.ofRegs piecePublic) piece h).isSome=true :=
  ⟨_,by taint_decide⟩

theorem piece_rel {s t : State} (sp : s.sp=t.sp) (agree : ∀ r ∈ piecePublic, s.gpr r=t.gpr r) :
    RelCT isa (Eq2 s t) piece TT := by
  obtain ⟨_,hc⟩ := piece_certificate
  exact RelCT.taint (A := vectorTaint) (Taint.ofRegs piecePublic) (fun a b ⟨rfl,rfl⟩ =>
    ⟨sp,fun r hr => agree r (Taint.mem_ofRegs.mp hr)⟩) hc

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Trace of the fused POWER8 helper and its caller's memory accesses -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.DirectGather
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq rel_taint rel_ite)
open VG.Proof.AesGcm.PPC64LE.SealSplit.Call (reads writes)

structure SharedRegs (V₁ V₂ : Reg → Addr) : Prop where
  data : V₁ .r27=V₂ .r27
  rounds : V₁ .r28=V₂ .r28
  key : V₁ .r29=V₂ .r29
  state : V₁ .r30=V₂ .r30
  work : V₁ .r31=V₂ .r31

theorem addresses_agree {V₁ V₂ : Reg → Addr} {E sp : Addr} {s t : State} (h : SharedRegs V₁ V₂)
    (e : Env (cursors V₁ E) sp s) (f : Env (cursors V₂ E) sp t)
    (ptr : s.gpr .r24=t.gpr .r24) (len : s.gpr .r25=t.gpr .r25) :
    ∀ r ∈ piecePublic, s.gpr r=t.gpr r := by
  intro r hr
  simp only [piecePublic,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (e.fr _ (by decide)).trans (f.fr .r21 (by decide)).symm
  · exact ptr
  · exact len
  · exact (e.fr _ (by decide)).trans (h.data.trans (f.fr .r27 (by decide)).symm)
  · exact e.r28.trans (h.rounds.trans f.r28.symm)
  · exact e.r29.trans (h.key.trans f.r29.symm)
  · exact e.r30.trans (h.state.trans f.r30.symm)
  · exact e.r31.trans (h.work.trans f.r31.symm)

theorem fusedCall_rel [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {sp C S E : Addr} {R b : Nat} {s t : State} (x : BulkAbi sp C S E R b s)
    (y : BulkAbi sp C S E R b t) (cfg : SealSplit.Call.Config s) (cfg' : SealSplit.Call.Config t) :
    RelCT isa (Eq2 s t) (.call "vg_aes_gcm_encrypt_blocks_split" Impl.AesGcm.PPC64LE.SplitBlocks.encrypt) TT := by
  refine RelCT.callEx SplitBlocks.encrypt_correct SplitBlocks.encrypt_ct ?_
  intro left right both
  obtain ⟨hl,hr⟩ := both
  subst left; subst right
  refine ⟨reads s,writes s,reads t,writes t,cfg.pre,cfg'.pre,?_,cfg.reads,cfg.writes,cfg'.reads,cfg'.writes⟩
  have rs : s.gpr .r4=t.gpr .r4 := BitVec.eq_of_toNat_eq (x.rounds.trans y.rounds.symm)
  have r8 : s.gpr .r8=t.gpr .r8 := BitVec.eq_of_toNat_eq (x.readBlocks.trans y.readBlocks.symm)
  have r10 : s.gpr .r10=t.gpr .r10 := BitVec.eq_of_toNat_eq (x.writeBlocks.trans y.writeBlocks.symm)
  sig_pub [Proof.Gcm.encryptBlocksSplitContract,Proof.Gcm.encryptBlocksSplitSig,
    PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop]
  simp only [x.stack,y.stack,x.key,y.key,rs,r8,r10,x.counter,y.counter,x.hash,y.hash,x.src,y.src,x.dst,y.dst,
    true_and]
  exact x.scratch.trans y.scratch.symm

theorem bulkPrepare_certificate : ∃ cert, (taint.check (Taint.ofRegs piecePublic) bulkPrepare cert).isSome=true :=
  ⟨_,by taint_decide⟩

theorem bulkRun_rel [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {V₁ V₂ : Reg → Addr} {sp S E : Addr} {R n : Nat} {s t : State} (pub : SharedRegs V₁ V₂)
    (env : Env (cursors V₁ E) sp s) (env' : Env (cursors V₂ E) sp t)
    (w : V₁ .r31=sp+128) (st : V₁ .r30=sp+144)
    (p : s.gpr .r24=S) (p' : t.gpr .r24=S) (l : s.gpr .r25=BitVec.ofNat 64 n) (l' : t.gpr .r25=BitVec.ofNat 64 n)
    (hn : n<2^64) (hR : (V₁ .r28).toNat=R) (rounds : R=10 ∨ R=12 ∨ R=14)
    (space : BulkSpace sp (V₁ .r29) S E n s) (space' : BulkSpace sp (V₂ .r29) S E n t) :
    RelCT isa (Eq2 s t) bulkRun TT := by
  obtain ⟨_,cert⟩ := bulkPrepare_certificate
  exact rel_seq (rel_taint piecePublic (env.sp.trans env'.sp.symm) (addresses_agree pub env env' (p.trans p'.symm) (l.trans l'.symm)) cert)
    (bulkPrepare_wp env w st p l hn hR rounds space)
    (bulkPrepare_wp env' (pub.work.symm.trans w) (pub.state.symm.trans st) p' l' hn (by rwa [←pub.rounds]) rounds space')
    (fun _ _ a b => fusedCall_rel a.abi (pub.key ▸ b.abi) a.cfg b.cfg)

theorem bulkTest (s : State) {n : Nat} (h : s.gpr .r25=BitVec.ofNat 64 n) (fit : n<2^64) :
    WP isa (.block [.lsr .d .r12 .r25 9]) s (· = s.write .r12 (BitVec.ofNat 64 (n/512))) := by
  have sh : s.gpr .r25 >>> 9=BitVec.ofNat 64 (n/512) := by rw [h]; exact shrNat 9 fit
  crun [sh]

theorem bulk_rel [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {V₁ V₂ : Reg → Addr} {sp S E : Addr} {R n : Nat} {s t : State} (pub : SharedRegs V₁ V₂)
    (env : Env (cursors V₁ E) sp s) (env' : Env (cursors V₂ E) sp t)
    (w : V₁ .r31=sp+128) (st : V₁ .r30=sp+144)
    (p : s.gpr .r24=S) (p' : t.gpr .r24=S) (l : s.gpr .r25=BitVec.ofNat 64 n) (l' : t.gpr .r25=BitVec.ofNat 64 n)
    (hn : n<2^64) (hR : (V₁ .r28).toNat=R) (rounds : R=10 ∨ R=12 ∨ R=14)
    (space : BulkSpace sp (V₁ .r29) S E n s) (space' : BulkSpace sp (V₂ .r29) S E n t) :
    RelCT isa (Eq2 s t) bulk TT := by
  have th : ∃ hint, (taint.check (Taint.ofRegs [.r25]) (.block [.lsr .d .r12 .r25 9]) hint).isSome=true :=
    ⟨_,by taint_decide⟩
  obtain ⟨_,cert⟩ := th
  refine rel_seq (rel_taint [.r25] (env.sp.trans env'.sp.symm) (by simpa using l.trans l'.symm) cert)
    (bulkTest s l hn) (bulkTest t l' hn) (fun u v hu hv => ?_)
  subst u; subst v
  have e {V : Reg → Addr} {st' : State} (e0 : Env (cursors V E) sp st') :
      Env (cursors V E) sp (st'.write .r12 (BitVec.ofNat 64 (n/512))) :=
    e0.keep (fun r hr => by
      have h12 : r≠.r12 := by revert r; decide
      simp [State.write,h12]) rfl rfl rfl
  have z (u : State) : isa.eval (.zero .d .r12) (u.write .r12 (BitVec.ofNat 64 (n/512))) = some (decide (n/512=0)) :=
    eval_zero (by simp [State.write]) (by omega_using [hn])
  refine rel_ite (z s) (z t) (fun _ => ?_) (fun _ => ?_)
  · exact rel_taint [] (env.sp.trans env'.sp.symm) (by simp) (by taint_decide)
  · exact bulkRun_rel pub (e env) (e env') w st p p' l l' hn hR rounds (space.sub (Nat.le_refl _) rfl rfl)
      (space'.sub (Nat.le_refl _) rfl rfl)

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Public control flow and addresses across the gather descriptor loop -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.DirectGather
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq rel_ite rel_taint gl_mono gl_agree sb_agree sl_agree)

structure LoopPublic (a d : LoopArgs) (e f : State) : Prop where
  sp : a.sp=d.sp
  desc : a.desc=d.desc
  count : a.count=d.count
  regs : SharedRegs a.V d.V
  mem : ∀ j<a.count*16, e.mem (a.desc+BitVec.ofNat 64 j)=f.mem (a.desc+BitVec.ofNat 64 j)

variable {a d : LoopArgs} {e f s t u v : State} {i b c : Nat}

theorem LoopPublic.pos (p : LoopPublic a d e f) (hi : i≤a.count) : a.pos e i=d.pos f i := by
  simpa only [LoopArgs.pos,←p.desc] using gl_agree p.mem hi

theorem LoopPublic.base (p : LoopPublic a d e f) (hi : i<a.count) : a.base e i=d.base f i := by
  simpa only [LoopArgs.base,←p.desc] using sb_agree p.mem hi

theorem LoopPublic.len (p : LoopPublic a d e f) (hi : i<a.count) : a.len e i=d.len f i := by
  simpa only [LoopArgs.len,←p.desc] using sl_agree p.mem hi

theorem LoopPublic.hashed (p : LoopPublic a d e f) (hi : i≤a.count) : a.hashed e i=d.hashed f i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have lt : i<a.count := hi
    simp only [LoopArgs.hashed,p.pos (Nat.le_of_lt lt),p.len lt,ih (Nat.le_of_lt lt)]

theorem LoopPublic.atRegs (p : LoopPublic a d e f) (j : Nat) : SharedRegs (a.regs j) (d.regs j) :=
  ⟨p.regs.data,p.regs.rounds,p.regs.key,p.regs.state,p.regs.work⟩

def LoopArgs.skip (a : LoopArgs) (e : State) (i : Nat) :=
  if a.pos e i=0 then prefixLen (a.len e i) else 0

structure PieceStart (a : LoopArgs) (e : State) (i : Nat) (s : State) : Prop where
  env : Env (cursors (a.regs (i+1)) ((a.O+BitVec.ofNat 64 (a.pos e i))+BitVec.ofNat 64 (a.skip e i))) a.sp s
  ptr : s.gpr .r24=a.base e i+BitVec.ofNat 64 (a.skip e i)
  left : s.gpr .r25=BitVec.ofNat 64 (a.len e i-a.skip e i)

variable [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]

theorem prefix_wp (h : LoopInput a e) (prev : LoopAt a e i b s) (r : Read a e s i u) (hi : i<a.count) :
    WP isa (.ite (.zero .d .r11) bulk (.block [])) u (PieceStart a e i) := by
  have fit := Nat.lt_of_le_of_lt (gl_mono e.mem a.desc prev.idx) h.totalFit
  refine WP.ite (decide (a.pos e i=0)) (eval_zero r.offset fit) (fun yes => ?_) (fun no => ?_)
  · have z : a.pos e i=0 := by simpa using yes
    have env := r.env
    rw [z,add_ofNat_zero] at env
    have b0 : b=0 := by have bound := prev.hashLe; rw [z] at bound; omega_using [bound]
    have slot : u.mem.readW (a.sp+240) 64=0 := by rw [r.keeps.mem,prev.hashed,b0]; rfl
    exact WP.mono (bulk_wp env h.work h.state r.ptr r.left (e.mem.readW _ 64).isLt h.roundReg h.rounds
      ((prev.space h hi z).sub (Nat.le_refl _) r.keeps.rd r.keeps.wr) slot) fun _ q => by
        constructor
        · simpa only [LoopArgs.skip,z,ite_true,add_ofNat_zero] using q.env
        · simpa only [LoopArgs.skip,z,ite_true] using q.ptr
        · simpa only [LoopArgs.skip,z,ite_true] using q.left
  · have nz : a.pos e i≠0 := by simpa using no
    refine WP.block_nil ⟨?_,?_,?_⟩
    all_goals simp only [LoopArgs.skip,ite_eq_right nz,add_ofNat_zero,Nat.sub_zero]
    exact r.env
    exact r.ptr
    exact r.left

theorem iteration_rel (p : LoopPublic a d e f) (h : LoopInput a e) (g : LoopInput d f)
    (x : LoopAt a e i b s) (y : LoopAt d f i c t) (hi : i<a.count) :
    RelCT isa (Eq2 s t) (.seq (.block (next ++ ([.sub .r11 .r21 .r27] : List Instr))) (.seq (.ite (.zero .d .r11) bulk (.block [])) piece)) TT := by
  have hd : i<d.count := p.count ▸ hi
  have hsp := p.sp
  have dst := p.regs.data
  change a.O=d.O at dst
  have pos := p.pos x.idx
  have src := p.base hi
  have len := p.len hi
  have leftSp := x.env.sp.trans (p.sp.trans y.env.sp.symm)
  have reg : s.gpr .r19=t.gpr .r19 := by
    have a19 : s.gpr .r19=a.dp i := x.env.fr _ (by decide)
    have d19 : t.gpr .r19=d.dp i := y.env.fr _ (by decide)
    rw [a19,d19,LoopArgs.dp,LoopArgs.dp,p.desc]
  refine rel_seq (rel_taint [.r19] leftSp (by simpa using reg) (by taint_decide))
    (read_at h x hi) (read_at g y hd) (fun u v r q => ?_)
  have fit := Nat.lt_of_le_of_lt (gl_mono e.mem a.desc x.idx) h.totalFit
  have eqeval := eval_zero q.offset (Nat.lt_of_le_of_lt (gl_mono f.mem d.desc y.idx) g.totalFit)
  rw [←pos] at eqeval
  refine rel_seq (rel_ite (eval_zero r.offset fit) eqeval (fun yes => ?_) (fun _ => ?_))
    (prefix_wp h x r hi) (prefix_wp g y q hd) (fun u v l m => ?_)
  · have z : a.pos e i=0 := by simpa using yes
    have z' := pos.symm.trans z
    have en := r.env
    have en' := q.env
    rw [z,add_ofNat_zero] at en
    rw [z',add_ofNat_zero,←dst,←hsp] at en'
    have space := (y.space g hd z').sub (Nat.le_refl _) q.keeps.rd q.keeps.wr
    rw [←hsp,←dst,←len,←src] at space
    exact bulk_rel (p.atRegs (i+1)) en en' h.work h.state r.ptr (q.ptr.trans src.symm) r.left
      (by rw [q.left,len]) (e.mem.readW _ 64).isLt h.roundReg h.rounds
      ((x.space h hi z).sub (Nat.le_refl _) r.keeps.rd r.keeps.wr) space
  · exact rel_taint [] (r.env.sp.trans (hsp.trans q.env.sp.symm)) (by simp) (by taint_decide)
  · have skip : a.skip e i=d.skip f i := by simp only [LoopArgs.skip,pos,len]
    have en := m.env
    rw [←hsp,←dst,←pos,←skip] at en
    exact piece_rel (l.env.sp.trans en.sp.symm) (addresses_agree (p.atRegs _) l.env en
      (by rw [l.ptr,m.ptr,src,skip]) (by rw [l.left,m.left,len,skip]))

theorem pieces_rel (p : LoopPublic a d e f) (h : LoopInput a e) (g : LoopInput d f)
    (x : LoopAt a e 0 0 s) (y : LoopAt d f 0 0 t) : RelCT isa (Eq2 s t) pieces TT := by
  have fit := h.countFit
  have r18 : s.gpr .r18=BitVec.ofNat 64 a.count := x.env.fr _ (by decide)
  have l18 : t.gpr .r18=BitVec.ofNat 64 d.count := y.env.fr _ (by decide)
  rw [←p.count] at l18
  refine rel_ite (eval_zero r18 (by omega_using [fit])) (eval_zero l18 (by omega_using [fit]))
    (fun _ => by exact rel_taint [] (x.env.sp.trans (p.sp.trans y.env.sp.symm)) (by simp) (by taint_decide)) (fun nonempty => ?_)
  have nz : a.count≠0 := by simpa using nonempty
  refine (RelCT.loop (Q := TT) (fun m u v => ∃ i, m=a.count-i ∧ i<a.count ∧
      LoopAt a e i (a.hashed e i) u ∧ LoopAt d f i (d.hashed f i) v) (fun m => ?_) a.count).mono
    (fun u v ⟨hu,hv⟩ => by subst u v; exact ⟨0,rfl,Nat.pos_of_ne_zero nz,x,y⟩) fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases bounds : m=a.count-i ∧ i<a.count
  · obtain ⟨rfl,hi⟩ := bounds
    have step : RelCT isa (fun u v => LoopAt a e i (a.hashed e i) u ∧ LoopAt d f i (d.hashed f i) v)
        (.seq (.block (next ++ ([.sub .r11 .r21 .r27] : List Instr))) (.seq (.ite (.zero .d .r11) bulk (.block [])) piece)) TT :=
      fun u v _ _ _ _ q => iteration_rel p h g q.1 q.2 hi u v _ _ _ _ ⟨rfl,rfl⟩
    refine (step.wp fun _ _ q => ⟨iteration_wp h q.1 hi,iteration_wp g q.2 (p.count ▸ hi)⟩).mono
      (fun _ _ q => q.2.2) ?_
    rintro u v ⟨_,l,r⟩
    have l18 : u.gpr .r18=BitVec.ofNat 64 (a.count-(i+1)) := l.env.fr _ (by decide)
    have r18 : v.gpr .r18=BitVec.ofNat 64 (d.count-(i+1)) := r.env.fr _ (by decide)
    rw [←p.count] at r18
    have left := VG.Proof.Gather.PPC64LE.eval_nonzero l18 (by omega_using [fit])
    have right := VG.Proof.Gather.PPC64LE.eval_nonzero r18 (by omega_using [fit])
    refine ⟨by rw [left,right],fun _ => trivial,fun again => ?_⟩
    rw [left] at again
    have lt : i+1<a.count := by simp at again; omega_using [again]
    exact ⟨a.count-(i+1),by omega_using [hi],i+1,rfl,lt,l,r⟩
  · exact RelCT.of_false fun _ _ q => bounds ⟨q.1,q.2.1⟩

end VG.Proof.AesGcm.PPC64LE.DirectGather
