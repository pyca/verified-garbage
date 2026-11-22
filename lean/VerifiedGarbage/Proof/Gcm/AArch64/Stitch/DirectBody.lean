module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GeneralFrame
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericStream
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectGeneral
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GeneralSetup
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericLoop
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem

/-! Public gather layout viewed as the work, key, descriptor and buffer
regions used by the AArch64 descriptor loop. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather
open VG VG.AArch64
open VG.Proof.AesGcm.AArch64

abbrev genState (o : State) (wn : Nat) := genWork o wn + BitVec.ofNat 64 16

theorem genWork_sub (o : State) {wn : Nat} (hw : wn ≤ 2560) :
    Region.Sub ⟨genWork o wn,wn⟩ (Gather.stkR o) :=
  fun x hx => genStack_sub o hw x (Offset.sub_base (genBase o wn) (d := 32) (by change 32+wn ≤ wn+32; omega) x hx)

theorem genState_sub (o : State) {wn : Nat} (hw : 768 ≤ wn) :
    Region.Sub ⟨genState o wn,80⟩ ⟨genWork o wn,wn⟩ := Lay.wSub (by omega)

theorem genLay {o s : State} {wn : Nat} (e : GeneralEntry o s wn) (hwn : 768 ≤ wn) :
    Lay wn (Gather.K o) (genState o wn) (genWork o wn) := by
  have b := e.bound
  have sep := e.lay.bk.symm.sub_right (genWork_sub o b)
  have wsp := e.lay.w₁
  have hbase : (genBase o wn).toNat + wn + 32 ≤ 2^64 := by
    unfold genBase
    rw [BitVec.toNat_sub,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a := wn+32) (by omega)]
    have := o.sp.isLt
    omega
  have ww : (genWork o wn).toNat + wn ≤ 2^64 := by
    unfold genWork
    rw [BitVec.toNat_add]; have := (genBase o wn).isLt
    change ((genBase o wn).toNat + 32) % 2^64 + wn ≤ 2^64
    omega
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_⟩ := e.lay.pre
  refine ⟨⟨hwn,b⟩,wc,?_,ww,sep.sub_right (genState_sub o hwn),sep,?_,?_⟩
  · unfold genState; rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a := 16) (by decide)]
    have := (genWork o wn).isLt; omega
  · simpa using Offset.disjoint (genWork o wn)
      (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
  · exact Offset.disjoint (genWork o wn) (.inl (by decide)) (by decide) (by omega)

/-- Before any ciphertext writes, all bytes in external regions still
come from the entry of the public API. -/
theorem inputsAgree {o t : State} (L : Gather.Lay .plain o) (f : Frame [Gather.stkR o] o.mem t.mem) :
    ∀ r ∈ Sig.descRegion 64 (Gather.Src o) (Gather.Cnt o) :: Gather.lsR o, ∀ x, r.Contains x 1 → o.mem x = t.mem x := by
  intro r hr x hx
  symm
  refine f x fun q hq hqc => ?_
  simp only [List.mem_singleton] at hq; subst q
  rcases List.mem_cons.mp hr with rfl | listed
  · apply L.bds x hqc
    simpa only [Gather.dsR,Sig.descRegion,Nat.reduceDiv,Nat.reduceMul] using hx
  · exact L.bl _ listed x hqc hx

structure PublicBuffers (wn : Nat) (o t : State) : Prop where
  nonce : DataOk wn (genState o wn) (genWork o wn) t (Gather.Nn o) (Gather.NL o)
  aad : DataOk wn (genState o wn) (genWork o wn) t (Gather.Ad o) (Gather.AL o)
  dst : DataW wn (Gather.K o) (genState o wn) (genWork o wn) t (Gather.Dst o) (Gather.L o)
  desc : DataOk wn (genState o wn) (genWork o wn) t (Gather.Src o) (16*Gather.Cnt o)
  apart : (⟨Gather.Src o,16*Gather.Cnt o⟩ : Region).Disjoint ⟨Gather.Dst o,Gather.L o⟩
  src : ∀ i < Gather.Cnt o, DataOk wn (genState o wn) (genWork o wn) t (Gather.sb t.mem (Gather.Src o) i)
    (Gather.sl t.mem (Gather.Src o) i)
  srcApart : ∀ i < Gather.Cnt o, (⟨Gather.sb t.mem (Gather.Src o) i,Gather.sl t.mem (Gather.Src o) i⟩ : Region).Disjoint
    ⟨Gather.Dst o,Gather.L o⟩

theorem buffers_of {o s t : State} {wn : Nat} (e : GeneralEntry o s wn) (hwn : 768 ≤ wn)
    (fr : Frame [Gather.stkR o] o.mem t.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : PublicBuffers wn o t := by
  obtain ⟨rdo,wro,kd,_,_,_,_,_,dsd,_,lsd,_,_,_,_,_,_,_,_,_,_,_,_,wnon,waad,wdesc,wsrc,wd,_⟩ := e.lay.pre
  have Wsub := genWork_sub o e.bound
  have Ssub := genState_sub o hwn
  have read (r : Region) (hr : r ∈ o.rd) := covers_of_mem (List.mem_append_left t.wr
    (show r ∈ t.rd by rw [rd,e.rd]; exact hr))
  have out := covers_of_mem (show Gather.dR o ∈ t.wr by rw [wr,e.wr,wro]; simp)
  have ok (r : Region) (hr : r ∈ o.rd) (lt : r.len < 2^64) (ww : r.base.toNat + r.len ≤ 2^64)
      (apart : (Gather.stkR o).Disjoint r) : DataOk wn (genState o wn) (genWork o wn) t r.base r.len :=
    ⟨read r hr,lt,ww,(apart.symm.sub_right Wsub).sub_right Ssub,apart.symm.sub_right Wsub⟩
  have listed := (Proof.AesGcm.listed_congr_le (Nat.le_refl _) (inputsAgree e.lay fr)).1
  have dlt : (Gather.dsR o).len < 2^64 := by
    have dis := e.lay.bds (Gather.Bs o)
      (show (Gather.stkR o).Contains (Gather.Bs o) 1 from by simp [Gather.Bs,Region.Contains])
    have := (Gather.Bs o - Gather.Src o).isLt
    change ¬ (Gather.Bs o - Gather.Src o).toNat + 1 ≤ _ at dis
    omega
  refine ⟨ok (Gather.nR o) (by rw [rdo]; simp) (o.gpr .x3).isLt wnon e.lay.bn,
    ok (Gather.aR o) (by rw [rdo]; simp) (o.gpr .x5).isLt waad e.lay.ba,
    ⟨⟨covers_left out,(stackArg o 1).isLt,wd,(e.lay.bd.symm.sub_right Wsub).sub_right Ssub,
      e.lay.bd.symm.sub_right Wsub⟩,out,kd⟩,
    by simpa only [Nat.mul_comm] using ok (Gather.dsR o) (by rw [rdo]; simp) dlt wdesc e.lay.bds,
    by simpa only [Gather.dsR,Nat.mul_comm] using dsd, ?_, ?_⟩
  · intro i hi
    have hr := Gather.slice_mem t.mem (Gather.Src o) hi
    rw [listed] at hr
    exact ok _ (by rw [rdo]; simp [hr]) (t.mem.readW _ 64).isLt (wsrc _ hr) (e.lay.bl _ hr)
  · intro i hi
    have hr := Gather.slice_mem t.mem (Gather.Src o) hi
    rw [listed] at hr
    exact (lsd _ hr).1

end VG.Proof.AesGcm.AArch64.DirectGather

/-! The general descriptor path meets the public gather contract with
the original caller's plaintext, key, nonce, AAD and output locations. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64 (mov imm dataO)
open VG.Impl.AesGcm.AArch64.DirectGather (hashO countO descO)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt blocksAt)
open VG.Proof.Gcm.AArch64.Stitch (GatherLaws)

abbrev textSetup : List Instr := [.ldr .x .x27 .x19 descO,.ldr .x .x28 .x19 countO,.ldr .x .x26 .x19 dataO,
  .str .x .x26 .x19 hashO,imm .x25 0]

structure TextSetupPost (s u : State) (W S D : Addr) (n : Nat) : Prop where
  x25 : u.gpr .x25 = 0
  x26 : u.gpr .x26 = D
  x27 : u.gpr .x27 = S
  x28 : u.gpr .x28 = BitVec.ofNat 64 n
  ptr : u.mem.readW (W+352) 64 = D
  mem : Frame [⟨W+352,8⟩] s.mem u.mem
  gpr : Others [.x27,.x28,.x26,.x25] s u
  sp : u.sp = s.sp
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem textSetup_ok {wn n : Nat} {Ctx St W SP S D : Addr} {s : State} (he : Env wn Ctx St W SP s)
    (desc : s.mem.readW (W+336) 64 = S) (count : s.mem.readW (W+344) 64 = BitVec.ofNat 64 n)
    (dst : s.mem.readW (W+232) 64 = D) : WP isa (.block textSetup) s (fun u => TextSetupPost s u W S D n) := by
  have r (d : Nat) (h : d+8 ≤ 512) := he.perm.wR h
  have w := he.perm.wW (d := 352) (n := 8) (by decide)
  have s1 : s.mem.read (W+336#64) 8 = S := desc
  have s2 : s.mem.read (W+344#64) 8 = BitVec.ofNat 64 n := count
  have s3 : s.mem.read (W+232#64) 8 = D := dst
  have r1 := r 336 (by decide)
  have r2 := r 344 (by decide)
  have r3 := r 232 (by decide)
  refine WP.of_runBlock ⟨_,by arun [textSetup,descO,countO,hashO,he.x19,r1,r2,r3,w],?_⟩
  refine ⟨by simp [gpr_write],by simp [gpr_write,s3],by simp [gpr_write,s1],by simp [gpr_write,s2],?_,?_,
    by others_tac,rfl,rfl,rfl⟩
  · change (s.mem.writeW (W+352) (s.mem.read (W+232#64) 8)).readW (W+352) 64 = _
    rw [s3,Mem.readW_writeW_self64]
  · change Frame [⟨W+352,8⟩] s.mem (s.mem.writeW (W+352) (s.mem.read (W+232#64) 8))
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) (s.mem.read (W+232#64) 8) (Region.contains_self _ _)

abbrev afterFrame (wn : Nat) (W D : Addr) (n : Nat) : List Region :=
  [⟨W+BitVec.ofNat 64 32,96⟩,⟨W+BitVec.ofNat 64 352,wn-352⟩,⟨D,n⟩]

private theorem lowSub (W : Addr) {d n : Nat} (hd : 32 ≤ d) (hn : d+n ≤ 128) :
    Region.Sub ⟨W+BitVec.ofNat 64 d,n⟩ ⟨W+BitVec.ofNat 64 32,96⟩ := Offset.sub _ hd (by omega)

private theorem frameText {wn n : Nat} {W D : Addr} {m m' : Mem} (hw : 768 ≤ wn)
    (f : Frame [⟨D,n⟩,⟨(W+BitVec.ofNat 64 16)+BitVec.ofNat 64 16,16⟩,
      ⟨(W+BitVec.ofNat 64 16)+BitVec.ofNat 64 48,32⟩,⟨W+BitVec.ofNat 64 352,8⟩,
      ⟨W+BitVec.ofNat 64 512,wn-512⟩] m m') : Frame (afterFrame wn W D n) m m' := by
  refine f.sub fun r hr => ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false,Offset.add_add] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact ⟨⟨D,n⟩,by simp [afterFrame],fun _ h => h⟩
  · exact ⟨_,List.mem_cons_self ..,lowSub _ (by decide) (by decide)⟩
  · exact ⟨_,List.mem_cons_self ..,lowSub _ (by decide) (by decide)⟩
  · exact ⟨⟨W+BitVec.ofNat 64 352,wn-352⟩,by simp [afterFrame],Region.sub_prefix (by omega)⟩
  · exact ⟨⟨W+BitVec.ofNat 64 352,wn-352⟩,by simp [afterFrame],Offset.sub _ (by decide) (by omega)⟩

private theorem frameTail {wn n : Nat} {W D : Addr} {m m' : Mem} (hw : 768 ≤ wn)
    (f : Frame (tailFrame (W+BitVec.ofNat 64 16) W) m m') : Frame (afterFrame wn W D n) m m' := by
  refine f.sub fun r hr => ?_
  simp only [tailFrame,absFrame,tFrame,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false,
    Offset.add_add] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> first
    | exact ⟨_,List.mem_cons_self ..,lowSub _ (by decide) (by decide)⟩
    | exact ⟨⟨W+BitVec.ofNat 64 352,wn-352⟩,by simp [afterFrame],Offset.sub _ (by decide) (by omega)⟩

private theorem preservedAfter {wn n d k : Nat} {W D : Addr} (hw : 768 ≤ wn ∧ wn ≤ 2560)
    (dd : (⟨D,n⟩ : Region).Disjoint ⟨W,wn⟩) (lo : d+k ≤ 32 ∨ 128 ≤ d) (hi : d+k ≤ 352) :
    ∀ r ∈ afterFrame wn W D n, (⟨W+BitVec.ofNat 64 d,k⟩ : Region).Disjoint r := by
  intro r hr; simp only [afterFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact Offset.disjoint _ lo (by omega) (by decide)
  · exact Offset.disjoint _ (.inl hi) (by omega) (by omega)
  · exact dd.symm.sub_left (Lay.wSub (by omega))

private theorem separateAfter {wn n : Nat} {W D : Addr} {X : Region} (hw : 768 ≤ wn)
    (w : X.Disjoint ⟨W,wn⟩) (d : X.Disjoint ⟨D,n⟩) : ∀ r ∈ afterFrame wn W D n, X.Disjoint r := by
  intro r hr; simp only [afterFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact w.sub_right (Lay.wSub (by omega))
  · exact w.sub_right (Lay.wSub (by omega))
  · exact d

private theorem seq4 {a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (p : WP isa (.seq a (.seq b (.seq c d))) s (fun t => WP isa e t Q)) :
    WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp p) fun _ q => WP.seq
    (WP.mono (WP.seq_iff.mp q) fun _ u => WP.seq (WP.mono (WP.seq_iff.mp u) fun _ => WP.seq)))


abbrev generalIv (o : State) := bytesAt o.mem (Gather.Nn o) (Gather.NL o)
abbrev generalAad (o : State) := bytesAt o.mem (Gather.Ad o) (Gather.AL o)
abbrev generalH (o : State) := Spec.Gcm.ctxH o.mem (Gather.K o)
abbrev generalArgs (o s : State) (wn : Nat) : Generic.TextArgs :=
  ⟨wn,Gather.K o,genState o wn,genWork o wn,s.sp,(o.gpr .x1).toNat,
    Spec.Gcm.inc32 (Spec.Gcm.j0 (generalH o) (generalIv o)),Gather.Src o,Gather.Cnt o,Gather.Dst o⟩

abbrev GeneralAadReady (o s : State) (wn : Nat) (a b : State) :=
  AadReady wn (Gather.K o) (genState o wn) (genWork o wn) s.sp (generalH o) (generalIv o) (generalAad o) a b
abbrev GeneralTextSetup (o : State) (wn : Nat) (b c : State) :=
  TextSetupPost b c (genWork o wn) (Gather.Src o) (Gather.Dst o) (Gather.Cnt o)

theorem generalPiecesPre {o s a b c : State} {wn : Nat} (e : GeneralEntry o s wn) (hw : 768 ≤ wn)
    (st : BodyEntry o s wn a) (ready : GeneralAadReady o s wn a b) (set : GeneralTextSetup o wn b c) :
    Generic.PiecesPre (generalArgs o s wn) c ∧ (generalArgs o s wn).total c = Gather.L o ∧
      Frame [Gather.stkR o] o.mem c.mem := by
  let W := genWork o wn
  let St := genState o wn
  let n := Gather.L o
  let R := (o.gpr .x1).toNat
  let args := generalArgs o s wn
  have hi := e.bound
  have L := genLay e hw
  have rounds := e.lay.hR
  have wsp : Region.Sub ⟨W,wn⟩ (Gather.stkR o) := genWork_sub o hi
  have expand {u u' : State} (f : Frame [⟨W,wn⟩] u.mem u'.mem) : Frame [Gather.stkR o] u.mem u'.mem :=
    f.sub fun r hr => ⟨_,List.mem_singleton_self _,List.mem_singleton.mp hr ▸ wsp⟩
  have F₀ : Frame [Gather.stkR o] o.mem s.mem := e.frame.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,fun x hx => genStack_sub o hi x (Region.sub_prefix (by omega : 32 ≤ wn+32) x hx)⟩
  have Fa := F₀.trans (expand st.frame)
  have f₁ : Frame (generalScratch wn W) a.mem b.mem := scratchFrame_Aad ready.frame hw
  have Fb := Fa.trans (expand (scratchFrame_work f₁ hw))
  have fc : Frame [⟨W,wn⟩] b.mem c.mem := set.mem.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,Lay.wSub (d := 352) (by omega)⟩
  have Fc := Fb.trans (expand fc)
  have rd := set.rd.trans (ready.rd.trans st.rd)
  have wr := set.wr.trans (ready.wr.trans st.wr)
  have bufs := buffers_of e hw Fc rd wr
  have agree := inputsAgree e.lay Fc
  have total : args.total c = n := (Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) agree).trans e.lay.hgl
  have hSt (d l : Nat) (hl : d+l ≤ 80) : ∀ q ∈ [⟨W+352,8⟩],
      (⟨St+BitVec.ofNat 64 d,l⟩ : Region).Disjoint q := by
    intro q hq; obtain rfl := List.mem_singleton.mp hq
    exact L.st_w hl (.inr ⟨by decide,by decide⟩)
  have x22 : c.gpr .x22 = BitVec.ofNat 64 R := by
    rw [set.gpr _ (by decide),ready.x22,st.x22]; simp [R]
  have pr : Generic.PiecesPre args c :=
    ⟨L,ready.env.keep (fun j hj => set.gpr _ (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        rcases hj with rfl|rfl|rfl <;> decide)) set.sp set.rd set.wr,rounds,x22,
      set.x25,set.x26,set.x27,set.x28,bufs.desc.lt,bufs.desc,total ▸ bufs.dst,total ▸ bufs.apart,bufs.src,
      total ▸ bufs.srcApart, Proof.Gcm.ctr_zero _ _ _ _ ((blockAt_frame set.mem (hSt 48 16 (by decide))).trans ready.cb),
      set.ptr⟩
  exact ⟨pr,total,Fc⟩


/-- Slots holding public arguments survive the descriptor loop and the final hash flush. -/
theorem generalFinSlot {o s a b c t u : State} {wn j d : Nat} (e : GeneralEntry o s wn)
    (hw : 768 ≤ wn) (ready : GeneralAadReady o s wn a b) (set : GeneralTextSetup o wn b c)
    (total : (generalArgs o s wn).total c = Gather.L o)
    (p : Generic.TextAt (generalArgs o s wn) c (Gather.Cnt o) j t)
    (tail : Frame (tailFrame (genState o wn) (genWork o wn)) t.mem u.mem)
    (lo : 128 ≤ d) (le : d+8 ≤ 352) :
    u.mem.readW (genWork o wn+BitVec.ofNat 64 d) 64 = a.mem.readW (genWork o wn+BitVec.ofNat 64 d) 64 := by
  let W := genWork o wn
  let O := Gather.Dst o
  let n := Gather.L o
  have nEq : (generalArgs o s wn).total c = n := total
  have textF : Frame (afterFrame wn W O n) c.mem t.mem := nEq ▸ frameText hw p.frame
  have initF : Frame (afterFrame wn W O n) b.mem c.mem := set.mem.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨W+BitVec.ofNat 64 352,wn-352⟩,by simp [afterFrame],Region.sub_prefix (by omega)⟩
  have F := (initF.trans textF).trans (frameTail hw tail)
  have dis := e.lay.bd.symm.sub_right (genWork_sub o e.bound)
  exact (F.readW (Region.contains_self _ _)
    (preservedAfter ⟨hw,e.bound⟩ dis (.inr lo) le) (by decide)).trans
    (scratch_slot (scratchFrame_Aad ready.frame hw) e.bound lo (by omega))


theorem generalTail_ok {o s a b c t : State} {wn j : Nat} (v : GcmImpl) (e : GeneralEntry o s wn) (hw : 768 ≤ wn)
    (st : BodyEntry o s wn a) (ready : GeneralAadReady o s wn a b) (set : GeneralTextSetup o wn b c)
    (p : Generic.TextAt (generalArgs o s wn) c (Gather.Cnt o) j t) :
    WP isa (tailCode v.callees) t fun u =>
      Env wn (Gather.K o) (genState o wn) (genWork o wn) s.sp u ∧ u.gpr .x22 = t.gpr .x22 ∧
      blockAt u.mem (genState o wn+16) = Spec.Gcm.ghash (generalH o)
        (Spec.Gcm.blocks (Proof.Gcm.padded (generalAad o) (bytesAt t.mem (Gather.Dst o) (Gather.L o)))) ∧
      Frame (tailFrame (genState o wn) (genWork o wn)) t.mem u.mem ∧ u.rd = t.rd ∧ u.wr = t.wr := by
  let C := Gather.K o
  let W := genWork o wn
  let St := genState o wn
  let O := Gather.Dst o
  let n := Gather.L o
  let H := Spec.Gcm.ctxH o.mem C
  let aad := bytesAt o.mem (Gather.Ad o) (Gather.AL o)
  let args := generalArgs o s wn

  have L := genLay e hw
  obtain ⟨pr,hlen,Fc⟩ := generalPiecesPre e hw st ready set
  have total : args.total c = n := hlen
  have kC : Spec.Gcm.ctxH c.mem C = H := blockAt_frame Fc fun r hr =>
    List.mem_singleton.mp hr ▸ e.lay.bk.symm.sub_left (Lay.ctxSub (by decide))
  have textF : Frame (afterFrame wn W O n) c.mem t.mem := total ▸ frameText hw p.frame
  have kg := separateAfter hw (e.lay.bk.symm.sub_right (genWork_sub o e.bound)) e.lay.pre.2.2.1
  have kT : Spec.Gcm.ctxH t.mem C = H :=
    (blockAt_frame textF (fun r hr => (kg r hr).sub_left (Lay.ctxSub (by decide)))).trans kC
  have hSt (d l : Nat) (hl : d+l ≤ 80) : ∀ q ∈ [⟨W+352,8⟩],
      (⟨St+BitVec.ofNat 64 d,l⟩ : Region).Disjoint q := by
    intro q hq; obtain rfl := List.mem_singleton.mp hq
    exact L.st_w hl (.inr ⟨by decide,by decide⟩)
  have modY : blockAt t.mem (St+16) = Spec.Gcm.ghashFrom H (Spec.Gcm.ghash H (Spec.Gcm.blocks (aadPad aad)))
      (blocksAt t.mem O j) := by
    have eqY := (blockAt_frame set.mem (hSt 16 16 (by decide))).trans ready.hash
    exact (p.y.trans (by rw [show Spec.Gcm.ctxH c.mem args.Ctx = H from kC,
      show blockAt c.mem (args.St+16) = _ from eqY]))
  have dslot : t.mem.readW (W+352) 64 = O+BitVec.ofNat 64 (16*j) := p.hashPtr
  have d26 : t.gpr .x26 = O+BitVec.ofNat 64 n := total ▸ p.dst
  have hbound : 16*j ≤ n := total ▸ p.hashBound

  have data : DataOk wn St W c O n := total ▸ pr.dst.ok
  exact tailCode_ok v L p.env (data.of_eq p.rd p.wr) hbound d26 dslot kT modY

theorem generalBody_ok {o s : State} {wn : Nat} (v : GcmImpl) (stitch : Bool) (e : GeneralEntry o s wn)
    (hw : 768 ≤ wn) (hv : v.ctr.scratch ≤ wn-512) (gh : stitch = true → GatherLaws) :
    WP isa (Impl.AesGcm.AArch64.DirectGather.body v.callees stitch) s
      (fun t => Gather.gatherPost o t ∧ GprAbi s t) := by
  let C := Gather.K o
  let W := genWork o wn
  let St := genState o wn
  let O := Gather.Dst o
  let n := Gather.L o
  let R := (o.gpr .x1).toNat
  let cnt := Gather.Cnt o
  let H := Spec.Gcm.ctxH o.mem C
  let iv := bytesAt o.mem (Gather.Nn o) (Gather.NL o)
  let aad := bytesAt o.mem (Gather.Ad o) (Gather.AL o)
  let J := Spec.Gcm.j0 H iv
  let args := generalArgs o s wn
  have hi := e.bound
  have L := genLay e hw
  have rounds := e.lay.hR
  have wsp : Region.Sub ⟨W,wn⟩ (Gather.stkR o) := genWork_sub o hi
  have expand {u u' : State} (f : Frame [⟨W,wn⟩] u.mem u'.mem) : Frame [Gather.stkR o] u.mem u'.mem :=
    f.sub fun r hr => ⟨_,List.mem_singleton_self _,List.mem_singleton.mp hr ▸ wsp⟩
  have F₀ : Frame [Gather.stkR o] o.mem s.mem := e.frame.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,fun x hx => genStack_sub o hi x (Region.sub_prefix (by omega : 32 ≤ wn+32) x hx)⟩
  have apart {r : Region} (hr : (Gather.stkR o).Disjoint r) : ∀ q ∈ [Gather.stkR o], r.Disjoint q :=
    fun q hq => List.mem_singleton.mp hq ▸ hr.symm
  refine WP.seq (WP.mono (generalSetup_ok e hw) fun a st => ?_)
  have Fa := F₀.trans (expand st.frame)
  have ba := buffers_of e hw Fa st.rd st.wr
  have sameH {u : State} (f : Frame [Gather.stkR o] o.mem u.mem) : Spec.Gcm.ctxH u.mem C = H :=
    blockAt_frame f fun r hr => (apart e.lay.bk r hr).sub_left (Lay.ctxSub (by decide))
  have ivA : bytesAt a.mem (Gather.Nn o) (Gather.NL o) = iv := bytesAt_frame Fa (apart e.lay.bn) (Nat.le_of_lt (o.gpr .x3).isLt)
  have aadA : bytesAt a.mem (Gather.Ad o) (Gather.AL o) = aad := bytesAt_frame Fa (apart e.lay.ba) (Nat.le_of_lt (o.gpr .x5).isLt)
  refine aadReady_ok L v st.env st.x23 (by simpa using st.x24) (by simpa using st.x26) st.x27 ba.nonce ba.aad
    (sameH Fa) st.aad (by simpa using st.alen) fun b ready => ?_
  rw [ivA,aadA] at ready
  have f₁ : Frame (generalScratch wn W) a.mem b.mem := scratchFrame_Aad ready.frame hw
  have Fb := Fa.trans (expand (scratchFrame_work f₁ hw))
  have slotsB (d : Nat) (lo : 128 ≤ d) (le : d+8 ≤ 512) := scratch_slot f₁ hi lo le
  refine WP.seq (WP.seq (WP.mono (textSetup_ok ready.env ((slotsB 336 (by decide) (by decide)).trans st.desc)
    ((slotsB 344 (by decide) (by decide)).trans st.count) ((slotsB 232 (by decide) (by decide)).trans st.dst))
    fun c set => ?_))
  obtain ⟨pr,hlen,Fc⟩ := generalPiecesPre e hw st ready set
  have total : args.total c = n := hlen
  have rd := set.rd.trans (ready.rd.trans st.rd)
  have wr := set.wr.trans (ready.wr.trans st.wr)
  have bufs := buffers_of e hw Fc rd wr
  have agree := inputsAgree e.lay Fc
  have pt : args.pt c args.count = Gather.pt o cnt := Proof.AesGcm.gathered_congr_le (Nat.le_refl _) agree
  refine WP.mono (Generic.pieces_ok v stitch pr hv gh) fun t ⟨j,p⟩ => ?_
  have textF : Frame (afterFrame wn W O n) c.mem t.mem := total ▸ frameText hw p.frame
  have initF : Frame (afterFrame wn W O n) b.mem c.mem := set.mem.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨W+BitVec.ofNat 64 352,wn-352⟩,by simp [afterFrame],Region.sub_prefix (by omega)⟩
  have past := initF.trans textF
  have destW := bufs.dst.ok.w
  have keyW := e.lay.bk.symm.sub_right wsp
  have keyD := e.lay.pre.2.2.1
  have kg : ∀ r ∈ afterFrame wn W O n, (⟨C,256⟩ : Region).Disjoint r := separateAfter hw keyW keyD
  have ctxCipher := ciph_frame Fc (apart e.lay.bk) rounds
  have encrypt : bytesAt t.mem O n = Spec.Gcm.gctr (Spec.Gcm.ctxCiph o.mem C R) (Spec.Gcm.inc32 J) (Gather.pt o cnt) := by
    rw [← total,p.out,pt,Proof.Gcm.gctr_eq]
    change Proof.Gcm.xorKs (ciphOf c.mem C R) _ _ _ = _
    rw [ctxCipher]; rfl
  refine seq4 (e := finalCode v.callees) (WP.mono (generalTail_ok v e hw st ready set p)
    fun u ⟨en,x22',yy,fu,ru,wu⟩ => ?_)
  have F := past.trans (frameTail hw fu)
  have aadlen : aad.length = Gather.AL o := length_bytesAt _ _ _
  have Clen : (bytesAt t.mem O n).length = n := length_bytesAt _ _ _
  have eqOutput : bytesAt u.mem O n = bytesAt t.mem O n := bytesAt_frame
    (scratchFrame_work (scratchFrame_tail fu hw) hw) (fun r hr => List.mem_singleton.mp hr ▸ destW)
    (Nat.le_of_lt (stackArg o 1).isLt)
  have saved := (st.saved.frame f₁ (protected_scratch hi (by decide) (by decide))).frame F
    (preservedAfter ⟨hw,hi⟩ destW (.inr (by decide)) (by decide))
  have slotsU (d : Nat) (lo : 128 ≤ d) (le : d+8 ≤ 352) : u.mem.readW (W+BitVec.ofNat 64 d) 64 =
      a.mem.readW (W+BitVec.ofNat 64 d) 64 := generalFinSlot e hw ready set total p fu lo le
  have ciphU : ciphOf u.mem C R = Spec.Gcm.ctxCiph o.mem C R :=
    (ciph_frame F kg rounds).trans (ciph_frame Fb (apart e.lay.bk) rounds)
  have keyU : Spec.Gcm.ctxH u.mem C = H :=
    (blockAt_frame F (fun r hr => (kg r hr).sub_left (Lay.ctxSub (by decide)))).trans (sameH Fb)
  have jj : blockAt u.mem St = J := (blockAt_frame F
    (preservedAfter ⟨hw,hi⟩ destW (.inl (by decide : 16+16 ≤ 32)) (by decide))).trans ready.j0
  have tagW := e.lay.bt.symm.sub_right wsp
  obtain ⟨_,outWr,_,_,_,_,_,_,_,_,_,dt,_⟩ := e.lay.pre
  have cover : Covers [⟨Gather.Tg o,16⟩] u.wr := covers_of_mem (by rw [wu,p.wr,wr,e.wr,outWr]; simp [Gather.tgR])
  have h22u := x22'.trans p.x22
  refine WP.mono (finalCode_ok (O := O) v L en h22u rounds (by simp)
    (aad := aad) (cipher := bytesAt t.mem O n) (by rw [aadlen]; simpa using (slotsU 224 (by decide) (by decide)).trans st.alen)
    (by rw [Clen]; exact (slotsU 240 (by decide) (by decide)).trans st.len)
    ((slotsU 248 (by decide) (by decide)).trans st.tag) saved cover tagW (by rw [Clen]; exact destW)
    (by rw [Clen]; exact dt) (aadlen ▸ (o.gpr .x5).isLt) (by rw [Clen]; exact (stackArg o 1).isLt) (by rw [Clen]; exact eqOutput) keyU jj yy hv)
    fun z ⟨abi,data,tag⟩ => ?_
  refine ⟨?_,abi⟩
  rw [Clen,encrypt] at data
  rw [Clen,encrypt,ciphU] at tag
  change Spec.Gcm.encryptWith _ _ 16 iv (Gather.pt o cnt) aad = (bytesAt z.mem O n,_)
  rw [data,tag,Spec.Gcm.encryptWith,Proof.Gcm.fullTag_eq,List.take_of_length_le (by rw [Proof.Cmac.toBytes_length])]
  have outlen : (Spec.Gcm.gctr (Spec.Gcm.ctxCiph o.mem C R) (Spec.Gcm.inc32 J) (Gather.pt o cnt)).length = n := by rw [← encrypt, Clen]
  rw [outlen]

end VG.Proof.AesGcm.AArch64.DirectGather
