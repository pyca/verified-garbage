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
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
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
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.AesGcm.AArch64.Env

/-! Compute the tag mask and keystream with one round-key load per batch. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.CounterBatch
open VG VG.AArch64
open VG.Impl.AesGcm.AArch64.DirectGather.CounterBatch (lane lanes storeLane countCode step finish kernel)
open VG.Proof.Aes.AArch64.Aese
open VG.Proof.AesGcm.AArch64.DirectGather.Counters (blockAddr seedRegs countWord)

open VG.Proof.Gcm.AArch64.Stitch (sch)
open VG.Proof.AesGcm.AArch64.DirectGather.Counters (CanLoadKeys)
open VG.Spec.Aes (roundKey)
open VG.AArch64.RegUpd

/-- Progress of the counter lanes through the public number of AES rounds. -/
structure RoundState (n nr : Nat) (o : State) (x : VReg → Spec.Aes.State) (i : Nat) (s : State) : Prop where
  frame : Fr [.x9,.x10] (.v30 :: lanes n) o s
  cursor : s.gpr .x9 = o.gpr .x21 + BitVec.ofNat 64 (16*i)
  left : s.gpr .x10 = BitVec.ofNat 64 (nr-1-i)
  value : RInv (lanes n) (sch nr o) x i s

theorem nodup {n : Nat} (hn : n ≤ 15) : (lanes n).Nodup := by
  exact (by decide : ∀ j < 16, (lanes j).Nodup) n (by omega)

theorem step_ok {n nr i : Nat} {o s : State} {x : VReg → Spec.Aes.State}
    (width : n ≤ 15) (nr14 : nr ≤ 14) (hi : i < nr-1) (can : CanLoadKeys nr o) (h : RoundState n nr o x i s) :
    WP isa (.block (step n)) s (RoundState n nr o x (i+1)) := by
  have hin : InRegions (s.rd++s.wr) (s.gpr .x9+0#64) 16 := by
    rw [BitVec.add_zero,h.cursor,h.frame.rd,h.frame.wr]; exact can i (by omega)
  let key := s.mem.readW (s.gpr .x9+0#64) 128
  have keyOk : KeyIs key (roundKey (sch nr o) i) := by
    dsimp [key]; rw [BitVec.add_zero,h.cursor,h.frame.mem]; exact keyIs_readW _ _ (by omega)
  unfold step
  rw [List.append_assoc,List.singleton_append,WP.block_cons_iff]
  refine ⟨_,exec_ldrq (by decide) hin,?_⟩
  rw [WP.block_append_iff]
  refine (each_ok _ (fun v k => aesMixColumns (aesMapBytes aesSbox (aesShiftRows (v ^^^ k))))
    .v30 (fun b t _ => rnd_run _ b t) (lanes n) (s.setV .v30 key) (nodup width) (ne_round n)).mono ?_
  rintro u ⟨val,f⟩
  refine WP.of_runBlock ⟨_,by arun [],?_⟩
  have g9 : u.gpr .x9 = s.gpr .x9 := congrFun f.gpr _
  have g10 : u.gpr .x10 = s.gpr .x10 := congrFun f.gpr _
  refine ⟨⟨fun r hr => ?_,fun r hr => ?_,f.sp.trans h.frame.sp,f.mem.trans h.frame.mem,
    f.rd.trans h.frame.rd,f.wr.trans h.frame.wr⟩,?_,?_,fun r hr => ?_⟩
  · simp only [List.mem_cons,not_or] at hr
    simp only [gpr_write,hr.1,hr.2,ite_false]
    exact (congrFun f.gpr _).trans (h.frame.gpr _ (by simpa using hr))
  · change u.v r = o.v r
    rw [f.v r (fun q => hr (List.mem_cons_of_mem _ q)),setV_v_of_ne _ _ (show r ≠ .v30 from fun e => hr (e ▸ List.mem_cons_self))]
    exact h.frame.v r hr
  · simp only [gpr_write,reduceCtorEq,ite_false,ite_true,BitVec.setWidth_eq,g9,h.cursor,Offset.add_add]
    congr 2 <;> omega
  · simp only [gpr_write,reduceCtorEq,ite_false,ite_true,BitVec.setWidth_eq,g10,h.left]
    rw [show nr-1-i = (nr-1-(i+1))+1 by omega,BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  · change Spec.Aes.addRoundKey (st (u.v r)) _ = _
    rw [val r hr,setV_v_self,setV_v_of_ne _ _ (show r ≠ .v30 from fun e => ne_round n (e ▸ hr))]
    exact round_st keyOk (h.value r hr)

theorem loop_ok {n nr : Nat} {o s : State} {x : VReg → Spec.Aes.State}
    (width : n ≤ 15) (rounds : 1 < nr ∧ nr ≤ 14) (can : CanLoadKeys nr o) (start : RoundState n nr o x 0 s) :
    WP isa (.loop (.block (step n)) (.nonzero .x .x10)) s (RoundState n nr o x (nr-1)) := by
  let I := fun m t => ∃ i, m = nr-1-i ∧ i < nr-1 ∧ RoundState n nr o x i t
  apply WP.loop (M := isa) I _ (nr-1) s ⟨0,rfl,by omega_using [rounds],start⟩
  rintro m u ⟨i,rfl,hi,atI⟩
  refine (step_ok width rounds.2 hi can atI).mono fun v next => ?_
  have c : eval (.nonzero .x .x10) v = some (decide (nr-1-(i+1) ≠ 0)) := by
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,next.left,
      VG.Proof.AesGcm.AArch64.ofNat_bne_zero (show nr-1-(i+1) < 2^64 by omega_using [rounds]),decide_not]
  change isa.eval (.nonzero .x .x10) v = some (decide (nr-1-(i+1) ≠ 0)) at c
  by_cases last : nr-1-(i+1) = 0
  · exact .inl ⟨by rw [c,decide_eq_false (fun ne => ne last)],(show i+1 = nr-1 by omega) ▸ next⟩
  · exact .inr ⟨by rw [c,decide_eq_true last],nr-1-(i+1),by omega,i+1,rfl,by omega,next⟩

structure BatchOut (n base : Nat) (o t : State) (bytes : Nat → Nat → Byte) (gs : List Reg := [.x9,.x10]) (vs : List VReg := .v30::lanes n) : Prop where
  cells : ∀ j < n, ∀ k < 16, t.mem (blockAddr o base j + BitVec.ofNat 64 k) = bytes j k
  frame : Frame [⟨blockAddr o base 0,16*n⟩] o.mem t.mem
  gpr : ∀ r ∉ gs, t.gpr r = o.gpr r
  vecs : ∀ r ∉ vs, t.v r = o.v r
  sp : t.sp = o.sp
  rd : t.rd = o.rd
  wr : t.wr = o.wr

private theorem setKey (n : Nat) (u : State) (key : BitVec 128) :
    VFrame (.v30::lanes n) u (u.setV .v30 key) :=
  ⟨rfl,rfl,rfl,rfl,rfl,fun r hr => setV_v_of_ne _ _ (show r ≠ .v30 from fun e => hr (e ▸ List.mem_cons_self))⟩

theorem finish_ok {n base nr : Nat} {o s : State} {x : VReg → Spec.Aes.State}
    (width : n ≤ 15) (rounds : 1 < nr ∧ nr ≤ 14) (can : CanLoadKeys nr o)
    (hb : base % 16 = 0) (hm : base+16*n ≤ 65536)
    (write : ∀ i < n, InRegions o.wr (blockAddr o base i) 16) (h : RoundState n nr o x (nr-1) s) :
    WP isa (.block (finish n base)) s (BatchOut n base o ·
      (fun j k => (Spec.Aes.cipher nr (sch nr o) (x (lane j))).getD k 0)) := by
  have stepA : s.gpr .x9 + 0#64 = o.gpr .x21 + BitVec.ofNat 64 (16*(nr-1)) := by rw [BitVec.add_zero,h.cursor]
  have stepB : s.gpr .x9 + 16#64 = o.gpr .x21 + BitVec.ofNat 64 (16*nr) := by
    rw [h.cursor,Offset.add_add]; congr 2 <;> omega_using [rounds]
  have a : InRegions (s.rd++s.wr) (s.gpr .x9+0#64) 16 := by rw [stepA,h.frame.rd,h.frame.wr]; exact can _ (by omega)
  let keyA := s.mem.readW (s.gpr .x9+0#64) 128
  have ha : KeyIs keyA (roundKey (sch nr o) (nr-1)) := by
    dsimp [keyA];rw [stepA,h.frame.mem]; exact keyIs_readW _ _ (by omega)
  unfold finish
  rw [List.append_assoc,List.append_assoc,List.singleton_append,WP.block_cons_iff]
  refine ⟨_,exec_ldrq (by decide) a,?_⟩
  rw [WP.block_append_iff]
  have aes (t : State) : WP isa (.block ((lanes n).map (fun r => Instr.vop (.aese r .v30)))) t fun u =>
      (∀ b ∈ lanes n, u.v b = aesMapBytes aesSbox (aesShiftRows (t.v b ^^^ t.v .v30))) ∧ VFrame (lanes n) t u := by
    rw [List.map_eq_flatMap]
    exact each_ok (fun r => [.vop (.aese r .v30)]) (fun v k => aesMapBytes aesSbox (aesShiftRows (v ^^^ k))) .v30 (fun _ _ _ => rfl) (lanes n) t (nodup width) (ne_round n)
  refine (aes (s.setV .v30 keyA)).mono ?_
  rintro u ⟨ea,f⟩
  have fu := (setKey n s keyA).trans (f.mono (fun _ h => List.mem_cons_of_mem _ h))
  have rdB : InRegions (u.rd++u.wr) (u.gpr .x9+16#64) 16 := by
    rw [fu.gpr,fu.rd,fu.wr,stepB,h.frame.rd,h.frame.wr]; exact can _ (Nat.le_refl _)
  rw [List.singleton_append,WP.block_cons_iff]
  refine ⟨_,exec_ldrq (by decide) rdB,?_⟩
  let keyB := u.mem.readW (u.gpr .x9+16#64) 128
  have hb' : KeyIs keyB (roundKey (sch nr o) nr) := by
    dsimp [keyB]; rw [fu.gpr,stepB,fu.mem,h.frame.mem]; exact keyIs_readW _ _ (Nat.le_refl _)
  have fv := fu.trans (setKey n u keyB)
  have addr : blockAddr (u.setV .v30 keyB) base = blockAddr o base := by
    unfold blockAddr; rw [fv.gpr,h.frame.gpr .x19 (by decide)]
  refine (stores_ok width (u.setV .v30 keyB) hb hm (fun i hi => by rw [fv.wr,h.frame.wr,addr]; exact write i hi)).mono fun t hz => ?_
  refine ⟨fun j hj k hk => ?_,by rw [←addr,←h.frame.mem,←fv.mem]; exact hz.frame,
    fun r hr => (congrFun (hz.gpr.trans fv.gpr) r).trans (h.frame.gpr r hr),fun r hr => ?_,
    hz.sp.trans (fv.sp.trans h.frame.sp),hz.rd.trans (fv.rd.trans h.frame.rd),hz.wr.trans (fv.wr.trans h.frame.wr)⟩
  · have cell := hz.bytes j hj k hk
    have ne : lane j ≠ .v30 := fun e => ne_round n (e ▸ lane_mem hj)
    rw [addr,setV_v_self,setV_v_of_ne _ _ ne,ea _ (lane_mem hj),setV_v_self,setV_v_of_ne _ _ ne,
      ←getD_st _ hk,last_st ha hb' (h.value _ (lane_mem hj))] at cell
    exact cell
  · exact (hz.vecs _ (fun hm => hr (List.mem_cons_of_mem _ hm))).trans ((fv.v _ hr).trans (h.frame.v _ hr))

open VG.Proof.AesGcm.AArch64.DirectGather.Counters (seedCode seedVec seedRegs seed_ok nonce jZero seed_byte jZero_low)
open VG.Proof.Gcm.AArch64.Stitch (kp)
open VG.Impl.AesGcm.AArch64 (mov)

theorem initInputs {n : Nat} (wide : 7 ≤ n) :
    ∀ r ∈ Counters.seedVecs, r ∈ .v31 :: lanes n := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl|hl
  · exact List.mem_cons_self
  · obtain ⟨i,mem,rfl⟩ := List.mem_map.mp hl
    have hi := List.mem_range.mp mem
    have eq : VG.Impl.Gcm.AArch64.Stitch.breg i = lane i :=
      (by decide : ∀ j < 7, VG.Impl.Gcm.AArch64.Stitch.breg j = lane j) i hi
    exact List.mem_cons_of_mem _ (eq ▸ lane_mem (by omega))

theorem kernel_ok {n nr base : Nat} (s : State) (wide : 7 ≤ n ∧ n ≤ 15)
    (rounds : 1 < nr ∧ nr ≤ 14) (nrReg : s.gpr .x22 = BitVec.ofNat 64 nr)
    (read0 : InRegions (s.rd++s.wr) (s.gpr .x23+0#64) 8)
    (read8 : InRegions (s.rd++s.wr) (s.gpr .x23+8#64) 4)
    (can : CanLoadKeys nr s) (hb : base%16=0) (hm : base+16*n ≤ 65536)
    (write : ∀ i < n, InRegions s.wr (blockAddr s base i) 16) :
    WP isa (kernel n base) s (BatchOut n base s ·
      (fun j k => (Spec.Aes.cipher nr (sch nr s) (Proof.Aes.ctrState (jZero s) j)).getD k 0)
      seedRegs (.v31 :: .v30 :: lanes n)) := by
  apply WP.seq
  rw [List.append_assoc,WP.block_append_iff]
  refine (seed_ok s read0 read8).mono ?_
  rintro u ⟨seed,fseed⟩
  rw [WP.block_append_iff]
  refine (counts_ok wide.2 u).mono ?_
  rintro v ⟨inputs,fcount⟩
  have f := (fseed.mono (fun _ h => h) (initInputs wide.1)).trans
    (fcount.mono (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h))
  refine WP.of_runBlock ⟨_,by arun [mov],?_⟩
  let w := (v.write .x .x9 (v.gpr .x21)).write .x .x10 (v.gpr .x22-1#64)
  let x := fun r => st (v.v r)
  have keyG : v.gpr .x21 = s.gpr .x21 := f.gpr _ (by decide)
  have nrG : v.gpr .x22 = BitVec.ofNat 64 nr := (f.gpr _ (by decide)).trans nrReg
  have start : RoundState n nr v x 0 w := by
    refine ⟨⟨fun r hr => ?_,fun _ _ => rfl,rfl,rfl,rfl,rfl⟩,?_,?_,fun _ _ => rfl⟩
    · simp only [List.mem_cons,not_or] at hr; simp [w,gpr_write,hr]
    · simp [w,gpr_write]
    · simp only [w,gpr_write,reduceCtorEq,ite_true,ite_false,BitVec.setWidth_eq,Nat.sub_zero,nrG]
      rw [show nr=(nr-1)+1 by omega_using [rounds],BitVec.ofNat_add,BitVec.add_sub_cancel]
      congr 1 <;> omega
  have canV : CanLoadKeys nr v := fun i hi => by rw [f.rd,f.wr,keyG]; exact can i hi
  have addr : blockAddr v base = blockAddr s base := by unfold blockAddr; rw [f.gpr .x19 (by decide)]
  simp only [BitVec.add_zero]
  refine WP.seq ((loop_ok wide.2 rounds canV start).mono fun a h =>
    (finish_ok wide.2 rounds canV hb hm (fun i hi => by rw [f.wr,addr]; exact write i hi) h).mono ?_)
  intro t out
  have schEq : sch nr v = sch nr s := by unfold VG.Proof.Gcm.AArch64.Stitch.sch VG.Proof.Gcm.AArch64.Stitch.kp; rw [keyG,f.mem]
  refine ⟨fun j hj k hk => ?_,by rw [←f.mem,←addr]; exact out.frame,fun r hr => ?_,fun r hr => ?_,
    out.sp.trans f.sp,out.rd.trans f.rd,out.wr.trans f.wr⟩
  · have ctr : x (lane j) = Proof.Aes.ctrState (jZero s) j := by
      change st (v.v (lane j)) = _
      rw [inputs _ hj,seed,Counters.count_state s (by omega_using [hj,wide])]
    simpa only [addr,ctr,schEq] using out.cells j hj k hk
  · exact (out.gpr _ (fun q => hr (by rcases List.mem_cons.mp q with h|h <;> simp_all [seedRegs]))).trans (f.gpr _ hr)
  · exact (out.vecs _ (fun q => hr (List.mem_cons_of_mem _ q))).trans (f.v _ (fun q => hr (by
      rcases List.mem_cons.mp q with h|h
      · exact List.mem_cons.mpr (.inl h)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))))

open VG.Spec.Gcm (blockAt inc32 aesWith)
open VG.Proof.Gcm (ksByte)

theorem BatchOut.mask {n base nr : Nat} {s t : State} {gs vs} (hn : 0 < n)
    (h : BatchOut n base s t (fun j k => (Spec.Aes.cipher nr (sch nr s) (Proof.Aes.ctrState (jZero s) j)).getD k 0) gs vs) :
    blockAt t.mem (blockAddr s base 0) = aesWith nr (sch nr s) (jZero s) := by
  apply Proof.Aes.block_ext; intro k hk
  rw [Proof.Aes.toBytes_blockAt _ _ hk,h.cells 0 hn k hk,aesWith,
    Proof.Aes.toBytes_ofBytes (by simp) hk,Proof.Aes.getD_eq _ hk,List.getD_eq_getElem?_getD,
    Vector.getElem?_toList,Vector.getElem?_eq_getElem hk,Option.getD_some]
  rfl

theorem BatchOut.stream {n base nr : Nat} {s t : State} {gs vs}
    (h : BatchOut n base s t (fun j k => (Spec.Aes.cipher nr (sch nr s) (Proof.Aes.ctrState (jZero s) j)).getD k 0) gs vs)
    {k : Nat} (hk : k+16 < 16*n) :
    t.mem (blockAddr s base 1+BitVec.ofNat 64 k) = ksByte (aesWith nr (sch nr s)) (inc32 (jZero s)) k := by
  have pos : blockAddr s base 1+BitVec.ofNat 64 k = blockAddr s base (k/16+1)+BitVec.ofNat 64 (k%16) := by
    simp only [blockAddr,Offset.add_add]; congr 2; omega
  have byte := Nat.mod_lt k (by decide : 0<16)
  rw [pos,h.cells _ (by omega) _ byte,ksByte,aesWith,Proof.Aes.toBytes_ofBytes (by simp) byte,
    Proof.Aes.getD_eq _ byte,List.getD_eq_getElem?_getD,Vector.getElem?_toList,Vector.getElem?_eq_getElem byte,
    Option.getD_some,Proof.Aes.ctrState,Proof.Gcm.repeat_add]
  rfl

end VG.Proof.AesGcm.AArch64.DirectGather.CounterBatch

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

private theorem zeroAuth_ok {W : Addr} (s : State) (hb : s.gpr .x19 = W)
    (hw : Covers [⟨W,Medium.work⟩] s.wr) :
    WP isa (.block VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect.zeroAuth) s fun t =>
      t.mem = WriteBytes.writeBytes s.mem (W+480#64) (List.replicate 272 0) ∧
      t.gpr = s.gpr ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect.zeroAuth
  rw [WP.block_cons_iff]
  refine ⟨_,Proof.Gcm.AArch64.Pmull.exec_movi0 .v0 s,?_⟩
  refine WP.mono (Stitch.zstores_range (off := Medium.authO) 17 _ (by rfl) hb hw (by decide) (by decide) (by decide)) fun _ ⟨hm,hg,_,hs,hr,hw⟩ => ⟨hm,hg,hs,hr,hw⟩

theorem prefix_ok {o : State} (c : Caller o) (hn : len o ≤ 224) (hal : AL o ≤ 16) :
    WP isa (.seq (.block (shortSetupAt Medium.work))
      (.seq (.block VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect.zeroAuth) (Medium.aadWith true))) (allocated Medium.work o)
      fun t => Mid.Header o t (len o) ∧ Spec.Aes.bytesAt t.mem (Mid.ghBase o) 256 = Mid.aadLayout o (len o) ∧
        Spec.Aes.bytesAt t.mem (Mid.base o+736) 16 = Spec.Gcm.zeros 16 := by
  refine WP.seq ((enter c hn).mono fun a ⟨h,x4⟩ => WP.seq ((zeroAuth_ok a h.x19 h.scratchWr).mono ?_))
  rintro z ⟨zm,zg,zsp,zrd,zwr⟩
  rw [show 480#64 = (480:Addr) by decide] at zm
  have fr : Frame [⟨Mid.base o+480,272⟩] a.mem z.mem := by
    rw [zm]; apply WriteBytes.writeBytes_frame
    rw [List.length_replicate]; exact Region.contains_self _ _
  have hz := h.advance fr (by decide) (by decide) (fun r _ => congrFun zg r) zsp zrd zwr
  have all : Spec.Aes.bytesAt z.mem (Mid.base o+480) 272 = Spec.Gcm.zeros 272 := by
    rw [zm]; simpa only [Spec.Gcm.zeros,List.length_replicate] using bytesAt_writeBytes_self a.mem (Mid.base o+480) (List.replicate 272 0) (by rw [List.length_replicate]; decide)
  have zero : Spec.Aes.bytesAt z.mem (Mid.ghBase o) 256 = Spec.Gcm.zeros 256 := by
    change Spec.Aes.bytesAt z.mem (Mid.base o+480) 256 = _
    rw [← bytesAt_take z.mem (Mid.base o+480) (show 256 ≤ 272 by decide),all,Spec.Gcm.zeros,List.take_replicate]; rfl
  have endZero : Spec.Aes.bytesAt z.mem (Mid.base o+736) 16 = Spec.Gcm.zeros 16 := by
    rw [show Mid.base o+736=Mid.base o+480+256#64 by rw [BitVec.add_assoc]; rfl,Proof.Cmac.Stream.bytesAt_offset _ _ (show 256+16 ≤ 272 by decide),all,Spec.Gcm.zeros,List.drop_replicate,List.take_replicate]; rfl
  refine (Mid.fillAad true hn hal (BoundedArgs.scratchApart Mid.size _ c _ (by simp [externalRegions]))
    ((Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans c.read)
    hz ((congrFun zg .x4).trans x4) zero).mono ?_
  rintro t ⟨header,auth,f⟩
  refine ⟨header,auth,?_⟩
  rw [bytesAt_frame f (by
    intro q hq; obtain rfl := List.mem_singleton.mp hq
    exact Offset.disjoint _ (.inr (by change 480+224-16*((len o+15)/16)+AL o ≤ 736; omega))
      (by decide) (by change 480+224-16*((len o+15)/16)+AL o ≤ 2^64; omega)) (by decide),endZero]

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

/-! Relate the counter batch to the contiguous record’s keystream and tag mask. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.MediumDirect
open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather
open VG.Impl.AesGcm.AArch64.DirectGather VG.Proof.AesGcm.AArch64.DirectGather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt inc32 zeros)
open Short (len count)
open VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect (cursors)

open VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect (stream streamFor)
open VG.AArch64.RegUpd

private theorem chooseWidth {o s : State} (n : Nat) (cut : n=129 ∨ n=161)
    (lenReg : s.gpr .x26 = BitVec.ofNat 64 (len o)) (hn : len o ≤ 224)
    {yes no : Prog isa} {Q : State → Prop}
    (small : ∀ flag, len o < n → WP isa yes (s.write .x .x11 flag) Q)
    (large : ∀ flag, WP isa no (s.write .x .x11 flag) Q) :
    WP isa (Medium.chooseGroup n yes no) s Q := by
  apply chooseGroup_ok (.inr cut)
  · intro hit
    apply small
    by_contra bad
    apply hit
    change ((s.gpr .x26 - BitVec.ofNat 64 n) >>> 63) = 0
    rw [lenReg]
    have lenNat : (BitVec.ofNat 64 (len o)).toNat = len o := Nat.mod_eq_of_lt (stackArg o 0).isLt
    have cutNat : (BitVec.ofNat 64 n).toNat = n := by rcases cut with rfl|rfl <;> decide
    have le : BitVec.ofNat 64 n ≤ BitVec.ofNat 64 (len o) := by
      change (BitVec.ofNat 64 n).toNat ≤ (BitVec.ofNat 64 (len o)).toNat; rw [lenNat,cutNat]; omega
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_sub_of_le le,lenNat,cutNat]
    exact Nat.div_eq_of_lt (by change len o - n < 9223372036854775808; omega)
  · exact fun _ => large _

theorem stream_ok {o s : State} (c : Caller o) (iv : NL o=12) (hn : len o ≤ 224) (h : Mid.Header o s (len o)) :
    WP isa stream s (MediumKeysPost (Mid.base o) (K o) (o.gpr .x1).toNat (count o) s) := by
  let W := Mid.base o
  let R := (o.gpr .x1).toNat
  have bounds : 1 < R ∧ R ≤ 14 := by rcases c.rounds with eq|eq|eq <;> simp [R,eq]
  have readKeys : Covers [kR .plain o] (s.rd++s.wr) :=
    ((Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans c.read).trans h.toLocalMem.read
  have readNonce : Covers [⟨Nn o,12⟩] (s.rd++s.wr) := by
    rw [←iv]
    exact ((Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans c.read).trans h.toLocalMem.read
  have applyN (n : Nat) (wide : 7 ≤ n ∧ n ≤ 15) (size : count o + 1 ≤ n) (flag : Addr) :
      WP isa (streamFor n) (s.write .x .x11 flag) (MediumKeysPost W (K o) R (count o) s) := by
    let u := s.write .x .x11 flag
    let v := (u.write .x .x27 (u.gpr .x6+0#64)).write .x .x28 (u.gpr .x7+0#64)
    apply WP.seq
    refine WP.of_runBlock ⟨v,by arun [VG.Impl.AesGcm.AArch64.mov],?_⟩
    have keeps (r : Reg) (h : r ∉ [.x11,.x27,.x28]) : v.gpr r = s.gpr r := by
      simp only [List.mem_cons,not_or] at h
      simp [v,u,gpr_write,h]
    have key := (keeps .x21 (by decide)).trans h.x21
    have nonce := (keeps .x23 (by decide)).trans h.x23
    have work := (keeps .x19 (by decide)).trans h.x19
    have nrReg : v.gpr .x22 = BitVec.ofNat 64 R := by
      rw [keeps _ (by decide),h.x22]; simp [R]
    have keys : Counters.CanLoadKeys R v := by
      intro i hi; rw [key]; exact in_off readKeys (by change 16*i+16 ≤ 256; omega_using [hi,bounds]) (by decide)
    have addr (j : Nat) : Counters.blockAddr v Medium.keyO j = W+BitVec.ofNat 64 (224+16*j) := by
      unfold Counters.blockAddr; rw [work]; rfl
    have read0 : InRegions (v.rd++v.wr) (v.gpr .x23+0#64) 8 := by rw [nonce]; exact in_off readNonce (by decide) (by decide)
    have read8 : InRegions (v.rd++v.wr) (v.gpr .x23+8#64) 4 := by rw [nonce]; exact in_off readNonce (by decide) (by decide)
    refine (CounterBatch.kernel_ok v wide bounds nrReg read0 read8 keys (base:=Medium.keyO) (by decide)
      (by change 224+16*n ≤ 65536; omega_using [wide])
      (fun j hj => by rw [addr]; exact in_off h.scratchWr (by change 224+16*j+16 ≤ 752; omega_using [hj,wide]) (by decide))).mono ?_
    intro t out
    have cipher : Spec.Gcm.aesWith R (Proof.Gcm.AArch64.Stitch.sch R v) = ciphOf s.mem (K o) R := by
      unfold Proof.Gcm.AArch64.Stitch.sch Proof.Gcm.AArch64.Stitch.kp; rw [key]; rfl
    have nz : Counters.jZero v = Counters.jZero s := by
      unfold Counters.jZero Counters.nonce; rw [keeps .x23 (by decide)]; rfl
    refine ⟨?_,fun j hj => ?_,?_,fun r hr => ?_,?_,?_,out.sp,out.rd,out.wr⟩
    · simpa only [addr,cipher,nz,Nat.mul_zero,Nat.add_zero] using out.mask (by omega_using [wide])
    · simpa only [addr,cipher,nz,show BitVec.ofNat 64 (224+16*1)=(240:Addr) by decide] using out.stream (k:=j) (by omega_using [size,hj])
    · apply out.frame.sub
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      rw [addr]; exact ⟨⟨medD W,256⟩,by simp,Region.sub_prefix (by omega_using [wide])⟩
    · have e : r ∉ Counters.seedRegs ∧ r ∉ [.x11,.x27,.x28] := by
        simp only [medKept,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      exact (out.gpr _ e.1).trans (keeps _ e.2)
    · simpa [v,u,gpr_write] using out.gpr .x27 (by decide)
    · simpa [v,u,gpr_write] using out.gpr .x28 (by decide)
  apply chooseWidth 129 (.inl rfl) h.x26 hn
  · intro flag small
    exact applyN 9 (by decide) (by unfold count; omega) flag
  · intro outer
    apply chooseWidth 161 (.inr rfl) (by exact h.x26) hn
    · intro flag small
      simpa only [writeFlag_twice] using applyN 11 (by decide) (by unfold count; omega) flag
    · intro flag
      simpa only [writeFlag_twice] using applyN 15 (by decide) (by unfold count; omega) flag

theorem ready {o s : State} (c : Caller o)
    (iv : NL o = 12) (hn : len o ≤ 224) (h : Mid.Header o s (len o))
    (input : bytesAt s.mem (Mid.ghBase o) 256 = Mid.aadLayout o (len o))
    (acc : bytesAt s.mem (Mid.base o+736) 16 = zeros 16) :
    WP isa (.seq stream (.block cursors)) s (Ready o) := by
  have hc : count o ≤ 14 := by unfold Short.count; omega
  refine WP.seq ((stream_ok c iv hn h).mono ?_)
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

theorem frame_ok (hash : Hash16WithOk) {o : State}
    (c : Caller o) (pw : Prepared.Powers o) (iv : NL o=12) (al : AL o≤16) (hn : len o≤224)
    (keep : frame.allInstrs keepsV = true) :
    WP isa frame o fun t => abiPreserved o t ∧ result o t := by
  apply WP.withPreservedV (hc := keep)
  apply WP.alloc (by decide) (by change 752 ≤ o.sp.toNat; have := c.room; omega)
  have front := prefix_ok c hn al
  refine WP.seq ((WP.seq_iff.mp front).mono fun _ w => WP.seq ((WP.seq_iff.mp w).mono fun _ w => WP.seq (w.mono ?_)))
  intro u ⟨header,input,acc⟩
  refine WP.seq ((WP.seq_iff.mp (ready c iv hn header input acc)).mono fun _ w => WP.seq (w.mono ?_))
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

theorem frame_rel (hash : Hash16WithOk) {a b : State} (ca : Caller a) (cb : Caller b)
    (ka : Prepared.Powers a) (kb : Prepared.Powers b)
    (ai : NL a = 12) (bi : NL b = 12) (aa : AL a ≤ 16) (ba : AL b ≤ 16)
    (an : len a ≤ 224) (bn : len b ≤ 224) (pub : onePub 3 a b) :
    RelCT isa (Eq2 a b) frame TT := by
  apply RelCT.alloc (R := TT)
  suffices body : RelCT isa (Eq2 (allocated Medium.work a) (allocated Medium.work b)) body TT from
    body.mono (by rintro x y ⟨_,_,⟨rfl,rfl⟩,rfl,rfl⟩; exact ⟨rfl,rfl⟩) (fun _ _ h => h)
  obtain ⟨q0,q1,q2,_,q4,q5,q6,q7,qsp,stk⟩ := pub
  have w : Mid.base a = Mid.base b := by simp only [Mid.base,qsp]
  have n : len a = len b := congrArg BitVec.toNat (stk 0 (by decide))
  have ce : count a = count b := by rw [Short.count,Short.count,n]
  have al : AL a = AL b := congrArg BitVec.toNat q5
  have preRel : RelCT isa (Eq2 (allocated Medium.work a) (allocated Medium.work b))
      (.seq (.block (shortSetupAt Medium.work)) (.seq (.block VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect.zeroAuth) (Medium.aadWith true))) TT := by
    refine rel_seq (rel_taint [] w (by agree_tac []) ⟨_,by taint_decide⟩) (enter ca an) (enter cb bn) ?_
    intro u v ⟨p,p4⟩ ⟨q,q4'⟩
    exact rel_taint [.x4,.x19,.x24,.x25] (p.sp.trans (w.trans q.sp.symm))
      (by agree_tac [p4,q4',Ad,q4,p.x19,q.x19,p.x24,q.x24,p.x25,q.x25,al,w,n]) ⟨_,by taint_decide⟩
  unfold Impl.AesGcm.AArch64.Contiguous.MediumDirect.body
  apply VG.RelCT.assoc
  apply VG.RelCT.assoc
  refine rel_seq (Fast.RelCT.assoc' preRel) (VG.WP.assoc' (prefix_ok ca an aa))
    (VG.WP.assoc' (prefix_ok cb bn ba)) ?_
  intro e f ⟨p,pin,pa⟩ ⟨q,qin,qa⟩
  have ps := p.sp.trans (w.trans q.sp.symm)
  have kp : RelCT isa (Eq2 e f) (.seq VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect.stream (.block cursors)) TT :=
    rel_taint [.x19,.x21,.x22,.x23,.x26] ps (by agree_tac [p.x19,q.x19,p.x21,q.x21,p.x22,q.x22,
      p.x23,q.x23,p.x26,q.x26,w,K,q0,q1,Nn,q2,n]) ⟨_,by taint_decide⟩
  apply VG.RelCT.assoc
  refine rel_seq kp (ready ca ai an p pin pa) (ready cb bi bn q qin qa) ?_
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
