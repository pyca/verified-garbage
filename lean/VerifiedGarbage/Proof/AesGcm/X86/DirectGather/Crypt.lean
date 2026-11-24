module

public import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Whole
public import VerifiedGarbage.Proof.AesGcm.X86.Loops
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole

/-! The final partial counter block for a gather piece. Its unused suffix
stays in the state for the next nonempty piece. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Gcm (Block blockAt)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (xorKs)

structure KeyStreamPost (C St W SP : BitVec 32) (ciph : Block → Block) (icb : Block) (off k : Nat)
    (s t : State) : Prop where
  env : Env C St W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (ksFrame St W SP) s.mem t.mem
  ctr : CtrS t.mem St ciph icb (off+k)
  xor : ∀ d : List Byte, d.length = k → List.zipWith (· ^^^ ·) d (bytesAt t.mem (w64 St+64#64) k) = xorKs ciph icb off d

theorem keyStream_ok (v : GcmImpl) {C St W SP : BitVec 32} {s : State} {R off k : Nat}
    {ciph : Block → Block} {icb : Block} (L : Lay C St W SP 32) (E : Env C St W SP s)
    (r : RoundsAt s.mem W R) (cipher : ciphOf s.mem C R = ciph) (ctr : CtrS s.mem St ciph icb off)
    (aligned : off%16 = 0) (hk : k < 16) (nz : k ≠ 0) :
    WP isa (.seq (.block ksArgs) (.seq (ctrCall v.callees) (.block unscr))) s (KeyStreamPost C St W SP ciph icb off k s) := by
  refine WP.seq (WP.mono (ksReady L rfl E r) ?_)
  rintro u ⟨m,ready,rd,wr⟩
  refine WP.mono (ctrW_ok (vg:=v) L rfl ready) ?_
  intro t h
  obtain ⟨ks,cb⟩ := ksBlock_of L m h
  have zero : Frame [⟨w64 St+64#64,16⟩] s.mem u.mem := by rw [m]; exact Cmac.frame_store4 _ _ _ _ _
  rw [ciph_frame zero (fun a ha => by
    simp only [List.mem_singleton] at ha
    subst ha
    exact L.cs.sub_right (Lay.stSub (by decide))) r.2,cipher] at ks
  have f := h.frame
  rw [L.aS (by decide),L.aS (by decide)] at f
  have key (d : List Byte) (hd : d.length = k) := Proof.Gcm.ctr_tail ctr aligned ks cb (d:=d)
    (hd ▸ hk) (hd ▸ nz)
  refine ⟨h.env,h.rd.trans rd,h.wr.trans wr,?_,?_,?_⟩
  · refine (zero.sub ?_).trans f
    intro a ha
    simp only [List.mem_singleton] at ha; subst ha
    exact ⟨_,by simp [ksFrame],fun _ q => q⟩
  · have len : (List.replicate k (0 : Byte)).length = k := List.length_replicate
    simpa only [len] using (key _ len).2
  · intro d hd
    simpa only [hd] using (key d hd).1

theorem tailCursors_ok {C St W SP D T : BitVec 32} {s : State} {n : Nat}
    (L : Lay C St W SP 32) (E : Env C St W SP s)
    (src : slotv s.mem W dataO = D) (len : slotv s.mem W lenO = BitVec.ofNat 32 n)
    (arg : s.mem.readW (w64 SP) 32 = T) (ar : InRegions (s.rd++s.wr) (w64 SP) 4) (hlt : n < 2^32) :
    WP isa (.block Open.tailRegs) s fun t =>
      t.gpr .edx = St+64#32 ∧ t.gpr .edi = T+BitVec.ofNat 32 (16*(n/16)) ∧
      t.gpr .esi = D+BitVec.ofNat 32 (16*(n/16)) ∧ t.gpr .ecx = BitVec.ofNat 32 (n%16) ∧
      t.gpr .ebp = W ∧ t.gpr .esp = SP ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain mask := and15 (BitVec.ofNat 32 n)
  rw [toNat_ofNat32 hlt] at mask
  have sub : BitVec.ofNat 32 n - BitVec.ofNat 32 (n%16) = BitVec.ofNat 32 (16*(n/16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) hlt]; congr 1; omega_using []
  refine WP.of_runBlock ⟨_,by xrun [Open.tailRegs,E.ebp,E.esp,E.esi,L.aW,E.wIn',len,src,ar,arg,add_zero32],?_⟩
  refine ⟨rfl,?_,?_,?_,E.ebp,E.esp,rfl,rfl,rfl⟩ <;> regs [mask,sub]

abbrev tailPtr (D : BitVec 32) (n : Nat) := D+BitVec.ofNat 32 (16*(n/16))

theorem xorTail_ok {C St W SP D T : BitVec 32} {s : State} {n : Nat}
    (L : Lay C St W SP 32) (st : St = W+16#32) (E : Env C St W SP s)
    (P : PieceRegions C W SP D T n) (A : PieceAccess s SP D T n)
    (src : slotv s.mem W dataO = D) (len : slotv s.mem W lenO = BitVec.ofNat 32 n)
    (hlt : n < 2^32) (nz : n%16 ≠ 0) (words : Bool := false) :
    WP isa (.seq (.block Open.tailRegs) (.seq (xorTailCode words) (.block [.mov .esi (.reg .ebp),.alu .add .esi (imm stO)])))
      s fun t => t.mem = WriteBytes.writeBytes s.mem (w64 (tailPtr T n))
          (xorBytes s.mem (w64 (tailPtr D n)) (w64 (St+64#32)) (n%16)) ∧
        t.gpr .ebp = W ∧ t.gpr .esi = St ∧ t.gpr .esp = SP ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.seq (WP.mono (tailCursors_ok L E src len A.dstArg (by simpa using in_off A.argR (d:=0) (n:=4) (by decide) (by decide)) hlt) ?_)
  rintro u ⟨dx,di,si,cx,bp,sp,m,rd,wr⟩
  have fd := P.fD
  have ft := P.fT
  have d : w64 (tailPtr D n) = w64 D+BitVec.ofNat 64 (16*(n/16)) := w64_add (by omega_using [fd,nz])
  have t : w64 (tailPtr T n) = w64 T+BitVec.ofNat 64 (16*(n/16)) := w64_add (by omega_using [ft,nz])
  have key := L.aS (o:=64) (by decide)
  have ds : Region.Sub ⟨w64 (tailPtr D n),n%16⟩ ⟨w64 D,n⟩ := by rw [d]; exact Offset.sub_base _ (by omega_using [])
  have ts : Region.Sub ⟨w64 (tailPtr T n),n%16⟩ ⟨w64 T,n⟩ := by rw [t]; exact Offset.sub_base _ (by omega_using [])
  have ks : Region.Sub ⟨w64 (St+64#32),n%16⟩ ⟨w64 W,2560⟩ := by
    rw [st,BitVec.add_assoc]
    change Region.Sub ⟨w64 (W+80#32),_⟩ _
    rw [L.aW (by decide)]; exact Lay.wSub (by omega_using [])
  have hx : XorPreG true u (St+64#32) (tailPtr D n) (tailPtr T n) (n%16) :=
    ⟨dx,di,si,(fun h => nomatch h),cx,by omega_using [nz],by omega_using [],
      by rw [L.nS (by decide)]; have h := L.fs; omega_using [h],
      by unfold tailPtr; rw [toNat_add32 (by omega_using [fd,nz])]; omega_using [fd],
      by unfold tailPtr; rw [toNat_add32 (by omega_using [ft,nz])]; omega_using [ft],
      by rw [rd,wr,key]; exact covers_left (E.stC (by omega_using [])),
      by rw [rd,wr,d]; exact covers_off A.rd (by omega_using []) (by omega_using [hlt]),
      by rw [wr,t]; exact covers_off A.wr (by omega_using []) (by omega_using [hlt]),
      ((P.dstWork.sub_left ts).sub_right ks).symm,P.srcDst.imp (congrArg (fun p => tailPtr p n)) (fun hd => (hd.sub_left ds).sub_right ts)⟩
  refine WP.seq (WP.mono (xorTailCode_ok words hx) ?_)
  intro z hz
  have bp' := (hz.other .ebp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans bp
  have sp' := (hz.other .esp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans sp
  refine WP.of_runBlock ⟨_,by xrun [bp'],?_⟩
  refine ⟨?_,bp',st.symm,sp',hz.rd.trans rd,hz.wr.trans wr⟩
  change z.mem = _
  rw [hz.mem,m]

end VG.Proof.AesGcm.X86.DirectGather

end

/-! Encryption of the aligned remainder of one fragment. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block)
open VG.Proof.Gcm (xorKs)

section
variable {C St W SP D T : BitVec 32} {R n : Nat} (L : Lay C St W SP 32) (st : St = W+16#32)
  (P : PieceRegions C W SP D T n)

include L st P

omit P in
theorem stSub : Region.Sub ⟨w64 St,80⟩ ⟨w64 W,2560⟩ := by
  rw [st,L.aW (by decide)]; exact Lay.wSub (by decide)

theorem PieceAccess.dataW {s : State} (A : PieceAccess s SP D T n) : DataW C St W SP 32 s T n :=
  ⟨⟨covers_left A.wr,P.fT,P.dstWork.sub_right (stSub L st),P.dstWork,P.stackDst⟩,A.wr,P.dstCtx⟩

omit st P in
theorem whole_crFrame {m m' : Mem} (f : Frame (wholeFrame St W SP T (n/16)) m m') :
    Frame (crFrame St W SP 32 T n) m m' := by
  refine f.sub ?_
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨⟨w64 St+48#64,32⟩,by simp [crFrame],by rw [L.aS (by decide)]; exact Region.sub_prefix (by decide)⟩
  · exact ⟨_,List.mem_cons_self ..,Region.sub_prefix (Nat.mul_div_le _ _)⟩
  · exact ⟨wsR W,by simp [crFrame],by rw [L.aW (by decide)]; exact Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨below SP 32,by simp [crFrame],L.below_sub (by decide)⟩

theorem keptSlot {s : State} (A : PieceAccess s SP D T n) {m u : Mem}
    (f : Frame (crFrame St W SP 32 T n) m u) {d : Nat} (lo : 128 ≤ d) (hi : d+4 ≤ 240) :
    slotv u W d = slotv m W d :=
  slot_frame f (fun r hr => (kept_crFrame L (A.dataW L st P) r hr).sub_left (Offset.sub _ lo (by omega_using [hi])))

theorem afterAccess {s t : State} (A : PieceAccess s SP D T n) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (f : Frame (crFrame St W SP 32 T n) s.mem t.mem) :
    PieceAccess t SP D T n := by
  refine ⟨?_,by rw [rd,wr]; exact A.argR,by rw [rd,wr]; exact A.rd,by rw [wr]; exact A.wr⟩
  refine Eq.trans (f.readW (r:=⟨w64 SP,4⟩) (Region.contains_self _ _) ?_ (by decide)) A.dstArg
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact P.argDst
  · exact P.argWork.sub_right (fun _ h => stSub L st _ (Lay.stSub (by decide) _ h))
  · exact P.argWork.sub_right (Lay.wSub (by decide))
  · exact ret_below L.sp

structure PiecePost (s : State) (C St W SP D T : BitVec 32) (ciph : Block → Block) (icb : Block)
    (off n : Nat) (t : State) : Prop where
  env : Env C St W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (crFrame St W SP 32 T n) s.mem t.mem
  ctr : CtrS t.mem St ciph icb (off+n)
  out : bytesAt t.mem (w64 T) n = xorKs ciph icb off (bytesAt s.mem (w64 D) n)

theorem tailResult {s u z : State} {off : Nat} {ciph : Block → Block} {icb : Block}
    (A : PieceAccess s SP D T n) (h : WholePost s St W SP D T ciph icb off (n/16) u)
    (v : State) (k : KeyStreamPost C St W SP ciph icb (off+16*(n/16)) (n%16) u v)
    (m : z.mem = WriteBytes.writeBytes v.mem (w64 (tailPtr T n)) (xorBytes v.mem (w64 (tailPtr D n)) (w64 (St+64#32)) (n%16)))
    (bp : z.gpr .ebp = W) (si : z.gpr .esi = St) (sp : z.gpr .esp = SP)
    (rd : z.rd = v.rd) (wr : z.wr = v.wr) (nz : n%16 ≠ 0) : PiecePost s C St W SP D T ciph icb off n z := by
  have hn := P.fD
  have ht := P.fT
  have n64 : n < 2^64 := by omega_using [hn]
  have jle : 16*(n/16) ≤ n := Nat.mul_div_le _ _
  have total : 16*(n/16) + n%16 = n := by omega_using []
  have ts : w64 (tailPtr T n) = w64 T + BitVec.ofNat 64 (16*(n/16)) := w64_add (by omega_using [nz,ht])
  have ds : w64 (tailPtr D n) = w64 D + BitVec.ofNat 64 (16*(n/16)) := w64_add (by omega_using [nz,hn])
  have xlen := length_xorBytes v.mem (w64 (tailPtr D n)) (w64 (St+64#32)) (n%16)
  have xt : Frame [⟨w64 T+BitVec.ofNat 64 (16*(n/16)),n%16⟩] v.mem z.mem := by
    rw [m,←ts]; exact writeBytes_frame' _ xlen
  have before := (whole_crFrame L h.frame).trans (ksFrame_crFrame L rfl k.frame (D:=T) (n:=n))
  have wf := part_crFrame (St:=St) (W:=W) (SP:=SP) (K:=32) (n:=n) (by omega_using []) xt
  have dataW := A.dataW L st P
  have outPre : bytesAt z.mem (w64 T) (16*(n/16)) = bytesAt u.mem (w64 T) (16*(n/16)) := by
    rw [bytesAt_frame xt (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact split_disj (by omega_using [n64])) (by omega_using [n64])]
    have d := data_ksFrame L rfl dataW (a:=0) (l:=16*(n/16)) (by omega_using [])
    simp only [BitVec.add_zero] at d
    exact bytesAt_frame k.frame d (by omega_using [n64])
  -- Only the unprocessed suffix must still contain the original plaintext.
  have prefixFrame := (whole_crFrame (n:=16*(n/16)) L (by simpa using h.frame)).trans
    (ksFrame_crFrame L rfl k.frame (D:=T) (n:=16*(n/16)))
  have source : bytesAt v.mem (w64 D + BitVec.ofNat 64 (16*(n/16))) (n%16) =
      bytesAt s.mem (w64 D + BitVec.ofNat 64 (16*(n/16))) (n%16) := by
    refine bytesAt_frame prefixFrame ?_ (by omega_using [n64])
    intro r hr
    have sub : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16*(n/16)),n%16⟩ ⟨w64 D,n⟩ :=
      Offset.sub_base _ (by omega_using [])
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases P.srcDst with rfl | hd
      · exact (split_disj (by omega_using [n64])).symm
      exact (hd.sub_left sub).sub_right (Region.sub_prefix jle)
    · exact (P.srcWork.sub_left sub).sub_right (fun _ hx => stSub L st _ (Lay.stSub (by decide) _ hx))
    · exact (P.srcWork.sub_left sub).sub_right (Lay.wSub (by decide))
    · exact (P.stackSrc.sub_right sub).symm
  have written := bytesAt_writeBytes_self v.mem (w64 (tailPtr T n)) _ (by rw [xlen]; omega_using [])
  rw [xlen] at written
  have tail : bytesAt z.mem (w64 T+BitVec.ofNat 64 (16*(n/16))) (n%16) =
      xorKs ciph icb (off+16*(n/16)) (bytesAt s.mem (w64 D+BitVec.ofNat 64 (16*(n/16))) (n%16)) := by
    rw [←ts,m,written,xorBytes,ds,L.aS (by decide),←source]
    exact k.xor _ (length_bytesAt _ _ _)
  have pres (i : Nat) (hi : i+16 ≤ 80) : ∀ r ∈ [⟨w64 T+BitVec.ofNat 64 (16*(n/16)),n%16⟩],
      (⟨w64 St+BitVec.ofNat 64 i,16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ((dataW.ok.st.symm.sub_left (Lay.stSub hi)).sub_right (Offset.sub_base _ (by omega_using [])))
  have endCtr := k.ctr.congr (blockAt_frame xt (pres 48 (by decide))) (blockAt_frame xt (pres 64 (by decide)))
  have zrd := rd.trans (k.rd.trans h.rd)
  have zwr := wr.trans (k.wr.trans h.wr)
  refine ⟨env_crFrame L (dataW.of_eq (k.rd.trans h.rd) (k.wr.trans h.wr)) k.env wf
    (bp.trans k.env.ebp.symm) (si.trans k.env.esi.symm) (sp.trans k.env.esp.symm) rd wr,zrd,zwr,before.trans wf,?_,?_⟩
  · rwa [Nat.add_assoc,total] at endCtr
  · conv => lhs; rw [←total,bytesAt_add]
    conv => rhs; rw [←total,bytesAt_add]
    rw [Proof.Gcm.xorKs_append,length_bytesAt,outPre,h.out,tail]

omit st P in
theorem tailTest {u : State} (env : Env C St W SP u) (len : slotv u.mem W lenO = BitVec.ofNat 32 n)
    (hlt : n < 2^32) : WP isa (.block Open.tailLen) u fun y =>
    y.zf = some (decide (n%16=0)) ∧ Env C St W SP y ∧ y.mem = u.mem ∧ y.rd = u.rd ∧ y.wr = u.wr := by
  have mask := and15 (BitVec.ofNat 32 n)
  rw [toNat_ofNat32 hlt] at mask
  refine WP.of_runBlock ⟨_,by xrun [Open.tailLen,env.ebp,L.aW,env.wIn',len],?_⟩
  refine ⟨?_,⟨env.ebp,env.esi,env.esp,env.ctxR,env.stW,env.wW,env.ctx⟩,rfl,rfl,rfl⟩
  change some ((_ &&& _) == 0) = _
  rw [mask,and_self_beq32 (by omega_using [])]

theorem decTo_ok (v : GcmImpl) {s : State} {off : Nat} {ciph : Block → Block} {icb : Block}
    (E : Env C St W SP s) (A : PieceAccess s SP D T n) (r : RoundsAt s.mem W R)
    (src : slotv s.mem W dataO = D) (len : slotv s.mem W lenO = BitVec.ofNat 32 n) (hlt : n < 2^32)
    (aligned : n ≠ 0 → off%16 = 0) (cipher : ciphOf s.mem C R = ciph) (ctr : CtrS s.mem St ciph icb off) (words : Bool := false) :
    WP isa (Open.decTo v.callees v.callees.ctr words) s (PiecePost s C St W SP D T ciph icb off n) := by
  have dataW := A.dataW L st P
  refine WP.seq (WP.mono (wholeTo_ok v L st E P A r src len hlt (fun h => aligned (by omega_using [h])) cipher ctr) ?_)
  intro u h
  have f := whole_crFrame L h.frame
  have e := env_crFrame L dataW E f (h.bp.trans E.ebp.symm) (h.si.trans E.esi.symm) (h.sp.trans E.esp.symm) h.rd h.wr
  have ln := (keptSlot L st P A f (d:=lenO) (by decide) (by decide)).trans len
  refine WP.seq (WP.mono (tailTest L e ln hlt) ?_)
  rintro y ⟨zf,ey,m,rd,wr⟩
  refine WP.ite (decide (n%16=0)) zf (fun z => ?_) (fun nz => ?_)
  · have h0 : n%16=0 := by simpa using z
    have jn : 16*(n/16) = n := by omega_using [h0]
    refine WP.block_nil ⟨ey,rd.trans h.rd,wr.trans h.wr,by rw [m]; exact f,?_,?_⟩
    · rw [m,←jn]; exact h.ctr
    · rw [m,←jn]; exact h.out
  · have hk : n%16 ≠ 0 := by simpa using nz
    have rounds : RoundsAt y.mem W R := by rw [m]; exact rounds_frame f (kept_crFrame L dataW) r
    have cipher' : ciphOf y.mem C R = ciph := by rw [m,ciph_crFrame L dataW f r.2,cipher]
    have ct : CtrS y.mem St ciph icb (off+16*(n/16)) := by rw [m]; exact h.ctr
    refine WP.seq (WP.mono (keyStream_ok v L ey rounds cipher' ct (by have a := aligned (by omega_using [hk]); omega_using [a])
      (k:=n%16) (by omega_using []) hk) ?_)
    intro z k₁
    have k : KeyStreamPost C St W SP ciph icb (off+16*(n/16)) (n%16) u z :=
      ⟨k₁.env,k₁.rd.trans rd,k₁.wr.trans wr,by rw [←m]; exact k₁.frame,k₁.ctr,k₁.xor⟩
    have sf := f.trans (ksFrame_crFrame L rfl k.frame (D:=T) (n:=n))
    have access := afterAccess L st P A (k.rd.trans h.rd) (k.wr.trans h.wr) sf
    refine WP.mono (xorTail_ok L st k.env P access ((keptSlot L st P A sf (by decide) (by decide)).trans src)
        ((keptSlot L st P A sf (by decide) (by decide)).trans len) hlt hk words) ?_
    rintro t ⟨mem,bp,si,sp,r',w'⟩
    exact tailResult L st P A h z k mem bp si sp r' w' hk

omit P st in
/-- The empty remainder can contain a wrapped one-past-end input or output
pointer on IA-32. Its value is never used as a memory address. -/
theorem decTo_empty (v : GcmImpl) {s : State} (e : Env C St W SP s) (len : slotv s.mem W lenO = 0) :
    WP isa (Open.decTo v.callees v.callees.ctr) s fun t =>
      t.mem = s.mem ∧ t.gpr .ebp = W ∧ t.gpr .esi = St ∧ t.gpr .esp = SP ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.seq (WP.seq (WP.of_runBlock ⟨_,by xrun [e.ebp,L.aW,e.wIn',len],?_⟩))
  refine WP.ite true rfl (fun _ => WP.block_nil ?_) (fun h => nomatch h)
  refine WP.seq (WP.of_runBlock ⟨_,by xrun [Open.tailLen,e.ebp,L.aW,e.wIn',len],?_⟩)
  exact WP.ite true rfl (fun _ => WP.block_nil ⟨rfl,e.ebp,e.esi,e.esp,rfl,rfl⟩) (fun h => nomatch h)

end
end VG.Proof.AesGcm.X86.DirectGather

end
