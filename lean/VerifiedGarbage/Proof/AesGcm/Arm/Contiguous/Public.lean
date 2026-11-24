module
public import VerifiedGarbage.Spec.Gcm.Contiguous
public import VerifiedGarbage.Proof.AesGcm.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Sig

public import VerifiedGarbage.Proof.AesGcm.SealBuffers
public import VerifiedGarbage.Proof.AesGcm.Arm.Contiguous.Frame
public import VerifiedGarbage.Proof.AesGcm.Arm.Contiguous.Body
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.AesGcm.Arm.Contiguous.Timing
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.AesGcm.Arm.Gather.LoopCT
import VerifiedGarbage.Proof.Cmac.Frame

/-! Functional correctness of the two-pointer ARM entry, including frame allocation and cleanup. -/
@[expose] public section
namespace VG.Proof.AesGcm.Arm.Contiguous.Caller
open VG VG.Arm VG.Arm.FrameStack VG.Impl.AesGcm.Arm.Contiguous
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm


abbrev ctx (s : State) : Region := ⟨State.addr (s.gpr .r0), 256⟩
abbrev nonce (s : State) : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
abbrev aad (s : State) : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
abbrev length (s : State) := (stackArg s 4).toNat
abbrev src (s : State) : Region := ⟨State.addr (stackArg s 2), length s⟩
abbrev dst (s : State) : Region := ⟨State.addr (stackArg s 3), length s⟩
abbrev tag (s : State) : Region := ⟨State.addr (stackArg s 5), 16⟩
abbrev incoming (s : State) : Region := ⟨State.addr s.sp, 24⟩
abbrev stkR (s : State) : Region := ⟨State.addr s.sp - 2608#64, 2608⟩

structure Fits (o : State) : Prop where
  down : 2608 ≤ o.sp.toNat
  up : o.sp.toNat + 24 ≤ 2^32

structure Layout (o : State) : Prop extends Fits o where
  ctxRead : ctx o ∈ o.rd
  nonceRead : nonce o ∈ o.rd
  aadRead : aad o ∈ o.rd
  arguments : incoming o ∈ o.rd
  srcRead : src o ∈ o.rd ∨ stackArg o 2 = stackArg o 3
  dstWrite : dst o ∈ o.wr
  tagWrite : tag o ∈ o.wr
  apart : stackArg o 2 = stackArg o 3 ∨ (src o).Disjoint (dst o)
  ctxOut : (ctx o).Disjoint (dst o)
  nonceOut : (nonce o).Disjoint (dst o)
  aadOut : (aad o).Disjoint (dst o)
  outTag : (dst o).Disjoint (tag o)
  stack : ∀ r ∈ [ctx o, nonce o, aad o, src o, dst o, tag o], (stkR o).Disjoint r
  ctxFit : (o.gpr .r0).toNat + 256 ≤ 2^32
  nonceFit : (o.gpr .r2).toNat + (o.gpr .r3).toNat ≤ 2^32
  aadFit : (stackArg o 0).toNat + (stackArg o 1).toNat ≤ 2^32
  srcFit : (stackArg o 2).toNat + length o ≤ 2^32
  dstFit : (stackArg o 3).toNat + length o ≤ 2^32
  tagFit : (stackArg o 5).toNat + 16 ≤ 2^32
  rounds : roundsOk o

abbrev sp (o : State) := o.sp - 2592#32
abbrev work (o : State) := sp o+32#32
abbrev part (o : State) (d n : Nat) : Region := ⟨(stkR o).base+BitVec.ofNat 64 d,n⟩
abbrev workR (o : State) : Region := ⟨State.addr (work o),2560⟩
abbrev argsR (o : State) : Region := ⟨State.addr (sp o),28⟩

theorem Fits.ptr {o : State} (h : Fits o) : (sp o).toNat=o.sp.toNat-2592 :=
  sub_toNat' (by have := h.down; omega)

theorem Fits.addr {o : State} (h : Fits o) : State.addr (sp o)=(stkR o).base+16#64 := by
  have a := addr_sub' (x:=o.sp) (k:=2592) (by have := h.down; omega)
  change State.addr (o.sp-BitVec.ofNat 32 2592) = State.addr o.sp-2608#64+16#64
  rw [a,BitVec.sub_eq_add_neg,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rfl

theorem Fits.workAddr {o : State} (h : Fits o) : State.addr (work o)=(stkR o).base+48#64 := by
  change sa (sp o) 32=_
  rw [sa_eq (by have := h.ptr; have := h.up; omega),h.addr,BitVec.add_assoc]; rfl

theorem Fits.workNat {o : State} (h : Fits o) : (work o).toNat=(sp o).toNat+32 := by
  have := h.ptr
  have := h.up
  rw [work,BitVec.toNat_add, Nat.mod_eq_of_lt (by change _+32<2^32; omega)]
  rfl

theorem Fits.argsEq {o : State} (h : Fits o) : argsR o=part o 16 28 := congrArg (fun p => Region.mk p 28) h.addr
theorem Fits.workEq {o : State} (h : Fits o) : workR o=part o 48 2560 := congrArg (fun p => Region.mk p 2560) h.workAddr

theorem Fits.belowEq {o : State} (h : Fits o) : below (sp o)=part o 8 8 := by
  change (Region.mk (State.addr _ - 8#64) 8)=_
  rw [h.addr]; congr 1
  simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem Fits.below12Eq {o : State} (h : Fits o) : below12 (sp o)=part o 4 12 := by
  change (Region.mk (State.addr _ - 12#64) 12)=_
  rw [h.addr]; congr 1
  simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem sub (o : State) {d n : Nat} (h : d+n≤2608) : (part o d n).Sub (stkR o) :=
  Offset.sub_base _ h

theorem disj (o : State) {d n e k : Nat} (sep : d+n≤e ∨ e+k≤d) (dn : d+n≤2608) (ek : e+k≤2608) :
    (part o d n).Disjoint (part o e k) := Offset.disjoint _ sep (by omega) (by omega)

theorem allocatedSlots {o : State} (h : Layout o) : Args.Layout slots (allocState 2592 o) := by
  have n := h.toFits.ptr
  have up := h.up
  have down := h.down
  refine ⟨by change (sp o).toNat + 2616 ≤ 2^32; omega, ?_, ?_⟩
  · intro j hj
    have index := slots.indexLt j hj
    change slots.index j < 6 at index
    have shift : sa (sp o) (slots.source j) = State.addr o.sp + BitVec.ofNat 64 (4 * slots.index j) := by
      change State.addr (o.sp - 2592#32 + BitVec.ofNat 32 (2592+4*slots.index j)) = _
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      exact sa_eq (by omega)
    exact ⟨incoming o, List.mem_append_left _ h.arguments, by change (incoming o).Contains (sa (sp o) (slots.source j)) 4; rw [shift]; exact Offset.contains_base _ (by omega) (by omega)⟩
  · intro d hd
    change d+4 ≤ 32 at hd
    refine ⟨_, List.mem_cons_self .., ?_⟩
    change (Region.mk (State.addr (sp o)) 2592).Contains (sa (sp o) d) 4
    rw [sa_eq (by omega)]
    exact Offset.contains_base _ (by omega) (by omega)

def narrow (o t : State) := t.withRegions (o.rd ++ [argsR o]) [dst o, tag o, workR o]
abbrev Prepared (o t : State) := Args.Ready slots (allocState 2592 o) t

theorem Prepared.word {o t : State} (p : Prepared o t) {i : Nat} (hi : i<6) :
    arg (narrow o t) i = stackArg o (slots.index i) := by
  change t.mem.readW (sa t.sp (4*i)) 32 = o.mem.readW (sa o.sp (4*slots.index i)) 32
  rw [p.sp,p.words i hi]
  change o.mem.readW (State.addr (o.sp-2592#32+BitVec.ofNat 32 (2592+4*slots.index i))) 32 = _
  rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.sub_add_cancel]

theorem Prepared.workspace {o t : State} (p : Prepared o t) : arg (narrow o t) 6 = work o := by
  change t.mem.readW (sa t.sp 24) 32 = _
  rw [p.sp]
  exact p.scratch

theorem Prepared.one {o t : State} (p : Prepared o t) (h : Layout o) :
    onePre 7 6 (narrow o t) := by
  let b := narrow o t
  have f := h.toFits
  have fp := f.ptr
  have down := f.down
  have up := f.up
  have argsE : args b 7 = argsR o := by
    change Region.mk (State.addr (t.sp + 0#32)) 28 = _
    rw [BitVec.add_zero,p.sp]; rfl
  have a0 : arg b 0 = stackArg o 0 := p.word (by decide)
  have a1 : arg b 1 = stackArg o 1 := p.word (by decide)
  have a2 : arg b 2 = stackArg o 3 := p.word (by decide)
  have a3 : arg b 3 = stackArg o 4 := p.word (by decide)
  have w : arg b 6 = work o := p.workspace
  have g (r : Reg) (hr : r ≠ .r12) : b.gpr r = o.gpr r := p.regs _ hr
  have eSp : b.sp = sp o := p.sp
  have eBel : bel b = part o 8 8 := by change below b.sp = _; rw [eSp, f.belowEq]
  have wk : (workR o).Sub (stkR o) := f.workEq ▸ sub o (by decide)
  have ar : (argsR o).Sub (stkR o) := f.argsEq ▸ sub o (by decide)
  have bw : (part o 8 8).Disjoint (workR o) := by rw [f.workEq]; exact disj _ (.inl (by decide)) (by decide) (by decide)
  have aw : (argsR o).Disjoint (workR o) := by rw [f.argsEq,f.workEq]; exact disj _ (.inl (by decide)) (by decide) (by decide)
  have sk := h.stack (ctx o) (by simp)
  have sn := h.stack (nonce o) (by simp)
  have sa := h.stack (aad o) (by simp)
  have sd := h.stack (dst o) (by simp)
  have stg := h.stack (tag o) (by simp)
  change onePre 7 6 b
  simp only [onePre,roundsOk,g _ (by decide : Reg.r0 ≠ .r12),g _ (by decide : Reg.r1 ≠ .r12),
    g _ (by decide : Reg.r2 ≠ .r12),g _ (by decide : Reg.r3 ≠ .r12),a0,a1,a2,a3,w,argsE,eBel,eSp]
  have subBelow := sub o (d:=8) (n:=8) (by decide)
  refine ⟨?_, ?_, fun _ => h.ctxOut, (sk.sub_left wk).symm, fun _ => h.nonceOut,
    (sn.sub_left wk).symm, fun _ => h.aadOut, (sa.sub_left wk).symm, (sd.sub_left wk).symm,
    fun _ => (sd.sub_left ar).symm, aw.symm, sk.sub_left subBelow, sn.sub_left subBelow,
    sa.sub_left subBelow, sd.sub_left subBelow, bw, h.ctxFit, h.nonceFit, h.aadFit, h.dstFit,
    by rw [f.workNat]; omega, by omega, by omega, h.rounds⟩
  · change ctx o ∈ o.rd ++ [argsR o] ∧ nonce o ∈ o.rd ++ [argsR o] ∧ aad o ∈ o.rd ++ [argsR o] ∧ argsR o ∈ o.rd ++ [argsR o]
    simp [h.ctxRead, h.nonceRead, h.aadRead]
  · change dst o ∈ (o.rd ++ [argsR o]) ++ [dst o, tag o, workR o] ∧ workR o ∈ [dst o, tag o, workR o] ∧ _
    refine ⟨by simp, by simp, ?_⟩
    intro r hr
    change r ∈ [dst o, tag o, workR o] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sd.sub_left ar
    · exact stg.sub_left ar
    · exact aw

theorem Prepared.layout {o t : State} (p : Prepared o t) (h : Layout o) :
    Contiguous.Layout (narrow o t) := by
  let b := narrow o t
  have f := h.toFits
  have fp := f.ptr
  have down := h.down
  have a2 : arg b 2 = stackArg o 3 := p.word (by decide)
  have a3 : arg b 3 = stackArg o 4 := p.word (by decide)
  have a4 : arg b 4 = stackArg o 5 := p.word (by decide)
  have a5 : arg b 5 = stackArg o 2 := p.word (by decide)
  have w : arg b 6 = work o := p.workspace
  have g (r : Reg) (hr : r ≠ .r12) : b.gpr r = o.gpr r := p.regs _ hr
  have eSp : b.sp = sp o := p.sp
  have wk : (workR o).Sub (stkR o) := f.workEq ▸ sub o (by decide)
  have sk := h.stack (ctx o) (by simp)
  have ss := h.stack (src o) (by simp)
  have sd := h.stack (dst o) (by simp)
  have stg := h.stack (tag o) (by simp)
  have dc : (⟨State.addr (arg b 2), (arg b 3).toNat⟩ : Region) = dst o := by rw [a2, a3]
  have sc : (⟨State.addr (arg b 5), (arg b 3).toNat⟩ : Region) = src o := by rw [a5, a3]
  have tc : (⟨State.addr (arg b 4), 16⟩ : Region) = tag o := by rw [a4]
  have wc : (⟨State.addr (arg b 6), 2560⟩ : Region) = workR o := by rw [w]
  have one := p.one h
  change Contiguous.Layout b
  have sw : (src o).Disjoint ⟨State.addr (arg b 6),2560⟩ := wc ▸ (ss.sub_left wk).symm
  have canRead : src o ∈ b.rd ++ b.wr := by
    rcases h.srcRead with rd | eq
    · exact List.mem_append_left _ (List.mem_append_left _ rd)
    · have same : src o = dst o := congrArg (fun a => Region.mk (State.addr a) (length o)) eq
      rw [same]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have srcOk : DataOk (oSt b 6) (arg b 6) b.sp b (arg b 5) (arg b 3).toNat := by
    refine ⟨by rw [sc]; exact covers_of_mem canRead, (arg b 3).isLt, by rw [a5,a3]; exact h.srcFit,
      by rw [sc]; exact oSt_disj one sw, by rw [sc]; exact sw, ?_⟩
    rw [sc, eSp, f.belowEq]; exact ss.sub_left (sub _ (by decide))
  refine ⟨one, by rw [dc]; exact List.mem_cons_self .., srcOk, ?_, by rw [tc]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_, ?_, ?_⟩
  · have bk := sub o (d:=4) (n:=12) (by decide)
    have stkPos : (below12 b.sp) = part o 4 12 := by rw [eSp, f.below12Eq]
    have wkBelow : (part o 4 12).Disjoint (workR o) := by rw [f.workEq]; exact disj _ (.inl (by decide)) (by decide) (by decide)
    refine ⟨?_, by rw [eSp]; omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [a5, a2, a3]; exact h.apart
    · rw [stkPos, g _ (by decide)]; exact sk.sub_left bk
    · exact oSt_disj one (by rw [stkPos, wc]; exact wkBelow)
    · rw [stkPos,wc]; exact wkBelow
    · rw [stkPos,sc]; exact ss.sub_left bk
    · rw [stkPos,dc]; exact sd.sub_left bk
  · rw [dc,tc]; exact h.outTag
  · rw [tc,wc]; exact (stg.sub_left wk).symm
  · rw [a4]; exact h.tagFit

theorem widen {o t : State} (h : Layout o) (p : Prepared o t) :
    Covers ((narrow o t).rd ++ (narrow o t).wr) (t.rd ++ t.wr) ∧ Covers (narrow o t).wr t.wr := by
  have f := h.toFits
  have rd : t.rd = o.rd := p.rd
  have wr : t.wr = ⟨State.addr (sp o),2592⟩ :: o.wr := p.wr
  have frame : Covers [⟨State.addr (sp o),2592⟩] t.wr := covers_of_mem (by rw [wr]; exact List.mem_cons_self ..)
  have wk : Covers [workR o] t.wr := by
    change Covers [Region.mk (sa (sp o) 32) 2560] _
    rw [sa_eq (by have := f.ptr; have := f.up; omega)]
    exact covers_off frame (by decide) (by decide)
  have out : Covers (narrow o t).wr t.wr := by
    apply covers_cons (covers_of_mem (by rw [wr]; exact List.mem_cons_of_mem _ h.dstWrite))
    apply covers_cons (covers_of_mem (by rw [wr]; exact List.mem_cons_of_mem _ h.tagWrite))
    exact wk
  refine ⟨covers_append' (covers_append' ?_ (covers_left (covers_prefix frame (by decide : 28≤2592)))) (covers_left out),out⟩
  intro x n hx
  obtain ⟨r,hr,inside⟩ := hx
  exact ⟨r,List.mem_append_left _ (rd ▸ hr),inside⟩

def Result (o z : State) : Prop :=
  encryptWith (sealCipher o) (sealH o) 16 (sealNonce o)
    (bytesAt o.mem (src o).base (length o)) (bytesAt o.mem (aad o).base (aad o).len) =
    (bytesAt z.mem (dst o).base (length o),bytesAt z.mem (tag o).base 16)

theorem Prepared.result {o t z : State} (p : Prepared o t) (h : Layout o)
    (result : encryptWith (sealCipher (narrow o t)) (sealH (narrow o t)) 16 (sealNonce (narrow o t))
      (source (narrow o t)) (sealAad (narrow o t)) =
      (sealData (narrow o t) z, bytesAt z.mem (State.addr (arg (narrow o t) 4)) 16)) : Result o z := by
  let b := narrow o t
  have g (r : Reg) (hr : r≠.r12) : b.gpr r=o.gpr r := p.regs _ hr
  have a0 : arg b 0=stackArg o 0 := p.word (by decide)
  have a1 : arg b 1=stackArg o 1 := p.word (by decide)
  have a2 : arg b 2=stackArg o 3 := p.word (by decide)
  have a3 : arg b 3=stackArg o 4 := p.word (by decide)
  have a4 : arg b 4=stackArg o 5 := p.word (by decide)
  have a5 : arg b 5=stackArg o 2 := p.word (by decide)
  have old : Frame [stkR o] o.mem b.mem := p.frame.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (Region.mk (State.addr (sp o)) 32).Sub (stkR o)
    rw [h.toFits.addr]; exact sub o (by decide))
  have agree (r : Region) (hr : r ∈ [ctx o, nonce o, aad o, src o, dst o, tag o]) :
      SealBuffers.Agree b.mem o.mem r.base r.len := by
    intro x hx
    exact old x fun q hq inside => (h.stack r hr) x (List.mem_singleton.mp hq ▸ inside) hx
  change SealBuffers.Equation (State.addr (b.gpr .r0)) (State.addr (b.gpr .r2)) (State.addr (arg b 0))
    (State.addr (arg b 5)) (State.addr (arg b 2)) (State.addr (arg b 4)) (b.gpr .r1).toNat
    (b.gpr .r3).toNat (arg b 1).toNat (arg b 3).toNat b.mem z.mem at result
  rw [g _ (by decide : Reg.r0 ≠ .r12), g _ (by decide : Reg.r2 ≠ .r12),
    g _ (by decide : Reg.r1 ≠ .r12), g _ (by decide : Reg.r3 ≠ .r12),
    a0, a5, a2, a4, a1, a3] at result
  have rounds : (o.gpr .r1).toNat ≤ 15 := by rcases h.rounds with a | a | a <;> omega
  exact (SealBuffers.input_congr rounds (agree (ctx o) (by simp)) (agree (nonce o) (by simp))
    (agree (aad o) (by simp)) (agree (src o) (by simp))).mp result

theorem entry_wp [VG.Proof.Gcm.Arm.GhashLaw] {o : State} (h : Layout o) :
    WP isa sealContiguous o fun z => abiPreserved o z ∧ Result o z := by
  have f := h.toFits
  refine WP.alloc ⟨by decide,by decide,by decide,by decide⟩ (by have := f.down; omega) ?_
  obtain ⟨t,head,p⟩ := frameArgs_run (allocatedSlots h)
  refine WP.seq ⟨_,t,Exec.block head,?_⟩
  obtain ⟨tr,z,run,abi,res⟩ := body_wp (Prepared.layout p h)
  obtain ⟨r,w⟩ := widen h p
  have wide := VG.Arm.Exec.widen run r w
  refine ⟨tr,z.withRegions t.rd t.wr,wide,?_⟩
  intro m u fm
  have frameSub : (Region.mk (State.addr (sp o)) 2592).Sub (stkR o) := by rw [f.addr]; exact sub o (by decide)
  have mem (r : Region) (hr : r∈[ctx o,nonce o,aad o,src o,dst o,tag o]) (fit : r.len ≤ 2^64) :
      bytesAt m r.base r.len = bytesAt z.mem r.base r.len := bytesAt_frame fm
        (fun q hq => List.mem_singleton.mp hq ▸ ((h.stack r hr).sub_left frameSub).symm) fit
  refine ⟨⟨fun r hr => (abi.1 r hr).trans (p.regs _ (by intro eq; subst eq; exact (by decide : Reg.r12 ∉ preserved) hr)),?_⟩,?_⟩
  · change z.sp+2592#32 = o.sp
    rw [abi.2]; change t.sp+2592#32=o.sp
    rw [p.sp]; exact BitVec.sub_add_cancel _ _
  · change _ = (bytesAt m (dst o).base (dst o).len, bytesAt m (tag o).base (tag o).len)
    rw [mem (dst o) (by simp) (by change (stackArg o 4).toNat≤2^64; have := (stackArg o 4).isLt; omega),
      mem (tag o) (by simp) (by decide : 16≤2^64)]
    exact Prepared.result p h res

/-- The detached tag and ciphertext computed under each represented AES key,
at the original caller's addresses. -/
theorem keyed [VG.Proof.Gcm.Arm.GhashLaw] {o : State} (h : Layout o) :
    WP isa sealContiguous o fun z => abiPreserved o z ∧ ∀ key,
      KeyRounds o.mem (ctx o).base (o.gpr .r1).toNat key →
      aesGcmEncrypt key 16 (sealNonce o) (bytesAt o.mem (src o).base (length o))
        (bytesAt o.mem (aad o).base (aad o).len) =
        (bytesAt z.mem (dst o).base (length o), bytesAt z.mem (tag o).base 16) :=
  (entry_wp h).mono fun _ ⟨abi, result⟩ => ⟨abi, fun _ hk => SealBuffers.keyed hk result⟩

theorem prepared_public {o o' t t' : State} (p : Prepared o t) (p' : Prepared o' t')
    (pub : onePub 6 o o') : onePub 7 (narrow o t) (narrow o' t') := by
  obtain ⟨spEq, c, r, nonceEq, lenEq, argsEq⟩ := pub
  have stack : (sp o) = sp o' := congrArg (· - 2592#32) spEq
  have reg (x : Reg) (hr : x≠.r12) (eq : o.gpr x=o'.gpr x) :
      (narrow o t).gpr x = (narrow o' t').gpr x := (p.regs x hr).trans (eq.trans (p'.regs x hr).symm)
  refine ⟨p.sp.trans (stack.trans p'.sp.symm),reg _ (by decide) c,reg _ (by decide) r,
    reg _ (by decide) nonceEq,reg _ (by decide) lenEq,?_⟩
  intro i hi
  by_cases ordinary : i<6
  · rw [p.word ordinary,p'.word ordinary]
    exact argsEq _ (slots.indexLt i ordinary)
  · obtain rfl : i=6 := by omega
    rw [p.workspace,p'.workspace]
    exact congrArg (· + 32#32) stack

theorem entry_rel [VG.Proof.Gcm.Arm.GhashLaw] {o o' : State} (h : Layout o) (h' : Layout o')
    (pub : onePub 6 o o') : RelCT isa (fun a b => a = o ∧ b = o') sealContiguous (fun _ _ => True) := by
  apply Gather.rel_alloc
  obtain ⟨t,run,p⟩ := frameArgs_run (allocatedSlots h)
  obtain ⟨t',run',p'⟩ := frameArgs_run (allocatedSlots h')
  have spEq : (allocState 2592 o).sp=(allocState 2592 o').sp := congrArg (· - 2592#32) pub.1
  have fixed : RelCT isa (Gather.Eq2 (allocState 2592 o) (allocState 2592 o')) (.block frameArgs) Gather.TT := by
    rintro _ _ _ _ _ _ ⟨rfl,rfl⟩ ex ex'
    exact ⟨(ex.det (.block run)).1.trans ((congrArg slots.frameTrace spEq).trans (ex'.det (.block run')).1.symm),trivial⟩
  have v : WP isa (.block frameArgs) (allocState 2592 o) (fun z => z=t) := ⟨_,_,Exec.block run,rfl⟩
  have v' : WP isa (.block frameArgs) (allocState 2592 o') (fun z => z=t') := ⟨_,_,Exec.block run',rfl⟩
  refine Gather.rel_seq fixed v v' ?_
  rintro _ _ rfl rfl
  have ct := body_rel (Prepared.layout p h) (Prepared.layout p' h') (prepared_public p p' pub)
  obtain ⟨_,_,exec,_⟩ := body_wp (Prepared.layout p h)
  obtain ⟨_,_,exec',_⟩ := body_wp (Prepared.layout p' h')
  obtain ⟨r,w⟩ := widen h p
  obtain ⟨r',w'⟩ := widen h' p'
  have wide := VG.Arm.Exec.widen exec r w
  have wide' := VG.Arm.Exec.widen exec' r' w'
  rintro _ _ _ _ _ _ ⟨rfl,rfl⟩ ex ex'
  exact ⟨(ex.det wide).1.trans
    ((ct _ _ _ _ _ _ ⟨rfl,rfl⟩ exec exec').1.trans (ex'.det wide').1.symm), trivial⟩

end VG.Proof.AesGcm.Arm.Contiguous.Caller

/-! The contiguous contract at its ARM and Thumb-2 calling convention. -/

namespace VG.Proof.AesGcm.Arm.Contiguous.Caller
open VG VG.Arm VG.Impl.AesGcm.Arm.Contiguous

abbrev publicContract := Spec.Gcm.sealContiguousContract Arm.abi 2608

theorem public_pub {a b : State} (h : publicContract.pub a b) : onePub 6 a b := by
  sig_pub [publicContract, Spec.Gcm.sealContiguousContract, Spec.Gcm.sealContiguousSig,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, List.append_eq] at h
  obtain ⟨sp, r0, r1, r2, r3, a0, a1, a2, a3, a4, a5⟩ := h
  refine ⟨sp, r0, r1, r2, r3, fun i hi => ?_⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4, a5]

theorem public_wp [VG.Proof.Gcm.Arm.GhashLaw] {s : State} (layout : Layout s) :
    WP isa sealContiguous s fun t => abiPreserved s t ∧ publicContract.post s t := by
  apply (keyed layout).mono
  rintro t ⟨abi, encryption⟩
  refine ⟨abi, ?_⟩
  sig_post [publicContract, Spec.Gcm.sealContiguousContract, Spec.Gcm.sealContiguousSig,
    Spec.Gcm.sealContiguousPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, List.append_eq]
  exact encryption


theorem public_layout {s : State} (h : publicContract.pre s) : Layout s := by
  have widen (x y : BitVec 32) : (x.setWidth 64 = y.setWidth 64) ↔ x = y :=
    ⟨fun h => by simpa using congrArg (BitVec.setWidth 32) h, congrArg _⟩
  have small (x : BitVec 32) : x.toNat % 18446744073709551616 = x.toNat :=
    Nat.mod_eq_of_lt (by have := x.isLt; omega)
  by_cases eq : stackArg s 2 = stackArg s 3
  all_goals
    sig_pre [publicContract, Spec.Gcm.sealContiguousContract, Spec.Gcm.sealContiguousSig,
      Spec.Gcm.sealPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, List.append_eq,
      Sig.bufs, Sig.lists] at h
    simp [widen, small, eq, Sig.pairFacts, Sig.conj, List.filterMap_cons, and_assoc] at h
  case pos =>
    obtain ⟨down, up, rd, wr, kd, _, nd, _, ad, _, dt, _, _, sk, sn, sa, sd, st, _, kf, nf, af, df, tf, rounds⟩ := h
    have alias : src s = dst s := by simp [src, dst, eq]
    refine ⟨⟨down, by omega⟩, ?_, ?_, ?_, ?_, .inr eq, ?_, ?_, .inl eq, kd, nd, ad, dt,
      ?_, by omega, nf, af, ?_, df, by omega, rounds⟩
    · simp [rd, ctx, State.addr]
    · simp [rd, nonce, State.addr]
    · simp [rd, aad, State.addr]
    · simp [rd, incoming, stackArgAddr, State.addr]
    · simp [wr, dst, length, State.addr]
    · simp [wr, tag, State.addr]
    · simp only [List.forall_mem_cons, List.not_mem_nil, forall_false, implies_true, and_true, alias]
      exact ⟨sk, sn, sa, sd, sd, st⟩
    · simpa only [eq] using df
  case neg =>
    obtain ⟨down, up, rd, wr, kd, _, nd, _, ad, _, pd, _, dt, _, _, sk, sn, sa, ss, sd, st, _, kf, nf, af, sf, df, tf, rounds⟩ := h
    refine ⟨⟨down, by omega⟩, ?_, ?_, ?_, ?_, .inl ?_, ?_, ?_, .inr pd, kd, nd, ad, dt,
      ?_, by omega, nf, af, sf, df, by omega, rounds⟩
    · simp [rd, ctx, State.addr]
    · simp [rd, nonce, State.addr]
    · simp [rd, aad, State.addr]
    · simp [rd, incoming, stackArgAddr, State.addr]
    · simp [rd, src, length, State.addr]
    · simp [wr, dst, length, State.addr]
    · simp [wr, tag, State.addr]
    · simp only [List.forall_mem_cons, List.not_mem_nil, forall_false, implies_true, and_true]
      exact ⟨sk, sn, sa, ss, sd, st⟩

/-- A nonempty source and destination, with the tag in separate storage. -/
def witness (same : Bool) : State :=
  { mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
      ([⟨0x1000,256⟩, ⟨0x2000,0⟩, ⟨0,0⟩] ++
        (if same then [] else [⟨0x3000,16⟩]) ++ [⟨0x8000,24⟩])
      [⟨if same then 0x3000 else 0x4000,16⟩, ⟨0x5000,16⟩] with
    mem := fun a => if a = 0x8009 then 0x30 else if a = 0x800d then (if same then 0x30 else 0x40)
                    else if a = 0x8010 then 16 else if a = 0x8015 then 0x50 else 0 }

theorem witness_pre (same : Bool) : publicContract.pre (witness same) := by
  cases same <;>
    sig_pre [publicContract, Spec.Gcm.sealContiguousContract, Spec.Gcm.sealContiguousSig, Spec.Gcm.sealPre,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Sig.bufs, Sig.lists, List.append_eq]
  all_goals
    simp [witness, mkSat, Arm.stackArg, Arm.stackArgAddr, Arm.State.addr, Mem.readW, Mem.read]
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem public_verified [VG.Proof.Gcm.Arm.GhashLaw] : Verified target sealContiguous publicContract :=
  ⟨fun _ pre => public_wp (public_layout pre),
   fun _ _ _ _ _ _ p q pub run run' =>
     (entry_rel (public_layout p) (public_layout q) (public_pub pub) _ _ _ _ _ _ ⟨rfl,rfl⟩ run run').1,
   ⟨_, witness_pre true⟩⟩


/-- The final scrub preserves the only two exit regions observed by GCM. -/
theorem public_postOut : VG.Arm.Scrub.PostOut publicContract 0 := by
  apply VG.Arm.Scrub.postOut_of_local (leak := none) VG.Arm.Scrub.ScrubAbi.plain
  intro vs _ _ _ _ hlen hb h
  match vs, hlen with
  | [ctx, rounds, nonce, nl, aad, al, src, dst, len, tag], _ =>
    by_cases eq : src = dst
    all_goals
      simp only [Spec.Gcm.sealContiguousSig, Sig.bufs, eq, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      apply (h key hk).trans
      apply Prod.ext
      · first | exact (Scrub.bytesAt_of hb.2.2.2.1 (Scrub.len_le len)).symm | exact (Scrub.bytesAt_of hb.2.2.2.2.1 (Scrub.len_le len)).symm
      · first | exact (Scrub.bytesAt_of hb.2.2.2.2 (Nat.le_refl 16)).symm | exact (Scrub.bytesAt_of hb.2.2.2.2.2 (Nat.le_refl 16)).symm

open VG.Arm.Scrub in
theorem scrubbed [VG.Proof.Gcm.Arm.GhashLaw] :
    VerifiedScrubbed target (VG.Impl.Scrub.Arm.scrubAll 0 2608 sealContiguous) publicContract 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.sealContiguousApi)
    { code := sealContiguous, verified := public_verified }
    public_postOut (scrubSideF_of codeOk Scrub.frameOk_2608 _)

end VG.Proof.AesGcm.Arm.Contiguous.Caller
