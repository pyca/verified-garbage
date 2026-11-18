module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Writes
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Entry
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Data
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Search
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptInput
import VerifiedGarbage.Proof.Dsa.PackedBytes
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.NativeTimingState
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Ffdh.AArch64.Front
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow

/-! ### `Ffdh.AArch64.Cached.SearchProof.Guards`, which this module and modules that import it used -/

section

/-! # The key-generation controller's tests of its budgets, tape and status (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search
open VG.Impl.Bignum.AArch64 (movi)

theorem ofNat_beq_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h]
  exact Iff.rfl

/-- A budget, at the controller's word `j`, compared with zero. -/
theorem budget_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {j n : Nat} (hj : j = 0 ∨ j = 1)
    (hv : (j, BitVec.ofNat 64 n) ∈ p.headers used keys scalars) (hn : n ≤ 128) :
    WP isa (.block [ldf .x9 j]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .x .x9) t = some (decide (n = 0)) := by
  have a := h.access
  have hw := h.header hv
  simp only [Bignum.word, off] at hw
  rcases hj with rfl | rfl <;> simp only [Nat.reduceMul] at hw <;>
  · refine WP.mono (WP.keep [.x9] (Q := fun t =>
      isa.eval (.zero .x .x9) t = some (decide (n = 0)) ∧ t.mem = s.mem) ?_ (by decide) (by decide)
      (by decide +kernel)) fun _ ⟨⟨he, hm⟩, k⟩ => ⟨h.keep k hm, he⟩
    brun [ldf, h.x19, hw, a.ld 0 (by decide), a.ld 8 (by decide), a.ld0]
    simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq,
      ofNat_beq_zero (show n < 2 ^ 64 by omega_using [hn])]

theorem keys_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .x9 0]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .x .x9) t = some (decide (keys = 0)) :=
  budget_guard h (j := 0) (.inl rfl) (by simp [KeyPublic.headers]) h.keys_le

theorem scalars_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .x9 1]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .x .x9) t = some (decide (scalars = 0)) :=
  budget_guard h (j := 1) (.inr rfl) (by simp [KeyPublic.headers]) h.scalars_le

/-- Whether the tape holds less than an attempt. -/
theorem room_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block room) s fun t =>
      KeyLive p original used keys scalars t ∧
        isa.eval (.zero .x .x12) t = some (decide (p.randLen - used < p.len)) := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv10 := h.header (j := 10) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv10
  have hr : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
  have hk : p.len < 2 ^ 64 := by have := h.input.len_lt; omega_using [this]
  refine WP.mono (WP.keep [.x9, .x10, .x11, .x12, .x13, .x14] (Q := fun t =>
    isa.eval (.zero .x .x12) t = some (decide (p.randLen - used < p.len)) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun _ ⟨⟨he, hm⟩, k⟩ => ⟨h.keep k hm, he⟩
  unfold room
  brun [ldf, h.x19, hv2, hv10, a.ld 16 (by decide), a.ld 80 (by decide), imm64 (show 0 < 65536 by decide),
    imm64 (show 1 < 65536 by decide), subs_ge (show p.randLen - used < 2 ^ 64 by omega_using [hr]) hk]
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  by_cases hb : p.len ≤ p.randLen - used
  · simp only [hb, decide_true, ite_true, show ¬p.randLen - used < p.len by omega_using [hb], decide_false]
    decide
  · simp only [hb, decide_false, ite_false, show p.randLen - used < p.len by omega_using [hb], decide_true,
      Bool.false_eq_true]
    decide

/-- The status word, minus 4. -/
theorem status_guard {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .x19 = B) {st : Nat}
    (hs : word s.mem B 112 = BitVec.ofNat 64 st) (hst : st < 5) :
    WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) s fun t =>
      (isa.eval (.zero .x .x9) t = some (decide (st = 4)) ∧ t.mem = s.mem) ∧ Keep [.x9] s t := by
  simp only [Bignum.word, off] at hs
  refine WP.keep [.x9] ?_ (by decide) (by decide) (by decide +kernel)
  brun [ldf, hb, hs, a.ld 112 (by decide)]
  have : ∀ st < 5, ((BitVec.ofNat 64 st - BitVec.ofNat 64 4) == 0) = decide (st = 4) := by decide
  have hb' := this st hst
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq,
    Option.some.injEq] at hb' ⊢
  exact hb'

theorem done_loop_guard {p : KeyPublic} {original s : State} {r : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) :
    WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) s fun t =>
      isa.eval (.zero .x .x9) t = some false ∧ KeyDone p original r t := by
  have scr := h.input.control_scr (t := s) h.wr
  have a : CtlAccess s p.control := ⟨fun _ hd => scr.ld hd, fun _ hd => scr.st hd,
    by simpa only [off, BitVec.add_zero] using scr.ld (d := 0) (by decide),
    by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)⟩
  have hb : r.status < 5 := by unfold Spec.Ffdh.KeySearchResult.status; split <;> decide
  refine WP.mono (status_guard a h.x19 h.status hb) fun t ⟨⟨he, hm⟩, k⟩ => ⟨?_, h.keep k hm⟩
  rw [he]
  congr 1
  unfold Spec.Ffdh.KeySearchResult.status
  split <;> rfl

theorem live_loop_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) s fun t =>
      isa.eval (.zero .x .x9) t = some true ∧ KeyLive p original used keys scalars t :=
  WP.mono (status_guard (st := 4) h.access h.x19 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨he, h.keep k hm⟩

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! ### `Ffdh.AArch64.Cached.SearchProof.AttemptRun`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.AttemptCorrect`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.GenerateNative`, which only this module used -/

section

/-! The complete native cached attempt, from its original register and stack arguments. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem generateNative_ok (M : Mont) {p : Parameters} {s : State} {dom rb : List Byte} {dp rp yp : Addr} {dl count : Nat}
 (scratch : Scr s p.B p.Z) (words : p.w=(p.k+7)/8)
 (positive : 0<p.k) (size : p.k<2^31) (shape : dl=2*p.k ∨ dl=3*p.k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid p.k dom=true)
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (table : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w))
 (view : ContextView p.B p.Z p.ctx count p.k dom s)
 (domainSource : Src s p.B p.Z dp dom) (randomSource : Src s p.B p.Z rp rb) (rbLength : rb.length=p.k)
 (xArg : s.gpr .x0=p.src) (yArg : s.gpr .x2=yp) (domArg : s.gpr .x4=dp)
 (dlArg : s.gpr .x5=BitVec.ofNat 64 dl) (lenArg : s.gpr .x6=BitVec.ofNat 64 p.k) (randArg : s.gpr .x7=rp)
 (readB : s.mem.readW (s.sp+8#64) 64=p.B) (readCtx : s.mem.readW (s.sp+24#64) 64=p.ctx)
 (stackB : InRegions (s.rd++s.wr) (s.sp+8#64) 8) (stackCtx : InRegions (s.rd++s.wr) (s.sp+24#64) 8)
 (bitsPositive : 0<p.N) (bitsBound : p.N≤8192) (width : p.N≤8*p.k)
 (writeX : ∀ i<p.k,InRegions s.wr (p.src+BitVec.ofNat 64 i) 1)
 (writeY : ∀ i<p.k,InRegions s.wr (yp+BitVec.ofNat 64 i) 1)
 (outsideX : ∀ i<p.k,p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i))
 (outsideY : ∀ i<p.k,p.Z≤ofs p.B (yp+BitVec.ofNat 64 i))
 (separateRand : ∀ i<p.k,∀ j<p.k,rp+BitVec.ofNat 64 i≠p.src+BitVec.ofNat 64 j)
 (separateDomain : ∀ i<dom.length,p.k≤ofs p.src (dp+BitVec.ofNat 64 i))
 (separateContext : ∀ i<8*count,p.k≤ofs p.src (p.ctx+BitVec.ofNat 64 i))
 (separateOutputs : ∀ i<p.k,p.k≤ofs yp (p.src+BitVec.ofNat 64 i)) :
 WP isa (Generate.code M.mm) s fun t =>
 let a := Spec.Ffdh.domainOf p.k dom
 let x := Spec.Ffdh.vettedScalarOfOctets a rb
 t.gpr .x0=BitVec.ofNat 64 (Spec.Ffdh.keyStatus a x) ∧
 (if Spec.Ffdh.keyStatus a x=1 then
  Spec.Rsa.bytesAt t.mem p.src p.k=Spec.Rsa.i2osp x p.k ∧
  Spec.Rsa.bytesAt t.mem yp p.k=Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) p.k
 else Spec.Rsa.bytesAt t.mem p.src p.k=List.replicate p.k 0 ∧ Spec.Rsa.bytesAt t.mem yp p.k=List.replicate p.k 0) ∧
 Keep (.x0::mmRegs) s t := by
 have room : 256≤p.Z := by have := p.room;dsimp only [slot,hdrBytes] at this;omega_using [this]
 have count3 : 3≤count := by rw [context_words_count view.canonical];omega_using []
 have domSize : p.k≤dom.length := by omega_using [shape, domLength]
 have head (i : Nat) (hi : i<3) := context_header domSize (VG.Proof.Ffdh.domainValid_mod valid) view.canonical hi
 have head0 : word s.mem p.ctx 0=BitVec.ofNat 64 p.N := by simpa [word,off,policy] using head 0 (by decide)
 have head1 : word s.mem p.ctx 8=BitVec.ofNat 64 ((p.N+7)/8) := by simpa [word,off,policy] using head 1 (by decide)
 have head2 : word s.mem p.ctx 16=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N) := by simpa [word,off,policy] using head 2 (by decide)
 unfold Generate.code
 rw [WP.seq_iff]
 refine WP.mono (generateEntry_ok scratch room readB readCtx stackB stackCtx
  (fun i hi =>view.readable i (by omega_using [count3, hi])) (fun i hi =>view.outside i (by omega_using [count3, hi])) head0 head1 head2) ?_
 rintro u ⟨baseU,memU,frameU,restU⟩
 have frame : InScr p.B p.Z s.mem u.mem := InScr.of_outside frameU (by omega_using [room])
 have headers := generationEntry_headers s.mem p.B p.src yp dp (BitVec.ofNat 64 dl) (BitVec.ofNat 64 p.k) rp p.ctx
  (BitVec.ofNat 64 p.N) (BitVec.ofNat 64 ((p.N+7)/8)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N))
 simp only [xArg,yArg,domArg,dlArg,lenArg,randArg] at memU
 rw [←memU] at headers
 rcases headers with ⟨ctxU,domU,lenU,dlU,xU,yU,randU,bitsU,bytesU,rowsU⟩
 change WP isa (generatePrepared M.mm) u _
 refine WP.mono (generatePrepared_ok M (scratch.congr restU.wr) baseU words positive size shape domLength valid modulus generator policy table
  (view.after_inscr frame restU) (domainSource.congrK frame restU) (randomSource.congrK frame restU) rbLength
  ⟨ctxU,xU,lenU,bitsU,rowsU⟩ domU dlU yU randU bytesU bitsPositive bitsBound width
  (fun i hi =>by rw [restU.wr];exact writeX i hi)
  (fun i hi =>by rw [restU.wr];exact writeY i hi) outsideX outsideY separateRand separateDomain separateContext separateOutputs) ?_
 rintro t ⟨status,outputs,restT⟩
 exact ⟨status,outputs,(restU.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The native cached attempt implements the exact reviewed ABI postcondition. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached

theorem keyStatus_lt_four (a : Spec.Ffdh.Parameters) (x : Nat) : Spec.Ffdh.keyStatus a x<4 :=by
 unfold Spec.Ffdh.keyStatus
 split
 · decide
 · split <;>decide

theorem attempt_correct (M : Mont) {s : State} (pre : attemptPre s) :
 WP isa (Generate.code M.mm) s fun t =>abiPreserved s t ∧ attemptPost s t :=by
 let g:=attempt_geometry pre
 let q:=attemptFront s g
 have ns:=attempt_native_state g
 refine WP.mono (generateNative_ok M ns.scratch q.body.scalar.words q.body.scalar.positive q.body.scalar.size
  q.body.scalar.shape q.body.scalar.domLength q.checked q.body.scalar.modulus q.generator q.policy q.body.table
  ns.view ns.domainSource ns.randomSource ns.rbLength ns.xArg ns.yArg ns.domArg ns.dlArg ns.lenArg ns.randArg
  ns.readB ns.readCtx ns.stackB ns.stackCtx q.body.bitsPositive q.body.bitsBound q.body.width
  g.writeX g.writeY g.outsideX g.outsideY g.separateRand g.separateDomain g.separateContext g.separateOutputs) ?_
 rintro t ⟨status,outputs,rest⟩
 refine ⟨abiPreserved_of_keep rest,?_,outputs⟩
 change t.gpr .x0=BitVec.ofNat 64 (Spec.Ffdh.keyStatus (attemptParameters s) (attemptScalar s)) at status
 change ((t.gpr .x0).setWidth 32).toNat=Spec.Ffdh.keyStatus (attemptParameters s) (attemptScalar s)
 rw [status]
 exact VG.Proof.Ffdh.AArch64.setWidth32_ofNat (Nat.lt_trans (keyStatus_lt_four _ _) (by decide))

/-- Callable form used by the verified rejection controller. -/
theorem attempt_callable (M : Mont) (s : State) (pre : attemptContract.pre s) :
 ∃trace t,Exec isa (Generate.code M.mm) s trace t ∧ abiPreserved s t ∧ attemptContract.post s t :=by
 obtain ⟨trace,t,run,preserved,post⟩:=attempt_correct M pre
 exact ⟨trace,t,run,preserved,post⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.SearchProof.Arguments`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.SearchProof.CallFacts`, which only this module used -/

section

/-! # Where the attempt's buffers are, from the controller's (AArch64)

The attempt's buffers are the controller's (`x`, `y`, the domain, a slice
of the tape and the working space), and its stack arguments are in the
attempt's frame, in the 64 bytes of stack below the controller's stack
pointer on entry, which no buffer overlaps.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

/-- The stack pointer in the attempt's frame. -/
abbrev callSp (p : KeyPublic) : Addr := p.sp - 16 - BitVec.ofNat 64 48

theorem callSp_eq (p : KeyPublic) : callSp p = p.sp - BitVec.ofNat 64 64 := by
  rw [callSp, BitVec.sub_sub]; rfl

/-- The attempt's regions: its outputs, the domain, the tape's slice, the
working space and its arguments. -/
abbrev rX (p : KeyPublic) : Region := ⟨p.xp, p.len⟩
abbrev rY (p : KeyPublic) : Region := ⟨p.yp, p.len⟩
abbrev rD (p : KeyPublic) : Region := ⟨p.dp, p.dlen⟩
abbrev rR (p : KeyPublic) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.len⟩
abbrev rS (p : KeyPublic) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : KeyPublic) : Region := ⟨callSp p, 40⟩

structure CallFacts (p : KeyPublic) (used : Nat) : Prop where
  room : 64 ≤ p.sp.toNat
  xy : (rX p).Disjoint (rY p)
  xd : (rX p).Disjoint (rD p)
  xr : (rX p).Disjoint (rR p used)
  xs : (rX p).Disjoint (rS p)
  xa : (rX p).Disjoint (rA p)
  yd : (rY p).Disjoint (rD p)
  yr : (rY p).Disjoint (rR p used)
  ys : (rY p).Disjoint (rS p)
  ya : (rY p).Disjoint (rA p)
  ds : (rD p).Disjoint (rS p)
  rs : (rR p used).Disjoint (rS p)
  sa : (rS p).Disjoint (rA p)
  nx : p.xp.toNat + p.len ≤ 2 ^ 64
  ny : p.yp.toNat + p.len ≤ 2 ^ 64
  nd : p.dp.toNat + p.dlen ≤ 2 ^ 64
  nr : (p.rp + BitVec.ofNat 64 used).toNat + p.len ≤ 2 ^ 64
  ns : p.B.toNat + p.Z ≤ 2 ^ 64
  len : Spec.Ffdh.pLenValid p.len
  dlen : Spec.Ffdh.domainLenValid p.len p.dlen
  scratch : Spec.Rsa.scratchWords p.len ≤ p.Z / 8
  z8 : p.Z / 8 * 8 = p.Z
  len64 : p.len < 2 ^ 64
  dlen64 : p.dlen < 2 ^ 64

private theorem sub_tape {r : Addr} {n used len : Nat}
    (hu : used + len ≤ n) : Region.Sub ⟨r + BitVec.ofNat 64 used, len⟩ ⟨r, n⟩ :=
  Offset.sub_base r hu

private theorem nowrap_tape {r : Addr} {n used len : Nat} (hn : r.toNat + n ≤ 2 ^ 64)
    (hu : used + len ≤ n) : (r + BitVec.ofNat 64 used).toNat + len ≤ 2 ^ 64 := by
  have hul : used < 2 ^ 64 ∨ len = 0 := by omega_using [hn, hu]
  rcases hul with hul | hz
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
    have := Nat.mod_le (r.toNat + used) (2 ^ 64)
    by_cases hz : r.toNat + used < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hz]; omega_using [hn, hu]
    · omega_using [hn, hu]
  · subst hz; simp only [Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _)

theorem rA_sub (p : KeyPublic) : Region.Sub (rA p) (below p.sp stackUse) := by
  rw [rA, callSp_eq]; exact Offset.sub_below _ (by decide) (by decide)

theorem KeyLive.callFacts {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen) :
    CallFacts p used := by
  have hi := h.input
  obtain ⟨_, hsp, _, _, hnw, hpw, hwr, hstk, hlen, hdlen, hx1, hx3, hscr, -, -, -, -⟩ := hi.1
  cases hi.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pxy, pxu, pxs, pxc⟩, ⟨pyu, pys, pyc⟩, ⟨pus, puc⟩, psc⟩ := hpw
  obtain ⟨⟨wxd, wxr, wxa⟩, ⟨wyd, wyr, wya⟩, -, ⟨wsd, wsr, wsa⟩, -⟩ := hwr
  obtain ⟨bx, by', -, bs, -, bd, br, -⟩ := hstk
  obtain ⟨nx, ny, -, ns, -, nd, nr, -⟩ := hnw
  have hX : rX (keyOfState original) = inX original := by
    simp only [rX, inX, keyOfState, hx1]
  have hY : rY (keyOfState original) = inY original := by
    simp only [rY, inY, keyOfState, hx3]
  have hD : rD (keyOfState original) = inDom original := rfl
  have hS : rS (keyOfState original) = inScr original := rfl
  have hR : Region.Sub (rR (keyOfState original) used) (inRand original) :=
    sub_tape hroom
  have hA := rA_sub (keyOfState original)
  have hsp' : (keyOfState original).sp = original.sp := rfl
  rw [hsp'] at hA
  rw [← hX] at pxy pxs wxd wxr bx nx
  rw [← hY] at pxy pys wyd wyr by' ny
  rw [← hD] at wxd wyd wsd bd nd
  rw [← hS] at pxs pys wsd wsr bs ns
  refine ⟨by rw [hsp']; exact hsp, pxy, wxd, wxr.sub_right hR, pxs, (bx.symm.sub_right hA),
    wyd, wyr.sub_right hR, pys, by'.symm.sub_right hA, wsd.symm, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, nx, ny, nd, nowrap_tape nr hroom, ns, hlen, hdlen, ?_, ?_, ?_, ?_⟩
  · simp only [keyOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [keyOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
  · exact BitVec.isLt _
  · exact BitVec.isLt _

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! # The attempt's arguments (AArch64) -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SearchProof/ReadOnly.lean`, which only this module imported.
section

/-! The context and original stack arguments survive every controller and callee write. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem KeyInput.context_frame {p : KeyPublic} {s : State} (h : KeyInput p s) {m m' : Mem}
 (hf : Frame (KeyInput.changes s) m m') :
 Spec.Rsa.wordsAt m' p.ctx p.ctxLen=Spec.Rsa.wordsAt m p.ctx p.ctxLen :=by
 rw [←h.2]
 unfold Spec.Rsa.wordsAt
 apply List.map_congr_left
 intro i hi
 apply hf.readW (r:=inContext s)
 · have inside : i<(stackArg s 6).toNat :=List.mem_range.mp hi
   have size:=h.nowrap (r:=inContext s) (by simp [inReads])
   change (stackArg s 5).toNat+(stackArg s 6).toNat*8≤2^64 at size
   exact Offset.contains_base _ (by omega_using [inside]) (by omega_using [inside, size])
 · exact h.read_disjoint (by simp [inReads])
 · decide

theorem KeyInput.argument_frame {p : KeyPublic} {s : State} (h : KeyInput p s) {m m' : Mem}
 (hf : Frame (KeyInput.changes s) m m') (j : Nat) (hj : j<7) :
 m'.readW (s.sp+BitVec.ofNat 64 (8*j)) 64=m.readW (s.sp+BitVec.ofNat 64 (8*j)) 64 :=by
 apply hf.readW (r:=inArgs s)
 · simp only [inArgs,stackArgAddr,Nat.mul_zero,BitVec.add_zero]
   exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
 · exact h.read_disjoint (by simp [inReads])
 · decide

theorem KeyLive.context_args {p : KeyPublic} {original s : State} {used keys scalars : Nat}
 (h : KeyLive p original used keys scalars s) :
 s.mem.readW (p.sp+40#64) 64=p.ctx ∧ s.mem.readW (p.sp+48#64) 64=BitVec.ofNat 64 p.ctxLen :=by
 have a:=h.input.argument_frame h.frame 5 (by decide)
 have b:=h.input.argument_frame h.frame 6 (by decide)
 rw [←h.input.sp_eq] at a b
 have ctx : original.mem.readW (p.sp+40#64) 64=p.ctx :=by
  have hctx :=congrArg KeyPublic.ctx h.input.2
  change stackArg original 5=p.ctx at hctx
  simpa only [stackArg,stackArgAddr,←h.input.sp_eq] using hctx
 have count : BitVec.ofNat 64 (stackArg original 6).toNat=BitVec.ofNat 64 p.ctxLen :=
  congrArg (BitVec.ofNat 64) (congrArg KeyPublic.ctxLen h.input.2)
 simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at count
 change original.mem.readW (original.sp+48#64) 64=BitVec.ofNat 64 p.ctxLen at count
 rw [←h.input.sp_eq] at count
 exact ⟨a.trans ctx,b.trans count⟩

theorem KeyLive.context_canonical {p : KeyPublic} {original s : State} {used keys scalars : Nat}
 (h : KeyLive p original used keys scalars s) :
 p.ctxLen=Spec.Ffdh.generationPrecomputedWords p.len ∧
 Spec.Ffdh.generationPrecompute p.len p.dom=some (Spec.Rsa.wordsAt s.mem p.ctx p.ctxLen) :=by
 rw [h.input.context_frame h.frame,←h.input.2]
 obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,count,canonical⟩:=h.input.1
 exact ⟨count,canonical⟩

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
end

end

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame_size
  controllerValue)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

/-- The attempt's stack arguments: `rand_len` (`p_len`), `scratch` and
`scratch_len`. -/
def callValues (p : KeyPublic) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 p.len), (1, p.B), (2, BitVec.ofNat 64 (p.Z / 8)),(3,p.ctx),(4,BitVec.ofNat 64 p.ctxLen)]

theorem callValues_bound (p : KeyPublic) : ∀ e ∈ callValues p, e.1 < 16 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The attempt's register arguments. -/
def KeyArgs (p : KeyPublic) (used : Nat) (t : State) : Prop :=
  t.gpr .x0 = p.xp ∧ t.gpr .x1 = BitVec.ofNat 64 p.len ∧ t.gpr .x2 = p.yp ∧
  t.gpr .x3 = BitVec.ofNat 64 p.len ∧ t.gpr .x4 = p.dp ∧ t.gpr .x5 = BitVec.ofNat 64 p.dlen ∧
  t.gpr .x6 = BitVec.ofNat 64 p.len ∧ t.gpr .x7 = p.rp + BitVec.ofNat 64 used

/-- The registers the arguments' block writes. -/
abbrev argRegsW : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x10, .x11,.x12,.x13]

theorem key_arguments_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block cachedArguments) (allocated 48 s) fun u =>
      (KeyArgs p used u ∧ u.mem = writeController s.mem (callSp p) (callValues p)) ∧
      Keep argRegsW (allocated 48 s) u := by
  have a := h.access
  have hw : ∀ d, d + 8 ≤ 48 → InRegions (⟨callSp p, 48⟩ :: s.wr) (callSp p + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨⟨callSp p, 48⟩, List.mem_cons_self .., Offset.contains_base _ hd (by omega_using [hd])⟩
  have hw0 : InRegions (⟨callSp p, 48⟩ :: s.wr) (callSp p) 8 := by
    simpa only [BitVec.add_zero] using hw 0 (by decide)
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ ⟨callSp p, 48⟩ :: s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun d hd => by
      obtain ⟨r, hr, hc⟩ := a.ld d hd
      refine ⟨r, ?_, hc⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv5 := h.header (j := 5) (v := p.xp) (by simp [KeyPublic.headers])
  have hv6 := h.header (j := 6) (v := p.yp) (by simp [KeyPublic.headers])
  have hv7 := h.header (j := 7) (v := p.dp) (by simp [KeyPublic.headers])
  have hv8 := h.header (j := 8) (v := BitVec.ofNat 64 p.dlen) (by simp [KeyPublic.headers])
  have hv9 := h.header (j := 9) (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  have hv12 := h.header (j := 12) (v := p.B) (by simp [KeyPublic.headers])
  have hv13 := h.header (j := 13) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv5 hv6 hv7 hv8 hv9 hv12 hv13
  have contextArgs:=h.context_args
  have spEq (d : Nat) : (allocated 48 s).sp+BitVec.ofNat 64 (64+d)=p.sp+BitVec.ofNat 64 d :=by
    simp only [allocated,h.sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [show -(16 : BitVec 64)+(-BitVec.ofNat 64 48+BitVec.ofNat 64 (64+d))=BitVec.ofNat 64 d by
      rw [BitVec.ofNat_add]
      simp only [←BitVec.add_assoc]
      change (0 : BitVec 64)+BitVec.ofNat 64 d=BitVec.ofNat 64 d
      exact BitVec.zero_add _]
  have readOriginal (j : Nat) (hj : j<7) :
    InRegions ((allocated 48 s).rd++(allocated 48 s).wr) (p.sp+BitVec.ofNat 64 (8*j)) 8 :=by
    obtain ⟨r,hr,hc⟩:=input_args h.input j hj
    refine ⟨r,?_,?_⟩
    · rw [allocated,h.rd]
      rcases List.mem_append.mp hr with hr|hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (by rw [h.wr];exact hr))
    · rw [h.input.sp_eq];exact hc
  have readCtx : InRegions ((allocated 48 s).rd++(allocated 48 s).wr) ((allocated 48 s).sp+104#64) 8 :=by
    change InRegions _ ((allocated 48 s).sp+BitVec.ofNat 64 (64+40)) 8
    rw [spEq 40]
    exact readOriginal 5 (by decide)
  have readLen : InRegions ((allocated 48 s).rd++(allocated 48 s).wr) ((allocated 48 s).sp+112#64) 8 :=by
    change InRegions _ ((allocated 48 s).sp+BitVec.ofNat 64 (64+48)) 8
    rw [spEq 48]
    exact readOriginal 6 (by decide)
  have ctxLoad :=exec_ldrSp_x' (t:=.x12) (allocated 48 s) (show 104%8=0 ∧ 104<32768 by decide) readCtx
  have lenLoad :=exec_ldrSp_x' (t:=.x13) ((allocated 48 s).write .x .x12 p.ctx) (show 112%8=0 ∧ 112<32768 by decide)
   (by simpa only [RegUpd.rd_write,RegUpd.wr_write,RegUpd.sp_write] using readLen)
  have ctxValue : s.mem.readW ((allocated 48 s).sp+104#64) 64=p.ctx :=by
    change s.mem.readW ((allocated 48 s).sp+BitVec.ofNat 64 (64+40)) 64=p.ctx
    rw [spEq 40];exact contextArgs.1
  have lenValue : s.mem.readW ((allocated 48 s).sp+112#64) 64=BitVec.ofNat 64 p.ctxLen :=by
    change s.mem.readW ((allocated 48 s).sp+BitVec.ofNat 64 (64+48)) 64=BitVec.ofNat 64 p.ctxLen
    rw [spEq 48];exact contextArgs.2
  simp only [allocated,h.sp] at ctxLoad lenLoad ctxValue lenValue
  refine WP.keep argRegsW ?_ (by decide) (by decide) (by decide +kernel)
  unfold cachedArguments arguments writeController callValues KeyArgs
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ctxLoad,lenLoad,ctxValue,lenValue,ldf, stf,allocated, h.sp, h.x19, exec_addSp (show 0 < 4096 by decide),
    hl 16 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide), hl 64 (by decide),
    hl 72 (by decide), hl 96 (by decide), hl 104 (by decide), hw0, hw 8 (by decide), hw 16 (by decide),hw 24 (by decide),hw 32 (by decide),
    hv2, hv5, hv6, hv7, hv8, hv9, hv12, hv13]
  simp only [off, Nat.mul_zero, BitVec.add_zero]

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end


/-! # One attempt of the key-generation controller (AArch64)

In its frame, the controller passes `vg_ffdh_generate_key_cached` the next `p_len`
octets of the tape. The attempt keeps the controller's state, and leaves
its status, and the key pair or zeros, in `x` and `y`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame_size
  controllerValue)
open VG.Proof.Ffdh.AArch64.Cached (attemptPre attemptPost attemptContract attemptDomain attemptRandom attemptParameters attemptScalar attempt_callable)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

/-- The regions the attempt reads: the domain, `p_len` octets of the tape at
`used`, and its stack arguments; those it writes: `x`, `y` and the working
space. -/
def callRd (p : KeyPublic) (used : Nat) : List Region := [rD p, rR p used,⟨p.ctx,p.ctxLen*8⟩,rA p]
def callWr (p : KeyPublic) : List Region := [rX p, rY p, rS p]

/-- The callee's entry, as the call makes it. -/
abbrev callState (p : KeyPublic) (used : Nat) (u : State) : State :=
  u.callEntry.withRegions (callRd p used) (callWr p)

theorem call_gpr {p : KeyPublic} {used : Nat} {u : State} {r : Reg} (hr : r ∉ linkRegs) :
    (callState p used u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem call_stackArg (p : KeyPublic) (used : Nat) (u : State) (j : Nat) :
    stackArg (callState p used u) j = stackArg u j := rfl

theorem call_args {p : KeyPublic} {u : State} {m : Mem} (hu : u.sp = callSp p)
    (hm : u.mem = writeController m (callSp p) (callValues p)) :
    stackArg u 0 = BitVec.ofNat 64 p.len ∧ stackArg u 1 = p.B ∧
      stackArg u 2 = BitVec.ofNat 64 (p.Z / 8) ∧ stackArg u 3=p.ctx ∧ stackArg u 4=BitVec.ofNat 64 p.ctxLen := by
  have hw (j : Nat) (hj : j < 5) : stackArg u j = controllerValue (callValues p) j (word m (callSp p) (8 * j)) := by
    unfold stackArg stackArgAddr
    rw [hu, hm]
    exact writeController_word _ _ _ (callValues_bound p) j (by omega_using [hj])
  refine ⟨?_, ?_, ?_,?_,?_⟩ <;> [rw [hw 0 (by decide)]; rw [hw 1 (by decide)]; rw [hw 2 (by decide)];rw [hw 3 (by decide)];rw [hw 4 (by decide)]] <;>
    simp only [callValues, controllerValue, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]

theorem callSp_toNat {p : KeyPublic} (hf : 64 ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 64 := by
  rw [callSp_eq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hf])]
  simp only [BitVec.toNat_ofNat]

/-- What an attempt at `used` leaves: its status, and the key pair for 1,
zeros otherwise. -/
def AttemptPost (p : KeyPublic) (rand : List Byte) (used : Nat) (t : State) : Prop :=
  let st := attemptStatus .cached p.a p.len (rand.drop used)
  let x := Spec.Ffdh.vettedScalarOfOctets p.a ((rand.drop used).take p.len)
  ((t.gpr .x0).setWidth 32).toNat = st ∧
    if st = 1 then
      Spec.Rsa.bytesAt t.mem p.xp p.len = Spec.Rsa.i2osp x p.len ∧
        Spec.Rsa.bytesAt t.mem p.yp p.len = Spec.Rsa.i2osp (Spec.Rsa.powMod p.a.g x p.a.p) p.len
    else Spec.Rsa.bytesAt t.mem p.xp p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt t.mem p.yp p.len = List.replicate p.len 0

theorem AttemptPost.keep {p : KeyPublic} {rand : List Byte} {used : Nat} {s t : State}
    (h : AttemptPost p rand used s) (hm : t.mem = s.mem)
    (hr : (t.gpr .x0).setWidth 32 = (s.gpr .x0).setWidth 32) : AttemptPost p rand used t := by
  unfold AttemptPost at h ⊢
  rw [hm, hr]
  exact h

theorem AttemptPost.frame {p : KeyPublic} {rand : List Byte} {used : Nat} {s t : State} {F : Region}
    (h : AttemptPost p rand used s) (hf : Frame [F] s.mem t.mem)
    (hx : (rX p).Disjoint F) (hy : (rY p).Disjoint F)
    (hr : (t.gpr .x0).setWidth 32 = (s.gpr .x0).setWidth 32) : AttemptPost p rand used t := by
  have ex : Spec.Rsa.bytesAt t.mem p.xp p.len = Spec.Rsa.bytesAt s.mem p.xp p.len :=
    List.map_congr_left fun i hi => lost_byte hf hx (List.mem_range.mp hi)
  have ey : Spec.Rsa.bytesAt t.mem p.yp p.len = Spec.Rsa.bytesAt s.mem p.yp p.len :=
    List.map_congr_left fun i hi => lost_byte hf hy (List.mem_range.mp hi)
  unfold AttemptPost at h ⊢
  rw [ex, ey, hr]
  exact h

section

variable {p : KeyPublic} {original s : State} {used keys scalars : Nat}

theorem call_covers_writes (h : KeyLive p original used keys scalars s) {u : State}
    (hw : u.wr = (allocated 48 s).wr) : Covers (callWr p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [hw]
  apply List.mem_cons_of_mem
  rw [h.wr, h.input.1.2.2.2.1]
  simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · show (⟨p.xp, p.len⟩ : Region) ∈ _; rw [← h.input.x_eq]; simp [inWrites]
  · show (⟨p.yp, p.len⟩ : Region) ∈ _; rw [← h.input.y_eq]; simp [inWrites]
  · rw [← h.input.2]; simp [inWrites, inScr, keyOfState]

theorem call_covers_reads (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    {u : State} (hrd : u.rd = (allocated 48 s).rd) (hw : u.wr = (allocated 48 s).wr) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  obtain ⟨-, -, hrd', -⟩ := hi.1
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨inDom original, ?_, 0, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inDom original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; simp only [BitVec.add_zero]; rfl
    · cases hi.2; simp only [Nat.zero_add]; exact Nat.le_refl _
  · refine ⟨inRand original, ?_, used, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inRand original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; rfl
    · cases hi.2; exact hroom
  · refine ⟨inContext original,?_,0,?_,?_⟩
    · rw [hrd];exact List.mem_append_left _ (by change inContext original∈s.rd;rw [h.rd,h.input.1.2.2.1];simp [inReads])
    · cases h.input.2;simp only [BitVec.add_zero];rfl
    · cases h.input.2;simp only [Nat.zero_add];exact Nat.le_refl _
  · refine ⟨⟨callSp p, 48⟩, ?_, 0, ?_, by show 0 + 40 ≤ 48; decide⟩
    · rw [hw]; refine List.mem_append_right _ ?_
      show _ ∈ (⟨s.sp - BitVec.ofNat 64 48, 48⟩ :: s.wr)
      rw [h.sp]; exact List.mem_cons_self ..
    · rw [BitVec.add_zero]

/-- What the attempt writes, as the controller sees it. -/
theorem attempt_frame (h : KeyLive p original used keys scalars s) {u t : State} {d : Nat}
    (hm : u.mem = writeController s.mem (callSp p) (callValues p))
    (hf : Frame (callWr p ++ [below u.sp (16 * d)]) u.mem t.mem) (hd : d = 0) :
    Frame (KeyInput.callChanges original) s.mem t.mem := by
  have hi := h.input
  have hsp : p.sp = original.sp := hi.sp_eq
  have h1 : Frame (KeyInput.callChanges original) s.mem u.mem := by
    rw [hm]
    apply (writeController_frame_size _ _ (callValues p) (size := 40) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨below original.sp stackUse, by simp [KeyInput.callChanges], ?_⟩
    rw [← hsp]
    exact rA_sub p
  have h2 : Frame (KeyInput.callChanges original) u.mem t.mem := by
    apply hf.sub
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨inX original, by simp [KeyInput.callChanges], by rw [hi.x_eq]; exact fun _ h => h⟩
      · exact ⟨inY original, by simp [KeyInput.callChanges], by rw [hi.y_eq]; exact fun _ h => h⟩
      · exact ⟨inScr original, by simp [KeyInput.callChanges], by
          rw [← hi.2]; exact fun _ h => h⟩
    · obtain rfl := List.mem_singleton.mp hr
      refine ⟨inX original, by simp [KeyInput.callChanges], fun a ha => ?_⟩
      subst hd
      simp only [Region.Contains, Nat.mul_zero] at ha
      omega
  exact h1.trans h2

/-- The attempt's view of the domain and the tape, at its entry. -/
theorem call_inputs (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hf : CallFacts p used) {u : State}
    (hm : u.mem = writeController s.mem (callSp p) (callValues p)) (hu : u.sp = callSp p)
    (ha : KeyArgs p used u) :
    attemptDomain (callState p used u) = p.dom ∧
      attemptRandom (callState p used u) = ((keyRand original).drop used).take p.len ∧
      ((callState p used u).gpr .x6).toNat = p.len := by
  have hfr : Frame (KeyInput.changes original) s.mem u.mem :=
    frame_of_callChanges original (attempt_frame (t := u) (d := 0) h hm (by
      intro x _; rfl) rfl)
  obtain ⟨h0, -, -, -, -⟩ := call_args hu hm
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have hdl : (BitVec.ofNat 64 p.dlen).toNat = p.dlen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64]
  refine ⟨?_, ?_, by rw [call_gpr (by decide), ha.2.2.2.2.2.2.1, hlen]⟩
  · simp only [attemptDomain, call_gpr (by decide : Reg.x4 ∉ linkRegs), call_gpr (by decide : Reg.x5 ∉ linkRegs),
      ha.2.2.2.2.1, ha.2.2.2.2.2.1, hdl, State.withRegions_mem, State.callEntry_mem]
    exact (h.input.domain_frame hfr).trans h.domain
  · simp only [attemptRandom, call_gpr (by decide : Reg.x7 ∉ linkRegs), call_stackArg, ha.2.2.2.2.2.2.2, h0, hlen,
      State.withRegions_mem, State.callEntry_mem]
    have hr := (h.input.random_frame hfr).trans h.random
    rw [← VG.Proof.Dsa.bytesAt_slice _ _ hroom, ← hr]

theorem call_attempt_pre {p : KeyPublic} {original s : State} {used keys scalars : Nat}
 (h : KeyLive p original used keys scalars s) (hroom : used+p.len≤p.randLen) (hf : CallFacts p used)
 {u : State} (hu : u.sp=callSp p) (ha : KeyArgs p used u)
 (hm : u.mem=writeController s.mem (callSp p) (callValues p)) : attemptPre (callState p used u) :=by
 obtain ⟨h0,h1,h2,h3,h4⟩:=call_args hu hm
 obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7⟩:=ha
 have hlen : (BitVec.ofNat 64 p.len).toNat=p.len :=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hf.len64]
 have hdl : (BitVec.ofNat 64 p.dlen).toNat=p.dlen :=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hf.dlen64]
 have hzw : (BitVec.ofNat 64 (p.Z/8)).toNat=p.Z/8 :=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have :=hf.ns;omega_using [this])]
 have cx : (⟨p.ctx,p.ctxLen*8⟩ : Region)=inContext original :=by rw [←h.input.2];rfl
 have xx : rX p=inX original :=h.input.x_eq.symm
 have yy : rY p=inY original :=h.input.y_eq.symm
 have ss : rS p=inScr original :=by rw [←h.input.2];rfl
 have nc : p.ctx.toNat+p.ctxLen*8≤2^64 :=by
  have n:=h.input.nowrap (r:=inContext original) (by simp [inReads]);rw [←cx] at n;exact n
 have ctx64 : p.ctxLen<2^64 :=by omega_using [nc]
 have hcl : (BitVec.ofNat 64 p.ctxLen).toNat=p.ctxLen :=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt ctx64]
 have xc : (rX p).Disjoint ⟨p.ctx,p.ctxLen*8⟩ :=by rw [xx,cx];exact h.input.write_disjoint (by simp [inWrites]) (by simp [inReads])
 have yc : (rY p).Disjoint ⟨p.ctx,p.ctxLen*8⟩ :=by rw [yy,cx];exact h.input.write_disjoint (by simp [inWrites]) (by simp [inReads])
 have sc : (rS p).Disjoint ⟨p.ctx,p.ctxLen*8⟩ :=by rw [ss,cx];exact h.input.write_disjoint (by simp [inWrites]) (by simp [inReads])
 have frameU:=frame_of_callChanges original (attempt_frame (t:=u) (d:=0) h hm (Frame.refl _ _) rfl)
 have same:=h.input.context_frame frameU
 have canonical:=h.context_canonical
 have inputs:=call_inputs h hroom hf hm hu ⟨r0,r1,r2,r3,r4,r5,r6,r7⟩
 have domainValid : Spec.Ffdh.domainValid p.len (attemptDomain (callState p used u))=true :=by rw [inputs.1];exact h.input.domain_valid
 have contextValid : Spec.Ffdh.generationContextAt u.mem p.ctx p.ctxLen p.len (attemptDomain (callState p used u)) :=by
  rw [inputs.1]
  exact ⟨canonical.1,by rw [same];exact canonical.2⟩
 have hsp:=callSp_toNat hf.room
 have hlt:=p.sp.isLt
 unfold attemptPre
 simp only [call_gpr (by decide : Reg.x0∉linkRegs),call_gpr (by decide : Reg.x1∉linkRegs),
  call_gpr (by decide : Reg.x2∉linkRegs),call_gpr (by decide : Reg.x3∉linkRegs),
  call_gpr (by decide : Reg.x4∉linkRegs),call_gpr (by decide : Reg.x5∉linkRegs),
  call_gpr (by decide : Reg.x6∉linkRegs),call_gpr (by decide : Reg.x7∉linkRegs),
  call_stackArg,h0,h1,h2,h3,h4,r0,r1,r2,r3,r4,r5,r6,r7,hlen,hdl,hzw,hcl,hf.z8,
  State.withRegions_rd,State.withRegions_wr,stackArgAddr,State.withRegions_sp,State.callEntry_sp,hu,Nat.mul_zero,BitVec.add_zero]
 refine ⟨by omega_using [hsp],rfl,rfl,hf.xy,hf.xd,hf.xr,hf.xs,xc,hf.xa,hf.yd,hf.yr,hf.ys,yc,hf.ya,
  hf.ds,hf.rs,sc,hf.sa,hf.nx,hf.ny,hf.nd,hf.nr,hf.ns,nc,hf.len,hf.dlen,True.intro,True.intro,True.intro,hf.scratch,?_,?_⟩
 · simpa only [call_gpr (by decide : Reg.x4∉linkRegs),call_gpr (by decide : Reg.x5∉linkRegs),r4,r5,hdl] using domainValid
 · simpa only [State.withRegions_mem,State.callEntry_mem] using contextValid

/-- The outputs are apart from the stack the search uses. -/
theorem KeyInput.outStack {p : KeyPublic} {original : State} (hi : KeyInput p original) :
    (rX p).Disjoint (below p.sp stackUse) ∧ (rY p).Disjoint (below p.sp stackUse) := by
  obtain ⟨_, _, _, _, _, _, _, hstk, _, _, hx1, hx3, _, -, -, -, -⟩ := hi.1
  cases hi.2
  simp only [inWrites, inReads, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append] at hstk
  obtain ⟨bx, by', -⟩ := hstk
  have hX : rX (keyOfState original) = inX original := by
    simp only [rX, inX, keyOfState, hx1]
  have hY : rY (keyOfState original) = inY original := by
    simp only [rY, inY, keyOfState, hx3]
  rw [← hX] at bx
  rw [← hY] at by'
  exact ⟨bx.symm, by'.symm⟩

theorem key_attempt_run (a : Attempt) (h : KeyLive p original used keys scalars s)
    (hroom : used + p.len ≤ p.randLen) :
    WP isa (attemptRun a.call) s fun t =>
      KeyLive p original used keys scalars t ∧ AttemptPost p (keyRand original) used t := by
  have hf := h.callFacts hroom
  have hroom' : 48 ≤ s.sp.toNat := by
    have := hf.room
    have h16 : (p.sp - BitVec.ofNat 64 16).toNat = p.sp.toNat - 16 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [this])]
      simp only [BitVec.toNat_ofNat]
    rw [h.sp, show (p.sp - 16 : Addr) = p.sp - BitVec.ofNat 64 16 from rfl, h16]
    omega_using [this]
  unfold attemptRun
  refine WP.alloc (by decide) hroom' ?_
  refine WP.seq (WP.mono (key_arguments_ok h) fun u ⟨⟨ha, hm⟩, k⟩ => ?_)
  have hu : u.sp = callSp p := by rw [k.sp]; show s.sp - BitVec.ofNat 64 48 = _; rw [h.sp]
  refine WP.callFV (k := attemptContract) (attempt_callable a.M) (call_attempt_pre h hroom hf hu ha hm)
    (call_covers_reads h hroom k.rd k.wr) (call_covers_writes h k.wr) ?_ (by rw [a.depth]; decide)
  intro t hrd hwr hsp hfr hcs hvs hpost m u f
  have hA : Region.Sub ⟨s.sp - BitVec.ofNat 64 48, 48⟩ (below p.sp stackUse) := by
    rw [h.sp, show (p.sp - 16 : Addr) - BitVec.ofNat 64 48 = callSp p from rfl, callSp_eq]
    exact Region.sub_prefix (by decide)
  have hA' : ∀ R ∈ [(⟨s.sp - BitVec.ofNat 64 48, 48⟩ : Region)],
      ∃ R' ∈ KeyInput.callChanges original, Region.Sub R R' := by
    intro R hR
    obtain rfl := List.mem_singleton.mp hR
    refine ⟨below original.sp stackUse, by simp [KeyInput.callChanges], ?_⟩
    rw [← h.input.sp_eq]
    exact hA
  refine ⟨?_, ?_⟩
  · -- The loop state, after the frame.
    apply h.restore (t := { freed 48 t with mem := m, unknowns := u })
      (show (freed 48 t).rd = s.rd from hrd.trans k.rd)
      (show (freed 48 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.wr]; rfl)
    · change t.sp + BitVec.ofNat 64 48 = s.sp
      rw [hsp, k.sp]
      exact BitVec.sub_add_cancel _ _
    · intro r hr h30
      exact (hcs r hr h30).trans (k.gpr r (by revert r hr; decide))
    · intro r hr
      exact (hvs r hr).trans (k.vcs r hr)
    · exact (attempt_frame h hm hfr a.depth).trans (f.sub hA')
  · -- The attempt's status and outputs.
    refine AttemptPost.frame (s := t) ?_ f ((h.input.outStack).1.sub_right hA) ((h.input.outStack).2.sub_right hA) rfl
    obtain ⟨hdom, hrand, h6⟩ := call_inputs h hroom hf hm hu ha
    have hp := hpost
    simp only [attemptContract, attemptPost, attemptParameters, attemptScalar, hdom, hrand, h6] at hp
    obtain ⟨hst, hout⟩ := hp
    simp only [call_gpr (by decide : Reg.x0 ∉ linkRegs), call_gpr (by decide : Reg.x2 ∉ linkRegs),
      ha.1, ha.2.2.1, State.withRegions_gpr, State.withRegions_mem] at hst hout
    unfold AttemptPost
    exact ⟨hst, hout⟩

end

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! ### `Ffdh.AArch64.Cached.SearchProof.Classify`, which only this module used -/

section

/-! # After an attempt: the key, or one fewer scalar or key (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

theorem exec_addImm_w {s : State} {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.addImm .w d n imm) s = some (s.write .w d ((s.gpr n).setWidth 32 + BitVec.ofNat 32 imm)) := by
  simp [exec, h, State.read]

theorem sub_beq : ∀ st < 4, ∀ k < 4,
    ((BitVec.ofNat 64 st - BitVec.ofNat 64 k) == 0) = decide (st = k) := by decide

/-- The status `x9` minus `k`, compared with zero. -/
theorem test_ok {s : State} {st k : Nat} (h9 : s.gpr .x9 = BitVec.ofNat 64 st) (hst : st < 4)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    WP isa (.block (test k)) s fun t =>
      (isa.eval (.zero .x .x10) t = some (decide (st = k)) ∧ t.mem = s.mem) ∧ Keep [.x10] s t := by
  have hk4 : k < 4 := by omega_using [hk]
  rcases hk with rfl | rfl | rfl <;>
  · refine WP.keep [.x10] ?_ (by decide) (by decide) (by decide +kernel)
    unfold test
    brun [h9]
    have hb := sub_beq st hst _ hk4
    simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq,
      Option.some.injEq] at hb ⊢
    exact hb

/-- The controller's word-only writes keep `x` and `y`. -/
theorem output_frame {p : KeyPublic} {original : State} (hi : KeyInput p original) {m m' : Mem}
    (hf : Frame [⟨p.control, 128⟩] m m') :
    Spec.Rsa.bytesAt m' p.xp p.len = Spec.Rsa.bytesAt m p.xp p.len ∧
      Spec.Rsa.bytesAt m' p.yp p.len = Spec.Rsa.bytesAt m p.yp p.len := by
  have hk := hi.len_lt
  have hpw := hi.writes_pairwise
  have hx : (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
    simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hpw
    have := hpw.1.2.2.2
    rwa [hi.x_eq, show inCtl original = ⟨p.control, 128⟩ by rw [← hi.2]; rfl] at this
  have hy : (⟨p.yp, p.len⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
    simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hpw
    have := hpw.2.1.2.2
    rwa [hi.y_eq, show inCtl original = ⟨p.control, 128⟩ by rw [← hi.2]; rfl] at this
  constructor <;> simp only [Spec.Rsa.bytesAt] <;> refine List.map_congr_left fun i hi => ?_
  · exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hx)
      (show p.len ≤ 2 ^ 64 by omega_using [hk]) (List.mem_range.mp hi)
  · exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hy)
      (show p.len ≤ 2 ^ 64 by omega_using [hk]) (List.mem_range.mp hi)

/-- The octets consumed by an attempt. -/
def advanceValues (p : KeyPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(9, p.rp + BitVec.ofNat 64 (used + p.len)), (10, BitVec.ofNat 64 (p.randLen - (used + p.len))),
    (11, BitVec.ofNat 64 (used + p.len))]

theorem advanceValues_bound (p : KeyPublic) (used : Nat) : ∀ e ∈ advanceValues p used, e.1 < 16 := by
  simp only [advanceValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem key_advance_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen) :
    WP isa (.block advance) s fun t =>
      (t.mem = writeController s.mem p.control (advanceValues p used) ∧
        t.gpr .x9 = ((s.gpr .x0).setWidth 32).setWidth 64) ∧
        Keep [.x9, .x11, .x12, .x13, .x14] s t := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv9 := h.header (j := 9) (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  have hv10 := h.header (j := 10) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [KeyPublic.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv9 hv10 hv11
  have hlen : p.randLen < 2 ^ 64 := by
    rw [← h.input.2]; exact BitVec.isLt _
  have e9 : p.rp + BitVec.ofNat 64 used + BitVec.ofNat 64 p.len = p.rp + BitVec.ofNat 64 (used + p.len) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have e10 : BitVec.ofNat 64 (p.randLen - used) - BitVec.ofNat 64 p.len =
      BitVec.ofNat 64 (p.randLen - (used + p.len)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by
      simp only [BitVec.le_def, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega_using [hroom, hlen]), Nat.mod_eq_of_lt (by omega_using [hlen])]; omega_using [hroom])]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [hlen]), Nat.mod_eq_of_lt (by omega_using [hroom, hlen]), Nat.mod_eq_of_lt (by omega_using [hlen])]
    omega_using []
  have e11 : BitVec.ofNat 64 used + BitVec.ofNat 64 p.len = BitVec.ofNat 64 (used + p.len) := by
    rw [← BitVec.ofNat_add]
  refine WP.keep [.x9, .x11, .x12, .x13, .x14] ?_ (by decide) (by decide) (by decide +kernel)
  unfold advance writeController advanceValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.x19, exec_addImm_w (show 0 < 4096 by decide), hv2, hv9, hv10, hv11,
    a.ld 16 (by decide), a.ld 72 (by decide), a.ld 80 (by decide), a.ld 88 (by decide),
    a.st 72 (by decide), a.st 80 (by decide), a.st 88 (by decide), e9, e10, e11]
  rw [BitVec.add_zero]

/-- The status, normalized, and the attempt's octets consumed. -/
theorem key_classify_head {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hp : AttemptPost p (keyRand original) used s) :
    WP isa (.block (advance ++ test 1)) s fun t =>
      KeyLive p original (used + p.len) keys scalars t ∧ AttemptPost p (keyRand original) used t ∧
      t.gpr .x9 = BitVec.ofNat 64 (attemptStatus .cached p.a p.len ((keyRand original).drop used)) ∧
      isa.eval (.zero .x .x10) t =
        some (decide (attemptStatus .cached p.a p.len ((keyRand original).drop used) = 1)) := by
  have hst : attemptStatus .cached p.a p.len ((keyRand original).drop used) < 4 := by
    rcases attemptStatus_cases (policy:=.cached) p.a p.len ((keyRand original).drop used) with he | he | he <;> omega_using [he]
  rw [WP.block_append_iff]
  refine WP.mono (key_advance_ok h hroom) fun v ⟨⟨hmv, h9⟩, kv⟩ => ?_
  have hb := advanceValues_bound p used
  have hh : Slots v.mem p.control (p.headers (used + p.len) keys scalars) := by
    refine headers_after _ hb hmv ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, advanceValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  have hv := h.update (u := used + p.len) (k := keys) (c := scalars) hroom h.keys_le h.scalars_le _
    hb (by simp only [advanceValues, List.mem_cons, List.not_mem_nil, or_false]
           rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hmv kv.mono hh
  have hout := output_frame h.input (hmv ▸ writeController_frame s.mem p.control _ hb)
  have hpv : AttemptPost p (keyRand original) used v := by
    unfold AttemptPost at hp ⊢
    rw [hout.1, hout.2, kv.gpr .x0 (by decide)]
    exact hp
  have h9' : v.gpr .x9 = BitVec.ofNat 64 (attemptStatus .cached p.a p.len ((keyRand original).drop used)) := by
    rw [h9]
    apply BitVec.eq_of_toNat_eq
    have := hp.1
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this ⊢
    omega_using [this]
  refine WP.mono (test_ok h9' hst (.inl rfl)) fun t ⟨⟨he, hmt⟩, kt⟩ => ?_
  exact ⟨hv.keep kt hmt, hpv.keep hmt (by rw [kt.gpr .x0 (by decide)]),
    (kt.gpr .x9 (by decide)).trans h9', he⟩

/-- The scalar of the attempt at `used`. -/
abbrev KeyPublic.scalarAt (p : KeyPublic) (rand : List Byte) (used : Nat) : Nat :=
  Spec.Ffdh.vettedScalarOfOctets p.a ((rand.drop used).take p.len)

/-- The key search's result for an accepted attempt at `used`. -/
def acceptedResult (p : KeyPublic) (rand : List Byte) (used : Nat) : Spec.Ffdh.KeySearchResult :=
  ⟨.accepted (p.scalarAt rand used) (Spec.Rsa.powMod p.a.g (p.scalarAt rand used) p.a.p),
    used + p.len, [1]⟩

/-- Where an attempt at `used` leads. -/
def KeyClassified (p : KeyPublic) (original : State) (used keys scalars : Nat) (t : State) : Prop :=
  let st := attemptStatus .cached p.a p.len ((keyRand original).drop used)
  if st = 1 then KeyDone p original (acceptedResult p (keyRand original) used) t
  else if st = 2 then KeyLive p original (used + p.len) keys (scalars - 1) t ∧ word t.mem p.control 112 = 4
  else KeyLive p original (used + p.len) (keys - 1) 128 t ∧ word t.mem p.control 112 = 4

/-- A terminal status written over a loop state, whose outputs are already
the result's. -/
theorem key_terminal_done {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (status : Nat) (hst : status = 1 ∨ status = 3)
    {r : Spec.Ffdh.KeySearchResult} (hu : r.used = used) (hs : r.status = status)
    (hr : r.retries = ⟨0, 0⟩) (ho : KeyOutput p r s.mem) :
    WP isa (.block (terminal status)) s (KeyDone p original r) := by
  refine WP.mono (key_terminal_live h hst) fun t ⟨ht, hm⟩ => ?_
  have hb := terminalValues_bound status
  have hst0 : status ≠ 0 := by omega_using [hst]
  have hw (j : Nat) (hj : j < 16) : word t.mem p.control (8 * j) =
      controllerValue (terminalValues status) j (word s.mem p.control (8 * j)) := by
    rw [hm, writeController_word _ _ _ hb j hj]
  have hout := output_frame h.input (hm ▸ writeController_frame s.mem p.control _ hb)
  refine ht.done hu ?_ ?_ ?_
  · rw [show (112 : Nat) = 8 * 14 from rfl, hw 14 (by decide)]
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false, hs]
  · change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
      word t.mem p.control (8 * 3)] = _
    rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)]
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_false, KeyPublic.policy, hr, hs, hst0]
    rw [h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])]
    rfl
  · unfold KeyOutput at ho ⊢
    rw [hout.1, hout.2]
    exact ho

theorem key_classify {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hk : 0 < keys) (hs : 0 < scalars) (hp : AttemptPost p (keyRand original) used s) :
    WP isa classify s (KeyClassified p original used keys scalars) := by
  unfold classify
  refine WP.seq (WP.mono (key_classify_head h hroom hp) fun u ⟨hu, hpu, hax, he⟩ => ?_)
  rcases attemptStatus_cases (policy:=.cached) p.a p.len ((keyRand original).drop used) with h1 | h2 | h3
  · rw [h1] at he
    refine WP.ite true he (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_terminal_done (r := acceptedResult p (keyRand original) used) hu 1 (.inl rfl)
      rfl rfl rfl ?_) fun t ht => ?_
    rotate_left
    · dsimp only [KeyClassified]; rw [ite_eq_left h1]; exact ht
    have hpu' := hpu
    unfold AttemptPost at hpu'
    simp only [h1, ite_true] at hpu'
    exact hpu'.2
  · rw [h2] at he hax
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (test_ok hax (by decide) (.inr (.inl rfl)))
      fun v ⟨⟨he2, hmv⟩, kv⟩ => ?_)
    have hv := hu.keep kv hmv
    refine WP.ite true he2 (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_rejected_scalar hv hs) fun t ht => ?_
    dsimp only [KeyClassified]
    rw [ite_eq_right (by rw [h2]; decide), ite_eq_left h2]
    exact ht
  · rw [h3] at he hax
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (test_ok hax (by decide) (.inr (.inl rfl)))
      fun v ⟨⟨he2, hmv⟩, kv⟩ => ?_)
    have hv := hu.keep kv hmv
    refine WP.ite false he2 (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (test_ok ((kv.gpr .x9 (by decide)).trans hax) (by decide) (.inr (.inr rfl)))
      fun w ⟨⟨he3, hmw⟩, kw⟩ => ?_)
    have hw := hv.keep kw hmw
    refine WP.ite true he3 (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_rejected_public hw hk) fun t ht => ?_
    dsimp only [KeyClassified]
    rw [ite_eq_right (by rw [h3]; decide), ite_eq_right (by rw [h3]; decide)]
    exact ht

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end


/-! # Total correctness of the key-generation controller's loop (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Ffdh.GenerationSearch
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

/-- The loop's state: the search from octet `used`, with `keys` and `scalars`
left, leads to the expected result. -/
def KeyInvariant (p : KeyPublic) (original : State) (expected : Spec.Ffdh.KeySearchResult)
    (n : Nat) (s : State) : Prop :=
  ∃ used keys scalars, n = 128 * keys + scalars + 1 ∧ KeyLive p original used keys scalars s ∧
    expected.outcome = (p.tail (keyRand original) used keys scalars).outcome ∧
    expected.used = (p.tail (keyRand original) used keys scalars).used

theorem KeyLive.rand_length {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) : (keyRand original).length = p.randLen := by
  rw [← h.random]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]

theorem key_iteration (a : Attempt) {p : KeyPublic} {original s : State}
    {expected : Spec.Ffdh.KeySearchResult} {n : Nat}
    (h : KeyInvariant p original expected n s) :
    WP isa (iteration a.call) s fun t =>
      (isa.eval (.zero .x .x9) t = some false ∧ KeyDone p original expected t) ∨
      (isa.eval (.zero .x .x9) t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) := by
  obtain ⟨used, keys, scalars, hn, h, ho, hu⟩ := h
  have hlen := h.rand_length
  have done : ∀ (r : Spec.Ffdh.KeySearchResult) t, KeyDone p original r t →
      r.outcome = (p.tail (keyRand original) used keys scalars).outcome →
      r.used = (p.tail (keyRand original) used keys scalars).used →
      WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) t fun t =>
        (isa.eval (.zero .x .x9) t = some false ∧ KeyDone p original expected t) ∨
        (isa.eval (.zero .x .x9) t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) :=
    fun _ _ hd hro hru => WP.mono (done_loop_guard hd) fun _ ⟨hq, hdq⟩ =>
      Or.inl ⟨hq, hdq.congr (hro.trans ho.symm) (hru.trans hu.symm)⟩
  unfold iteration
  refine WP.seq (WP.mono (keys_guard h) fun u ⟨hu1, he⟩ => ?_)
  apply WP.seq
  unfold branch
  refine WP.ite (decide (keys = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    refine WP.mono (key_exhausted hu1) fun t ht => done _ t ht ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_exhausted (Or.inl hz')]
  intro hnz
  have hk : keys ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (scalars_guard hu1) fun u ⟨hu2, he2⟩ => ?_)
  refine WP.ite (decide (scalars = 0)) he2 ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    refine WP.mono (key_exhausted hu2) fun t ht => done _ t ht ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_exhausted (Or.inr hz')]
  intro hnz2
  have hs : scalars ≠ 0 := of_decide_eq_false hnz2
  unfold attemptOrRequest
  refine WP.seq (WP.mono (room_guard hu2) fun u ⟨hu3, hb⟩ => ?_)
  refine WP.ite _ hb ?_ ?_
  · intro hshort
    have hr : (keyRand original).length - used < p.len := by
      rw [hlen]; exact of_decide_eq_true hshort
    refine WP.mono (key_request hu3) fun t ht => done _ t ht ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_short hk hs hr]
  intro hlong
  have hroom : used + p.len ≤ p.randLen := by
    have := of_decide_eq_false hlong; have := h.used_le; omega_arith
  have hr : p.len ≤ (keyRand original).length - used := by rw [hlen]; omega_using [hroom]
  refine WP.seq (WP.mono (key_attempt_run a hu3 hroom) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (key_classify ht hroom (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hs) hp)
    fun q hq => ?_
  rcases attemptStatus_cases (policy:=.cached) p.a p.len ((keyRand original).drop used) with h1 | h2 | h3
  · simp only [KeyClassified, h1, ite_true] at hq
    refine done _ q hq ?_ ?_ <;> simp only [KeyPublic.tail, keyTail_accepted hk hs hr h1] <;> rfl
  · simp only [KeyClassified, h2, Nat.reduceEqDiff, ite_true, ite_false] at hq
    refine WP.mono (live_loop_guard hq.1 hq.2) fun z ⟨hz, hzl⟩ => Or.inr ⟨hz, _, ?_,
      used + p.len, keys, scalars - 1, rfl, hzl, ?_, ?_⟩
    · omega_using [hn, hs]
    · rw [ho]; simp only [KeyPublic.tail, keyTail_scalar hk hs hr h2]
    · rw [hu]; simp only [KeyPublic.tail, keyTail_scalar hk hs hr h2]
  · simp only [KeyClassified, h3, Nat.reduceEqDiff, ite_false] at hq
    refine WP.mono (live_loop_guard hq.1 hq.2) fun z ⟨hz, hzl⟩ => Or.inr ⟨hz, _, ?_,
      used + p.len, keys - 1, 128, rfl, hzl, ?_, ?_⟩
    · omega_using [hn, hk, hs]
    · rw [ho]; simp only [KeyPublic.tail, keyTail_public hk hs hr h3]
    · rw [hu]; simp only [KeyPublic.tail, keyTail_public hk hs hr h3]

theorem key_loop (a : Attempt) {p : KeyPublic} {original s : State}
    {expected : Spec.Ffdh.KeySearchResult} {n : Nat}
    (h : KeyInvariant p original expected n s) :
    WP isa (.loop (iteration a.call) (.zero .x .x9)) s (KeyDone p original expected) :=
  WP.loop (M := isa) (body := iteration a.call) (c := .zero .x .x9)
    (Q := KeyDone p original expected) (KeyInvariant p original expected)
    (fun _ _ h => key_iteration a h) n s h

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
