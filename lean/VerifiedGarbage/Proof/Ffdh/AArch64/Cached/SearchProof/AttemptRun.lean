module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Arguments
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptContract
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Outputs
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Live

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
    exact writeController_word _ _ _ (callValues_bound p) j (by omega)
  refine ⟨?_, ?_, ?_,?_,?_⟩ <;> [rw [hw 0 (by decide)]; rw [hw 1 (by decide)]; rw [hw 2 (by decide)];rw [hw 3 (by decide)];rw [hw 4 (by decide)]] <;>
    simp only [callValues, controllerValue, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]

theorem callSp_toNat {p : KeyPublic} (hf : 64 ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 64 := by
  rw [callSp_eq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
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
 have hzw : (BitVec.ofNat 64 (p.Z/8)).toNat=p.Z/8 :=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have :=hf.ns;omega)]
 have cx : (⟨p.ctx,p.ctxLen*8⟩ : Region)=inContext original :=by rw [←h.input.2];rfl
 have xx : rX p=inX original :=h.input.x_eq.symm
 have yy : rY p=inY original :=h.input.y_eq.symm
 have ss : rS p=inScr original :=by rw [←h.input.2];rfl
 have nc : p.ctx.toNat+p.ctxLen*8≤2^64 :=by
  have n:=h.input.nowrap (r:=inContext original) (by simp [inReads]);rw [←cx] at n;exact n
 have ctx64 : p.ctxLen<2^64 :=by omega
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
 refine ⟨by omega,rfl,rfl,hf.xy,hf.xd,hf.xr,hf.xs,xc,hf.xa,hf.yd,hf.yr,hf.ys,yc,hf.ya,
  hf.ds,hf.rs,sc,hf.sa,hf.nx,hf.ny,hf.nd,hf.nr,hf.ns,nc,hf.len,hf.dlen,True.intro,True.intro,True.intro,hf.scratch,?_,?_⟩
 · simpa only [call_gpr (by decide : Reg.x4∉linkRegs),call_gpr (by decide : Reg.x5∉linkRegs),r4,r5,hdl] using domainValid
 · simpa only [State.withRegions_mem,State.callEntry_mem] using contextValid

theorem key_attempt_run (a : Attempt) (h : KeyLive p original used keys scalars s)
    (hroom : used + p.len ≤ p.randLen) :
    WP isa (attemptRun a.call) s fun t =>
      KeyLive p original used keys scalars t ∧ AttemptPost p (keyRand original) used t := by
  have hf := h.callFacts hroom
  have hroom' : 48 ≤ s.sp.toNat := by
    have := hf.room
    have h16 : (p.sp - BitVec.ofNat 64 16).toNat = p.sp.toNat - 16 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
      simp only [BitVec.toNat_ofNat]
    rw [h.sp, show (p.sp - 16 : Addr) = p.sp - BitVec.ofNat 64 16 from rfl, h16]
    omega
  unfold attemptRun
  refine WP.alloc (by decide) hroom' ?_
  refine WP.seq (WP.mono (key_arguments_ok h) fun u ⟨⟨ha, hm⟩, k⟩ => ?_)
  have hu : u.sp = callSp p := by rw [k.sp]; show s.sp - BitVec.ofNat 64 48 = _; rw [h.sp]
  refine WP.callFV (k := attemptContract) (attempt_callable a.M) (call_attempt_pre h hroom hf hu ha hm)
    (call_covers_reads h hroom k.rd k.wr) (call_covers_writes h k.wr) ?_ (by rw [a.depth]; decide)
  intro t hrd hwr hsp hfr hcs hvs hpost
  refine ⟨?_, ?_⟩
  · -- The loop state, after the frame.
    apply h.restore (show (freed 48 t).rd = s.rd from hrd.trans k.rd)
      (show (freed 48 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.wr]; rfl)
    · change t.sp + BitVec.ofNat 64 48 = s.sp
      rw [hsp, k.sp]
      exact BitVec.sub_add_cancel _ _
    · intro r hr h30
      exact (hcs r hr h30).trans (k.gpr r (by revert r hr; decide))
    · intro r hr
      exact (hvs r hr).trans (k.vcs r hr)
    · exact attempt_frame h hm hfr a.depth
  · -- The attempt's status and outputs.
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
