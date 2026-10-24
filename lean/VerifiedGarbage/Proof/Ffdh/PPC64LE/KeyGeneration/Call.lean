module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.CallFacts
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Live
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # One attempt of the key-generation controller (PPC64LE)

In its frame of 128 bytes, the controller passes `vg_ffdh_generate_key` the
next `p_len` octets of the tape, its stack arguments at offset 96 of the
frame. The attempt keeps the controller's state, and leaves its status, and
the key pair or zeros, in `x` and `y`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame_size
  controllerValue)
open VG.Proof.Ffdh.PPC64LE.GenerateKey (gkContract gkStack gkScalar)
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search

/-- The attempt's stack arguments: `rand_len` (`p_len`), `scratch` and
`scratch_len`, at offset 96 of its frame. -/
def callValues (p : KeyPublic) : List (Nat × BitVec 64) :=
  [(12, BitVec.ofNat 64 p.len), (13, p.B), (14, BitVec.ofNat 64 (p.Z / 8))]

theorem callValues_bound (p : KeyPublic) : ∀ e ∈ callValues p, e.1 < 16 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The attempt's register arguments. -/
def KeyArgs (p : KeyPublic) (used : Nat) (t : State) : Prop :=
  t.gpr .r3 = p.xp ∧ t.gpr .r4 = BitVec.ofNat 64 p.len ∧ t.gpr .r5 = p.yp ∧
  t.gpr .r6 = BitVec.ofNat 64 p.len ∧ t.gpr .r7 = p.dp ∧ t.gpr .r8 = BitVec.ofNat 64 p.dlen ∧
  t.gpr .r9 = BitVec.ofNat 64 p.len ∧ t.gpr .r10 = p.rp + BitVec.ofNat 64 used

/-- The registers the arguments' block writes. -/
abbrev argRegsW : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem callSp_eq' (p : KeyPublic) : p.sp - 48 - BitVec.ofNat 64 128 = callSp p := rfl

/-- The frame's push writes its back chain below the stack pointer. -/
theorem alloc_frame {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    Frame (KeyInput.callChanges original) s.mem (allocated 128 s).mem := by
  have hi := h.input
  refine Frame.write (Frame.refl _ _) (r := below original.sp stackUse) (by simp [KeyInput.callChanges]) _ ?_
  rw [h.sp, callSp_eq', callSp_eq, ← hi.sp_eq]
  exact Offset.contains_below p.sp (a := 176) (b := 176) (by decide) (by decide) (by decide)

theorem key_arguments_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block arguments) (allocated 128 s) fun u =>
      (KeyArgs p used u ∧ u.mem = writeController (allocated 128 s).mem (callSp p) (callValues p)) ∧
      Keep argRegsW (allocated 128 s) u := by
  have a := h.access
  have hc := h.input.control_frame (alloc_frame h)
  have e0 : s.sp - BitVec.ofNat 64 128 = callSp p := by rw [h.sp]
  have hw : ∀ e, e + 8 ≤ 96 → InRegions (allocated 128 s).wr (callSp p + 32 + BitVec.ofNat 64 e) 8 := by
    intro e he
    refine ⟨frameR 128 s, List.mem_cons_self .., ?_⟩
    simp only [frameR, e0]
    exact Offset.contains_base _ he (by omega)
  have hl : ∀ d, d + 8 ≤ 128 →
      InRegions ((allocated 128 s).rd ++ (allocated 128 s).wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun d hd => by
      obtain ⟨r, hr, hc⟩ := a.ld d hd
      refine ⟨r, ?_, hc⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv (j : Nat) (hj : j < 16) {v : BitVec 64} (he : (j, v) ∈ p.headers used keys scalars) :
      (allocated 128 s).mem.readW (p.control + BitVec.ofNat 64 (8 * j)) 64 = v :=
    (hc j hj).trans (h.header he)
  have hv2 := hv 2 (by decide) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv5 := hv 5 (by decide) (v := p.xp) (by simp [KeyPublic.headers])
  have hv6 := hv 6 (by decide) (v := p.yp) (by simp [KeyPublic.headers])
  have hv7 := hv 7 (by decide) (v := p.dp) (by simp [KeyPublic.headers])
  have hv8 := hv 8 (by decide) (v := BitVec.ofNat 64 p.dlen) (by simp [KeyPublic.headers])
  have hv9 := hv 9 (by decide) (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  have hv12 := hv 12 (by decide) (v := p.B) (by simp [KeyPublic.headers])
  have hv13 := hv 13 (by decide) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [KeyPublic.headers])
  simp only [Nat.reduceMul] at hv2 hv5 hv6 hv7 hv8 hv9 hv12 hv13
  have ea : ∀ t : State, exec (.addSp .r11 96) t = some (t.write .r11 (t.sp + BitVec.ofNat 64 96)) := by
    intro t; simp [exec]
  have hwo : ∀ e, e + 8 ≤ 96 → InRegions (allocated 128 s).wr (Mont.off (callSp p) (32 + e)) 8 := by
    intro e he
    have := hw e he
    rwa [BitVec.add_assoc, show (32 : Addr) + BitVec.ofNat 64 e = BitVec.ofNat 64 (32 + e) by
      rw [BitVec.ofNat_add]; rfl] at this
  have hw96 := hwo 64 (by decide)
  have hw104 := hwo 72 (by decide)
  have hw112 := hwo 80 (by decide)
  have hw96' : InRegions (allocated 128 s).wr (callSp p + 96#64) 8 := hw96
  simp only [Nat.reduceAdd] at hw96 hw104 hw112
  refine WP.keep argRegsW ?_ (by decide)
  unfold arguments writeController callValues KeyArgs
  simp only [List.foldl_cons, List.foldl_nil]
  have r31 : (allocated 128 s).gpr .r31 = p.control := h.r31
  have sp' : (allocated 128 s).sp = callSp p := e0
  prun [ldf, r31, sp', ea, hl 16 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide),
    hl 64 (by decide), hl 72 (by decide), hl 96 (by decide), hl 104 (by decide), hw96, hw96', hw104, hw112, hv2, hv5, hv6, hv7, hv8,
    hv9, hv12, hv13]

namespace KeyInput

variable {p : KeyPublic} {original : State}

theorem x_eq (h : KeyInput p original) : inX original = ⟨p.xp, p.len⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hx1, -, -, -, -, -, -⟩ := h.1
  rw [← h.2]; simp only [inX, keyOfState, hx1]

theorem y_eq (h : KeyInput p original) : inY original = ⟨p.yp, p.len⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hx3, -, -, -, -, -⟩ := h.1
  rw [← h.2]; simp only [inY, keyOfState, hx3]

end KeyInput

/-- The regions the attempt reads: the domain, `p_len` octets of the tape at
`used`, and its stack arguments; those it writes: `x`, `y` and the working
space. -/
def callRd (p : KeyPublic) (used : Nat) : List Region := [rD p, rR p used, rA p]
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
      stackArg u 2 = BitVec.ofNat 64 (p.Z / 8) := by
  have hw (j : Nat) (hj : j < 3) :
      stackArg u j = controllerValue (callValues p) (12 + j) (word m (callSp p) (8 * (12 + j))) := by
    unfold stackArg stackArgAddr
    rw [hu, hm]
    rw [show callSp p + BitVec.ofNat 64 (32 + 8 * (8 + j)) = callSp p + BitVec.ofNat 64 (8 * (12 + j)) by
      congr 2; omega]
    exact writeController_word _ _ _ (callValues_bound p) (12 + j) (by omega)
  refine ⟨?_, ?_, ?_⟩ <;> [rw [hw 0 (by decide)]; rw [hw 1 (by decide)]; rw [hw 2 (by decide)]] <;>
    simp only [callValues, controllerValue, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, Nat.reduceAdd,
      ite_true, ite_false]

theorem callSp_toNat {p : KeyPublic} (hf : 176 ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 176 := by
  rw [callSp_eq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]

theorem call_attempt_pre {p : KeyPublic} {used : Nat} {u : State} {m : Mem} (hf : CallFacts p used)
    (hu : u.sp = callSp p) (ha : KeyArgs p used u)
    (hm : u.mem = writeController m (callSp p) (callValues p)) :
    gkContract.pre (callState p used u) := by
  obtain ⟨h0, h1, h2⟩ := call_args hu hm
  obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have hdl : (BitVec.ofNat 64 p.dlen).toNat = p.dlen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64]
  have hzw : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.ns; omega)]
  have hsp := callSp_toNat hf.room
  have hlt := p.sp.isLt
  have hsa : stackArgAddr (callState p used u) 0 = callSp p + BitVec.ofNat 64 96 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hu]
  show _ ∧ _
  simp only [gkStack, call_gpr (by decide : Reg.r3 ∉ linkRegs), call_gpr (by decide : Reg.r4 ∉ linkRegs),
    call_gpr (by decide : Reg.r5 ∉ linkRegs), call_gpr (by decide : Reg.r6 ∉ linkRegs),
    call_gpr (by decide : Reg.r7 ∉ linkRegs), call_gpr (by decide : Reg.r8 ∉ linkRegs),
    call_gpr (by decide : Reg.r9 ∉ linkRegs), call_gpr (by decide : Reg.r10 ∉ linkRegs),
    call_stackArg, hsa, h0, h1, h2, r3, r4, r5, r6, r7, r8, r9, r10, hlen, hdl, hzw, hf.z8,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, hu]
  exact ⟨by omega, rfl, rfl, hf.xy, hf.xd, hf.xr, hf.xs, hf.xa, hf.yd, hf.yr, hf.ys, hf.ya, hf.ds,
    hf.rs, hf.sa, hf.nx, hf.ny, hf.nd, hf.nr, hf.ns, hf.len, hf.dlen, trivial, trivial, trivial, hf.scratch⟩

/-- What an attempt at `used` leaves: its status, and the key pair for 1,
zeros otherwise. -/
def AttemptPost (p : KeyPublic) (rand : List Byte) (used : Nat) (t : State) : Prop :=
  let st := attemptStatus p.a p.len (rand.drop used)
  let x := Spec.Ffdh.scalarOfOctets p.a ((rand.drop used).take p.len)
  ((t.gpr .r3).setWidth 32).toNat = st ∧
    if st = 1 then
      Spec.Rsa.bytesAt t.mem p.xp p.len = Spec.Rsa.i2osp x p.len ∧
        Spec.Rsa.bytesAt t.mem p.yp p.len = Spec.Rsa.i2osp (Spec.Rsa.powMod p.a.g x p.a.p) p.len
    else Spec.Rsa.bytesAt t.mem p.xp p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt t.mem p.yp p.len = List.replicate p.len 0

theorem AttemptPost.keep {p : KeyPublic} {rand : List Byte} {used : Nat} {s t : State}
    (h : AttemptPost p rand used s) (hm : t.mem = s.mem)
    (hr : (t.gpr .r3).setWidth 32 = (s.gpr .r3).setWidth 32) : AttemptPost p rand used t := by
  unfold AttemptPost at h ⊢
  rw [hm, hr]
  exact h

section

variable {p : KeyPublic} {original s : State} {used keys scalars : Nat}

theorem call_covers_writes (h : KeyLive p original used keys scalars s) {u : State}
    (hw : u.wr = (allocated 128 s).wr) : Covers (callWr p) u.wr := by
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
    {u : State} (hrd : u.rd = (allocated 128 s).rd) (hw : u.wr = (allocated 128 s).wr) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  obtain ⟨-, -, hrd', -⟩ := hi.1
  have e0 : s.sp - BitVec.ofNat 64 128 = callSp p := by rw [h.sp]
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
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
  · refine ⟨frameR 128 s, ?_, 64, ?_, by show 64 + 24 ≤ 128 - 32; decide⟩
    · rw [hw]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · show callSp p + BitVec.ofNat 64 96 = s.sp - BitVec.ofNat 64 128 + 32 + BitVec.ofNat 64 64
      rw [e0, BitVec.add_assoc]; rfl

/-- What the attempt writes, as the controller sees it. -/
theorem attempt_frame (h : KeyLive p original used keys scalars s) {u t : State} {d : Nat}
    (hm : u.mem = writeController (allocated 128 s).mem (callSp p) (callValues p))
    (hf : Frame (callWr p ++ [below u.sp d]) u.mem t.mem) (hd : d = 0) :
    Frame (KeyInput.callChanges original) s.mem t.mem := by
  have hi := h.input
  have hsp : p.sp = original.sp := hi.sp_eq
  have h1 : Frame (KeyInput.callChanges original) (allocated 128 s).mem u.mem := by
    rw [hm]
    apply (writeController_frame_size _ _ (callValues p) (size := 128) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨below original.sp stackUse, by simp [KeyInput.callChanges], ?_⟩
    rw [← hsp, callSp_eq]
    exact Offset.sub_below p.sp (a := 176) (b := 176) (by decide) (by decide)
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
      simp only [Region.Contains] at ha
      omega
  exact (alloc_frame h).trans (h1.trans h2)

/-- The attempt's view of the domain and the tape, at its entry. -/
theorem call_inputs (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hf : CallFacts p used) {u : State}
    (hm : u.mem = writeController (allocated 128 s).mem (callSp p) (callValues p)) (hu : u.sp = callSp p)
    (ha : KeyArgs p used u) :
    Spec.Rsa.bytesAt (callState p used u).mem ((callState p used u).gpr .r7)
        ((callState p used u).gpr .r8).toNat = p.dom ∧
      Spec.Rsa.bytesAt (callState p used u).mem ((callState p used u).gpr .r10)
        (stackArg (callState p used u) 0).toNat = ((keyRand original).drop used).take p.len ∧
      ((callState p used u).gpr .r9).toNat = p.len := by
  have hfr : Frame (KeyInput.changes original) s.mem u.mem :=
    frame_of_callChanges original (attempt_frame (t := u) (d := 0) h hm (by
      intro x _; rfl) rfl)
  obtain ⟨h0, -, -⟩ := call_args hu hm
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have hdl : (BitVec.ofNat 64 p.dlen).toNat = p.dlen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64]
  refine ⟨?_, ?_, by rw [call_gpr (by decide), ha.2.2.2.2.2.2.1, hlen]⟩
  · simp only [call_gpr (by decide : Reg.r7 ∉ linkRegs), call_gpr (by decide : Reg.r8 ∉ linkRegs),
      ha.2.2.2.2.1, ha.2.2.2.2.2.1, hdl, State.withRegions_mem, State.callEntry_mem]
    exact (h.input.domain_frame hfr).trans h.domain
  · simp only [call_gpr (by decide : Reg.r10 ∉ linkRegs), call_stackArg, ha.2.2.2.2.2.2.2, h0, hlen,
      State.withRegions_mem, State.callEntry_mem]
    have hr := (h.input.random_frame hfr).trans h.random
    rw [← VG.Proof.Dsa.bytesAt_slice _ _ hroom, ← hr]

theorem key_attempt_run (a : Attempt) (h : KeyLive p original used keys scalars s)
    (hroom : used + p.len ≤ p.randLen) :
    WP isa (attemptRun a.call) s fun t =>
      KeyLive p original used keys scalars t ∧ AttemptPost p (keyRand original) used t := by
  have hf := h.callFacts hroom
  have e0 : s.sp - BitVec.ofNat 64 128 = callSp p := by rw [h.sp]
  have hroom' : 128 ≤ s.sp.toNat := by
    have := hf.room
    have h48 : (p.sp - 48).toNat = p.sp.toNat - 48 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; show 48 ≤ _; omega)]; rfl
    rw [h.sp, h48]
    omega
  unfold attemptRun
  refine WP.alloc (by decide) hroom' ?_
  refine WP.seq (WP.mono (key_arguments_ok h) fun u ⟨⟨ha, hm⟩, k⟩ => ?_)
  have hu : u.sp = callSp p := k.sp.trans e0
  refine WP.callAny (k := gkContract) a.correct (call_attempt_pre hf hu ha hm)
    (call_covers_reads h hroom k.rd k.wr) (call_covers_writes h k.wr) ?_ (by rw [a.stack]; decide)
  intro t hrd hwr hsp hfr hcs hpost
  refine ⟨?_, ?_⟩
  · -- The loop state, after the frame.
    apply h.restore (show (freed 128 t).rd = s.rd from hrd.trans k.rd)
      (show (freed 128 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.wr]; rfl)
    · change t.sp + BitVec.ofNat 64 128 = s.sp
      rw [hsp, k.sp]
      exact BitVec.sub_add_cancel _ _
    · intro r hr
      exact (hcs r hr).trans (k.gpr r (by revert r hr; decide))
    · exact attempt_frame h hm hfr a.stack
  · -- The attempt's status and outputs.
    obtain ⟨hdom, hrand, h9⟩ := call_inputs h hroom hf hm hu ha
    have hp := hpost
    simp only [gkContract, gkScalar, hdom, hrand, h9] at hp
    obtain ⟨hst, hout⟩ := hp h.input.domain_valid
    simp only [call_gpr (by decide : Reg.r3 ∉ linkRegs), call_gpr (by decide : Reg.r5 ∉ linkRegs),
      ha.1, ha.2.2.1, State.withRegions_gpr, State.withRegions_mem] at hst hout
    unfold AttemptPost
    exact ⟨hst, hout⟩

end

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
