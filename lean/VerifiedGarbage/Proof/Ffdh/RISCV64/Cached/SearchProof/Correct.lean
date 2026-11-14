module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.SearchProof.Data
public import VerifiedGarbage.Impl.Ffdh.RISCV64.CachedSearch
public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Correct
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The cached key-generation controller's correctness (RISC-V)

As on PPC64LE (`Proof/Ffdh/PPC64LE/Cached/SearchProof/`). In its frame of 48
bytes, the controller passes `vg_ffdh_generate_key_cached` the next `p_len`
octets of the tape and the context, its stack arguments at the frame's base
(`ctx` and `ctx_len` copied from the controller's own; `key_attempt_run`,
from the callee's contract by `WP.callAny`); the attempt keeps the
controller's state, and leaves its status, and the key pair or zeros, in `x`
and `y`. Its status then gives the key, or one fewer scalar or key
(`key_classify`). The loop is total by the budgets' measure (`key_loop`). The
entry stores the arguments in the controller's words (`entry_ok`); the frame
around the loop saves `ra` (`WP.frameRegAny`); `finish` then stores the
octets consumed, returns the status and restores `s0` (`key_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached.SearchProof

open VG VG.RISCV64 VG.Spec.Ffdh VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.RISCV64.KeyGeneration (tmpRegs CtlAccess WP.ctl low32 al8 WP.frameRegAny)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  writeController_frame_size controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.RISCV64.KeyGeneration.Search
open VG.Impl.Ffdh.RISCV64.Cached.Search

/-! ## Frames -/

/-! ## The attempt -/

/-- The attempt's stack arguments: `rand_len` (`p_len`), `scratch`,
`scratch_len`, `ctx` and `ctx_len`, at its frame's base. -/
def callValues (p : KeyPublic) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 p.len), (1, p.B), (2, BitVec.ofNat 64 (p.Z / 8)), (3, p.ctx),
    (4, BitVec.ofNat 64 p.ctxLen)]

theorem callValues_bound (p : KeyPublic) : ∀ e ∈ callValues p, e.1 < 16 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The attempt's register arguments. -/
def KeyArgs (p : KeyPublic) (used : Nat) (t : State) : Prop :=
  t.gpr .a0 = p.xp ∧ t.gpr .a1 = BitVec.ofNat 64 p.len ∧ t.gpr .a2 = p.yp ∧
  t.gpr .a3 = BitVec.ofNat 64 p.len ∧ t.gpr .a4 = p.dp ∧ t.gpr .a5 = BitVec.ofNat 64 p.dlen ∧
  t.gpr .a6 = BitVec.ofNat 64 p.len ∧ t.gpr .a7 = p.rp + BitVec.ofNat 64 used

theorem KeyLive.access_alloc {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) : CtlAccess (allocd 48 s) p.control := by
  obtain ⟨⟨B₀, o, L, hm, hb, hL, hL'⟩, hn, ha⟩ := h.input.control_scr (t := s) h.wr
  exact CtlAccess.of_scr ⟨⟨B₀, o, L, List.mem_cons_of_mem _ hm, hb, hL, hL'⟩, hn, ha⟩

theorem allocd_sp {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) : (allocd 48 s).sp = callSp p := by
  show s.sp - BitVec.ofNat 64 48 = _; rw [h.sp]

/-- The controller's stack argument `j`, through writes of its buffers and
its stack only. -/
theorem KeyInput.arg_frame {p : KeyPublic} {original : State} (h : KeyInput p original) {m : Mem}
    (hf : Frame (KeyInput.changes original) original.mem m) (j : Nat) (hj : j < 7) :
    m.readW (original.sp + BitVec.ofNat 64 (8 * j)) 64 = stackArg original j := by
  refine hf.readW (r := inArgs original) ?_ (h.read_disjoint (by simp [inReads])) (by decide)
  simp only [inArgs, stackArgAddr, Nat.mul_zero, add_ofNat_zero]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem KeyInput.arg_in {p : KeyPublic} {original : State} (h : KeyInput p original) (j : Nat) (hj : j < 7) :
    InRegions original.rd (original.sp + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs original, by rw [h.rd_eq]; simp [inReads], ?_⟩
  simp only [inArgs, stackArgAddr, Nat.mul_zero, add_ofNat_zero]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- The context's two arguments, as the attempt's frame reaches them. -/
theorem KeyLive.ctx_args {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    (InRegions ((allocd 48 s).rd ++ (allocd 48 s).wr) (callSp p + BitVec.ofNat 64 104) 8 ∧
      (callSp p + BitVec.ofNat 64 104).toNat % 8 = 0 ∧
      (allocd 48 s).mem.readW (callSp p + BitVec.ofNat 64 104) 64 = p.ctx) ∧
    (InRegions ((allocd 48 s).rd ++ (allocd 48 s).wr) (callSp p + BitVec.ofNat 64 112) 8 ∧
      (callSp p + BitVec.ofNat 64 112).toNat % 8 = 0 ∧
      (allocd 48 s).mem.readW (callSp p + BitVec.ofNat 64 112) 64 =
        BitVec.ofNat 64 p.ctxLen) := by
  have hi := h.input
  have hsp0 : p.sp = original.sp := hi.sp_eq
  have hal : original.sp.toNat % 8 = 0 := by rw [← hsp0]; have := hi.sp_al; omega
  have e5 : callSp p + BitVec.ofNat 64 104 = original.sp + BitVec.ofNat 64 (8 * 5) := by
    rw [callSp_eq, hsp0]; bv_omega
  have e6 : callSp p + BitVec.ofNat 64 112 = original.sp + BitVec.ofNat 64 (8 * 6) := by
    rw [callSp_eq, hsp0]; bv_omega
  have hrd : (allocd 48 s).rd = original.rd := h.rd
  have hm : (allocd 48 s).mem = s.mem := rfl
  rw [e6, e5, hrd, hm, hi.arg_frame h.frame 5 (by decide), hi.arg_frame h.frame 6 (by decide)]
  refine ⟨⟨?_, al8 hal (by decide), congrArg KeyPublic.ctx hi.2⟩, ⟨?_, al8 hal (by decide), ?_⟩⟩
  · obtain ⟨r, hr, hc⟩ := hi.arg_in 5 (by decide); exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := hi.arg_in 6 (by decide); exact ⟨r, List.mem_append_left _ hr, hc⟩
  · have hc := congrArg KeyPublic.ctxLen hi.2
    change (stackArg original 6).toNat = p.ctxLen at hc
    rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem key_arguments_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block cachedArguments) (allocd 48 s) fun u =>
      (KeyArgs p used u ∧ u.mem = writeController (allocd 48 s).mem (callSp p) (callValues p)) ∧
      Keep tmpRegs (allocd 48 s) u ∧ u.sp = (allocd 48 s).sp := by
  have a := h.access_alloc
  have sp' := allocd_sp h
  have hspal : (callSp p).toNat % 16 = 0 := by
    rw [callSp_toNat h.input.sp_room]; have := h.input.sp_al; have := h.input.sp_room; omega
  have hw : ∀ d, d + 8 ≤ 48 → InRegions (allocd 48 s).wr (callSp p + BitVec.ofNat 64 d) 8 := by
    intro d hd
    refine ⟨⟨s.sp - BitVec.ofNat 64 48, 48⟩, List.mem_cons_self .., ?_⟩
    rw [show s.sp - BitVec.ofNat 64 48 = callSp p from sp']
    exact Offset.contains_base _ hd (by omega)
  have hv (j : Nat) {v : BitVec 64} (he : (j, v) ∈ p.headers used keys scalars) :
      (allocd 48 s).mem.readW (p.control + BitVec.ofNat 64 (8 * j)) 64 = v :=
    h.header he
  have hv2 := hv 2 (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv5 := hv 5 (v := p.xp) (by simp [KeyPublic.headers])
  have hv6 := hv 6 (v := p.yp) (by simp [KeyPublic.headers])
  have hv7 := hv 7 (v := p.dp) (by simp [KeyPublic.headers])
  have hv8 := hv 8 (v := BitVec.ofNat 64 p.dlen) (by simp [KeyPublic.headers])
  have hv9 := hv 9 (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  have hv12 := hv 12 (v := p.B) (by simp [KeyPublic.headers])
  have hv13 := hv 13 (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [KeyPublic.headers])
  simp only [Nat.reduceMul] at hv2 hv5 hv6 hv7 hv8 hv9 hv12 hv13
  obtain ⟨⟨c5r, c5a, c5v⟩, ⟨c6r, c6a, c6v⟩⟩ := h.ctx_args
  have hw0 := hw 0 (by decide)
  have hw8 := hw 8 (by decide)
  have hw16 := hw 16 (by decide)
  have hw24 := hw 24 (by decide)
  have hw32 := hw 32 (by decide)
  have hal0 := al8 (B := callSp p) (by omega) (d := 0) (by decide)
  have hal8 := al8 (B := callSp p) (by omega) (d := 8) (by decide)
  have hal16 := al8 (B := callSp p) (by omega) (d := 16) (by decide)
  have hal24 := al8 (B := callSp p) (by omega) (d := 24) (by decide)
  have hal32 := al8 (B := callSp p) (by omega) (d := 32) (by decide)
  simp only [add_ofNat_zero] at hw0 hal0
  have s0' : (allocd 48 s).gpr .s0 = p.control := h.s0
  refine WP.ctl ?_ (by rfl)
  unfold cachedArguments arguments writeController callValues KeyArgs
  simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
  brun [ldf, s0', sp', exec_addSp (show 0 < 2048 by decide), exec_addSp (show 104 < 2048 by decide),
    add_ofNat_zero, c5r, c5a, c5v, c6r, c6a, c6v,
    a.ld 16 (by decide), a.ld 40 (by decide), a.ld 48 (by decide), a.ld 56 (by decide),
    a.ld 64 (by decide), a.ld 72 (by decide), a.ld 96 (by decide), a.ld 104 (by decide),
    a.al 16 (by decide) (by decide), a.al 40 (by decide) (by decide), a.al 48 (by decide) (by decide),
    a.al 56 (by decide) (by decide), a.al 64 (by decide) (by decide), a.al 72 (by decide) (by decide),
    a.al 96 (by decide) (by decide), a.al 104 (by decide) (by decide),
    hw0, hw8, hw16, hw24, hw32, hal0, hal8, hal16, hal24, hal32, hv2, hv5, hv6, hv7, hv8, hv9, hv12, hv13]

/-- The regions the attempt reads: the domain, `p_len` octets of the tape at
`used`, the context and its stack arguments; those it writes: `x`, `y` and
the working space. -/
def callRd (p : KeyPublic) (used : Nat) : List Region := [rD p, rR p used, ⟨p.ctx, p.ctxLen * 8⟩, rA p]
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
      stackArg u 2 = BitVec.ofNat 64 (p.Z / 8) ∧ stackArg u 3 = p.ctx ∧
      stackArg u 4 = BitVec.ofNat 64 p.ctxLen := by
  have hw (j : Nat) (hj : j < 5) :
      stackArg u j = controllerValue (callValues p) j (word m (callSp p) (8 * j)) := by
    unfold stackArg stackArgAddr
    rw [hu, hm]
    exact writeController_word _ _ _ (callValues_bound p) j (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> [rw [hw 0 (by decide)]; rw [hw 1 (by decide)]; rw [hw 2 (by decide)];
    rw [hw 3 (by decide)]; rw [hw 4 (by decide)]] <;>
    simp only [callValues, controllerValue, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]

/-- What an attempt at `used` leaves: its status, and the key pair for 1,
zeros otherwise. -/
def AttemptPost (p : KeyPublic) (rand : List Byte) (used : Nat) (t : State) : Prop :=
  let st := attemptStatus .cached p.a p.len (rand.drop used)
  let x := Spec.Ffdh.vettedScalarOfOctets p.a ((rand.drop used).take p.len)
  ((t.gpr .a0).setWidth 32).toNat = st ∧
    if st = 1 then
      Spec.Rsa.bytesAt t.mem p.xp p.len = Spec.Rsa.i2osp x p.len ∧
        Spec.Rsa.bytesAt t.mem p.yp p.len = Spec.Rsa.i2osp (Spec.Rsa.powMod p.a.g x p.a.p) p.len
    else Spec.Rsa.bytesAt t.mem p.xp p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt t.mem p.yp p.len = List.replicate p.len 0

section

variable {p : KeyPublic} {original s : State} {used keys scalars : Nat}

theorem call_covers_writes (h : KeyLive p original used keys scalars s) {u : State}
    (hw : u.wr = (allocd 48 s).wr) : Covers (callWr p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [hw]
  apply List.mem_cons_of_mem
  rw [h.wr, h.input.wr_eq]
  simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.input.x_mem
  · exact h.input.y_mem
  · rw [← h.input.2]; simp [inWrites, inScr, keyOfState]

theorem call_covers_reads (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    {u : State} (hrd : u.rd = (allocd 48 s).rd) (hw : u.wr = (allocd 48 s).wr) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  have e0 := allocd_sp h
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨inDom original, ?_, 0, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inDom original ∈ s.rd; rw [h.rd, hi.rd_eq]; simp [inReads])
    · cases hi.2; simp only [BitVec.add_zero]; rfl
    · cases hi.2; simp only [Nat.zero_add]; exact Nat.le_refl _
  · refine ⟨inRand original, ?_, used, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inRand original ∈ s.rd; rw [h.rd, hi.rd_eq]; simp [inReads])
    · cases hi.2; rfl
    · cases hi.2; exact hroom
  · refine ⟨inContext original, ?_, 0, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inContext original ∈ s.rd; rw [h.rd, hi.rd_eq]; simp [inReads])
    · cases hi.2; simp only [BitVec.add_zero]; rfl
    · cases hi.2; simp only [Nat.zero_add]; exact Nat.le_refl _
  · refine ⟨⟨s.sp - BitVec.ofNat 64 48, 48⟩, ?_, 0, ?_, by show 0 + 40 ≤ 48; decide⟩
    · rw [hw]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · show callSp p = s.sp - BitVec.ofNat 64 48 + BitVec.ofNat 64 0
      rw [add_ofNat_zero]; exact e0.symm

/-- What the attempt writes, as the controller sees it. -/
theorem attempt_frame (h : KeyLive p original used keys scalars s) {u t : State} {d : Nat}
    (hm : u.mem = writeController (allocd 48 s).mem (callSp p) (callValues p))
    (hf : Frame (callWr p ++ [below u.sp d]) u.mem t.mem) (hd : d = 0) :
    Frame (KeyInput.callChanges original) s.mem t.mem := by
  have hi := h.input
  have hsp : p.sp = original.sp := hi.sp_eq
  have h1 : Frame (KeyInput.callChanges original) (allocd 48 s).mem u.mem := by
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
      simp only [Region.Contains] at ha
      omega
  exact h1.trans h2

/-- The attempt's view of the domain and the tape, at its entry. -/
theorem call_inputs (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hf : CallFacts p used) {u : State}
    (hm : u.mem = writeController (allocd 48 s).mem (callSp p) (callValues p)) (hu : u.sp = callSp p)
    (ha : KeyArgs p used u) :
    Spec.Rsa.bytesAt (callState p used u).mem ((callState p used u).gpr .a4)
        ((callState p used u).gpr .a5).toNat = p.dom ∧
      Spec.Rsa.bytesAt (callState p used u).mem ((callState p used u).gpr .a7)
        (stackArg (callState p used u) 0).toNat = ((keyRand original).drop used).take p.len ∧
      ((callState p used u).gpr .a6).toNat = p.len := by
  have hfr : Frame (KeyInput.changes original) s.mem u.mem :=
    frame_of_callChanges original (attempt_frame (t := u) (d := 0) h hm (by
      intro x _; rfl) rfl)
  obtain ⟨h0, -, -, -, -⟩ := call_args hu hm
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have hdl : (BitVec.ofNat 64 p.dlen).toNat = p.dlen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64]
  refine ⟨?_, ?_, by rw [call_gpr (by decide), ha.2.2.2.2.2.2.1, hlen]⟩
  · simp only [call_gpr (by decide : Reg.a4 ∉ linkRegs), call_gpr (by decide : Reg.a5 ∉ linkRegs),
      ha.2.2.2.2.1, ha.2.2.2.2.2.1, hdl, State.withRegions_mem, State.callEntry_mem]
    exact (h.input.domain_frame hfr).trans h.domain
  · simp only [call_gpr (by decide : Reg.a7 ∉ linkRegs), call_stackArg, ha.2.2.2.2.2.2.2, h0, hlen,
      State.withRegions_mem, State.callEntry_mem]
    have hr := (h.input.random_frame hfr).trans h.random
    rw [← VG.Proof.Dsa.bytesAt_slice _ _ hroom, ← hr]

/-- The context is read only. -/
theorem KeyInput.context_frame {p : KeyPublic} {s : State} (h : KeyInput p s) {m m' : Mem}
    (hf : Frame (KeyInput.changes s) m m') :
    Spec.Rsa.wordsAt m' p.ctx p.ctxLen = Spec.Rsa.wordsAt m p.ctx p.ctxLen := by
  rw [← h.2]
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  apply hf.readW (r := inContext s)
  · have inside : i < (stackArg s 6).toNat := List.mem_range.mp hi
    have size := h.nowrap (r := inContext s) (by simp [inReads])
    change (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64 at size
    exact Offset.contains_base _ (by omega) (by omega)
  · exact h.read_disjoint (by simp [inReads])
  · decide

/-- The context of a loop state is the one the precompute writes. -/
theorem KeyLive.context_canonical (h : KeyLive p original used keys scalars s) :
    p.ctxLen = Spec.Ffdh.generationPrecomputedWords p.len ∧
      Spec.Ffdh.generationPrecompute p.len p.dom = some (Spec.Rsa.wordsAt s.mem p.ctx p.ctxLen) := by
  rw [h.input.context_frame h.frame, ← h.input.2]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, count, canonical, -⟩ := h.input.1
  exact ⟨count, canonical⟩

theorem call_attempt_pre (h : KeyLive p original used keys scalars s)
    (hf : CallFacts p used) {u : State} (hu : u.sp = callSp p) (ha : KeyArgs p used u)
    (hm : u.mem = writeController (allocd 48 s).mem (callSp p) (callValues p)) :
    cgContract.pre (callState p used u) := by
  have hfr : Frame (KeyInput.changes original) s.mem u.mem :=
    frame_of_callChanges original (attempt_frame (t := u) (d := 0) h hm (by intro x _; rfl) rfl)
  obtain ⟨h0, h1, h2, h3, h4⟩ := call_args hu hm
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have hdl : (BitVec.ofNat 64 p.dlen).toNat = p.dlen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64]
  have hzw : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.ns; omega)]
  have cx : (⟨p.ctx, p.ctxLen * 8⟩ : Region) = inContext original := by rw [← h.input.2]; rfl
  have xx : rX p = inX original := h.input.x_eq.symm
  have yy : rY p = inY original := h.input.y_eq.symm
  have ss : rS p = inScr original := by rw [← h.input.2]; rfl
  have nc : p.ctx.toNat + p.ctxLen * 8 ≤ 2 ^ 64 := by
    have n := h.input.nowrap (r := inContext original) (by simp [inReads]); rw [← cx] at n; exact n
  have hcl : (BitVec.ofNat 64 p.ctxLen).toNat = p.ctxLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have xc : (rX p).Disjoint ⟨p.ctx, p.ctxLen * 8⟩ := by
    rw [xx, cx]; exact h.input.write_disjoint (by simp [inWrites]) (by simp [inReads])
  have yc : (rY p).Disjoint ⟨p.ctx, p.ctxLen * 8⟩ := by
    rw [yy, cx]; exact h.input.write_disjoint (by simp [inWrites]) (by simp [inReads])
  have sc : (rS p).Disjoint ⟨p.ctx, p.ctxLen * 8⟩ := by
    rw [ss, cx]; exact h.input.write_disjoint (by simp [inWrites]) (by simp [inReads])
  have cal : p.ctx.toNat % 8 = 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, al⟩ := h.input.1
    rw [← h.input.2]; exact al
  have canonical := h.context_canonical
  have hdom : Spec.Rsa.bytesAt u.mem p.dp p.dlen = p.dom := (h.input.domain_frame hfr).trans h.domain
  have hsa : stackArgAddr (callState p used u) 0 = callSp p := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hu, Nat.mul_zero, add_ofNat_zero]
  show _ ∧ _
  simp only [cgStack, cgDom, call_gpr (by decide : Reg.a0 ∉ linkRegs), call_gpr (by decide : Reg.a1 ∉ linkRegs),
    call_gpr (by decide : Reg.a2 ∉ linkRegs), call_gpr (by decide : Reg.a3 ∉ linkRegs),
    call_gpr (by decide : Reg.a4 ∉ linkRegs), call_gpr (by decide : Reg.a5 ∉ linkRegs),
    call_gpr (by decide : Reg.a6 ∉ linkRegs), call_gpr (by decide : Reg.a7 ∉ linkRegs),
    call_stackArg, hsa, h0, h1, h2, h3, h4, r0, r1, r2, r3, r4, r5, r6, r7, hlen, hdl, hzw, hcl, hf.z8,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, hu,
    State.withRegions_mem, State.callEntry_mem, hdom]
  exact ⟨rfl, rfl, hf.xy, hf.xd, hf.xr, hf.xs, xc, hf.xa, hf.yd, hf.yr, hf.ys, yc, hf.ya, hf.ds,
    hf.rs, sc, hf.sa, hf.nx, hf.ny, hf.nd, hf.nr, hf.ns, nc, hf.len, hf.dlen, trivial, trivial, trivial,
    hf.scratch, h.input.domain_valid, ⟨canonical.1, by rw [h.input.context_frame hfr]; exact canonical.2⟩,
    hf.bal, cal, hf.spal⟩

theorem key_attempt_run (a : Attempt) (h : KeyLive p original used keys scalars s)
    (hroom : used + p.len ≤ p.randLen) :
    WP isa (attemptRun a.call) s fun t =>
      KeyLive p original used keys scalars t ∧ AttemptPost p (keyRand original) used t := by
  have hf := h.callFacts hroom
  have e0 := allocd_sp h
  have hroom' : 48 ≤ s.sp.toNat := by
    have := hf.room
    have h16 : (p.sp - 16).toNat = p.sp.toNat - 16 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; show 16 ≤ _; omega)]; rfl
    rw [h.sp, h16]
    omega
  unfold attemptRun
  refine WP.alloc (by decide) hroom' ?_
  refine WP.seq (WP.mono (key_arguments_ok h) fun u ⟨⟨ha, hm⟩, k, husp⟩ => ?_)
  have hu : u.sp = callSp p := husp.trans e0
  refine WP.callAny (k := cgContract) a.correct (call_attempt_pre h hf hu ha hm)
    (call_covers_reads h hroom k.2.1 k.2.2) (call_covers_writes h k.2.2) ?_ (by rw [a.stack]; decide)
  intro t hrd hwr hsp hfr hcs hpost
  refine ⟨?_, ?_⟩
  · -- The loop state, after the frame.
    apply h.restore (show (freed 48 t).rd = s.rd from hrd.trans k.2.1)
      (show (freed 48 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.2.2]; rfl)
    · change t.sp + BitVec.ofNat 64 48 = s.sp
      rw [hsp, husp]
      exact BitVec.sub_add_cancel _ _
    · intro r hr
      exact (hcs r hr).trans (k.gpr (by revert r hr; decide))
    · exact attempt_frame h hm hfr a.stack
  · -- The attempt's status and outputs.
    obtain ⟨hdom, hrand, h6⟩ := call_inputs h hroom hf hm hu ha
    have hp := hpost
    simp only [cgContract, cgScalar, cgA, cgDom, hdom, hrand, h6] at hp
    obtain ⟨hst, hout⟩ := hp
    simp only [call_gpr (by decide : Reg.a0 ∉ linkRegs), call_gpr (by decide : Reg.a2 ∉ linkRegs),
      ha.1, ha.2.2.1, State.withRegions_gpr, State.withRegions_mem] at hst hout
    exact ⟨hst, hout⟩

end

/-! ## After an attempt: the key, or one fewer scalar or key -/

/-- An attempt's outputs: the key, or zeros. -/
def AttemptOut (p : KeyPublic) (rand : List Byte) (used : Nat) (m : Mem) : Prop :=
  let st := attemptStatus .cached p.a p.len (rand.drop used)
  let x := Spec.Ffdh.vettedScalarOfOctets p.a ((rand.drop used).take p.len)
  if st = 1 then
    Spec.Rsa.bytesAt m p.xp p.len = Spec.Rsa.i2osp x p.len ∧
      Spec.Rsa.bytesAt m p.yp p.len = Spec.Rsa.i2osp (Spec.Rsa.powMod p.a.g x p.a.p) p.len
  else Spec.Rsa.bytesAt m p.xp p.len = List.replicate p.len 0 ∧
    Spec.Rsa.bytesAt m p.yp p.len = List.replicate p.len 0

/-- The controller's word-only writes keep `x` and `y`. -/
theorem output_frame {p : KeyPublic} {original : State} (hi : KeyInput p original) {m m' : Mem}
    (hf : Frame [⟨p.control, 128⟩] m m') :
    Spec.Rsa.bytesAt m' p.xp p.len = Spec.Rsa.bytesAt m p.xp p.len ∧
      Spec.Rsa.bytesAt m' p.yp p.len = Spec.Rsa.bytesAt m p.yp p.len := by
  have hk := hi.len_lt
  constructor <;> simp only [Spec.Rsa.bytesAt] <;> refine List.map_congr_left fun i hi' => ?_
  · exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hi.x_ctl)
      (show p.len ≤ 2 ^ 64 by omega) (List.mem_range.mp hi')
  · exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hi.y_ctl)
      (show p.len ≤ 2 ^ 64 by omega) (List.mem_range.mp hi')

theorem AttemptOut.frame {p : KeyPublic} {original : State} (hi : KeyInput p original)
    {rand : List Byte} {used : Nat} {m m' : Mem} (h : AttemptOut p rand used m)
    (hf : Frame [⟨p.control, 128⟩] m m') : AttemptOut p rand used m' := by
  have hout := output_frame hi hf
  unfold AttemptOut at h ⊢
  rw [hout.1, hout.2]
  exact h

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
        t.gpr .t0 = (s.gpr .a0 <<< 32) >>> 32) ∧ Keep tmpRegs s t ∧ t.sp = s.sp := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv9 := h.header (j := 9) (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  have hv10 := h.header (j := 10) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [KeyPublic.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  simp only [Bignum.word, Nat.reduceMul] at hv2 hv9 hv10 hv11
  have hlen : p.randLen < 2 ^ 64 := by
    rw [← h.input.2]; exact BitVec.isLt _
  have e9 : p.rp + BitVec.ofNat 64 used + BitVec.ofNat 64 p.len = p.rp + BitVec.ofNat 64 (used + p.len) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have e10 : BitVec.ofNat 64 (p.randLen - used) - BitVec.ofNat 64 p.len =
      BitVec.ofNat 64 (p.randLen - (used + p.len)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by
      simp only [BitVec.le_def, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have e11 : BitVec.ofNat 64 used + BitVec.ofNat 64 p.len = BitVec.ofNat 64 (used + p.len) := by
    rw [← BitVec.ofNat_add]
  refine WP.ctl ?_ (by rfl)
  unfold advance writeController advanceValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.s0, hv2, hv9, hv10, hv11,
    a.ld 16 (by decide), a.ld 72 (by decide), a.ld 80 (by decide), a.ld 88 (by decide),
    a.st 72 (by decide), a.st 80 (by decide), a.st 88 (by decide),
    a.al 16 (by decide) (by decide), a.al 72 (by decide) (by decide), a.al 80 (by decide) (by decide),
    a.al 88 (by decide) (by decide), e9, e10, e11]

/-- The status, normalized, and the attempt's octets consumed. -/
theorem key_classify_head {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hp : AttemptPost p (keyRand original) used s) :
    WP isa (.block (advance ++ test 1)) s fun t =>
      KeyLive p original (used + p.len) keys scalars t ∧ AttemptOut p (keyRand original) used t.mem ∧
      t.gpr .t0 = BitVec.ofNat 64 (attemptStatus .cached p.a p.len ((keyRand original).drop used)) ∧
      isa.eval (.zero .t1) t =
        some (decide (attemptStatus .cached p.a p.len ((keyRand original).drop used) = 1)) := by
  have hst : attemptStatus .cached p.a p.len ((keyRand original).drop used) < 4 := by
    rcases attemptStatus_cases (policy := .cached) p.a p.len ((keyRand original).drop used) with he | he | he <;> omega
  rw [WP.block_append_iff]
  refine WP.mono (key_advance_ok h hroom) fun v ⟨⟨hmv, h9⟩, kv, hspv⟩ => ?_
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
           rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hmv kv hspv hh
  have hpv : AttemptOut p (keyRand original) used v.mem :=
    AttemptOut.frame h.input (by unfold AttemptOut; exact hp.2)
      (hmv ▸ writeController_frame s.mem p.control _ hb)
  have h9' : v.gpr .t0 = BitVec.ofNat 64 (attemptStatus .cached p.a p.len ((keyRand original).drop used)) :=
    h9.trans (low32 hp.1)
  refine WP.mono (test_ok h9' hst (.inl rfl)) fun t ⟨⟨he, hmt⟩, kt, hspt⟩ => ?_
  exact ⟨hv.keep kt hspt hmt, hmt ▸ hpv, (kt.gpr (by decide)).trans h9', he⟩

/-- The scalar of the attempt at `used`. -/
abbrev KeyPublic.scalarAt (p : KeyPublic) (rand : List Byte) (used : Nat) : Nat :=
  Spec.Ffdh.vettedScalarOfOctets p.a ((rand.drop used).take p.len)

/-- The key search's result for an accepted attempt at `used`. -/
def acceptedResult (p : KeyPublic) (rand : List Byte) (used : Nat) : KeySearchResult :=
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
    {r : KeySearchResult} (hu : r.used = used) (hs : r.status = status)
    (hr : r.retries = ⟨0, 0⟩) (ho : KeyOutput p r s.mem) :
    WP isa (.block (terminal status)) s (KeyDone p original r) := by
  refine WP.mono (key_terminal_live h hst) fun t ⟨ht, hm⟩ => ?_
  have hb := terminalValues_bound status
  have hst0 : status ≠ 0 := by omega
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
  rcases attemptStatus_cases (policy := .cached) p.a p.len ((keyRand original).drop used) with h1 | h2 | h3
  · rw [h1] at he
    refine WP.ite true he (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_terminal_done (r := acceptedResult p (keyRand original) used) hu 1 (.inl rfl)
      rfl rfl rfl ?_) fun t ht => ?_
    rotate_left
    · dsimp only [KeyClassified]; rw [ite_eq_left h1]; exact ht
    unfold AttemptOut at hpu
    simp only [h1, ite_true] at hpu
    exact hpu
  · rw [h2] at he hax
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (test_ok hax (by decide) (.inr (.inl rfl)))
      fun v ⟨⟨he2, hmv⟩, kv, hspv⟩ => ?_)
    have hv := hu.keep kv hspv hmv
    refine WP.ite true he2 (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_rejected_scalar hv hs) fun t ht => ?_
    dsimp only [KeyClassified]
    rw [ite_eq_right (by rw [h2]; decide), ite_eq_left h2]
    exact ht
  · rw [h3] at he hax
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (test_ok hax (by decide) (.inr (.inl rfl)))
      fun v ⟨⟨he2, hmv⟩, kv, hspv⟩ => ?_)
    have hv := hu.keep kv hspv hmv
    refine WP.ite false he2 (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (test_ok ((kv.gpr (by decide)).trans hax) (by decide) (.inr (.inr rfl)))
      fun w ⟨⟨he3, hmw⟩, kw, hspw⟩ => ?_)
    have hw := hv.keep kw hspw hmw
    refine WP.ite true he3 (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_rejected_public hw hk) fun t ht => ?_
    dsimp only [KeyClassified]
    rw [ite_eq_right (by rw [h3]; decide), ite_eq_right (by rw [h3]; decide)]
    exact ht

/-! ## The loop -/

/-- The loop's state: the search from octet `used`, with `keys` and `scalars`
left, leads to the expected result. -/
def KeyInvariant (p : KeyPublic) (original : State) (expected : KeySearchResult)
    (n : Nat) (s : State) : Prop :=
  ∃ used keys scalars, n = 128 * keys + scalars + 1 ∧ KeyLive p original used keys scalars s ∧
    expected.outcome = (p.tail (keyRand original) used keys scalars).outcome ∧
    expected.used = (p.tail (keyRand original) used keys scalars).used

theorem key_iteration (a : Attempt) {p : KeyPublic} {original s : State}
    {expected : KeySearchResult} {n : Nat}
    (h : KeyInvariant p original expected n s) :
    WP isa (iteration a.call) s fun t =>
      (isa.eval (.zero .t0) t = some false ∧ KeyDone p original expected t) ∨
      (isa.eval (.zero .t0) t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) := by
  obtain ⟨used, keys, scalars, hn, h, ho, hu⟩ := h
  have hlen := h.rand_length
  have done : ∀ (r : KeySearchResult) t, KeyDone p original r t →
      r.outcome = (p.tail (keyRand original) used keys scalars).outcome →
      r.used = (p.tail (keyRand original) used keys scalars).used →
      WP isa (.block [ldf .t0 14, .addi .t0 .t0 (-4)]) t fun t =>
        (isa.eval (.zero .t0) t = some false ∧ KeyDone p original expected t) ∨
        (isa.eval (.zero .t0) t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) :=
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
    have := of_decide_eq_false hlong; have := h.used_le; omega
  have hr : p.len ≤ (keyRand original).length - used := by rw [hlen]; omega
  refine WP.seq (WP.mono (key_attempt_run a hu3 hroom) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (key_classify ht hroom (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hs) hp)
    fun q hq => ?_
  rcases attemptStatus_cases (policy := .cached) p.a p.len ((keyRand original).drop used) with h1 | h2 | h3
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
    {expected : KeySearchResult} {n : Nat}
    (h : KeyInvariant p original expected n s) :
    WP isa (.loop (iteration a.call) (.zero .t0)) s (KeyDone p original expected) :=
  WP.loop (M := isa) (body := iteration a.call) (c := .zero .t0)
    (Q := KeyDone p original expected) (KeyInvariant p original expected)
    (fun _ _ h => key_iteration a h) n s h

/-! ## The entry -/

def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .s0), (5, s.gpr .a0), (6, s.gpr .a2), (7, s.gpr .a5), (8, s.gpr .a6), (15, s.gpr .a4),
    (9, stackArg s 0), (10, stackArg s 1), (11, 0), (12, stackArg s 2), (13, stackArg s 3)]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem input_args {p : KeyPublic} {s : State} (h : KeyInput p s) (j : Nat) (hj : j < 7) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, List.mem_append_left _ (by rw [h.rd_eq]; simp [inReads]), ?_⟩
  have e : inArgs s = ⟨s.sp, 56⟩ := by simp only [inArgs, stackArgAddr, Nat.mul_zero, add_ofNat_zero]
  rw [e]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- The registers the entry writes. -/
abbrev entryRegs : List Reg := [.t1, .t2, .t3, .t4, .t5, .t6, .s0]

theorem entry_ok {p : KeyPublic} {s : State} (h : KeyInput p s) :
    WP isa (.block entry) s fun t =>
      (t.gpr .s0 = p.control ∧ t.mem = writeController s.mem p.control (entryValues s)) ∧
      Keep entryRegs s t ∧ t.sp = s.sp := by
  have a := CtlAccess.of_scr (h.control_scr (t := s) rfl)
  have hc : stackArg s 4 = p.control := congrArg KeyPublic.control h.2
  have hsp : s.sp.toNat % 8 = 0 := by have := h.1.2.2.1; omega
  have v0 : s.mem.readW s.sp 64 = stackArg s 0 := by
    simp only [stackArg, stackArgAddr, Nat.mul_zero, add_ofNat_zero]
  have v1 : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = stackArg s 1 := rfl
  have v2 : s.mem.readW (s.sp + BitVec.ofNat 64 16) 64 = stackArg s 2 := rfl
  have v3 : s.mem.readW (s.sp + BitVec.ofNat 64 24) 64 = stackArg s 3 := rfl
  have v4 : s.mem.readW (s.sp + BitVec.ofNat 64 32) 64 = p.control :=
    (show _ = stackArg s 4 from rfl).trans hc
  have a0 : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa only [Nat.mul_zero, add_ofNat_zero] using input_args h 0 (by decide)
  have a1 := input_args h 1 (by decide)
  have a2 := input_args h 2 (by decide)
  have a3 := input_args h 3 (by decide)
  have a4 := input_args h 4 (by decide)
  simp only [Nat.reduceMul] at a1 a2 a3 a4
  refine WP.mono (WP.rdwr (WP.keep entryRegs ?_ (by rfl) rfl)) fun _ ⟨⟨hq, k⟩, _, _, hsp⟩ => ⟨hq, k, hsp⟩
  unfold entry writeController entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, exec_addSp (show 0 < 2048 by decide), add_ofNat_zero, v0, v1, v2, v3, v4, a0, a1, a2, a3, a4,
    hsp, al8 hsp (d := 8) (by decide), al8 hsp (d := 16) (by decide), al8 hsp (d := 24) (by decide),
    al8 hsp (d := 32) (by decide), a.st 32 (by decide), a.st 40 (by decide), a.st 48 (by decide),
    a.st 56 (by decide), a.st 64 (by decide), a.st 72 (by decide), a.st 80 (by decide),
    a.st 88 (by decide), a.st 96 (by decide), a.st 104 (by decide), a.st 120 (by decide),
    a.al 32 (by decide) (by decide), a.al 40 (by decide) (by decide), a.al 48 (by decide) (by decide),
    a.al 56 (by decide) (by decide), a.al 64 (by decide) (by decide), a.al 72 (by decide) (by decide),
    a.al 80 (by decide) (by decide), a.al 88 (by decide) (by decide), a.al 96 (by decide) (by decide),
    a.al 104 (by decide) (by decide), a.al 120 (by decide) (by decide), fin64_exec_li_zero]

private theorem word_zero (m : Mem) (B : Addr) : word m B 0 = m.readW B 64 := by
  simp only [Bignum.word, off, BitVec.add_zero]

theorem entry_headers {p : KeyPublic} {s : State} (h : KeyInput p s) :
    Slots (writeController s.mem p.control (entryValues s)) p.control
      (p.headers 0 p.keys p.scalars) := by
  have hw := h.width_word
  cases h.2
  intro e he
  simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (entryValues_bound s) _ (by dsimp only; decide)] <;>
    simp only [keyOfState, controllerValue, entryValues,
      List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.sub_zero, Nat.mul_zero, BitVec.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 8), word_zero]
  all_goals first
    | rfl
    | (simp only [Bignum.word, off]; rfl)
    | (simp only [Bignum.word, off, Nat.reduceMul]
       exact hw.trans (by simp only [keyLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]))

/-- The push of the frame saving `ra` writes only below the stack pointer. -/
theorem push_frame (s : State) (m : Mem) (v : BitVec 64) :
    Frame (KeyInput.callChanges s) m (m.write (s.sp - 16 + 8) 8 v) := by
  have e : s.sp - 16 + 8 = s.sp - BitVec.ofNat 64 8 := by bv_omega
  have hr : below s.sp stackUse ∈ KeyInput.callChanges s := by simp [KeyInput.callChanges]
  refine Frame.write (Frame.refl _ _) hr _ ?_
  rw [e]; exact Offset.contains_below s.sp (a := 8) (b := 64) (by decide) (by decide) (by decide)

theorem key_start {p : KeyPublic} {s t : State} (h : KeyInput p s)
    (hx : t.gpr .s0 = p.control) (hm : t.mem = writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) (hsp : t.sp = s.sp) :
    KeyLive p s 0 p.keys p.scalars (framed .ra t) := by
  have hf := writeController_frame s.mem p.control (entryValues s) (entryValues_bound s)
  have hf₁ : Frame (KeyInput.changes s) s.mem t.mem := by
    rw [hm]
    exact hf.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inCtl s, by simp [KeyInput.changes, inWrites], by rw [← h.2]; exact fun _ hi => hi⟩
  have hp := push_frame s t.mem (t.gpr .ra)
  rw [← hsp] at hp
  have hf₂ : Frame (KeyInput.changes s) s.mem (framed .ra t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 16) : word (framed .ra t).mem p.control (8 * j) = word t.mem p.control (8 * j) :=
    h.control_frame hp j hj
  refine ⟨h, Nat.zero_le _, h.keys_le, h.scalars_le, k.2.1, k.2.2, ?_, hx, ?_, ?_, ?_, ?_, ?_, hf₂⟩
  · show t.sp - 16 = p.sp - 16
    rw [hsp, h.sp_eq]
  · intro r hr h0
    exact k.gpr (by revert r hr h0; decide)
  · rw [show (32 : Nat) = 8 * 4 from rfl, hc 4 (by decide), hm,
      writeController_word _ _ _ (entryValues_bound s) 4 (by decide)]
    rfl
  · rw [h.random_frame hf₂]
    cases h.2
    rfl
  · rw [h.domain_frame hf₂]
    cases h.2
    rfl
  · intro e he
    rw [hc e.1 (KeyPublic.headers_index he), hm]
    exact entry_headers h e he

/-! ## Returning -/

theorem KeyInput.used_disjoint {p : KeyPublic} {s : State} (h : KeyInput p s) :
    (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ ∧ (⟨p.yp, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ ∧
      (⟨p.control, 128⟩ : Region).Disjoint ⟨p.up, 8⟩ := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  have hu : inUsed s = ⟨p.up, 8⟩ := by rw [← h.2]; rfl
  have hc : inCtl s = ⟨p.control, 128⟩ := by rw [← h.2]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← h.x_eq, ← hu]; exact hpw.1.2.1
  · rw [← h.y_eq, ← hu]; exact hpw.2.1.1
  · rw [← hc, ← hu]; exact hpw.2.2.1.2.symm

theorem KeyInput.used_wr {p : KeyPublic} {s : State} (h : KeyInput p s) {t : State}
    (hw : t.wr = s.wr) : InRegions t.wr p.up 8 :=
  ⟨⟨p.up, 8⟩, by rw [hw, h.wr_eq, ← h.2]; simp [inWrites, inUsed, keyOfState],
    Region.contains_self _ _⟩

theorem key_finish_values {p : KeyPublic} {original s : State} {result : KeySearchResult}
    (h : KeyDone p original result s) :
    WP isa (.block finish) s fun t =>
      (t.gpr .a0 = BitVec.ofNat 64 result.status ∧ t.gpr .s0 = original.gpr .s0 ∧
        t.mem = s.mem.writeW p.up (BitVec.ofNat 64 result.used)) ∧
      Keep [.t0, .t1, .a0, .s0] s t := by
  have a := CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)
  have hup := h.input.used_wr h.wr
  have hual := h.input.up_al
  have hu := h.usedPtr
  have hd := h.used
  have hs := h.status
  have hx := h.savedS0
  simp only [Bignum.word, off] at hu hd hs hx
  have hf : Frame [⟨p.up, 8⟩] s.mem (s.mem.writeW p.up (BitVec.ofNat 64 result.used)) :=
    Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hx' : (s.mem.writeW p.up (BitVec.ofNat 64 result.used)).readW (p.control + BitVec.ofNat 64 32) 64 =
      original.gpr .s0 :=
    (hf.readW (r := ⟨p.control, 128⟩) (Offset.contains_base _ (by decide) (by decide))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.input.used_disjoint.2.2)
      (by decide)).trans hx
  refine WP.keep [.t0, .t1, .a0, .s0] ?_ (by rfl) rfl
  unfold finish
  brun [ldf, h.s0, hu, hd, hs, hx', hup, hual, add_ofNat_zero, a.ld 120 (by decide), a.ld 88 (by decide),
    a.ld 112 (by decide), a.ld 32 (by decide), a.al 120 (by decide) (by decide), a.al 88 (by decide) (by decide),
    a.al 112 (by decide) (by decide), a.al 32 (by decide) (by decide)]

/-- What the search returns, for its result. -/
def KeyReturned (p : KeyPublic) (result : KeySearchResult) (t : State) : Prop :=
  ((t.gpr .a0).setWidth 32).toNat = result.status ∧ KeyOutput p result t.mem ∧
    Spec.Rsa.wordsAt t.mem p.control 4 = p.policy result ∧
    Spec.Rsa.wordsAt t.mem p.up 1 = [BitVec.ofNat 64 result.used]

theorem key_finish {p : KeyPublic} {original s : State} {result : KeySearchResult}
    (h : KeyDone p original result s) :
    WP isa (.block finish) s fun t => KeyReturned p result t ∧
      (∀ reg ∈ preserved, t.gpr reg = original.gpr reg) ∧ t.sp = s.sp ∧ t.gpr .ra = s.gpr .ra := by
  refine WP.mono (WP.rdwr (key_finish_values h)) fun t ⟨⟨⟨ha, hs0, hm⟩, k⟩, _, _, hsp⟩ => ?_
  have hd := h.input.used_disjoint
  have hk := h.input.len_lt
  have hf : Frame [⟨p.up, 8⟩] s.mem t.mem := by
    rw [hm]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hb : ∀ q : Addr, (⟨q, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ →
      Spec.Rsa.bytesAt t.mem q p.len = Spec.Rsa.bytesAt s.mem q p.len := by
    intro q hq
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hq)
      (show p.len ≤ 2 ^ 64 by omega) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd.2.2) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, hsp, k.gpr (by decide)⟩
  · rw [ha]
    have := key_status_lt result
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · have ho := h.output
    unfold KeyOutput at ho ⊢
    rw [hb _ hd.1, hb _ hd.2.1]
    exact ho
  · have he : Spec.Rsa.wordsAt t.mem p.control 4 = Spec.Rsa.wordsAt s.mem p.control 4 := by
      change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
        word t.mem p.control (8 * 3)] = [word s.mem p.control (8 * 0), word s.mem p.control (8 * 1),
        word s.mem p.control (8 * 2), word s.mem p.control (8 * 3)]
      rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]
    exact he.trans h.policy
  · change [word t.mem p.up 0] = [_]
    rw [hm]
    congr 1
    simpa only [Bignum.word, off, BitVec.add_zero] using
      Mem.readW_writeW_self64 s.mem p.up (BitVec.ofNat 64 result.used)
  · intro reg hreg
    by_cases he : reg = .s0
    · subst he; exact hs0
    · exact (k.gpr (by revert reg hreg he; decide)).trans (h.saved reg hreg he)

/-! ## The search's frame -/

theorem iteration_depth (a : Attempt) : sdepth (iteration a.call) = 48 := by
  have := a.stack
  simp only [iteration, branch, attemptOrRequest, attemptRun, exhausted, zeroOutputs, zeroOut, classify,
    request, Impl.Bignum.RISCV64.countLoop, sdepth, Attempt.call, Instr.frameBytes, this, Nat.max_def]
  decide

/-- After the frame: a finished search, with `ra` and the stack pointer
back. -/
theorem KeyDone.popped {p : KeyPublic} {original s : State} {r : KeySearchResult}
    (h : KeyDone p original r s) (v sp : BitVec 64) :
    KeyDone p original r { s.write .ra v with sp := sp } := by
  refine ⟨h.input, h.rd, h.wr, ?_, fun reg hr h0 => ?_, h.savedS0, h.usedPtr, h.used,
    h.status, h.policy, h.output⟩
  · show (s.write .ra v).gpr .s0 = _
    rw [RegUpd.gpr_write, ite_eq_right (by decide)]; exact h.s0
  · show (s.write .ra v).gpr reg = _
    rw [RegUpd.gpr_write, ite_eq_right (fun e => by subst e; exact absurd hr (by decide))]
    exact h.saved reg hr h0

theorem KeyInput.tail_eq {p : KeyPublic} {s : State} (h : KeyInput p s) :
    keyResult s = p.tail (keyRand s) 0 p.keys p.scalars := by
  cases h.2
  simp only [keyResult, KeyPublic.tail, keyTail, after, GenerationPolicy.search, keyOfState, KeyPublic.a, List.drop_zero,
    Nat.zero_add]

theorem key_body {p : KeyPublic} {s t : State} (a : Attempt) (h : KeyInput p s)
    (hx : t.gpr .s0 = p.control)
    (hm : t.mem = writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) (hsp : t.sp = s.sp) :
    WP isa (search a.call) t fun u =>
      KeyDone p s (keyResult s) u ∧ u.gpr .ra = s.gpr .ra ∧ u.sp = s.sp := by
  have hl := key_start h hx hm k hsp
  have hsp' : 16 ≤ t.sp.toNat := by rw [hsp, ← h.sp_eq]; have := h.sp_room; omega
  unfold search
  refine WP.frameRegAny (r := .ra)
    (Q := fun u => KeyDone p s (keyResult s) u ∧ u.gpr .ra = s.gpr .ra ∧ u.sp = s.sp) hsp' ?_ ?_ ?_
  · intro R hR
    rw [k.2.2, h.wr_eq] at hR
    have hd := h.stack_disjoint (r := R) (List.mem_append_left _ hR)
    refine hd.sub_left ?_
    rw [hsp, show s.sp - 16 = s.sp - BitVec.ofNat 64 16 from rfl]
    exact Offset.sub_below s.sp (a := 16) (b := 64) (by decide) (by decide)
  · refine WP.mono (key_loop a (expected := keyResult s) (n := 128 * p.keys + p.scalars + 1)
      ⟨0, p.keys, p.scalars, rfl, hl, by rw [h.tail_eq], by rw [h.tail_eq]⟩)
      fun u hu => ⟨hu.popped _ _, ?_, hsp⟩
    show (u.write .ra (t.gpr .ra)).gpr .ra = _
    rw [RegUpd.gpr_write_self, k.gpr (by decide)]
  · show sdepth (iteration a.call) + 16 < 2 ^ 64
    rw [iteration_depth a]; decide

theorem KeyReturned.post {s t : State} (h : KeyReturned (keyOfState s) (keyResult s) t) : keyPost s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem key_correct_ok (a : Attempt) {s : State} (h : keyPre s) :
    WP isa (code a.call) s fun t => keyPost s t ∧ abiPreserved s t := by
  let p := keyOfState s
  have hp : KeyInput p s := ⟨h, rfl⟩
  unfold code
  refine WP.seq (WP.mono (entry_ok hp) fun t ⟨⟨hx, hm⟩, k, hsp⟩ => ?_)
  refine WP.seq (WP.mono (key_body a hp hx hm k hsp) fun u ⟨hd, hra, husp⟩ => ?_)
  refine WP.mono (key_finish hd) fun q ⟨hr, hg, hqsp, hqra⟩ => ?_
  exact ⟨hr.post, hg, hqsp.trans husp, hqra.trans hra⟩

theorem key_correct (a : Attempt) (s : State) (h : keyContract.pre s) :
    ∃ tr t, Exec isa (code a.call) s tr t ∧ abiPreserved s t ∧ keyContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := key_correct_ok a h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.Ffdh.RISCV64.Cached.SearchProof
