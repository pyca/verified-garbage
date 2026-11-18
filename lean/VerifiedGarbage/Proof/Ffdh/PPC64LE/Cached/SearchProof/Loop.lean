module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Cached
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Writes
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Loop
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Outputs
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ffdh.PPC64LE.Cached.SearchProof.Call`, which this module and modules that import it used -/

section

/-! ### `Ffdh.PPC64LE.Cached.SearchProof.Entry`, which this module and modules that import it used -/

section

/-! # The key-generation controller's entry (PPC64LE)

The stack arguments are loaded, the caller's `r31` saved in word 4 and the
arguments stored in the controller's words; then, in the frame saving the
link register, the controller is at the tape's start (`key_start`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.PPC64LE.Generation (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue)
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search (ldf stf entry arguments terminal zeroOut zeroOutputs exhausted advance
  rejectedScalar rejectedPublic test classify request room finish)
open VG.Impl.Ffdh.PPC64LE.Cached.Search

def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .r31), (5, s.gpr .r3), (6, s.gpr .r5), (7, s.gpr .r8), (8, s.gpr .r9), (15, s.gpr .r7),
    (9, stackArg s 0), (10, stackArg s 1), (11, 0), (12, stackArg s 2), (13, stackArg s 3)]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem input_args {p : KeyPublic} {s : State} (h : KeyInput p s) (j : Nat) (hj : j < 7) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, ?_, ?_⟩
  · rw [h.1.2.2.1]
    exact List.mem_append_left _ (by simp [inReads])
  · simp only [inArgs, stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem arg_value (s : State) (j : Nat) :
    s.mem.readW (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * j)) 64 = stackArg s j := by
  simp only [stackArg, stackArgAddr]
  rw [VG.Offset.add_add]
  congr 3
  omega_using []

/-- The registers the entry writes. -/
abbrev entryRegs : List Reg := [.r0, .r4, .r6, .r10, .r11, .r12, .r31]

theorem entry_ok {p : KeyPublic} {s : State} (h : KeyInput p s) :
    WP isa (.block entry) s fun t =>
      (t.gpr .r31 = p.control ∧ t.mem = writeController s.mem p.control (entryValues s)) ∧
      Keep entryRegs s t := by
  have scr := h.control_scr (t := s) rfl
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hc : stackArg s 4 = p.control := congrArg KeyPublic.control h.2
  have v0 : s.mem.readW (s.sp + BitVec.ofNat 64 96) 64 = stackArg s 0 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using arg_value s 0
  have v1 := arg_value s 1
  have v2 := arg_value s 2
  have v3 := arg_value s 3
  have v4 : s.mem.readW (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 32) 64 = p.control :=
    (arg_value s 4).trans hc
  have a0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96) 8 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using input_args h 0 (by decide)
  have a1 := input_args h 1 (by decide)
  have a2 := input_args h 2 (by decide)
  have a3 := input_args h 3 (by decide)
  have a4 := input_args h 4 (by decide)
  simp only [Nat.reduceMul] at v1 v2 v3 a1 a2 a3 a4
  have w1 := v1; have w2 := v2; have w3 := v3; have w4 := v4
  have b1 := a1; have b2 := a2; have b3 := a3; have b4 := a4
  rw [VG.Offset.add_add] at w1 w2 w3 w4 b1 b2 b3 b4
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  refine WP.keep entryRegs ?_ (by decide)
  unfold entry writeController entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [ldf, stf, ea, v0, v1, v2, v3, v4, a0, a1, a2, a3, a4, w1, w2, w3, w4, b1, b2, b3, b4, hs 32 (by decide), hs 40 (by decide),
    hs 48 (by decide), hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 80 (by decide),
    hs 88 (by decide), hs 96 (by decide), hs 104 (by decide), hs 120 (by decide)]
  refine ⟨BitVec.add_zero _, ?_⟩
  rfl

private theorem word_zero (m : Mem) (B : Addr) : word m B 0 = m.readW B 64 := by
  simp only [Bignum.word, off, BitVec.add_zero]

theorem KeyInput.width_word {p : KeyPublic} {s : State} (h : KeyInput p s) :
    s.mem.readW (stackArg s 4 + 16) 64 = BitVec.ofNat 64 (keyLen s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hw, -, -⟩ := h.1
  exact hw

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

/-- The push of the frame saving the link register writes only below the
stack pointer. -/
theorem push_frame (s : State) (m : Mem) (v : BitVec 64) :
    Frame (KeyInput.callChanges s) m ((m.write (s.sp - 48) 8 s.sp).write (s.sp - 48 + 32) 8 v) := by
  have e : s.sp - 48 + 32 = s.sp - BitVec.ofNat 64 16 := by bv_omega
  have hr : below s.sp stackUse ∈ KeyInput.callChanges s := by simp [KeyInput.callChanges]
  refine Frame.write (Frame.write (Frame.refl _ _) hr _ ?_) hr _ ?_
  · exact Offset.contains_below s.sp (a := 48) (b := 192) (by decide) (by decide) (by decide)
  · rw [e]; exact Offset.contains_below s.sp (a := 16) (b := 192) (by decide) (by decide) (by decide)

theorem key_start {p : KeyPublic} {s t : State} (h : KeyInput p s)
    (hx : t.gpr .r31 = p.control) (hm : t.mem = writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) :
    KeyLive p s 0 p.keys p.scalars (framed .r0 t) := by
  have hf := writeController_frame s.mem p.control (entryValues s) (entryValues_bound s)
  have hf₁ : Frame (KeyInput.changes s) s.mem t.mem := by
    rw [hm]
    exact hf.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inCtl s, by simp [KeyInput.changes, inWrites], by rw [← h.2]; exact fun _ hi => hi⟩
  have hp := push_frame s t.mem (t.gpr .r0)
  rw [← k.sp] at hp
  have hf₂ : Frame (KeyInput.changes s) s.mem (framed .r0 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 16) : word (framed .r0 t).mem p.control (8 * j) = word t.mem p.control (8 * j) :=
    h.control_frame hp j hj
  refine ⟨h, Nat.zero_le _, h.keys_le, h.scalars_le, k.rd, k.wr, ?_, hx, ?_, ?_, ?_, ?_, ?_, hf₂⟩
  · show t.sp - 48 = p.sp - 48
    rw [k.sp, h.sp_eq]
  · intro r hr h31
    exact k.gpr r (by revert r hr h31; decide)
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

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

end

end

/-! # One attempt of the cached key-generation controller (PPC64LE)

In its frame of 144 bytes, the controller passes `vg_ffdh_generate_key_cached`
the next `p_len` octets of the tape and the context, its stack arguments at
offset 96 of the frame (`ctx` and `ctx_len` copied from the controller's own
stack arguments). The attempt keeps the controller's state, and leaves its
status, and the key pair or zeros, in `x` and `y`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame_size
  controllerValue)
open VG.Proof.Ffdh.PPC64LE.Cached (cgContract cgStack cgScalar cgA cgDom)
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search (ldf stf entry arguments terminal zeroOut zeroOutputs exhausted advance
  rejectedScalar rejectedPublic test classify request room finish)
open VG.Impl.Ffdh.PPC64LE.Cached.Search

/-! ## Where the attempt's buffers are, from the controller's

The attempt's buffers are the controller's (`x`, `y`, the domain, a slice
of the tape, the context and the working space), and its stack arguments
are in the attempt's frame at offset 96, in the 192 bytes of stack below the
controller's stack pointer on entry, which no buffer overlaps.
-/

/-- The stack pointer in the attempt's frame. -/
abbrev callSp (p : KeyPublic) : Addr := p.sp - 48 - BitVec.ofNat 64 144

theorem callSp_eq (p : KeyPublic) : callSp p = p.sp - BitVec.ofNat 64 192 := by
  rw [callSp, BitVec.sub_sub]; rfl

/-- The attempt's regions: its outputs, the domain, the tape's slice, the
working space and its arguments. -/
abbrev rX (p : KeyPublic) : Region := ⟨p.xp, p.len⟩
abbrev rY (p : KeyPublic) : Region := ⟨p.yp, p.len⟩
abbrev rD (p : KeyPublic) : Region := ⟨p.dp, p.dlen⟩
abbrev rR (p : KeyPublic) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.len⟩
abbrev rS (p : KeyPublic) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : KeyPublic) : Region := ⟨callSp p + BitVec.ofNat 64 96, 40⟩

structure CallFacts (p : KeyPublic) (used : Nat) : Prop where
  room : 192 ≤ p.sp.toNat
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
  xC : (rX p).Disjoint ⟨callSp p, 144⟩
  yC : (rY p).Disjoint ⟨callSp p, 144⟩

private theorem sub_tape {r : Addr} {n used len : Nat}
    (hu : used + len ≤ n) : Region.Sub ⟨r + BitVec.ofNat 64 used, len⟩ ⟨r, n⟩ :=
  Offset.sub_base r hu

private theorem nowrap_tape {r : Addr} {n used len : Nat} (hn : r.toNat + n ≤ 2 ^ 64)
    (hu : used + len ≤ n) : (r + BitVec.ofNat 64 used).toNat + len ≤ 2 ^ 64 := by
  obtain hul : used < 2 ^ 64 ∨ len = 0 := by omega_using [hn, hu]
  rcases hul with hul | hz
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
    have := Nat.mod_le (r.toNat + used) (2 ^ 64)
    by_cases hz : r.toNat + used < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hz]; omega_using [hn, hu]
    · omega_using [hn, hu]
  · subst hz; simp only [Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _)

theorem rA_eq (p : KeyPublic) : callSp p + BitVec.ofNat 64 96 = p.sp - BitVec.ofNat 64 96 := by
  rw [callSp_eq]; exact (Offset.sub_ofNat_eq p.sp (by decide : 96 ≤ 192)).symm

theorem rA_sub (p : KeyPublic) : Region.Sub (rA p) (below p.sp stackUse) := by
  rw [rA, rA_eq]; exact Offset.sub_below _ (by decide) (by decide)

theorem KeyLive.callFacts {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen) :
    CallFacts p used := by
  have hi := h.input
  obtain ⟨_, hsp, _, _, hnw, hpw, hwr, hstk, hlen, hdlen, hx1, hx3, hscr, -, -, -, -, -, -⟩ := hi.1
  cases hi.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pxy, pxu, pxs, pxc⟩, ⟨pyu, pys, pyc⟩, ⟨pus, puc⟩, psc⟩ := hpw
  obtain ⟨⟨wxd, wxr, -, wxa⟩, ⟨wyd, wyr, -, wya⟩, -, ⟨wsd, wsr, -, wsa⟩, -⟩ := hwr
  obtain ⟨bx, by', -, bs, -, bd, br, -, -⟩ := hstk
  obtain ⟨nx, ny, -, ns, -, nd, nr, -, -⟩ := hnw
  obtain hX : rX (keyOfState original) = inX original := by
    simp only [rX, inX, keyOfState, hx1]
  obtain hY : rY (keyOfState original) = inY original := by
    simp only [rY, inY, keyOfState, hx3]
  have hD : rD (keyOfState original) = inDom original := rfl
  have hS : rS (keyOfState original) = inScr original := rfl
  obtain hR : Region.Sub (rR (keyOfState original) used) (inRand original) :=
    sub_tape hroom
  obtain hA := rA_sub (keyOfState original)
  obtain hC : Region.Sub ⟨callSp (keyOfState original), 144⟩ (below (keyOfState original).sp stackUse) := by
    rw [callSp_eq]; exact Offset.sub_below _ (by decide) (by decide)
  have hsp' : (keyOfState original).sp = original.sp := rfl
  rw [hsp'] at hA hC
  rw [← hX] at pxy pxs wxd wxr bx nx
  rw [← hY] at pxy pys wyd wyr by' ny
  rw [← hD] at wxd wyd wsd bd nd
  rw [← hS] at pxs pys wsd wsr bs ns
  refine ⟨by rw [hsp']; exact hsp, pxy, wxd, wxr.sub_right hR, pxs, (bx.symm.sub_right hA),
    wyd, wyr.sub_right hR, pys, by'.symm.sub_right hA, wsd.symm, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, nx, ny, nd, nowrap_tape nr hroom, ns, hlen, hdlen, ?_, ?_, ?_, ?_,
    bx.symm.sub_right hC, by'.symm.sub_right hC⟩
  · simp only [keyOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [keyOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
  · exact BitVec.isLt _
  · exact BitVec.isLt _

/-- The uncached attempt's stack arguments: `rand_len` (`p_len`), `scratch`
and `scratch_len`, at offset 96 of its frame. -/
def baseValues (p : KeyPublic) : List (Nat × BitVec 64) :=
  [(12, BitVec.ofNat 64 p.len), (13, p.B), (14, BitVec.ofNat 64 (p.Z / 8))]

/-- Then `ctx` and `ctx_len`. -/
def ctxValues (p : KeyPublic) : List (Nat × BitVec 64) := [(15, p.ctx), (16, BitVec.ofNat 64 p.ctxLen)]

def callValues (p : KeyPublic) : List (Nat × BitVec 64) := baseValues p ++ ctxValues p

theorem callValues_bound (p : KeyPublic) : ∀ e ∈ callValues p, e.1 < 17 := by
  simp only [callValues, baseValues, ctxValues, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The block after `arguments`: the context's two arguments. -/
abbrev ctxArguments : List Instr :=
  [.addSp .r12 328, .load .d .r0 .r12 0, .store .d .r0 .r11 24, .load .d .r0 .r12 8, .store .d .r0 .r11 32]

theorem cachedArguments_eq : cachedArguments = arguments ++ ctxArguments := rfl

/-- Word `j < 17` of a controller's values at `B`, as `writeController_word`
for sixteen. -/
theorem writeController_word17 (m : Mem) (B : Addr) (values : List (Nat × BitVec 64))
    (hvalues : ∀ e ∈ values, e.1 < 17) (j : Nat) (hj : j < 17) :
    word (writeController m B values) B (8 * j) = controllerValue values j (word m B (8 * j)) := by
  induction values generalizing m with
  | nil => rfl
  | cons e values ih =>
    obtain he := hvalues e (List.mem_cons_self ..)
    change word (writeController (m.writeW (off B (8 * e.1)) e.2) B values) B (8 * j) = _
    rw [ih _ (fun x hx => hvalues x (List.mem_cons_of_mem _ hx))]
    refine congrArg (controllerValue values j) ?_
    change _ = if j = e.1 then e.2 else word m B (8 * j)
    by_cases hje : j = e.1
    · subst hje; rw [ite_eq_left rfl]; exact word_writeW_self _ _ _ _
    · rw [ite_eq_right hje]; exact hdrStore_hdr _ _ _ (by omega_using [he]) (by omega_using [hj]) (Ne.symm hje)

/-- The attempt's register arguments. -/
def KeyArgs (p : KeyPublic) (used : Nat) (t : State) : Prop :=
  t.gpr .r3 = p.xp ∧ t.gpr .r4 = BitVec.ofNat 64 p.len ∧ t.gpr .r5 = p.yp ∧
  t.gpr .r6 = BitVec.ofNat 64 p.len ∧ t.gpr .r7 = p.dp ∧ t.gpr .r8 = BitVec.ofNat 64 p.dlen ∧
  t.gpr .r9 = BitVec.ofNat 64 p.len ∧ t.gpr .r10 = p.rp + BitVec.ofNat 64 used

/-- The registers the arguments' block writes. -/
abbrev argRegsW : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem callSp_eq' (p : KeyPublic) : p.sp - 48 - BitVec.ofNat 64 144 = callSp p := rfl

/-- The frame's push writes its back chain below the stack pointer. -/
theorem alloc_frame {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    Frame (KeyInput.callChanges original) s.mem (allocated 144 s).mem := by
  have hi := h.input
  refine Frame.write (Frame.refl _ _) (r := below original.sp stackUse) (by simp [KeyInput.callChanges]) _ ?_
  rw [h.sp, callSp_eq', callSp_eq, ← hi.sp_eq]
  exact Offset.contains_below p.sp (a := 192) (b := 192) (by decide) (by decide) (by decide)

theorem base_arguments_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block arguments) (allocated 144 s) fun u =>
      (KeyArgs p used u ∧ u.mem = writeController (allocated 144 s).mem (callSp p) (baseValues p) ∧
        u.gpr .r11 = callSp p + BitVec.ofNat 64 96) ∧
      Keep argRegsW (allocated 144 s) u := by
  have a := h.access
  obtain hc := h.input.control_frame (alloc_frame h)
  obtain e0 : s.sp - BitVec.ofNat 64 144 = callSp p := by rw [h.sp]
  obtain hw : ∀ e, e + 8 ≤ 112 → InRegions (allocated 144 s).wr (callSp p + 32 + BitVec.ofNat 64 e) 8 := by
    intro e he
    refine ⟨frameR 144 s, List.mem_cons_self .., ?_⟩
    simp only [frameR, e0]
    exact Offset.contains_base _ he (by omega_using [he])
  obtain hl : ∀ d, d + 8 ≤ 128 →
      InRegions ((allocated 144 s).rd ++ (allocated 144 s).wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun d hd => by
      obtain ⟨r, hr, hc⟩ := a.ld d hd
      refine ⟨r, ?_, hc⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv (j : Nat) (hj : j < 16) {v : BitVec 64} (he : (j, v) ∈ p.headers used keys scalars) :
      (allocated 144 s).mem.readW (p.control + BitVec.ofNat 64 (8 * j)) 64 = v :=
    (hc j hj).trans (h.header he)
  obtain hv2 := hv 2 (by decide) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  obtain hv5 := hv 5 (by decide) (v := p.xp) (by simp [KeyPublic.headers])
  obtain hv6 := hv 6 (by decide) (v := p.yp) (by simp [KeyPublic.headers])
  obtain hv7 := hv 7 (by decide) (v := p.dp) (by simp [KeyPublic.headers])
  obtain hv8 := hv 8 (by decide) (v := BitVec.ofNat 64 p.dlen) (by simp [KeyPublic.headers])
  obtain hv9 := hv 9 (by decide) (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  obtain hv12 := hv 12 (by decide) (v := p.B) (by simp [KeyPublic.headers])
  obtain hv13 := hv 13 (by decide) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [KeyPublic.headers])
  simp only [Nat.reduceMul] at hv2 hv5 hv6 hv7 hv8 hv9 hv12 hv13
  obtain ea : ∀ t : State, exec (.addSp .r11 96) t = some (t.write .r11 (t.sp + BitVec.ofNat 64 96)) := by
    intro t; simp [exec]
  obtain hwo : ∀ e, e + 8 ≤ 112 → InRegions (allocated 144 s).wr (Mont.off (callSp p) (32 + e)) 8 := by
    intro e he
    have := hw e he
    rwa [BitVec.add_assoc, show (32 : Addr) + BitVec.ofNat 64 e = BitVec.ofNat 64 (32 + e) by
      rw [BitVec.ofNat_add]; rfl] at this
  obtain hw96 := hwo 64 (by decide)
  obtain hw104 := hwo 72 (by decide)
  obtain hw112 := hwo 80 (by decide)
  have hw96' : InRegions (allocated 144 s).wr (callSp p + 96#64) 8 := hw96
  simp only [Nat.reduceAdd] at hw96 hw104 hw112
  refine WP.keep argRegsW ?_ (by decide)
  unfold arguments writeController baseValues KeyArgs
  simp only [List.foldl_cons, List.foldl_nil]
  have r31 : (allocated 144 s).gpr .r31 = p.control := h.r31
  have sp' : (allocated 144 s).sp = callSp p := e0
  prun [ldf, r31, sp', ea, hl 16 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide),
    hl 64 (by decide), hl 72 (by decide), hl 96 (by decide), hl 104 (by decide), hw96, hw96', hw104, hw112, hv2, hv5, hv6, hv7, hv8,
    hv9, hv12, hv13]


/-- The controller's stack argument `j`, through writes of its buffers and
its stack only. -/
theorem KeyInput.arg_frame {p : KeyPublic} {original : State} (h : KeyInput p original) {m : Mem}
    (hf : Frame (KeyInput.changes original) original.mem m) (j : Nat) (hj : j < 7) :
    m.readW (original.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * j)) 64 = stackArg original j := by
  rw [← arg_value original j]
  refine hf.readW (r := inArgs original) ?_ (h.read_disjoint (by simp [inReads])) (by decide)
  simp only [inArgs, stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem KeyInput.arg_in {p : KeyPublic} {original : State} (h : KeyInput p original) (j : Nat) (hj : j < 7) :
    InRegions original.rd (original.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs original, by rw [h.1.2.2.1]; simp [inReads], ?_⟩
  simp only [inArgs, stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- The frame's push and the base arguments write only the attempt's frame. -/
theorem base_frame {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {values : List (Nat × BitVec 64)}
    (hb : ∀ e ∈ values, 8 * e.1 + 8 ≤ 144) :
    Frame (KeyInput.callChanges original) s.mem (writeController (allocated 144 s).mem (callSp p) values) := by
  have hsp : p.sp = original.sp := h.input.sp_eq
  refine (alloc_frame h).trans ((writeController_frame_size _ _ values (size := 144) (by decide) hb).sub ?_)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨below original.sp stackUse, by simp [KeyInput.callChanges], ?_⟩
  rw [← hsp, callSp_eq]
  exact Offset.sub_below p.sp (a := 192) (b := 192) (by decide) (by decide)

/-- `ctx` and `ctx_len`, from the controller's stack arguments 5 and 6 to
the attempt's 3 and 4. -/
theorem ctx_arguments_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {u : State}
    (hsp : u.sp = callSp p) (h11 : u.gpr .r11 = callSp p + BitVec.ofNat 64 96)
    (hrd : u.rd = s.rd) (hwr : u.wr = (allocated 144 s).wr)
    (hm : u.mem = writeController (allocated 144 s).mem (callSp p) (baseValues p)) :
    WP isa (.block ctxArguments) u fun v =>
      v.mem = writeController u.mem (callSp p) (ctxValues p) ∧ Keep [.r0, .r12] u v := by
  have hi := h.input
  have hsp0 : p.sp = original.sp := hi.sp_eq
  obtain hbase : ∀ e ∈ baseValues p, 8 * e.1 + 8 ≤ 144 := by
    simp only [baseValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide
  obtain hfu : Frame (KeyInput.changes original) original.mem u.mem := by
    rw [hm]; exact h.frame.trans (frame_of_callChanges original (base_frame h hbase))
  obtain e0 : s.sp - BitVec.ofNat 64 144 = callSp p := by rw [h.sp]
  obtain eA : callSp p + BitVec.ofNat 64 328 = original.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * 5) := by
    rw [callSp_eq, hsp0]; bv_omega
  obtain eB : callSp p + BitVec.ofNat 64 336 = original.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * 6) := by
    rw [callSp_eq, hsp0]; bv_omega
  obtain eC : callSp p + BitVec.ofNat 64 120 = s.sp - BitVec.ofNat 64 144 + 32 + BitVec.ofNat 64 88 := by
    rw [e0]; bv_omega
  obtain eD : callSp p + BitVec.ofNat 64 128 = s.sp - BitVec.ofNat 64 144 + 32 + BitVec.ofNat 64 96 := by
    rw [e0]; bv_omega
  obtain rA : InRegions (u.rd ++ u.wr) (callSp p + BitVec.ofNat 64 328) 8 := by
    obtain ⟨r, hr, hc⟩ := hi.arg_in 5 (by decide)
    rw [eA]; exact ⟨r, List.mem_append_left _ (by rw [hrd, h.rd]; exact hr), hc⟩
  obtain rB : InRegions (u.rd ++ u.wr) (callSp p + BitVec.ofNat 64 336) 8 := by
    obtain ⟨r, hr, hc⟩ := hi.arg_in 6 (by decide)
    rw [eB]; exact ⟨r, List.mem_append_left _ (by rw [hrd, h.rd]; exact hr), hc⟩
  obtain wC : InRegions u.wr (callSp p + BitVec.ofNat 64 120) 8 := by
    refine ⟨frameR 144 s, by rw [hwr]; exact List.mem_cons_self .., ?_⟩
    rw [eC]; exact Offset.contains_base _ (by decide) (by decide)
  obtain wD : InRegions u.wr (callSp p + BitVec.ofNat 64 128) 8 := by
    refine ⟨frameR 144 s, by rw [hwr]; exact List.mem_cons_self .., ?_⟩
    rw [eD]; exact Offset.contains_base _ (by decide) (by decide)
  obtain vA : u.mem.readW (callSp p + BitVec.ofNat 64 328) 64 = p.ctx := by
    rw [eA, hi.arg_frame hfu 5 (by decide)]
    exact congrArg KeyPublic.ctx hi.2
  obtain hC : (below original.sp stackUse).Contains (callSp p + BitVec.ofNat 64 120) (64 / 8) := by
    rw [show callSp p + BitVec.ofNat 64 120 = original.sp - BitVec.ofNat 64 72 by
      rw [callSp_eq, hsp0]; bv_omega]
    exact Offset.contains_below original.sp (a := 72) (b := 192) (by decide) (by decide) (by decide)
  obtain vB : (u.mem.writeW (callSp p + BitVec.ofNat 64 120) p.ctx).readW
      (callSp p + BitVec.ofNat 64 336) 64 = BitVec.ofNat 64 p.ctxLen := by
    rw [eB, hi.arg_frame (hfu.writeW (r := below original.sp stackUse) (by simp [KeyInput.changes]) p.ctx hC)
      6 (by decide)]
    obtain hc := congrArg KeyPublic.ctxLen hi.2
    change (stackArg original 6).toNat = p.ctxLen at hc
    rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ea : ∀ t : State, exec (.addSp .r12 328) t = some (t.write .r12 (t.sp + BitVec.ofNat 64 328)) := by
    intro t; simp [exec]
  refine WP.keep [.r0, .r12] ?_ (by decide)
  unfold writeController ctxValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [hsp, h11, ea, rA, rB, wC, wD, vA, vB]

theorem key_arguments_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block cachedArguments) (allocated 144 s) fun u =>
      (KeyArgs p used u ∧ u.mem = writeController (allocated 144 s).mem (callSp p) (callValues p)) ∧
      Keep argRegsW (allocated 144 s) u := by
  rw [cachedArguments_eq, WP.block_append_iff]
  refine WP.mono (base_arguments_ok h) fun u ⟨⟨ha, hm, h11⟩, k⟩ => ?_
  obtain e0 : s.sp - BitVec.ofNat 64 144 = callSp p := by rw [h.sp]
  refine WP.mono (ctx_arguments_ok h (k.sp.trans e0) h11 k.rd k.wr hm) fun v ⟨hv, k'⟩ => ?_
  obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, k.trans' (k'.mono (by decide))⟩
  · rw [k'.gpr _ (by decide)]; exact r3
  · rw [k'.gpr _ (by decide)]; exact r4
  · rw [k'.gpr _ (by decide)]; exact r5
  · rw [k'.gpr _ (by decide)]; exact r6
  · rw [k'.gpr _ (by decide)]; exact r7
  · rw [k'.gpr _ (by decide)]; exact r8
  · rw [k'.gpr _ (by decide)]; exact r9
  · rw [k'.gpr _ (by decide)]; exact r10
  · rw [hv, hm]
    simp only [writeController, callValues, List.foldl_append]

/-- The regions the attempt reads: the domain, `p_len` octets of the tape at
`used`, the context and its stack arguments; those it writes: `x`, `y` and the working
space. -/
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
      stackArg u j = controllerValue (callValues p) (12 + j) (word m (callSp p) (8 * (12 + j))) := by
    unfold stackArg stackArgAddr
    rw [hu, hm]
    rw [show callSp p + BitVec.ofNat 64 (32 + 8 * (8 + j)) = callSp p + BitVec.ofNat 64 (8 * (12 + j)) by
      congr 2; omega_using []]
    exact writeController_word17 _ _ _ (callValues_bound p) (12 + j) (by omega_using [hj])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> [rw [hw 0 (by decide)]; rw [hw 1 (by decide)]; rw [hw 2 (by decide)];
    rw [hw 3 (by decide)]; rw [hw 4 (by decide)]] <;>
    simp only [callValues, baseValues, ctxValues, List.cons_append, List.nil_append, controllerValue,
      List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false]

theorem callSp_toNat {p : KeyPublic} (hf : 192 ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 192 := by
  rw [callSp_eq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hf])]
  simp only [BitVec.toNat_ofNat]

/-- What an attempt at `used` leaves: its status, and the key pair for 1,
zeros otherwise. -/
def AttemptPost (p : KeyPublic) (rand : List Byte) (used : Nat) (t : State) : Prop :=
  let st := attemptStatus .cached p.a p.len (rand.drop used)
  let x := Spec.Ffdh.vettedScalarOfOctets p.a ((rand.drop used).take p.len)
  ((t.gpr .r3).setWidth 32).toNat = st ∧
    if st = 1 then
      Spec.Rsa.bytesAt t.mem p.xp p.len = Spec.Rsa.i2osp x p.len ∧
        Spec.Rsa.bytesAt t.mem p.yp p.len = Spec.Rsa.i2osp (Spec.Rsa.powMod p.a.g x p.a.p) p.len
    else Spec.Rsa.bytesAt t.mem p.xp p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt t.mem p.yp p.len = List.replicate p.len 0

section

variable {p : KeyPublic} {original s : State} {used keys scalars : Nat}

theorem call_covers_writes (h : KeyLive p original used keys scalars s) {u : State}
    (hw : u.wr = (allocated 144 s).wr) : Covers (callWr p) u.wr := by
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
    {u : State} (hrd : u.rd = (allocated 144 s).rd) (hw : u.wr = (allocated 144 s).wr) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  obtain ⟨-, -, hrd', -⟩ := hi.1
  obtain e0 : s.sp - BitVec.ofNat 64 144 = callSp p := by rw [h.sp]
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
  · refine ⟨inContext original, ?_, 0, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inContext original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; simp only [BitVec.add_zero]; rfl
    · cases hi.2; simp only [Nat.zero_add]; exact Nat.le_refl _
  · refine ⟨frameR 144 s, ?_, 64, ?_, by show 64 + 40 ≤ 144 - 32; decide⟩
    · rw [hw]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · show callSp p + BitVec.ofNat 64 96 = s.sp - BitVec.ofNat 64 144 + 32 + BitVec.ofNat 64 64
      rw [e0, BitVec.add_assoc]; rfl

/-- What the attempt writes, as the controller sees it. -/
theorem attempt_frame (h : KeyLive p original used keys scalars s) {u t : State} {d : Nat}
    (hm : u.mem = writeController (allocated 144 s).mem (callSp p) (callValues p))
    (hf : Frame (callWr p ++ [below u.sp d]) u.mem t.mem) (hd : d = 0) :
    Frame (KeyInput.callChanges original) s.mem t.mem := by
  have hi := h.input
  have hsp : p.sp = original.sp := hi.sp_eq
  obtain h1 : Frame (KeyInput.callChanges original) (allocated 144 s).mem u.mem := by
    rw [hm]
    apply (writeController_frame_size _ _ (callValues p) (size := 144) (by decide) (by
      simp only [callValues, baseValues, ctxValues, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨below original.sp stackUse, by simp [KeyInput.callChanges], ?_⟩
    rw [← hsp, callSp_eq]
    exact Offset.sub_below p.sp (a := 192) (b := 192) (by decide) (by decide)
  obtain h2 : Frame (KeyInput.callChanges original) u.mem t.mem := by
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
    (hm : u.mem = writeController (allocated 144 s).mem (callSp p) (callValues p)) (hu : u.sp = callSp p)
    (ha : KeyArgs p used u) :
    Spec.Rsa.bytesAt (callState p used u).mem ((callState p used u).gpr .r7)
        ((callState p used u).gpr .r8).toNat = p.dom ∧
      Spec.Rsa.bytesAt (callState p used u).mem ((callState p used u).gpr .r10)
        (stackArg (callState p used u) 0).toNat = ((keyRand original).drop used).take p.len ∧
      ((callState p used u).gpr .r9).toNat = p.len := by
  obtain hfr : Frame (KeyInput.changes original) s.mem u.mem :=
    frame_of_callChanges original (attempt_frame (t := u) (d := 0) h hm (by
      intro x _; rfl) rfl)
  obtain ⟨h0, -, -, -, -⟩ := call_args hu hm
  obtain hlen : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  obtain hdl : (BitVec.ofNat 64 p.dlen).toNat = p.dlen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64]
  refine ⟨?_, ?_, by rw [call_gpr (by decide), ha.2.2.2.2.2.2.1, hlen]⟩
  · simp only [call_gpr (by decide : Reg.r7 ∉ linkRegs), call_gpr (by decide : Reg.r8 ∉ linkRegs),
      ha.2.2.2.2.1, ha.2.2.2.2.2.1, hdl, State.withRegions_mem, State.callEntry_mem]
    exact (h.input.domain_frame hfr).trans h.domain
  · simp only [call_gpr (by decide : Reg.r10 ∉ linkRegs), call_stackArg, ha.2.2.2.2.2.2.2, h0, hlen,
      State.withRegions_mem, State.callEntry_mem]
    obtain hr := (h.input.random_frame hfr).trans h.random
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
    obtain size := h.nowrap (r := inContext s) (by simp [inReads])
    change (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64 at size
    exact Offset.contains_base _ (by omega_using [inside]) (by omega_using [inside, size])
  · exact h.read_disjoint (by simp [inReads])
  · decide

/-- The context of a loop state is the one the precompute writes. -/
theorem KeyLive.context_canonical (h : KeyLive p original used keys scalars s) :
    p.ctxLen = Spec.Ffdh.generationPrecomputedWords p.len ∧
      Spec.Ffdh.generationPrecompute p.len p.dom = some (Spec.Rsa.wordsAt s.mem p.ctx p.ctxLen) := by
  rw [h.input.context_frame h.frame, ← h.input.2]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, count, canonical⟩ := h.input.1
  exact ⟨count, canonical⟩

theorem call_attempt_pre (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hf : CallFacts p used) {u : State} (hu : u.sp = callSp p) (ha : KeyArgs p used u)
    (hm : u.mem = writeController (allocated 144 s).mem (callSp p) (callValues p)) :
    cgContract.pre (callState p used u) := by
  have hfr : Frame (KeyInput.changes original) s.mem u.mem :=
    frame_of_callChanges original (attempt_frame (t := u) (d := 0) h hm (by intro x _; rfl) rfl)
  have inputs := call_inputs h hroom hf hm hu ha
  obtain ⟨h0, h1, h2, h3, h4⟩ := call_args hu hm
  obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have hdl : (BitVec.ofNat 64 p.dlen).toNat = p.dlen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64]
  have hzw : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.ns; omega_using [this])]
  have cx : (⟨p.ctx, p.ctxLen * 8⟩ : Region) = inContext original := by rw [← h.input.2]; rfl
  have xx : rX p = inX original := h.input.x_eq.symm
  have yy : rY p = inY original := h.input.y_eq.symm
  have ss : rS p = inScr original := by rw [← h.input.2]; rfl
  have nc : p.ctx.toNat + p.ctxLen * 8 ≤ 2 ^ 64 := by
    have n := h.input.nowrap (r := inContext original) (by simp [inReads]); rw [← cx] at n; exact n
  have hcl : (BitVec.ofNat 64 p.ctxLen).toNat = p.ctxLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [nc])]
  have xc : (rX p).Disjoint ⟨p.ctx, p.ctxLen * 8⟩ := by
    rw [xx, cx]; exact h.input.write_disjoint (by simp [inWrites]) (by simp [inReads])
  have yc : (rY p).Disjoint ⟨p.ctx, p.ctxLen * 8⟩ := by
    rw [yy, cx]; exact h.input.write_disjoint (by simp [inWrites]) (by simp [inReads])
  have sc : (rS p).Disjoint ⟨p.ctx, p.ctxLen * 8⟩ := by
    rw [ss, cx]; exact h.input.write_disjoint (by simp [inWrites]) (by simp [inReads])
  have canonical := h.context_canonical
  have hdom : Spec.Rsa.bytesAt u.mem p.dp p.dlen = p.dom := (h.input.domain_frame hfr).trans h.domain
  have hsp := callSp_toNat hf.room
  have hlt := p.sp.isLt
  have hsa : stackArgAddr (callState p used u) 0 = callSp p + BitVec.ofNat 64 96 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hu]
  show _ ∧ _
  simp only [cgStack, cgDom, call_gpr (by decide : Reg.r3 ∉ linkRegs), call_gpr (by decide : Reg.r4 ∉ linkRegs),
    call_gpr (by decide : Reg.r5 ∉ linkRegs), call_gpr (by decide : Reg.r6 ∉ linkRegs),
    call_gpr (by decide : Reg.r7 ∉ linkRegs), call_gpr (by decide : Reg.r8 ∉ linkRegs),
    call_gpr (by decide : Reg.r9 ∉ linkRegs), call_gpr (by decide : Reg.r10 ∉ linkRegs),
    call_stackArg, hsa, h0, h1, h2, h3, h4, r3, r4, r5, r6, r7, r8, r9, r10, hlen, hdl, hzw, hcl, hf.z8,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, hu,
    State.withRegions_mem, State.callEntry_mem, hdom]
  exact ⟨by omega_using [hsp], rfl, rfl, hf.xy, hf.xd, hf.xr, hf.xs, xc, hf.xa, hf.yd, hf.yr, hf.ys, yc, hf.ya, hf.ds,
    hf.rs, sc, hf.sa, hf.nx, hf.ny, hf.nd, hf.nr, hf.ns, nc, hf.len, hf.dlen, trivial, trivial, trivial,
    hf.scratch, h.input.domain_valid, canonical.1, by rw [h.input.context_frame hfr]; exact canonical.2⟩

theorem key_attempt_run (a : Attempt) (h : KeyLive p original used keys scalars s)
    (hroom : used + p.len ≤ p.randLen) :
    WP isa (attemptRun a.call) s fun t =>
      KeyLive p original used keys scalars t ∧ AttemptPost p (keyRand original) used t := by
  obtain hf := h.callFacts hroom
  obtain e0 : s.sp - BitVec.ofNat 64 144 = callSp p := by rw [h.sp]
  obtain hroom' : 144 ≤ s.sp.toNat := by
    have := hf.room
    obtain h48 : (p.sp - 48).toNat = p.sp.toNat - 48 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; show 48 ≤ _; omega_using [this])]; rfl
    rw [h.sp, h48]
    omega_using [this]
  unfold attemptRun
  refine WP.alloc (by decide) hroom' ?_
  refine WP.seq (WP.mono (key_arguments_ok h) fun u ⟨⟨ha, hm⟩, k⟩ => ?_)
  obtain hu : u.sp = callSp p := k.sp.trans e0
  refine WP.callAny (k := cgContract) a.correct (call_attempt_pre h hroom hf hu ha hm)
    (call_covers_reads h hroom k.rd k.wr) (call_covers_writes h k.wr) ?_ (by rw [a.stack]; decide)
  intro t hrd hwr hsp hfr hcs hpost mL _ fl
  -- Whatever the released frame's bytes hold: the outputs lie apart from it.
  rw [e0] at fl
  obtain hC : Region.Sub ⟨callSp p, 144⟩ (below original.sp stackUse) := by
    rw [callSp_eq, ← h.input.sp_eq]; exact Offset.sub_below _ (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · -- The loop state, after the frame.
    refine h.restore ?_ ?_ ?_ ?_ ?_
    · exact hrd.trans k.rd
    · change t.wr.tail = s.wr; rw [hwr, k.wr]; rfl
    · change t.sp + BitVec.ofNat 64 144 = s.sp
      rw [hsp, k.sp]
      exact BitVec.sub_add_cancel _ _
    · intro r hr
      exact (hcs r hr).trans (k.gpr r (by revert r hr; decide))
    · exact (attempt_frame h hm hfr a.stack).trans (fl.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, by simp [KeyInput.callChanges], hC⟩)
  · -- The attempt's status and outputs.
    obtain ⟨hdom, hrand, h9⟩ := call_inputs h hroom hf hm hu ha
    have hp := hpost
    simp only [cgContract, cgScalar, cgA, cgDom, hdom, hrand, h9] at hp
    obtain ⟨hst, hout⟩ := hp
    simp only [call_gpr (by decide : Reg.r3 ∉ linkRegs), call_gpr (by decide : Reg.r5 ∉ linkRegs),
      ha.1, ha.2.2.1, State.withRegions_gpr, State.withRegions_mem] at hst hout
    obtain hbx : Spec.Rsa.bytesAt mL p.xp p.len = Spec.Rsa.bytesAt t.mem p.xp p.len :=
      List.map_congr_left fun i hi => lost_byte fl (R := rX p) hf.xC (List.mem_range.mp hi)
    obtain hby : Spec.Rsa.bytesAt mL p.yp p.len = Spec.Rsa.bytesAt t.mem p.yp p.len :=
      List.map_congr_left fun i hi => lost_byte fl (R := rY p) hf.yC (List.mem_range.mp hi)
    unfold AttemptPost
    refine ⟨hst, ?_⟩
    dsimp only
    rw [hbx, hby]
    exact hout

end

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

end

end

/-! ### `Ffdh.PPC64LE.Cached.SearchProof.Guards`, which this module and modules that import it used -/

section

/-! # The key-generation controller's tests of its budgets, tape and status (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.PPC64LE.Generation (CtlAccess sign_sub status_guard)
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search (ldf stf entry arguments terminal zeroOut zeroOutputs exhausted advance
  rejectedScalar rejectedPublic test classify request room finish)
open VG.Impl.Ffdh.PPC64LE.Cached.Search

/-- A budget, at the controller's word `j`, compared with zero. -/
theorem budget_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {j n : Nat} (hj : j = 0 ∨ j = 1)
    (hv : (j, BitVec.ofNat 64 n) ∈ p.headers used keys scalars) (hn : n ≤ 128) :
    WP isa (.block [ldf .r9 j]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .d .r9) t = some (decide (n = 0)) := by
  have a := h.access
  have hw := h.header hv
  simp only [Bignum.word, off] at hw
  rcases hj with rfl | rfl <;> simp only [Nat.reduceMul, Nat.mul_zero, BitVec.add_zero] at hw <;>
  · refine WP.mono (WP.keep [.r9] (Q := fun t =>
      isa.eval (.zero .d .r9) t = some (decide (n = 0)) ∧ t.mem = s.mem) ?_ (by decide))
      fun _ ⟨⟨he, hm⟩, k⟩ => ⟨h.keep k hm, he⟩
    prun [ldf, h.r31, hw, a.ld 0 (by decide), a.ld 8 (by decide), a.ld0, BitVec.add_zero]
    refine (eval_zero _ _).trans ?_
    rw [RegUpd.gpr_write_self, ofNat_beq_zero (show n < 2 ^ 64 by omega_using [hn])]

theorem keys_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .r9 0]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .d .r9) t = some (decide (keys = 0)) :=
  budget_guard h (j := 0) (.inl rfl) (by simp [KeyPublic.headers]) h.keys_le

theorem scalars_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .r9 1]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .d .r9) t = some (decide (scalars = 0)) :=
  budget_guard h (j := 1) (.inr rfl) (by simp [KeyPublic.headers]) h.scalars_le

/-- `room`'s bit: the sign of `a − l`, cleared when `a`'s top bit is set. -/
theorem room_bit {a l : Nat} (ha : a < 2 ^ 64) (hl : l < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63 ^^^
      (BitVec.ofNat 64 a >>> 63 &&& (BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63) =
      BitVec.ofNat 64 (if a < l then 1 else 0) := by
  by_cases h : a < 2 ^ 63
  · have ht : BitVec.ofNat 64 a >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega_using [h]
    rw [ht, sign_sub h hl, BitVec.zero_and, BitVec.xor_zero]
  · have ht : BitVec.ofNat 64 a >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega_using [ha, h]
    have hd : (BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63 = 0#64 ∨
        (BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63 = 1#64 := by
      have : ((BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63).toNat < 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have := (BitVec.ofNat 64 a - BitVec.ofNat 64 l).isLt
        omega_using []
      rcases (by omega_using [this] : ((BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63).toNat = 0 ∨
          ((BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63).toNat = 1) with h0 | h1
      · exact .inl (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
      · exact .inr (BitVec.eq_of_toNat_eq (by rw [h1]; rfl))
    have hn : ¬a < l := by omega_using [hl, h]
    simp only [ht, hn, ↓reduceIte]
    rcases hd with hd | hd <;> rw [hd] <;> decide

/-- Whether the tape holds an attempt: `r12` is zero exactly then. -/
theorem room_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block room) s fun t =>
      KeyLive p original used keys scalars t ∧
        isa.eval (.zero .d .r12) t = some (decide (p.len ≤ p.randLen - used)) := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv10 := h.header (j := 10) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv10
  have hr : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
  have hk : p.len < 2 ^ 63 := by have := h.input.len_lt; omega_using [this]
  have hb := room_bit (a := p.randLen - used) (show p.randLen - used < 2 ^ 64 by omega_using [hr]) hk
  refine WP.mono (WP.keep [.r9, .r10, .r11, .r12] (Q := fun t =>
    isa.eval (.zero .d .r12) t = some (decide (p.len ≤ p.randLen - used)) ∧ t.mem = s.mem) ?_
    (by decide)) fun _ ⟨⟨he, hm⟩, k⟩ => ⟨h.keep k hm, he⟩
  unfold room
  prun [ldf, h.r31, hv2, hv10, a.ld 16 (by decide), a.ld 80 (by decide), hb]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self]
  by_cases hs : p.randLen - used < p.len
  · simp only [hs, ↓reduceIte, show ¬p.len ≤ p.randLen - used by omega_using [hs], decide_false]
    decide
  · simp only [hs, ↓reduceIte, show p.len ≤ p.randLen - used by omega_using [hs], decide_true]
    decide

theorem key_status_lt (r : Spec.Ffdh.KeySearchResult) : r.status < 5 := by
  unfold Spec.Ffdh.KeySearchResult.status; split <;> decide

theorem key_status_ne (r : Spec.Ffdh.KeySearchResult) : r.status ≠ 4 := by
  unfold Spec.Ffdh.KeySearchResult.status; split <;> decide

theorem done_loop_guard {p : KeyPublic} {original s : State} {r : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) :
    WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) s fun t =>
      isa.eval (.zero .d .r9) t = some false ∧ KeyDone p original r t := by
  have a := CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)
  refine WP.mono (status_guard a h.r31 h.status (key_status_lt r)) fun t ⟨⟨he, hm⟩, k⟩ =>
    ⟨?_, h.keep k hm⟩
  rw [he, decide_eq_false (key_status_ne r)]

theorem live_loop_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) s fun t =>
      isa.eval (.zero .d .r9) t = some true ∧ KeyLive p original used keys scalars t :=
  WP.mono (status_guard (st := 4) h.access h.r31 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨he, h.keep k hm⟩

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

end

end

/-! # The cached key-generation controller's attempts' outcomes, and its loop (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.GenerationSearch
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search (ldf stf entry arguments terminal zeroOut zeroOutputs exhausted advance
  rejectedScalar rejectedPublic test classify request room finish)
open VG.Impl.Ffdh.PPC64LE.Cached.Search
open VG.Proof.Ffdh.PPC64LE.Generation (Slots low32)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)

/-! ## After an attempt: the key, or one fewer scalar or key -/

/-- The status `r9` minus `k`, compared with zero. -/
theorem test_ok {s : State} {st k : Nat} (h9 : s.gpr .r9 = BitVec.ofNat 64 st) (hst : st < 4)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    WP isa (.block (test k)) s fun t =>
      (isa.eval (.zero .d .r10) t = some (decide (st = k)) ∧ t.mem = s.mem) ∧ Keep [.r10] s t := by
  have hb : ∀ st < 4, ∀ k < 4,
      ((BitVec.ofNat 64 st - BitVec.ofNat 64 k) == 0) = decide (st = k) := by decide
  rcases hk with rfl | rfl | rfl <;>
  · refine WP.keep [.r10] ?_ (by decide)
    unfold test
    prun [h9]
    refine (eval_zero _ _).trans ?_
    rw [RegUpd.gpr_write_self, hb st hst _ (by decide)]

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
        t.gpr .r9 = (s.gpr .r3 <<< 32) >>> 32) ∧
        Keep [.r3, .r4, .r9, .r11, .r12] s t := by
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
  refine WP.keep [.r3, .r4, .r9, .r11, .r12] ?_ (by decide)
  unfold advance writeController advanceValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [ldf, stf, h.r31, hv2, hv9, hv10, hv11,
    a.ld 16 (by decide), a.ld 72 (by decide), a.ld 80 (by decide), a.ld 88 (by decide),
    a.st 72 (by decide), a.st 80 (by decide), a.st 88 (by decide), e9, e10, e11]

/-- The status, normalized, and the attempt's octets consumed. -/
theorem key_classify_head {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hp : AttemptPost p (keyRand original) used s) :
    WP isa (.block (advance ++ test 1)) s fun t =>
      KeyLive p original (used + p.len) keys scalars t ∧ AttemptOut p (keyRand original) used t.mem ∧
      t.gpr .r9 = BitVec.ofNat 64 (attemptStatus .cached p.a p.len ((keyRand original).drop used)) ∧
      isa.eval (.zero .d .r10) t =
        some (decide (attemptStatus .cached p.a p.len ((keyRand original).drop used) = 1)) := by
  have hst : attemptStatus .cached p.a p.len ((keyRand original).drop used) < 4 := by
    rcases attemptStatus_cases (policy := .cached) p.a p.len ((keyRand original).drop used) with he | he | he <;> omega_using [he]
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
  have hpv : AttemptOut p (keyRand original) used v.mem :=
    AttemptOut.frame h.input (by unfold AttemptOut; exact hp.2)
      (hmv ▸ writeController_frame s.mem p.control _ hb)
  have h9' : v.gpr .r9 = BitVec.ofNat 64 (attemptStatus .cached p.a p.len ((keyRand original).drop used)) :=
    h9.trans (low32 hp.1)
  refine WP.mono (test_ok h9' hst (.inl rfl)) fun t ⟨⟨he, hmt⟩, kt⟩ => ?_
  exact ⟨hv.keep kt hmt, hmt ▸ hpv, (kt.gpr .r9 (by decide)).trans h9', he⟩

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
    refine WP.seq (WP.mono (test_ok ((kv.gpr .r9 (by decide)).trans hax) (by decide) (.inr (.inr rfl)))
      fun w ⟨⟨he3, hmw⟩, kw⟩ => ?_)
    have hw := hv.keep kw hmw
    refine WP.ite true he3 (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_rejected_public hw hk) fun t ht => ?_
    dsimp only [KeyClassified]
    rw [ite_eq_right (by rw [h3]; decide), ite_eq_right (by rw [h3]; decide)]
    exact ht

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
      (isa.eval (.zero .d .r9) t = some false ∧ KeyDone p original expected t) ∨
      (isa.eval (.zero .d .r9) t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) := by
  obtain ⟨used, keys, scalars, hn, h, ho, hu⟩ := h
  have hlen := h.rand_length
  have done : ∀ (r : Spec.Ffdh.KeySearchResult) t, KeyDone p original r t →
      r.outcome = (p.tail (keyRand original) used keys scalars).outcome →
      r.used = (p.tail (keyRand original) used keys scalars).used →
      WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) t fun t =>
        (isa.eval (.zero .d .r9) t = some false ∧ KeyDone p original expected t) ∨
        (isa.eval (.zero .d .r9) t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) :=
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
  swap
  · intro hshort
    have hr : (keyRand original).length - used < p.len := by
      rw [hlen]; have := of_decide_eq_false hshort; omega_using [this]
    refine WP.mono (key_request hu3) fun t ht => done _ t ht ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_short hk hs hr]
  intro hlong
  have hroom : used + p.len ≤ p.randLen := by
    have := of_decide_eq_true hlong; have := h.used_le; omega_arith
  have hr : p.len ≤ (keyRand original).length - used := by rw [hlen]; omega_using [hroom]
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
    {expected : Spec.Ffdh.KeySearchResult} {n : Nat}
    (h : KeyInvariant p original expected n s) :
    WP isa (.loop (iteration a.call) (.zero .d .r9)) s (KeyDone p original expected) :=
  WP.loop (M := isa) (body := iteration a.call) (c := .zero .d .r9)
    (Q := KeyDone p original expected) (KeyInvariant p original expected)
    (fun _ _ h => key_iteration a h) n s h

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof
