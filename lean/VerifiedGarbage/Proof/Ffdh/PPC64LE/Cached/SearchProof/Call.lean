module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Cached
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Data
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Outputs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Entry

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

private theorem sub_tape {r : Addr} {n used len : Nat}
    (hu : used + len ≤ n) : Region.Sub ⟨r + BitVec.ofNat 64 used, len⟩ ⟨r, n⟩ :=
  Offset.sub_base r hu

private theorem nowrap_tape {r : Addr} {n used len : Nat} (hn : r.toNat + n ≤ 2 ^ 64)
    (hu : used + len ≤ n) : (r + BitVec.ofNat 64 used).toNat + len ≤ 2 ^ 64 := by
  have hul : used < 2 ^ 64 ∨ len = 0 := by omega
  rcases hul with hul | hz
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
    have := Nat.mod_le (r.toNat + used) (2 ^ 64)
    by_cases hz : r.toNat + used < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hz]; omega
    · omega
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
    have he := hvalues e (List.mem_cons_self ..)
    change word (writeController (m.writeW (off B (8 * e.1)) e.2) B values) B (8 * j) = _
    rw [ih _ (fun x hx => hvalues x (List.mem_cons_of_mem _ hx))]
    refine congrArg (controllerValue values j) ?_
    change _ = if j = e.1 then e.2 else word m B (8 * j)
    by_cases hje : j = e.1
    · subst hje; rw [ite_eq_left rfl]; exact word_writeW_self _ _ _ _
    · rw [ite_eq_right hje]; exact hdrStore_hdr _ _ _ (by omega) (by omega) (Ne.symm hje)

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
  have hc := h.input.control_frame (alloc_frame h)
  have e0 : s.sp - BitVec.ofNat 64 144 = callSp p := by rw [h.sp]
  have hw : ∀ e, e + 8 ≤ 112 → InRegions (allocated 144 s).wr (callSp p + 32 + BitVec.ofNat 64 e) 8 := by
    intro e he
    refine ⟨frameR 144 s, List.mem_cons_self .., ?_⟩
    simp only [frameR, e0]
    exact Offset.contains_base _ he (by omega)
  have hl : ∀ d, d + 8 ≤ 128 →
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
  have hwo : ∀ e, e + 8 ≤ 112 → InRegions (allocated 144 s).wr (Mont.off (callSp p) (32 + e)) 8 := by
    intro e he
    have := hw e he
    rwa [BitVec.add_assoc, show (32 : Addr) + BitVec.ofNat 64 e = BitVec.ofNat 64 (32 + e) by
      rw [BitVec.ofNat_add]; rfl] at this
  have hw96 := hwo 64 (by decide)
  have hw104 := hwo 72 (by decide)
  have hw112 := hwo 80 (by decide)
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
  have hbase : ∀ e ∈ baseValues p, 8 * e.1 + 8 ≤ 144 := by
    simp only [baseValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide
  have hfu : Frame (KeyInput.changes original) original.mem u.mem := by
    rw [hm]; exact h.frame.trans (frame_of_callChanges original (base_frame h hbase))
  have e0 : s.sp - BitVec.ofNat 64 144 = callSp p := by rw [h.sp]
  have eA : callSp p + BitVec.ofNat 64 328 = original.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * 5) := by
    rw [callSp_eq, hsp0]; bv_omega
  have eB : callSp p + BitVec.ofNat 64 336 = original.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * 6) := by
    rw [callSp_eq, hsp0]; bv_omega
  have eC : callSp p + BitVec.ofNat 64 120 = s.sp - BitVec.ofNat 64 144 + 32 + BitVec.ofNat 64 88 := by
    rw [e0]; bv_omega
  have eD : callSp p + BitVec.ofNat 64 128 = s.sp - BitVec.ofNat 64 144 + 32 + BitVec.ofNat 64 96 := by
    rw [e0]; bv_omega
  have rA : InRegions (u.rd ++ u.wr) (callSp p + BitVec.ofNat 64 328) 8 := by
    obtain ⟨r, hr, hc⟩ := hi.arg_in 5 (by decide)
    rw [eA]; exact ⟨r, List.mem_append_left _ (by rw [hrd, h.rd]; exact hr), hc⟩
  have rB : InRegions (u.rd ++ u.wr) (callSp p + BitVec.ofNat 64 336) 8 := by
    obtain ⟨r, hr, hc⟩ := hi.arg_in 6 (by decide)
    rw [eB]; exact ⟨r, List.mem_append_left _ (by rw [hrd, h.rd]; exact hr), hc⟩
  have wC : InRegions u.wr (callSp p + BitVec.ofNat 64 120) 8 := by
    refine ⟨frameR 144 s, by rw [hwr]; exact List.mem_cons_self .., ?_⟩
    rw [eC]; exact Offset.contains_base _ (by decide) (by decide)
  have wD : InRegions u.wr (callSp p + BitVec.ofNat 64 128) 8 := by
    refine ⟨frameR 144 s, by rw [hwr]; exact List.mem_cons_self .., ?_⟩
    rw [eD]; exact Offset.contains_base _ (by decide) (by decide)
  have vA : u.mem.readW (callSp p + BitVec.ofNat 64 328) 64 = p.ctx := by
    rw [eA, hi.arg_frame hfu 5 (by decide)]
    exact congrArg KeyPublic.ctx hi.2
  have hC : (below original.sp stackUse).Contains (callSp p + BitVec.ofNat 64 120) (64 / 8) := by
    rw [show callSp p + BitVec.ofNat 64 120 = original.sp - BitVec.ofNat 64 72 by
      rw [callSp_eq, hsp0]; bv_omega]
    exact Offset.contains_below original.sp (a := 72) (b := 192) (by decide) (by decide) (by decide)
  have vB : (u.mem.writeW (callSp p + BitVec.ofNat 64 120) p.ctx).readW
      (callSp p + BitVec.ofNat 64 336) 64 = BitVec.ofNat 64 p.ctxLen := by
    rw [eB, hi.arg_frame (hfu.writeW (r := below original.sp stackUse) (by simp [KeyInput.changes]) p.ctx hC)
      6 (by decide)]
    have hc := congrArg KeyPublic.ctxLen hi.2
    change (stackArg original 6).toNat = p.ctxLen at hc
    rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have ea : ∀ t : State, exec (.addSp .r12 328) t = some (t.write .r12 (t.sp + BitVec.ofNat 64 328)) := by
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
  have e0 : s.sp - BitVec.ofNat 64 144 = callSp p := by rw [h.sp]
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
      congr 2; omega]
    exact writeController_word17 _ _ _ (callValues_bound p) (12 + j) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> [rw [hw 0 (by decide)]; rw [hw 1 (by decide)]; rw [hw 2 (by decide)];
    rw [hw 3 (by decide)]; rw [hw 4 (by decide)]] <;>
    simp only [callValues, baseValues, ctxValues, List.cons_append, List.nil_append, controllerValue,
      List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false]

theorem callSp_toNat {p : KeyPublic} (hf : 192 ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 192 := by
  rw [callSp_eq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
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

theorem AttemptPost.keep {p : KeyPublic} {rand : List Byte} {used : Nat} {s t : State}
    (h : AttemptPost p rand used s) (hm : t.mem = s.mem)
    (hr : (t.gpr .r3).setWidth 32 = (s.gpr .r3).setWidth 32) : AttemptPost p rand used t := by
  unfold AttemptPost at h ⊢
  rw [hm, hr]
  exact h

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
  have e0 : s.sp - BitVec.ofNat 64 144 = callSp p := by rw [h.sp]
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
  have h1 : Frame (KeyInput.callChanges original) (allocated 144 s).mem u.mem := by
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
    (hm : u.mem = writeController (allocated 144 s).mem (callSp p) (callValues p)) (hu : u.sp = callSp p)
    (ha : KeyArgs p used u) :
    Spec.Rsa.bytesAt (callState p used u).mem ((callState p used u).gpr .r7)
        ((callState p used u).gpr .r8).toNat = p.dom ∧
      Spec.Rsa.bytesAt (callState p used u).mem ((callState p used u).gpr .r10)
        (stackArg (callState p used u) 0).toNat = ((keyRand original).drop used).take p.len ∧
      ((callState p used u).gpr .r9).toNat = p.len := by
  have hfr : Frame (KeyInput.changes original) s.mem u.mem :=
    frame_of_callChanges original (attempt_frame (t := u) (d := 0) h hm (by
      intro x _; rfl) rfl)
  obtain ⟨h0, -, -, -, -⟩ := call_args hu hm
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
  exact ⟨by omega, rfl, rfl, hf.xy, hf.xd, hf.xr, hf.xs, xc, hf.xa, hf.yd, hf.yr, hf.ys, yc, hf.ya, hf.ds,
    hf.rs, sc, hf.sa, hf.nx, hf.ny, hf.nd, hf.nr, hf.ns, nc, hf.len, hf.dlen, trivial, trivial, trivial,
    hf.scratch, h.input.domain_valid, canonical.1, by rw [h.input.context_frame hfr]; exact canonical.2⟩

theorem key_attempt_run (a : Attempt) (h : KeyLive p original used keys scalars s)
    (hroom : used + p.len ≤ p.randLen) :
    WP isa (attemptRun a.call) s fun t =>
      KeyLive p original used keys scalars t ∧ AttemptPost p (keyRand original) used t := by
  have hf := h.callFacts hroom
  have e0 : s.sp - BitVec.ofNat 64 144 = callSp p := by rw [h.sp]
  have hroom' : 144 ≤ s.sp.toNat := by
    have := hf.room
    have h48 : (p.sp - 48).toNat = p.sp.toNat - 48 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; show 48 ≤ _; omega)]; rfl
    rw [h.sp, h48]
    omega
  unfold attemptRun
  refine WP.alloc (by decide) hroom' ?_
  refine WP.seq (WP.mono (key_arguments_ok h) fun u ⟨⟨ha, hm⟩, k⟩ => ?_)
  have hu : u.sp = callSp p := k.sp.trans e0
  refine WP.callAny (k := cgContract) a.correct (call_attempt_pre h hroom hf hu ha hm)
    (call_covers_reads h hroom k.rd k.wr) (call_covers_writes h k.wr) ?_ (by rw [a.stack]; decide)
  intro t hrd hwr hsp hfr hcs hpost
  refine ⟨?_, ?_⟩
  · -- The loop state, after the frame.
    apply h.restore (show (freed 144 t).rd = s.rd from hrd.trans k.rd)
      (show (freed 144 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.wr]; rfl)
    · change t.sp + BitVec.ofNat 64 144 = s.sp
      rw [hsp, k.sp]
      exact BitVec.sub_add_cancel _ _
    · intro r hr
      exact (hcs r hr).trans (k.gpr r (by revert r hr; decide))
    · exact attempt_frame h hm hfr a.stack
  · -- The attempt's status and outputs.
    obtain ⟨hdom, hrand, h9⟩ := call_inputs h hroom hf hm hu ha
    have hp := hpost
    simp only [cgContract, cgScalar, cgA, cgDom, hdom, hrand, h9] at hp
    obtain ⟨hst, hout⟩ := hp
    simp only [call_gpr (by decide : Reg.r3 ∉ linkRegs), call_gpr (by decide : Reg.r5 ∉ linkRegs),
      ha.1, ha.2.2.1, State.withRegions_gpr, State.withRegions_mem] at hst hout
    unfold AttemptPost
    exact ⟨hst, hout⟩

end

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof
