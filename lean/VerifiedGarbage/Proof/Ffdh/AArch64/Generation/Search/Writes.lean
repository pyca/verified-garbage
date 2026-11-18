module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Live
public import VerifiedGarbage.Impl.Ffdh.AArch64.Generation.Search
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Data
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! ### `Ffdh.AArch64.Generation.Search.Call`, which the modules that import this one used -/

section

/-! # One candidate of the parameter search (AArch64)

In its frame, the controller passes `vg_ffdh_parameter_candidate_sieved` the rest
of the tape. The candidate's buffers are the controller's (`out`, `used`,
the tape's rest and the working space), and its stack argument is in the
candidate's frame, in the 32 bytes of stack below the controller's stack
pointer on entry, which no buffer overlaps. The candidate keeps the
controller's state, and leaves its status, p or zeros at `out`, and the
octets it read at `used`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame_size
  controllerValue)
open VG.Proof.Ffdh.AArch64.ParameterCandidate (pcPre pcPost pcResult pcRand)
open VG.Impl.Ffdh.AArch64.Generation.Search

/-- The stack pointer in the candidate's frame. -/
abbrev callSp (p : SPub) : Addr := p.sp - 16 - BitVec.ofNat 64 16

theorem callSp_eq (p : SPub) : callSp p = p.sp - BitVec.ofNat 64 32 := by
  rw [callSp, BitVec.sub_sub]; rfl

/-- The candidate's regions: `out`, `used`, the tape's rest, the working
space and its argument. -/
abbrev rO (p : SPub) : Region := ⟨p.op, p.len⟩
abbrev rU (p : SPub) : Region := ⟨p.up, 8⟩
abbrev rR (p : SPub) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.randLen - used⟩
abbrev rS (p : SPub) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : SPub) : Region := ⟨callSp p, 8⟩

structure CallFacts (p : SPub) (used : Nat) : Prop where
  room : 32 ≤ p.sp.toNat
  ou : (rO p).Disjoint (rU p)
  or : (rO p).Disjoint (rR p used)
  os : (rO p).Disjoint (rS p)
  oa : (rO p).Disjoint (rA p)
  ur : (rU p).Disjoint (rR p used)
  us : (rU p).Disjoint (rS p)
  ua : (rU p).Disjoint (rA p)
  rs : (rR p used).Disjoint (rS p)
  sa : (rS p).Disjoint (rA p)
  no : p.op.toNat + p.len ≤ 2 ^ 64
  nu : p.up.toNat + 8 ≤ 2 ^ 64
  nr : (p.rp + BitVec.ofNat 64 used).toNat + (p.randLen - used) ≤ 2 ^ 64
  ns : p.B.toNat + p.Z ≤ 2 ^ 64
  bits : 512 ≤ p.bits ∧ p.bits ≤ 8192
  len : p.len = (p.bits + 7) / 8
  gen : p.gen = 2 ∨ p.gen = 5
  scratch : Spec.Rsa.scratchWords p.len ≤ p.Z / 8
  z8 : p.Z / 8 * 8 = p.Z
  randLen : p.randLen < 2 ^ 64

private theorem nowrap_tape {r : Addr} {n used len : Nat} (hn : r.toNat + n ≤ 2 ^ 64)
    (hu : used + len ≤ n) : (r + BitVec.ofNat 64 used).toNat + len ≤ 2 ^ 64 := by
  have hul : used < 2 ^ 64 ∨ len = 0 := by omega_arith
  rcases hul with hul | hz
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
    have := Nat.mod_le (r.toNat + used) (2 ^ 64)
    by_cases hz : r.toNat + used < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hz]; omega_arith
    · omega_arith
  · subst hz; simp only [Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _)

theorem rA_sub (p : SPub) : Region.Sub (rA p) (below p.sp stackUse) := by
  rw [rA, callSp_eq]; exact Offset.sub_below _ (by decide) (by decide)

theorem SLive.callFacts {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) : CallFacts p used := by
  have hi := h.input
  have hroom : used + (p.randLen - used) ≤ p.randLen := by have := h.used_le; omega_arith
  obtain ⟨_, hsp, _, _, hnw, hpw, hwr, hstk, hb1, hb2, hl, hg, hscr, -, -, -, -⟩ := hi.1
  cases hi.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pou, pos, -⟩, ⟨pus, -⟩, -⟩ := hpw
  obtain ⟨⟨wor, -⟩, ⟨wur, -⟩, ⟨wsr, -⟩, -⟩ := hwr
  obtain ⟨bo, bu, bs, -, br, -⟩ := hstk
  obtain ⟨no, nu, ns, -, nr, -⟩ := hnw
  have hR : Region.Sub (rR (sOfState original) used) (inRand original) :=
    Offset.sub_base _ hroom
  have hA := rA_sub (sOfState original)
  have hsp' : (sOfState original).sp = original.sp := rfl
  rw [hsp'] at hA
  refine ⟨by rw [hsp']; exact hsp, pou, wor.sub_right hR, pos, bo.symm.sub_right hA,
    wur.sub_right hR, pus, bu.symm.sub_right hA, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, no, nu, nowrap_tape nr hroom, ns, ⟨hb1, hb2⟩, hl, hg, ?_, ?_, BitVec.isLt _⟩
  · simp only [sOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [sOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]

/-- The output and `used` are apart from the stack the search uses. -/
theorem SInput.outStack {p : SPub} {original : State} (hi : SInput p original) :
    (rO p).Disjoint (below p.sp stackUse) ∧ (rU p).Disjoint (below p.sp stackUse) := by
  obtain ⟨_, _, _, _, _, _, _, hstk, _, _, _, _, _, -, -, -, -⟩ := hi.1
  cases hi.2
  simp only [inWrites, inReads, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append] at hstk
  obtain ⟨bo, bu, -⟩ := hstk
  exact ⟨bo.symm, bu.symm⟩

/-- The candidate's stack argument: `scratch_len`. -/
def callValues (p : SPub) : List (Nat × BitVec 64) := [(0, BitVec.ofNat 64 (p.Z / 8))]

theorem callValues_bound (p : SPub) : ∀ e ∈ callValues p, e.1 < 16 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ rfl; show 0 < 16; decide

/-- The candidate's register arguments. -/
def SArgs (p : SPub) (used : Nat) (t : State) : Prop :=
  t.gpr .x0 = p.op ∧ t.gpr .x1 = BitVec.ofNat 64 p.len ∧ t.gpr .x2 = p.up ∧
  t.gpr .x3 = BitVec.ofNat 64 p.bits ∧ t.gpr .x4 = BitVec.ofNat 64 p.gen ∧
  t.gpr .x5 = p.rp + BitVec.ofNat 64 used ∧ t.gpr .x6 = BitVec.ofNat 64 (p.randLen - used) ∧
  t.gpr .x7 = p.B

/-- The registers the arguments' block writes. -/
abbrev argRegsW : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x11]

theorem search_arguments_ok {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa (.block arguments) (allocated 16 s) fun u =>
      (SArgs p used u ∧ u.mem = writeController s.mem (callSp p) (callValues p)) ∧
      Keep argRegsW (allocated 16 s) u := by
  have a := h.access
  have hw0 : InRegions (⟨callSp p, 16⟩ :: s.wr) (callSp p) 8 :=
    ⟨⟨callSp p, 16⟩, List.mem_cons_self .., by
      simpa only [BitVec.add_zero] using Offset.contains_base (callSp p) (d := 0) (n := 8) (k := 16)
        (by decide) (by decide)⟩
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ ⟨callSp p, 16⟩ :: s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun d hd => by
      obtain ⟨r, hr, hc⟩ := a.ld d hd
      refine ⟨r, ?_, hc⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv5 := h.header (j := 5) (v := p.op) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  have hv7 := h.header (j := 7) (v := p.up) (by simp [SPub.headers])
  have hv8 := h.header (j := 8) (v := BitVec.ofNat 64 p.bits) (by simp [SPub.headers])
  have hv9 := h.header (j := 9) (v := BitVec.ofNat 64 p.gen) (by simp [SPub.headers])
  have hv10 := h.header (j := 10) (v := p.rp + BitVec.ofNat 64 used) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  have hv13 := h.header (j := 13) (v := p.B) (by simp [SPub.headers])
  have hv15 := h.header (j := 15) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv13 hv15
  refine WP.keep argRegsW ?_ (by decide) (by decide) (by decide +kernel)
  unfold arguments writeController callValues SArgs
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, allocated, h.sp, h.x19, exec_addSp (show 0 < 4096 by decide),
    hl 40 (by decide), hl 48 (by decide), hl 56 (by decide), hl 64 (by decide), hl 72 (by decide),
    hl 80 (by decide), hl 88 (by decide), hl 104 (by decide), hl 120 (by decide), hw0,
    hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv13, hv15]
  simp only [off, Nat.mul_zero, BitVec.add_zero]

/-- The regions the candidate reads: the tape's rest and its stack argument;
those it writes: `out`, `used` and the working space. -/
def callRd (p : SPub) (used : Nat) : List Region := [rR p used, rA p]
def callWr (p : SPub) : List Region := [rO p, rU p, rS p]

/-- The callee's entry, as the call makes it. -/
abbrev callState (p : SPub) (used : Nat) (u : State) : State :=
  u.callEntry.withRegions (callRd p used) (callWr p)

theorem call_gpr {p : SPub} {used : Nat} {u : State} {r : Reg} (hr : r ∉ linkRegs) :
    (callState p used u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem call_stackArg (p : SPub) (used : Nat) (u : State) (j : Nat) :
    stackArg (callState p used u) j = stackArg u j := rfl

theorem call_arg {p : SPub} {u : State} {m : Mem} (hu : u.sp = callSp p)
    (hm : u.mem = writeController m (callSp p) (callValues p)) :
    stackArg u 0 = BitVec.ofNat 64 (p.Z / 8) := by
  unfold stackArg stackArgAddr
  rw [hu, hm]
  exact writeController_word _ _ _ (callValues_bound p) 0 (by decide)

theorem callSp_toNat {p : SPub} (hf : 32 ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 32 := by
  rw [callSp_eq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith)]
  simp only [BitVec.toNat_ofNat]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem gen_setWidth {g : Nat} (h : g = 2 ∨ g = 5) : ((BitVec.ofNat 64 g).setWidth 32).toNat = g := by
  rcases h with rfl | rfl <;> decide

theorem call_candidate_pre {p : SPub} {used : Nat} {u : State} {m : Mem} (hf : CallFacts p used)
    (hu : u.sp = callSp p) (ha : SArgs p used u)
    (hm : u.mem = writeController m (callSp p) (callValues p)) :
    pcPre (callState p used u) := by
  have h0 := call_arg hu hm
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  have hb := hf.bits
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := toNat_ofNat_lt (by have := hf.len; omega_arith)
  have hbits : (BitVec.ofNat 64 p.bits).toNat = p.bits := toNat_ofNat_lt (by omega_arith)
  have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := hf.randLen; omega_arith)
  have hzw : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 :=
    toNat_ofNat_lt (by have := hf.ns; omega_arith)
  have hsp := callSp_toNat hf.room
  have hlt := p.sp.isLt
  unfold pcPre
  simp only [call_gpr (by decide : Reg.x0 ∉ linkRegs), call_gpr (by decide : Reg.x1 ∉ linkRegs),
    call_gpr (by decide : Reg.x2 ∉ linkRegs), call_gpr (by decide : Reg.x3 ∉ linkRegs),
    call_gpr (by decide : Reg.x4 ∉ linkRegs), call_gpr (by decide : Reg.x5 ∉ linkRegs),
    call_gpr (by decide : Reg.x6 ∉ linkRegs), call_gpr (by decide : Reg.x7 ∉ linkRegs),
    call_stackArg, h0, r0, r1, r2, r3, r4, r5, r6, r7, hlen, hbits, hrl, hzw, hf.z8,
    gen_setWidth hf.gen, State.withRegions_rd, State.withRegions_wr, stackArgAddr, State.withRegions_sp,
    State.callEntry_sp, hu, Nat.mul_zero, BitVec.add_zero]
  exact ⟨by omega_arith, rfl, rfl, hf.ou, hf.or, hf.os, hf.oa, hf.ur, hf.us, hf.ua, hf.rs, hf.sa, hf.no, hf.nu,
    hf.nr, hf.ns, hb.1, hb.2, hf.len, hf.gen, hf.scratch⟩

/-- What the candidate at `used` leaves: its status, p or zeros at `out`,
and the octets it read at `used`. -/
def CandPost (p : SPub) (used : Nat) (t : State) : Prop :=
  let res := sievedParameterCandidate p.bits p.gen (p.rand.drop used)
  ((t.gpr .x0).setWidth 32).toNat = candidateStatus res ∧
    Spec.Rsa.bytesAt t.mem p.op p.len =
      (match res with
        | some (some q, _) => Spec.Rsa.i2osp q p.len
        | _ => List.replicate p.len 0) ∧
    Spec.Rsa.wordsAt t.mem p.up 1 =
      [BitVec.ofNat 64 (match res with
        | some (_, rest) => (p.randLen - used) - rest.length
        | none => 0)]

theorem CandPost.frame {p : SPub} {used : Nat} {s t : State} {F : Region}
    (h : CandPost p used s) (hf : Frame [F] s.mem t.mem)
    (ho : (rO p).Disjoint F) (hu : (rU p).Disjoint F)
    (hr : (t.gpr .x0).setWidth 32 = (s.gpr .x0).setWidth 32) : CandPost p used t := by
  have eo : Spec.Rsa.bytesAt t.mem p.op p.len = Spec.Rsa.bytesAt s.mem p.op p.len :=
    List.map_congr_left fun i hi => lost_byte hf ho (List.mem_range.mp hi)
  have eu : Spec.Rsa.wordsAt t.mem p.up 1 = Spec.Rsa.wordsAt s.mem p.up 1 := by
    refine List.map_congr_left fun i hi => ?_
    obtain rfl : i = 0 := by simpa using hi
    exact hf.readW (r := rU p) (Offset.contains_base _ (by decide) (by decide))
      (fun R hR => by obtain rfl := List.mem_singleton.mp hR; exact hu) (by decide)
  unfold CandPost at h ⊢
  rw [eo, eu, hr]
  exact h

section

variable {p : SPub} {original s : State} {used k : Nat}

theorem call_covers_writes (h : SLive p original used k s) {u : State}
    (hw : u.wr = (allocated 16 s).wr) : Covers (callWr p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [hw]
  apply List.mem_cons_of_mem
  rw [h.wr, h.input.1.2.2.2.1]
  simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · show (⟨p.op, p.len⟩ : Region) ∈ _; rw [← h.input.out_eq]; simp [inWrites]
  · show (⟨p.up, 8⟩ : Region) ∈ _; rw [← h.input.used_eq]; simp [inWrites]
  · rw [← h.input.2]; simp [inWrites, inScr, sOfState]

theorem call_covers_reads (h : SLive p original used k s)
    {u : State} (hrd : u.rd = (allocated 16 s).rd) (hw : u.wr = (allocated 16 s).wr) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  obtain ⟨-, -, hrd', -⟩ := hi.1
  have hroom : used + (p.randLen - used) ≤ p.randLen := by have := h.used_le; omega_arith
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨inRand original, ?_, used, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inRand original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; rfl
    · cases hi.2; exact hroom
  · refine ⟨⟨callSp p, 16⟩, ?_, 0, ?_, by show 0 + 8 ≤ 16; decide⟩
    · rw [hw]; refine List.mem_append_right _ ?_
      show _ ∈ (⟨s.sp - BitVec.ofNat 64 16, 16⟩ :: s.wr)
      rw [h.sp]; exact List.mem_cons_self ..
    · rw [BitVec.add_zero]

/-- What the candidate writes, as the controller sees it. -/
theorem candidate_frame (h : SLive p original used k s) {u t : State}
    (hm : u.mem = writeController s.mem (callSp p) (callValues p))
    (hf : Frame (callWr p) u.mem t.mem) :
    Frame (SInput.callChanges original) s.mem t.mem := by
  have hi := h.input
  have hsp : p.sp = original.sp := hi.sp_eq
  have h1 : Frame (SInput.callChanges original) s.mem u.mem := by
    rw [hm]
    apply (writeController_frame_size _ _ (callValues p) (size := 8) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ rfl; show 8 * 0 + 8 ≤ 8; decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨below original.sp stackUse, by simp [SInput.callChanges], ?_⟩
    rw [← hsp]
    exact rA_sub p
  have h2 : Frame (SInput.callChanges original) u.mem t.mem := by
    apply hf.sub
    intro r hr
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inOut original, by simp [SInput.callChanges], by rw [hi.out_eq]; exact fun _ h => h⟩
    · exact ⟨inUsed original, by simp [SInput.callChanges], by rw [hi.used_eq]; exact fun _ h => h⟩
    · exact ⟨inScr original, by simp [SInput.callChanges], by rw [← hi.2]; exact fun _ h => h⟩
  exact h1.trans h2

/-- The candidate's view of the tape, at its entry. -/
theorem call_rand (h : SLive p original used k s) {u : State}
    (hm : u.mem = writeController s.mem (callSp p) (callValues p)) (ha : SArgs p used u) :
    pcRand (callState p used u) = p.rand.drop used := by
  have hfr : Frame (SInput.changes original) s.mem u.mem :=
    frame_of_callChanges original (candidate_frame (t := u) h hm (fun _ _ => rfl))
  have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := h.input.randLen_lt; omega_arith)
  simp only [pcRand, call_gpr (by decide : Reg.x5 ∉ linkRegs), call_gpr (by decide : Reg.x6 ∉ linkRegs),
    ha.2.2.2.2.2.1, ha.2.2.2.2.2.2.1, hrl, State.withRegions_mem, State.callEntry_mem]
  have hr := (h.input.random_frame hfr).trans h.random
  have hl := h.rand_length
  rw [← VG.Proof.Dsa.bytesAt_slice _ _ (show used + (p.randLen - used) ≤ p.randLen by
    have := h.used_le; omega_arith), hr, List.take_of_length_le (by simp only [List.length_drop, hl]; omega_arith)]

theorem search_candidate_run (c : Cand) (h : SLive p original used k s) :
    WP isa (candidateRun c.call) s fun t => SLive p original used k t ∧ CandPost p used t := by
  have hf := h.callFacts
  have hroom' : 16 ≤ s.sp.toNat := by
    have := hf.room
    have h16 : (p.sp - BitVec.ofNat 64 16).toNat = p.sp.toNat - 16 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith)]
      simp only [BitVec.toNat_ofNat]
    rw [h.sp, show (p.sp - 16 : Addr) = p.sp - BitVec.ofNat 64 16 from rfl, h16]
    omega_arith
  unfold candidateRun
  refine WP.alloc (by decide) hroom' ?_
  refine WP.seq (WP.mono (search_arguments_ok h) fun u ⟨⟨ha, hm⟩, k⟩ => ?_)
  have hu : u.sp = callSp p := by rw [k.sp]; show s.sp - BitVec.ofNat 64 16 = _; rw [h.sp]
  refine WP.callV (k := ParameterCandidate.pcContract) c.correct (call_candidate_pre hf hu ha hm)
    (call_covers_reads h k.rd k.wr) (call_covers_writes h k.wr) ?_ c.noFrames
  intro t hrd hwr hsp hfr hcs _ hvs hpost m u f
  have hA : Region.Sub ⟨s.sp - BitVec.ofNat 64 16, 16⟩ (below p.sp stackUse) := by
    rw [h.sp, show (p.sp - 16 : Addr) - BitVec.ofNat 64 16 = callSp p from rfl, callSp_eq]
    exact Region.sub_prefix (by decide)
  have hA' : ∀ R ∈ [(⟨s.sp - BitVec.ofNat 64 16, 16⟩ : Region)],
      ∃ R' ∈ SInput.callChanges original, Region.Sub R R' := by
    intro R hR
    obtain rfl := List.mem_singleton.mp hR
    refine ⟨below original.sp stackUse, by simp [SInput.callChanges], ?_⟩
    rw [← h.input.sp_eq]
    exact hA
  refine ⟨?_, ?_⟩
  · -- The loop state, after the frame.
    apply h.restore (t := { freed 16 t with mem := m, unknowns := u }) (show (freed 16 t).rd = s.rd from hrd.trans k.rd)
      (show (freed 16 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.wr]; rfl)
    · change t.sp + BitVec.ofNat 64 16 = s.sp
      rw [hsp, k.sp]
      exact BitVec.sub_add_cancel _ _
    · intro r hr h30
      exact (hcs r hr h30).trans (k.gpr r (by revert r hr; decide))
    · intro r hr
      exact (hvs r hr).trans (k.vcs r hr)
    · exact (candidate_frame h hm hfr).trans (f.sub hA')
  · -- The candidate's status and outputs.
    refine CandPost.frame (s := t) ?_ f ((h.input.outStack).1.sub_right hA) ((h.input.outStack).2.sub_right hA) rfl
    have hrand := call_rand h hm ha
    obtain ⟨r0, r1, r2, r3, r4, -, r6, -⟩ := ha
    have hb := hf.bits
    have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := toNat_ofNat_lt (by have := hf.len; omega_arith)
    have hbits : (BitVec.ofNat 64 p.bits).toNat = p.bits := toNat_ofNat_lt (by omega_arith)
    have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
      toNat_ofNat_lt (by have := hf.randLen; omega_arith)
    have hp := hpost
    simp only [ParameterCandidate.pcContract, pcPost, pcResult, hrand, call_gpr (by decide : Reg.x0 ∉ linkRegs),
      call_gpr (by decide : Reg.x1 ∉ linkRegs), call_gpr (by decide : Reg.x2 ∉ linkRegs),
      call_gpr (by decide : Reg.x3 ∉ linkRegs), call_gpr (by decide : Reg.x4 ∉ linkRegs),
      call_gpr (by decide : Reg.x6 ∉ linkRegs), r0, r1, r2, r3, r4, r6, hlen, hbits, hrl,
      gen_setWidth hf.gen, State.withRegions_gpr, State.withRegions_mem] at hp
    exact hp

end

end VG.Proof.Ffdh.AArch64.Generation

end

end

/-! # The parameter search's writes of its own words, and zeros at `out` (AArch64)

The terminal statuses and the exit for an exhausted bound
(`search_exhausted`); the zeroing of `out`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.AArch64.Generation.Search
open VG.Impl.Bignum.AArch64 (movi)

namespace SInput

variable {p : SPub} {original : State}

theorem out_mem (h : SInput p original) : (⟨p.op, p.len⟩ : Region) ∈ inWrites original := by
  rw [← h.out_eq]; simp [inWrites]

theorem out_ctl (h : SInput p original) : (⟨p.op, p.len⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  rw [← h.out_eq, ← h.ctl_eq]
  exact this.1.2.2

end SInput

/-- The controller's word-only writes keep `out`. -/
theorem out_frame {p : SPub} {original : State} (hi : SInput p original) {m m' : Mem}
    (hf : Frame [⟨p.control, 128⟩] m m') :
    Spec.Rsa.bytesAt m' p.op p.len = Spec.Rsa.bytesAt m p.op p.len := by
  have hk := hi.len_bounds
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi' => ?_
  exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hi.out_ctl)
    (show p.len ≤ 2 ^ 64 by omega_using [hk]) (List.mem_range.mp hi')

/-! ## Terminal statuses -/

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (3, 0), (14, BitVec.ofNat 64 status)]

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 16 := by
  simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem terminal_ok {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .x19 = B)
    {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      t.mem = writeController s.mem B (terminalValues status) ∧ Keep [.x10, .x11] s t := by
  rcases hst with rfl | rfl <;>
  refine WP.keep [.x10, .x11] ?_ (by decide) (by decide) (by decide +kernel) <;>
  unfold terminal writeController terminalValues <;>
  simp only [List.foldl_cons, List.foldl_nil]
  all_goals
    brun [ldf, stf, hb, imm64 (show 0 < 65536 by decide), imm64 (show 1 < 65536 by decide),
      imm64 (show 3 < 65536 by decide), a.st0, a.st 0 (by decide), a.st 24 (by decide),
      a.st 112 (by decide)]
    rfl

/-- A terminal status written over a loop state, with no attempts left. -/
theorem terminal_live {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      SLive p original used 0 t ∧ t.mem = writeController s.mem p.control (terminalValues status) := by
  refine WP.mono (terminal_ok h.access h.x19 hst) fun t ⟨hm, k⟩ => ?_
  have hh : Slots t.mem p.control (p.headers used 0) := by
    refine headers_after _ (terminalValues_bound status) hm ?_
    intro e he
    simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [SPub.headers])
  refine ⟨h.update (u := used) (k' := 0) h.used_le (Nat.zero_le _) _
    (terminalValues_bound status) (by
      simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm k.mono hh, hm⟩

/-- The words of a terminal status written over a loop state. -/
theorem terminal_words {p : SPub} {original s t : State} {used k : Nat}
    (h : SLive p original used k s) {status : Nat}
    (hm : (j : Nat) → j < 16 → word t.mem p.control (8 * j) =
      controllerValue (terminalValues status) j (word s.mem p.control (8 * j))) :
    word t.mem p.control 112 = BitVec.ofNat 64 status ∧
      Spec.Rsa.wordsAt t.mem p.control 4 = [0, BitVec.ofNat 64 p.len,
        BitVec.ofNat 64 (parameterEntropy p.bits), 0] := by
  refine ⟨?_, ?_⟩
  · rw [show (112 : Nat) = 8 * 14 from rfl, hm 14 (by decide)]
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]
  · change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
      word t.mem p.control (8 * 3)] = _
    rw [hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)]
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]
    rw [h.header (j := 1) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers]),
      h.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])]

/-! ## Zeros at `out` -/

/-- A zeroing of `out` changes memory only there. -/
theorem zero_frame {p : SPub} {original : State} (hinput : SInput p original) {m m' : Mem}
    (hf : ∀ x, (∀ j < p.len, x ≠ p.op + BitVec.ofNat 64 j) → m' x = m x) :
    Frame (SInput.callChanges original) m m' := by
  intro a ha
  apply hf
  intro i hi he
  have hk := hinput.len_bounds
  have hin : (⟨p.op, p.len⟩ : Region) ∈ SInput.callChanges original := by
    rw [← hinput.out_eq]; simp [SInput.callChanges]
  apply ha _ hin
  rw [he]
  exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])

theorem search_zero_out {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa zeroOut s fun t =>
      SLive p original used k t ∧ Spec.Rsa.bytesAt t.mem p.op p.len = List.replicate p.len 0 ∧
      (∀ j < 16, word t.mem p.control (8 * j) = word s.mem p.control (8 * j)) := by
  have hk := h.input.len_bounds
  have scr := h.input.control_scr (t := s) h.wr
  have hv := h.header (j := 5) (v := p.op) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv hv6
  have hl : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 40) 8 := scr.ld (by decide)
  have hl6 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 48) 8 := scr.ld (by decide)
  have hout : ∀ i < p.len, InRegions s.wr (p.op + BitVec.ofNat 64 i) 1 := fun i hi =>
    ⟨⟨p.op, p.len⟩, by rw [h.wr, h.input.1.2.2.2.1]; exact h.input.out_mem,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 p.len ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    brun [ldf, h.x19, imm64 (show 0 < 65536 by decide), hl, hl6, hv, hv6]) (by decide) (by decide)
      (by decide +kernel)) fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (N := p.len) (by omega_using [hk]) (by omega_using [hk]) (BInv s₁ p.op)
    (fun i hi t hI _ => bStep_ok (by omega_using [hk]) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hi hI)
    ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h2) fun t hI => ?_
  have hf : ∀ x, (∀ i < p.len, x ≠ p.op + BitVec.ofNat 64 i) → t.mem x = s.mem x :=
    fun x hx => by rw [hI.frame x hx, hm₁]
  have kk := k₁.trans hI.keep
  have hfr := zero_frame h.input hf
  refine ⟨h.restore kk.rd kk.wr kk.sp (fun r hr _ => kk.gpr r (by revert r hr; decide)) kk.vcs hfr, ?_,
    fun j hj => h.input.control_frame hfr j hj⟩
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact hI.bytes i (List.mem_range.mp hi)

theorem search_exhausted {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa exhausted s (SDone p original (.exhausted used)) := by
  unfold exhausted
  refine WP.seq (WP.mono (terminal_live h (status := 3) (.inr rfl)) fun t ⟨ht, hm⟩ => ?_)
  refine WP.mono (search_zero_out ht) fun u ⟨hu, hz, hc⟩ => ?_
  have hw (j : Nat) (hj : j < 16) : word u.mem p.control (8 * j) =
      controllerValue (terminalValues 3) j (word s.mem p.control (8 * j)) := by
    rw [hc j hj, hm, writeController_word _ _ _ (terminalValues_bound 3) j hj]
  obtain ⟨hs, hp⟩ := terminal_words h hw
  exact hu.done rfl hs hp hz

end VG.Proof.Ffdh.AArch64.Generation
