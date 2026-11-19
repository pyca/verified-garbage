module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Live
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Writes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline

/-! ### `Ffdh.PPC64LE.Generation.Search.Call`, which this module and modules that import it used -/

section

/-! # One candidate of the parameter search (PPC64LE)

In its frame of 112 bytes, the controller passes
`vg_ffdh_parameter_candidate_sieved` the rest of the tape. The candidate's
buffers are the controller's (`out`, `used`, the tape's rest and the working
space, and the table of trial division it reads),
and its stack argument is at offset 96 of the candidate's frame, in the 336
bytes of stack below the controller's stack pointer on entry, which no buffer
overlaps. The candidate keeps the controller's state, and leaves its status,
p or zeros at `out`, and the octets it read at `used`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame_size
  controllerValue)
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (pcPre pcPost pcResult pcRand)
open VG.Impl.Ffdh.PPC64LE.Generation.Search

/-- The stack pointer in the candidate's frame. -/
abbrev callSp (p : SPub) : Addr := p.sp - BitVec.ofNat 64 160

theorem callSp_eq (p : SPub) : p.sp - 48 - BitVec.ofNat 64 112 = callSp p := by
  rw [BitVec.sub_sub]; rfl

/-- The candidate's regions: `out`, `used`, the tape's rest, the working
space and its argument. -/
abbrev rO (p : SPub) : Region := ⟨p.op, p.len⟩
abbrev rU (p : SPub) : Region := ⟨p.up, 8⟩
abbrev rR (p : SPub) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.randLen - used⟩
abbrev rS (p : SPub) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : SPub) : Region := ⟨callSp p + BitVec.ofNat 64 96, 8⟩
abbrev rT (p : SPub) : Region := ⟨p.T, 8192⟩
/-- The stack the candidate may use. -/
abbrev rB (p : SPub) : Region := below (callSp p) 176

theorem rA_eq (p : SPub) : callSp p + BitVec.ofNat 64 96 = p.sp - BitVec.ofNat 64 64 :=
  (Offset.sub_ofNat_eq p.sp (by decide : 64 ≤ 160)).symm

theorem rA_sub (p : SPub) : Region.Sub (rA p) (below p.sp stackUse) := by
  rw [rA, rA_eq]; exact Offset.sub_below _ (by decide) (by decide)

theorem rB_sub (p : SPub) : Region.Sub (rB p) (below p.sp stackUse) :=
  below_body' p.sp 160 176

theorem rA_rB (p : SPub) : (rA p).Disjoint (rB p) :=
  Offset.disjoint_below (callSp p) (n := 176) (d := 96) (k := 8) (by decide)

structure CallFacts (p : SPub) (used : Nat) : Prop where
  room : 336 ≤ p.sp.toNat
  ou : (rO p).Disjoint (rU p)
  or : (rO p).Disjoint (rR p used)
  os : (rO p).Disjoint (rS p)
  oa : (rO p).Disjoint (rA p)
  ur : (rU p).Disjoint (rR p used)
  us : (rU p).Disjoint (rS p)
  ua : (rU p).Disjoint (rA p)
  rs : (rR p used).Disjoint (rS p)
  sa : (rS p).Disjoint (rA p)
  bo : (rB p).Disjoint (rO p)
  bu : (rB p).Disjoint (rU p)
  br : (rB p).Disjoint (rR p used)
  bs : (rB p).Disjoint (rS p)
  ba : (rB p).Disjoint (rA p)
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
  nt : p.T.toNat + 8192 ≤ 2 ^ 64
  to : (rT p).Disjoint (rO p)
  ts : (rT p).Disjoint (rS p)
  oC : (rO p).Disjoint ⟨callSp p, 112⟩
  uC : (rU p).Disjoint ⟨callSp p, 112⟩

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
  obtain ⟨⟨wor, -, wot⟩, ⟨wur, -⟩, ⟨wsr, -, wst⟩, -⟩ := hwr
  obtain ⟨bo, bu, bs, -, br, -⟩ := hstk
  obtain ⟨no, nu, ns, -, nr, -, nt⟩ := hnw
  have hR : Region.Sub (rR (sOfState original) used) (inRand original) :=
    Offset.sub_base _ hroom
  have hA := rA_sub (sOfState original)
  have hB := rB_sub (sOfState original)
  obtain hC : Region.Sub ⟨callSp (sOfState original), 112⟩ (below (sOfState original).sp stackUse) :=
    Offset.sub_below _ (by decide) (by decide)
  have hsp' : (sOfState original).sp = original.sp := rfl
  rw [hsp'] at hA hB hC
  refine ⟨by rw [hsp']; exact hsp, pou, wor.sub_right hR, pos, bo.symm.sub_right hA,
    wur.sub_right hR, pus, bu.symm.sub_right hA, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, bo.sub_left hB, bu.sub_left hB, (br.sub_left hB).sub_right hR, bs.sub_left hB,
    (rA_rB _).symm, no, nu, nowrap_tape nr hroom, ns, ⟨hb1, hb2⟩, hl, hg, ?_, ?_, BitVec.isLt _, nt,
    wot.symm, wst.symm, bo.symm.sub_right hC, bu.symm.sub_right hC⟩
  · simp only [sOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [sOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]

/-- The candidate's stack argument: `scratch_len`, at offset 96 of its
frame. -/
def callValues (p : SPub) : List (Nat × BitVec 64) := [(12, BitVec.ofNat 64 (p.Z / 8))]

theorem callValues_bound (p : SPub) : ∀ e ∈ callValues p, e.1 < 16 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ rfl; show 12 < 16; decide

/-- The candidate's register arguments. -/
def SArgs (p : SPub) (used : Nat) (t : State) : Prop :=
  t.gpr .r3 = p.op ∧ t.gpr .r4 = BitVec.ofNat 64 p.len ∧ t.gpr .r5 = p.up ∧
  t.gpr .r6 = BitVec.ofNat 64 p.bits ∧ t.gpr .r7 = BitVec.ofNat 64 p.gen ∧
  t.gpr .r8 = p.rp + BitVec.ofNat 64 used ∧ t.gpr .r9 = BitVec.ofNat 64 (p.randLen - used) ∧
  t.gpr .r10 = p.B

/-- The registers the arguments' block writes. -/
abbrev argRegsW : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The frame's push writes its back chain below the stack pointer. -/
theorem alloc_frame {p : SPub} {original s : State} {used k : Nat} (h : SLive p original used k s) :
    Frame (SInput.callChanges original) s.mem (allocated 112 s).mem := by
  have hi := h.input
  refine Frame.write (Frame.refl _ _) (r := below original.sp stackUse) (by simp [SInput.callChanges]) _ ?_
  rw [h.sp, callSp_eq, ← hi.sp_eq]
  exact Offset.contains_below p.sp (a := 160) (b := 336) (by decide) (by decide) (by decide)

theorem search_arguments_ok {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa (.block arguments) (allocated 112 s) fun u =>
      (SArgs p used u ∧ u.mem = writeController (allocated 112 s).mem (callSp p) (callValues p)) ∧
      Keep argRegsW (allocated 112 s) u := by
  have a := h.access
  have hc := h.input.control_frame (alloc_frame h)
  have e0 : s.sp - BitVec.ofNat 64 112 = callSp p := by rw [h.sp]; exact callSp_eq p
  have hw0 : InRegions (allocated 112 s).wr (callSp p + BitVec.ofNat 64 96) 8 := by
    refine ⟨frameR 112 s, List.mem_cons_self .., ?_⟩
    simp only [frameR, e0]
    rw [show callSp p + BitVec.ofNat 64 96 = callSp p + 32 + BitVec.ofNat 64 64 by
      rw [BitVec.add_assoc]; rfl]
    exact Offset.contains_base _ (by decide) (by decide)
  have hl : ∀ d, d + 8 ≤ 128 →
      InRegions ((allocated 112 s).rd ++ (allocated 112 s).wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun d hd => by
      obtain ⟨r, hr, hc⟩ := a.ld d hd
      refine ⟨r, ?_, hc⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv (j : Nat) (hj : j < 16) {v : BitVec 64} (he : (j, v) ∈ p.headers used k) :
      (allocated 112 s).mem.readW (p.control + BitVec.ofNat 64 (8 * j)) 64 = v :=
    (hc j hj).trans (h.header he)
  have hv5 := hv 5 (by decide) (v := p.op) (by simp [SPub.headers])
  have hv6 := hv 6 (by decide) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  have hv7 := hv 7 (by decide) (v := p.up) (by simp [SPub.headers])
  have hv8 := hv 8 (by decide) (v := BitVec.ofNat 64 p.bits) (by simp [SPub.headers])
  have hv9 := hv 9 (by decide) (v := BitVec.ofNat 64 p.gen) (by simp [SPub.headers])
  have hv10 := hv 10 (by decide) (v := p.rp + BitVec.ofNat 64 used) (by simp [SPub.headers])
  have hv11 := hv 11 (by decide) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  have hv13 := hv 13 (by decide) (v := p.B) (by simp [SPub.headers])
  have hv15 := hv 15 (by decide) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [SPub.headers])
  simp only [Nat.reduceMul] at hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv13 hv15
  have ea : ∀ t : State, exec (.addSp .r11 96) t = some (t.write .r11 (t.sp + BitVec.ofNat 64 96)) := by
    intro t; simp [exec]
  refine WP.keep argRegsW ?_ (by decide)
  unfold arguments writeController callValues SArgs
  simp only [List.foldl_cons, List.foldl_nil]
  have r31 : (allocated 112 s).gpr .r31 = p.control := h.r31
  have sp' : (allocated 112 s).sp = callSp p := e0
  prun [ldf, r31, sp', ea, hl 40 (by decide), hl 48 (by decide), hl 56 (by decide), hl 64 (by decide),
    hl 72 (by decide), hl 80 (by decide), hl 88 (by decide), hl 104 (by decide), hl 120 (by decide), hw0,
    hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv13, hv15]

/-- The regions the candidate reads: the tape's rest, its stack argument
and the table;
those it writes: `out`, `used` and the working space. -/
def callRd (p : SPub) (used : Nat) : List Region := [rR p used, rA p, rT p]
def callWr (p : SPub) : List Region := [rO p, rU p, rS p]

/-- The callee's entry, as the call makes it. -/
abbrev callState (p : SPub) (used : Nat) (u : State) : State :=
  u.callEntry.withRegions (callRd p used) (callWr p)

theorem call_gpr {p : SPub} {used : Nat} {u : State} {r : Reg} (hr : r ∉ linkRegs) :
    (callState p used u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem call_arg {p : SPub} {u : State} {m : Mem} (hu : u.sp = callSp p)
    (hm : u.mem = writeController m (callSp p) (callValues p)) :
    stackArg u 0 = BitVec.ofNat 64 (p.Z / 8) := by
  unfold stackArg stackArgAddr
  rw [hu, hm]
  exact writeController_word _ _ _ (callValues_bound p) 12 (by decide)

theorem callSp_toNat {p : SPub} (hf : 336 ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 160 := by
  rw [callSp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith)]
  simp only [BitVec.toNat_ofNat]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem gen_setWidth {g : Nat} (h : g = 2 ∨ g = 5) : ((BitVec.ofNat 64 g).setWidth 32).toNat = g := by
  rcases h with rfl | rfl <;> decide

theorem call_candidate_pre {p : SPub} {used : Nat} {u : State} {m : Mem} (hf : CallFacts p used)
    (hu : u.sp = callSp p) (ha : SArgs p used u)
    (hm : u.mem = writeController m (callSp p) (callValues p))
    (hy : u.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = p.T)
    (ht : VG.Proof.Ffdh.PPC64LE.ParameterCandidate.TabAt p.T u.mem) :
    pcPre (callState p used u) := by
  have h0 := call_arg hu hm
  obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
  have hb := hf.bits
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := toNat_ofNat_lt (by have := hf.len; omega_arith)
  have hbits : (BitVec.ofNat 64 p.bits).toNat = p.bits := toNat_ofNat_lt (by omega_arith)
  have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := hf.randLen; omega_arith)
  have hzw : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 :=
    toNat_ofNat_lt (by have := hf.ns; omega_arith)
  have hsp := callSp_toNat hf.room
  have hroom := hf.room
  have hlt := p.sp.isLt
  have hst : stackArg (callState p used u) 0 = stackArg u 0 := rfl
  have hsa : stackArgAddr (callState p used u) 0 = callSp p + BitVec.ofNat 64 96 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hu]
  have hys : (callState p used u).syms VG.Impl.RsaKeyGen.TrialTable32.symbol = p.T := hy
  unfold pcPre
  simp only [ParameterCandidate.tabR, ParameterCandidate.PcTab, hys]
  simp only [call_gpr (by decide : Reg.r3 ∉ linkRegs), call_gpr (by decide : Reg.r4 ∉ linkRegs),
    call_gpr (by decide : Reg.r5 ∉ linkRegs), call_gpr (by decide : Reg.r6 ∉ linkRegs),
    call_gpr (by decide : Reg.r7 ∉ linkRegs), call_gpr (by decide : Reg.r8 ∉ linkRegs),
    call_gpr (by decide : Reg.r9 ∉ linkRegs), call_gpr (by decide : Reg.r10 ∉ linkRegs),
    hst, hsa, h0, r3, r4, r5, r6, r7, r8, r9, r10, hlen, hbits, hrl, hzw, hf.z8,
    gen_setWidth hf.gen, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, hu]
  exact ⟨by omega_arith, by omega_arith, rfl, rfl, hf.ou, hf.or, hf.os, hf.oa, hf.ur, hf.us, hf.ua, hf.rs, hf.sa,
    hf.bo, hf.bu, hf.br, hf.bs, hf.ba, hf.no, hf.nu, hf.nr, hf.ns, hb.1, hb.2, hf.len, hf.gen, hf.scratch,
    hf.nt, ht, hf.to, hf.ts⟩

/-- What the candidate at `used` leaves: its status, p or zeros at `out`,
and the octets it read at `used`. -/
def CandPost (p : SPub) (used : Nat) (t : State) : Prop :=
  let res := sievedParameterCandidate p.bits p.gen (p.rand.drop used)
  ((t.gpr .r3).setWidth 32).toNat = candidateStatus res ∧
    Spec.Rsa.bytesAt t.mem p.op p.len =
      (match res with
        | some (some q, _) => Spec.Rsa.i2osp q p.len
        | _ => List.replicate p.len 0) ∧
    Spec.Rsa.wordsAt t.mem p.up 1 =
      [BitVec.ofNat 64 (match res with
        | some (_, rest) => (p.randLen - used) - rest.length
        | none => 0)]

section

variable {p : SPub} {original s : State} {used k : Nat}

theorem call_covers_writes (h : SLive p original used k s) {u : State}
    (hw : u.wr = (allocated 112 s).wr) : Covers (callWr p) u.wr := by
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
    {u : State} (hrd : u.rd = (allocated 112 s).rd) (hw : u.wr = (allocated 112 s).wr) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  obtain ⟨-, -, hrd', -⟩ := hi.1
  have hroom : used + (p.randLen - used) ≤ p.randLen := by have := h.used_le; omega_arith
  have e0 : s.sp - BitVec.ofNat 64 112 = callSp p := by rw [h.sp]; exact callSp_eq p
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨inRand original, ?_, used, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inRand original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; rfl
    · cases hi.2; exact hroom
  · refine ⟨frameR 112 s, ?_, 64, ?_, by show 64 + 8 ≤ 112 - 32; decide⟩
    · rw [hw]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · show callSp p + BitVec.ofNat 64 96 = s.sp - BitVec.ofNat 64 112 + 32 + BitVec.ofNat 64 64
      rw [e0, BitVec.add_assoc]; rfl
  · refine ⟨inTab original, ?_, 0, ?_, by show 0 + 8192 ≤ 8192; decide⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inTab original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; show _ = _ + BitVec.ofNat 64 0; rw [BitVec.add_zero]; rfl

/-- What the candidate writes, as the controller sees it. -/
theorem candidate_frame (h : SLive p original used k s) {u t : State}
    (hm : u.mem = writeController (allocated 112 s).mem (callSp p) (callValues p))
    (hf : Frame (callWr p ++ [below (callSp p) 176]) u.mem t.mem) :
    Frame (SInput.callChanges original) s.mem t.mem := by
  have hi := h.input
  have hsp : p.sp = original.sp := hi.sp_eq
  have h1 : Frame (SInput.callChanges original) (allocated 112 s).mem u.mem := by
    rw [hm]
    apply (writeController_frame_size _ _ (callValues p) (size := 104) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ rfl; show 8 * 12 + 8 ≤ 104; decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨below original.sp stackUse, by simp [SInput.callChanges], ?_⟩
    rw [← hsp]
    exact Offset.sub_below p.sp (a := 160) (b := 336) (by decide) (by decide)
  have h2 : Frame (SInput.callChanges original) u.mem t.mem := by
    apply hf.sub
    intro r hr
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨inOut original, by simp [SInput.callChanges], by rw [hi.out_eq]; exact fun _ h => h⟩
    · exact ⟨inUsed original, by simp [SInput.callChanges], by rw [hi.used_eq]; exact fun _ h => h⟩
    · exact ⟨inScr original, by simp [SInput.callChanges], by rw [← hi.2]; exact fun _ h => h⟩
    · exact ⟨below original.sp stackUse, by simp [SInput.callChanges], by rw [← hsp]; exact rB_sub p⟩
  exact (alloc_frame h).trans (h1.trans h2)

/-- The candidate's view of the tape, at its entry. -/
theorem call_rand (h : SLive p original used k s) {u : State}
    (hm : u.mem = writeController (allocated 112 s).mem (callSp p) (callValues p)) (ha : SArgs p used u) :
    pcRand (callState p used u) = p.rand.drop used := by
  have hfr : Frame (SInput.changes original) s.mem u.mem :=
    frame_of_callChanges original (candidate_frame (t := u) h hm (fun _ _ => rfl))
  have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := h.input.randLen_lt; omega_arith)
  simp only [pcRand, call_gpr (by decide : Reg.r8 ∉ linkRegs), call_gpr (by decide : Reg.r9 ∉ linkRegs),
    ha.2.2.2.2.2.1, ha.2.2.2.2.2.2.1, hrl, State.withRegions_mem, State.callEntry_mem]
  have hr := (h.input.random_frame hfr).trans h.random
  have hl := h.rand_length
  rw [← VG.Proof.Dsa.bytesAt_slice _ _ (show used + (p.randLen - used) ≤ p.randLen by
    have := h.used_le; omega_arith), hr, List.take_of_length_le (by simp only [List.length_drop, hl]; omega_arith)]

theorem search_candidate_run (c : Cand) (h : SLive p original used k s) :
    WP isa (candidateRun c.call) s fun t => SLive p original used k t ∧ CandPost p used t := by
  have hf := h.callFacts
  have e0 : s.sp - BitVec.ofNat 64 112 = callSp p := by rw [h.sp]; exact callSp_eq p
  have hroom' : 112 ≤ s.sp.toNat := by
    have := hf.room
    have h48 : (p.sp - 48).toNat = p.sp.toNat - 48 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; show 48 ≤ _; omega_arith)]; rfl
    rw [h.sp, h48]
    omega_arith
  unfold candidateRun
  refine WP.of_syms (WP.alloc (by decide) hroom' ?_)
  refine WP.seq (WP.mono_syms (search_arguments_ok h) fun u ⟨⟨ha, hm⟩, ku⟩ syu => ?_)
  have hu : u.sp = callSp p := ku.sp.trans e0
  have hT : original.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = p.T := by rw [← h.input.2]; rfl
  have hy : u.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = p.T := by
    rw [syu]; show s.syms _ = _; rw [h.syms]; exact hT
  have htu : VG.Proof.Ffdh.PPC64LE.ParameterCandidate.TabAt p.T u.mem :=
    h.input.table_frame (frame_of_callChanges original (candidate_frame (t := u) h hm (fun _ _ => rfl))) h.table
  refine WP.callAny (k := ParameterCandidate.pcContract) c.correct (call_candidate_pre hf hu ha hm hy htu)
    (call_covers_reads h ku.rd ku.wr) (call_covers_writes h ku.wr) ?_ (by have := c.stack; omega_arith)
  intro t hrd hwr hsp hfr hcs hpost mL _ fl hyt
  -- Whatever the released frame's bytes hold: the outputs lie apart from it.
  rw [e0] at fl
  obtain hC : Region.Sub ⟨callSp p, 112⟩ (below original.sp stackUse) := by
    rw [← h.input.sp_eq]; exact Offset.sub_below _ (by decide) (by decide)
  have hfr' : Frame (callWr p ++ [below (callSp p) 176]) u.mem t.mem := by
    rw [hu] at hfr
    exact hfr.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          Offset.below_mono _ c.stack (by decide)⟩
  refine ⟨?_, ?_⟩
  · -- The loop state, after the frame.
    refine h.restore ?_ ?_ ?_ ?_ ?_ ?_
    · exact hrd.trans ku.rd
    · change t.wr.tail = s.wr; rw [hwr, ku.wr]; rfl
    · change t.sp + BitVec.ofNat 64 112 = s.sp
      rw [hsp, ku.sp]
      exact BitVec.sub_add_cancel _ _
    · intro r hr
      exact (hcs r hr).trans (ku.gpr r (by revert r hr; decide))
    · exact (candidate_frame h hm hfr').trans (fl.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, by simp [SInput.callChanges], hC⟩)
    · exact hyt
  · -- The candidate's status and outputs.
    have hrand := call_rand h hm ha
    obtain ⟨r3, r4, r5, r6, r7, -, r9, -⟩ := ha
    have hb := hf.bits
    have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := toNat_ofNat_lt (by have := hf.len; omega_arith)
    have hbits : (BitVec.ofNat 64 p.bits).toNat = p.bits := toNat_ofNat_lt (by omega_arith)
    have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
      toNat_ofNat_lt (by have := hf.randLen; omega_arith)
    have hp := hpost
    simp only [ParameterCandidate.pcContract, pcPost, pcResult, hrand, call_gpr (by decide : Reg.r3 ∉ linkRegs),
      call_gpr (by decide : Reg.r4 ∉ linkRegs), call_gpr (by decide : Reg.r5 ∉ linkRegs),
      call_gpr (by decide : Reg.r6 ∉ linkRegs), call_gpr (by decide : Reg.r7 ∉ linkRegs),
      call_gpr (by decide : Reg.r9 ∉ linkRegs), r3, r4, r5, r6, r7, r9, hlen, hbits, hrl,
      gen_setWidth hf.gen, State.withRegions_gpr, State.withRegions_mem] at hp
    obtain ⟨q1, q2, q3⟩ := hp
    refine ⟨q1, ?_, ?_⟩
    · refine Eq.trans ?_ q2
      exact List.map_congr_left fun i hi => lost_byte fl (R := rO p) hf.oC (List.mem_range.mp hi)
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
        at q3 ⊢
      refine Eq.trans (congrArg (fun x => [x]) ?_) q3
      exact fl.readW (r := rU p) (Region.contains_self _ _)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hf.uC) (by decide)

end

end VG.Proof.Ffdh.PPC64LE.Generation

end

end

/-! ### `Ffdh.PPC64LE.Generation.Search.Classify`, which this module and modules that import it used -/

section

/-! # After a candidate: p, the next candidate, or an exit (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.PPC64LE.Generation.Search

/-- The candidate at octet `used` of the tape. -/
abbrev SPub.cand (p : SPub) (used : Nat) : Option (Option Nat × List Byte) :=
  sievedParameterCandidate p.bits p.gen (p.rand.drop used)

/-- The octets the candidate at `used` reads. -/
def SPub.read (p : SPub) (used : Nat) : Nat :=
  match p.cand used with
  | some (_, rest) => (p.randLen - used) - rest.length
  | none => 0

theorem SPub.read_le {p : SPub} {original s : State} {used k : Nat} (h : SLive p original used k s) :
    used + p.read used ≤ p.randLen := by
  have hu := h.used_le
  unfold SPub.read
  split
  · omega_arith
  · omega_arith

theorem status_lt (r : Option (Option Nat × List Byte)) : candidateStatus r < 3 := by
  unfold candidateStatus; split <;> decide

/-- The status, the low 32 bits of `r3`. -/
theorem low32 {x : BitVec 64} {st : Nat} (h : (x.setWidth 32).toNat = st) :
    (x <<< 32) >>> 32 = BitVec.ofNat 64 st := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, ← h, BitVec.toNat_setWidth]
  have := x.isLt
  omega_arith

/-- The status and the octets read, after the candidate. -/
theorem search_head {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hp : CandPost p used s) :
    WP isa (.block (head ++ ([.subi .r12 .r9 1] : List Instr))) s fun t =>
      SLive p original used k t ∧ CandPost p used t ∧
      t.gpr .r9 = BitVec.ofNat 64 (candidateStatus (p.cand used)) ∧
      t.gpr .r10 = BitVec.ofNat 64 (p.read used) ∧
      isa.eval (.zero .d .r12) t = some (decide (candidateStatus (p.cand used) = 1)) := by
  have a := h.access
  have hv7 := h.header (j := 7) (v := p.up) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have hu : InRegions (s.rd ++ s.wr) (p.up + BitVec.ofNat 64 0) 8 := by
    refine ⟨⟨p.up, 8⟩, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.1.2.2.2.1, ← h.input.used_eq]; simp [inWrites]
    · exact Offset.contains_base p.up (d := 0) (n := 8) (k := 8) (by decide) (by decide)
  have hw : s.mem.readW (p.up + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (p.read used) := by
    have := hp.2.2
    change [word s.mem p.up 0] = _ at this
    simp only [Bignum.word, off, List.cons.injEq, and_true] at this
    rw [this]; rfl
  have hst := status_lt (p.cand used)
  have h9 := low32 hp.1
  have hb : ∀ st < 3, (BitVec.ofNat 64 st - BitVec.ofNat 64 1 == 0) = decide (st = 1) := by decide
  refine WP.mono_syms (WP.keep [.r9, .r10, .r11, .r12] (Q := fun t =>
    (t.gpr .r9 = BitVec.ofNat 64 (candidateStatus (p.cand used)) ∧
      t.gpr .r10 = BitVec.ofNat 64 (p.read used) ∧
      isa.eval (.zero .d .r12) t = some (decide (candidateStatus (p.cand used) = 1))) ∧ t.mem = s.mem) ?_
    (by decide)) fun t ⟨⟨⟨h9, h10, he⟩, hm⟩, k⟩ hy => ?_
  · unfold head
    prun [ldf, h.r31, hv7, a.ld 56 (by decide), hu, hw, h9]
    refine (eval_zero _ _).trans ?_
    rw [RegUpd.gpr_write_self, hb _ hst]
  · refine ⟨h.keep k hm hy, ?_, h9, h10, he⟩
    unfold CandPost at hp ⊢
    rw [hm, k.gpr .r3 (by decide)]
    exact hp

/-- A finished search, from a loop state through writes of the controller's
words but the saved `r31` and the pointer to `used`. -/
theorem SLive.doneWrites {p : SPub} {original s t : State} {used k : Nat}
    (h : SLive p original used k s) (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1) (h7 : ∀ e ∈ values, 7 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (kp : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t)
    {r : ParameterSearchResult} (hu : word t.mem p.control 96 = BitVec.ofNat 64 r.used)
    (hs : word t.mem p.control 112 = BitVec.ofNat 64 r.status)
    (hp : Spec.Rsa.wordsAt t.mem p.control 4 = p.policy r) (ho : SOutput p r s.mem) :
    SDone p original r t := by
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (by revert r hr; decide)
  have hw (j : Nat) (hj : j < 16) (hn : ∀ e ∈ values, j ≠ e.1) :
      word t.mem p.control (8 * j) = word s.mem p.control (8 * j) := by
    rw [hm, writeController_word _ _ _ hb j hj, controllerValue_unchanged _ _ _ hn]
  refine ⟨h.input, kp.rd.trans h.rd, kp.wr.trans h.wr, (hg .r31 (by decide)).trans h.r31,
    fun reg hreg h31 => (hg reg hreg).trans (h.saved reg hreg h31), ?_, ?_, hu, hs, hp, ?_⟩
  · exact (hw 4 (by decide) h4).trans h.savedR31
  · exact (hw 7 (by decide) h7).trans (h.header (j := 7) (by simp [SPub.headers]))
  · unfold SOutput at ho ⊢
    rw [hm, out_frame h.input (writeController_frame s.mem p.control values hb)]
    exact ho

/-! ## An accepted candidate -/

def acceptValues (used : Nat) : List (Nat × BitVec 64) :=
  (12, BitVec.ofNat 64 used) :: terminalValues 1

theorem acceptValues_bound (used : Nat) : ∀ e ∈ acceptValues used, e.1 < 16 := by
  simp only [acceptValues, terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem search_accept {p : SPub} {original s : State} {used k q : Nat} {rest : List Byte}
    (h : SLive p original used k s) (hp : CandPost p used s) (hk : k ≠ 0)
    (hc : p.cand used = some (some q, rest)) (h10 : s.gpr .r10 = BitVec.ofNat 64 (p.read used)) :
    WP isa (.block accept) s (SDone p original (p.tail used k)) := by
  have a := h.access
  have hv12 := h.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv12
  have hn : p.read used = (p.randLen - used) - rest.length := by simp only [SPub.read, hc]
  have e12 : BitVec.ofNat 64 used + BitVec.ofNat 64 (p.read used) =
      BitVec.ofNat 64 (used + ((p.randLen - used) - rest.length)) := by
    rw [hn, ← BitVec.ofNat_add]
  rw [SPub.tail_accept hk h.rand_length hc]
  refine WP.mono (WP.keep [.r10, .r11] (Q := fun t =>
    t.mem = writeController s.mem p.control (acceptValues (used + ((p.randLen - used) - rest.length)))) ?_
      (by decide)) fun t ⟨hm, kt⟩ => ?_
  · unfold accept terminal writeController acceptValues terminalValues
    simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
    prun [ldf, stf, h.r31, h10, hv12, e12, a.ld 96 (by decide), a.st 96 (by decide), a.st0,
      a.st 0 (by decide), a.st 24 (by decide), a.st 112 (by decide), BitVec.add_zero]
    rfl
  have hb := acceptValues_bound (used + ((p.randLen - used) - rest.length))
  have hw (j : Nat) (hj : j < 16) : word t.mem p.control (8 * j) =
      controllerValue (acceptValues (used + ((p.randLen - used) - rest.length))) j
        (word s.mem p.control (8 * j)) := by
    rw [hm, writeController_word _ _ _ hb j hj]
  refine h.doneWrites _ hb (by
      simp only [acceptValues, terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) (by
      simp only [acceptValues, terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) hm kt.mono ?_ ?_ ?_ ?_
  · rw [show (96 : Nat) = 8 * 12 from rfl, hw 12 (by decide)]
    simp only [controllerValue, acceptValues, terminalValues, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_true, ite_false]
    rfl
  · rw [show (112 : Nat) = 8 * 14 from rfl, hw 14 (by decide)]
    simp only [controllerValue, acceptValues, terminalValues, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_true, ite_false]
    rfl
  · change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
      word t.mem p.control (8 * 3)] = _
    rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)]
    simp only [controllerValue, acceptValues, terminalValues, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_true, ite_false]
    rw [h.header (j := 1) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers]),
      h.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])]
    rfl
  · have ho := hp.2.1
    simp only [hc] at ho
    exact ho

/-! ## A rejected candidate -/

def rejectValues (p : SPub) (used k : Nat) : List (Nat × BitVec 64) :=
  [(12, BitVec.ofNat 64 used), (10, p.rp + BitVec.ofNat 64 used),
    (11, BitVec.ofNat 64 (p.randLen - used)), (0, BitVec.ofNat 64 k), (14, 4)]

theorem rejectValues_bound (p : SPub) (used k : Nat) : ∀ e ∈ rejectValues p used k, e.1 < 16 := by
  simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem ofNat_pred {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by
    simp only [BitVec.le_def, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt h]; omega_arith)]
  simp only [BitVec.toNat_ofNat]
  omega_arith

theorem search_reject {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (h10 : s.gpr .r10 = BitVec.ofNat 64 (p.read used)) :
    WP isa (.block reject) s fun t =>
      SLive p original (used + p.read used) (k - 1) t ∧ word t.mem p.control 112 = 4 := by
  have a := h.access
  have hv0 := h.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers])
  have hv10 := h.header (j := 10) (v := p.rp + BitVec.ofNat 64 used) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  have hv12 := h.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.mul_zero, BitVec.add_zero] at hv0
  simp only [Bignum.word, off, Nat.reduceMul] at hv10 hv11 hv12
  have hle := SPub.read_le h
  have hlen := h.input.randLen_lt
  have hkl : k < 2 ^ 64 := by have := h.k_le; have := h.input.attempts_lt; omega_arith
  have e12 : BitVec.ofNat 64 used + BitVec.ofNat 64 (p.read used) =
      BitVec.ofNat 64 (used + p.read used) := by rw [← BitVec.ofNat_add]
  have e10 : p.rp + BitVec.ofNat 64 used + BitVec.ofNat 64 (p.read used) =
      p.rp + BitVec.ofNat 64 (used + p.read used) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have e11 : BitVec.ofNat 64 (p.randLen - used) - BitVec.ofNat 64 (p.read used) =
      BitVec.ofNat 64 (p.randLen - (used + p.read used)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by
      simp only [BitVec.le_def, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]; omega_arith)]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  have e0 := ofNat_pred (Nat.pos_of_ne_zero hk) hkl
  refine WP.mono_syms (WP.keep [.r3, .r4, .r5, .r11, .r12] (Q := fun t =>
    t.mem = writeController s.mem p.control (rejectValues p (used + p.read used) (k - 1))) ?_
      (by decide)) fun t ⟨hm, kt⟩ hy => ?_
  · unfold reject writeController rejectValues
    simp only [List.foldl_cons, List.foldl_nil]
    prun [ldf, stf, h.r31, h10, hv0, hv10, hv11, hv12, e0, e10, e11, e12,
      a.ld0, a.ld 0 (by decide), a.ld 80 (by decide), a.ld 88 (by decide), a.ld 96 (by decide), a.st0, a.st 0 (by decide),
      a.st 80 (by decide), a.st 88 (by decide), a.st 96 (by decide), a.st 112 (by decide), BitVec.add_zero]
    rfl
  have hb := rejectValues_bound p (used + p.read used) (k - 1)
  have hh : Slots t.mem p.control (p.headers (used + p.read used) (k - 1)) := by
    refine headers_after _ hb hm ?_
    intro e he
    simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, rejectValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [SPub.headers])
  refine ⟨h.update hle (by have := h.k_le; omega_arith) _ hb (by
      simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) hm kt.mono hh hy, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ hb 14 (by decide)]
  simp only [controllerValue, rejectValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

/-! ## A tape too short for the candidate -/

def requestValues (p : SPub) (used : Nat) : List (Nat × BitVec 64) :=
  [(3, BitVec.ofNat 64 (parameterRequest p.bits (p.randLen - used))), (14, 0)]

theorem requestValues_bound (p : SPub) (used : Nat) : ∀ e ∈ requestValues p used, e.1 < 16 := by
  simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> dsimp only <;> decide

/-- The sign of a difference of numbers below `2^63`. -/
theorem sign_sub {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 = BitVec.ofNat 64 (if x < y then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  split <;> omega_arith

theorem sel_max {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x ^^^ BitVec.ofNat 64 y) &&& (0#64 - (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63) ^^^
      BitVec.ofNat 64 x = BitVec.ofNat 64 (max x y) := by
  rw [sign_sub hx hy]
  by_cases h : x < y
  · simp only [h, ↓reduceIte]
    rw [show (0#64 - BitVec.ofNat 64 1) = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.xor_comm (BitVec.ofNat 64 x), BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero,
      Nat.max_eq_right (by omega_arith)]
  · simp only [h, ↓reduceIte]
    rw [show (0#64 - BitVec.ofNat 64 0) = 0#64 by decide, BitVec.and_zero, BitVec.zero_xor,
      Nat.max_eq_left (by omega_arith)]

theorem sel_min {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x ^^^ BitVec.ofNat 64 y) &&& (0#64 - (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63) ^^^
      BitVec.ofNat 64 y = BitVec.ofNat 64 (min x y) := by
  rw [sign_sub hx hy]
  by_cases h : x < y
  · simp only [h, ↓reduceIte]
    rw [show (0#64 - BitVec.ofNat 64 1) = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, Nat.min_eq_left (by omega_arith)]
  · simp only [h, ↓reduceIte]
    rw [show (0#64 - BitVec.ofNat 64 0) = 0#64 by decide, BitVec.and_zero, BitVec.zero_xor,
      Nat.min_eq_right (by omega_arith)]

theorem shl8_ofNat (n : Nat) : (BitVec.ofNat 64 n) <<< 8 = BitVec.ofNat 64 (n * 2 ^ 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod, Nat.mod_mod]

theorem request_value {p : SPub} {original s : State} {used k : Nat} (h : SLive p original used k s) :
    WP isa (.block (request.take 19)) s fun t =>
      (t.gpr .r7 = BitVec.ofNat 64 (parameterRequest p.bits (p.randLen - used)) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r4, .r5, .r6, .r7] s t := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv6 hv11
  have hlen := h.input.len_bounds
  have hl := h.input.len_eq
  have hrl := h.input.randLen_le
  have hb := h.input.bits_bounds
  have hE : parameterEntropy p.bits ≤ 32769 * 1024 := by
    unfold parameterEntropy; omega_arith
  have hA : p.randLen - used ≤ parameterEntropy p.bits := by omega_arith
  have m1 := sel_max (x := p.randLen - used) (y := p.len * 2 ^ 8) (by omega_arith) (by omega_arith)
  have e2 : BitVec.ofNat 64 (max (p.randLen - used) (p.len * 2 ^ 8)) +
      BitVec.ofNat 64 (max (p.randLen - used) (p.len * 2 ^ 8)) =
      BitVec.ofNat 64 (2 * max (p.randLen - used) (p.len * 2 ^ 8)) := by
    rw [← BitVec.ofNat_add, Nat.two_mul]
  have m2 := sel_min (x := 2 * max (p.randLen - used) (p.len * 2 ^ 8)) (y := parameterEntropy p.bits)
    (by omega_arith) (by omega_arith)
  refine WP.keep [.r0, .r3, .r4, .r5, .r6, .r7] ?_ (by decide)
  unfold request sel
  simp only [Bool.false_eq_true, ite_true, ite_false, List.cons_append, List.nil_append, List.take_succ_cons,
    List.take_zero]
  prun [ldf, h.r31, hv2, hv6, hv11, a.ld 16 (by decide), a.ld 48 (by decide), a.ld 88 (by decide),
    shl8_ofNat, m1, e2, m2]
  unfold parameterRequest Entropy.request
  rw [show p.len * 256 = 256 * ((p.bits + 7) / 8) by omega_arith]

theorem search_request {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (hc : p.cand used = none)
    (hshort : ¬parameterEntropy p.bits ≤ p.randLen - used)
    (hout : Spec.Rsa.bytesAt s.mem p.op p.len = List.replicate p.len 0) :
    WP isa (.block request) s (SDone p original (p.tail used k)) := by
  rw [show request = request.take 19 ++ request.drop 19 from (List.take_append_drop _ _).symm,
    WP.block_append_iff]
  refine WP.mono_syms (request_value h) fun v ⟨⟨h7, hmv⟩, kv⟩ hyv => ?_
  have hv := h.keep kv hmv hyv
  have a := hv.access
  refine WP.mono (WP.keep [.r8] (Q := fun t =>
    t.mem = writeController v.mem p.control (requestValues p used)) ?_
      (by decide)) fun t ⟨hm, kt⟩ => ?_
  · unfold request sel writeController requestValues
    simp only [Bool.false_eq_true, ite_true, ite_false, List.cons_append, List.nil_append, List.drop_succ_cons,
      List.drop_zero, List.foldl_cons, List.foldl_nil]
    prun [ldf, stf, hv.r31, h7, a.st 24 (by decide), a.st 112 (by decide)]
    rfl
  rw [SPub.tail_short hk h.rand_length hc, ite_eq_right hshort]
  have hb := requestValues_bound p used
  have hw (j : Nat) (hj : j < 16) : word t.mem p.control (8 * j) =
      controllerValue (requestValues p used) j (word v.mem p.control (8 * j)) := by
    rw [hm, writeController_word _ _ _ hb j hj]
  refine hv.doneWrites _ hb (by
      simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> dsimp only <;> decide) (by
      simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> dsimp only <;> decide) hm (kt.mono) ?_ ?_ ?_ ?_
  · rw [show (96 : Nat) = 8 * 12 from rfl, hw 12 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_false]
    exact hv.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  · rw [show (112 : Nat) = 8 * 14 from rfl, hw 14 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]
    rfl
  · change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
      word t.mem p.control (8 * 3)] = _
    rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]
    rw [hv.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers]),
      hv.header (j := 1) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers]),
      hv.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])]
    rfl
  · unfold SOutput
    rw [hmv]
    exact hout

/-- Whether the tape holds the entropy cap. -/
theorem short_guard {p : SPub} {original s : State} {used k : Nat} (h : SLive p original used k s) :
    WP isa (.block [ldf .r3 11, ldf .r4 2, .sub .r5 .r3 .r4, .lsr .d .r5 .r5 63]) s fun t =>
      (SLive p original used k t ∧ t.mem = s.mem) ∧
        isa.eval (.zero .d .r5) t = some (decide (parameterEntropy p.bits ≤ p.randLen - used)) := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv11
  have hrl := h.input.randLen_le
  have hE : parameterEntropy p.bits < 2 ^ 63 := by
    have := h.input.bits_bounds; unfold parameterEntropy; omega_arith
  have hs := sign_sub (x := p.randLen - used) (y := parameterEntropy p.bits) (by omega_arith) hE
  refine WP.mono_syms (WP.keep [.r3, .r4, .r5] (Q := fun t =>
    isa.eval (.zero .d .r5) t = some (decide (parameterEntropy p.bits ≤ p.randLen - used)) ∧ t.mem = s.mem) ?_
    (by decide)) fun _ ⟨⟨he, hm⟩, k⟩ hy => ⟨⟨h.keep k hm hy, hm⟩, he⟩
  prun [ldf, h.r31, hv2, hv11, a.ld 16 (by decide), a.ld 88 (by decide), hs]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self]
  by_cases hb : p.randLen - used < parameterEntropy p.bits
  · simp only [hb, ↓reduceIte, show ¬parameterEntropy p.bits ≤ p.randLen - used by omega_arith, decide_false]
    decide
  · simp only [hb, ↓reduceIte, show parameterEntropy p.bits ≤ p.randLen - used by omega_arith, decide_true]
    decide

theorem search_short {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (hc : p.cand used = none)
    (hout : Spec.Rsa.bytesAt s.mem p.op p.len = List.replicate p.len 0) :
    WP isa short s (SDone p original (p.tail used k)) := by
  unfold short
  refine WP.seq (WP.mono (short_guard h) fun u ⟨⟨hu, hm⟩, he⟩ => ?_)
  refine WP.ite _ he ?_ ?_
  · intro hs
    have hs' := of_decide_eq_true hs
    rw [SPub.tail_short hk h.rand_length hc, ite_eq_left hs']
    exact search_exhausted hu
  · intro hs
    have hs' := of_decide_eq_false hs
    exact search_request hu hk hc hs' (by rw [hm]; exact hout)

/-! ## The classification -/

/-- Where the candidate at `used` leads: on to the next one after a
rejection, or the end of the search. -/
def SClassified (p : SPub) (original : State) (used k : Nat) (t : State) : Prop :=
  if candidateStatus (p.cand used) = 2 then
    SLive p original (used + p.read used) (k - 1) t ∧ word t.mem p.control 112 = 4
  else SDone p original (p.tail used k) t

theorem test_two {s : State} {st : Nat} (h9 : s.gpr .r9 = BitVec.ofNat 64 st) (hst : st < 3) :
    WP isa (.block [.subi .r12 .r9 2]) s fun t =>
      (isa.eval (.zero .d .r12) t = some (decide (st = 2)) ∧ t.mem = s.mem) ∧ Keep [.r12] s t := by
  refine WP.keep [.r12] ?_ (by decide)
  prun [h9]
  have hb : ∀ st < 3, ((BitVec.ofNat 64 st - BitVec.ofNat 64 2) == 0) = decide (st = 2) := by decide
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, hb st hst]

theorem search_classify {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (hp : CandPost p used s) :
    WP isa classify s (SClassified p original used k) := by
  unfold classify
  refine WP.seq (WP.mono (search_head h hp) fun u ⟨hu, hpu, h9, h10, he⟩ => ?_)
  have hst := status_lt (p.cand used)
  cases hc : p.cand used with
  | none =>
    simp only [hc, candidateStatus] at he h9
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono_syms (test_two h9 (by decide)) fun v ⟨⟨he2, hmv⟩, kv⟩ hyv => ?_)
    refine WP.ite false he2 (fun hf => by cases hf) fun _ => ?_
    have hout := hpu.2.1
    simp only [hc] at hout
    have hs := search_short (hu.keep kv hmv hyv) hk hc (by rw [hmv]; exact hout)
    refine WP.mono hs fun t ht => ?_
    simp only [SClassified, hc, candidateStatus, Nat.reduceEqDiff, ite_false]
    exact ht
  | some pair =>
    obtain ⟨value, rest⟩ := pair
    cases value with
    | some q =>
      simp only [hc, candidateStatus] at he h9
      refine WP.ite true he (fun _ => ?_) (fun hf => by cases hf)
      refine WP.mono (search_accept hu hpu hk hc h10) fun t ht => ?_
      simp only [SClassified, hc, candidateStatus, Nat.reduceEqDiff, ite_false]
      exact ht
    | none =>
      simp only [hc, candidateStatus] at he h9
      refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
      refine WP.seq (WP.mono_syms (test_two h9 (by decide)) fun v ⟨⟨he2, hmv⟩, kv⟩ hyv => ?_)
      refine WP.ite true he2 (fun _ => ?_) (fun hf => by cases hf)
      have hv := hu.keep kv hmv hyv
      refine WP.mono (search_reject hv hk ((kv.gpr .r10 (by decide)).trans h10)) fun t ht => ?_
      simp only [SClassified, hc, candidateStatus, ite_true]
      exact ht

end VG.Proof.Ffdh.PPC64LE.Generation

end

end

/-! # Total correctness of the parameter search's loop (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Impl.Ffdh.PPC64LE.Generation.Search

theorem ofNat_beq_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h]
  exact Iff.rfl

/-- The attempts left compared with zero. -/
theorem attempts_guard {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa (.block [ldf .r9 0]) s fun t =>
      SLive p original used k t ∧ isa.eval (.zero .d .r9) t = some (decide (k = 0)) := by
  have a := h.access
  have hw := h.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.mul_zero, BitVec.add_zero] at hw
  have hk : k < 2 ^ 64 := by have := h.k_le; have := h.input.attempts_lt; omega_arith
  refine WP.mono_syms (WP.keep [.r9] (Q := fun t =>
    isa.eval (.zero .d .r9) t = some (decide (k = 0)) ∧ t.mem = s.mem) ?_ (by decide))
    fun _ ⟨⟨he, hm⟩, kt⟩ hy => ⟨h.keep kt hm hy, he⟩
  prun [ldf, h.r31, hw, a.ld 0 (by decide), a.ld0, BitVec.add_zero]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, ofNat_beq_zero hk]

/-- The status word, minus 4. -/
theorem status_guard {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .r31 = B) {st : Nat}
    (hs : word s.mem B 112 = BitVec.ofNat 64 st) (hst : st < 5) :
    WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) s fun t =>
      (isa.eval (.zero .d .r9) t = some (decide (st = 4)) ∧ t.mem = s.mem) ∧ Keep [.r9] s t := by
  simp only [Bignum.word, off] at hs
  refine WP.keep [.r9] ?_ (by decide)
  prun [ldf, hb, hs, a.ld 112 (by decide)]
  have : ∀ st < 5, ((BitVec.ofNat 64 st - BitVec.ofNat 64 4) == 0) = decide (st = 4) := by decide
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, this st hst]

theorem result_status_lt (r : ParameterSearchResult) : r.status < 5 := by
  unfold ParameterSearchResult.status; split <;> decide

theorem result_status_ne (r : ParameterSearchResult) : r.status ≠ 4 := by
  unfold ParameterSearchResult.status; split <;> decide

theorem done_loop_guard {p : SPub} {original s : State} {r : ParameterSearchResult}
    (h : SDone p original r s) :
    WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) s fun t =>
      isa.eval (.zero .d .r9) t = some false ∧ SDone p original r t := by
  have a := CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)
  refine WP.mono (status_guard a h.r31 h.status (result_status_lt r)) fun t ⟨⟨he, hm⟩, k⟩ =>
    ⟨?_, h.keep k hm⟩
  rw [he, decide_eq_false (result_status_ne r)]

theorem live_loop_guard {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) s fun t =>
      isa.eval (.zero .d .r9) t = some true ∧ SLive p original used k t :=
  WP.mono_syms (status_guard (st := 4) h.access h.r31 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k⟩ hy => ⟨he, h.keep k hm hy⟩

/-- The loop's state: the search from octet `used`, with `k` attempts left,
leads to the expected result. -/
def SInvariant (p : SPub) (original : State) (expected : ParameterSearchResult) (n : Nat) (s : State) :
    Prop :=
  ∃ used k, n = k + 1 ∧ SLive p original used k s ∧ expected = p.tail used k

theorem search_iteration (c : Cand) {p : SPub} {original s : State}
    {expected : ParameterSearchResult} {n : Nat}
    (h : SInvariant p original expected n s) :
    WP isa (iteration c.call) s fun t =>
      (isa.eval (.zero .d .r9) t = some false ∧ SDone p original expected t) ∨
      (isa.eval (.zero .d .r9) t = some true ∧ ∃ m < n, SInvariant p original expected m t) := by
  obtain ⟨used, k, hn, h, he⟩ := h
  subst he
  have done : ∀ t, SDone p original (p.tail used k) t →
      WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) t fun t =>
        (isa.eval (.zero .d .r9) t = some false ∧ SDone p original (p.tail used k) t) ∨
        (isa.eval (.zero .d .r9) t = some true ∧ ∃ m < n, SInvariant p original (p.tail used k) m t) :=
    fun _ hd => WP.mono (done_loop_guard hd) fun _ ⟨hq, hdq⟩ => Or.inl ⟨hq, hdq⟩
  unfold iteration
  refine WP.seq (WP.mono (attempts_guard h) fun u ⟨hu, he⟩ => ?_)
  apply WP.seq
  refine WP.ite (decide (k = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    subst hz'
    rw [SPub.tail_zero]
    exact WP.mono (search_exhausted hu) fun t ht => done t (by rw [SPub.tail_zero]; exact ht)
  intro hnz
  have hk : k ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (search_candidate_run c hu) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (search_classify ht hk hp) fun q hq => ?_
  unfold SClassified at hq
  split at hq
  · rename_i h2
    obtain ⟨rest, hc⟩ : ∃ rest, p.cand used = some (none, rest) := by
      revert h2
      cases p.cand used with
      | none => intro h2; cases h2
      | some pair =>
        obtain ⟨value, rest⟩ := pair
        cases value with
        | some _ => intro h2; cases h2
        | none => intro _; exact ⟨rest, rfl⟩
    have hr : p.read used = (p.randLen - used) - rest.length := by simp only [SPub.read, hc]
    refine WP.mono (live_loop_guard hq.1 hq.2) fun z ⟨hz, hzl⟩ => Or.inr ⟨hz, _, ?_,
      used + p.read used, k - 1, rfl, hzl, ?_⟩
    · omega_using [hn, hk]
    · rw [hr]; exact SPub.tail_reject hk h.rand_length hc
  · exact done q hq

theorem search_loop (c : Cand) {p : SPub} {original s : State}
    {expected : ParameterSearchResult} {n : Nat}
    (h : SInvariant p original expected n s) :
    WP isa (.loop (iteration c.call) (.zero .d .r9)) s (SDone p original expected) :=
  WP.loop (M := isa) (body := iteration c.call) (c := .zero .d .r9)
    (Q := SDone p original expected) (SInvariant p original expected)
    (fun _ _ h => search_iteration c h) n s h

end VG.Proof.Ffdh.PPC64LE.Generation
