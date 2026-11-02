module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Search.Data
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Correct
import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Init
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.GenerationBounds

/-! # The parameter search's correctness (RISC-V)

As on PPC64LE (`Proof/Ffdh/PPC64LE/Generation/Search/`). In its frame of 16
bytes, the controller passes `vg_ffdh_parameter_candidate` the rest of the
tape, its stack argument at the frame's base (`search_candidate_run`, from
the candidate's contract by `WP.callAny`); the candidate keeps the
controller's state, and leaves its status, p or zeros at `out`, and the
octets it read at `used`. Its status then gives p, the next candidate, or an
exit (`search_classify`). The loop is total by the attempts left
(`search_loop`). The entry stores the arguments in the controller's words
(`entry_ok`); the frame around the loop saves `ra` (`WP.frameRegAny`);
`finish` then stores the octets consumed, returns the status and restores
`s0` (`search_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Generation

open VG VG.RISCV64 VG.Spec.Ffdh VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  writeController_frame_size controllerValue controllerValue_unchanged)
open VG.Proof.Ffdh.RISCV64.KeyGeneration (CtlAccess tmpRegs al8 low32 ofNat_pred)
open VG.Impl.Ffdh.RISCV64.Generation.Search

/-! ## Where the candidate's buffers are

The candidate's buffers are the controller's (`out`, `used`, the tape's rest
and the working space), and its stack argument is at the base of the
candidate's frame, in the `S + 32` bytes of stack below the controller's
stack pointer on entry, which no buffer overlaps; so are the `S` bytes the
candidate may use below its frame. -/

/-- The stack pointer in the candidate's frame. -/
abbrev callSp (p : SPub) : Addr := p.sp - 16 - BitVec.ofNat 64 16

theorem callSp_eq (p : SPub) : callSp p = p.sp - BitVec.ofNat 64 32 := by
  rw [callSp, BitVec.sub_sub]; rfl

/-- The candidate's regions: `out`, `used`, the tape's rest, the working
space, its argument and the stack it may use. -/
abbrev rO (p : SPub) : Region := ⟨p.op, p.len⟩
abbrev rU (p : SPub) : Region := ⟨p.up, 8⟩
abbrev rR (p : SPub) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.randLen - used⟩
abbrev rS (p : SPub) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : SPub) : Region := ⟨callSp p, 8⟩
abbrev rB (p : SPub) : Region := below (callSp p) p.S

theorem rA_sub (p : SPub) : Region.Sub (rA p) (below p.sp (stackUse p.S)) := by
  rw [rA, callSp_eq, stackUse]; exact Offset.sub_below _ (by omega) (by omega)

theorem rB_sub (p : SPub) : Region.Sub (rB p) (below p.sp (stackUse p.S)) := by
  rw [rB, callSp_eq]; exact below_body' p.sp 32 p.S

theorem rA_rB (p : SPub) (h : p.S + 8 ≤ 2 ^ 64) : (rA p).Disjoint (rB p) :=
  Offset.base_disjoint_below (callSp p) (n := p.S) (k := 8) (by omega)

theorem callSp_toNat {p : SPub} (hf : 32 ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 32 := by
  rw [callSp_eq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]

structure CallFacts (p : SPub) (used : Nat) : Prop where
  room : p.S + 32 ≤ p.sp.toNat
  top : p.sp.toNat + 16 ≤ 2 ^ 64
  spal : p.sp.toNat % 16 = 0
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
  ual : p.up.toNat % 8 = 0
  bal : p.B.toNat % 8 = 0

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

theorem SLive.callFacts {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) : CallFacts p used := by
  have hu := h.used_le
  obtain ⟨hpre, hp⟩ := h.input
  generalize hS : p.S = S at hpre hp
  subst hp
  have hroom : used + ((sOfState S original).randLen - used) ≤ (sOfState S original).randLen := by omega
  obtain ⟨hst, hsr, hspal, _, _, hnw, hpw, hwr, hstk, hual, hbal, _, hb1, hb2, hl, hg, hscr, -⟩ := hpre
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pou, pos, -⟩, ⟨pus, -⟩, -⟩ := hpw
  obtain ⟨⟨wor, -⟩, ⟨wur, -⟩, ⟨wsr, -⟩, -⟩ := hwr
  obtain ⟨bo, bu, bs, -, br, -⟩ := hstk
  obtain ⟨no, nu, ns, -, nr, -⟩ := hnw
  have hR : Region.Sub (rR (sOfState S original) used) (inRand original) :=
    Offset.sub_base _ hroom
  have hA := rA_sub (sOfState S original)
  have hB := rB_sub (sOfState S original)
  have hsp' : (sOfState S original).sp = original.sp := rfl
  have hsr' : S + 32 ≤ original.sp.toNat := hsr
  rw [hsp'] at hA hB
  refine ⟨hsr, hst, hspal, pou, wor.sub_right hR, pos, bo.symm.sub_right hA,
    wur.sub_right hR, pus, bu.symm.sub_right hA, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, bo.sub_left hB, bu.sub_left hB, (br.sub_left hB).sub_right hR, bs.sub_left hB,
    (rA_rB _ (by show S + 8 ≤ 2 ^ 64; omega)).symm, no, nu, nowrap_tape nr hroom, ns, ⟨hb1, hb2⟩, hl, hg,
    ?_, ?_, BitVec.isLt _, hual, hbal⟩
  · simp only [sOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]; exact hscr
  · simp only [sOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]

/-! ## The candidate's entry, and its contract there -/

/-- The candidate's entry state: its arguments, its stack pointer and its
regions. -/
structure CandEntry (p : SPub) (used : Nat) (t : State) : Prop where
  a0 : t.gpr .a0 = p.op
  a1 : t.gpr .a1 = BitVec.ofNat 64 p.len
  a2 : t.gpr .a2 = p.up
  a3 : t.gpr .a3 = BitVec.ofNat 64 p.bits
  a4 : t.gpr .a4 = BitVec.ofNat 64 p.gen
  a5 : t.gpr .a5 = p.rp + BitVec.ofNat 64 used
  a6 : t.gpr .a6 = BitVec.ofNat 64 (p.randLen - used)
  a7 : t.gpr .a7 = p.B
  sp : t.sp = callSp p
  arg : stackArg t 0 = BitVec.ofNat 64 (p.Z / 8)
  rd : t.rd = [rR p used, rA p]
  wr : t.wr = [rO p, rU p, rS p]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem gen_setWidth {g : Nat} (h : g = 2 ∨ g = 5) : ((BitVec.ofNat 64 g).setWidth 32).toNat = g := by
  rcases h with rfl | rfl <;> decide

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem cand_pre {p : SPub} {used : Nat} {t : State} (hf : CallFacts p used) (hS : 0 < p.S)
    (ht : CandEntry p used t) : (Proof.Ffdh.parameterCandidateContract abi p.S).pre t := by
  obtain ⟨n, hn⟩ : ∃ n, p.S = n + 1 := ⟨p.S - 1, by omega⟩
  have hb := hf.bits
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := toNat_ofNat_lt (by have := hf.len; omega)
  have hbits : (BitVec.ofNat 64 p.bits).toNat = p.bits := toNat_ofNat_lt (by omega)
  have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := hf.randLen; omega)
  have hzw : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 :=
    toNat_ofNat_lt (by have := hf.ns; omega)
  have hsp := callSp_toNat (p := p) (by have := hf.room; omega)
  have hroom := hf.room
  have htop := hf.top
  have hspal := hf.spal
  have hsa : stackArgAddr t 0 = callSp p := by
    simp only [stackArgAddr, ht.sp, Nat.mul_zero, add_ofNat_zero]
  have hbo := hf.bo
  have hbu := hf.bu
  have hbr := hf.br
  have hbs := hf.bs
  have hba := hf.ba
  simp only [rB, below, hn] at hbo hbu hbr hbs hba
  rw [hn]
  sig_pre [Proof.Ffdh.parameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs, stackBelow,
    stackArgs_one, List.append_eq]
  sig_pre [Proof.Ffdh.parameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs, stackBelow,
    stackArgs_one, List.append_eq]
  simp only [ht.a0, ht.a1, ht.a2, ht.a3, ht.a4, ht.a5, ht.a6, ht.a7, ht.sp, ht.arg, ht.rd, ht.wr, hsa,
    hlen, hbits, hrl, hzw, hf.z8, gen_setWidth hf.gen, hsp]
  exact ⟨by omega, by omega, by omega, trivial, trivial, hf.ou, hf.or, hf.os, hf.oa, hf.ur, hf.us, hf.ua, hf.rs, hf.sa,
    hbo, hbu, hbr, hbs, hba, hf.no, hf.nu, hf.nr, hf.ns, hb.1, hb.2, hf.len, hf.gen, hf.scratch, hf.ual,
    hf.bal⟩

/-- What the candidate at `used` leaves: its status, p or zeros at `out`,
and the octets it read at `used`. -/
def CandPost (p : SPub) (used : Nat) (t : State) : Prop :=
  ((t.gpr .a0).setWidth 32).toNat = candidateStatus (p.cand used) ∧
    bytesAt t.mem p.op p.len =
      (match p.cand used with
        | some (some q, _) => i2osp q p.len
        | _ => List.replicate p.len 0) ∧
    wordsAt t.mem p.up 1 = [BitVec.ofNat 64 (p.read used)]

theorem cand_post {p : SPub} {used : Nat} {t t' : State} (hf : CallFacts p used) (ht : CandEntry p used t)
    (hr : bytesAt t.mem (p.rp + BitVec.ofNat 64 used) (p.randLen - used) = p.rand.drop used) {S : Nat}
    (hpost : (Proof.Ffdh.parameterCandidateContract abi S).post t t') : CandPost p used t' := by
  have hb := hf.bits
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := toNat_ofNat_lt (by have := hf.len; omega)
  have hbits : (BitVec.ofNat 64 p.bits).toNat = p.bits := toNat_ofNat_lt (by omega)
  have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := hf.randLen; omega)
  sig_post [Proof.Ffdh.parameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
    stackArgs_one, List.append_eq] at hpost
  simp only [ht.a0, ht.a1, ht.a2, ht.a3, ht.a4, ht.a5, ht.a6, hlen, hbits, hrl, gen_setWidth hf.gen, hr] at hpost
  exact hpost

/-! ## The candidate's call -/

/-- The candidate's stack argument: `scratch_len`, at its frame's base. -/
def callValues (p : SPub) : List (Nat × BitVec 64) := [(0, BitVec.ofNat 64 (p.Z / 8))]

/-- The candidate's register arguments. -/
def SArgs (p : SPub) (used : Nat) (t : State) : Prop :=
  t.gpr .a0 = p.op ∧ t.gpr .a1 = BitVec.ofNat 64 p.len ∧ t.gpr .a2 = p.up ∧
  t.gpr .a3 = BitVec.ofNat 64 p.bits ∧ t.gpr .a4 = BitVec.ofNat 64 p.gen ∧
  t.gpr .a5 = p.rp + BitVec.ofNat 64 used ∧ t.gpr .a6 = BitVec.ofNat 64 (p.randLen - used) ∧
  t.gpr .a7 = p.B

section

variable {p : SPub} {original s : State} {used k : Nat}

theorem SLive.access_alloc (h : SLive p original used k s) : CtlAccess (allocd 16 s) p.control := by
  obtain ⟨⟨B₀, o, L, hm, hb, hL, hL'⟩, hn, ha⟩ := h.input.control_scr (t := s) h.wr
  exact CtlAccess.of_scr ⟨⟨B₀, o, L, List.mem_cons_of_mem _ hm, hb, hL, hL'⟩, hn, ha⟩

theorem allocd_sp (h : SLive p original used k s) : (allocd 16 s).sp = callSp p := by
  show s.sp - BitVec.ofNat 64 16 = _; rw [h.sp]

theorem search_arguments_ok (h : SLive p original used k s) :
    WP isa (.block arguments) (allocd 16 s) fun u =>
      (SArgs p used u ∧ u.mem = writeController (allocd 16 s).mem (callSp p) (callValues p)) ∧
      Keep tmpRegs (allocd 16 s) u ∧ u.sp = (allocd 16 s).sp := by
  have a := h.access_alloc
  have hf := h.callFacts
  have sp' := allocd_sp h
  have hspal : (callSp p).toNat % 16 = 0 := by
    rw [callSp_toNat (by have := hf.room; omega)]; have := hf.spal; have := hf.room; omega
  have hw0 : InRegions (allocd 16 s).wr (callSp p) 8 := by
    refine ⟨⟨s.sp - BitVec.ofNat 64 16, 16⟩, List.mem_cons_self .., ?_⟩
    rw [show s.sp - BitVec.ofNat 64 16 = callSp p from sp']
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  have hv (j : Nat) {v : BitVec 64} (he : (j, v) ∈ p.headers used k) :
      (allocd 16 s).mem.readW (p.control + BitVec.ofNat 64 (8 * j)) 64 = v :=
    h.header he
  have hv5 := hv 5 (v := p.op) (by simp [SPub.headers])
  have hv6 := hv 6 (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  have hv7 := hv 7 (v := p.up) (by simp [SPub.headers])
  have hv8 := hv 8 (v := BitVec.ofNat 64 p.bits) (by simp [SPub.headers])
  have hv9 := hv 9 (v := BitVec.ofNat 64 p.gen) (by simp [SPub.headers])
  have hv10 := hv 10 (v := p.rp + BitVec.ofNat 64 used) (by simp [SPub.headers])
  have hv11 := hv 11 (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  have hv13 := hv 13 (v := p.B) (by simp [SPub.headers])
  have hv15 := hv 15 (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [SPub.headers])
  simp only [Nat.reduceMul] at hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv13 hv15
  have hal0 : (callSp p).toNat % 8 = 0 := by omega
  have s0' : (allocd 16 s).gpr .s0 = p.control := h.s0
  refine KeyGeneration.WP.ctl ?_ (by rfl)
  unfold arguments writeController callValues SArgs
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, s0', sp', exec_addSp (show 0 < 2048 by decide), add_ofNat_zero,
    a.ld 40 (by decide), a.ld 48 (by decide), a.ld 56 (by decide), a.ld 64 (by decide),
    a.ld 72 (by decide), a.ld 80 (by decide), a.ld 88 (by decide), a.ld 104 (by decide), a.ld 120 (by decide),
    a.al 40 (by decide) (by decide), a.al 48 (by decide) (by decide), a.al 56 (by decide) (by decide),
    a.al 64 (by decide) (by decide), a.al 72 (by decide) (by decide), a.al 80 (by decide) (by decide),
    a.al 88 (by decide) (by decide), a.al 104 (by decide) (by decide), a.al 120 (by decide) (by decide),
    hw0, hal0, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv13, hv15]

/-- The regions the candidate reads: the tape's rest and its stack argument;
those it writes: `out`, `used` and the working space. -/
def callRd (p : SPub) (used : Nat) : List Region := [rR p used, rA p]
def callWr (p : SPub) : List Region := [rO p, rU p, rS p]

/-- The callee's entry, as the call makes it. -/
abbrev callState (p : SPub) (used : Nat) (u : State) : State :=
  u.callEntry.withRegions (callRd p used) (callWr p)

theorem call_gpr {u : State} {r : Reg} (hr : r ∉ linkRegs) : (callState p used u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem call_arg {u : State} {m : Mem} (hu : u.sp = callSp p)
    (hm : u.mem = writeController m (callSp p) (callValues p)) :
    stackArg u 0 = BitVec.ofNat 64 (p.Z / 8) := by
  unfold stackArg stackArgAddr
  rw [hu, hm]
  exact writeController_word _ _ _ (by
    simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ rfl; show 0 < 16; decide) 0 (by decide)

theorem call_entry {u : State} {m : Mem} (hu : u.sp = callSp p) (ha : SArgs p used u)
    (hm : u.mem = writeController m (callSp p) (callValues p)) : CandEntry p used (callState p used u) := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  exact ⟨(call_gpr (by decide)).trans r0, (call_gpr (by decide)).trans r1, (call_gpr (by decide)).trans r2,
    (call_gpr (by decide)).trans r3, (call_gpr (by decide)).trans r4, (call_gpr (by decide)).trans r5,
    (call_gpr (by decide)).trans r6, (call_gpr (by decide)).trans r7,
    by simp only [State.withRegions_sp, State.callEntry_sp, hu], call_arg (u := u) hu hm, rfl, rfl⟩

theorem call_covers_writes (h : SLive p original used k s) {u : State}
    (hw : u.wr = (allocd 16 s).wr) : Covers (callWr p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [hw]
  apply List.mem_cons_of_mem
  rw [h.wr, h.input.wr_eq]
  simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · show (⟨p.op, p.len⟩ : Region) ∈ _; rw [← h.input.out_eq]; simp [inWrites]
  · show (⟨p.up, 8⟩ : Region) ∈ _; rw [← h.input.used_eq]; simp [inWrites]
  · show (⟨p.B, p.Z⟩ : Region) ∈ _; rw [← h.input.scr_eq]; simp [inWrites]

theorem call_covers_reads (h : SLive p original used k s)
    {u : State} (hrd : u.rd = (allocd 16 s).rd) (hw : u.wr = (allocd 16 s).wr) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  have hroom : used + (p.randLen - used) ≤ p.randLen := by have := h.used_le; omega
  have e0 := allocd_sp h
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨inRand original, ?_, used, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inRand original ∈ s.rd; rw [h.rd, hi.rd_eq]; simp [inReads])
    · rw [← hi.2]; rfl
    · rw [← hi.2] at hroom ⊢; exact hroom
  · refine ⟨⟨s.sp - BitVec.ofNat 64 16, 16⟩, ?_, 0, ?_, by show 0 + 8 ≤ 16; decide⟩
    · rw [hw]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · show callSp p = s.sp - BitVec.ofNat 64 16 + BitVec.ofNat 64 0
      rw [add_ofNat_zero]; exact e0.symm

/-- What the candidate writes, as the controller sees it. -/
theorem candidate_frame (h : SLive p original used k s) {u t : State} {d : Nat} (hd : d ≤ p.S)
    (hm : u.mem = writeController (allocd 16 s).mem (callSp p) (callValues p))
    (hf : Frame (callWr p ++ [below (callSp p) d]) u.mem t.mem) :
    Frame (callChanges p.S original) s.mem t.mem := by
  have hi := h.input
  have hsp : p.sp = original.sp := hi.sp_eq
  have hroom := hi.sp_room
  have h1 : Frame (callChanges p.S original) (allocd 16 s).mem u.mem := by
    rw [hm]
    apply (writeController_frame_size _ _ (callValues p) (size := 8) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ rfl; show 8 * 0 + 8 ≤ 8; decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨below original.sp (stackUse p.S), by simp [callChanges], ?_⟩
    rw [← hsp]
    exact rA_sub p
  have h2 : Frame (callChanges p.S original) u.mem t.mem := by
    apply hf.sub
    intro r hr
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨inOut original, by simp [callChanges], by rw [hi.out_eq]; exact fun _ h => h⟩
    · exact ⟨inUsed original, by simp [callChanges], by rw [hi.used_eq]; exact fun _ h => h⟩
    · exact ⟨inScr original, by simp [callChanges], by rw [hi.scr_eq]; exact fun _ h => h⟩
    · refine ⟨below original.sp (stackUse p.S), by simp [callChanges], ?_⟩
      rw [← hsp]
      exact fun x hx => rB_sub p x (below_sub hd (by have := p.sp.isLt; omega) x hx)
  exact h1.trans h2

/-- The candidate's view of the tape, at its entry. -/
theorem call_rand (h : SLive p original used k s) {u : State}
    (hm : u.mem = writeController (allocd 16 s).mem (callSp p) (callValues p)) :
    bytesAt u.mem (p.rp + BitVec.ofNat 64 used) (p.randLen - used) = p.rand.drop used := by
  have hfr : Frame (changes p.S original) s.mem u.mem :=
    frame_of_callChanges p.S original (candidate_frame (t := u) (d := 0) h (Nat.zero_le _) hm
      (fun _ _ => rfl))
  have hr := (h.input.random_frame hfr).trans h.random
  have hl := h.rand_length
  rw [← VG.Proof.Dsa.bytesAt_slice _ _ (show used + (p.randLen - used) ≤ p.randLen by
    have := h.used_le; omega), hr, List.take_of_length_le (by simp only [List.length_drop, hl]; omega)]

theorem search_candidate_run (c : Cand) (hS : p.S = c.S) (h : SLive p original used k s) :
    WP isa (candidateRun c.call) s fun t => SLive p original used k t ∧ CandPost p used t := by
  have hf := h.callFacts
  have e0 := allocd_sp h
  have hroom' : 16 ≤ s.sp.toNat := by
    have := hf.room
    have h16 : (p.sp - 16).toNat = p.sp.toNat - 16 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; show 16 ≤ _; omega)]; rfl
    rw [h.sp, h16]
    omega
  have hcs := c.stack
  have hsm := c.small
  unfold candidateRun
  refine WP.alloc (by decide) hroom' ?_
  refine WP.seq (WP.mono (search_arguments_ok h) fun u ⟨⟨ha, hm⟩, k, husp⟩ => ?_)
  have hu : u.sp = callSp p := husp.trans e0
  have he := call_entry hu ha hm
  have hpre : (Proof.Ffdh.parameterCandidateContract abi c.S).pre (callState p used u) := by
    rw [← hS]; exact cand_pre hf (by rw [hS]; exact c.pos) he
  refine WP.callAny (k := Proof.Ffdh.parameterCandidateContract abi c.S) c.verified.1 hpre
    (call_covers_reads h k.2.1 k.2.2) (call_covers_writes h k.2.2) ?_ (by omega)
  intro t hrd hwr hsp hfr hcs' hpost
  refine ⟨?_, ?_⟩
  · -- The loop state, after the frame.
    apply h.restore (show (freed 16 t).rd = s.rd from hrd.trans k.2.1)
      (show (freed 16 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.2.2]; rfl)
    · change t.sp + BitVec.ofNat 64 16 = s.sp
      rw [hsp, husp]
      exact BitVec.sub_add_cancel _ _
    · intro r hr
      exact (hcs' r hr).trans (k.gpr (by revert r hr; decide))
    · rw [hu] at hfr
      exact candidate_frame h (by omega) hm hfr
  · -- The candidate's status and outputs.
    have hp := cand_post hf he (by
      simp only [State.withRegions_mem, State.callEntry_mem]; exact call_rand h hm) hpost
    unfold CandPost at hp ⊢
    simp only [State.withRegions_gpr, State.withRegions_mem] at hp
    exact hp

end

/-! ## After a candidate: p, the next candidate, or an exit -/

theorem status_lt (r : Option (Option Nat × List Byte)) : candidateStatus r < 3 := by
  unfold candidateStatus; split <;> decide

/-- The status `t0` minus `k`, compared with zero. -/
theorem test_ok {s : State} {st k : Nat} (h0 : s.gpr .t0 = BitVec.ofNat 64 st) (hst : st < 3)
    (hk : k = 1 ∨ k = 2) :
    WP isa (.block (test k)) s fun t =>
      (isa.eval (.zero .t1) t = some (decide (st = k)) ∧ t.mem = s.mem) ∧ Keep [.t1] s t ∧ t.sp = s.sp := by
  have hb : ∀ st < 3, ∀ k < 3,
      ((BitVec.ofNat 64 st - BitVec.ofNat 64 k) == 0) = decide (st = k) := by decide
  rcases hk with rfl | rfl <;>
  · refine WP.mono (WP.rdwr (WP.keep [.t1] ?_ (by rfl) rfl)) fun _ ⟨⟨hq, k⟩, _, _, hsp⟩ => ⟨hq, k, hsp⟩
    unfold test
    brun [h0, KeyGeneration.eval_zero', hb st hst 1 (by decide), hb st hst 2 (by decide)]

/-- The status and the octets read, after the candidate. -/
theorem search_head {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hp : CandPost p used s) :
    WP isa (.block (head ++ test 1)) s fun t =>
      SLive p original used k t ∧ CandPost p used t ∧
      t.gpr .t0 = BitVec.ofNat 64 (candidateStatus (p.cand used)) ∧
      t.gpr .t2 = BitVec.ofNat 64 (p.read used) ∧
      isa.eval (.zero .t1) t = some (decide (candidateStatus (p.cand used) = 1)) := by
  have a := h.access
  have hv7 := h.header (j := 7) (v := p.up) (by simp [SPub.headers])
  simp only [Bignum.word, Nat.reduceMul] at hv7
  have hu : InRegions (s.rd ++ s.wr) p.up 8 := by
    obtain ⟨r, hr, hc⟩ := h.input.used_wr h.wr
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hw : s.mem.readW p.up 64 = BitVec.ofNat 64 (p.read used) := by
    have := hp.2.2
    change [word s.mem p.up 0] = _ at this
    simp only [Bignum.word, off, BitVec.add_zero, List.cons.injEq, and_true] at this
    exact this
  have hual := h.input.up_al
  have hst := status_lt (p.cand used)
  have h0 := low32 hp.1
  rw [WP.block_append_iff]
  refine WP.mono (WP.rdwr (WP.keep [.t0, .t2] (Q := fun t =>
    (t.gpr .t0 = BitVec.ofNat 64 (candidateStatus (p.cand used)) ∧
      t.gpr .t2 = BitVec.ofNat 64 (p.read used)) ∧ t.mem = s.mem) ?_ (by rfl) rfl))
    fun v ⟨⟨⟨⟨v0, v2⟩, hmv⟩, kv⟩, _, _, hspv⟩ => ?_
  · unfold head
    brun [ldf, h.s0, hv7, a.ld 56 (by decide), a.al 56 (by decide) (by decide), hu, hw, hual, h0,
      add_ofNat_zero]
  refine WP.mono (test_ok v0 hst (.inl rfl)) fun t ⟨⟨he, hmt⟩, kt, hspt⟩ => ?_
  have hpv : CandPost p used t := by
    unfold CandPost at hp ⊢
    rw [hmt, hmv, (kt.gpr (by decide)).trans (kv.gpr (by decide))]
    exact hp
  exact ⟨(h.keep kv hspv hmv).keep kt hspt hmt, hpv, (kt.gpr (by decide)).trans v0,
    (kt.gpr (by decide)).trans v2, he⟩

/-! ### An accepted candidate -/

def acceptValues (used : Nat) : List (Nat × BitVec 64) :=
  (12, BitVec.ofNat 64 used) :: terminalValues 1

theorem acceptValues_bound (used : Nat) : ∀ e ∈ acceptValues used, e.1 < 16 := by
  simp only [acceptValues, terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem search_accept {p : SPub} {original s : State} {used k q : Nat} {rest : List Byte}
    (h : SLive p original used k s) (hp : CandPost p used s) (hk : k ≠ 0)
    (hc : p.cand used = some (some q, rest)) (h2 : s.gpr .t2 = BitVec.ofNat 64 (p.read used)) :
    WP isa (.block accept) s (SDone p original (p.tail used k)) := by
  have a := h.access
  have hv12 := h.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  simp only [Bignum.word, Nat.reduceMul] at hv12
  have hn : p.read used = (p.randLen - used) - rest.length := by simp only [SPub.read, hc]
  have e12 : BitVec.ofNat 64 used + BitVec.ofNat 64 (p.read used) =
      BitVec.ofNat 64 (used + ((p.randLen - used) - rest.length)) := by
    rw [hn, ← BitVec.ofNat_add]
  rw [SPub.tail_accept hk h.rand_length hc]
  refine WP.mono (KeyGeneration.WP.ctl (Q := fun t =>
    t.mem = writeController s.mem p.control (acceptValues (used + ((p.randLen - used) - rest.length)))) ?_
      (by rfl)) fun t ⟨hm, kt, _⟩ => ?_
  · unfold accept terminal writeController acceptValues terminalValues
    simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.s0, h2, hv12, e12, a.ld 96 (by decide), a.st 96 (by decide),
      a.al 96 (by decide) (by decide), a.st 0 (by decide), a.st 24 (by decide), a.st 112 (by decide),
      a.al 0 (by decide) (by decide), a.al 24 (by decide) (by decide), a.al 112 (by decide) (by decide),
      fin64_exec_li_zero, fin64_exec_li_lit (show 1 < 2048 by decide)]
  have hb := acceptValues_bound (used + ((p.randLen - used) - rest.length))
  have hw (j : Nat) (hj : j < 16) : word t.mem p.control (8 * j) =
      controllerValue (acceptValues (used + ((p.randLen - used) - rest.length))) j
        (word s.mem p.control (8 * j)) := by
    rw [hm, writeController_word _ _ _ hb j hj]
  refine h.doneWrites _ hb (by
      simp only [acceptValues, terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) (by
      simp only [acceptValues, terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) hm kt ?_ ?_ ?_ ?_
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

/-! ### A rejected candidate -/

def rejectValues (p : SPub) (used k : Nat) : List (Nat × BitVec 64) :=
  [(12, BitVec.ofNat 64 used), (10, p.rp + BitVec.ofNat 64 used),
    (11, BitVec.ofNat 64 (p.randLen - used)), (0, BitVec.ofNat 64 k), (14, 4)]

theorem rejectValues_bound (p : SPub) (used k : Nat) : ∀ e ∈ rejectValues p used k, e.1 < 16 := by
  simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem search_reject {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (h2 : s.gpr .t2 = BitVec.ofNat 64 (p.read used)) :
    WP isa (.block reject) s fun t =>
      SLive p original (used + p.read used) (k - 1) t ∧ word t.mem p.control 112 = 4 := by
  have a := h.access
  have hv0 := h.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers])
  have hv10 := h.header (j := 10) (v := p.rp + BitVec.ofNat 64 used) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  have hv12 := h.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  simp only [Bignum.word, Nat.reduceMul] at hv0 hv10 hv11 hv12
  have hle := SPub.read_le h
  have hlen := h.input.randLen_lt
  have hkl : k < 2 ^ 64 := by have := h.k_le; have := h.input.attempts_lt; omega
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
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have e0 := ofNat_pred (Nat.pos_of_ne_zero hk) hkl
  refine WP.mono (KeyGeneration.WP.ctl (Q := fun t =>
    t.mem = writeController s.mem p.control (rejectValues p (used + p.read used) (k - 1))) ?_
      (by rfl)) fun t ⟨hm, kt, hspt⟩ => ?_
  · unfold reject writeController rejectValues
    simp only [List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.s0, h2, hv0, hv10, hv11, hv12, e0, e10, e11, e12,
      a.ld 0 (by decide), a.ld 80 (by decide), a.ld 88 (by decide), a.ld 96 (by decide),
      a.al 0 (by decide) (by decide), a.al 80 (by decide) (by decide), a.al 88 (by decide) (by decide),
      a.al 96 (by decide) (by decide), a.st 0 (by decide), a.st 80 (by decide), a.st 88 (by decide),
      a.st 96 (by decide), a.st 112 (by decide), a.al 112 (by decide) (by decide),
      fin64_exec_li_lit (show 4 < 2048 by decide)]
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
  refine ⟨h.update hle (by have := h.k_le; omega) _ hb (by
      simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) hm kt hspt hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ hb 14 (by decide)]
  simp only [controllerValue, rejectValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

/-! ### A tape too short for the candidate -/

def requestValues (p : SPub) (used : Nat) : List (Nat × BitVec 64) :=
  [(3, BitVec.ofNat 64 (parameterRequest p.bits (p.randLen - used))), (14, 0)]

theorem requestValues_bound (p : SPub) (used : Nat) : ∀ e ∈ requestValues p used, e.1 < 16 := by
  simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> dsimp only <;> decide

/-- `sel d a b false`: the larger of `a` and `b`. -/
theorem sel_max {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b) &&&
        ((if BitVec.ofNat 64 a < BitVec.ofNat 64 b then 1 else 0) - 1#64)) ^^^ BitVec.ofNat 64 b =
      BitVec.ofNat 64 (max a b) := by
  by_cases h : a < b
  · rw [ite_eq_left ((ofNat_lt ha hb).mpr h), show (1 : BitVec 64) - 1#64 = 0#64 by decide, BitVec.and_zero,
      BitVec.zero_xor, Nat.max_eq_right (by omega)]
  · rw [ite_eq_right (fun h' => h ((ofNat_lt ha hb).mp h')), show (0 : BitVec 64) - 1#64 = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, Nat.max_eq_left (by omega)]

/-- `sel d a b true`: the smaller of `a` and `b`. -/
theorem sel_min {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b) &&&
        ((if BitVec.ofNat 64 a < BitVec.ofNat 64 b then 1 else 0) - 1#64)) ^^^ BitVec.ofNat 64 a =
      BitVec.ofNat 64 (min a b) := by
  by_cases h : a < b
  · rw [ite_eq_left ((ofNat_lt ha hb).mpr h), show (1 : BitVec 64) - 1#64 = 0#64 by decide, BitVec.and_zero,
      BitVec.zero_xor, Nat.min_eq_left (by omega)]
  · rw [ite_eq_right (fun h' => h ((ofNat_lt ha hb).mp h')), show (0 : BitVec 64) - 1#64 = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes, BitVec.xor_comm (BitVec.ofNat 64 a), BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero, Nat.min_eq_right (by omega)]

theorem request_ok {p : SPub} {original s : State} {used k : Nat} (h : SLive p original used k s) :
    WP isa (.block request) s fun t =>
      t.mem = writeController s.mem p.control (requestValues p used) ∧ Keep tmpRegs s t ∧ t.sp = s.sp := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  simp only [Bignum.word, Nat.reduceMul] at hv2 hv6 hv11
  have hlen := h.input.len_bounds
  have hl := h.input.len_eq
  have hrl := h.input.randLen_le
  have hE := h.input.entropy_lt
  have hA : p.randLen - used ≤ parameterEntropy p.bits := by omega
  have m1 := sel_max (a := p.randLen - used) (b := p.len * 2 ^ 8) (by omega) (by omega)
  have e2 : BitVec.ofNat 64 (max (p.randLen - used) (p.len * 2 ^ 8)) +
      BitVec.ofNat 64 (max (p.randLen - used) (p.len * 2 ^ 8)) =
      BitVec.ofNat 64 (2 * max (p.randLen - used) (p.len * 2 ^ 8)) := by
    rw [← BitVec.ofNat_add, Nat.two_mul]
  have m2 := sel_min (a := 2 * max (p.randLen - used) (p.len * 2 ^ 8)) (b := parameterEntropy p.bits)
    (by omega) (by omega)
  have hr : min (2 * max (p.randLen - used) (p.len * 2 ^ 8)) (parameterEntropy p.bits) =
      parameterRequest p.bits (p.randLen - used) := by
    unfold parameterRequest
    rw [show p.len * 2 ^ 8 = 256 * ((p.bits + 7) / 8) by omega]
  refine KeyGeneration.WP.ctl ?_ (by rfl)
  unfold request sel writeController requestValues
  simp only [Bool.false_eq_true, ite_true, ite_false, List.cons_append, List.nil_append,
    List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.s0, hv2, hv6, hv11, a.ld 16 (by decide), a.ld 48 (by decide), a.ld 88 (by decide),
    a.al 16 (by decide) (by decide), a.al 48 (by decide) (by decide), a.al 88 (by decide) (by decide),
    a.st 24 (by decide), a.st 112 (by decide), a.al 24 (by decide) (by decide),
    a.al 112 (by decide) (by decide), fin64_exec_li_zero]
  rw [shift_ofNat, m1, e2, m2, hr]

theorem search_request {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (hc : p.cand used = none)
    (hshort : ¬parameterEntropy p.bits ≤ p.randLen - used)
    (hout : bytesAt s.mem p.op p.len = List.replicate p.len 0) :
    WP isa (.block request) s (SDone p original (p.tail used k)) := by
  refine WP.mono (request_ok h) fun t ⟨hm, kt, _⟩ => ?_
  rw [SPub.tail_short hk h.rand_length hc, ite_eq_right hshort]
  have hb := requestValues_bound p used
  have hw (j : Nat) (hj : j < 16) : word t.mem p.control (8 * j) =
      controllerValue (requestValues p used) j (word s.mem p.control (8 * j)) := by
    rw [hm, writeController_word _ _ _ hb j hj]
  refine h.doneWrites _ hb (by
      simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> dsimp only <;> decide) (by
      simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> dsimp only <;> decide) hm kt ?_ ?_ ?_ hout
  · rw [show (96 : Nat) = 8 * 12 from rfl, hw 12 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_false]
    exact h.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  · rw [show (112 : Nat) = 8 * 14 from rfl, hw 14 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]
    rfl
  · change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
      word t.mem p.control (8 * 3)] = _
    rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]
    rw [h.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers]),
      h.header (j := 1) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers]),
      h.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])]
    rfl

/-- Whether the tape is short of the entropy cap: `t0 < t1`. -/
theorem short_guard {p : SPub} {original s : State} {used k : Nat} (h : SLive p original used k s) :
    WP isa (.block [ldf .t0 11, ldf .t1 2]) s fun t =>
      (SLive p original used k t ∧ t.mem = s.mem) ∧
        isa.eval (.ltu .t0 .t1) t = some (decide (p.randLen - used < parameterEntropy p.bits)) := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  simp only [Bignum.word, Nat.reduceMul] at hv2 hv11
  have hr := h.input.randLen_lt
  have hE := h.input.entropy_lt
  have hlt := KeyGeneration.ofNat_lt_ofNat (a := p.randLen - used) (b := parameterEntropy p.bits)
    (by omega) (by omega)
  refine WP.mono (KeyGeneration.WP.ctl (Q := fun t =>
    isa.eval (.ltu .t0 .t1) t = some (decide (p.randLen - used < parameterEntropy p.bits)) ∧ t.mem = s.mem) ?_
    (by rfl)) fun _ ⟨⟨he, hm⟩, k, hsp⟩ => ⟨⟨h.keep k hsp hm, hm⟩, he⟩
  brun [ldf, h.s0, hv2, hv11, a.ld 16 (by decide), a.ld 88 (by decide), a.al 16 (by decide) (by decide),
    a.al 88 (by decide) (by decide), KeyGeneration.eval_ltu, hlt]

theorem search_short {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (hc : p.cand used = none)
    (hout : bytesAt s.mem p.op p.len = List.replicate p.len 0) :
    WP isa short s (SDone p original (p.tail used k)) := by
  unfold short
  refine WP.seq (WP.mono (short_guard h) fun u ⟨⟨hu, hm⟩, he⟩ => ?_)
  refine WP.ite _ he ?_ ?_
  · intro hs
    have hs' := of_decide_eq_true hs
    exact search_request hu hk hc (by omega) (by rw [hm]; exact hout)
  · intro hs
    have hs' := of_decide_eq_false hs
    rw [SPub.tail_short hk h.rand_length hc, ite_eq_left (by omega)]
    exact search_exhausted hu

/-! ### The classification -/

/-- Where the candidate at `used` leads: on to the next one after a
rejection, or the end of the search. -/
def SClassified (p : SPub) (original : State) (used k : Nat) (t : State) : Prop :=
  if candidateStatus (p.cand used) = 2 then
    SLive p original (used + p.read used) (k - 1) t ∧ word t.mem p.control 112 = 4
  else SDone p original (p.tail used k) t

theorem search_classify {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (hp : CandPost p used s) :
    WP isa classify s (SClassified p original used k) := by
  unfold classify
  refine WP.seq (WP.mono (search_head h hp) fun u ⟨hu, hpu, h0, h2, he⟩ => ?_)
  cases hc : p.cand used with
  | none =>
    simp only [hc, candidateStatus] at he h0
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (test_ok h0 (by decide) (.inr rfl)) fun v ⟨⟨he2, hmv⟩, kv, hspv⟩ => ?_)
    refine WP.ite false he2 (fun hf => by cases hf) fun _ => ?_
    have hout := hpu.2.1
    simp only [hc] at hout
    have hs := search_short (hu.keep kv hspv hmv) hk hc (by rw [hmv]; exact hout)
    refine WP.mono hs fun t ht => ?_
    simp only [SClassified, hc, candidateStatus, Nat.reduceEqDiff, ite_false]
    exact ht
  | some pair =>
    obtain ⟨value, rest⟩ := pair
    cases value with
    | some q =>
      simp only [hc, candidateStatus] at he h0
      refine WP.ite true he (fun _ => ?_) (fun hf => by cases hf)
      refine WP.mono (search_accept hu hpu hk hc h2) fun t ht => ?_
      simp only [SClassified, hc, candidateStatus, Nat.reduceEqDiff, ite_false]
      exact ht
    | none =>
      simp only [hc, candidateStatus] at he h0
      refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
      refine WP.seq (WP.mono (test_ok h0 (by decide) (.inr rfl)) fun v ⟨⟨he2, hmv⟩, kv, hspv⟩ => ?_)
      refine WP.ite true he2 (fun _ => ?_) (fun hf => by cases hf)
      have hv := hu.keep kv hspv hmv
      refine WP.mono (search_reject hv hk ((kv.gpr (by decide)).trans h2)) fun t ht => ?_
      simp only [SClassified, hc, candidateStatus, ite_true]
      exact ht

/-! ## The loop -/

/-- The loop's state: the search from octet `used`, with `k` attempts left,
leads to the expected result. -/
def SInvariant (p : SPub) (original : State) (expected : ParameterSearchResult) (n : Nat) (s : State) :
    Prop :=
  ∃ used k, n = k + 1 ∧ SLive p original used k s ∧ expected = p.tail used k

theorem search_iteration (c : Cand) {p : SPub} (hS : p.S = c.S) {original s : State}
    {expected : ParameterSearchResult} {n : Nat}
    (h : SInvariant p original expected n s) :
    WP isa (iteration c.call) s fun t =>
      (isa.eval (.zero .t0) t = some false ∧ SDone p original expected t) ∨
      (isa.eval (.zero .t0) t = some true ∧ ∃ m < n, SInvariant p original expected m t) := by
  obtain ⟨used, k, hn, h, he⟩ := h
  subst he
  have done : ∀ t, SDone p original (p.tail used k) t →
      WP isa (.block [ldf .t0 14, .addi .t0 .t0 (-4)]) t fun t =>
        (isa.eval (.zero .t0) t = some false ∧ SDone p original (p.tail used k) t) ∨
        (isa.eval (.zero .t0) t = some true ∧ ∃ m < n, SInvariant p original (p.tail used k) m t) :=
    fun _ hd => WP.mono (done_loop_guard hd) fun _ ⟨hq, hdq⟩ => Or.inl ⟨hq, hdq⟩
  unfold iteration
  refine WP.seq (WP.mono (attempts_guard h) fun u ⟨hu, he⟩ => ?_)
  apply WP.seq
  refine WP.ite (decide (k = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    subst hz'
    exact WP.mono (search_exhausted hu) fun t ht => done t (by rw [SPub.tail_zero]; exact ht)
  intro hnz
  have hk : k ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (search_candidate_run c hS hu) fun t ⟨ht, hp⟩ => ?_)
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
    · omega
    · rw [hr]; exact SPub.tail_reject hk h.rand_length hc
  · exact done q hq

theorem search_loop (c : Cand) {p : SPub} (hS : p.S = c.S) {original s : State}
    {expected : ParameterSearchResult} {n : Nat}
    (h : SInvariant p original expected n s) :
    WP isa (.loop (iteration c.call) (.zero .t0)) s (SDone p original expected) :=
  WP.loop (M := isa) (body := iteration c.call) (c := .zero .t0)
    (Q := SDone p original expected) (SInvariant p original expected)
    (fun _ _ h => search_iteration c hS h) n s h

/-! ## The entry -/

def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .s0), (5, s.gpr .a0), (6, s.gpr .a1), (7, s.gpr .a2), (8, s.gpr .a3),
    (9, BitVec.ofNat 64 (genGen s)), (10, s.gpr .a5), (11, s.gpr .a6), (12, 0), (13, s.gpr .a7),
    (15, stackArg s 0)]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem input_args {p : SPub} {s : State} (h : SInput p s) (j : Nat) (hj : j < 2) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, List.mem_append_left _ (by rw [h.rd_eq]; simp [inReads]), ?_⟩
  have e : inArgs s = ⟨s.sp, 16⟩ := by simp only [inArgs, stackArgAddr, Nat.mul_zero, add_ofNat_zero]
  rw [e]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- The registers the entry writes. -/
abbrev entryRegs : List Reg := [.t1, .t2, .t3, .t4, .s0]

theorem entry_ok {p : SPub} {s : State} (h : SInput p s) :
    WP isa (.block entry) s fun t =>
      (t.gpr .s0 = p.control ∧ t.mem = writeController s.mem p.control (entryValues s)) ∧
      Keep entryRegs s t ∧ t.sp = s.sp := by
  have a := CtlAccess.of_scr (h.control_scr (t := s) rfl)
  have hc : stackArg s 1 = p.control := congrArg SPub.control h.2
  have hsp : s.sp.toNat % 8 = 0 := by have := h.1.2.2.1; omega
  have v0 : s.mem.readW s.sp 64 = stackArg s 0 := by
    simp only [stackArg, stackArgAddr, Nat.mul_zero, add_ofNat_zero]
  have v1 : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = p.control :=
    (show _ = stackArg s 1 from rfl).trans hc
  have a0 : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa only [Nat.mul_zero, add_ofNat_zero] using input_args h 0 (by decide)
  have a1 := input_args h 1 (by decide)
  simp only [Nat.reduceMul] at a1
  refine WP.mono (WP.rdwr (WP.keep entryRegs ?_ (by rfl) rfl)) fun _ ⟨⟨hq, k⟩, _, _, hsp⟩ => ⟨hq, k, hsp⟩
  unfold entry writeController entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, exec_addSp (show 0 < 2048 by decide), add_ofNat_zero, v0, v1, a0, a1,
    hsp, al8 hsp (d := 8) (by decide), zext32, fin64_exec_li_zero,
    a.st 32 (by decide), a.st 40 (by decide), a.st 48 (by decide),
    a.st 56 (by decide), a.st 64 (by decide), a.st 72 (by decide), a.st 80 (by decide),
    a.st 88 (by decide), a.st 96 (by decide), a.st 104 (by decide), a.st 120 (by decide),
    a.al 32 (by decide) (by decide), a.al 40 (by decide) (by decide), a.al 48 (by decide) (by decide),
    a.al 56 (by decide) (by decide), a.al 64 (by decide) (by decide), a.al 72 (by decide) (by decide),
    a.al 80 (by decide) (by decide), a.al 88 (by decide) (by decide), a.al 96 (by decide) (by decide),
    a.al 104 (by decide) (by decide), a.al 120 (by decide) (by decide)]

private theorem word_zero (m : Mem) (B : Addr) : word m B 0 = m.readW B 64 := by
  simp only [Bignum.word, off, BitVec.add_zero]

theorem entry_headers {p : SPub} {s : State} (h : SInput p s) :
    Slots (writeController s.mem p.control (entryValues s)) p.control (p.headers 0 p.attempts) := by
  have hw1 := h.width_word
  have hw2 := h.entropy_word
  obtain ⟨hpre, hp⟩ := h
  generalize hS : p.S = S at hpre hp
  subst hp
  intro e he
  simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (entryValues_bound s) _ (by dsimp only; decide)] <;>
    simp only [sOfState, controllerValue, entryValues,
      List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.sub_zero, Nat.mul_zero, BitVec.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 8), word_zero]
  · simp only [Bignum.word, off, Nat.reduceMul]
    exact hw1.trans (by simp only [genLen, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  · simp only [Bignum.word, off, Nat.reduceMul]
    exact hw2
  all_goals rfl

/-- The push of the frame saving `ra` writes only below the stack pointer. -/
theorem push_frame (S : Nat) (s : State) (m : Mem) (v : BitVec 64) (hS : S + 32 < 2 ^ 64) :
    Frame (callChanges S s) m (m.write (s.sp - 16 + 8) 8 v) := by
  have e : s.sp - 16 + 8 = s.sp - BitVec.ofNat 64 8 := by bv_omega
  have hr : below s.sp (stackUse S) ∈ callChanges S s := by simp [callChanges]
  refine Frame.write (Frame.refl _ _) hr _ ?_
  rw [e, stackUse]; exact Offset.contains_below s.sp (a := 8) (b := S + 32) (by omega) (by omega) hS

theorem search_start {p : SPub} {s t : State} (h : SInput p s)
    (hx : t.gpr .s0 = p.control) (hm : t.mem = writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) (hsp : t.sp = s.sp) :
    SLive p s 0 p.attempts (framed .ra t) := by
  have hf := writeController_frame s.mem p.control (entryValues s) (entryValues_bound s)
  have hf₁ : Frame (changes p.S s) s.mem t.mem := by
    rw [hm]
    exact hf.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inCtl s, by simp [changes, inWrites], by rw [h.ctl_eq]; exact fun _ hi => hi⟩
  have hp := push_frame p.S s t.mem (t.gpr .ra) (by have := h.sp_room; have := p.sp.isLt; omega)
  rw [← hsp] at hp
  have hf₂ : Frame (changes p.S s) s.mem (framed .ra t).mem :=
    hf₁.trans (frame_of_callChanges p.S s hp)
  have hc (j : Nat) (hj : j < 16) : word (framed .ra t).mem p.control (8 * j) = word t.mem p.control (8 * j) :=
    h.control_frame hp j hj
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.2.1, k.2.2, ?_, hx, ?_, ?_, ?_, ?_⟩
  · show t.sp - 16 = p.sp - 16
    rw [hsp, h.sp_eq]
  · intro r hr h0
    exact k.gpr (by revert r hr h0; decide)
  · rw [show (32 : Nat) = 8 * 4 from rfl, hc 4 (by decide), hm,
      writeController_word _ _ _ (entryValues_bound s) 4 (by decide)]
    rfl
  · rw [h.random_frame hf₂, ← h.2]
    rfl
  · intro e he
    rw [hc e.1 (SPub.headers_index he), hm]
    exact entry_headers h e he

/-! ## Returning -/

theorem search_finish_values {p : SPub} {original s : State} {result : ParameterSearchResult}
    (h : SDone p original result s) :
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
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.input.used_disjoint.2)
      (by decide)).trans hx
  refine WP.keep [.t0, .t1, .a0, .s0] ?_ (by rfl) rfl
  unfold finish
  brun [ldf, h.s0, hu, hd, hs, hx', hup, hual, add_ofNat_zero, a.ld 56 (by decide), a.ld 96 (by decide),
    a.ld 112 (by decide), a.ld 32 (by decide), a.al 56 (by decide) (by decide), a.al 96 (by decide) (by decide),
    a.al 112 (by decide) (by decide), a.al 32 (by decide) (by decide)]

/-- What the search returns, for its result. -/
def SReturned (p : SPub) (result : ParameterSearchResult) (t : State) : Prop :=
  ((t.gpr .a0).setWidth 32).toNat = result.status ∧ SOutput p result t.mem ∧
    wordsAt t.mem p.control 4 = p.policy result ∧
    wordsAt t.mem p.up 1 = [BitVec.ofNat 64 result.used]

theorem search_finish {p : SPub} {original s : State} {result : ParameterSearchResult}
    (h : SDone p original result s) :
    WP isa (.block finish) s fun t => SReturned p result t ∧
      (∀ reg ∈ preserved, t.gpr reg = original.gpr reg) ∧ t.sp = s.sp ∧ t.gpr .ra = s.gpr .ra := by
  refine WP.mono (WP.rdwr (search_finish_values h)) fun t ⟨⟨⟨ha, hs0, hm⟩, k⟩, _, _, hsp⟩ => ?_
  have hd := h.input.used_disjoint
  have hk := h.input.len_bounds
  have hf : Frame [⟨p.up, 8⟩] s.mem t.mem := by
    rw [hm]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hb : bytesAt t.mem p.op p.len = bytesAt s.mem p.op p.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd.1)
      (show p.len ≤ 2 ^ 64 by omega) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd.2) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, hsp, k.gpr (by decide)⟩
  · rw [ha]
    have := result_status_lt result
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · have ho := h.output
    unfold SOutput at ho ⊢
    rw [hb]
    exact ho
  · have he : wordsAt t.mem p.control 4 = wordsAt s.mem p.control 4 := by
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

theorem iteration_depth (c : Cand) : sdepth (iteration c.call) ≤ c.S + 16 := by
  have := c.stack
  simp only [iteration, candidateRun, exhausted, zeroOut, classify, short, Impl.Bignum.RISCV64.countLoop,
    sdepth, Cand.call, Instr.frameBytes, Nat.max_le, Nat.zero_le, and_true, true_and]
  omega

/-- After the frame: a finished search, with `ra` and the stack pointer
back. -/
theorem SDone.popped {p : SPub} {original s : State} {r : ParameterSearchResult}
    (h : SDone p original r s) (v sp : BitVec 64) :
    SDone p original r { s.write .ra v with sp := sp } := by
  refine ⟨h.input, h.rd, h.wr, ?_, fun reg hr h0 => ?_, h.savedS0, h.usedPtr, h.used,
    h.status, h.policy, h.output⟩
  · show (s.write .ra v).gpr .s0 = _
    rw [RegUpd.gpr_write, ite_eq_right (by decide)]; exact h.s0
  · show (s.write .ra v).gpr reg = _
    rw [RegUpd.gpr_write, ite_eq_right (fun e => by subst e; exact absurd hr (by decide))]
    exact h.saved reg hr h0

theorem SInput.tail_eq {p : SPub} {s : State} (h : SInput p s) : searchResult s = p.tail 0 p.attempts := by
  obtain ⟨_, hp⟩ := h
  generalize p.S = S at hp
  subst hp
  simp only [searchResult, SPub.tail, sOfState, List.drop_zero, Proof.Ffdh.Generation.consume_zero]

theorem search_body {p : SPub} {s t : State} (c : Cand) (hS : p.S = c.S) (h : SInput p s)
    (hx : t.gpr .s0 = p.control)
    (hm : t.mem = writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) (hsp : t.sp = s.sp) :
    WP isa (search c.call) t fun u =>
      SDone p s (searchResult s) u ∧ u.gpr .ra = s.gpr .ra ∧ u.sp = s.sp := by
  have hl := search_start h hx hm k hsp
  have hroom := h.sp_room
  have hsp' : 16 ≤ t.sp.toNat := by rw [hsp, ← h.sp_eq]; omega
  unfold search
  refine KeyGeneration.WP.frameRegAny (r := .ra)
    (Q := fun u => SDone p s (searchResult s) u ∧ u.gpr .ra = s.gpr .ra ∧ u.sp = s.sp) hsp' ?_ ?_ ?_
  · intro R hR
    rw [k.2.2, h.wr_eq] at hR
    have hd := h.stack_disjoint (r := R) (List.mem_append_left _ hR)
    refine hd.sub_left ?_
    rw [hsp, show s.sp - 16 = s.sp - BitVec.ofNat 64 16 from rfl]
    exact Offset.sub_below s.sp (a := 16) (b := p.S + 32) (by omega) (by unfold stackUse; omega)
  · refine WP.mono (search_loop c hS (expected := searchResult s) (n := p.attempts + 1)
      ⟨0, p.attempts, rfl, hl, h.tail_eq⟩) fun u hu => ⟨hu.popped _ _, ?_, hsp⟩
    show (u.write .ra (t.gpr .ra)).gpr .ra = _
    rw [RegUpd.gpr_write_self, k.gpr (by decide)]
  · show sdepth (iteration c.call) + 16 < 2 ^ 64
    have := iteration_depth c
    have := c.small
    omega

theorem SReturned.post {S : Nat} {s t : State} (h : SReturned (sOfState S s) (searchResult s) t) :
    searchPost s t :=
  ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩

theorem search_correct_ok (c : Cand) {s : State} (h : searchPre c.S s) :
    WP isa (code c.call) s fun t => searchPost s t ∧ abiPreserved s t := by
  let p := sOfState c.S s
  have hp : SInput p s := ⟨h, rfl⟩
  unfold code
  refine WP.seq (WP.mono (entry_ok hp) fun t ⟨⟨hx, hm⟩, k, hsp⟩ => ?_)
  refine WP.seq (WP.mono (search_body c rfl hp hx hm k hsp) fun u ⟨hd, hra, husp⟩ => ?_)
  refine WP.mono (search_finish hd) fun q ⟨hr, hg, hqsp, hqra⟩ => ?_
  exact ⟨hr.post, hg, hqsp.trans husp, hqra.trans hra⟩

theorem search_correct (c : Cand) (s : State) (h : (searchContract c.S).pre s) :
    ∃ tr t, Exec isa (code c.call) s tr t ∧ abiPreserved s t ∧ (searchContract c.S).post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := search_correct_ok c h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.Ffdh.RISCV64.Generation
