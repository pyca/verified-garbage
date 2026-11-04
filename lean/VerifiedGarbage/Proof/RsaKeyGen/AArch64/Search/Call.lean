module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Search
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Data
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: it builds in parallel with `Writes`, which `Classify` also imports

/-! # One candidate of the RSA prime search (AArch64)

In its frame, the search passes `vg_rsa_keygen_candidate` the rest of the
tape. The candidate's buffers are the search's (`out`, `used`, `e`, `p`, the
tape's rest and the working space), and its stack arguments are in the
candidate's frame, in the 48 bytes of stack below the search's frame, which
no buffer overlaps. The candidate keeps the search's state, and leaves its
status, its prime or zeros at `out`, and the octets it read at `used`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame_size
  controllerValue)
open VG.Proof.RsaKeyGen.AArch64 (candPre candPost candRes)
open VG.Impl.RsaKeyGen.AArch64.Search

/-- The stack pointer in the candidate's frame. -/
abbrev callSp (p : SPub) : Addr := p.F - 16 - BitVec.ofNat 64 32

theorem callSp_eq (p : SPub) : callSp p = p.sp - BitVec.ofNat 64 208 := by
  simp only [callSp, SPub.F, BitVec.sub_sub]; rfl

/-- The candidate's regions: `out`, `used`, `e`, `p`, the tape's rest, the
working space and its stack arguments. -/
abbrev rO (p : SPub) : Region := ⟨p.op, p.len⟩
abbrev rU (p : SPub) : Region := ⟨p.up, 8⟩
abbrev rE (p : SPub) : Region := ⟨p.ep, p.elen⟩
abbrev rP (p : SPub) : Region := ⟨p.pp, p.plen⟩
abbrev rR (p : SPub) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.randLen - used⟩
abbrev rS (p : SPub) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : SPub) : Region := ⟨callSp p, 24⟩

namespace SInput

variable {p : SPub} {s : State}

theorem e_eq (h : SInput p s) : inE s = ⟨p.ep, p.elen⟩ := by rw [← h.2]; rfl
theorem p_eq (h : SInput p s) : inP s = ⟨p.pp, p.plen⟩ := by rw [← h.2]; rfl
theorem rand_eq (h : SInput p s) : inRand s = ⟨p.rp, p.randLen⟩ := by rw [← h.2]; rfl
theorem scr_eq (h : SInput p s) : inScr s = ⟨p.B, p.Z⟩ := by rw [← h.2]; rfl

end SInput

structure CallFacts (p : SPub) (used : Nat) : Prop where
  room : 208 ≤ p.sp.toNat
  top : p.sp.toNat + 32 ≤ 2 ^ 64
  oU : (rO p).Disjoint (rU p)
  oE : (rO p).Disjoint (rE p)
  oP : (rO p).Disjoint (rP p)
  oR : (rO p).Disjoint (rR p used)
  oS : (rO p).Disjoint (rS p)
  oA : (rO p).Disjoint (rA p)
  uE : (rU p).Disjoint (rE p)
  uP : (rU p).Disjoint (rP p)
  uR : (rU p).Disjoint (rR p used)
  uS : (rU p).Disjoint (rS p)
  uA : (rU p).Disjoint (rA p)
  eS : (rE p).Disjoint (rS p)
  pS : (rP p).Disjoint (rS p)
  rS' : (rR p used).Disjoint (rS p)
  sA : (rS p).Disjoint (rA p)
  nO : p.op.toNat + p.len ≤ 2 ^ 64
  nU : p.up.toNat + 8 ≤ 2 ^ 64
  nE : p.ep.toNat + p.elen ≤ 2 ^ 64
  nP : p.pp.toNat + p.plen ≤ 2 ^ 64
  nR : (p.rp + BitVec.ofNat 64 used).toNat + (p.randLen - used) ≤ 2 ^ 64
  nS : p.B.toNat + p.Z ≤ 2 ^ 64
  len : Spec.RsaKeyGen.primeLenValid p.len
  e1 : 1 ≤ p.elen
  e8 : p.elen ≤ 8
  plen : p.plen = 0 ∨ p.plen = p.len
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
  obtain ⟨htop, hsp, _, _, hnw, hpw, hwr, hstk, hlen, he1, he8, hpl, hscr, -, -, -, -⟩ := hi.1
  cases hi.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pou, pos, -⟩, ⟨pus, -⟩, -⟩ := hpw
  obtain ⟨⟨woe, wop, wor, -⟩, ⟨wue, wup, wur, -⟩, ⟨wse, wsp, wsr, -⟩, -⟩ := hwr
  obtain ⟨bo, bu, bs, -, -, -, -, -⟩ := hstk
  obtain ⟨no, nu, ns, -, ne, np, nr, -⟩ := hnw
  have hR : Region.Sub (rR (sOfState original) used) (inRand original) :=
    Offset.sub_base _ hroom
  have hA := rA_sub (sOfState original)
  have hsp' : (sOfState original).sp = original.sp := rfl
  rw [hsp'] at hA
  refine ⟨by rw [hsp']; exact hsp, by rw [hsp']; exact htop, pou, woe, wop, wor.sub_right hR, pos,
    bo.symm.sub_right hA, wue, wup, wur.sub_right hR, pus, bu.symm.sub_right hA, wse.symm, wsp.symm,
    (wsr.sub_right hR).symm, bs.symm.sub_right hA, no, nu, ne, np, nowrap_tape nr hroom, ns,
    hlen, he1, he8, hpl, ?_, ?_, BitVec.isLt _⟩
  · simp only [sOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [sOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]

/-- The candidate's stack arguments: the tape's rest's length, `scratch` and
`scratch_len`. -/
def callValues (p : SPub) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 (p.randLen - used)), (1, p.B), (2, BitVec.ofNat 64 (p.Z / 8))]

theorem callValues_bound (p : SPub) (used : Nat) : ∀ e ∈ callValues p used, e.1 < 16 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The candidate's register arguments. -/
def SArgs (p : SPub) (used : Nat) (t : State) : Prop :=
  t.gpr .x0 = p.op ∧ t.gpr .x1 = BitVec.ofNat 64 p.len ∧ t.gpr .x2 = p.up ∧
  t.gpr .x3 = p.ep ∧ t.gpr .x4 = BitVec.ofNat 64 p.elen ∧ t.gpr .x5 = p.pp ∧
  t.gpr .x6 = BitVec.ofNat 64 p.plen ∧ t.gpr .x7 = p.rp + BitVec.ofNat 64 used

/-- The registers the arguments' block writes. -/
abbrev argRegsW : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x10, .x11, .x12]

theorem search_arguments_ok {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa (.block arguments) (allocated 32 s) fun u =>
      (SArgs p used u ∧ u.mem = writeController s.mem (callSp p) (callValues p used)) ∧
      Keep argRegsW (allocated 32 s) u := by
  have a := h.access
  have hw : ∀ d, d + 8 ≤ 32 → InRegions (⟨callSp p, 32⟩ :: s.wr) (callSp p + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨⟨callSp p, 32⟩, List.mem_cons_self .., Offset.contains_base (callSp p) hd (by omega)⟩
  have hw0 : InRegions (⟨callSp p, 32⟩ :: s.wr) (callSp p) 8 := by
    simpa only [BitVec.add_zero] using hw 0 (by decide)
  have hl : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ ⟨callSp p, 32⟩ :: s.wr) (p.F + BitVec.ofNat 64 d) 8 :=
    fun d hd => by
      obtain ⟨r, hr, hc⟩ := a.ld d hd
      refine ⟨r, ?_, hc⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv5 := h.header (j := 5) (v := p.op) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  have hv7 := h.header (j := 7) (v := p.up) (by simp [SPub.headers])
  have hv8 := h.header (j := 8) (v := p.ep) (by simp [SPub.headers])
  have hv9 := h.header (j := 9) (v := BitVec.ofNat 64 p.elen) (by simp [SPub.headers])
  have hv10 := h.header (j := 10) (v := p.rp + BitVec.ofNat 64 used) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  have hv13 := h.header (j := 13) (v := p.B) (by simp [SPub.headers])
  have hv15 := h.header (j := 15) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [SPub.headers])
  have hv16 := h.header (j := 16) (v := p.pp) (by simp [SPub.headers])
  have hv17 := h.header (j := 17) (v := BitVec.ofNat 64 p.plen) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv13 hv15 hv16 hv17
  have hcs : s.sp - BitVec.ofNat 64 32 = callSp p := by rw [h.sp]
  refine WP.keep argRegsW ?_ (by decide) (by decide) (by decide +kernel)
  unfold arguments writeController callValues SArgs
  simp only [List.foldl_cons, List.foldl_nil, allocated, hcs]
  brun [ldf, h.x19, exec_addSp (show 0 < 4096 by decide),
    hl 40 (by decide), hl 48 (by decide), hl 56 (by decide), hl 64 (by decide), hl 72 (by decide),
    hl 80 (by decide), hl 88 (by decide), hl 104 (by decide), hl 120 (by decide), hl 128 (by decide),
    hl 136 (by decide), hw0, hw 8 (by decide), hw 16 (by decide),
    hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv13, hv15, hv16, hv17]
  simp only [off, Nat.mul_zero, BitVec.add_zero, Nat.reduceMul]

/-- The regions the candidate reads: `e`, `p`, the tape's rest and its stack
arguments; those it writes: `out`, `used` and the working space. -/
def callRd (p : SPub) (used : Nat) : List Region := [rE p, rP p, rR p used, rA p]
def callWr (p : SPub) : List Region := [rO p, rU p, rS p]

/-- The callee's entry, as the call makes it. -/
abbrev callState (p : SPub) (used : Nat) (u : State) : State :=
  u.callEntry.withRegions (callRd p used) (callWr p)

theorem call_gpr {p : SPub} {used : Nat} {u : State} {r : Reg} (hr : r ∉ linkRegs) :
    (callState p used u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem call_stackArg (p : SPub) (used : Nat) (u : State) (j : Nat) :
    stackArg (callState p used u) j = stackArg u j := rfl

theorem call_args {p : SPub} {used : Nat} {u : State} {m : Mem} (hu : u.sp = callSp p)
    (hm : u.mem = writeController m (callSp p) (callValues p used)) :
    stackArg u 0 = BitVec.ofNat 64 (p.randLen - used) ∧ stackArg u 1 = p.B ∧
      stackArg u 2 = BitVec.ofNat 64 (p.Z / 8) := by
  unfold stackArg stackArgAddr
  rw [hu, hm]
  refine ⟨?_, ?_, ?_⟩
  · have := writeController_word m (callSp p) _ (callValues_bound p used) 0 (by decide)
    simp only [Bignum.word, off, controllerValue, callValues, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceMul] at this ⊢
    exact this
  · have := writeController_word m (callSp p) _ (callValues_bound p used) 1 (by decide)
    simp only [Bignum.word, off, controllerValue, callValues, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceMul] at this ⊢
    exact this
  · have := writeController_word m (callSp p) _ (callValues_bound p used) 2 (by decide)
    simp only [Bignum.word, off, controllerValue, callValues, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceMul] at this ⊢
    exact this

theorem callSp_toNat {p : SPub} (hf : 208 ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 208 := by
  rw [callSp_eq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith)]
  simp only [BitVec.toNat_ofNat]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem CallFacts.len_lt {p : SPub} {used : Nat} (hf : CallFacts p used) : p.len < 2 ^ 64 := by
  have := hf.len; unfold Spec.RsaKeyGen.primeLenValid at this; omega_arith

theorem call_candidate_pre {p : SPub} {used : Nat} {u : State} {m : Mem} (hf : CallFacts p used)
    (hu : u.sp = callSp p) (ha : SArgs p used u)
    (hm : u.mem = writeController m (callSp p) (callValues p used)) :
    candPre (callState p used u) := by
  obtain ⟨a0, a1, a2⟩ := call_args hu hm
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := toNat_ofNat_lt hf.len_lt
  have hel : (BitVec.ofNat 64 p.elen).toNat = p.elen := toNat_ofNat_lt (by have := hf.e8; omega_arith)
  have hpl : (BitVec.ofNat 64 p.plen).toNat = p.plen :=
    toNat_ofNat_lt (by have := hf.plen; have := hf.len_lt; omega_arith)
  have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := hf.randLen; omega_arith)
  have hzw : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 :=
    toNat_ofNat_lt (by have := hf.nS; omega_arith)
  have hsp := callSp_toNat hf.room
  have hlt := p.sp.isLt
  unfold candPre
  simp only [call_gpr (by decide : Reg.x0 ∉ linkRegs), call_gpr (by decide : Reg.x1 ∉ linkRegs),
    call_gpr (by decide : Reg.x2 ∉ linkRegs), call_gpr (by decide : Reg.x3 ∉ linkRegs),
    call_gpr (by decide : Reg.x4 ∉ linkRegs), call_gpr (by decide : Reg.x5 ∉ linkRegs),
    call_gpr (by decide : Reg.x6 ∉ linkRegs), call_gpr (by decide : Reg.x7 ∉ linkRegs),
    call_stackArg, a0, a1, a2, r0, r1, r2, r3, r4, r5, r6, r7, hlen, hel, hpl, hrl, hzw, hf.z8,
    State.withRegions_rd, State.withRegions_wr, VG.Proof.RsaKeyGen.AArch64.args, stackArgAddr,
    State.withRegions_sp, State.callEntry_sp, hu, Nat.mul_zero, BitVec.add_zero, callRd, callWr]
  exact ⟨by omega_arith, trivial, trivial, hf.oU, hf.oE, hf.oP, hf.oR, hf.oS, hf.oA, hf.uE, hf.uP, hf.uR, hf.uS,
    hf.uA, hf.eS, hf.pS, hf.rS', hf.sA, hf.nO, hf.nU, hf.nE, hf.nP, hf.nR, hf.nS, hf.len, hf.e1, hf.e8,
    hf.plen, hf.scratch⟩

/-- What the candidate at `used` leaves: its status, its prime or zeros at
`out`, and the octets it read at `used`. -/
def CandPost (p : SPub) (pB rand : List Byte) (used : Nat) (t : State) : Prop :=
  ((t.gpr .x0).setWidth 32).toNat =
      Spec.RsaKeyGen.candidateStatus (Spec.RsaKeyGen.candidateOp p.len p.eB pB (rand.drop used)) ∧
    Spec.Rsa.bytesAt t.mem p.op p.len =
      (match Spec.RsaKeyGen.candidateOp p.len p.eB pB (rand.drop used) with
        | some (.prime c, _) => Spec.Rsa.i2osp c p.len
        | _ => List.replicate p.len 0) ∧
    Spec.Rsa.wordsAt t.mem p.up 1 =
      [BitVec.ofNat 64 (match Spec.RsaKeyGen.candidateOp p.len p.eB pB (rand.drop used) with
        | some (_, rest) => (p.randLen - used) - rest.length
        | none => 0)]

theorem CandPost.keep {p : SPub} {pB rand : List Byte} {used : Nat} {s t : State}
    (h : CandPost p pB rand used s) (hm : t.mem = s.mem)
    (hr : (t.gpr .x0).setWidth 32 = (s.gpr .x0).setWidth 32) : CandPost p pB rand used t := by
  unfold CandPost at h ⊢
  rw [hm, hr]
  exact h

section

variable {p : SPub} {original s : State} {used k : Nat}

theorem call_covers_writes (h : SLive p original used k s) {u : State}
    (hw : u.wr = (allocated 32 s).wr) : Covers (callWr p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [hw]
  apply List.mem_cons_of_mem
  rw [h.wr]
  apply List.mem_cons_of_mem
  rw [h.input.1.2.2.2.1]
  simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · show (⟨p.op, p.len⟩ : Region) ∈ _; rw [← h.input.out_eq]; simp [inWrites]
  · show (⟨p.up, 8⟩ : Region) ∈ _; rw [← h.input.used_eq]; simp [inWrites]
  · show (⟨p.B, p.Z⟩ : Region) ∈ _; rw [← h.input.scr_eq]; simp [inWrites]

theorem call_covers_reads (h : SLive p original used k s)
    {u : State} (hrd : u.rd = (allocated 32 s).rd) (hw : u.wr = (allocated 32 s).wr) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  obtain ⟨-, -, hrd', -⟩ := hi.1
  have hroom : used + (p.randLen - used) ≤ p.randLen := by have := h.used_le; omega_arith
  have hread : ∀ r ∈ inReads original, r ∈ u.rd ++ u.wr := fun r hr => by
    rw [hrd]; exact List.mem_append_left _ (by change r ∈ s.rd; rw [h.rd, hrd']; exact hr)
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨inE original, hread _ (by simp [inReads]), 0, by rw [hi.e_eq, BitVec.add_zero], by
      rw [hi.e_eq]; simp⟩
  · exact ⟨inP original, hread _ (by simp [inReads]), 0, by rw [hi.p_eq, BitVec.add_zero], by
      rw [hi.p_eq]; simp⟩
  · exact ⟨inRand original, hread _ (by simp [inReads]), used, by rw [hi.rand_eq], by
      rw [hi.rand_eq]; exact hroom⟩
  · refine ⟨⟨callSp p, 32⟩, ?_, 0, ?_, by show 0 + 24 ≤ 32; decide⟩
    · rw [hw]; refine List.mem_append_right _ ?_
      show _ ∈ (⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr)
      rw [h.sp]; exact List.mem_cons_self ..
    · rw [BitVec.add_zero]

/-- What the candidate writes, as the search sees it. -/
theorem candidate_frame (h : SLive p original used k s) {u t : State}
    (hm : u.mem = writeController s.mem (callSp p) (callValues p used))
    (hf : Frame (callWr p) u.mem t.mem) :
    Frame (SInput.callChanges original) s.mem t.mem := by
  have hi := h.input
  have hsp : p.sp = original.sp := hi.sp_eq
  have h1 : Frame (SInput.callChanges original) s.mem u.mem := by
    rw [hm]
    apply (writeController_frame_size _ _ (callValues p used) (size := 24) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨⟨original.sp - BitVec.ofNat 64 stackUse, 48⟩, by simp [SInput.callChanges], ?_⟩
    rw [← hsp, callSp_eq]
    show Region.Sub ⟨p.sp - BitVec.ofNat 64 208, 24⟩ ⟨p.sp - BitVec.ofNat 64 208, 48⟩
    exact fun _ hi => by simp only [Region.Contains] at hi ⊢; omega
  have h2 : Frame (SInput.callChanges original) u.mem t.mem := by
    apply hf.sub
    intro r hr
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inOut original, by simp [SInput.callChanges], by rw [hi.out_eq]; exact fun _ h => h⟩
    · exact ⟨inUsed original, by simp [SInput.callChanges], by rw [hi.used_eq]; exact fun _ h => h⟩
    · exact ⟨inScr original, by simp [SInput.callChanges], by rw [hi.scr_eq]; exact fun _ h => h⟩
  exact h1.trans h2

/-- The candidate's view of `e`, `p` and the tape, at its entry. -/
theorem call_inputs (h : SLive p original used k s) {u : State}
    (hm : u.mem = writeController s.mem (callSp p) (callValues p used)) (ha : SArgs p used u) :
    Spec.Rsa.bytesAt (callState p used u).mem ((callState p used u).gpr .x3)
        ((callState p used u).gpr .x4).toNat = p.eB ∧
      Spec.Rsa.bytesAt (callState p used u).mem ((callState p used u).gpr .x5)
        ((callState p used u).gpr .x6).toNat = searchP original ∧
      Spec.Rsa.bytesAt (callState p used u).mem ((callState p used u).gpr .x7)
        (p.randLen - used) = (searchRand original).drop used := by
  have hf := h.callFacts
  have hfr : Frame (SInput.changes original) s.mem u.mem :=
    frame_of_callChanges original (candidate_frame (t := u) h hm (fun _ _ => rfl))
  have hel : (BitVec.ofNat 64 p.elen).toNat = p.elen := toNat_ofNat_lt (by have := hf.e8; omega_arith)
  have hpl : (BitVec.ofNat 64 p.plen).toNat = p.plen :=
    toNat_ofNat_lt (by have := hf.plen; have := hf.len_lt; omega_arith)
  obtain ⟨-, -, -, r3, r4, r5, r6, r7⟩ := ha
  simp only [call_gpr (by decide : Reg.x3 ∉ linkRegs), call_gpr (by decide : Reg.x4 ∉ linkRegs),
    call_gpr (by decide : Reg.x5 ∉ linkRegs), call_gpr (by decide : Reg.x6 ∉ linkRegs),
    call_gpr (by decide : Reg.x7 ∉ linkRegs), r3, r4, r5, r6, r7, hel, hpl,
    State.withRegions_mem, State.callEntry_mem]
  refine ⟨(h.input.e_frame hfr).trans h.e, (h.input.p_frame hfr).trans h.other, ?_⟩
  have hr := (h.input.random_frame hfr).trans h.random
  have hl := h.rand_length
  rw [← VG.Proof.Dsa.bytesAt_slice _ _ (show used + (p.randLen - used) ≤ p.randLen by
    have := h.used_le; omega_arith), hr, List.take_of_length_le (by simp only [List.length_drop, hl]; omega_arith)]

theorem search_candidate_run (c : Cand) (h : SLive p original used k s) :
    WP isa (candidateRun c.call) s fun t =>
      SLive p original used k t ∧ CandPost p (searchP original) (searchRand original) used t := by
  have hf := h.callFacts
  have hroom' : 32 ≤ s.sp.toNat := by
    have := hf.room
    have h16 : (p.F - 16).toNat = p.sp.toNat - 176 := by
      rw [SPub.F, BitVec.sub_sub, BitVec.toNat_sub_of_le (by
        simp only [BitVec.le_def]; show 176 ≤ p.sp.toNat; omega_arith)]
      rfl
    rw [h.sp, h16]
    omega_arith
  unfold candidateRun
  refine WP.alloc (by decide) hroom' ?_
  refine WP.seq (WP.mono (search_arguments_ok h) fun u ⟨⟨ha, hm⟩, k⟩ => ?_)
  have hu : u.sp = callSp p := by rw [k.sp]; show s.sp - BitVec.ofNat 64 32 = _; rw [h.sp]
  refine WP.callV (k := VG.Proof.RsaKeyGen.AArch64.candContract) c.correct (call_candidate_pre hf hu ha hm)
    (call_covers_reads h k.rd k.wr) (call_covers_writes h k.wr) ?_ c.noFrames
  intro t hrd hwr hsp hfr hcs _ hvs hpost
  refine ⟨?_, ?_⟩
  · -- The loop state, after the frame.
    apply h.restore (show (freed 32 t).rd = s.rd from hrd.trans k.rd)
      (show (freed 32 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.wr]; rfl)
    · change t.sp + BitVec.ofNat 64 32 = s.sp
      rw [hsp, k.sp]
      exact BitVec.sub_add_cancel _ _
    · intro r hr h30
      exact (hcs r hr h30).trans (k.gpr r (by revert r hr; decide))
    · intro r hr
      exact (hvs r hr).trans (k.vcs r hr)
    · exact candidate_frame h hm hfr
  · -- The candidate's status and outputs.
    obtain ⟨he, hpb, hrand⟩ := call_inputs h hm ha
    obtain ⟨a0, -, -⟩ := call_args hu hm
    obtain ⟨r0, r1, r2, -, -, -, -, -⟩ := ha
    have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := toNat_ofNat_lt hf.len_lt
    have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
      toNat_ofNat_lt (by have := hf.randLen; omega_arith)
    have hp := hpost
    simp only [VG.Proof.RsaKeyGen.AArch64.candContract, candPost, candRes,
      call_gpr (by decide : Reg.x0 ∉ linkRegs), call_gpr (by decide : Reg.x1 ∉ linkRegs),
      call_gpr (by decide : Reg.x2 ∉ linkRegs), call_stackArg, a0, hrl, r0, r1, r2, hlen,
      State.withRegions_gpr, State.withRegions_mem] at hp
    simp only [State.withRegions_gpr, State.withRegions_mem] at he hpb hrand
    rw [he, hpb, hrand] at hp
    exact hp

end

end VG.Proof.RsaKeyGen.AArch64.Search
