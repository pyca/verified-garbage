module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Search
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Data
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Entry

/-! # One candidate of the search (AArch64)

In its frame, the search passes `vg_rsa_keygen_candidate` the rest of the
tape. The candidate's buffers are the search's (`out`, `used`, `e`, `p`, the
tape's rest and the working space), and its three stack arguments are in the
candidate's frame, at `sp - 208` for the search's stack pointer on entry,
which no buffer overlaps. The candidate keeps the search's state, and leaves
its status, its prime or zeros at `out`, and the octets it read at `used`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.RsaKeyGen.AArch64 (candContract candPre candPost candRes args)
open VG.Impl.RsaKeyGen.AArch64.Search

/-- The stack pointer in the candidate's frame. -/
abbrev callSp (p : SearchPublic) : Addr := p.sp - BitVec.ofNat 64 208

theorem callSp_eq (p : SearchPublic) : p.F - 16 - BitVec.ofNat 64 32 = callSp p := by
  rw [SearchPublic.F, BitVec.sub_sub, BitVec.sub_sub]; rfl

/-! ## Where the candidate's buffers are -/

/-- The candidate's regions: its output, `used`, `e`, `p`, the rest of the
tape, the working space and its stack arguments. -/
abbrev rO (p : SearchPublic) : Region := ⟨p.op, p.len⟩
abbrev rU (p : SearchPublic) : Region := ⟨p.up, 8⟩
abbrev rE (p : SearchPublic) : Region := ⟨p.ep, p.elen⟩
abbrev rP (p : SearchPublic) : Region := ⟨p.pp, p.plen⟩
abbrev rR (p : SearchPublic) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.randLen - used⟩
abbrev rS (p : SearchPublic) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : SearchPublic) : Region := ⟨callSp p, 24⟩

structure CallFacts (p : SearchPublic) (used : Nat) : Prop where
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
  len64 : p.len < 2 ^ 64
  plen64 : p.plen < 2 ^ 64
  rand64 : p.randLen < 2 ^ 64

private theorem sub_tape {r : Addr} {n used : Nat} (hu : used ≤ n) :
    Region.Sub ⟨r + BitVec.ofNat 64 used, n - used⟩ ⟨r, n⟩ :=
  Offset.sub_base r (by omega)

private theorem nowrap_tape {r : Addr} {n used : Nat} (hn : r.toNat + n ≤ 2 ^ 64) (hu : used ≤ n) :
    (r + BitVec.ofNat 64 used).toNat + (n - used) ≤ 2 ^ 64 := by
  have hul : used < 2 ^ 64 ∨ n - used = 0 := by omega
  rcases hul with hul | hz
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
    have := Nat.mod_le (r.toNat + used) (2 ^ 64)
    by_cases hz : r.toNat + used < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hz]; omega
    · omega
  · rw [hz, Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _)

theorem rA_sub (p : SearchPublic) : Region.Sub (rA p) (below p.sp stackUse) :=
  Offset.sub_below _ (by decide) (by decide)

theorem SearchLive.callFacts {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) : CallFacts p used := by
  have hi := h.input
  obtain ⟨htop, hsp, _, _, hnw, hpw, hwr, hstk, hlen, he1, he8, hpl, hscr, -, -, -, -⟩ := hi.1
  have hu := h.used_le
  cases hi.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pou, pos, -⟩, ⟨pus, -⟩, -⟩ := hpw
  obtain ⟨⟨woe, wop, wor, -⟩, ⟨wue, wup, wur, -⟩, ⟨wse, wsp, wsr, -⟩, -⟩ := hwr
  obtain ⟨bo, bu, bs, -, -, -, -, -⟩ := hstk
  obtain ⟨no, nu, ns, -, ne, np, nr, -⟩ := hnw
  have hR : Region.Sub (rR (searchOfState original) used) (inRand original) := sub_tape hu
  have hA := rA_sub (searchOfState original)
  have hsp' : (searchOfState original).sp = original.sp := rfl
  rw [hsp'] at hA
  refine ⟨hsp, htop, pou, woe, wop, wor.sub_right hR, pos, bo.symm.sub_right hA,
    wue, wup, wur.sub_right hR, pus, bu.symm.sub_right hA, wse.symm, wsp.symm, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, no, nu, ne, np, nowrap_tape nr hu, ns, hlen, he1, he8, hpl, ?_, ?_,
    BitVec.isLt _, BitVec.isLt _, BitVec.isLt _⟩
  · simp only [searchOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [searchOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]

/-! ## The candidate's arguments -/

/-- The candidate's stack arguments, in its frame. -/
def callValues (p : SearchPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 (p.randLen - used)), (1, p.B), (2, BitVec.ofNat 64 (p.Z / 8))]

theorem callValues_bound (p : SearchPublic) (used : Nat) : ∀ e ∈ callValues p used, e.1 < 20 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The candidate's arguments in registers. -/
def CallRegs (p : SearchPublic) (used : Nat) (t : State) : Prop :=
  t.gpr .x0 = p.op ∧ t.gpr .x1 = BitVec.ofNat 64 p.len ∧ t.gpr .x2 = p.up ∧ t.gpr .x3 = p.ep ∧
    t.gpr .x4 = BitVec.ofNat 64 p.elen ∧ t.gpr .x5 = p.pp ∧ t.gpr .x6 = BitVec.ofNat 64 p.plen ∧
    t.gpr .x7 = p.rp + BitVec.ofNat 64 used

/-- The registers the arguments' block writes. -/
abbrev argRegsW : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x10, .x11, .x12]

theorem SearchLive.frame_ld {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) {t : State} (hw : t.wr = (allocated 32 s).wr) :
    ∀ d, d + 8 ≤ 160 → InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 d) 8 := by
  have scr := h.input.frame_scr h.wr
  intro d hd
  obtain ⟨r, hr, hc⟩ := scr.st hd
  refine ⟨r, List.mem_append_right _ ?_, hc⟩
  rw [hw]
  exact List.mem_cons_of_mem _ hr

theorem alloc_call_sp {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) : (allocated 32 s).sp = callSp p := by
  show s.sp - _ = _
  rw [h.sp, callSp_eq]

theorem search_arguments_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block arguments) (allocated 32 s) fun u =>
      (CallRegs p used u ∧ u.mem = writeFrame s.mem (callSp p) (callValues p used)) ∧
      Keep argRegsW (allocated 32 s) u := by
  have hl := h.frame_ld (t := allocated 32 s) rfl
  have hsp := alloc_call_sp h
  have haw : (allocated 32 s).wr = ⟨callSp p, 32⟩ :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 32, 32⟩ : Region) :: s.wr = _
    rw [h.sp, callSp_eq]
  have hw : ∀ d, d + 8 ≤ 32 → InRegions (allocated 32 s).wr (callSp p + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨⟨callSp p, 32⟩, by rw [haw]; exact List.mem_cons_self .., Offset.contains_base _ hd (by omega)⟩
  have hw0 : InRegions (allocated 32 s).wr (callSp p) 8 := by
    simpa only [BitVec.add_zero] using hw 0 (by decide)
  have hv (j : Nat) (v : BitVec 64) (hj : (j, v) ∈ p.headers used remaining) :
      s.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v := h.headers (j, v) hj
  have hv5 := hv 5 p.op (by simp [SearchPublic.headers])
  have hv6 := hv 6 (BitVec.ofNat 64 p.len) (by simp [SearchPublic.headers])
  have hv7 := hv 7 p.up (by simp [SearchPublic.headers])
  have hv8 := hv 8 p.ep (by simp [SearchPublic.headers])
  have hv9 := hv 9 (BitVec.ofNat 64 p.elen) (by simp [SearchPublic.headers])
  have hv10 := hv 10 p.pp (by simp [SearchPublic.headers])
  have hv11 := hv 11 (BitVec.ofNat 64 p.plen) (by simp [SearchPublic.headers])
  have hv12 := hv 12 (p.rp + BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  have hv13 := hv 13 (BitVec.ofNat 64 (p.randLen - used)) (by simp [SearchPublic.headers])
  have hv14 := hv 14 p.B (by simp [SearchPublic.headers])
  have hv15 := hv 15 (BitVec.ofNat 64 (p.Z / 8)) (by simp [SearchPublic.headers])
  simp only [Nat.reduceMul] at hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15
  have hmem : (allocated 32 s).mem = s.mem := rfl
  have hx19 : (allocated 32 s).gpr .x19 = p.F := h.x19
  refine WP.keep argRegsW ?_ (by decide) (by decide) (by decide +kernel)
  unfold arguments writeFrame callValues CallRegs
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, hsp, hmem, hx19, exec_addSp (show 0 < 4096 by decide),
    hl 40 (by decide), hl 48 (by decide), hl 56 (by decide), hl 64 (by decide), hl 72 (by decide),
    hl 80 (by decide), hl 88 (by decide), hl 96 (by decide), hl 104 (by decide), hl 112 (by decide),
    hl 120 (by decide), hw0, hw 8 (by decide), hw 16 (by decide),
    hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
  simp only [off, Nat.mul_zero, BitVec.add_zero]

/-! ## The candidate's entry -/

/-- The regions the candidate reads, and those it writes. -/
def callReads (p : SearchPublic) (used : Nat) : List Region := [rE p, rP p, rR p used, rA p]
def callWrites (p : SearchPublic) : List Region := [rO p, rU p, rS p]

/-- The callee's entry, as the call makes it. -/
abbrev callState (p : SearchPublic) (used : Nat) (u : State) : State :=
  u.callEntry.withRegions (callReads p used) (callWrites p)

theorem call_gpr {p : SearchPublic} {used : Nat} {u : State} {r : Reg} (hr : r ∉ linkRegs) :
    (callState p used u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem call_stackArg (p : SearchPublic) (used : Nat) (u : State) (j : Nat) :
    stackArg (callState p used u) j = stackArg u j := rfl

theorem call_arg {p : SearchPublic} {used : Nat} {u : State} {m : Mem} (hu : u.sp = callSp p)
    (hm : u.mem = writeFrame m (callSp p) (callValues p used)) (j : Nat) (hj : j < 3) :
    stackArg u j = frameValue (callValues p used) j (word m (callSp p) (8 * j)) := by
  unfold stackArg stackArgAddr
  rw [hu, hm]
  exact writeFrame_word _ _ _ (callValues_bound p used) j (by omega)

theorem call_args {p : SearchPublic} {used : Nat} {u : State} {m : Mem} (hu : u.sp = callSp p)
    (hm : u.mem = writeFrame m (callSp p) (callValues p used)) :
    stackArg u 0 = BitVec.ofNat 64 (p.randLen - used) ∧ stackArg u 1 = p.B ∧
      stackArg u 2 = BitVec.ofNat 64 (p.Z / 8) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [call_arg hu hm 0 (by decide)]; rfl
  · rw [call_arg hu hm 1 (by decide)]; rfl
  · rw [call_arg hu hm 2 (by decide)]; rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem callSp_toNat {p : SearchPublic} (hf : 208 ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 208 := by
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]

/-- The candidate's precondition at its entry. -/
theorem call_cand_pre {p : SearchPublic} {used : Nat} {u : State} {m : Mem} (hf : CallFacts p used)
    (hu : u.sp = callSp p) (ha : CallRegs p used u)
    (hm : u.mem = writeFrame m (callSp p) (callValues p used)) :
    candPre (callState p used u) := by
  obtain ⟨a0, a1, a2⟩ := call_args hu hm
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  have tl := toNat_ofNat_lt hf.len64
  have te : (BitVec.ofNat 64 p.elen).toNat = p.elen := toNat_ofNat_lt (by have := hf.e8; omega)
  have tp := toNat_ofNat_lt hf.plen64
  have tr : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := hf.rand64; omega)
  have tz : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 := toNat_ofNat_lt (by have := hf.nS; omega)
  have hsp := callSp_toNat hf.room
  have hlt := hf.top
  unfold candPre
  simp only [args, call_gpr (by decide : Reg.x0 ∉ linkRegs), call_gpr (by decide : Reg.x1 ∉ linkRegs),
    call_gpr (by decide : Reg.x2 ∉ linkRegs), call_gpr (by decide : Reg.x3 ∉ linkRegs),
    call_gpr (by decide : Reg.x4 ∉ linkRegs), call_gpr (by decide : Reg.x5 ∉ linkRegs),
    call_gpr (by decide : Reg.x6 ∉ linkRegs), call_gpr (by decide : Reg.x7 ∉ linkRegs),
    call_stackArg, a0, a1, a2, r0, r1, r2, r3, r4, r5, r6, r7, tl, te, tp, tr, tz, hf.z8,
    State.withRegions_rd, State.withRegions_wr, stackArgAddr, State.withRegions_sp,
    State.callEntry_sp, hu, Nat.mul_zero, BitVec.add_zero, callReads, callWrites]
  exact ⟨by omega, trivial, trivial, hf.oU, hf.oE, hf.oP, hf.oR, hf.oS, hf.oA, hf.uE, hf.uP, hf.uR, hf.uS,
    hf.uA, hf.eS, hf.pS, hf.rS', hf.sA, hf.nO, hf.nU, hf.nE, hf.nP, hf.nR, hf.nS, hf.len, hf.e1,
    hf.e8, hf.plen, hf.scratch⟩

/-! ## The call -/

section

variable {p : SearchPublic} {original s : State} {used remaining : Nat}

theorem call_covers_writes (h : SearchLive p original used remaining s) {u : State}
    (hw : u.wr = (allocated 32 s).wr) : Covers (callWrites p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [hw]
  apply List.mem_cons_of_mem
  rw [h.wr]
  apply List.mem_cons_of_mem
  have hi := h.input
  rw [hi.1.2.2.2.1]
  cases hi.2
  simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simp [inWrites, inOut, searchOfState]
  · simp [inWrites, inUsed, searchOfState]
  · simp [inWrites, inScr, searchOfState]

theorem call_covers_reads (h : SearchLive p original used remaining s) {u : State}
    (hrd : u.rd = (allocated 32 s).rd) (hw : u.wr = (allocated 32 s).wr) :
    Covers (callReads p used ++ callWrites p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  have hu := h.used_le
  have hrd' := hi.1.2.2.1
  intro r hr
  simp only [callReads, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨inE original, ?_, 0, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inE original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; simp only [BitVec.add_zero]; rfl
    · cases hi.2; simp only [Nat.zero_add]; exact Nat.le_refl _
  · refine ⟨inP original, ?_, 0, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inP original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; simp only [BitVec.add_zero]; rfl
    · cases hi.2; simp only [Nat.zero_add]; exact Nat.le_refl _
  · refine ⟨inRand original, ?_, used, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inRand original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; rfl
    · cases hi.2; simp only [searchOfState, inRand] at hu ⊢; omega
  · refine ⟨⟨callSp p, 32⟩, ?_, 0, ?_, by show 0 + 24 ≤ 32; decide⟩
    · rw [hw, ← alloc_call_sp h]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · rw [BitVec.add_zero]

theorem writeFrame_frame_size (m : Mem) (B : Addr) (values : List (Nat × BitVec 64)) {size : Nat}
    (hsize : size ≤ 2 ^ 64) (hvalues : ∀ e ∈ values, 8 * e.1 + 8 ≤ size) :
    Frame [⟨B, size⟩] m (writeFrame m B values) := by
  induction values generalizing m with
  | nil => exact Frame.refl _ _
  | cons e values ih =>
    have he := hvalues e (List.mem_cons_self ..)
    have hstore : Frame [⟨B, size⟩] m (m.writeW (off B (8 * e.1)) e.2) :=
      Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Offset.contains_base _ he (by omega))
    exact hstore.trans (ih _ (fun x hx => hvalues x (List.mem_cons_of_mem _ hx)))

/-- The stores of the candidate's stack arguments. -/
theorem args_frame (h : SearchLive p original used remaining s) :
    Frame (SearchInput.callChanges original) s.mem (writeFrame s.mem (callSp p) (callValues p used)) := by
  apply (writeFrame_frame_size _ _ (callValues p used) (size := 24) (by decide) (by
    simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨⟨original.sp - BitVec.ofNat 64 stackUse, 48⟩, by simp [SearchInput.callChanges], fun x hx => ?_⟩
  rw [← h.input.sp_eq]
  simp only [Region.Contains] at hx ⊢
  show (x - (p.sp - BitVec.ofNat 64 208)).toNat < 48
  change (x - (p.sp - BitVec.ofNat 64 208)).toNat < 24 at hx
  omega

/-- What the call writes, as the search sees it. -/
theorem call_frame (h : SearchLive p original used remaining s) {u t : State}
    (hm : u.mem = writeFrame s.mem (callSp p) (callValues p used))
    (hf : Frame (callWrites p) u.mem t.mem) :
    Frame (SearchInput.callChanges original) s.mem t.mem := by
  have hi := h.input
  have h1 : Frame (SearchInput.callChanges original) s.mem u.mem := by
    rw [hm]; exact args_frame h
  have h2 : Frame (SearchInput.callChanges original) u.mem t.mem := by
    apply hf.sub
    intro r hr
    cases hi.2
    simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inOut original, by simp [SearchInput.callChanges], by
        simp only [inOut, searchOfState, searchLen]; exact fun _ hi => hi⟩
    · exact ⟨inUsed original, by simp [SearchInput.callChanges], fun _ hi => hi⟩
    · exact ⟨inScr original, by simp [SearchInput.callChanges], fun _ hi => hi⟩
  exact h1.trans h2

end

theorem bytesAt_drop (m : Mem) (P : Addr) (k n : Nat) :
    Spec.Rsa.bytesAt m (P + BitVec.ofNat 64 k) (n - k) = (Spec.Rsa.bytesAt m P n).drop k := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_drop,
    BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The candidate's inputs: `e`, `p` and the rest of the tape. -/
theorem call_inputs {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) {u : State}
    (hm : u.mem = writeFrame s.mem (callSp p) (callValues p used)) :
    Spec.Rsa.bytesAt u.mem p.ep p.elen = p.eB ∧
      Spec.Rsa.bytesAt u.mem p.pp p.plen = searchP original ∧
      Spec.Rsa.bytesAt u.mem (p.rp + BitVec.ofNat 64 used) (p.randLen - used) =
        (searchRand original).drop used := by
  have hf : Frame (SearchInput.changes original) s.mem u.mem := by
    rw [hm]; exact frame_of_callChanges original (args_frame h)
  refine ⟨(h.input.e_frame hf).trans h.e, (h.input.p_frame hf).trans h.other, ?_⟩
  rw [bytesAt_drop, h.input.random_frame hf, h.random]

/-! ## The candidate, run -/

/-- What the candidate at `used` leaves: its status, its prime or zeros, and
the octets it read. -/
def CandPost (p : SearchPublic) (pB rand : List Byte) (used : Nat) (t : State) : Prop :=
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

theorem CandPost.keep {p : SearchPublic} {pB rand : List Byte} {used : Nat} {s t : State}
    (h : CandPost p pB rand used s) (hm : t.mem = s.mem)
    (hr : (t.gpr .x0).setWidth 32 = (s.gpr .x0).setWidth 32) : CandPost p pB rand used t := by
  unfold CandPost at h ⊢
  rw [hm, hr]
  exact h

theorem search_candidate_run (c : Cand) {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (candidateRun c.call) s fun t =>
      SearchLive p original used remaining t ∧ CandPost p (searchP original) (searchRand original) used t := by
  have hf := h.callFacts
  have hroom : 32 ≤ s.sp.toNat := by
    rw [h.sp, F_16, BitVec.toNat_sub_of_le (by
      simp only [BitVec.le_def, BitVec.toNat_ofNat]; have := hf.room; omega)]
    simp only [BitVec.toNat_ofNat]; have := hf.room; omega
  unfold candidateRun
  refine WP.alloc (by decide) hroom ?_
  refine WP.seq (WP.mono (search_arguments_ok h) fun u ⟨⟨ha, hm⟩, k⟩ => ?_)
  have hu : u.sp = callSp p := k.sp.trans (alloc_call_sp h)
  refine WP.callV (k := candContract) c.correct (call_cand_pre hf hu ha hm)
    (call_covers_reads h k.rd k.wr) (call_covers_writes h k.wr) ?_ c.noFrames
  intro t hrd hwr hsp hfr hcs _ hvs hpost
  refine ⟨?_, ?_⟩
  · apply h.restore (show (freed 32 t).rd = s.rd from hrd.trans k.rd)
      (show (freed 32 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.wr]; rfl)
    · change t.sp + BitVec.ofNat 64 32 = s.sp
      rw [hsp, k.sp]
      exact BitVec.sub_add_cancel _ _
    · intro r hr h30
      exact (hcs r hr h30).trans (k.gpr r (by revert r hr; decide))
    · intro r hr
      exact (hvs r hr).trans (k.vcs r hr)
    · exact call_frame h hm hfr
  · obtain ⟨he, hpb, hrand⟩ := call_inputs h hm
    obtain ⟨a0, -, -⟩ := call_args hu hm
    obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
    have tl := toNat_ofNat_lt hf.len64
    have te : (BitVec.ofNat 64 p.elen).toNat = p.elen := toNat_ofNat_lt (by have := hf.e8; omega)
    have tp := toNat_ofNat_lt hf.plen64
    have tr : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
      toNat_ofNat_lt (by have := hf.rand64; omega)
    have hres : candRes (callState p used u) =
        Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) := by
      simp only [candRes, call_gpr (by decide : Reg.x1 ∉ linkRegs), call_gpr (by decide : Reg.x3 ∉ linkRegs),
        call_gpr (by decide : Reg.x4 ∉ linkRegs), call_gpr (by decide : Reg.x5 ∉ linkRegs),
        call_gpr (by decide : Reg.x6 ∉ linkRegs), call_gpr (by decide : Reg.x7 ∉ linkRegs), call_stackArg,
        r1, r3, r4, r5, r6, r7, a0, tl, te, tp, tr, State.withRegions_mem, State.callEntry_mem, he, hpb, hrand]
    have hp := hpost
    simp only [candContract, candPost, hres, call_stackArg, a0, tr, call_gpr (by decide : Reg.x0 ∉ linkRegs),
      call_gpr (by decide : Reg.x1 ∉ linkRegs), call_gpr (by decide : Reg.x2 ∉ linkRegs), r0, r1, r2, tl,
      State.withRegions_gpr, State.withRegions_mem] at hp
    exact hp

end VG.Proof.RsaKeyGen.AArch64.Search
