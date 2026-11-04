module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Search
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Search.Data
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Search.Entry
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-! # One candidate of the search (PPC64LE)

In its frame of 128 bytes, the search passes `vg_rsa_keygen_candidate` the
rest of the tape. The candidate's buffers are the search's (`out`, `used`,
`e`, `p`, the tape's rest and the working space) and the table of trial
division, and its three stack arguments are at offset 96 of the candidate's
frame, at `sp - 272` for the search's stack pointer on entry, which no buffer
overlaps. The candidate keeps the search's state, and leaves its status, its
prime or zeros at `out`, and the octets it read at `used`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.RsaKeyGen.PPC64LE.Cand (CIn TabOk CQ cOp outOf usedOf oL rL)
open VG.Impl.RsaKeyGen.PPC64LE.Search

/-- The stack pointer in the candidate's frame. -/
abbrev callSp (p : SearchPublic) : Addr := p.sp - BitVec.ofNat 64 368

theorem callSp_eq (p : SearchPublic) : p.F - 80 - BitVec.ofNat 64 128 = callSp p := by
  rw [SearchPublic.F, BitVec.sub_sub, BitVec.sub_sub]; rfl

/-! ## Where the candidate's buffers are -/

/-- The candidate's regions: its output, `used`, `e`, `p`, the rest of the
tape, the working space, its stack arguments, and the stack it may use. -/
abbrev rO (p : SearchPublic) : Region := ⟨p.op, p.len⟩
abbrev rU (p : SearchPublic) : Region := ⟨p.up, 8⟩
abbrev rE (p : SearchPublic) : Region := ⟨p.ep, p.elen⟩
abbrev rP (p : SearchPublic) : Region := ⟨p.pp, p.plen⟩
abbrev rR (p : SearchPublic) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.randLen - used⟩
abbrev rS (p : SearchPublic) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : SearchPublic) : Region := ⟨callSp p + BitVec.ofNat 64 96, 24⟩
abbrev rF (p : SearchPublic) : Region := below (callSp p) 400

theorem rA_eq (p : SearchPublic) : callSp p + BitVec.ofNat 64 96 = p.sp - BitVec.ofNat 64 272 :=
  (Offset.sub_ofNat_eq p.sp (by decide : 272 ≤ 368)).symm

theorem rA_sub (p : SearchPublic) : Region.Sub (rA p) (below p.sp stackUse) := by
  rw [rA, rA_eq]; exact Offset.sub_below _ (by decide) (by decide)

theorem rF_sub (p : SearchPublic) : Region.Sub (rF p) (below p.sp stackUse) :=
  below_body' p.sp 368 400

theorem rF_eq (p : SearchPublic) : rF p = ⟨p.sp - BitVec.ofNat 64 768, 400⟩ := by
  simp only [rF, below, callSp, BitVec.sub_sub]; rfl

theorem rF_rA (p : SearchPublic) : (rF p).Disjoint (rA p) :=
  (Offset.disjoint_below (callSp p) (n := 400) (d := 96) (k := 24) (by decide)).symm

structure CallFacts (p : SearchPublic) (used : Nat) : Prop where
  room : stackUse ≤ p.sp.toNat
  top : p.sp.toNat + 128 ≤ 2 ^ 64
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
  Fo : (rF p).Disjoint (rO p)
  Fu : (rF p).Disjoint (rU p)
  Fe : (rF p).Disjoint (rE p)
  Fp : (rF p).Disjoint (rP p)
  Fr : (rF p).Disjoint (rR p used)
  FS : (rF p).Disjoint (rS p)
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

theorem SearchLive.callFacts {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) : CallFacts p used := by
  have hi := h.input
  obtain ⟨htop, hsp, _, _, hnw, hpw, hwr, hstk, hlen, he1, he8, hpl, hscr, -, -, -, -⟩ := hi.base
  have hu := h.used_le
  cases hi.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pou, pos, -⟩, ⟨pus, -⟩, -⟩ := hpw
  obtain ⟨⟨woe, wop, wor, -⟩, ⟨wue, wup, wur, -⟩, ⟨wse, wsp, wsr, -⟩, -⟩ := hwr
  obtain ⟨bo, bu, bs, -, be, bp, br, -⟩ := hstk
  obtain ⟨no, nu, ns, -, ne, np, nr, -⟩ := hnw
  have hR : Region.Sub (rR (searchOfState original) used) (inRand original) := sub_tape hu
  have hA := rA_sub (searchOfState original)
  have hF := rF_sub (searchOfState original)
  have hsp' : (searchOfState original).sp = original.sp := rfl
  rw [hsp'] at hA hF
  refine ⟨hsp, by simp only [stripConsts_sp] at htop; show original.sp.toNat + 128 ≤ _; omega, pou, woe, wop, wor.sub_right hR, pos, bo.symm.sub_right hA,
    wue, wup, wur.sub_right hR, pus, bu.symm.sub_right hA, wse.symm, wsp.symm, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, bo.sub_left hF, bu.sub_left hF, be.sub_left hF, bp.sub_left hF,
    (br.sub_left hF).sub_right hR, bs.sub_left hF, no, nu, ne, np, nowrap_tape nr hu, ns, hlen, he1, he8,
    hpl, ?_, ?_, BitVec.isLt _, BitVec.isLt _, BitVec.isLt _⟩
  · simp only [searchOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [searchOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]

/-! ## The candidate's arguments -/

/-- The candidate's stack arguments, at offset 96 of its frame. -/
def callValues (p : SearchPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 (p.randLen - used)), (1, p.B), (2, BitVec.ofNat 64 (p.Z / 8))]

theorem callValues_bound (p : SearchPublic) (used : Nat) : ∀ e ∈ callValues p used, e.1 < 20 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The candidate's frame, its stack arguments stored. -/
abbrev callMem (p : SearchPublic) (used : Nat) (s : State) : Mem :=
  writeFrame (allocated 128 s).mem (callSp p + BitVec.ofNat 64 96) (callValues p used)

/-- The candidate's arguments in registers. -/
def CallRegs (p : SearchPublic) (used : Nat) (t : State) : Prop :=
  t.gpr .r3 = p.op ∧ t.gpr .r4 = BitVec.ofNat 64 p.len ∧ t.gpr .r5 = p.up ∧ t.gpr .r6 = p.ep ∧
    t.gpr .r7 = BitVec.ofNat 64 p.elen ∧ t.gpr .r8 = p.pp ∧ t.gpr .r9 = BitVec.ofNat 64 p.plen ∧
    t.gpr .r10 = p.rp + BitVec.ofNat 64 used

/-- The registers the arguments' blocks write. -/
abbrev stackArgRegsW : List Reg := [.r9, .r10, .r11, .r12]
abbrev argRegsW : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

theorem SearchLive.frame_ld {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) {t : State} (hw : t.wr = (allocated 128 s).wr) :
    ∀ d, d + 8 ≤ 160 → InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 d) 8 := by
  have scr := h.input.frame_scr h.wr
  intro d hd
  obtain ⟨r, hr, hc⟩ := scr.st hd
  refine ⟨r, List.mem_append_right _ ?_, hc⟩
  rw [hw]
  exact List.mem_cons_of_mem _ hr

theorem alloc_call_sp {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) : (allocated 128 s).sp = callSp p := by
  show s.sp - _ = _
  rw [h.sp, callSp_eq]

theorem alloc_call_wr {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    (allocated 128 s).wr = ⟨callSp p + 32, 96⟩ :: s.wr := by
  show (⟨s.sp - BitVec.ofNat 64 128 + 32, 128 - 32⟩ : Region) :: s.wr = _
  rw [h.sp, callSp_eq]

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

/-- The candidate frame's back chain: below the search's frame. -/
theorem alloc_frame {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    Frame (SearchInput.callChanges original) s.mem (allocated 128 s).mem := by
  have hr : (⟨original.sp - BitVec.ofNat 64 stackUse, 576⟩ : Region) ∈ SearchInput.callChanges original := by
    simp [SearchInput.callChanges]
  refine Frame.write (Frame.refl _ _) hr _ ?_
  rw [h.sp, callSp_eq, ← h.input.sp_eq]
  exact Offset.contains_below p.sp (a := 368) (b := stackUse) (by decide) (by decide) (by decide)

/-- And its stack arguments. -/
theorem alloc_args_frame {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    Frame (SearchInput.callChanges original) s.mem (callMem p used s) := by
  have hr : (⟨original.sp - BitVec.ofNat 64 stackUse, 576⟩ : Region) ∈ SearchInput.callChanges original := by
    simp [SearchInput.callChanges]
  refine (alloc_frame h).trans ((writeFrame_frame_size _ _ (callValues p used) (size := 24) (by decide) (by
    simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide)).sub fun r hr' => ?_)
  obtain rfl := List.mem_singleton.mp hr'
  refine ⟨_, hr, ?_⟩
  rw [rA_eq, ← h.input.sp_eq]
  exact Offset.sub_below p.sp (by decide) (by decide)

/-- The frame's words, through what a candidate call may write. -/
theorem SearchLive.call_word {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) {m : Mem}
    (hf : Frame (SearchInput.callChanges original) s.mem m) {j : Nat} {v : BitVec 64}
    (hj : (j, v) ∈ p.headers used remaining) : m.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v :=
  (h.input.frame_words hf j (SearchPublic.headers_bound _ _ _ _ hj)).trans (h.headers (j, v) hj)

theorem search_stack_arguments_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block stackArguments) (allocated 128 s) fun u =>
      u.mem = callMem p used s ∧ Keep stackArgRegsW (allocated 128 s) u := by
  have hl := h.frame_ld (t := allocated 128 s) rfl
  have hsp := alloc_call_sp h
  have haw := alloc_call_wr h
  have hw : ∀ d, 32 ≤ d → d + 8 ≤ 128 → InRegions (allocated 128 s).wr (callSp p + BitVec.ofNat 64 d) 8 :=
    fun d h1 hd => ⟨⟨callSp p + 32, 96⟩, by rw [haw]; exact List.mem_cons_self .., by
      rw [show callSp p + BitVec.ofNat 64 d = callSp p + 32 + BitVec.ofNat 64 (d - 32) by
        rw [BitVec.add_assoc]
        congr 1
        rw [show d = 32 + (d - 32) by omega, BitVec.ofNat_add, Nat.add_sub_cancel_left]; rfl]
      exact Offset.contains_base _ (by omega) (by omega)⟩
  have hf := alloc_frame h
  have hv13 := h.call_word hf (j := 13) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SearchPublic.headers])
  have hv14 := h.call_word hf (j := 14) (v := p.B) (by simp [SearchPublic.headers])
  have hv15 := h.call_word hf (j := 15) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [SearchPublic.headers])
  simp only [Nat.reduceMul] at hv13 hv14 hv15
  have h31 : (allocated 128 s).gpr .r31 = p.F := h.r31
  have ea : ∀ t : State, exec (.addSp .r12 96) t = some (t.write .r12 (t.sp + BitVec.ofNat 64 96)) := by
    intro t; simp [exec]
  refine WP.keep stackArgRegsW ?_ (by decide)
  unfold stackArguments callMem writeFrame callValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [ldf, ea, hsp, h31, hl 104 (by decide), hl 112 (by decide), hl 120 (by decide), hv13, hv14, hv15,
    hw 96 (by decide) (by decide), hw 104 (by decide) (by decide), hw 112 (by decide) (by decide), off]

theorem search_arguments_ok {p : SearchPublic} {original s u : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hm : u.mem = callMem p used s)
    (ku : Keep stackArgRegsW (allocated 128 s) u) :
    WP isa (.block arguments) u fun v => (CallRegs p used v ∧ v.mem = u.mem) ∧ Keep argRegsW u v := by
  have hl := h.frame_ld (t := u) ku.wr
  have hf := alloc_args_frame h
  rw [← hm] at hf
  have hv (j : Nat) (v : BitVec 64) (hj : (j, v) ∈ p.headers used remaining) :
      u.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v := h.call_word hf hj
  have hv5 := hv 5 p.op (by simp [SearchPublic.headers])
  have hv6 := hv 6 (BitVec.ofNat 64 p.len) (by simp [SearchPublic.headers])
  have hv7 := hv 7 p.up (by simp [SearchPublic.headers])
  have hv8 := hv 8 p.ep (by simp [SearchPublic.headers])
  have hv9 := hv 9 (BitVec.ofNat 64 p.elen) (by simp [SearchPublic.headers])
  have hv10 := hv 10 p.pp (by simp [SearchPublic.headers])
  have hv11 := hv 11 (BitVec.ofNat 64 p.plen) (by simp [SearchPublic.headers])
  have hv12 := hv 12 (p.rp + BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  simp only [Nat.reduceMul] at hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12
  have h31 : u.gpr .r31 = p.F := (ku.gpr .r31 (by decide)).trans h.r31
  refine WP.keep argRegsW ?_ (by decide)
  unfold arguments CallRegs
  prun [ldf, h31, hl 40 (by decide), hl 48 (by decide), hl 56 (by decide), hl 64 (by decide), hl 72 (by decide),
    hl 80 (by decide), hl 88 (by decide), hl 96 (by decide), hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12]

/-! ## The candidate's entry -/

/-- The table's region, at `T`. -/
abbrev rT (T : Addr) : Region := ⟨T, 8 * 1024⟩

/-- The regions the candidate reads, and those it writes. -/
def callReads (p : SearchPublic) (used : Nat) (T : Addr) : List Region := [rE p, rP p, rR p used, rA p, rT T]
def callWrites (p : SearchPublic) : List Region := [rO p, rU p, rS p]

/-- The callee's entry, as the call makes it. -/
abbrev callState (p : SearchPublic) (used : Nat) (T : Addr) (u : State) : State :=
  u.callEntry.withRegions (callReads p used T) (callWrites p)

theorem call_gpr {p : SearchPublic} {used : Nat} {T : Addr} {u : State} {r : Reg} (hr : r ∉ linkRegs) :
    (callState p used T u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem call_stackArg (p : SearchPublic) (used : Nat) (T : Addr) (u : State) (j : Nat) :
    stackArg (callState p used T u) j = stackArg u j := rfl

theorem call_syms (p : SearchPublic) (used : Nat) (T : Addr) (u : State) :
    (callState p used T u).syms = u.syms := rfl

theorem call_args {p : SearchPublic} {used : Nat} {u : State} {m : Mem} (hu : u.sp = callSp p)
    (hm : u.mem = writeFrame m (callSp p + BitVec.ofNat 64 96) (callValues p used)) :
    stackArg u 0 = BitVec.ofNat 64 (p.randLen - used) ∧ stackArg u 1 = p.B ∧
      stackArg u 2 = BitVec.ofNat 64 (p.Z / 8) := by
  have hw (j : Nat) (hj : j < 3) : stackArg u j =
      frameValue (callValues p used) j (word m (callSp p + BitVec.ofNat 64 96) (8 * j)) := by
    unfold stackArg stackArgAddr
    rw [hu, hm, ← writeFrame_word _ _ _ (callValues_bound p used) j (by omega)]
    simp only [word, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 3
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hw 0 (by decide)]; rfl
  · rw [hw 1 (by decide)]; rfl
  · rw [hw 2 (by decide)]; rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem callSp_toNat {p : SearchPublic} (hf : stackUse ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 368 := by
  have h768 : stackUse = 768 := rfl
  rw [h768] at hf
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]

/-- The candidate's precondition at its entry, but the table's. -/
theorem call_cin {p : SearchPublic} {used : Nat} {T : Addr} {u : State} {m : Mem} (hf : CallFacts p used)
    (hu : u.sp = callSp p) (ha : CallRegs p used u)
    (hm : u.mem = writeFrame m (callSp p + BitVec.ofNat 64 96) (callValues p used)) :
    CIn (callState p used T u) := by
  obtain ⟨a0, a1, a2⟩ := call_args hu hm
  obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
  have tl := toNat_ofNat_lt hf.len64
  have te : (BitVec.ofNat 64 p.elen).toNat = p.elen := toNat_ofNat_lt (by have := hf.e8; omega)
  have tp := toNat_ofNat_lt hf.plen64
  have tr : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := hf.rand64; omega)
  have tz : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 := toNat_ofNat_lt (by have := hf.nS; omega)
  have hsp := callSp_toNat hf.room
  have hlt := hf.top
  have hroom := hf.room
  have hsa : stackArgAddr (callState p used T u) 0 = callSp p + BitVec.ofNat 64 96 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hu]
  have hcs : (callState p used T u).sp = callSp p := by
    simp only [State.withRegions_sp, State.callEntry_sp, hu]
  constructor
  all_goals simp only [Cand.cO, Cand.cU, Cand.cE, Cand.cP, Cand.cR, Cand.cS, Cand.cA, Cand.cF,
    call_gpr (by decide : Reg.r3 ∉ linkRegs), call_gpr (by decide : Reg.r4 ∉ linkRegs),
    call_gpr (by decide : Reg.r5 ∉ linkRegs), call_gpr (by decide : Reg.r6 ∉ linkRegs),
    call_gpr (by decide : Reg.r7 ∉ linkRegs), call_gpr (by decide : Reg.r8 ∉ linkRegs),
    call_gpr (by decide : Reg.r9 ∉ linkRegs), call_gpr (by decide : Reg.r10 ∉ linkRegs),
    call_stackArg, a0, a1, a2, r3, r4, r5, r6, r7, r8, r9, r10, tl, te, tp, tr, tz, hf.z8, hsa, hcs,
    State.withRegions_rd, State.withRegions_wr, callReads, callWrites]
  all_goals first
    | (simp only [List.mem_cons, true_or, or_true]; done)
    | rfl
    | omega
    | exact hf.oU | exact hf.oE | exact hf.oP | exact hf.oR | exact hf.oS | exact hf.oA
    | exact hf.uE | exact hf.uP | exact hf.uR | exact hf.uS | exact hf.uA | exact hf.eS
    | exact hf.pS | exact hf.rS' | exact hf.sA | exact hf.Fo | exact hf.Fu | exact hf.Fe
    | exact hf.Fp | exact hf.Fr | exact hf.FS | exact rF_rA p | exact hf.nO | exact hf.nU
    | exact hf.nE | exact hf.nP | exact hf.nR | exact hf.nS | exact hf.len | exact hf.e1
    | exact hf.e8 | exact hf.plen | exact hf.scratch
    | (rw [hsp]; have h768 : stackUse = 768 := rfl; omega)

/-- The table's address. -/
abbrev tabAddr (s : State) : Addr := s.syms Impl.RsaKeyGen.TrialTable32.symbol

/-- The table at the candidate's entry. -/
theorem call_tab {p : SearchPublic} {original s u : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hm : u.mem = callMem p used s) (hy : u.syms = original.syms)
    (hu : u.sp = callSp p) (ha : CallRegs p used u) :
    TabOk (callState p used (tabAddr original) u) := by
  have hi := h.input
  have hc := h.callFacts
  have hf : Frame (SearchInput.changes original) original.mem u.mem := by
    rw [hm]; exact h.tab.trans (frame_of_callChanges original (alloc_args_frame h))
  have hT : (callState p used (tabAddr original) u).syms Impl.RsaKeyGen.TrialTable32.symbol = tabAddr original := by
    rw [call_syms, hy]
  have hF := rF_sub p
  rw [hi.sp_eq] at hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hT]; exact hi.tab_fit
  · rw [hT]; simp [callReads]
  · intro i hi'
    rw [hT]
    exact hi.tab_frame hf i hi'
  · intro ρ hρ
    rw [hT]
    obtain ⟨-, a1, a2⟩ := call_args hu hm
    obtain ⟨r3, r4, r5, -⟩ := ha
    have tl := toNat_ofNat_lt hc.len64
    have tz : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 := toNat_ofNat_lt (by have := hc.nS; omega)
    have hcs : (callState p used (tabAddr original) u).sp = callSp p := by
      simp only [State.withRegions_sp, State.callEntry_sp, hu]
    have hw : ∀ r ∈ inWrites original, (tabR original).Disjoint r :=
      fun r hr => hi.tab_wr (by rw [hi.wr_eq]; exact hr)
    simp only [Cand.cO, Cand.cU, Cand.cS, Cand.cF, call_gpr (by decide : Reg.r3 ∉ linkRegs),
      call_gpr (by decide : Reg.r4 ∉ linkRegs), call_gpr (by decide : Reg.r5 ∉ linkRegs), call_stackArg,
      a1, a2, r3, r4, r5, tl, tz, hc.z8, hcs, List.mem_cons, List.not_mem_nil, or_false] at hρ
    cases hi.2
    rcases hρ with rfl | rfl | rfl | rfl
    · exact hw (inOut original) (by simp [inWrites])
    · exact hw (inUsed original) (by simp [inWrites])
    · exact hw (inScr original) (by simp [inWrites])
    · exact hi.tab_stack.sub_right hF

/-! ## The call -/

section

variable {p : SearchPublic} {original s : State} {used remaining : Nat}

theorem call_covers_writes (h : SearchLive p original used remaining s) {u : State}
    (hw : u.wr = (allocated 128 s).wr) : Covers (callWrites p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [hw]
  apply List.mem_cons_of_mem
  rw [h.wr]
  apply List.mem_cons_of_mem
  have hi := h.input
  rw [hi.wr_eq]
  cases hi.2
  simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simp [inWrites, inOut, searchOfState]
  · simp [inWrites, inUsed, searchOfState]
  · simp [inWrites, inScr, searchOfState]

theorem call_covers_reads (h : SearchLive p original used remaining s) {u : State}
    (hrd : u.rd = (allocated 128 s).rd) (hw : u.wr = (allocated 128 s).wr) :
    Covers (callReads p used (tabAddr original) ++ callWrites p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  have hu := h.used_le
  have hrd' : (allocated 128 s).rd = original.rd := h.rd
  intro r hr
  simp only [callReads, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · refine ⟨inE original, ?_, 0, ?_, ?_⟩
    · rw [hrd, hrd']; exact List.mem_append_left _ (hi.rd_mem (by simp [inReads]))
    · cases hi.2; simp only [BitVec.add_zero]; rfl
    · cases hi.2; simp only [Nat.zero_add]; exact Nat.le_refl _
  · refine ⟨inP original, ?_, 0, ?_, ?_⟩
    · rw [hrd, hrd']; exact List.mem_append_left _ (hi.rd_mem (by simp [inReads]))
    · cases hi.2; simp only [BitVec.add_zero]; rfl
    · cases hi.2; simp only [Nat.zero_add]; exact Nat.le_refl _
  · refine ⟨inRand original, ?_, used, ?_, ?_⟩
    · rw [hrd, hrd']; exact List.mem_append_left _ (hi.rd_mem (by simp [inReads]))
    · cases hi.2; rfl
    · cases hi.2; simp only [searchOfState, inRand] at hu ⊢; omega
  · refine ⟨⟨callSp p + 32, 96⟩, ?_, 64, ?_, by show 64 + 24 ≤ 96; decide⟩
    · rw [hw, alloc_call_wr h]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · show callSp p + BitVec.ofNat 64 96 = callSp p + 32 + BitVec.ofNat 64 64
      rw [BitVec.add_assoc]; rfl
  · refine ⟨tabR original, ?_, 0, ?_, ?_⟩
    · rw [hrd, hrd']; exact List.mem_append_left _ hi.tab_rd
    · simp only [BitVec.add_zero]
    · exact Nat.le_refl _

theorem callChanges_mem (s : State) :
    inOut s ∈ SearchInput.callChanges s ∧ inUsed s ∈ SearchInput.callChanges s ∧
      inScr s ∈ SearchInput.callChanges s ∧
      (⟨s.sp - BitVec.ofNat 64 stackUse, 576⟩ : Region) ∈ SearchInput.callChanges s := by
  simp [SearchInput.callChanges]

/-- What the call writes, as the search sees it. -/
theorem call_frame (h : SearchLive p original used remaining s) {u t : State}
    (hm : u.mem = callMem p used s) (hf : Frame (callWrites p ++ [rF p]) u.mem t.mem) :
    Frame (SearchInput.callChanges original) s.mem t.mem := by
  have hi := h.input
  have h1 : Frame (SearchInput.callChanges original) s.mem u.mem := by
    rw [hm]; exact alloc_args_frame h
  obtain ⟨mo, mu, ms, mf⟩ := callChanges_mem original
  have eo : rO p = inOut original := by rw [← hi.2]; rfl
  have eu : rU p = inUsed original := by rw [← hi.2]; rfl
  have es : rS p = inScr original := by rw [← hi.2]; rfl
  have hF : Region.Sub (rF p) ⟨original.sp - BitVec.ofNat 64 stackUse, 576⟩ := by
    rw [rF_eq, ← hi.sp_eq]; exact Offset.sub_below p.sp (a := 768) (b := 768) (by decide) (by decide)
  have h2 : Frame (SearchInput.callChanges original) u.mem t.mem := by
    apply hf.sub
    intro r hr
    simp only [callWrites, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, mo, by rw [eo]; exact fun _ hi => hi⟩
    · exact ⟨_, mu, by rw [eu]; exact fun _ hi => hi⟩
    · exact ⟨_, ms, by rw [es]; exact fun _ hi => hi⟩
    · exact ⟨_, mf, hF⟩
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
    (h : SearchLive p original used remaining s) {u : State} (hm : u.mem = callMem p used s) :
    Spec.Rsa.bytesAt u.mem p.ep p.elen = p.eB ∧
      Spec.Rsa.bytesAt u.mem p.pp p.plen = searchP original ∧
      Spec.Rsa.bytesAt u.mem (p.rp + BitVec.ofNat 64 used) (p.randLen - used) =
        (searchRand original).drop used := by
  have hf : Frame (SearchInput.changes original) s.mem u.mem := by
    rw [hm]; exact frame_of_callChanges original (alloc_args_frame h)
  refine ⟨(h.input.e_frame hf).trans h.e, (h.input.p_frame hf).trans h.other, ?_⟩
  rw [bytesAt_drop, h.input.random_frame hf, h.random]

/-! ## The candidate, run -/

/-- What the candidate at `used` leaves: its status, its prime or zeros, and
the octets it read. -/
def CandPost (p : SearchPublic) (pB rand : List Byte) (used : Nat) (t : State) : Prop :=
  ((t.gpr .r3).setWidth 32).toNat =
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
    (hr : (t.gpr .r3).setWidth 32 = (s.gpr .r3).setWidth 32) : CandPost p pB rand used t := by
  unfold CandPost at h ⊢
  rw [hm, hr]
  exact h

/-- The candidate's contract, in the terms of its proof. -/
def candK : Contract isa where
  pre s := CIn s ∧ TabOk s
  post s s' := CQ s (s'.gpr .r3) s'.mem
  pub _ _ := True

theorem status_small (r : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand)) :
    Spec.RsaKeyGen.candidateStatus r < 4 := by
  unfold Spec.RsaKeyGen.candidateStatus; split <;> decide

theorem search_candidate_run (c : Cand) {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (candidateRun c.call) s fun t =>
      SearchLive p original used remaining t ∧ CandPost p (searchP original) (searchRand original) used t := by
  have hf := h.callFacts
  have h768 : stackUse = 768 := rfl
  have hroom : 128 ≤ s.sp.toNat := by
    rw [h.sp, SearchPublic.F, BitVec.sub_sub, BitVec.toNat_sub_of_le (by
      simp only [BitVec.le_def]; have := hf.room; show 240 ≤ _; omega)]
    have := hf.room; show 128 ≤ _ - 240; omega
  unfold candidateRun
  refine WP.alloc (by decide) hroom ?_
  refine WP.seq (VG.PPC64LE.WP.mono_syms (search_stack_arguments_ok h) fun u ⟨hm, ku⟩ hyu => ?_)
  refine WP.seq (VG.PPC64LE.WP.mono_syms (search_arguments_ok h hm ku) fun v ⟨⟨ha, hmv⟩, kv⟩ hyv => ?_)
  have hu : v.sp = callSp p := kv.sp.trans (ku.sp.trans (alloc_call_sp h))
  have hm' : v.mem = callMem p used s := hmv.trans hm
  have hy : v.syms = original.syms := hyv.trans (hyu.trans h.syms)
  have krd : v.rd = (allocated 128 s).rd := kv.rd.trans ku.rd
  have kwr : v.wr = (allocated 128 s).wr := kv.wr.trans ku.wr
  refine VG.PPC64LE.WP.of_syms (WP.callAny (k := candK) (fun s' ⟨h₁, h₂⟩ => c.correct s' h₁ h₂)
    ⟨call_cin hf hu ha hm', call_tab h hm' hy hu ha⟩
    (call_covers_reads h krd kwr) (call_covers_writes h kwr) ?_ (by have := c.stack; omega))
  intro t hrd hwr hsp hfr hcs hpost hyt
  have hfr' : Frame (callWrites p ++ [rF p]) v.mem t.mem := by
    rw [hu] at hfr
    exact hfr.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          below_sub c.stack (by decide)⟩
  refine ⟨?_, ?_⟩
  · refine h.restore (show (freed 128 t).rd = s.rd from hrd.trans (krd.trans rfl))
      (show (freed 128 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, kwr]; rfl) ?_
      (hyt.trans (hyv.trans hyu)) (fun r hr => (hcs r hr).trans ((kv.gpr r (by revert r hr; decide)).trans
        (ku.gpr r (by revert r hr; decide)))) (call_frame h hm' hfr')
    change t.sp + BitVec.ofNat 64 128 = s.sp
    rw [hsp, hu, ← callSp_eq, ← h.sp]
    exact BitVec.sub_add_cancel _ _
  · obtain ⟨he, hpb, hrand⟩ := call_inputs h hm'
    obtain ⟨a0, -, -⟩ := call_args hu hm'
    obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
    have tl := toNat_ofNat_lt hf.len64
    have te : (BitVec.ofNat 64 p.elen).toNat = p.elen := toNat_ofNat_lt (by have := hf.e8; omega)
    have tp := toNat_ofNat_lt hf.plen64
    have tr : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
      toNat_ofNat_lt (by have := hf.rand64; omega)
    have hres : cOp (callState p used (tabAddr original) v) =
        Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) := by
      simp only [cOp, oL, rL, call_gpr (by decide : Reg.r4 ∉ linkRegs), call_gpr (by decide : Reg.r6 ∉ linkRegs),
        call_gpr (by decide : Reg.r7 ∉ linkRegs), call_gpr (by decide : Reg.r8 ∉ linkRegs),
        call_gpr (by decide : Reg.r9 ∉ linkRegs), call_gpr (by decide : Reg.r10 ∉ linkRegs), call_stackArg,
        r4, r6, r7, r8, r9, r10, a0, tl, te, tp, tr, State.withRegions_mem, State.callEntry_mem, he, hpb, hrand]
    obtain ⟨q1, q2, q3⟩ := hpost
    simp only [Cand.outOf, Cand.usedOf, oL, rL, hres, call_stackArg, a0, tr,
      call_gpr (by decide : Reg.r3 ∉ linkRegs), call_gpr (by decide : Reg.r4 ∉ linkRegs),
      call_gpr (by decide : Reg.r5 ∉ linkRegs), r3, r4, r5, tl, State.withRegions_gpr,
      State.withRegions_mem] at q1 q2 q3
    refine ⟨?_, q2, q3⟩
    change ((t.gpr .r3).setWidth 32).toNat = _
    rw [BitVec.toNat_setWidth, q1, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (status_small _) (by decide))]

end VG.Proof.RsaKeyGen.PPC64LE.Search
