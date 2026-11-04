module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Args
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CallFacts
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-! # A candidate call (ARMv7)

`candidateRun`: the candidate's frame, its arguments, and the call of
`vg_rsa_keygen_candidate` on the tape from `used`, which holds at least a
candidate's octets (`candidateStep` does not call it otherwise).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.RsaKeyGen.Arm.Search

/-- The regions the candidate reads and writes. -/
def callRd (p : SearchPublic) (used : Nat) : List Region := [rE p, rP p, rR p used, rA p]
def callWr (p : SearchPublic) : List Region := [rO p, rU p, rS p]

namespace ArgDone

variable {p : SearchPublic} {o a u : State} {used : Nat}

/-- The candidate's stack argument `j`, as stored. -/
theorem stackArg_eq (h : ArgDone p o a used u) (R W : List Region) {j : Nat} (hj : j < 7) :
    stackArg (u.callEntry.withRegions R W) j = slotValue (callArgs p used) j (slot a.mem (State.addr p.S2) j) := by
  have fits := h.1.S2_fits
  have e : stackArgAddr (u.callEntry.withRegions R W) j = off (State.addr p.S2) (4 * j) := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, h.1.sp]
    exact VG.Arm.addr_add (by omega)
  unfold stackArg
  rw [e, State.withRegions_mem, State.callEntry_mem, h.1.mem]
  exact slot_writeSlots _ _ (N := 8) (by decide) _ (fun e he => callArgs_bound p used e (List.mem_of_mem_take he))
    j (by omega)

theorem sa0 (h : ArgDone p o a used u) (R W : List Region) :
    stackArg (u.callEntry.withRegions R W) 0 = BitVec.ofNat 32 p.elen := h.stackArg_eq R W (by decide)
theorem sa1 (h : ArgDone p o a used u) (R W : List Region) :
    stackArg (u.callEntry.withRegions R W) 1 = p.pp := h.stackArg_eq R W (by decide)
theorem sa2 (h : ArgDone p o a used u) (R W : List Region) :
    stackArg (u.callEntry.withRegions R W) 2 = BitVec.ofNat 32 p.plen := h.stackArg_eq R W (by decide)
theorem sa3 (h : ArgDone p o a used u) (R W : List Region) :
    stackArg (u.callEntry.withRegions R W) 3 = p.rp + BitVec.ofNat 32 used := h.stackArg_eq R W (by decide)
theorem sa4 (h : ArgDone p o a used u) (R W : List Region) :
    stackArg (u.callEntry.withRegions R W) 4 = BitVec.ofNat 32 p.randLen - BitVec.ofNat 32 used :=
  h.stackArg_eq R W (by decide)
theorem sa5 (h : ArgDone p o a used u) (R W : List Region) :
    stackArg (u.callEntry.withRegions R W) 5 = p.B := h.stackArg_eq R W (by decide)
theorem sa6 (h : ArgDone p o a used u) (R W : List Region) :
    stackArg (u.callEntry.withRegions R W) 6 = BitVec.ofNat 32 p.words := h.stackArg_eq R W (by decide)

theorem argAddr (h : ArgDone p o a used u) (R W : List Region) :
    stackArgAddr (u.callEntry.withRegions R W) 0 = State.addr p.S2 := by
  simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, h.1.sp, Nat.mul_zero, BitVec.add_zero]

end ArgDone

theorem toNat_small {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_diff {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b).toNat = a - b := by
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hb, toNat_small (by omega)]

theorem call_pre {p : SearchPublic} {o a u : State} {used : Nat} (h : ArgDone p o a used u)
    (hu : used ≤ p.randLen) :
    (Spec.RsaKeyGen.candidateContract abi 112).pre (u.callEntry.withRegions (callRd p used) (callWr p)) := by
  have hi := h.1.input
  have f := hi.facts
  have cf := hi.callFacts hu
  have hl := f.valid
  unfold Spec.RsaKeyGen.primeLenValid at hl
  have rl := f.randLen
  unfold Spec.RsaKeyGen.primeEntropy at rl
  sig_pre [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, reduceClassify, Loc.val]
  simp only [h.sa0, h.sa1, h.sa2, h.sa3, h.sa4, h.sa5, h.sa6, h.argAddr, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
    h.1.sp, toNat_small (n := p.len) (by omega), toNat_small (n := p.elen) (by have := f.e8; omega),
    toNat_small (n := p.plen) (by rcases f.plen with e | e <;> omega),
    toNat_small (n := p.words) (by have := f.nS; omega), toNat_diff hu (by omega)]
  exact ⟨cf.spLo, cf.spHi, rfl, rfl, cf.oU, cf.oE, cf.oP, cf.oR, cf.oS, cf.oA, cf.uE, cf.uP, cf.uR, cf.uS, cf.uA,
    cf.eS, cf.pS, cf.rS', cf.sA, cf.fO, cf.fU, cf.fE, cf.fP, cf.fR, cf.fS, cf.fA, cf.no, cf.nu, cf.ne, cf.np,
    cf.nr, cf.ns, f.valid, f.e1, f.e8, f.plen, f.scr⟩

/-- What the candidate leaves: its status, `out`, and the octets it consumed. -/
def CandPost (p : SearchPublic) (pB rand : List Byte) (used : Nat) (t : State) : Prop :=
  (t.gpr .r0).toNat = Spec.RsaKeyGen.candidateStatus (Spec.RsaKeyGen.candidateOp p.len p.eB pB (rand.drop used)) ∧
    Spec.Rsa.bytesAt t.mem (State.addr p.op) p.len =
      (match Spec.RsaKeyGen.candidateOp p.len p.eB pB (rand.drop used) with
        | some (.prime c, _) => Spec.Rsa.i2osp c p.len
        | _ => List.replicate p.len 0) ∧
    Spec.Rsa.wordsAt t.mem (State.addr p.up) 1 =
      [BitVec.ofNat 64 (match Spec.RsaKeyGen.candidateOp p.len p.eB pB (rand.drop used) with
        | some (_, rest) => (p.randLen - used) - rest.length
        | none => 0)]

theorem bytesAt_drop (m : Mem) (P : Addr) (k n : Nat) :
    Spec.Rsa.bytesAt m (P + BitVec.ofNat 64 k) (n - k) = (Spec.Rsa.bytesAt m P n).drop k := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_drop,
    BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The regions of a call, among the state's. -/
theorem call_covers {p : SearchPublic} {o s a u : State} {used remaining : Nat}
    (h : SearchLive p o used remaining s) (ha : a = allocated 32 s) (hd : ArgDone p o a used u)
    (hroom : used < p.randLen) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) ∧ Covers (callWr p) u.wr := by
  have hi := h.input
  have f := hi.facts
  obtain ⟨eO, eU, eE, eP, eR, eS, -⟩ := hi.regions
  have hrd : u.rd = inReads o := hd.1.rd.trans hi.rd
  have hwr : u.wr = ⟨State.addr p.S2, 32⟩ :: ⟨State.addr p.S1, 40⟩ :: inWrites o := by
    rw [hd.1.wr, ha]; change _ :: s.wr = _; rw [h.wr, hi.wr]
  have w : Covers (callWr p) u.wr := by
    refine Covers.of_mem fun r hr => ?_
    rw [hwr]
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [← eO]; simp [inWrites]
    · rw [← eU]; simp [inWrites]
    · rw [← eS]; simp [inWrites]
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) w.right, w⟩
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨rE p, by rw [hrd, ← eE]; simp [inReads], 0, by rw [BitVec.add_zero], by simp⟩
  · exact ⟨rP p, by rw [hrd, ← eP]; simp [inReads], 0, by rw [BitVec.add_zero], by simp⟩
  · refine ⟨⟨State.addr p.rp, p.randLen⟩, by rw [hrd, ← eR]; simp [inReads], used,
      VG.Arm.addr_add (by have := f.nR; omega), by simp only; omega⟩
  · exact ⟨⟨State.addr p.S2, 32⟩, by rw [hwr]; simp, 0, by rw [BitVec.add_zero], by simp⟩

theorem addr_toNat (x : BitVec 32) : (State.addr x).toNat = x.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

/-- The push's frame, the candidate's, and the candidate's stack, in terms
of the stack pointer. -/
theorem S1_toNat {p : SearchPublic} {o : State} (h : SearchInput p o) : (State.addr p.S1).toNat = p.sp.toNat - 40 := by
  rw [addr_toNat]; exact FrameStack.sub_toNat' (Nat.le_trans (by decide) h.facts.room)

theorem S2_toNat {p : SearchPublic} {o : State} (h : SearchInput p o) : (State.addr p.S2).toNat = p.sp.toNat - 72 := by
  rw [addr_toNat]; exact FrameStack.sub_toNat' (Nat.le_trans (by decide) h.facts.room)

theorem below_toNat {p : SearchPublic} {o : State} (h : SearchInput p o) {k : Nat} (hk : k ≤ 112) :
    (FrameStack.belowA p.S2 k).base.toNat = p.sp.toNat - 72 - k := by
  have room := h.facts.room
  have e := FrameStack.sub_toNat' (sp := p.S2) (k := k) (by rw [← addr_toNat, S2_toNat h]; omega)
  change (State.addr (p.S2 - BitVec.ofNat 32 k)).toNat = _
  rw [addr_toNat, e, ← addr_toNat, S2_toNat h]

theorem S2_sub {p : SearchPublic} {o : State} (h : SearchInput p o) :
    Region.Sub ⟨State.addr p.S2, 32⟩ (inStack o) := by
  have room := h.facts.room
  rw [SearchPublic.S2, FrameStack.addr_sub' (by omega), h.sp_eq]
  exact h.stack_sub (by decide) (by decide)

theorem below_sub {p : SearchPublic} {o : State} (h : SearchInput p o) {k : Nat} (hk : k ≤ 112) :
    Region.Sub (FrameStack.belowA p.S2 k) (inStack o) := by
  have room := h.facts.room
  change Region.Sub ⟨State.addr (p.sp - BitVec.ofNat 32 72 - BitVec.ofNat 32 k), k⟩ _
  rw [BitVec.sub_sub, ← BitVec.ofNat_add, FrameStack.addr_sub' (by omega), h.sp_eq]
  exact h.stack_sub (by show 72 + k ≤ 184; omega) (by show 184 - (72 + k) + k ≤ 184; omega)

/-- What a call may change, among what the search may. -/
theorem call_changes {p : SearchPublic} {o : State} (h : SearchInput p o) {k : Nat} (hk : k ≤ 112) :
    ∀ r ∈ (⟨State.addr p.S2, 32⟩ :: callWr p) ++ [FrameStack.belowA p.S2 k], ∃ q ∈ changes o, Region.Sub r q := by
  obtain ⟨eO, eU, -, -, -, eS, -⟩ := h.regions
  have st : inStack o ∈ changes o := by simp [changes]
  intro r hr
  simp only [callWr, List.cons_append, List.mem_cons, List.nil_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, st, S2_sub h⟩
  · exact ⟨inOut o, by simp [changes, inWrites], by rw [eO]; exact fun _ h => h⟩
  · exact ⟨inUsed o, by simp [changes, inWrites], by rw [eU]; exact fun _ h => h⟩
  · exact ⟨inScr o, by simp [changes, inWrites], by rw [eS]; exact fun _ h => h⟩
  · exact ⟨_, st, below_sub h hk⟩

/-- The pushed registers are apart from what a call may change. -/
theorem saved_apart {p : SearchPublic} {o : State} (h : SearchInput p o) {k : Nat} (hk : k ≤ 112) :
    ∀ r ∈ (⟨State.addr p.S2, 32⟩ :: callWr p) ++ [FrameStack.belowA p.S2 k],
      Region.Disjoint ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ r := by
  have room := h.facts.room
  have top := h.facts.top
  have e1 := S1_toNat h
  have e2 := S2_toNat h
  have push : Region.Sub ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ (inStack o) := by
    rw [BitVec.add_zero, SearchPublic.S1, FrameStack.addr_sub' (by omega), h.sp_eq]
    exact h.stack_sub (by decide) (by decide)
  obtain ⟨eO, eU, -, -, -, eS, -⟩ := h.regions
  have w (q : Region) (hq : q ∈ inWrites o) : Region.Disjoint ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ q :=
    SearchInput.disj_sub (h.stack_disjoint (List.mem_append_left _ hq)) push
  intro r hr
  simp only [callWr, List.cons_append, List.mem_cons, List.nil_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · refine (Offset.disjoint_of_le (by simp only; rw [e2, BitVec.add_zero, e1]; omega) ?_).symm
    simp only; rw [BitVec.add_zero, e1]; omega
  · rw [← eO]; exact w _ (by simp [inWrites])
  · rw [← eU]; exact w _ (by simp [inWrites])
  · rw [← eS]; exact w _ (by simp [inWrites])
  · refine (Offset.disjoint_of_le (by rw [below_toNat h hk]; simp only; rw [BitVec.add_zero, e1]; omega) ?_).symm
    simp only; rw [BitVec.add_zero, e1]; omega

theorem S2_add (x : BitVec 32) : x - BitVec.ofNat 32 72 + BitVec.ofNat 32 32 = x - BitVec.ofNat 32 40 := by
  rw [show (72 : Nat) = 40 + 32 from rfl, BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem candidateRun_ok (c : Cand) {p : SearchPublic} {o s : State} {used remaining : Nat}
    (h : SearchLive p o used remaining s) (hroom : used + p.len ≤ p.randLen) :
    WP isa (candidateRun c.call) s fun t =>
      SearchLive p o used remaining t ∧ CandPost p (searchP o) (searchRand o) used t := by
  have hi := h.input
  have f := hi.facts
  have hl := f.valid
  unfold Spec.RsaKeyGen.primeLenValid at hl
  have room := f.room
  have hsp : s.sp.toNat = p.sp.toNat - 40 := by rw [h.sp]; exact FrameStack.sub_toNat' (by omega)
  unfold candidateRun
  refine WP.alloc (by decide) (by omega) ?_
  refine WP.seq (WP.mono (arguments_ok h) fun u ⟨hd, ku⟩ => ?_)
  have hu : used ≤ p.randLen := by omega
  obtain ⟨cov, covW⟩ := call_covers h rfl hd (by omega)
  have hS2 : 112 ≤ u.sp.toNat := by rw [hd.1.sp, ← addr_toNat, S2_toNat hi]; omega
  refine FrameStack.WP.callF c.verified.1 (call_pre hd hu) cov covW (Nat.le_trans c.stack hS2)
    fun t hrd hwr hspt hfr hpres hpost => ?_
  rw [hd.1.sp] at hfr
  -- memory
  have hargs : Frame [⟨State.addr p.S2, 32⟩] s.mem u.mem := by
    rw [hd.1.mem]
    exact writeSlots_frame _ _ (N := 8) (by decide) _ fun e he => callArgs_bound p used e (List.mem_of_mem_take he)
  have hcall : Frame ((⟨State.addr p.S2, 32⟩ :: callWr p) ++ [FrameStack.belowA p.S2 (FrameStack.armStack c.code)])
      s.mem t.mem :=
    (hargs.mono fun r hr => by simp at hr; simp [hr]).trans (hfr.mono fun r hr => by simp at hr ⊢; exact Or.inr hr)
  have hfu : Frame (changes o) o.mem u.mem := h.frame.trans (hargs.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact ⟨_, by simp [changes], S2_sub hi⟩)
  have hreg (r : Reg) (hr : r ∈ preserved) (hlr : r ≠ .lr) (hk : r ∉ [.r0, .r1, .r2, .r3, .r12, .lr]) :
      t.gpr r = s.gpr r := (hpres r hr hlr).trans (ku.gpr r hk)
  refine ⟨⟨⟨hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h.used_le, h.remaining_le, ?_, ?_, ?_⟩, ?_⟩
  · exact hrd.trans (ku.rd.trans h.rd)
  · change t.wr.tail = _; rw [hwr, ku.wr]; exact h.wr
  · change t.sp + BitVec.ofNat 32 32 = _
    rw [hspt, hd.1.sp, SearchPublic.S2, S2_add]
  · exact (hreg .r4 (by decide) (by decide) (by decide)).trans h.r4
  · exact (hreg .r5 (by decide) (by decide) (by decide)).trans h.r5
  · exact (hreg .r6 (by decide) (by decide) (by decide)).trans h.r6
  · exact (hreg .r7 (by decide) (by decide) (by decide)).trans h.r7
  · exact Spill.Saved.frame h.saved (lo := 0) (hi := 40) (by decide) hcall (saved_apart hi c.stack)
  · exact h.frame.trans (hcall.sub (call_changes hi c.stack))
  · exact (hreg .r8 (by decide) (by decide) (by decide)).trans h.r8
  · exact (hreg .r9 (by decide) (by decide) (by decide)).trans h.r9
  · exact (hreg .r11 (by decide) (by decide) (by decide)).trans h.r11
  · have eB : Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 p.ep) p.elen = p.eB := by
      change Spec.Rsa.bytesAt u.mem (State.addr p.ep) p.elen = _
      rw [hi.e_frame hfu, ← hi.2]; rfl
    have pB : Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 p.pp) p.plen = searchP o := by
      change Spec.Rsa.bytesAt u.mem (State.addr p.pp) p.plen = _
      rw [hi.p_frame hfu, ← hi.2]; rfl
    have rB : Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 (p.rp + BitVec.ofNat 32 used)) (p.randLen - used) =
        (searchRand o).drop used := by
      change Spec.Rsa.bytesAt u.mem (State.addr (p.rp + BitVec.ofNat 32 used)) (p.randLen - used) = _
      rw [VG.Arm.addr_add (by have := f.nR; omega), bytesAt_drop, hi.random_frame hfu, ← hi.2]; rfl
    change CandPost p (searchP o) (searchRand o) used t
    sig_post [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, reduceClassify,
      Loc.val] at hpost
    simp only [hd.sa0, hd.sa1, hd.sa2, hd.sa3, hd.sa4, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2,
      toNat_small (n := p.len) (by omega), toNat_small (n := p.elen) (by have := f.e8; omega),
      toNat_small (n := p.plen) (by rcases f.plen with e | e <;> omega),
      toNat_diff hu (by have := f.randLen; unfold Spec.RsaKeyGen.primeEntropy at this; omega),
      eB, pB, rB] at hpost
    obtain ⟨h0, h1, h2⟩ := hpost
    refine ⟨?_, h1, h2⟩
    rw [← h0, BitVec.setWidth_append_eq_right]

end VG.Proof.RsaKeyGen.Arm.Search
