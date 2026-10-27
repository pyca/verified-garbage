module

public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Params
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntrySpill
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Entry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeInput
import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Exit
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFootprint
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntrySavedAbi
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryRestore
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryLink
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # The probable-prime test's body, between its frame's push and pop

The body is the generation's own: its register saves, the test from the
generation's frame slots, and its restores; between the test and the
restores, the exit writes `used` and the status. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.ProbablePrime VG.Impl.Dsa.Generation.Layout
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Proof.MillerRabin.AArch64
open VG.Proof.Dsa.AArch64.Generation (PrimeParams PrimeInput primeExtras primeRanges allocState
  generationBase linkState linkRegion)
open VG.Impl.Bignum.AArch64 (seqs)

/-- The body of the function, inside its frame. -/
abbrev body (bits : Nat) (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) : Prog isa :=
  seqs [.block Impl.Dsa.AArch64.Generation.entrySave, .block entry, test bits mul roundCode, .block exit,
    .block Impl.Dsa.AArch64.Generation.entryRestore]

/-- The memory the test may change. -/
def changed (bits : Nat) (s : State) : List Region :=
  [⟨off (s.gpr .x0) arithmetic, arithmeticBytes⟩, ⟨off (s.gpr .x0) witness, len bits⟩,
    ⟨generationBase s, 448⟩, ⟨s.gpr .x4, 8⟩]

/-- The test's result as the function returns it. -/
def BodyPost (bits : Nat) (s t : State) : Prop :=
  let res := Spec.Dsa.probablePrime (candidateOf bits s)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.ProbablePrime.status res) ∧
  (∀ b rest, res = some (b, rest) →
    t.mem.readW (s.gpr .x4) 64 = BitVec.ofNat 64 ((s.gpr .x3).toNat - rest.length)) ∧
  Frame (changed bits s) s.mem t.mem ∧
  (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
  (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)

theorem frame_toNat {bits : Nat} {s : State} (A : PrimeABI bits s) :
    (generationBase s).toNat + 448 = s.sp.toNat := by
  have h : 448 ≤ s.sp.toNat := A.stackLower
  have hle : BitVec.ofNat 64 448 ≤ s.sp := by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega
  rw [generationBase, BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat]
  omega

theorem frame_sub (s : State) : Region.Sub ⟨generationBase s, 448⟩ (below s.sp 448) :=
  fun _ h => h

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ 448) :
    (⟨generationBase s, 448⟩ : Region).Contains (off (generationBase s) d) n :=
  Offset.contains_base _ h (by omega)

/-- The frame's region. -/
abbrev frameRegion (s : State) : Region := ⟨generationBase s, 448⟩

/-- What the entry leaves: the test's arguments in the frame, the arithmetic
workspace in `x0`, and the memory changed only in the frame. -/
structure Prepared {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) (u : State) : Prop where
  scr : Scr u (params hb A).B (params hb A).Z
  x0 : u.gpr .x0 = (params hb A).B
  sp : u.sp = generationBase s
  wr : u.wr = (allocState 448 s).wr
  rd : u.rd = s.rd
  frame : Frame [frameRegion s] s.mem u.mem
  link : Frame [⟨generationBase s, 296⟩] (linkState s).mem u.mem
  arena : word u.mem (generationBase s) 40 = s.gpr .x0
  tapePtr : word u.mem (generationBase s) 112 = s.gpr .x2
  tapeLength : word u.mem (generationBase s) 120 = s.gpr .x3
  usedPtr : word u.mem (generationBase s) usedSlot = s.gpr .x4
  used : word u.mem (generationBase s) 128 = 0
  tape : Src u (params hb A).B (params hb A).Z (params hb A).rp (params hb A).rand
  source : Src u (params hb A).B (params hb A).Z (off (s.gpr .x0) (candidate bits))
    (Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) (candidate bits)) (len bits))

theorem prepared {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {u2 : State}
    (m2 : u2.mem = entryMem (linkState s) (generationBase s))
    (x02 : u2.gpr .x0 = off ((linkState s).gpr .x0) arithmetic) (k2 : Keep [.x0, .x3] (linkState s) u2) :
    Prepared hb A u2 := by
  have hFn := frame_toNat A
  have hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  have hU : (⟨s.gpr .x4, 8⟩ : Region) ∈ s.wr := by rw [A.wr]; simp
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have hw48 : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have fws : ∀ {e k : Nat}, e + k ≤ domainCheck →
      Region.Disjoint ⟨generationBase s, 448⟩ ⟨off (s.gpr .x0) e, k⟩ := fun h =>
    (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A h)
  have fused : Region.Disjoint ⟨generationBase s, 448⟩ ⟨s.gpr .x4, 8⟩ :=
    A.stackUsed.sub_left (frame_sub s)
  have frand : Region.Disjoint ⟨generationBase s, 448⟩ ⟨s.gpr .x2, (s.gpr .x3).toNat⟩ :=
    A.stackRand.sub_left (frame_sub s)
  have g0 : (linkState s).gpr .x0 = s.gpr .x0 := rfl
  have g2 : (linkState s).gpr .x2 = s.gpr .x2 := rfl
  have g3 : (linkState s).gpr .x3 = s.gpr .x3 := rfl
  have g4 : (linkState s).gpr .x4 = s.gpr .x4 := rfl
  have wr2 : u2.wr = (allocState 448 s).wr := k2.wr
  have rd2 : u2.rd = s.rd := k2.rd
  have sp2 : u2.sp = generationBase s := k2.sp
  -- The frame is all the entry and the save changed.
  have F02 : Frame [⟨generationBase s, 448⟩] s.mem u2.mem := by
    have fl : Frame [⟨generationBase s, 448⟩] s.mem (linkState s).mem :=
      (VG.Proof.Dsa.AArch64.Generation.link_frame s).sub fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨⟨generationBase s, 448⟩, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    rw [m2]
    unfold entryMem
    exact ((((fl.writeW List.mem_cons_self _ (frame_contains s (by decide))).writeW List.mem_cons_self _
      (frame_contains s (by decide))).writeW List.mem_cons_self _ (frame_contains s (by decide))).writeW
      List.mem_cons_self _ (frame_contains s (by decide))).writeW List.mem_cons_self _ (frame_contains s (by decide))
  -- Words of the frame, and the candidate's and the tape's bytes.
  have ew := entryMem_word (linkState s) (generationBase s)
  rw [g0, g2, g3, g4] at ew
  have hB : Scr u2 (params hb A).B (params hb A).Z := by
    have h0 : Scr u2 (s.gpr .x0) ((s.gpr .x1).toNat * 8) :=
      Scr.of_mem (by rw [wr2]; exact List.mem_cons_of_mem _ hws) A.wsBound
    exact h0.sub (o := arithmetic) (n := arithmeticBytes)
      (by have := A.size; have : arithmetic + arithmeticBytes = domainCheck := rfl; omega) (by decide)
  have D0 : Region.Disjoint ⟨generationBase s, 448⟩ ⟨(params hb A).B, (params hb A).Z⟩ :=
    fws (e := arithmetic) (k := arithmeticBytes) (by decide)
  have candOut : ∀ i < len bits, ¬ (⟨generationBase s, 448⟩ : Region).Contains
      (off (s.gpr .x0) (candidate bits) + BitVec.ofNat 64 i) 1 := by
    intro i hi hc
    have hd := fws (e := candidate bits) (k := len bits)
      (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    exact hd _ hc (contains_byte _ hi (by omega))
  have randOut : ∀ i < (s.gpr .x3).toNat, ¬ (⟨generationBase s, 448⟩ : Region).Contains
      (s.gpr .x2 + BitVec.ofNat 64 i) 1 := by
    intro i hi hc
    exact frand _ hc (contains_byte _ hi (by have := A.randBound; omega))
  have htape : Src u2 (params hb A).B (params hb A).Z (params hb A).rp (params hb A).rand := by
    change Src u2 (off (s.gpr .x0) arithmetic) arithmeticBytes (s.gpr .x2)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [bytesAt_length] at hi
      refine ⟨_, List.mem_append_left _ (by rw [rd2, A.rd]; exact List.mem_cons_self), ?_⟩
      exact contains_byte _ hi (by have := A.randBound; omega)
    · have hi' : i < (s.gpr .x3).toNat := by rw [bytesAt_length] at hi; exact hi
      rw [F02 _ (by simpa only [List.mem_singleton, forall_eq] using randOut i hi')]
      simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
    · have hi' : i < (s.gpr .x3).toNat := by rw [bytesAt_length] at hi; exact hi
      exact out_scr ((A.wsRand.symm).sub_right (ws_sub A (by decide)))
        (contains_byte _ hi' (by have := A.randBound; omega))
  have hsrc : Src u2 (params hb A).B (params hb A).Z
      (word u2.mem (generationBase s) (8 * 5) + BitVec.ofNat 64 (candidate bits))
      (Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) (candidate bits)) (len bits)) := by
    rw [show 8 * 5 = 40 from rfl, m2, ew.1]
    change Src u2 (off (s.gpr .x0) arithmetic) arithmeticBytes (off (s.gpr .x0) (candidate bits))
      (Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) (candidate bits)) (len bits))
    have hcand : candidate bits + len bits ≤ witness := by
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [bytesAt_length] at hi
      refine ⟨_, List.mem_append_right _ (by rw [wr2]; exact List.mem_cons_of_mem _ hws), ?_⟩
      rw [show off (s.gpr .x0) (candidate bits) + BitVec.ofNat 64 i = off (s.gpr .x0) (candidate bits + i) by
        simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
      exact Offset.contains_base _ (by have := A.size; have : witness ≤ domainCheck := (by decide); omega)
        (by have : witness < 2 ^ 64 := (by decide); omega)
    · have hi' : i < len bits := by rw [bytesAt_length] at hi; exact hi
      rw [F02 _ (by simpa only [List.mem_singleton, forall_eq] using candOut i hi')]
      simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
    · have hi' : i < len bits := by rw [bytesAt_length] at hi; exact hi
      refine out_scr (r := ⟨off (s.gpr .x0) (candidate bits), len bits⟩) ?_
        (contains_byte _ hi' (by omega))
      exact Offset.disjoint (s.gpr .x0) (Or.inl (by have : witness ≤ arithmetic := (by decide); omega))
        (by have : witness < 2 ^ 64 := (by decide); omega) (by decide)
  have FL2 : Frame [⟨generationBase s, 296⟩] (linkState s).mem u2.mem := by
    have c : ∀ {d : Nat}, d + 8 ≤ 296 → (⟨generationBase s, 296⟩ : Region).Contains (off (generationBase s) d) 8 :=
      fun h => Offset.contains_base _ h (by omega)
    rw [m2]
    unfold entryMem
    exact (((((Frame.refl _ _).writeW List.mem_cons_self _ (c (by decide))).writeW List.mem_cons_self _
      (c (by decide))).writeW List.mem_cons_self _ (c (by decide))).writeW List.mem_cons_self _
      (c (by decide))).writeW List.mem_cons_self _ (c (by decide))
  refine ⟨hB, x02.trans (by rw [g0]; rfl), sp2, wr2, rd2, F02, FL2, by rw [m2]; exact ew.1, by rw [m2]; exact ew.2.1,
    by rw [m2]; exact ew.2.2.1, by rw [m2]; exact ew.2.2.2.1, by rw [m2]; exact ew.2.2.2.2, htape, ?_⟩
  have h := hsrc
  rw [show 8 * 5 = 40 from rfl, m2, ew.1] at h
  exact h

/-- What the test leaves. -/
structure Tested {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) (u : State) : Prop where
  input : ∃ used', PrimeInput (params hb A) used' u ∧ used' ≤ (params hb A).rand.length ∧
    (Spec.Dsa.probablePrime (params hb A).N ((params hb A).rand.drop 0) = none →
      word u.mem (params hb A).B (8 * kStat) = BitVec.ofNat 64 0) ∧
    (∀ b rest, Spec.Dsa.probablePrime (params hb A).N ((params hb A).rand.drop 0) = some (b, rest) →
      word u.mem (params hb A).B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
      used' = (params hb A).rand.length - rest.length)
  sp : u.sp = generationBase s
  wr : u.wr = (allocState 448 s).wr
  rd : u.rd = s.rd
  frame : Frame [frameRegion s, ⟨(params hb A).B, arithmeticBytes⟩, ⟨(params hb A).p, len bits⟩] s.mem u.mem
  link : Frame [⟨generationBase s, 296⟩, ⟨(params hb A).B, arithmeticBytes⟩, ⟨(params hb A).p, len bits⟩]
    (linkState s).mem u.mem
  usedPtr : word u.mem (generationBase s) usedSlot = s.gpr .x4

theorem test_ok (M : Mont) (K : Kernel) {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s)
    {u2 : State} (P : Prepared hb A u2) :
    WP isa (test bits M.mm K.run) u2 (Tested hb A) := by
  have hFn := frame_toNat A
  have hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  have hU : (⟨s.gpr .x4, 8⟩ : Region) ∈ s.wr := by rw [A.wr]; simp
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have hw48 : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have fws : ∀ {e k : Nat}, e + k ≤ domainCheck →
      Region.Disjoint ⟨generationBase s, 448⟩ ⟨off (s.gpr .x0) e, k⟩ := fun h =>
    (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A h)
  have fused : Region.Disjoint ⟨generationBase s, 448⟩ ⟨s.gpr .x4, 8⟩ :=
    A.stackUsed.sub_left (frame_sub s)
  have D0 : Region.Disjoint ⟨generationBase s, 448⟩ ⟨(params hb A).B, (params hb A).Z⟩ :=
    fws (e := arithmetic) (k := arithmeticBytes) (by decide)
  have frameOut : ∀ r ∈ [(⟨(params hb A).B, arithmeticBytes⟩ : Region), ⟨(params hb A).p, len bits⟩],
      Region.Disjoint ⟨generationBase s, 448⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact D0
    · exact fws (by have : witness + 384 ≤ domainCheck := (by decide); omega)
  have inFrame : ∀ {d n : Nat}, d + n ≤ 448 → ∀ r ∈ [(⟨(params hb A).B, arithmeticBytes⟩ : Region),
      ⟨(params hb A).p, len bits⟩], Region.Disjoint ⟨off (generationBase s) d, n⟩ r :=
    fun h r hr => (frameOut r hr).sub_left (Offset.sub_base _ h)
  unfold test
  have hlow := ((bitLength_iff_bounds (by have := hb.le; omega)).mp A.bits).1
  -- The test.
  refine WP.mono (VG.Proof.Dsa.AArch64.Generation.checkPrime_ok M K (P := params hb A) (s := u2)
    (used := 0) (candidate := candidate bits) (W := fun k => word u2.mem (generationBase s) (8 * k))
    P.scr P.x0
    (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by change checks bits < _; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    P.sp
    (fun k hk => ⟨_, List.mem_append_right _ (by rw [P.wr]; exact List.mem_cons_self),
      frame_contains s (by omega)⟩)
    (fun _ _ => rfl)
    (fun k hk j hj => D0.sep (frame_contains s (by omega))
      (Offset.contains_base _ (by change 8 * j + 8 ≤ arithmeticBytes; unfold arithmeticBytes; omega) (by omega)))
    (fun k hk i hi => by
      rw [off_off]
      exact out_scr D0 (frame_contains s (by omega)))
    (by rw [show 8 * 5 = 40 from rfl, P.arena]; rfl)
    (by rw [show 8 * 14 = 112 from rfl, P.tapePtr]; rfl)
    (by
      rw [show 8 * 15 = 120 from rfl, P.tapeLength]
      change s.gpr .x3 = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat).length
      rw [bytesAt_length, ofNat_toNat64])
    (by rw [show 8 * 16 = 128 from rfl, P.used]; rfl)
    P.tape
    (fun i hi => by
      refine ⟨_, by rw [P.wr]; exact List.mem_cons_of_mem _ hws, ?_⟩
      change (wsRegion s).Contains (off (off (s.gpr .x0) witness) i) 1
      rw [off_off]
      exact Offset.contains_base _ (by have := A.size; have : witness + 384 ≤ domainCheck := (by decide); change i < len bits at hi; omega)
        (by have : witness + 384 < 2 ^ 64 := (by decide); change i < len bits at hi; omega))
    (bytesAt_length _ _ _) rfl (by rw [show 8 * 5 = 40 from rfl, P.arena]; exact P.source) (Nat.zero_le _) hw48
    (by change Bignum.slot (words bits) aTab + 2048 ≤ arithmeticBytes
        rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      change 8161 < candidateOf bits s
      have h2 : 2 ^ 159 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by have := hb.le; omega)
      have : (8161 : Nat) < 2 ^ 159 := by decide
      exact Nat.lt_of_lt_of_le this (Nat.le_trans h2 hlow))
    (by
      change 1024 < Spec.Dsa.bitLength (candidateOf bits s) ↔ 16 < words bits
      rw [A.bits]; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      change checks bits = Spec.Dsa.primeChecks (Spec.Dsa.bitLength (candidateOf bits s))
      rw [A.bits]; rfl)) fun u3 h3 => ?_
  obtain ⟨used', inp, hub, hnone, hsome, wf3, k3⟩ := h3
  have F23 : Frame [⟨(params hb A).B, arithmeticBytes⟩, ⟨(params hb A).p, len bits⟩] u2.mem u3.mem :=
    VG.Proof.Dsa.AArch64.Generation.prime_global_frame wf3
      (VG.Proof.Dsa.AArch64.Generation.checkPrimeRanges_bound hw48)
  refine ⟨⟨used', inp, hub, hnone, hsome⟩, k3.sp.trans P.sp, k3.wr.trans P.wr, k3.rd.trans P.rd,
    (P.frame.mono (by simp)).trans (F23.mono (by simp)), (P.link.mono (by simp)).trans (F23.mono (by simp)), ?_⟩
  rw [← P.usedPtr]
  exact F23.readW (Offset.contains_base _ (d := 0) (n := 8) (k := 8) (by decide) (by decide) |> fun h => by
    simpa only [off, BitVec.add_zero] using h) (inFrame (d := usedSlot) (n := 8) (by decide)) (by decide)

theorem finish_ok {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {u3 : State}
    (T : Tested hb A u3) :
    WP isa (.seq (.block exit) (.block Impl.Dsa.AArch64.Generation.entryRestore)) u3 fun t =>
      t.sp = (allocState 448 s).sp ∧ t.wr = (allocState 448 s).wr ∧ t.rd = s.rd ∧ BodyPost bits s t := by
  have hFn := frame_toNat A
  have hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  have hU : (⟨s.gpr .x4, 8⟩ : Region) ∈ s.wr := by rw [A.wr]; simp
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have hw48 : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have fws : ∀ {e k : Nat}, e + k ≤ domainCheck →
      Region.Disjoint ⟨generationBase s, 448⟩ ⟨off (s.gpr .x0) e, k⟩ := fun h =>
    (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A h)
  have fused : Region.Disjoint ⟨generationBase s, 448⟩ ⟨s.gpr .x4, 8⟩ :=
    A.stackUsed.sub_left (frame_sub s)
  have D0 : Region.Disjoint ⟨generationBase s, 448⟩ ⟨(params hb A).B, (params hb A).Z⟩ :=
    fws (e := arithmetic) (k := arithmeticBytes) (by decide)
  have frameOut : ∀ r ∈ [(⟨(params hb A).B, arithmeticBytes⟩ : Region), ⟨(params hb A).p, len bits⟩],
      Region.Disjoint ⟨generationBase s, 448⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact D0
    · exact fws (by have : witness + 384 ≤ domainCheck := (by decide); omega)
  have inFrame : ∀ {d n : Nat}, d + n ≤ 448 → ∀ r ∈ [(⟨(params hb A).B, arithmeticBytes⟩ : Region),
      ⟨(params hb A).p, len bits⟩], Region.Disjoint ⟨off (generationBase s) d, n⟩ r :=
    fun h r hr => (frameOut r hr).sub_left (Offset.sub_base _ h)
  obtain ⟨⟨used', inp, hub, hnone, hsome⟩, sp3, wr3, rd3, F03, FL3, hU3⟩ := T
  -- The exit.
  refine WP.seq (WP.mono (exit_ok (u := u3) (B := (params hb A).B) (F := generationBase s) (U := s.gpr .x4)
    (used := BitVec.ofNat 64 used') (st := word u3.mem (params hb A).B (8 * kStat))
    inp.ws.x0 sp3
    (inp.ws.scr.ld (d := 216) (by have := inp.ws.h256; omega))
    (inp.ws.scr.ld (d := 248) (by have := inp.ws.h256; omega))
    ⟨_, List.mem_append_right _ (by rw [wr3]; exact List.mem_cons_self), frame_contains s (by decide)⟩
    ⟨⟨s.gpr .x4, 8⟩, by rw [wr3]; exact List.mem_cons_of_mem _ hU, Region.contains_self _ _⟩
    hU3 inp.used rfl
    (by
      have h := A.wsUsed.sub_left (ws_sub A (d := arithmetic + 248) (n := 8) (by decide))
      rw [show off (s.gpr .x0) (arithmetic + 248) = off (params hb A).B (8 * kStat) by
        simp only [params, off, BitVec.add_assoc, BitVec.ofNat_add]; rfl] at h
      exact h.sep (Region.contains_self _ _) (Region.contains_self _ _))) fun u4 h4 => ?_)
  obtain ⟨m4, x04, k4⟩ := h4
  have sp4 : u4.sp = generationBase s := k4.sp.trans sp3
  have wr4 : u4.wr = (allocState 448 s).wr := k4.wr.trans wr3
  have rd4 : u4.rd = s.rd := k4.rd.trans rd3
  -- What changed since the save: the entry's slots, the test's workspace and buffer, and `used`.
  have F34 : Frame [⟨s.gpr .x4, 8⟩] u3.mem u4.mem := by
    rw [m4]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have FL4 : Frame [⟨generationBase s, 296⟩, ⟨(params hb A).B, arithmeticBytes⟩, ⟨(params hb A).p, len bits⟩,
      ⟨s.gpr .x4, 8⟩] (linkState s).mem u4.mem :=
    (FL3.mono (by simp)).trans (F34.mono (by simp))
  have hlink : ∀ r ∈ [(⟨generationBase s, 296⟩ : Region), ⟨(params hb A).B, arithmeticBytes⟩,
      ⟨(params hb A).p, len bits⟩, ⟨s.gpr .x4, 8⟩],
      Region.Disjoint ⟨generationBase s + BitVec.ofNat 64 296, 152⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by decide) (by decide)
    · exact inFrame (d := 296) (n := 152) (by decide) _ (by simp)
    · exact inFrame (d := 296) (n := 152) (by decide) _ (by simp)
    · exact fused.sub_left (Offset.sub_base _ (by decide))
  have g4 := (VG.Proof.Dsa.AArch64.Generation.link_gprs s).frame_in (lo := 296) (n := 152) (by decide) FL4 hlink
  have v4 := (VG.Proof.Dsa.AArch64.Generation.link_vectors s).frame_in (lo := 296) (n := 152) (by decide) FL4 hlink
  have lr4 : u4.mem.readW (generationBase s + BitVec.ofNat 64 296) 64 = s.gpr .x30 := by
    have c296 : (⟨generationBase s + BitVec.ofNat 64 296, 8⟩ : Region).Contains
        (generationBase s + BitVec.ofNat 64 296) (64 / 8) := Region.contains_self _ _
    have dis : ∀ r ∈ [(⟨generationBase s, 296⟩ : Region), ⟨(params hb A).B, arithmeticBytes⟩,
        ⟨(params hb A).p, len bits⟩, ⟨s.gpr .x4, 8⟩],
        Region.Disjoint ⟨generationBase s + BitVec.ofNat 64 296, 8⟩ r :=
      fun r hr => (hlink r hr).sub_left (Offset.sub (generationBase s) (d := 296) (n := 8) (e := 296) (k := 152)
        (by decide) (by decide))
    rw [FL4.readW c296 dis (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  -- Restore the callee-saved registers.
  refine WP.mono (VG.Proof.Dsa.AArch64.Generation.entryRestore_ok (s := s) sp4
    (fun d hd => ⟨_, List.mem_append_right _ (by rw [wr4]; exact List.mem_cons_self), frame_contains s hd⟩)
    g4 v4 lr4) fun u5 R5 => ?_
  refine ⟨R5.stack.trans sp4, R5.write.trans wr4, R5.read.trans rd4, ?_, ?_, ?_, R5.gprs, R5.vectors⟩
  · rw [R5.result, x04]
    change word u3.mem (params hb A).B (8 * kStat) - word u3.mem (params hb A).B (8 * kStat) >>> 1 =
      BitVec.ofNat 64 (Spec.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime (params hb A).N (params hb A).rand))
    rw [show Spec.Dsa.probablePrime (params hb A).N (params hb A).rand =
      Spec.Dsa.probablePrime (params hb A).N (List.drop 0 (params hb A).rand) from rfl]
    cases h : Spec.Dsa.probablePrime (params hb A).N (List.drop 0 (params hb A).rand) with
    | none => rw [hnone h]; decide
    | some r =>
      obtain ⟨b, rest⟩ := r
      rw [(hsome b rest h).1]
      cases b <;> simp only [Spec.Dsa.ProbablePrime.status] <;> decide
  · intro b rest h
    have h' : Spec.Dsa.probablePrime (params hb A).N (List.drop 0 (params hb A).rand) = some (b, rest) := h
    rw [R5.memory, m4, Mem.readW_writeW_self64, (hsome b rest h').2]
    change BitVec.ofNat 64 ((Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat).length - rest.length) = _
    rw [bytesAt_length]
  · rw [R5.memory]
    refine (F03.mono ?_).trans (F34.mono (by simp [changed]))
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [changed, params]

theorem body_ok (M : Mont) (K : Kernel) {bits : Nat} (hb : Supported bits) {s : State}
    (A : PrimeABI bits s) :
    WP isa (body bits M.mm K.run) (allocState 448 s) fun t =>
      t.sp = (allocState 448 s).sp ∧ t.wr = (allocState 448 s).wr ∧ t.rd = s.rd ∧
      BodyPost bits s t := by
  have hwF : ∀ d, d + 8 ≤ 448 → InRegions (linkState s).wr (off (generationBase s) d) 8 :=
    fun d hd => ⟨_, List.mem_cons_self, frame_contains s hd⟩
  simp only [body, seqs]
  refine WP.seq (WP.mono (VG.Proof.Dsa.AArch64.Generation.entrySave_ok s) fun u1 h1 => ?_)
  subst h1
  refine WP.seq (WP.mono (entry_ok (s := linkState s) (F := generationBase s) rfl hwF)
    fun u2 ⟨m2, x02, k2⟩ => ?_)
  exact WP.seq (WP.mono (test_ok M K hb A (prepared hb A m2 x02 k2)) fun u3 T => finish_ok hb A T)

end VG.Proof.Dsa.AArch64.ProbablePrime
