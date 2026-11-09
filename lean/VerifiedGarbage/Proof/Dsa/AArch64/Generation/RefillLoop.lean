module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillOutcome
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSearch
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeState
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # The refillable-tape search's controller on AArch64

The controller runs one seed per iteration while seeds are rejected. Its
invariant (`LoopInv`): the whole search's result is the search from the
octets `c` it has consumed on, those consumed before it
(`RefillSearch.lean`), and the controller's words hold the pointers to
`used` and `state` and the seeds it may still reject. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation.Refill

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 (Lay Rep Geo upd nW cF)
open VG.Impl.RsaOaep.AArch64 (frameBytes oRsa)
open VG.Proof.Dsa.AArch64.Generation

/-! ## Blocks -/

theorem ctl_in {s : State} {F : Addr} (hv : (⟨F, 480⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < 4) :
    InRegions s.wr (off F (448 + 8 * k)) 8 :=
  ⟨_, hv, Offset.contains_base F (by omega) (by omega)⟩

theorem ctl_in' {s : State} {F : Addr} (hv : (⟨F, 480⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < 4) :
    InRegions (s.rd ++ s.wr) (off F (448 + 8 * k)) 8 :=
  let ⟨r, hr, hc⟩ := ctl_in hv hk
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- `subs` of two numbers: the carry is set iff there is no borrow. -/
theorem loop_subs_ge {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide (2 ^ 64 ≤ (BitVec.ofNat 64 a).toNat + (~~~BitVec.ofNat 64 b).toNat + (true).toNat) = decide (b ≤ a) := by
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Bool.toNat_true]
  exact decide_eq_decide.mpr (by omega_arith)

theorem movi_small {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The start of an iteration: the seed's start into `x0` and `ctl 3`, the
seeds left into `x3`. -/
theorem iterStart_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hv : (⟨F, 480⟩ : Region) ∈ s.wr)
    {c n : Nat} (h16 : W 16 = BitVec.ofNat 64 c) (h2 : ctlWord s.mem F 2 = BitVec.ofNat 64 n) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.iterStart) s fun t =>
      (t.gpr .x0 = BitVec.ofNat 64 c ∧ t.gpr .x3 = BitVec.ofNat 64 n ∧
        t.mem = s.mem.writeW (off F 472) (BitVec.ofNat 64 c)) ∧ Keep [.x0, .x3] s t := by
  have w16 : s.mem.readW (s.sp + BitVec.ofNat 64 128) 64 = BitVec.ofNat 64 c := by
    rw [L.sp]; exact (R.fr 16 (by decide)).trans h16
  have w2 : s.mem.readW (s.sp + BitVec.ofNat 64 464) 64 = BitVec.ofNat 64 n := by rw [L.sp]; exact h2
  have l128 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 128) 8 := by rw [L.sp]; exact L.ld (d := 128) (by decide)
  have l464 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 464) 8 := by rw [L.sp]; exact ctl_in' hv (k := 2) (by decide)
  have s472 : InRegions s.wr (s.sp + BitVec.ofNat 64 472) 8 := by rw [L.sp]; exact ctl_in hv (k := 3) (by decide)
  refine WP.keep [.x0, .x3] ?_ (by decide)
  simp only [Impl.Dsa.AArch64.Generation.Refill.iterStart, Impl.Dsa.AArch64.Generation.Refill.ctl, Nat.reduceMul,
    Nat.reduceAdd]
  brun [State.write, exec_ldrSp (off := 128) (by decide), exec_ldrSp (off := 464) (by decide),
    exec_storeSp (off := 472) (by decide), w16, w2, l128, l464, s472]
  rw [L.sp]

/-- `x3 := 1` exactly when fewer than `q` octets are left from `x0`. -/
theorem roomCheck_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {c len q : Nat} (hx0 : s.gpr .x0 = BitVec.ofNat 64 c)
    (h15 : W 15 = BitVec.ofNat 64 len) (hc : c ≤ len) (hl : len < 2 ^ 64) (hq2 : q = 20 ∨ q = 32) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.roomCheck q)) s fun t =>
      (t.gpr .x3 = BitVec.ofNat 64 (if len - c < q then 1 else 0) ∧ t.mem = s.mem) ∧ Keep [.x3, .x4, .x5] s t := by
  have w15 : s.mem.readW (s.sp + BitVec.ofNat 64 120) 64 = BitVec.ofNat 64 len := by
    rw [L.sp]; exact (R.fr 15 (by decide)).trans h15
  have l120 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 120) 8 := by rw [L.sp]; exact L.ld (d := 120) (by decide)
  have hsub : BitVec.ofNat 64 len - BitVec.ofNat 64 c = BitVec.ofNat 64 (len - c) := Offset.ofNat_sub_ofNat hc
  have hm := movi_small (show q < 2 ^ 16 by omega)
  refine WP.keep [.x3, .x4, .x5] ?_ (by rcases hq2 with rfl | rfl <;> decide) rfl
    (by rcases hq2 with rfl | rfl <;> decide +kernel)
  unfold Impl.Dsa.AArch64.Generation.Refill.roomCheck
  brun [State.write, exec_ldrSp (off := 120) (by decide), w15, l120, hx0, hsub, hm,
    loop_subs_ge (show len - c < 2 ^ 64 by omega) (show q < 2 ^ 64 by omega),
    movi_small (show 0 < 2 ^ 16 by decide), movi_small (show 1 < 2 ^ 16 by decide)]
  by_cases h : q ≤ len - c
  · simp only [h, decide_true, ite_true, show ¬ len - c < q by omega, ite_false]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, show len - c < q by omega, ite_true]

/-- The seed's octets at `W 1`, and its witnesses after them. -/
theorem seedStart_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {c q : Nat} {ptr : Addr} (hx0 : s.gpr .x0 = BitVec.ofNat 64 c)
    (h14 : W 14 = ptr) (hq2 : q = 20 ∨ q = 32) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.seedStart q)) s fun t =>
      t.mem = ((((s.mem.writeW (off F 88) ptr).writeW (off F 8) (off ptr c)).writeW (off F 128)
        (BitVec.ofNat 64 (c + q))).writeW (off F 104) (0 : BitVec 64)) ∧ Keep [.x0, .x3, .x4] s t := by
  have w14 : s.mem.readW (s.sp + BitVec.ofNat 64 112) 64 = ptr := by
    rw [L.sp]; exact (R.fr 14 (by decide)).trans h14
  have l112 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 112) 8 := by rw [L.sp]; exact L.ld (d := 112) (by decide)
  have s8 : InRegions s.wr (s.sp + BitVec.ofNat 64 8) 8 := by rw [L.sp]; exact L.st (d := 8) (by decide)
  have s128 : InRegions s.wr (s.sp + BitVec.ofNat 64 128) 8 := by rw [L.sp]; exact L.st (d := 128) (by decide)
  have s88 : InRegions s.wr (s.sp + BitVec.ofNat 64 88) 8 := by rw [L.sp]; exact L.st (d := 88) (by decide)
  have s104 : InRegions s.wr (s.sp + BitVec.ofNat 64 104) 8 := by rw [L.sp]; exact L.st (d := 104) (by decide)
  have hm := movi_small (show q < 2 ^ 16 by omega)
  refine WP.keep [.x0, .x3, .x4] ?_ (by rcases hq2 with rfl | rfl <;> decide) rfl
    (by rcases hq2 with rfl | rfl <;> decide +kernel)
  unfold Impl.Dsa.AArch64.Generation.Refill.seedStart
  brun [State.write, exec_ldrSp (off := 112) (by decide), exec_storeSp (off := 8) (by decide),
    exec_storeSp (off := 128) (by decide), exec_storeSp (off := 88) (by decide), exec_storeSp (off := 104) (by decide),
    w14, l112, s8, s128, s88, s104, hx0, hm, movi_small (show 0 < 2 ^ 16 by decide)]
  rw [L.sp, ← BitVec.ofNat_add]
  rfl

/-- A rejected seed: one fewer left. -/
theorem rejected_run {s : State} {F : Addr} (hsp : s.sp = F) (hv : (⟨F, 480⟩ : Region) ∈ s.wr)
    {n : Nat} (hn : n + 1 < 2 ^ 64) (h2 : ctlWord s.mem F 2 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.rejected) s fun t =>
      t.mem = s.mem.writeW (off F 464) (BitVec.ofNat 64 n) ∧ Keep [.x3] s t := by
  have w2 : s.mem.readW (s.sp + BitVec.ofNat 64 464) 64 = BitVec.ofNat 64 (n + 1) := by rw [hsp]; exact h2
  have l464 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 464) 8 := by rw [hsp]; exact ctl_in' hv (k := 2) (by decide)
  have s464 : InRegions s.wr (s.sp + BitVec.ofNat 64 464) 8 := by rw [hsp]; exact ctl_in hv (k := 2) (by decide)
  have e : BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 n := by
    rw [Offset.ofNat_sub_ofNat (by omega)]; rfl
  refine WP.keep [.x3] ?_ (by decide)
  simp only [Impl.Dsa.AArch64.Generation.Refill.rejected, Impl.Dsa.AArch64.Generation.Refill.ctl, Nat.reduceMul,
    Nat.reduceAdd]
  brun [State.write, exec_ldrSp (off := 464) (by decide), exec_storeSp (off := 464) (by decide),
    exec_subImm_x' (by decide : 1 < 4096), w2, l464, s464, e]
  rw [hsp]

/-! ## Contexts -/

theorem tapeMemory_frame {g : GenerationGeometry} {tape : GenerationTape g} {s t : State}
    (h : GenerationTapeMemory tape s) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, (⟨tape.ptr, tape.bytes.length⟩ : Region).Disjoint r) (hr : t.rd = s.rd) (hw : t.wr = s.wr) :
    GenerationTapeMemory tape t where
  cover := by rw [hr, hw]; exact h.cover
  bytes := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt hf hd (Nat.le_of_lt tape.size)]
    exact h.bytes

theorem genMem_keep {p : GenerationContext} {W : Nat → BitVec 64} {s t : State} (hm : GenerationMemory p W s)
    (hmem : t.mem = s.mem) {rs : List Reg} (hk : Keep rs s t) : GenerationMemory p W t := by
  obtain ⟨V, R⟩ := hm.rep
  have Rt : Rep t.mem p.geo.F p.geo.hash V W := hmem ▸ R
  exact hm.frame (lay_of_rep hm.layout R Rt rfl hk.sp hk.wr) ⟨V, Rt⟩ (fun _ _ => rfl)
    (by rw [hmem]; exact Frame.refl _ _) hk.rd hk.wr

theorem ofNat_beq_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  by_cases hn : n = 0
  · subst hn; rfl
  · have : BitVec.ofNat 64 n ≠ 0 := fun e => hn (by
      have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this; exact this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [hn]

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

/-- An `h` tape inside the random tape. -/
def HsIn (hs : GenerationTape (refillGeometry h)) : Prop :=
  Region.Sub ⟨hs.ptr, hs.bytes.length⟩ ⟨(randTape h).ptr, (randTape h).bytes.length⟩

theorem rand_ctl : (⟨(randTape h).ptr, (randTape h).bytes.length⟩ : Region).Disjoint (ctlRegion (refillBase s₀)) := by
  change (⟨s₀.gpr .x3, (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat).length⟩ : Region).Disjoint _
  rw [bytesAt_length]
  exact h.frame_disjoint (r := inRand s₀) (by simp) (by decide)

theorem ctl_changed : ∀ r ∈ (refillContext h).changed, (ctlRegion (refillBase s₀)).Disjoint r := by
  intro r hr
  simp only [GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.ctl_arena
  · exact ctl_frame _
  · exact ctl_below _ (by decide)

/-- The search's memory across a write of the controller's words. -/
theorem GenerationMemory.ctlFrame {hs : GenerationTape (refillGeometry h)} (hin : HsIn h hs)
    {W : Nat → BitVec 64} {s t : State} (hm : GenerationMemory ((refillContext h).withHs hs) W s)
    (hf : Frame [ctlRegion (refillBase s₀)] s.mem t.mem) (hsp : t.sp = s.sp)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) : GenerationMemory ((refillContext h).withHs hs) W t := by
  obtain ⟨V, R⟩ := hm.rep
  have Rt : Rep t.mem (refillBase s₀) (refillGeometry h).hash V W :=
    rep_of_disjoint_frame R hf (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact (ctl_frame _).symm)
      (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact h.ctl_hash.symm)
  exact ⟨lay_of_rep hm.layout R Rt rfl hsp hw, ⟨V, Rt⟩, hm.slots, hm.scratch.congr hw,
    tapeMemory_frame hm.seeds hf (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact rand_ctl h) hr hw,
    tapeMemory_frame hm.hs hf (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact (rand_ctl h).sub_left hin)
      hr hw,
    tapeMemory_frame hm.rand hf (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact rand_ctl h) hr hw⟩

theorem ctlWord_changed {m m' : Mem} (hf : Frame (refillContext h).changed m m') {k : Nat} (hk : k < 4) :
    ctlWord m' (refillBase s₀) k = ctlWord m (refillBase s₀) k :=
  ctlWord_frame hf (ctl_changed h) hk

/-- A status word stored. -/
theorem statusMem_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State} (hm : GenerationMemory p W s)
    (status : Nat) (hs : status < 2 ^ 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.stackStatus status)) s fun t =>
      GenerationMemory p (upd W 19 (BitVec.ofNat 64 status)) t ∧ Frame p.changed s.mem t.mem ∧ Keep [.x3] s t := by
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (stackStatus_ok hm.layout R status hs) fun t ⟨Lt, Rt, ot, kt⟩ => ?_
  have ft := GenerationContext.status_frame ot
  refine ⟨hm.frame Lt ⟨V, Rt⟩ ?_ ft kt.rd kt.wr, ft, kt⟩
  intro k hk
  simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The status compared with 3. -/
theorem statusTest_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State} (hm : GenerationMemory p W s) :
    WP isa (.block Impl.Dsa.AArch64.Generation.tapeStatus) s fun t =>
      eval (.zero .x .x0) t = some (W 19 == 3) ∧ GenerationMemory p W t ∧ t.mem = s.mem ∧ Keep [.x0] s t := by
  obtain ⟨V, R⟩ := hm.rep
  exact WP.mono (tapeStatus_ok hm.layout R) fun t ⟨hz, hmt, kt⟩ => ⟨hz, genMem_keep hm hmt kt, hmt, kt⟩

/-- The whole search's result. -/
def total : Spec.Dsa.ParameterSearchResult :=
  Spec.Dsa.parameterSearch pBytes (s₀.mem.readW (s₀.gpr .x7) 64).toNat (randTape h).bytes

/-- The `refillAttempt` of the seed at `c`. -/
def seedResult (c : Nat) : Option (Option Spec.Dsa.Params × List Byte) :=
  VG.Proof.Dsa.Generation.refillAttempt pBytes (Spec.Dsa.generationQLen pBytes)
    (((randTape h).bytes.drop c).take (Spec.Dsa.generationQLen pBytes))
    ((randTape h).bytes.drop (c + Spec.Dsa.generationQLen pBytes))

/-- Where the next seed starts after a rejected one at `c`. -/
def nextUsed (c : Nat) : Nat :=
  match seedResult h c with
  | some (_, rest) => (randTape h).bytes.length - rest.length
  | none => c

/-- The status the controller ends with, from `n` seeds left at `c`. -/
def exitStatus (n c : Nat) : Nat :=
  if n = 0 then 2 else if (randTape h).bytes.length - c < Spec.Dsa.generationQLen pBytes then 0 else
    match seedResult h c with
    | some (some _, _) => 1
    | _ => 0

/-- The controller's state with `n` seeds it may still reject, the next
starting at `c`, from the loop's entry `v`. -/
def LoopState (v : State) (n c : Nat) (t : State) : Prop :=
  ∃ (hs : GenerationTape (refillGeometry h)) (W : Nat → BitVec 64), HsIn h hs ∧
    GenerationMemory ((refillContext h).withHs hs) W t ∧ W 16 = BitVec.ofNat 64 c ∧ W 10 = 0 ∧
    c ≤ (randTape h).bytes.length ∧
    ctlWord t.mem (refillBase s₀) 0 = s₀.gpr .x2 ∧ ctlWord t.mem (refillBase s₀) 1 = s₀.gpr .x7 ∧
    ctlWord t.mem (refillBase s₀) 2 = BitVec.ofNat 64 n ∧ n ≤ Spec.Dsa.parameterSeeds ∧
    total h = (Spec.Dsa.parameterSearch pBytes n ((randTape h).bytes.drop c)).consume c [] ∧
    Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t.mem ∧ t.rd = v.rd ∧ t.wr = v.wr

/-- How the controller's loop ends, from its last iteration's `n` and `c`. -/
def LoopDone (v : State) (n c : Nat) (t : State) : Prop :=
  ∃ (hs : GenerationTape (refillGeometry h)) (W : Nat → BitVec 64), HsIn h hs ∧
    GenerationMemory ((refillContext h).withHs hs) W t ∧
    ctlWord t.mem (refillBase s₀) 0 = s₀.gpr .x2 ∧ ctlWord t.mem (refillBase s₀) 1 = s₀.gpr .x7 ∧
    Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t.mem ∧ t.rd = v.rd ∧ t.wr = v.wr ∧
    W 19 = BitVec.ofNat 64 (exitStatus h n c) ∧ ctlWord t.mem (refillBase s₀) 3 = BitVec.ofNat 64 c ∧
    ((W 19 = 2 ∧ c ≤ (randTape h).bytes.length ∧ total h = ⟨.exhausted, c, []⟩) ∨
      (W 19 = 0 ∧ c ≤ (randTape h).bytes.length ∧
        ctlWord t.mem (refillBase s₀) 2 = BitVec.ofNat 64 n ∧ n ≤ Spec.Dsa.parameterSeeds ∧
        total h = VG.Proof.Dsa.Generation.ranOutResult pBytes n ((randTape h).bytes.length - c) c) ∨
      (W 19 = 1 ∧ ∃ a u, u ≤ (randTape h).bytes.length ∧ W 16 = BitVec.ofNat 64 u ∧
        total h = ⟨.accepted a, u, []⟩ ∧
        Spec.Rsa.bytesAt t.mem (off (s₀.gpr .x5) VG.Impl.Dsa.Generation.Layout.packed)
          (2 * pBytes + Spec.Dsa.generationQLen pBytes) = Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes) a))

/-- What the controller needs of a seed's attempt (`refillAttempt_ok` for this search's context). -/
def AttemptOk (attempt : Prog isa) : Prop :=
  ∀ (hs : GenerationTape (refillGeometry h)) (W : Nat → BitVec 64) (t : State) (seed : GenerationTape (refillGeometry h)),
    HsIn h hs → GenerationMemory ((refillContext h).withHs hs) W t →
    seed.bytes.length = Spec.Dsa.generationQLen pBytes → GenerationTapeMemory seed t → W 1 = seed.ptr →
    ∀ used, W 16 = BitVec.ofNat 64 used → used ≤ (randTape h).bytes.length →
    WP isa attempt t (RefillFinished ((refillContext h).withHs hs) W
      (VG.Proof.Dsa.Generation.refillAttempt pBytes (Spec.Dsa.generationQLen pBytes) seed.bytes
        ((randTape h).bytes.drop used)) t)

theorem ctlWord_eq_of_mem {m m' : Mem} (he : m' = m) (F : Addr) (k : Nat) : ctlWord m' F k = ctlWord m F k := by
  rw [he]

/-- The controller's state across a step that keeps the memory. -/
theorem LoopState.keep {v : State} {n c : Nat} {t t' : State} (hi : LoopState h v n c t) (hmem : t'.mem = t.mem)
    {rs : List Reg} (hk : Keep rs t t') : LoopState h v n c t' := by
  obtain ⟨hs, W, hin, hm, h16, h10, hc, c0, c1, c2, hn, htot, hf, hrd, hwr⟩ := hi
  exact ⟨hs, W, hin, genMem_keep hm hmem hk, h16, h10, hc, by rw [ctlWord_eq_of_mem hmem, c0],
    by rw [ctlWord_eq_of_mem hmem, c1], by rw [ctlWord_eq_of_mem hmem, c2], hn, htot, by rw [hmem]; exact hf,
    hk.rd.trans hrd, hk.wr.trans hwr⟩

/-- The start of an iteration: the seed's start in `x0` and `ctl 3`, the
seeds left in `x3`. -/
theorem iterStart_ok {v : State} (hv : (⟨refillBase s₀, 480⟩ : Region) ∈ v.wr) {n c : Nat} {t : State}
    (hi : LoopState h v n c t) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.iterStart) t fun t₁ =>
      LoopState h v n c t₁ ∧ ctlWord t₁.mem (refillBase s₀) 3 = BitVec.ofNat 64 c ∧
        t₁.gpr .x0 = BitVec.ofNat 64 c ∧ t₁.gpr .x3 = BitVec.ofNat 64 n := by
  obtain ⟨hs, W, hin, hm, h16, h10, hc, c0, c1, c2, hn, htot, hf, hrd, hwr⟩ := hi
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (iterStart_run hm.layout R (hwr ▸ hv) h16 c2) fun t₁ ⟨⟨x0₁, x3₁, mem₁⟩, k₁⟩ => ?_
  have fr₁ : Frame [ctlRegion (refillBase s₀)] t.mem t₁.mem := by
    rw [mem₁]; exact ctl_write t.mem _ (k := 3) (by decide) _
  have ctl₁ : ∀ j < 3, ctlWord t₁.mem (refillBase s₀) j = ctlWord t.mem (refillBase s₀) j := fun j hj => by
    rw [mem₁]; exact ctlWord_write_other t.mem _ (k := 3) (by omega) (by decide) (by omega) _
  refine ⟨⟨hs, W, hin, GenerationMemory.ctlFrame h hin hm fr₁ k₁.sp k₁.rd k₁.wr, h16, h10, hc,
    by rw [ctl₁ 0 (by decide), c0], by rw [ctl₁ 1 (by decide), c1], by rw [ctl₁ 2 (by decide), c2], hn, htot,
    hf.trans (fr₁.mono fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..),
    k₁.rd.trans hrd, k₁.wr.trans hwr⟩, by rw [mem₁]; exact ctlWord_write_self t.mem _ 3 _, x0₁, x3₁⟩

/-- Whether fewer octets than a seed's are left from `c`. -/
def short (c : Nat) : Prop := (randTape h).bytes.length - c < Spec.Dsa.generationQLen pBytes

instance (c : Nat) : Decidable (short h c) := by unfold short; infer_instance

theorem roomCheck_ok {v : State} {n c : Nat} {t : State} (hi : LoopState h v n c t)
    (x0 : t.gpr .x0 = BitVec.ofNat 64 c) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.roomCheck (Spec.Dsa.generationQLen pBytes))) t fun t₂ =>
      LoopState h v n c t₂ ∧ t₂.mem = t.mem ∧ t₂.gpr .x0 = BitVec.ofNat 64 c ∧
        t₂.gpr .x3 = BitVec.ofNat 64 (if short h c then 1 else 0) := by
  have hi' := hi
  obtain ⟨hs, W, hin, hm, h16, h10, hc, c0, c1, c2, hn, htot, hf, hrd, hwr⟩ := hi
  have hq2 : Spec.Dsa.generationQLen pBytes = 20 ∨ Spec.Dsa.generationQLen pBytes = 32 := by
    unfold Spec.Dsa.generationQLen; split <;> simp
  have h15 : W 15 = BitVec.ofNat 64 (randTape h).bytes.length :=
    (hm.slots 15 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randLengthSlot
  obtain ⟨V, R⟩ := hm.rep
  exact WP.mono (roomCheck_run hm.layout R x0 h15 hc (randTape h).size hq2) fun t₂ ⟨⟨x3₂, mem₂⟩, k₂⟩ =>
    ⟨hi'.keep h mem₂ k₂, mem₂, (k₂.gpr .x0 (by decide)).trans x0, x3₂⟩

/-- The seed at `c`. -/
def seedAt (c : Nat) (room : c + Spec.Dsa.generationQLen pBytes ≤ (randTape h).bytes.length) :
    GenerationTape (refillGeometry h) :=
  (randTape h).slice c (Spec.Dsa.generationQLen pBytes) room

/-- Before a seed's attempt: the seed at `W 1`, its witnesses from `W 16`,
the context's own empty `h` tape. -/
def Seeded (v : State) (n c : Nat) (t : State) : Prop :=
  ∃ (room : c + Spec.Dsa.generationQLen pBytes ≤ (randTape h).bytes.length) (W : Nat → BitVec 64),
    GenerationMemory (refillContext h) W t ∧ W 1 = (seedAt h c room).ptr ∧
    W 16 = BitVec.ofNat 64 (c + Spec.Dsa.generationQLen pBytes) ∧ W 10 = 0 ∧
    GenerationTapeMemory (seedAt h c room) t ∧
    ctlWord t.mem (refillBase s₀) 0 = s₀.gpr .x2 ∧ ctlWord t.mem (refillBase s₀) 1 = s₀.gpr .x7 ∧
    ctlWord t.mem (refillBase s₀) 2 = BitVec.ofNat 64 n ∧ ctlWord t.mem (refillBase s₀) 3 = BitVec.ofNat 64 c ∧
    n ≤ Spec.Dsa.parameterSeeds ∧
    total h = (Spec.Dsa.parameterSearch pBytes n ((randTape h).bytes.drop c)).consume c [] ∧
    Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t.mem ∧ t.rd = v.rd ∧ t.wr = v.wr

theorem seedStart_ok {v : State} {n c : Nat} {t : State} (hi : LoopState h v n c t)
    (c3 : ctlWord t.mem (refillBase s₀) 3 = BitVec.ofNat 64 c) (x0 : t.gpr .x0 = BitVec.ofNat 64 c)
    (room : c + Spec.Dsa.generationQLen pBytes ≤ (randTape h).bytes.length) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.seedStart (Spec.Dsa.generationQLen pBytes))) t
      (Seeded h v n c) := by
  obtain ⟨hs, W, hin, hm₂, h16, h10, hc, c0, c1, c2, hn, htot, hf, hrd, hwr⟩ := hi
  have hq2 : Spec.Dsa.generationQLen pBytes = 20 ∨ Spec.Dsa.generationQLen pBytes = 32 := by
    unfold Spec.Dsa.generationQLen; split <;> simp
  have h14 : W 14 = (randTape h).ptr :=
    (hm₂.slots 14 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randSlot
  obtain ⟨V₂, R₂⟩ := hm₂.rep
  have L₂ := hm₂.layout
  refine WP.mono (seedStart_run L₂ R₂ x0 h14 hq2) fun t₃ ⟨mem₃, k₃⟩ => ?_
  let W₃ := upd (upd (upd (upd W 11 (randTape h).ptr) 1 (off (randTape h).ptr c)) 16
    (BitVec.ofNat 64 (c + Spec.Dsa.generationQLen pBytes))) 13 0
  have R₃ : Rep t₃.mem (refillBase s₀) (refillGeometry h).hash V₂ W₃ := by
    rw [mem₃]
    exact (((R₂.wf L₂.geo (k := 11) (by decide) _).wf L₂.geo (k := 1) (by decide) _).wf L₂.geo (k := 16)
      (by decide) _).wf L₂.geo (k := 13) (by decide) _
  have f₃ : Frame [⟨refillBase s₀, frameBytes⟩] t.mem t₃.mem := by
    rw [mem₃]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (cF _ (d := 88) (by decide))).writeW
      List.mem_cons_self _ (cF _ (d := 8) (by decide))).writeW
      List.mem_cons_self _ (cF _ (d := 128) (by decide))).writeW List.mem_cons_self _ (cF _ (d := 104) (by decide))
  have fc₃ : Frame (refillContext h).changed t.mem t₃.mem := GenerationContext.frame_single f₃
  have rand₃ := hm₂.rand.frame (p := (refillContext h).withHs hs) fc₃ k₃.rd k₃.wr
  have hm₃ : GenerationMemory (refillContext h) W₃ t₃ := by
    refine ⟨lay_of_rep L₂ R₂ R₃ (by simp [W₃, upd]) k₃.sp k₃.wr, ⟨V₂, R₃⟩, ?_, hm₂.scratch.congr k₃.wr,
      hm₂.seeds.frame (p := (refillContext h).withHs hs) fc₃ k₃.rd k₃.wr, rand₃.slice (Nat.zero_le _), rand₃⟩
    intro k hk
    by_cases e11 : k = 11
    · subst e11; simp [W₃, upd, refillContext, refillWords, randTape]
    by_cases e13 : k = 13
    · subst e13; simp [W₃, upd, refillContext, refillWords]
    have e1 : k ≠ 1 := by rintro rfl; simp [generationSlots] at hk
    have e16 : k ≠ 16 := by rintro rfl; simp [generationSlots] at hk
    simp only [W₃, upd, e11, e13, e1, e16, ite_false]
    rw [hm₂.slots k hk]
    simp [GenerationContext.withHs, e11, e13]
  have cw₃ : ∀ j < 4, ctlWord t₃.mem (refillBase s₀) j = ctlWord t.mem (refillBase s₀) j := fun j hj =>
    ctlWord_changed h fc₃ hj
  refine ⟨room, W₃, hm₃, by simp [W₃, upd, seedAt, GenerationTape.slice], by simp [W₃, upd],
    by simpa [W₃, upd] using h10, hm₃.rand.slice room, by rw [cw₃ 0 (by decide), c0], by rw [cw₃ 1 (by decide), c1],
    by rw [cw₃ 2 (by decide), c2], by rw [cw₃ 3 (by decide), c3], hn, htot,
    hf.trans (fc₃.mono fun r hr => List.mem_cons_of_mem _ hr), k₃.rd.trans hrd, k₃.wr.trans hwr⟩

/-- Whether the controller goes on after the seed at `c`, with `n` seeds left. -/
def continues (n c : Nat) : Bool :=
  n != 0 && !decide (short h c) &&
    match seedResult h c with
    | some (none, _) => true
    | _ => false

/-- After one iteration from `n` seeds left at `c`. -/
def StepPost (v : State) (n c : Nat) (t : State) : Prop :=
  eval (.zero .x .x0) t = some (continues h n c) ∧ (continues h n c = false → LoopDone h v n c t) ∧
    (continues h n c = true → ∃ m, n = m + 1 ∧ LoopState h v m (nextUsed h c) t)

theorem stepPost_done {v t : State} {n c : Nat} (hc : continues h n c = false)
    (z : eval (.zero .x .x0) t = some false) (d : LoopDone h v n c t) : StepPost h v n c t :=
  ⟨z.trans (by rw [hc]), fun _ => d, fun e => by rw [hc] at e; cases e⟩

theorem step_ok {attempt : Prog isa}
    (hA : AttemptOk h attempt) {v : State} (hv : (⟨refillBase s₀, 480⟩ : Region) ∈ v.wr) (n c : Nat) (t : State)
    (hi : LoopState h v n c t) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.iteration attempt (Spec.Dsa.generationQLen pBytes)) t
      (StepPost h v n c) := by
  have hpos : 0 < pBytes := by have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega
  have hn₀ : n ≤ Spec.Dsa.parameterSeeds := by obtain ⟨_, _, _, _, _, _, _, _, _, _, hn, _⟩ := hi; exact hn
  have hseeds : n < 2 ^ 63 := by unfold Spec.Dsa.parameterSeeds at hn₀; omega
  simp only [Impl.Dsa.AArch64.Generation.Refill.iteration, VG.Impl.Bignum.AArch64.seqs]
  apply WP.seq
  refine WP.mono (iterStart_ok h hv hi) fun t₁ ⟨hi₁, c3, x0₁, x3₁⟩ => ?_
  have ev₁ : eval (.zero .x .x3) t₁ = some (decide (n = 0)) := by
    simp only [eval, State.read, x3₁, BitVec.setWidth_eq, ofNat_beq_zero (by omega : n < 2 ^ 64)]
  apply WP.seq
  by_cases hn0 : n = 0
  · subst hn0
    obtain ⟨hs, W, hin, hm₁, _, _, hc, c0, c1, _, _, htot, fv₁, rd₁, wr₁⟩ := hi₁
    refine WP.ite true (ev₁.trans (by simp)) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    refine WP.mono (statusMem_ok hm₁ 2 (by decide)) fun t₂ ⟨hm₂, f₂, k₂⟩ => ?_
    refine WP.mono (statusTest_ok hm₂) fun t₃ ⟨z₃, hm₃, mem₃, k₃⟩ =>
      stepPost_done h (by simp [continues]) (z₃.trans rfl) ?_
    refine ⟨hs, _, hin, hm₃, ?_, ?_, ?_, k₃.rd.trans (k₂.rd.trans rd₁), k₃.wr.trans (k₂.wr.trans wr₁),
      by simp [upd, exitStatus], ?_, Or.inl ⟨rfl, hc, ?_⟩⟩
    · rw [ctlWord_eq_of_mem mem₃, ctlWord_changed h f₂ (by decide), c0]
    · rw [ctlWord_eq_of_mem mem₃, ctlWord_changed h f₂ (by decide), c1]
    · rw [mem₃]; exact fv₁.trans (f₂.mono fun r hr => List.mem_cons_of_mem _ hr)
    · rw [ctlWord_eq_of_mem mem₃, ctlWord_changed h f₂ (by decide), c3]
    · rw [htot, VG.Proof.Dsa.Generation.search_zero]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  refine WP.ite false (ev₁.trans (by simp)) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
  apply WP.seq
  refine WP.mono (roomCheck_ok h hi₁ x0₁) fun t₂ ⟨hi₂, mem₂, x0₂, x3₂⟩ => ?_
  have ev₂ : eval (.nonzero .x .x3) t₂ = some (decide (short h c)) := by
    simp only [eval, State.read, x3₂, BitVec.setWidth_eq]
    by_cases hr : short h c <;> simp [hr]
  by_cases hr : short h c
  · obtain ⟨hs, W, hin, hm₂, _, _, hc, c0, c1, c2, hn, htot, fv₂, rd₂, wr₂⟩ := hi₂
    refine WP.ite true (ev₂.trans (by simp [hr])) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    refine WP.mono (statusMem_ok hm₂ 0 (by decide)) fun t₃ ⟨hm₃, f₃, k₃⟩ => ?_
    refine WP.mono (statusTest_ok hm₃) fun t₄ ⟨z₄, hm₄, mem₄, k₄⟩ =>
      stepPost_done h (by simp [continues, hr]) (z₄.trans rfl) ?_
    have cw : ∀ j < 4, ctlWord t₄.mem (refillBase s₀) j = ctlWord t₂.mem (refillBase s₀) j := fun j hj => by
      rw [ctlWord_eq_of_mem mem₄, ctlWord_changed h f₃ hj]
    refine ⟨hs, _, hin, hm₄, by rw [cw 0 (by decide), c0], by rw [cw 1 (by decide), c1], ?_,
      k₄.rd.trans (k₃.rd.trans rd₂), k₄.wr.trans (k₃.wr.trans wr₂), by simp [upd, exitStatus, show
        (randTape h).bytes.length - c < Spec.Dsa.generationQLen pBytes from hr],
      by rw [cw 3 (by decide), ctlWord_eq_of_mem mem₂, c3],
      Or.inr (Or.inl ⟨rfl, hc, by rw [cw 2 (by decide), c2], hn, ?_⟩)⟩
    · rw [mem₄]; exact fv₂.trans (f₃.mono fun r hr => List.mem_cons_of_mem _ hr)
    · rw [htot]; exact VG.Proof.Dsa.Generation.search_short hr
  refine WP.ite false (ev₂.trans (by simp [hr])) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
  have room : c + Spec.Dsa.generationQLen pBytes ≤ (randTape h).bytes.length := by
    have hq2 : Spec.Dsa.generationQLen pBytes = 20 ∨ Spec.Dsa.generationQLen pBytes = 32 := by
      unfold Spec.Dsa.generationQLen; split <;> simp
    unfold short at hr; omega
  apply WP.seq
  refine WP.mono (seedStart_ok h hi₂ (by rw [ctlWord_eq_of_mem mem₂, c3]) x0₂ room) fun t₃ hs₃ => ?_
  obtain ⟨_, W₃, hm₃, w1, w16, w10, seedMem, c0, c1, c2, c3₃, hn, htot, fv₃, rd₃, wr₃⟩ := hs₃
  have hc : c ≤ (randTape h).bytes.length := by omega
  have hm₃' : GenerationMemory ((refillContext h).withHs (refillContext h).hs) W₃ t₃ := by
    rw [GenerationContext.withHs_self]; exact hm₃
  have hin₀ : HsIn h (refillContext h).hs := by
    intro a ha
    simp [Region.Contains, refillContext, GenerationTape.slice] at ha
  have seedLen : (seedAt h c room).bytes.length = Spec.Dsa.generationQLen pBytes := by
    simp only [seedAt, GenerationTape.slice, List.length_take, List.length_drop]; omega
  apply WP.seq
  refine WP.mono (hA _ W₃ t₃ _ hin₀ hm₃' seedLen seedMem w1 (c + Spec.Dsa.generationQLen pBytes) w16 room)
    fun t₅ hfin => ?_
  obtain ⟨hs', W', u, sub', hm₅', hu, h16', slots₅, outcome, f₅, rd₅, wr₅⟩ := hfin
  have hm₅ : GenerationMemory ((refillContext h).withHs hs') W' t₅ :=
    GenerationContext.withHs_withHs (refillContext h) _ hs' ▸ hm₅'
  have hin' : HsIn h hs' := sub'
  have w10' : W' 10 = 0 := by rw [slots₅ 10 (by simp [refillSlots])]; exact w10
  have cw₅ : ∀ j < 4, ctlWord t₅.mem (refillBase s₀) j = ctlWord t₃.mem (refillBase s₀) j := fun j hj =>
    ctlWord_changed h f₅ hj
  have fv₅ : Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t₅.mem :=
    fv₃.trans (f₅.mono fun r hr => List.mem_cons_of_mem _ hr)
  have rd₅' : t₅.rd = v.rd := rd₅.trans rd₃
  have wr₅' : t₅.wr = v.wr := wr₅.trans wr₃
  change SeedOutcome _ (seedResult h c) W' u t₅ at outcome
  apply WP.seq
  refine WP.mono (statusTest_ok hm₅) fun t₆ ⟨z₆, hm₆, mem₆, k₆⟩ => ?_
  have cw₆ : ∀ j < 4, ctlWord t₆.mem (refillBase s₀) j = ctlWord t₃.mem (refillBase s₀) j := fun j hj => by
    rw [ctlWord_eq_of_mem mem₆, cw₅ j hj]
  have hr' : ¬ (randTape h).bytes.length - c < Spec.Dsa.generationQLen pBytes := hr
  rcases outcome with ⟨h19, hres⟩ | ⟨h19, hres⟩ | ⟨h19, a, hres, bytes⟩
  · refine WP.ite false (z₆.trans (by rw [h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => WP.block_nil ?_)
    refine WP.mono (statusTest_ok hm₆) fun t₇ ⟨z₇, hm₇, mem₇, k₇⟩ =>
      stepPost_done h (by simp [continues, hr, hres]) (z₇.trans (by rw [h19]; rfl)) ?_
    refine ⟨hs', W', hin', hm₇, by rw [ctlWord_eq_of_mem mem₇, cw₆ 0 (by decide), c0],
      by rw [ctlWord_eq_of_mem mem₇, cw₆ 1 (by decide), c1], by rw [mem₇, mem₆]; exact fv₅,
      k₇.rd.trans (k₆.rd.trans rd₅'), k₇.wr.trans (k₆.wr.trans wr₅'),
      by rw [h19]; simp [exitStatus, hr', hres], by rw [ctlWord_eq_of_mem mem₇, cw₆ 3 (by decide), c3₃],
      Or.inr (Or.inl ⟨h19, hc, by rw [ctlWord_eq_of_mem mem₇, cw₆ 2 (by decide), c2], hn, ?_⟩)⟩
    rw [htot]; exact VG.Proof.Dsa.Generation.search_attemptNone hpos room hres
  · refine WP.ite true (z₆.trans (by rw [h19]; rfl)) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    have c2₆ : ctlWord t₆.mem (refillBase s₀) 2 = BitVec.ofNat 64 (n' + 1) := by
      rw [cw₆ 2 (by decide), c2]
    have hv₆ : (⟨refillBase s₀, 480⟩ : Region) ∈ t₆.wr := by rw [k₆.wr, wr₅']; exact hv
    refine WP.mono (rejected_run (k₆.sp.trans hm₅.layout.sp) hv₆ (by omega) c2₆) fun t₇ ⟨mem₇, k₇⟩ => ?_
    have fr₇ : Frame [ctlRegion (refillBase s₀)] t₆.mem t₇.mem := by
      rw [mem₇]; exact ctl_write t₆.mem _ (k := 2) (by decide) _
    have hm₇ := GenerationMemory.ctlFrame h hin' hm₆ fr₇ k₇.sp k₇.rd k₇.wr
    have cw₇ : ∀ j < 2, ctlWord t₇.mem (refillBase s₀) j = ctlWord t₆.mem (refillBase s₀) j := fun j hj => by
      rw [mem₇]; exact ctlWord_write_other t₆.mem _ (k := 2) (by omega) (by decide) (by omega) _
    have hu' : u ≤ (randTape h).bytes.length := hu
    have next : nextUsed h c = u := by
      simp only [nextUsed, hres, List.length_drop]
      change (randTape h).bytes.length - ((randTape h).bytes.length - u) = u
      omega
    have hcont : continues h (n' + 1) c = true := by simp [continues, hr, hres]
    refine WP.mono (statusTest_ok hm₇) fun t₈ ⟨z₈, hm₈, mem₈, k₈⟩ =>
      ⟨z₈.trans (by rw [h19, hcont]; rfl), fun e => (by rw [hcont] at e; cases e), fun _ => ⟨n', rfl, ?_⟩⟩
    rw [next]
    refine ⟨hs', W', hin', hm₈, h16', w10', hu,
      by rw [ctlWord_eq_of_mem mem₈, cw₇ 0 (by decide), cw₆ 0 (by decide), c0],
      by rw [ctlWord_eq_of_mem mem₈, cw₇ 1 (by decide), cw₆ 1 (by decide), c1],
      by rw [ctlWord_eq_of_mem mem₈, mem₇]; exact ctlWord_write_self t₆.mem _ 2 _, by omega, ?_, ?_,
      k₈.rd.trans (k₇.rd.trans (k₆.rd.trans rd₅')), k₈.wr.trans (k₇.wr.trans (k₆.wr.trans wr₅'))⟩
    · rw [htot]; exact VG.Proof.Dsa.Generation.search_rejected hpos room hu hres
    · rw [mem₈]; exact (mem₆ ▸ fv₅).trans (fr₇.mono fun r hr => by
        rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)
  · refine WP.ite false (z₆.trans (by rw [h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => WP.block_nil ?_)
    refine WP.mono (statusTest_ok hm₆) fun t₇ ⟨z₇, hm₇, mem₇, k₇⟩ =>
      stepPost_done h (by simp [continues, hr, hres]) (z₇.trans (by rw [h19]; rfl)) ?_
    refine ⟨hs', W', hin', hm₇, by rw [ctlWord_eq_of_mem mem₇, cw₆ 0 (by decide), c0],
      by rw [ctlWord_eq_of_mem mem₇, cw₆ 1 (by decide), c1], by rw [mem₇, mem₆]; exact fv₅,
      k₇.rd.trans (k₆.rd.trans rd₅'), k₇.wr.trans (k₆.wr.trans wr₅'),
      by rw [h19]; simp [exitStatus, hr', hres], by rw [ctlWord_eq_of_mem mem₇, cw₆ 3 (by decide), c3₃],
      Or.inr (Or.inr ⟨h19, a, u, hu, h16', ?_, by rw [mem₇, mem₆]; exact bytes⟩)⟩
    rw [htot]; exact VG.Proof.Dsa.Generation.search_accepted hpos room hu hres

theorem controller_ok {attempt : Prog isa}
    (hA : AttemptOk h attempt) {v : State} (hv : (⟨refillBase s₀, 480⟩ : Region) ∈ v.wr) (n c : Nat) (t : State)
    (hi : LoopState h v n c t) :
    WP isa (.loop (Impl.Dsa.AArch64.Generation.Refill.iteration attempt (Spec.Dsa.generationQLen pBytes))
      (.zero .x .x0)) t (fun t' => ∃ n c, LoopDone h v n c t') :=
  WP.loop (M := isa) (Q := fun t' => ∃ n c, LoopDone h v n c t') (fun n t => ∃ c, LoopState h v n c t)
    (fun n t ⟨c, hi⟩ => WP.mono (step_ok h hA hv n c t hi) fun t' ⟨e, d, k⟩ => by
      cases hc : continues h n c
      · exact Or.inl ⟨e.trans (by rw [hc]), n, c, d hc⟩
      · obtain ⟨m, hm, st⟩ := k hc
        exact Or.inr ⟨e.trans (by rw [hc]), m, by omega, _, st⟩) n t ⟨c, hi⟩

/-- The controller's state on entry. -/
theorem loop_initial {W : Nat → BitVec 64} {v : State} (hm : GenerationMemory (refillContext h) W v)
    (h16 : W 16 = 0) (h10 : W 10 = 0) (c0 : ctlWord v.mem (refillBase s₀) 0 = s₀.gpr .x2)
    (c1 : ctlWord v.mem (refillBase s₀) 1 = s₀.gpr .x7)
    (c2 : ctlWord v.mem (refillBase s₀) 2 = s₀.mem.readW (s₀.gpr .x7) 64) :
    LoopState h v (s₀.mem.readW (s₀.gpr .x7) 64).toNat 0 v := by
  refine ⟨(refillContext h).hs, W, ?_, (GenerationContext.withHs_self _).symm ▸ hm, h16, h10, Nat.zero_le _, c0, c1,
    by rw [c2, BitVec.ofNat_toNat, BitVec.setWidth_eq], h.seeds, ?_, Frame.refl _ _, rfl, rfl⟩
  · intro a ha
    simp [Region.Contains, refillContext, GenerationTape.slice] at ha
  · simp [total, Spec.Entropy.Result.consume]

end

end VG.Proof.Dsa.AArch64.Generation.Refill
