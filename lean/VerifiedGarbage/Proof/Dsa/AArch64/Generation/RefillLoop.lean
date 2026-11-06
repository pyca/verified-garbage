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
      t.mem = (s.mem.writeW (off F 8) (off ptr c)).writeW (off F 128) (BitVec.ofNat 64 (c + q)) ∧
        Keep [.x0, .x3, .x4] s t := by
  have w14 : s.mem.readW (s.sp + BitVec.ofNat 64 112) 64 = ptr := by
    rw [L.sp]; exact (R.fr 14 (by decide)).trans h14
  have l112 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 112) 8 := by rw [L.sp]; exact L.ld (d := 112) (by decide)
  have s8 : InRegions s.wr (s.sp + BitVec.ofNat 64 8) 8 := by rw [L.sp]; exact L.st (d := 8) (by decide)
  have s128 : InRegions s.wr (s.sp + BitVec.ofNat 64 128) 8 := by rw [L.sp]; exact L.st (d := 128) (by decide)
  have hm := movi_small (show q < 2 ^ 16 by omega)
  refine WP.keep [.x0, .x3, .x4] ?_ (by rcases hq2 with rfl | rfl <;> decide) rfl
    (by rcases hq2 with rfl | rfl <;> decide +kernel)
  unfold Impl.Dsa.AArch64.Generation.Refill.seedStart
  brun [State.write, exec_ldrSp (off := 112) (by decide), exec_storeSp (off := 8) (by decide),
    exec_storeSp (off := 128) (by decide), w14, l112, s8, s128, hx0, hm]
  rw [L.sp, ← BitVec.ofNat_add]

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

/-- The controller's invariant with `n` seeds it may still reject, from the loop's entry `v`. -/
def LoopInv (v : State) (n : Nat) (t : State) : Prop :=
  ∃ (hs : GenerationTape (refillGeometry h)) (W : Nat → BitVec 64) (c : Nat), HsIn h hs ∧
    GenerationMemory ((refillContext h).withHs hs) W t ∧ W 16 = BitVec.ofNat 64 c ∧ c ≤ (randTape h).bytes.length ∧
    ctlWord t.mem (refillBase s₀) 0 = s₀.gpr .x2 ∧ ctlWord t.mem (refillBase s₀) 1 = s₀.gpr .x7 ∧
    ctlWord t.mem (refillBase s₀) 2 = BitVec.ofNat 64 n ∧ n ≤ Spec.Dsa.parameterSeeds ∧
    total h = (Spec.Dsa.parameterSearch pBytes n ((randTape h).bytes.drop c)).consume c [] ∧
    Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t.mem ∧ t.rd = v.rd ∧ t.wr = v.wr

/-- How the controller's loop ends. -/
def LoopDone (v t : State) : Prop :=
  ∃ (hs : GenerationTape (refillGeometry h)) (W : Nat → BitVec 64), HsIn h hs ∧
    GenerationMemory ((refillContext h).withHs hs) W t ∧
    ctlWord t.mem (refillBase s₀) 0 = s₀.gpr .x2 ∧ ctlWord t.mem (refillBase s₀) 1 = s₀.gpr .x7 ∧
    Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t.mem ∧ t.rd = v.rd ∧ t.wr = v.wr ∧
    ((W 19 = 2 ∧ ∃ c, c ≤ (randTape h).bytes.length ∧ ctlWord t.mem (refillBase s₀) 3 = BitVec.ofNat 64 c ∧
        total h = ⟨.exhausted, c, []⟩) ∨
      (W 19 = 0 ∧ ∃ c k, c ≤ (randTape h).bytes.length ∧ ctlWord t.mem (refillBase s₀) 3 = BitVec.ofNat 64 c ∧
        ctlWord t.mem (refillBase s₀) 2 = BitVec.ofNat 64 k ∧ k ≤ Spec.Dsa.parameterSeeds ∧
        total h = VG.Proof.Dsa.Generation.ranOutResult pBytes k ((randTape h).bytes.length - c) c) ∨
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

theorem step_ok {qBytes : Nat} (hq : qBytes = Spec.Dsa.generationQLen pBytes) {attempt : Prog isa}
    (hA : AttemptOk h attempt) {v : State} (hv : (⟨refillBase s₀, 480⟩ : Region) ∈ v.wr) (n : Nat) (t : State)
    (hi : LoopInv h v n t) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.iteration attempt qBytes) t fun t' =>
      (eval (.zero .x .x0) t' = some false ∧ LoopDone h v t') ∨
        (eval (.zero .x .x0) t' = some true ∧ ∃ m < n, LoopInv h v m t') := by
  obtain ⟨hs, W, c, hin, hm, h16, hc, c0, c1, c2, hn, htot, hf, hrd, hwr⟩ := hi
  have hlen := (randTape h).size
  have hq2 : qBytes = 20 ∨ qBytes = 32 := by
    have := h.lengths; subst hq; unfold Spec.Dsa.generationLengthsValid at this
    rcases this with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> simp [e]
  have hpos : 0 < pBytes := by have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega
  have hseeds : n < 2 ^ 63 := by unfold Spec.Dsa.parameterSeeds at hn; omega
  have h15 : W 15 = BitVec.ofNat 64 (randTape h).bytes.length :=
    (hm.slots 15 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randLengthSlot
  have h14 : W 14 = (randTape h).ptr :=
    (hm.slots 14 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randSlot
  have hctl : ∀ u : State, u.wr = v.wr → (⟨refillBase s₀, 480⟩ : Region) ∈ u.wr := fun u hu => hu ▸ hv
  obtain ⟨V, R⟩ := hm.rep
  simp only [Impl.Dsa.AArch64.Generation.Refill.iteration, VG.Impl.Bignum.AArch64.seqs]
  apply WP.seq
  have L := hm.layout
  refine WP.mono (iterStart_run L R (hctl t hwr) h16 c2)
    fun t₁ ⟨⟨x0₁, x3₁, mem₁⟩, k₁⟩ => ?_
  have fr₁ : Frame [ctlRegion (refillBase s₀)] t.mem t₁.mem := by
    rw [mem₁]; exact ctl_write t.mem _ (k := 3) (by decide) _
  have hm₁ := GenerationMemory.ctlFrame h hin hm fr₁ k₁.sp k₁.rd k₁.wr
  have fv₁ : Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t₁.mem :=
    hf.trans (fr₁.mono fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)
  have ctl₁ : ∀ j < 3, ctlWord t₁.mem (refillBase s₀) j = ctlWord t.mem (refillBase s₀) j := fun j hj => by
    rw [mem₁]; exact ctlWord_write_other t.mem _ (k := 3) (by omega) (by decide) (by omega) _
  have c3 : ctlWord t₁.mem (refillBase s₀) 3 = BitVec.ofNat 64 c := by
    rw [mem₁]; exact ctlWord_write_self t.mem _ 3 _
  have rd₁ : t₁.rd = v.rd := k₁.rd.trans hrd
  have wr₁ : t₁.wr = v.wr := k₁.wr.trans hwr
  have ev₁ : eval (.zero .x .x3) t₁ = some (decide (n = 0)) := by
    simp only [eval, State.read, x3₁, BitVec.setWidth_eq, ofNat_beq_zero (by omega : n < 2 ^ 64)]
  apply WP.seq
  by_cases hn0 : n = 0
  · subst hn0
    refine WP.ite true (ev₁.trans (by simp)) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    refine WP.mono (statusMem_ok hm₁ 2 (by decide)) fun t₂ ⟨hm₂, f₂, k₂⟩ => ?_
    refine WP.mono (statusTest_ok hm₂) fun t₃ ⟨z₃, hm₃, mem₃, k₃⟩ => Or.inl ⟨z₃.trans rfl, ?_⟩
    refine ⟨hs, _, hin, hm₃, ?_, ?_, ?_, k₃.rd.trans (k₂.rd.trans rd₁), k₃.wr.trans (k₂.wr.trans wr₁),
      Or.inl ⟨rfl, c, hc, ?_, ?_⟩⟩
    · rw [ctlWord_eq_of_mem mem₃, ctlWord_changed h f₂ (by decide), ctl₁ 0 (by decide), c0]
    · rw [ctlWord_eq_of_mem mem₃, ctlWord_changed h f₂ (by decide), ctl₁ 1 (by decide), c1]
    · rw [mem₃]; exact fv₁.trans (f₂.mono fun r hr => List.mem_cons_of_mem _ hr)
    · rw [ctlWord_eq_of_mem mem₃, ctlWord_changed h f₂ (by decide), c3]
    · rw [htot, VG.Proof.Dsa.Generation.search_zero]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  refine WP.ite false (ev₁.trans (by simp)) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
  obtain ⟨V₁, R₁⟩ := hm₁.rep
  apply WP.seq
  refine WP.mono (roomCheck_run hm₁.layout R₁ x0₁ h15 hc hlen (hq ▸ hq2 |> fun e => by rw [← hq] at e; exact e))
    fun t₂ ⟨⟨x3₂, mem₂⟩, k₂⟩ => ?_
  have hm₂ := genMem_keep hm₁ mem₂ k₂
  have rd₂ : t₂.rd = v.rd := k₂.rd.trans rd₁
  have wr₂ : t₂.wr = v.wr := k₂.wr.trans wr₁
  have ev₂ : eval (.nonzero .x .x3) t₂ = some (decide ((randTape h).bytes.length - c < qBytes)) := by
    simp only [eval, State.read, x3₂, BitVec.setWidth_eq]
    by_cases hr : (randTape h).bytes.length - c < qBytes <;> simp [hr]
  by_cases hr : (randTape h).bytes.length - c < qBytes
  · refine WP.ite true (ev₂.trans (by simp [hr])) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    refine WP.mono (statusMem_ok hm₂ 0 (by decide)) fun t₃ ⟨hm₃, f₃, k₃⟩ => ?_
    refine WP.mono (statusTest_ok hm₃) fun t₄ ⟨z₄, hm₄, mem₄, k₄⟩ => Or.inl ⟨z₄.trans rfl, ?_⟩
    have cw : ∀ j < 4, ctlWord t₄.mem (refillBase s₀) j = ctlWord t₁.mem (refillBase s₀) j := fun j hj => by
      rw [ctlWord_eq_of_mem mem₄, ctlWord_changed h f₃ hj, ctlWord_eq_of_mem mem₂]
    refine ⟨hs, _, hin, hm₄, by rw [cw 0 (by decide), ctl₁ 0 (by decide), c0],
      by rw [cw 1 (by decide), ctl₁ 1 (by decide), c1], ?_, k₄.rd.trans (k₃.rd.trans rd₂),
      k₄.wr.trans (k₃.wr.trans wr₂), Or.inr (Or.inl ⟨rfl, c, n' + 1, hc, by rw [cw 3 (by decide), c3],
        by rw [cw 2 (by decide), ctl₁ 2 (by decide), c2], hn, ?_⟩)⟩
    · rw [mem₄]; exact (mem₂ ▸ fv₁).trans (f₃.mono fun r hr => List.mem_cons_of_mem _ hr)
    · rw [htot]; exact VG.Proof.Dsa.Generation.search_short (hq ▸ hr)
  refine WP.ite false (ev₂.trans (by simp [hr])) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
  have room : c + qBytes ≤ (randTape h).bytes.length := by omega
  obtain ⟨V₂, R₂⟩ := hm₂.rep
  apply WP.seq
  refine WP.mono (seedStart_run hm₂.layout R₂ ((k₂.gpr .x0 (by decide)).trans x0₁) h14 hq2)
    fun t₃ ⟨mem₃, k₃⟩ => ?_
  have L₂ := hm₂.layout
  have R₃ : Rep t₃.mem (refillBase s₀) (refillGeometry h).hash V₂
      (upd (upd W 1 (off (randTape h).ptr c)) 16 (BitVec.ofNat 64 (c + qBytes))) := by
    rw [mem₃]; exact (R₂.wf L₂.geo (k := 1) (by decide) _).wf L₂.geo (k := 16) (by decide) _
  have f₃ : Frame [⟨refillBase s₀, frameBytes⟩] t₂.mem t₃.mem := by
    rw [mem₃]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (cF _ (d := 8) (by decide))).writeW
      List.mem_cons_self _ (cF _ (d := 128) (by decide))
  have hm₃ : GenerationMemory ((refillContext h).withHs hs)
      (upd (upd W 1 (off (randTape h).ptr c)) 16 (BitVec.ofNat 64 (c + qBytes))) t₃ := by
    refine hm₂.frame (lay_of_rep L₂ R₂ R₃ (by simp [upd]) k₃.sp k₃.wr) ⟨V₂, R₃⟩ ?_
      (GenerationContext.frame_single f₃) k₃.rd k₃.wr
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have cw₃ : ∀ j < 4, ctlWord t₃.mem (refillBase s₀) j = ctlWord t₁.mem (refillBase s₀) j := fun j hj => by
    rw [ctlWord_changed h (GenerationContext.frame_single f₃) hj, ctlWord_eq_of_mem mem₂]
  have fv₃ : Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t₃.mem :=
    (mem₂ ▸ fv₁).trans ((GenerationContext.frame_single f₃).mono fun r hr => List.mem_cons_of_mem _ hr)
  let seed := (randTape h).slice c qBytes room
  have seedLen : seed.bytes.length = Spec.Dsa.generationQLen pBytes := by
    change ((((randTape h).bytes.drop c).take qBytes)).length = _
    simp only [List.length_take, List.length_drop]; omega
  apply WP.seq
  refine WP.mono (hA hs _ t₃ seed hin hm₃ seedLen (hm₃.rand.slice room) (by simp [upd, seed, GenerationTape.slice])
    (c + qBytes) (by simp [upd]) room) fun t₅ hfin => ?_
  obtain ⟨hs', W', u, sub', hm₅', hu, h16', -, outcome, f₅, rd₅, wr₅⟩ := hfin
  have hm₅ : GenerationMemory ((refillContext h).withHs hs') W' t₅ :=
    GenerationContext.withHs_withHs (refillContext h) hs hs' ▸ hm₅'
  have hin' : HsIn h hs' := sub'
  have cw₅ : ∀ j < 4, ctlWord t₅.mem (refillBase s₀) j = ctlWord t₁.mem (refillBase s₀) j := fun j hj => by
    rw [ctlWord_changed h f₅ hj, cw₃ j hj]
  have fv₅ : Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t₅.mem :=
    fv₃.trans (f₅.mono fun r hr => List.mem_cons_of_mem _ hr)
  have rd₅' : t₅.rd = v.rd := rd₅.trans (k₃.rd.trans rd₂)
  have wr₅' : t₅.wr = v.wr := wr₅.trans (k₃.wr.trans wr₂)
  have hseed : seed.bytes = ((randTape h).bytes.drop c).take (Spec.Dsa.generationQLen pBytes) := by
    rw [← hq]; rfl
  change SeedOutcome _ (VG.Proof.Dsa.Generation.refillAttempt pBytes
    (Spec.Dsa.generationQLen pBytes) seed.bytes ((randTape h).bytes.drop (c + qBytes))) W' u t₅ at outcome
  rw [hseed, hq] at outcome
  rw [hq] at room
  apply WP.seq
  refine WP.mono (statusTest_ok hm₅) fun t₆ ⟨z₆, hm₆, mem₆, k₆⟩ => ?_
  have cw₆ : ∀ j < 4, ctlWord t₆.mem (refillBase s₀) j = ctlWord t₁.mem (refillBase s₀) j := fun j hj => by
    rw [ctlWord_eq_of_mem mem₆, cw₅ j hj]
  rcases outcome with ⟨h19, hres⟩ | ⟨h19, hres⟩ | ⟨h19, a, hres, bytes⟩
  · refine WP.ite false (z₆.trans (by rw [h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => WP.block_nil ?_)
    refine WP.mono (statusTest_ok hm₆) fun t₇ ⟨z₇, hm₇, mem₇, k₇⟩ => Or.inl ⟨z₇.trans (by rw [h19]; rfl), ?_⟩
    refine ⟨hs', W', hin', hm₇, by rw [ctlWord_eq_of_mem mem₇, cw₆ 0 (by decide), ctl₁ 0 (by decide), c0],
      by rw [ctlWord_eq_of_mem mem₇, cw₆ 1 (by decide), ctl₁ 1 (by decide), c1], by rw [mem₇, mem₆]; exact fv₅,
      k₇.rd.trans (k₆.rd.trans rd₅'), k₇.wr.trans (k₆.wr.trans wr₅'),
      Or.inr (Or.inl ⟨h19, c, n' + 1, hc, by rw [ctlWord_eq_of_mem mem₇, cw₆ 3 (by decide), c3],
        by rw [ctlWord_eq_of_mem mem₇, cw₆ 2 (by decide), ctl₁ 2 (by decide), c2], hn, ?_⟩)⟩
    rw [htot]; exact VG.Proof.Dsa.Generation.search_attemptNone hpos room hres
  · refine WP.ite true (z₆.trans (by rw [h19]; rfl)) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    have c2₆ : ctlWord t₆.mem (refillBase s₀) 2 = BitVec.ofNat 64 (n' + 1) := by
      rw [cw₆ 2 (by decide), ctl₁ 2 (by decide), c2]
    refine WP.mono (rejected_run (k₆.sp.trans hm₅.layout.sp) (hctl _ (k₆.wr.trans wr₅'))
      (by omega) c2₆) fun t₇ ⟨mem₇, k₇⟩ => ?_
    have fr₇ : Frame [ctlRegion (refillBase s₀)] t₆.mem t₇.mem := by
      rw [mem₇]; exact ctl_write t₆.mem _ (k := 2) (by decide) _
    have hm₇ := GenerationMemory.ctlFrame h hin' hm₆ fr₇ k₇.sp k₇.rd k₇.wr
    have cw₇ : ∀ j < 2, ctlWord t₇.mem (refillBase s₀) j = ctlWord t₆.mem (refillBase s₀) j := fun j hj => by
      rw [mem₇]; exact ctlWord_write_other t₆.mem _ (k := 2) (by omega) (by decide) (by omega) _
    refine WP.mono (statusTest_ok hm₇) fun t₈ ⟨z₈, hm₈, mem₈, k₈⟩ => Or.inr ⟨z₈.trans (by rw [h19]; rfl), n', by omega, ?_⟩
    refine ⟨hs', W', u, hin', hm₈, h16', hu,
      by rw [ctlWord_eq_of_mem mem₈, cw₇ 0 (by decide), cw₆ 0 (by decide), ctl₁ 0 (by decide), c0],
      by rw [ctlWord_eq_of_mem mem₈, cw₇ 1 (by decide), cw₆ 1 (by decide), ctl₁ 1 (by decide), c1],
      by rw [ctlWord_eq_of_mem mem₈, mem₇]; exact ctlWord_write_self t₆.mem _ 2 _, by omega, ?_, ?_,
      k₈.rd.trans (k₇.rd.trans (k₆.rd.trans rd₅')), k₈.wr.trans (k₇.wr.trans (k₆.wr.trans wr₅'))⟩
    · rw [htot]; exact VG.Proof.Dsa.Generation.search_rejected hpos room hu hres
    · rw [mem₈]; exact (mem₆ ▸ fv₅).trans (fr₇.mono fun r hr => by
        rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)
  · refine WP.ite false (z₆.trans (by rw [h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => WP.block_nil ?_)
    refine WP.mono (statusTest_ok hm₆) fun t₇ ⟨z₇, hm₇, mem₇, k₇⟩ => Or.inl ⟨z₇.trans (by rw [h19]; rfl), ?_⟩
    refine ⟨hs', W', hin', hm₇, by rw [ctlWord_eq_of_mem mem₇, cw₆ 0 (by decide), ctl₁ 0 (by decide), c0],
      by rw [ctlWord_eq_of_mem mem₇, cw₆ 1 (by decide), ctl₁ 1 (by decide), c1], by rw [mem₇, mem₆]; exact fv₅,
      k₇.rd.trans (k₆.rd.trans rd₅'), k₇.wr.trans (k₆.wr.trans wr₅'),
      Or.inr (Or.inr ⟨h19, a, u, hu, h16', ?_, by rw [mem₇, mem₆]; exact bytes⟩)⟩
    rw [htot]; exact VG.Proof.Dsa.Generation.search_accepted hpos room hu hres

theorem controller_ok {qBytes : Nat} (hq : qBytes = Spec.Dsa.generationQLen pBytes) {attempt : Prog isa}
    (hA : AttemptOk h attempt) {v : State} (hv : (⟨refillBase s₀, 480⟩ : Region) ∈ v.wr) (n : Nat) (t : State)
    (hi : LoopInv h v n t) :
    WP isa (.loop (Impl.Dsa.AArch64.Generation.Refill.iteration attempt qBytes) (.zero .x .x0)) t (LoopDone h v) :=
  WP.loop (M := isa) (Q := LoopDone h v) (LoopInv h v) (fun n t hi => step_ok h hq hA hv n t hi) n t hi

/-- The controller's invariant on entry. -/
theorem loop_initial {W : Nat → BitVec 64} {v : State} (hm : GenerationMemory (refillContext h) W v)
    (h16 : W 16 = 0) (c0 : ctlWord v.mem (refillBase s₀) 0 = s₀.gpr .x2)
    (c1 : ctlWord v.mem (refillBase s₀) 1 = s₀.gpr .x7)
    (c2 : ctlWord v.mem (refillBase s₀) 2 = s₀.mem.readW (s₀.gpr .x7) 64) :
    LoopInv h v (s₀.mem.readW (s₀.gpr .x7) 64).toNat v := by
  refine ⟨(refillContext h).hs, W, 0, ?_, (GenerationContext.withHs_self _).symm ▸ hm, h16, Nat.zero_le _, c0, c1,
    by rw [c2, BitVec.ofNat_toNat, BitVec.setWidth_eq], h.seeds, ?_, Frame.refl _ _, rfl, rfl⟩
  · intro a ha
    simp [Region.Contains, refillContext, GenerationTape.slice] at ha
  · simp [total, Spec.Entropy.Result.consume]

end

end VG.Proof.Dsa.AArch64.Generation.Refill
