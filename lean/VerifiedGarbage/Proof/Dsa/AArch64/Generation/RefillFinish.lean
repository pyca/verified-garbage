module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillEntry
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecOut
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccess
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillOutcome
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSearch
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeIteration
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
import VerifiedGarbage.Proof.Dsa.Generation.Chunks

/-! ### `Dsa.AArch64.Generation.RefillLoop`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.ParameterInvariant`, which only this module used -/

section

/-! # The outer seed loop retains the exact remaining parameter search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem GenerationContext.status_frame {p : GenerationContext} {m m' : Mem}
    (h : Outside p.geo.F 152 8 m m') : Frame p.changed m m' := by
  apply GenerationContext.frame_single
  intro a ha
  apply h a
  right
  obtain hn := ha ⟨p.geo.F, frameBytes⟩ (by simp)
  change ¬ ofs p.geo.F a < frameBytes at hn
  unfold frameBytes at hn
  omega_using [hn]

end VG.Proof.Dsa.AArch64.Generation

end

end


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
  ⟨_, hv, Offset.contains_base F (by omega_using [hk]) (by omega_using [hk])⟩

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
  omega_using [h]

/-- The start of an iteration: the seed's start into `x0` and `ctl 3`, the
seeds left into `x3`. -/
theorem iterStart_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hv : (⟨F, 480⟩ : Region) ∈ s.wr)
    {c n : Nat} (h16 : W 16 = BitVec.ofNat 64 c) (h2 : ctlWord s.mem F 2 = BitVec.ofNat 64 n) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.iterStart) s fun t =>
      (t.gpr .x0 = BitVec.ofNat 64 c ∧ t.gpr .x3 = BitVec.ofNat 64 n ∧
        t.mem = s.mem.writeW (off F 472) (BitVec.ofNat 64 c)) ∧ Keep [.x0, .x3] s t := by
  obtain w16 : s.mem.readW (s.sp + BitVec.ofNat 64 128) 64 = BitVec.ofNat 64 c := by
    rw [L.sp]; exact (R.fr 16 (by decide)).trans h16
  obtain w2 : s.mem.readW (s.sp + BitVec.ofNat 64 464) 64 = BitVec.ofNat 64 n := by rw [L.sp]; exact h2
  obtain l128 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 128) 8 := by rw [L.sp]; exact L.ld (d := 128) (by decide)
  obtain l464 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 464) 8 := by rw [L.sp]; exact ctl_in' hv (k := 2) (by decide)
  obtain s472 : InRegions s.wr (s.sp + BitVec.ofNat 64 472) 8 := by rw [L.sp]; exact ctl_in hv (k := 3) (by decide)
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
  obtain w15 : s.mem.readW (s.sp + BitVec.ofNat 64 120) 64 = BitVec.ofNat 64 len := by
    rw [L.sp]; exact (R.fr 15 (by decide)).trans h15
  obtain l120 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 120) 8 := by rw [L.sp]; exact L.ld (d := 120) (by decide)
  obtain hsub : BitVec.ofNat 64 len - BitVec.ofNat 64 c = BitVec.ofNat 64 (len - c) := Offset.ofNat_sub_ofNat hc
  obtain hm := movi_small (show q < 2 ^ 16 by omega_using [hq2])
  refine WP.keep [.x3, .x4, .x5] ?_ (by rcases hq2 with rfl | rfl <;> decide) rfl
    (by rcases hq2 with rfl | rfl <;> decide +kernel)
  unfold Impl.Dsa.AArch64.Generation.Refill.roomCheck
  brun [State.write, exec_ldrSp (off := 120) (by decide), w15, l120, hx0, hsub, hm,
    loop_subs_ge (show len - c < 2 ^ 64 by omega_using [hl]) (show q < 2 ^ 64 by omega_using [hq2]),
    movi_small (show 0 < 2 ^ 16 by decide), movi_small (show 1 < 2 ^ 16 by decide)]
  by_cases h : q ≤ len - c
  · simp only [h, decide_true, ite_true, show ¬ len - c < q by omega_using [h], ite_false]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, show len - c < q by omega_using [h], ite_true]

/-- The seed's octets at `W 1`, and its witnesses after them. -/
theorem seedStart_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {c q : Nat} {ptr : Addr} (hx0 : s.gpr .x0 = BitVec.ofNat 64 c)
    (h14 : W 14 = ptr) (hq2 : q = 20 ∨ q = 32) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.seedStart q)) s fun t =>
      t.mem = ((((s.mem.writeW (off F 88) ptr).writeW (off F 8) (off ptr c)).writeW (off F 128)
        (BitVec.ofNat 64 (c + q))).writeW (off F 104) (0 : BitVec 64)) ∧ Keep [.x0, .x3, .x4] s t := by
  obtain w14 : s.mem.readW (s.sp + BitVec.ofNat 64 112) 64 = ptr := by
    rw [L.sp]; exact (R.fr 14 (by decide)).trans h14
  obtain l112 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 112) 8 := by rw [L.sp]; exact L.ld (d := 112) (by decide)
  obtain s8 : InRegions s.wr (s.sp + BitVec.ofNat 64 8) 8 := by rw [L.sp]; exact L.st (d := 8) (by decide)
  obtain s128 : InRegions s.wr (s.sp + BitVec.ofNat 64 128) 8 := by rw [L.sp]; exact L.st (d := 128) (by decide)
  obtain s88 : InRegions s.wr (s.sp + BitVec.ofNat 64 88) 8 := by rw [L.sp]; exact L.st (d := 88) (by decide)
  obtain s104 : InRegions s.wr (s.sp + BitVec.ofNat 64 104) 8 := by rw [L.sp]; exact L.st (d := 104) (by decide)
  obtain hm := movi_small (show q < 2 ^ 16 by omega_using [hq2])
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
  obtain w2 : s.mem.readW (s.sp + BitVec.ofNat 64 464) 64 = BitVec.ofNat 64 (n + 1) := by rw [hsp]; exact h2
  obtain l464 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 464) 8 := by rw [hsp]; exact ctl_in' hv (k := 2) (by decide)
  obtain s464 : InRegions s.wr (s.sp + BitVec.ofNat 64 464) 8 := by rw [hsp]; exact ctl_in hv (k := 2) (by decide)
  obtain e : BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 n := by
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
  obtain Rt : Rep t.mem p.geo.F p.geo.hash V W := hmem ▸ R
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
  obtain Rt : Rep t.mem (refillBase s₀) (refillGeometry h).hash V W :=
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
  obtain ft := GenerationContext.status_frame ot
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
  obtain fr₁ : Frame [ctlRegion (refillBase s₀)] t.mem t₁.mem := by
    rw [mem₁]; exact ctl_write t.mem _ (k := 3) (by decide) _
  obtain ctl₁ : ∀ j < 3, ctlWord t₁.mem (refillBase s₀) j = ctlWord t.mem (refillBase s₀) j := fun j hj => by
    rw [mem₁]; exact ctlWord_write_other t.mem _ (k := 3) (by omega_using [hj]) (by decide) (by omega_using [hj]) _
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
  obtain hq2 : Spec.Dsa.generationQLen pBytes = 20 ∨ Spec.Dsa.generationQLen pBytes = 32 := by
    unfold Spec.Dsa.generationQLen; split <;> simp
  obtain h15 : W 15 = BitVec.ofNat 64 (randTape h).bytes.length :=
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
  obtain hq2 : Spec.Dsa.generationQLen pBytes = 20 ∨ Spec.Dsa.generationQLen pBytes = 32 := by
    unfold Spec.Dsa.generationQLen; split <;> simp
  obtain h14 : W 14 = (randTape h).ptr :=
    (hm₂.slots 14 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randSlot
  obtain ⟨V₂, R₂⟩ := hm₂.rep
  have L₂ := hm₂.layout
  refine WP.mono (seedStart_run L₂ R₂ x0 h14 hq2) fun t₃ ⟨mem₃, k₃⟩ => ?_
  let W₃ := upd (upd (upd (upd W 11 (randTape h).ptr) 1 (off (randTape h).ptr c)) 16
    (BitVec.ofNat 64 (c + Spec.Dsa.generationQLen pBytes))) 13 0
  obtain R₃ : Rep t₃.mem (refillBase s₀) (refillGeometry h).hash V₂ W₃ := by
    rw [mem₃]
    exact (((R₂.wf L₂.geo (k := 11) (by decide) _).wf L₂.geo (k := 1) (by decide) _).wf L₂.geo (k := 16)
      (by decide) _).wf L₂.geo (k := 13) (by decide) _
  obtain f₃ : Frame [⟨refillBase s₀, frameBytes⟩] t.mem t₃.mem := by
    rw [mem₃]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (cF _ (d := 88) (by decide))).writeW
      List.mem_cons_self _ (cF _ (d := 8) (by decide))).writeW
      List.mem_cons_self _ (cF _ (d := 128) (by decide))).writeW List.mem_cons_self _ (cF _ (d := 104) (by decide))
  obtain fc₃ : Frame (refillContext h).changed t.mem t₃.mem := GenerationContext.frame_single f₃
  obtain rand₃ := hm₂.rand.frame (p := (refillContext h).withHs hs) fc₃ k₃.rd k₃.wr
  obtain hm₃ : GenerationMemory (refillContext h) W₃ t₃ := by
    refine ⟨lay_of_rep L₂ R₂ R₃ (by simp [W₃, upd]) k₃.sp k₃.wr, ⟨V₂, R₃⟩, ?_, hm₂.scratch.congr k₃.wr,
      hm₂.seeds.frame (p := (refillContext h).withHs hs) fc₃ k₃.rd k₃.wr, rand₃.slice (Nat.zero_le _), rand₃⟩
    intro k hk
    by_cases e11 : k = 11
    · subst e11; simp [W₃, upd, refillContext, refillWords, randTape]
    by_cases e13 : k = 13
    · subst e13; simp [W₃, upd, refillContext, refillWords]
    obtain e1 : k ≠ 1 := by rintro rfl; simp [generationSlots] at hk
    obtain e16 : k ≠ 16 := by rintro rfl; simp [generationSlots] at hk
    simp only [W₃, upd, e11, e13, e1, e16, ite_false]
    rw [hm₂.slots k hk]
    simp [GenerationContext.withHs, e11, e13]
  obtain cw₃ : ∀ j < 4, ctlWord t₃.mem (refillBase s₀) j = ctlWord t.mem (refillBase s₀) j := fun j hj =>
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
  obtain hpos : 0 < pBytes := by have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega_using [this]
  obtain hn₀ : n ≤ Spec.Dsa.parameterSeeds := by obtain ⟨_, _, _, _, _, _, _, _, _, _, hn, _⟩ := hi; exact hn
  obtain hseeds : n < 2 ^ 63 := by unfold Spec.Dsa.parameterSeeds at hn₀; omega_using [hn₀]
  simp only [Impl.Dsa.AArch64.Generation.Refill.iteration, VG.Impl.Bignum.AArch64.seqs]
  apply WP.seq
  refine WP.mono (iterStart_ok h hv hi) fun t₁ ⟨hi₁, c3, x0₁, x3₁⟩ => ?_
  obtain ev₁ : eval (.zero .x .x3) t₁ = some (decide (n = 0)) := by
    simp only [eval, State.read, x3₁, BitVec.setWidth_eq, ofNat_beq_zero (by omega_using [hseeds] : n < 2 ^ 64)]
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
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega_using [hn0]⟩
  refine WP.ite false (ev₁.trans (by simp)) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
  apply WP.seq
  refine WP.mono (roomCheck_ok h hi₁ x0₁) fun t₂ ⟨hi₂, mem₂, x0₂, x3₂⟩ => ?_
  obtain ev₂ : eval (.nonzero .x .x3) t₂ = some (decide (short h c)) := by
    simp only [eval, State.read, x3₂, BitVec.setWidth_eq]
    by_cases hr : short h c <;> simp [hr]
  by_cases hr : short h c
  · obtain ⟨hs, W, hin, hm₂, _, _, hc, c0, c1, c2, hn, htot, fv₂, rd₂, wr₂⟩ := hi₂
    refine WP.ite true (ev₂.trans (by simp [hr])) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    refine WP.mono (statusMem_ok hm₂ 0 (by decide)) fun t₃ ⟨hm₃, f₃, k₃⟩ => ?_
    refine WP.mono (statusTest_ok hm₃) fun t₄ ⟨z₄, hm₄, mem₄, k₄⟩ =>
      stepPost_done h (by simp [continues, hr]) (z₄.trans rfl) ?_
    obtain cw : ∀ j < 4, ctlWord t₄.mem (refillBase s₀) j = ctlWord t₂.mem (refillBase s₀) j := fun j hj => by
      rw [ctlWord_eq_of_mem mem₄, ctlWord_changed h f₃ hj]
    refine ⟨hs, _, hin, hm₄, by rw [cw 0 (by decide), c0], by rw [cw 1 (by decide), c1], ?_,
      k₄.rd.trans (k₃.rd.trans rd₂), k₄.wr.trans (k₃.wr.trans wr₂), by simp [upd, exitStatus, show
        (randTape h).bytes.length - c < Spec.Dsa.generationQLen pBytes from hr],
      by rw [cw 3 (by decide), ctlWord_eq_of_mem mem₂, c3],
      Or.inr (Or.inl ⟨rfl, hc, by rw [cw 2 (by decide), c2], hn, ?_⟩)⟩
    · rw [mem₄]; exact fv₂.trans (f₃.mono fun r hr => List.mem_cons_of_mem _ hr)
    · rw [htot]; exact VG.Proof.Dsa.Generation.search_short hr
  refine WP.ite false (ev₂.trans (by simp [hr])) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
  obtain room : c + Spec.Dsa.generationQLen pBytes ≤ (randTape h).bytes.length := by
    obtain hq2 : Spec.Dsa.generationQLen pBytes = 20 ∨ Spec.Dsa.generationQLen pBytes = 32 := by
      unfold Spec.Dsa.generationQLen; split <;> simp
    unfold short at hr; omega_using [hr, hq2]
  apply WP.seq
  refine WP.mono (seedStart_ok h hi₂ (by rw [ctlWord_eq_of_mem mem₂, c3]) x0₂ room) fun t₃ hs₃ => ?_
  obtain ⟨_, W₃, hm₃, w1, w16, w10, seedMem, c0, c1, c2, c3₃, hn, htot, fv₃, rd₃, wr₃⟩ := hs₃
  obtain hc : c ≤ (randTape h).bytes.length := by omega_using [room]
  obtain hm₃' : GenerationMemory ((refillContext h).withHs (refillContext h).hs) W₃ t₃ := by
    rw [GenerationContext.withHs_self]; exact hm₃
  obtain hin₀ : HsIn h (refillContext h).hs := by
    intro a ha
    simp [Region.Contains, refillContext, GenerationTape.slice] at ha
  obtain seedLen : (seedAt h c room).bytes.length = Spec.Dsa.generationQLen pBytes := by
    simp only [seedAt, GenerationTape.slice, List.length_take, List.length_drop]; omega_using [room]
  apply WP.seq
  refine WP.mono (hA _ W₃ t₃ _ hin₀ hm₃' seedLen seedMem w1 (c + Spec.Dsa.generationQLen pBytes) w16 room)
    fun t₅ hfin => ?_
  obtain ⟨hs', W', u, sub', hm₅', hu, h16', slots₅, outcome, f₅, rd₅, wr₅⟩ := hfin
  obtain hm₅ : GenerationMemory ((refillContext h).withHs hs') W' t₅ :=
    GenerationContext.withHs_withHs (refillContext h) _ hs' ▸ hm₅'
  have hin' : HsIn h hs' := sub'
  obtain w10' : W' 10 = 0 := by rw [slots₅ 10 (by simp [refillSlots])]; exact w10
  obtain cw₅ : ∀ j < 4, ctlWord t₅.mem (refillBase s₀) j = ctlWord t₃.mem (refillBase s₀) j := fun j hj =>
    ctlWord_changed h f₅ hj
  obtain fv₅ : Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t₅.mem :=
    fv₃.trans (f₅.mono fun r hr => List.mem_cons_of_mem _ hr)
  obtain rd₅' : t₅.rd = v.rd := rd₅.trans rd₃
  obtain wr₅' : t₅.wr = v.wr := wr₅.trans wr₃
  change SeedOutcome _ (seedResult h c) W' u t₅ at outcome
  apply WP.seq
  refine WP.mono (statusTest_ok hm₅) fun t₆ ⟨z₆, hm₆, mem₆, k₆⟩ => ?_
  obtain cw₆ : ∀ j < 4, ctlWord t₆.mem (refillBase s₀) j = ctlWord t₃.mem (refillBase s₀) j := fun j hj => by
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
    obtain c2₆ : ctlWord t₆.mem (refillBase s₀) 2 = BitVec.ofNat 64 (n' + 1) := by
      rw [cw₆ 2 (by decide), c2]
    obtain hv₆ : (⟨refillBase s₀, 480⟩ : Region) ∈ t₆.wr := by rw [k₆.wr, wr₅']; exact hv
    refine WP.mono (rejected_run (k₆.sp.trans hm₅.layout.sp) hv₆ (by omega_using [hseeds]) c2₆) fun t₇ ⟨mem₇, k₇⟩ => ?_
    obtain fr₇ : Frame [ctlRegion (refillBase s₀)] t₆.mem t₇.mem := by
      rw [mem₇]; exact ctl_write t₆.mem _ (k := 2) (by decide) _
    obtain hm₇ := GenerationMemory.ctlFrame h hin' hm₆ fr₇ k₇.sp k₇.rd k₇.wr
    obtain cw₇ : ∀ j < 2, ctlWord t₇.mem (refillBase s₀) j = ctlWord t₆.mem (refillBase s₀) j := fun j hj => by
      rw [mem₇]; exact ctlWord_write_other t₆.mem _ (k := 2) (by omega_using [hj]) (by decide) (by omega_using [hj]) _
    have hu' : u ≤ (randTape h).bytes.length := hu
    obtain next : nextUsed h c = u := by
      simp only [nextUsed, hres, List.length_drop]
      change (randTape h).bytes.length - ((randTape h).bytes.length - u) = u
      omega_using [hu']
    obtain hcont : continues h (n' + 1) c = true := by simp [continues, hr, hres]
    refine WP.mono (statusTest_ok hm₇) fun t₈ ⟨z₈, hm₈, mem₈, k₈⟩ =>
      ⟨z₈.trans (by rw [h19, hcont]; rfl), fun e => (by rw [hcont] at e; cases e), fun _ => ⟨n', rfl, ?_⟩⟩
    rw [next]
    refine ⟨hs', W', hin', hm₈, h16', w10', hu,
      by rw [ctlWord_eq_of_mem mem₈, cw₇ 0 (by decide), cw₆ 0 (by decide), c0],
      by rw [ctlWord_eq_of_mem mem₈, cw₇ 1 (by decide), cw₆ 1 (by decide), c1],
      by rw [ctlWord_eq_of_mem mem₈, mem₇]; exact ctlWord_write_self t₆.mem _ 2 _, by omega_using [hn₀], ?_, ?_,
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
        exact Or.inr ⟨e.trans (by rw [hc]), m, by omega_using [hm], _, st⟩) n t ⟨c, hi⟩

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

end

end

/-! ### `Dsa.AArch64.Generation.FinishOutput`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.OutputZero`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.ZeroBytes`, which only this module used -/

section

/-! Precise byte and memory framing for the shared native output-clearing loop. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.WriteBytes (writeW8_apply)

structure OutputZeroInv (s : State) (out : Addr) (n j : Nat) (t : State) : Prop where
  keep : Keep [.x11, .x12] s t
  r10 : t.gpr .x11 = out + BitVec.ofNat 64 j
  r11 : t.gpr .x12 = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem zeroOut_bytes_ok {s : State} {F S op : Addr} {k : Nat}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep s.mem F S V W)
    (hO : W 19 = op) (hK : W 21 = BitVec.ofNat 64 k)
    (hk1 : 0 < k) (hk' : k < 2 ^ 64)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa zeroOut s fun t => (∀ i < k, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Keep [.x11, .x12, .x13] s t := by
  obtain ho : s.mem.readW (F + BitVec.ofNat 64 sOut) 64 = op := (R.fr 19 (by decide)).trans hO
  obtain hk : s.mem.readW (F + BitVec.ofNat 64 sK) 64 = BitVec.ofNat 64 k := (R.fr 21 (by decide)).trans hK
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.x11, .x12, .x13] (Q := fun t => t.gpr .x11 = op ∧
      t.gpr .x12 = BitVec.ofNat 64 k ∧ t.gpr .x13 = 0 ∧ t.mem = s.mem) (by
    brun [exec_ldrSp (off := sOut) (by decide), exec_ldrSp (off := sK) (by decide), L.sp,
      L.ld (d := sOut) (n := 8) (by decide), L.ld (d := sK) (n := 8) (by decide), ho, hk]) rfl rfl rfl)
    fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (VG.Proof.RsaOaep.AArch64.count_loop (cr := .x12) hk1 (OutputZeroInv s₁ op k) ?_
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega_using []), fun x _ => rfl⟩) fun t hI => ⟨hI.bytes, fun x hx => by
        rw [hI.frame x hx, hm₁], ((k₁.trans hI.keep).mono (by decide))⟩
  intro j hj t hI
  obtain hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.wr, k₁.wr]; exact hout j hj
  obtain hax' : (t.gpr .x13).setWidth 8 = 0 := by rw [hI.keep.gpr .x13 (by decide), hax]; rfl
  obtain hp : BitVec.ofNat 64 (k - j) - 1#64 = BitVec.ofNat 64 (k - (j + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [hj]
  refine WP.mono (WP.keep [.x11, .x12] (Q := fun t' =>
      t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t'.gpr .x11 = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .x12 = BitVec.ofNat 64 (k - (j + 1)))
      (by brun [hI.r10, hI.r11, hst, hax', hp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl)
      rfl rfl rfl) fun t' ⟨⟨hm, hsi', hcx'⟩, k'⟩ => ?_
  refine ⟨⟨(hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_using [hk', hj, hi]) (by omega_using [hk', hj]) hij))]
      exact hI.bytes i (by omega_using [hi, hij])
  · intro x hx
    rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_using [])))]
    exact hI.frame x fun i hi => hx i (by omega_using [hi])
  · rw [hcx']
    exact VG.Proof.RsaOaep.AArch64.counter_ne (by omega_using [hj]) hk'

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! Every failed search clears the complete output and returns zero. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

theorem outputZero_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {len : Nat}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hlen : W 7 = BitVec.ofNat 64 len)
    (hl : 0 < len ∧ len ≤ 1024) (hw : (⟨W 6, len⟩ : Region) ∈ s.wr)
    (_hb : (W 6).toNat + len ≤ 2 ^ 64) (_ha : Apart F S ⟨W 6, len⟩) :
    WP isa Impl.Dsa.AArch64.Generation.outputZero s fun t =>
      t.gpr .x0 = 0 ∧ Spec.Rsa.bytesAt t.mem (W 6) len = List.replicate len 0 ∧
      Frame [⟨F, frameBytes⟩, ⟨W 6, len⟩] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  unfold Impl.Dsa.AArch64.Generation.outputZero
  refine WP.seq (WP.mono (zeroArgs_ok L R) fun u ⟨Lu, Ru, fu, ku⟩ => ?_)
  refine WP.seq (WP.mono (zeroOut_bytes_ok (op := W 6) (k := len) Lu Ru (by simp [upd]) (by simpa [upd] using hlen)
    hl.1 (by omega_using [hl]) (fun i hi => by
      rw [ku.wr]
      exact ⟨⟨W 6, len⟩, hw, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])⟩))
    fun v ⟨zeros, fv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = v.mem)
    (by brun) rfl rfl rfl) fun t ⟨⟨hr, hm⟩, kt⟩ => ?_
  refine ⟨hr, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · apply List.ext_getElem
    · simp only [VG.Proof.Bignum.bytesAt_length, List.length_replicate]
    · intro i hi hi'
      obtain hil : i < len := by simpa only [VG.Proof.Bignum.bytesAt_length] using hi
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate, hm]
      exact zeros i hil
  · have ff : Frame [⟨W 6, len⟩] u.mem t.mem := by
      intro a ha
      rw [hm]
      apply fv a
      intro i hi he
      apply ha ⟨W 6, len⟩ (by simp)
      rw [he]
      exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])
    exact (fu.mono (by simp)).trans (ff.mono (by simp))

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # Normalize every search outcome to the public output and status convention -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem finishOutput_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (expected : Option Spec.Dsa.Params)
    (result : ((W 19 ≠ 1 ∧ expected = none) ∨
      (W 19 = 1 ∧ ∃ a, expected = some a ∧
        Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a))) :
    WP isa Impl.Dsa.AArch64.Generation.finishOutput s fun t =>
      t.gpr .x0 = (if expected.isSome then 1 else 0) ∧
      Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) =
        (expected.map (Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen)).getD
          (List.replicate (2 * p.geo.pLen + p.geo.qLen) 0) ∧
      Frame [⟨p.geo.F, frameBytes⟩, ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩] s.mem t.mem ∧
      Keep (.x0 :: mmRegs) s t := by
  obtain pn : 0 < p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  obtain qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  obtain ⟨V, R⟩ := h.rep
  unfold Impl.Dsa.AArch64.Generation.finishOutput
  refine WP.seq (WP.mono (successStatus_ok h.layout R) fun u ⟨hz, hm, ku⟩ => ?_)
  obtain mu := h.congr hm ku
  obtain hwu : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ u.wr := by rw [ku.wr]; exact hw
  rcases result with ⟨h19, he⟩ | ⟨h19, a, he, bytes⟩
  · have hn : W 19 ≠ 1 := h19
    refine WP.ite false (by exact hz.trans (congrArg some (beq_eq_false_iff_ne.mpr hn)))
      (fun impossible => Bool.noConfusion impossible) (fun _ => ?_)
    obtain ⟨Vu, Ru⟩ := mu.rep
    obtain h6 := mu.slots 6 (by simp [generationSlots])
    obtain h7 := (mu.slots 7 (by simp [generationSlots])).trans o.lengthSlot
    obtain call := outputZero_ok mu.layout Ru h7 ⟨by omega_using [pn], by omega_using [pn, qn]⟩
    rw [h6] at call
    refine WP.mono (call hwu o.bound o.apart) fun t ⟨hr, bt, ft, kt⟩ => ?_
    rw [he]
    exact ⟨hr, bt, by simpa only [hm] using ft, (ku.trans kt).mono (by decide)⟩
  · refine WP.ite true (by apply hz.trans; rw [h19]; rfl)
      (fun _ => ?_) (fun impossible => Bool.noConfusion impossible)
    obtain bytesu : Spec.Rsa.bytesAt u.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) =
        Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a := hm ▸ bytes
    refine WP.mono (output_copy_context mu o hwu _ (VG.Proof.Dsa.Generation.encodeParams_length _ _ _) bytesu)
      fun t ⟨hr, bt, ft, kt⟩ => ?_
    rw [he]
    refine ⟨hr, bt, ?_, (ku.trans kt).mono (by decide)⟩
    rw [hm] at ft
    exact ft.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp)

end VG.Proof.Dsa.AArch64.Generation

end

end


-- separate module: the end's symbolic execution, built in parallel with the constant-time proofs importing `RefillLoop`

/-! # The refillable-tape search's end on AArch64

`finish`: the words written to `used` and `state` and the status kept for
each way the controller ended (`results`), the parameters or zeros at `out`
(`finishOutput`), and the status returned. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation.Refill

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 (Lay Rep Geo upd nW cF)
open VG.Impl.RsaOaep.AArch64 (frameBytes oRsa)
open VG.Impl.Dsa.Generation.Layout (packed)
open VG.Proof.Dsa.AArch64.Generation

/-! ## Blocks -/

/-- The memory with `state[0]`, `state[3]` and `used[0]` written. -/
def written (m : Mem) (St U : Addr) (r0 r3 uv : BitVec 64) : Mem :=
  ((m.writeW St r0).writeW (off St 24) r3).writeW U uv

/-- What the blocks writing the words read and write. -/
structure ResEnv (s : State) (F St U : Addr) : Prop where
  sp : s.sp = F
  ctl : (⟨F, 480⟩ : Region) ∈ s.wr
  st : (⟨St, 32⟩ : Region) ∈ s.wr
  us : (⟨U, 8⟩ : Region) ∈ s.wr

theorem contains_head (a : Addr) {n k : Nat} (h : n ≤ k) : (⟨a, k⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem stores_run {s : State} {F St U : Addr} (e : ResEnv s F St U) {a b c : BitVec 64} (k : Nat) (hk : k < 2 ^ 16)
    (h11 : s.gpr .x11 = a) (h10 : s.gpr .x10 = b) (h12 : s.gpr .x12 = c) (h14 : s.gpr .x14 = St)
    (h15 : s.gpr .x15 = U) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.stores ++ Impl.Dsa.AArch64.Generation.Refill.statusWord k)) s
      fun t => t.mem = (written s.mem St U a b c).writeW (off F 472) (BitVec.ofNat 64 k) ∧ t.sp = s.sp ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  obtain s472 : InRegions s.wr (s.sp + BitVec.ofNat 64 472) 8 := by rw [e.sp]; exact ctl_in e.ctl (k := 3) (by decide)
  obtain st0 : InRegions s.wr St 8 := ⟨_, e.st, contains_head St (n := 8) (k := 32) (by decide)⟩
  obtain st24 : InRegions s.wr (St + BitVec.ofNat 64 24) 8 := ⟨_, e.st, Offset.contains_base St (by decide) (by decide)⟩
  obtain us0 : InRegions s.wr U 8 := ⟨_, e.us, contains_head U (n := 8) (k := 8) (by decide)⟩
  obtain hm := movi_small hk
  simp only [Impl.Dsa.AArch64.Generation.Refill.stores, Impl.Dsa.AArch64.Generation.Refill.statusWord,
    Impl.Dsa.AArch64.Generation.Refill.ctl, Nat.reduceMul, Nat.reduceAdd, List.cons_append, List.nil_append,
    VG.Impl.Bignum.AArch64.st]
  brun [State.write, exec_str_x (off := 0) (by decide), exec_str_x (off := 24) (by decide),
    exec_storeSp (off := 472) (by decide), s472, st0, st24, us0, h10, h11, h12, h14, h15, hm]
  simp only [written, e.sp, off]

theorem shl_small (n k : Nat) (h : n * 2 ^ k < 2 ^ 64) : BitVec.ofNat 64 n <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have : n < 2 ^ 64 := by
    have := Nat.one_le_two_pow (n := k)
    exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right n (by omega)) h
  rw [Nat.mod_eq_of_lt this]

/-- A seed that ran out: the octets left from its start, the budget, and
whether they reach it. -/
theorem ranOutCheck_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hv : (⟨F, 480⟩ : Region) ∈ s.wr) {c len pLen : Nat}
    (h3 : ctlWord s.mem F 3 = BitVec.ofNat 64 c) (h15 : W 15 = BitVec.ofNat 64 len)
    (hc : c ≤ len) (hl : len < 2 ^ 64) (hp3 : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.ranOutCheck pLen)) s fun t =>
      (t.gpr .x10 = BitVec.ofNat 64 (len - c) ∧ t.gpr .x9 = BitVec.ofNat 64 pLen ∧
        t.gpr .x11 = BitVec.ofNat 64 (32769 * pLen) ∧
        t.gpr .x12 = BitVec.ofNat 64 (if 32769 * pLen ≤ len - c then 1 else 0) ∧ t.mem = s.mem) ∧
      Keep [.x9, .x10, .x11, .x12, .x13] s t := by
  obtain w15 : s.mem.readW (s.sp + BitVec.ofNat 64 120) 64 = BitVec.ofNat 64 len := by
    rw [L.sp]; exact (R.fr 15 (by decide)).trans h15
  obtain w3 : s.mem.readW (s.sp + BitVec.ofNat 64 472) 64 = BitVec.ofNat 64 c := by rw [L.sp]; exact h3
  obtain l120 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 120) 8 := by rw [L.sp]; exact L.ld (d := 120) (by decide)
  obtain l472 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 472) 8 := by rw [L.sp]; exact ctl_in' hv (k := 3) (by decide)
  obtain hsub : BitVec.ofNat 64 len - BitVec.ofNat 64 c = BitVec.ofNat 64 (len - c) := Offset.ofNat_sub_ofNat hc
  obtain hp : pLen ≤ 384 := by omega_using [hp3]
  obtain e15 := shl_small pLen 15 (by omega_using [hp3])
  obtain eb : BitVec.ofNat 64 (pLen * 2 ^ 15) + BitVec.ofNat 64 pLen = BitVec.ofNat 64 (32769 * pLen) := by
    rw [← BitVec.ofNat_add]; congr 1; omega_using []
  refine WP.keep [.x9, .x10, .x11, .x12, .x13] ?_ (by rcases hp3 with rfl | rfl | rfl <;> decide) rfl
    (by rcases hp3 with rfl | rfl | rfl <;> decide +kernel)
  simp only [Impl.Dsa.AArch64.Generation.Refill.ranOutCheck, Impl.Dsa.AArch64.Generation.Refill.ctl,
    Nat.reduceMul, Nat.reduceAdd]
  brun [State.write, exec_ldrSp (off := 120) (by decide), exec_ldrSp (off := 472) (by decide), w15, w3, l120, l472,
    hsub, movi_small (show pLen < 2 ^ 16 by omega_using [hp3]), movi_small (show 0 < 2 ^ 16 by decide),
    movi_small (show 1 < 2 ^ 16 by decide), exec_lsl_x (by decide : 15 < 64), e15, eb,
    loop_subs_ge (show len - c < 2 ^ 64 by omega_using [hl]) (show 32769 * pLen < 2 ^ 64 by omega_using [hp3])]
  by_cases h : 32769 * pLen ≤ len - c <;> simp [h]

/-- The next tape's length. -/
theorem request_run {s : State} {L B pLen : Nat} (hL : L < 2 ^ 32) (hB : B < 2 ^ 32) (hp : pLen ≤ 384)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 pLen) (h10 : s.gpr .x10 = BitVec.ofNat 64 L)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 B) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.request) s fun t =>
      (t.gpr .x10 = BitVec.ofNat 64 (VG.Proof.Entropy.request (256 * pLen) B L) ∧ t.gpr .x11 = BitVec.ofNat 64 B ∧
        t.mem = s.mem) ∧ Keep [.x10, .x12, .x13] s t := by
  obtain e8 := shl_small pLen 8 (by omega_using [hp])
  refine WP.keep [.x10, .x12, .x13] ?_ (by decide) rfl (by decide +kernel)
  unfold Impl.Dsa.AArch64.Generation.Refill.request
  brun [State.write, exec_lsl_x (by decide : 8 < 64), e8, h9, h10, h11,
    loop_subs_ge (show L < 2 ^ 64 by omega_using [hL]) (show pLen * 2 ^ 8 < 2 ^ 64 by omega_using [hp])]
  unfold VG.Proof.Entropy.request
  by_cases h1 : pLen * 2 ^ 8 ≤ L
  · simp only [h1, decide_true, ite_true, ← BitVec.ofNat_add,
      loop_subs_ge (show L + L < 2 ^ 64 by omega_using [hL]) (show B < 2 ^ 64 by omega_using [hB])]
    by_cases h2 : B ≤ L + L
    · simp only [h2, decide_true, ite_true]; congr 1; omega_using [h2]
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false]; congr 1; omega_using [h1, h2]
  · simp only [h1, decide_false, Bool.false_eq_true, ite_false, ← BitVec.ofNat_add,
      loop_subs_ge (show pLen * 2 ^ 8 + pLen * 2 ^ 8 < 2 ^ 64 by omega_using [hp]) (show B < 2 ^ 64 by omega_using [hB])]
    by_cases h2 : B ≤ pLen * 2 ^ 8 + pLen * 2 ^ 8
    · simp only [h2, decide_true, ite_true]; congr 1; omega_using [h2]
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false]; congr 1; omega_using [h1, h2]

/-- The pointers to `state` and `used`, and the controller's status. -/
theorem resultsStart_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hv : (⟨F, 480⟩ : Region) ∈ s.wr) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.resultsStart) s fun t =>
      (t.gpr .x14 = ctlWord s.mem F 1 ∧ t.gpr .x15 = ctlWord s.mem F 0 ∧ t.gpr .x3 = W 19 ∧ t.mem = s.mem) ∧
        Keep [.x3, .x14, .x15] s t := by
  obtain w : s.mem.readW (s.sp + BitVec.ofNat 64 152) 64 = W 19 := by rw [L.sp]; exact R.fr 19 (by decide)
  obtain l : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 152) 8 := by rw [L.sp]; exact L.ld (d := 152) (by decide)
  obtain l448 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 448) 8 := by rw [L.sp]; exact ctl_in' hv (k := 0) (by decide)
  obtain l456 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 456) 8 := by rw [L.sp]; exact ctl_in' hv (k := 1) (by decide)
  refine WP.keep [.x3, .x14, .x15] ?_ (by decide)
  simp only [Impl.Dsa.AArch64.Generation.Refill.resultsStart, Impl.Dsa.AArch64.Generation.Refill.ctl,
    Nat.reduceMul, Nat.reduceAdd]
  brun [State.write, exec_ldrSp (off := 152) (by decide), exec_ldrSp (off := 448) (by decide),
    exec_ldrSp (off := 456) (by decide), w, l, l448, l456]
  simp only [ctlWord, off, L.sp, and_self]

theorem minusOne_run {s : State} :
    WP isa (.block [.subImm .x .x3 .x3 1]) s fun t =>
      (eval (.zero .x .x3) t = some (s.gpr .x3 == 1) ∧ t.mem = s.mem) ∧ Keep [.x3] s t := by
  refine WP.keep [.x3] ?_ (by decide)
  brun [State.write, eval]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
  rfl

theorem prefixE_run {s : State} {F : Addr} (hsp : s.sp = F) (hv : (⟨F, 480⟩ : Region) ∈ s.wr) :
    WP isa (.block [.ldrSp .x11 (Impl.Dsa.AArch64.Generation.Refill.ctl 2),
        .ldrSp .x12 (Impl.Dsa.AArch64.Generation.Refill.ctl 3)]) s fun t =>
      (t.gpr .x11 = ctlWord s.mem F 2 ∧ t.gpr .x12 = ctlWord s.mem F 3 ∧ t.mem = s.mem) ∧ Keep [.x11, .x12] s t := by
  obtain l2 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 464) 8 := by rw [hsp]; exact ctl_in' hv (k := 2) (by decide)
  obtain l3 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 472) 8 := by rw [hsp]; exact ctl_in' hv (k := 3) (by decide)
  refine WP.keep [.x11, .x12] ?_ (by decide)
  simp only [Impl.Dsa.AArch64.Generation.Refill.ctl, Nat.reduceMul, Nat.reduceAdd]
  brun [State.write, exec_ldrSp (off := 464) (by decide), exec_ldrSp (off := 472) (by decide), l2, l3]
  simp only [ctlWord, off, hsp, and_self]

theorem prefixZ_run {s : State} {F : Addr} (hsp : s.sp = F) (hv : (⟨F, 480⟩ : Region) ∈ s.wr) {d : Nat}
    (hd : d = 472 ∨ d = 128) :
    WP isa (.block [VG.Impl.Bignum.AArch64.movi .x11 0, VG.Impl.Bignum.AArch64.movi .x10 0,
        .ldrSp .x12 d]) s fun t =>
      (t.gpr .x11 = 0 ∧ t.gpr .x10 = 0 ∧ t.gpr .x12 = s.mem.readW (off F d) 64 ∧ t.mem = s.mem) ∧
        Keep [.x10, .x11, .x12] s t := by
  obtain l : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 d) 8 := by
    rw [hsp]; exact ⟨_, List.mem_append_right _ hv, Offset.contains_base F (by omega_using [hd]) (by omega_using [hd])⟩
  refine WP.keep [.x10, .x11, .x12] ?_ (by rcases hd with rfl | rfl <;> decide) rfl
    (by rcases hd with rfl | rfl <;> decide +kernel)
  brun [State.write, exec_ldrSp (off := d) (by omega_using [hd]), l, movi_small (show 0 < 2 ^ 16 by decide)]
  simp only [off, hsp]

/-! ## The words for `used` and `state` -/

/-- The expected parameters. -/
def expectedOf (r : Spec.Dsa.ParameterSearchResult) : Option Spec.Dsa.Params :=
  match r.outcome with
  | .accepted a => some a
  | _ => none

theorem results_frame (m : Mem) (St U F : Addr) (r0 r3 uv v : BitVec 64) :
    Frame [⟨St, 32⟩, ⟨U, 8⟩, ctlRegion F] m ((written m St U r0 r3 uv).writeW (off F 472) v) :=
  (((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_head St (by decide))).writeW (List.mem_cons_self ..) _
    (Offset.contains_base St (d := 24) (by decide) (by decide))).writeW
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ (contains_head U (by decide)) |>.writeW
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) _
    (ctl_contains F (k := 3) (by decide))

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

theorem state_hash : (inState s₀).Disjoint ⟨(refillGeometry h).hash, oRsa⟩ :=
  (h.scrState.symm.sub_right h.arena_sub).sub_right ((refillGeometry h).part_sub
    ((refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)))

theorem used_hash : (inUsed s₀).Disjoint ⟨(refillGeometry h).hash, oRsa⟩ :=
  (h.usedScr.sub_right h.arena_sub).sub_right ((refillGeometry h).part_sub
    ((refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)))

/-- The regions the end writes, apart from the search's memory. -/
theorem results_regions : ∀ r ∈ [inState s₀, inUsed s₀, ctlRegion (refillBase s₀)],
    r.Disjoint ⟨refillBase s₀, frameBytes⟩ ∧ r.Disjoint ⟨(refillGeometry h).hash, oRsa⟩ ∧
      (⟨(randTape h).ptr, (randTape h).bytes.length⟩ : Region).Disjoint r ∧
      r.Disjoint ⟨s₀.gpr .x5, VG.Impl.Dsa.Generation.Layout.usedBytes pBytes⟩ := by
  obtain hrl : (⟨(randTape h).ptr, (randTape h).bytes.length⟩ : Region) = inRand s₀ := by
    simp only [randTape, bytesAt_length, inRand]
  obtain fb : ∀ {r : Region}, (r = inOut s₀ ∨ r = inUsed s₀ ∨ r = inRand s₀ ∨ r = inScr s₀ ∨ r = inState s₀) →
      r.Disjoint ⟨refillBase s₀, frameBytes⟩ := fun hr => by
    have := h.frame_disjoint hr (d := 0) (n := frameBytes) (by decide)
    simpa only [off, BitVec.add_zero] using this
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨fb (by simp), state_hash h, hrl ▸ h.randState, h.scrState.symm.sub_right h.arena_sub⟩
  · exact ⟨fb (by simp), used_hash h, hrl ▸ h.usedRand.symm, h.usedScr.sub_right h.arena_sub⟩
  · exact ⟨ctl_frame _, h.ctl_hash, rand_ctl h, h.ctl_arena⟩

theorem genMem_results {hs : GenerationTape (refillGeometry h)} (hin : HsIn h hs) {W : Nat → BitVec 64} {s t : State}
    (hm : GenerationMemory ((refillContext h).withHs hs) W s)
    (hf : Frame [inState s₀, inUsed s₀, ctlRegion (refillBase s₀)] s.mem t.mem)
    (hsp : t.sp = s.sp) (hr : t.rd = s.rd) (hw : t.wr = s.wr) :
    GenerationMemory ((refillContext h).withHs hs) W t := by
  obtain ⟨V, R⟩ := hm.rep
  obtain Rt : Rep t.mem (refillBase s₀) (refillGeometry h).hash V W :=
    rep_of_disjoint_frame R hf (fun r hr => ((results_regions h) r hr).1.symm)
      (fun r hr => ((results_regions h) r hr).2.1.symm)
  exact ⟨lay_of_rep hm.layout R Rt rfl hsp hw, ⟨V, Rt⟩, hm.slots, hm.scratch.congr hw,
    tapeMemory_frame hm.seeds hf (fun r hr => ((results_regions h) r hr).2.2.1) hr hw,
    tapeMemory_frame hm.hs hf (fun r hr => ((results_regions h) r hr).2.2.1.sub_left hin) hr hw,
    tapeMemory_frame hm.rand hf (fun r hr => ((results_regions h) r hr).2.2.1) hr hw⟩

/-- After `results`: the words written to `state` and `used` over the memory `m₁` the
controller left, the status kept in `ctl 3`, and the parameters still to output. -/
def ResultsDone (v : State) (n c : Nat) (t : State) : Prop :=
  ∃ (hs : GenerationTape (refillGeometry h)) (W : Nat → BitVec 64) (m₁ : Mem) (r0 r3 uv : BitVec 64) (st : Nat),
    HsIn h hs ∧ GenerationMemory ((refillContext h).withHs hs) W t ∧ W 19 = BitVec.ofNat 64 (exitStatus h n c) ∧
    Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem m₁ ∧
    t.mem = (written m₁ (s₀.gpr .x7) (s₀.gpr .x2) r0 r3 uv).writeW (off (refillBase s₀) 472) (BitVec.ofNat 64 st) ∧
    r0 = BitVec.ofNat 64 (total h).remaining ∧
    r3 = BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested pBytes (total h)) ∧
    uv = BitVec.ofNat 64 (total h).used ∧ st = (total h).status ∧
    ((W 19 ≠ 1 ∧ expectedOf (total h) = none) ∨
      (W 19 = 1 ∧ ∃ a, expectedOf (total h) = some a ∧
        Spec.Rsa.bytesAt t.mem (off (s₀.gpr .x5) packed) (2 * pBytes + Spec.Dsa.generationQLen pBytes) =
          Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes) a)) ∧
    t.sp = refillBase s₀ ∧ t.rd = v.rd ∧ t.wr = v.wr

theorem results_ok {v t : State} {n c : Nat} (hv : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr)
    (hd : LoopDone h v n c t) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.results pBytes) t (ResultsDone h v n c) := by
  obtain ⟨hs, W, hin, hm, c0, c1, fv, rdv, wrv, hx19, c3, cases⟩ := hd
  obtain hp3 : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384 := by
    have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega_using [this]
  obtain hp : pBytes ≤ 384 := by omega_using [hp3]
  obtain wt : t.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr := wrv.trans hv
  obtain env : ∀ x : State, x.sp = refillBase s₀ → x.wr = t.wr → ResEnv x (refillBase s₀) (s₀.gpr .x7) (s₀.gpr .x2) :=
    fun x hsp hw =>
    { sp := hsp
      ctl := by rw [hw, wt]; exact List.mem_cons_self ..
      st := by rw [hw, wt]; exact List.mem_cons_of_mem _ (by rw [h.wr]; simp [inState])
      us := by rw [hw, wt]; exact List.mem_cons_of_mem _ (by rw [h.wr]; simp [inUsed]) }
  obtain hlen : (randTape h).bytes.length < 2 ^ 32 := by
    have hr := h.randLength
    rw [h.width] at hr
    change (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat).length < _
    rw [bytesAt_length]; unfold Spec.Dsa.parameterEntropy at hr; omega_using [hp3, hr]
  obtain h15 : W 15 = BitVec.ofNat 64 (randTape h).bytes.length :=
    (hm.slots 15 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randLengthSlot
  obtain hv480 : (⟨refillBase s₀, 480⟩ : Region) ∈ t.wr := by rw [wt]; exact List.mem_cons_self ..
  obtain packedSub : ∀ r ∈ [inState s₀, inUsed s₀, ctlRegion (refillBase s₀)],
      (⟨off (s₀.gpr .x5) packed, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region).Disjoint r := by
    obtain qn : Spec.Dsa.generationQLen pBytes ≤ 32 := by unfold Spec.Dsa.generationQLen; split <;> omega_using []
    intro r hr
    exact ((results_regions h) r hr).2.2.2.symm.sub_left ((refillGeometry h).part_sub
      ((refillGeometry h).small_bound (d := packed) (n := 2 * pBytes + Spec.Dsa.generationQLen pBytes) (by decide)
        (by unfold VG.Impl.Dsa.Generation.Layout.arithmeticBytes; omega_using [hp3, qn])))
  -- the end, from the words stored
  obtain fin : ∀ {x y : State} {a b d : BitVec 64} {st : Nat}, x.mem = t.mem → x.sp = refillBase s₀ →
      x.rd = t.rd → x.wr = t.wr →
      y.mem = (written x.mem (s₀.gpr .x7) (s₀.gpr .x2) a b d).writeW (off (refillBase s₀) 472) (BitVec.ofNat 64 st) →
      y.sp = x.sp → y.rd = x.rd → y.wr = x.wr →
      a = BitVec.ofNat 64 (total h).remaining → b = BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested pBytes (total h)) →
      d = BitVec.ofNat 64 (total h).used → st = (total h).status →
      ((W 19 ≠ 1 ∧ expectedOf (total h) = none) ∨
        (W 19 = 1 ∧ ∃ p, expectedOf (total h) = some p ∧
          Spec.Rsa.bytesAt t.mem (off (s₀.gpr .x5) packed) (2 * pBytes + Spec.Dsa.generationQLen pBytes) =
            Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes) p)) →
      ResultsDone h v n c y := by
    intro x y a b d st xm xsp xrd xwr ym ysp yrd ywr ha hb hd hst out
    obtain fw : Frame [inState s₀, inUsed s₀, ctlRegion (refillBase s₀)] x.mem y.mem := by
      rw [ym]; exact results_frame _ _ _ _ _ _ _ _
    obtain hmx : GenerationMemory ((refillContext h).withHs hs) W x := by
      obtain ⟨V, R⟩ := hm.rep
      obtain Rx : Rep x.mem (refillBase s₀) (refillGeometry h).hash V W := xm ▸ R
      exact hm.frame (lay_of_rep hm.layout R Rx rfl (xsp.trans hm.layout.sp.symm) xwr) ⟨V, Rx⟩ (fun _ _ => rfl)
        (by rw [xm]; exact Frame.refl _ _) xrd xwr
    refine ⟨hs, W, t.mem, a, b, d, st, hin, genMem_results h hin hmx fw ysp yrd ywr, hx19, fv, by rw [ym, xm],
      ha, hb, hd, hst, ?_, ysp.trans xsp, yrd.trans (xrd.trans rdv), ywr.trans (xwr.trans wrv)⟩
    rcases out with o | ⟨h19, p, he, bytes⟩
    · exact Or.inl o
    · refine Or.inr ⟨h19, p, he, ?_⟩
      rw [VG.Proof.Dsa.Generation.frame_bytesAt fw packedSub (by unfold Spec.Dsa.generationQLen; split <;> omega_using [hp3]), xm]
      exact bytes
  obtain ⟨V, R⟩ := hm.rep
  unfold Impl.Dsa.AArch64.Generation.Refill.results
  refine WP.seq (WP.mono (resultsStart_run hm.layout R hv480) fun t₁ ⟨⟨x14₁, x15₁, x3₁, m₁⟩, k₁⟩ => ?_)
  replace x14₁ : t₁.gpr .x14 = s₀.gpr .x7 := x14₁.trans c1
  replace x15₁ : t₁.gpr .x15 = s₀.gpr .x2 := x15₁.trans c0
  obtain sp₁ : t₁.sp = refillBase s₀ := k₁.sp.trans hm.layout.sp
  obtain ev₁ : eval (.zero .x .x3) t₁ = some (W 19 == 0) := by simp only [eval, State.read, x3₁, BitVec.setWidth_eq]
  obtain cw₁ : ∀ k, ctlWord t₁.mem (refillBase s₀) k = ctlWord t.mem (refillBase s₀) k := fun k => by rw [m₁]
  rcases cases with ⟨h19, hc, htot⟩ | ⟨h19, hc, c2, hk, htot⟩ | ⟨h19, a, u, hu, h16, htot, bytes⟩
  · -- no seeds left
    refine WP.ite false (ev₁.trans (by rw [h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    refine WP.seq (WP.mono minusOne_run fun t₂ ⟨⟨ev₂, m₂⟩, k₂⟩ => ?_)
    refine WP.ite false (ev₂.trans (by rw [x3₁, h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    obtain sp₂ : t₂.sp = refillBase s₀ := k₂.sp.trans sp₁
    simp only [Impl.Dsa.AArch64.Generation.Refill.exhaustedWords, Impl.Dsa.AArch64.Generation.Refill.ctl,
      List.append_assoc, Nat.reduceMul, Nat.reduceAdd]
    apply WP.block_append
    refine WP.mono (prefixZ_run sp₂ (by rw [k₂.wr, k₁.wr]; exact hv480) (d := 472) (Or.inl rfl))
      fun t₃ ⟨⟨x11, x10, x12, m₃⟩, k₃⟩ => ?_
    obtain mt₃ : t₃.mem = t.mem := m₃.trans (m₂.trans m₁)
    refine WP.mono (stores_run (env t₃ (k₃.sp.trans sp₂) (k₃.wr.trans (k₂.wr.trans k₁.wr)))
      3 (by decide) x11 x10 x12 ((k₃.gpr .x14 (by decide)).trans ((k₂.gpr .x14 (by decide)).trans x14₁))
      ((k₃.gpr .x15 (by decide)).trans ((k₂.gpr .x15 (by decide)).trans x15₁)))
      fun t₄ ⟨m₄, sp₄, rd₄, wr₄⟩ => ?_
    refine fin mt₃ (k₃.sp.trans sp₂) (k₃.rd.trans (k₂.rd.trans k₁.rd)) (k₃.wr.trans (k₂.wr.trans k₁.wr))
      m₄ sp₄ rd₄ wr₄ ?_ ?_ ?_ ?_ (Or.inl ⟨by rw [h19]; decide, by rw [htot]; rfl⟩)
    all_goals simp only [htot, Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested,
      VG.Proof.Entropy.requested, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status]
    all_goals first | rfl | (rw [mt₃]; exact c3) | (rw [m₂, m₁]; exact c3)
  · -- the tape ran out
    refine WP.ite true (ev₁.trans (by rw [h19]; rfl)) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    obtain ⟨V₁, R₁⟩ := (genMem_keep hm m₁ k₁).rep
    obtain L₁ := (genMem_keep hm m₁ k₁).layout
    refine WP.seq (WP.mono (ranOutCheck_run L₁ R₁ (by rw [k₁.wr]; exact hv480) (by change ctlWord t₁.mem (refillBase s₀) 3 = _; rw [cw₁]; exact c3) h15 hc
      (by omega_using [hlen]) hp3) fun t₂ ⟨⟨x10₂, x9₂, x11₂, x12₂, m₂⟩, k₂⟩ => ?_)
    obtain sp₂ : t₂.sp = refillBase s₀ := k₂.sp.trans sp₁
    obtain mt₂ : t₂.mem = t.mem := m₂.trans m₁
    by_cases hL : 32769 * pBytes ≤ (randTape h).bytes.length - c
    · refine WP.ite false (by simp [eval, State.read, x12₂, hL]) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
      simp only [Impl.Dsa.AArch64.Generation.Refill.exhaustedWords, Impl.Dsa.AArch64.Generation.Refill.ctl,
        List.append_assoc, Nat.reduceMul, Nat.reduceAdd]
      apply WP.block_append
      refine WP.mono (prefixZ_run sp₂ (by rw [k₂.wr, k₁.wr]; exact hv480) (d := 472) (Or.inl rfl))
        fun t₃ ⟨⟨x11, x10, x12, m₃⟩, k₃⟩ => ?_
      obtain mt₃ : t₃.mem = t.mem := m₃.trans mt₂
      refine WP.mono (stores_run (env t₃ (k₃.sp.trans sp₂) (k₃.wr.trans (k₂.wr.trans k₁.wr)))
        3 (by decide) x11 x10 x12 ((k₃.gpr .x14 (by decide)).trans ((k₂.gpr .x14 (by decide)).trans x14₁))
        ((k₃.gpr .x15 (by decide)).trans ((k₂.gpr .x15 (by decide)).trans x15₁)))
        fun t₄ ⟨m₄, sp₄, rd₄, wr₄⟩ => ?_
      obtain hL' : Spec.Dsa.parameterEntropy pBytes ≤ (randTape h).bytes.length - c := by
        unfold Spec.Dsa.parameterEntropy; omega_using [hL]
      refine fin mt₃ (k₃.sp.trans sp₂) (k₃.rd.trans (k₂.rd.trans k₁.rd)) (k₃.wr.trans (k₂.wr.trans k₁.wr))
        m₄ sp₄ rd₄ wr₄ ?_ ?_ ?_ ?_ (Or.inl ⟨by rw [h19]; decide, ?_⟩)
      all_goals simp only [htot, VG.Proof.Dsa.Generation.ranOutResult, hL', ↓reduceIte,
        Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested,
        VG.Proof.Entropy.requested, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status, expectedOf]
      all_goals first | rfl | (rw [mt₃]; exact c3) | (rw [mt₂]; exact c3)
    · refine WP.ite true (by simp [eval, State.read, x12₂, hL]) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
      simp only [Impl.Dsa.AArch64.Generation.Refill.entropyWords, List.append_assoc]
      apply WP.block_append
      refine WP.mono (request_run (L := (randTape h).bytes.length - c) (B := Spec.Dsa.parameterEntropy pBytes)
        (by omega_using [hlen]) (by unfold Spec.Dsa.parameterEntropy; omega_using [hp3]) hp x9₂ x10₂ x11₂) fun t₃ ⟨⟨x10₃, x11₃, m₃⟩, k₃⟩ => ?_
      obtain sp₃ : t₃.sp = refillBase s₀ := k₃.sp.trans sp₂
      obtain mt₃ : t₃.mem = t.mem := m₃.trans mt₂
      apply WP.block_append
      refine WP.mono (prefixE_run sp₃ (by rw [k₃.wr, k₂.wr, k₁.wr]; exact hv480))
        fun t₄ ⟨⟨x11₄, x12₄, m₄⟩, k₄⟩ => ?_
      obtain mt₄ : t₄.mem = t.mem := m₄.trans mt₃
      refine WP.mono (stores_run (env t₄ (k₄.sp.trans sp₃) (k₄.wr.trans (k₃.wr.trans (k₂.wr.trans k₁.wr))))
        0 (by decide) x11₄ ((k₄.gpr .x10 (by decide)).trans x10₃) x12₄
        ((k₄.gpr .x14 (by decide)).trans ((k₃.gpr .x14 (by decide)).trans ((k₂.gpr .x14 (by decide)).trans x14₁)))
        ((k₄.gpr .x15 (by decide)).trans ((k₃.gpr .x15 (by decide)).trans ((k₂.gpr .x15 (by decide)).trans x15₁))))
        fun t₅ ⟨m₅, sp₅, rd₅, wr₅⟩ => ?_
      obtain hL' : ¬Spec.Dsa.parameterEntropy pBytes ≤ (randTape h).bytes.length - c := by
        unfold Spec.Dsa.parameterEntropy; omega_using [hL]
      refine fin mt₄ (k₄.sp.trans sp₃) (k₄.rd.trans (k₃.rd.trans (k₂.rd.trans k₁.rd)))
        (k₄.wr.trans (k₃.wr.trans (k₂.wr.trans k₁.wr))) m₅ sp₅ rd₅ wr₅ ?_ ?_ ?_ ?_ (Or.inl ⟨by rw [h19]; decide, ?_⟩)
      all_goals simp only [htot, VG.Proof.Dsa.Generation.ranOutResult, hL', ↓reduceIte,
        Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested,
        VG.Proof.Entropy.requested, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status, expectedOf]
      · exact (congrArg (fun m => ctlWord m (refillBase s₀) 2) mt₃).trans c2
      · simp only [VG.Proof.Dsa.Generation.parameterRequest]
      · exact (congrArg (fun m => ctlWord m (refillBase s₀) 3) mt₃).trans c3
  · -- parameters
    refine WP.ite false (ev₁.trans (by rw [h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    refine WP.seq (WP.mono minusOne_run fun t₂ ⟨⟨ev₂, m₂⟩, k₂⟩ => ?_)
    refine WP.ite true (ev₂.trans (by rw [x3₁, h19]; rfl)) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    obtain sp₂ : t₂.sp = refillBase s₀ := k₂.sp.trans sp₁
    simp only [Impl.Dsa.AArch64.Generation.Refill.acceptedWords, List.append_assoc]
    apply WP.block_append
    refine WP.mono (prefixZ_run sp₂ (by rw [k₂.wr, k₁.wr]; exact hv480) (d := 128) (Or.inr rfl))
      fun t₃ ⟨⟨x11, x10, x12, m₃⟩, k₃⟩ => ?_
    obtain mt₃ : t₃.mem = t.mem := m₃.trans (m₂.trans m₁)
    refine WP.mono (stores_run (env t₃ (k₃.sp.trans sp₂) (k₃.wr.trans (k₂.wr.trans k₁.wr)))
      1 (by decide) x11 x10 x12 ((k₃.gpr .x14 (by decide)).trans ((k₂.gpr .x14 (by decide)).trans x14₁))
      ((k₃.gpr .x15 (by decide)).trans ((k₂.gpr .x15 (by decide)).trans x15₁)))
      fun t₄ ⟨m₄, sp₄, rd₄, wr₄⟩ => ?_
    refine fin mt₃ (k₃.sp.trans sp₂) (k₃.rd.trans (k₂.rd.trans k₁.rd)) (k₃.wr.trans (k₂.wr.trans k₁.wr))
      m₄ sp₄ rd₄ wr₄ ?_ ?_ ?_ ?_ (Or.inr ⟨h19, a, by rw [htot]; rfl, bytes⟩)
    all_goals simp only [htot, Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested,
      VG.Proof.Entropy.requested, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status]
    all_goals first | rfl | (rw [mt₃]; exact (R.fr 16 (by decide)).trans h16) |
      (rw [m₂, m₁]; exact (R.fr 16 (by decide)).trans h16)

end

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

/-- The search's end, from the controller's: what `results` wrote, the
output, and the status in `x0`. -/
def FinishDone (v t : State) : Prop :=
  ∃ (m₁ : Mem) (r0 r3 uv : BitVec 64), Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem m₁ ∧
    r0 = BitVec.ofNat 64 (total h).remaining ∧
    r3 = BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested pBytes (total h)) ∧
    uv = BitVec.ofNat 64 (total h).used ∧
    Frame [⟨refillBase s₀, frameBytes⟩, inOut s₀]
      ((written m₁ (s₀.gpr .x7) (s₀.gpr .x2) r0 r3 uv).writeW (off (refillBase s₀) 472)
        (BitVec.ofNat 64 (total h).status)) t.mem ∧
    t.gpr .x0 = BitVec.ofNat 64 (total h).status ∧
    Spec.Rsa.bytesAt t.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat =
      ((expectedOf (total h)).map (Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes))).getD
        (List.replicate (s₀.gpr .x1).toNat 0) ∧
    t.sp = refillBase s₀ ∧ t.rd = v.rd ∧ t.wr = v.wr

theorem finish_ok {v t : State} {n c : Nat} (hv : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr) (hd : LoopDone h v n c t) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.finish pBytes) t (FinishDone h v) := by
  obtain o := refillOutputPlan h
  obtain outLen : 2 * pBytes + Spec.Dsa.generationQLen pBytes = (s₀.gpr .x1).toNat := by
    rw [← h.width]; exact h.outLength.symm
  unfold Impl.Dsa.AArch64.Generation.Refill.finish
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (results_ok h hv hd) fun t₁ D => ?_)
  obtain ⟨hs, W, m₁, r0, r3, uv, st, hin, hm, -, fv, mt₁, hr0, hr3, huv, hst, out, sp₁, rd₁, wr₁⟩ := D
  obtain o' : OutputPlan ((refillContext h).withHs hs) := ⟨o.lengthSlot, o.bound, o.separate⟩
  obtain hw : (⟨((refillContext h).withHs hs).saved 6,
      2 * ((refillContext h).withHs hs).geo.pLen + ((refillContext h).withHs hs).geo.qLen⟩ : Region) ∈ t₁.wr := by
    change (⟨s₀.gpr .x0, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region) ∈ t₁.wr
    rw [outLen, wr₁, hv]; exact List.mem_cons_of_mem _ (by rw [h.wr]; simp [inOut])
  refine WP.seq (WP.mono (finishOutput_ok hm o' hw (expectedOf (total h)) out) fun t₂ ⟨_, bytes₂, f₂, k₂⟩ => ?_)
  obtain f₂' : Frame [⟨refillBase s₀, frameBytes⟩, inOut s₀] t₁.mem t₂.mem := by
    refine f₂.mono fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl
    · exact Or.inl rfl
    · right; change _ = (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region); rw [← outLen]; rfl
  obtain c3 : ctlWord t₂.mem (refillBase s₀) 3 = BitVec.ofNat 64 (total h).status := by
    rw [ctlWord_frame f₂' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ctl_frame _
      · exact (h.frame_disjoint (r := inOut s₀) (by simp) (d := 448) (n := 32) (by decide)).symm) (by decide),
      mt₁, hst]
    exact ctlWord_write_self _ _ 3 _
  obtain sp₂ : t₂.sp = refillBase s₀ := k₂.sp.trans sp₁
  obtain l : InRegions (t₂.rd ++ t₂.wr) (t₂.sp + BitVec.ofNat 64 472) 8 := by
    rw [sp₂]
    exact ctl_in' (s := t₂) (F := refillBase s₀) (by rw [k₂.wr, wr₁, hv]; exact List.mem_cons_self ..) (k := 3) (by decide)
  obtain w : t₂.mem.readW (t₂.sp + BitVec.ofNat 64 472) 64 = BitVec.ofNat 64 (total h).status := by
    rw [sp₂]; exact c3
  refine WP.mono (WP.keep [.x0] (Q := fun t₃ => t₃.gpr .x0 = BitVec.ofNat 64 (total h).status ∧ t₃.mem = t₂.mem) (by
    simp only [Impl.Dsa.AArch64.Generation.Refill.ctl, Nat.reduceMul, Nat.reduceAdd]
    brun [State.write, exec_ldrSp (off := 472) (by decide), l, w]) (by decide)) fun t₃ ⟨⟨x0₃, m₃⟩, k₃⟩ => ?_
  refine ⟨m₁, r0, r3, uv, fv, hr0, hr3, huv, by rw [m₃, ← hst, ← mt₁]; exact f₂', x0₃, ?_,
    k₃.sp.trans sp₂, k₃.rd.trans (k₂.rd.trans rd₁), k₃.wr.trans (k₂.wr.trans wr₁)⟩
  rw [m₃]
  have := bytes₂
  change Spec.Rsa.bytesAt t₂.mem (s₀.gpr .x0) (2 * pBytes + Spec.Dsa.generationQLen pBytes) =
    ((expectedOf (total h)).map (Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes))).getD
      (List.replicate (2 * pBytes + Spec.Dsa.generationQLen pBytes) 0) at this
  rw [outLen] at this
  exact this

end

end VG.Proof.Dsa.AArch64.Generation.Refill
