module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputPlan
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FinishOutput
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.EntropyRequest

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
  c0 : ctlWord s.mem F 0 = U
  c1 : ctlWord s.mem F 1 = St

theorem contains_head (a : Addr) {n k : Nat} (h : n ≤ k) : (⟨a, k⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem stores_run {s : State} {F St U : Addr} (e : ResEnv s F St U) {a b c : BitVec 64} (k : Nat) (hk : k < 2 ^ 16)
    (h11 : s.gpr .x11 = a) (h10 : s.gpr .x10 = b) (h12 : s.gpr .x12 = c) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.stores ++ Impl.Dsa.AArch64.Generation.Refill.statusWord k)) s
      fun t => t.mem = (written s.mem St U a b c).writeW (off F 472) (BitVec.ofNat 64 k) ∧ t.sp = s.sp ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  have w0 : s.mem.readW (s.sp + BitVec.ofNat 64 448) 64 = U := by rw [e.sp]; exact e.c0
  have w1 : s.mem.readW (s.sp + BitVec.ofNat 64 456) 64 = St := by rw [e.sp]; exact e.c1
  have l448 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 448) 8 := by rw [e.sp]; exact ctl_in' e.ctl (k := 0) (by decide)
  have l456 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 456) 8 := by rw [e.sp]; exact ctl_in' e.ctl (k := 1) (by decide)
  have s472 : InRegions s.wr (s.sp + BitVec.ofNat 64 472) 8 := by rw [e.sp]; exact ctl_in e.ctl (k := 3) (by decide)
  have st0 : InRegions s.wr St 8 := ⟨_, e.st, contains_head St (n := 8) (k := 32) (by decide)⟩
  have st24 : InRegions s.wr (St + BitVec.ofNat 64 24) 8 := ⟨_, e.st, Offset.contains_base St (by decide) (by decide)⟩
  have us0 : InRegions s.wr U 8 := ⟨_, e.us, contains_head U (n := 8) (k := 8) (by decide)⟩
  have hm := movi_small hk
  simp only [Impl.Dsa.AArch64.Generation.Refill.stores, Impl.Dsa.AArch64.Generation.Refill.statusWord,
    Impl.Dsa.AArch64.Generation.Refill.ctl, Nat.reduceMul, Nat.reduceAdd, List.cons_append, List.nil_append,
    VG.Impl.Bignum.AArch64.st]
  brun [State.write, exec_ldrSp (off := 448) (by decide), exec_ldrSp (off := 456) (by decide),
    exec_str_x (off := 0) (by decide), exec_str_x (off := 24) (by decide), exec_storeSp (off := 472) (by decide),
    w0, w1, l448, l456, s472, st0, st24, us0, h10, h11, h12, hm]
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
  have w15 : s.mem.readW (s.sp + BitVec.ofNat 64 120) 64 = BitVec.ofNat 64 len := by
    rw [L.sp]; exact (R.fr 15 (by decide)).trans h15
  have w3 : s.mem.readW (s.sp + BitVec.ofNat 64 472) 64 = BitVec.ofNat 64 c := by rw [L.sp]; exact h3
  have l120 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 120) 8 := by rw [L.sp]; exact L.ld (d := 120) (by decide)
  have l472 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 472) 8 := by rw [L.sp]; exact ctl_in' hv (k := 3) (by decide)
  have hsub : BitVec.ofNat 64 len - BitVec.ofNat 64 c = BitVec.ofNat 64 (len - c) := Offset.ofNat_sub_ofNat hc
  have hp : pLen ≤ 384 := by omega
  have e15 := shl_small pLen 15 (by omega)
  have eb : BitVec.ofNat 64 (pLen * 2 ^ 15) + BitVec.ofNat 64 pLen = BitVec.ofNat 64 (32769 * pLen) := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  refine WP.keep [.x9, .x10, .x11, .x12, .x13] ?_ (by rcases hp3 with rfl | rfl | rfl <;> decide) rfl
    (by rcases hp3 with rfl | rfl | rfl <;> decide +kernel)
  simp only [Impl.Dsa.AArch64.Generation.Refill.ranOutCheck, Impl.Dsa.AArch64.Generation.Refill.ctl,
    Nat.reduceMul, Nat.reduceAdd]
  brun [State.write, exec_ldrSp (off := 120) (by decide), exec_ldrSp (off := 472) (by decide), w15, w3, l120, l472,
    hsub, movi_small (show pLen < 2 ^ 16 by omega), movi_small (show 0 < 2 ^ 16 by decide),
    movi_small (show 1 < 2 ^ 16 by decide), exec_lsl_x (by decide : 15 < 64), e15, eb,
    loop_subs_ge (show len - c < 2 ^ 64 by omega) (show 32769 * pLen < 2 ^ 64 by omega)]
  by_cases h : 32769 * pLen ≤ len - c <;> simp [h]

/-- The next tape's length. -/
theorem request_run {s : State} {L B pLen : Nat} (hL : L < 2 ^ 32) (hB : B < 2 ^ 32) (hp : pLen ≤ 384)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 pLen) (h10 : s.gpr .x10 = BitVec.ofNat 64 L)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 B) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.request) s fun t =>
      (t.gpr .x10 = BitVec.ofNat 64 (VG.Proof.Entropy.request (256 * pLen) B L) ∧ t.gpr .x11 = BitVec.ofNat 64 B ∧
        t.mem = s.mem) ∧ Keep [.x10, .x12, .x13] s t := by
  have e8 := shl_small pLen 8 (by omega)
  refine WP.keep [.x10, .x12, .x13] ?_ (by decide) rfl (by decide +kernel)
  unfold Impl.Dsa.AArch64.Generation.Refill.request
  brun [State.write, exec_lsl_x (by decide : 8 < 64), e8, h9, h10, h11,
    loop_subs_ge (show L < 2 ^ 64 by omega) (show pLen * 2 ^ 8 < 2 ^ 64 by omega)]
  unfold VG.Proof.Entropy.request
  by_cases h1 : pLen * 2 ^ 8 ≤ L
  · simp only [h1, decide_true, ite_true, ← BitVec.ofNat_add,
      loop_subs_ge (show L + L < 2 ^ 64 by omega) (show B < 2 ^ 64 by omega)]
    by_cases h2 : B ≤ L + L
    · simp only [h2, decide_true, ite_true]; congr 1; omega
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false]; congr 1; omega
  · simp only [h1, decide_false, Bool.false_eq_true, ite_false, ← BitVec.ofNat_add,
      loop_subs_ge (show pLen * 2 ^ 8 + pLen * 2 ^ 8 < 2 ^ 64 by omega) (show B < 2 ^ 64 by omega)]
    by_cases h2 : B ≤ pLen * 2 ^ 8 + pLen * 2 ^ 8
    · simp only [h2, decide_true, ite_true]; congr 1; omega
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false]; congr 1; omega

theorem statusLoad_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block [.ldrSp .x3 152]) s fun t =>
      (t.gpr .x3 = W 19 ∧ t.mem = s.mem) ∧ Keep [.x3] s t := by
  have w : s.mem.readW (s.sp + BitVec.ofNat 64 152) 64 = W 19 := by rw [L.sp]; exact R.fr 19 (by decide)
  have l : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 152) 8 := by rw [L.sp]; exact L.ld (d := 152) (by decide)
  refine WP.keep [.x3] ?_ (by decide)
  brun [State.write, exec_ldrSp (off := 152) (by decide), w, l]

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
  have l2 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 464) 8 := by rw [hsp]; exact ctl_in' hv (k := 2) (by decide)
  have l3 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 472) 8 := by rw [hsp]; exact ctl_in' hv (k := 3) (by decide)
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
  have l : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 d) 8 := by
    rw [hsp]; exact ⟨_, List.mem_append_right _ hv, Offset.contains_base F (by omega) (by omega)⟩
  refine WP.keep [.x10, .x11, .x12] ?_ (by rcases hd with rfl | rfl <;> decide) rfl
    (by rcases hd with rfl | rfl <;> decide +kernel)
  brun [State.write, exec_ldrSp (off := d) (by omega), l, movi_small (show 0 < 2 ^ 16 by decide)]
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
  have hrl : (⟨(randTape h).ptr, (randTape h).bytes.length⟩ : Region) = inRand s₀ := by
    simp only [randTape, bytesAt_length, inRand]
  have fb : ∀ {r : Region}, (r = inOut s₀ ∨ r = inUsed s₀ ∨ r = inRand s₀ ∨ r = inScr s₀ ∨ r = inState s₀) →
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
  have Rt : Rep t.mem (refillBase s₀) (refillGeometry h).hash V W :=
    rep_of_disjoint_frame R hf (fun r hr => ((results_regions h) r hr).1.symm)
      (fun r hr => ((results_regions h) r hr).2.1.symm)
  exact ⟨lay_of_rep hm.layout R Rt rfl hsp hw, ⟨V, Rt⟩, hm.slots, hm.scratch.congr hw,
    tapeMemory_frame hm.seeds hf (fun r hr => ((results_regions h) r hr).2.2.1) hr hw,
    tapeMemory_frame hm.hs hf (fun r hr => ((results_regions h) r hr).2.2.1.sub_left hin) hr hw,
    tapeMemory_frame hm.rand hf (fun r hr => ((results_regions h) r hr).2.2.1) hr hw⟩

/-- After `results`: the words written to `state` and `used` over the memory `m₁` the
controller left, the status kept in `ctl 3`, and the parameters still to output. -/
def ResultsDone (v t : State) : Prop :=
  ∃ (hs : GenerationTape (refillGeometry h)) (W : Nat → BitVec 64) (m₁ : Mem) (r0 r3 uv : BitVec 64) (st : Nat),
    HsIn h hs ∧ GenerationMemory ((refillContext h).withHs hs) W t ∧
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

theorem results_ok {v t : State} (hv : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr)
    (hd : LoopDone h v t) : WP isa (Impl.Dsa.AArch64.Generation.Refill.results pBytes) t (ResultsDone h v) := by
  obtain ⟨hs, W, hin, hm, c0, c1, fv, rdv, wrv, cases⟩ := hd
  have hp3 : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384 := by
    have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega
  have hp : pBytes ≤ 384 := by omega
  have wt : t.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr := wrv.trans hv
  have env : ∀ x : State, x.sp = refillBase s₀ → x.wr = t.wr → ctlWord x.mem (refillBase s₀) 0 = s₀.gpr .x2 →
      ctlWord x.mem (refillBase s₀) 1 = s₀.gpr .x7 → ResEnv x (refillBase s₀) (s₀.gpr .x7) (s₀.gpr .x2) :=
    fun x hsp hw e0 e1 =>
    { sp := hsp
      ctl := by rw [hw, wt]; exact List.mem_cons_self ..
      st := by rw [hw, wt]; exact List.mem_cons_of_mem _ (by rw [h.wr]; simp [inState])
      us := by rw [hw, wt]; exact List.mem_cons_of_mem _ (by rw [h.wr]; simp [inUsed])
      c0 := e0
      c1 := e1 }
  have hlen : (randTape h).bytes.length < 2 ^ 32 := by
    have hr := h.randLength
    rw [h.width] at hr
    change (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat).length < _
    rw [bytesAt_length]; unfold Spec.Dsa.parameterEntropy at hr; omega
  have h15 : W 15 = BitVec.ofNat 64 (randTape h).bytes.length :=
    (hm.slots 15 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randLengthSlot
  have hv480 : (⟨refillBase s₀, 480⟩ : Region) ∈ t.wr := by rw [wt]; exact List.mem_cons_self ..
  have packedSub : ∀ r ∈ [inState s₀, inUsed s₀, ctlRegion (refillBase s₀)],
      (⟨off (s₀.gpr .x5) packed, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region).Disjoint r := by
    have qn : Spec.Dsa.generationQLen pBytes ≤ 32 := by unfold Spec.Dsa.generationQLen; split <;> omega
    intro r hr
    exact ((results_regions h) r hr).2.2.2.symm.sub_left ((refillGeometry h).part_sub
      ((refillGeometry h).small_bound (d := packed) (n := 2 * pBytes + Spec.Dsa.generationQLen pBytes) (by decide)
        (by unfold VG.Impl.Dsa.Generation.Layout.arithmeticBytes; omega)))
  -- the end, from the words stored
  have fin : ∀ {x y : State} {a b c : BitVec 64} {st : Nat}, x.mem = t.mem → x.sp = refillBase s₀ →
      x.rd = t.rd → x.wr = t.wr →
      y.mem = (written x.mem (s₀.gpr .x7) (s₀.gpr .x2) a b c).writeW (off (refillBase s₀) 472) (BitVec.ofNat 64 st) →
      y.sp = x.sp → y.rd = x.rd → y.wr = x.wr →
      a = BitVec.ofNat 64 (total h).remaining → b = BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested pBytes (total h)) →
      c = BitVec.ofNat 64 (total h).used → st = (total h).status →
      ((W 19 ≠ 1 ∧ expectedOf (total h) = none) ∨
        (W 19 = 1 ∧ ∃ p, expectedOf (total h) = some p ∧
          Spec.Rsa.bytesAt t.mem (off (s₀.gpr .x5) packed) (2 * pBytes + Spec.Dsa.generationQLen pBytes) =
            Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes) p)) →
      ResultsDone h v y := by
    intro x y a b c st xm xsp xrd xwr ym ysp yrd ywr ha hb hc hst out
    have fw : Frame [inState s₀, inUsed s₀, ctlRegion (refillBase s₀)] x.mem y.mem := by
      rw [ym]; exact results_frame _ _ _ _ _ _ _ _
    have hmx : GenerationMemory ((refillContext h).withHs hs) W x := by
      obtain ⟨V, R⟩ := hm.rep
      have Rx : Rep x.mem (refillBase s₀) (refillGeometry h).hash V W := xm ▸ R
      exact hm.frame (lay_of_rep hm.layout R Rx rfl (xsp.trans hm.layout.sp.symm) xwr) ⟨V, Rx⟩ (fun _ _ => rfl)
        (by rw [xm]; exact Frame.refl _ _) xrd xwr
    refine ⟨hs, W, t.mem, a, b, c, st, hin, genMem_results h hin hmx fw ysp yrd ywr, fv, by rw [ym, xm],
      ha, hb, hc, hst, ?_, ysp.trans xsp, yrd.trans (xrd.trans rdv), ywr.trans (xwr.trans wrv)⟩
    rcases out with o | ⟨h19, p, he, bytes⟩
    · exact Or.inl o
    · refine Or.inr ⟨h19, p, he, ?_⟩
      rw [VG.Proof.Dsa.Generation.frame_bytesAt fw packedSub (by unfold Spec.Dsa.generationQLen; split <;> omega), xm]
      exact bytes
  obtain ⟨V, R⟩ := hm.rep
  unfold Impl.Dsa.AArch64.Generation.Refill.results
  refine WP.seq (WP.mono (statusLoad_run hm.layout R) fun t₁ ⟨⟨x3₁, m₁⟩, k₁⟩ => ?_)
  have sp₁ : t₁.sp = refillBase s₀ := k₁.sp.trans hm.layout.sp
  have ev₁ : eval (.zero .x .x3) t₁ = some (W 19 == 0) := by simp only [eval, State.read, x3₁, BitVec.setWidth_eq]
  have cw₁ : ∀ k, ctlWord t₁.mem (refillBase s₀) k = ctlWord t.mem (refillBase s₀) k := fun k => by rw [m₁]
  rcases cases with ⟨h19, c, hc, c3, htot⟩ | ⟨h19, c, k, hc, c3, c2, hk, htot⟩ | ⟨h19, a, u, hu, h16, htot, bytes⟩
  · -- no seeds left
    refine WP.ite false (ev₁.trans (by rw [h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    refine WP.seq (WP.mono minusOne_run fun t₂ ⟨⟨ev₂, m₂⟩, k₂⟩ => ?_)
    refine WP.ite false (ev₂.trans (by rw [x3₁, h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    have sp₂ : t₂.sp = refillBase s₀ := k₂.sp.trans sp₁
    simp only [Impl.Dsa.AArch64.Generation.Refill.exhaustedWords, Impl.Dsa.AArch64.Generation.Refill.ctl,
      List.append_assoc, Nat.reduceMul, Nat.reduceAdd]
    apply WP.block_append
    refine WP.mono (prefixZ_run sp₂ (by rw [k₂.wr, k₁.wr]; exact hv480) (d := 472) (Or.inl rfl))
      fun t₃ ⟨⟨x11, x10, x12, m₃⟩, k₃⟩ => ?_
    have mt₃ : t₃.mem = t.mem := m₃.trans (m₂.trans m₁)
    refine WP.mono (stores_run (env t₃ (k₃.sp.trans sp₂) (k₃.wr.trans (k₂.wr.trans k₁.wr))
      (by rw [mt₃]; exact c0) (by rw [mt₃]; exact c1)) 3 (by decide) x11 x10 x12)
      fun t₄ ⟨m₄, sp₄, rd₄, wr₄⟩ => ?_
    refine fin mt₃ (k₃.sp.trans sp₂) (k₃.rd.trans (k₂.rd.trans k₁.rd)) (k₃.wr.trans (k₂.wr.trans k₁.wr))
      m₄ sp₄ rd₄ wr₄ ?_ ?_ ?_ ?_ (Or.inl ⟨by rw [h19]; decide, by rw [htot]; rfl⟩)
    all_goals simp only [htot, Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested,
      VG.Proof.Entropy.requested, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status]
    all_goals first | rfl | (rw [mt₃]; exact c3) | (rw [m₂, m₁]; exact c3)
  · -- the tape ran out
    refine WP.ite true (ev₁.trans (by rw [h19]; rfl)) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    obtain ⟨V₁, R₁⟩ := (genMem_keep hm m₁ k₁).rep
    have L₁ := (genMem_keep hm m₁ k₁).layout
    refine WP.seq (WP.mono (ranOutCheck_run L₁ R₁ (by rw [k₁.wr]; exact hv480) (by change ctlWord t₁.mem (refillBase s₀) 3 = _; rw [cw₁]; exact c3) h15 hc
      (by omega) hp3) fun t₂ ⟨⟨x10₂, x9₂, x11₂, x12₂, m₂⟩, k₂⟩ => ?_)
    have sp₂ : t₂.sp = refillBase s₀ := k₂.sp.trans sp₁
    have mt₂ : t₂.mem = t.mem := m₂.trans m₁
    by_cases hL : 32769 * pBytes ≤ (randTape h).bytes.length - c
    · refine WP.ite false (by simp [eval, State.read, x12₂, hL]) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
      simp only [Impl.Dsa.AArch64.Generation.Refill.exhaustedWords, Impl.Dsa.AArch64.Generation.Refill.ctl,
        List.append_assoc, Nat.reduceMul, Nat.reduceAdd]
      apply WP.block_append
      refine WP.mono (prefixZ_run sp₂ (by rw [k₂.wr, k₁.wr]; exact hv480) (d := 472) (Or.inl rfl))
        fun t₃ ⟨⟨x11, x10, x12, m₃⟩, k₃⟩ => ?_
      have mt₃ : t₃.mem = t.mem := m₃.trans mt₂
      refine WP.mono (stores_run (env t₃ (k₃.sp.trans sp₂) (k₃.wr.trans (k₂.wr.trans k₁.wr))
        (by rw [mt₃]; exact c0) (by rw [mt₃]; exact c1)) 3 (by decide) x11 x10 x12)
        fun t₄ ⟨m₄, sp₄, rd₄, wr₄⟩ => ?_
      have hL' : Spec.Dsa.parameterEntropy pBytes ≤ (randTape h).bytes.length - c := by
        unfold Spec.Dsa.parameterEntropy; omega
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
        (by omega) (by unfold Spec.Dsa.parameterEntropy; omega) hp x9₂ x10₂ x11₂) fun t₃ ⟨⟨x10₃, x11₃, m₃⟩, k₃⟩ => ?_
      have sp₃ : t₃.sp = refillBase s₀ := k₃.sp.trans sp₂
      have mt₃ : t₃.mem = t.mem := m₃.trans mt₂
      apply WP.block_append
      refine WP.mono (prefixE_run sp₃ (by rw [k₃.wr, k₂.wr, k₁.wr]; exact hv480))
        fun t₄ ⟨⟨x11₄, x12₄, m₄⟩, k₄⟩ => ?_
      have mt₄ : t₄.mem = t.mem := m₄.trans mt₃
      refine WP.mono (stores_run (env t₄ (k₄.sp.trans sp₃) (k₄.wr.trans (k₃.wr.trans (k₂.wr.trans k₁.wr)))
        (by rw [mt₄]; exact c0) (by rw [mt₄]; exact c1)) 0 (by decide) x11₄
        ((k₄.gpr .x10 (by decide)).trans x10₃) x12₄)
        fun t₅ ⟨m₅, sp₅, rd₅, wr₅⟩ => ?_
      have hL' : ¬Spec.Dsa.parameterEntropy pBytes ≤ (randTape h).bytes.length - c := by
        unfold Spec.Dsa.parameterEntropy; omega
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
    have sp₂ : t₂.sp = refillBase s₀ := k₂.sp.trans sp₁
    simp only [Impl.Dsa.AArch64.Generation.Refill.acceptedWords, List.append_assoc]
    apply WP.block_append
    refine WP.mono (prefixZ_run sp₂ (by rw [k₂.wr, k₁.wr]; exact hv480) (d := 128) (Or.inr rfl))
      fun t₃ ⟨⟨x11, x10, x12, m₃⟩, k₃⟩ => ?_
    have mt₃ : t₃.mem = t.mem := m₃.trans (m₂.trans m₁)
    refine WP.mono (stores_run (env t₃ (k₃.sp.trans sp₂) (k₃.wr.trans (k₂.wr.trans k₁.wr))
      (by rw [mt₃]; exact c0) (by rw [mt₃]; exact c1)) 1 (by decide) x11 x10 x12)
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

theorem finish_ok {v t : State} (hv : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr) (hd : LoopDone h v t) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.finish pBytes) t (FinishDone h v) := by
  have o := refillOutputPlan h
  have outLen : 2 * pBytes + Spec.Dsa.generationQLen pBytes = (s₀.gpr .x1).toNat := by
    rw [← h.width]; exact h.outLength.symm
  unfold Impl.Dsa.AArch64.Generation.Refill.finish
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (results_ok h hv hd) fun t₁ D => ?_)
  obtain ⟨hs, W, m₁, r0, r3, uv, st, hin, hm, fv, mt₁, hr0, hr3, huv, hst, out, sp₁, rd₁, wr₁⟩ := D
  have o' : OutputPlan ((refillContext h).withHs hs) := ⟨o.lengthSlot, o.bound, o.separate⟩
  have hw : (⟨((refillContext h).withHs hs).saved 6,
      2 * ((refillContext h).withHs hs).geo.pLen + ((refillContext h).withHs hs).geo.qLen⟩ : Region) ∈ t₁.wr := by
    change (⟨s₀.gpr .x0, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region) ∈ t₁.wr
    rw [outLen, wr₁, hv]; exact List.mem_cons_of_mem _ (by rw [h.wr]; simp [inOut])
  refine WP.seq (WP.mono (finishOutput_ok hm o' hw (expectedOf (total h)) out) fun t₂ ⟨_, bytes₂, f₂, k₂⟩ => ?_)
  have f₂' : Frame [⟨refillBase s₀, frameBytes⟩, inOut s₀] t₁.mem t₂.mem := by
    refine f₂.mono fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl
    · exact Or.inl rfl
    · right; change _ = (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region); rw [← outLen]; rfl
  have c3 : ctlWord t₂.mem (refillBase s₀) 3 = BitVec.ofNat 64 (total h).status := by
    rw [ctlWord_frame f₂' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ctl_frame _
      · exact (h.frame_disjoint (r := inOut s₀) (by simp) (d := 448) (n := 32) (by decide)).symm) (by decide),
      mt₁, hst]
    exact ctlWord_write_self _ _ 3 _
  have sp₂ : t₂.sp = refillBase s₀ := k₂.sp.trans sp₁
  have l : InRegions (t₂.rd ++ t₂.wr) (t₂.sp + BitVec.ofNat 64 472) 8 := by
    rw [sp₂]
    exact ctl_in' (s := t₂) (F := refillBase s₀) (by rw [k₂.wr, wr₁, hv]; exact List.mem_cons_self ..) (k := 3) (by decide)
  have w : t₂.mem.readW (t₂.sp + BitVec.ofNat 64 472) 64 = BitVec.ofNat 64 (total h).status := by
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
