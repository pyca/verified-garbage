module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillFinish
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySave
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-! # The refillable-tape search on x86-64: correctness for one width

`refill_correct`: from `vg_dsa_parameter_search`'s precondition for one
width, the code runs to its postcondition and keeps the calling convention,
given the correctness of one seed's attempt (`RefillAttempt.lean`'s
`refillAttempt_ok`). The stack it needs is 568 octets: the saved
registers' 48, the controller's 32, the attempts' 296 and the 192 their
calls use. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.X86_64.Spill VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64

/-! ## The words written -/

theorem written_state (m : Mem) {St U : Addr} (hd : (⟨U, 8⟩ : Region).Disjoint ⟨St, 32⟩) (r0 r3 uv : BitVec 64) :
    Spec.Rsa.wordsAt (written m St U r0 r3 uv) St 4 =
      [r0, m.readW (St + BitVec.ofNat 64 8) 64, m.readW (St + BitVec.ofNat 64 16) 64, r3] := by
  have hf : Frame [⟨St, 8⟩, ⟨off St 24, 8⟩, ⟨U, 8⟩] m (written m St U r0 r3 uv) := by
    unfold written
    exact (((Frame.refl [⟨St, 8⟩, ⟨off St 24, 8⟩, ⟨U, 8⟩] m).writeW (List.mem_cons_self ..) r0
      (Region.contains_self St 8)).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) r3 (Region.contains_self (off St 24) 8)).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) uv (Region.contains_self U 8)
  have mid : ∀ d, 8 ≤ d → d + 8 ≤ 24 → (written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 d) 64 =
      m.readW (St + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    hf.readW (Region.contains_self _ _) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint_base St h₁ (by omega)
      · exact Offset.disjoint St (d := d) (e := 24) (by omega) (by omega) (by omega)
      · exact (hd.symm.sub_left (Offset.sub_base St (by omega))) ) (by decide)
  have uSt : Mem.Sep St 8 U 8 := hd.symm.sep (contains_head _ (by decide)) (contains_head _ (by decide))
  have uSt24 : Mem.Sep (off St 24) 8 U 8 := hd.symm.sep (Offset.contains_base _ (by decide) (by decide))
    (contains_head _ (by decide))
  change [(written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 0) 64,
    (written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 8) 64,
    (written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 16) 64,
    (written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 24) 64] = _
  rw [mid 8 (by decide) (by decide), mid 16 (by decide) (by decide), show St + BitVec.ofNat 64 0 = St from BitVec.add_zero St]
  unfold written
  rw [Mem.readW_writeW_sep uSt (by decide), Mem.readW_writeW_sep (Offset.sep_base St (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self64, show St + BitVec.ofNat 64 24 = off St 24 from rfl, Mem.readW_writeW_sep uSt24 (by decide),
    Mem.readW_writeW_self64]

theorem written_used (m : Mem) (St U : Addr) (r0 r3 uv : BitVec 64) :
    Spec.Rsa.wordsAt (written m St U r0 r3 uv) U 1 = [uv] := by
  change [(written m St U r0 r3 uv).readW (U + BitVec.ofNat 64 0) 64] = _
  rw [show U + BitVec.ofNat 64 0 = U from BitVec.add_zero U]
  exact congrArg (· :: []) (Mem.readW_writeW_self64 _ _ _)

theorem wordsAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 8 * n⟩ : Region).Disjoint r) (hn : 8 * n < 2 ^ 64) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf.readW (Offset.contains_base p (d := 8 * i) (n := 8) (k := 8 * n) (by omega) (by omega)) hd (by decide)

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

/-- What the body may write. -/
def bodyRegions : List Region :=
  ctlRegion (refillBase s₀) :: (refillContext h).changed ++ [inState s₀, inUsed s₀, inOut s₀]

/-- The saved registers' slots. -/
def savedRegion : Region := ⟨off (low s₀) 520, 48⟩

theorem buffer_disjoint {r : Region} (hr : r = inOut s₀ ∨ r = inUsed s₀ ∨ r = inRand s₀ ∨ r = inState s₀ ∨ r = inArgs s₀) :
    ∀ q ∈ savedRegion (s₀ := s₀) :: ctlRegion (refillBase s₀) :: (refillContext h).changed, r.Disjoint q := by
  have scr : r.Disjoint (inScr s₀) := by
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.outScr
    · exact h.usedScr
    · exact h.randScr
    · exact h.scrState.symm
    · exact h.scrArgs.symm
  have hr' : r = inOut s₀ ∨ r = inUsed s₀ ∨ r = inRand s₀ ∨ r = inScr s₀ ∨ r = inState s₀ ∨ r = inArgs s₀ := by
    rcases hr with h' | h' | h' | h' | h' <;> simp [h']
  intro q hq
  simp only [savedRegion, GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact (h.stack_disjoint (by decide) hr').symm
  · rw [ctlRegion_eq]; exact (h.stack_disjoint (by decide) hr').symm
  · exact scr.sub_right h.arena_sub
  · exact (h.stack_disjoint (d := 192) (n := 296) (by decide) hr').symm
  · change r.Disjoint (below (refillBase s₀) 192)
    rw [refillBase_below]
    simpa only [off, BitVec.add_zero] using (h.stack_disjoint (d := 0) (n := 192) (by decide) hr').symm

/-- The body's results. -/
def BodyPost (u t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (total h).status ∧
  Spec.Rsa.bytesAt t.mem (s₀.gpr .rdi) (2 * pBytes + Spec.Dsa.generationQLen pBytes) =
    ((expectedOf (total h)).map (Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes))).getD
      (List.replicate (2 * pBytes + Spec.Dsa.generationQLen pBytes) 0) ∧
  Spec.Rsa.wordsAt t.mem (s₀.gpr .rdx) 1 = [BitVec.ofNat 64 (total h).used] ∧
  Spec.Rsa.wordsAt t.mem (stackArg s₀ 1) 4 = [BitVec.ofNat 64 (total h).remaining,
    s₀.mem.readW (stackArg s₀ 1 + BitVec.ofNat 64 8) 64, s₀.mem.readW (stackArg s₀ 1 + BitVec.ofNat 64 16) 64,
    BitVec.ofNat 64 (total h).requested] ∧
  Frame (bodyRegions h) u.mem t.mem ∧ t.gpr .rsp = u.gpr .rsp ∧ t.rd = u.rd ∧ t.wr = u.wr

variable {checkName : String}

theorem body_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream} {sq : Prog isa} {mul : Nat → Nat → Nat → Prog isa}
    {prime : Prog isa} {qBytes : Nat} (hq : qBytes = Spec.Dsa.generationQLen pBytes)
    (hA : AttemptOk h (Impl.Dsa.X86_64.Generation.Refill.refillAttempt (checkName := checkName) G1 G256 sq mul prime
      pBytes qBytes))
    {u : State} (a : RefillAllocated h u) :
    WP isa (Impl.Dsa.X86_64.Generation.Refill.body (checkName := checkName) G1 G256 sq mul prime pBytes qBytes) u
      (BodyPost h u) := by
  simp only [Impl.Dsa.X86_64.Generation.Refill.body, Impl.Dsa.X86_64.Generation.Refill.controller,
    Impl.Dsa.X86_64.Generation.Refill.finish, VG.Impl.Bignum.X86_64.seqs]
  apply WP.seq
  refine WP.mono (entry_ok h a hq) fun v ⟨W, hm, h16, _, c0, c1, c2, fE, kE⟩ => ?_
  have hcv : ctlRegion (refillBase s₀) ∈ v.wr := kE.2.2 ▸ a.ctl
  have hwv : ∀ r ∈ s₀.wr, r ∈ v.wr := fun r hr => kE.2.2 ▸ a.wr r hr
  apply WP.seq
  refine WP.mono (controller_ok h hq hA hcv _ v (loop_initial h hm h16 c0 c1 c2)) fun t hd => ?_
  apply WP.seq
  refine WP.mono (results_ok h hcv hwv hd) fun t₁ hr => ?_
  obtain ⟨hs, W', m₁, r0, r3, uv, hin, hm₁, fm₁, mem₁, e0, e3, eu, est, hres, sp₁, rd₁, wr₁⟩ := hr
  have o : OutputPlan ((refillContext h).withHs hs) :=
    ⟨(refillOutputPlan h).lengthSlot, (refillOutputPlan h).bound, (refillOutputPlan h).separate⟩
  have outLen : 2 * pBytes + Spec.Dsa.generationQLen pBytes = (s₀.gpr .rsi).toNat := by
    rw [h.outLength, h.width]
  have hw : (⟨((refillContext h).withHs hs).saved 6,
      2 * ((refillContext h).withHs hs).geo.pLen + ((refillContext h).withHs hs).geo.qLen⟩ : Region) ∈ t₁.wr := by
    change (⟨s₀.gpr .rdi, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region) ∈ t₁.wr
    rw [outLen, wr₁]; exact hwv _ (by rw [h.wr]; simp [inOut])
  refine WP.mono (finishTail_ok hm₁ o hw (expectedOf (total h)) hres) fun t ⟨rax, bytes, ft, spt, rdt, wrt⟩ => ?_
  have stateFt : ∀ q ∈ [(⟨refillBase s₀, frameBytes⟩ : Region), inOut s₀], (inState s₀).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact h.frame_disjoint (r := inState s₀) (by simp) _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact h.outState.symm
  have ft' : Frame [(⟨refillBase s₀, frameBytes⟩ : Region), inOut s₀] t₁.mem t.mem := by
    have e : (⟨((refillContext h).withHs hs).saved 6,
        2 * ((refillContext h).withHs hs).geo.pLen + ((refillContext h).withHs hs).geo.qLen⟩ : Region) = inOut s₀ := by
      change (⟨s₀.gpr .rdi, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region) = _
      rw [outLen]; rfl
    rw [← e]; exact ft
  have stateM : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' → (∀ q ∈ rs, (inState s₀).Disjoint q) →
      ∀ d, d + 8 ≤ 32 → m'.readW (stackArg s₀ 1 + BitVec.ofNat 64 d) 64 = m.readW (stackArg s₀ 1 + BitVec.ofNat 64 d) 64 :=
    fun hf hd d hd8 => hf.readW (Offset.contains_base _ (d := d) (n := 8) (k := 32) hd8 (by omega)) hd (by decide)
  have allPrior : ∀ q ∈ savedRegion (s₀ := s₀) :: ctlRegion (refillBase s₀) :: (refillContext h).changed,
      (inState s₀).Disjoint q := buffer_disjoint h (by simp)
  have fu : Frame [savedRegion (s₀ := s₀), ⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] s₀.mem v.mem :=
    (a.mem.mono fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..).trans
      (fE.mono fun r hr => List.mem_cons_of_mem _ hr)
  have fs : Frame (savedRegion (s₀ := s₀) :: ctlRegion (refillBase s₀) :: (refillContext h).changed) s₀.mem m₁ :=
    (fu.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl
      · exact Or.inl rfl
      · simp [GenerationContext.changed, refillContext, refillGeometry]
      · exact Or.inr (Or.inl rfl)).trans (fm₁.mono fun r hr => List.mem_cons_of_mem _ hr)
  have usedState : (⟨s₀.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s₀ 1, 32⟩ := h.usedState
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rax, est]
  · exact bytes
  · rw [wordsAt_frame ft (n := 1) (fun q hq => ?_) (by decide), mem₁, written_used, eu]
    have hd : ∀ q ∈ [(⟨refillBase s₀, frameBytes⟩ : Region), inOut s₀], (inUsed s₀).Disjoint q := by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact h.frame_disjoint (r := inUsed s₀) (by simp) _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact h.outUsed.symm
    rw [← (show _ = inOut s₀ from by
      change (⟨s₀.gpr .rdi, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region) = _
      rw [outLen]; rfl)] at hd
    exact hd q hq
  · rw [wordsAt_frame ft' (n := 4) stateFt (by decide), mem₁, written_state _ usedState, e0, e3,
      stateM fs allPrior 8 (by decide), stateM fs allPrior 16 (by decide)]
  · have fr : ⟨refillBase s₀, frameBytes⟩ ∈ bodyRegions h := by
      simp [bodyRegions, GenerationContext.changed, refillContext, refillGeometry]
    refine ((fE.mono ?_).trans (fm₁.mono ?_)).trans (((mem₁ ▸ written_frame m₁ _ _ _ _ _).mono ?_).trans (ft'.mono ?_))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact fr
      · exact List.mem_cons_self ..
    · intro r hr
      simp only [bodyRegions, List.cons_append, List.mem_cons, List.mem_append] at hr ⊢
      rcases hr with hr | hr
      · exact Or.inl hr
      · exact Or.inr (Or.inl hr)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [bodyRegions, inState, inUsed]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact fr
      · simp [bodyRegions]
  · rw [spt, sp₁, a.rsp]
  · rw [rdt, rd₁, kE.2.1]
  · rw [wrt, wr₁, kE.2.2]

/-! ## The frames -/

theorem saved_body : ∀ r ∈ bodyRegions h, (savedRegion (s₀ := s₀)).Disjoint r := by
  intro r hr
  simp only [bodyRegions, GenerationContext.changed, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ctlRegion_eq]; exact Offset.disjoint (low s₀) (d := 520) (e := 488) (by omega) (by omega) (by omega)
  · exact (h.stack_disjoint (r := inScr s₀) (by decide) (by simp)).sub_right h.arena_sub
  · exact Offset.disjoint (low s₀) (d := 520) (e := 192) (k := 296) (by omega) (by omega) (by omega)
  · change savedRegion.Disjoint (below (refillBase s₀) 192)
    rw [refillBase_below]
    exact Offset.disjoint_base (low s₀) (by omega) (by omega)
  · exact h.stack_disjoint (by decide) (by simp)
  · exact h.stack_disjoint (by decide) (by simp)
  · exact h.stack_disjoint (by decide) (by simp)

theorem toNat_sub_k {x : Addr} {k : Nat} (h : k ≤ x.toNat) : (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by
  have := x.isLt
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem rsp_alloc (x : Addr) :
    x - BitVec.ofNat 64 48 - BitVec.ofNat 64 32 - BitVec.ofNat 64 296 = off (x - BitVec.ofNat 64 568) 192 := by
  simp only [off]; bv_omega

theorem ctl_alloc (x : Addr) :
    x - BitVec.ofNat 64 48 - BitVec.ofNat 64 32 = off (off (x - BitVec.ofNat 64 568) 192) 296 := by
  simp only [off]; bv_omega

theorem saved_alloc (x : Addr) : x - BitVec.ofNat 64 48 = off (x - BitVec.ofNat 64 568) 520 := by
  simp only [off]; bv_omega

/-- The results the function returns. -/
def RefillRes (t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (total h).status ∧
  Spec.Rsa.bytesAt t.mem (s₀.gpr .rdi) (2 * pBytes + Spec.Dsa.generationQLen pBytes) =
    ((expectedOf (total h)).map (Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes))).getD
      (List.replicate (2 * pBytes + Spec.Dsa.generationQLen pBytes) 0) ∧
  Spec.Rsa.wordsAt t.mem (s₀.gpr .rdx) 1 = [BitVec.ofNat 64 (total h).used] ∧
  Spec.Rsa.wordsAt t.mem (stackArg s₀ 1) 4 = [BitVec.ofNat 64 (total h).remaining,
    s₀.mem.readW (stackArg s₀ 1 + BitVec.ofNat 64 8) 64, s₀.mem.readW (stackArg s₀ 1 + BitVec.ofNat 64 16) 64,
    BitVec.ofNat 64 (total h).requested]

theorem RefillRes.congr {t t' : State} (r : RefillRes h t) (hr : t'.gpr .rax = t.gpr .rax) (hm : t'.mem = t.mem) :
    RefillRes h t' := by
  obtain ⟨a, b, c, d⟩ := r
  exact ⟨hr.trans a, hm ▸ b, hm ▸ c, hm ▸ d⟩

theorem inner_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream} {sq : Prog isa} {mul : Nat → Nat → Nat → Prog isa}
    {prime : Prog isa} {qBytes : Nat} (hq : qBytes = Spec.Dsa.generationQLen pBytes)
    (hA : AttemptOk h (Impl.Dsa.X86_64.Generation.Refill.refillAttempt (checkName := checkName) G1 G256 sq mul prime
      pBytes qBytes))
    {u : State} (hg : u.gpr = (allocState 48 s₀).gpr) (hr : u.rd = s₀.rd) (hw : u.wr = (allocState 48 s₀).wr)
    (hf : Frame [⟨(allocState 48 s₀).gpr .rsp, 48⟩] s₀.mem u.mem)
    (saved : Saved u.mem ((allocState 48 s₀).gpr .rsp) s₀.gpr spillSlots) :
    WP isa (.frame (.alloc 32) (.frame (.alloc Impl.Dsa.X86_64.Generation.Refill.frameBytes)
        (Impl.Dsa.X86_64.Generation.Refill.body (checkName := checkName) G1 G256 sq mul prime pBytes qBytes)
        (.free Impl.Dsa.X86_64.Generation.Refill.frameBytes)) (.free 32)) u fun t =>
      RefillRes h t ∧ Saved t.mem ((allocState 48 s₀).gpr .rsp) s₀.gpr spillSlots ∧
      t.gpr .rsp = u.gpr .rsp ∧ t.rd = u.rd ∧ t.wr = u.wr := by
  have lower : 568 ≤ (s₀.gpr .rsp).toNat := h.stackLower
  have ursp : u.gpr .rsp = s₀.gpr .rsp - BitVec.ofNat 64 48 := by rw [hg]; rfl
  have u48 : (u.gpr .rsp).toNat = (s₀.gpr .rsp).toNat - 48 := by rw [ursp, toNat_sub_k (by omega)]
  have r1 : 32 ≤ (u.gpr .rsp).toNat := by omega
  apply alloc_frame_ok (by decide) r1
  have r2 : 296 ≤ ((allocState 32 u).gpr .rsp).toNat := by
    change 296 ≤ (u.gpr .rsp - BitVec.ofNat 64 32).toNat
    rw [toNat_sub_k (by omega)]; omega
  apply alloc_frame_ok (by decide) r2
  have a : RefillAllocated h (allocState 296 (allocState 32 u)) :=
    { rsp := by
        change u.gpr .rsp - BitVec.ofNat 64 32 - BitVec.ofNat 64 296 = _
        rw [ursp, rsp_alloc]; rfl
      frame := by
        have e : (allocState 296 (allocState 32 u)).gpr .rsp = refillBase s₀ := by
          change u.gpr .rsp - BitVec.ofNat 64 32 - BitVec.ofNat 64 296 = _
          rw [ursp, rsp_alloc]; rfl
        rw [← e]; exact List.mem_cons_self ..
      ctl := by
        change ctlRegion (refillBase s₀) ∈ _ :: ⟨u.gpr .rsp - BitVec.ofNat 64 32, 32⟩ :: u.wr
        rw [ursp, ctl_alloc]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      wr := fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [hw]; exact List.mem_cons_of_mem _ hr))
      rd := hr
      regs := fun r hne => by
        simp only [allocState, State.setReg, hne, ↓reduceIte, hg]
      mem := by
        change Frame _ s₀.mem u.mem
        rw [show off (low s₀) 520 = (allocState 48 s₀).gpr .rsp from (saved_alloc _).symm]; exact hf }
  refine WP.mono (body_ok h hq hA a) fun t ⟨rax, bytes, uw, sw, fr, sp, rd, wr⟩ => ⟨sp, wr, ?_, ?_, ?_⟩
  · change (freeState 296 t).gpr .rsp = _; exact freeState_rsp sp
  · exact freeState_wr wr
  refine ⟨RefillRes.congr h ⟨rax, bytes, uw, sw⟩ (by simp [freeState, State.setReg]) rfl, ?_,
    freeState_rsp (freeState_rsp sp), rd, freeState_wr (freeState_wr wr)⟩
  apply saved.frame (rs := bodyRegions h) fr
  intro p hp r hr
  refine (saved_body h r hr).sub_left ?_
  rw [savedRegion, show off (low s₀) 520 = (allocState 48 s₀).gpr .rsp from (saved_alloc _).symm]
  exact Offset.sub_base _ (spillSlots_fit p hp)

theorem run_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream} {sq : Prog isa} {mul : Nat → Nat → Nat → Prog isa}
    {prime : Prog isa} {qBytes : Nat} (hq : qBytes = Spec.Dsa.generationQLen pBytes)
    (hA : AttemptOk h (Impl.Dsa.X86_64.Generation.Refill.refillAttempt (checkName := checkName) G1 G256 sq mul prime
      pBytes qBytes)) :
    WP isa (Impl.Dsa.X86_64.Generation.Refill.code (checkName := checkName) G1 G256 sq mul prime pBytes qBytes) s₀
      fun t => RefillRes h t ∧ (∀ r ∈ calleeSaved, t.gpr r = s₀.gpr r) ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr := by
  unfold Impl.Dsa.X86_64.Generation.Refill.code
  apply alloc_frame_ok (by decide) (by have hl : 568 ≤ (s₀.gpr .rsp).toNat := h.stackLower; omega)
  refine WP.seq (WP.mono (entrySave_ok (s := allocState 48 s₀) (List.mem_cons_self ..)) ?_)
  intro u ⟨hg, hr, hw, saved, hf⟩
  have saved' : Saved u.mem ((allocState 48 s₀).gpr .rsp) s₀.gpr spillSlots := by
    intro p hp
    have hh := saved p hp
    change u.mem.readW (Spill.slot ((allocState 48 s₀).gpr .rsp) p.2) 64 = (allocState 48 s₀).gpr p.1 at hh
    change u.mem.readW _ 64 = _
    rw [hh]
    have hn : p.1 ≠ .rsp := by
      simp only [spillSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [allocState, State.setReg, hn]
  refine WP.seq (WP.mono (inner_ok h hq hA hg hr hw hf saved') ?_)
  intro v ⟨result, sv, spv, rdv, wrv⟩
  have vsp : v.gpr .rsp = (allocState 48 s₀).gpr .rsp := by rw [spv, hg]
  have vwr : (⟨v.gpr .rsp, 48⟩ : Region) ∈ v.wr := by
    rw [vsp, wrv, hw]
    exact List.mem_cons_self ..
  apply WP.mono (entryRestore_ok s₀.gpr vwr (by rw [vsp]; exact sv))
  intro t ⟨restore, rax, sp, mem, rd, wr⟩
  have tsp : t.gpr .rsp = (allocState 48 s₀).gpr .rsp := by rw [sp, vsp]
  have twr : t.wr = (allocState 48 s₀).wr := wr.trans (wrv.trans hw)
  refine ⟨tsp, twr, RefillRes.congr h (result.congr h rax mem) (by simp [freeState, State.setReg]) rfl, ?_,
    rd.trans (rdv.trans hr), freeState_wr twr⟩
  intro r hr
  by_cases hs : r = .rsp
  · subst r; exact freeState_rsp tsp
  · have hin : r ∈ spillSlots.map Prod.fst := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact False.elim (hs rfl) | decide
    have he := restore r hin
    simpa only [freeState, State.setReg, hs, ↓reduceIte] using he

end

/-! ## Correctness -/

variable {checkName : String}

/-- One seed's attempt is correct (`RefillAttempt.lean`'s `refillAttempt_ok`). -/
def AttemptCorrect (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest) : Prop :=
  ∀ {p : GenerationContext} {W : Nat → BitVec 64} {s : State}, GenerationMemory p W s →
    Region.Sub ⟨p.hs.ptr, p.hs.bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩ →
    ∀ (seed : GenerationTape p.geo), seed.bytes.length = p.geo.qLen → GenerationTapeMemory seed s →
    W 1 = seed.ptr → ∀ {used : Nat}, W 16 = BitVec.ofNat 64 used → used ≤ p.rand.bytes.length →
    WP isa (Impl.Dsa.X86_64.Generation.Refill.refillAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm
        T.run p.geo.pLen p.geo.qLen) s
      (RefillFinished p W (VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen seed.bytes
        (p.rand.bytes.drop used)) s)

theorem refill_correct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (attempt_ok : AttemptCorrect (checkName := checkName) H M Sq T)
    (pBytes qBytes : Nat) (hq : qBytes = Spec.Dsa.generationQLen pBytes)
    (sp : (Impl.Dsa.X86_64.Generation.Refill.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run
      pBytes qBytes).all (fun i => !isa.writesSp i) = true)
    (depth : (Impl.Dsa.X86_64.Generation.Refill.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run
      pBytes qBytes).x86_64Depth ≤ refillStack)
    (ctl : ctlOk (Impl.Dsa.X86_64.Generation.Refill.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run
      pBytes qBytes) = true)
    (s : State) (pre : (contract pBytes abi refillStack).pre s) :
    ∃ tr t, Exec isa (Impl.Dsa.X86_64.Generation.Refill.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm
        T.run pBytes qBytes) s tr t ∧
      abiPreserved s t ∧ (contract pBytes abi refillStack).post s t := by
  subst hq
  have h := refillABI_of pre
  have hA : AttemptOk h (Impl.Dsa.X86_64.Generation.Refill.refillAttempt (checkName := checkName) H.sha1 H.sha256
      Sq.mm M.mm T.run pBytes (Spec.Dsa.generationQLen pBytes)) :=
    fun hs W t seed hin hm hlen hseed h1 used h16 hu => attempt_ok hm hin seed hlen hseed h1 h16 hu
  obtain ⟨tr, t, he, result, callee, _, _⟩ := run_ok h rfl hA
  refine ⟨tr, t, he, ⟨callee, ?_, VG.X86_64.Exec.ctl ctl he⟩, ?_⟩
  · have hf := Exec.stackFrame (SpSafe.of_all sp) he (by have : refillStack = 568 := rfl; omega)
    have hfb := VG.X86_64.Frame.below_mono hf depth (by decide)
    apply hfb.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rw [h.wr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.retOut
      · exact h.retUsed
      · exact h.retScr
      · exact h.retState
    · simp only [List.mem_singleton] at hr
      subst r
      exact Offset.base_disjoint_below _ (by decide)
  · obtain ⟨rax, bytes, used, words⟩ := result
    sig_post [contract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two]
    have hw : (s.mem.readW (stackArg s 1 + 8) 64).toNat = pBytes := h.width
    have ht : Spec.Dsa.parameterSearch pBytes (s.mem.readW (stackArg s 1) 64).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) = total h := rfl
    have e8 : stackArg s 1 + BitVec.ofNat 64 8 = stackArg s 1 + 8 := rfl
    have e16 : stackArg s 1 + BitVec.ofNat 64 16 = stackArg s 1 + 16 := rfl
    have w8 : s.mem.readW (stackArg s 1 + 8) 64 = BitVec.ofNat 64 pBytes := by
      rw [← hw, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have w16 : s.mem.readW (stackArg s 1 + 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy pBytes) := by
      have := h.budget; rw [h.width] at this; exact this
    have outLen : (s.gpr .rsi).toNat = 2 * pBytes + Spec.Dsa.generationQLen pBytes := by
      rw [h.outLength, h.width]
    rw [hw, ht]
    refine ⟨?_, ?_, used, ?_⟩
    · have hs : (total h).status < 4 := by
        unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
      rw [rax, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    · rw [outLen, bytes]
      unfold expectedOf
      generalize (total h).outcome = o
      cases o <;> rfl
    · rw [words, e8, e16, w8, w16]

end VG.Proof.Dsa.X86_64.Generation.Refill
