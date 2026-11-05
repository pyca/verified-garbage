module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillEntry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillOutcome
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSearch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameStore
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess

/-! # The refillable-tape search's controller on x86-64

The controller runs one seed per iteration while seeds are rejected. Its
invariant (`LoopInv`): the whole search's result is the search from the
octets `c` it has consumed on, those consumed before it
(`RefillSearch.lean`), and the controller's words hold the pointers to
`used` and `state` and the seeds it may still reject. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

/-! ## Blocks -/

/-- The start of an iteration: the seed's start into `ctl 3`, and the seeds left tested. -/
theorem iterStart_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hctl : ctlRegion F ∈ s.wr) (hb : F.toNat + 328 ≤ 2 ^ 64)
    {c n : Nat} (h16 : W 16 = BitVec.ofNat 64 c) (hn : n < 2 ^ 64)
    (h2 : (s.mem.writeW (off F 320) (BitVec.ofNat 64 c)).readW (off F 312) 64 = BitVec.ofNat 64 n) :
    WP isa (.block [.mov .rax (.mem (sp 128)), .store (Impl.Dsa.X86_64.Generation.Refill.ctl 3) .rax,
        .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 2)), .alu .test .rcx (.reg .rcx)]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 c ∧ t.zf = some (decide (n = 0)) ∧
      t.mem = s.mem.writeW (off F 320) (BitVec.ofNat 64 c) ∧ Keep [.rax, .rcx] s t := by
  have cs : Scr s (off F 296) 32 := Scr.of_mem hctl (by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have c2 : InRegions (s.rd ++ s.wr) (off F 312) 8 := by simpa [off_off] using cs.ld (d := 16) (by decide)
  have c3 : InRegions s.wr (off F 320) 8 := by simpa [off_off] using cs.st (d := 24) (by decide)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 c ∧
    t.zf = some (decide (n = 0)) ∧ t.mem = s.mem.writeW (off F 320) (BitVec.ofNat 64 c)) ?_ rfl)
    fun _ ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes,
    ea_sp, L.rsp, L.ld (d := 128) (by decide), R.slot (d := 128) (k := 16) rfl (by decide) h16, c2, c3, h2,
    BitVec.and_self, ofNat_beq_zero hn]

/-- The octets left from the seed's start, compared with a seed's. -/
theorem roomCheck_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {c len q : Nat} (hrax : s.gpr .rax = BitVec.ofNat 64 c)
    (h15 : W 15 = BitVec.ofNat 64 len) (hc : c ≤ len) (hl : len < 2 ^ 64) (hq : q < 2 ^ 31) :
    WP isa (.block [.mov .rcx (.mem (sp 120)), .alu .sub .rcx (.reg .rax),
        .alu .cmp .rcx (.imm (BitVec.ofNat 32 q))]) s fun t =>
      t.cf = some (decide (len - c < q)) ∧ t.mem = s.mem ∧ Keep [.rcx] s t := by
  have hsub : BitVec.ofNat 64 len - BitVec.ofNat 64 c = BitVec.ofNat 64 (len - c) := Offset.ofNat_sub_ofNat hc
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.cf = some (decide (len - c < q)) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩
  xrun [ea_sp, L.rsp, L.ld (d := 120) (by decide), R.slot (d := 120) (k := 15) rfl (by decide) h15, hrax, hsub,
    sx_ofNat hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len - c < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : q < 2 ^ 64)]

/-- The seed's octets at `W 1`, and its witnesses after them. -/
theorem seedStart_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {c q : Nat} {ptr : Addr} (hrax : s.gpr .rax = BitVec.ofNat 64 c)
    (h13 : W 13 = ptr) (hq : q < 2 ^ 31) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.Refill.seedStart q)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd W 1 (off ptr c)) 16 (BitVec.ofNat 64 (c + q))) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax, .rcx] s t := by
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem =
      (s.mem.writeW (off F 8) (off ptr c)).writeW (off F 128) (BitVec.ofNat 64 (c + q))) ?_ rfl)
    fun t ⟨hm, kt⟩ => ?_
  · xrun [Impl.Dsa.X86_64.Generation.Refill.seedStart, ea_sp, L.rsp, L.ld (d := 104) (by decide),
      R.slot (d := 104) (k := 13) rfl (by decide) h13, hrax, L.st (d := 8) (by decide), L.st (d := 128) (by decide),
      sx_ofNat hq, off, BitVec.ofNat_add]
  have Rt : Rep t.mem F S V (upd (upd W 1 (off ptr c)) 16 (BitVec.ofNat 64 (c + q))) := by
    rw [hm]; exact (R.wf L.geo (k := 1) (by decide) _).wf L.geo (k := 16) (by decide) _
  refine ⟨lay_of_rep L R Rt (by simp [upd]) (kt.gpr (by decide)) kt.2.2, Rt, ?_, kt⟩
  rw [hm]
  exact (frameWord_write (k := 1) (by decide) _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base F (d := 128) (by decide) (by decide))

/-- A rejected seed: one fewer left. -/
theorem rejected_ok {s : State} {F : Addr} (hsp : s.gpr .rsp = F) (hctl : ctlRegion F ∈ s.wr)
    (hb : F.toNat + 328 ≤ 2 ^ 64) {n : Nat} (hn : n + 1 < 2 ^ 64)
    (h2 : s.mem.readW (off F 312) 64 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block Impl.Dsa.X86_64.Generation.Refill.rejected) s fun t =>
      t.mem = s.mem.writeW (off F 312) (BitVec.ofNat 64 n) ∧ Keep [.rax] s t := by
  have cs : Scr s (off F 296) 32 := Scr.of_mem hctl (by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have c2 : InRegions s.wr (off F 312) 8 := by simpa [off_off] using cs.st (d := 16) (by decide)
  have c2' : InRegions (s.rd ++ s.wr) (off F 312) 8 := by simpa [off_off] using cs.ld (d := 16) (by decide)
  have e : BitVec.ofNat 64 (n + 1) - 1 = BitVec.ofNat 64 n := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    rfl
  refine WP.keep [.rax] ?_ rfl
  xrun [Impl.Dsa.X86_64.Generation.Refill.rejected, Impl.Dsa.X86_64.Generation.Refill.ctl,
    Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp, hsp, c2, c2', h2]
  rw [e]

/-! ## Contexts -/

theorem withHs_withHs (p : GenerationContext) (hs hs' : GenerationTape p.geo) :
    (p.withHs hs).withHs hs' = p.withHs hs' := by
  simp only [GenerationContext.withHs]
  congr 1
  funext k
  by_cases h11 : k = 11 <;> by_cases h12 : k = 12 <;> simp [h11, h12]

theorem tapeMemory_ctl {g : GenerationGeometry} {tape : GenerationTape g} {s t : State}
    (h : GenerationTapeMemory tape s) {r : Region} (hf : Frame [r] s.mem t.mem)
    (hd : (⟨tape.ptr, tape.bytes.length⟩ : Region).Disjoint r) (hr : t.rd = s.rd) (hw : t.wr = s.wr) :
    GenerationTapeMemory tape t where
  cover := by rw [hr, hw]; exact h.cover
  bytes := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt hf (fun q hq => by rcases List.mem_singleton.mp hq with rfl; exact hd)
      (Nat.le_of_lt tape.size)]
    exact h.bytes

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

/-- An `h` tape inside the random tape. -/
def HsIn (hs : GenerationTape (refillGeometry h)) : Prop :=
  Region.Sub ⟨hs.ptr, hs.bytes.length⟩ ⟨(randTape h).ptr, (randTape h).bytes.length⟩

theorem rand_ctl : (⟨(randTape h).ptr, (randTape h).bytes.length⟩ : Region).Disjoint (ctlRegion (refillBase s₀)) := by
  change (⟨s₀.gpr .rcx, (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat).length⟩ : Region).Disjoint _
  rw [bytesAt_length]
  exact h.frame_disjoint (r := inRand s₀) (by simp) _ (by simp)

theorem ctl_changed : ∀ r ∈ (refillContext h).changed, (ctlRegion (refillBase s₀)).Disjoint r := by
  intro r hr
  simp only [GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.ctl_arena
  · exact ctl_frame _
  · exact ctl_below _

/-- The search's memory across a write of the controller's words. -/
theorem GenerationMemory.ctlFrame {hs : GenerationTape (refillGeometry h)} (hin : HsIn h hs)
    {W : Nat → BitVec 64} {s t : State} (hm : GenerationMemory ((refillContext h).withHs hs) W s)
    (hf : Frame [ctlRegion (refillBase s₀)] s.mem t.mem) (hsp : t.gpr .rsp = s.gpr .rsp)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) : GenerationMemory ((refillContext h).withHs hs) W t := by
  obtain ⟨V, R⟩ := hm.rep
  have Rt : Rep t.mem (refillBase s₀) (refillGeometry h).hash V W :=
    rep_of_disjoint_frame R hf (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact (ctl_frame _).symm)
      (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact h.ctl_hash.symm)
  exact ⟨lay_of_rep hm.layout R Rt rfl hsp hw, ⟨V, Rt⟩, hm.slots, hm.scratch.congr hw,
    tapeMemory_ctl hm.seeds hf (rand_ctl h) hr hw, tapeMemory_ctl hm.hs hf ((rand_ctl h).sub_left hin) hr hw,
    tapeMemory_ctl hm.rand hf (rand_ctl h) hr hw⟩

theorem ctlWord_changed {m m' : Mem} (hf : Frame (refillContext h).changed m m') {k : Nat} (hk : k < 4) :
    ctlWord m' (refillBase s₀) k = ctlWord m (refillBase s₀) k :=
  ctlWord_frame hf (ctl_changed h) hk

/-- A status word stored. -/
theorem statusMem_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State} (hm : GenerationMemory p W s)
    (status : Nat) (hs : status < 2 ^ 32) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.stackStatus status)) s fun t =>
      GenerationMemory p (upd W 19 (BitVec.ofNat 64 status)) t ∧ Frame p.changed s.mem t.mem ∧ Keep [.rax] s t := by
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (stackStatus_ok hm.layout R status hs) fun t ⟨Lt, Rt, ot, kt⟩ => ?_
  have ft := GenerationContext.status_frame ot
  refine ⟨hm.frame Lt ⟨V, Rt⟩ ?_ ft kt.2.1 kt.2.2, ft, kt⟩
  intro k hk
  simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The whole search's result. -/
def total : Spec.Dsa.ParameterSearchResult :=
  Spec.Dsa.parameterSearch pBytes (s₀.mem.readW (stackArg s₀ 1) 64).toNat (randTape h).bytes

/-- The controller's invariant with `n` seeds it may still reject, from the loop's entry `v`. -/
def LoopInv (v : State) (n : Nat) (t : State) : Prop :=
  ∃ (hs : GenerationTape (refillGeometry h)) (W : Nat → BitVec 64) (c : Nat), HsIn h hs ∧
    GenerationMemory ((refillContext h).withHs hs) W t ∧ W 16 = BitVec.ofNat 64 c ∧ c ≤ (randTape h).bytes.length ∧
    ctlWord t.mem (refillBase s₀) 0 = s₀.gpr .rdx ∧ ctlWord t.mem (refillBase s₀) 1 = stackArg s₀ 1 ∧
    ctlWord t.mem (refillBase s₀) 2 = BitVec.ofNat 64 n ∧ n ≤ Spec.Dsa.parameterSeeds ∧
    total h = (Spec.Dsa.parameterSearch pBytes n ((randTape h).bytes.drop c)).consume c [] ∧
    Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t.mem ∧ t.rd = v.rd ∧ t.wr = v.wr

/-- How the controller's loop ends. -/
def LoopDone (v t : State) : Prop :=
  ∃ (hs : GenerationTape (refillGeometry h)) (W : Nat → BitVec 64), HsIn h hs ∧
    GenerationMemory ((refillContext h).withHs hs) W t ∧
    ctlWord t.mem (refillBase s₀) 0 = s₀.gpr .rdx ∧ ctlWord t.mem (refillBase s₀) 1 = stackArg s₀ 1 ∧
    Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t.mem ∧ t.rd = v.rd ∧ t.wr = v.wr ∧
    ((W 19 = 2 ∧ ∃ c, c ≤ (randTape h).bytes.length ∧ ctlWord t.mem (refillBase s₀) 3 = BitVec.ofNat 64 c ∧
        total h = ⟨.exhausted, c, []⟩) ∨
      (W 19 = 0 ∧ ∃ c k, c ≤ (randTape h).bytes.length ∧ ctlWord t.mem (refillBase s₀) 3 = BitVec.ofNat 64 c ∧
        ctlWord t.mem (refillBase s₀) 2 = BitVec.ofNat 64 k ∧ k ≤ Spec.Dsa.parameterSeeds ∧
        total h = VG.Proof.Dsa.Generation.ranOutResult pBytes k ((randTape h).bytes.length - c) c) ∨
      (W 19 = 1 ∧ ∃ a u, u ≤ (randTape h).bytes.length ∧ W 16 = BitVec.ofNat 64 u ∧
        total h = ⟨.accepted a, u, []⟩ ∧
        Spec.Rsa.bytesAt t.mem (off (s₀.gpr .r9) VG.Impl.Dsa.Generation.Layout.packed)
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

/-- The status compared with 3. -/
theorem statusTest_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State} (hm : GenerationMemory p W s) :
    WP isa (.block Impl.Dsa.X86_64.Generation.tapeStatus) s fun t =>
      isa.eval .e t = some (W 19 == 3) ∧ GenerationMemory p W t ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  obtain ⟨V, R⟩ := hm.rep
  exact WP.mono (tapeStatus_ok hm.layout R) fun t ⟨hz, hmt, kt⟩ => ⟨hz, hm.congr hmt kt, hmt, kt⟩

theorem ctlWord_eq_of_mem {m m' : Mem} (he : m' = m) (F : Addr) (k : Nat) : ctlWord m' F k = ctlWord m F k := by
  rw [he]

theorem step_ok {qBytes : Nat} (hq : qBytes = Spec.Dsa.generationQLen pBytes) {attempt : Prog isa}
    (hA : AttemptOk h attempt) {v : State} (hv : ctlRegion (refillBase s₀) ∈ v.wr) (n : Nat) (t : State)
    (hi : LoopInv h v n t) :
    WP isa (Impl.Dsa.X86_64.Generation.Refill.iteration attempt qBytes) t fun t' =>
      (isa.eval .e t' = some false ∧ LoopDone h v t') ∨ (isa.eval .e t' = some true ∧ ∃ m < n, LoopInv h v m t') := by
  obtain ⟨hs, W, c, hin, hm, h16, hc, c0, c1, c2, hn, htot, hf, hrd, hwr⟩ := hi
  have hb := refillBase_bound h
  have hlen := (randTape h).size
  have hq31 : qBytes < 2 ^ 31 := by have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega
  have hpos : 0 < pBytes := by have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega
  have h15 : W 15 = BitVec.ofNat 64 (randTape h).bytes.length :=
    (hm.slots 15 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randLengthSlot
  have h13 : W 13 = (randTape h).ptr :=
    (hm.slots 13 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randSlot
  have hctl : ∀ u : State, u.wr = v.wr → ctlRegion (refillBase s₀) ∈ u.wr := fun u hu => hu ▸ hv
  obtain ⟨V, R⟩ := hm.rep
  simp only [Impl.Dsa.X86_64.Generation.Refill.iteration, VG.Impl.Bignum.X86_64.seqs]
  apply WP.seq
  have h2 : (t.mem.writeW (off (refillBase s₀) 320) (BitVec.ofNat 64 c)).readW (off (refillBase s₀) 312) 64 =
      BitVec.ofNat 64 n := by
    rw [← c2]; exact ctlWord_write_other t.mem _ (j := 2) (k := 3) (by decide) (by decide) (by decide) _
  refine WP.mono (iterStart_ok hm.layout R (hctl t hwr) hb h16 (by unfold Spec.Dsa.parameterSeeds at hn; omega) h2)
    fun t₁ ⟨rax₁, zf₁, mem₁, k₁⟩ => ?_
  have fr₁ : Frame [ctlRegion (refillBase s₀)] t.mem t₁.mem := by
    rw [mem₁]; exact ctl_write t.mem _ (k := 3) (by decide) _
  have hm₁ := GenerationMemory.ctlFrame h hin hm fr₁ (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
  have fv₁ : Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t₁.mem :=
    hf.trans (fr₁.mono fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)
  have ctl₁ : ∀ j < 3, ctlWord t₁.mem (refillBase s₀) j = ctlWord t.mem (refillBase s₀) j := fun j hj => by
    rw [mem₁]; exact ctlWord_write_other t.mem _ (k := 3) (by omega) (by decide) (by omega) _
  have c3 : ctlWord t₁.mem (refillBase s₀) 3 = BitVec.ofNat 64 c := by
    rw [mem₁]; exact ctlWord_write_self t.mem _ 3 _
  have rd₁ : t₁.rd = v.rd := k₁.2.1.trans hrd
  have wr₁ : t₁.wr = v.wr := k₁.2.2.trans hwr
  apply WP.seq
  by_cases hn0 : n = 0
  · subst hn0
    refine WP.ite true (by simp only [eval, zf₁, decide_true]) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    refine WP.mono (statusMem_ok hm₁ 2 (by decide)) fun t₂ ⟨hm₂, f₂, k₂⟩ => ?_
    refine WP.mono (statusTest_ok hm₂) fun t₃ ⟨z₃, hm₃, mem₃, k₃⟩ => Or.inl ⟨z₃.trans rfl, ?_⟩
    refine ⟨hs, _, hin, hm₃, ?_, ?_, ?_, k₃.2.1.trans (k₂.2.1.trans rd₁), k₃.2.2.trans (k₂.2.2.trans wr₁),
      Or.inl ⟨rfl, c, hc, ?_, ?_⟩⟩
    · rw [ctlWord_eq_of_mem mem₃, ctlWord_changed h f₂ (by decide), ctl₁ 0 (by decide), c0]
    · rw [ctlWord_eq_of_mem mem₃, ctlWord_changed h f₂ (by decide), ctl₁ 1 (by decide), c1]
    · rw [mem₃]; exact fv₁.trans (f₂.mono fun r hr => List.mem_cons_of_mem _ hr)
    · rw [ctlWord_eq_of_mem mem₃, ctlWord_changed h f₂ (by decide), c3]
    · rw [htot, VG.Proof.Dsa.Generation.search_zero]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  refine WP.ite false (by simp only [eval, zf₁, decide_false, Nat.add_one_ne_zero]) (fun hh => Bool.noConfusion hh)
    (fun _ => ?_)
  obtain ⟨V₁, R₁⟩ := hm₁.rep
  apply WP.seq
  refine WP.mono (roomCheck_ok hm₁.layout R₁ rax₁ h15 hc hlen (hq ▸ hq31)) fun t₂ ⟨cf₂, mem₂, k₂⟩ => ?_
  have hm₂ := hm₁.congr2 mem₂ (k₂.mono (by decide))
  have rd₂ : t₂.rd = v.rd := k₂.2.1.trans rd₁
  have wr₂ : t₂.wr = v.wr := k₂.2.2.trans wr₁
  by_cases hr : (randTape h).bytes.length - c < qBytes
  · refine WP.ite true (by simp only [eval, cf₂, hr, decide_true]) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    refine WP.mono (statusMem_ok hm₂ 0 (by decide)) fun t₃ ⟨hm₃, f₃, k₃⟩ => ?_
    refine WP.mono (statusTest_ok hm₃) fun t₄ ⟨z₄, hm₄, mem₄, k₄⟩ => Or.inl ⟨z₄.trans rfl, ?_⟩
    have cw : ∀ j < 4, ctlWord t₄.mem (refillBase s₀) j = ctlWord t₁.mem (refillBase s₀) j := fun j hj => by
      rw [ctlWord_eq_of_mem mem₄, ctlWord_changed h f₃ hj, ctlWord_eq_of_mem mem₂]
    refine ⟨hs, _, hin, hm₄, by rw [cw 0 (by decide), ctl₁ 0 (by decide), c0],
      by rw [cw 1 (by decide), ctl₁ 1 (by decide), c1], ?_, k₄.2.1.trans (k₃.2.1.trans rd₂),
      k₄.2.2.trans (k₃.2.2.trans wr₂), Or.inr (Or.inl ⟨rfl, c, n' + 1, hc, by rw [cw 3 (by decide), c3],
        by rw [cw 2 (by decide), ctl₁ 2 (by decide), c2], hn, ?_⟩)⟩
    · rw [mem₄]; exact (mem₂ ▸ fv₁).trans (f₃.mono fun r hr => List.mem_cons_of_mem _ hr)
    · rw [htot]; exact VG.Proof.Dsa.Generation.search_short (hq ▸ hr)
  refine WP.ite false (by simp only [eval, cf₂, hr, decide_false]) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
  have room : c + qBytes ≤ (randTape h).bytes.length := by omega
  obtain ⟨V₂, R₂⟩ := hm₂.rep
  apply WP.seq
  refine WP.mono (seedStart_ok hm₂.layout R₂ ((k₂.gpr (by decide)).trans rax₁) h13 hq31)
    fun t₃ ⟨L₃, R₃, f₃, k₃⟩ => ?_
  have hm₃ : GenerationMemory ((refillContext h).withHs hs)
      (upd (upd W 1 (off (randTape h).ptr c)) 16 (BitVec.ofNat 64 (c + qBytes))) t₃ := by
    refine hm₂.frame L₃ ⟨V₂, R₃⟩ ?_ (GenerationContext.frame_single f₃) k₃.2.1 k₃.2.2
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
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
  have hm₅ : GenerationMemory ((refillContext h).withHs hs') W' t₅ := withHs_withHs (refillContext h) hs hs' ▸ hm₅'
  have hin' : HsIn h hs' := sub'
  have cw₅ : ∀ j < 4, ctlWord t₅.mem (refillBase s₀) j = ctlWord t₁.mem (refillBase s₀) j := fun j hj => by
    rw [ctlWord_changed h f₅ hj, cw₃ j hj]
  have fv₅ : Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem t₅.mem :=
    fv₃.trans (f₅.mono fun r hr => List.mem_cons_of_mem _ hr)
  have rd₅' : t₅.rd = v.rd := rd₅.trans (k₃.2.1.trans rd₂)
  have wr₅' : t₅.wr = v.wr := wr₅.trans (k₃.2.2.trans wr₂)
  have hseed : seed.bytes = ((randTape h).bytes.drop c).take (Spec.Dsa.generationQLen pBytes) := by
    rw [← hq]; rfl
  change VG.Proof.Dsa.X86_64.Generation.SeedOutcome _ (VG.Proof.Dsa.Generation.refillAttempt pBytes
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
      k₇.2.1.trans (k₆.2.1.trans rd₅'), k₇.2.2.trans (k₆.2.2.trans wr₅'),
      Or.inr (Or.inl ⟨h19, c, n' + 1, hc, by rw [ctlWord_eq_of_mem mem₇, cw₆ 3 (by decide), c3],
        by rw [ctlWord_eq_of_mem mem₇, cw₆ 2 (by decide), ctl₁ 2 (by decide), c2], hn, ?_⟩)⟩
    rw [htot]; exact VG.Proof.Dsa.Generation.search_attemptNone hpos room hres
  · refine WP.ite true (z₆.trans (by rw [h19]; rfl)) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    have c2₆ : t₆.mem.readW (off (refillBase s₀) 312) 64 = BitVec.ofNat 64 (n' + 1) := by
      rw [← c2, ← ctl₁ 2 (by decide), ← cw₆ 2 (by decide)]; rfl
    refine WP.mono (rejected_ok ((k₆.gpr (by decide)).trans hm₅.layout.rsp) (hctl _ (k₆.2.2.trans wr₅')) hb
      (by unfold Spec.Dsa.parameterSeeds at hn; omega) c2₆) fun t₇ ⟨mem₇, k₇⟩ => ?_
    have fr₇ : Frame [ctlRegion (refillBase s₀)] t₆.mem t₇.mem := by
      rw [mem₇]; exact ctl_write t₆.mem _ (k := 2) (by decide) _
    have hm₇ := GenerationMemory.ctlFrame h hin' hm₆ fr₇ (k₇.gpr (by decide)) k₇.2.1 k₇.2.2
    have cw₇ : ∀ j < 2, ctlWord t₇.mem (refillBase s₀) j = ctlWord t₆.mem (refillBase s₀) j := fun j hj => by
      rw [mem₇]; exact ctlWord_write_other t₆.mem _ (k := 2) (by omega) (by decide) (by omega) _
    refine WP.mono (statusTest_ok hm₇) fun t₈ ⟨z₈, hm₈, mem₈, k₈⟩ => Or.inr ⟨z₈.trans (by rw [h19]; rfl), n', by omega, ?_⟩
    refine ⟨hs', W', u, hin', hm₈, h16', hu,
      by rw [ctlWord_eq_of_mem mem₈, cw₇ 0 (by decide), cw₆ 0 (by decide), ctl₁ 0 (by decide), c0],
      by rw [ctlWord_eq_of_mem mem₈, cw₇ 1 (by decide), cw₆ 1 (by decide), ctl₁ 1 (by decide), c1],
      by rw [ctlWord_eq_of_mem mem₈, mem₇]; exact ctlWord_write_self t₆.mem _ 2 _, by omega, ?_, ?_,
      k₈.2.1.trans (k₇.2.1.trans (k₆.2.1.trans rd₅')), k₈.2.2.trans (k₇.2.2.trans (k₆.2.2.trans wr₅'))⟩
    · rw [htot]; exact VG.Proof.Dsa.Generation.search_rejected hpos room hu hres
    · rw [mem₈]; exact (mem₆ ▸ fv₅).trans (fr₇.mono fun r hr => by
        rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)
  · refine WP.ite false (z₆.trans (by rw [h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => WP.block_nil ?_)
    refine WP.mono (statusTest_ok hm₆) fun t₇ ⟨z₇, hm₇, mem₇, k₇⟩ => Or.inl ⟨z₇.trans (by rw [h19]; rfl), ?_⟩
    refine ⟨hs', W', hin', hm₇, by rw [ctlWord_eq_of_mem mem₇, cw₆ 0 (by decide), ctl₁ 0 (by decide), c0],
      by rw [ctlWord_eq_of_mem mem₇, cw₆ 1 (by decide), ctl₁ 1 (by decide), c1], by rw [mem₇, mem₆]; exact fv₅,
      k₇.2.1.trans (k₆.2.1.trans rd₅'), k₇.2.2.trans (k₆.2.2.trans wr₅'),
      Or.inr (Or.inr ⟨h19, a, u, hu, h16', ?_, by rw [mem₇, mem₆]; exact bytes⟩)⟩
    rw [htot]; exact VG.Proof.Dsa.Generation.search_accepted hpos room hu hres

theorem controller_ok {qBytes : Nat} (hq : qBytes = Spec.Dsa.generationQLen pBytes) {attempt : Prog isa}
    (hA : AttemptOk h attempt) {v : State} (hv : ctlRegion (refillBase s₀) ∈ v.wr) (n : Nat) (t : State)
    (hi : LoopInv h v n t) :
    WP isa (.loop (Impl.Dsa.X86_64.Generation.Refill.iteration attempt qBytes) .e) t (LoopDone h v) :=
  WP.loop (M := isa) (Q := LoopDone h v) (LoopInv h v) (fun n t hi => step_ok h hq hA hv n t hi) n t hi

theorem withHs_self (p : GenerationContext) : p.withHs p.hs = p := by
  cases p
  simp only [GenerationContext.withHs, GenerationContext.mk.injEq, heq_eq_eq, true_and]
  funext k
  by_cases h11 : k = 11
  · subst h11; simp [*]
  · by_cases h12 : k = 12
    · subst h12; simp [*]
    · simp [h11, h12]

/-- The controller's invariant on entry. -/
theorem loop_initial {W : Nat → BitVec 64} {v : State} (hm : GenerationMemory (refillContext h) W v)
    (h16 : W 16 = 0) (c0 : ctlWord v.mem (refillBase s₀) 0 = s₀.gpr .rdx)
    (c1 : ctlWord v.mem (refillBase s₀) 1 = stackArg s₀ 1)
    (c2 : ctlWord v.mem (refillBase s₀) 2 = s₀.mem.readW (stackArg s₀ 1) 64) :
    LoopInv h v (s₀.mem.readW (stackArg s₀ 1) 64).toNat v := by
  refine ⟨(refillContext h).hs, W, 0, ?_, (withHs_self _).symm ▸ hm, h16, Nat.zero_le _, c0, c1,
    by rw [c2, BitVec.ofNat_toNat, BitVec.setWidth_eq], h.seeds, ?_, Frame.refl _ _, rfl, rfl⟩
  · intro a ha
    simp [Region.Contains, refillContext, GenerationTape.slice] at ha
  · simp [total, Spec.Entropy.Result.consume]

end

end VG.Proof.Dsa.X86_64.Generation.Refill
