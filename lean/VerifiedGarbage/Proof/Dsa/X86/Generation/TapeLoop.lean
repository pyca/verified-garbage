module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeIteration
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeControl

/-! # Termination of the seed and generator searches on bounded input tapes -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

/-- The body provides algorithm-specific progress; the tape controller
owns complete-chunk selection, cursor advancement, and loop termination. -/
structure TapeDriver (slots : TapeSlots) (F : Addr) (width total : Nat)
    (body : Prog isa) (I : Nat → State → Prop) (Q : State → Prop) : Prop where
  baseBound : slots.base < 37
  totalBound : slots.total < 37
  usedBound : slots.used < 37
  pointerBound : slots.pointer < 37
  widthBound : width < 2 ^ 32
  widthPositive : 0 < width
  totalFits : total < 2 ^ 32
  stable : ∀ n, TapeStable (I n)
  finish : TapeStable Q
  view : ∀ n s, I n s → TapeView slots F n total s
  done : ∀ used s t W, I used s → total - used < width →
    SearchFrame s F → FrameWords s.mem F W →
    SearchFrame t F → FrameWords t.mem F (frameUpdate W 19 3) →
    Outside F 76 4 s.mem t.mem → Keeps [.eax] s t → Q t
  step : ∀ used s t W, I used s → width ≤ total - used →
    SearchFrame s F → FrameWords s.mem F W → W slots.used = BitVec.ofNat 32 used →
    SearchFrame t F → FrameWords t.mem F
      (frameUpdate (frameUpdate W slots.pointer (W slots.base + BitVec.ofNat 32 used)) slots.used (BitVec.ofNat 32 (used + width))) →
    Outside F 0 frameBytes s.mem t.mem → Keeps [.eax, .ecx] s t →
    WP isa body t fun u => ∃ W', SearchFrame u F ∧ FrameWords u.mem F W' ∧
      (if W' 19 = 3 then I (used + width) u else Q u)

theorem TapeDriver.loop_ok {slots : TapeSlots} {F : Addr} {width total : Nat}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (d : TapeDriver slots F width total body I Q)
    {s : State} {used : Nat} (hle : used ≤ total) (hi : I used s) :
    WP isa (.loop (tapeIteration slots width body) .e) s Q := by
  exact WP.loop
    (fun n t => ∃ used, n = total - used + 1 ∧ used ≤ total ∧ I used t)
    (fun n t ⟨u, hn, hu, hit⟩ =>
      WP.mono (tapeIteration_ok d.baseBound d.totalBound d.usedBound d.pointerBound
        d.widthBound d.totalFits
        d.stable d.finish d.view (d.done u) (d.step u) hu hit)
        fun t' ht => ht.imp (fun h => h) fun ⟨hz, hi', hbound⟩ =>
          ⟨hz, total - (u + width) + 1, by omega_using [d.widthPositive, hn, hu, hbound],
            u + width, rfl, hbound, hi'⟩)
    (total - used + 1) s ⟨used, rfl, hle, hi⟩

/-- Resetting the cursor makes each generator search reuse the original h
tape, and each top-level call begin at the first seed. -/
theorem TapeDriver.run_ok {slots : TapeSlots} {F : Addr} {width total : Nat}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (d : TapeDriver slots F width total body I Q)
    {s : State} {W : Nat → BitVec 32}
    (L : SearchFrame s F) (R : FrameWords s.mem F W)
    (start : ∀ t, SearchFrame t F → FrameWords t.mem F (frameUpdate W slots.used 0) →
      Outside F (4 * slots.used) 4 s.mem t.mem → Keeps [.eax] s t → I 0 t) :
    WP isa (tapeLoop slots width body) s Q := by
  unfold tapeLoop
  refine WP.seq (WP.mono (tapeReset_ok L R slots d.usedBound)
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_)
  exact d.loop_ok (Nat.zero_le _) (start t Lt Rt ft kt)

end VG.Proof.Dsa.X86.Generation
