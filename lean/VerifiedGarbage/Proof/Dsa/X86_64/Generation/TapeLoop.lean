module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeIteration
import VerifiedGarbage.Proof.Framework.Omega

/-! # Termination of native seed and generator tape searches -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

/-- The body provides algorithm-specific progress; the tape controller
owns complete-chunk selection, cursor advancement, and loop termination. -/
structure TapeDriver (slots : TapeSlots) (F S : Addr) (width total : Nat)
    (body : Prog isa) (I : Nat → State → Prop) (Q : State → Prop) : Prop where
  baseBound : slots.base < 37
  totalBound : slots.total < 37
  usedBound : slots.used < 37
  pointerBound : slots.pointer < 37
  usedNotScratch : slots.used ≠ 14
  pointerNotScratch : slots.pointer ≠ 14
  widthBound : width < 2 ^ 31
  widthPositive : 0 < width
  totalFits : total < 2 ^ 64
  stable : ∀ n, TapeStable (I n)
  finish : TapeStable Q
  view : ∀ n s, I n s → TapeView slots F S n total s
  done : ∀ used s t V W, I used s → total - used < width →
    Lay s F S → Rep s.mem F S V W →
    Lay t F S → Rep t.mem F S V (upd W 19 3) →
    Outside F 152 8 s.mem t.mem → Keep [.rax] s t → Q t
  step : ∀ used s t V W, I used s → width ≤ total - used →
    Lay s F S → Rep s.mem F S V W → W slots.used = BitVec.ofNat 64 used →
    Lay t F S → Rep t.mem F S V
      (upd (upd W slots.pointer (off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) →
    Frame [⟨F, frameBytes⟩] s.mem t.mem → Keep [.rax, .rcx] s t →
    WP isa body t fun u => ∃ V' W', Lay u F S ∧ Rep u.mem F S V' W' ∧
      (if W' 19 = 3 then I (used + width) u else Q u)

theorem TapeDriver.loop_ok {slots : TapeSlots} {F S : Addr} {width total : Nat}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (d : TapeDriver slots F S width total body I Q)
    {s : State} {used : Nat} (hle : used ≤ total) (hi : I used s) :
    WP isa (.loop (tapeIteration slots width body) .e) s Q := by
  exact WP.loop
    (fun n t => ∃ used, n = total - used + 1 ∧ used ≤ total ∧ I used t)
    (fun n t ⟨u, hn, hu, hit⟩ =>
      WP.mono (tapeIteration_ok d.baseBound d.totalBound d.usedBound d.pointerBound
        d.usedNotScratch d.pointerNotScratch d.widthBound d.totalFits
        d.stable d.finish d.view (d.done u) (d.step u) hu hit)
        fun t' ht => ht.imp (fun h => h) fun ⟨hz, hi', hbound⟩ =>
          ⟨hz, total - (u + width) + 1, by omega_using [d.widthPositive, hn, hu, hbound],
            u + width, rfl, hbound, hi'⟩)
    (total - used + 1) s ⟨used, rfl, hle, hi⟩

/-- Resetting the cursor makes each generator search reuse the original h
tape, and each top-level call begin at the first seed. -/
theorem TapeDriver.run_ok {slots : TapeSlots} {F S : Addr} {width total : Nat}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (d : TapeDriver slots F S width total body I Q)
    {s : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (start : ∀ t, Lay t F S → Rep t.mem F S V (upd W slots.used 0) →
      Outside F (8 * slots.used) 8 s.mem t.mem → Keep [.rax] s t → I 0 t) :
    WP isa (tapeLoop slots width body) s Q := by
  unfold tapeLoop
  refine WP.seq (WP.mono (tapeReset_ok L R slots d.usedBound d.usedNotScratch)
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_)
  exact d.loop_ok (Nat.zero_le _) (start t Lt Rt ft kt)

end VG.Proof.Dsa.X86_64.Generation
