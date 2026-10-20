module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TapeLoop
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeControl
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeState
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeTake

/-! # Complete native tape iteration, including exhaustion and retry -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

/-- Payloads can depend on memory and preserved registers, but not the
comparison's volatile registers or flags. -/
def TapeStable (P : State → Prop) : Prop :=
  ∀ {s t}, P s → t.mem = s.mem → Keeps [.eax, .ecx] s t → P t

def TapeView (slots : TapeSlots) (F : Addr) (used total : Nat) (s : State) : Prop :=
  ∃ W, SearchFrame s F ∧ FrameWords s.mem F W ∧
    W slots.used = BitVec.ofNat 32 used ∧ W slots.total = BitVec.ofNat 32 total

theorem tapeIteration_ok {slots : TapeSlots} {width total used : Nat} {F : Addr}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (hb : slots.base < 37) (ht : slots.total < 37) (hu : slots.used < 37) (hp : slots.pointer < 37)
    (hw : width < 2 ^ 32) (hmax : total < 2 ^ 32)
    (stable : ∀ n, TapeStable (I n)) (finish : TapeStable Q)
    (view : ∀ n s, I n s → TapeView slots F n total s)
    (done : ∀ s t W, I used s → total - used < width →
      SearchFrame s F → FrameWords s.mem F W →
      SearchFrame t F → FrameWords t.mem F (frameUpdate W 19 3) →
      Outside F 76 4 s.mem t.mem → Keeps [.eax] s t → Q t)
    (step : ∀ s t W, I used s → width ≤ total - used →
      SearchFrame s F → FrameWords s.mem F W → W slots.used = BitVec.ofNat 32 used →
      SearchFrame t F → FrameWords t.mem F
        (frameUpdate (frameUpdate W slots.pointer (W slots.base + BitVec.ofNat 32 used)) slots.used (BitVec.ofNat 32 (used + width))) →
      Outside F 0 frameBytes s.mem t.mem → Keeps [.eax, .ecx] s t →
      WP isa body t fun u => ∃ W', SearchFrame u F ∧ FrameWords u.mem F W' ∧
        (if W' 19 = 3 then I (used + width) u else Q u))
    {s : State} (hle : used ≤ total) (hi : I used s) :
    WP isa (tapeIteration slots width body) s fun t =>
      (eval .e t = some false ∧ Q t) ∨
      (eval .e t = some true ∧ I (used + width) t ∧ used + width ≤ total) := by
  obtain ⟨W, L, R, hused, htotal⟩ := view used s hi
  unfold tapeIteration
  refine WP.seq (WP.mono (chunkCheck_ok L R slots hu ht hle hmax hw hused htotal)
    fun u ⟨hcf, hm, ku⟩ => ?_)
  have Ru : FrameWords u.mem F W := hm ▸ R
  have Lu := L.keeps ku (by decide)
  have hiu := stable used hi hm ku
  by_cases exhausted : total - used < width
  · refine WP.ite true (by simp [eval, hcf, exhausted]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (tapeExhausted_ok Lu Ru) fun t ⟨hz, Lt, Rt, ft, kt⟩ => ?_
    exact Or.inl ⟨by simpa [eval] using hz, done u t W hiu exhausted Lu Ru Lt Rt ft kt⟩
  · have available : width ≤ total - used := by omega
    refine WP.ite false (by simp [eval, hcf, exhausted]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono (tapeTake_ok Lu Ru slots width hb hu hp hused)
      fun v ⟨Lv, Rv, fv, kv⟩ => ?_)
    refine WP.seq (WP.mono (step u v W hiu available Lu Ru hused Lv Rv fv kv)
      fun w ⟨Ww, Lw, Rw, outcome⟩ => ?_)
    refine WP.mono (tapeStatus_ok Lw Rw) fun t ⟨hz, hmt, kt⟩ => ?_
    by_cases retry : Ww 19 = 3
    · have hit : I (used + width) t := stable _ (by simpa only [retry, ite_true, ite_false] using outcome) hmt (kt.mono (by decide))
      exact Or.inr ⟨by simp [eval, hz, retry], hit, by omega⟩
    · have hqt : Q t := finish (by simpa only [retry, ite_true, ite_false] using outcome) hmt (kt.mono (by decide))
      exact Or.inl ⟨by simp only [eval, hz, beq_eq_false_iff_ne.mpr retry], hqt⟩

end VG.Proof.Dsa.X86.Generation
