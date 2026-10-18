module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ChunkCheck
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ChunkTake
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState
import VerifiedGarbage.Proof.Framework.Omega

/-! # Complete native tape iteration, including exhaustion and retry -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

/-- Payloads can depend on memory and preserved registers, but not the
comparison's volatile registers or flags. -/
def TapeStable (P : State → Prop) : Prop :=
  ∀ {s t}, P s → t.mem = s.mem → Keep [.rax, .rcx] s t → P t

def TapeView (slots : TapeSlots) (F S : Addr) (used total : Nat) (s : State) : Prop :=
  ∃ V W, Lay s F S ∧ Rep s.mem F S V W ∧
    W slots.used = BitVec.ofNat 64 used ∧ W slots.total = BitVec.ofNat 64 total

theorem tapeIteration_ok {slots : TapeSlots} {width total used : Nat} {F S : Addr}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (hb : slots.base < 37) (ht : slots.total < 37) (hu : slots.used < 37) (hp : slots.pointer < 37)
    (hu14 : slots.used ≠ 14) (hp14 : slots.pointer ≠ 14)
    (hw : width < 2 ^ 31) (hmax : total < 2 ^ 64)
    (stable : ∀ n, TapeStable (I n)) (finish : TapeStable Q)
    (view : ∀ n s, I n s → TapeView slots F S n total s)
    (done : ∀ s t V W, I used s → total - used < width →
      Lay s F S → Rep s.mem F S V W →
      Lay t F S → Rep t.mem F S V (upd W 19 3) →
      Outside F 152 8 s.mem t.mem → Keep [.rax] s t → Q t)
    (step : ∀ s t V W, I used s → width ≤ total - used →
      Lay s F S → Rep s.mem F S V W → W slots.used = BitVec.ofNat 64 used →
      Lay t F S → Rep t.mem F S V
        (upd (upd W slots.pointer (off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) →
      Frame [⟨F, frameBytes⟩] s.mem t.mem → Keep [.rax, .rcx] s t →
      WP isa body t fun u => ∃ V' W', Lay u F S ∧ Rep u.mem F S V' W' ∧
        (if W' 19 = 3 then I (used + width) u else Q u))
    {s : State} (hle : used ≤ total) (hi : I used s) :
    WP isa (tapeIteration slots width body) s fun t =>
      (eval .e t = some false ∧ Q t) ∨
      (eval .e t = some true ∧ I (used + width) t ∧ used + width ≤ total) := by
  obtain ⟨V, W, L, R, hused, htotal⟩ := view used s hi
  unfold tapeIteration
  refine WP.seq (WP.mono (chunkCheck_ok L R slots ht hu hw hused htotal hle hmax)
    fun u ⟨hcf, hm, ku⟩ => ?_)
  have Ru : Rep u.mem F S V W := hm ▸ R
  have Lu := lay_of_rep L R Ru rfl (ku.gpr (by decide)) ku.2.2
  have hiu := stable used hi hm ku
  by_cases exhausted : total - used < width
  · refine WP.ite true (by simp [eval, hcf, exhausted]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (tapeExhausted_ok Lu Ru) fun t ⟨hz, Lt, Rt, ft, kt⟩ => ?_
    exact Or.inl ⟨by simpa [eval] using hz, done u t V W hiu exhausted Lu Ru Lt Rt ft kt⟩
  · have available : width ≤ total - used := by omega
    refine WP.ite false (by simp [eval, hcf, exhausted]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono (chunkTake_ok Lu Ru slots hb hu hp hu14 hp14 hw hused)
      fun v ⟨Lv, Rv, fv, kv⟩ => ?_)
    refine WP.seq (WP.mono (step u v V W hiu available Lu Ru hused Lv Rv fv kv)
      fun w ⟨Vw, Ww, Lw, Rw, outcome⟩ => ?_)
    refine WP.mono (tapeStatus_ok Lw Rw) fun t ⟨hz, hmt, kt⟩ => ?_
    by_cases retry : Ww 19 = 3
    · have hit : I (used + width) t := stable _ (by simpa only [retry, ite_true, ite_false] using outcome) hmt (kt.mono (by decide))
      exact Or.inr ⟨by simp [eval, hz, retry], hit, by omega⟩
    · have hqt : Q t := finish (by simpa only [retry, ite_true, ite_false] using outcome) hmt (kt.mono (by decide))
      exact Or.inl ⟨by simp only [eval, hz, beq_eq_false_iff_ne.mpr retry], hqt⟩

end VG.Proof.Dsa.X86_64.Generation
