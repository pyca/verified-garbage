module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputContext
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePort
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Export all seven key components without losing earlier outputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure ExportProgress (g : OutputGeometry) (m : Mem) (accept : Bool) (i : Nat) (s : State) : Prop where
  input : OutputInput g s
  zero : num s.mem g.base g.n aZero = 0
  mask : slot s.mem g.base kOk = if accept then 1 else 0
  header : ∀ d, d + 4 ≤ hdr → slot s.mem g.base d = slot m g.base d
  pending : ∀ j, i ≤ j → j < 7 → num s.mem g.base g.n (outputIndex j) = num m g.base g.n (outputIndex j)
  done : ∀ j, j < i → j < 7 → Spec.Rsa.bytesAt s.mem (g.region j).base (g.region j).len = portResult g m accept j

theorem ExportProgress.step {g : OutputGeometry} {m : Mem} {accept : Bool} {i : Nat} {s : State}
    (P : ExportProgress g m accept i s) (hi : i < 7) :
    WP isa (writePort g.n i) s fun t =>
      ExportProgress g m accept (i + 1) t ∧ Frame g.writes s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  refine WP.mono (writePort_ok P.input hi P.zero accept P.mask)
    fun t ⟨ht, value, F, header, other, K⟩ => ?_
  refine ⟨⟨ht, (other aZero (by decide) (outputIndex_zero hi)).trans P.zero,
    (header kOk (by decide)).trans P.mask, ?_, ?_, ?_⟩, portFrame_global P.input hi F, K⟩
  · intro d hd
    exact (header d hd).trans (P.header d hd)
  · intro j lower upper
    exact (other (outputIndex j) (outputIndex_bound upper)
      (outputIndex_injective upper hi (by omega))).trans (P.pending j (by omega) upper)
  · intro j lower upper
    by_cases last : j = i
    · subst j
      unfold portResult at value ⊢
      rw [P.pending i (Nat.le_refl _) hi] at value
      exact value
    · exact (portFrame_other P.input hi upper (by omega) F).trans (P.done j (by omega) upper)

theorem writePorts_ok {g : OutputGeometry} {m : Mem} {accept : Bool} {i count : Nat} {s : State}
    (P : ExportProgress g m accept i s) (bound : i + count ≤ 7) :
    WP isa (writePorts g.n i count) s fun t =>
      ExportProgress g m accept (i + count) t ∧ Frame g.writes s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  induction count generalizing i s with
  | zero => exact WP.block_nil ⟨P, Frame.refl _ _, Keeps.refl _ _⟩
  | succ count ih =>
    unfold writePorts
    refine WP.seq (WP.mono (P.step (by omega)) fun u ⟨Pu, Fu, Ku⟩ => ?_)
    refine WP.mono (ih Pu (by omega)) fun t ⟨Pt, Ft, Kt⟩ => ?_
    have index : i + 1 + count = i + (count + 1) := by omega
    rw [index] at Pt
    exact ⟨Pt, Fu.trans Ft, Ku.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Key
