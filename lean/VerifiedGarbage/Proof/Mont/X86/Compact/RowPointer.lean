module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingSetup
import VerifiedGarbage.Proof.Mont.X86.Compact.Setup
import VerifiedGarbage.Proof.Mont.X86.Compact.PairFrame
import VerifiedGarbage.Proof.Mont.X86.Compact.CarryPointer

/-! # Each complete product row preserves its public window position -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem mulRow_pointer {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (modulus : Bool) (w : Nat) (low : g.S ≤ w)
    (high : w + 4 * g.N + 8 ≤ g.S + 8 * g.N + 28)
    (edi : PtrAt s g.W .edi g.S) (ebp : PtrAt s g.W .ebp w) :
    WP isa (Compact.mulRow (rowSource modulus)) s fun t =>
      PtrAt t g.W .edi g.S ∧ PtrAt t g.W .ebp w ∧
      Outs g.W g.writes s.mem t.mem ∧ Keeps clob6 s t := by
  unfold Compact.mulRow
  refine WP.seq (WP.mono (setup_ok v C (rowSource modulus) (sourceNumber g modulus) w edi ebp
    (fun _ M hw ha => sourcePointer_ok v modulus C M hw ha)) fun a ⟨P, M, K⟩ => ?_)
  have Oa : Outs g.W g.writes s.mem a.mem := by rw [M]; exact Outs.refl _ _ _
  have Ca := C.keepK v K (by decide) Oa
  have even : g.N % 2 = 0 := by have := C.metadata.width; omega
  have fit := v.lay.scr
  have mult : Rt.multOff = 20 := rfl
  refine WP.seq (WP.mono (pairLoop_frame Ca.ws v.positive even P.edi P.ecx P.ebp P.esi
    (by omega) (source_fit v modulus) (by omega)) fun b ⟨Ob, Pb, _, _, Kb⟩ => ?_)
  have writes : Outs g.W g.writes a.mem b.mem :=
    Outs.widen (Outs.of_outside Ob (List.mem_singleton_self _)) fun x hx r hr => by
      have outside := hx _ (List.mem_cons_self ..)
      simp only [List.mem_singleton] at hr
      subst hr
      dsimp only at *
      omega
  have Cb := Ca.keepK v Kb (by decide) writes
  refine WP.mono (carryUp_pointer v Cb w low high Pb) ?_
  rintro t ⟨Pt, Ot, Kt⟩
  have keep : Keeps clob6 s t := ((K.mono (by decide)).trans Kb).trans (Kt.mono (by decide))
  refine ⟨?_, Pt, (Oa.trans writes).trans Ot, keep⟩
  rw [PtrAt, keep.1 .edi (by decide)]; exact edi

end VG.Proof.Mont.X86.Compact
