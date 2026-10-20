module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Sized
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Sized
import VerifiedGarbage.Proof.Bignum.X86.CrtValue
meta import VerifiedGarbage.Proof.Bignum.X86.CrtValue
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeBase
meta import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeBase

/-! # The trace of private CRT at a run-time width, from the components to the result

The components' import, the acceptance, the recombination and the output
are checked by the taint analysis, the powers and the coefficient related
by `power_relCT` and `coefficient_relCT` (`sized_relCT`), on states whose
permissions are narrowed to the output and the working space; the runs
from the states themselves leak the same traces (`sizedNarrow_relCT`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_narrow)
open VG.Proof.Bignum.X86.Crt (componentValue)

/-- The taint checks of `sized`. -/
structure SizedChecks : Prop where
  front : ACheck (Prog.chain [importComponents, validate] (.block []))
  p₁ : PowChecks 10 12 16 7
  p₂ : PowChecks 11 13 17 9
  co : CoChecks
  back : ACheck (.seq recombine exportResult)

theorem sizedChecks : SizedChecks := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    (try dsimp only [MulCheck, ACheck]) <;> taint_decide

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}

theorem front_run (R : Run base bytes len args sp s) :
    WP isa (Prog.chain [importComponents, validate] (.block [])) s (Run base bytes len args sp) :=
  front_ok R.1 fun _ hu _ _ _ K => WP.block_nil ⟨hu, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩

theorem sized_relCT (sp : BitVec 32) :
    RelCT isa (Both (Run base bytes len args sp)) CrtRt.sized fun _ _ => True := by
  have hc := sizedChecks
  show RelCT isa _ (Prog.chain [importComponents, validate] (.seq (power 10 12 16 7) (.seq (power 11 13 17 9)
    (.seq coefficient (.seq recombine exportResult))))) _
  refine VG.RelCT.chain (VG.RelCT.seq (taint_both (fun _ _ R₁ R₂ => R₁.agree R₂) _ hc.front
    fun _ R => front_run R) ?_)
  refine VG.RelCT.seq (power_relCT hc.p₁ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) ?_
  refine VG.RelCT.seq (power_relCT hc.p₂ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) ?_
  refine VG.RelCT.seq (coefficient_relCT hc.co) ?_
  exact RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) hc.back

/-- The permissions of `sized`'s narrowed runs: everything readable, the output and the working space
writable. -/
abbrev narrowW (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) : List Region :=
  [⟨byteAddr (args 0), len⟩, ⟨base, bytes⟩]

/-- What the runs of `sized` from the states themselves need: the inputs, a valid modulus, `esp`, and
the arguments apart from the output and the working space. -/
def SizedAt (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  In base bytes len args s ∧ s.gpr .esp = sp ∧
    Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ ⟨byteAddr (args 0), len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ ⟨base, bytes⟩

theorem narrow_in (S : SizedAt base bytes len args sp s) :
    In base bytes len args (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) := by
  obtain ⟨⟨h, need, hbase, hbytes⟩, _, _, _, _⟩ := S
  refine ⟨⟨⟨h.scratch.edi, by simp, h.scratch.nowrap, h.scratch.stk⟩, h.lower, h.upper, h.space,
    fun i hi => ⟨⟨?_, (h.stack i hi).stack.apart⟩, (h.stack i hi).value⟩, h.outLen, h.nLen, h.inLen, h.pShort,
    h.qShort, h.dpLen, h.dqLen, h.qiLen, h.outFit, ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
    h.outApart, h.positive, h.bounded, h.fits, fun i hi => ?_, h.apart, h.room, h.top⟩, need, hbase, hbytes⟩
  · obtain ⟨r, hr, hc⟩ := (h.stack i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.readable i hi
    exact ⟨r, List.mem_append_left _ hr, hc⟩

theorem narrow_run (S : SizedAt base bytes len args sp s) :
    Run base bytes len args sp (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) := by
  refine ⟨narrow_in S, ⟨S.1.crt.top, fun r hr => ?_⟩, S.2.1⟩
  simp only [State.withRegions, narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact S.2.2.2.1
  · exact S.2.2.2.2

theorem sizedNarrow_relCT (sp : BitVec 32) :
    RelCT isa (Both (SizedAt base bytes len args sp)) CrtRt.sized fun _ _ => True := by
  refine relCT_narrow (Pn := Both (Run base bytes len args sp)) (fun s => s.rd ++ s.wr)
    (fun _ => narrowW base bytes len args) (fun s₁ s₂ ⟨S₁, S₂⟩ => ?_) (sized_relCT sp)
  have cov : ∀ {s : State}, SizedAt base bytes len args sp s → Covers (narrowW base bytes len args) s.wr := by
    intro s S
    rintro a n ⟨r, hr, hc⟩
    simp only [narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one S.1.crt.outWrite a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, S.1.crt.scratch.wr, hc⟩
  have wp : ∀ {s : State}, SizedAt base bytes len args sp s →
      ∃ F, WP isa CrtRt.sized (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) F :=
    fun S => ⟨_, sized_ok (narrow_in S) S.2.2.1⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂,
    narrow_run S₁, narrow_run S₂⟩

end

end VG.Proof.Bignum.X86.CrtRt
