module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateFrameCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateFrame
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateCall
import Mathlib.Tactic.Attr.Core

/-! # Domain-validation control flow depends only on the packed public parameters -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

def ValidateAt (P : SearchContextPlan) (bytes : List Byte) (s : State) : Prop :=
  SearchContextAt P s ∧ Spec.Rsa.bytesAt s.mem (off P.geometry.base packed) (2 * P.geometry.pLen + P.geometry.qLen) = bytes

theorem validateArgs_ct (P : SearchContextPlan) (bytes : List Byte) :
    RelCT isa (Two fun (_ : Unit) => ValidateAt P bytes) (.block (validateArgs P.geometry.pLen P.geometry.qLen))
      (Two fun (_ : Unit) => ValidateFrameAt P bytes) := by
  refine two_piece [.esp] ?_ (hc := .block []) ?_ ?_
  · rintro _ s t ⟨⟨Ws, Rs⟩, _⟩ ⟨⟨Wt, Rt⟩, _⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (Rs.arena.frame.esp_toNat.trans Rt.arena.frame.esp_toNat.symm)
  · exact (congrArg Option.isSome (check_of_erase_eq (.block (validateArgs P.geometry.pLen P.geometry.qLen))
      (.block (validateArgs 1 1)) (τr [.esp]) (.block []) rfl rfl rfl)).trans (by rfl)
  · rintro _ s ⟨⟨W, R⟩, value⟩
    have parent : s.mem.readW (off P.geometry.frameBase 20) 32 = P.geometry.parent :=
      (R.representation 5 (by decide)).trans ((R.fixed 5 (by decide) (by decide)).trans P.parent)
    refine WP.mono (validateArgs_ok R.arena parent) fun t ⟨regs, mem, K⟩ => ?_
    exact ⟨⟨W, R.congr mem K (by decide)⟩, regs, by rw [mem]; exact value⟩

theorem validate_ct (F : KeyRandom.CheckCall.CheckFn) (P : SearchContextPlan) (bytes : List Byte) :
    RelCT isa (Two fun (_ : Unit) => ValidateAt P bytes)
      (validate F.name F.code P.geometry.pLen P.geometry.qLen) (fun _ _ => True) := by
  refine RelCT.seq (validateArgs_ct P bytes) (RelCT.seq (two_post
    (Ψ := fun (_ : Unit) s => SearchFrame s P.geometry.frameBase ∧
      s.gpr .eax = if Spec.Dsa.checkParametersBytes P.geometry.pLen P.geometry.qLen bytes then 1 else 0)
    (validateFrame_ct F P bytes) ?_) ?_)
  · rintro _ s ⟨⟨W, R⟩, regs, value⟩
    refine WP.mono (validateFrame_ok F R regs) fun t ⟨Rt, ax, _, _⟩ => ?_
    exact ⟨Rt.arena.frame, by simpa only [validateResult, value] using ax⟩
  · refine two_taint [.eax, .esp] ?_ (by taint_decide)
    intro _ s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.trans ht.2.symm
    · exact BitVec.eq_of_toNat_eq (hs.1.esp_toNat.trans ht.1.esp_toNat.symm)
end VG.Proof.Dsa.X86.Generation
