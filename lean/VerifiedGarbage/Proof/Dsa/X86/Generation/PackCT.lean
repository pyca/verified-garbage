module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Pack
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PackArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.PackPart

/-! # Packing a public domain uses fixed component lengths and buffer addresses -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

theorem packPart_ct (src dst len : Nat) : RelCT isa (Two (FrameAt [5]))
    (packPart src dst len) (fun _ _ => True) := by
  refine RelCT.seq (two_piece (Ψ := fun P s =>
    s.gpr .esi = P.words 5 + BitVec.ofNat 32 src ∧ s.gpr .edx = P.words 5 + BitVec.ofNat 32 dst ∧
    s.gpr .ecx = BitVec.ofNat 32 len) [.esp] (frameAt_pins _) (hc := .block []) ?_ ?_) ?_
  · exact (congrArg Option.isSome (check_of_erase_eq (.block (packArgs src dst len))
      (.block (packArgs 0 0 1)) (τr [.esp]) (.block []) rfl rfl rfl)).trans (by rfl)
  · intro P s R
    exact WP.mono (packArgs_ok R.1 (R.2 5 (by simp)) src dst len) fun _ ⟨si, dx, cx, _, _, _⟩ => ⟨si, dx, cx⟩
  · refine copyMasked_ct.mono ?_ (fun _ _ h => h)
    rintro s t ⟨P, hs, ht⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hs.1.trans ht.1.symm, hs.2.1.trans ht.2.1.symm, hs.2.2.trans ht.2.2.symm]

def SearchContextAt (P : SearchContextPlan) (s : State) : Prop := ∃ W, SearchContext P W s

theorem packPart_context_ct (P : SearchContextPlan) (src dst len : Nat)
    (positive : 0 < len) (small : len < 2 ^ 32)
    (sourceRoom : src + len ≤ usedBytes P.geometry.pLen) (destRoom : dst + len ≤ usedBytes P.geometry.pLen)
    (mutable : VG.Impl.Dsa.Generation.Layout.hash ≤ dst)
    (apart : (P.geometry.part src len).Disjoint (P.geometry.part dst len)) :
    RelCT isa (Two fun (_ : Unit) => SearchContextAt P) (packPart src dst len)
      (Two fun (_ : Unit) => SearchContextAt P) := by
  refine two_post (two_map (fun (_ : Unit) => (⟨P.geometry.frameBase, P.saved⟩ : PublicFrame)) ?_
    (packPart_ct src dst len)) ?_
  · rintro _ s ⟨W, R⟩
    refine ⟨R.arena.frame, ?_⟩
    intro i hi
    obtain rfl := List.mem_singleton.mp hi
    exact (R.representation 5 (by decide)).trans (R.fixed 5 (by decide) (by decide))
  · rintro _ s ⟨W, R⟩
    exact WP.mono (packPart_ok R positive small sourceRoom destRoom mutable apart) fun _ ⟨Rt, _, _, _⟩ => ⟨W, Rt⟩

theorem pack_ct (P : SearchContextPlan) : RelCT isa (Two fun (_ : Unit) => SearchContextAt P)
    (pack P.geometry.pLen P.geometry.qLen) (fun _ _ => True) := by
  have pw := P.geometry.width
  have qw := P.geometry.qWidth
  have pr : p + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by unfold p usedBytes domainCheck; omega
  have qr : q + P.geometry.qLen ≤ usedBytes P.geometry.pLen := by unfold q usedBytes domainCheck; omega
  have gr : g + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by unfold g usedBytes domainCheck; omega
  have r1 : packed + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by unfold packed usedBytes domainCheck; omega
  have r2 : packed + P.geometry.pLen + P.geometry.qLen ≤ usedBytes P.geometry.pLen := by unfold packed usedBytes domainCheck; omega
  have r3 : packed + P.geometry.pLen + P.geometry.qLen + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by unfold packed usedBytes domainCheck; omega
  refine RelCT.seq (packPart_context_ct P p packed _ (by omega) (by omega) pr r1 (by decide)
    (P.geometry.parts_disjoint pr r1 (.inl (by unfold p packed; omega))))
    (RelCT.seq (packPart_context_ct P q (packed + P.geometry.pLen) _ (by omega) (by omega) qr r2
      (by unfold VG.Impl.Dsa.Generation.Layout.hash packed; omega)
      (P.geometry.parts_disjoint qr r2 (.inl (by unfold q packed; omega)))) ?_)
  exact (packPart_context_ct P g (packed + P.geometry.pLen + P.geometry.qLen) _ (by omega) (by omega) gr r3
    (by unfold VG.Impl.Dsa.Generation.Layout.hash packed; omega)
    (P.geometry.parts_disjoint gr r3 (.inl (by unfold g packed; omega)))).mono (fun _ _ h => h) (fun _ _ _ => trivial)
end VG.Proof.Dsa.X86.Generation
