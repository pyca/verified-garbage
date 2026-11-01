module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareHeader
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Frame
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.Constants
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentReady
import VerifiedGarbage.Proof.Mont.RangeCover

/-! # Complete candidate preparation reuses all expensive state across witnesses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

def ranges (g : Geometry) : List (Nat × Nat) :=
  PrepareHeader.ranges ++ PreparedR2.ranges g ++ Constants.ranges g ++ Exponent.preparedRanges g

theorem code_full_okAt {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) (bound : g.w ≤ 64) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) {e : Nat} (I : Input g c capacity p s e) (positive : 1 ≤ e) (eLt : e < 64 * g.w) :
    WP isa (VG.Impl.RsaKeyGen.X86.Prepare.codeAt e g.w name mont) s fun t =>
      Data g c capacity p t ∧ Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps clob s t ∧
      WorkspaceFrame g (ranges g) s.mem t.mem := by
  unfold VG.Impl.RsaKeyGen.X86.Prepare.codeAt
  rw [Prepared.slot_eq, Prepared.slot_eq, Prepared.slot_eq]
  refine WP.seq (WP.mono (PrepareHeader.code_ok v I.scratch I.caller length I.candidate I.odd)
    fun a ⟨A, Oa, Ka, strideA⟩ => ?_)
  have minusA : val32 a.mem g.W (g.array 5) g.words = c - 1 := by
    rw [Oa.val32 (fun r mem => by
      simp only [PrepareHeader.ranges, Header.ranges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      have := v.arrayHeader 5
      rcases mem with (rfl | rfl | rfl) | rfl <;> right <;> omega)
      (by have := I.scratch.nowrap; have := v.arrayFit (j := 5) (by decide); omega)]
    exact I.minusOne
  refine WP.seq (WP.mono (PreparedR2.code_okAt verified noSp stack v length A bound I.odd positive eLt I.top)
    fun b ⟨B, r2B, Fb, Kb, Wb⟩ => ?_)
  have strideB : word b.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
    change b.mem.readW (off g.W 224) 64 = _
    rw [Wb.read64 (by have := v.headerFit; omega) (fun r mem => by
      simp only [PreparedR2.ranges, PreparedR2.coreRanges, PreparedR2.phaseRanges, montWrites, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl <;>
        exact Or.inl (by have := v.arrayHeader 1; simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega))]
    exact strideA
  have minusB := (PreparedR2.preserve v Wb (j := 5) (Or.inl rfl)).trans minusA
  refine WP.seq (WP.mono (Constants.code_ok verified noSp stack v length B I.odd (by have := I.large; omega) r2B)
    fun d ⟨D, oneD, minusD, Wd, Fd, Kd⟩ => ?_)
  have strideD : word d.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
    change d.mem.readW (off g.W 224) 64 = _
    rw [Wd.read64 (by have := v.headerFit; omega) (fun r mem => by
      simp only [Constants.ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl | rfl) | (rfl | rfl) <;> exact Or.inl (by have := v.arrayHeader 1; simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega))]
    exact strideB
  have minusSaved := (Constants.preserve v Wd (j := 5) (Or.inr (Or.inl rfl))).trans minusB
  have r2D := (Constants.preserve v Wd (j := 4) (Or.inl rfl)).trans r2B
  refine WP.mono (Exponent.ready_ok v D minusSaved I.odd I.large) fun t ⟨T, exponentT, markerT, Ot, Kt⟩ => ?_
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem a.mem :=
    (workspaceGlobalFrame Oa (fun r mem => by
      simp only [PrepareHeader.ranges, Header.ranges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      have := v.headerFit
      rcases mem with (rfl | rfl | rfl) | rfl <;> omega)).mono (fun r mem => List.mem_append_left _ mem)
  have Ft : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) d.mem t.mem :=
    (workspaceGlobalFrame Ot (fun r mem => by
      simp only [Exponent.preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
      have srcFit := Prepared.paddedFit v (j := 0) (by decide)
      have outFit := Prepared.paddedFit v (j := 27) (by decide)
      have := v.headerFit
      rcases mem with rfl | rfl | rfl <;>
        simp only [VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega)).mono
      (fun r mem => List.mem_append_left _ mem)
  have Wa : WorkspaceFrame g PrepareHeader.ranges s.mem a.mem := WorkspaceFrame.of_outs I.scratch.nowrap Oa
  have Wt : WorkspaceFrame g (Exponent.preparedRanges g) d.mem t.mem := WorkspaceFrame.of_outs I.scratch.nowrap Ot
  have allWrites : WorkspaceFrame g (ranges g) s.mem t.mem :=
    (((Wa.mono (fun _ mem => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ mem)))).trans
      (Wb.mono (fun _ mem => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ mem))))).trans
      (Wd.mono (fun _ mem => List.mem_append_left _ (List.mem_append_right _ mem)))).trans
      (Wt.mono (fun _ mem => List.mem_append_right _ mem))
  refine ⟨⟨T, ?_, ?_, ?_, exponentT, markerT, ?_⟩, ((Fa.trans Fb).trans Fd).trans Ft, ?_, allWrites⟩
  · exact (Exponent.prepared_preserve v Ot (j := 4) (Or.inl rfl)).trans r2D
  · exact (Exponent.prepared_preserve v Ot (j := 9) (Or.inr (Or.inr (Or.inl rfl)))).trans oneD
  · exact (Exponent.prepared_preserve v Ot (j := 10) (Or.inr (Or.inr (Or.inr rfl)))).trans minusD
  · rw [Ot.word (fun r mem => by
      simp only [Exponent.preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · right; decide
      · left; have := v.arrayHeader 0; omega
      · left; have := v.arrayHeader 27; omega) (by decide)]
    exact strideD
  · exact (((Ka.mono (by unfold clob PrepareHeader.clob; decide)).widen Kb).widen Kd).widen Kt

theorem code_full_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) (bound : g.w ≤ 64) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (I : Input g c capacity p s) :
    WP isa (VG.Impl.RsaKeyGen.X86.Prepare.code g.w name mont) s fun t =>
      Data g c capacity p t ∧ Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps clob s t ∧
      WorkspaceFrame g (ranges g) s.mem t.mem :=
  code_full_okAt verified noSp stack v bound length I
    (by have := v.minWidth; omega) (by have := v.minWidth; omega)

theorem code_okAt {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) (bound : g.w ≤ 64) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) {e : Nat} (I : Input g c capacity p s e) (positive : 1 ≤ e) (eLt : e < 64 * g.w) :
    WP isa (VG.Impl.RsaKeyGen.X86.Prepare.codeAt e g.w name mont) s fun t =>
      Data g c capacity p t ∧ Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps clob s t :=
  WP.mono (code_full_okAt verified noSp stack v bound length I positive eLt) fun _ ⟨D, F, K, _⟩ => ⟨D, F, K⟩

theorem code_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) (bound : g.w ≤ 64) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (I : Input g c capacity p s) :
    WP isa (VG.Impl.RsaKeyGen.X86.Prepare.code g.w name mont) s fun t =>
      Data g c capacity p t ∧ Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps clob s t :=
  WP.mono (code_full_ok verified noSp stack v bound length I) fun _ ⟨D, F, K, _⟩ => ⟨D, F, K⟩

end VG.Proof.RsaKeyGen.X86.Prepare
