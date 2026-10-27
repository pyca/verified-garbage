module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Prepare
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Code
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Frame
import VerifiedGarbage.Proof.RsaKeyGen.X86.Constants
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareMetadata
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatch
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Preparation with Miller–Rabin's exponent at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready)

/-- The header, R² and the constants at width `g.w`: `Prepare.code_full_okAt`
but for the exponent. -/
theorem head_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) (bound : g.w ≤ 64) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (I : Prepare.Input g c capacity p s) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.prepareHead g.w name mont) s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 4) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c ∧
      val32 t.mem g.W (g.array 9) g.words = 2 ^ (64 * g.w) % c ∧
      val32 t.mem g.W (g.array 10) g.words = c - 2 ^ (64 * g.w) % c ∧
      val32 t.mem g.W (g.array 5) g.words = c - 1 ∧ word t.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps Prepare.clob s t ∧
      WorkspaceFrame g (PrepareHeader.ranges ++ PreparedR2.ranges g ++ Constants.ranges g) s.mem t.mem := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.prepareHead VG.Impl.RsaKeyGen.X86.PreparedR2.code
  refine WP.seq (WP.mono (PrepareHeader.code_ok v I.scratch I.caller length I.candidate I.odd)
    fun a ⟨A, Oa, Ka, strideA⟩ => ?_)
  have minusA : val32 a.mem g.W (g.array 5) g.words = c - 1 := by
    rw [Oa.val32 (fun r mem => by
      simp only [PrepareHeader.ranges, Header.ranges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      have := v.arrayHeader 5
      rcases mem with (rfl | rfl | rfl) | rfl <;> right <;> omega)
      (by have := I.scratch.nowrap; have := v.arrayFit (j := 5) (by decide); omega)]
    exact I.minusOne
  refine WP.seq (WP.mono (PreparedR2.code_okAt verified noSp stack v length A bound I.odd
    (by have := v.minWidth; omega) (by have := v.minWidth; omega) I.top)
    fun b ⟨B, r2B, Fb, Kb, Wb⟩ => ?_)
  have strideB : word b.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
    change b.mem.readW (off g.W 224) 64 = _
    rw [Wb.read64 (by have := v.headerFit; omega) (fun r mem => by
      simp only [PreparedR2.ranges, PreparedR2.coreRanges, PreparedR2.phaseRanges, montWrites, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl <;>
        exact Or.inl (by have := v.arrayHeader 1; simp only [Geometry.array, Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes]; omega))]
    exact strideA
  have minusB := (PreparedR2.preserve v Wb (j := 5) (Or.inl rfl)).trans minusA
  refine WP.mono (Constants.code_ok verified noSp stack v length B I.odd (by have := I.large; omega) r2B)
    fun d ⟨D, oneD, minusD, Wd, Fd, Kd⟩ => ?_
  have strideD : word d.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
    change d.mem.readW (off g.W 224) 64 = _
    rw [Wd.read64 (by have := v.headerFit; omega) (fun r mem => by
      simp only [Constants.ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl | rfl) | (rfl | rfl) <;> exact Or.inl (by have := v.arrayHeader 1; simp only [Geometry.array, Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes]; omega))]
    exact strideB
  have minusSaved := (Constants.preserve v Wd (j := 5) (Or.inr (Or.inl rfl))).trans minusB
  have r2D := (Constants.preserve v Wd (j := 4) (Or.inl rfl)).trans r2B
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem a.mem :=
    (workspaceGlobalFrame Oa (fun r mem => by
      simp only [PrepareHeader.ranges, Header.ranges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      have := v.headerFit
      rcases mem with (rfl | rfl | rfl) | rfl <;> omega)).mono (fun r mem => List.mem_append_left _ mem)
  have Wa : WorkspaceFrame g PrepareHeader.ranges s.mem a.mem := WorkspaceFrame.of_outs I.scratch.nowrap Oa
  refine ⟨D, r2D, oneD, minusD, minusSaved, strideD, (Fa.trans Fb).trans Fd,
    ((Ka.mono (by unfold Prepare.clob PrepareHeader.clob; decide)).widen Kb).widen Kd, ?_⟩
  exact ((Wa.mono (fun _ mem => List.mem_append_left _ (List.mem_append_left _ mem))).trans
    (Wb.mono (fun _ mem => List.mem_append_left _ (List.mem_append_right _ mem)))).trans
    (Wd.mono (fun _ mem => List.mem_append_right _ mem))

theorem input_keep {P : MillerRabinLoop.Parameters} {s t : State} (I : CandidatePrepare.Input P s)
    {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs) (edi : .edi ∉ rs) (M : t.mem = s.mem) :
    CandidatePrepare.Input P t := by
  refine ⟨⟨I.prepare.scratch.of_keeps K edi sp,
    I.prepare.caller.keepFrame K sp (by rw [M]; exact Frame.refl _ _),
    by rw [M]; exact I.prepare.candidate, by rw [M]; exact I.prepare.minusOne, I.prepare.odd, I.prepare.large,
    I.prepare.top⟩, by rw [K.2.1, K.2.2]; exact I.readable, by rw [M]; exact I.entropy,
    by rw [M]; exact I.randPtr, by rw [M]; exact I.randLength, by rw [M]; exact I.used⟩

theorem width_member {w : Nat} (width : 4 ≤ w) (bound : w ≤ 64) : w ∈ VG.Impl.RsaKeyGen.X86.Candidate.widths :=
  List.mem_map.mpr ⟨w - 4, List.mem_range.mpr (by omega), by omega⟩

theorem widths_bounded : ∀ x ∈ VG.Impl.RsaKeyGen.X86.Candidate.widths, x < 2 ^ 32 := by
  intro w mem
  obtain ⟨i, index, rfl⟩ := List.mem_map.mp mem
  have bound := List.mem_range.mp index
  omega

/-- Preparation at the width in the header, the exponent at the run-time
width: what `CandidatePrepare.code_ok` gives. -/
theorem prepared_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (width : 4 ≤ P.g.w) (bound : P.g.w ≤ 64)
    (seed : P.seed = 64 * P.g.w - 1) {s : State} (I : CandidatePrepare.Input P s)
    (len : s.mem.readW (off P.g.W 4) 32 = BitVec.ofNat 32 (8 * P.g.w)) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.prepared name mont) s fun t =>
      CandidatePrepare.Ready P t ∧ WorkspaceFrame P.g (Prepare.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 80]) s.mem t.mem ∧ Keeps Prepare.clob s t := by
  have G := v.geometry
  unfold VG.Impl.RsaKeyGen.X86.Candidate.prepared VG.Impl.RsaKeyGen.X86.Candidate.width
  refine WP.seq (wp_movS (readSrc_sc I.prepare.scratch (d := 4) (by have := G.headerFit; omega)) fun a A _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun b B => WP.block_nil ?_)
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  have Kb : Keeps [.eax] s b := A.keeps.trans B.keeps
  have eax : b.gpr .eax = BitVec.ofNat 32 P.g.w := by
    rw [B.gpr, A.gpr, len]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  refine WP.seq (Candidate.dispatch_ok eax (by omega) _ (width_member width bound) widths_bounded fun c C => ?_)
  have Mc : c.mem = s.mem := C.mem.trans Mb
  have Kc : Keeps [.eax] s c := Kb.widen (C.keeps [])
  have Ic := input_keep I Kc (by decide) (by decide) Mc
  have Ip : Prepare.Input P.g P.candidate P.capacity P.p c := by
    have := Ic.prepare
    rw [seed] at this
    exact this
  refine WP.mono (head_ok verified noSp stack G bound v.length Ip)
    fun d ⟨D, r2D, oneD, minusD, savedD, strideD, Fd, Kd, Wd⟩ => ?_
  refine WP.mono (MrExponentRt.code_ok G D savedD Ip.odd (by have := Ip.large; omega))
    fun t ⟨T, exponentT, markerT, Wt, Ft, Kt⟩ => ?_
  rw [Mc] at Fd Wd
  have preserve {j : Nat} (index : j = 4 ∨ j = 9 ∨ j = 10) :
      val32 t.mem P.g.W (P.g.array j) P.g.words = val32 d.mem P.g.W (P.g.array j) P.g.words := by
    apply Wt.val32 (G.arrayFit (by omega))
    intro r mem
    simp only [Exponent.preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases index with rfl | rfl | rfl <;> rcases mem with rfl | rfl | rfl <;>
      simp only [Geometry.array, Geometry.words, Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes,
        VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega
  have strideT : word t.mem P.g.W 224 = BitVec.ofNat 64 (8 * (P.g.w + 2)) := by
    change t.mem.readW (off P.g.W 224) 64 = _
    rw [Wt.read64 (by have := G.headerFit; omega) (fun r mem => by
      simp only [Exponent.preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · right; decide
      · left; have := G.arrayHeader 0; omega
      · left; have := G.arrayHeader 27; omega)]
    exact strideD
  have W : WorkspaceFrame P.g (Prepare.ranges P.g) s.mem t.mem :=
    (Wd.mono (fun _ mem => List.mem_append_left _ mem)).trans (Wt.mono (fun _ mem => List.mem_append_right _ mem))
  have F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 80]) s.mem t.mem := Fd.trans Ft
  have data : Prepare.Data P.g P.candidate P.capacity P.p t :=
    ⟨T, (preserve (Or.inl rfl)).trans r2D, (preserve (Or.inr (Or.inl rfl))).trans oneD,
      (preserve (Or.inr (Or.inr rfl))).trans minusD, exponentT, markerT, strideT⟩
  refine ⟨⟨data, ?_, ?_, ?_, ?_, ?_⟩, W, F, ((Kc.mono (by decide)).trans Kd).trans Kt⟩
  · rw [Kt.2.1, Kt.2.2, Kd.2.1, Kd.2.2, Kc.2.1, Kc.2.2]; exact I.readable
  · rw [frame_bytesAt F (by
      intro r mem
      simp only [List.mem_append, List.mem_singleton] at mem
      rcases mem with rfl | rfl
      · exact v.randSeparate
      · exact v.randStackFar.sub_right (below_sub (by decide) v.low)) (by have := v.randLenFit; omega)]
    exact I.entropy
  · rw [Prepare.metadata32 G W (d := 28) (by unfold Prepare.protectedHeader; omega)]
    exact I.randPtr
  · rw [w32, Prepare.metadata32 G W (d := 32) (by unfold Prepare.protectedHeader; omega)]
    exact I.randLength
  · rw [w32, Prepare.metadata32 G W (d := 152) (by unfold Prepare.protectedHeader; omega)]
    exact I.used

end VG.Proof.RsaKeyGen.X86.MrExponentRt
