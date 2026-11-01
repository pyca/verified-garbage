module

import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Load
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRound
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessMont
import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundCall
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRt
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Each witness iteration at the run-time width computes the exact sampled Miller–Rabin test -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessRound (uniformOffset)

theorem round_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s) {input : Import.Geometry}
    (C : Import.Context input s) (count : input.count = g.words)
    (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst)
    (odd : c % 2 = 1) (large : 3 ≤ c) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * g.w)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessRt.round montName mont roundName round) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (8 * g.w)))
      Prepare.Data g c capacity p t ∧ (t.gpr .eax).toNat = (if Proof.MillerRabin.Round.round c sampled.1 then 1 else 0) ∧
      t.mem.readW (off g.W uniformOffset) 32 = cmask sampled.2 ∧
      WorkspaceFrame g (WitnessRound.ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps WitnessRound.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.round
  refine WP.seq (WP.mono (drawn_ok v S C count source destination odd shape)
    fun a ⟨A, Va, uniform, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Prepare.storeGap_ok v A (d := uniformOffset) (by decide) (by decide))
    fun b ⟨B, uniformB, Ob, Kb⟩ => ?_)
  rw [uniform] at uniformB
  have Vb := (Ob.val32 (Or.inr (by have := v.arrayHeader 6; unfold uniformOffset; omega))
    (by have := A.ready.scratch.nowrap; have := v.arrayFit (j := 6) (by decide); omega)).trans Va
  refine WP.seq (WP.mono (WitnessMont.code_ok montVerified montNoSp montStack v length B odd (by omega))
    fun d ⟨D, Vd, Wd, Fd, Kd⟩ => ?_)
  rw [Vb] at Vd
  have uniformD : d.mem.readW (off g.W uniformOffset) 32 = b.mem.readW (off g.W uniformOffset) 32 :=
    Wd.read32 (by have := v.headerFit; unfold uniformOffset; omega) (fun r mem => by
      simp only [WitnessMont.ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl | rfl) | rfl <;>
        exact Or.inl (by simp only [uniformOffset, Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega))
  refine WP.mono (RoundCall.code_ok (b := (Spec.RsaKeyGen.witness (c - 1)
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (8 * g.w)))).1)
    roundVerified roundNoSp roundStack v length D odd large
    (by rw [Nat.mod_mul_mod]; exact Vd) fit far lengthFar) fun t ⟨T, result, Wt, Ft, Kt⟩ => ?_
  have uniformT : t.mem.readW (off g.W uniformOffset) 32 = d.mem.readW (off g.W uniformOffset) 32 :=
    Wt.read32 (by have := v.headerFit; unfold uniformOffset; omega) (fun r mem => by
      simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [uniformOffset, Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega)
  have Wa : WorkspaceFrame g (WitnessRound.ranges g) s.mem a.mem :=
    WorkspaceFrame.of_outs S.ready.scratch.nowrap (Outs.of_outside
      (Oa.mono (o' := g.array 6) (n' := 8 * (g.w + 2)) (Nat.le_refl _) (by unfold Geometry.words; omega))
      (by simp [WitnessRound.ranges, WitnessMont.ranges, montWrites]))
  have Wb : WorkspaceFrame g (WitnessRound.ranges g) a.mem b.mem :=
    WorkspaceFrame.of_outs A.ready.scratch.nowrap (Outs.of_outside Ob (by simp [WitnessRound.ranges]))
  have Wd' := Wd.mono (fun r mem => List.mem_append_left _ (List.mem_append_left _ mem) : ∀ r ∈ WitnessMont.ranges g, r ∈ WitnessRound.ranges g)
  have Wt' := Wt.mono (fun r mem => List.mem_append_left _ (List.mem_append_right _ mem) : ∀ r ∈ roundWrites g, r ∈ WitnessRound.ranges g)
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem a.mem :=
    (workspaceGlobalFrame (Outs.of_outside Oa (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  have Fb : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) a.mem b.mem :=
    (workspaceGlobalFrame (Outs.of_outside Ob (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; unfold uniformOffset; omega)).mono
      (fun r mem => List.mem_append_left _ mem)
  have Fd' := VG.X86.Frame.below_mono Fd (by decide : 80 ≤ 108) fit
  exact ⟨T, result, (uniformT.trans uniformD).trans uniformB,
    ((Wa.trans Wb).trans Wd').trans Wt', ((Fa.trans Fb).trans Fd').trans Ft,
    (((Ka.mono (by unfold WitnessRound.clob WitnessRt.clob; decide)).widen Kb).widen Kd).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessRt
