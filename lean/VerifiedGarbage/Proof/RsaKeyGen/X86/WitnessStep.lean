module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRoundFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessCount
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessAdvance
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessInput
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRound

/-! # A complete loop step accounts for entropy and both witness counters exactly -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessStep
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessStep

def ranges (g : Geometry) : List (Nat × Nat) :=
  [(152, 4)] ++ WitnessRound.ranges g ++ WitnessCount.ranges

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem flag_value {x : BitVec 32} {b : Bool} (h : x.toNat = if b then 1 else 0) :
    x = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  cases b <;> simpa using h

theorem codeAt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity used randLen draw k : Nat} {p rand : BitVec 32}
    (two : 2 ≤ k) (narrow : 4 * k ≤ draw) (wide : draw ≤ 8 * g.w) (four : draw % 4 = 0)
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s)
    (source : s.mem.readW (off g.W 28) 32 = rand) (consumed : w32 s.mem g.W 152 = used)
    (randFit : rand.toNat + randLen ≤ 2 ^ 32) (randLenFit : randLen < 2 ^ 32)
    (enough : used + draw ≤ randLen)
    (readable : InRegions (s.rd ++ s.wr) (rand.setWidth 64) randLen)
    (separate : (⟨rand.setWidth 64, randLen⟩ : Region).Disjoint ⟨g.W, g.L⟩)
    (odd : c % 2 = 1) (large : 3 ≤ c) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k)
    (roundsFit : w32 s.mem g.W 176 + 1 < 2 ^ 32) (uniformFit : w32 s.mem g.W 192 + 1 < 2 ^ 32)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (codeAt draw k g.w montName mont roundName round) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) draw))
      Prepare.Data g c capacity p t ∧ w32 t.mem g.W 152 = used + draw ∧
      w32 t.mem g.W 176 = w32 s.mem g.W 176 + 1 ∧
      w32 t.mem g.W 192 = w32 s.mem g.W 192 + sampled.2.toNat ∧
      w32 t.mem g.W 168 = WitnessStatus.status (Proof.MillerRabin.Round.round c sampled.1)
        (w32 s.mem g.W 176 + 1) (w32 s.mem g.W 192 + sampled.2.toNat) (w32 s.mem g.W 200) ∧
      WorkspaceFrame g (ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps clob s t := by
  unfold codeAt
  refine WP.seq (WP.mono (WitnessAdvance.codeAt_ok (step := draw) v S source consumed (by omega))
    fun a ⟨A, sourceA, usedA, Oa, Ka⟩ => ?_)
  let input := WitnessInput.geometryAt g rand used (draw / 4)
  have readA : InRegions (a.rd ++ a.wr) (rand.setWidth 64) randLen := by
    rw [Ka.2.1, Ka.2.2]; exact readable
  have C := WitnessInput.context_okAt (used := used) (count := draw / 4) v A.ready.scratch randFit (by omega)
    (by unfold Geometry.words; omega) (by omega) readA separate
  have inputSource : input.src.setWidth 64 = off (rand.setWidth 64) used :=
    WitnessInput.source_address (by omega)
  have bytesA : Spec.Rsa.bytesAt a.mem (input.src.setWidth 64) draw =
      Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) draw := by
    rw [inputSource]
    apply VG.Proof.Bignum.scratch_bytes
      (Oa.mono (o' := 0) (n' := g.L) (by decide) (by have := v.headerFit; unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; omega))
      (by have := randLenFit; omega)
    exact separate.sub_left (Offset.sub_base _ enough)
  refine WP.seq (WP.mono (WitnessRound.codeAt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v length A
    C (by change 4 * (draw / 4) = draw; omega) two (by change k ≤ draw / 4; omega)
    (by change draw / 4 ≤ g.words; unfold Geometry.words; omega) sourceA
    (WitnessInput.destination_pointer v A.ready.scratch).symm odd large shape fit far lengthFar)
    fun b ⟨B, resultB, uniformB, Wb, Fb, Kb⟩ => ?_)
  rw [bytesA] at resultB uniformB
  have roundB : w32 b.mem g.W 176 = w32 s.mem g.W 176 :=
    (WitnessRound.header32 v Wb (by unfold WitnessRound.safeHeader; decide)).trans
      (Oa.w32 (by unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; decide) (by decide))
  have uniB : w32 b.mem g.W 192 = w32 s.mem g.W 192 :=
    (WitnessRound.header32 v Wb (by unfold WitnessRound.safeHeader; decide)).trans
      (Oa.w32 (by unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; decide) (by decide))
  have checksB : w32 b.mem g.W 200 = w32 s.mem g.W 200 :=
    (WitnessRound.header32 v Wb (by unfold WitnessRound.safeHeader; decide)).trans
      (Oa.w32 (by unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; decide) (by decide))
  have flagB : b.gpr .eax = BitVec.ofNat 32 (Proof.MillerRabin.Round.round c
      (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip
        (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) draw))).1).toNat := by
    exact flag_value resultB
  refine WP.mono (WitnessCount.code_ok v B flagB uniformB (by change w32 b.mem g.W 176 + 1 < 2 ^ 32; rw [roundB]; exact roundsFit)
    (by change w32 b.mem g.W 192 + _ < 2 ^ 32; rw [uniB]; have := Bool.toNat_le (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip
      (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) draw))).2; omega))
    fun t ⟨T, countT, uniT, statusT, Ot, Kt⟩ => ?_
  dsimp only [VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset,
    VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.checksOffset] at countT uniT statusT
  rw [roundB] at countT
  rw [uniB] at uniT
  rw [roundB, uniB, checksB] at statusT
  have usedB := (WitnessRound.header32 v Wb (d := 152) (by unfold WitnessRound.safeHeader; decide)).trans usedA
  have usedT : w32 t.mem g.W 152 = used + draw := by
    have same := (WorkspaceFrame.of_outs B.ready.scratch.nowrap Ot).read32
      (d := 152) (by have := v.headerFit; omega) (by
        intro r mem
        simp only [WitnessCount.ranges, WitnessCount.nextRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with (rfl | rfl) | rfl <;> left <;> decide)
    rw [show w32 t.mem g.W 152 = w32 b.mem g.W 152 from congrArg BitVec.toNat same]
    exact usedB
  have Wa : WorkspaceFrame g (ranges g) s.mem a.mem := WorkspaceFrame.of_outs S.ready.scratch.nowrap
    (Outs.of_outside Oa (by simp [ranges, VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset]))
  have Wb' := Wb.mono (fun r mem => List.mem_append_left _ (List.mem_append_right _ mem) : ∀ r ∈ WitnessRound.ranges g, r ∈ ranges g)
  have Wt : WorkspaceFrame g (ranges g) b.mem t.mem := WorkspaceFrame.of_outs B.ready.scratch.nowrap
    (Ot.mono (fun r mem => List.mem_append_right _ mem))
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem a.mem :=
    (workspaceGlobalFrame (Outs.of_outside Oa (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; omega)).mono
      (fun r mem => List.mem_append_left _ mem)
  have Ft : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) b.mem t.mem :=
    (workspaceGlobalFrame Ot (fun r mem => by
      simp only [WitnessCount.ranges, WitnessCount.nextRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl) | rfl <;> have := v.headerFit <;>
        simp only [VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset,
          VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset] <;> omega)).mono
      (fun r mem => List.mem_append_left _ mem)
  exact ⟨T, usedT, countT, uniT, statusT, (Wa.trans Wb').trans Wt, (Fa.trans Fb).trans Ft,
    ((Ka.mono (by unfold clob; decide)).widen Kb).widen Kt⟩

theorem code_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity used randLen : Nat} {p rand : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s)
    (source : s.mem.readW (off g.W 28) 32 = rand) (consumed : w32 s.mem g.W 152 = used)
    (randFit : rand.toNat + randLen ≤ 2 ^ 32) (randLenFit : randLen < 2 ^ 32)
    (enough : used + 8 * g.w ≤ randLen)
    (readable : InRegions (s.rd ++ s.wr) (rand.setWidth 64) randLen)
    (separate : (⟨rand.setWidth 64, randLen⟩ : Region).Disjoint ⟨g.W, g.L⟩)
    (odd : c % 2 = 1) (large : 3 ≤ c) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * g.w)
    (roundsFit : w32 s.mem g.W 176 + 1 < 2 ^ 32) (uniformFit : w32 s.mem g.W 192 + 1 < 2 ^ 32)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (code g.w montName mont roundName round) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) (8 * g.w)))
      Prepare.Data g c capacity p t ∧ w32 t.mem g.W 152 = used + 8 * g.w ∧
      w32 t.mem g.W 176 = w32 s.mem g.W 176 + 1 ∧
      w32 t.mem g.W 192 = w32 s.mem g.W 192 + sampled.2.toNat ∧
      w32 t.mem g.W 168 = WitnessStatus.status (Proof.MillerRabin.Round.round c sampled.1)
        (w32 s.mem g.W 176 + 1) (w32 s.mem g.W 192 + sampled.2.toNat) (w32 s.mem g.W 200) ∧
      WorkspaceFrame g (ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps clob s t :=
  codeAt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v
    (by have := v.minWidth; omega) (by omega) (by omega) (by omega) length S source consumed randFit randLenFit enough
    readable separate odd large (by rw [shape]; omega) roundsFit uniformFit fit far lengthFar

end VG.Proof.RsaKeyGen.X86.WitnessStep
