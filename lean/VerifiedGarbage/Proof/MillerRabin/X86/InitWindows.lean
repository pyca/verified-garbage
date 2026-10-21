module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.StageLoadWord
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.MillerRabin.X86.StageStore
import VerifiedGarbage.Proof.MillerRabin.X86.StageLiteral

/-! # Initialize the public exponent length and the secret pass flag -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem initWindows_ok {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V [] s) :
    WP isa (.block initWindows) s fun t =>
      Stage g capacity c p A Js (setAt (setAt V sWords (BitVec.ofNat 32 g.words)) sFlag 0#32) wordFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax, .esi] s t := by
  unfold initWindows
  refine WP.block_append (WP.mono (words_ok v S.data.context) fun a ⟨Count, M, K⟩ => ?_)
  have Sa := S.keepMem K (by decide) (by decide) M
  have reg : a.gpr .esi = BitVec.ofNat 32 g.words := by
    apply BitVec.eq_of_toNat_eq
    rw [Count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.maxWidth; unfold Geometry.words; omega)]
  change WP isa (.block ([.store (slot sWords) .esi] ++ [.mov .eax (.imm 0), .store (slot sFlag) .eax])) a _
  refine WP.block_append (WP.mono (Sa.storeRegister v sWords (by unfold scratchWord sWords; simp) .esi _ reg)
    fun b ⟨Sb, Ob, Kb⟩ => ?_)
  refine WP.mono (Sb.literal v sFlag (by unfold scratchWord sFlag; simp) 0#32) fun t ⟨St, Ot, Kt⟩ => ?_
  rw [M] at Ob
  exact ⟨St, Ob.trans Ot, ((K.mono (by decide)).trans (Kb.mono (by decide))).trans (Kt.mono (by decide))⟩

end VG.Proof.MillerRabin.X86
