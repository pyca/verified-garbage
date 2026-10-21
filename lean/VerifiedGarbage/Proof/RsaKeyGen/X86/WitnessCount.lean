module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessCountNext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStatus
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap

/-! # The complete masked counting policy retains candidate preparation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessCount
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessCount

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]
def ranges : List (Nat × Nat) := nextRanges ++ [(statusOffset, 4)]

theorem code_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32} {passed uniform : Bool}
    (S : Prepare.Data g c capacity p s) (flag : s.gpr .eax = BitVec.ofNat 32 passed.toNat)
    (mask : s.mem.readW (off g.W 144) 32 = cmask uniform)
    (roundsFit : w32 s.mem g.W roundsOffset + 1 < 2 ^ 32)
    (uniformFit : w32 s.mem g.W uniformOffset + uniform.toNat < 2 ^ 32) :
    WP isa code s fun t =>
      Prepare.Data g c capacity p t ∧
      w32 t.mem g.W roundsOffset = w32 s.mem g.W roundsOffset + 1 ∧
      w32 t.mem g.W uniformOffset = w32 s.mem g.W uniformOffset + uniform.toNat ∧
      w32 t.mem g.W statusOffset = WitnessStatus.status passed (w32 s.mem g.W roundsOffset + 1)
        (w32 s.mem g.W uniformOffset + uniform.toNat) (w32 s.mem g.W checksOffset) ∧
      Outs g.W ranges s.mem t.mem ∧ Keeps clob s t := by
  unfold code
  refine WP.seq (WP.mono (next_ok v S mask roundsFit uniformFit)
    fun a ⟨A, flagA, roundsA, uniformA, checksA, countA, uniA, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (WitnessStatus.code_ok (flagA.trans flag)) fun b ⟨statusB, memB, Kb⟩ => ?_)
  rw [roundsA, uniformA, checksA, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt roundsFit, Nat.mod_eq_of_lt uniformFit] at statusB
  have B : Prepare.Data g c capacity p b :=
    A.keepHeader v (d := 128) (bytes := 0) (by decide) (by decide)
      (by rw [memB]; exact Outside.refl _ _ _ _) Kb (by decide) (by decide)
  refine wp_storeS (B.ready.scratch.ea (by have := v.headerFit; unfold statusOffset; omega))
    (B.ready.scratch.write (by have := v.headerFit; unfold statusOffset; omega)) fun t T => WP.block_nil ?_
  have Ot : Outside g.W statusOffset 4 b.mem t.mem := by
    rw [T.mem]
    exact writeW32_outside _ _ _ (by unfold statusOffset; decide)
  have statusBound : WitnessStatus.status passed (w32 s.mem g.W roundsOffset + 1)
      (w32 s.mem g.W uniformOffset + uniform.toNat) (w32 s.mem g.W checksOffset) < 2 ^ 32 := by
    unfold WitnessStatus.status
    split <;> first | decide | (split <;> decide)
  have statusT : w32 t.mem g.W statusOffset = WitnessStatus.status passed (w32 s.mem g.W roundsOffset + 1)
      (w32 s.mem g.W uniformOffset + uniform.toNat) (w32 s.mem g.W checksOffset) := by
    rw [T.mem, w32_write_self, statusB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt statusBound]
  have countT : w32 t.mem g.W roundsOffset = w32 s.mem g.W roundsOffset + 1 := by
    rw [Ot.w32 (by unfold statusOffset roundsOffset; decide) (by unfold roundsOffset; decide), memB]
    exact countA
  have uniT : w32 t.mem g.W uniformOffset = w32 s.mem g.W uniformOffset + uniform.toNat := by
    rw [Ot.w32 (by unfold statusOffset uniformOffset; decide) (by unfold uniformOffset; decide), memB]
    exact uniA
  have Oab : Outs g.W ranges s.mem b.mem := by
    rw [memB]
    exact Oa.mono (fun r mem => List.mem_append_left _ mem)
  exact ⟨B.keepGap v (by unfold statusOffset; decide) (by unfold statusOffset; decide) Ot (T.keeps []) (by decide) (by decide),
    countT, uniT, statusT, Oab.trans (Outs.of_outside Ot (by simp [ranges])),
    ((Ka.mono (by unfold clob nextClob; decide)).widen Kb).widen (T.keeps [])⟩

end VG.Proof.RsaKeyGen.X86.WitnessCount
