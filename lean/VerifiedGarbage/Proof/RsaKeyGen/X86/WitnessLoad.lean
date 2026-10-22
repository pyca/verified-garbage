module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessSample
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.RegionOutside
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessZeros
import VerifiedGarbage.Proof.RsaKeyGen.WitnessSample
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData

/-! # Entropy import and interval sampling retain all reusable candidate preparation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLoad
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem codeAt_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) {input : Import.Geometry}
    (C : Import.Context input s) {D k : Nat} (width : 4 * input.count = D) (two : 2 ≤ k)
    (narrow : k ≤ input.count) (wide : input.count ≤ g.words)
    (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst)
    (odd : c % 2 = 1) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt D k g.w) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) D))
      Prepare.Data g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = sampled.1 ∧
      t.gpr .eax = cmask sampled.2 ∧ Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt VG.Impl.RsaKeyGen.X86.WitnessLoad.zeroTail
  rw [Prepared.slot_eq, Prepared.slot_eq, ← width, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
  have arrayFit : g.array 6 + 4 * g.words ≤ g.L := v.arrayFit (by decide)
  have hw : g.words = 2 * g.w := rfl
  have dstAddr : input.dst.setWidth 64 = off g.W (g.array 6) := by
    rw [← destination]
    have fit : g.array 6 < g.L := by
      have := v.minWidth
      unfold Geometry.words at arrayFit
      omega
    exact S.ready.scratch.ea fit
  have region : input.destRegion = ⟨off g.W (g.array 6), 4 * input.count⟩ := by
    unfold Import.Geometry.destRegion
    rw [dstAddr]
  have load := Import.load_ok C source destination
  change WP isa (VG.Impl.RsaKeyGen.X86.Import.load input.count (g.array 6)) s _ at load
  refine WP.seq (WP.mono load fun a ⟨value, F, K⟩ => ?_)
  have Va : val32 a.mem g.W (g.array 6) input.count =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (4 * input.count)) := by
    rw [dstAddr] at value
    rw [← VG.Proof.Bignum.read_eq_val32]
    exact value
  rw [region] at F
  have Oa := frame_outside F (by have := S.ready.scratch.nowrap; omega)
  have A := WitnessMont.data_outside v S (Oa.mono (by omega) (by omega)) K (by decide) (by decide)
  refine WP.seq (WP.mono (WitnessLoad.zeros_ok A.ready.scratch (g.array 6 + 4 * k) (2 * g.w - k)
    (by omega)) fun b ⟨Zb, Ob, Kb⟩ => ?_)
  have B := WitnessMont.data_outside v A
    (Ob.mono (by have := g.arrayBefore (i := 5) (j := 6) (by decide); omega)
      (by omega)) Kb (by decide) (by decide)
  -- The witness: the draw's low `32 k` bits, zeros above.
  have lowB : val32 b.mem g.W (g.array 6) k =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (4 * input.count)) % 2 ^ (32 * k) := by
    rw [← Va, show input.count = k + (input.count - k) by omega, VG.Proof.Mont.val32_append,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]
    exact Ob.val32 (by omega) (by have := S.ready.scratch.nowrap; omega)
  have wordsB : val32 b.mem g.W (g.array 6) (2 * g.w) = val32 b.mem g.W (g.array 6) k := by
    rw [show 2 * g.w = k + (2 * g.w - k) by omega, VG.Proof.Mont.val32_append, Zb,
      Nat.mul_zero, Nat.add_zero]
  refine WP.mono (WitnessSample.codeAt_ok B.ready.scratch (by have := v.minWidth; omega) two
    (by omega)
    (by omega)
    (by have := v.arrayFit (j := 0) (by decide); unfold Geometry.words at this; omega)
    (Or.inr (by have := g.arrayBefore (i := 0) (j := 6) (by decide); unfold Geometry.words at this; omega))
    B.ready.modulus.candidate (wordsB.trans lowB) odd shape (Nat.mod_lt _ (Nat.two_pow_pos _)))
    fun t ⟨Vt, mask, Ot, Kt⟩ => ?_
  rw [VG.Proof.RsaKeyGen.witness_mod shape] at Vt mask
  have Ot' : Outside g.W (g.array 6) (4 * g.words) b.mem t.mem := by
    rw [show 4 * g.words = 8 * g.w by unfold Geometry.words; omega]
    exact Ot
  exact ⟨WitnessMont.data_outside v B Ot' Kt (by unfold WitnessSample.clob; decide)
    (by unfold WitnessSample.clob; decide), Vt, mask,
    ((Oa.mono (by omega) (by omega)).trans
      (Ob.mono (by omega) (by omega))).trans Ot',
    ((K.mono (by unfold clob; decide)).widen Kb).widen Kt⟩

theorem code_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) {input : Import.Geometry}
    (C : Import.Context input s) (width : input.count = g.words)
    (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst)
    (odd : c % 2 = 1) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * g.w) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessLoad.code g.w) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (8 * g.w)))
      Prepare.Data g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = sampled.1 ∧
      t.gpr .eax = cmask sampled.2 ∧ Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps clob s t :=
  codeAt_ok v S C (by rw [width]; unfold Geometry.words; omega) (by have := v.minWidth; omega)
    (by rw [width]; unfold Geometry.words; omega) (by rw [width])
    source destination odd (by rw [shape]; omega)

end VG.Proof.RsaKeyGen.X86.WitnessLoad
