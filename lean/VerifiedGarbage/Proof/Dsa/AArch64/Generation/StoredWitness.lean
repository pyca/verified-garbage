module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Sample
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ForceWitness
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusWords
import VerifiedGarbage.Proof.Framework.Omega

/-! Force a stored witness while retaining every prepared modulus word. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Proof.MlKem.AArch64

theorem forceStoredWitness_ok {s : State} {B p : Addr} {Z w N len : Nat}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hp : word s.mem B (8 * kOut) = p) (hlen : 2 ≤ len) (hmax : len < 4096)
    (hwr : ∀ i < len, InRegions s.wr (off p i) 1)
    (hsep : ∀ i < len, Z ≤ ofs B (off p i)) :
    WP isa (Impl.Dsa.AArch64.Generation.forceStoredWitness len) s fun t =>
      ModulusReady t B Z w N ∧
      Spec.Rsa.bytesAt t.mem p len = VG.Proof.Dsa.Generation.forcedWitnessBytes (Spec.Rsa.bytesAt s.mem p len) ∧
      (∀ a, (∀ i < len, a ≠ off p i) → t.mem a = s.mem a) ∧
      (∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d) ∧ Keep [.x1, .x3, .x4] s t := by
  unfold Impl.Dsa.AArch64.Generation.forceStoredWitness
  apply WP.block_append_iff.mpr
  refine WP.mono (WP.keep [.x1] (Q := fun u => u.gpr .x1 = p ∧ u.mem = s.mem)
    (by
      brun [h.ws.x0, hdr_enc (show kOut < 32 by decide), hp,
        h.ws.scr.ld (d := 8 * kOut) (by have := h.ws.h256; simp only [kOut, sFn]; omega)])
    rfl rfl rfl) fun u ⟨⟨hu1, hum⟩, ku⟩ => ?_
  have hwu : ∀ i < len, InRegions u.wr (off p i) 1 := by
    intro i hi; rw [ku.wr]; exact hwr i hi
  have hru : ∀ i < len, InRegions (u.rd ++ u.wr) (off p i) 1 := by
    intro i hi
    obtain ⟨r, hr, hc⟩ := hwu i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (forceWitness_ok hlen hmax hu1 hru hwu) fun t ⟨htm, kt⟩ => ?_
  have hmfinal : t.mem = (s.mem.writeW p (s.mem p &&& (127 : Byte))).writeW
      (off p (len - 1)) (s.mem (off p (len - 1)) ||| (2 : Byte)) := by rw [htm, hum]
  have hf : ∀ a, (∀ i < len, a ≠ off p i) → t.mem a = s.mem a := by
    intro a ha
    have hzero : a ≠ p := by simpa only [off, BitVec.add_zero] using ha 0 (by omega)
    rw [hmfinal, WriteBytes.writeW8_apply, ite_eq_right (ha (len - 1) (by omega)),
      WriteBytes.writeW8_apply, ite_eq_right hzero]
  have hwords := words_outside_bytes (by have := h.ws.scr.nowrap; omega : Z ≤ 2 ^ 64) hf hsep
  have k := ku.trans kt
  refine ⟨h.of_words hEZ hwords k.wr ((k.gpr .x0 (by decide)).trans h.ws.x0), ?_, hf, hwords,
    k.mono (by decide)⟩
  rw [hmfinal, VG.Proof.Dsa.Generation.forcedWitness_memory s.mem p hlen (by omega)]

end VG.Proof.Dsa.AArch64.Generation
