module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeSetup
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! # Montgomery setup for DSA's full and padded prime candidates -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Proof.RsaKeyGen.X86_64

theorem primeR2_ok (M : Mont) {s : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw48 : w ≤ 48)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hN : 1 < N) :
    WP isa (Impl.Dsa.X86_64.Generation.primeR2 M.mm) s fun t => ∃ mi', Good t B Z w mi' ∧
      ((word t.mem B (slot w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t.mem B (slot w aN) w = N ∧ wv t.mem B (slot w aOne) w = 1 ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aR2) w < N ∧ Frm B (prepareRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := hg.scr.nowrap
  have hN8 := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hodd0 : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 (n := w) _ _ _ (by omega), hn, Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide)]
    exact hodd
  unfold Impl.Dsa.X86_64.Generation.primeR2
  refine WP.seq (WP.mono (msHead_ok hg hZ hodd0) fun u ⟨hgu, hinv, _, _, _, hmu, ku⟩ => ?_)
  have hnu : wv u.mem B (slot w aN) w = N := by
    rw [hmu, hdrStore_wv _ _ _ (by decide) (by decide) (by omega)]
    exact hn
  have hwu : word u.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [hmu, hdrStore_word _ _ _ (by decide) (by decide) (by omega)]
  refine WP.mono (VG.Proof.Dsa.X86_64.constants_ok M hgu hZ hw hw48 hnu hN hodd (by rw [hwu]; exact hinv))
    fun t ⟨hgt, hone, hr2, hf, kt⟩ => ?_
  have hsep := VG.Proof.Dsa.X86_64.constantRanges_modulus w
  have hnt : wv t.mem B (slot w aN) w = N := by
    rw [hf.wv_eq (fun r hr => by have := hsep r hr; omega) (by omega)]
    exact hnu
  have hwt : word t.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [hf.word_eq (fun r hr => by have := hsep r hr; omega) (by omega), hwu]
  refine ⟨u.gpr .r15, hgt, by rw [hwt]; exact hinv, hnt, hone, ?_, ?_, ?_, (ku.trans kt).mono (by decide)⟩
  · rw [hr2, ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega]
  · rw [hr2]
    exact Nat.mod_lt _ (by omega)
  · have hhead : Frm B [(8 * sMinv, 8)] s.mem u.mem := by
      rw [hmu]
      exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
    exact hhead.append hf

end VG.Proof.Dsa.X86_64.Generation
