module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeySetup
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the same key-expansion program satisfies APIs with and without a scratch argument.
/-! # POWER8 AES key-expansion correctness -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE

theorem expandKey_ok (s : State) (hc : KeyConfig s (s.gpr .r3) (s.gpr .r5) (s.gpr .r4).toNat) :
    WP isa Impl.Aes.PPC64LE.Crypto.expandKey s fun t => Keep keyGprs s t ∧
      Spec.Aes.bytesAt t.mem (s.gpr .r5) (16*(Spec.Aes.rounds ((s.gpr .r4).toNat/4)+1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) := by
  let K := (s.gpr .r4).toNat
  let nk := K/4
  let P := s.gpr .r3
  let S := s.gpr .r5
  have hK : K = 16 ∨ K = 24 ∨ K = 32 := hc.length
  have hkn : 4*nk = K := by omega
  have hnk : 0 < nk ∧ nk ≤ 8 := by omega
  have hdiv : 8*((4*nk)/8) = 4*nk := by omega
  rw [Impl.Aes.PPC64LE.Crypto.expandKey]
  have hmov : WP isa (.block [Impl.Aes.PPC64LE.Crypto.mov .r7 .r4]) s (· = s.write .r7 (s.gpr .r4)) := by
    apply WP.of_runBlock
    simp only [Impl.Aes.PPC64LE.Crypto.mov, runBlock_cons, runStep_some, runBlock_nil,
      reduceExec, BitVec.or_self, Option.some.injEq, exists_eq_left']
  refine WP.seq (WP.mono hmov fun base hb => ?_)
  subst base
  let base := s.write .r7 (s.gpr .r4)
  have he : Local [.r7] [] s base := Local.write _ _ _
  have hcfg : KeyConfig base P S (4*nk) := by
    rw [hkn]
    exact ⟨hc.length, by rw [he.keep.2.1, he.keep.2.2]; exact hc.key,
      by rw [he.keep.2.2]; exact hc.schedule, hc.sep⟩
  have hi : CopyInv base P S (4*nk) 0 base := by
    refine ⟨by omega, Keep.refl _ _, ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _⟩
    · rw [he.keep.gpr (by decide)]
      simp only [Nat.mul_zero, BitVec.add_zero]; rfl
    · rw [he.keep.gpr (by decide)]
      simp only [Nat.mul_zero, BitVec.add_zero]; rfl
    · rw [he.keep.gpr (by decide), Nat.mul_zero, Nat.sub_zero, hkn]
      simp only [K, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (copy_loop_ok hcfg hi) fun u hu => ?_)
  have h7 : u.gpr .r7 = BitVec.ofNat 64 (4*nk) := by
    rw [hu.keep.gpr (by decide), hkn]
    simp only [base, RegUpd.gpr_write_self, K, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (wordSetup_ok hcfg hu h7) fun v hv => ?_)
  refine WP.mono (word_loop_ok hcfg hv (by omega)) fun t ht => ⟨?_, ?_⟩
  · exact (he.keep.trans ht.keep).mono (by simp [keyGprs])
  · have hbytes := VG.Proof.Aes.KeyWords.bytesAt_eq t.mem S (VG.Proof.Aes.KeyWords.W base.mem P nk)
      (4*(nk+7)) ht.good
    have hexpand := VG.Proof.Aes.KeyWords.expandKey_eq base.mem P hnk.1
    have hrounds : Spec.Aes.rounds nk = nk+6 := rfl
    rw [hrounds, show nk+6+1 = nk+7 by omega] at hexpand
    have hout := hbytes.trans hexpand.symm
    rw [he.mem, hkn] at hout
    have hlen : 16*(Spec.Aes.rounds nk+1) = 4*(4*(nk+7)) := by rw [hrounds]; omega
    change Spec.Aes.bytesAt t.mem S (16*(Spec.Aes.rounds nk+1)) = _
    rw [hlen]
    exact hout

end VG.Proof.Aes.PPC64LE.Crypto
