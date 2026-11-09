module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeySetup
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyVec
import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyTemp
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
open VG.Impl.Aes.KeyWords (rc)

theorem CopyInv.write0 {base s : State} {P S : Addr} {K c : Nat} (h : CopyInv base P S K c s) (x : BitVec 64) :
    CopyInv base P S K c (s.write .r0 x) := by
  have l := Local.write s .r0 x
  exact ⟨h.bound, (h.keep.trans l.keep).mono (by simp), (l.keep.gpr (by decide)).trans h.ptr,
    (l.keep.gpr (by decide)).trans h.out, (l.keep.gpr (by decide)).trans h.left,
    by rw [l.mem]; exact h.copied, by rw [l.mem]; exact h.frame⟩

theorem li4_ok (s : State) (k : Nat) (hk : k < 2^15) :
    WP isa (.block [.li .r4 k]) s (· = s.write .r4 (BitVec.ofNat 64 k)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, hk, ite_true, Option.some.injEq, exists_eq_left']

/-- The start of a vector loop: `r4` its count. -/
theorem VStart.vinv4 {base s : State} {P S : Addr} (h : VStart base P S 4 s) (x : BitVec 64) :
    VInv4 base P S 0 ((s.write .r0 x).write .r4 (BitVec.ofNat 64 10)) := by
  have l := (Local.write s .r0 x).trans (Local.write _ .r4 (BitVec.ofNat 64 10))
  exact ⟨by decide, (h.keep.trans l.keep).mono (by simp [keyGprs]), h.cst.of_keep l.keep (by simp)
    (fun r _ => l.v r (by simp)), (l.keep.gpr (by decide)).trans h.out, RegUpd.gpr_write_self ..,
    (l.keep.gpr (by decide)).trans h.rcon, by rw [l.v _ (by simp)]; exact h.keyA,
    by rw [l.mem]; exact h.good, by rw [l.mem]; exact h.frame⟩

theorem VStart.vinv8 {base s : State} {P S : Addr} (h : VStart base P S 8 s) (x : BitVec 64) :
    VInv8 base P S 0 ((s.write .r0 x).write .r4 (BitVec.ofNat 64 6)) := by
  have l := (Local.write s .r0 x).trans (Local.write _ .r4 (BitVec.ofNat 64 6))
  exact ⟨by decide, (h.keep.trans l.keep).mono (by simp [keyGprs]), h.cst.of_keep l.keep (by simp)
    (fun r _ => l.v r (by simp)), (l.keep.gpr (by decide)).trans h.out, RegUpd.gpr_write_self ..,
    (l.keep.gpr (by decide)).trans h.rcon, by rw [l.v _ (by simp)]; exact h.keyA,
    by rw [l.v _ (by simp)]; exact h.keyB rfl, by rw [l.mem]; exact h.good, by rw [l.mem]; exact h.frame⟩

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
  suffices H : WP isa (.seq (.block [.subi .r0 .r7 24])
      (.ite (.zero .d .r0) Impl.Aes.PPC64LE.Crypto.wordTail Impl.Aes.PPC64LE.Crypto.vecTail)) u
      (fun t => Keep keyGprs base t ∧ VG.Proof.Aes.KeyWords.Good t.mem S (VG.Proof.Aes.KeyWords.W base.mem P nk)
        (4*(nk+7))) by
    refine WP.mono H fun t ⟨htk, htg⟩ => ⟨?_, ?_⟩
    · exact (he.keep.trans htk).mono (by simp [keyGprs])
    · have hbytes := VG.Proof.Aes.KeyWords.bytesAt_eq t.mem S (VG.Proof.Aes.KeyWords.W base.mem P nk)
        (4*(nk+7)) htg
      have hexpand := VG.Proof.Aes.KeyWords.expandKey_eq base.mem P hnk.1
      have hrounds : Spec.Aes.rounds nk = nk+6 := rfl
      rw [hrounds, show nk+6+1 = nk+7 by omega] at hexpand
      have hout := hbytes.trans hexpand.symm
      rw [he.mem, hkn] at hout
      have hlen : 16*(Spec.Aes.rounds nk+1) = 4*(4*(nk+7)) := by rw [hrounds]; omega
      change Spec.Aes.bytesAt t.mem S (16*(Spec.Aes.rounds nk+1)) = _
      rw [hlen]
      exact hout
  have h7' : (u.write .r0 (u.gpr .r7 - BitVec.ofNat 64 24)).gpr .r7 = BitVec.ofNat 64 (4*nk) :=
    ((Local.write u .r0 _).keep.gpr (by decide)).trans h7
  refine test_choice .r7 (4*nk) 24 u _ _ _ (by decide) (by omega) (by decide) h7 (fun h24 => ?_) (fun h24 => ?_)
  · have hu' := hu.write0 (u.gpr .r7 - BitVec.ofNat 64 24)
    rw [Impl.Aes.PPC64LE.Crypto.wordTail]
    refine WP.seq (WP.mono (wordSetup_ok hcfg hu' h7') fun v hv => ?_)
    refine WP.seq (WP.mono (prev_load_ok hcfg hv) fun w hw => ?_)
    exact WP.mono (word_loop_ok hcfg hw.1 hw.2 (by omega)) fun t ht => ⟨ht.keep, ht.good⟩
  · have h48 : nk = 4 ∨ nk = 8 := by omega
    have hu' := hu.write0 (u.gpr .r7 - BitVec.ofNat 64 24)
    have hdiv : 8*((4*nk)/8) = 4*nk := by omega
    rw [Impl.Aes.PPC64LE.Crypto.vecTail]
    refine WP.seq (WP.mono (vecSetup_ok hcfg h48 (hu'.keep.mono (by simp [keyGprs]))
      (by simpa only [hdiv] using hu'.out) h7' (by rw [RegUpd.mem_write]; exact copied_good hu hdiv) hu'.frame)
      fun v hv => ?_)
    refine test_choice .r7 (4*nk) 16 v _ _ _ (by decide) (by omega) (by decide) hv.len (fun h16 => ?_) (fun h16 => ?_)
    · have h4 : nk = 4 := by omega
      have hc4 : KeyConfig base P S 16 := by rw [show (16 : Nat) = 4 * nk by omega]; exact hcfg
      rw [h4] at hv ⊢
      rw [Impl.Aes.PPC64LE.Crypto.loop128]
      refine WP.seq (WP.mono (li4_ok _ 10 (by decide)) fun w hw => ?_)
      subst hw
      exact WP.mono (loop128_ok hc4 (hv.vinv4 _)) fun t ht => ⟨ht.keep, ht.good⟩
    · have h8 : nk = 8 := by omega
      have hc8 : KeyConfig base P S 32 := by rw [show (32 : Nat) = 4 * nk by omega]; exact hcfg
      rw [h8] at hv ⊢
      rw [Impl.Aes.PPC64LE.Crypto.loop256]
      refine WP.seq (WP.mono (li4_ok _ 6 (by decide)) fun w hw => ?_)
      subst hw
      exact loop256_ok hc8 (hv.vinv8 _)

end VG.Proof.Aes.PPC64LE.Crypto
