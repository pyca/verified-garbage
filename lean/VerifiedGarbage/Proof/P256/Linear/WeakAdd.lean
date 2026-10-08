import VerifiedGarbage.Proof.P256.Linear.WeakCertificate

namespace VG.Proof.P256.Linear
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

theorem weakAdd_ok {s : State} {base : Addr} (hs : Scr s base 8192)
    (ha : wordsVal s.mem base 512 4<Weak.p) (hb : wordsVal s.mem base 800 4<Weak.p) :
    WP isa (.block (Impl.P256.Linear.weakAdd 864 512 800)) s fun t =>
      KeepRegs (clob 4) s t ∧ Outside base 864 32 s.mem t.mem ∧
      wordsVal t.mem base 864 4<Weak.R ∧
      wordsVal t.mem base 864 4%Weak.p=(wordsVal s.mem base 512 4+wordsVal s.mem base 800 4)%Weak.p := by
  have hb1 : ∀i∈WeakCertificate.original,instrBound i≤8192 := by decide +kernel
  have hb2 : ∀i∈WeakCertificate.optimized,instrBound i≤8192 := by decide +kernel
  have hc : ∀r∈WeakCertificate.optimized.flatMap instrClob,r∈clob 4 := by decide +kernel
  refine WP.mono (WeakCertificate.checked.refine (by decide) (by decide) hs hb1 hb2
    (Weak.reference_ok hs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha hb))
    fun t ⟨u,⟨_,ho,he⟩,hm,hk⟩ => ?_
  refine ⟨hk.mono hc,?_,wordsVal_lt ..,?_⟩
  · simpa only [hm] using ho
  · simpa only [hm] using he
end VG.Proof.P256.Linear
