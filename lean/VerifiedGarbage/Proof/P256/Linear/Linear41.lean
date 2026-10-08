import VerifiedGarbage.Proof.P256.Linear.FortyOneCertificate

namespace VG.Proof.P256.Linear
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

theorem linear41_ok {s : State} {base : Addr} (hs : Scr s base 8192)
    (ha : wordsVal s.mem base 928 4<p) (hb : wordsVal s.mem base 960 4<p) :
    WP isa (.block (Impl.P256.Linear.linear41 512 928 960)) s fun t =>
      KeepRegs (clob 4) s t ∧ Outside base 512 32 s.mem t.mem ∧
      wordsVal t.mem base 512 4<p ∧
      wordsVal t.mem base 512 4=(4*wordsVal s.mem base 928 4+p-wordsVal s.mem base 960 4)%p := by
  have hb1 : ∀i∈FortyOneCertificate.original,instrBound i≤8192 := by decide +kernel
  have hb2 : ∀i∈FortyOneCertificate.optimized,instrBound i≤8192 := by decide +kernel
  have hc : ∀r∈FortyOneCertificate.optimized.flatMap instrClob,r∈clob 4 := by decide +kernel
  refine WP.mono (FortyOneCertificate.checked.refine (by decide) (by decide) hs hb1 hb2
    (FortyOne.reference_ok hs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha hb))
    fun t ⟨u,⟨_,ho,he⟩,hm,hk⟩ => ?_
  refine ⟨hk.mono hc,?_,?_,?_⟩
  · simpa only [hm] using ho
  · rw [hm,he]; exact Nat.mod_lt _ (by decide)
  · simpa only [hm] using he
end VG.Proof.P256.Linear
