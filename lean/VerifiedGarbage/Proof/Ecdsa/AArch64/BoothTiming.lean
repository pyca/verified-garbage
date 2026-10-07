import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothLit
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.EcKey.AArch64.Verified

namespace VG.Proof.Ecdsa.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
theorem booth_sign_ct : ConstantTime isa signAArch64.pre signAArch64.pub Impl.P256.Booth.sign :=
  VG.Taint.constantTime (A := taintS [p256.tsym]) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

end VG.Proof.Ecdsa.AArch64

namespace VG.Proof.EcKey.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
theorem booth_pk_ct : ConstantTime isa pkAArch64.pre pkAArch64.pub Impl.P256.Booth.publicKey :=
  VG.Taint.constantTime (A := taintS [p256.tsym]) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ ⟨h0, h1, h2, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

end VG.Proof.EcKey.AArch64
