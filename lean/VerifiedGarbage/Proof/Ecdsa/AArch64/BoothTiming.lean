module

public import VerifiedGarbage.Proof.EcKey.AArch64.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Contract
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothLit
public import VerifiedGarbage.Impl.P256.Booth
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.EcKey.AArch64.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.EcKey.AArch64.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothLit
meta import VerifiedGarbage.Impl.P256.Booth
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.EcKey.AArch64.Lit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

@[expose] public section

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
