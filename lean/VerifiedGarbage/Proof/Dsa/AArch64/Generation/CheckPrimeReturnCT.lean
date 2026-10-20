module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrimeCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrime
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrimeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrime
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash

/-! # Return the native primality cursor and status to the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation


theorem checkPrime_return {M : Mont} {K : Kernel} {w candidate len draw checks : Nat}
    {p : PrimeFramePublic} {s : State} (h : CheckPrimeBefore w candidate len draw checks p s) :
    WP isa (checkPrime M.mm K.run w candidate len draw checks) s (fun t => t.gpr .x0 = p.bytes.call.draw.prime.B) := by
  have hw := checkPrime_ok M K h.2.1 h.2.2.1 p.candidateBound p.checksBound h.1.stack h.1.read
    (W := fun k => VG.Proof.Bignum.word s.mem p.F (8 * k)) (fun _ _ => rfl) p.separate p.outside
    (by change VG.Proof.Bignum.word s.mem p.F 40 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.witness = _
        rw [h.1.arena, p.witness])
    h.1.tapePtr h.1.tapeLength h.1.used h.1.tape h.1.writable p.bytes.length p.bytes.value
    (by simpa only [h.1.arena, ← p.source] using h.1.source)
    h.1.usedBound p.bytes.call.width p.bytes.call.tab p.bytes.call.large p.bytes.call.policy p.checks
  rw [h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2] at hw
  exact WP.mono hw fun _ ⟨used, ht, _, _, _, _, _⟩ => ht.ws.x0

theorem checkPrimeReturn_ct (M : Mont) (K : Kernel) (w candidate len draw checks : Nat)
    (hwidth : PrimeWidths len draw) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (workspace w) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (primeArguments candidate len draw checks))) hc₂).isSome = true) :
    RelCT isa (Two (CheckPrimeBefore w candidate len draw checks))
      (.seq (checkPrime M.mm K.run w candidate len draw checks) (.block primeResult)) (fun _ _ => True) :=
  RelCT.seq (two_post (checkPrime_ct M K w candidate len draw checks hwidth ht₁ ht₂)
    (fun _ _ h => checkPrime_return h))
    (two_taint [.x0] (fun _ _ _ hs ht r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hs.trans ht.symm) (by taint_decide))

end VG.Proof.Dsa.AArch64.Generation
