module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrimeCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArgumentBlocksCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrimeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime

/-! # Return the native primality cursor and status to the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Dsa.X86_64.Generation

def PrimeFramePublic.pointers (p : PrimeFramePublic) : ArgumentPointers :=
  ⟨p.bytes.call.draw.prime.B, p.bytes.call.draw.prime.sp⟩

theorem checkPrime_return {M : Mont} {K : Kernel} {w candidate len draw checks : Nat}
    {p : PrimeFramePublic} {s : State} (h : CheckPrimeBefore w candidate len draw checks p s) :
    WP isa (checkPrime M.mm K.run w candidate len draw checks) s (ArgumentRegisters p.pointers) := by
  have hw := checkPrime_ok M K h.2.1 h.2.2.1 p.candidateBound p.checksBound h.1.stack h.1.read
    (W := fun k => word s.mem p.bytes.call.draw.prime.sp (8 * k)) (fun _ _ => rfl) p.separate p.outside
    (by change word s.mem p.bytes.call.draw.prime.sp 40 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.witness = _
        rw [h.1.arena, p.witness])
    h.1.tapePtr h.1.tapeLength h.1.used h.1.tape h.1.writable p.bytes.length p.bytes.value
    (by simpa only [h.1.arena, ← p.source] using h.1.source)
    h.1.usedBound p.bytes.call.width p.bytes.call.tab p.bytes.call.large p.bytes.call.policy p.checks
  rw [h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2] at hw
  exact WP.mono hw fun _ ⟨mi, used, ht, _, _, _, _, hk⟩ =>
    ⟨ht.good.rdi, (hk.gpr (by decide)).trans h.1.stack⟩

theorem checkPrimeReturn_ct (M : Mont) (K : Kernel) (w candidate len draw checks : Nat)
    (hwidth : PrimeWidths len draw) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi]) (workspace w) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .rsp])
      (.block (headerArguments (primeArguments candidate len draw checks))) hc₂).isSome = true) :
    RelCT isa (Two (CheckPrimeBefore w candidate len draw checks))
      (.seq (checkPrime M.mm K.run w candidate len draw checks) (.block primeResult)) (fun _ _ => True) :=
  RelCT.seq (two_post (checkPrime_ct M K w candidate len draw checks hwidth ht₁ ht₂)
    (fun _ _ h => checkPrime_return h))
    (two_map PrimeFramePublic.pointers (fun _ _ h => h) primeResult_ct)

end VG.Proof.Dsa.X86_64.Generation
