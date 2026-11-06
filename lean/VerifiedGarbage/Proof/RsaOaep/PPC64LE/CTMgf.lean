module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Mgf
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View

/-!
# RSA paddings on PPC64LE: MGF1, twice

Untrusted: everything here is checked by Lean. `pins_mono`: what pins
registers `rs` pins any of them.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo Two Pins two_post wp_li wp_addi wp_mov wp_nil eval_nonzero)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  {Dg src srcLen dst dstLen : Nat}

theorem pins_mono {α : Type} {Φ : α → State → Prop} {rs rs' : List Reg} (h : Pins Φ rs)
    (hs : ∀ r ∈ rs', r ∈ rs := by decide) : Pins Φ rs' := fun a t₁ t₂ h₁ h₂ =>
  ⟨(h a t₁ t₂ h₁ h₂).1, fun r hr => (h a t₁ t₂ h₁ h₂).2 r (hs r hr)⟩

end

end VG.Proof.RsaOaep.PPC64LE
