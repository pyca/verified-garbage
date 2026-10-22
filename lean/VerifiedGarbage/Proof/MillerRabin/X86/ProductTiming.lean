module

public import VerifiedGarbage.Proof.MillerRabin.X86.ProductCall

/-! # Timing of a borrowed Montgomery call from public argument construction -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)
open VG.Proof.Bignum.X86.PublicRt (rtPub_of calleeOf_eq rtPre_of)

def ProductInput (base : Addr) (bytes w : Nat) (sp len : BitVec 32) (b : Nat) (s : State) : Prop :=
  PieceInput base bytes w sp len s ∧
    (val32 s.mem base 256 (2 * w) * w32 s.mem base 56 + 1) % 2 ^ 32 = 0 ∧
    val32 s.mem base (arrAt w b) (2 * w) < val32 s.mem base 256 (2 * w)

theorem product_relCT {base : Addr} {bytes w o a b : Nat} {sp len : BitVec 32}
    (size : bytes = len.toNat * 8) (hw : 4 ≤ w) (hu : w ≤ 128) (hf : arrAt w 28 ≤ bytes)
    (ho : 5 ≤ o ∧ o < 28) (ha : 5 ≤ a ∧ a < 28) (hb : 5 ≤ b ∧ b < 28)
    (cert : ∃ hc, (VG.Taint.check VG.X86.taint argsTaint (.block (productArgs o a b)) hc).isSome = true) :
    RelCT isa (fun s t => ProductInput base bytes w sp len b s ∧ ProductInput base bytes w sp len b t)
      (product o a b) (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := cert
  unfold product
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  let P := fun f₁ f₂ => ∃ s₁ s₂,
    (ProductInput base bytes w sp len b s₁ ∧ ProductInput base bytes w sp len b s₂) ∧
    f₁ = allocFrame 36 s₁ ∧ f₂ = allocFrame 36 s₂
  have argsCT : RelCT isa P (.block (productArgs o a b)) (fun _ _ => True) :=
    RelCT.taint (A := taint) argsTaint (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂⟩, eq₁, eq₂⟩ => by
      subst eq₁ eq₂
      exact h₁.1.agree_args h₂.1) checked
  have argsPost := argsCT.wp (F₁ := ProductCall base bytes w sp len o a b)
    (F₂ := ProductCall base bytes w sp len o a b) (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂⟩, eq₁, eq₂⟩ => by
      subst eq₁ eq₂
      exact ⟨product_call_setup h₁.1 size hw hu hf ho ha hb h₁.2.1 h₁.2.2,
        product_call_setup h₂.1 size hw hu hf ho ha hb h₂.2.1 h₂.2.2⟩)
  refine VG.RelCT.seq argsPost ?_
  exact VG.Proof.Bignum.X86.RtCall.call_ct.mono
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩) (fun _ _ _ => trivial)

end VG.Proof.MillerRabin.X86
