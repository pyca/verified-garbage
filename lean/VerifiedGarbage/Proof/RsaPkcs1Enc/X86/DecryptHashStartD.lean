module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashMemory

/-! # Initialize SHA-256 while retaining the padded private exponent -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem hashStartD_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {D : List Byte}
    (h : Context g bs s) (bytes : Spec.Rsa.bytesAt s.mem (g.scratch sD g.length).base g.length = D) :
    WP isa (callAfter shaInitArgs (hashFns v).initN (hashFns v).initC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Keeps callClobbers s t ∧
      Spec.Sha256.Repr t.mem (g.scratch sSt 96).base [] ∧
      Spec.Rsa.bytesAt t.mem (g.scratch sD g.length).base g.length = D := by
  have fit : sD + g.length ≤ 8448 := by have := h.valid.maxLength; unfold sD; omega
  unfold callAfter
  refine WP.seq (WP.mono (shaInitArgs_ok h) ?_)
  rintro a ⟨ha, args, Fa, Ka⟩
  have bytesA := (scratchBytes_args h fit Fa).trans bytes
  refine WP.mono (shaInit_call v ha args) ?_
  rintro t ⟨ht, F, Ffine, K, repr⟩
  refine ⟨ht, (argsFrame_hash Fa).trans F, (Ka.mono (by decide)).trans K, repr, ?_⟩
  have kept : Spec.Rsa.bytesAt t.mem (g.scratch sD g.length).base g.length =
      Spec.Rsa.bytesAt a.mem (g.scratch sD g.length).base g.length := by
    apply scratchBytes_callee ha fit Ffine
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact scratchDisjoint g (Or.inr (by decide : sSt + 96 ≤ sD)) fit (by decide : sSt + 96 ≤ 8448)
  exact kept.trans bytesA

end VG.Proof.RsaPkcs1Enc.X86.Dec
