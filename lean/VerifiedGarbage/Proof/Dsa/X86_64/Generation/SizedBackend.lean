module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sized
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BackendVerified
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BackendCorrect
import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256

/-! # One active hash backend for each restricted generation helper

The opposite hash below is only a proof witness for the original two-hash
verification theorem. `single128`, `single256` and `single384` prove that
it does not occur in the emitted helper code. Backend selection remains
fully generic over the active hash and Miller–Rabin implementations.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation.Sized
open VG VG.X86_64 VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64


variable {checkName : String}

private def sha1Witness : MdHash := VG.Proof.Pbkdf2.Md.X86_64.Sha1.variant .scalar
private def sha256Witness : MdHash := VG.Proof.Variants.MdHash.X86_64.Sha256.variant

theorem large_width {p : Nat} (h : p ∈ ([256, 384] : List Nat)) : p = 256 ∨ p = 384 := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

theorem sha1_verified (h : MdHash) (v : RoundImpl) (hh : h.mgf.G.rust = "sha1") :
    Verified target (Impl.Dsa.X86_64.Generation.Sized.single (checkName := checkName) 128 h.H.stream
      v.inlineMont.toS.mm v.inlineMont.mm (Kernel.called v).run)
      (Spec.Dsa.GenerationSized.contract 128 abi 472) := by
  have hv := verified (checkName := checkName) h.H.stream sha256Witness.H.stream v.inlineMont.toS.mm v.inlineMont.mm
    (Kernel.called v).run (backend_verified (checkName := checkName) h sha256Witness v hh rfl) 128 (Or.inl rfl)
  rw [← single128] at hv
  exact hv

theorem sha1_safe (h : MdHash) (v : RoundImpl) :
    (Impl.Dsa.X86_64.Generation.Sized.single (checkName := checkName) 128 h.H.stream
      v.inlineMont.toS.mm v.inlineMont.mm (Kernel.called v).run).all (fun i => !isa.writesSp i) = true := by
  have hs := code_all (checkName := checkName) h.H.stream sha256Witness.H.stream v.inlineMont.toS.mm v.inlineMont.mm
    (Kernel.called v).run 128 (fun i => !isa.writesSp i) (backend_safe (checkName := checkName) h sha256Witness v).sp
  rw [← single128] at hs
  exact hs

theorem sha256_verified (h : MdHash) (v : RoundImpl) (hh : h.mgf.G.rust = "sha256")
    (pBytes : Nat) (hp : pBytes = 256 ∨ pBytes = 384) :
    Verified target (Impl.Dsa.X86_64.Generation.Sized.single (checkName := checkName) pBytes h.H.stream
      v.inlineMont.toS.mm v.inlineMont.mm (Kernel.called v).run)
      (Spec.Dsa.GenerationSized.contract pBytes abi 472) := by
  have hv := verified (checkName := checkName) sha1Witness.H.stream h.H.stream v.inlineMont.toS.mm v.inlineMont.mm
    (Kernel.called v).run (backend_verified (checkName := checkName) sha1Witness h v rfl hh) pBytes (Or.inr hp)
  rcases hp with rfl | rfl
  · rw [← single256] at hv
    exact hv
  · rw [← single384] at hv
    exact hv

theorem sha256_safe (h : MdHash) (v : RoundImpl) (pBytes : Nat) (hp : pBytes = 256 ∨ pBytes = 384) :
    (Impl.Dsa.X86_64.Generation.Sized.single (checkName := checkName) pBytes h.H.stream
      v.inlineMont.toS.mm v.inlineMont.mm (Kernel.called v).run).all (fun i => !isa.writesSp i) = true := by
  have hs := code_all (checkName := checkName) sha1Witness.H.stream h.H.stream v.inlineMont.toS.mm v.inlineMont.mm
    (Kernel.called v).run pBytes (fun i => !isa.writesSp i) (backend_safe (checkName := checkName) sha1Witness h v).sp
  rcases hp with rfl | rfl
  · rw [← single256] at hs
    exact hs
  · rw [← single384] at hs
    exact hs

end VG.Proof.Dsa.X86_64.Generation.Sized
