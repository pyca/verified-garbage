module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SizedBackend
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SharedChecker
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Emit

/-! # Share parameter generation by modulus width and its active hash -/

@[expose] public section
namespace VG.Generic.MdHash.MillerRabin.X86_64.DsaGeneration
open VG.Proof.Dsa.X86_64.Generation.Sized VG.Proof.MillerRabin.X86_64

def artifacts (h : Proof.Pbkdf2.Md.X86_64.MdHash) (v : RoundImpl) : List Artifact :=
  let features := h.features ++ v.features.filter (!h.features.contains ·)
  if hh : h.mgf.G.rust = "sha1" then
    [(Spec.Dsa.GenerationSized.api 128).artifact X86_64.target {
      suffix := Emit.qualifiedName "" [("sha1", h.suffix), ("mr", v.suffix)]
      stack := 536
      code := Impl.Dsa.X86_64.Generation.Sized.single (checkName := VG.Proof.Dsa.X86_64.Generation.SharedChecker.name v) 128 h.H.stream
        v.inlineMont.toS.mm v.inlineMont.mm (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run
      verified := sha1_verified h v hh
      spSafe := sha1_safe h v
      features := features }]
  else if hh : h.mgf.G.rust = "sha256" then
    ([256, 384] : List Nat).attach.map fun (p : { n : Nat // n ∈ ([256, 384] : List Nat) }) =>
      have hp : p.val = 256 ∨ p.val = 384 := large_width p.property
      (Spec.Dsa.GenerationSized.api p.val).artifact X86_64.target {
        suffix := Emit.qualifiedName "" [("sha256", h.suffix), ("mr", v.suffix)]
        stack := 536
        code := Impl.Dsa.X86_64.Generation.Sized.single (checkName := VG.Proof.Dsa.X86_64.Generation.SharedChecker.name v) p.val h.H.stream
          v.inlineMont.toS.mm v.inlineMont.mm (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run
        verified := sha256_verified h v hh p.val hp
        spSafe := sha256_safe h v p.val hp
        features := features }
  else []

end VG.Generic.MdHash.MillerRabin.X86_64.DsaGeneration
