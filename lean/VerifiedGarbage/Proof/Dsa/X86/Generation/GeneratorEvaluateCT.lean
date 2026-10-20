module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorPowerCT
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorEvaluate
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorExponent

/-! # Loading the public quotient exponent before generator evaluation -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

structure GeneratorEvaluatePublic where
  power : GeneratorPublic
  input : BitVec 32

structure GeneratorEvaluateAt (len : Nat) (p : GeneratorEvaluatePublic) (s : State) : Prop where
  context : Context ((len + 7) / 8) p.power.modulus p.power.base p.power.size s
  width : (len + 7) / 8 ≤ 48
  words : len % 4 = 0
  one : wordsVal s.mem p.power.base (slot ((len + 7) / 8) 3) ((len + 7) / 8) = 1
  r2 : wordsVal s.mem p.power.base (slot ((len + 7) / 8) 4) ((len + 7) / 8) = 2 ^ (128 * ((len + 7) / 8)) % p.power.modulus
  value : wordsVal s.mem p.power.base (slot ((len + 7) / 8) 5) ((len + 7) / 8) = p.power.value
  exponent : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.input.setWidth 64) len) = p.power.exponent
  pointer : s.gpr .esi = p.input
  fit : p.input.toNat + len ≤ 2 ^ 32
  read : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) (off (p.input.setWidth 64) d) 4
  apart : Region.Disjoint ⟨p.input.setWidth 64, len⟩ ⟨p.power.base, p.power.size⟩

theorem generatorLoadExponent_ct (len : Nat) (minimum : 4 ≤ len) :
    RelCT isa (Two (GeneratorEvaluateAt len))
      (VG.Impl.Dsa.X86.loadComponent len ((len + 7) / 8) (slot ((len + 7) / 8) 8))
      (Two fun (p : GeneratorEvaluatePublic) => GeneratorPowerAt ((len + 7) / 8) p.power) := by
  refine two_post ((loadComponent_relCT _ _ _).mono ?_ (fun _ _ _ => trivial)) ?_
  · rintro s t ⟨p, hs, ht⟩
    apply agree_regs
    intro r hr
    have cases : r = .edi ∨ r = .esi := by simpa [workspaceTaint] using hr
    rcases cases with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (hs.context.scr.edi_toNat.trans ht.context.scr.edi_toNat.symm)
    · exact hs.pointer.trans ht.pointer.symm
  · intro p s R
    refine WP.mono (generatorExponent_ok R.context minimum (by omega) R.words
      (by rw [R.pointer]; exact R.fit) (fun d hd => by rw [R.pointer]; exact R.read d hd)
      (by rw [R.pointer]; exact R.apart)) fun t ⟨C, exponent, saved, _, _⟩ => ?_
    rw [R.pointer, R.exponent] at exponent
    exact ⟨C, R.width, (saved 3 (by decide)).trans R.one, (saved 4 (by decide)).trans R.r2,
      (saved 5 (by decide)).trans R.value, exponent⟩

theorem generatorEvaluate_ct (len : Nat) (minimum : 4 ≤ len) :
    RelCT isa (Two (GeneratorEvaluateAt len)) (generatorEvaluate len) (fun _ _ => True) :=
  RelCT.seq (generatorLoadExponent_ct len minimum)
    (two_map GeneratorEvaluatePublic.power (fun _ _ h => h) (generatorPower_ct ((len + 7) / 8) (by omega)))
end VG.Proof.Dsa.X86.Generation
