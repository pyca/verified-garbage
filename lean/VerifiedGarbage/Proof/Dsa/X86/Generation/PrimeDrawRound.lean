module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeResult
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeDraw
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeResultReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRound
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeSample

/-! # One complete witness draw, sample, primality round and decision -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation VG.Proof.Ecdsa.X86

def primeDrawValue (G : PrimeConfig) (mem : Mem) (used : Nat) : Nat × Bool :=
  Spec.RsaKeyGen.witness (G.modulus - 1) (Spec.Dsa.decodeBE
    (Spec.Rsa.bytesAt mem (off (G.tape.setWidth 64) (used + (G.draw - G.len))) G.len))

theorem primeDrawRound_ok {G : PrimeConfig} {s : State} {used uniform : Nat} (R : PrimeReady G s)
    (full : used + G.draw ≤ G.tapeLen) (bound : uniform + 1 < 2 ^ 32)
    (consumed : s.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 used)
    (count : s.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 uniform) :
    WP isa (primeDrawRound G.len G.draw G.checks) s fun t =>
      let w := primeDrawValue G s.mem used
      let passed := Spec.RsaKeyGen.mrIteration G.modulus G.twos G.exponent w.1
      PrimeReady G t ∧
      t.mem.readW (off G.base primeStatus) 32 =
        BitVec.ofNat 32 (primeResultStatus passed (uniform + w.2.toNat) G.checks) ∧
      t.mem.readW (off G.base primeUniform) 32 =
        BitVec.ofNat 32 (if passed then uniform + w.2.toNat else uniform) ∧
      t.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 (used + G.draw) ∧
      PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧ Keeps powerClob s t := by
  unfold primeDrawRound
  refine WP.seq (WP.mono (primeDraw_ok R full consumed) fun a ⟨Ra, bytes, useda, pointer, ua, Fa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (primeSample_ok Ra pointer) fun b ⟨Rb, value, flag, usedb, ub, Fb, Kb⟩ => ?_)
  rw [bytes] at value flag
  change wordsVal b.mem G.base (slot G.n 5) G.n = (primeDrawValue G s.mem used).1 at value
  change b.mem.readW (off G.base primeIsUniform) 32 = mask32 ((primeDrawValue G s.mem used).2 = true) at flag
  refine WP.seq (WP.mono (primeRound_ok Rb) fun c ⟨Rc, answer, controls, Fc, Kc⟩ => ?_)
  rw [value] at answer
  refine WP.mono (primeResultReady_ok Rc bound answer
    ((controls _ (.inr (.inr rfl))).trans flag)
    ((controls _ (.inr (.inl rfl))).trans (ub.trans (ua.trans count))))
    fun t ⟨Rt, status, uniformt, usedt, Ft, Kt⟩ => ?_
  exact ⟨Rt, status, uniformt, usedt.trans ((controls _ (.inl rfl)).trans (usedb.trans useda)),
    ((Fa.trans Fb).trans Fc).trans Ft,
    (((Ka.mono (by decide)).trans (Kb.mono (by decide))).trans Kc).trans (Kt.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
