module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.ProbablePrime
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-!
# DSA's probable-prime test on PPC64LE: the contract's precondition

`CIn bits s`: the contract's precondition (with the table's region readable
too, `CIn.ofStrip`), as the proofs use it (`cin_of_pre`). `Bits`: the widths of DSA's primes, and
`Shape`: what the code needs of each (`shape_of`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime

/-- The widths of DSA's primes. -/
abbrev Bits (bits : Nat) : Prop := bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072

/-- The arguments' regions. -/
abbrev cW (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩
abbrev cR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev cU (s : State) : Region := ⟨s.gpr .r7, 8⟩
abbrev cS (s : State) : Region := ⟨s.sp - 176#64, 176⟩

/-- The contract's precondition. -/
structure CIn (bits : Nat) (s : State) : Prop where
  spLo : 176 ≤ s.sp.toNat
  rd : cR s ∈ s.rd
  wr : s.wr = [cW s, cU s]
  wR : (cW s).Disjoint (cR s)
  wU : (cW s).Disjoint (cU s)
  rU : (cR s).Disjoint (cU s)
  sW : (cS s).Disjoint (cW s)
  sR : (cS s).Disjoint (cR s)
  sU : (cS s).Disjoint (cU s)
  fw : (s.gpr .r3).toNat + (s.gpr .r4).toNat * 8 ≤ 2 ^ 64
  fr : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  fu : (s.gpr .r7).toNat + 8 ≤ 2 ^ 64
  size : keyOff + 8 * keyWords bits ≤ 8 * (s.gpr .r4).toNat
  odd : Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (s.gpr .r3) % 2 = 1
  bl : Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (s.gpr .r3)) = bits

theorem cin_of_pre (bits : Nat) (s : State) (h : (Proof.Dsa.ProbablePrime.contract (layout bits) abi 176).pre s) :
    CIn bits s := by
  sig_pre [Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs] at h
  obtain ⟨spLo, rd, wr, wR, wU, rU, sW, sR, sU, fw, fr, fu, size, odd, bl⟩ := h
  exact ⟨spLo, by rw [rd]; exact List.mem_singleton_self _, wr, wR, wU, rU, sW, sR, sU, fw, fr, fu, size, odd, bl⟩

/-- What the code needs of a width: the immediates fit, and the witness's
top word is word `t` with `b` bits. -/
structure Shape (bits : Nat) : Prop where
  w4 : 4 ≤ words bits
  w48 : words bits ≤ 48
  kw : keyWords bits < 2 ^ 15
  hlen : len bits = bits / 8
  hlen8 : 8 * len bits = bits
  hlenw : len bits ≤ 8 * words bits
  hlen1 : 1 ≤ len bits
  t0 : 0 < (bits - 1) / 64
  tw : (bits - 1) / 64 < words bits
  b1 : 1 ≤ topBits bits
  b64 : topBits bits ≤ 64
  bt : bits = 64 * ((bits - 1) / 64) + topBits bits
  hdraw : draw bits = 8 * ((bits - 1) / 64 + 1)
  hoff : topOff bits = 8 * ((bits - 1) / 64)
  hchecks : checks bits = Spec.Dsa.primeChecks bits
  hcount : count bits = if words bits ≤ 16 then 512 else 1024
  stride : 8 * (words bits + 2) < 2 ^ 15
  arr7 : 256 + 7 * (8 * (words bits + 2)) < 2 ^ 15
  big : 13 ≤ bits - 1
  key : keyWords bits = 32 + 28 * (words bits + 2)
  maskb : 64 - topBits bits < 64
  wbits : 64 * words bits = bits ∨ (bits = 160 ∧ words bits = 4)

theorem shape_of {bits : Nat} (hb : Bits bits) : Shape bits := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end VG.Proof.Dsa.PPC64LE.Prime
