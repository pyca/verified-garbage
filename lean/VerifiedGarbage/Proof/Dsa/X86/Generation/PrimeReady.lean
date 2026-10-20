module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFrame
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFixed

/-! # Stable resources shared by every draw in one candidate's primality test -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

structure PrimeConfig where
  base : Addr
  size : Nat
  len : Nat
  modulus : Nat
  tape : BitVec 32
  tapeLen : Nat
  witness : BitVec 32
  lenMin : 4 ≤ len
  lenMax : len ≤ 384
  lenWords : len % 4 = 0
  modulusBits : Spec.RsaKeyGen.bitLength modulus = 8 * len
  predecessorBits : Spec.RsaKeyGen.bitLength (modulus - 1) = 8 * len
  twosPos : 1 ≤ (Spec.Rsa.splitTwos (modulus - 1)).1
  twosBound : (Spec.Rsa.splitTwos (modulus - 1)).1 ≤ Spec.RsaKeyGen.bitLength modulus
  room : primeExponent + 8 * ((len + 7) / 8) ≤ size
  tapeLen32 : tapeLen < 2 ^ 32
  tapeFit : tape.toNat + tapeLen ≤ 2 ^ 32
  witnessFit : witness.toNat + len ≤ 2 ^ 32
  tapeScratch : Region.Disjoint ⟨tape.setWidth 64, tapeLen⟩ ⟨base, size⟩
  witnessScratch : Region.Disjoint ⟨witness.setWidth 64, len⟩ ⟨base, size⟩
  tapeWitness : Region.Disjoint ⟨tape.setWidth 64, tapeLen⟩ ⟨witness.setWidth 64, len⟩

def PrimeConfig.n (G : PrimeConfig) : Nat := (G.len + 7) / 8
def PrimeConfig.draw (G : PrimeConfig) : Nat := 8 * G.n
def PrimeConfig.checks (G : PrimeConfig) : Nat := Spec.Dsa.primeChecks (8 * G.len)
def PrimeConfig.twos (G : PrimeConfig) : Nat := (Spec.Rsa.splitTwos (G.modulus - 1)).1
def PrimeConfig.exponent (G : PrimeConfig) : Nat := (Spec.Rsa.splitTwos (G.modulus - 1)).2

theorem PrimeConfig.width (G : PrimeConfig) : G.n ≤ 48 := by have := G.lenMax; unfold n; omega

theorem PrimeConfig.flagRoom (G : PrimeConfig) : primeIsUniform + 4 ≤ G.size := by
  have := G.room; unfold primeExponent primeIsUniform at *; omega

theorem PrimeConfig.twos32 (G : PrimeConfig) : G.twos < 2 ^ 32 := by
  have h := G.twosBound
  rw [G.modulusBits] at h
  have := G.lenMax
  exact Nat.lt_of_le_of_lt h (by omega)

structure PrimeReady (G : PrimeConfig) (s : State) : Prop where
  context : Context G.n G.modulus G.base G.size s
  one : wordsVal s.mem G.base (slot G.n 3) G.n = 1
  r2 : wordsVal s.mem G.base (slot G.n 4) G.n = 2 ^ (128 * G.n) % G.modulus
  exponent : val32 s.mem G.base primeExponent (2 * G.n) = G.exponent
  twos : s.mem.readW (off G.base primeTwos) 32 = BitVec.ofNat 32 G.twos
  tape : s.mem.readW (off G.base primeTape) 32 = G.tape
  tapeLen : s.mem.readW (off G.base primeTapeLen) 32 = BitVec.ofNat 32 G.tapeLen
  witness : s.mem.readW (off G.base primeWitness) 32 = G.witness
  tapeRead : ∀ i < G.tapeLen, InRegions (s.rd ++ s.wr) (off (G.tape.setWidth 64) i) 1
  witnessRead : ∀ i, i + 4 ≤ G.len → InRegions (s.rd ++ s.wr) (off (G.witness.setWidth 64) i) 4
  witnessReadByte : ∀ i < G.len, InRegions (s.rd ++ s.wr) (off (G.witness.setWidth 64) i) 1
  witnessWrite : ∀ i < G.len, InRegions s.wr (off (G.witness.setWidth 64) i) 1

theorem PrimeReady.keep {G : PrimeConfig} {s t : State} {rs : List Reg} (R : PrimeReady G s)
    (O : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem)
    (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs) : PrimeReady G t := by
  have sizeBound : G.size ≤ 2 ^ 64 := by have := R.context.scr.nowrap; omega
  have apart := G.witnessScratch.symm
  have header (d : Nat) (hd : primeFixedHeader d) := O.header G.width sizeBound G.room apart hd
  refine ⟨O.context R.context G.width G.room apart K di sp,
    (O.constants G.width sizeBound G.flagRoom apart (.inr (.inl rfl))).trans R.one,
    (O.constants G.width sizeBound G.flagRoom apart (.inr (.inr rfl))).trans R.r2,
    (O.exponent G.width sizeBound G.room apart).trans R.exponent,
    (header _ (.inr (.inl rfl))).trans R.twos,
    (header _ (.inr (.inr (.inl rfl)))).trans R.tape,
    (header _ (.inr (.inr (.inr (.inl rfl))))).trans R.tapeLen,
    (header _ (.inr (.inr (.inr (.inr rfl))))).trans R.witness, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [K.2.1, K.2.2]; exact R.tapeRead i hi
  · intro i hi; rw [K.2.1, K.2.2]; exact R.witnessRead i hi
  · intro i hi; rw [K.2.1, K.2.2]; exact R.witnessReadByte i hi
  · intro i hi; rw [K.2.2]; exact R.witnessWrite i hi
end VG.Proof.Dsa.X86.Generation
