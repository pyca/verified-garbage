module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.MillerRabin.Contract

/-! # Inputs and reusable prepared data for all of a candidate's witnesses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86.PreparedR2

/-- A candidate of at least `e + 1` bits, its top bit for RSA's full-width candidates. -/
structure Input (g : Geometry) (c capacity : Nat) (p : BitVec 32) (s : State) (e : Nat := 64 * g.w - 1) : Prop where
  scratch : Scr s g.W g.L
  caller : Caller g capacity p s
  candidate : val32 s.mem g.W (g.array 0) g.words = c
  minusOne : val32 s.mem g.W (g.array 5) g.words = c - 1
  odd : c % 2 = 1
  large : 1 < c
  top : 2 ^ e ≤ c

structure Data (g : Geometry) (c capacity : Nat) (p : BitVec 32) (s : State) : Prop where
  ready : Ready g c capacity p s
  r2 : val32 s.mem g.W (g.array 4) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c
  one : val32 s.mem g.W (g.array 9) g.words = 2 ^ (64 * g.w) % c
  minusOne : val32 s.mem g.W (g.array 10) g.words = c - 2 ^ (64 * g.w) % c
  exponent : val32 s.mem g.W (g.array 27) g.words = Proof.MillerRabin.Round.exponent c
  marker : word s.mem g.W (g.array 27 + 8 * g.w) = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64)

  stride : word s.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2))

end VG.Proof.RsaKeyGen.X86.Prepare
