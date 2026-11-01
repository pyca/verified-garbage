module

import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
public import VerifiedGarbage.Proof.MillerRabin.X86.Caller
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.Proof.Mont.X86.Ops

/-! # State retained between the short doubling phase and prepared squarings -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

structure Ready (g : Geometry) (c capacity : Nat) (p : BitVec 32) (s : State) : Prop where
  context : Context g s
  modulus : Modulus g c s.mem
  caller : Caller g capacity p s
  scratch : Scr s g.W g.L

def phaseRanges (g : Geometry) : List (Nat × Nat) :=
  [(g.array 6, 8 * g.w), (g.array 1, 8 * g.w), (g.array 2, accLen (modulus g.w))]

theorem phase_header (g : Geometry) {r : Nat × Nat} (mem : r ∈ phaseRanges g) : 256 ≤ r.1 := by
  simp only [phaseRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl <;>
    simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega

theorem phase_fits {g : Geometry} (v : g.Valid) {r : Nat × Nat} (mem : r ∈ phaseRanges g) :
    r.1 + r.2 ≤ g.L := by
  have lo := Prepared.layout v
  have tmp := v.arrayFit (j := 1) (by decide)
  simp only [phaseRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact lo.o_le
  · change g.array 1 + 8 * g.w ≤ g.L
    unfold Geometry.words at tmp
    omega
  · exact lo.acc_le

theorem phase_candidate (g : Geometry) {r : Nat × Nat} (mem : r ∈ phaseRanges g) :
    g.array 0 + 4 * g.words ≤ r.1 := by
  have a := g.arrayBefore (i := 0) (j := 6) (by decide)
  have b := g.arrayBefore (i := 0) (j := 1) (by decide)
  have d := g.arrayBefore (i := 0) (j := 2) (by decide)
  simp only [phaseRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact a
  · exact b
  · exact d

end VG.Proof.RsaKeyGen.X86.PreparedR2
