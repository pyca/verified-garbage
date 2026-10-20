module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrepareExponent
public import VerifiedGarbage.Proof.Mont.X86.ContextInit

/-! # Candidate resources before Montgomery preparation -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

structure PrimeInputs (G : PrimeConfig) (s : State) : Prop where
  scratch : Scr s G.base G.size
  odd : G.modulus % 2 = 1
  gtOne : 1 < G.modulus
  modulus : wordsVal s.mem G.base (slot G.n 0) G.n = G.modulus
  tape : s.mem.readW (off G.base primeTape) 32 = G.tape
  tapeLen : s.mem.readW (off G.base primeTapeLen) 32 = BitVec.ofNat 32 G.tapeLen
  witness : s.mem.readW (off G.base primeWitness) 32 = G.witness
  tapeRead : ∀ i < G.tapeLen, InRegions (s.rd ++ s.wr) (off (G.tape.setWidth 64) i) 1
  witnessRead : ∀ i, i + 4 ≤ G.len → InRegions (s.rd ++ s.wr) (off (G.witness.setWidth 64) i) 4
  witnessReadByte : ∀ i < G.len, InRegions (s.rd ++ s.wr) (off (G.witness.setWidth 64) i) 1
  witnessWrite : ∀ i < G.len, InRegions s.wr (off (G.witness.setWidth 64) i) 1

def primePrepareWrites (n : Nat) : List (Nat × Nat) := setupRanges n ++ prepareWrites n

theorem setupRanges_word {n d : Nat} {base : Addr} {s t : Mem}
    (O : Outs base (setupRanges n) s t) (width : n ≤ 48)
    (above : 8192 ≤ d) (bound : d + 4 ≤ 2 ^ 64) :
    t.readW (off base d) 32 = s.readW (off base d) 32 := by
  apply BitVec.eq_of_toNat_eq
  have v := O.val32 (d := d) (k := 1) (by
    intro r hr
    simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega) bound
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using v

theorem primePrepareWrites_header {n d : Nat} {base : Addr} {s t : Mem}
    (O : Outs base (primePrepareWrites n) s t) (width : n ≤ 48)
    (hd : d = primeTape ∨ d = primeTapeLen ∨ d = primeWitness ∨ d = primeUsed) :
    t.readW (off base d) 32 = s.readW (off base d) 32 := by
  apply BitVec.eq_of_toNat_eq
  have v := O.val32 (d := d) (k := 1) (by
    intro r hr
    simp only [primePrepareWrites, setupRanges, prepareWrites, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
      rcases hd with rfl | rfl | rfl | rfl <;>
      simp only [slot, stride, primeTwos, primeExponent,
        primeTape, primeTapeLen, primeWitness, primeUsed] <;> omega)
    (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using v
end VG.Proof.Dsa.X86.Generation
