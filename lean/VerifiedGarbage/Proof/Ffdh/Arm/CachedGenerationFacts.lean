module

public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain

/-! Native reads of the canonical context's public metadata. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem CachedGenerationContext.words {p : Inputs} {s : State} (h : CachedGenerationContext p s) :
    Spec.Rsa.wordsAt s.mem (State.addr p.cachedContext) p.cachedWords =
      VG.Proof.Ffdh.generationValues p.k p.dom := by
  have valid := VG.Proof.Ffdh.domainValid_mod h.valid
  have length : p.k ≤ p.dom.length := by rw [p.domainLength]; split <;> omega
  have equation := VG.Proof.Ffdh.generationPrecompute_eq length valid
  rw [h.canonical.2] at equation
  exact Option.some.inj equation

theorem cached_read_low32 (m : Mem) (a : Addr) :
    (m.readW a 64).setWidth 32 = m.readW a 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hi,
    Nat.lt_trans hi (by decide : 32 < 64), decide_true, Bool.true_and]
  simp only [Mem.read, BitVec.getLsbD_append]
  split <;> rename_i h0
  · rfl
  · split <;> rename_i h1
    · rfl
    · split <;> rename_i h2
      · rfl
      · split <;> rename_i h3
        · rfl
        · omega

theorem CachedGenerationContext.header {p : Inputs} {s : State}
    (h : CachedGenerationContext p s) (j : Nat) (hj : j < 3) :
    s.mem.readW (State.addr p.cachedContext + BitVec.ofNat 64 (8 * j)) 64 =
      ([BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)),
        BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom) + 7) / 8),
        BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)))] : List (BitVec 64)).getD j 0 := by
  have words := congrArg (fun xs : List (BitVec 64) => xs[j]?) h.words
  have count : 3 ≤ p.cachedWords := by
    rw [h.canonical.1, Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords]
    omega
  simp only [Spec.Rsa.wordsAt, List.getElem?_map, List.getElem?_range (by omega : j < p.cachedWords),
    Option.map_some] at words
  have heads := VG.Proof.Ffdh.generationValues_headers p.k p.dom
  have heads' := congrArg (fun xs : List (BitVec 64) => xs[j]?) heads
  simp only [List.getElem?_take, ite_eq_left hj] at heads'
  rw [heads'] at words
  have range : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases range with rfl | rfl | rfl <;> simpa using words

theorem CachedGenerationContext.header32 {p : Inputs} {s : State}
    (h : CachedGenerationContext p s) (j : Nat) (hj : j < 3) :
    s.mem.readW (State.addr p.cachedContext + BitVec.ofNat 64 (8 * j)) 32 =
      ([BitVec.ofNat 32 (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)),
        BitVec.ofNat 32 ((Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom) + 7) / 8),
        BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)))] : List (BitVec 32)).getD j 0 := by
  rw [← cached_read_low32, h.header j hj]
  have range : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases range with rfl | rfl | rfl <;> simp [BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]

theorem cached_words_slice (m : Mem) (base : Addr) (n c w : Nat) (fit : c + w ≤ n) :
    Spec.Rsa.wordsAt m (base + BitVec.ofNat 64 (8 * c)) w =
      ((Spec.Rsa.wordsAt m base n).drop c).take w := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.wordsAt, List.length_map, List.length_range, List.length_take, List.length_drop]
    omega
  · intro i hi hj
    have iw : i < w := by simpa only [Spec.Rsa.wordsAt, List.length_map, List.length_range] using hi
    simp only [Spec.Rsa.wordsAt, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop, Offset.add_add]
    simp only [Nat.mul_add]

theorem CachedGenerationContext.montgomery {p : Inputs} {s : State}
    (h : CachedGenerationContext p s) :
    Spec.Rsa.wordsAt s.mem (State.addr p.cachedContext + 24) (2 * p.w) =
      Spec.Rsa.toWords p.P p.w ++ Spec.Rsa.toWords (2 ^ (128 * p.w) % p.P) p.w := by
  have fit : 3 + 2 * p.w ≤ p.cachedWords := by
    rw [h.canonical.1, Spec.Ffdh.generationPrecomputedWords,
      Spec.Rsa.FixedBaseComb.precomputedWords, Spec.Rsa.precomputedWords, Inputs.w]
    omega
  rw [show (24 : BitVec 64) = BitVec.ofNat 64 (8 * 3) from rfl,
    cached_words_slice s.mem _ p.cachedWords 3 (2 * p.w) fit, h.words]
  exact VG.Proof.Ffdh.generationValues_montgomery p.k p.dom

theorem CachedGenerationContext.montgomeryReads {p : Inputs} {s : State}
    (h : CachedGenerationContext p s) :
    (s.mem.read (State.addr p.cachedContext + 24) (8 * p.w)).toNat = p.P ∧
    (s.mem.read (State.addr p.cachedContext + 24 + BitVec.ofNat 64 (8 * p.w)) (8 * p.w)).toNat =
      2 ^ (128 * p.w) % p.P := by
  have bound : p.P < 2 ^ (64 * p.w) :=
    Nat.lt_of_lt_of_le p.modulusBound (Nat.pow_le_pow_right (by decide) (by have := p.width.2.2.2.1; omega))
  have valid := VG.Proof.Ffdh.domainValid_mod h.valid
  have large := (VG.Proof.Bignum.valid_facts valid p.minLength).2.1
  change 1 < p.P at large
  have values := VG.Proof.Bignum.pre_words h.montgomery bound
    (Nat.lt_trans (Nat.mod_lt _ (by omega)) bound)
  rw [← VG.Proof.Bignum.read_eq_wv, ← VG.Proof.Bignum.read_eq_wv] at values
  simpa only [VG.Proof.Bignum.off, BitVec.add_zero] using values

end VG.Proof.Ffdh.Arm
