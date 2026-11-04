module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Start
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth
import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Front
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.KeyScalar

/-! # FFDH key generation from the context on x86-64: the attempt's data

`vg_ffdh_generate_key`'s data (`GkP`) with the scalar cut at the context's
public width (`cgOf`), and what the attempt keeps of the context: its words,
outside the working space and both outputs, and its pointer in the sixth
stack argument (`CtxIn`). -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.GenerateKey

/-- The attempt's public scalar width. -/
abbrev cgBits (s : State) : Nat := Spec.Ffdh.generationScalarBits (gkA s)

/-- Its bytes. -/
abbrev cgEl (s : State) : Nat := (cgBits s + 7) / 8

/-- The mask `metaLoad` computes: `255 >> (8 bytes - width)`. -/
def cgMask (bits : Nat) : BitVec 64 := BitVec.ofNat 64 255 >>> ((8 * ((bits + 7) / 8) - bits) % 64)

/-- `vg_ffdh_generate_key`'s data, with the scalar of the context's width. -/
def cgOf (s : State) : GkP :=
  { gkOf s with
    sv := Spec.Ffdh.privateValid (gkA s) (Spec.Ffdh.vettedScalarOfOctets (gkA s) (gkRand s))
    ld := (stackArg s 0).toNat - cgEl s
    msk := cgMask (cgBits s)
    sf := Spec.Ffdh.vettedScalarOfOctets (gkA s) }

theorem cgMask_byte {bits : Nat} (h1 : 1 ≤ bits) :
    (cgMask bits).setWidth 8 = ScalarWidth.mask bits := by
  have hw : ScalarWidth.width bits = (bits + 7) / 8 := by unfold ScalarWidth.width; omega
  have hh : ScalarWidth.headBits bits = 8 - (8 * ((bits + 7) / 8) - bits) := by
    unfold ScalarWidth.headBits; rw [hw]; omega
  have hd : 8 * ((bits + 7) / 8) - bits < 8 := by omega
  obtain ⟨d, hd'⟩ : ∃ d, d = 8 * ((bits + 7) / 8) - bits := ⟨_, rfl⟩
  rw [← hd'] at hd hh
  unfold cgMask ScalarWidth.mask
  rw [← hd', hh]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have key : ∀ d < 8, 255 % 2 ^ 64 / 2 ^ (d % 64) % 2 ^ 8 = (2 ^ (8 - d) - 1) % 2 ^ 8 := by decide
  exact key d hd

/-- The context's words. -/
structure CtxIn (p : GkP) (cp : Addr) (s : State) : Prop where
  reg : CtxRd s p.B p.Z cp (3 + 34 * p.w)
  ax : ∀ i < 8 * (3 + 34 * p.w), ∀ j < p.k, cp + BitVec.ofNat 64 i ≠ off p.xp j
  ay : ∀ i < 8 * (3 + 34 * p.w), ∀ j < p.k, cp + BitVec.ofNat 64 i ≠ off p.yp j
  words : Spec.Rsa.wordsAt s.mem cp (3 + 34 * p.w) = VG.Proof.Ffdh.generationValues p.k p.dom
  sprd : InRegions (s.rd ++ s.wr) (off p.sp (8 * 6)) 8
  spout : ∀ b < 8, p.Z ≤ ofs p.B (off p.sp (8 * 6) + BitVec.ofNat 64 b)
  spx : ∀ b < 8, ∀ j < p.k, off p.sp (8 * 6) + BitVec.ofNat 64 b ≠ off p.xp j
  spy : ∀ b < 8, ∀ j < p.k, off p.sp (8 * 6) + BitVec.ofNat 64 b ≠ off p.yp j
  sp : word s.mem p.sp (8 * 6) = cp

theorem wordsAt_congr {m m' : Mem} {cp : Addr} {n : Nat}
    (h : ∀ i < 8 * n, m' (cp + BitVec.ofNat 64 i) = m (cp + BitVec.ofNat 64 i)) :
    Spec.Rsa.wordsAt m' cp n = Spec.Rsa.wordsAt m cp n := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left fun i hi => Mem.readW_congr fun b hb => ?_
  have hi' := List.mem_range.mp hi
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact h _ (by omega)

theorem CtxIn.keep {p : GkP} {cp : Addr} {s t : State} (h : CtxIn p cp s) (hf : RunFrame p s.mem t.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : CtxIn p cp t := by
  refine ⟨h.reg.congr hrd hwr, h.ax, h.ay, ?_, by rw [hrd, hwr]; exact h.sprd, h.spout, h.spx, h.spy, ?_⟩
  · rw [← h.words]
    exact wordsAt_congr fun i hi => hf _ (h.reg.sep i hi) (h.ax i hi) (h.ay i hi)
  · rw [← h.sp]
    exact Mem.readW_congr fun b hb => hf _ (h.spout b hb) (h.spx b hb) (h.spy b hb)

/-- The stack argument's word is outside the working space. -/
theorem CtxIn.sp_inScr {p : GkP} {cp : Addr} {s : State} (h : CtxIn p cp s) {m m' : Mem}
    (hm : InScr p.B p.Z m m') : word m' p.sp (8 * 6) = word m p.sp (8 * 6) :=
  Mem.readW_congr fun b hb => hm _ (h.spout b hb)

/-- Word `i` of the context. -/
theorem word_of_wordsAt {m : Mem} {cp : Addr} {n i : Nat} (hi : i < n) :
    word m cp (8 * i) = (Spec.Rsa.wordsAt m cp n)[i]'(by simp [Spec.Rsa.wordsAt, hi]) := by
  simp [Spec.Rsa.wordsAt, Bignum.word, off]

/-- Row `j` of the context, a slice of its words. -/
theorem row_of_wordsAt {m : Mem} {cp : Addr} {w j n : Nat} (hj : 3 + w * j + w ≤ n) :
    row m cp w j = ((Spec.Rsa.wordsAt m cp n).drop (3 + j * w)).take w := by
  apply List.ext_getElem
  · simp only [row, List.length_map, List.length_range, List.length_take, List.length_drop, Spec.Rsa.wordsAt]
    rw [Nat.mul_comm j w]; omega
  · intro i h1 h2
    simp only [row, List.length_map, List.length_range] at h1
    simp only [row, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop, Spec.Rsa.wordsAt]
    rw [rowOff]
    simp only [Bignum.word, off]
    rw [show 3 + w * j + i = 3 + j * w + i by rw [Nat.mul_comm j w]]

/-- The comb's data for the attempt's context. -/
def cgT (p : GkP) (mi : BitVec 64) (cp : Addr) : TabP :=
  ⟨p.B, p.Z, VG.Proof.Ffdh.X86_64.inner p.w, p.w, mi, cp, p.P, Spec.Rsa.os2ip ((p.dom.drop p.k).take p.k),
    Spec.Ffdh.generationScalarBits p.params⟩

theorem CtxIn.hdr {p : GkP} {cp : Addr} {s : State} (h : CtxIn p cp s) :
    word s.mem cp 0 = BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits p.params) ∧
    word s.mem cp 8 = BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits p.params + 7) / 8) ∧
    word s.mem cp 16 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits p.params)) := by
  have e := VG.Proof.Ffdh.generationValues_headers p.k p.dom
  rw [← h.words] at e
  have g : ∀ i (hi : i < 3), word s.mem cp (8 * i) = ((Spec.Rsa.wordsAt s.mem cp (3 + 34 * p.w)).take 3)[i]'(by
      simp [Spec.Rsa.wordsAt]; omega) := fun i hi => by
    rw [word_of_wordsAt (n := 3 + 34 * p.w) (by omega), List.getElem_take]
  refine ⟨?_, ?_, ?_⟩
  · have := g 0 (by decide); simp only [e] at this; simpa using this
  · have := g 1 (by decide); simp only [e] at this; simpa using this
  · have := g 2 (by decide); simp only [e] at this; simpa using this

theorem CtxIn.ent {p : GkP} {cp : Addr} {s : State} (h : CtxIn p cp s) (mi : BitVec 64) :
    ∀ a < 32, row s.mem cp p.w (2 + a) = Spec.Rsa.toWords ((cgT p mi cp).entry a) p.w := by
  intro a ha
  have hfit : 3 + p.w * (2 + a) + p.w ≤ 3 + 34 * p.w := by
    have h' := Nat.mul_le_mul_left p.w (show 2 + a + 1 ≤ 34 by omega); rw [Nat.mul_succ] at h'; omega
  rw [row_of_wordsAt hfit, h.words]
  exact VG.Proof.Ffdh.generationValues_entry p.k p.dom a ha

theorem bitLength_le_of_lt {x n : Nat} (h : x < 2 ^ n) : Spec.RsaKeyGen.bitLength x ≤ n := by
  by_cases hx : x = 0
  · subst hx; unfold Spec.RsaKeyGen.bitLength; simp
  · have hb := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds hx).1
    by_contra hc
    have : 2 ^ n ≤ 2 ^ (Spec.RsaKeyGen.bitLength x - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- The public scalar width of valid parameters: at least 1 and at most
p's bits. -/
theorem genBits_facts {k : Nat} {dom : List Byte} (hv : Spec.Ffdh.domainValid k dom = true) :
    1 ≤ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) ∧
      Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) ≤ 8 * k := by
  have hv' := (VG.Proof.Ffdh.domainValid_iff k dom).mp hv
  have hbnd : 2 ≤ Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv'.2.2 q hq).1.2.1; simp only [Option.getD_some]; omega
  have hle : Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≤ (Spec.Ffdh.domainOf k dom).p := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv'.2.2 q hq).1.2.2; simp only [Option.getD_some]; omega
  have hp : (Spec.Ffdh.domainOf k dom).p < 2 ^ (8 * k) := by
    have h1 := VG.Proof.Bignum.os2ip_lt (dom.take k)
    have h2 : 256 ^ (dom.take k).length ≤ 2 ^ (8 * k) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by simp only [List.length_take]; omega)
    change Spec.Rsa.os2ip (dom.take k) < _
    omega
  have hb := VG.Proof.Ffdh.VettedPolicy.bits_le_bound (Spec.Ffdh.domainOf k dom)
  have hbl : 1 ≤ Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) := by
    have := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds
      (show Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≠ 0 by omega)).2
    by_contra hc
    have e : Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) = 0 := by omega
    rw [e] at this; omega
  refine ⟨?_, Nat.le_trans hb (bitLength_le_of_lt (Nat.lt_of_le_of_lt hle hp))⟩
  unfold Spec.Ffdh.generationScalarBits
  cases he : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom) with
  | none => simpa using hbl
  | some b => have := recognized_nonzero he; simp only; omega

end VG.Proof.Ffdh.X86_64.Cached
