module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptContract
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scan
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutInputs
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Finish
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Core
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.PublicOutput
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Zero
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Start
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth
import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Front
import VerifiedGarbage.Proof.Ffdh.KeyScalar

/-! # FFDH key generation from the context on x86-64: the attempt meets its contract -/

@[expose] public section

/-! # FFDH key generation from the context on x86-64: the attempt

`vg_ffdh_generate_key`'s attempt with the scalar cut at the context's width
(`metaLoad`) and `g^x mod p` by the context's comb (`comb_ok`). -/

/-! # FFDH key generation from the context on x86-64: the attempt's data

`vg_ffdh_generate_key`'s data (`GkP`) with the scalar cut at the context's
public width (`cgOf`), and what the attempt keeps of the context: its words,
outside the working space and both outputs, and its pointer in the sixth
stack argument (`CtxIn`). -/

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

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Ffdh.X86_64.Cached (at_)
open VG.Impl.Ffdh.X86_64.Cached.Generate (metaLoad)
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.GenerateKey
open VG.Proof.Rsa.X86_64 (OutOk Apart)

theorem toNat_mod64 {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat % 64 = x % 64 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- The context's width: `sEl :=` its bytes, `sMsk :=` the mask of its first byte. -/
theorem metaLoad_inputs {p : GkP} {rb : List Byte} {s : State} {cp : Addr} (h : Inputs p rb s)
    (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8 * p.k)
    (hld : p.ld = p.k - (Spec.Ffdh.generationScalarBits p.params + 7) / 8)
    (hmsk : p.msk = cgMask (Spec.Ffdh.generationScalarBits p.params)) :
    WP isa (.block metaLoad) s fun t =>
      Inputs p rb t ∧ word t.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n ∧
      word t.mem p.B (8 * sMsk) = p.msk ∧ Frm p.B scanRanges s.mem t.mem ∧
      Keep [.rax, .rsi, .rdx, .rcx] s t := by
  have hZ := h.base.hZ
  have hk := h.base.k2
  obtain ⟨hw0, hw1, _⟩ := hc.hdr
  have hr0 : InRegions (s.rd ++ s.wr) cp 8 := by simpa [off] using hc.reg.rd 0 (by omega)
  have hw0' : s.mem.readW cp 64 = BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits p.params) := by
    simpa [Bignum.word, off] using hw0
  have hr1 : InRegions (s.rd ++ s.wr) (off cp 8) 8 := hc.reg.rd 1 (by omega)
  have hn : p.n = (Spec.Ffdh.generationScalarBits p.params + 7) / 8 := by
    change p.k - p.ld = _; rw [hld]; omega
  have hsub : BitVec.ofNat 64 (8 * ((Spec.Ffdh.generationScalarBits p.params + 7) / 8)) -
      BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits p.params) =
      BitVec.ofNat 64 (8 * ((Spec.Ffdh.generationScalarBits p.params + 7) / 8) - Spec.Ffdh.generationScalarBits p.params) :=
    sub_ofNat (by omega) (by omega)
  let m := (s.mem.writeW (off p.B (8 * sEl)) (BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits p.params + 7) / 8))).writeW
    (off p.B (8 * sMsk)) (cgMask (Spec.Ffdh.generationScalarBits p.params))
  refine WP.mono (WP.keep [.rax, .rsi, .rdx, .rcx] (Q := fun t => t.mem = m) (by
    unfold metaLoad
    xrun [State.ea, VG.Impl.Rsa.X86_64.Crt.stk, hdr, at_, h.rdi, hsp, hdrOff, hc.sprd, hc.sp, atOff', hr0, hr1,
      hw0', hw1, h.base.scr.st (d := 8 * sEl) (by change 200 ≤ p.Z; omega),
      h.base.scr.st (d := 8 * sMsk) (by change 256 ≤ p.Z; omega), shl3 (show 8 * ((Spec.Ffdh.generationScalarBits p.params + 7) / 8) < 2 ^ 64 by omega),
      hsub, execShiftCl, VarShiftOp.eval, toNat_mod64 (show 8 * ((Spec.Ffdh.generationScalarBits p.params + 7) / 8) -
        Spec.Ffdh.generationScalarBits p.params < 2 ^ 64 by omega), m, cgMask]
    rfl) rfl)
    fun t ⟨hm, k⟩ => ?_
  have o1 := writeW_outside s.mem p.B (d := 8 * sEl)
    (BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits p.params + 7) / 8)) (by decide)
  have o2 := writeW_outside (s.mem.writeW (off p.B (8 * sEl))
    (BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits p.params + 7) / 8))) p.B (d := 8 * sMsk)
    (cgMask (Spec.Ffdh.generationScalarBits p.params)) (by decide)
  have hf : Frm p.B scanRanges s.mem t.mem := by
    rw [hm]
    exact (Frm.of_outside o1 (by simp [scanRanges])).trans (Frm.of_outside o2 (by simp [scanRanges]))
  refine ⟨h.keep hf k (by decide), ?_, ?_, hf, k⟩
  · rw [hm, o2.word (by decide) (by decide), word_writeW_self, hn]
  · rw [hm, word_writeW_self, hmsk]

/-- The sampled scalar is ready for the existing private-key arithmetic proofs. -/
def ScalarPostC (p : GkP) (rb : List Byte) (s t : State) : Prop :=
  CheckPrivate.Base p.kp (p.xb rb) t ∧ Src t p.B p.Z p.xp (p.cut rb) ∧ t.gpr .rdi = p.B ∧
    word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep mmRegs s t

/-- The sampled scalar, cut at the context's width. -/
theorem scalarC_ok {p : GkP} {rb : List Byte} {s : State} {cp : Addr} (h : Inputs p rb s)
    (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp) (hm : p.mv = true)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8 * p.k)
    (hld : p.ld = p.k - (Spec.Ffdh.generationScalarBits p.params + 7) / 8)
    (hmsk : p.msk = cgMask (Spec.Ffdh.generationScalarBits p.params)) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Cached.Generate.scalar) s fun t => ScalarPostC p rb s t ∧ CtxIn p cp t := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.scalar
  change WP isa (.seq (.block metaLoad) (.seq (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutSetup)
    (.seq (.loop (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutBody) .ne)
      (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutFinish)))) s _
  refine WP.seq (WP.mono (metaLoad_inputs h hc hsp h1 h8 hld hmsk) fun v ⟨hv, hnv, hmask, hfv, k₂⟩ => ?_)
  refine WP.seq (WP.mono (cutSetup_ok hv hnv hmask) fun z ⟨⟨hr, hmz⟩, k₃⟩ => ?_)
  have hz : Inputs p rb z := hv.keep (by intro a _; rw [hmz]) k₃ (by decide)
  refine WP.seq (WP.mono (cut_inputs hz hr) fun a ⟨ha, hx, hh, h8', hf₄, k₄⟩ => ?_)
  have hna : word a.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n := by
    rw [hh _ (by have := ha.base.hZ; change 200 ≤ p.Z; omega), hmz]
    exact hnv
  refine WP.mono (finish_base ha hx hm hna h8') fun t ⟨hb, hd, hG, hQ, hs, hi, k₅⟩ => ?_
  have hZ : 256 ≤ p.Z := by have := h.base.hZ; omega
  have f₁ : RunFrame p s.mem v.mem := .of_frm hfv (fun r hr => Nat.le_trans (scanRanges_end r hr) hZ)
  have f₃ : RunFrame p v.mem z.mem := by rw [hmz]; exact .refl _ _
  have F : RunFrame p s.mem t.mem := ((f₁.trans f₃).trans hf₄).trans (.of_scr hi)
  have K := ((k₂.trans k₃).trans (k₄.trans k₅))
  refine ⟨⟨hb, hx.congrK hi k₅, hd, hG, hQ, ?_, F, K.mono (by decide)⟩, hc.keep F K.2.1 K.2.2⟩
  intro i hi'
  have sv : word v.mem p.B (8 * i) = word s.mem p.B (8 * i) := hfv.word_eq (by
    simp only [scanRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [sEp, sEl, sMsk, sFn] <;> omega) (by omega)
  rw [hs i hi', hh _ (by have := h.base.hZ; omega), hmz, sv]

/-- `g^x mod p` by the context's comb, from `R² mod p`. -/
theorem ready_comb (Mo : Mont) {p : GkP} {rb : List Byte} {cp : Addr} {s : State}
    (h : CheckPrivate.Ready p.kp (p.xb rb) s) (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8192)
    (hxb : Spec.Rsa.os2ip (p.xb rb) < 2 ^ Spec.Ffdh.generationScalarBits p.params) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.comb Mo.mm)) s
      (CheckPrivate.StepPost p.kp s (CheckPrivate.Value p.kp (p.xb rb))) := by
  obtain ⟨mi, hb, hcm, hG⟩ := h
  have hk := hb.k2
  have hrs := Rsa.FixedBaseComb.rows_small h8
  have hrp := Rsa.FixedBaseComb.rows_pos (show 0 < Spec.Ffdh.generationScalarBits p.params by omega)
  have hxl : (p.xb rb).length = p.kp.xl := hb.xlen
  have hxk : p.kp.xl ≤ p.kp.k := hb.xl2
  refine WP.mono (comb_ok Mo (T := cgT p mi cp) hcm (by rw [hsp]; exact hc.sprd)
    (fun hm => by rw [hsp]; exact hc.sp_inScr hm) (by rw [hsp]; exact hc.sp)
    (hb.hdr (sX, p.kp.xp) (by simp [CheckPrivate.KpP.headers]))
    (by rw [hxl]; exact hb.hdr (sXl, BitVec.ofNat 64 p.kp.xl) (by simp [CheckPrivate.KpP.headers]))
    hc.reg hc.hdr.2.2 (hc.ent mi) hb.x hrp
    (show 5 * Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits p.params) < 2 ^ 31 by omega) (by rw [hxl]; change 8 * p.kp.xl < 2 ^ 32; omega) hxb)
    fun t ⟨hct, hy, hf, k⟩ => ?_
  have hr : ∀ r ∈ innerR p.w, r.1 + r.2 ≤ slot p.w 8 + tabBytes p.w 32 :=
    fun r hr => by have := (innerR_ok p.w r hr).2.1; omega
  obtain ⟨hb', hi, hs⟩ := hb.child hcm.sub hf hr k
  obtain ⟨hh, _⟩ := VG.Proof.Ffdh.X86_64.child_frm hcm.sub hcm.wide hf hr
  refine ⟨⟨⟨mi, hb', hct, (hh _ (by decide)).trans hG⟩, hy.trans ?_⟩, hi, hs, k.mono (by decide)⟩
  rw [powMod_eq]
  rfl

/-- `vg_ffdh_generate_key`'s tail with the comb. -/
theorem tailC_ok (Mo : Mont) (R : R2Impl Mo)
    {p : GkP} {rb : List Byte} {mi : BitVec 64} {s : State} {cp : Addr}
    (h : CheckPrivate.Work p.kp (p.xb rb) mi s) (hd : s.gpr .rdi = off p.B (VG.Proof.Ffdh.X86_64.inner p.w))
    (hm : p.mv = true) (hx : Src s p.B p.Z p.xp (p.cut rb))
    (hoX : OutOk s p.B p.Z p.xp p.k) (hoY : OutOk s p.B p.Z p.yp p.k)
    (ha : Apart p.xp p.k p.yp p.k) (hlen : (p.cut rb).length = p.k) (hld : p.ld < p.k)
    (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8192)
    (hxb : Spec.Rsa.os2ip (p.xb rb) < 2 ^ Spec.Ffdh.generationScalarBits p.params) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.tail Mo.mm (.seq (.block r2Head) R.code))) s
      (PowerPost p rb s) := by
  have hZ : 128 * p.k + 256 ≤ p.Z := h.base.hZ
  have hk : p.k ≤ 1024 := h.base.k2
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.tail
  simp only [List.append_assoc]
  refine wp_seqs_append (a := [.seq (.block r2Head) R.code]) (by simp) (by simp)
    (WP.mono (CheckPrivate.work_ready Mo R h hd hm) fun u ⟨hu, hi₁, hs₁, k₁⟩ => ?_)
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Cached.Generate.comb Mo.mm)
    (b := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput ++
      [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, .block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.status])
    (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.comb]) (by simp)
    (WP.mono (ready_comb Mo hu (hc.keep (.of_scr hi₁) k₁.2.1 k₁.2.2) ((k₁.gpr (by decide)).trans hsp) h1 h8 hxb)
      fun v ⟨hv, hi₂, hs₂, k₂⟩ => ?_)
  have hxy := (hx.congrK hi₁ k₁).congrK hi₂ k₂
  have hyv : OutOk v p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact hoY.wr i hi, hoY.sep⟩
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput)
    (b := [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, .block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.status])
    (by simp [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput]) (by simp)
    (WP.mono (publicOutput_ok hv hxy hyv ha hlen) fun z hz => ?_)
  have hz' := hz
  obtain ⟨_, _, _, _, _, _, _, _, hs₃, hf₃, k₃⟩ := hz
  have hox : OutOk z p.B p.Z p.xp p.k :=
    ⟨fun i hi => by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hoX.wr i hi, hoX.sep⟩
  have hoy : OutOk z p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hoY.wr i hi, hoY.sep⟩
  refine WP.mono (outputs_ok hz' hox hoy ha (by omega) (by omega) hld hlen)
    fun t ⟨hret, hdi, hX, hY, hs₄, hf₄, k₄⟩ => ?_
  refine ⟨hret, hdi, hX, hY, ?_, ?_, (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · intro i hi
    have a₁ : word u.mem p.B (8 * i) = word s.mem p.B (8 * i) := hs₁ i hi
    have a₂ : word v.mem p.B (8 * i) = word u.mem p.B (8 * i) := hs₂ i hi
    exact (hs₄ i hi).trans ((hs₃ i hi).trans (a₂.trans a₁))
  · exact (RunFrame.of_scr hi₁).trans ((RunFrame.of_scr hi₂).trans (hf₃.trans hf₄))

/-- A complete attempt, from a valid modulus. -/
theorem mainC_ok (Mo : Mont) (R : R2Impl Mo)
    {p : GkP} {rb : List Byte} {s : State} {cp : Addr} (h : Base p rb s) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8 * p.k)
    (hld : p.ld = p.k - (Spec.Ffdh.generationScalarBits p.params + 7) / 8)
    (hmsk : p.msk = cgMask (Spec.Ffdh.generationScalarBits p.params))
    (hsf : p.sf rb = Spec.Ffdh.vettedScalarOfOctets p.params rb) :
    WP isa (VG.Impl.Ffdh.X86_64.Cached.Generate.main Mo.mm (.seq (.block r2Head) R.code)) s
      (AttemptPost p rb s) := by
  have hk := h.k1
  have hk' := h.k2
  have hZ := h.hZ
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.main
  change WP isa (.seq (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK)
    (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.scalar ++
      VG.Impl.Ffdh.X86_64.Cached.Generate.core Mo.mm (.seq (.block r2Head) R.code)))) s _
  refine WP.seq (WP.mono (zero_ok h hd) fun u ⟨hu, hy, hf₁, hh, k₁⟩ => ?_)
  have hdi : u.gpr .rdi = p.B := (k₁.gpr (by decide)).trans hd
  have hg : word u.mem p.B (8 * sG) = off p.dp p.k := by
    rw [hh _ (by change 224 ≤ p.Z; omega)]; exact hG
  have hq : word u.mem p.B (8 * sQ) = off p.dp (2 * p.k) := by
    rw [hh _ (by change 232 ≤ p.Z; omega)]; exact hQ
  have hcu : CtxIn p cp u := hc.keep (RunFrame.of_y hf₁) k₁.2.1 k₁.2.2
  have hspu : u.gpr .rsp = p.sp := (k₁.gpr (by decide)).trans hsp
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Cached.Generate.scalar)
    (b := VG.Impl.Ffdh.X86_64.Cached.Generate.core Mo.mm (.seq (.block r2Head) R.code))
    (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.scalar])
    (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.core, pSetup])
    (WP.mono (scalarC_ok ⟨hu, hdi, hy, hg, hq⟩ hcu hspu hm h1 h8 hld hmsk)
      fun v ⟨⟨hb, hx, hdv, hgv, hqv, hs₂, hf₂, k₂⟩, hcv⟩ => ?_)
  have hox : OutOk v p.B p.Z p.xp p.k :=
    ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact h.x.wr i hi, h.x.sep⟩
  have hoy : OutOk v p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact h.y.wr i hi, h.y.sep⟩
  have hxb : Spec.Rsa.os2ip (p.xb rb) < 2 ^ Spec.Ffdh.generationScalarBits p.params := by
    change Spec.Rsa.os2ip ((p.cut rb).drop p.ld) < _
    rw [VG.Proof.Ffdh.KeyScalar.os2ip_cut_drop, h.cutv hm]
    change p.sf rb < _
    rw [hsf]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hspv : v.gpr .rsp = p.sp := (k₂.gpr (by decide)).trans hspu
  refine WP.mono (coreWith_ok (tl := VG.Impl.Ffdh.X86_64.Cached.Generate.tail Mo.mm (.seq (.block r2Head) R.code))
    (fun mi w hw hdw hxw hoxw hoyw hiw kw => tailC_ok Mo R hw hdw hm hxw hoxw hoyw h.xy h.cut_length h.ld_lt
      (hcv.keep (.of_scr hiw) kw.2.1 kw.2.2) ((kw.gpr (by decide)).trans hspv) h1 (by omega) hxb)
    hb hdv hgv hqv hm hx hox hoy h.xy h.cut_length h.ld_lt)
    fun t ⟨hr, hdt, hX, hY, hs₃, hf₃, k₃⟩ => ?_
  refine ⟨hr, hdt, hX, hY, ?_, (RunFrame.of_y hf₁).trans (hf₂.trans hf₃), ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  intro i hi
  rw [hs₃ i hi, hs₂ i hi, hh _ (by omega)]

end VG.Proof.Ffdh.X86_64.Cached

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.GenerateKey
open VG.Proof.Rsa.X86_64 (OutOk Apart apart_of)

theorem genWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = 3 + 34 * ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords]
  omega

/-- The attempt's precondition: `vg_ffdh_generate_key`'s, the context, and valid parameters. -/
theorem cgCtx_of {s : State} (h : cgPre s) :
    GkCtx s ∧ CtxIn (cgOf s) (stackArg s 5) s ∧ Spec.Ffdh.domainValid (stackArg s 0).toNat (gkDom s) = true := by
  obtain ⟨hsp, hrd, hwr, dxy, dxd, dxr, dxs, dxc, dxa, dyd, dyr, dys, dyc, dya, dds, drs, dsc, dsa,
    wX, wY, wD, wR, wS, wC, _, _, _, _, _, _, _, ⟨hk1, hk2⟩, hdl, hxl, hyl, hrl, hsl, hdv, hcl, hcw⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  have hargs : ∀ i < 7, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8 := fun i hi => by
    refine ⟨⟨stackArgAddr s 0, 56⟩, by rw [hrd]; simp, ?_⟩
    rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
      simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨⟨hk1, hk2, hdl, hxl, hyl, hrl, by omega, Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega) dds,
    src_of_region (by rw [hrd]; simp) (by omega) drs, fun i hi => hargs i (by omega), ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩, ?_, hdv⟩
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, contains_byte _ (by omega) (by omega)⟩
  · intro i hi
    exact out_scr dxs (contains_byte _ (by omega) (by omega))
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, by simp, contains_byte _ (by omega) (by omega)⟩
  · intro i hi
    exact out_scr dys (contains_byte _ (by omega) (by omega))
  · simpa only [hxl, hyl] using (apart_of dxy (by omega) (by omega))
  · simpa only [hxl] using (apart_of dxd (by omega) (by omega))
  · simpa only [hxl, hrl] using (apart_of dxr (by omega) (by omega))
  · simpa only [hyl] using (apart_of dyd (by omega) (by omega))
  · simpa only [hyl, hrl] using (apart_of dyr (by omega) (by omega))
  · have hn : (stackArg s 6).toNat = 3 + 34 * ((cgOf s).w) := by rw [hcl, genWords_eq]; rfl
    have hdl' : (stackArg s 0).toNat ≤ (gkDom s).length := by
      have h2 : (s.gpr .r9).toNat = 2 * (stackArg s 0).toNat ∨ (s.gpr .r9).toNat = 3 * (stackArg s 0).toNat := hdl
      rw [show (gkDom s).length = (s.gpr .r9).toNat from VG.Proof.Bignum.bytesAt_length _ _ _]; omega
    have hmv := VG.Proof.Ffdh.domainValid_mod hdv
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_, by rw [← hn]; omega⟩, fun i hi j hj => ?_, fun i hi j hj => ?_,
      ?_, hargs 5 (by decide), fun b hb => ?_, fun b hb j hj => ?_, fun b hb j hj => ?_, rfl⟩
    · refine ⟨⟨stackArg s 5, (stackArg s 6).toNat * 8⟩, by rw [hrd]; simp, ?_⟩
      exact Offset.contains_base _ (by rw [hn]; omega) (by omega)
    · exact out_scr dsc.symm (contains_byte _ (by rw [hn]; omega) (by omega))
    · have := apart_of dxc.symm (by omega) (by omega) i (by rw [hn]; omega) j (by rw [hxl]; exact hj)
      exact this
    · have := apart_of dyc.symm (by omega) (by omega) i (by rw [hn]; omega) j (by rw [hyl]; exact hj)
      exact this
    · have e := VG.Proof.Ffdh.generationPrecompute_eq hdl' hmv
      rw [hcw, hn] at e
      exact Option.some.inj e
    · have e : off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (40 + b) := by
        simp only [stackArgAddr, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 8 * (0 + 1) + (40 + b) = 8 * 6 + b by omega]
      change (cgOf s).Z ≤ ofs (cgOf s).B (off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b)
      rw [e]
      exact out_scr dsa.symm (contains_byte _ (by omega) (by omega))
    · have e : off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (40 + b) := by
        simp only [stackArgAddr, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 8 * (0 + 1) + (40 + b) = 8 * 6 + b by omega]
      change off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b ≠ off (cgOf s).xp j
      rw [e]
      exact (apart_of dxa (by omega) (by omega) j (by rw [hxl]; exact hj) (40 + b) (by omega)).symm
    · have e : off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (40 + b) := by
        simp only [stackArgAddr, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 8 * (0 + 1) + (40 + b) = 8 * 6 + b by omega]
      change off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b ≠ off (cgOf s).yp j
      rw [e]
      exact (apart_of dya (by omega) (by omega) j (by rw [hyl]; exact hj) (40 + b) (by omega)).symm

/-- `vg_ffdh_generate_key`'s inputs, with the scalar of the context's width. -/
theorem _root_.VG.Proof.Ffdh.X86_64.GenerateKey.Base.cached {s t : State} (hb : Base (gkOf s) (gkRand s) t)
    (hv : Spec.Ffdh.domainValid (stackArg s 0).toNat (gkDom s) = true) : Base (cgOf s) (gkRand s) t := by
  have hbits := genBits_facts hv
  have hb1 : 1 ≤ cgBits s := hbits.1
  have hb2 : cgBits s ≤ 8 * (stackArg s 0).toNat := hbits.2
  have hk := hb.k1
  have hrl := hb.rl
  refine ⟨hb.k1, hb.k2, hb.dl, hb.doml, hb.rl, hb.hZ, hb.scr, hb.dom, hb.rand, hb.x, hb.y, hb.xy, hb.xd, hb.xr,
    hb.yd, hb.yr, hb.hdr, rfl, ?_, fun _ => ?_⟩
  · change (stackArg s 0).toNat - cgEl s < (stackArg s 0).toNat
    have : 1 ≤ cgEl s := by unfold cgEl; omega
    change 64 ≤ (stackArg s 0).toNat at hk
    omega
  · change Spec.Rsa.os2ip (VG.Proof.Ffdh.KeyScalar.cut (gkRand s) ((stackArg s 0).toNat - cgEl s)
      ((cgMask (cgBits s)).setWidth 8)) = Spec.Ffdh.vettedScalarOfOctets (gkA s) (gkRand s)
    have hl : (gkRand s).length = (stackArg s 0).toNat := hrl
    have hw : ScalarWidth.width (cgBits s) = cgEl s := by unfold ScalarWidth.width cgEl; omega
    rw [cgMask_byte hb1]
    change 64 ≤ (stackArg s 0).toNat at hk
    have := ScalarWidth.cut_value (r := gkRand s) (bits := cgBits s) (by omega) (by omega)
    rw [hl, hw] at this
    exact this

theorem resultStatus_lt' (p : GkP) (rb : List Byte) : resultStatus p rb < 2 ^ 32 := by
  unfold resultStatus
  split
  · decide
  · split <;> decide

/-- The attempt's outputs, by `keyStatus`. -/
theorem attempt_specC {p : GkP} {rb : List Byte} {s u t : State} (hb : Base p rb u)
    (hm : p.mv = true) (ha : Spec.Ffdh.parametersValid p.params = true) (h : AttemptPost p rb s t) :
    ((t.gpr .rax).setWidth 32).toNat = Spec.Ffdh.keyStatus p.params (p.scalar rb) ∧
      if Spec.Ffdh.keyStatus p.params (p.scalar rb) = 1 then
        Spec.Rsa.bytesAt t.mem p.xp p.k = Spec.Rsa.i2osp (p.scalar rb) p.k ∧
          Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (Spec.Rsa.powMod p.params.g (p.scalar rb) p.params.p) p.k
      else Spec.Rsa.bytesAt t.mem p.xp p.k = List.replicate p.k 0 ∧
        Spec.Rsa.bytesAt t.mem p.yp p.k = List.replicate p.k 0 := by
  obtain ⟨hr, _, hx, hy, _⟩ := h
  have hst := hb.resultStatus_eq hm ha
  have hlt := resultStatus_lt' p rb
  refine ⟨?_, ?_⟩
  · rw [hr]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide)), Nat.mod_eq_of_lt hlt]
    exact hst
  · rw [← hst]
    by_cases hs : resultStatus p rb = 1
    · simp only [ite_eq_left hs] at hx hy ⊢
      refine ⟨hx.trans (hb.cut_i2osp hm), ?_⟩
      rw [hb.power_value hm] at hy
      rw [VG.Proof.Bignum.powMod_eq]
      exact hy
    · simp only [ite_eq_right hs] at hx hy ⊢
      exact ⟨hx, by rw [hy, i2osp_zero']⟩

theorem cgBody_ok (Mo : Mont) (R : R2Impl Mo) {s : State} (hpre : cgPre s) :
    WP isa (VG.Impl.Ffdh.X86_64.Cached.Generate.body Mo.mm (.seq (.block r2Head) R.code)) s fun t =>
      cgPost s t ∧ t.gpr .rdi = (cgOf s).B ∧ RunFrame (cgOf s) s.mem t.mem ∧
      (∀ i < 6, word t.mem (cgOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t := by
  obtain ⟨c, hci, hv⟩ := cgCtx_of hpre
  have hbits := genBits_facts hv
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (entry_base c) fun u ⟨hb, hd, hi, hs, k⟩ => ?_
  have hb₁ : Base (cgOf s) (gkRand s) u := hb.cached hv
  refine WP.mono (dom_base hb₁ hd) fun v ⟨hb', hz, hd', hG, hQ, hi', hs', k'⟩ => ?_
  have H : InScr (cgOf s).B (cgOf s).Z s.mem v.mem := hi.trans hi'
  have K := keep_trans k k'
  have hS : ∀ i < 6, word v.mem (cgOf s).B (8 * i) = s.gpr (saved.getD i .rax) :=
    fun i hi => (hs' i hi).trans (hs i hi)
  have hm : (cgOf s).mv = true := VG.Proof.Ffdh.domainValid_mod hv
  refine WP.ite (!(cgOf s).mv) (by simp [eval, hz]) (fun hf => ?_) (fun _ => ?_)
  · exfalso
    rw [hm] at hf
    exact absurd hf (by decide)
  · refine WP.mono (mainC_ok Mo R hb' hd' hG hQ hm (hci.keep (.of_scr H) K.2.1 K.2.2)
      ((K.gpr (by decide)).trans rfl) hbits.1 hbits.2 rfl rfl rfl) fun t hh => ?_
    have hmain := hh
    obtain ⟨_, hdt, _, _, hsave, hframe, kk⟩ := hh
    refine ⟨?_, hdt, (RunFrame.of_scr H).trans hframe,
      (fun i hi => (hsave i hi).trans (hS i hi)), keep_trans K kk⟩
    have hp : Spec.Ffdh.parametersValid (cgOf s).params = true := by
      unfold Spec.Ffdh.domainValid at hv
      exact ((Bool.and_eq_true _ _).mp hv).1
    exact attempt_specC (p := cgOf s) (rb := gkRand s) (s := v) (u := v) (t := t) hb' hm hp hmain

theorem cg_correct (Mo : Mont) (R : R2Impl Mo)
    (hmx : (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) (s : State) (h : cgContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ cgContract.post s t := by
  have hpre := h
  have c := (cgCtx_of h).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hRetX, hRetY, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ cgContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.code
  refine WP.seq (WP.mono (cgBody_ok Mo R hpre) fun u ⟨hp, hd, hf, hs, k⟩ => ?_)
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exit_ok (c.hs.congr k.2.2) hd (by omega) hs)
    fun t ⟨hRestore, hm, kk⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact (kk.gpr (by decide)).trans (k.gpr (by decide))
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
  · rw [hm]
    apply Mem.readW_congr
    intro i hi
    have hbyte := contains_byte (s.gpr .rsp) hi (by decide)
    refine hf _ (out_scr hRetScr hbyte) ?_ ?_
    · intro j hj he
      exact hRetX _ hbyte (by rw [he]; exact contains_byte _ (by rw [c.xl]; exact hj) (by have := c.k2; omega))
    · intro j hj he
      exact hRetY _ hbyte (by rw [he]; exact contains_byte _ (by rw [c.yl]; exact hj) (by have := c.k2; omega))
  · change cgPost s t
    unfold cgPost
    rw [kk.gpr (show .rax ∉ saved by decide), hm]
    exact hp

end VG.Proof.Ffdh.X86_64.Cached
