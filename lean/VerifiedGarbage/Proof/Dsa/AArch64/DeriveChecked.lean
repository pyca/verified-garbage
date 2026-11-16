module

public import VerifiedGarbage.Proof.Dsa.AArch64.Derive
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCopy
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveWrite
import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.Set
import VerifiedGarbage.Impl.Dsa.AArch64.Generate
import VerifiedGarbage.Proof.Dsa.AArch64.Finish
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Bignum.AArch64.PubFail
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
import VerifiedGarbage.Proof.Dsa.AArch64.PublicCalls
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Dsa.AArch64.SigningKey
import VerifiedGarbage.Proof.Dsa.AArch64.CheckEffects
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCalls
import VerifiedGarbage.Proof.Dsa.AArch64.Parameters
import VerifiedGarbage.Proof.Dsa.AArch64.SharedCall

/-! # Functional correctness of AArch64 DSA key derivation

`Generate.deriveKey` computes y = g^x and checks `g^q mod p = 1` in one
pass over both exponents (`SharedPower.pow`). `Generate.deriveChecked` is
it without that check: for a domain whose check has succeeded, the
remaining checks of the signer accept exactly what the full ones do. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- The signer's checks of g and y but `g^q = 1`, as `signingKeyAccepted`. -/
def prefixAccepted (L : ExecutionLayout) (gb yb : List Byte) (valid : Bool) : Bool :=
  decide ((L.modulus - 1) % L.subgroup = 0) &&
  (decide (1 < Spec.Dsa.decodeBE yb ∧ Spec.Dsa.decodeBE yb < L.modulus) &&
  (decide (1 < Spec.Dsa.decodeBE gb ∧ Spec.Dsa.decodeBE gb < L.modulus) && valid))

theorem keyPrefix_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb yb qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator gb)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hgl : gb.length = L.pLen) (hyl : yb.length = L.pLen)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (seqs (Checks.publicPrefix M.mm)) s0 fun s6 =>
      Ready L s6 ∧ word s6.mem L.base Field.mask.offset = mask (prefixAccepted L gb yb valid) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s6.mem ∧ Keep coreRegs s0 s6 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have fitq (n : Nat) (h : n < L.subgroup) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.qLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hqf)
  have fitp (n : Nat) (h : n < L.modulus) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.pLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hpf)
  have ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega
  have hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega
  unfold Checks.publicPrefix seqs
  refine WP.seq (WP.mono (readyRange_ok h0 .p Core.generator (by trivial) hg.active
    (by rw [hgl]; omega) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true hm) fun s1 h1 => ?_)
  have hg1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg
  have hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  have hq1 := h1.preserve h0 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb
  refine WP.seq (WP.mono (readyRange_ok h1.ready .p Core.publicValue (by trivial) hy1.active
    (by rw [hyl]; omega) (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true h1.mask) fun s2 h2 => ?_)
  have hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  have hq2 := h2.preserve h1.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq1
  refine WP.seq (WP.mono (readyMinus_ok h2.ready .p 1 (by decide) (by change 1 ≤ L.modulus; omega)
    t (by decide) ht) fun s3 h3 => ?_)
  have hg3 := h3.external (by decide) ht hg2
  have hq3 := h3.external (by decide) ht hq2
  have hm3 := (h3.fields (by decide) ht .mask).trans h2.mask
  have step4 := readyReduce_ok M h3.ready hq hoq (Core.element t) (by change t < 2 ^ 16; decide)
    (h3.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega) u (by decide) hu
  have step4' : WP isa (Core.reduce M.mm (Core.element t) (Core.scalar u)) s3
      (CallResult L .q u ((L.modulus - 1) % L.subgroup) s3) := by
    simpa only [ModulusSide.length, ModulusSide.value, fitp (L.modulus - 1) (by omega)] using step4
  refine WP.seq (WP.mono step4' fun s4 h4 => ?_)
  have hg4 := h4.external (by decide) hu hg3
  have hq4 := h4.external (by decide) hu hq3
  have hm4 := (h4.fields (by decide) hu .mask).trans hm3
  refine WP.seq (WP.mono (readyZero_ok h4.ready (Core.scalar u) (by change u < 2 ^ 16; decide)
    (h4.output (by decide) hu) (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) false hm4) fun s5 h5 => ?_)
  have hziff : (∀ b ∈ Spec.Dsa.encodeBE L.qLen ((L.modulus - 1) % L.subgroup), b = 0) ↔
      (L.modulus - 1) % L.subgroup = 0 := by
    rw [← VG.Proof.Dsa.decodeBE_eq_zero, fitq _ (Nat.mod_lt _ (by omega))]
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length] at hm5
  simp only [hziff] at hm5
  have hg5 := h5.preserve h4.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg4
  have hq5 := h5.preserve h4.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq4
  refine WP.mono (readyMinus_ok h5.ready .q 2 (by decide) (by change 2 ≤ L.subgroup; omega)
    qMinusTwo (by decide) hqm) fun s6 h6 => ?_
  refine ⟨h6.ready, (h6.fields (by decide) hqm .mask).trans hm5, ?_, ?_⟩
  · exact ((((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans
      (h4.scheduleFrame (by decide) hu)).trans h5.scheduleFrame).trans (h6.scheduleFrame (by decide) hqm)
  · exact (((((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).trans h5.keep).trans h6.keep).mono (by decide)

/-- After y = g^x at `t2`: y copied past the signer's layout, and the
signer's checks of the domain and that y but `g^q = 1`. -/
theorem deriveCopyPrefix_ok (M : Mont) {L : ExecutionLayout} {s2 : State} (h2 : Ready L s2)
    (hs2 : Scr s2 L.base deriveExtent)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup) (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb qb : List Byte}
    (hg2 : OperandBytes s2 L.base deriveExtent Core.generator gb)
    (hq2 : OperandBytes s2 L.base deriveExtent ⟨.input .q, .qLen⟩ qb)
    (hgl : gb.length = L.pLen) (hy : L.fields .y = off L.base derivedY) {y : Nat}
    (hb2 : ∀ i (hi : i < L.pLen), s2.mem (off L.base t2 + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi))
    {v : Bool} (hm2 : word s2.mem L.base Field.mask.offset = mask v) :
    WP isa (seqs [Generate.copyY, seqs (Checks.publicPrefix M.mm)]) s2 fun t =>
      Ready L t ∧
      word t.mem L.base Field.mask.offset = mask (prefixAccepted L gb (Spec.Dsa.encodeBE L.pLen y) v) ∧
      (∀ i (hi : i < L.pLen), t.mem (off L.base derivedY + BitVec.ofNat 64 i) =
        (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)) ∧
      Outside L.base 128 (deriveExtent - 128) s2.mem t.mem ∧ Keep coreRegs s2 t := by
  obtain hp384 : 0 < L.pLen ∧ L.pLen ≤ 384 := by
    obtain hl := L.lengths; unfold Spec.Dsa.lengthsValid at hl; omega_using [hl]
  unfold seqs
  -- y, copied past the signer's layout
  refine WP.seq (WP.mono (copyY_ok h2 hs2) fun s3 ⟨h3, hy3, hf3o, hk3⟩ => ?_)
  obtain hf3 : Outside L.base 128 (deriveExtent - 128) s2.mem s3.mem :=
    hf3o.mono (by decide) (by unfold deriveExtent; omega_using [hp384])
  obtain hg3 := hg2.frame h2 h3 hf3 hk3 (by decide) (by simp [stablePointer, Core.generator])
  obtain hq3 := hq2.frame h2 h3 hf3 hk3 (by decide) (by change Field.q ≠ .mask; decide)
  obtain hm3 : word s3.mem L.base Field.mask.offset = mask v :=
    (hf3o.word (Or.inl (by decide)) (by decide)).trans hm2
  obtain hyb : ∀ i (hi : i < L.pLen), s3.mem (off L.base derivedY + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi) := by
    intro i hi
    rw [hy3 i hi]
    exact hb2 i hi
  obtain hys : OperandBytes s3 L.base usedBytes Core.publicValue (Spec.Dsa.encodeBE L.pLen y) := by
    refine ⟨(h3.fields .pLen (by decide)).trans (by rw [VG.Proof.Dsa.encodeBE_length]; exact L.pLength), ?_⟩
    simp only [Core.publicValue, pointerValue, h3.fields .y (by decide), hy]
    refine ⟨fun i hi => ?_, fun i hi => hyb i (by rwa [VG.Proof.Dsa.encodeBE_length] at hi), fun i hi => ?_⟩
    · rw [VG.Proof.Dsa.encodeBE_length] at hi
      rw [off_add]
      exact scr_byte_rd (hs2.congr hk3.wr)
        (by unfold deriveExtent; omega_using [hi, hp384])
    · rw [VG.Proof.Dsa.encodeBE_length] at hi
      rw [ofs_off _ (by have := hs2.nowrap; unfold deriveExtent at this; omega_using [this, hi, hp384])]
      exact Nat.le_add_right _ _
  -- the signer's checks of the domain and y
  refine WP.mono (keyPrefix_ok M h3 hp hq hpo hqo hpf hqf (hg3.shrink (by decide)) hys (hq3.shrink (by decide))
    hgl (VG.Proof.Dsa.encodeBE_length _ _) hm3) fun t ⟨ht, hmt, hft, hkt⟩ => ?_
  refine ⟨ht, hmt, fun i hi => (hft _ (Or.inr ?_)).trans (hyb i hi), ?_, (hk3.trans hkt).mono (by decide)⟩
  · rw [ofs_off _ (by have := hs2.nowrap; unfold deriveExtent at this; omega_using [this, hi, hp384])]
    exact Nat.le_trans (by decide) (Nat.le_add_right _ _)
  · exact hf3.trans (hft.mono (by decide) (by decide))


/-- What domain-checked derivation computes before writing the key: x's
range, y = g^x copied past the signer's layout, and the signer's checks with
that y but `g^q = 1`. -/
theorem deriveCheckedBody_ok (M : Mont) {L : ExecutionLayout} {s : State} (hr : Ready L s)
    (hs : Scr s L.base deriveExtent)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup) (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb qb xb : List Byte}
    (hg : OperandBytes s L.base deriveExtent Core.generator gb)
    (hqb : OperandBytes s L.base deriveExtent ⟨.input .q, .qLen⟩ qb)
    (hx : OperandBytes s L.base deriveExtent Core.privateScalar xb)
    (hgl : gb.length = L.pLen) (hxl : xb.length = L.qLen) (hy : L.fields .y = off L.base derivedY)
    (hm : word s.mem L.base Field.mask.offset = mask true) :
    let y := Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE xb) L.modulus
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
        Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, seqs (Checks.publicPrefix M.mm)]) s fun t =>
      Ready L t ∧
      word t.mem L.base Field.mask.offset = mask (prefixAccepted L gb (Spec.Dsa.encodeBE L.pLen y)
        (decide (0 < Spec.Dsa.decodeBE xb ∧ Spec.Dsa.decodeBE xb < L.subgroup) && true)) ∧
      (∀ i (hi : i < L.pLen), t.mem (off L.base derivedY + BitVec.ofNat 64 i) =
        (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)) ∧
      Outside L.base 128 (deriveExtent - 128) s.mem t.mem ∧ Keep coreRegs s t := by
  intro y
  obtain ⟨hql1, hqu, hqp, hpu⟩ := L.widths
  obtain hp384 : 0 < L.pLen ∧ L.pLen ≤ 384 := by
    obtain hl := L.lengths; unfold Spec.Dsa.lengthsValid at hl; omega_using [hl]
  obtain hend : t2 + L.pLen ≤ usedBytes := by unfold t2 usedBytes; omega_using [hp384]
  unfold seqs
  -- 0 < x < q
  refine WP.seq (WP.mono (readyRange_ok hr .q Core.privateScalar (by trivial) (hx.shrink (by decide)).active
    (by rw [hxl]; omega_using [hql1]) (by simp only [hxl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm) fun s1 h1 => ?_)
  obtain hf1 : Outside L.base 128 (deriveExtent - 128) s.mem s1.mem := h1.frame.mono (by decide) (by decide)
  obtain hg1 := hg.frame hr h1.ready hf1 h1.keep (by decide) (by simp [stablePointer, Core.generator])
  obtain hq1 := hqb.frame hr h1.ready hf1 h1.keep (by decide) (by change Field.q ≠ .mask; decide)
  obtain hx1 := hx.frame hr h1.ready hf1 h1.keep (by decide) (by simp [stablePointer, Core.privateScalar])
  -- y = g^x mod p, at t2
  obtain step2 := readyPow_ok M h1.ready .p hp hpo Core.generator Core.privateScalar (by trivial) (by trivial)
    (hg1.shrink (by decide)).active (hx1.shrink (by decide)).active (by rw [hgl]; omega_using [hp384])
    (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hxl]; omega_using [hql1]) (by rw [hxl]; omega_using [hqu]) t2 (by decide) hend
  obtain step2' : WP isa (Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2)) s1
      (CallResult L .p t2 y s1) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value] using step2
  refine WP.seq (WP.mono step2' fun s2 h2 => ?_)
  obtain hf2 : Outside L.base 128 (deriveExtent - 128) s1.mem s2.mem :=
    (h2.scheduleFrame (by decide) hend).mono (by decide) (by decide)
  obtain hg2 := hg1.frame h1.ready h2.ready hf2 h2.keep (by decide) (by simp [stablePointer, Core.generator])
  obtain hq2 := hq1.frame h1.ready h2.ready hf2 h2.keep (by decide) (by change Field.q ≠ .mask; decide)
  obtain hm2 := (h2.fields (by decide) hend .mask).trans h1.mask
  obtain hs2 : Scr s2 L.base deriveExtent := hs.congr (h1.keep.trans h2.keep).wr
  obtain hb2 : ∀ i (hi : i < L.pLen), s2.mem (off L.base t2 + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi) := by
    intro i hi
    obtain hb := congrArg (fun l => l[i]?) h2.bytes
    simp only [ModulusSide.length, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi,
      Option.map_some] at hb
    rw [List.getElem?_eq_getElem (by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)] at hb
    exact Option.some.inj hb
  obtain hm2' : word s2.mem L.base Field.mask.offset = mask (decide (0 < Spec.Dsa.decodeBE xb ∧
      Spec.Dsa.decodeBE xb < L.subgroup) && true) := by
    simpa only [Bool.false_eq_true, ↓reduceIte, ModulusSide.value] using hm2
  refine WP.mono (deriveCopyPrefix_ok M h2.ready hs2 hp hq hpo hqo hpf hqf hg2 hq2 hgl hy hb2 hm2')
    fun t ⟨ht, hmt, hyt, hft, hkt⟩ => ?_
  exact ⟨ht, hmt, hyt, (hf1.trans hf2).trans hft, ((h1.keep.trans h2.keep).trans hkt).mono (by decide)⟩

/-- The key written out, or zeros, for the acceptance mask `valid` the
checks left, and y past the signer's layout. -/
theorem deriveOutput_ok {p : DeriveInput} {original v : State} (h : DerivePre p original) (pi qi : BitVec 64)
    {valid : Bool} (hv : Ready ((p.layout original h.pLength).withInverses pi qi) v)
    (hmv : word v.mem p.base Field.mask.offset = mask valid)
    (hyv : ∀ i (hi : i < p.pLen), v.mem (off p.base derivedY + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE p.pLen (Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.x)
        (Spec.Dsa.decodeBE p.pb)))[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi))
    (hframe' : InScr p.base deriveExtent original.mem v.mem) (hkeep' : Keep coreRegs original v)
    (hres : Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x =
      if valid then some (p.params ++ p.yb ++ p.x) else none) :
    WP isa (seqs [Generate.writeKey, .block SignVerify.result]) v (DerivePost p original) := by
  have hl := p.lengths
  unfold Spec.Dsa.lengthsValid at hl
  obtain hsv' : Scr v p.base deriveExtent := h.scratch.congr hkeep'.wr
  obtain ⟨_, _, _, hxs⟩ := h.sources hframe' hkeep'
  obtain hparams := h.paramsSource.congrK hframe' hkeep'
  obtain hfields : KeyFields v p.base (original.gpr .x0) (original.gpr .x2) (off p.base derivedY)
      (original.gpr .x5) p.pLen p.qLen valid :=
    ⟨hv.fields .out (by decide), hv.fields .p (by decide), hv.fields .y (by decide),
      hv.fields .x (by decide), (hv.fields .pLen (by decide)).trans h.pLength,
      hv.fields .qLen (by decide), hmv⟩
  have hn := hsv'.nowrap
  obtain hp384 : p.pLen ≤ 384 := by omega_using [hl]
  obtain hpq : 0 < p.pLen ∧ 0 < p.qLen := by omega_using [hl]
  obtain hreg : v.rd = original.rd ∧ v.wr = original.wr := ⟨hkeep'.rd, hkeep'.wr⟩
  unfold seqs
  refine WP.seq (WP.mono (writeKey_ok hsv' hv.parent.x0 (by decide) hfields hpq.1 hpq.2 (by omega_using [hl])
    ⟨fun i hi => hparams.rd i (by rw [p.paramsLength]; exact hi), h.paramsOut⟩
    ⟨fun i hi => by
      rw [off_add]; exact scr_byte_rd hsv' (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hp384]),
     fun i hi j hj => scr_ne_out h.outSeparate (d := derivedY) (i := i)
      (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hp384]) (by omega_using [hn]) j hj⟩
    ⟨fun i hi => hxs.rd i (by rw [p.xLength]; exact hi), h.xOut⟩
    (fun i hi => by rw [hreg.2]; exact h.outWrite i hi))
    fun w ⟨hw₁, hw₂, hw₃, hwf, hkw⟩ => ?_)
  obtain hwv : ∀ d, d + 8 ≤ deriveExtent → word w.mem p.base d = word v.mem p.base d := fun d hd =>
    Mem.readW_congr fun b hb => hwf _ (scr_ne_out h.outSeparate (d := d) (i := b) (by omega_using [hd, hb]) (by omega_using [hn]))
  refine WP.mono (result_ok (hsv'.congr hkw.wr) ((hkw.gpr .x0 (by decide)).trans hv.parent.x0) (by decide)
    ((hwv _ (by decide)).trans hmv)) fun t ⟨hret, hmem, hkt⟩ => ?_
  obtain hlen : p.outLen = p.params.length + p.yb.length + p.x.length := by
    rw [p.paramsLength, VG.Proof.Dsa.encodeBE_length, p.xLength]; unfold DeriveInput.outLen; omega_arith
  refine ⟨?_, ?_, ?_,
    ((hkeep'.trans hkw).trans hkt).mono (by decide)⟩
  · rw [hret]
    change BitVec.ofNat 64 valid.toNat = _
    rw [hres]
    cases valid <;> rfl
  · rw [hmem, hres]
    cases hvb : valid
    · apply bytesAt_zero_list
      intro i hi
      by_cases h1 : i < 2 * p.pLen + p.qLen
      · rw [hw₁ i h1, hvb]; rfl
      by_cases h2 : i < 3 * p.pLen + p.qLen
      · have := hw₂ (i - (2 * p.pLen + p.qLen)) (by omega_arith)
        rw [show 2 * p.pLen + p.qLen + (i - (2 * p.pLen + p.qLen)) = i by omega_arith, hvb] at this
        exact this
      · have := hw₃ (i - (3 * p.pLen + p.qLen)) (by unfold DeriveInput.outLen at hi; omega_arith)
        rw [show 3 * p.pLen + p.qLen + (i - (3 * p.pLen + p.qLen)) = i by omega_arith, hvb] at this
        exact this
    · simp only [↓reduceIte, Option.getD_some]
      rw [hlen]
      apply bytesAt_key
      · intro i hi
        rw [p.paramsLength] at hi
        rw [hw₁ i hi, hvb]
        simp only [↓reduceIte]
        exact hparams.val i (by rw [p.paramsLength]; exact hi)
      · intro i hi
        rw [VG.Proof.Dsa.encodeBE_length] at hi
        rw [p.paramsLength, hw₂ i hi, hvb]
        simp only [↓reduceIte]
        exact hyv i hi
      · intro i hi
        rw [p.xLength] at hi
        rw [p.paramsLength, VG.Proof.Dsa.encodeBE_length,
          show 2 * p.pLen + p.qLen + p.pLen = 3 * p.pLen + p.qLen by omega_arith, hw₃ i hi, hvb]
        simp only [↓reduceIte]
        exact hxs.val i (by rw [p.xLength]; exact hi)
  · intro x hx hout
    rw [hmem, hwf x hout]
    exact hframe' x hx


theorem deriveCheckedSuccess_ok (M : Mont) {p : DeriveInput} {original st : State}
    (h : DerivePre p original) (hs : DeriveShapePost p original h.pLength st) (ha : p.accepted = true)
    (hc : Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
      Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm), Generate.writeKey, .block SignVerify.result]) st
      (DerivePost p original) := by
  obtain ⟨hsize, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  obtain hpf : Spec.Dsa.decodeBE p.pb ≤ 256 ^ p.pLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.pb; rw [p.pbLength] at hh; exact Nat.le_of_lt hh
  obtain hqf : Spec.Dsa.decodeBE p.qb ≤ 256 ^ p.qLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.qb; rw [p.qbLength] at hh; exact Nat.le_of_lt hh
  refine WP.seq (WP.mono (deriveInitialize_ok h hs ha) fun u ⟨pi, qi, hr, ho, hm, hframe, hkeep⟩ => ?_)
  let L := (p.layout original h.pLength).withInverses pi qi
  obtain hsu : Scr u p.base deriveExtent := h.scratch.congr hkeep.wr
  apply wpAppendSequences (a := [Checks.range qWorkspace Core.privateScalar,
    Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine WP.mono (deriveCheckedBody_ok (L := L) M hr hsu hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar
    p.gbLength p.xLength rfl hm) fun v ⟨hv, hmv, hyv, hfv, hkv⟩ => ?_
  obtain hframe' : InScr p.base deriveExtent original.mem v.mem :=
    hframe.trans (InScr.of_outside hfv (by decide))
  obtain hkeep' : Keep coreRegs original v := (hkeep.trans hkv).mono (by decide)
  have hmv' : word v.mem p.base Field.mask.offset = mask (prefixAccepted L p.gb p.yb
      (decide (0 < Spec.Dsa.decodeBE p.x ∧ Spec.Dsa.decodeBE p.x < L.subgroup) && true)) := hmv
  refine deriveOutput_ok h pi qi hv hmv' hyv hframe' hkeep' ?_
  obtain hyfit : p.y < 256 ^ p.pLen :=
    Nat.lt_of_lt_of_le (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp1])) hpf
  obtain hg : Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.qb) (Spec.Dsa.decodeBE p.pb) = 1 := by
    rw [p.check_eq, ha, Bool.true_and] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1
  rw [p.derive_eq, ha, Bool.true_and, decide_eq_true hg, Bool.true_and]
  unfold prefixAccepted
  rw [VG.Proof.Dsa.decodeBE_encodeBE hyfit]
  rfl

/-- What derivation computes before writing the key: x's range, y = g^x
with whether `g^q = 1` (one pass over both exponents), y copied past the
signer's layout, and the signer's other checks with that y. -/
theorem deriveBody_ok (M : Mont) {L : ExecutionLayout} {s : State} (hr : Ready L s)
    (hs : Scr s L.base deriveExtent)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup) (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb qb xb : List Byte}
    (hg : OperandBytes s L.base deriveExtent Core.generator gb)
    (hqb : OperandBytes s L.base deriveExtent ⟨.input .q, .qLen⟩ qb)
    (hx : OperandBytes s L.base deriveExtent Core.privateScalar xb)
    (hgl : gb.length = L.pLen) (hql : qb.length = L.qLen) (hxl : xb.length = L.qLen)
    (hy : L.fields .y = off L.base derivedY)
    (hm : word s.mem L.base Field.mask.offset = mask true) :
    let y := Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE xb) L.modulus
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
        SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, seqs (Checks.publicPrefix M.mm)]) s fun t =>
      Ready L t ∧
      word t.mem L.base Field.mask.offset = mask (prefixAccepted L gb (Spec.Dsa.encodeBE L.pLen y)
        (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE qb) L.modulus = 1) &&
          (decide (0 < Spec.Dsa.decodeBE xb ∧ Spec.Dsa.decodeBE xb < L.subgroup) && true))) ∧
      (∀ i (hi : i < L.pLen), t.mem (off L.base derivedY + BitVec.ofNat 64 i) =
        (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)) ∧
      Outside L.base 128 (deriveExtent - 128) s.mem t.mem ∧ Keep coreRegs s t := by
  intro y
  obtain ⟨hql1, hqu, hqp, hpu⟩ := L.widths
  obtain hp384 : 0 < L.pLen ∧ L.pLen ≤ 384 := by
    obtain hl := L.lengths; unfold Spec.Dsa.lengthsValid at hl; omega_using [hl]
  obtain hend : t2 + L.pLen ≤ usedBytes := by unfold t2 usedBytes; omega_using [hp384]
  unfold seqs
  -- 0 < x < q
  refine WP.seq (WP.mono (readyRange_ok hr .q Core.privateScalar (by trivial) (hx.shrink (by decide)).active
    (by rw [hxl]; omega_using [hql1]) (by simp only [hxl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm) fun s1 h1 => ?_)
  obtain hf1 : Outside L.base 128 (deriveExtent - 128) s.mem s1.mem := h1.frame.mono (by decide) (by decide)
  obtain hg1 := hg.frame hr h1.ready hf1 h1.keep (by decide) (by simp [stablePointer, Core.generator])
  obtain hq1 := hqb.frame hr h1.ready hf1 h1.keep (by decide) (by change Field.q ≠ .mask; decide)
  obtain hx1 := hx.frame hr h1.ready hf1 h1.keep (by decide) (by simp [stablePointer, Core.privateScalar])
  obtain hm1 : word s1.mem L.base Field.mask.offset = mask (decide (0 < Spec.Dsa.decodeBE xb ∧
      Spec.Dsa.decodeBE xb < L.subgroup) && true) := by
    simpa only [Bool.false_eq_true, ↓reduceIte, ModulusSide.value] using h1.mask
  -- y = g^x mod p, at t2, and whether g^q mod p = 1
  refine WP.seq (WP.mono (SharedPower.readySharedPow_ok M h1.ready hp hpo Core.generator Core.privateScalar
    (by trivial) (by trivial) (hg1.shrink (by decide)).active (hx1.shrink (by decide)).active
    (hq1.shrink (by decide)).active.source (hql.trans hxl.symm) (by rw [hgl]; omega_using [hp384])
    (by rw [hgl]) (by rw [hxl]; omega_using [hql1]) (by rw [hxl]; omega_using [hqu])
    t2 (by decide) hend hm1) fun s2 ⟨u, h2, h2c⟩ => ?_)
  obtain hfu : Outside L.base 128 (deriveExtent - 128) s1.mem u.mem :=
    (h2.scheduleFrame (by decide) hend).mono (by decide) (by decide)
  obtain hf2 : Outside L.base 128 (deriveExtent - 128) u.mem s2.mem := h2c.frame.mono (by decide) (by decide)
  obtain hg2 := (hg1.frame h1.ready h2.ready hfu h2.keep (by decide) (by simp [stablePointer, Core.generator])).frame
    h2.ready h2c.ready hf2 h2c.keep (by decide) (by simp [stablePointer, Core.generator])
  obtain hq2 := (hq1.frame h1.ready h2.ready hfu h2.keep (by decide) (by change Field.q ≠ .mask; decide)).frame
    h2.ready h2c.ready hf2 h2c.keep (by decide) (by change Field.q ≠ .mask; decide)
  obtain hs2 : Scr s2 L.base deriveExtent := hs.congr ((h1.keep.trans h2.keep).trans h2c.keep).wr
  obtain hout := h2c.preserve h2.ready (Nat.le_refl _) (by change Field.pLen ≠ .mask; decide) (by trivial)
    (h2.output (by decide) hend)
  obtain hb2 : ∀ i (hi : i < L.pLen), s2.mem (off L.base t2 + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi) :=
    fun i hi => hout.source.val i (by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)
  refine WP.mono (deriveCopyPrefix_ok M h2c.ready hs2 hp hq hpo hqo hpf hqf hg2 hq2 hgl hy hb2 h2c.mask)
    fun t ⟨ht, hmt, hyt, hft, hkt⟩ => ?_
  exact ⟨ht, hmt, hyt, ((hf1.trans hfu).trans hf2).trans hft,
    (((h1.keep.trans h2.keep).trans h2c.keep).trans hkt).mono (by decide)⟩

theorem and_rotate (g a b c r : Bool) : (g && (a && (b && (c && r)))) = (a && (b && (c && (g && r)))) := by
  cases g <;> cases a <;> cases b <;> cases c <;> rfl

theorem deriveSuccess_ok (M : Mont) {p : DeriveInput} {original st : State}
    (h : DerivePre p original) (hs : DeriveShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
      SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm), Generate.writeKey, .block SignVerify.result]) st
      (DerivePost p original) := by
  obtain ⟨hsize, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  obtain hpf : Spec.Dsa.decodeBE p.pb ≤ 256 ^ p.pLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.pb; rw [p.pbLength] at hh; exact Nat.le_of_lt hh
  obtain hqf : Spec.Dsa.decodeBE p.qb ≤ 256 ^ p.qLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.qb; rw [p.qbLength] at hh; exact Nat.le_of_lt hh
  refine WP.seq (WP.mono (deriveInitialize_ok h hs ha) fun u ⟨pi, qi, hr, ho, hm, hframe, hkeep⟩ => ?_)
  let L := (p.layout original h.pLength).withInverses pi qi
  obtain hsu : Scr u p.base deriveExtent := h.scratch.congr hkeep.wr
  apply wpAppendSequences (a := [Checks.range qWorkspace Core.privateScalar,
    SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine WP.mono (deriveBody_ok (L := L) M hr hsu hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar
    p.gbLength p.qbLength p.xLength rfl hm) fun v ⟨hv, hmv, hyv, hfv, hkv⟩ => ?_
  obtain hframe' : InScr p.base deriveExtent original.mem v.mem :=
    hframe.trans (InScr.of_outside hfv (by decide))
  obtain hkeep' : Keep coreRegs original v := (hkeep.trans hkv).mono (by decide)
  have hmv' : word v.mem p.base Field.mask.offset = mask (prefixAccepted L p.gb p.yb
      (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.qb) L.modulus = 1) &&
        (decide (0 < Spec.Dsa.decodeBE p.x ∧ Spec.Dsa.decodeBE p.x < L.subgroup) && true))) := hmv
  refine deriveOutput_ok h pi qi hv hmv' hyv hframe' hkeep' ?_
  obtain hyfit : p.y < 256 ^ p.pLen :=
    Nat.lt_of_lt_of_le (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp1])) hpf
  rw [p.derive_eq, ha, Bool.true_and, and_rotate]
  unfold prefixAccepted
  rw [VG.Proof.Dsa.decodeBE_encodeBE hyfit]
  rfl

/-- Key derivation: the checks of the domain and the key, `g^q = 1` among
them, and the key written out. -/
theorem deriveMain_ok (M : Mont) {p : DeriveInput} {s0 : State} (h : DerivePre p s0) :
    WP isa (Generate.deriveKey M.mm) s0 (DerivePost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (deriveShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => deriveRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    rw [hs.branch, ha]; rfl
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => deriveSuccess_ok M h hs ha)
    change some (s.gpr .x3 == (0#64)) = some false
    rw [hs.branch, ha]; rfl

theorem deriveCheckedMain_ok (M : Mont) {p : DeriveInput} {s0 : State} (h : DerivePre p s0)
    (hc : Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params = true) :
    WP isa (Generate.deriveChecked M.mm) s0 (DerivePost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (deriveShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => deriveRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    rw [hs.branch, ha]; rfl
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => deriveCheckedSuccess_ok M h hs ha hc)
    change some (s.gpr .x3 == (0#64)) = some false
    rw [hs.branch, ha]; rfl

end VG.Proof.Dsa.AArch64
