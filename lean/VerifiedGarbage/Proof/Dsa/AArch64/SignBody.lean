module

public import VerifiedGarbage.Proof.Dsa.AArch64.SignBytesSpec
public import VerifiedGarbage.Proof.Dsa.AArch64.SignRelease
import VerifiedGarbage.Proof.Dsa.SizeBounds

/-! # Complete computation and signature release from initialized scratch -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure SigningOperands (L : ExecutionLayout) (data : SignValues) (yb qb : List Byte) (s : State) : Prop where
  generator : OperandBytes s L.base usedBytes Core.generator data.generator
  publicValue : OperandBytes s L.base usedBytes Core.publicValue yb
  subgroup : OperandBytes s L.base usedBytes ⟨.input .q, .qLen⟩ qb
  privateScalar : OperandBytes s L.base usedBytes Core.privateScalar data.privateScalar
  nonce : OperandBytes s L.base usedBytes Core.nonce data.nonce
  digest : OperandBytes s L.base usedBytes Core.digest data.digest
  generatorLength : data.generator.length = L.pLen
  publicLength : yb.length = L.pLen
  subgroupLength : qb.length = L.qLen
  privateLength : data.privateScalar.length = L.qLen
  nonceLength : data.nonce.length = L.qLen
  digestBound : data.digest.length < 2 ^ 64
  subgroupValue : Spec.Dsa.decodeBE qb = L.subgroup

def signBody (mul : Nat → Nat → Nat → Prog isa) : Prog isa := .seq (signCompute mul) signRelease

theorem signBody_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : SignValues) {yb qb : List Byte} (h : SigningOperands L data yb qb s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa (signBody M.mm) s0 fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (signAccepted L data yb valid).toNat ∧
      Spec.Rsa.bytesAt t.mem (L.fields .out) (2 * L.qLen) =
        (if signAccepted L data yb valid then Spec.Dsa.encodeBE L.qLen (data.r L) ++
          Spec.Dsa.encodeBE L.qLen (data.s L) else List.replicate (2 * L.qLen) 0) ∧
      (∀ x, usedBytes ≤ ofs L.base x → (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) →
        t.mem x = s0.mem x) ∧ Keep coreRegs s0 t := by
  unfold signBody
  refine WP.seq (WP.mono (signCompute_ok M h0 hp hq hop hoq hpf hqf data h.generator h.publicValue
    h.subgroup h.privateScalar h.nonce h.digest h.generatorLength h.publicLength h.subgroupLength
    h.privateLength h.nonceLength h.digestBound h.subgroupValue hm)
    fun s1 ⟨h1, hm1, hr1, hs1, hf1, hk1⟩ => ?_)
  refine WP.mono (signRelease_ok h1 hm1 (fun i hi => by rw [hk1.wr]; exact hw i hi) hsep)
    fun t ⟨ha, hb, hf, hk⟩ => ?_
  refine ⟨ha, ?_, ?_, (hk1.trans hk).mono (by decide)⟩
  · rw [hr1, hs1] at hb
    exact hb
  · intro x hx ho
    exact (hf x ho).trans (hf1 x (Or.inr (by
      have hu : 128 ≤ usedBytes := by decide
      omega)))

theorem signBody_spec (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (data : SignValues) {yb qb key digest : List Byte} {n : Nat}
    (h : SigningOperands L data yb qb s0)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hkl : key.length = 3 * L.pLen + 2 * L.qLen)
    (hk : Spec.Dsa.privateKeyBytes L.pLen L.qLen key = data.key L yb)
    (hqn : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n)
    (hm : word s0.mem L.base Field.mask.offset = mask true)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa (signBody M.mm) s0 fun t =>
      let result := Spec.Dsa.signBytes L.pLen L.qLen key data.nonce digest
      t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.signStatus result) ∧
      Spec.Rsa.bytesAt t.mem (L.fields .out) (2 * L.qLen) = result.getD (List.replicate (2 * L.qLen) 0) ∧
      (∀ x, usedBytes ≤ ofs L.base x → (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) →
        t.mem x = s0.mem x) ∧ Keep coreRegs s0 t := by
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have he := signBytes_compute L data yb key digest n hsize hop hoq hpf hqf h.publicLength hkl h.nonceLength hk hqn hz
  refine WP.mono (signBody_ok M h0 hp hq hop hoq hpf hqf data h hm hw hsep) fun t ht => ?_
  rw [he]
  cases hc : signAccepted L data yb true <;> simpa only [hc, Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true, ↓reduceIte,
    Spec.Dsa.signStatus, Option.isSome_none, Option.isSome_some, Option.getD_none, Option.getD_some] using ht

end VG.Proof.Dsa.AArch64
