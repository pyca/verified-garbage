module

public import VerifiedGarbage.Proof.Dsa.AArch64.CoreSign
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicKey
public import VerifiedGarbage.Proof.Dsa.AArch64.PrivateKey
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Signing computation, including every key and scalar rejection mask -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def privateAccepted (L : ExecutionLayout) (data : SignValues) (yb : List Byte) (valid : Bool) : Bool :=
  decide (Spec.Dsa.encodeBE L.pLen
    (Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) (Spec.Dsa.decodeBE data.privateScalar) L.modulus) = yb) &&
  (decide (0 < Spec.Dsa.decodeBE data.nonce ∧ Spec.Dsa.decodeBE data.nonce < L.subgroup) &&
  (decide (0 < Spec.Dsa.decodeBE data.privateScalar ∧ Spec.Dsa.decodeBE data.privateScalar < L.subgroup) &&
    publicAccepted L data.generator yb valid))

def signAccepted (L : ExecutionLayout) (data : SignValues) (yb : List Byte) (valid : Bool) : Bool :=
  !decide (∀ b ∈ Spec.Dsa.encodeBE L.qLen (data.s L), b = 0) &&
  (!decide (∀ b ∈ Spec.Dsa.encodeBE L.qLen (data.r L), b = 0) && privateAccepted L data yb valid)

def signCompute (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  Checks.publicKey mul, Checks.privateKey mul, Core.sign mul,
  Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true]

theorem signCompute_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : SignValues) {yb qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator data.generator)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hx : OperandBytes s0 L.base usedBytes Core.privateScalar data.privateScalar)
    (hn : OperandBytes s0 L.base usedBytes Core.nonce data.nonce)
    (hz : OperandBytes s0 L.base usedBytes Core.digest data.digest)
    (hgl : data.generator.length = L.pLen) (hyl : yb.length = L.pLen) (hqlen : qb.length = L.qLen)
    (hxl : data.privateScalar.length = L.qLen) (hnl : data.nonce.length = L.qLen)
    (hzl : data.digest.length < 2 ^ 64) (hqval : Spec.Dsa.decodeBE qb = L.subgroup)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (signCompute M.mm) s0 fun s5 =>
      Ready L s5 ∧ word s5.mem L.base Field.mask.offset = mask (signAccepted L data yb valid) ∧
      Spec.Rsa.bytesAt s5.mem (off L.base r) L.qLen = Spec.Dsa.encodeBE L.qLen (data.r L) ∧
      Spec.Rsa.bytesAt s5.mem (off L.base s) L.qLen = Spec.Dsa.encodeBE L.qLen (data.s L) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s5.mem ∧ Keep coreRegs s0 s5 := by
  obtain ⟨hql, hqu, _, _⟩ := L.widths
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega
  have hr : r + L.qLen ≤ usedBytes := by unfold r usedBytes; omega
  have hs : s + L.qLen ≤ usedBytes := by unfold s usedBytes; omega
  unfold signCompute
  refine WP.seq (WP.mono (publicKey_ok M h0 hp hq hop hoq hpf hqf hg hy hqb hgl hyl hqlen hqval hm)
    fun s1 ⟨h1, hm1, hqm1, hf1, hk1⟩ => ?_)
  have hg1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.generator]) hg
  have hy1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.publicValue]) hy
  have hx1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.privateScalar]) hx
  have hn1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.nonce]) hn
  have hz1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.digest]) hz
  refine WP.seq (WP.mono (privateKey_ok M h1 hp hop hg1 hy1 hx1 hn1 hgl hyl hxl hnl hm1)
    fun s2 ⟨h2, hm2, hqm2bytes, hf2, hk2⟩ => ?_)
  have hg2 := h1.preserveExternal h2 hf2 hk2 (by decide) (by simp [stablePointer, Core.generator]) hg1
  have hx2 := h1.preserveExternal h2 hf2 hk2 (by decide) (by simp [stablePointer, Core.privateScalar]) hx1
  have hn2 := h1.preserveExternal h2 hf2 hk2 (by decide) (by simp [stablePointer, Core.nonce]) hn1
  have hz2 := h1.preserveExternal h2 hf2 hk2 (by decide) (by simp [stablePointer, Core.digest]) hz1
  have hqm1bytes := operand_bytesAt hqm1
  rw [encodeBE_length] at hqm1bytes
  have hqm2 := h2.encodedLocal .q qMinusTwo (L.subgroup - 2) (by decide) hqm (hqm2bytes.trans hqm1bytes)
  refine WP.seq (WP.mono (coreSign_ok M h2 hp hq hop hoq hpf hqf data hg2 hn2 hx2 hz2 hgl hnl hxl hzl hqm2)
    fun s3 ⟨h3, hr3bytes, hs3bytes, hf3, hm3eq, hk3⟩ => ?_)
  have hm3 : word s3.mem L.base Field.mask.offset = mask (privateAccepted L data yb valid) := hm3eq.trans hm2
  have hr3 := h3.encodedLocal .q r (data.r L) (by decide) hr hr3bytes
  have hs3 := h3.encodedLocal .q s (data.s L) (by decide) hs hs3bytes
  refine WP.seq (WP.mono (readyZero_ok h3 (Core.scalar r) (by change r < 2 ^ 16; decide) hr3
    (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) true hm3) fun s4 h4 => ?_)
  have hr4 := h4.preserve h3 (Nat.le_refl _) (by decide) (by trivial) hr3
  have hs4 := h4.preserve h3 (Nat.le_refl _) (by decide) (by trivial) hs3
  refine WP.mono (readyZero_ok h4.ready (Core.scalar s) (by change s < 2 ^ 16; decide) hs4
    (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) true h4.mask) fun s5 h5 => ?_
  have hr5 := h5.preserve h4.ready (Nat.le_refl _) (by decide) (by trivial) hr4
  have hs5 := h5.preserve h4.ready (Nat.le_refl _) (by decide) (by trivial) hs4
  refine ⟨h5.ready, ?_, ?_, ?_, (((hf1.trans hf2).trans hf3).trans h4.scheduleFrame).trans h5.scheduleFrame,
    ((((hk1.trans hk2).trans hk3).trans h4.keep).trans h5.keep).mono (by decide)⟩
  · have hm5 := h5.mask
    simp only [↓reduceIte, ModulusSide.length] at hm5
    exact hm5
  · have hh := operand_bytesAt hr5
    rw [encodeBE_length] at hh
    exact hh
  · have hh := operand_bytesAt hs5
    rw [encodeBE_length] at hh
    exact hh

end VG.Proof.Dsa.AArch64
