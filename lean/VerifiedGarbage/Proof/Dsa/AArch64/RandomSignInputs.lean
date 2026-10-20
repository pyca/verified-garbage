module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFrame
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Bignum.Octets

/-! Read-only inputs and the sampler context derived from the public ABI. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomInput (s : State) : VG.Proof.Dsa.RandomSignInput where
  pLen := (s.gpr .x5).toNat
  qLen := (s.gpr .x6).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat
  digest := Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat
  rand := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat

def randomQBytes (s : State) : List Byte :=
  ((randomInput s).key.drop (randomInput s).pLen).take (randomInput s).qLen

theorem random_q_length {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    (randomQBytes s).length = (s.gpr .x6).toNat := by
  simp only [randomQBytes, randomInput, List.length_take, List.length_drop, bytesAt_length, h.keyLength]
  omega

theorem random_q_decode (s : State) :
    Spec.Dsa.decodeBE (randomQBytes s) =
      (Spec.Dsa.privateKeyBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key).params.q := rfl

theorem random_initial_source {extra : Nat} {s : State} (h : RandomSignABI extra s)
    {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ s.rd)
    (hn : n ≤ 2 ^ 64) (hd : (below (s.sp) (extra + 256)).Disjoint ⟨p, n⟩) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes p (Spec.Rsa.bytesAt s.mem p n) :=
  src_of_region (List.mem_append_left _ hr) hn ((hd.sub_left (random_frame_sub h)).symm)

theorem random_initial_key {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes (s.gpr .x3) (randomInput s).key :=
  random_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x4).isLt) h.stackKey

theorem random_initial_rand {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes (stackArg s 1) (randomInput s).rand :=
  random_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 2).isLt) h.stackRand

theorem random_initial_digest {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes (s.gpr .x7) (randomInput s).digest :=
  random_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 0).isLt) h.stackDigest

theorem random_initial_q {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes
      (s.gpr .x3 + s.gpr .x5) (randomQBytes s) := by
  have hh := random_src_take (random_src_drop (random_initial_key h) (randomInput s).pLen) (randomInput s).qLen
  simpa only [randomQBytes, randomInput, ofNat_toNat64] using hh

def randomContextOf {extra : Nat} {s : State} (h : RandomSignABI extra s) (m : Mem)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) : RandomContext where
  B := randomBase s
  initialMem := m
  R := stackArg s 1
  Q := s.gpr .x3 + s.gpr .x5
  qBytes := randomQBytes s
  rand := (randomInput s).rand
  qlen := by
    rw [random_q_length h]
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  randBound := by rw [randomInput, bytesAt_length]; exact (stackArg s 2).isLt
  positive := by
    have hh := (VG.Proof.Dsa.random_valid_scan (randomQBytes s)).mp hq
    omega

end VG.Proof.Dsa.AArch64
