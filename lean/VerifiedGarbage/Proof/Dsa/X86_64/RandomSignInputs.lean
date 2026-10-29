module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFrame
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Read-only inputs and the sampler context derived from the public ABI. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomInput (s : State) : VG.Proof.Dsa.RandomSignInput where
  pLen := (s.gpr .r9).toNat
  qLen := (stackArg s 0).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat
  digest := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat
  rand := Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat

def randomQBytes (s : State) : List Byte :=
  ((randomInput s).key.drop (randomInput s).pLen).take (randomInput s).qLen

theorem random_q_length {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    (randomQBytes s).length = (stackArg s 0).toNat := by
  simp only [randomQBytes, randomInput, List.length_take, List.length_drop, bytesAt_length, h.keyLength]
  omega

theorem random_q_decode (s : State) :
    Spec.Dsa.decodeBE (randomQBytes s) =
      (Spec.Dsa.privateKeyBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key).params.q := rfl

theorem random_initial_source {extra : Nat} {s : State} (h : RandomSignABI extra s)
    {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ s.rd)
    (hn : n ≤ 2 ^ 64) (hd : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, n⟩) :
    Src (allocState Random.frameBytes s) (randomBase s) Random.frameBytes p (Spec.Rsa.bytesAt s.mem p n) :=
  src_of_region (List.mem_append_left _ hr) hn ((hd.sub_left (random_frame_sub h)).symm)

theorem random_initial_key {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Src (allocState Random.frameBytes s) (randomBase s) Random.frameBytes (s.gpr .rcx) (randomInput s).key :=
  random_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .r8).isLt) h.stackKey

theorem random_initial_rand {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Src (allocState Random.frameBytes s) (randomBase s) Random.frameBytes (stackArg s 3) (randomInput s).rand :=
  random_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 4).isLt) h.stackRand

theorem random_initial_digest {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Src (allocState Random.frameBytes s) (randomBase s) Random.frameBytes (stackArg s 1) (randomInput s).digest :=
  random_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 2).isLt) h.stackDigest

theorem random_initial_q {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Src (allocState Random.frameBytes s) (randomBase s) Random.frameBytes
      (s.gpr .rcx + s.gpr .r9) (randomQBytes s) := by
  have hh := random_src_take (random_src_drop (random_initial_key h) (randomInput s).pLen) (randomInput s).qLen
  simpa only [randomQBytes, randomInput, ofNat_toNat64] using hh

def randomContextOf {extra : Nat} {s : State} (h : RandomSignABI extra s) (m : Mem)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) : RandomContext where
  B := randomBase s
  initialMem := m
  R := stackArg s 3
  Q := s.gpr .rcx + s.gpr .r9
  qBytes := randomQBytes s
  rand := (randomInput s).rand
  qlen := by
    rw [random_q_length h]
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  randBound := by rw [randomInput, bytesAt_length]; exact (stackArg s 4).isLt
  positive := by
    have hh := (VG.Proof.Dsa.random_valid_scan (randomQBytes s)).mp hq
    omega

end VG.Proof.Dsa.X86_64
