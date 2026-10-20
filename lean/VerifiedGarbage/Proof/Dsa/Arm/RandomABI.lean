module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
public import VerifiedGarbage.Proof.Dsa.DomainShape

/-!
# The randomized signer's resources on 32-bit ARM, from the shared contract

`vg_dsa_sign_random(out, out_len, used, key, key_len, p_len, q_len, digest,
digest_len, rand, rand_len, scratch, scratch_len)` has its first four
arguments in `r0`–`r3` and the others on the stack (AAPCS). The 144 bytes
of stack below `sp` hold its frame (112 bytes) and, below it, the stack
arguments it pushes for the supplied-nonce signer (32 bytes).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm

section
variable (s : State)

/-- The caller's buffers, and its stack arguments. -/
abbrev rOut : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
abbrev rUsed : Region := ⟨State.addr (s.gpr .r2), 8⟩
abbrev rKeyR : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
abbrev rDigestR : Region := ⟨State.addr (stackArg s 3), (stackArg s 4).toNat⟩
abbrev rRandR : Region := ⟨State.addr (stackArg s 5), (stackArg s 6).toNat⟩
abbrev rScratch : Region := ⟨State.addr (stackArg s 7), (stackArg s 8).toNat * 8⟩
abbrev rArgs : Region := ⟨State.addr s.sp, 36⟩

/-- The lowest byte of the stack the signer uses, 144 bytes below `sp`. -/
abbrev rLow : Addr := State.addr s.sp - 144#64

abbrev rStack : Region := ⟨rLow s, 144⟩

end

structure RandomABI (s : State) : Prop where
  stackLow : 144 ≤ s.sp.toNat
  stackBound : s.sp.toNat + 36 ≤ 2 ^ 32
  rd : s.rd = [rKeyR s, rDigestR s, rRandR s, rArgs s]
  wr : s.wr = [rOut s, rUsed s, rScratch s]
  outUsed : (rOut s).Disjoint (rUsed s)
  outKey : (rOut s).Disjoint (rKeyR s)
  outDigest : (rOut s).Disjoint (rDigestR s)
  outRand : (rOut s).Disjoint (rRandR s)
  outScratch : (rOut s).Disjoint (rScratch s)
  outArgs : (rOut s).Disjoint (rArgs s)
  usedKey : (rUsed s).Disjoint (rKeyR s)
  usedDigest : (rUsed s).Disjoint (rDigestR s)
  usedRand : (rUsed s).Disjoint (rRandR s)
  usedScratch : (rUsed s).Disjoint (rScratch s)
  usedArgs : (rUsed s).Disjoint (rArgs s)
  keyScratch : (rKeyR s).Disjoint (rScratch s)
  digestScratch : (rDigestR s).Disjoint (rScratch s)
  randScratch : (rRandR s).Disjoint (rScratch s)
  scratchArgs : (rScratch s).Disjoint (rArgs s)
  stackOut : (rStack s).Disjoint (rOut s)
  stackUsed : (rStack s).Disjoint (rUsed s)
  stackKey : (rStack s).Disjoint (rKeyR s)
  stackDigest : (rStack s).Disjoint (rDigestR s)
  stackRand : (rStack s).Disjoint (rRandR s)
  stackScratch : (rStack s).Disjoint (rScratch s)
  stackArgs : (rStack s).Disjoint (rArgs s)
  outBound : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  usedBound : (s.gpr .r2).toNat + 8 ≤ 2 ^ 32
  keyBound : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  digestBound : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 32
  randBound : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 32
  scratchBound : (stackArg s 7).toNat + (stackArg s 8).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (stackArg s 1).toNat (stackArg s 2).toNat
  outLength : (s.gpr .r1).toNat = 2 * (stackArg s 2).toNat
  keyLength : (stackArg s 0).toNat = 3 * (stackArg s 1).toNat + 2 * (stackArg s 2).toNat
  scratchLength : Spec.Dsa.randomSignScratchWords (stackArg s 1).toNat ≤ (stackArg s 8).toNat

theorem randomABI_of {s : State} (h : (Spec.Dsa.randomSignContract Arm.abi 144).pre s) : RandomABI s := by
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.stackArgAddr, BitVec.add_zero] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36⟩

/-! ## What the specification reads -/

/-- The inputs of the specification. -/
def rInput (s₀ : State) : VG.Proof.Dsa.RandomSignInput where
  pLen := (stackArg s₀ 1).toNat
  qLen := (stackArg s₀ 2).toNat
  key := Spec.Rsa.bytesAt s₀.mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat
  digest := Spec.Rsa.bytesAt s₀.mem (State.addr (stackArg s₀ 3)) (stackArg s₀ 4).toNat
  rand := Spec.Rsa.bytesAt s₀.mem (State.addr (stackArg s₀ 5)) (stackArg s₀ 6).toNat

/-- The specification's result. -/
abbrev rResult (s₀ : State) : Spec.Dsa.RandomSignResult :=
  Spec.Dsa.randomSignBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key (rInput s₀).digest (rInput s₀).rand

/-- The public key bytes of the entry. -/
abbrev keyLeak (s₀ : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key

/-- q's bytes, and their address. -/
def rQBytes (s₀ : State) : List Byte := ((rInput s₀).key.drop (rInput s₀).pLen).take (rInput s₀).qLen
def rQ (s₀ : State) : BitVec 32 := s₀.gpr .r3 + stackArg s₀ 1

/-- q's significant bytes, and the first of them. -/
abbrev rWidth (s₀ : State) : Nat := (VG.Proof.Dsa.significant (rQBytes s₀)).1
abbrev rLead (s₀ : State) : Byte := (VG.Proof.Dsa.significant (rQBytes s₀)).2

/-- q, as the specification reads it. -/
abbrev rq (s₀ : State) : Nat := Spec.Dsa.decodeBE (rQBytes s₀)

theorem rQ_decode (s₀ : State) :
    rq s₀ = (Spec.Dsa.privateKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key).params.q := rfl

theorem rBytes_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem rQBytes_length {s₀ : State} (A : RandomABI s₀) : (rQBytes s₀).length = (stackArg s₀ 2).toNat := by
  simp only [rQBytes, rInput, List.length_take, List.length_drop, rBytes_length, A.keyLength]
  omega

theorem rQBytes_le {s₀ : State} (A : RandomABI s₀) : (rQBytes s₀).length ≤ 32 := by
  rw [rQBytes_length A]; have := A.lengths; unfold Spec.Dsa.lengthsValid at this; omega

theorem rQBytes_pos {s₀ : State} (A : RandomABI s₀) : 0 < (rQBytes s₀).length := by
  rw [rQBytes_length A]; have := A.lengths; unfold Spec.Dsa.lengthsValid at this; omega

theorem rWidth_le (s₀ : State) : rWidth s₀ ≤ (rQBytes s₀).length :=
  VG.Proof.Dsa.significant_fits _

end VG.Proof.Dsa.Arm
