module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract

/-! # RSA key generation's contract in terms of the machine (AArch64)

`vg_rsa_generate(key = x0, key_len = x1, used = x2, rand = x3, rand_len = x4,
scratch = x5, scratch_len = x6, state = x7)`: eight arguments in registers.
It uses 416 bytes of stack: its frame of 160, the frame saving `x30`, and the
prime search's call (a frame of 32 and the search's 208) or the key's (a
frame of 80; the key has no frames).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG VG.AArch64
open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Spec.RsaKeyGen

/-- The stack the controller uses below the stack pointer. -/
abbrev stackUse : Nat := 416

def inKey (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .x2, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat * 8⟩
def inState (s : State) : Region := ⟨s.gpr .x7, 56⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inKey s, inUsed s, inScr s, inState s]
def inReads (s : State) : List Region := [inRand s]

/-- The primes' octets, the exponent, the tape and the progress on entry. -/
abbrev genLen (s : State) : Nat := (s.mem.readW (s.gpr .x7 + 8) 64).toNat
abbrev genE (s : State) : List Byte := bytesAt s.mem (s.gpr .x7 + 48) 8
abbrev genRand (s : State) : List Byte := bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat
abbrev genProgress (s : State) : KeyProgress := keyProgressAt s.mem (s.gpr .x0) (s.gpr .x7) (genLen s)

def genPre (s : State) : Prop :=
  stackUse ≤ s.sp.toNat ∧ s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp stackUse).Disjoint r) ∧
    primeLenValid (genLen s) ∧ (s.gpr .x1).toNat = 9 * genLen s ∧
    Spec.Rsa.scratchWords (2 * genLen s) ≤ (s.gpr .x6).toNat ∧
    (s.mem.readW (s.gpr .x7) 64).toNat ≤ primeLimit (8 * genLen s) (Spec.Rsa.os2ip (genE s)) ∧
    s.mem.readW (s.gpr .x7 + 16) 64 = BitVec.ofNat 64 (primeEntropy (genLen s)) ∧
    (s.mem.readW (s.gpr .x7 + 32) 64).toNat ≤ 1 ∧
    (s.gpr .x4).toNat ≤ primeEntropy (genLen s)

def genResult (s : State) : KeySearchResult := keySearch (genLen s) (genE s) (genProgress s) (genRand s)

def genPost (s t : State) : Prop :=
  ((t.gpr .x0).setWidth 32).toNat = (genResult s).keyStatus ∧
    bytesAt t.mem (s.gpr .x0) (9 * genLen s) = keySearchBytes (genLen s) (genResult s) ∧
    wordsAt t.mem (s.gpr .x2) 1 = [BitVec.ofNat 64 (genResult s).used] ∧
    ∃ requested, wordsAt t.mem (s.gpr .x7) 6 = [BitVec.ofNat 64 (genResult s).progress.remaining,
      BitVec.ofNat 64 (genLen s), BitVec.ofNat 64 (primeEntropy (genLen s)), BitVec.ofNat 64 requested,
      BitVec.ofNat 64 (if (genResult s).progress.phase = .p then 0 else 1),
      BitVec.ofNat 64 (genResult s).progress.left] ∧
      bytesAt t.mem (s.gpr .x7 + 48) 8 = genE s ∧
      (genResult s).Requests (primeEntropy (genLen s)) requested

/-- What timing may depend on: the arguments, the state's words, and the
result's status, consumption, octets left and trace. -/
def genPub (s t : State) : Prop :=
  s.sp = t.sp ∧
    s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧
    s.gpr .x4 = t.gpr .x4 ∧ s.gpr .x5 = t.gpr .x5 ∧ s.gpr .x6 = t.gpr .x6 ∧ s.gpr .x7 = t.gpr .x7 ∧
    wordsAt s.mem (s.gpr .x7) 7 = wordsAt t.mem (t.gpr .x7) 7 ∧
    (genResult s).keyStatus = (genResult t).keyStatus ∧ (genResult s).used = (genResult t).used ∧
    (genResult s).available = (genResult t).available ∧ (genResult s).trace = (genResult t).trace

def genContract : Contract isa where
  pre := genPre
  post := genPost
  pub := genPub

end VG.Proof.RsaKeyGen.AArch64.Generate
