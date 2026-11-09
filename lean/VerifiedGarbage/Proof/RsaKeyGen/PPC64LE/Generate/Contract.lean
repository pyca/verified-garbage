module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32

/-! # RSA key generation's contract in terms of the machine (PPC64LE)

`vg_rsa_generate(key = r3, key_len = r4, used = r5, rand = r6,
rand_len = r7, scratch = r8, scratch_len = r9, state = r10)`: eight
arguments in registers. It uses 1088 bytes of stack: its frame of 144, the
frame of 48 saving the link register, and the prime search's call (a frame
of 128 and the search's 768) or the key's (a frame of 176; the key uses no
stack below its own).

The prime search's candidates read RSA's table of trial division
(`TrialTable32`), so the controller's contract is under `abi.withConsts`, as
the search's is (`Proof/RsaKeyGen/PPC64LE/Search/Contract.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Generate

open VG VG.PPC64LE
open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Spec.RsaKeyGen

/-- The stack the controller uses below the stack pointer. -/
abbrev stackUse : Nat := 1088

/-- The table of trial division. -/
abbrev tables : List (String × List (BitVec 64)) := Impl.RsaKeyGen.TrialTable32.consts

def inKey (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .r5, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩
def inState (s : State) : Region := ⟨s.gpr .r10, 56⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inKey s, inUsed s, inScr s, inState s]
def inReads (s : State) : List Region := [inRand s]

/-- The primes' octets, the exponent, the tape and the progress on entry. -/
abbrev genLen (s : State) : Nat := (s.mem.readW (s.gpr .r10 + 8) 64).toNat
abbrev genE (s : State) : List Byte := bytesAt s.mem (s.gpr .r10 + 48) 8
abbrev genRand (s : State) : List Byte := bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
abbrev genProgress (s : State) : KeyProgress := keyProgressAt s.mem (s.gpr .r3) (s.gpr .r10) (genLen s)

/-- The precondition without the table. -/
def basePre (s : State) : Prop :=
  stackUse ≤ s.sp.toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp stackUse).Disjoint r) ∧
    primeLenValid (genLen s) ∧ (s.gpr .r4).toNat = 9 * genLen s ∧
    Spec.Rsa.scratchWords (2 * genLen s) ≤ (s.gpr .r9).toNat ∧
    (s.mem.readW (s.gpr .r10) 64).toNat ≤ primeLimit (8 * genLen s) (Spec.Rsa.os2ip (genE s)) ∧
    s.mem.readW (s.gpr .r10 + 16) 64 = BitVec.ofNat 64 (primeEntropy (genLen s)) ∧
    (s.mem.readW (s.gpr .r10 + 32) 64).toNat ≤ 1 ∧
    (s.gpr .r7).toNat ≤ primeEntropy (genLen s)

def genPre (s : State) : Prop := basePre (stripConsts tables s) ∧ ConstsOk tables stackUse s

def genResult (s : State) : KeySearchResult := keySearch (genLen s) (genE s) (genProgress s) (genRand s)

def genPost (s t : State) : Prop :=
  ((t.gpr .r3).setWidth 32).toNat = (genResult s).keyStatus ∧
    bytesAt t.mem (s.gpr .r3) (9 * genLen s) = keySearchBytes (genLen s) (genResult s) ∧
    wordsAt t.mem (s.gpr .r5) 1 = [BitVec.ofNat 64 (genResult s).used] ∧
    ∃ requested, wordsAt t.mem (s.gpr .r10) 6 = [BitVec.ofNat 64 (genResult s).progress.remaining,
      BitVec.ofNat 64 (genLen s), BitVec.ofNat 64 (primeEntropy (genLen s)), BitVec.ofNat 64 requested,
      BitVec.ofNat 64 (if (genResult s).progress.phase = .p then 0 else 1),
      BitVec.ofNat 64 (genResult s).progress.left] ∧
      bytesAt t.mem (s.gpr .r10 + 48) 8 = genE s ∧
      (genResult s).Requests (primeEntropy (genLen s)) requested

/-- What timing may depend on: the arguments, the state's words, the
result's status, consumption, octets left and trace, and the table's
address. -/
def genPub (s t : State) : Prop :=
  s.sp = t.sp ∧
    s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r5 = t.gpr .r5 ∧ s.gpr .r6 = t.gpr .r6 ∧
    s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9 ∧ s.gpr .r10 = t.gpr .r10 ∧
    wordsAt s.mem (s.gpr .r10) 7 = wordsAt t.mem (t.gpr .r10) 7 ∧
    (genResult s).keyStatus = (genResult t).keyStatus ∧ (genResult s).used = (genResult t).used ∧
    (genResult s).available = (genResult t).available ∧ (genResult s).trace = (genResult t).trace ∧
    s.syms Impl.RsaKeyGen.TrialTable32.symbol = t.syms Impl.RsaKeyGen.TrialTable32.symbol

def genContract : Contract isa where
  pre := genPre
  post := genPost
  pub := genPub

end VG.Proof.RsaKeyGen.PPC64LE.Generate
