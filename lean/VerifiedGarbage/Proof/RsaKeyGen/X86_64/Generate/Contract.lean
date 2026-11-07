module
public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.TCB.X86_64.Target

/-! # RSA key generation's contract in terms of the machine

`vg_rsa_generate(key, key_len, used, rand, rand_len, scratch, scratch_len,
state)`: six arguments in registers and two on the stack. It uses 552 octets
of stack: its frame of 160, the prime search's call (a frame of 48, its return
address and the search's 336) or the key's (a frame of 96 and its return
address).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG VG.X86_64
open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Spec.RsaKeyGen

/-- The stack the controller uses below its return address. -/
abbrev stackUse : Nat := 552

def inKey (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .rdx, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .r9, (stackArg s 0).toNat * 8⟩
def inState (s : State) : Region := ⟨stackArg s 1, 56⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inKey s, inUsed s, inScr s, inState s]
def inReads (s : State) : List Region := [inRand s, inArgs s]

/-- The primes' octets, the exponent, the tape and the progress on entry. -/
abbrev genLen (s : State) : Nat := (s.mem.readW (stackArg s 1 + 8) 64).toNat
abbrev genE (s : State) : List Byte := bytesAt s.mem (stackArg s 1 + 48) 8
abbrev genRand (s : State) : List Byte := bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat
abbrev genProgress (s : State) : KeyProgress := keyProgressAt s.mem (s.gpr .rdi) (stackArg s 1) (genLen s)

def genPre (s : State) : Prop :=
  (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64 ∧ stackUse ≤ (s.gpr .rsp).toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r ∧
      (below (s.gpr .rsp) stackUse).Disjoint r) ∧
    primeLenValid (genLen s) ∧ (s.gpr .rsi).toNat = 9 * genLen s ∧
    Spec.Rsa.scratchWords (2 * genLen s) ≤ (stackArg s 0).toNat ∧
    (s.mem.readW (stackArg s 1) 64).toNat ≤ primeLimit (8 * genLen s) (Spec.Rsa.os2ip (genE s)) ∧
    s.mem.readW (stackArg s 1 + 16) 64 = BitVec.ofNat 64 (primeEntropy (genLen s)) ∧
    (s.mem.readW (stackArg s 1 + 32) 64).toNat ≤ 1 ∧
    (s.gpr .r8).toNat ≤ primeEntropy (genLen s)

def genResult (s : State) : KeySearchResult := keySearch (genLen s) (genE s) (genProgress s) (genRand s)

/-- The length the code asks for after `r`. -/
def keyRequested (L : Nat) (r : KeySearchResult) : Nat := Entropy.requested (primeRequest L) r

def genPost (s t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = (genResult s).keyStatus ∧
    bytesAt t.mem (s.gpr .rdi) (9 * genLen s) = keySearchBytes (genLen s) (genResult s) ∧
    wordsAt t.mem (s.gpr .rdx) 1 = [BitVec.ofNat 64 (genResult s).used] ∧
    ∃ requested, wordsAt t.mem (stackArg s 1) 6 = [BitVec.ofNat 64 (genResult s).progress.remaining,
      BitVec.ofNat 64 (genLen s), BitVec.ofNat 64 (primeEntropy (genLen s)), BitVec.ofNat 64 requested,
      BitVec.ofNat 64 (if (genResult s).progress.phase = .p then 0 else 1),
      BitVec.ofNat 64 (genResult s).progress.left] ∧
      bytesAt t.mem (stackArg s 1 + 48) 8 = genE s ∧
      (genResult s).Requests (primeEntropy (genLen s)) requested

/-- What timing may depend on: the arguments, the state's words, and the
result's status, consumption, octets left and trace. -/
def genPub (s t : State) : Prop :=
  s.gpr .rsp = t.gpr .rsp ∧
    s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧
    s.gpr .rcx = t.gpr .rcx ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9 ∧
    (∀ j < 2, stackArg s j = stackArg t j) ∧
    wordsAt s.mem (stackArg s 1) 7 = wordsAt t.mem (stackArg t 1) 7 ∧
    (genResult s).keyStatus = (genResult t).keyStatus ∧ (genResult s).used = (genResult t).used ∧
    (genResult s).available = (genResult t).available ∧ (genResult s).trace = (genResult t).trace

def genContract : Contract isa where
  pre := genPre
  post := genPost
  pub := genPub

end VG.Proof.RsaKeyGen.X86_64.Generate
