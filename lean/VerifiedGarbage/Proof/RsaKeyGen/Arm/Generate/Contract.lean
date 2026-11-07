module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.TCB.Arm.Target

/-! # RSA key generation's contract in terms of the machine (ARMv7)

`vg_rsa_generate(key = r0, key_len = r1, used = r2, rand = r3, rand_len,
scratch, scratch_len, state)`: four arguments in registers and four on the
stack. It uses 256 bytes of stack: the frame of 40 bytes saving the
callee-saved registers, and the prime search's call (a frame of 32 and the
search's 184) or the key's (a frame of 56 and the key's 56).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm
open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Spec.RsaKeyGen

/-- The stack the controller uses below the stack pointer. -/
abbrev stackUse : Nat := 256

def inKey (s : State) : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
def inUsed (s : State) : Region := ⟨State.addr (s.gpr .r2), 8⟩
def inRand (s : State) : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
def inScr (s : State) : Region := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat * 8⟩
def inState (s : State) : Region := ⟨State.addr (stackArg s 3), 56⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inKey s, inUsed s, inScr s, inState s]
def inReads (s : State) : List Region := [inRand s, inArgs s]

/-- The stack below the stack pointer the controller uses. -/
def inStack (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 stackUse, stackUse⟩

/-- The primes' octets, the exponent, the tape and the progress on entry. -/
abbrev genStp (s : State) : Addr := State.addr (stackArg s 3)
abbrev genLen (s : State) : Nat := (s.mem.readW (genStp s + 8) 64).toNat
abbrev genE (s : State) : List Byte := bytesAt s.mem (genStp s + 48) 8
abbrev genRand (s : State) : List Byte := bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat
abbrev genProgress (s : State) : KeyProgress :=
  keyProgressAt s.mem (State.addr (s.gpr .r0)) (genStp s) (genLen s)

def genPre (s : State) : Prop :=
  stackUse ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 32 ∧ s.rd = inReads s ∧ s.wr = inWrites s ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (inStack s).Disjoint r) ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8 ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 32 ∧ (stackArg s 3).toNat + 56 ≤ 2 ^ 32 ∧
    primeLenValid (genLen s) ∧ (s.gpr .r1).toNat = 9 * genLen s ∧
    Spec.Rsa.scratchWords (2 * genLen s) ≤ (stackArg s 2).toNat ∧
    (s.mem.readW (genStp s) 64).toNat ≤ primeLimit (8 * genLen s) (Spec.Rsa.os2ip (genE s)) ∧
    s.mem.readW (genStp s + 16) 64 = BitVec.ofNat 64 (primeEntropy (genLen s)) ∧
    (s.mem.readW (genStp s + 32) 64).toNat ≤ 1 ∧
    (stackArg s 0).toNat ≤ primeEntropy (genLen s)

def genResult (s : State) : KeySearchResult := keySearch (genLen s) (genE s) (genProgress s) (genRand s)

def genPost (s t : State) : Prop :=
  ((t.gpr .r1 ++ t.gpr .r0).setWidth 32).toNat = (genResult s).keyStatus ∧
    bytesAt t.mem (State.addr (s.gpr .r0)) (9 * genLen s) = keySearchBytes (genLen s) (genResult s) ∧
    wordsAt t.mem (State.addr (s.gpr .r2)) 1 = [BitVec.ofNat 64 (genResult s).used] ∧
    ∃ requested, wordsAt t.mem (genStp s) 6 = [BitVec.ofNat 64 (genResult s).progress.remaining,
      BitVec.ofNat 64 (genLen s), BitVec.ofNat 64 (primeEntropy (genLen s)), BitVec.ofNat 64 requested,
      BitVec.ofNat 64 (if (genResult s).progress.phase = .p then 0 else 1),
      BitVec.ofNat 64 (genResult s).progress.left] ∧
      bytesAt t.mem (genStp s + 48) 8 = genE s ∧
      (genResult s).Requests (primeEntropy (genLen s)) requested

/-- What timing may depend on: the arguments, the state's words, and the
result's status, consumption, octets left and trace. -/
def genPub (s t : State) : Prop :=
  s.sp = t.sp ∧
    s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧
    (∀ j < 4, stackArg s j = stackArg t j) ∧
    wordsAt s.mem (genStp s) 7 = wordsAt t.mem (genStp t) 7 ∧
    (genResult s).keyStatus = (genResult t).keyStatus ∧ (genResult s).used = (genResult t).used ∧
    (genResult s).available = (genResult t).available ∧ (genResult s).trace = (genResult t).trace

def genContract : Contract isa where
  pre := genPre
  post := genPost
  pub := genPub

end VG.Proof.RsaKeyGen.Arm.Generate
