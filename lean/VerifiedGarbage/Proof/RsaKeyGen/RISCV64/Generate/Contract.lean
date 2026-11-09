module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32

/-! # RSA key generation's contract in terms of the machine (RISCV64)

`vg_rsa_generate(key = a0, key_len = a1, used = a2, rand = a3,
rand_len = a4, scratch = a5, scratch_len = a6, state = a7)`: eight
arguments in registers. It uses 656 bytes of stack: its frame of 112, the
frame of 16 saving `ra`, and the prime search's call (a frame of 32 and the
search's 496) or the key's (a frame of 80; the key uses no stack below its
own).

The prime search's candidates read RSA's table of trial division
(`TrialTable32`), so the controller's contract is under `abi.withConsts`, as
the search's is (`Proof/RsaKeyGen/RISCV64/Search/Contract.lean`). The stack
pointer is 16-byte aligned, and `used`, the working space and the state,
arrays of 64-bit words, are 8-byte aligned (`abi`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Generate

open VG VG.RISCV64
open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Spec.RsaKeyGen

/-- The stack the controller uses below the stack pointer. -/
abbrev stackUse : Nat := 656

/-- The table of trial division. -/
abbrev tables : List (String × List (BitVec 64)) := Impl.RsaKeyGen.TrialTable32.consts

def inKey (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .a2, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat * 8⟩
def inState (s : State) : Region := ⟨s.gpr .a7, 56⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inKey s, inUsed s, inScr s, inState s]
def inReads (s : State) : List Region := [inRand s]

/-- The primes' octets, the exponent, the tape and the progress on entry. -/
abbrev genLen (s : State) : Nat := (s.mem.readW (s.gpr .a7 + 8) 64).toNat
abbrev genE (s : State) : List Byte := bytesAt s.mem (s.gpr .a7 + 48) 8
abbrev genRand (s : State) : List Byte := bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat
abbrev genProgress (s : State) : KeyProgress := keyProgressAt s.mem (s.gpr .a0) (s.gpr .a7) (genLen s)

/-- The precondition without the table. -/
def basePre (s : State) : Prop :=
  s.sp.toNat % 16 = 0 ∧ stackUse ≤ s.sp.toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp stackUse).Disjoint r) ∧
    primeLenValid (genLen s) ∧ (s.gpr .a1).toNat = 9 * genLen s ∧
    Spec.Rsa.scratchWords (2 * genLen s) ≤ (s.gpr .a6).toNat ∧
    (s.mem.readW (s.gpr .a7) 64).toNat ≤ primeLimit (8 * genLen s) (Spec.Rsa.os2ip (genE s)) ∧
    s.mem.readW (s.gpr .a7 + 16) 64 = BitVec.ofNat 64 (primeEntropy (genLen s)) ∧
    (s.mem.readW (s.gpr .a7 + 32) 64).toNat ≤ 1 ∧
    (s.gpr .a4).toNat ≤ primeEntropy (genLen s) ∧
    (s.gpr .a2).toNat % 8 = 0 ∧ (s.gpr .a5).toNat % 8 = 0 ∧ (s.gpr .a7).toNat % 8 = 0

def genPre (s : State) : Prop := basePre (stripConsts tables s) ∧ ConstsOk tables stackUse s

def genResult (s : State) : KeySearchResult := keySearch (genLen s) (genE s) (genProgress s) (genRand s)

def genPost (s t : State) : Prop :=
  ((t.gpr .a0).setWidth 32).toNat = (genResult s).keyStatus ∧
    bytesAt t.mem (s.gpr .a0) (9 * genLen s) = keySearchBytes (genLen s) (genResult s) ∧
    wordsAt t.mem (s.gpr .a2) 1 = [BitVec.ofNat 64 (genResult s).used] ∧
    ∃ requested, wordsAt t.mem (s.gpr .a7) 6 = [BitVec.ofNat 64 (genResult s).progress.remaining,
      BitVec.ofNat 64 (genLen s), BitVec.ofNat 64 (primeEntropy (genLen s)), BitVec.ofNat 64 requested,
      BitVec.ofNat 64 (if (genResult s).progress.phase = .p then 0 else 1),
      BitVec.ofNat 64 (genResult s).progress.left] ∧
      bytesAt t.mem (s.gpr .a7 + 48) 8 = genE s ∧
      (genResult s).Requests (primeEntropy (genLen s)) requested

/-- What timing may depend on: the arguments, the state's words, the
result's status, consumption, octets left and trace, and the table's
address. -/
def genPub (s t : State) : Prop :=
  s.sp = t.sp ∧
    s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧ s.gpr .a2 = t.gpr .a2 ∧ s.gpr .a3 = t.gpr .a3 ∧
    s.gpr .a4 = t.gpr .a4 ∧ s.gpr .a5 = t.gpr .a5 ∧ s.gpr .a6 = t.gpr .a6 ∧ s.gpr .a7 = t.gpr .a7 ∧
    wordsAt s.mem (s.gpr .a7) 7 = wordsAt t.mem (t.gpr .a7) 7 ∧
    (genResult s).keyStatus = (genResult t).keyStatus ∧ (genResult s).used = (genResult t).used ∧
    (genResult s).available = (genResult t).available ∧ (genResult s).trace = (genResult t).trace ∧
    s.syms Impl.RsaKeyGen.TrialTable32.symbol = t.syms Impl.RsaKeyGen.TrialTable32.symbol

def genContract : Contract isa where
  pre := genPre
  post := genPost
  pub := genPub

end VG.Proof.RsaKeyGen.RISCV64.Generate
