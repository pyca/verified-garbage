module

public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Fn
public import VerifiedGarbage.Spec.Ffdh.KeyGeneration

/-! # The key-generation controller's contract in terms of the machine (PPC64LE)

`vg_ffdh_generate_key_search(x = r3, x_len = r4, y = r5, y_len = r6,
used = r7, domain = r8, domain_len = r9, p_len = r10, rand, rand_len,
scratch, scratch_len, state)`: eight arguments in registers and five on the
stack. The controller uses 176 bytes of stack: the frame of 48 bytes saving
the link register and its attempt's frame of 128 bytes; the attempt uses
none below its own (`Attempt.stack`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Proof.Ffdh.PPC64LE.GenerateKey (gkContract)

/-- The stack the controller uses below the stack pointer. -/
abbrev stackUse : Nat := 176

/-- An implementation of `vg_ffdh_generate_key`, as the controller calls it:
its name, its code, the stack it uses, and its proofs. -/
structure Attempt where
  name : String
  code : Prog isa
  stack : sdepth code = 0
  correct : ∀ s, gkContract.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ gkContract.post s s'
  ct : ConstantTime isa gkContract.pre gkContract.pub code

/-- The attempt, as the controller calls it. -/
abbrev Attempt.call (a : Attempt) : Prog isa := .call a.name a.code

def inX (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
def inY (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .r7, 8⟩
def inDom (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
def inRand (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
def inScr (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
def inCtl (s : State) : Region := ⟨stackArg s 4, 128⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 40⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inX s, inY s, inUsed s, inScr s, inCtl s]
def inReads (s : State) : List Region := [inDom s, inRand s, inArgs s]

/-- The width, the domain and the random octets on entry. -/
abbrev keyLen (s : State) : Nat := (s.gpr .r10).toNat
abbrev keyDom (s : State) : List Byte := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
abbrev keyRand (s : State) : List Byte := bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
abbrev keyA (s : State) : Parameters := domainOf (keyLen s) (keyDom s)
abbrev keyRetries (s : State) : KeyRetries :=
  ⟨(s.mem.readW (stackArg s 4) 64).toNat, (s.mem.readW (stackArg s 4 + 8) 64).toNat⟩

def keyPre (s : State) : Prop :=
  s.sp.toNat + 32 + 8 * 13 ≤ 2 ^ 64 ∧ stackUse ≤ s.sp.toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp stackUse).Disjoint r) ∧
    pLenValid (keyLen s) ∧ domainLenValid (keyLen s) (s.gpr .r9).toNat ∧
    (s.gpr .r4).toNat = keyLen s ∧ (s.gpr .r6).toNat = keyLen s ∧
    Spec.Rsa.scratchWords (keyLen s) ≤ (stackArg s 3).toNat ∧
    domainValid (keyLen s) (keyDom s) ∧
    (s.mem.readW (stackArg s 4) 64).toNat ≤ 128 ∧
    (s.mem.readW (stackArg s 4 + 8) 64).toNat ≤ 128 ∧
    s.mem.readW (stackArg s 4 + 16) 64 = BitVec.ofNat 64 (keyLen s)

def keyResult (s : State) : KeySearchResult :=
  keySearch (keyA s) (keyLen s) (keyRetries s) (keyRand s)

def keyPost (s t : State) : Prop :=
  ((t.gpr .r3).setWidth 32).toNat = (keyResult s).status ∧
    (match (keyResult s).outcome with
      | .accepted sx sy => bytesAt t.mem (s.gpr .r3) (keyLen s) = i2osp sx (keyLen s) ∧
          bytesAt t.mem (s.gpr .r5) (keyLen s) = i2osp sy (keyLen s)
      | _ => bytesAt t.mem (s.gpr .r3) (keyLen s) = List.replicate (keyLen s) 0 ∧
          bytesAt t.mem (s.gpr .r5) (keyLen s) = List.replicate (keyLen s) 0) ∧
    wordsAt t.mem (stackArg s 4) 4 = [BitVec.ofNat 64 (keyResult s).retries.keys,
      BitVec.ofNat 64 (keyResult s).retries.scalars, BitVec.ofNat 64 (keyLen s),
      BitVec.ofNat 64 (if (keyResult s).status = 0 then keyLen s else 0)] ∧
    wordsAt t.mem (s.gpr .r7) 1 = [BitVec.ofNat 64 (keyResult s).used]

/-- What timing may depend on: the arguments but the random octets, the
domain, the controller's public words and the attempts' statuses. -/
def keyPub (s t : State) : Prop :=
  s.sp = t.sp ∧ (∀ r ∈ argRegs, s.gpr r = t.gpr r) ∧
    (∀ j < 5, stackArg s j = stackArg t j) ∧
    keyDom s = keyDom t ∧ wordsAt s.mem (stackArg s 4) 4 = wordsAt t.mem (stackArg t 4) 4 ∧
    (keyResult s).statuses = (keyResult t).statuses

def keyContract : Contract isa where
  pre := keyPre
  post := keyPost
  pub := keyPub

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
