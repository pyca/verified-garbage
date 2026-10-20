module
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Spec.Ffdh.KeyGeneration
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.TCB.X86_64.Target


/-! # The key-generation controller's contract in terms of the machine

`vg_ffdh_generate_key_search(x, x_len, y, y_len, used, domain | domain_len,
p_len, rand, rand_len, scratch, scratch_len, state)`: six arguments in
registers and seven on the stack. The controller uses 56 octets of stack:
its attempt's frame of 40, the call's return address and the callee's own 8.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp powMod)

/-- The stack the controller uses below its return address. -/
abbrev stackUse : Nat := 56

def inX (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def inY (s : State) : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .r8, 8⟩
def inDom (s : State) : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
def inRand (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
def inScr (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
def inCtl (s : State) : Region := ⟨stackArg s 6, 128⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 56⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inX s, inY s, inUsed s, inScr s, inCtl s]
def inReads (s : State) : List Region := [inDom s, inRand s, inArgs s]

/-- The width, the domain and the random octets on entry. -/
abbrev keyLen (s : State) : Nat := (stackArg s 1).toNat
abbrev keyDom (s : State) : List Byte := bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
abbrev keyRand (s : State) : List Byte := bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat
abbrev keyA (s : State) : Parameters := domainOf (keyLen s) (keyDom s)
abbrev keyRetries (s : State) : KeyRetries :=
  ⟨(s.mem.readW (stackArg s 6) 64).toNat, (s.mem.readW (stackArg s 6 + 8) 64).toNat⟩

def keyPre (s : State) : Prop :=
  (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64 ∧ stackUse ≤ (s.gpr .rsp).toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r ∧
      (below (s.gpr .rsp) stackUse).Disjoint r) ∧
    pLenValid (keyLen s) ∧ domainLenValid (keyLen s) (stackArg s 0).toNat ∧
    (s.gpr .rsi).toNat = keyLen s ∧ (s.gpr .rcx).toNat = keyLen s ∧
    Spec.Rsa.scratchWords (keyLen s) ≤ (stackArg s 5).toNat ∧
    domainValid (keyLen s) (keyDom s) ∧
    (s.mem.readW (stackArg s 6) 64).toNat ≤ 128 ∧
    (s.mem.readW (stackArg s 6 + 8) 64).toNat ≤ 128 ∧
    s.mem.readW (stackArg s 6 + 16) 64 = BitVec.ofNat 64 (keyLen s)

def keyResult (s : State) : KeySearchResult :=
  keySearch (keyA s) (keyLen s) (keyRetries s) (keyRand s)

def keyPost (s t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = (keyResult s).status ∧
    (match (keyResult s).outcome with
      | .accepted sx sy => bytesAt t.mem (s.gpr .rdi) (keyLen s) = i2osp sx (keyLen s) ∧
          bytesAt t.mem (s.gpr .rdx) (keyLen s) = i2osp sy (keyLen s)
      | _ => bytesAt t.mem (s.gpr .rdi) (keyLen s) = List.replicate (keyLen s) 0 ∧
          bytesAt t.mem (s.gpr .rdx) (keyLen s) = List.replicate (keyLen s) 0) ∧
    wordsAt t.mem (stackArg s 6) 4 = [BitVec.ofNat 64 (keyResult s).retries.keys,
      BitVec.ofNat 64 (keyResult s).retries.scalars, BitVec.ofNat 64 (keyLen s),
      BitVec.ofNat 64 (if (keyResult s).status = 0 then keyLen s else 0)] ∧
    wordsAt t.mem (s.gpr .r8) 1 = [BitVec.ofNat 64 (keyResult s).used]

/-- What timing may depend on: the arguments but the random octets, the
domain, the controller's public words and the attempts' statuses. -/
def keyPub (s t : State) : Prop :=
  s.gpr .rsp = t.gpr .rsp ∧
    s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧
    s.gpr .rcx = t.gpr .rcx ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9 ∧
    (∀ j < 7, stackArg s j = stackArg t j) ∧
    keyDom s = keyDom t ∧ wordsAt s.mem (stackArg s 6) 4 = wordsAt t.mem (stackArg t 6) 4 ∧
    (keyResult s).statuses = (keyResult t).statuses

def keyContract : Contract isa where
  pre := keyPre
  post := keyPost
  pub := keyPub

end VG.Proof.Ffdh.X86_64.KeyGeneration
