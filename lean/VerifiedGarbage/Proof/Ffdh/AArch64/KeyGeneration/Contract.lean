module

public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Spec.Ffdh.KeyGeneration

/-! # The key-generation controller's contract in terms of the machine (AArch64)

`vg_ffdh_generate_key_search(x = x0, x_len = x1, y = x2, y_len = x3,
used = x4, domain = x5, domain_len = x6, p_len = x7, rand, rand_len,
scratch, scratch_len, state)`: eight arguments in registers and five on the
stack. The controller uses 48 bytes of stack: the frame saving `x30` and
its attempt's frame of 32 bytes; the attempt it calls uses none
(`Attempt.depth`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.KeyGeneration

open VG VG.AArch64 VG.Proof.Bignum VG.Spec.Ffdh
open VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive
open VG.Spec.Rsa (bytesAt wordsAt i2osp powMod)

/-- The stack the controller uses below the stack pointer. -/
abbrev stackUse : Nat := 48

/-- An implementation of `vg_ffdh_generate_key`, the attempt: the backend's
code, which uses no stack of its own. -/
structure Attempt where
  W : Window
  M : Mont
  S : Selector
  depth : (Impl.Ffdh.AArch64.Domain.GenerateKey.code W.code S.code M.mm).aarch64Depth = 0

/-- The attempt's code. -/
abbrev Attempt.code (a : Attempt) : Prog isa :=
  Impl.Ffdh.AArch64.Domain.GenerateKey.code a.W.code a.S.code a.M.mm

/-- The attempt, as the controller calls it. -/
abbrev Attempt.call (a : Attempt) : Prog isa := .call Spec.Ffdh.generateKeyApi.name a.code

def inX (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
def inY (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .x4, 8⟩
def inDom (s : State) : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
def inRand (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
def inScr (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
def inCtl (s : State) : Region := ⟨stackArg s 4, 128⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 40⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inX s, inY s, inUsed s, inScr s, inCtl s]
def inReads (s : State) : List Region := [inDom s, inRand s, inArgs s]

/-- The width, the domain and the random octets on entry. -/
abbrev keyLen (s : State) : Nat := (s.gpr .x7).toNat
abbrev keyDom (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
abbrev keyRand (s : State) : List Byte := bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
abbrev keyA (s : State) : Parameters := domainOf (keyLen s) (keyDom s)
abbrev keyRetries (s : State) : KeyRetries :=
  ⟨(s.mem.readW (stackArg s 4) 64).toNat, (s.mem.readW (stackArg s 4 + 8) 64).toNat⟩

def keyPre (s : State) : Prop :=
  s.sp.toNat + 40 ≤ 2 ^ 64 ∧ stackUse ≤ s.sp.toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp stackUse).Disjoint r) ∧
    pLenValid (keyLen s) ∧ domainLenValid (keyLen s) (s.gpr .x6).toNat ∧
    (s.gpr .x1).toNat = keyLen s ∧ (s.gpr .x3).toNat = keyLen s ∧
    Spec.Rsa.scratchWords (keyLen s) ≤ (stackArg s 3).toNat ∧
    domainValid (keyLen s) (keyDom s) ∧
    (s.mem.readW (stackArg s 4) 64).toNat ≤ 128 ∧
    (s.mem.readW (stackArg s 4 + 8) 64).toNat ≤ 128 ∧
    s.mem.readW (stackArg s 4 + 16) 64 = BitVec.ofNat 64 (keyLen s)

def keyResult (s : State) : KeySearchResult :=
  keySearch (keyA s) (keyLen s) (keyRetries s) (keyRand s)

def keyPost (s t : State) : Prop :=
  ((t.gpr .x0).setWidth 32).toNat = (keyResult s).status ∧
    (match (keyResult s).outcome with
      | .accepted sx sy => bytesAt t.mem (s.gpr .x0) (keyLen s) = i2osp sx (keyLen s) ∧
          bytesAt t.mem (s.gpr .x2) (keyLen s) = i2osp sy (keyLen s)
      | _ => bytesAt t.mem (s.gpr .x0) (keyLen s) = List.replicate (keyLen s) 0 ∧
          bytesAt t.mem (s.gpr .x2) (keyLen s) = List.replicate (keyLen s) 0) ∧
    wordsAt t.mem (stackArg s 4) 4 = [BitVec.ofNat 64 (keyResult s).retries.keys,
      BitVec.ofNat 64 (keyResult s).retries.scalars, BitVec.ofNat 64 (keyLen s),
      BitVec.ofNat 64 (if (keyResult s).status = 0 then keyLen s else 0)] ∧
    wordsAt t.mem (s.gpr .x4) 1 = [BitVec.ofNat 64 (keyResult s).used]

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

end VG.Proof.Ffdh.AArch64.KeyGeneration
