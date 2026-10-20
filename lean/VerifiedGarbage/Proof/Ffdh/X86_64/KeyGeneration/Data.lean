module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Contract
public import VerifiedGarbage.Proof.Ffdh.KeyGeneration
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitValues
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory

/-! # The key-generation controller's public data and loop states

`KeyPublic` is everything two constant-time runs share: the arguments but
the random octets' values, the domain and the initial budgets. A loop
state (`KeyLive`) is at an offset into the tape with budgets left; the
search from there (`keyTail`) is what the controller returns.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Spec.Ffdh
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Ffdh.X86_64.Generation (writeController)
open VG.Proof.Ffdh.X86_64 (Slots)

structure KeyPublic where
  xp : Addr
  yp : Addr
  up : Addr
  dp : Addr
  rp : Addr
  B : Addr
  control : Addr
  sp : Addr
  len : Nat
  dlen : Nat
  randLen : Nat
  Z : Nat
  keys : Nat
  scalars : Nat
  dom : List Byte

def keyOfState (s : State) : KeyPublic where
  xp := s.gpr .rdi
  yp := s.gpr .rdx
  up := s.gpr .r8
  dp := s.gpr .r9
  rp := stackArg s 2
  B := stackArg s 4
  control := stackArg s 6
  sp := s.gpr .rsp
  len := keyLen s
  dlen := (stackArg s 0).toNat
  randLen := (stackArg s 3).toNat
  Z := (stackArg s 5).toNat * 8
  keys := (keyRetries s).keys
  scalars := (keyRetries s).scalars
  dom := keyDom s

/-- The domain's parameters. -/
abbrev KeyPublic.a (p : KeyPublic) : Parameters := domainOf p.len p.dom

def KeyInput (p : KeyPublic) (s : State) : Prop := keyPre s ∧ keyOfState s = p

/-- The search from octet `used` of `rand`, with `keys` and `scalars` left. -/
abbrev KeyPublic.tail (p : KeyPublic) (rand : List Byte) (used keys scalars : Nat) : KeySearchResult :=
  keyTail p.a p.len rand used keys scalars

/-- The controller's words while it searches. -/
def KeyPublic.headers (p : KeyPublic) (used keys scalars : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 keys), (1, BitVec.ofNat 64 scalars), (2, BitVec.ofNat 64 p.len),
    (5, p.xp), (6, p.yp), (7, p.dp), (8, BitVec.ofNat 64 p.dlen),
    (9, p.rp + BitVec.ofNat 64 used), (10, BitVec.ofNat 64 (p.randLen - used)),
    (11, BitVec.ofNat 64 used), (12, p.B), (13, BitVec.ofNat 64 (p.Z / 8)), (15, p.up)]

theorem KeyPublic.headers_bound (p : KeyPublic) (used keys scalars : Nat) :
    ∀ e ∈ p.headers used keys scalars, e.1 < 16 := by
  simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    dsimp only <;> decide

/-- A state of the loop: `used` octets consumed, `keys` and `scalars` left.
The entry state is functional-proof data only: its callee-saved registers
may hold secrets, and its tape is secret. -/
structure KeyLive (p : KeyPublic) (original : State) (used keys scalars : Nat) (s : State) : Prop where
  input : KeyInput p original
  used_le : used ≤ p.randLen
  keys_le : keys ≤ 128
  scalars_le : scalars ≤ 128
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  rsp : s.gpr .rsp = p.sp
  r12 : s.gpr .r12 = p.control
  saved : ∀ r ∈ calleeSaved, r ≠ .r12 → s.gpr r = original.gpr r
  savedR12 : word s.mem p.control 32 = original.gpr .r12
  random : Spec.Rsa.bytesAt s.mem p.rp p.randLen = keyRand original
  domain : Spec.Rsa.bytesAt s.mem p.dp p.dlen = p.dom
  headers : Slots s.mem p.control (p.headers used keys scalars)

/-- The outputs of a finished search. -/
def KeyOutput (p : KeyPublic) (result : KeySearchResult) (m : Mem) : Prop :=
  match result.outcome with
  | .accepted sx sy => Spec.Rsa.bytesAt m p.xp p.len = Spec.Rsa.i2osp sx p.len ∧
      Spec.Rsa.bytesAt m p.yp p.len = Spec.Rsa.i2osp sy p.len
  | _ => Spec.Rsa.bytesAt m p.xp p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt m p.yp p.len = List.replicate p.len 0

/-- The controller's four public words for a finished search. -/
def KeyPublic.policy (p : KeyPublic) (result : KeySearchResult) : List (BitVec 64) :=
  [BitVec.ofNat 64 result.retries.keys, BitVec.ofNat 64 result.retries.scalars,
    BitVec.ofNat 64 p.len, BitVec.ofNat 64 (if result.status = 0 then p.len else 0)]

/-- A finished search, before `finish` stores `used` and restores r12. -/
structure KeyDone (p : KeyPublic) (original : State) (result : KeySearchResult) (s : State) : Prop where
  input : KeyInput p original
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  rsp : s.gpr .rsp = p.sp
  r12 : s.gpr .r12 = p.control
  saved : ∀ r ∈ calleeSaved, r ≠ .r12 → s.gpr r = original.gpr r
  savedR12 : word s.mem p.control 32 = original.gpr .r12
  usedPtr : word s.mem p.control 120 = p.up
  used : word s.mem p.control 88 = BitVec.ofNat 64 result.used
  status : word s.mem p.control 112 = BitVec.ofNat 64 result.status
  policy : Spec.Rsa.wordsAt s.mem p.control 4 = p.policy result
  output : KeyOutput p result s.mem

end VG.Proof.Ffdh.X86_64.KeyGeneration
