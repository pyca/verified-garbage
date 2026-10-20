module

public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! Public inputs and loop-state representation for the native ARMv7 key
search. The retry counters and width fit in native words; their packed-u64
high halves remain zero. Each attempt may use 128 bytes below its 32-byte
argument frame, within the search's 24-byte AAPCS frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Spec.Ffdh VG.Proof.Mont

abbrev stackUse : Nat := 184

def inX (s : State) : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
def inY (s : State) : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
def inUsed (s : State) : Region := ⟨State.addr (stackArg s 0), 8⟩
def inDomain (s : State) : Region := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩
def inRand (s : State) : Region := ⟨State.addr (stackArg s 4), (stackArg s 5).toNat⟩
def inScratch (s : State) : Region := ⟨State.addr (stackArg s 6), (stackArg s 7).toNat * 8⟩
def inControl (s : State) : Region := ⟨State.addr (stackArg s 8), 128⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 36⟩

def writes (s : State) : List Region := [inX s, inY s, inUsed s, inScratch s, inControl s]
def reads (s : State) : List Region := [inDomain s, inRand s, inArgs s]

structure KeyPublic where
  xp : BitVec 32
  yp : BitVec 32
  up : BitVec 32
  dp : BitVec 32
  rp : BitVec 32
  scratch : BitVec 32
  control : BitVec 32
  sp : BitVec 32
  len : Nat
  dlen : Nat
  randLen : Nat
  capacity : Nat
  keys : Nat
  scalars : Nat
  dom : List Byte

def keyOfState (s : State) : KeyPublic where
  xp := s.gpr .r0
  yp := s.gpr .r2
  up := stackArg s 0
  dp := stackArg s 1
  rp := stackArg s 4
  scratch := stackArg s 6
  control := stackArg s 8
  sp := s.sp
  len := (stackArg s 3).toNat
  dlen := (stackArg s 2).toNat
  randLen := (stackArg s 5).toNat
  capacity := (stackArg s 7).toNat
  keys := (s.mem.readW (State.addr (stackArg s 8)) 64).toNat
  scalars := (s.mem.readW (off (State.addr (stackArg s 8)) 8) 64).toNat
  dom := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat

def KeyInput (p : KeyPublic) (s : State) : Prop := (keySearchContract abi stackUse).pre s ∧ keyOfState s = p

abbrev KeyPublic.a (p : KeyPublic) : Parameters := domainOf p.len p.dom

def KeyPublic.headers (p : KeyPublic) (used keys scalars : Nat) : List (Nat × BitVec 32) :=
  [(0, BitVec.ofNat 32 keys), (1, BitVec.ofNat 32 scalars), (2, BitVec.ofNat 32 p.len),
    (5, p.xp), (6, p.yp), (7, p.dp), (8, BitVec.ofNat 32 p.dlen),
    (9, p.rp + BitVec.ofNat 32 used), (10, BitVec.ofNat 32 (p.randLen - used)),
    (11, BitVec.ofNat 32 used), (12, p.scratch), (13, BitVec.ofNat 32 p.capacity), (15, p.up)]

def Slots (m : Mem) (base : BitVec 32) (values : List (Nat × BitVec 32)) : Prop :=
  ∀ e ∈ values, lowWord m base e.1 = e.2

def savedSlots : List (Reg × Nat) := [(.r4, 0), (.r9, 4), (.r10, 8), (.r11, 12), (.r12, 16), (.lr, 20)]

def KeyOutput (p : KeyPublic) (result : KeySearchResult) (m : Mem) : Prop :=
  match result.outcome with
  | .accepted x y => Spec.Rsa.bytesAt m (State.addr p.xp) p.len = Spec.Rsa.i2osp x p.len ∧
      Spec.Rsa.bytesAt m (State.addr p.yp) p.len = Spec.Rsa.i2osp y p.len
  | _ => Spec.Rsa.bytesAt m (State.addr p.xp) p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt m (State.addr p.yp) p.len = List.replicate p.len 0

structure KeyLive (p : KeyPublic) (original : State) (used keys scalars : Nat) (s : State) : Prop where
  input : KeyInput p original
  used_le : used ≤ p.randLen
  keys_le : keys ≤ 128
  scalars_le : scalars ≤ 128
  rd : s.rd = original.rd
  wr : s.wr = ⟨State.addr (p.sp - BitVec.ofNat 32 24), 24⟩ :: original.wr
  sp : s.sp = p.sp - BitVec.ofNat 32 24
  pointer : s.gpr .r4 = p.control
  kept : ∀ r ∈ [.r5, .r6, .r7, .r8], s.gpr r = original.gpr r
  saved : Spill.Saved s.mem (State.addr (p.sp - BitVec.ofNat 32 24)) original.gpr savedSlots
  random : Spec.Rsa.bytesAt s.mem (State.addr p.rp) p.randLen = Spec.Rsa.bytesAt original.mem (State.addr p.rp) p.randLen
  domain : Spec.Rsa.bytesAt s.mem (State.addr p.dp) p.dlen = p.dom
  headers : Slots s.mem p.control (p.headers used keys scalars)
  high : ∀ j < 3, s.mem.readW (off (State.addr p.control) (8 * j + 4)) 32 = 0

structure KeyDone (p : KeyPublic) (original : State) (result : KeySearchResult) (s : State) : Prop where
  input : KeyInput p original
  rd : s.rd = original.rd
  wr : s.wr = ⟨State.addr (p.sp - BitVec.ofNat 32 24), 24⟩ :: original.wr
  sp : s.sp = p.sp - BitVec.ofNat 32 24
  pointer : s.gpr .r4 = p.control
  kept : ∀ r ∈ [.r5, .r6, .r7, .r8], s.gpr r = original.gpr r
  saved : Spill.Saved s.mem (State.addr (p.sp - BitVec.ofNat 32 24)) original.gpr savedSlots
  usedPtr : lowWord s.mem p.control 15 = p.up
  used : lowWord s.mem p.control 11 = BitVec.ofNat 32 result.used
  status : lowWord s.mem p.control 14 = BitVec.ofNat 32 result.status
  policy : Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 =
    [BitVec.ofNat 64 result.retries.keys, BitVec.ofNat 64 result.retries.scalars,
      BitVec.ofNat 64 p.len, BitVec.ofNat 64 (if result.status = 0 then p.len else 0)]
  output : KeyOutput p result s.mem

end VG.Proof.Ffdh.Arm.KeySearch
