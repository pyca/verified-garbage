module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.ABI
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Words
public import VerifiedGarbage.Proof.Ffdh.KeyGeneration

/-! # The key search's public data and loop states (x86)

`KPub` is everything two constant-time runs share: the arguments but the
random octets' values, the domain and the initial budgets. A loop state
(`Live`) is at an offset into the tape with budgets left; the search from
there (`KPub.tail`) is what the controller returns. Every state of the run
differs from the entry's memory only in the writable arguments and the stack
below the entry's (`Frame (frameR o)`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.Spec.Ffdh
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Dsa.X86 (argumentPointer)

structure KPub where
  sp : BitVec 32
  S : BitVec 32
  xp : BitVec 32
  yp : BitVec 32
  up : BitVec 32
  dp : BitVec 32
  rp : BitVec 32
  B : BitVec 32
  len : Nat
  dlen : Nat
  randLen : Nat
  slen : Nat
  keys : Nat
  scalars : Nat
  dom : List Byte

def ofState (s : State) : KPub where
  sp := s.gpr .esp
  S := arg s 12
  xp := arg s 0
  yp := arg s 2
  up := arg s 4
  dp := arg s 5
  rp := arg s 8
  B := arg s 10
  len := (arg s 7).toNat
  dlen := (arg s 6).toNat
  randLen := (arg s 9).toNat
  slen := (arg s 11).toNat
  keys := (s.mem.readW (argumentPointer s 12) 64).toNat
  scalars := (s.mem.readW (argumentPointer s 12 + 8) 64).toNat
  dom := Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat

/-- The domain's parameters. -/
abbrev KPub.a (p : KPub) : Parameters := domainOf p.len p.dom

def Input (p : KPub) (o : State) : Prop := KeySearchABI o ∧ ofState o = p

/-- The random octets at entry. -/
abbrev randOf (o : State) : List Byte := Spec.Rsa.bytesAt o.mem (argumentPointer o 8) (arg o 9).toNat

/-- The search from octet `used` of `rand`, with `keys` and `scalars` left. -/
abbrev KPub.tail (p : KPub) (rand : List Byte) (used keys scalars : Nat) : KeySearchResult :=
  keyTail p.a p.len rand used keys scalars

/-- Where the run may write: the writable arguments and the stack below the entry's. -/
abbrev frameR (o : State) : List Region := o.wr ++ [lowR o]

/-- The offsets of the words the loop keeps. -/
def liveDs : List Nat := [0, 4, 8, 12, 16, 20, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 76]

/-- The words the loop keeps: the budgets, the width and the request's high half, the caller's
`esi`, the arguments passed on, the tape's pointer and length and the octets consumed. -/
def liveF (p : KPub) (esi : BitVec 32) (used keys scalars : Nat) (d : Nat) : BitVec 32 :=
  if d = 0 then BitVec.ofNat 32 keys else
  if d = 8 then BitVec.ofNat 32 scalars else
  if d = 16 then BitVec.ofNat 32 p.len else
  if d = 32 then esi else
  if d = 36 then p.xp else
  if d = 40 then p.yp else
  if d = 44 then p.dp else
  if d = 48 then BitVec.ofNat 32 p.dlen else
  if d = 52 then p.rp + BitVec.ofNat 32 used else
  if d = 56 then BitVec.ofNat 32 (p.randLen - used) else
  if d = 60 then BitVec.ofNat 32 used else
  if d = 64 then p.B else
  if d = 68 then BitVec.ofNat 32 p.slen else
  if d = 76 then p.up else 0

/-- A state of the loop: `used` octets consumed, `keys` and `scalars` left. -/
structure Live (p : KPub) (o : State) (used keys scalars : Nat) (s : State) : Prop where
  input : Input p o
  used_le : used ≤ p.randLen
  keys_le : keys ≤ 128
  scalars_le : scalars ≤ 128
  rd : s.rd = o.rd
  wr : s.wr = o.wr
  esp : s.gpr .esp = p.sp
  esi : s.gpr .esi = p.S
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem p.S liveDs (liveF p (o.gpr .esi) used keys scalars)

/-- The outputs of a finished search. -/
def Output (p : KPub) (result : KeySearchResult) (m : Mem) : Prop :=
  match result.outcome with
  | .accepted sx sy => Spec.Rsa.bytesAt m (p.xp.setWidth 64) p.len = Spec.Rsa.i2osp sx p.len ∧
      Spec.Rsa.bytesAt m (p.yp.setWidth 64) p.len = Spec.Rsa.i2osp sy p.len
  | _ => Spec.Rsa.bytesAt m (p.xp.setWidth 64) p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt m (p.yp.setWidth 64) p.len = List.replicate p.len 0

/-- The offsets of the words a finished search leaves. -/
def doneDs : List Nat := [0, 4, 8, 12, 16, 20, 24, 28, 32, 60, 72, 76]

/-- The words a finished search leaves: the four public words, the caller's `esi`, the octets
consumed, the status and `used`. -/
def doneF (p : KPub) (esi : BitVec 32) (result : KeySearchResult) (d : Nat) : BitVec 32 :=
  if d = 0 then BitVec.ofNat 32 result.retries.keys else
  if d = 8 then BitVec.ofNat 32 result.retries.scalars else
  if d = 16 then BitVec.ofNat 32 p.len else
  if d = 24 then BitVec.ofNat 32 (if result.status = 0 then p.len else 0) else
  if d = 32 then esi else
  if d = 60 then BitVec.ofNat 32 result.used else
  if d = 72 then BitVec.ofNat 32 result.status else
  if d = 76 then p.up else 0

/-- A finished search, before `finish` stores `used` and restores `esi`. -/
structure Done (p : KPub) (o : State) (result : KeySearchResult) (s : State) : Prop where
  input : Input p o
  rd : s.rd = o.rd
  wr : s.wr = o.wr
  esp : s.gpr .esp = p.sp
  esi : s.gpr .esi = p.S
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem p.S doneDs (doneF p (o.gpr .esi) result)
  output : Output p result s.mem

end VG.Proof.Ffdh.X86.KeySearch
