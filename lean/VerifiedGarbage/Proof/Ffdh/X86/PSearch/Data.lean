module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.ABI
public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Tail
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Words

/-! # The parameter search's public data and loop states (x86)

`PPub` is everything two constant-time runs share: the arguments, the tape,
the attempts at entry and the table's address, all public in this
contract. A loop state
(`Live`) is at an offset into the tape with attempts left; the search from
there (`PPub.tail`) is what the controller returns. Every state of the run
differs from the entry's memory only in the writable arguments and the stack
below the entry's (`Frame (frameR o)`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.Spec.Ffdh
open VG.Proof.Ffdh.X86.KeySearch (Ctl)
open VG.Proof.Dsa.X86 (argumentPointer)

structure PPub where
  sp : BitVec 32
  S : BitVec 32
  op : BitVec 32
  up : BitVec 32
  rp : BitVec 32
  B : BitVec 32
  len : Nat
  bits : Nat
  gen : Nat
  randLen : Nat
  slen : Nat
  attempts : Nat
  rand : List Byte
  T : BitVec 32

def ofState (s : State) : PPub where
  sp := s.gpr .esp
  S := arg s 9
  op := arg s 0
  up := arg s 2
  rp := arg s 5
  B := arg s 7
  len := (arg s 1).toNat
  bits := (arg s 3).toNat
  gen := (arg s 4).toNat
  randLen := (arg s 6).toNat
  slen := (arg s 8).toNat
  attempts := (s.mem.readW (argumentPointer s 9) 64).toNat
  rand := Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat
  T := s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol

def Input (p : PPub) (o : State) : Prop := PSearchABI o ∧ ofState o = p

/-- The search from octet `used` of the tape, with `n` attempts left. -/
abbrev PPub.tail (p : PPub) (used n : Nat) : ParameterSearchResult := ptail p.bits p.gen p.rand used n

/-- The entropy cap. -/
abbrev PPub.cap (p : PPub) : Nat := parameterEntropy p.bits

/-- Where the run may write: the writable arguments and the stack below the entry's. -/
abbrev frameR (o : State) : List Region := o.wr ++ [lowR o]

/-- The offsets of the words the loop keeps. -/
def liveDs : List Nat := [0, 4, 8, 12, 16, 20, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 72]

/-- The words the loop keeps: the attempts (64 bits), the width and the cap and the request's high
halves, the caller's `esi`, the arguments passed on, the tape's pointer and length and the octets
consumed. -/
def liveF (p : PPub) (esi : BitVec 32) (used n : Nat) (d : Nat) : BitVec 32 :=
  if d = 0 then BitVec.ofNat 32 n else
  if d = 4 then BitVec.ofNat 32 (n / 2 ^ 32) else
  if d = 8 then BitVec.ofNat 32 p.len else
  if d = 16 then BitVec.ofNat 32 p.cap else
  if d = 32 then esi else
  if d = 36 then p.op else
  if d = 40 then p.up else
  if d = 44 then BitVec.ofNat 32 p.bits else
  if d = 48 then BitVec.ofNat 32 p.gen else
  if d = 52 then p.rp + BitVec.ofNat 32 used else
  if d = 56 then BitVec.ofNat 32 (p.randLen - used) else
  if d = 60 then p.B else
  if d = 64 then BitVec.ofNat 32 p.slen else
  if d = 72 then BitVec.ofNat 32 used else 0

/-- A state of the loop: `used` octets consumed, `n` attempts left. -/
structure Live (p : PPub) (o : State) (used n : Nat) (s : State) : Prop where
  input : Input p o
  used_le : used ≤ p.randLen
  n_le : n ≤ p.attempts
  rd : s.rd = o.rd
  wr : s.wr = o.wr
  syms : s.syms = o.syms
  esp : s.gpr .esp = p.sp
  esi : s.gpr .esi = p.S
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem p.S liveDs (liveF p (o.gpr .esi) used n)

/-- The outputs of a finished search. -/
def Output (p : PPub) (result : ParameterSearchResult) (m : Mem) : Prop :=
  match result with
  | .accepted q _ => Spec.Rsa.bytesAt m (p.op.setWidth 64) p.len = Spec.Rsa.i2osp q p.len
  | _ => Spec.Rsa.bytesAt m (p.op.setWidth 64) p.len = List.replicate p.len 0

/-- The offsets of the words a finished search leaves. -/
def doneDs : List Nat := [0, 4, 8, 12, 16, 20, 24, 28, 32, 40, 68, 72]

/-- The words a finished search leaves: the four public words (64 bits), the caller's `esi`, `used`'s
pointer, the status and the octets consumed. -/
def doneF (p : PPub) (esi : BitVec 32) (result : ParameterSearchResult) (d : Nat) : BitVec 32 :=
  if d = 0 then BitVec.ofNat 32 result.remaining else
  if d = 4 then BitVec.ofNat 32 (result.remaining / 2 ^ 32) else
  if d = 8 then BitVec.ofNat 32 p.len else
  if d = 16 then BitVec.ofNat 32 p.cap else
  if d = 24 then BitVec.ofNat 32 result.requested else
  if d = 32 then esi else
  if d = 40 then p.up else
  if d = 68 then BitVec.ofNat 32 result.status else
  if d = 72 then BitVec.ofNat 32 result.used else 0

/-- A finished search, before `finish` stores `used` and restores `esi`. -/
structure Done (p : PPub) (o : State) (result : ParameterSearchResult) (s : State) : Prop where
  input : Input p o
  rd : s.rd = o.rd
  wr : s.wr = o.wr
  syms : s.syms = o.syms
  esp : s.gpr .esp = p.sp
  esi : s.gpr .esi = p.S
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem p.S doneDs (doneF p (o.gpr .esi) result)
  output : Output p result s.mem
  small : result.remaining ≤ p.attempts ∧ result.requested ≤ p.cap ∧ result.used ≤ p.randLen

end VG.Proof.Ffdh.X86.PSearch
