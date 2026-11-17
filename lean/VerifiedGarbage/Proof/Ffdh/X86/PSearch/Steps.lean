module

import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Zero
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.X86.KeySearch
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Words
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Ffdh.X86.ParamSearch
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Spec.Ffdh.SievedGeneration
import VerifiedGarbage.Proof.Ffdh.SievedBounds
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Ffdh.SievedContract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI

/-! ### `Ffdh.X86.PSearch.Data`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86.PSearch.ABI`, which this module and modules that import it used -/

section

/-! # The parameter search on i686: what its cdecl contract supplies

`vg_ffdh_generate_parameters(out, out_len, used, bits, generator, rand, rand_len, scratch,
scratch_len, state)`: ten arguments on the stack, and RSA's table of primes as a constant. The
controller uses 212 bytes of stack: its attempt's frame of 36, the call's return address and the
candidate's own 172.
-/

@[expose] public section
namespace VG.Proof.Ffdh.X86.PSearch
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The bytes of stack the controller uses. -/
abbrev stack : Nat := 212

/-- The contract, with RSA's table of primes as the constants. -/
abbrev contract : Contract isa :=
  Spec.Ffdh.sievedParameterSearchContract (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) stack

/-- The arguments' regions: `out`, `used`, `rand`, `scratch` and `state`. -/
abbrev oR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat⟩
abbrev uR (s : State) : Region := ⟨argumentPointer s 2, 8⟩
abbrev rR (s : State) : Region := ⟨argumentPointer s 5, (arg s 6).toNat⟩
abbrev bR (s : State) : Region := ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
abbrev sR (s : State) : Region := ⟨argumentPointer s 9, 128⟩
/-- The arguments themselves. -/
abbrev aR (s : State) : Region := ⟨argAddr s 0, 40⟩
/-- The return address and the stack below it. -/
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev lowR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 212#64, 212⟩
/-- RSA's table. -/
abbrev tR (s : State) : Region := ⟨(s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64, 8192⟩

structure PSearchABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 40 ≤ 2 ^ 32
  rdTable : s.rd.drop (s.rd.length - 1) = Abi.constRegions (fun name => (s.syms name).setWidth 64)
    [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)]
  held : Abi.constsHeld s.mem (fun name => (s.syms name).setWidth 64)
    [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)]
  tableFar : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64)
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)],
    t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧ t.Disjoint (retR s) ∧ t.Disjoint (lowR s)
  tableAligned : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64)
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)], t.base.toNat % 64 = 0
  rdPrefix : s.rd.take (s.rd.length - 1) = [rR s]
  wr : s.wr = [oR s, uR s, bR s, sR s, aR s]
  ou : (oR s).Disjoint (uR s)
  or_ : (oR s).Disjoint (rR s)
  ob : (oR s).Disjoint (bR s)
  os : (oR s).Disjoint (sR s)
  oa : (oR s).Disjoint (aR s)
  ur : (uR s).Disjoint (rR s)
  ub : (uR s).Disjoint (bR s)
  us : (uR s).Disjoint (sR s)
  ua : (uR s).Disjoint (aR s)
  rb : (rR s).Disjoint (bR s)
  rs : (rR s).Disjoint (sR s)
  ra : (rR s).Disjoint (aR s)
  bs : (bR s).Disjoint (sR s)
  ba : (bR s).Disjoint (aR s)
  sa : (sR s).Disjoint (aR s)
  retO : (retR s).Disjoint (oR s)
  retU : (retR s).Disjoint (uR s)
  retRand : (retR s).Disjoint (rR s)
  retB : (retR s).Disjoint (bR s)
  retS : (retR s).Disjoint (sR s)
  retA : (retR s).Disjoint (aR s)
  lowO : (lowR s).Disjoint (oR s)
  lowU : (lowR s).Disjoint (uR s)
  lowRand : (lowR s).Disjoint (rR s)
  lowB : (lowR s).Disjoint (bR s)
  lowS : (lowR s).Disjoint (sR s)
  lowA : (lowR s).Disjoint (aR s)
  oBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  uBound : (arg s 2).toNat + 8 ≤ 2 ^ 32
  rBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  bBound : (arg s 7).toNat + (arg s 8).toNat * 8 ≤ 2 ^ 32
  sBound : (arg s 9).toNat + 128 ≤ 2 ^ 32
  bitsLow : 512 ≤ (arg s 3).toNat
  bitsHigh : (arg s 3).toNat ≤ 8192
  outLen : (arg s 1).toNat = ((arg s 3).toNat + 7) / 8
  gen : (arg s 4).toNat = 2 ∨ (arg s 4).toNat = 5
  scratchLength : Spec.Rsa.scratchWords (arg s 1).toNat ≤ (arg s 8).toNat
  attempts : (s.mem.readW (argumentPointer s 9) 64).toNat ≤ Spec.Ffdh.parameterAttempts (arg s 3).toNat
  width : s.mem.readW (argumentPointer s 9 + 8) 64 = BitVec.ofNat 64 (arg s 1).toNat
  cap : s.mem.readW (argumentPointer s 9 + 16) 64 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy (arg s 3).toNat)
  randLen : (arg s 6).toNat ≤ Spec.Ffdh.parameterEntropy (arg s 3).toNat

theorem pSearchABI_of {s : State} (h : contract.pre s) : PSearchABI s := by
  sig_pre [contract, Spec.Ffdh.sievedParameterSearchContract, Spec.Ffdh.parameterSearchSig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, VG.Proof.RsaKeyGen.X86.Candidate.packed_length,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Ffdh.X86.PSearch

end

end

/-! ### `Ffdh.X86.PSearch.Tail`, which only this module used -/

section

/-! # The sieved parameter search from an offset into the tape

`ptail` is the search from octet `used` of the tape with `n` attempts left,
counting the octets consumed from the tape's start, as the controller's loop
tracks it; each of its cases after a candidate (`ptail_short`,
`ptail_accept`, `ptail_reject`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.Spec.Ffdh
open VG.Spec.RsaKeyGen (Rand)

/-- The search from octet `used` of `rand`, with `n` attempts left. -/
def ptail (bits gen : Nat) (rand : Rand) (used n : Nat) : ParameterSearchResult :=
  (sievedParameterSearch bits gen n (rand.drop used)).consume used

/-- The candidate at octet `used`. -/
abbrev candAt (bits gen : Nat) (rand : Rand) (used : Nat) : Option (Option Nat × Rand) :=
  sievedParameterCandidate bits gen (rand.drop used)

/-- The octets the candidate at `used` consumes: none on a shortage. -/
def candUsed (bits gen : Nat) (rand : Rand) (used : Nat) : Nat :=
  match candAt bits gen rand used with
  | some (_, rest) => (rand.length - used) - rest.length
  | none => 0

theorem ptail_zero (bits gen : Nat) (rand : Rand) (used : Nat) : ptail bits gen rand used 0 = .exhausted used := by
  simp only [ptail, sievedParameterSearch, ParameterSearchResult.consume, Nat.add_zero]

theorem candUsed_le (bits gen : Nat) (rand : Rand) (used : Nat) : candUsed bits gen rand used ≤ rand.length - used := by
  unfold candUsed
  split <;> omega_using []

theorem cand_short {bits gen : Nat} {rand : Rand} {used : Nat} (h : rand.length - used < (bits + 7) / 8) :
    candAt bits gen rand used = none := by
  unfold candAt sievedParameterCandidate
  rw [ParameterCandidate.draw_of_short (by rw [List.length_drop]; exact h)]
  rfl

theorem ptail_short {bits gen : Nat} {rand : Rand} {used n : Nat} (hn : n ≠ 0) (h : candAt bits gen rand used = none) :
    ptail bits gen rand used n = if parameterEntropy bits ≤ rand.length - used then .exhausted used
      else .entropy n (rand.length - used) used := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hn]⟩
  unfold ptail
  rw [sievedParameterSearch, show sievedParameterCandidate bits gen (rand.drop used) = none from h]
  simp only [List.length_drop]
  split <;> simp only [ParameterSearchResult.consume, Nat.add_zero]

theorem ptail_accept {bits gen : Nat} {rand : Rand} {used n p : Nat} {rest : Rand} (hn : n ≠ 0)
    (h : candAt bits gen rand used = some (some p, rest)) :
    ptail bits gen rand used n = .accepted p (used + candUsed bits gen rand used) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hn]⟩
  unfold ptail candUsed
  rw [sievedParameterSearch, show sievedParameterCandidate bits gen (rand.drop used) = some (some p, rest) from h]
  simp only [List.length_drop, ParameterSearchResult.consume, h]

theorem ptail_reject {bits gen : Nat} {rand : Rand} {used n : Nat} {rest : Rand} (hn : n ≠ 0)
    (h : candAt bits gen rand used = some (none, rest)) :
    ptail bits gen rand used n = ptail bits gen rand (used + candUsed bits gen rand used) (n - 1) := by
  have step := SievedGeneration.search_reject (by omega_using [hn] : 0 < n) h
  simpa only [ptail, candUsed, h, List.length_drop] using step

end VG.Proof.Ffdh.X86.PSearch

end

end


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
  if d = 24 then BitVec.ofNat 32 (Proof.Ffdh.requested p.bits result) else
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
  small : result.remaining ≤ p.attempts ∧ (Proof.Ffdh.requested p.bits result) ≤ p.cap ∧ result.used ≤ p.randLen

end VG.Proof.Ffdh.X86.PSearch

end

end

/-! ### `Ffdh.X86.KeySearch.Steps`, which only this module used -/

section

/-! # Steps of the key search (x86)

The registers the controller uses for itself (`Scratch`), which no
callee-saved register is (`saved_ne`), and the words of its state through a
store (`Ctl.write'`) and on fewer offsets (`Ctl.sub`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch

/-- The registers the controller uses for itself. -/
abbrev Scratch (r : Reg) : Prop := r = .eax ∨ r = .ecx ∨ r = .edx

theorem saved_ne {r q : Reg} (hq : Scratch q) (hr : r ∈ calleeSaved) : r ≠ q := by
  rcases hq with rfl | rfl | rfl <;> simp [calleeSaved] at hr <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- A store and the word it keeps. -/
theorem Ctl.write' {m : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {ds : List Nat}
    {f : Nat → BitVec 32} (h : Ctl m S ds f) (hA : Aligned ds) {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0)
    (v : BitVec 32) : Ctl (m.writeW (addr S d) v) S (d :: ds) (upd f d v) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · rw [readW_write hS v hd hd (Or.inl rfl)]; simp [upd]
  · exact h.write hS hA hd hd4 v e he

theorem Aligned.cons {ds : List Nat} (h : Aligned ds) {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0) :
    Aligned (d :: ds) := fun e he => by
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨hd, hd4⟩
  · exact h e he

theorem Ctl.sub {m : Mem} {S : BitVec 32} {ds ds' : List Nat} {f : Nat → BitVec 32} (h : Ctl m S ds f)
    (hs : ∀ d ∈ ds', d ∈ ds) : Ctl m S ds' f := fun d hd => h d (hs d hd)

end VG.Proof.Ffdh.X86.KeySearch

end

end


/-! # Steps of the parameter search (x86)

`St o ds f`: a state of the run from the entry state `o`, `esi` at the
state, whose words at the offsets `ds` hold `f`, whose memory differs from
the entry's only where the run may write. A load of a word (`St.ld`), a
store (`St.stw`), a register-only instruction (`St.reg`, `St.fupd`) and the
zeros at the output (`St.zeroOut`) keep it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd stR contains_addr bytes_frame Scratch saved_ne ZInv zeroStep_ok)
open VG.Proof.Dsa.X86 (argumentPointer)

/-- Argument `i`'s word lies in the arguments' region. -/
theorem arg_in {o : State} (A : PSearchABI o) {i : Nat} (hi : i < 10) :
    (aR o).Contains (addr (o.gpr .esp) (4 + 4 * i)) 4 := by
  have hb := A.stackBound
  show (⟨argAddr o 0, 40⟩ : Region).Contains _ _
  rw [addr_eq (by omega_using [hi, hb]), show argAddr o 0 = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from
    addr_eq (k := 4) (by omega_using [hb])]
  exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [])

/-- The state's word at `d` lies in the state's region. -/
theorem st_in {o : State} (A : PSearchABI o) {d : Nat} (hd : d + 4 ≤ 128) :
    (sR o).Contains (addr (arg o 9) d) 4 :=
  contains_addr A.sBound hd

theorem oR_mem {o : State} (A : PSearchABI o) : oR o ∈ o.wr := by rw [A.wr]; simp
theorem uR_mem {o : State} (A : PSearchABI o) : uR o ∈ o.wr := by rw [A.wr]; simp
theorem bR_mem {o : State} (A : PSearchABI o) : bR o ∈ o.wr := by rw [A.wr]; simp
theorem sR_mem {o : State} (A : PSearchABI o) : sR o ∈ o.wr := by rw [A.wr]; simp
theorem aR_mem {o : State} (A : PSearchABI o) : aR o ∈ o.wr := by rw [A.wr]; simp

theorem st_ea {s : State} {S : BitVec 32} (h : s.gpr .esi = S) (d : Nat) : s.ea (st d) = addr S d := by
  show s.ea ⟨.esi, d⟩ = _; rw [ea_mk, h]

structure St (o : State) (ds : List Nat) (f : Nat → BitVec 32) (s : State) : Prop where
  abi : PSearchABI o
  rd : s.rd = o.rd
  wr : s.wr = o.wr
  syms : s.syms = o.syms
  esp : s.gpr .esp = o.gpr .esp
  esi : s.gpr .esi = arg o 9
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem (arg o 9) ds f

theorem St.reg {o s t : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {r : Reg} {v : BitVec 32}
    (U : Upd s t r v) (hr : Scratch r) : St o ds f t := by
  refine ⟨h.abi, U.rd.trans h.rd, U.wr.trans h.wr, U.syms.trans h.syms, ?_, ?_, fun q hq hne => ?_,
    U.mem ▸ h.frame, U.mem ▸ h.words⟩
  · rw [U.other _ (saved_ne hr (by decide)), h.esp]
  · rw [U.other _ (saved_ne hr (by decide)), h.esi]
  · rw [U.other _ (saved_ne hr hq), h.saved q hq hne]

theorem St.fupd {o s t : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (F : Fupd s t) :
    St o ds f t :=
  ⟨h.abi, F.rd.trans h.rd, F.wr.trans h.wr, F.syms.trans h.syms, by rw [F.gpr, h.esp], by rw [F.gpr, h.esi],
    fun q hq hne => by rw [F.gpr, h.saved q hq hne], F.mem ▸ h.frame, F.mem ▸ h.words⟩

theorem Live.st {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) :
    St o liveDs (liveF p (o.gpr .esi) used n) s := by
  obtain ⟨A, rfl⟩ := h.input
  exact ⟨A, h.rd, h.wr, h.syms, h.esp, h.esi, h.saved, h.frame, h.words⟩

theorem liveDs_aligned : Aligned liveDs := by decide

/-- The state's words are readable and writable. -/
theorem St.wIn {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {d : Nat} (hd : d + 4 ≤ 128) :
    InRegions s.wr (addr (arg o 9) d) 4 := by
  rw [h.wr]; exact ⟨_, sR_mem h.abi, st_in h.abi hd⟩

theorem St.rIn {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {d : Nat} (hd : d + 4 ≤ 128) :
    InRegions (s.rd ++ s.wr) (addr (arg o 9) d) 4 :=
  let ⟨r, hr, hc⟩ := h.wIn hd; ⟨r, List.mem_append_right _ hr, hc⟩

/-- `mov r, [esi + d]`. -/
theorem St.ld {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {r : Reg} (hr : Scratch r)
    {d : Nat} (hd : d ∈ ds) (hd4 : d + 4 ≤ 128) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, St o ds f t → t.gpr r = f d → (∀ q, q ≠ r → t.gpr q = s.gpr q) → t.cf = s.cf →
      t.mem = s.mem → WP isa (.block rest) t Q) :
    WP isa (.block (.mov r (.mem (st d)) :: rest)) s Q := by
  show WP isa (.block (.mov r (.mem ⟨.esi, d⟩) :: rest)) s Q
  refine wp_movS (readSrc_mem h.esi (h.rIn hd4)) fun t U c => k t (h.reg U hr) ?_ U.other c U.mem
  rw [U.gpr]; exact h.words.get hd

/-- `mov [esi + d], r`. -/
theorem St.stw {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds) {r : Reg}
    {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, St o (d :: ds) (upd f d (s.gpr r)) t → t.gpr = s.gpr → t.zf = s.zf → t.cf = s.cf →
      Frame [sR o] s.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (.store (st d) r :: rest)) s Q := by
  refine wp_storeS (st_ea h.esi d) (h.wIn hd) fun t M => k t ?_ M.gpr M.zf M.cf
    (by rw [M.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (st_in h.abi hd))
  refine ⟨h.abi, M.rd.trans h.rd, M.wr.trans h.wr, M.syms.trans h.syms, by rw [M.gpr, h.esp],
    by rw [M.gpr, h.esi], fun q hq hne => by rw [M.gpr, h.saved q hq hne], ?_, ?_⟩
  · rw [M.mem]; exact h.frame.writeW (List.mem_append_left _ (sR_mem h.abi)) _ (st_in h.abi hd)
  · rw [M.mem]; exact h.words.write' h.abi.sBound hA hd hd4 _

theorem St.sub {o s : State} {ds ds' : List Nat} {f : Nat → BitVec 32} (h : St o ds f s)
    (hs : ∀ d ∈ ds', d ∈ ds) : St o ds' f s :=
  ⟨h.abi, h.rd, h.wr, h.syms, h.esp, h.esi, h.saved, h.frame, h.words.sub hs⟩

theorem St.congr {o s : State} {ds : List Nat} {f g : Nat → BitVec 32} (h : St o ds f s)
    (e : ∀ d ∈ ds, f d = g d) : St o ds g s :=
  ⟨h.abi, h.rd, h.wr, h.syms, h.esp, h.esi, h.saved, h.frame, h.words.congr e⟩

theorem len_pos {o : State} (A : PSearchABI o) : 64 ≤ (arg o 1).toNat ∧ (arg o 1).toNat ≤ 1024 := by
  have := A.outLen
  have := A.bitsLow
  have := A.bitsHigh
  omega_arith

/-- Zeros at the output, the width's octets. -/
theorem zeroOut_ok {s : State} {S P : BitVec 32} {n : Nat} (hesi : s.gpr .esi = S)
    (hd : InRegions (s.rd ++ s.wr) (addr S outOff) 4) (hl : InRegions (s.rd ++ s.wr) (addr S widthOff) 4)
    (hP : s.mem.readW (addr S outOff) 32 = P) (hn : s.mem.readW (addr S widthOff) 32 = BitVec.ofNat 32 n)
    (hR : (⟨P.setWidth 64, n⟩ : Region) ∈ s.wr) (h0 : 0 < n) (hb : P.toNat + n ≤ 2 ^ 32) (hn32 : n < 2 ^ 32) :
    WP isa zeroOut s fun u => Frame [⟨P.setWidth 64, n⟩] s.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (P.setWidth 64) n = List.replicate n 0 ∧ Keeps [.eax, .ecx, .edx] s u := by
  unfold zeroOut
  refine WP.seq (wp_ldm hesi hd fun t₁ u₁ => ?_)
  refine wp_ldm ((u₁.other _ (by decide)).trans hesi) (by rw [u₁.rd, u₁.wr]; exact hl) fun t₂ u₂ => ?_
  refine wp_movi fun t₃ u₃ => WP.block_nil ?_
  have k₃ : Keeps [.eax, .ecx, .edx] s t₃ :=
    ((KeySearch.Upd.keeps u₁ |>.mono (by decide)).trans (KeySearch.Upd.keeps u₂ |>.mono (by decide))).trans
      (KeySearch.Upd.keeps u₃ |>.mono (by decide))
  have m₃ : t₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have I₀ : ZInv s P n 0 t₃ := ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hP, BitVec.add_zero],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, hn, Nat.sub_zero],
    u₃.gpr, by rw [m₃]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), k₃⟩
  refine WP.loop (M := isa) (fun (j : Nat) (u : State) => ∃ k, j = n - k ∧ k < n ∧ ZInv s P n k u)
    (fun j u hu => ?_) _ t₃ ⟨0, rfl, h0, I₀⟩
  obtain ⟨k, rfl, hk, I⟩ := hu
  refine WP.mono (zeroStep_ok hR hb hn32 hk I) fun v ⟨J, z⟩ => ?_
  by_cases he : n - (k + 1) = 0
  · left
    refine ⟨by simp only [eval, z, he, decide_true, Option.map_some, Bool.not_true], J.frame, ?_, J.keeps⟩
    apply List.ext_getElem
    · simp [Spec.Rsa.bytesAt]
    · intro i h₁ _
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
      exact J.zero i (by omega_using [he, h₁])
  · right
    exact ⟨by simp only [eval, z, he, decide_false, Option.map_some, Bool.not_false], _, by omega_using [hk],
      k + 1, rfl, by omega_using [he], J⟩

/-- Zeros at the output. -/
theorem St.zeroOut {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (ho : f outOff = arg o 0) (hl : f widthOff = BitVec.ofNat 32 (arg o 1).toNat)
    (hdo : outOff ∈ ds) (hdl : widthOff ∈ ds) :
    WP isa zeroOut s fun u => St o ds f u ∧
      Spec.Rsa.bytesAt u.mem (argumentPointer o 0) (arg o 1).toNat = List.replicate (arg o 1).toNat 0 ∧
      Frame [oR o] s.mem u.mem ∧ (∀ r, ¬ Scratch r → u.gpr r = s.gpr r) := by
  have A := h.abi
  have hp := len_pos A
  have ob := A.oBound
  refine WP.mono_syms (zeroOut_ok h.esi (h.rIn (by decide)) (h.rIn (by decide))
    ((h.words.get hdo).trans ho) ((h.words.get hdl).trans hl) (by rw [h.wr]; exact oR_mem A) (by omega_using [hp]) ob
    (by omega_using [])) fun t ⟨F, Z, K⟩ sy => ?_
  refine ⟨⟨A, K.2.1.trans h.rd, K.2.2.trans h.wr, sy.trans h.syms, by rw [K.1 _ (by decide), h.esp],
      by rw [K.1 _ (by decide), h.esi], fun q hq hne => ?_, h.frame.trans (F.mono fun r hr => ?_),
      h.words.frame A.sBound hA F fun r hr => ?_⟩, Z, F, fun r hr => K.1 _ fun hm => hr (by simp at hm; omega)⟩
  · rw [K.1 _ (fun hm => saved_ne (q := q) (by simp at hm; omega) hq rfl), h.saved q hq hne]
  · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ (oR_mem A)
  · simp only [List.mem_singleton] at hr; subst hr; exact A.os.symm

end VG.Proof.Ffdh.X86.PSearch
