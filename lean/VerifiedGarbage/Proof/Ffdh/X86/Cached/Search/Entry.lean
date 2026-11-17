module

public import VerifiedGarbage.Impl.Ffdh.X86.Cached
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Ffdh.GenerationSearch
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rsa.Contract

/-! ### `Ffdh.X86.Cached.Search.Data`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86.Cached.Search.Words`, which this module and modules that import it used -/

section

/-! # The key search's state words (x86)

The controller keeps its words in the 128-byte state, at `addr S d`:
reading one through a store to another (`readW_write`), and through writes
apart from the state (`readW_frame`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86

/-- The state's region. -/
abbrev stR (S : BitVec 32) : Region := ⟨S.setWidth 64, 128⟩

/-- A store to the state's word at `d`, read at `e`. -/
theorem readW_write {m : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {d e : Nat} (v : BitVec 32)
    (hd : d + 4 ≤ 128) (he : e + 4 ≤ 128) (hde : d = e ∨ d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr S d) v).readW (addr S e) 32 = if d = e then v else m.readW (addr S e) 32 := by
  rw [Spill.addr_eq_of hS hd, Spill.addr_eq_of hS he]
  split
  · subst e; exact Mem.readW_writeW_self32 _ _ _
  · refine Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_using [he]) (by omega_using [hd])) (by decide)

/-- The state's word at `d` lies in the state. -/
theorem contains_addr {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {d : Nat} (hd : d + 4 ≤ 128) :
    (stR S).Contains (addr S d) 4 := by
  rw [Spill.addr_eq_of hS hd]
  exact Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])

/-- A word of the state, through writes apart from it. -/
theorem readW_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {S : BitVec 32}
    (hS : S.toNat + 128 ≤ 2 ^ 32) (hd : ∀ r ∈ rs, (stR S).Disjoint r) {d : Nat} (hd4 : d + 4 ≤ 128) :
    m'.readW (addr S d) 32 = m.readW (addr S d) 32 :=
  h.readW (contains_addr hS hd4) hd (by decide)

/-- Bytes apart from the regions a frame names. -/
theorem bytes_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  exact List.map_congr_left fun i hi => h.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-! ## Words by their offsets -/

/-- The state's words at the offsets `ds` hold `f` of their offsets. -/
def Ctl (m : Mem) (S : BitVec 32) (ds : List Nat) (f : Nat → BitVec 32) : Prop :=
  ∀ d ∈ ds, m.readW (addr S d) 32 = f d

/-- Offsets of whole words in the state. -/
def Aligned (ds : List Nat) : Prop := ∀ d ∈ ds, d + 4 ≤ 128 ∧ d % 4 = 0

instance (ds : List Nat) : Decidable (Aligned ds) := inferInstanceAs (Decidable (∀ d ∈ ds, _))

/-- `f` with `v` at `d`. -/
def upd (f : Nat → BitVec 32) (d : Nat) (v : BitVec 32) : Nat → BitVec 32 := fun e => if e = d then v else f e

theorem Ctl.get {m : Mem} {S : BitVec 32} {ds : List Nat} {f : Nat → BitVec 32} (h : Ctl m S ds f) {d : Nat}
    (hd : d ∈ ds) : m.readW (addr S d) 32 = f d := h d hd

theorem Ctl.congr {m : Mem} {S : BitVec 32} {ds : List Nat} {f g : Nat → BitVec 32} (h : Ctl m S ds f)
    (e : ∀ d ∈ ds, f d = g d) : Ctl m S ds g := fun d hd => (h d hd).trans (e d hd)

/-- A store to a word of the state. -/
theorem Ctl.write {m : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {ds : List Nat}
    {f : Nat → BitVec 32} (h : Ctl m S ds f) (hA : Aligned ds) {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0)
    (v : BitVec 32) : Ctl (m.writeW (addr S d) v) S ds (upd f d v) := by
  intro e he
  obtain ⟨he1, he4⟩ := hA e he
  rw [readW_write hS v hd he1 (by omega_using [hd4, he4])]
  unfold upd
  by_cases hde : d = e
  · subst hde; simp
  · rw [ite_eq_right hde, ite_eq_right (Ne.symm hde)]; exact h e he

/-- Writes apart from the state. -/
theorem Ctl.frame {m m' : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {ds : List Nat}
    {f : Nat → BitVec 32} (h : Ctl m S ds f) (hA : Aligned ds) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (stR S).Disjoint r) : Ctl m' S ds f := fun e he => by
  rw [readW_frame hf hS hd (hA e he).1]; exact h e he

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! ### `Ffdh.X86.Cached.Search.ABI`, which this module and modules that import it used -/

section

/-! # The key search from the context on i686: what its cdecl contract supplies

`vg_ffdh_generate_key_search_cached(x, x_len, y, y_len, used, domain, domain_len, p_len, rand,
rand_len, scratch, scratch_len, state, ctx, ctx_len)`: fifteen arguments on the stack. The
controller uses 228 bytes of stack: its attempt's frame of 52, the call's return address and the
callee's own 172.
-/

@[expose] public section
namespace VG.Proof.Ffdh.X86.Cached.Search
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The bytes of stack the controller uses. -/
abbrev stack : Nat := 228

/-- The arguments' regions: `x`, `y`, `used`, `domain`, `rand`, `scratch` and `state`. -/
abbrev xR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat⟩
abbrev yR (s : State) : Region := ⟨argumentPointer s 2, (arg s 3).toNat⟩
abbrev uR (s : State) : Region := ⟨argumentPointer s 4, 8⟩
abbrev dR (s : State) : Region := ⟨argumentPointer s 5, (arg s 6).toNat⟩
abbrev rR (s : State) : Region := ⟨argumentPointer s 8, (arg s 9).toNat⟩
abbrev bR (s : State) : Region := ⟨argumentPointer s 10, (arg s 11).toNat * 8⟩
abbrev sR (s : State) : Region := ⟨argumentPointer s 12, 128⟩
abbrev cR (s : State) : Region := ⟨argumentPointer s 13, (arg s 14).toNat * 8⟩
/-- The arguments themselves. -/
abbrev aR (s : State) : Region := ⟨argAddr s 0, 60⟩
/-- The return address and the stack below it. -/
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev lowR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 228#64, 228⟩

structure KeySearchABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 60 ≤ 2 ^ 32
  rd : s.rd = [dR s, rR s, cR s]
  wr : s.wr = [xR s, yR s, uR s, bR s, sR s, aR s]
  xy : (xR s).Disjoint (yR s)
  xu : (xR s).Disjoint (uR s)
  xd : (xR s).Disjoint (dR s)
  xr : (xR s).Disjoint (rR s)
  xb : (xR s).Disjoint (bR s)
  xs : (xR s).Disjoint (sR s)
  xc : (xR s).Disjoint (cR s)
  xa : (xR s).Disjoint (aR s)
  yu : (yR s).Disjoint (uR s)
  yd : (yR s).Disjoint (dR s)
  yr : (yR s).Disjoint (rR s)
  yb : (yR s).Disjoint (bR s)
  ys : (yR s).Disjoint (sR s)
  yc : (yR s).Disjoint (cR s)
  ya : (yR s).Disjoint (aR s)
  ud : (uR s).Disjoint (dR s)
  ur : (uR s).Disjoint (rR s)
  ub : (uR s).Disjoint (bR s)
  us : (uR s).Disjoint (sR s)
  uc : (uR s).Disjoint (cR s)
  ua : (uR s).Disjoint (aR s)
  db : (dR s).Disjoint (bR s)
  ds : (dR s).Disjoint (sR s)
  da : (dR s).Disjoint (aR s)
  rb : (rR s).Disjoint (bR s)
  rs : (rR s).Disjoint (sR s)
  ra : (rR s).Disjoint (aR s)
  bs : (bR s).Disjoint (sR s)
  bc : (bR s).Disjoint (cR s)
  ba : (bR s).Disjoint (aR s)
  sc : (sR s).Disjoint (cR s)
  sa : (sR s).Disjoint (aR s)
  ca : (cR s).Disjoint (aR s)
  retX : (retR s).Disjoint (xR s)
  retY : (retR s).Disjoint (yR s)
  retU : (retR s).Disjoint (uR s)
  retD : (retR s).Disjoint (dR s)
  retRand : (retR s).Disjoint (rR s)
  retB : (retR s).Disjoint (bR s)
  retS : (retR s).Disjoint (sR s)
  retC : (retR s).Disjoint (cR s)
  retA : (retR s).Disjoint (aR s)
  lowX : (lowR s).Disjoint (xR s)
  lowY : (lowR s).Disjoint (yR s)
  lowU : (lowR s).Disjoint (uR s)
  lowD : (lowR s).Disjoint (dR s)
  lowRand : (lowR s).Disjoint (rR s)
  lowB : (lowR s).Disjoint (bR s)
  lowS : (lowR s).Disjoint (sR s)
  lowC : (lowR s).Disjoint (cR s)
  lowA : (lowR s).Disjoint (aR s)
  xBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  yBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  uBound : (arg s 4).toNat + 8 ≤ 2 ^ 32
  dBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  rBound : (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32
  bBound : (arg s 10).toNat + (arg s 11).toNat * 8 ≤ 2 ^ 32
  sBound : (arg s 12).toNat + 128 ≤ 2 ^ 32
  cBound : (arg s 13).toNat + (arg s 14).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 7).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 7).toNat (arg s 6).toNat
  xLen : (arg s 1).toNat = (arg s 7).toNat
  yLen : (arg s 3).toNat = (arg s 7).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 7).toNat ≤ (arg s 11).toNat
  domValid : Spec.Ffdh.domainValid (arg s 7).toNat (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
  keys : (s.mem.readW (argumentPointer s 12) 64).toNat ≤ 128
  scalars : (s.mem.readW (argumentPointer s 12 + 8) 64).toNat ≤ 128
  width : s.mem.readW (argumentPointer s 12 + 16) 64 = BitVec.ofNat 64 (arg s 7).toNat
  ctxLen : (arg s 14).toNat = Spec.Ffdh.generationPrecomputedWords (arg s 7).toNat
  ctx : Spec.Ffdh.generationPrecompute (arg s 7).toNat (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat) =
    some (Spec.Rsa.wordsAt s.mem (argumentPointer s 13) (arg s 14).toNat)

theorem keySearchABI_of {s : State} (h : (Spec.Ffdh.cachedKeySearchContract abi stack).pre s) : KeySearchABI s := by
  sig_pre [Spec.Ffdh.cachedKeySearchContract, Spec.Ffdh.cachedKeySearchSig, Spec.Ffdh.keySearchSig, abi, argSlots,
    argVal, argBytes, stackBelow, Spec.Ffdh.generationContextAt] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! # The key search's public data and loop states (x86)

`KPub` is everything two constant-time runs share: the arguments but the
random octets' values, the domain and the initial budgets. A loop state
(`Live`) is at an offset into the tape with budgets left; the search from
there (`KPub.tail`) is what the controller returns. Every state of the run
differs from the entry's memory only in the writable arguments and the stack
below the entry's (`Frame (frameR o)`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.Spec.Ffdh
open VG.Proof.Ffdh.GenerationSearch
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
  C : BitVec 32
  clen : Nat

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
  C := arg s 13
  clen := (arg s 14).toNat

/-- The domain's parameters. -/
abbrev KPub.a (p : KPub) : Parameters := domainOf p.len p.dom

def Input (p : KPub) (o : State) : Prop := KeySearchABI o ∧ ofState o = p

/-- The random octets at entry. -/
abbrev randOf (o : State) : List Byte := Spec.Rsa.bytesAt o.mem (argumentPointer o 8) (arg o 9).toNat

/-- The search from octet `used` of `rand`, with `keys` and `scalars` left. -/
abbrev KPub.tail (p : KPub) (rand : List Byte) (used keys scalars : Nat) : KeySearchResult :=
  keyTail .cached p.a p.len rand used keys scalars

/-- Where the run may write: the writable arguments and the stack below the entry's. -/
abbrev frameR (o : State) : List Region := o.wr ++ [lowR o]

/-- The offsets of the words the loop keeps. -/
def liveDs : List Nat := [0, 4, 8, 12, 16, 20, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 76, 80, 84]

/-- The words the loop keeps: the budgets, the width and the request's high half, the caller's
`esi`, the arguments passed on, the tape's pointer and length, the octets consumed and the context. -/
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
  if d = 76 then p.up else
  if d = 80 then p.C else
  if d = 84 then BitVec.ofNat 32 p.clen else 0

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
  small : result.retries.keys ≤ 128 ∧ result.retries.scalars ≤ 128 ∧ result.used ≤ p.randLen

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! # The key search's entry (x86)

`entry` saves the caller's `esi` in the state, points `esi` at it and keeps
the arguments the loop needs there (`keep_ok`, one argument at a time):
from the contract's precondition, a loop state with nothing consumed and the
caller's budgets (`entry_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- Argument `i`'s word lies in the arguments' region. -/
theorem arg_in {o : State} (A : KeySearchABI o) {i : Nat} (hi : i < 15) :
    (aR o).Contains (addr (o.gpr .esp) (4 + 4 * i)) 4 := by
  have hb := A.stackBound
  show (⟨argAddr o 0, 60⟩ : Region).Contains _ _
  rw [addr_eq (by omega_using [hi, hb]), show argAddr o 0 = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from
    addr_eq (k := 4) (by omega_using [hb])]
  exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [])

/-- The state's word at `d` lies in the state's region. -/
theorem st_in {o : State} (A : KeySearchABI o) {d : Nat} (hd : d + 4 ≤ 128) :
    (sR o).Contains (addr (arg o 12) d) 4 :=
  contains_addr A.sBound hd

theorem sR_mem {o : State} (A : KeySearchABI o) : sR o ∈ o.wr := by rw [A.wr]; simp
theorem aR_mem {o : State} (A : KeySearchABI o) : aR o ∈ o.wr := by rw [A.wr]; simp

theorem st_ea {s : State} {S : BitVec 32} (h : s.gpr .esi = S) (d : Nat) : s.ea (st d) = addr S d := by
  show s.ea ⟨.esi, d⟩ = _; rw [ea_mk, h]

/-- An entry state: the state's words at `ds` hold `f`, the memory differs from the entry's only in
the state. -/
structure Ent (o : State) (ds : List Nat) (f : Nat → BitVec 32) (s : State) : Prop where
  rd : s.rd = o.rd
  wr : s.wr = o.wr
  esp : s.gpr .esp = o.gpr .esp
  esi : s.gpr .esi = arg o 12
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → s.gpr r = o.gpr r
  frame : Frame [sR o] o.mem s.mem
  words : Ctl s.mem (arg o 12) ds f

/-- Argument `i`, read from an entry state. -/
theorem Ent.argSrc {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (A : KeySearchABI o) (h : Ent o ds f s)
    {i : Nat} (hi : i < 15) :
    readSrc s (.mem (argAt 0 i)) = some (arg o i) := by
  have e : argAt 0 i = ⟨.esp, 4 + 4 * i⟩ := by simp [argAt, at_]
  rw [e, readSrc_mem h.esp (by rw [h.rd, h.wr]; exact ⟨_, List.mem_append_right _ (aR_mem A), arg_in A hi⟩)]
  congr 1
  exact h.frame.readW (arg_in A hi) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact A.sa.symm) (by decide)

/-- `keep i d`: argument `i` to the state's word at `d`. -/
theorem keep_ok {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (A : KeySearchABI o) (h : Ent o ds f s)
    (hA : Aligned ds) {i d : Nat} (hi : i < 15) (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0) {rest : List Instr}
    {Q : State → Prop} (k : ∀ t, Ent o ds (upd f d (arg o i)) t → WP isa (.block rest) t Q) :
    WP isa (.block (keep i d ++ rest)) s Q := by
  refine wp_movS (h.argSrc A hi) fun t U _ => ?_
  refine wp_storeS (st_ea ((U.other _ (by decide)).trans h.esi) d)
    (by rw [U.wr, h.wr]; exact ⟨_, sR_mem A, st_in A hd⟩) fun t' M => k t' ?_
  rw [U.gpr] at M
  refine ⟨M.rd.trans (U.rd.trans h.rd), M.wr.trans (U.wr.trans h.wr), ?_, ?_, fun r hr hne => ?_, ?_, ?_⟩
  · rw [M.gpr, U.other _ (by decide), h.esp]
  · rw [M.gpr, U.other _ (by decide), h.esi]
  · rw [M.gpr, U.other _ (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      first | decide | exact absurd rfl hne), h.saved r hr hne]
  · rw [M.mem, U.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ (st_in A hd)
  · rw [M.mem, U.mem]; exact h.words.write A.sBound hA hd hd4 _

/-- The halves of a 64-bit word below `2³²`. -/
theorem halves {m : Mem} {a : Addr} {k : Nat} (h : m.readW a 64 = BitVec.ofNat 64 k) (hk : k < 2 ^ 32) :
    m.readW a 32 = BitVec.ofNat 32 k ∧ m.readW (a + BitVec.ofNat 64 4) 32 = 0 := by
  refine ⟨(Mem.readW_lo32 h).trans ?_, (Mem.readW_hi32 h).trans ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using []
  · simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega_using [hk] : k < 2 ^ 64), Nat.div_eq_of_lt hk]; rfl

/-- The state's first three words, from the contract's precondition. -/
theorem entry_words {o : State} (A : KeySearchABI o) :
    o.mem.readW (addr (arg o 12) 0) 32 = BitVec.ofNat 32 (ofState o).keys ∧
      o.mem.readW (addr (arg o 12) 4) 32 = 0 ∧
      o.mem.readW (addr (arg o 12) 8) 32 = BitVec.ofNat 32 (ofState o).scalars ∧
      o.mem.readW (addr (arg o 12) 12) 32 = 0 ∧ o.mem.readW (addr (arg o 12) 20) 32 = 0 := by
  have hS := A.sBound
  have e : ∀ d, d + 4 ≤ 128 → addr (arg o 12) d = argumentPointer o 12 + BitVec.ofNat 64 d :=
    fun d hd => Spill.addr_eq_of hS hd
  have k0 := halves (m := o.mem) (a := argumentPointer o 12) (k := (ofState o).keys)
    (by simp only [ofState, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by have := A.keys; simp only [ofState]; omega_using [this])
  have k1 := halves (m := o.mem) (a := argumentPointer o 12 + 8) (k := (ofState o).scalars)
    (by simp only [ofState, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by have := A.scalars; simp only [ofState]; omega_using [this])
  have k2 := halves A.width (by have := A.pLen.2; unfold Spec.Ffdh.pLenValid at *; omega_using [])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e 0 (by decide), BitVec.add_zero]; exact k0.1
  · rw [e 4 (by decide)]; exact k0.2
  · rw [e 8 (by decide)]; exact k1.1
  · rw [e 12 (by decide), show BitVec.ofNat 64 12 = (8 : BitVec 64) + 4#64 from rfl, ← BitVec.add_assoc]
    exact k1.2
  · rw [e 20 (by decide), show BitVec.ofNat 64 20 = (16 : BitVec 64) + 4#64 from rfl, ← BitVec.add_assoc]
    exact k2.2

/-- The words before the entry. -/
abbrev f0 (o : State) : Nat → BitVec 32 := fun d => o.mem.readW (addr (arg o 12) d) 32

theorem entry_ok {o : State} (A : KeySearchABI o) :
    WP isa (.block Impl.Ffdh.X86.Cached.Search.entry) o (Live (ofState o) o 0 (ofState o).keys (ofState o).scalars) := by
  have hA : Aligned liveDs := by decide
  have e12 : argAt 0 12 = ⟨.esp, 4 + 4 * 12⟩ := by simp [argAt, at_]
  have r12 : readSrc o (.mem (argAt 0 12)) = some (arg o 12) := by
    rw [e12, readSrc_mem rfl ⟨_, List.mem_append_right _ (aR_mem A), arg_in A (i := 12) (by decide)⟩]; rfl
  unfold Impl.Ffdh.X86.Cached.Search.entry
  simp only [List.cons_append, List.append_assoc]
  refine wp_movS r12 fun t U _ => ?_
  refine wp_storeS (show t.ea ⟨.eax, savedOff⟩ = addr (arg o 12) 32 by rw [ea_mk, U.gpr]; rfl)
    (by rw [U.wr]; exact ⟨_, sR_mem A, st_in A (d := 32) (by decide)⟩) fun t₁ M => ?_
  refine wp_movS (v := t₁.gpr .eax) rfl fun t₂ U₂ _ => ?_
  have E : Ent o liveDs (upd (f0 o) 32 (o.gpr .esi)) t₂ := by
    refine ⟨U₂.rd.trans (M.rd.trans U.rd), U₂.wr.trans (M.wr.trans U.wr), ?_, ?_, fun r hr hne => ?_, ?_, ?_⟩
    · rw [U₂.other _ (by decide), M.gpr, U.other _ (by decide)]
    · rw [U₂.gpr, M.gpr, U.gpr]
    · have h1 : r ≠ .eax := by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [U₂.other _ hne, M.gpr, U.other _ h1]
    · rw [U₂.mem, M.mem, U.other _ (by decide), U.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (st_in A (by decide))
    · rw [U₂.mem, M.mem, U.other _ (by decide), U.mem]
      exact (show Ctl o.mem (arg o 12) liveDs (f0 o) from fun _ _ => rfl).write A.sBound hA (by decide)
        (by decide) _
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine wp_movS (v := 0) rfl fun t₃ U₃ _ => ?_
  have esi₃ : t₃.gpr .esi = arg o 12 := (U₃.other _ (by decide)).trans E.esi
  refine wp_storeS (st_ea esi₃ usedOff)
    (by rw [U₃.wr, E.wr]; exact ⟨_, sR_mem A, st_in A (d := 60) (by decide)⟩) fun t₄ M₄ => ?_
  refine wp_storeS (st_ea (M₄.gpr ▸ esi₃) (requestOff + 4))
    (by rw [M₄.wr, U₃.wr, E.wr]; exact ⟨_, sR_mem A, st_in A (d := 28) (by decide)⟩) fun t₅ M₅ => ?_
  refine WP.block_nil_iff.mpr ?_
  have W := entry_words A
  simp only [ofState] at W
  have g₄ : t₄.gpr .eax = 0 := by rw [M₄.gpr, U₃.gpr]
  have hm : t₅.mem = (t.mem.writeW (addr (arg o 12) usedOff) (0 : BitVec 32)).writeW
      (addr (arg o 12) (requestOff + 4)) (0 : BitVec 32) := by
    rw [M₅.mem, M₄.mem, M₄.gpr, U₃.gpr, U₃.mem]
  have C := (E.words.write A.sBound hA (d := usedOff) (by decide) (by decide) 0).write A.sBound hA
    (d := requestOff + 4) (by decide) (by decide) 0
  rw [← hm] at C
  have F : Frame [sR o] o.mem t₅.mem := by
    rw [hm]
    exact (E.frame.writeW (List.mem_singleton_self _) _ (st_in A (d := usedOff) (by decide))).writeW
      (List.mem_singleton_self _) _ (st_in A (d := requestOff + 4) (by decide))
  refine ⟨⟨A, rfl⟩, Nat.zero_le _, A.keys, A.scalars, M₅.rd.trans (M₄.rd.trans (U₃.rd.trans E.rd)),
    M₅.wr.trans (M₄.wr.trans (U₃.wr.trans E.wr)), ?_, ?_, fun r hr hne => ?_, ?_, C.congr ?_⟩
  · rw [M₅.gpr, M₄.gpr, U₃.other _ (by decide), E.esp]; rfl
  · rw [M₅.gpr, M₄.gpr, esi₃]; rfl
  · have h1 : r ≠ .eax := by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [M₅.gpr, M₄.gpr, U₃.other _ h1, E.saved r hr hne]
  · exact F.mono fun r hr => List.mem_append_left _ (by
      simp only [List.mem_singleton] at hr; subst hr; exact sR_mem A)
  · simp only [liveDs, List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl) <;>
      simp only [upd, liveF, ofState, xOff, yOff, upOff, domOff, dlenOff, lenOff, randOff, leftOff, scratchOff,
        slenOff, usedOff, requestOff, Impl.Ffdh.X86.Cached.Search.ctxOff, Impl.Ffdh.X86.Cached.Search.ctxLenOff] <;>
      simp [W.1, W.2.1, W.2.2.1, W.2.2.2.1, W.2.2.2.2]

end VG.Proof.Ffdh.X86.Cached.Search
