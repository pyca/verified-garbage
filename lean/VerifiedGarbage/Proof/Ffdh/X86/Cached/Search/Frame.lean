module

public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Ffdh.X86.Cached
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.Mont.X86
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Ffdh.GenerationSearch
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rsa.Contract

/-! ### `Ffdh.X86.Cached.Search.Entry`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Ffdh.X86.Cached.Search.Steps`, which this module and modules that import it used -/

section

/-! # Steps of the key search (x86)

`St o ds f`: a state of the run from the entry state `o`, `esi` at the
state, whose words at the offsets `ds` hold `f`, whose memory differs from
the entry's only where the run may write. A load of a word (`St.ld`), a
store (`St.stw`), a register-only instruction (`St.reg`, `St.fupd`) and the
zeros at the outputs (`St.zeroOutputs`) keep it.
-/

@[expose] public section

/-! ## Zeros at an output (x86)

`zeroOut d` writes `p_len` zeros at the pointer in the state's word at `d`,
one byte at a time (`zeroOut_ok`), changing only `eax`, `ecx` and `edx`.
-/

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search

/-- A byte of a store of one byte. -/
theorem byte_write {m : Mem} {a x : Addr} {v : BitVec 8} : (m.writeW a v) x = if x = a then v else m x := by
  have e : (x - a).toNat < 8 / 8 ↔ x = a := by
    rw [show 8 / 8 = 1 from rfl, Nat.lt_one_iff, ← BitVec.toNat_zero (w := 64), BitVec.toNat_inj]
    constructor
    · intro h; rw [← BitVec.sub_add_cancel x a, h, BitVec.zero_add]
    · intro h; rw [h, BitVec.sub_self]
  simp only [Mem.writeW, Mem.write, e]
  split
  · next h => subst h; simp
  · rfl

/-- `mov byte [m], r`. -/
theorem wp_store8 {is : List Instr} {s : State} {Q : State → Prop} {r : Reg8} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := {s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8)})
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- The output after `k` of its `n` bytes are zeroed. -/
structure ZInv (s₀ : State) (P : BitVec 32) (n k : Nat) (t : State) : Prop where
  edx : t.gpr .edx = P + BitVec.ofNat 32 k
  ecx : t.gpr .ecx = BitVec.ofNat 32 (n - k)
  eax : t.gpr .eax = 0
  frame : Frame [⟨P.setWidth 64, n⟩] s₀.mem t.mem
  zero : ∀ i < k, t.mem (P.setWidth 64 + BitVec.ofNat 64 i) = 0
  keeps : Keeps [.eax, .ecx, .edx] s₀ t

theorem zeroStep_ok {s₀ t : State} {P : BitVec 32} {n k : Nat} (hR : (⟨P.setWidth 64, n⟩ : Region) ∈ s₀.wr)
    (hb : P.toNat + n ≤ 2 ^ 32) (hn : n < 2 ^ 32) (hk : k < n) (I : ZInv s₀ P n k t) :
    WP isa (.block [.store8 (at_ .edx 0) .al, .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) t
      fun u => ZInv s₀ P n (k + 1) u ∧ u.zf = some (decide (n - (k + 1) = 0)) := by
  have hp : t.ea (at_ .edx 0) = P.setWidth 64 + BitVec.ofNat 64 k := by
    show (t.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = _
    rw [BitVec.add_zero, I.edx]; exact addr_eq (by omega_using [hb, hk])
  have hw : InRegions t.wr (P.setWidth 64 + BitVec.ofNat 64 k) 1 :=
    ⟨_, by rw [I.keeps.2.2]; exact hR, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hb, hk])⟩
  refine wp_store8 hp hw fun u₁ m₁ => wp_addi fun u₂ v₂ => wp_subi fun u₃ v₃ _ z₃ => WP.block_nil ?_
  have hv : (t.gpr (Reg8.al).reg).setWidth 8 = 0 := by show (t.gpr .eax).setWidth 8 = 0; rw [I.eax]; rfl
  rw [hv] at m₁
  have kk : Keeps [.eax, .ecx, .edx] t u₃ :=
    ((m₁.keeps _).trans (v₂.keeps.mono (by decide))).trans (v₃.keeps.mono (by decide))
  have mem₃ : u₃.mem = t.mem.writeW (P.setWidth 64 + BitVec.ofNat 64 k) (0 : BitVec 8) := by
    rw [v₃.mem, v₂.mem, m₁.mem]
  have fr : Frame [⟨P.setWidth 64, n⟩] t.mem u₃.mem := by
    rw [mem₃]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hb, hk]))
  refine ⟨⟨?_, ?_, ?_, I.frame.trans fr, fun i hi => ?_, I.keeps.trans kk⟩, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.edx, BitVec.add_assoc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.ecx, ofNat_pred (by omega_using [hk])]; rfl
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), m₁.gpr, I.eax]
  · rw [mem₃, byte_write]
    by_cases hik : i = k
    · subst hik; simp
    · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega_using [hb, hk, hi]) (by omega_using [hb, hk]) hik)]
      exact I.zero i (by omega_using [hi, hik])
  · rw [z₃, v₂.other _ (by decide), m₁.gpr, I.ecx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega_using [hn]) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega_using [hk]))

/-- `p_len` zeros at the pointer `P` in the state's word at `d`. -/
theorem zeroOut_ok {s : State} {S P : BitVec 32} {d n : Nat} (hesi : s.gpr .esi = S)
    (hd : InRegions (s.rd ++ s.wr) (addr S d) 4) (hl : InRegions (s.rd ++ s.wr) (addr S lenOff) 4)
    (hP : s.mem.readW (addr S d) 32 = P) (hn : s.mem.readW (addr S lenOff) 32 = BitVec.ofNat 32 n)
    (hR : (⟨P.setWidth 64, n⟩ : Region) ∈ s.wr) (h0 : 0 < n) (hb : P.toNat + n ≤ 2 ^ 32) (hn32 : n < 2 ^ 32) :
    WP isa (zeroOut d) s fun u => Frame [⟨P.setWidth 64, n⟩] s.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (P.setWidth 64) n = List.replicate n 0 ∧ Keeps [.eax, .ecx, .edx] s u := by
  unfold zeroOut
  refine WP.seq (wp_ldm hesi hd fun t₁ u₁ => ?_)
  refine wp_ldm ((u₁.other _ (by decide)).trans hesi) (by rw [u₁.rd, u₁.wr]; exact hl) fun t₂ u₂ => ?_
  refine wp_movi fun t₃ u₃ => WP.block_nil ?_
  have k₃ : Keeps [.eax, .ecx, .edx] s t₃ :=
    ((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))
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

end VG.Proof.Ffdh.X86.Cached.Search

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The registers the controller uses for itself. -/
abbrev Scratch (r : Reg) : Prop := r = .eax ∨ r = .ecx ∨ r = .edx

structure St (o : State) (ds : List Nat) (f : Nat → BitVec 32) (s : State) : Prop where
  abi : KeySearchABI o
  rd : s.rd = o.rd
  wr : s.wr = o.wr
  esp : s.gpr .esp = o.gpr .esp
  esi : s.gpr .esi = arg o 12
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem (arg o 12) ds f

theorem saved_ne {r q : Reg} (hq : Scratch q) (hr : r ∈ calleeSaved) : r ≠ q := by
  rcases hq with rfl | rfl | rfl <;> simp [calleeSaved] at hr <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem St.reg {o s t : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {r : Reg} {v : BitVec 32}
    (U : Upd s t r v) (hr : Scratch r) : St o ds f t := by
  refine ⟨h.abi, U.rd.trans h.rd, U.wr.trans h.wr, ?_, ?_, fun q hq hne => ?_, U.mem ▸ h.frame, U.mem ▸ h.words⟩
  · rw [U.other _ (saved_ne hr (by decide)), h.esp]
  · rw [U.other _ (saved_ne hr (by decide)), h.esi]
  · rw [U.other _ (saved_ne hr hq), h.saved q hq hne]

theorem St.fupd {o s t : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (F : Fupd s t) :
    St o ds f t :=
  ⟨h.abi, F.rd.trans h.rd, F.wr.trans h.wr, by rw [F.gpr, h.esp], by rw [F.gpr, h.esi],
    fun q hq hne => by rw [F.gpr, h.saved q hq hne], F.mem ▸ h.frame, F.mem ▸ h.words⟩

theorem Live.st {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    St o liveDs (liveF p (o.gpr .esi) used keys scalars) s := by
  obtain ⟨A, rfl⟩ := h.input
  exact ⟨A, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words⟩

theorem liveDs_aligned : Aligned liveDs := by decide

/-- The state's words are readable and writable. -/
theorem St.wIn {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {d : Nat} (hd : d + 4 ≤ 128) :
    InRegions s.wr (addr (arg o 12) d) 4 := by
  rw [h.wr]; exact ⟨_, sR_mem h.abi, st_in h.abi hd⟩

theorem St.rIn {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {d : Nat} (hd : d + 4 ≤ 128) :
    InRegions (s.rd ++ s.wr) (addr (arg o 12) d) 4 :=
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

/-- `mov [esi + d], r`. -/
theorem St.stw {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds) {r : Reg}
    {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, St o (d :: ds) (upd f d (s.gpr r)) t → t.gpr = s.gpr → t.zf = s.zf → t.cf = s.cf →
      Frame [sR o] s.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (.store (st d) r :: rest)) s Q := by
  refine wp_storeS (st_ea h.esi d) (h.wIn hd) fun t M => k t ?_ M.gpr M.zf M.cf
    (by rw [M.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (st_in h.abi hd))
  refine ⟨h.abi, M.rd.trans h.rd, M.wr.trans h.wr, by rw [M.gpr, h.esp], by rw [M.gpr, h.esi],
    fun q hq hne => by rw [M.gpr, h.saved q hq hne], ?_, ?_⟩
  · rw [M.mem]; exact h.frame.writeW (List.mem_append_left _ (sR_mem h.abi)) _ (st_in h.abi hd)
  · rw [M.mem]; exact h.words.write' h.abi.sBound hA hd hd4 _

theorem Ctl.sub {m : Mem} {S : BitVec 32} {ds ds' : List Nat} {f : Nat → BitVec 32} (h : Ctl m S ds f)
    (hs : ∀ d ∈ ds', d ∈ ds) : Ctl m S ds' f := fun d hd => h d (hs d hd)

theorem St.sub {o s : State} {ds ds' : List Nat} {f : Nat → BitVec 32} (h : St o ds f s)
    (hs : ∀ d ∈ ds', d ∈ ds) : St o ds' f s :=
  ⟨h.abi, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words.sub hs⟩

theorem St.congr {o s : State} {ds : List Nat} {f g : Nat → BitVec 32} (h : St o ds f s)
    (e : ∀ d ∈ ds, f d = g d) : St o ds g s :=
  ⟨h.abi, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words.congr e⟩

/-- The outputs' regions. -/
theorem xR_eq {o : State} (A : KeySearchABI o) : xR o = ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by
  rw [xR, A.xLen]
theorem yR_eq {o : State} (A : KeySearchABI o) : yR o = ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
  rw [yR, A.yLen]

/-- Zeros at the output `P` (`x` or `y`). -/
theorem St.zeroOne {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    {d : Nat} {P : BitVec 32} (hdP : f d = P) (hl : f lenOff = BitVec.ofNat 32 (arg o 7).toNat)
    (hdd : d ∈ ds) (hdl : lenOff ∈ ds) (hd4 : d + 4 ≤ 128)
    (hin : (⟨P.setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr)
    (hs : (stR (arg o 12)).Disjoint ⟨P.setWidth 64, (arg o 7).toNat⟩) (hb : P.toNat + (arg o 7).toNat ≤ 2 ^ 32) :
    WP isa (zeroOut d) s fun u => St o ds f u ∧
      Spec.Rsa.bytesAt u.mem (P.setWidth 64) (arg o 7).toNat = List.replicate (arg o 7).toNat 0 ∧
      Frame [⟨P.setWidth 64, (arg o 7).toNat⟩] s.mem u.mem ∧ (∀ r, ¬ Scratch r → u.gpr r = s.gpr r) := by
  have A := h.abi
  have hp := A.pLen
  unfold Spec.Ffdh.pLenValid at hp
  refine WP.mono (zeroOut_ok h.esi (h.rIn hd4) (h.rIn (by decide)) ((h.words.get hdd).trans hdP)
    ((h.words.get hdl).trans hl) (by rw [h.wr]; exact hin) (by omega_using [hp]) hb (by omega_using [])) fun t ⟨F, Z, K⟩ => ?_
  refine ⟨⟨A, K.2.1.trans h.rd, K.2.2.trans h.wr, by rw [K.1 _ (by decide), h.esp],
      by rw [K.1 _ (by decide), h.esi], fun q hq hne => ?_, h.frame.trans (F.mono fun r hr => ?_),
      h.words.frame A.sBound hA F fun r hr => ?_⟩, Z, F, fun r hr => K.1 _ fun hm => hr (by simp at hm; omega)⟩
  · rw [K.1 _ (fun hm => saved_ne (q := q) (by simp at hm; omega) hq rfl), h.saved q hq hne]
  · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ hin
  · simp only [List.mem_singleton] at hr; subst hr; exact hs

/-- Zeros at `x` and `y`. -/
theorem St.zeroOutputs {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (hx : f xOff = arg o 0) (hy : f yOff = arg o 2) (hl : f lenOff = BitVec.ofNat 32 (arg o 7).toNat)
    (hdx : xOff ∈ ds) (hdy : yOff ∈ ds) (hdl : lenOff ∈ ds) :
    WP isa zeroOutputs s fun u => St o ds f u ∧
      Spec.Rsa.bytesAt u.mem (argumentPointer o 0) (arg o 7).toNat = List.replicate (arg o 7).toNat 0 ∧
      Spec.Rsa.bytesAt u.mem (argumentPointer o 2) (arg o 7).toNat = List.replicate (arg o 7).toNat 0 ∧
      u.gpr .esp = s.gpr .esp ∧ (∀ r, ¬ Scratch r → u.gpr r = s.gpr r) := by
  have A := h.abi
  have hS := A.sBound
  have hp := A.pLen
  unfold Spec.Ffdh.pLenValid at hp
  have xb : (arg o 0).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.xBound; rw [A.xLen] at this; exact this
  have yb : (arg o 2).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.yBound; rw [A.yLen] at this; exact this
  have xin : (⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr := by
    rw [← xR_eq A, A.wr]; exact List.mem_cons_self ..
  have yin : (⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr := by
    rw [← yR_eq A, A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have xs : (stR (arg o 12)).Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← xR_eq A]; exact A.xs.symm
  have ys : (stR (arg o 12)).Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← yR_eq A]; exact A.ys.symm
  refine WP.seq (WP.mono (zeroOut_ok h.esi (h.rIn (by decide)) (h.rIn (by decide)) ((h.words.get hdx).trans hx)
    ((h.words.get hdl).trans hl) (by rw [h.wr]; exact xin) (by omega_using [hp]) xb (by omega_using [])) fun t ⟨F, Z, K⟩ => ?_)
  have ht : St o ds f t := by
    refine ⟨A, K.2.1.trans h.rd, K.2.2.trans h.wr, by rw [K.1 _ (by decide), h.esp],
      by rw [K.1 _ (by decide), h.esi], fun q hq hne => ?_, h.frame.trans (F.mono fun r hr => ?_),
      h.words.frame hS hA F fun r hr => ?_⟩
    · rw [K.1 _ (fun hm => saved_ne (q := q) (by simp at hm; omega) hq rfl), h.saved q hq hne]
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ xin
    · simp only [List.mem_singleton] at hr; subst hr; exact xs
  refine WP.mono (zeroOut_ok ht.esi (ht.rIn (by decide)) (ht.rIn (by decide)) ((ht.words.get hdy).trans hy)
    ((ht.words.get hdl).trans hl) (by rw [ht.wr]; exact yin) (by omega_using [hp]) yb (by omega_using [])) fun u ⟨F', Z', K'⟩ => ?_
  refine ⟨⟨A, K'.2.1.trans ht.rd, K'.2.2.trans ht.wr, by rw [K'.1 _ (by decide), ht.esp],
      by rw [K'.1 _ (by decide), ht.esi], fun q hq hne => ?_, ht.frame.trans (F'.mono fun r hr => ?_),
      ht.words.frame hS hA F' fun r hr => ?_⟩, ?_, Z', ?_, fun r hr => ?_⟩
  · rw [K'.1 _ (fun hm => saved_ne (q := q) (by simp at hm; omega) hq rfl), ht.saved q hq hne]
  · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ yin
  · simp only [List.mem_singleton] at hr; subst hr; exact ys
  · rw [bytes_frame F' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [← xR_eq A, ← yR_eq A]; exact A.xy) (by omega_using [])]
    exact Z
  · rw [K'.1 _ (by decide), K.1 _ (by decide)]
  · rw [K'.1 _ (fun hm => hr (by simp at hm; omega)), K.1 _ (fun hm => hr (by simp at hm; omega))]

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! # The attempt's frame of arguments (x86)

The attempt allocates 44 bytes below the entry's stack pointer and stores
`vg_ffdh_generate_key`'s eleven arguments there (`arguments_ok`). With the
call's return address and the callee's 172 bytes below them, they are the
228 bytes below the entry's stack pointer, at offsets of `low o`
(`low_sub`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The base of the stack the controller uses. -/
abbrev low (o : State) : Addr := (o.gpr .esp).setWidth 64 - 228#64

theorem low_toNat {o : State} (A : KeySearchABI o) : (low o).toNat = (o.gpr .esp).toNat - 228 := by
  have : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  have := (o.gpr .esp).isLt
  simp only [low, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- A stack pointer `k ≤ 228` bytes below the entry's, at its offset from `low o`. -/
theorem sw_sub {o : State} (A : KeySearchABI o) {k : Nat} (hk : k ≤ 228) :
    (o.gpr .esp - BitVec.ofNat 32 k).setWidth 64 = low o + BitVec.ofNat 64 (228 - k) := by
  have h1 : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  have h2 := (o.gpr .esp).isLt
  have hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega_arith

/-- A word at `d` above a stack pointer `k` bytes below the entry's. -/
theorem addr_sub {o : State} (A : KeySearchABI o) {k d : Nat} (hk : k ≤ 228) (hd : d ≤ k) :
    addr (o.gpr .esp - BitVec.ofNat 32 k) d = low o + BitVec.ofNat 64 (228 - k + d) := by
  have h1 : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  have h2 := (o.gpr .esp).isLt
  have hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [addr, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega_arith

/-- A range at offsets of `low o` lies in the stack the controller uses. -/
theorem low_sub {o : State} {d n : Nat} (h : d + n ≤ 228) : Region.Sub ⟨low o + BitVec.ofNat 64 d, n⟩ (lowR o) :=
  Offset.sub_base _ h

theorem low_contains {o : State} (A : KeySearchABI o) {d n : Nat} (h : d + n ≤ 228) :
    (lowR o).Contains (low o + BitVec.ofNat 64 d) n := by
  have : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  exact Offset.contains_base _ h (by omega_arith)

/-- The frame's region. -/
abbrev frR (o : State) : Region := ⟨low o + BitVec.ofNat 64 176, 52⟩

/-- A state in the attempt's frame: `St` but for the stack pointer and the frame's region. -/
structure Fr (o : State) (ds : List Nat) (f : Nat → BitVec 32) (s : State) : Prop where
  abi : KeySearchABI o
  rd : s.rd = o.rd
  wr : s.wr = frR o :: o.wr
  esp : s.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes
  esi : s.gpr .esi = arg o 12
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → r ≠ .esp → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem (arg o 12) ds f

theorem St.alloc {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) :
    Fr o ds f (allocFrame argsBytes s) := by
  refine ⟨h.abi, h.rd, ?_, by rw [allocFrame_esp, h.esp], by rw [allocFrame_gpr _ _ (by decide), h.esi],
    fun r hr hne hsp => by rw [allocFrame_gpr _ _ hsp, h.saved r hr hne], h.frame, h.words⟩
  rw [allocFrame_wr, h.esp, h.wr, sw_sub h.abi (by decide)]; rfl

/-- `vg_ffdh_generate_key_cached`'s arguments for `used` octets consumed. -/
def callArg (o : State) (used : Nat) (j : Nat) : BitVec 32 :=
  if j = 0 then arg o 0 else
  if j = 2 then arg o 2 else
  if j = 4 then arg o 5 else
  if j = 5 then arg o 6 else
  if j = 7 then arg o 8 + BitVec.ofNat 32 used else
  if j = 9 then arg o 10 else
  if j = 10 then arg o 11 else
  if j = 11 then arg o 13 else
  if j = 12 then arg o 14 else arg o 7

/-- The first `k` arguments are in the frame. -/
def ArgsAt (o : State) (used k : Nat) (m : Mem) : Prop :=
  ∀ j < k, m.readW (low o + BitVec.ofNat 64 (176 + 4 * j)) 32 = callArg o used j

/-- `pass d j`: the state's word at `d`, argument `j`, to the frame. -/
theorem pass_ok {o s : State} {ds : List Nat} {f : Nat → BitVec 32} {used : Nat} (h : Fr o ds f s)
    (hA : Aligned ds) {d j : Nat} (hd : d ∈ ds) (hd4 : d + 4 ≤ 128) (hj : j < 13) (hv : f d = callArg o used j)
    (ha : ArgsAt o used j s.mem) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Fr o ds f t → ArgsAt o used (j + 1) t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (pass d j ++ rest)) s Q := by
  have A := h.abi
  have hS := A.sBound
  show WP isa (.block (.mov .eax (.mem ⟨.esi, d⟩) :: .store ⟨.esp, 4 * j⟩ .eax :: rest)) s Q
  have rin : InRegions (s.rd ++ s.wr) (addr (arg o 12) d) 4 := by
    rw [h.rd, h.wr]; exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (sR_mem A)), st_in A hd4⟩
  refine wp_movS (readSrc_mem h.esi rin) fun t U _ => ?_
  have ea : addr (t.gpr .esp) (4 * j) = low o + BitVec.ofNat 64 (176 + 4 * j) := by
    rw [U.other _ (by decide), h.esp, addr_sub A (by decide) (by unfold argsBytes; omega_arith)]; rfl
  have win : (frR o).Contains (low o + BitVec.ofNat 64 (176 + 4 * j)) 4 := by
    have : 228 ≤ (o.gpr .esp).toNat := A.stackLow
    exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine wp_storeS (show t.ea ⟨.esp, 4 * j⟩ = _ by rw [ea_mk, ea])
    (by rw [U.wr, h.wr]; exact ⟨_, List.mem_cons_self .., win⟩) fun t' M => k t' ?_ ?_
  · have lc := low_contains A (d := 176 + 4 * j) (n := 4) (by omega_arith)
    have fr : Frame [lowR o] s.mem t'.mem := by
      rw [M.mem, U.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ lc
    refine ⟨A, M.rd.trans (U.rd.trans h.rd), M.wr.trans (U.wr.trans h.wr), ?_, ?_, fun r hr hne hsp => ?_,
      h.frame.trans (fr.mono fun r hr => ?_), h.words.frame hS hA fr fun r hr => ?_⟩
    · rw [M.gpr, U.other _ (by decide), h.esp]
    · rw [M.gpr, U.other _ (by decide), h.esi]
    · rw [M.gpr, U.other _ (saved_ne (Or.inl rfl) hr), h.saved r hr hne hsp]
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ (List.mem_singleton_self _)
    · simp only [List.mem_singleton] at hr; subst hr; exact A.lowS.symm
  · have hl := low_toNat A
    have hb := A.stackBound
    intro i hi
    rw [M.mem, U.gpr, U.mem]
    by_cases hij : i = j
    · subst hij; rw [Mem.readW_writeW_self32, h.words.get hd, hv]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact ha i (by omega_arith)

theorem arguments_ok {o s : State} {e : BitVec 32} {used keys scalars : Nat}
    (h : Fr o liveDs (liveF (ofState o) e used keys scalars) s) :
    WP isa (.block arguments) s fun t => Fr o liveDs (liveF (ofState o) e used keys scalars) t ∧
      ArgsAt o used 13 t.mem := by
  have hA : Aligned liveDs := by decide
  show WP isa (.block (pass xOff 0 ++ pass lenOff 1 ++ pass yOff 2 ++ pass lenOff 3 ++ pass domOff 4 ++
    pass dlenOff 5 ++ pass lenOff 6 ++ pass randOff 7 ++ pass lenOff 8 ++ pass scratchOff 9 ++
    pass slenOff 10 ++ pass ctxOff 11 ++ pass ctxLenOff 12 ++ [])) s _
  simp only [List.append_assoc]
  refine pass_ok (used := used) h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, xOff])
    (fun _ h => absurd h (Nat.not_lt_zero _)) fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, lenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, yOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, lenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, domOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, dlenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, lenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, randOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, lenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, scratchOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, slenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, ctxOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, ctxLenOff]) a
    fun t h a => WP.block_nil ⟨h, a⟩

end VG.Proof.Ffdh.X86.Cached.Search
