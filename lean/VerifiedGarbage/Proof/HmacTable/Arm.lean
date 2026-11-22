module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.Arm
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
public import VerifiedGarbage.Proof.Hmac.Stream.Arm.CodeOk
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyInstances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeySha256
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Tables of the interface `Hmac` on ARMv7

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Reduce.lean`), with every hash function that
has HMAC on ARMv7, each with one implementation (`vars`: MD5, SHA-1,
SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256, the
functions PBKDF2's code calls, `Proof.Pbkdf2.Whole.Arm`): the table of a
hash function (`tableOf`, `VG_HMAC_<HASH>`) holds the addresses of HMAC's
`init` for a key of any length (`Fns.hmacInitAny`, with `W + S` words of
working space, `vg_hmac_<hash>_init_any_scratch`) and `finalize` and of the
streaming `update`, in the forms that take their working space as an
argument (`_scratch`), then its data
(`Spec.HmacTable.dataOf`), each word 32 bits wide; an indirect call of the
functions of every table (`fnsOf`) to one of them reaches it (`tabOK_of`),
when the functions of distinct names are at distinct addresses and those of
the same name have the same code (`Coh`). `held_tableOf` reads a table's
words, and `hashAt_tableOf` the hash function it names.

A function that calls the table's HMAC `init` for a key of any length, in
the frame of its stack argument, runs it as `any_frame` says, and two runs of
it with the same arguments leak the same trace (`any_rel`); the table's
`update` and `finalize` are called as PBKDF2's code calls them
(`Proof/Pbkdf2/Whole/Arm/Upd.lean`, `Calls.lean`). `put6w` and `symT` make
a table in memory, for the states that meet the contracts of the functions
taking one. Deterministic ECDSA (`Proof/Ecdsa/Rfc6979/Arm/`) and HKDF
(`Proof/Hkdf/Arm/`) call the tables.
-/


@[expose] public section

namespace VG.Proof.HmacTable.Arm

open VG VG.Arm
open VG.Impl.Ecdsa.Rfc6979.Arm (Fns)
open VG.Proof.HashTable (pw_ne find_name)

/-- What `HVar.scrub` states of the functions of the hash function `M`, from
what `M` states of its own code. -/
theorem fnsScrub {I : Spec.Hmac.Instance} {M : Impl.Pbkdf2.Md.Arm.Hash} (h : Proof.Hmac.Stream.Arm.MdOk M) :
    Arm.Scrub.CodeOk (Impl.Hmac.Stream.Arm.fnsOf I M).hmacInitAny 16 ∧
      Arm.Scrub.CodeOk (Impl.Hmac.Stream.Arm.fnsOf I M).H.updC 8 ∧
      Arm.Scrub.CodeOk (Impl.Hmac.Stream.Arm.fnsOf I M).hfC 8 :=
  ⟨⟨Nat.le_of_eq (h.hmacInitAny_stack I), h.hmacInitAny_noIcall I⟩, h.upd.mono (by decide), h.hmacFin_ok⟩

/-- A hash function with HMAC on ARMv7: the functions PBKDF2's code calls,
what is proven of them, and its place in `Spec.Mgf1.hashes`, whose HMAC is
theirs. -/
structure HVar where
  F : Impl.Pbkdf2.Whole.Arm.Fns
  ok : Proof.Pbkdf2.Whole.Arm.FnsOK F
  G : Spec.Mgf1.Hash
  idx : Spec.Mgf1.hashes[Spec.HashTable.index G]? = some G
  glen : G.len = F.H.D
  hmac : Spec.HmacTable.hmacOf G = some ok.hH.SH.H
  /-- What the cleanup of a function that calls them through the table needs
  of HMAC's `init` for a key of any length, the streaming `update` and HMAC's
  `finalize`: their frames use at most 16, 8 and 8 bytes, and they make no
  indirect call (`Arm.Scrub.CodeOk`), from what the hash function states of
  its own code (`Proof.Hmac.Stream.Arm.MdOk`). -/
  scrub : Arm.Scrub.CodeOk F.hmacInitAny 16 ∧ Arm.Scrub.CodeOk F.H.updC 8 ∧ Arm.Scrub.CodeOk F.hfC 8
  /-- HMAC's `init` for a key of any length, which the table holds, meets
  its contract with `W + S` words of working space (`Any.verified`). -/
  any : Proof.Pbkdf2.Whole.Arm.Sound F.hmacInitAny
    (Proof.Pbkdf2.Whole.Arm.Any.anyScratchContract ok.hH.SH (F.W + F.H.S))

open Proof.Pbkdf2.Whole.Arm in
def md5V : HVar :=
  ⟨md5F, md5OKF, Spec.Mgf1.md5, rfl, rfl, rfl, fnsScrub Proof.Hmac.Stream.Arm.md5_mdOk,
    .of_verified (Any.verified md5OKF Any.md5_anyChecks rfl rfl Any.md5_anySat)⟩
open Proof.Pbkdf2.Whole.Arm in
def sha1V : HVar :=
  ⟨sha1F, sha1OKF, Spec.Mgf1.sha1, rfl, rfl, rfl, fnsScrub Proof.Hmac.Stream.Arm.sha1_mdOk,
    .of_verified (Any.verified sha1OKF Any.sha1_anyChecks rfl rfl Any.sha1_anySat)⟩
open Proof.Pbkdf2.Whole.Arm in
def sha224V : HVar :=
  ⟨sha224F, sha224OKF, Spec.Mgf1.sha224, rfl, rfl, rfl, fnsScrub Proof.Hmac.Stream.Arm.sha224_mdOk,
    .of_verified (Any.verified sha224OKF Any.sha224_anyChecks rfl rfl Any.sha224_anySat)⟩
open Proof.Pbkdf2.Whole.Arm in
def sha256V : HVar :=
  ⟨sha256F, sha256OKF, Spec.Mgf1.sha256, rfl, rfl, rfl, fnsScrub Proof.Hmac.Stream.Arm.sha256_mdOk,
    .of_verified (Any.verified sha256OKF Any.sha256_anyChecks rfl rfl Any.sha256_anySat)⟩
open Proof.Pbkdf2.Whole.Arm in
def sha384V : HVar :=
  ⟨sha384F, sha384OKF, Spec.Mgf1.sha384, rfl, rfl, rfl, fnsScrub (Proof.Hmac.Stream.Arm.sha512_mdOk _ _ _),
    .of_verified (Any.verified sha384OKF Any.sha384_anyChecks rfl rfl Any.sha384_anySat)⟩
open Proof.Pbkdf2.Whole.Arm in
def sha512V : HVar :=
  ⟨sha512F, sha512OKF, Spec.Mgf1.sha512, rfl, rfl, rfl, fnsScrub (Proof.Hmac.Stream.Arm.sha512_mdOk _ _ _),
    .of_verified (Any.verified sha512OKF Any.sha512_anyChecks rfl rfl Any.sha512_anySat)⟩
open Proof.Pbkdf2.Whole.Arm in
def sha512_224V : HVar :=
  ⟨sha512_224F, sha512_224OKF, Spec.Mgf1.sha512_224, rfl, rfl, rfl, fnsScrub (Proof.Hmac.Stream.Arm.sha512_mdOk _ _ _),
    .of_verified (Any.verified sha512_224OKF Any.sha512_224_anyChecks rfl rfl Any.sha512_224_anySat)⟩
open Proof.Pbkdf2.Whole.Arm in
def sha512_256V : HVar :=
  ⟨sha512_256F, sha512_256OKF, Spec.Mgf1.sha512_256, rfl, rfl, rfl, fnsScrub (Proof.Hmac.Stream.Arm.sha512_mdOk _ _ _),
    .of_verified (Any.verified sha512_256OKF Any.sha512_256_anyChecks rfl rfl Any.sha512_256_anySat)⟩

/-- Every hash function with HMAC on ARMv7. -/
def vars : List HVar := [md5V, sha1V, sha224V, sha256V, sha384V, sha512V, sha512_224V, sha512_256V]

/-- The table of `w`'s HMAC, `VG_HMAC_<HASH>`. -/
def tableOf (w : HVar) : FnTable where
  name := s!"VG_HMAC_{w.G.rust.toUpper}"
  iface := Spec.HmacTable.iface
  fns := [w.F.hiAnyN, w.F.H.updN, w.F.hfN]
  data := Spec.HmacTable.dataOf w.G

/-- The tables of `vs`. -/
def tables (vs : List HVar) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List HVar) : Fns :=
  ⟨vs.map fun w => (w.F.hiAnyN, w.F.hmacInitAny), vs.map fun w => (w.F.H.updN, w.F.H.updC),
    vs.map fun w => (w.F.hfN, w.F.hfC)⟩

/-- The functions of `tables vs`. -/
def names (vs : List HVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The functions of the same name have the same code. -/
def Coh (vs : List HVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.F.hiAnyN = w'.F.hiAnyN → w.F.hmacInitAny = w'.F.hmacInitAny) ∧
    (w.F.H.updN = w'.F.H.updN → w.F.H.updC = w'.F.H.updC) ∧ (w.F.hfN = w'.F.hfN → w.F.hfC = w'.F.hfC)

instance (vs : List HVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

/-- The table's word at `p + o`. -/
abbrev tA (p : BitVec 32) (o : Nat) : Addr := State.addr (p + BitVec.ofNat 32 o)

/-- At `p` in `m`, the addresses `sy` gives `F`'s HMAC `init` for a key of
any length, the streaming `update` and HMAC's `finalize`. -/
def TabMem (F : Impl.Pbkdf2.Whole.Arm.Fns) (sy : String → BitVec 32) (p : BitVec 32) (m : Mem) : Prop :=
  m.readW (tA p 0) 32 = sy F.hiAnyN ∧ m.readW (tA p 4) 32 = sy F.H.updN ∧ m.readW (tA p 8) 32 = sy F.hfN

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `F`'s HMAC functions reaches it. -/
structure TabOK (F : Impl.Pbkdf2.Whole.Arm.Fns) (f : Fns) (sy : String → BitVec 32) : Prop where
  i : f.init.find? (fun q => (sy q.1).setWidth 64 == (sy F.hiAnyN).setWidth 64) = some (F.hiAnyN, F.hmacInitAny)
  u : f.upd.find? (fun q => (sy q.1).setWidth 64 == (sy F.H.updN).setWidth 64) = some (F.H.updN, F.H.updC)
  f : f.fin.find? (fun q => (sy q.1).setWidth 64 == (sy F.hfN).setWidth 64) = some (F.hfN, F.hfC)

theorem mem_names {vs : List HVar} {w : HVar} (hw : w ∈ vs) :
    w.F.hiAnyN ∈ names vs ∧ w.F.H.updN ∈ names vs ∧ w.F.hfN ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem tabOK_of {vs : List HVar} (hc : Coh vs) {sy : String → BitVec 32}
    (hd64 : (names vs).Pairwise fun f g => f ≠ g → (sy f).setWidth 64 ≠ (sy g).setWidth 64) {w : HVar}
    (hw : w ∈ vs) : TabOK w.F (fnsOf vs) sy := by
  have hn := mem_names hw
  refine ⟨find_name (sy := fun n => (sy n).setWidth 64) (List.mem_map_of_mem hw) ?_ ?_,
    find_name (sy := fun n => (sy n).setWidth 64) (List.mem_map_of_mem hw) ?_ ?_,
    find_name (sy := fun n => (sy n).setWidth 64) (List.mem_map_of_mem hw) ?_ ?_⟩
  all_goals intro q hq
  all_goals obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq
  · exact pw_ne hd64 _ (mem_names hw').1 _ hn.1
  · exact (hc w' hw' w hw).1
  · exact pw_ne hd64 _ (mem_names hw').2.1 _ hn.2.1
  · exact (hc w' hw' w hw).2.1
  · exact pw_ne hd64 _ (mem_names hw').2.2 _ hn.2.2
  · exact (hc w' hw' w hw).2.2

/-- HMAC's block size, as the table holds it. -/
theorem blockSize_eq (w : HVar) : Spec.HmacTable.blockSize w.G = w.F.H.B := by
  simp only [Spec.HmacTable.blockSize, w.hmac, Option.map_some, Option.getD_some]
  exact w.ok.hH.hB

/-- The words of the table of `w`. -/
theorem words_tableOf (s : State) (w : HVar) :
    FnTable.words isa s (tableOf w) = [(s.syms w.F.hiAnyN).setWidth 64, (s.syms w.F.H.updN).setWidth 64,
      (s.syms w.F.hfN).setWidth 64, BitVec.ofNat 64 (Spec.HashTable.index w.G), BitVec.ofNat 64 w.G.len,
      BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)] := rfl

/-- What the table of `w` at `p` holds: its functions' addresses, its index,
its digest length and HMAC's block size, 32 bits each. -/
theorem held_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 24 ≤ 2 ^ 32) {s : State} {w : HVar}
    (h : Abi.tableHeld 32 m (State.addr p) (FnTable.words isa s (tableOf w))) :
    TabMem w.F s.syms p m ∧ m.readW (tA p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G) ∧
      m.readW (tA p 16) 32 = BitVec.ofNat 32 w.F.H.D ∧ m.readW (tA p 20) 32 = BitVec.ofNat 32 w.F.H.B := by
  rw [words_tableOf, blockSize_eq] at h
  have a : ∀ i, i < 6 → tA p (4 * i) = State.addr p + BitVec.ofNat 64 (32 / 8 * i) := fun i hi => by
    rw [tA, VG.Arm.addr_add (by omega_using [hp, hi])]
  have e : ∀ i (hi : i < 6), m.readW (tA p (4 * i)) 32 = _ := fun i hi => (a i hi).symm ▸ h i (by simp; omega_using [hi])
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have := e 0 (by decide); simp only [Nat.mul_zero] at this; rw [this]; simp
  · have := e 1 (by decide); simp only [Nat.mul_one] at this; rw [this]; simp
  · have := e 2 (by decide); rw [show 4 * 2 = 8 by rfl] at this; rw [this]; simp
  · have := e 3 (by decide); rw [show 4 * 3 = 12 by rfl] at this; rw [this]; simp
  · have := e 4 (by decide); rw [show 4 * 4 = 16 by rfl] at this; rw [this, w.glen]; simp
  · have := e 5 (by decide); rw [show 4 * 5 = 20 by rfl] at this; rw [this]; simp

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 24 ≤ 2 ^ 32) {w : HVar}
    (h : m.readW (tA p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G)) :
    Spec.HmacTable.hashAt 32 m (State.addr p) = some w.G := by
  simp only [Spec.HmacTable.hashAt, Spec.HmacTable.fns]
  rw [show State.addr p + BitVec.ofNat 64 (32 / 8 * 3) = tA p 12 by rw [tA, VG.Arm.addr_add (by omega_using [hp])], h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega_using [this])]
  exact w.idx


open VG.Proof.Pbkdf2.Whole.Arm (After HiArgs stk fr1)

/-! ## HMAC's `init` for a key of any length, in a frame of `scratch`

As `HiArgs`, `hi_frame` and `hi_rel` are `init`'s for a key of at most a
block (`Proof/Pbkdf2/Whole/Arm/Calls.lean`), for the function the tables
hold, `initAny` (`Impl/Pbkdf2/Md/AnyKey/Arm.lean`), verified against
`anyScratchContract` with `W` words of working space: what the state before
the frame's push needs (`AnyArgs`: a key of any length, and the 32 bytes
below the stack pointer, the frame's 8 and the 24 that `initAny`'s contract
takes, apart from the buffers), what holds when it returns (`any_frame`),
and that two runs with the same arguments leak the same trace (`any_rel`).
It writes only the 24 bytes below the stack pointer (`After`), as its code's
frames use at most 16 (`armStack`). -/

section
open VG.Arm.FrameStack
open VG.Proof.Pbkdf2.Whole.Arm (Sound ReprOK frame2_ok frame2_rel p2_sub p2_arg0 p2_argAddr p2_bytes stk_repr)
open VG.Proof.Pbkdf2.Whole.Arm.Any (anyScratchContract)

/-- What a framed call of `initAny` needs of the state before its push: the
states at `inn` and `out` in `r0` and `r1`, the `kl` bytes of key at `k` in
`r2` and `r3`, and `8 W` bytes of working space at `sc` in `r12`; the
regions the callee may read and write; that they are disjoint as it needs,
and from the 32 bytes below the stack pointer; and that none of them wraps
around. -/
structure AnyArgs (S : Spec.Hmac.StreamingHash) (W : Nat) (s : State) (inn out k sc : BitVec 32) (kl : Nat) : Prop where
  r0 : s.gpr .r0 = inn
  r1 : s.gpr .r1 = out
  r2 : s.gpr .r2 = k
  r3 : s.gpr .r3 = BitVec.ofNat 32 kl
  r12 : s.gpr .r12 = sc
  kl32 : kl < 2 ^ 32
  sp : 32 ≤ s.sp.toNat
  cr : Covers [⟨State.addr k, kl⟩] (s.rd ++ s.wr)
  cw : Covers [⟨State.addr inn, S.stateBytes⟩, ⟨State.addr out, S.stateBytes⟩, ⟨State.addr sc, W * 8⟩] s.wr
  i_o : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr out, S.stateBytes⟩
  i_k : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr k, kl⟩
  i_s : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr sc, W * 8⟩
  o_k : Region.Disjoint ⟨State.addr out, S.stateBytes⟩ ⟨State.addr k, kl⟩
  o_s : Region.Disjoint ⟨State.addr out, S.stateBytes⟩ ⟨State.addr sc, W * 8⟩
  k_s : Region.Disjoint ⟨State.addr k, kl⟩ ⟨State.addr sc, W * 8⟩
  b_i : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 32, 32⟩ ⟨State.addr inn, S.stateBytes⟩
  b_o : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 32, 32⟩ ⟨State.addr out, S.stateBytes⟩
  b_k : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 32, 32⟩ ⟨State.addr k, kl⟩
  b_s : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 32, 32⟩ ⟨State.addr sc, W * 8⟩
  ni : inn.toNat + S.stateBytes ≤ 2 ^ 32
  no : out.toNat + S.stateBytes ≤ 2 ^ 32
  nk : k.toNat + kl ≤ 2 ^ 32
  nsc : sc.toNat + W * 8 ≤ 2 ^ 32

/-- The 24 bytes below the stack pointer are among the 32. -/
theorem stk_sub32 (s : State) : Region.Sub (stk s) ⟨State.addr s.sp - BitVec.ofNat 64 32, 32⟩ :=
  Offset.sub_below _ (a := 24) (b := 32) (by decide) (by decide)

namespace AnyArgs
variable {S : Spec.Hmac.StreamingHash} {W : Nat} {s : State} {inn out k sc : BitVec 32} {kl : Nat}
  (h : AnyArgs S W s inn out k sc kl)
include h

/-- `initAny`'s precondition on entry. -/
theorem pre : (anyScratchContract S W).pre
    ((pushed fr1 s).callEntry.withRegions (HiArgs.rd s.sp k kl) (HiArgs.wr S W inn out sc)) := by
  have e := h.sp
  have h8 : (s.sp - BitVec.ofNat 32 8).toNat = s.sp.toNat - 8 := sub_toNat' (by omega_using [e])
  have a8 : State.addr (s.sp - BitVec.ofNat 32 8) = State.addr s.sp - BitVec.ofNat 64 8 := addr_sub' (by omega_using [e])
  -- The frame's first word, the stack argument, and the 24 bytes below it, among the 32.
  have sA4 : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8), 4⟩ ⟨State.addr s.sp - BitVec.ofNat 64 32, 32⟩ := by
    rw [a8]; exact Offset.sub_below _ (a := 8) (b := 32) (by decide) (by decide)
  have e24 : State.addr (s.sp - BitVec.ofNat 32 8) - 24 = State.addr s.sp - BitVec.ofNat 64 32 := by
    rw [a8, BitVec.sub_sub]; rfl
  have sR : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8) - 24, 24⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 32, 32⟩ := by
    rw [e24]; exact Region.sub_prefix (by decide)
  have cA : Region.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 8) - 24, 24⟩
      ⟨State.addr (s.sp - BitVec.ofNat 32 8), 4⟩ := by
    rw [e24, a8]
    exact VG.Proof.Pbkdf2.Whole.Arm.bdisj _ 32 (a := 32) (b := 8) (by decide) (by decide) (by omega_using [])
      (by decide) (by decide)
  sig_pre [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]
  simp only [h.r0, h.r1, h.r2, h.r3, p2_arg0 (s := s) (by omega_using [e]), p2_argAddr, h.r12, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h.kl32]
  exact ⟨by rw [h8]; omega_using [e], by rw [h8]; have := s.sp.isLt; omega_using [], rfl, rfl, h.i_o, h.i_k, h.i_s,
    (h.b_i.sub_left sA4).symm, h.o_k, h.o_s, (h.b_o.sub_left sA4).symm, h.k_s, (h.b_s.sub_left sA4).symm,
    h.b_i.sub_left sR, h.b_o.sub_left sR, h.b_k.sub_left sR, h.b_s.sub_left sR, cA,
    h.ni, h.no, h.nk, h.nsc⟩

/-- The `HiArgs` of the same registers and regions, but the key's length. -/
theorem cov : Covers (HiArgs.rd s.sp k kl ++ HiArgs.wr S W inn out sc) ((pushed fr1 s).rd ++ (pushed fr1 s).wr) := by
  intro a n ⟨q, hq, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rw [pushed_rd, pushed_wr]
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, List.mem_singleton_self _, hc⟩
    rcases List.mem_append.mp hq' with hq' | hq'
    · exact ⟨q', List.mem_append_left _ hq', hc'⟩
    · exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩
  · refine ⟨_, List.mem_append_right _ List.mem_cons_self, ?_⟩
    show Region.Contains ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ a n
    simp only [Region.Contains] at hc ⊢; omega_using [hc]
  all_goals
    obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
    exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩

theorem covW : Covers (HiArgs.wr S W inn out sc) (pushed fr1 s).wr := by
  intro a n hi
  obtain ⟨q', hq', hc'⟩ := h.cw a n hi
  exact ⟨q', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hq', hc'⟩

end AnyArgs

/-- A framed call of `initAny`: its states are those of the block key of
the key, of any length. -/
theorem any_frame {S : Spec.Hmac.StreamingHash} {W : Nat} {n : String} {c : Prog isa} (hR : ReprOK S)
    (hSn : S.stateBytes ≤ 2 ^ 64) (hv : Sound c (anyScratchContract S W)) (hst : armStack c ≤ 16)
    {s : State} {inn out k sc : BitVec 32} {kl : Nat} (h : AnyArgs S W s inn out k sc kl) {Q : State → Prop}
    (hQ : ∀ s', After s (HiArgs.wr S W inn out sc) s' →
      S.Repr s'.mem (State.addr inn) (Spec.Hmac.xorPad (Spec.Hmac.blockKey S.H (Spec.Sha256.bytesAt s.mem (State.addr k) kl)) Spec.Hmac.ipad) →
      S.Repr s'.mem (State.addr out) (Spec.Hmac.xorPad (Spec.Hmac.blockKey S.H (Spec.Sha256.bytesAt s.mem (State.addr k) kl)) Spec.Hmac.opad) → Q s') :
    WP isa (.frame (.push fr1) (.call n c) (.pop .r12 8)) s Q := by
  have h24 : 24 ≤ s.sp.toNat := by have := h.sp; omega_using [this]
  refine frame2_ok rfl (by decide) hv.ok hst h24 h.pre h.cov h.covW fun s₂ mL uL hfl a post => ?_
  sig_post [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at post
  simp only [h.r0, h.r1, h.r2, h.r3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.kl32] at post
  have ek : Spec.Sha256.bytesAt (storeWords s.mem (s.sp - BitVec.ofNat 32 8) [s.gpr .r12, s.gpr .lr]) (BitVec.setWidth 64 k) kl =
      Spec.Sha256.bytesAt s.mem (State.addr k) kl :=
    p2_bytes (ra := .r12) (rb := .lr) h24 (h.b_k.sub_left (stk_sub32 s)) (by have := h.kl32; omega_using [this])
  rw [ek] at post
  exact hQ _ a (stk_repr hR hSn hfl (h.b_i.sub_left (stk_sub32 s)) post.1)
    (stk_repr hR hSn hfl (h.b_o.sub_left (stk_sub32 s)) post.2)

/-- Two framed calls of `initAny` with the same arguments, from the same
stack pointer, leak the same trace. -/
theorem any_rel {S : Spec.Hmac.StreamingHash} {W : Nat} {n : String} {c : Prog isa}
    (hv : Sound c (anyScratchContract S W)) {P : State → State → Prop}
    {sp inn out k sc : BitVec 32} {kl : Nat}
    (h : ∀ s s', P s s' → AnyArgs S W s inn out k sc kl ∧ AnyArgs S W s' inn out k sc kl ∧
      s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push fr1) (.call n c) (.pop .r12 8)) fun _ _ => True := by
  refine frame2_rel rfl hv.ok hv.ct (HiArgs.rd sp k kl) (HiArgs.wr S W inn out sc) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c := a.pre; have c' := a'.pre
  rw [e] at c; rw [e'] at c'
  have v := a.cov; have v' := a'.cov
  rw [e] at v; rw [e'] at v'
  refine ⟨e.trans e'.symm, c, c', ?_, v, a.covW, v', a'.covW⟩
  sig_pub [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]
  simp only [a.r0, a'.r0, a.r1, a'.r1, a.r2, a'.r2, a.r3, a'.r3, p2_arg0 (s := s) (by have := a.sp; omega_using [this]),
    p2_arg0 (s := s') (by have := a'.sp; omega_using [this]), a.r12, a'.r12, e, e', and_self]

end

/-! ## A table in memory, for states meeting the contracts -/

open VG.Proof.HashTable (symsOf32 symsOf32_distinct)

/-- A word read apart from a word written. -/
theorem readW_sepW {m : Mem} {a b : Addr} {w : Nat} {v : BitVec 32} (h : a.toNat + w / 8 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat)
    (ha : a.toNat + w / 8 ≤ 2 ^ 64) (hb : b.toNat + 4 ≤ 2 ^ 64) (hw : w / 8 < 2 ^ 64) :
    (m.writeW b v).readW a w = m.readW a w :=
  Mem.readW_writeW_sep (fun x h1 h2 => by
    simp only [Nat.reduceDiv] at h1 h2
    rcases h with h | h <;> bv_omega) hw

/-- Six words at `p`. -/
def put6w (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 32) : Mem :=
  (((((m.writeW (p + BitVec.ofNat 64 (4 * 0)) w₀).writeW (p + BitVec.ofNat 64 (4 * 1)) w₁).writeW
    (p + BitVec.ofNat 64 (4 * 2)) w₂).writeW (p + BitVec.ofNat 64 (4 * 3)) w₃).writeW
    (p + BitVec.ofNat 64 (4 * 4)) w₄).writeW (p + BitVec.ofNat 64 (4 * 5)) w₅

/-- The table `put6w` writes at `0x300000`, of the low halves of `ws`. -/
theorem put6w_held {m : Mem} {ws : List (BitVec 64)} (hl : ws.length = 6) :
    Abi.tableHeld 32 (put6w m 0x300000 ((ws.getD 0 0).setWidth 32) ((ws.getD 1 0).setWidth 32)
      ((ws.getD 2 0).setWidth 32) ((ws.getD 3 0).setWidth 32) ((ws.getD 4 0).setWidth 32)
      ((ws.getD 5 0).setWidth 32)) 0x300000 ws := by
  intro i hi
  rw [hl] at hi
  simp only [put6w, Nat.reduceDiv]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32,
      Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32, Mem.readW_writeW_self32] <;> decide
  · rw [Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32,
      Proof.HashTable.readW_sep32, Mem.readW_writeW_self32] <;> decide
  · rw [Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32,
      Mem.readW_writeW_self32] <;> decide
  · rw [Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32, Mem.readW_writeW_self32] <;> decide
  · rw [Proof.HashTable.readW_sep32, Mem.readW_writeW_self32] <;> decide
  · rw [Mem.readW_writeW_self32]

/-- Below `0x300000`, `put6w` at `0x300000` changes no word. -/
theorem put6w_below {m : Mem} {a : Addr} {w : Nat} (hw : w / 8 ≤ 8) (ha : a.toNat + w / 8 ≤ 0x300000)
    (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 32) : (put6w m 0x300000 w₀ w₁ w₂ w₃ w₄ w₅).readW a w = m.readW a w := by
  have h0 : (0x300000 + BitVec.ofNat 64 (4 * 0) : Addr).toNat = 0x300000 := by decide
  have h1 : (0x300000 + BitVec.ofNat 64 (4 * 1) : Addr).toNat = 0x300004 := by decide
  have h2 : (0x300000 + BitVec.ofNat 64 (4 * 2) : Addr).toNat = 0x300008 := by decide
  have h3 : (0x300000 + BitVec.ofNat 64 (4 * 3) : Addr).toNat = 0x30000C := by decide
  have h4 : (0x300000 + BitVec.ofNat 64 (4 * 4) : Addr).toNat = 0x300010 := by decide
  have h5 : (0x300000 + BitVec.ofNat 64 (4 * 5) : Addr).toNat = 0x300014 := by decide
  simp only [put6w]
  rw [readW_sepW, readW_sepW, readW_sepW, readW_sepW, readW_sepW, readW_sepW]
  all_goals first | (simp only [h0, h1, h2, h3, h4, h5]; omega_arith) | omega_arith

/-- The stack arguments, at `0x9000`. -/
def put2w (m : Mem) (w₀ w₁ : BitVec 32) : Mem := (m.writeW 0x9000 w₀).writeW 0x9004 w₁

/-- Above the stack arguments, `put2w` changes no word. -/
theorem put2w_above {m : Mem} {a : Addr} {w : Nat} (hw : w / 8 ≤ 8) (ha : 0x9008 ≤ a.toNat)
    (ha' : a.toNat + w / 8 ≤ 2 ^ 64) (w₀ w₁ : BitVec 32) : (put2w m w₀ w₁).readW a w = m.readW a w := by
  have e₀ : (0x9000 : Addr).toNat = 0x9000 := by decide
  have e₄ : (0x9004 : Addr).toNat = 0x9004 := by decide
  simp only [put2w]
  rw [readW_sepW (.inr (by rw [e₄]; omega_using [ha])) ha' (by decide) (by omega_using [hw]),
    readW_sepW (.inr (by rw [e₀]; omega_using [ha])) ha' (by decide) (by omega_using [hw])]

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List HVar) (n : String) : BitVec 32 :=
  if n ∈ names vs then symsOf32 (names vs) n else 0x100000

theorem symT_distinct {vs : List HVar} (hl : (names vs).length < 2 ^ 24) :
    (names vs).Pairwise fun f g => f ≠ g → (symT vs f).setWidth 64 ≠ (symT vs g).setWidth 64 :=
  (symsOf32_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne

end VG.Proof.HmacTable.Arm
