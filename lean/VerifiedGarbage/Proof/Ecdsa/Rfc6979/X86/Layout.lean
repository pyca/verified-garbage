module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86
import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyInstances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeySha1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeySha256
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Md5.Md
import VerifiedGarbage.Proof.Sha1.Md
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.Hmac.Generic.Common

/-! ### `HmacTable.X86`, which this module and modules that import it used -/

section

/-!
# Tables of the interface `Hmac` on x86 (32-bit)

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Reduce.lean`), with the hash functions as
PBKDF2 on x86 has them (`Proof.Pbkdf2.Whole.X86.FnsOK`), each with the
suffix and the CPU features of its variant (`HVar`): MD5, SHA-1 with each of
its backends, SHA-224 and SHA-256 with each of theirs, and the SHA-512
family (`vars`). The table of a variant (`tableOf`,
`VG_HMAC_<HASH><SUFFIX>`) holds the addresses of HMAC's `init` for a key of
any length (`hmacInitAny`, `_init_any_scratch`, verified for each variant:
`HVar.any`) and `finalize` and of the streaming `update`, in the forms that
take their working space as an argument (`_scratch`), then its data
(`Spec.HmacTable.dataOf`), each word 32 bits wide; an indirect call of the
functions of every variant (`fnsOf`) to one of them reaches it (`tabOK_of`),
when the functions of distinct names are at distinct addresses and the
variants' functions of the same name have the same code (`Coh`).
`held_tableOf` reads a table's words, and `hashAt_tableOf` the hash
function it names.
-/

@[expose] public section

namespace VG.Proof.HmacTable.X86

open VG VG.X86
open VG.Impl.Ecdsa.Rfc6979.X86 (Fns)
open VG.Proof.Pbkdf2.Whole.X86 (FnsOK Sound)
open VG.Proof.HashTable (pw_ne find_name)

/-- A variant of a hash function with HMAC: the functions PBKDF2's code
calls, verified, the hash function of `Spec.Mgf1.hashes` it computes, the
suffix of its functions' names and the CPU features it needs, and HMAC's
`init` for a key of any length, which the table holds, verified with
`W + S` words of working space, keeping `esp` and using at most 76 bytes of
stack. -/
structure HVar where
  F : Impl.Pbkdf2.Whole.X86.Fns
  ok : FnsOK F
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.hH.SH.H.hash x
  glen : G.len = F.H.D
  /-- Its digests have `F.H.D` bytes. -/
  hlen : ∀ x, (ok.hH.SH.H.hash x).length = F.H.D
  suffix : String
  features : List String
  idx : Spec.Mgf1.hashes[Spec.HashTable.index G]? = some G
  any : Sound F.hmacInitAny (Proof.Pbkdf2.Whole.X86.Any.anyScratchContract ok.hH.SH (F.W + F.H.S))
  anySp : NoSp F.hmacInitAny
  anySU : stackUse F.hmacInitAny ≤ 76

open Proof.Pbkdf2.Whole.X86 in
def md5V : HVar := ⟨md5F, md5OKF, Spec.Mgf1.md5, fun _ => rfl, rfl, fun x => by
  show (Spec.Md5.hash x).length = 16; rw [Proof.Md5.hash_eq]; exact Proof.Md5.md.digest_length _, "", [], rfl,
  Sound.of_verified (Any.verified md5OKF Any.md5_anyChecks rfl rfl Any.md5_anySat),
  NoSp.of_all Any.md5_anyNoEsp, Any.hmacInitAny_stack md5OKF⟩
open Proof.Pbkdf2.Whole.X86 in
def sha1V (b : Proof.Sha1.X86.Variants.Backend) : HVar :=
  ⟨b.F, sha1OKF b, Spec.Mgf1.sha1, fun _ => rfl, rfl, fun x => by
    show (Spec.Sha1.hash x).length = 20; rw [Proof.Sha1.hash_eq]; exact Proof.Sha1.md.digest_length _,
    b.stream.suffix, b.features, rfl,
    Sound.of_verified (Any.verified (sha1OKF b) (Any.anyChecks_of_shape (F := b.F) Any.sha1Shape_anyChecks) rfl rfl
      Any.sha1_anySat),
    NoSp.of_all (Any.sha1_anyNoEsp b), Any.hmacInitAny_stack (sha1OKF b)⟩
open Proof.Pbkdf2.Whole.X86 in
def sha224V (b : Proof.Sha256.X86.Variants.Backend) : HVar :=
  ⟨b.F224, sha224OKF b, Spec.Mgf1.sha224, fun _ => rfl, rfl, fun x => by
    show (Spec.Sha256.sha224 x).length = 28
    simp [Spec.Sha256.sha224, Spec.Sha256.finalHash, Spec.Sha256.wordBytes, List.length_flatMap, List.map_const'],
    b.stream.suffix, b.features, rfl,
    Sound.of_verified (Any.verified (sha224OKF b) (Any.anyChecks_of_shape (F := b.F224) Any.sha224Shape_anyChecks) rfl rfl
      Any.sha224_anySat),
    NoSp.of_all (Any.sha224_anyNoEsp b), Any.hmacInitAny_stack (sha224OKF b)⟩
open Proof.Pbkdf2.Whole.X86 in
def sha256V (b : Proof.Sha256.X86.Variants.Backend) : HVar :=
  ⟨b.F, sha256OKF b, Spec.Mgf1.sha256, fun _ => rfl, rfl, fun x => by
    show (Spec.Sha256.hash x).length = 32; rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _,
    b.stream.suffix, b.features, rfl,
    Sound.of_verified (Any.verified (sha256OKF b) (Any.anyChecks_of_shape (F := b.F) Any.sha256Shape_anyChecks) rfl rfl
      Any.sha256_anySat),
    NoSp.of_all (Any.sha256_anyNoEsp b), Any.hmacInitAny_stack (sha256OKF b)⟩
open Proof.Pbkdf2.Whole.X86 in
def sha384V : HVar := ⟨sha384F, sha384OKF, Spec.Mgf1.sha384, fun _ => rfl, rfl, fun x => by
  show ((Spec.Sha512.finalHash Spec.Sha512.H0_384 x).take 48).length = 48
  rw [List.length_take, Proof.Hmac.Generic.Common.finalHash_length]; rfl, "", [], rfl,
  Sound.of_verified (Any.verified sha384OKF Any.sha384_anyChecks rfl rfl Any.sha384_anySat),
  NoSp.of_all Any.sha384_anyNoEsp, Any.hmacInitAny_stack sha384OKF⟩
open Proof.Pbkdf2.Whole.X86 in
def sha512V : HVar := ⟨sha512F, sha512OKF, Spec.Mgf1.sha512, fun _ => rfl, rfl, fun x => by
  show (Spec.Sha512.finalHash Spec.Sha512.H0_512 x).length = 64
  rw [Proof.Hmac.Generic.Common.finalHash_length], "", [], rfl,
  Sound.of_verified (Any.verified sha512OKF Any.sha512_anyChecks rfl rfl Any.sha512_anySat),
  NoSp.of_all Any.sha512_anyNoEsp, Any.hmacInitAny_stack sha512OKF⟩
open Proof.Pbkdf2.Whole.X86 in
def sha512_224V : HVar := ⟨sha512_224F, sha512_224OKF, Spec.Mgf1.sha512_224, fun _ => rfl, rfl, fun x => by
  show ((Spec.Sha512.finalHash Spec.Sha512.H0_512_224 x).take 28).length = 28
  rw [List.length_take, Proof.Hmac.Generic.Common.finalHash_length]; rfl, "", [], rfl,
  Sound.of_verified (Any.verified sha512_224OKF Any.sha512_224_anyChecks rfl rfl Any.sha512_224_anySat),
  NoSp.of_all Any.sha512_224_anyNoEsp, Any.hmacInitAny_stack sha512_224OKF⟩
open Proof.Pbkdf2.Whole.X86 in
def sha512_256V : HVar := ⟨sha512_256F, sha512_256OKF, Spec.Mgf1.sha512_256, fun _ => rfl, rfl, fun x => by
  show ((Spec.Sha512.finalHash Spec.Sha512.H0_512_256 x).take 32).length = 32
  rw [List.length_take, Proof.Hmac.Generic.Common.finalHash_length]; rfl, "", [], rfl,
  Sound.of_verified (Any.verified sha512_256OKF Any.sha512_256_anyChecks rfl rfl Any.sha512_256_anySat),
  NoSp.of_all Any.sha512_256_anyNoEsp, Any.hmacInitAny_stack sha512_256OKF⟩

/-- Every variant: MD5's, SHA-1's with the backends `vs1`, SHA-224's and
SHA-256's with `vs256`, and the SHA-512 family's. -/
def vars (vs1 : List Proof.Sha1.X86.Variants.Backend) (vs256 : List Proof.Sha256.X86.Variants.Backend) :
    List HVar :=
  md5V :: (vs1.map sha1V ++ vs256.map sha224V ++ vs256.map sha256V ++
    [sha384V, sha512V, sha512_224V, sha512_256V])

/-- The table of `w`'s HMAC, `VG_HMAC_<HASH><SUFFIX>`. -/
def tableOf (w : HVar) : FnTable where
  name := s!"VG_HMAC_{w.G.rust.toUpper}{w.suffix.toUpper}"
  iface := Spec.HmacTable.iface
  fns := [w.F.hiAnyN, w.F.H.updN, w.F.hfN]
  data := Spec.HmacTable.dataOf w.G

/-- The tables of the variants `vs`. -/
def tables (vs : List HVar) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List HVar) : Fns :=
  ⟨vs.map fun w => (w.F.hiAnyN, w.F.hmacInitAny), vs.map fun w => (w.F.H.updN, w.F.H.updC),
    vs.map fun w => (w.F.hfN, w.F.hfC)⟩

/-- The functions of `tables vs`. -/
def names (vs : List HVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The variants' functions of the same name have the same code. -/
def Coh (vs : List HVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.F.hiAnyN = w'.F.hiAnyN → w.F.hmacInitAny = w'.F.hmacInitAny) ∧
    (w.F.H.updN = w'.F.H.updN → w.F.H.updC = w'.F.H.updC) ∧ (w.F.hfN = w'.F.hfN → w.F.hfC = w'.F.hfC)

instance (vs : List HVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `F`'s HMAC functions reaches it. -/
structure TabOK (F : Impl.Pbkdf2.Whole.X86.Fns) (f : Fns) (sy : String → BitVec 32) : Prop where
  i : f.init.find? (fun q => (sy q.1).setWidth 64 == (sy F.hiAnyN).setWidth 64) = some (F.hiAnyN, F.hmacInitAny)
  u : f.upd.find? (fun q => (sy q.1).setWidth 64 == (sy F.H.updN).setWidth 64) = some (F.H.updN, F.H.updC)
  f : f.fin.find? (fun q => (sy q.1).setWidth 64 == (sy F.hfN).setWidth 64) = some (F.hfN, F.hfC)

/-- At `p` in `m`, the addresses `sy` gives `F`'s HMAC `init` for a key of any length, the streaming
`update` and HMAC's `finalize`. -/
def TabMem (F : Impl.Pbkdf2.Whole.X86.Fns) (sy : String → BitVec 32) (p : BitVec 32) (m : Mem) : Prop :=
  m.readW (VG.X86.addr p 0) 32 = sy F.hiAnyN ∧ m.readW (VG.X86.addr p 4) 32 = sy F.H.updN ∧
    m.readW (VG.X86.addr p 8) 32 = sy F.hfN

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

/-- The words of the table of `w`. -/
theorem words_tableOf (s : State) (w : HVar) :
    FnTable.words isa s (tableOf w) = [(s.syms w.F.hiAnyN).setWidth 64, (s.syms w.F.H.updN).setWidth 64,
      (s.syms w.F.hfN).setWidth 64, BitVec.ofNat 64 (Spec.HashTable.index w.G), BitVec.ofNat 64 w.G.len,
      BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)] := rfl

/-- What the table of `w` at `p` holds: its functions' addresses, its index,
its digest length and HMAC's block size, 32 bits each. -/
theorem held_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 24 ≤ 2 ^ 32) {s : State} {w : HVar}
    (h : Abi.tableHeld 32 m (p.setWidth 64) (FnTable.words isa s (tableOf w))) :
    TabMem w.F s.syms p m ∧
      m.readW (VG.X86.addr p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G) ∧
      m.readW (VG.X86.addr p 16) 32 = BitVec.ofNat 32 w.F.H.D ∧
      m.readW (VG.X86.addr p 20) 32 = BitVec.ofNat 32 (Spec.HmacTable.blockSize w.G) := by
  rw [words_tableOf] at h
  have a : ∀ i, i < 6 → VG.X86.addr p (4 * i) = p.setWidth 64 + BitVec.ofNat 64 (32 / 8 * i) := fun i hi => by
    rw [addr_eq (by omega_using [hp, hi])]
  have e : ∀ i (hi : i < 6), m.readW (VG.X86.addr p (4 * i)) 32 = _ := fun i hi => (a i hi).symm ▸ h i (by simp; omega_using [hi])
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have := e 0 (by decide); simp only [Nat.mul_zero] at this; rw [this]; simp
  · have := e 1 (by decide); simp only [Nat.mul_one] at this; rw [this]; simp
  · have := e 2 (by decide); rw [show 4 * 2 = 8 by rfl] at this; rw [this]; simp
  · have := e 3 (by decide); rw [show 4 * 3 = 12 by rfl] at this; rw [this]; simp
  · have := e 4 (by decide); rw [show 4 * 4 = 16 by rfl] at this; rw [this, w.glen]; simp
  · have := e 5 (by decide); rw [show 4 * 5 = 20 by rfl] at this; rw [this]; simp

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 24 ≤ 2 ^ 32) {w : HVar}
    (h : m.readW (VG.X86.addr p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G)) :
    Spec.HmacTable.hashAt 32 m (p.setWidth 64) = some w.G := by
  simp only [Spec.HmacTable.hashAt, Spec.HmacTable.fns]
  rw [show p.setWidth 64 + BitVec.ofNat 64 (32 / 8 * 3) = VG.X86.addr p 12 by rw [addr_eq (by omega_using [hp])], h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega_using [this])]
  exact w.idx

end VG.Proof.HmacTable.X86

end

end

/-!
# Deterministic ECDSA on x86 (32-bit): where everything is

The function's arguments (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`digest_len`, `scratch`, the table `hmac` of 24 bytes, and `esp` on entry
`E`) and the 612 bytes of stack below the return address, from
`B - 24 = E - 612` up (`Lay dn`): the 100 bytes the calls use (`CALLS`: a
frame of at most six arguments, the return address, and the 48 bytes HMAC's
functions use below it, or the 76 that HMAC's `init` for a key of any length
uses), then the frame of 512 bytes, from `B + 76` (`esp` in the body, `F`;
every place in the stack is at an offset of `B`): `K` and `V` (64 bytes
each), our caller's `ebx`, `esi`, `edi` and
`ebp`, `D` and `B`, and above them (`HIGH`) the length of `T`, the number of
candidates left, `h`, `X`, `core`'s digest and `T`. Above it, the return
address and our arguments. `Ctx` is what holds between the frame's entry
(`entry`, `tabDB`) and its release: the permissions, `esp`, the saved
registers, `D` and `B`, our arguments, immutable table contents and public
symbol addresses, what the table holds and which functions an indirect call
of it reaches, and that memory changed only in `out`, `scratch` and the
stack. Code that writes only regions apart from the saved registers, `D`
and `B` (`Safe`) keeps it (`Ctx.keep`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp
open VG.Impl.Ecdsa.Rfc6979.X86 (Fns)
open VG.Proof.HmacTable.X86 (TabOK TabMem)

/-- The arguments (`out`, `d`, `digest`, `digest_len`, `scratch`, `hmac`)
and `esp` on entry, for a digest of `dn` bytes and scalars of `q`, the
tables of constants `core` reads and their statics' addresses, the hash
function's functions whose table `hmac` is, the functions an indirect call
of a table's functions may reach, and the addresses of the table's
functions. -/
structure Lay (dn : Nat) where
  a0 : BitVec 32
  a1 : BitVec 32
  a2 : BitVec 32
  a3 : BitVec 32
  sc : BitVec 32
  tb : BitVec 32
  E : BitVec 32
  q : Nat
  cs : List (String × List (BitVec 64))
  sy : String → BitVec 32
  H : Impl.Pbkdf2.Whole.X86.Fns
  f : Fns
  fa : String → BitVec 32

namespace Lay

variable {dn : Nat} (L : Lay dn)

/-- Argument `i` of the layout. -/
def a : Nat → BitVec 32
  | 0 => L.a0
  | 1 => L.a1
  | 2 => L.a2
  | 3 => L.a3
  | 4 => L.sc
  | _ => L.tb

abbrev out : Addr := L.a0.setWidth 64
abbrev d : Addr := L.a1.setWidth 64
abbrev dg : Addr := L.a2.setWidth 64
abbrev scr : Addr := L.sc.setWidth 64
abbrev tab : Addr := L.tb.setWidth 64
/-- `esp` in the frame's body. -/
abbrev F : BitVec 32 := L.E - BitVec.ofNat 32 512
/-- The base of the offsets in the stack, 24 bytes above the lowest byte of
the stack used. -/
abbrev B : Addr := (L.E - BitVec.ofNat 32 588).setWidth 64

abbrev TBLs : List Region := Abi.constRegions (fun n => (L.sy n).setWidth 64) L.cs

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The table of HMAC. -/
abbrev TAB : Region := ⟨L.tab, 24⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B - BitVec.ofNat 64 24, 612⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 76, 512⟩
/-- The return address, and our arguments. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 588, 4⟩
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 592, 24⟩
/-- The stack below the saved registers: the calls', and `K` and `V`. -/
abbrev LOW : Region := ⟨L.B - BitVec.ofNat 64 24, 228⟩
/-- The stack below the frame, which the calls use. -/
abbrev CALLS : Region := ⟨L.B - BitVec.ofNat 64 24, 100⟩
/-- The frame above `D` and `B`. -/
abbrev HIGH : Region := ⟨L.B + BitVec.ofNat 64 228, 360⟩

/-- What the contract says of where the buffers and the stack are (`d` and
`digest`, which are only read, may overlap). -/
structure Ok : Prop where
  od : L.OUT.Disjoint L.D
  og : L.OUT.Disjoint L.DG
  oc : L.OUT.Disjoint L.SCR
  dc : L.D.Disjoint L.SCR
  gc : L.DG.Disjoint L.SCR
  ao : L.ARGS.Disjoint L.OUT
  ac : L.ARGS.Disjoint L.SCR
  ro : L.RET.Disjoint L.OUT
  rc : L.RET.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  kd : L.STK.Disjoint L.D
  kg : L.STK.Disjoint L.DG
  kc : L.STK.Disjoint L.SCR
  no : L.a0.toNat + 2 * L.q ≤ 2 ^ 32
  nd : L.a1.toNat + L.q ≤ 2 ^ 32
  ng : L.a2.toNat + dn ≤ 2 ^ 32
  nc : L.sc.toNat + 8192 ≤ 2 ^ 32
  e612 : 612 ≤ L.E.toNat
  e28 : L.E.toNat + 28 ≤ 2 ^ 32
  tbl : ∀ T ∈ L.TBLs, T.base.toNat + T.len ≤ 2 ^ 32 ∧
    T.Disjoint L.OUT ∧ T.Disjoint L.SCR ∧ T.Disjoint L.STK
  /-- The table does not wrap around, and is apart from what the code writes. -/
  nt : L.tb.toNat + 24 ≤ 2 ^ 32
  to : L.TAB.Disjoint L.OUT
  tc : L.TAB.Disjoint L.SCR
  tk : L.TAB.Disjoint L.STK
  ta : L.TAB.Disjoint L.ARGS

/-! ## Regions at offsets of `B`, and the 24 bytes below it -/

/-- `B + d`, at an offset of the lowest byte of the stack used. -/
theorem off24 (p : Addr) (d : Nat) : p + BitVec.ofNat 64 d = p - BitVec.ofNat 64 24 + BitVec.ofNat 64 (24 + d) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- A range at an offset of `p` within one from 24 bytes below `p`. -/
theorem sub24 (p : Addr) {d n k : Nat} (h : 24 + d + n ≤ k) :
    Region.Sub ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p - BitVec.ofNat 64 24, k⟩ := by
  rw [off24 p d]; exact Offset.sub_base _ (by omega_arith)

theorem sub24' (p : Addr) {n k : Nat} (h : 24 + n ≤ k) : Region.Sub ⟨p, n⟩ ⟨p - BitVec.ofNat 64 24, k⟩ := by
  have := sub24 p (d := 0) (n := n) (k := k) (by omega_arith)
  rwa [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

/-- A range from 24 bytes below `p` and one at an offset of `p` above it. -/
theorem disj24 (p : Addr) {k d n : Nat} (h₁ : k ≤ 24 + d) (h₂ : 24 + d + n ≤ 2 ^ 64) :
    Region.Disjoint ⟨p - BitVec.ofNat 64 24, k⟩ ⟨p + BitVec.ofNat 64 d, n⟩ := by
  rw [off24 p d]; exact Offset.base_disjoint _ h₁ h₂

variable {L}

theorem sub_STK {d n : Nat} (h : d + n ≤ 588) : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.STK :=
  sub24 _ (by omega_arith)

theorem sub_STK' {n : Nat} (h : n ≤ 588) : Region.Sub ⟨L.B, n⟩ L.STK := sub24' _ (by omega_arith)

theorem sub_LOW {d n : Nat} (h : d + n ≤ 204) : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.LOW :=
  sub24 _ (by omega_arith)

theorem sub_LOW' {n : Nat} (h : n ≤ 204) : Region.Sub ⟨L.B, n⟩ L.LOW := sub24' _ (by omega_arith)

/-- A range of the stack above the saved registers' place is apart from `LOW`. -/
theorem LOW_disj {d n : Nat} (h₁ : 204 ≤ d) (h₂ : 24 + d + n ≤ 2 ^ 64) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.LOW := (disj24 _ (by omega_arith) h₂).symm

theorem CALLS_LOW : Region.Sub L.CALLS L.LOW := Region.sub_prefix (by omega_arith)

theorem CALLS_STK : Region.Sub L.CALLS L.STK := Region.sub_prefix (by omega_arith)

/-- The 76 bytes from `B`, which every call but that of HMAC's `init` for a
key of any length uses, are among the calls'. -/
theorem sub_CALLS {n : Nat} (h : n ≤ 76) : Region.Sub ⟨L.B, n⟩ L.CALLS := sub24' _ (by omega_arith)

/-- The calls' stack is apart from the frame and what is above it. -/
theorem CALLS_disj {d n : Nat} (h₁ : 76 ≤ d) (h₂ : d + n ≤ 616) :
    Region.Disjoint L.CALLS ⟨L.B + BitVec.ofNat 64 d, n⟩ := disj24 _ (by omega_arith) (by omega_arith)

end Lay

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

theorem e588 (h : L.Ok) : 588 ≤ L.E.toNat := by have := h.e612; omega_arith

theorem B_eq (h : L.Ok) : L.B = L.E.setWidth 64 - BitVec.ofNat 64 588 := Taint.sub_setWidth h.e588

theorem BN (h : L.Ok) : L.B.toNat = L.E.toNat - 588 := by
  have := h.e588
  simp only [Lay.B, BitVec.toNat_setWidth]
  rw [sub_toNat (by omega_arith)]; have := L.E.isLt; omega_arith

theorem nB (h : L.Ok) : L.B.toNat + 616 ≤ 2 ^ 64 := by
  have := h.e588; have := h.e28; rw [h.BN]; omega_arith

/-- `[F + o]`, for `o` in the frame or the arguments above it. -/
theorem addrF (h : L.Ok) {o : Nat} (ho : o < 540) : addr L.F o = L.B + BitVec.ofNat 64 (76 + o) := by
  have := h.e588; have := h.e28
  have hF : L.F.toNat = L.E.toNat - 512 := sub_toNat (by omega_arith)
  rw [addr_eq (by rw [hF]; omega_arith), Lay.F, Taint.sub_setWidth (by omega_arith), h.B_eq,
    Offset.sub_ofNat_eq _ (show 512 ≤ 588 by omega_arith), show 588 - 512 = 76 by omega_arith, Offset.add_add]

theorem F64 (h : L.Ok) : L.F.setWidth 64 = L.B + BitVec.ofNat 64 76 := by
  have e := h.addrF (o := 0) (by omega_arith)
  rwa [addr, BitVec.add_zero] at e

/-- The frame's 76 bytes below `F`, which the calls use. -/
theorem below_F (_h : L.Ok) : below L.F 76 = ⟨L.B, 76⟩ := by
  show (⟨(L.F - BitVec.ofNat 32 76).setWidth 64, 76⟩ : Region) = _
  rw [Lay.F, show L.E - BitVec.ofNat 32 512 - BitVec.ofNat 32 76 = L.E - BitVec.ofNat 32 588 by
    rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat]]

/-- The frame's 100 bytes below `F`, which HMAC's `init` for a key of any
length uses: the calls'. -/
theorem below_F100 (h : L.Ok) : below L.F 100 = L.CALLS := by
  have := h.e612
  show (⟨(L.F - BitVec.ofNat 32 100).setWidth 64, 100⟩ : Region) = ⟨L.B - BitVec.ofNat 64 24, 100⟩
  rw [Lay.F, show L.E - BitVec.ofNat 32 512 - BitVec.ofNat 32 100 = L.E - BitVec.ofNat 32 612 by
    rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat], Taint.sub_setWidth (by omega_arith), h.B_eq, Offset.sub_sub_ofNat]

theorem FN (h : L.Ok) : L.F.toNat = L.E.toNat - 512 := sub_toNat (by have := h.e588; omega_arith)

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 588) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Lay.sub_STK h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_scr0 (h : L.Ok) {d n k : Nat} (h₁ : d + n ≤ 588) (h₂ : k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr, k⟩ :=
  (h.kc.sub_left (Lay.sub_STK h₁)).sub_right (Region.sub_prefix h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 588) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Lay.sub_STK h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 588) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Lay.sub_STK h₁)

/-- The calls' stack, and a range of `scratch`. -/
theorem calls_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint L.CALLS ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left Lay.CALLS_STK).sub_right (Offset.sub_base _ h₂)

theorem calls_scr0 (h : L.Ok) {k : Nat} (h₂ : k ≤ 8192) : Region.Disjoint L.CALLS ⟨L.scr, k⟩ :=
  (h.kc.sub_left Lay.CALLS_STK).sub_right (Region.sub_prefix h₂)

end Lay.Ok

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A region of the frame. -/
theorem within_fr (B : Addr) {d n : Nat} (h₁ : 76 ≤ d) (h₂ : d + n ≤ 588) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 76, 512⟩ :=
  ⟨d - 76, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega_arith⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below the saved registers or above `B`. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW ∨ Region.Sub r L.HIGH

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 204) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inl (Lay.sub_LOW h)))

/-- The calls' stack. -/
theorem safe_calls {dn : Nat} (L : Lay dn) {r : Region} (h : Region.Sub r L.CALLS) : Safe L r :=
  .inr (.inr (.inl (fun x hx => Lay.CALLS_LOW x (h x hx))))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

theorem safe_high {dn : Nat} (L : Lay dn) {d n : Nat} (h₁ : 228 ≤ d) (h₂ : d + n ≤ 588) :
    Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr (Offset.sub _ h₁ (by omega_arith))))

theorem Safe.of_sub {dn : Nat} {L : Lay dn} {r r' : Region} (hs : Safe L r') (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr (.inl fun x hx => hs x (h x hx))), .inr (.inr (.inr fun x hx => hs x (h x hx)))]

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

/-- Two adjacent ranges apart from `r`: so is their union. -/
theorem _root_.VG.Proof.Ecdsa.Rfc6979.X86.disjoint_join {p : Addr} {a b : Nat} {r : Region}
    (h₁ : Region.Disjoint ⟨p, a⟩ r)
    (h₂ : Region.Disjoint ⟨p + BitVec.ofNat 64 a, b⟩ r) : Region.Disjoint ⟨p, a + b⟩ r := by
  intro x hx
  simp only [Region.Contains] at hx
  rcases Nat.lt_or_ge (x - p).toNat a with hl | hl
  · exact h₁ x (by simp only [Region.Contains]; omega_arith)
  · refine h₂ x ?_
    have ha : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
    simp only [Region.Contains]
    rw [Offset.sub_add_eq, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ha]; exact hl), ha]
    omega_arith

/-- The saved registers, `D` and `B` are apart from every safe region. -/
theorem saved_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 204, 24⟩ r := by
  have nB := h.nB
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega_arith)).sub_right hs
  · exact (h.stk_SCR (by omega_arith)).sub_right hs
  · exact (Lay.disj24 _ (by omega_arith) (by omega_arith)).symm.sub_right hs
  · exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

/-- The return address and our arguments are apart from every safe region. -/
theorem top_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 588, 28⟩ r := by
  have nB := h.nB
  have j : ∀ {r : Region}, L.RET.Disjoint r → L.ARGS.Disjoint r →
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 588, 28⟩ r := fun h₂ h₃ =>
    disjoint_join (a := 4) (b := 24) h₂ (by rw [Offset.add_add]; exact h₃)
  rcases hs with hs | hs | hs | hs
  · exact (j h.ro h.ao).sub_right hs
  · exact (j h.rc h.ac).sub_right hs
  · exact (Lay.disj24 _ (by omega_arith) (by omega_arith)).symm.sub_right hs
  · exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

end Lay.Ok

/-! ## Between the frame's entry and release -/

/-- The state between the frame's entry and release: `g` are the registers
on entry, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG, L.TAB] ++ L.TBLs
  wr : t.wr = [L.FR, L.OUT, L.SCR, L.ARGS]
  esp : t.gpr .esp = L.F
  saved : ∀ p ∈ Impl.Ecdsa.Rfc6979.X86.saved, t.mem.readW (L.B + BitVec.ofNat 64 (76 + p.2)) 32 = g p.1
  pArg : ∀ i < 6, t.mem.readW (L.B + BitVec.ofNat 64 (592 + 4 * i)) 32 = L.a i
  /-- `D` and `B`, above the saved registers. -/
  pDl : t.mem.readW (L.B + BitVec.ofNat 64 220) 32 = BitVec.ofNat 32 L.H.H.D
  pBl : t.mem.readW (L.B + BitVec.ofNat 64 224) 32 = BitVec.ofNat 32 L.H.H.B
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sy : ∀ c ∈ L.cs, t.syms c.1 = L.sy c.1
  held : Abi.constsHeld m₀ (fun n => (L.sy n).setWidth 64) L.cs
  tabOk : TabOK L.H L.f t.syms
  tabMem : TabMem L.H t.syms L.tb m₀
  fsy : ∀ n ∈ [L.H.hiAnyN, L.H.H.updN, L.H.hfN], t.syms n = L.fa n

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B - BitVec.ofNat 64 24) (by omega_arith) a (h a ha)⟩
  · exact ⟨L.STK, by simp, fun a ha => Lay.sub_STK (L := L) (d := 228) (n := 360) (by omega_arith) a (h a ha)⟩

theorem saved_off : ∀ p ∈ Impl.Ecdsa.Rfc6979.X86.saved, 128 ≤ p.2 ∧ p.2 + 4 ≤ 144 := by decide

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions and `esp`, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .esp = t.gpr .esp) {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r)
    (hsy : t'.syms = t.syms) : Ctx L g m₀ t' := by
  have nB := hL.nB
  have keep : ∀ d, 204 ≤ d → d + 4 ≤ 228 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 32 = t.mem.readW (L.B + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 204, 24⟩)
      (Offset.contains _ h₁ (by omega_arith) (by omega_arith)) (fun r hr => hL.saved_safe (hs r hr)) (by decide)
  have keepA : ∀ d, 592 ≤ d → d + 4 ≤ 616 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 32 = t.mem.readW (L.B + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 588, 28⟩)
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)) (fun r hr => hL.top_safe (hs r hr))
      (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.esp, fun p hp => by
    have := saved_off p hp
    rw [keep _ (by omega_arith) (by omega_arith)]
    exact hc.saved p hp, fun i hi => (keepA _ (by omega_arith) (by omega_arith)).trans (hc.pArg i hi),
    (keep 220 (by omega_arith) (by omega_arith)).trans hc.pDl, (keep 224 (by omega_arith) (by omega_arith)).trans hc.pBl,
    hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame),
    fun c hc' => by rw [hsy]; exact hc.sy c hc', hc.held, by rw [hsy]; exact hc.tabOk,
    by rw [hsy]; exact hc.tabMem, by rw [hsy]; exact hc.fsy⟩

/-- Code that writes only registers but `esp`. -/
theorem regs (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.gpr .esp = t.gpr .esp) (hsy : t'.syms = t.syms) : Ctx L g m₀ t' :=
  hc.keep hL hrd hwr hsp (ws := []) (by rw [hm]; exact Frame.refl _ _) (by simp) hsy

/-- A byte of `d`, as on entry. -/
theorem d_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.q) :
    t.mem (L.d + BitVec.ofNat 64 i) = m₀ (L.d + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.D) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.od.symm
    · exact hL.dc
    · exact hL.kd.symm) (by show L.q ≤ 2 ^ 64; have := hL.nd; omega_arith) hi

/-- A byte of `digest`, as on entry. -/
theorem dg_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < dn) :
    t.mem (L.dg + BitVec.ofNat 64 i) = m₀ (L.dg + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.DG) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.og.symm
    · exact hL.gc
    · exact hL.kg.symm) (by show dn ≤ 2 ^ 64; have := hL.ng; omega_arith) hi

/-- The table's words, as on entry. -/
theorem tabWord (hL : L.Ok) (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 4 ≤ 24) :
    t.mem.readW (addr L.tb o) 32 = m₀.readW (addr L.tb o) 32 := by
  rw [addr_eq (by have := hL.nt; omega_arith)]
  exact hc.frame.readW (r := L.TAB) (Offset.contains_base _ ho (by have := hL.nt; omega_arith)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.to
    · exact hL.tc
    · exact hL.tk) (by decide)

theorem inFr (hc : Ctx L g m₀ t) {d : Nat} (h₁ : 76 ≤ d) (h₂ : d + 4 ≤ 588) (hL : L.Ok) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 4 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by have := hL.nB; omega_arith)⟩

theorem inFrW (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 76 ≤ d) (h₂ : d + n ≤ 588) (hL : L.Ok) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by have := hL.nB; omega_arith)⟩

theorem inArgs (hc : Ctx L g m₀ t) {i : Nat} (hi : i < 6) (hL : L.Ok) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 (592 + 4 * i)) 4 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ (by omega_arith) (by omega_arith) (by have := hL.nB; omega_arith)⟩

theorem inScr (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inScrW (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inTab (hL : L.Ok) (hc : Ctx L g m₀ t) {o : Nat} (h : o + 4 ≤ 24) :
    InRegions (t.rd ++ t.wr) (addr L.tb o) 4 :=
  ⟨L.TAB, by rw [hc.rd, hc.wr]; simp, by
    rw [addr_eq (by have := hL.nt; omega_arith)]
    exact Offset.contains_base _ h (by have := hL.nt; omega_arith)⟩

theorem inD (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ L.q) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.d + BitVec.ofNat 64 o) n :=
  ⟨L.D, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inDg (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ dn) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.dg + BitVec.ofNat 64 o) n :=
  ⟨L.DG, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

/-- Regions within the buffers and the frame are permitted. -/
theorem covers (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within r R) : Covers rs (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hR ⊢; rcases hR with h | h | h | h | h <;> simp [h], hw⟩

theorem coversW (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.FR, L.OUT, L.SCR], Within r R) : Covers rs t.wr :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    exact ⟨R, by rw [hc.wr]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢; rcases hR with h | h | h <;> simp [h], hw⟩

end Ctx

/-! ## The frame's entry -/

/-- What the contract says of the table, on entry: it holds `H`'s HMAC
functions, which an indirect call of `f`'s reaches, then its digest length
and HMAC's block size. -/
def tabFacts (H : Impl.Pbkdf2.Whole.X86.Fns) (f : Fns) (s : State) : Prop :=
  TabOK H f s.syms ∧ TabMem H s.syms (arg s 5) s.mem ∧
    s.mem.readW (addr (arg s 5) 16) 32 = BitVec.ofNat 32 H.H.D ∧
    s.mem.readW (addr (arg s 5) 20) 32 = BitVec.ofNat 32 H.H.B

/-- The layout of a call from `s`, with a digest of `dn` bytes, scalars of
`q`, the tables `cs` (the statics' addresses, public, of those tables only),
and the hash function `H`'s HMAC through the table, whose functions an
indirect call reaches among `f`'s. -/
def lay (dn q : Nat) (cs : List (String × List (BitVec 64))) (H : Impl.Pbkdf2.Whole.X86.Fns) (f : Fns)
    (s : State) : Lay dn :=
  ⟨arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, arg s 5, s.gpr .esp, q, cs,
    fun n => if n ∈ cs.map Prod.fst then s.syms n else 0, H, f,
    fun n => if n ∈ [H.hiAnyN, H.H.updN, H.hfN] then s.syms n else 0⟩

section
variable {dn q : Nat} {cs : List (String × List (BitVec 64))} {H : Impl.Pbkdf2.Whole.X86.Fns} {f : Fns}

theorem lay_sy (s : State) {c : String × List (BitVec 64)} (hc : c ∈ cs) :
    (lay dn q cs H f s).sy c.1 = s.syms c.1 :=
  ite_eq_left (List.mem_map.mpr ⟨c, hc, rfl⟩)

theorem lay_tbls (s : State) :
    (lay dn q cs H f s).TBLs = Abi.constRegions (fun n => (s.syms n).setWidth 64) cs := by
  apply List.map_congr_left
  intro c hc
  show (⟨((lay dn q cs H f s).sy c.1).setWidth 64, _⟩ : Region) = _
  rw [lay_sy s (show c ∈ cs from hc)]

theorem lay_a (s : State) : ∀ i < 6, (lay dn q cs H f s).a i = arg s i
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl

/-- The address of our argument `i`. -/
theorem lay_argAddr {s : State} (e588 : 588 ≤ (s.gpr .esp).toNat) (e28 : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32)
    {i : Nat} (hi : i < 6) : argAddr s i = (lay dn q cs H f s).B + BitVec.ofNat 64 (592 + 4 * i) := by
  have hB : (lay dn q cs H f s).B = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588 := Taint.sub_setWidth e588
  rw [hB]
  show addr (s.gpr .esp) (4 + 4 * i) = _
  rw [addr_eq (by omega_arith), show 592 + 4 * i = 588 + (4 + 4 * i) by omega_arith,
    ← Offset.add_add ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588) 588 (4 + 4 * i), BitVec.sub_add_cancel]

/-- Our arguments' slots. -/
theorem lay_ARGS {s : State} (e588 : 588 ≤ (s.gpr .esp).toNat) (e28 : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32) :
    (lay dn q cs H f s).ARGS = ⟨argAddr s 0, 24⟩ := by
  rw [lay_argAddr e588 e28 (by omega_arith)]

end

theorem lay_ok {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance}
    {H : Impl.Pbkdf2.Whole.X86.Fns} {f : Fns} {ns : List String} {s : State}
    (h : (rfcX86 cs I 612 (tabFacts H f) ns).pre s) : (lay I.hashLen I.ecdsa.curve.len cs H f s).Ok := by
  obtain ⟨e612, e28, -, -, od, og, oc, dc, gc, ao, ac, ro, rc, ko, kd, kg, kc, no, nd, ng, nc, ht, nt, tout, tsc,
    targ, -, tstk, -⟩ := h
  have e588 : 588 ≤ (s.gpr .esp).toNat := by omega_arith
  have hB : (lay I.hashLen I.ecdsa.curve.len cs H f s).B = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588 :=
    Taint.sub_setWidth e588
  have eR : (lay I.hashLen I.ecdsa.curve.len cs H f s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
    show (⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 588, 4⟩ : Region) = _
    rw [hB, BitVec.sub_add_cancel]
  have eA := lay_ARGS (dn := I.hashLen) (q := I.ecdsa.curve.len) (cs := cs) (H := H) (f := f) e588 e28
  have eK : (lay I.hashLen I.ecdsa.curve.len cs H f s).STK =
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 612, 612⟩ := by
    show (⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B - BitVec.ofNat 64 24, 612⟩ : Region) = _
    rw [hB, Offset.sub_sub_ofNat]
  refine ⟨od, og, oc, dc, gc, eA ▸ ao, eA ▸ ac, eR ▸ ro, eR ▸ rc, eK ▸ ko, eK ▸ kd, eK ▸ kg, eK ▸ kc,
    no, nd, ng, nc, e612, e28, ?_, nt, tout, tsc, eK ▸ tstk, eA ▸ targ⟩
  intro T hT
  rw [lay_tbls] at hT
  have hh := ht.2 T hT
  exact ⟨hh.1, hh.2 _ (by simp [Lay.OUT, Lay.out, lay]), hh.2 _ (by simp [Lay.SCR, Lay.scr, lay]),
    by rw [eK]; exact hh.2 _ (by simp)⟩

/-- The state after the frame's allocation. -/
abbrev entered (s : State) : State := allocState 512 s

theorem entered_esp (dn q : Nat) (cs : List (String × List (BitVec 64))) (H : Impl.Pbkdf2.Whole.X86.Fns)
    (f : Fns) (s : State) : (entered s).gpr .esp = (lay dn q cs H f s).F := by
  simp only [entered, allocState_esp]; rfl

theorem entered_wr {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance}
    {H : Impl.Pbkdf2.Whole.X86.Fns} {f : Fns} {ns : List String} {s : State}
    (h : (rfcX86 cs I 612 (tabFacts H f) ns).pre s) :
    (entered s).wr = (lay I.hashLen I.ecdsa.curve.len cs H f s).FR :: s.wr := by
  simp only [entered, allocState_wr]
  congr 1
  show (⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).F.setWidth 64, 512⟩ : Region) = _
  rw [(lay_ok h).F64]

/-- The release of the frame. -/
def released (s₂ : State) : State :=
  { s₂.setReg .esp (s₂.gpr .esp + BitVec.ofNat 32 512) with wr := s₂.wr.tail }

/-- The frame: its body, which never writes `esp`, runs from `entered s`,
and the frame's release leads to `released s₂`, of which the postcondition
may rely on nothing the frame's bytes hold, nor on the unknowns (as
`WP.frameAlloc`'s). -/
theorem WP.alloc {body : Prog isa} {s : State} {Q : State → Prop}
    (hn : 512 ≤ (s.gpr .esp).toNat) (hsp : NoSp body)
    (hb : WP isa body (entered s) fun s₂ => ∀ m u,
      Frame [below (s.gpr .esp) 512] s₂.mem m → Q { released s₂ with mem := m, unknowns := u }) :
    WP isa (.frame (.alloc 512) body (.free 512)) s Q := by
  obtain ⟨t, s₂, he', hq⟩ := hb
  obtain ⟨-, hw⟩ := Exec.rdwr he'
  have hp := Exec.gpr hsp he'
  have hpush : isa.push (.alloc 512) s = some (entered s) := by
    simp only [isa, push]
    exact ite_eq_left ⟨by omega_arith, by omega_arith, by decide, hn⟩
  have hpop : isa.pop (.free 512) (entered s) s₂ = some { released s₂ with
      mem := lose s₂.mem ((s₂.gpr .esp).setWidth 64) 512 s₂.unknowns
      unknowns := fun n => s₂.unknowns (n + 512 / 2) } := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by omega_arith, by omega_arith, by decide, hp, hw, rfl⟩
  have e : (s₂.gpr .esp).setWidth 64 = (below (s.gpr .esp) 512).base := by
    rw [hp]; simp [entered, allocState, State.setReg]
  exact ⟨_, _, Exec.frame hpush he' hpop, hq _ _ (by rw [e]; exact lose_frame _ _ _ _)⟩

end VG.Proof.Ecdsa.Rfc6979.X86
