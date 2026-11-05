module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.Arm
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# Tables of the interface `Hmac` on ARMv7

As on x86-64 (`Proof/HmacTable/X86_64.lean`), with every hash function that
has HMAC on ARMv7, each with one implementation (`vars`: MD5, SHA-1,
SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256, the
functions PBKDF2's code calls, `Proof.Pbkdf2.Whole.Arm`): the table of a
hash function (`tableOf`, `VG_HMAC_<HASH>`) holds the addresses of HMAC's
`init` and `finalize` and of the streaming `update`, in the forms that take
their working space as an argument (`_scratch`), then its data
(`Spec.HmacTable.dataOf`), each word 32 bits wide; an indirect call of the
functions of every table (`fnsOf`) to one of them reaches it (`tabOK_of`),
when the functions of distinct names are at distinct addresses and those of
the same name have the same code (`Coh`). `held_tableOf` reads a table's
words, and `hashAt_tableOf` the hash function it names.
-/

@[expose] public section

namespace VG.Proof.HmacTable.Arm

open VG VG.Arm
open VG.Impl.Ecdsa.Rfc6979.Arm (Fns)
open VG.Proof.HashTable (pw_ne find_name)

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

open Proof.Pbkdf2.Whole.Arm in
def md5V : HVar := ⟨md5F, md5OKF, Spec.Mgf1.md5, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha1V : HVar := ⟨sha1F, sha1OKF, Spec.Mgf1.sha1, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha224V : HVar := ⟨sha224F, sha224OKF, Spec.Mgf1.sha224, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha256V : HVar := ⟨sha256F, sha256OKF, Spec.Mgf1.sha256, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha384V : HVar := ⟨sha384F, sha384OKF, Spec.Mgf1.sha384, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha512V : HVar := ⟨sha512F, sha512OKF, Spec.Mgf1.sha512, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha512_224V : HVar := ⟨sha512_224F, sha512_224OKF, Spec.Mgf1.sha512_224, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha512_256V : HVar := ⟨sha512_256F, sha512_256OKF, Spec.Mgf1.sha512_256, rfl, rfl, rfl⟩

/-- Every hash function with HMAC on ARMv7. -/
def vars : List HVar := [md5V, sha1V, sha224V, sha256V, sha384V, sha512V, sha512_224V, sha512_256V]

/-- The table of `w`'s HMAC, `VG_HMAC_<HASH>`. -/
def tableOf (w : HVar) : FnTable where
  name := s!"VG_HMAC_{w.G.rust.toUpper}"
  iface := Spec.HmacTable.iface
  fns := [w.F.hiN, w.F.H.updN, w.F.hfN]
  data := Spec.HmacTable.dataOf w.G

/-- The tables of `vs`. -/
def tables (vs : List HVar) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List HVar) : Fns :=
  ⟨vs.map fun w => (w.F.hiN, w.F.hiC), vs.map fun w => (w.F.H.updN, w.F.H.updC),
    vs.map fun w => (w.F.hfN, w.F.hfC)⟩

/-- The functions of `tables vs`. -/
def names (vs : List HVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The functions of the same name have the same code. -/
def Coh (vs : List HVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.F.hiN = w'.F.hiN → w.F.hiC = w'.F.hiC) ∧
    (w.F.H.updN = w'.F.H.updN → w.F.H.updC = w'.F.H.updC) ∧ (w.F.hfN = w'.F.hfN → w.F.hfC = w'.F.hfC)

instance (vs : List HVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

/-- The table's word at `p + o`. -/
abbrev tA (p : BitVec 32) (o : Nat) : Addr := State.addr (p + BitVec.ofNat 32 o)

/-- At `p` in `m`, the addresses `sy` gives `F`'s HMAC `init`, the streaming
`update` and HMAC's `finalize`. -/
def TabMem (F : Impl.Pbkdf2.Whole.Arm.Fns) (sy : String → BitVec 32) (p : BitVec 32) (m : Mem) : Prop :=
  m.readW (tA p 0) 32 = sy F.hiN ∧ m.readW (tA p 4) 32 = sy F.H.updN ∧ m.readW (tA p 8) 32 = sy F.hfN

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `F`'s HMAC functions reaches it. -/
structure TabOK (F : Impl.Pbkdf2.Whole.Arm.Fns) (f : Fns) (sy : String → BitVec 32) : Prop where
  i : f.init.find? (fun q => (sy q.1).setWidth 64 == (sy F.hiN).setWidth 64) = some (F.hiN, F.hiC)
  u : f.upd.find? (fun q => (sy q.1).setWidth 64 == (sy F.H.updN).setWidth 64) = some (F.H.updN, F.H.updC)
  f : f.fin.find? (fun q => (sy q.1).setWidth 64 == (sy F.hfN).setWidth 64) = some (F.hfN, F.hfC)

theorem mem_names {vs : List HVar} {w : HVar} (hw : w ∈ vs) :
    w.F.hiN ∈ names vs ∧ w.F.H.updN ∈ names vs ∧ w.F.hfN ∈ names vs := by
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
    FnTable.words isa s (tableOf w) = [(s.syms w.F.hiN).setWidth 64, (s.syms w.F.H.updN).setWidth 64,
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
    rw [tA, VG.Arm.addr_add (by omega)]
  have e : ∀ i (hi : i < 6), m.readW (tA p (4 * i)) 32 = _ := fun i hi => (a i hi).symm ▸ h i (by simp; omega)
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
  rw [show State.addr p + BitVec.ofNat 64 (32 / 8 * 3) = tA p 12 by rw [tA, VG.Arm.addr_add (by omega)], h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega)]
  exact w.idx

end VG.Proof.HmacTable.Arm
