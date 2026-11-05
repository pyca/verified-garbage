module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Hashes
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Tables of the interface `Hmac` on PPC64LE

As on x86-64 (`Proof/HmacTable/X86_64.lean`), for the hash functions with
HMAC on PPC64LE, MD5, SHA-1 and the SHA-2 family, one implementation of each
(`vars`): the table of a hash function (`tableOf`, `VG_HMAC_<HASH>`) holds
the addresses of HMAC's `init` and `finalize` and of the streaming `update`,
in the forms that take their working space as an argument (`_scratch`, in
`r7`), then its data (`Spec.HmacTable.dataOf`: the hash function's index in
`Mgf1.hashes`, its digest length and HMAC's block size); the tables of a
list of them (`tables`); and the functions an indirect call of each of a
table's functions may reach (`fnsOf`).

A function's proof runs the code of whichever of these the table holds
(`TabOK`): the first function of `fnsOf vs` at the address called, which is
the table's function of that name (`tabOK_of`), when the functions of
distinct names are at distinct addresses (as `Abi.withTables` says) and the
functions of the same name have the same code (`Coh`, which the registration
checks). `held_tableOf` reads a table's words, and `hashAt_tableOf` the hash
function it names.
-/

@[expose] public section

namespace VG.Proof.HmacTable.PPC64LE

open VG VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.RsaOaep.PPC64LE (Fns)
open VG.Proof.RsaOaep.PPC64LE (Link)
open VG.Proof.HashTable (pw_ne find_name)

/-- A hash function's streaming functions (`H`, with what HMAC's and MGF1's
proofs need of them, `l`), its place in `Spec.Mgf1.hashes`, and its HMAC
`init` and `finalize` with their working space as an argument, verified
against the shared contracts of HMAC's instance `I` with 96 bytes of stack. -/
structure HVar where
  H : Hash
  l : Link H
  idx : Spec.Mgf1.hashes[Spec.HashTable.index l.G]? = some l.G
  I : Spec.Hmac.Instance
  hIS : I.S = l.ok.SH
  initV : Verified PPC64LE.target H.init (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi 96)
  finV : Verified PPC64LE.target H.finalize (Proof.Hmac.Instance.finalizeScratchContract I PPC64LE.abi 96)

namespace HVar

variable (w : HVar)

/-- HMAC's `init` with its working space as an argument. -/
def initN : String := w.H.hmacInitN

/-- HMAC's `finalize` with its working space as an argument. -/
def finN : String := s!"vg_hmac_{w.I.rust}_finalize_scratch"

end HVar

open Proof.Hmac.Stream.PPC64LE in
def md5V : HVar :=
  ⟨_, Proof.RsaOaep.PPC64LE.md5L, rfl, Spec.Hmac.md5I, rfl, Md5.initScratch, Md5.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha1V : HVar :=
  ⟨_, Proof.RsaOaep.PPC64LE.sha1L, rfl, Spec.Hmac.sha1I, rfl, Sha1.initScratch, Sha1.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha224V : HVar :=
  ⟨_, Proof.RsaOaep.PPC64LE.sha224L, rfl, Spec.Hmac.sha224I, rfl, Sha224.initScratch, Sha224.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha256V : HVar :=
  ⟨_, Proof.RsaOaep.PPC64LE.sha256L, rfl, Spec.Hmac.sha256I, rfl, Sha256.initScratch, Sha256.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha384V : HVar :=
  ⟨_, Proof.RsaOaep.PPC64LE.sha384L, rfl, Spec.Hmac.sha384I, rfl, Sha384.initScratch, Sha384.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha512V : HVar :=
  ⟨_, Proof.RsaOaep.PPC64LE.sha512L, rfl, Spec.Hmac.sha512I, rfl, Sha512.initScratch, Sha512.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha512_224V : HVar :=
  ⟨_, Proof.RsaOaep.PPC64LE.sha512_224L, rfl, Spec.Hmac.sha512_224I, rfl, Sha512_224.initScratch,
    Sha512_224.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha512_256V : HVar :=
  ⟨_, Proof.RsaOaep.PPC64LE.sha512_256L, rfl, Spec.Hmac.sha512_256I, rfl, Sha512_256.initScratch,
    Sha512_256.finalizeScratch⟩

/-- Every hash function with HMAC on PPC64LE. -/
def vars : List HVar := [md5V, sha1V, sha224V, sha256V, sha384V, sha512V, sha512_224V, sha512_256V]

/-- The table of `w`'s HMAC, `VG_HMAC_<HASH>`. -/
def tableOf (w : HVar) : FnTable where
  name := s!"VG_HMAC_{w.l.G.rust.toUpper}"
  iface := Spec.HmacTable.iface
  fns := [w.initN, w.H.updN, w.finN]
  data := Spec.HmacTable.dataOf w.l.G

/-- The tables of `vs`. -/
def tables (vs : List HVar) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List HVar) : Fns :=
  ⟨vs.map fun w => (w.initN, w.H.init), vs.map fun w => (w.H.updN, w.H.updC),
    vs.map fun w => (w.finN, w.H.finalize)⟩

/-- The functions of `tables vs`. -/
def names (vs : List HVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The functions of the same name have the same code. -/
def Coh (vs : List HVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.initN = w'.initN → w.H.init = w'.H.init) ∧
    (w.H.updN = w'.H.updN → w.H.updC = w'.H.updC) ∧ (w.finN = w'.finN → w.H.finalize = w'.H.finalize)

instance (vs : List HVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `w`'s HMAC functions reaches it. -/
structure TabOK (w : HVar) (f : Fns) (sy : String → Addr) : Prop where
  i : f.init.find? (fun q => sy q.1 == sy w.initN) = some (w.initN, w.H.init)
  u : f.upd.find? (fun q => sy q.1 == sy w.H.updN) = some (w.H.updN, w.H.updC)
  f : f.fin.find? (fun q => sy q.1 == sy w.finN) = some (w.finN, w.H.finalize)

/-- At `p` in `m`, the addresses `sy` gives `w`'s HMAC `init`, the streaming
`update` and HMAC's `finalize`. -/
def TabMem (w : HVar) (sy : String → Addr) (p : Addr) (m : Mem) : Prop :=
  m.readW (p + BitVec.ofNat 64 0) 64 = sy w.initN ∧ m.readW (p + BitVec.ofNat 64 8) 64 = sy w.H.updN ∧
    m.readW (p + BitVec.ofNat 64 16) 64 = sy w.finN

theorem mem_names {vs : List HVar} {w : HVar} (hw : w ∈ vs) :
    w.initN ∈ names vs ∧ w.H.updN ∈ names vs ∧ w.finN ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem tabOK_of {vs : List HVar} (hc : Coh vs) {sy : String → Addr}
    (hd : (names vs).Pairwise fun f g => f ≠ g → sy f ≠ sy g) {w : HVar} (hw : w ∈ vs) :
    TabOK w (fnsOf vs) sy := by
  have hn := mem_names hw
  refine ⟨find_name (List.mem_map_of_mem hw) ?_ ?_, find_name (List.mem_map_of_mem hw) ?_ ?_,
    find_name (List.mem_map_of_mem hw) ?_ ?_⟩
  all_goals intro q hq
  all_goals obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq
  · exact pw_ne hd _ (mem_names hw').1 _ hn.1
  · exact (hc w' hw' w hw).1
  · exact pw_ne hd _ (mem_names hw').2.1 _ hn.2.1
  · exact (hc w' hw' w hw).2.1
  · exact pw_ne hd _ (mem_names hw').2.2 _ hn.2.2
  · exact (hc w' hw' w hw).2.2

/-- The words of the table of `w`. -/
theorem words_tableOf (s : State) (w : HVar) :
    FnTable.words isa s (tableOf w) = [s.syms w.initN, s.syms w.H.updN, s.syms w.finN,
      BitVec.ofNat 64 (Spec.HashTable.index w.l.G), BitVec.ofNat 64 w.l.G.len,
      BitVec.ofNat 64 (Spec.HmacTable.blockSize w.l.G)] := rfl

/-- What the table of `w` at `p` holds: its functions' addresses, its index,
its digest length and HMAC's block size. -/
theorem held_tableOf {m : Mem} {p : Addr} {s : State} {w : HVar}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (tableOf w))) :
    TabMem w s.syms p m ∧
      m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.l.G) ∧
      m.readW (p + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
      m.readW (p + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (Spec.HmacTable.blockSize w.l.G) := by
  rw [words_tableOf] at h
  refine ⟨⟨h 0 (by simp), h 1 (by simp), h 2 (by simp)⟩, h 3 (by simp), ?_, h 5 (by simp)⟩
  exact (h 4 (by simp)).trans (by rw [w.l.len]; rfl)

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : Addr} {w : HVar}
    (h : m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.l.G)) :
    Spec.HmacTable.hashAt 64 m p = some w.l.G := by
  simp only [Spec.HmacTable.hashAt, Spec.HmacTable.fns]
  rw [show p + BitVec.ofNat 64 (64 / 8 * 3) = p + BitVec.ofNat 64 24 from rfl, h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.l.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega)]
  exact w.idx

end VG.Proof.HmacTable.PPC64LE
