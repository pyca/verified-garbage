module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Impl.RsaOaep.AArch64.Mgf1.Table
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Tables of the interface `Hmac` on AArch64

The table of a hash function's variant (`tableOf`, `VG_HMAC_<HASH><SUFFIX>`):
the addresses of HMAC's `init` and `finalize` and of the streaming `update`,
in the forms that take their working space as an argument (`_scratch`, in
`x4`: `Hash.hmacInit`, `Hash.updC`, `Hash.hmacFin`), then its data
(`Spec.HmacTable.dataOf`: the hash function's index in `Mgf1.hashes`, its
digest length and HMAC's block size); the tables of a list of variants
(`tables`, one for each), which a function taking a table of `Hmac` lists
as those it may be given; and the functions an indirect call of each of a
table's functions may reach (`fnsOf`), as on x86-64
(`Proof/HmacTable/X86_64.lean`).

A function's proof runs the code of whichever of these the table holds
(`TabOK`): the first function of `fnsOf vs` at the address called, which is
the table's function of that name (`tabOK_of`), when the functions of
distinct names are at distinct addresses (as `Abi.withTables` says) and the
variants' functions of the same name have the same code (`Coh`, which the
registration checks). `held_tableOf` reads a table's words, and
`hashAt_tableOf` the hash function it names.
-/

@[expose] public section

namespace VG.Proof.HmacTable.AArch64

open VG VG.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.HashTable (pw_ne find_name)

/-- The table of `w`'s HMAC, `VG_HMAC_<HASH><SUFFIX>`. -/
def tableOf (w : MdHash) : FnTable where
  name := s!"VG_HMAC_{w.mgf.G.rust.toUpper}{w.suffix.toUpper}"
  iface := Spec.HmacTable.iface
  fns := [w.H.hmacInitN, w.H.updN, w.H.hmacFinN]
  data := Spec.HmacTable.dataOf w.mgf.G

/-- The tables of the variants `vs`. -/
def tables (vs : List MdHash) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List MdHash) : Fns :=
  ⟨vs.map fun w => (w.H.hmacInitN, w.H.hmacInit), vs.map fun w => (w.H.updN, w.H.updC),
    vs.map fun w => (w.H.hmacFinN, w.H.hmacFin)⟩

/-- The functions of `tables vs`. -/
def names (vs : List MdHash) : List String := ((tables vs).map (·.fns)).flatten

/-- The variants' functions of the same name have the same code. -/
def Coh (vs : List MdHash) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.H.hmacInitN = w'.H.hmacInitN → w.H.hmacInit = w'.H.hmacInit) ∧
    (w.H.updN = w'.H.updN → w.H.updC = w'.H.updC) ∧ (w.H.hmacFinN = w'.H.hmacFinN → w.H.hmacFin = w'.H.hmacFin)

instance (vs : List MdHash) : Decidable (Coh vs) := by unfold Coh; infer_instance

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `H`'s HMAC functions reaches it. -/
structure TabOK (H : Hash) (f : Fns) (sy : String → Addr) : Prop where
  i : f.init.find? (fun q => sy q.1 == sy H.hmacInitN) = some (H.hmacInitN, H.hmacInit)
  u : f.upd.find? (fun q => sy q.1 == sy H.updN) = some (H.updN, H.updC)
  f : f.fin.find? (fun q => sy q.1 == sy H.hmacFinN) = some (H.hmacFinN, H.hmacFin)

/-- At `p` in `m`, the addresses `sy` gives `H`'s HMAC `init`, the streaming
`update` and HMAC's `finalize`. -/
def TabMem (H : Hash) (sy : String → Addr) (p : Addr) (m : Mem) : Prop :=
  m.readW (p + BitVec.ofNat 64 0) 64 = sy H.hmacInitN ∧ m.readW (p + BitVec.ofNat 64 8) 64 = sy H.updN ∧
    m.readW (p + BitVec.ofNat 64 16) 64 = sy H.hmacFinN

theorem mem_names {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) :
    w.H.hmacInitN ∈ names vs ∧ w.H.updN ∈ names vs ∧ w.H.hmacFinN ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem tabOK_of {vs : List MdHash} (hc : Coh vs) {sy : String → Addr}
    (hd : (names vs).Pairwise fun f g => f ≠ g → sy f ≠ sy g) {w : MdHash} (hw : w ∈ vs) :
    TabOK w.H (fnsOf vs) sy := by
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
theorem words_tableOf (s : State) (w : MdHash) :
    FnTable.words isa s (tableOf w) = [s.syms w.H.hmacInitN, s.syms w.H.updN, s.syms w.H.hmacFinN,
      BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G), BitVec.ofNat 64 w.mgf.G.len,
      BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G)] := rfl

/-- What the table of `w` at `p` holds: its functions' addresses, its index,
its digest length and HMAC's block size. -/
theorem held_tableOf {m : Mem} {p : Addr} {s : State} {w : MdHash}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (tableOf w))) :
    TabMem w.H s.syms p m ∧
      m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G) ∧
      m.readW (p + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
      m.readW (p + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G) := by
  rw [words_tableOf] at h
  refine ⟨⟨h 0 (by simp), h 1 (by simp), h 2 (by simp)⟩, h 3 (by simp), ?_, h 5 (by simp)⟩
  exact (h 4 (by simp)).trans (by rw [w.mgf.len]; rfl)

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : Addr} {w : MdHash}
    (h : m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)) :
    Spec.HmacTable.hashAt 64 m p = some w.mgf.G := by
  have hm := w.mgf.mem
  simp only [Spec.HmacTable.hashAt, Spec.HmacTable.fns]
  rw [show p + BitVec.ofNat 64 (64 / 8 * 3) = p + BitVec.ofNat 64 24 from rfl, h]
  simp only [Proof.Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e <;> rw [e] <;> rfl

end VG.Proof.HmacTable.AArch64
