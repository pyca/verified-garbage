module

public import VerifiedGarbage.Proof.RsaOaep.X86.Mgf
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha1
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha224
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha256
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha512
public import VerifiedGarbage.Spec.HashTable
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.X86.Exec

/-!
# Tables of the interface `Hash` on x86

As on x86-64 (`Proof/HashTable/X86_64.lean`), with the hash functions as
RSAES-OAEP on x86 has them (`OHash`), each with the suffix and the CPU
features of its variant (`TVar`): SHA-1 with each of its backends, SHA-224
and SHA-256 with each of theirs, and the SHA-512 family (`vars`). The table
of a variant (`tableOf`) holds the addresses of its streaming `init`,
`update` and `finalize`, then its data (`Spec.HashTable.dataOf`), each word
32 bits wide; an indirect call of the functions of every variant
(`fnsOf`) to one of them reaches it (`tabOK_of`), when the functions of
distinct names are at distinct addresses and the variants' functions of the
same name have the same code (`Coh`).
-/

@[expose] public section

namespace VG.Proof.HashTable.X86

open VG VG.X86
open VG.Impl.RsaOaep.X86 (Fns)
open VG.Proof.RsaOaep.X86 (OHash TabOK TabMem)
open VG.Proof.HashTable (pw_ne find_name)

/-- A variant of a hash function: the hash function, the suffix of its
functions' names and the CPU features it needs, and its place in
`Spec.Mgf1.hashes`. -/
structure TVar where
  g : OHash
  suffix : String
  features : List String
  idx : Spec.Mgf1.hashes[Spec.HashTable.index g.G]? = some g.G

def sha1V (b : Proof.Sha1.X86.Variants.Backend) : TVar := ⟨Proof.RsaOaep.X86.sha1 b, b.stream.suffix, b.features, rfl⟩
def sha224V (b : Proof.Sha256.X86.Variants.Backend) : TVar :=
  ⟨Proof.RsaOaep.X86.sha224 b, b.stream.suffix, b.features, rfl⟩
def sha256V (b : Proof.Sha256.X86.Variants.Backend) : TVar :=
  ⟨Proof.RsaOaep.X86.sha256 b, b.stream.suffix, b.features, rfl⟩
def sha384V : TVar := ⟨Proof.RsaOaep.X86.sha384, "", [], rfl⟩
def sha512V : TVar := ⟨Proof.RsaOaep.X86.sha512, "", [], rfl⟩
def sha512_224V : TVar := ⟨Proof.RsaOaep.X86.sha512_224, "", [], rfl⟩
def sha512_256V : TVar := ⟨Proof.RsaOaep.X86.sha512_256, "", [], rfl⟩

/-- Every variant: SHA-1's with the backends `vs1`, SHA-224's and SHA-256's
with `vs256`, and the SHA-512 family's. -/
def vars (vs1 : List Proof.Sha1.X86.Variants.Backend) (vs256 : List Proof.Sha256.X86.Variants.Backend) :
    List TVar :=
  vs1.map sha1V ++ vs256.map sha224V ++ vs256.map sha256V ++ [sha384V, sha512V, sha512_224V, sha512_256V]

/-- The table of `w`'s streaming functions, `VG_HASH_<HASH><SUFFIX>`. -/
def tableOf (w : TVar) : FnTable where
  name := s!"VG_HASH_{w.g.G.rust.toUpper}{w.suffix.toUpper}"
  iface := Spec.HashTable.iface
  fns := [w.g.H.initN, w.g.H.updN, w.g.H.finN]
  data := Spec.HashTable.dataOf w.g.G

/-- The tables of the variants `vs`. -/
def tables (vs : List TVar) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List TVar) : Fns :=
  ⟨vs.map fun w => (w.g.H.initN, w.g.H.initC), vs.map fun w => (w.g.H.updN, w.g.H.updC),
    vs.map fun w => (w.g.H.finN, w.g.H.finC)⟩

/-- The functions of `tables vs`. -/
def names (vs : List TVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The variants' functions of the same name have the same code. -/
def Coh (vs : List TVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.g.H.initN = w'.g.H.initN → w.g.H.initC = w'.g.H.initC) ∧
    (w.g.H.updN = w'.g.H.updN → w.g.H.updC = w'.g.H.updC) ∧ (w.g.H.finN = w'.g.H.finN → w.g.H.finC = w'.g.H.finC)

instance (vs : List TVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

theorem mem_names {vs : List TVar} {w : TVar} (hw : w ∈ vs) :
    w.g.H.initN ∈ names vs ∧ w.g.H.updN ∈ names vs ∧ w.g.H.finN ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem tabOK_of {vs : List TVar} (hc : Coh vs) {sy : String → BitVec 32}
    (hd : (names vs).Pairwise fun f g => f ≠ g → sy f ≠ sy g) {w : TVar} (hw : w ∈ vs) :
    TabOK w.g.H (fnsOf vs) sy := by
  have hn := mem_names hw
  have hd64 : (names vs).Pairwise fun f g => f ≠ g → (sy f).setWidth 64 ≠ (sy g).setWidth 64 :=
    hd.imp fun {a b} h hne e => h hne (by
      have := congrArg (fun x : BitVec 64 => x.toNat) e
      have ha := (sy a).isLt
      have hb := (sy b).isLt
      simp only [BitVec.toNat_setWidth] at this
      exact BitVec.eq_of_toNat_eq (by rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this))
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

/-- What the table of `w` at `p` holds: its functions' addresses, its index
and its digest length, 32 bits each. -/
theorem held_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 20 ≤ 2 ^ 32) {s : State} {w : TVar}
    (h : Abi.tableHeld 32 m (p.setWidth 64) (FnTable.words isa s (tableOf w))) :
    TabMem w.g.H s.syms p m ∧
      m.readW (VG.X86.addr p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.g.G) ∧
      m.readW (VG.X86.addr p 16) 32 = BitVec.ofNat 32 w.g.H.D := by
  have hw : FnTable.words isa s (tableOf w) = [(s.syms w.g.H.initN).setWidth 64, (s.syms w.g.H.updN).setWidth 64,
      (s.syms w.g.H.finN).setWidth 64, BitVec.ofNat 64 (Spec.HashTable.index w.g.G),
      BitVec.ofNat 64 w.g.G.len] := rfl
  rw [hw] at h
  have a : ∀ i, i < 5 → VG.X86.addr p (4 * i) = p.setWidth 64 + BitVec.ofNat 64 (32 / 8 * i) := fun i hi => by
    rw [addr_eq (by omega)]
  have e : ∀ i (hi : i < 5), m.readW (VG.X86.addr p (4 * i)) 32 = _ := fun i hi => (a i hi).symm ▸ h i (by simp; omega)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have := e 0 (by decide); simp only [Nat.mul_zero] at this; rw [this]; simp
  · have := e 1 (by decide); simp only [Nat.mul_one] at this; rw [this]; simp
  · have := e 2 (by decide); rw [show 4 * 2 = 8 by rfl] at this; rw [this]; simp
  · have := e 3 (by decide); rw [show 4 * 3 = 12 by rfl] at this; rw [this]; simp
  · have := e 4 (by decide); rw [show 4 * 4 = 16 by rfl] at this; rw [this, w.g.glen]; simp

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 20 ≤ 2 ^ 32) {w : TVar}
    (h : m.readW (VG.X86.addr p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.g.G)) :
    Spec.HashTable.hashAt 32 m (p.setWidth 64) = some w.g.G := by
  simp only [Spec.HashTable.hashAt, Spec.HashTable.fns]
  rw [show p.setWidth 64 + BitVec.ofNat 64 (32 / 8 * 3) = VG.X86.addr p 12 by rw [addr_eq (by omega)], h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.g.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega)]
  exact w.idx

end VG.Proof.HashTable.X86
