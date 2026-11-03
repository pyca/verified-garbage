module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Hashes
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfSteps
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Pre
public import VerifiedGarbage.Spec.HashTable
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Tables of the interface `Hash` on PPC64LE

As on AArch64 (`Proof/HashTable/AArch64.lean`), with the hash functions as
RSAES-OAEP on PPC64LE has them (`Link`), one implementation of each
(`vars`): the table of a hash function (`tableOf`) holds the addresses of
its streaming `init`, `update` and `finalize`, then its data
(`Spec.HashTable.dataOf`); an indirect call of the functions of every table
(`fnsOf`) to one of them reaches it (`tabOK_of`), when the functions of
distinct names are at distinct addresses and those of the same name have the
same code (`Coh`). What MGF1 needs of a table that is a stack argument, on
entry (`tabS_of`). For the contracts' satisfiability, a state holding the
table of `w` at `0x300000` (`withTable`).
-/

@[expose] public section

namespace VG.Proof.HashTable.PPC64LE

open VG VG.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (Fns arg)
open VG.Proof.RsaOaep.PPC64LE (Link TabOK TabMem TabS kR SC)
open VG.Proof.HashTable (pw_ne find_name symsOf put5 put5_held put5_below)

/-- A hash function, with its place in `Spec.Mgf1.hashes`. -/
structure TVar where
  H : Impl.Hmac.Stream.PPC64LE.Hash
  l : Link H
  idx : Spec.Mgf1.hashes[Spec.HashTable.index l.G]? = some l.G

def sha1V : TVar := ⟨_, Proof.RsaOaep.PPC64LE.sha1L, rfl⟩
def sha224V : TVar := ⟨_, Proof.RsaOaep.PPC64LE.sha224L, rfl⟩
def sha256V : TVar := ⟨_, Proof.RsaOaep.PPC64LE.sha256L, rfl⟩
def sha384V : TVar := ⟨_, Proof.RsaOaep.PPC64LE.sha384L, rfl⟩
def sha512V : TVar := ⟨_, Proof.RsaOaep.PPC64LE.sha512L, rfl⟩
def sha512_224V : TVar := ⟨_, Proof.RsaOaep.PPC64LE.sha512_224L, rfl⟩
def sha512_256V : TVar := ⟨_, Proof.RsaOaep.PPC64LE.sha512_256L, rfl⟩

/-- Every hash function. -/
def vars : List TVar := [sha1V, sha224V, sha256V, sha384V, sha512V, sha512_224V, sha512_256V]

/-- The table of `w`'s streaming functions, `VG_HASH_<HASH>`. -/
def tableOf (w : TVar) : FnTable where
  name := s!"VG_HASH_{w.l.G.rust.toUpper}"
  iface := Spec.HashTable.iface
  fns := [w.H.initN, w.H.updN, w.H.finN]
  data := Spec.HashTable.dataOf w.l.G

/-- The tables of `vs`. -/
def tables (vs : List TVar) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List TVar) : Fns :=
  ⟨vs.map fun w => (w.H.initN, w.H.initC), vs.map fun w => (w.H.updN, w.H.updC),
    vs.map fun w => (w.H.finN, w.H.finC)⟩

/-- The functions of `tables vs`. -/
def names (vs : List TVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The functions of the same name have the same code. -/
def Coh (vs : List TVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.H.initN = w'.H.initN → w.H.initC = w'.H.initC) ∧
    (w.H.updN = w'.H.updN → w.H.updC = w'.H.updC) ∧ (w.H.finN = w'.H.finN → w.H.finC = w'.H.finC)

instance (vs : List TVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

theorem mem_names {vs : List TVar} {w : TVar} (hw : w ∈ vs) :
    w.H.initN ∈ names vs ∧ w.H.updN ∈ names vs ∧ w.H.finN ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem tabOK_of {vs : List TVar} (hc : Coh vs) {sy : String → Addr}
    (hd : (names vs).Pairwise fun f g => f ≠ g → sy f ≠ sy g) {w : TVar} (hw : w ∈ vs) :
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

/-- What the table of `w` at `p` holds: its functions' addresses, its index
and its digest length. -/
theorem held_tableOf {m : Mem} {p : Addr} {s : State} {w : TVar}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (tableOf w))) :
    TabMem w.H s.syms p m ∧ m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.l.G) ∧
      m.readW (p + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D := by
  have hw : FnTable.words isa s (tableOf w) = [s.syms w.H.initN, s.syms w.H.updN, s.syms w.H.finN,
      BitVec.ofNat 64 (Spec.HashTable.index w.l.G), BitVec.ofNat 64 w.l.G.len] := rfl
  rw [hw] at h
  have h0 := h 0 (by simp)
  rw [show p + BitVec.ofNat 64 (64 / 8 * 0) = p by simp] at h0
  exact ⟨⟨h0, h 1 (by simp), h 2 (by simp)⟩, h 3 (by simp), (h 4 (by simp)).trans (by rw [w.l.len]; rfl)⟩

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : Addr} {w : TVar}
    (h : m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.l.G)) :
    Spec.HashTable.hashAt 64 m p = some w.l.G := by
  simp only [Spec.HashTable.hashAt, Spec.HashTable.fns]
  rw [show p + BitVec.ofNat 64 (64 / 8 * 3) = p + BitVec.ofNat 64 24 from rfl, h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.l.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega)]
  exact w.idx

/-- What MGF1 needs of the table of `w` at `p`, the stack argument `j` (in
`A`, a buffer only read, apart from `kR` and `SC`), itself a buffer only
read apart from them. -/
theorem tabS_of {S : State → Addr} {s : State} {j : Nat} (hj : arg j < 2 ^ 15 ∧ arg j % 4 = 0) {p : Addr}
    (harg : s.mem.readW (stackArgAddr s j) 64 = p) {A : Region} (hA : A ∈ s.rd)
    (hAc : A.Contains (stackArgAddr s j) 8) (hAs : Region.Sub ⟨stackArgAddr s j, 8⟩ A)
    (hkA : (kR s).Disjoint A) (hSA : (SC S s).Disjoint A)
    (hT : Sig.tableRegion 64 p 5 ∈ s.rd) (hkT : (kR s).Disjoint (Sig.tableRegion 64 p 5))
    (hST : (SC S s).Disjoint (Sig.tableRegion 64 p 5))
    {vs : List TVar} (hc : Coh vs) (hd : (names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    {w : TVar} (hw : w ∈ vs) (hh : Abi.tableHeld 64 s.mem p (FnTable.words isa s (tableOf w))) :
    TabS w.H (fnsOf vs) j S s p := by
  obtain ⟨hm, -, hD⟩ := held_tableOf hh
  have hk : ∀ k < 5, Region.Sub ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ (Sig.tableRegion 64 p 5) := fun k hk =>
    Offset.sub_base p (by show 8 * k + 8 ≤ 5 * (64 / 8); omega)
  refine ⟨hj, harg, ⟨A, hA, hAc⟩, (hkA.sub_right hAs).symm, (hSA.sub_right hAs).symm,
    fun k hk => ⟨_, hT, Offset.contains_base p (by show 8 * k + 8 ≤ 5 * (64 / 8); omega) (by omega)⟩,
    fun k hk' => (hkT.sub_right (hk k hk')).symm, fun k hk' => (hST.sub_right (hk k hk')).symm, hm, hD,
    tabOK_of hc hd hw⟩

/-! ## States holding a table, for the contracts' satisfiability -/

/-- The words of `w`'s table, at the addresses `symsOf` gives `vs`' functions. -/
def tw (vs : List TVar) (w : TVar) : List (BitVec 64) :=
  [symsOf (names vs) w.H.initN, symsOf (names vs) w.H.updN, symsOf (names vs) w.H.finN,
    BitVec.ofNat 64 (Spec.HashTable.index w.l.G), BitVec.ofNat 64 w.l.G.len]

/-- A state with `s`'s registers and regions, `w`'s table at `0x300000`,
and `vs`' functions at distinct addresses. -/
def withTable (s : State) (vs : List TVar) (w : TVar) : State :=
  { s with
    mem := put5 s.mem 0x300000 ((tw vs w).getD 0 0) ((tw vs w).getD 1 0) ((tw vs w).getD 2 0)
      ((tw vs w).getD 3 0) ((tw vs w).getD 4 0)
    syms := symsOf (names vs) }

/-- The table of `w`, at `0x300000`. -/
theorem withTable_held (s : State) (vs : List TVar) (w : TVar) :
    Abi.tableHeld 64 (withTable s vs w).mem 0x300000 (FnTable.words isa (withTable s vs w) (tableOf w)) :=
  put5_held (ws := tw vs w) rfl

/-- Below `0x300000`, a word as in `s`. -/
theorem withTable_below (s : State) (vs : List TVar) (w : TVar) {a : Addr} (ha : a.toNat + 8 ≤ 0x300000) :
    (withTable s vs w).mem.readW a 64 = s.mem.readW a 64 :=
  put5_below ha _ _ _ _ _

end VG.Proof.HashTable.PPC64LE
