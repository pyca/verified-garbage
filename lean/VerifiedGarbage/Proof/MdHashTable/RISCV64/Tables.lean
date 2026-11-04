module

public import VerifiedGarbage.Proof.HashTable.RISCV64
public import VerifiedGarbage.Proof.RsaPss.RISCV64.TabCall
public import VerifiedGarbage.Spec.MdHashTable
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Tables of the interface `MdHash` on RISC-V

As on x86-64 (`Proof/MdHashTable/X86_64/Tables.lean`), for the hash
functions of the tables of `Hash` (`Proof/HashTable/RISCV64.lean`, `TVar`)
with what hashing a message with their compression functions needs
(`MdL`, `MVar`): the table of a hash function (`tableOf`) holds the
addresses of its streaming `init`, `update` and `finalize`, its compression
function and the digest of its hash value (`digest`,
`Impl/MdHashTable/RISCV64.lean`), then its data: its index in
`Mgf1.hashes`, its digest length, its block size, the size of its length
field, the size of its streaming state, and whether it is big-endian. The
digest depends only on the hash value's size and byte order, so it is named
by the family of the hash function (`digName`): SHA-224 and SHA-256 (and
the SHA-512 family) share it. An indirect call of the functions of every
table (`fnsOf`) to one of them reaches it (`tabOKM_of`), when the functions
of distinct names are at distinct addresses and those of the same name have
the same code (`Coh`). What PSS needs of a table that is a stack argument,
on entry (`tabM_of`).
-/

@[expose] public section

namespace VG.Proof.MdHashTable.RISCV64

open VG VG.RISCV64
open VG.Impl.RsaOaep.RISCV64 (frameBytes)
open VG.Impl.RsaPss.RISCV64 (MdFns)
open VG.Proof.RsaOaep.RISCV64 (kR SC)
open VG.Proof.RsaPss.RISCV64 (MdL TabM TabMemM TabOKM)
open VG.Proof.HashTable (pw_ne find_name)
open VG.Proof.HashTable.RISCV64 (TVar)

/-- A hash function of a table of `Hash`, with its compression function and
digest. -/
structure MVar where
  w : TVar
  M : MdL w.H w.l.ok

def md5V : MVar := ⟨HashTable.RISCV64.md5V, Proof.RsaPss.RISCV64.md5M⟩
def sha1V : MVar := ⟨HashTable.RISCV64.sha1V, Proof.RsaPss.RISCV64.sha1M⟩
def sha224V : MVar := ⟨HashTable.RISCV64.sha224V, Proof.RsaPss.RISCV64.sha224M⟩
def sha256V : MVar := ⟨HashTable.RISCV64.sha256V, Proof.RsaPss.RISCV64.sha256M⟩
def sha384V : MVar := ⟨HashTable.RISCV64.sha384V, Proof.RsaPss.RISCV64.sha384M⟩
def sha512V : MVar := ⟨HashTable.RISCV64.sha512V, Proof.RsaPss.RISCV64.sha512M⟩
def sha512_224V : MVar := ⟨HashTable.RISCV64.sha512_224V, Proof.RsaPss.RISCV64.sha512_224M⟩
def sha512_256V : MVar := ⟨HashTable.RISCV64.sha512_256V, Proof.RsaPss.RISCV64.sha512_256M⟩

/-- Every hash function. -/
def vars : List MVar := [md5V, sha1V, sha224V, sha256V, sha384V, sha512V, sha512_224V, sha512_256V]

/-- The index of `v`'s hash function in `Mgf1.hashes`. -/
def idx (v : MVar) : Nat := Spec.HashTable.index v.w.l.G

/-- The name of the family of the hash function of index `i`. -/
def family : Nat → String
  | 0 => "md5" | 1 => "sha1" | 2 | 3 => "sha256" | _ => "sha512"

/-- The name of `v`'s digest. -/
def digName (v : MVar) : String := s!"vg_{family (idx v)}_state_digest"

/-- 1 if `v` is big-endian. -/
def bigEndian (v : MVar) : Nat := if v.M.be then 1 else 0

/-- The table of `v`'s functions, `VG_MD_HASH_<HASH>`. -/
def tableOf (v : MVar) : FnTable where
  name := s!"VG_MD_HASH_{v.w.l.G.rust.toUpper}"
  iface := Spec.MdHashTable.iface
  fns := [v.w.H.initN, v.w.H.updN, v.w.H.finN, v.M.compN, digName v]
  data := Spec.MdHashTable.dataOf v.w.l.G ++
    [BitVec.ofNat 64 v.w.H.B, BitVec.ofNat 64 v.M.L, BitVec.ofNat 64 v.w.H.S, BitVec.ofNat 64 (bigEndian v)]

/-- The tables of `vs`. -/
def tables (vs : List MVar) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List MVar) : MdFns :=
  ⟨vs.map fun v => (v.w.H.initN, v.w.H.initC), vs.map fun v => (v.w.H.updN, v.w.H.updC),
    vs.map fun v => (v.w.H.finN, v.w.H.finC), vs.map fun v => (v.M.compN, v.M.compC),
    vs.map fun v => (digName v, Impl.MdHashTable.RISCV64.digest v.M.out)⟩

/-- The functions of `tables vs`. -/
def names (vs : List MVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The functions of the same name have the same code. -/
def Coh (vs : List MVar) : Prop :=
  ∀ v ∈ vs, ∀ v' ∈ vs, (v.w.H.initN = v'.w.H.initN → v.w.H.initC = v'.w.H.initC) ∧
    (v.w.H.updN = v'.w.H.updN → v.w.H.updC = v'.w.H.updC) ∧
    (v.w.H.finN = v'.w.H.finN → v.w.H.finC = v'.w.H.finC) ∧
    (v.M.compN = v'.M.compN → v.M.compC = v'.M.compC) ∧ (digName v = digName v' → v.M.out = v'.M.out)

instance (vs : List MVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

theorem mem_names {vs : List MVar} {v : MVar} (hv : v ∈ vs) :
    v.w.H.initN ∈ names vs ∧ v.w.H.updN ∈ names vs ∧ v.w.H.finN ∈ names vs ∧ v.M.compN ∈ names vs ∧
      digName v ∈ names vs := by
  have : (tableOf v).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hv)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `v`'s. -/
theorem tabOKM_of {vs : List MVar} (hc : Coh vs) {sy : String → Addr}
    (hd : (names vs).Pairwise fun f g => f ≠ g → sy f ≠ sy g) {v : MVar} (hv : v ∈ vs) :
    TabOKM v.w.H v.M.compN v.M.compC (digName v) (Impl.MdHashTable.RISCV64.digest v.M.out) (fnsOf vs) sy := by
  have hn := mem_names hv
  refine ⟨find_name (List.mem_map_of_mem (f := fun v => (v.w.H.initN, v.w.H.initC)) hv) ?_ ?_,
    find_name (List.mem_map_of_mem (f := fun v => (v.w.H.updN, v.w.H.updC)) hv) ?_ ?_,
    find_name (List.mem_map_of_mem (f := fun v => (v.w.H.finN, v.w.H.finC)) hv) ?_ ?_,
    find_name (List.mem_map_of_mem (f := fun v => (v.M.compN, v.M.compC)) hv) ?_ ?_,
    find_name (List.mem_map_of_mem (f := fun v => (digName v, Impl.MdHashTable.RISCV64.digest v.M.out)) hv) ?_ ?_⟩
  all_goals intro q hq
  all_goals obtain ⟨v', hv', rfl⟩ := List.mem_map.mp hq
  · exact pw_ne hd _ (mem_names hv').1 _ hn.1
  · exact (hc v' hv' v hv).1
  · exact pw_ne hd _ (mem_names hv').2.1 _ hn.2.1
  · exact (hc v' hv' v hv).2.1
  · exact pw_ne hd _ (mem_names hv').2.2.1 _ hn.2.2.1
  · exact (hc v' hv' v hv).2.2.1
  · exact pw_ne hd _ (mem_names hv').2.2.2.1 _ hn.2.2.2.1
  · exact (hc v' hv' v hv).2.2.2.1
  · exact pw_ne hd _ (mem_names hv').2.2.2.2 _ hn.2.2.2.2
  · intro e; exact congrArg Impl.MdHashTable.RISCV64.digest ((hc v' hv' v hv).2.2.2.2 e)

/-- The words of `v`'s table in the state `s`. -/
theorem words_tableOf (s : State) (v : MVar) : FnTable.words isa s (tableOf v) =
    [s.syms v.w.H.initN, s.syms v.w.H.updN, s.syms v.w.H.finN, s.syms v.M.compN, s.syms (digName v),
      BitVec.ofNat 64 (idx v), BitVec.ofNat 64 v.w.l.G.len, BitVec.ofNat 64 v.w.H.B, BitVec.ofNat 64 v.M.L,
      BitVec.ofNat 64 v.w.H.S, BitVec.ofNat 64 (bigEndian v)] := rfl

/-- What the table of `v` at `p` holds: its functions' addresses and its
index. -/
theorem held_tableOf {m : Mem} {p : Addr} {s : State} {v : MVar}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (tableOf v))) :
    TabMemM v.w.H v.M.compN (digName v) s.syms p m ∧
      m.readW (p + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (idx v) := by
  rw [words_tableOf] at h
  have h0 := h 0 (by simp)
  rw [show p + BitVec.ofNat 64 (64 / 8 * 0) = p by simp] at h0
  exact ⟨⟨h0, h 1 (by simp), h 2 (by simp), h 3 (by simp), h 4 (by simp)⟩, h 5 (by simp)⟩

/-- The hash function a table of `v` names. -/
theorem hashAt_tableOf {m : Mem} {p : Addr} {v : MVar}
    (h : m.readW (p + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (idx v)) :
    Spec.MdHashTable.hashAt 64 m p = some v.w.l.G := by
  simp only [Spec.MdHashTable.hashAt, Spec.MdHashTable.fns]
  rw [show p + BitVec.ofNat 64 (64 / 8 * 5) = p + BitVec.ofNat 64 40 from rfl, h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == v.w.l.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [idx, Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega)]
  exact v.w.idx

/-- What PSS needs of the table of `v` at `p`, the stack argument `j` (in
`A`, a buffer only read, apart from `kR` and `SC`), itself a buffer only
read apart from them. -/
theorem tabM_of {S : State → Addr} {s : State} {j : Nat} (hj : frameBytes + 8 * j < 2048) {p : Addr}
    (harg : s.mem.readW (stackArgAddr s j) 64 = p) (hargA : (stackArgAddr s j).toNat % 8 = 0)
    (hpA : p.toNat % 8 = 0) (hpw : p.toNat + 40 ≤ 2 ^ 64) {A : Region} (hA : A ∈ s.rd)
    (hAc : A.Contains (stackArgAddr s j) 8) (hAs : Region.Sub ⟨stackArgAddr s j, 8⟩ A)
    (hkA : (kR s).Disjoint A) (hSA : (SC S s).Disjoint A)
    (hT : Sig.tableRegion 64 p 11 ∈ s.rd) (hkT : (kR s).Disjoint (Sig.tableRegion 64 p 11))
    (hST : (SC S s).Disjoint (Sig.tableRegion 64 p 11))
    {vs : List MVar} (hc : Coh vs) (hd : (names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    {v : MVar} (hv : v ∈ vs) (hh : Abi.tableHeld 64 s.mem p (FnTable.words isa s (tableOf v))) :
    TabM v.M (digName v) (fnsOf vs) j S s p := by
  obtain ⟨hm, -⟩ := held_tableOf hh
  have hk : ∀ k < 5, Region.Sub ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ (Sig.tableRegion 64 p 11) := fun k hk =>
    Offset.sub_base p (by show 8 * k + 8 ≤ 11 * (64 / 8); omega)
  refine ⟨hj, harg, hargA, ⟨A, hA, hAc⟩, (hkA.sub_right hAs).symm, (hSA.sub_right hAs).symm, hpA, hpw,
    fun k hk => ⟨_, hT, Offset.contains_base p (by show 8 * k + 8 ≤ 11 * (64 / 8); omega) (by omega)⟩,
    fun k hk' => (hkT.sub_right (hk k hk')).symm, fun k hk' => (hST.sub_right (hk k hk')).symm, hm,
    tabOKM_of hc hd hv⟩

end VG.Proof.MdHashTable.RISCV64
