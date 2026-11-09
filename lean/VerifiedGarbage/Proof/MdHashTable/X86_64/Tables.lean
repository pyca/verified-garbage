module

-- separate module: the tables a registration names (`tables`, `fnsOf`), apart from the proofs that use them

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Spec.MdHashTable
public import VerifiedGarbage.Impl.MdHashTable.X86_64
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.TabCall

/-!
# Tables of the interface `MdHash` on x86-64

The table of a hash function's variant (`tableOf`): the addresses of its
streaming `init`, `update` and `finalize`, its compression function and the
digest of its hash value (`digest`, `Impl/MdHashTable/X86_64.lean`), then its
data: its index in `Mgf1.hashes`, its digest length, its block size, the size
of its length field, the size of its streaming state, and whether it is
big-endian; the tables of a list of variants (`tables`, one for each), which
a function taking a table of `MdHash` lists as those it may be given; and the
functions an indirect call of each of a table's functions may reach
(`fnsOf`).

A function's proof runs the code of whichever of these the table holds
(`HTF`): the first function of `fnsOf vs` at the address called, which is the
table's function of that name (`htf_of`), when the functions of distinct
names are at distinct addresses (as `Abi.withTables` says) and the variants'
functions of the same name have the same code (`Coh`, which the registration
checks). The digest depends only on the streaming code's parameters, so it is
named by them (`digName`, as `shapeOf` gives them for the hash function's
index): the variants of one hash function, and SHA-224 and SHA-256 (and the
SHA-512 family), share it.
-/

@[expose] public section

namespace VG.Proof.MdHashTable.X86_64

open VG VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Impl.RsaPss.X86_64 (MdFns shapeOf)
open VG.Proof.RsaPss.X86_64 (HTF)
open VG.Proof.Bignum (off)
open VG.Proof.HashTable (pw_ne find_name)

/-- The index of `w`'s hash function in `Mgf1.hashes`. -/
def idx (w : MdHash) : Nat := Spec.HashTable.index w.mgf.G

/-- The name of the streaming code's family of the hash function of index
`i`, whose parameters `shapeOf i` gives. -/
def family : Nat → String
  | 0 => "md5" | 1 => "sha1" | 2 | 3 => "sha256" | _ => "sha512"

/-- The name of `w`'s digest. -/
def digName (w : MdHash) : String := s!"vg_{family (idx w)}_state_digest"

/-- 1 if the hash function of index `i` is big-endian (all but MD5). -/
def bigEndian (i : Nat) : Nat := if i = 0 then 0 else 1

/-- The table of `w`'s functions, `VG_MD_HASH_<HASH><SUFFIX>`. -/
def tableOf (w : MdHash) : FnTable where
  name := s!"VG_MD_HASH_{w.mgf.G.rust.toUpper}{w.suffix.toUpper}"
  iface := Spec.MdHashTable.iface
  fns := [w.H.initN, w.H.updN, w.H.finN, w.H.compN, digName w]
  data := Spec.MdHashTable.dataOf w.mgf.G ++
    [BitVec.ofNat 64 w.H.P.B, BitVec.ofNat 64 w.H.P.L, BitVec.ofNat 64 w.H.S, BitVec.ofNat 64 (bigEndian (idx w))]

/-- The tables of the variants `vs`. -/
def tables (vs : List MdHash) : List FnTable := vs.map tableOf

/-- For each of the functions PSS calls through a table, that function of
each of `vs`. -/
def fnsOf (vs : List MdHash) : MdFns :=
  ⟨vs.map fun w => (w.H.initN, w.H.initC), vs.map fun w => (w.H.compN, w.H.compC),
    vs.map fun w => (digName w, Impl.MdHashTable.X86_64.digest w.H.P)⟩

/-- The functions of `tables vs`. -/
def names (vs : List MdHash) : List String := ((tables vs).map (·.fns)).flatten

/-- The variants' functions of the same name have the same code. -/
def Coh (vs : List MdHash) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.H.initN = w'.H.initN → w.H.initC = w'.H.initC) ∧
    (w.H.compN = w'.H.compN → w.H.compC = w'.H.compC) ∧
    (digName w = digName w' → Impl.MdHashTable.X86_64.digest w.H.P = Impl.MdHashTable.X86_64.digest w'.H.P)

/-- The streaming code's parameters and the digest length of `w` are those
`shapeOf` gives its index, and its index is one of `idxs`. -/
def Shape (w : MdHash) : Prop :=
  idx w ∈ Impl.RsaPss.X86_64.idxs ∧ w.H.P = (shapeOf (idx w)).1 ∧ w.H.D = (shapeOf (idx w)).2

/-- The parameters' equality, field by field. -/
instance : DecidableEq Impl.MdStream.X86_64.Params := fun a b =>
  decidable_of_iff (a.N = b.N ∧ a.B = b.B ∧ a.L = b.L ∧ a.so = b.so ∧ a.len = b.len ∧ a.lenV = b.lenV ∧
      a.out = b.out) (by cases a; cases b; simp)

instance (vs : List MdHash) : Decidable (Coh vs) := by unfold Coh; infer_instance
instance (w : MdHash) : Decidable (Shape w) := by unfold Shape; infer_instance

theorem mem_names {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) :
    w.H.initN ∈ names vs ∧ w.H.updN ∈ names vs ∧ w.H.finN ∈ names vs ∧ w.H.compN ∈ names vs ∧
      digName w ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem htf_of {vs : List MdHash} (hc : Coh vs) {sy : String → Addr}
    (hd : (names vs).Pairwise fun f g => f ≠ g → sy f ≠ sy g) {w : MdHash} (hw : w ∈ vs) :
    HTF w.H (digName w) (fnsOf vs) sy := by
  have hn := mem_names hw
  refine ⟨find_name (List.mem_map_of_mem (f := fun w => (w.H.initN, w.H.initC)) hw) ?_ ?_,
    find_name (List.mem_map_of_mem (f := fun w => (w.H.compN, w.H.compC)) hw) ?_ ?_,
    find_name (List.mem_map_of_mem (f := fun w => (digName w, Impl.MdHashTable.X86_64.digest w.H.P)) hw) ?_ ?_⟩
  all_goals intro q hq
  all_goals obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq
  · exact pw_ne hd _ (mem_names hw').1 _ hn.1
  · exact (hc w' hw' w hw).1
  · exact pw_ne hd _ (mem_names hw').2.2.2.1 _ hn.2.2.2.1
  · exact (hc w' hw' w hw).2.1
  · exact pw_ne hd _ (mem_names hw').2.2.2.2 _ hn.2.2.2.2
  · exact (hc w' hw' w hw).2.2

/-- The words of `w`'s table in the state `s`. -/
theorem words_tableOf (s : State) (w : MdHash) : FnTable.words isa s (tableOf w) =
    [s.syms w.H.initN, s.syms w.H.updN, s.syms w.H.finN, s.syms w.H.compN, s.syms (digName w),
      BitVec.ofNat 64 (idx w), BitVec.ofNat 64 w.mgf.G.len, BitVec.ofNat 64 w.H.P.B, BitVec.ofNat 64 w.H.P.L,
      BitVec.ofNat 64 w.H.S, BitVec.ofNat 64 (bigEndian (idx w))] := rfl

/-- What the table of `w` at `p` holds: the addresses of its `init`,
compression function and digest, its index and its digest length. -/
theorem held_tableOf {m : Mem} {p : Addr} {s : State} {w : MdHash}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (tableOf w))) :
    m.readW (off p 0) 64 = s.syms w.H.initN ∧ m.readW (off p 24) 64 = s.syms w.H.compN ∧
      m.readW (off p 32) 64 = s.syms (digName w) ∧ m.readW (off p 40) 64 = BitVec.ofNat 64 (idx w) ∧
      m.readW (off p 48) 64 = BitVec.ofNat 64 w.mgf.G.len := by
  rw [words_tableOf] at h
  exact ⟨h 0 (by simp), h 3 (by simp), h 4 (by simp), h 5 (by simp), h 6 (by simp)⟩

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : Addr} {w : MdHash}
    (h : m.readW (off p 40) 64 = BitVec.ofNat 64 (idx w)) :
    Spec.MdHashTable.hashAt 64 m p = some w.mgf.G := by
  have hm := w.mgf.mem
  simp only [Spec.MdHashTable.hashAt, Spec.MdHashTable.fns]
  rw [show p + BitVec.ofNat 64 (64 / 8 * 5) = off p 40 from rfl, h]
  simp only [idx]
  simp only [Proof.Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e <;> rw [e] <;> rfl

end VG.Proof.MdHashTable.X86_64
