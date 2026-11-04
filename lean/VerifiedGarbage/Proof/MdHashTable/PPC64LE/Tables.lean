module

public import VerifiedGarbage.Proof.MdHashTable.PPC64LE.Fams
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Tab
public import VerifiedGarbage.Proof.HashTable.PPC64LE
public import VerifiedGarbage.Spec.MdHashTable
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Tables of the interface `MdHash` on PPC64LE

As on x86-64 (`Proof/MdHashTable/X86_64/Tables.lean`): a hash function's
variant (`MVar`): its streaming functions as RSAES-OAEP on PPC64LE has them
(`Link`), its family of streaming code (`Fam`) and the hash function of the
specification that code computes from its initial hash value. The table of
a variant (`tableOf`): the addresses of its streaming `init`, `update` and
`finalize`, its compression function and the digest of its hash value
(`digName`, named by the family, which SHA-224 and SHA-256 and the SHA-512
family share), then its data: its index in `Mgf1.hashes`, its digest length,
its block size, the size of its length field, the size of its streaming
state, and whether it is big-endian. An indirect call of the functions of
every table (`fnsOf`) to one of them reaches it (`mdTabOK_of`), when the
functions of distinct names are at distinct addresses and those of the same
name have the same code (`Coh`); what the proofs need of a table that is a
stack argument, on entry (`mdTabS_of`).
-/

@[expose] public section

namespace VG.Proof.MdHashTable.PPC64LE

open VG VG.PPC64LE VG.Proof.MdStream
open VG.Impl.RsaPss.PPC64LE (MdFns shapeOf idxs)
open VG.Impl.RsaOaep.PPC64LE (arg)
open VG.Impl.MdHashTable.PPC64LE (digest)
open VG.Proof.RsaOaep.PPC64LE (Link TabMem kR SC)
open VG.Proof.RsaPss.PPC64LE (MdTabOK MdTabS)
open VG.Proof.HashTable (pw_ne find_name)

/-- A hash function's variant. -/
structure MVar where
  H : Impl.Hmac.Stream.PPC64LE.Hash
  l : Link H
  idx : Spec.Mgf1.hashes[Spec.HashTable.index l.G]? = some l.G
  F : Fam
  iv : F.md.HV
  link : F.md.Link l.ok.SH iv H.D
  hN : H.N = F.P.N
  hB : H.B = F.P.B
  /-- Its index is one of `idxs`, whose code is for its digest length and its
  family's parameters. -/
  sh : Spec.HashTable.index l.G ∈ idxs ∧ (shapeOf (Spec.HashTable.index l.G)).1.D = H.D ∧
    (shapeOf (Spec.HashTable.index l.G)).2 = F.P

/-- The index of `w`'s hash function in `Mgf1.hashes`. -/
def idx (w : MVar) : Nat := Spec.HashTable.index w.l.G

/-- The name of the streaming code's family of the hash function of index
`i`, whose parameters `shapeOf i` gives. -/
def family : Nat → String
  | 0 => "md5" | 1 => "sha1" | 2 | 3 => "sha256" | _ => "sha512"

/-- The name of `w`'s digest. -/
def digName (w : MVar) : String := s!"vg_{family (idx w)}_state_digest"

/-- 1 if the hash function of index `i` is big-endian (all but MD5). -/
def bigEndian (i : Nat) : Nat := if i = 0 then 0 else 1

/-- The table of `w`'s functions, `VG_MD_HASH_<HASH>`. -/
def tableOf (w : MVar) : FnTable where
  name := s!"VG_MD_HASH_{w.l.G.rust.toUpper}"
  iface := Spec.MdHashTable.iface
  fns := [w.H.initN, w.H.updN, w.H.finN, w.F.cn, digName w]
  data := Spec.MdHashTable.dataOf w.l.G ++
    [BitVec.ofNat 64 w.F.P.B, BitVec.ofNat 64 w.F.P.L, BitVec.ofNat 64 w.H.S, BitVec.ofNat 64 (bigEndian (idx w))]

/-- The tables of the variants `vs`. -/
def tables (vs : List MVar) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List MVar) : MdFns :=
  ⟨vs.map fun w => (w.H.initN, w.H.initC), vs.map fun w => (w.H.updN, w.H.updC),
    vs.map fun w => (w.H.finN, w.H.finC), vs.map fun w => (w.F.cn, w.F.cc),
    vs.map fun w => (digName w, digest w.F.P)⟩

/-- The functions of `tables vs`. -/
def names (vs : List MVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The variants' functions of the same name have the same code. -/
def Coh (vs : List MVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.H.initN = w'.H.initN → w.H.initC = w'.H.initC) ∧
    (w.H.updN = w'.H.updN → w.H.updC = w'.H.updC) ∧ (w.H.finN = w'.H.finN → w.H.finC = w'.H.finC) ∧
    (w.F.cn = w'.F.cn → w.F.cc = w'.F.cc) ∧ (digName w = digName w' → digest w.F.P = digest w'.F.P)

instance (vs : List MVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

theorem mem_names {vs : List MVar} {w : MVar} (hw : w ∈ vs) :
    w.H.initN ∈ names vs ∧ w.H.updN ∈ names vs ∧ w.H.finN ∈ names vs ∧ w.F.cn ∈ names vs ∧
      digName w ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem mdTabOK_of {vs : List MVar} (hc : Coh vs) {sy : String → Addr}
    (hd : (names vs).Pairwise fun f g => f ≠ g → sy f ≠ sy g) {w : MVar} (hw : w ∈ vs) :
    MdTabOK w.H w.F.cn w.F.cc (digName w) (digest w.F.P) (fnsOf vs) sy := by
  have hn := mem_names hw
  refine ⟨find_name (List.mem_map_of_mem (f := fun w => (w.H.initN, w.H.initC)) hw) ?_ ?_,
    find_name (List.mem_map_of_mem (f := fun w => (w.H.updN, w.H.updC)) hw) ?_ ?_,
    find_name (List.mem_map_of_mem (f := fun w => (w.H.finN, w.H.finC)) hw) ?_ ?_,
    find_name (List.mem_map_of_mem (f := fun w => (w.F.cn, w.F.cc)) hw) ?_ ?_,
    find_name (List.mem_map_of_mem (f := fun w => (digName w, digest w.F.P)) hw) ?_ ?_⟩
  all_goals intro q hq
  all_goals obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq
  · exact pw_ne hd _ (mem_names hw').1 _ hn.1
  · exact (hc w' hw' w hw).1
  · exact pw_ne hd _ (mem_names hw').2.1 _ hn.2.1
  · exact (hc w' hw' w hw).2.1
  · exact pw_ne hd _ (mem_names hw').2.2.1 _ hn.2.2.1
  · exact (hc w' hw' w hw).2.2.1
  · exact pw_ne hd _ (mem_names hw').2.2.2.1 _ hn.2.2.2.1
  · exact (hc w' hw' w hw).2.2.2.1
  · exact pw_ne hd _ (mem_names hw').2.2.2.2 _ hn.2.2.2.2
  · exact (hc w' hw' w hw).2.2.2.2

/-- The words of `w`'s table in the state `s`. -/
theorem words_tableOf (s : State) (w : MVar) : FnTable.words isa s (tableOf w) =
    [s.syms w.H.initN, s.syms w.H.updN, s.syms w.H.finN, s.syms w.F.cn, s.syms (digName w),
      BitVec.ofNat 64 (idx w), BitVec.ofNat 64 w.l.G.len, BitVec.ofNat 64 w.F.P.B, BitVec.ofNat 64 w.F.P.L,
      BitVec.ofNat 64 w.H.S, BitVec.ofNat 64 (bigEndian (idx w))] := rfl

/-- What the table of `w` at `p` holds: its functions' addresses and its
index. -/
theorem held_tableOf {m : Mem} {p : Addr} {s : State} {w : MVar}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (tableOf w))) :
    TabMem w.H s.syms p m ∧ m.readW (p + BitVec.ofNat 64 24) 64 = s.syms w.F.cn ∧
      m.readW (p + BitVec.ofNat 64 32) 64 = s.syms (digName w) ∧
      m.readW (p + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (idx w) := by
  rw [words_tableOf] at h
  have h0 := h 0 (by simp)
  rw [show p + BitVec.ofNat 64 (64 / 8 * 0) = p by simp] at h0
  exact ⟨⟨h0, h 1 (by simp), h 2 (by simp)⟩, h 3 (by simp), h 4 (by simp), h 5 (by simp)⟩

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : Addr} {w : MVar}
    (h : m.readW (p + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (idx w)) :
    Spec.MdHashTable.hashAt 64 m p = some w.l.G := by
  simp only [Spec.MdHashTable.hashAt, Spec.MdHashTable.fns]
  rw [show p + BitVec.ofNat 64 (64 / 8 * 5) = p + BitVec.ofNat 64 40 from rfl, h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.l.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [idx, Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega)]
  exact w.idx

/-- What the proofs need of the table of `w` at `p`, the stack argument `j`
(in `A`, a buffer only read, apart from `kR` and `SC`), itself a buffer only
read apart from them. -/
theorem mdTabS_of {S : State → Addr} {s : State} {j : Nat} (hj : arg j < 2 ^ 15 ∧ arg j % 4 = 0) {p : Addr}
    (harg : s.mem.readW (stackArgAddr s j) 64 = p) {A : Region} (hA : A ∈ s.rd)
    (hAc : A.Contains (stackArgAddr s j) 8) (hAs : Region.Sub ⟨stackArgAddr s j, 8⟩ A)
    (hkA : (kR s).Disjoint A) (hSA : (SC S s).Disjoint A)
    (hT : Sig.tableRegion 64 p 11 ∈ s.rd) (hkT : (kR s).Disjoint (Sig.tableRegion 64 p 11))
    (hST : (SC S s).Disjoint (Sig.tableRegion 64 p 11))
    {vs : List MVar} (hc : Coh vs) (hd : (names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    {w : MVar} (hw : w ∈ vs) (hh : Abi.tableHeld 64 s.mem p (FnTable.words isa s (tableOf w))) :
    MdTabS w.H w.F.cn w.F.cc (digName w) (digest w.F.P) (fnsOf vs) j S s p := by
  obtain ⟨hm, hc3, hd4, -⟩ := held_tableOf hh
  have hk : ∀ k < 11, Region.Sub ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ (Sig.tableRegion 64 p 11) := fun k hk =>
    Offset.sub_base p (by show 8 * k + 8 ≤ 11 * (64 / 8); omega)
  exact ⟨hj, harg, ⟨A, hA, hAc⟩, (hkA.sub_right hAs).symm, (hSA.sub_right hAs).symm,
    fun k hk => ⟨_, hT, Offset.contains_base p (by show 8 * k + 8 ≤ 11 * (64 / 8); omega) (by omega)⟩,
    fun k hk' => (hkT.sub_right (hk k hk')).symm, fun k hk' => (hST.sub_right (hk k hk')).symm, hm, hc3, hd4,
    mdTabOK_of hc hd hw⟩

end VG.Proof.MdHashTable.PPC64LE
