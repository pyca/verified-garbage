module

public import VerifiedGarbage.Proof.RsaPss.X86.CtTab
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Spec.MdHashTable
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.HashTable.X86
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Tables of the interface `MdHash` on x86

As on x86-64 (`Proof/MdHashTable/X86_64/Tables.lean`), with the hash
functions as RSASSA-PSS on x86 has them (`PssHash`), each with the suffix and
the CPU features of its variant (`MVar`). The table of a variant (`tableOf`)
holds the addresses of its streaming `init`, `update` and `finalize`, its
compression function and the digest of its hash value
(`Impl/MdHashTable/X86.lean`, named by the family of the streaming code,
`digName`, whose digest code the variants of a family share), then its data,
each word 32 bits wide; an indirect call of the functions of every variant
(`fnsOf`) to one of them reaches it (`hfacts_of`), when the functions of
distinct names are at distinct addresses and the variants' functions of the
same name have the same code (`Coh`). In the state a function's entry
(`entered`) leaves, a table among its buffers only read holds what hashing
needs of it (`hFacts_entered`), and its index (`idx_entered`).
-/

-- separate module: the interface's tables, which signing, verification and their registrations all use

@[expose] public section

namespace VG.Proof.MdHashTable.X86

open VG VG.X86
open VG.Impl.RsaPss.X86 (MdFns)
open VG.Proof.RsaPss.X86 (PssHash HFacts)
open VG.Proof.RsaPkcs1Sig.X86 (layOf entered save_eq)
open VG.Proof.HashTable (pw_ne find_name)

/-- A variant of a hash function: the hash function, the suffix of its
functions' names and the CPU features it needs, and its place in
`Spec.Mgf1.hashes`. -/
structure MVar where
  h : PssHash
  suffix : String
  features : List String
  idx : Spec.Mgf1.hashes[Spec.HashTable.index h.G]? = some h.G

/-- The index of `w`'s hash function in `Mgf1.hashes`. -/
def idx (w : MVar) : Nat := Spec.HashTable.index w.h.G

/-- The name of the family of the streaming code of the hash function of
index `i`, whose digest code its variants share. -/
def family : Nat → String
  | 0 => "md5" | 1 => "sha1" | 2 | 3 => "sha256" | _ => "sha512"

/-- The name of `w`'s digest. -/
def digName (w : MVar) : String := s!"vg_{family (idx w)}_state_digest"

/-- 1 if the hash function of index `i` is big-endian (all but MD5). -/
def bigEndian (i : Nat) : Nat := if i = 0 then 0 else 1

/-- The table of `w`'s functions, `VG_MD_HASH_<HASH><SUFFIX>`. -/
def tableOf (w : MVar) : FnTable where
  name := s!"VG_MD_HASH_{w.h.G.rust.toUpper}{w.suffix.toUpper}"
  iface := Spec.MdHashTable.iface
  fns := [w.h.H.st.initN, w.h.H.st.updN, w.h.H.st.finN, w.h.H.compN, digName w]
  data := Spec.MdHashTable.dataOf w.h.G ++
    [BitVec.ofNat 64 w.h.H.B, BitVec.ofNat 64 w.h.H.L, BitVec.ofNat 64 w.h.H.S, BitVec.ofNat 64 (bigEndian (idx w))]

/-- The tables of the variants `vs`. -/
def tables (vs : List MVar) : List FnTable := vs.map tableOf

/-- For each of the functions PSS calls through a table, that function of
each of `vs`. -/
def fnsOf (vs : List MVar) : MdFns :=
  ⟨vs.map fun w => (w.h.H.st.initN, w.h.H.st.initC), vs.map fun w => (w.h.H.compN, w.h.H.compC),
    vs.map fun w => (digName w, Impl.MdHashTable.X86.digest w.h.H.out)⟩

/-- The functions of `tables vs`. -/
def names (vs : List MVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The variants' functions of the same name have the same code. -/
def Coh (vs : List MVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.h.H.st.initN = w'.h.H.st.initN → w.h.H.st.initC = w'.h.H.st.initC) ∧
    (w.h.H.compN = w'.h.H.compN → w.h.H.compC = w'.h.H.compC) ∧
    (digName w = digName w' → w.h.H.out = w'.h.H.out)

instance (vs : List MVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

/-- The sizes of `w`'s hash function are those `sizesOf` gives its index,
and its index is one of `idxs`. -/
def Shape (w : MVar) : Prop :=
  idx w ∈ Impl.RsaPss.X86.idxs ∧ Impl.RsaPss.X86.sizes w.h.H = Impl.RsaPss.X86.sizesOf (idx w)

instance (w : MVar) : Decidable (Shape w) := by unfold Shape; infer_instance

theorem mem_names {vs : List MVar} {w : MVar} (hw : w ∈ vs) :
    w.h.H.st.initN ∈ names vs ∧ w.h.H.st.updN ∈ names vs ∧ w.h.H.st.finN ∈ names vs ∧ w.h.H.compN ∈ names vs ∧
      digName w ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- The words of `w`'s table in the state `s`. -/
theorem words_tableOf (s : State) (w : MVar) : FnTable.words isa s (tableOf w) =
    [(s.syms w.h.H.st.initN).setWidth 64, (s.syms w.h.H.st.updN).setWidth 64, (s.syms w.h.H.st.finN).setWidth 64,
      (s.syms w.h.H.compN).setWidth 64, (s.syms (digName w)).setWidth 64, BitVec.ofNat 64 (idx w),
      BitVec.ofNat 64 w.h.G.len, BitVec.ofNat 64 w.h.H.B, BitVec.ofNat 64 w.h.H.L, BitVec.ofNat 64 w.h.H.S,
      BitVec.ofNat 64 (bigEndian (idx w))] := rfl

/-- What the table of `w` at `p` holds: the addresses of its `init`,
compression function and digest, and its index. -/
theorem held_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 44 ≤ 2 ^ 32) {s : State} {w : MVar}
    (h : Abi.tableHeld 32 m (p.setWidth 64) (FnTable.words isa s (tableOf w))) :
    m.readW (VG.X86.addr p (4 * 0)) 32 = s.syms w.h.H.st.initN ∧
      m.readW (VG.X86.addr p (4 * 3)) 32 = s.syms w.h.H.compN ∧
      m.readW (VG.X86.addr p (4 * 4)) 32 = s.syms (digName w) ∧
      m.readW (VG.X86.addr p 20) 32 = BitVec.ofNat 32 (idx w) := by
  rw [words_tableOf] at h
  have a : ∀ i, i < 11 → VG.X86.addr p (4 * i) = p.setWidth 64 + BitVec.ofNat 64 (32 / 8 * i) := fun i hi => by
    rw [addr_eq (by omega)]
  have e : ∀ i (hi : i < 11), m.readW (VG.X86.addr p (4 * i)) 32 = _ := fun i hi =>
    (a i hi).symm ▸ h i (by simp; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := e 0 (by decide); rw [this]; simp
  · have := e 3 (by decide); rw [this]; simp
  · have := e 4 (by decide); rw [this]; simp
  · have := e 5 (by decide); rw [show 4 * 5 = 20 by rfl] at this; rw [this]; simp

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 44 ≤ 2 ^ 32) {w : MVar}
    (h : m.readW (VG.X86.addr p 20) 32 = BitVec.ofNat 32 (idx w)) :
    Spec.MdHashTable.hashAt 32 m (p.setWidth 64) = some w.h.G := by
  simp only [Spec.MdHashTable.hashAt, Spec.MdHashTable.fns]
  rw [show p.setWidth 64 + BitVec.ofNat 64 (32 / 8 * 5) = VG.X86.addr p 20 by rw [addr_eq (by omega)], h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.h.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [idx, Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega)]
  exact w.idx

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem hfacts_of {vs : List MVar} (hc : Coh vs) {σ : State}
    (hd64 : (names vs).Pairwise fun f g => f ≠ g → (σ.syms f).setWidth 64 ≠ (σ.syms g).setWidth 64) {w : MVar}
    (hw : w ∈ vs) {p : BitVec 32}
    (h0 : σ.mem.readW (VG.X86.addr p (4 * 0)) 32 = σ.syms w.h.H.st.initN)
    (h3 : σ.mem.readW (VG.X86.addr p (4 * 3)) 32 = σ.syms w.h.H.compN)
    (h4 : σ.mem.readW (VG.X86.addr p (4 * 4)) 32 = σ.syms (digName w)) :
    HFacts w.h (digName w) (fnsOf vs) p (σ.syms w.h.H.st.initN) (σ.syms w.h.H.compN) (σ.syms (digName w)) σ := by
  have hn := mem_names hw
  refine ⟨find_name (sy := fun n => (σ.syms n).setWidth 64) (List.mem_map_of_mem hw) ?_ ?_,
    find_name (sy := fun n => (σ.syms n).setWidth 64) (List.mem_map_of_mem hw) ?_ ?_,
    find_name (sy := fun n => (σ.syms n).setWidth 64)
      (List.mem_map_of_mem (f := fun w => (digName w, Impl.MdHashTable.X86.digest w.h.H.out)) hw) ?_ ?_,
    h0, h3, h4, rfl, rfl, rfl⟩
  all_goals intro q hq
  all_goals obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq
  · exact pw_ne hd64 _ (mem_names hw').1 _ hn.1
  · exact (hc w' hw' w hw).1
  · exact pw_ne hd64 _ (mem_names hw').2.2.2.1 _ hn.2.2.2.1
  · exact (hc w' hw' w hw).2.1
  · exact pw_ne hd64 _ (mem_names hw').2.2.2.2 _ hn.2.2.2.2
  · intro e; rw [(hc w' hw' w hw).2.2 e]

section
variable {F C : Nat} {argv : List (BitVec 32)} {ro rw : List Region} {s : State}

/-- A word of a buffer only read, after the entry, as before it. -/
theorem entered_roW (hsp : 16 + F ≤ (s.gpr .esp).toNat) (h : (layOf F argv ro rw s C).Ok (entered F s))
    {R : Region} (hR : R ∈ ro) {a : Addr} (hc : R.Contains a 4) :
    (entered F s).mem.readW a 32 = s.mem.readW a 32 :=
  Proof.HashTable.X86.entered_roW hsp h hR hc

/-- The words of the table of `w` at `p`, one of the buffers only read,
after the entry. -/
theorem held_entered (hsp : 16 + F ≤ (s.gpr .esp).toNat) (h : (layOf F argv ro rw s C).Ok (entered F s))
    {p : BitVec 32} (hR : Sig.tableRegion 32 (p.setWidth 64) 11 ∈ ro) (hp : p.toNat + 44 ≤ 2 ^ 32) {w : MVar}
    (hh : Abi.tableHeld 32 s.mem (p.setWidth 64) (FnTable.words isa s (tableOf w))) :
    (entered F s).mem.readW (VG.X86.addr p (4 * 0)) 32 = (entered F s).syms w.h.H.st.initN ∧
      (entered F s).mem.readW (VG.X86.addr p (4 * 3)) 32 = (entered F s).syms w.h.H.compN ∧
      (entered F s).mem.readW (VG.X86.addr p (4 * 4)) 32 = (entered F s).syms (digName w) ∧
      (entered F s).mem.readW (VG.X86.addr p 20) 32 = BitVec.ofNat 32 (idx w) := by
  have sy : (entered F s).syms = s.syms := pushRegs_syms s _
  have e : ∀ o, o + 4 ≤ 44 → (entered F s).mem.readW (VG.X86.addr p o) 32 = s.mem.readW (VG.X86.addr p o) 32 :=
    fun o ho => entered_roW hsp h hR (by
      show (⟨p.setWidth 64, 11 * (32 / 8)⟩ : Region).Contains (VG.X86.addr p o) 4
      rw [addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega))
  obtain ⟨m0, m3, m4, m5⟩ := held_tableOf hp hh
  rw [sy, e _ (by decide), e _ (by decide), e _ (by decide), e _ (by decide)]
  exact ⟨m0, m3, m4, m5⟩
end

end VG.Proof.MdHashTable.X86
