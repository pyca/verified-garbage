module

public import VerifiedGarbage.Proof.MdHashTable.AArch64.Tables
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfT
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# The tables of hash functions RSAES-OAEP and MGF1 take on AArch64

What RSAES-OAEP and MGF1 use of a hash function's table of `MdHash`
(`Proof/MdHashTable/AArch64/Tables.lean`, `tableOf`): the addresses of its
streaming `init`, `update` and `finalize` (its functions 0, 1 and 2), its
index (word 5) and its digest length (word 6) (`held_tableOf`); and the
functions an indirect call of each of those may reach (`fnsOf`).

A function's proof runs the code of whichever of these the table holds
(`TabOK`): the first function of `fnsOf vs` at the address called, which is
the table's function of that name (`tabOK_of`), when the functions of
distinct names are at distinct addresses (as `Abi.withTables` says) and the
variants' functions of the same name have the same code (`Coh`, which the
registration checks).
-/

@[expose] public section

namespace VG.Proof.HashTable.AArch64

open VG VG.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.RsaOaep.AArch64.Table (TabOK TabMem)
open VG.Proof.Bignum (off)
open VG.Proof.HashTable (pw_ne find_name)

/-- The table of `w`'s functions: its table of `MdHash`, whose functions 0,
1 and 2 are the streaming `init`, `update` and `finalize`, and whose words 5
and 6 its index and digest length. -/
abbrev tableOf (w : MdHash) : FnTable := MdHashTable.AArch64.tableOf w

/-- The tables of the variants `vs`. -/
abbrev tables (vs : List MdHash) : List FnTable := MdHashTable.AArch64.tables vs

/-- For each of the streaming functions RSAES-OAEP and MGF1 call through a
table, that function of each of `vs`. -/
def fnsOf (vs : List MdHash) : Fns :=
  ⟨vs.map fun w => (w.H.initN, w.H.initC), vs.map fun w => (w.H.updN, w.H.updC),
    vs.map fun w => (w.H.finN, w.H.finC)⟩

/-- The functions of `tables vs`. -/
abbrev names (vs : List MdHash) : List String := MdHashTable.AArch64.names vs

/-- The variants' streaming functions of the same name have the same code. -/
def Coh (vs : List MdHash) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.H.initN = w'.H.initN → w.H.initC = w'.H.initC) ∧
    (w.H.updN = w'.H.updN → w.H.updC = w'.H.updC) ∧ (w.H.finN = w'.H.finN → w.H.finC = w'.H.finC)

instance (vs : List MdHash) : Decidable (Coh vs) := by unfold Coh; infer_instance

theorem mem_names {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) :
    w.H.initN ∈ names vs ∧ w.H.updN ∈ names vs ∧ w.H.finN ∈ names vs :=
  let h := MdHashTable.AArch64.mem_names hw
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem tabOK_of {vs : List MdHash} (hc : Coh vs) {sy : String → Addr}
    (hd : (names vs).Pairwise fun f g => f ≠ g → sy f ≠ sy g) {w : MdHash} (hw : w ∈ vs) :
    TabOK w.H.stream (fnsOf vs) sy := by
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

/-- What the table of `w` at `p` holds: its streaming functions' addresses,
its index (word 5) and its digest length (word 6). -/
theorem held_tableOf {m : Mem} {p : Addr} {s : State} {w : MdHash}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (tableOf w))) :
    TabMem w.H.stream s.syms p m ∧ m.readW (off p 40) 64 = BitVec.ofNat 64 (MdHashTable.AArch64.idx w) ∧
      m.readW (off p 48) 64 = BitVec.ofNat 64 w.H.D := by
  rw [MdHashTable.AArch64.words_tableOf] at h
  refine ⟨⟨h 0 (by simp), h 1 (by simp), h 2 (by simp)⟩, h 5 (by simp), ?_⟩
  exact (h 6 (by simp)).trans (by rw [w.mgf.len]; rfl)

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : Addr} {w : MdHash}
    (h : m.readW (off p 40) 64 = BitVec.ofNat 64 (MdHashTable.AArch64.idx w)) :
    Spec.MdHashTable.hashAt 64 m p = some w.mgf.G :=
  MdHashTable.AArch64.hashAt_tableOf h

/-! ## Two runs -/

/-- The words of a table, in a state naming its functions' addresses as `t`
does. -/
theorem words_congr {s t : State} (h : s.syms = t.syms) (T : FnTable) :
    FnTable.words isa s T = FnTable.words isa t T := by
  simp only [FnTable.words, h]

/-- The functions of the tables `ts`. -/
def tabFns (ts : List FnTable) : List String := (ts.map (·.fns)).flatten

/-- What the contract says of MGF1's table in two runs, with the memories
`m₁` and `m₂` on entry: in each, one of `ts` at `p` with the functions'
addresses distinct; and the same in both, with their functions at the same
addresses. -/
def TabAgree (ts : List FnTable) (p : Addr) (m₁ m₂ : Mem) (a b : State) : Prop :=
  ((∃ T ∈ ts, Abi.tableHeld 64 m₁ p (T.words isa a)) ∧
      (tabFns ts).Pairwise fun f g => f ≠ g → a.syms f ≠ a.syms g) ∧
    ((∃ T ∈ ts, Abi.tableHeld 64 m₂ p (T.words isa b)) ∧
      (tabFns ts).Pairwise fun f g => f ≠ g → b.syms f ≠ b.syms g) ∧
    (∀ f ∈ tabFns ts, a.syms f = b.syms f) ∧
    ∀ T ∈ ts, (Abi.tableHeld 64 m₁ p (T.words isa a) ↔ Abi.tableHeld 64 m₂ p (T.words isa b))

theorem TabAgree.congr {ts : List FnTable} {p : Addr} {m₁ m₂ : Mem} {a b a' b' : State}
    (h : TabAgree ts p m₁ m₂ a b) (ha : a'.syms = a.syms) (hb : b'.syms = b.syms) :
    TabAgree ts p m₁ m₂ a' b' := by
  simp only [TabAgree, words_congr ha, words_congr hb, ha, hb]
  exact h

end VG.Proof.HashTable.AArch64

namespace VG.Proof.RsaOaep.AArch64

open VG.Proof.Pbkdf2.Md.AArch64 (HashOK MgfLink)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- MGF1's hash function, as a hash function of `MdHash` takes it, is valid. -/
theorem mgf_valid {H : Hash} {hH : HashOK H} (lk : MgfLink H hH) : Proof.Mgf1.Valid lk.G := by
  have hD := hH.sizes.D0
  refine ⟨by rw [lk.len]; exact hD, fun x => ?_⟩
  rw [lk.hash, hH.hash, List.length_take, MdStream.Md.hash, hH.md.digest_length, lk.len]
  have := hH.sizes.DN
  omega_using [this]

end VG.Proof.RsaOaep.AArch64
