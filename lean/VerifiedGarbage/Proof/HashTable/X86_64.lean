module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
public import VerifiedGarbage.Spec.HashTable
public import VerifiedGarbage.Proof.HashTable.Basic

/-!
# Tables of the interface `Hash` on x86-64

The table of a hash function's variant (`tableOf`): the addresses of its
streaming `init`, `update` and `finalize`, then its data
(`Spec.HashTable.dataOf`); the tables of a list of variants (`tables`, one
for each), which a function taking a table of `Hash` lists as those it may
be given; and the functions an indirect call of each of a table's functions
may reach (`fnsOf`).

A function's proof runs the code of whichever of these the table holds
(`TabOK`): the first function of `fnsOf vs` at the address called, which is
the table's function of that name (`tabOK_of`), when the functions of
distinct names are at distinct addresses (as `Abi.withTables` says) and the
variants' functions of the same name have the same code (`Coh`, which the
registration checks, `Coh.decide`).
-/

@[expose] public section

namespace VG.Proof.HashTable.X86_64

open VG VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.RsaOaep.X86_64.Table (TabOK TabMem)
open VG.Proof.Bignum (off)
open VG.Proof.HashTable (pw_ne find_name)

deriving instance DecidableEq for VG.Code

/-- The table of `w`'s streaming functions, `VG_HASH_<HASH><SUFFIX>`. -/
def tableOf (w : MdHash) : FnTable where
  name := s!"VG_HASH_{w.mgf.G.rust.toUpper}{w.suffix.toUpper}"
  iface := Spec.HashTable.iface
  fns := [w.H.initN, w.H.updN, w.H.finN]
  data := Spec.HashTable.dataOf w.mgf.G

/-- The tables of the variants `vs`. -/
def tables (vs : List MdHash) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List MdHash) : Fns :=
  ⟨vs.map fun w => (w.H.initN, w.H.initC), vs.map fun w => (w.H.updN, w.H.updC),
    vs.map fun w => (w.H.finN, w.H.finC)⟩

/-- The functions of `tables vs`. -/
def names (vs : List MdHash) : List String := ((tables vs).map (·.fns)).flatten

/-- The variants' functions of the same name have the same code. -/
def Coh (vs : List MdHash) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.H.initN = w'.H.initN → w.H.initC = w'.H.initC) ∧
    (w.H.updN = w'.H.updN → w.H.updC = w'.H.updC) ∧ (w.H.finN = w'.H.finN → w.H.finC = w'.H.finC)

instance (vs : List MdHash) : Decidable (Coh vs) := by unfold Coh; infer_instance

theorem mem_names {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) :
    w.H.initN ∈ names vs ∧ w.H.updN ∈ names vs ∧ w.H.finN ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

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

/-- What the pieces need of the functions an indirect call may reach. -/
theorem fnsGood_of (vs : List MdHash) : Proof.RsaOaep.X86_64.Table.FnsGood (fnsOf vs).init ∧
    Proof.RsaOaep.X86_64.Table.FnsGood (fnsOf vs).upd ∧ Proof.RsaOaep.X86_64.Table.FnsGood (fnsOf vs).fin := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩ <;> obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq <;>
    have g := Proof.RsaOaep.X86_64.HGood.of w.ok w.K
  · exact ⟨g.init, g.initD⟩
  · exact ⟨g.upd, g.updD⟩
  · exact ⟨g.fin, g.finD⟩

/-- What the table of `w` at `p` holds: its functions' addresses, its index
and its digest length. -/
theorem held_tableOf {m : Mem} {p : Addr} {s : State} {w : MdHash}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (tableOf w))) :
    TabMem w.H.stream s.syms p m ∧ m.readW (off p 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G) ∧
      m.readW (off p 32) 64 = BitVec.ofNat 64 w.H.D := by
  have hw : FnTable.words isa s (tableOf w) = [s.syms w.H.initN, s.syms w.H.updN, s.syms w.H.finN,
      BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G), BitVec.ofNat 64 w.mgf.G.len] := rfl
  rw [hw] at h
  refine ⟨⟨h 0 (by simp), h 1 (by simp), h 2 (by simp)⟩, h 3 (by simp), ?_⟩
  exact (h 4 (by simp)).trans (by rw [w.mgf.len]; rfl)

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : Addr} {w : MdHash}
    (h : m.readW (off p 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)) :
    Spec.HashTable.hashAt 64 m p = some w.mgf.G := by
  have hm := w.mgf.mem
  simp only [Spec.HashTable.hashAt, Spec.HashTable.fns]
  rw [show p + BitVec.ofNat 64 (8 * 3) = off p 24 from rfl, h]
  simp only [Proof.Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e <;> rw [e] <;> rfl

end VG.Proof.HashTable.X86_64
