module

public import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Md5
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha1
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha224
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha256
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha384
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512_224
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512_256
public import VerifiedGarbage.Proof.MdHashTable.Arm.Tables
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The tables of hash functions RSAES-OAEP and MGF1 take on ARMv7

As on x86 (`Proof/HashTable/X86.lean`): each hash function (`TVar`) is its
table of `MdHash`'s (`m`, `Proof/MdHashTable/Arm/Tables.lean`) with the same
streaming functions and hash function as RSAES-OAEP on ARMv7 has them (`g`,
`OHash`), one implementation of each (`vars`). What RSAES-OAEP and MGF1 use
of its table (`tableOf`, the table of `MdHash`): the addresses of its
streaming `init`, `update` and `finalize` (its functions 0, 1 and 2), its
index (word 5) and its digest length (word 6), each word 32 bits wide
(`held_tableOf`); an indirect call of the functions of every table
(`fnsOf`) to one of them reaches it (`tabOK_of`), when the functions of
distinct names are at distinct addresses and those of the same name have the
same code (`Coh`). In the state a function's entry (`entered`) leaves, a
table among its buffers only read holds what MGF1 needs of it
(`tabFacts_entered`). For the contracts' satisfiability, a state holding the
table of `w` at `0x300000` (`withTable`).
-/

@[expose] public section

namespace VG.Proof.HashTable.Arm

open VG VG.Arm
open VG.Impl.RsaOaep.Arm (Fns)
open VG.Proof.RsaOaep.Arm (OHash TabOK TabMem TabFacts tA)
open VG.Proof.RsaPkcs1Sig.Arm (layOf entered)
open VG.Proof.HashTable (pw_ne find_name symsOf32 putWs32 putWs32_out putWs32_held)
open VG.Proof.MdHashTable.Arm (MVar md5M sha1M sha224M sha256M sha384M sha512M sha512_224M sha512_256M)

/-- A hash function: its variant as a table of `MdHash` (`m`), and the same
streaming functions and hash function as RSAES-OAEP on ARMv7 has them
(`g`). -/
structure TVar where
  m : MVar
  g : OHash
  st : g.H = m.h.H.md.st
  og : g.G = m.h.G

def md5V : TVar := ⟨md5M, .ofPss Proof.RsaPss.Arm.md5, rfl, rfl⟩
def sha1V : TVar := ⟨sha1M, .ofPss Proof.RsaPss.Arm.sha1, rfl, rfl⟩
def sha224V : TVar := ⟨sha224M, .ofPss Proof.RsaPss.Arm.sha224, rfl, rfl⟩
def sha256V : TVar := ⟨sha256M, .ofPss Proof.RsaPss.Arm.sha256, rfl, rfl⟩
def sha384V : TVar := ⟨sha384M, .ofPss Proof.RsaPss.Arm.sha384, rfl, rfl⟩
def sha512V : TVar := ⟨sha512M, .ofPss Proof.RsaPss.Arm.sha512, rfl, rfl⟩
def sha512_224V : TVar := ⟨sha512_224M, .ofPss Proof.RsaPss.Arm.sha512_224, rfl, rfl⟩
def sha512_256V : TVar := ⟨sha512_256M, .ofPss Proof.RsaPss.Arm.sha512_256, rfl, rfl⟩

/-- Every hash function. -/
def vars : List TVar := [md5V, sha1V, sha224V, sha256V, sha384V, sha512V, sha512_224V, sha512_256V]

/-- The table of `w`: its table of `MdHash`, whose functions 0, 1 and 2 are
the streaming `init`, `update` and `finalize`, and whose words 5 and 6 its
index and digest length. -/
abbrev tableOf (w : TVar) : FnTable := MdHashTable.Arm.tableOf w.m

/-- The tables of `vs`. -/
def tables (vs : List TVar) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List TVar) : Fns :=
  ⟨vs.map fun w => (w.g.H.initN, w.g.H.initC), vs.map fun w => (w.g.H.updN, w.g.H.updC),
    vs.map fun w => (w.g.H.finN, w.g.H.finC)⟩

/-- The functions of `tables vs`. -/
def names (vs : List TVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The functions of the same name have the same code. -/
def Coh (vs : List TVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.g.H.initN = w'.g.H.initN → w.g.H.initC = w'.g.H.initC) ∧
    (w.g.H.updN = w'.g.H.updN → w.g.H.updC = w'.g.H.updC) ∧ (w.g.H.finN = w'.g.H.finN → w.g.H.finC = w'.g.H.finC)

instance (vs : List TVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

theorem mem_names {vs : List TVar} {w : TVar} (hw : w ∈ vs) :
    w.g.H.initN ∈ names vs ∧ w.g.H.updN ∈ names vs ∧ w.g.H.finN ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf, MdHashTable.Arm.tableOf, w.st]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem tabOK_of {vs : List TVar} (hc : Coh vs) {sy : String → BitVec 32}
    (hd64 : (names vs).Pairwise fun f g => f ≠ g → (sy f).setWidth 64 ≠ (sy g).setWidth 64) {w : TVar}
    (hw : w ∈ vs) : TabOK w.g.H (fnsOf vs) sy := by
  have hn := mem_names hw
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

/-- What the table of `w` at `p` holds: its streaming functions' addresses,
its index (word 5) and its digest length (word 6), 32 bits each. -/
theorem held_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 44 ≤ 2 ^ 32) {s : State} {w : TVar}
    (h : Abi.tableHeld 32 m (State.addr p) (FnTable.words isa s (tableOf w))) :
    TabMem w.g.H s.syms p m ∧ m.readW (tA p 20) 32 = BitVec.ofNat 32 (MdHashTable.Arm.idx w.m) ∧
      m.readW (tA p 24) 32 = BitVec.ofNat 32 w.g.H.D := by
  rw [MdHashTable.Arm.words_tableOf] at h
  have a : ∀ i, i < 11 → tA p (4 * i) = State.addr p + BitVec.ofNat 64 (32 / 8 * i) := fun i hi => by
    rw [tA, VG.Arm.addr_add (by omega_using [hp, hi])]
  have e : ∀ i (hi : i < 11), m.readW (tA p (4 * i)) 32 = _ := fun i hi => (a i hi).symm ▸ h i (by simp; omega_using [hi])
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have := e 0 (by decide); simp only [Nat.mul_zero] at this; rw [this, w.st]; simp
  · have := e 1 (by decide); simp only [Nat.mul_one] at this; rw [this, w.st]; simp
  · have := e 2 (by decide); rw [show 4 * 2 = 8 by rfl] at this; rw [this, w.st]; simp
  · have := e 5 (by decide); rw [show 4 * 5 = 20 by rfl] at this; rw [this]; simp
  · have := e 6 (by decide); rw [show 4 * 6 = 24 by rfl] at this; rw [this, ← w.og, w.g.glen]; simp

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 44 ≤ 2 ^ 32) {w : TVar}
    (h : m.readW (tA p 20) 32 = BitVec.ofNat 32 (MdHashTable.Arm.idx w.m)) :
    Spec.MdHashTable.hashAt 32 m (State.addr p) = some w.g.G := by
  rw [w.og]; exact MdHashTable.Arm.hashAt_tableOf hp h

section
variable {F A C : Nat} {argv : List (BitVec 32)} {ro rw : List Region} {s : State}

/-- What MGF1 needs of the table of `w` at `p`, one of the buffers only
read, after the entry. -/
theorem tabFacts_entered (h : (layOf F A argv ro rw s C).Ok (entered F s)) (hsp : 56 + F ≤ s.sp.toNat)
    {p : BitVec 32} (hR : Sig.tableRegion 32 (State.addr p) 11 ∈ ro) (hp : p.toNat + 44 ≤ 2 ^ 32)
    {vs : List TVar} (hc : Coh vs)
    (hd64 : (names vs).Pairwise fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) {w : TVar}
    (hw : w ∈ vs) (hh : Abi.tableHeld 32 s.mem (State.addr p) (FnTable.words isa s (tableOf w))) :
    TabFacts w.g.H (fnsOf vs) p (s.syms w.g.H.initN) (s.syms w.g.H.updN) (s.syms w.g.H.finN) (entered F s) := by
  have sy : (entered F s).syms = s.syms := rfl
  have e : ∀ o, o + 4 ≤ 44 → (entered F s).mem.readW (tA p o) 32 = s.mem.readW (tA p o) 32 :=
    fun o ho => MdHashTable.Arm.entered_roW h hsp hR (by
      show (⟨State.addr p, 11 * (32 / 8)⟩ : Region).Contains (State.addr (p + BitVec.ofNat 32 o)) 4
      rw [VG.Arm.addr_add (by omega_using [hp, ho])]
      exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho]))
  obtain ⟨⟨m0, m1, m2⟩, -, hD⟩ := held_tableOf hp hh
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [sy]; exact tabOK_of hc hd64 hw
  · rw [e 0 (by decide), m0, sy]
  · rw [e 4 (by decide), m1, sy]
  · rw [e 8 (by decide), m2, sy]
  · rw [e 24 (by decide), hD]
  all_goals rw [sy]
end

/-! ## States holding a table, for the contracts' satisfiability -/

/-- The words of `w`'s table, its functions at the addresses `symsOf32` gives
`vs`' functions. -/
def tw (vs : List TVar) (w : TVar) : List (BitVec 64) :=
  (tableOf w).fns.map (fun n => (symsOf32 (names vs) n).setWidth 64) ++ (tableOf w).data

/-- The words of `w`'s table, one by one: a list whose cells unfold without
evaluating the words (`tw_eq`). -/
def twL (vs : List TVar) (w : TVar) : List (BitVec 64) :=
  [(tw vs w).getD 0 0, (tw vs w).getD 1 0, (tw vs w).getD 2 0, (tw vs w).getD 3 0, (tw vs w).getD 4 0,
    (tw vs w).getD 5 0, (tw vs w).getD 6 0, (tw vs w).getD 7 0, (tw vs w).getD 8 0, (tw vs w).getD 9 0,
    (tw vs w).getD 10 0]

theorem tw_eq (vs : List TVar) (w : TVar) : twL vs w = tw vs w := rfl

theorem twL_room (vs : List TVar) (w : TVar) : (0x300000 : Addr).toNat + 4 * (twL vs w).length < 2 ^ 64 := by
  simp only [twL, List.length_cons, List.length_nil]; decide

/-- A state with `s`'s registers and regions, `w`'s table at `0x300000`,
and `vs`' functions at distinct addresses. -/
def withTable (s : State) (vs : List TVar) (w : TVar) : State :=
  { s with mem := putWs32 s.mem 0x300000 (twL vs w), syms := symsOf32 (names vs) }

/-- `w`'s table at `0x300000`, in any memory `putWs32` writes it to, with
`vs`' functions at the addresses `symsOf32` gives them: a statement about
the memory as the contracts unfold it, which `exact` matches without
unfolding `putWs32`. -/
theorem held_twL (m : Mem) (vs : List TVar) (w : TVar) {st : State} (hs : st.syms = symsOf32 (names vs)) :
    Abi.tableHeld 32 (putWs32 m 0x300000 (twL vs w)) (State.addr (0x300000 : BitVec 32))
      (FnTable.words isa st (tableOf w)) := by
  rw [show State.addr (0x300000 : BitVec 32) = 0x300000 by decide]
  have h := putWs32_held (m := m) (p := 0x300000) (ws := twL vs w) (twL_room vs w)
  rw [tw_eq] at h
  have e : FnTable.words isa st (tableOf w) = tw vs w := by
    simp only [FnTable.words, tw]; rw [hs]
  rwa [e]

/-- The table of `w`, at `0x300000`. -/
theorem withTable_held (s : State) (vs : List TVar) (w : TVar) :
    Abi.tableHeld 32 (withTable s vs w).mem (State.addr (0x300000 : BitVec 32))
      (FnTable.words isa (withTable s vs w) (tableOf w)) :=
  held_twL _ _ _ rfl

/-- Below `0x300000`, a word as in `s`. -/
theorem withTable_below (s : State) (vs : List TVar) (w : TVar) {a : Addr} (ha : a.toNat + 4 ≤ 0x300000) :
    (withTable s vs w).mem.readW a 32 = s.mem.readW a 32 :=
  putWs32_out (a := a) (.inl (by simpa using ha)) (twL_room vs w) (by omega_using [ha])

end VG.Proof.HashTable.Arm
