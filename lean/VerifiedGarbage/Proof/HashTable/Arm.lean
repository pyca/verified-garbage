module

public import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha1
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha224
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha256
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha384
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512_224
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512_256
public import VerifiedGarbage.Spec.HashTable
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Tables of the interface `Hash` on ARMv7

As on x86 (`Proof/HashTable/X86.lean`), with the hash functions as
RSAES-OAEP on ARMv7 has them (`OHash`), one implementation of each (`vars`):
the table of a hash function (`tableOf`) holds the addresses of its
streaming `init`, `update` and `finalize`, then its data
(`Spec.HashTable.dataOf`), each word 32 bits wide; an indirect call of the
functions of every table (`fnsOf`) to one of them reaches it (`tabOK_of`),
when the functions of distinct names are at distinct addresses and those of
the same name have the same code (`Coh`). In the state a function's entry
(`entered`) leaves, a table among its buffers only read holds what MGF1
needs of it (`tabFacts_entered`). For the contracts' satisfiability, a state
holding the table of `w` at `0x300000` (`withTable`).
-/

@[expose] public section

namespace VG.Proof.HashTable.Arm

open VG VG.Arm
open VG.Impl.RsaOaep.Arm (Fns)
open VG.Proof.RsaOaep.Arm (OHash TabOK TabMem TabFacts tA)
open VG.Proof.RsaPkcs1Sig.Arm (layOf entered)
open VG.Proof.HashTable (pw_ne find_name symsOf32 put5w put5w_held put5w_below)

/-- A hash function, with its place in `Spec.Mgf1.hashes`. -/
structure TVar where
  g : OHash
  idx : Spec.Mgf1.hashes[Spec.HashTable.index g.G]? = some g.G

def sha1V : TVar := ⟨.ofPss Proof.RsaPss.Arm.sha1, rfl⟩
def sha224V : TVar := ⟨.ofPss Proof.RsaPss.Arm.sha224, rfl⟩
def sha256V : TVar := ⟨.ofPss Proof.RsaPss.Arm.sha256, rfl⟩
def sha384V : TVar := ⟨.ofPss Proof.RsaPss.Arm.sha384, rfl⟩
def sha512V : TVar := ⟨.ofPss Proof.RsaPss.Arm.sha512, rfl⟩
def sha512_224V : TVar := ⟨.ofPss Proof.RsaPss.Arm.sha512_224, rfl⟩
def sha512_256V : TVar := ⟨.ofPss Proof.RsaPss.Arm.sha512_256, rfl⟩

/-- Every hash function. -/
def vars : List TVar := [sha1V, sha224V, sha256V, sha384V, sha512V, sha512_224V, sha512_256V]

/-- The table of `w`'s streaming functions, `VG_HASH_<HASH>`. -/
def tableOf (w : TVar) : FnTable where
  name := s!"VG_HASH_{w.g.G.rust.toUpper}"
  iface := Spec.HashTable.iface
  fns := [w.g.H.initN, w.g.H.updN, w.g.H.finN]
  data := Spec.HashTable.dataOf w.g.G

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
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

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

/-- What the table of `w` at `p` holds: its functions' addresses, its index
and its digest length, 32 bits each. -/
theorem held_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 20 ≤ 2 ^ 32) {s : State} {w : TVar}
    (h : Abi.tableHeld 32 m (State.addr p) (FnTable.words isa s (tableOf w))) :
    TabMem w.g.H s.syms p m ∧ m.readW (tA p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.g.G) ∧
      m.readW (tA p 16) 32 = BitVec.ofNat 32 w.g.H.D := by
  have hw : FnTable.words isa s (tableOf w) = [(s.syms w.g.H.initN).setWidth 64, (s.syms w.g.H.updN).setWidth 64,
      (s.syms w.g.H.finN).setWidth 64, BitVec.ofNat 64 (Spec.HashTable.index w.g.G),
      BitVec.ofNat 64 w.g.G.len] := rfl
  rw [hw] at h
  have a : ∀ i, i < 5 → tA p (4 * i) = State.addr p + BitVec.ofNat 64 (32 / 8 * i) := fun i hi => by
    rw [tA, VG.Arm.addr_add (by omega)]
  have e : ∀ i (hi : i < 5), m.readW (tA p (4 * i)) 32 = _ := fun i hi => (a i hi).symm ▸ h i (by simp; omega)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have := e 0 (by decide); simp only [Nat.mul_zero] at this; rw [this]; simp
  · have := e 1 (by decide); simp only [Nat.mul_one] at this; rw [this]; simp
  · have := e 2 (by decide); rw [show 4 * 2 = 8 by rfl] at this; rw [this]; simp
  · have := e 3 (by decide); rw [show 4 * 3 = 12 by rfl] at this; rw [this]; simp
  · have := e 4 (by decide); rw [show 4 * 4 = 16 by rfl] at this; rw [this, w.g.glen]; simp

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 20 ≤ 2 ^ 32) {w : TVar}
    (h : m.readW (tA p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.g.G)) :
    Spec.HashTable.hashAt 32 m (State.addr p) = some w.g.G := by
  simp only [Spec.HashTable.hashAt, Spec.HashTable.fns]
  rw [show State.addr p + BitVec.ofNat 64 (32 / 8 * 3) = tA p 12 by rw [tA, VG.Arm.addr_add (by omega)], h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.g.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega)]
  exact w.idx

section
variable {F A C : Nat} {argv : List (BitVec 32)} {ro rw : List Region} {s : State}

/-- A word of a buffer only read, after the entry, as before it. -/
theorem entered_roW (h : (layOf F A argv ro rw s C).Ok (entered F s)) (hsp : 56 + F ≤ s.sp.toNat)
    {R : Region} (hR : R ∈ ro) {a : Addr} (hc : R.Contains a 4) :
    (entered F s).mem.readW a 32 = s.mem.readW a 32 := by
  have hpush : Frame [VG.Arm.FrameStack.belowA s.sp 56] s.mem (entered F s).mem :=
    VG.Arm.FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega)
  refine hpush.readW hc (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint _ ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩
  rw [← Proof.RsaPkcs1Sig.Arm.layOf_PUSH (A := A) (C := C) (argv := argv) (ro := ro) (rw := rw) hsp]
  exact ((h.stk R (List.mem_append_left _ hR)).sub_left (Proof.RsaPkcs1Sig.Arm.Lay.sub_stk (Nat.le_refl _))).symm

/-- What MGF1 needs of the table of `w` at `p`, one of the buffers only
read, after the entry. -/
theorem tabFacts_entered (h : (layOf F A argv ro rw s C).Ok (entered F s)) (hsp : 56 + F ≤ s.sp.toNat)
    {p : BitVec 32} (hR : Sig.tableRegion 32 (State.addr p) 5 ∈ ro) (hp : p.toNat + 20 ≤ 2 ^ 32)
    {vs : List TVar} (hc : Coh vs)
    (hd64 : (names vs).Pairwise fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) {w : TVar}
    (hw : w ∈ vs) (hh : Abi.tableHeld 32 s.mem (State.addr p) (FnTable.words isa s (tableOf w))) :
    TabFacts w.g.H (fnsOf vs) p (s.syms w.g.H.initN) (s.syms w.g.H.updN) (s.syms w.g.H.finN) (entered F s) := by
  have sy : (entered F s).syms = s.syms := rfl
  have e : ∀ o, o + 4 ≤ 20 → (entered F s).mem.readW (tA p o) 32 = s.mem.readW (tA p o) 32 :=
    fun o ho => entered_roW h hsp hR (by
      show (⟨State.addr p, 5 * (32 / 8)⟩ : Region).Contains (State.addr (p + BitVec.ofNat 32 o)) 4
      rw [VG.Arm.addr_add (by omega)]
      exact Offset.contains_base _ (by omega) (by omega))
  obtain ⟨⟨m0, m1, m2⟩, -, hD⟩ := held_tableOf hp hh
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [sy]; exact tabOK_of hc hd64 hw
  · rw [e 0 (by decide), m0, sy]
  · rw [e 4 (by decide), m1, sy]
  · rw [e 8 (by decide), m2, sy]
  · rw [e 16 (by decide), hD]
  all_goals rw [sy]
end

/-! ## States holding a table, for the contracts' satisfiability -/

/-- The words of `w`'s table, at the addresses `symsOf32` gives `vs`' functions. -/
def tw (vs : List TVar) (w : TVar) : List (BitVec 64) :=
  [(symsOf32 (names vs) w.g.H.initN).setWidth 64, (symsOf32 (names vs) w.g.H.updN).setWidth 64,
    (symsOf32 (names vs) w.g.H.finN).setWidth 64, BitVec.ofNat 64 (Spec.HashTable.index w.g.G),
    BitVec.ofNat 64 w.g.G.len]

/-- A state with `s`'s registers and regions, `w`'s table at `0x300000`,
and `vs`' functions at distinct addresses. -/
def withTable (s : State) (vs : List TVar) (w : TVar) : State :=
  { s with
    mem := put5w s.mem 0x300000 (((tw vs w).getD 0 0).setWidth 32) (((tw vs w).getD 1 0).setWidth 32)
      (((tw vs w).getD 2 0).setWidth 32) (((tw vs w).getD 3 0).setWidth 32) (((tw vs w).getD 4 0).setWidth 32)
    syms := symsOf32 (names vs) }

/-- The table of `w`, at `0x300000`. -/
theorem withTable_held (s : State) (vs : List TVar) (w : TVar) :
    Abi.tableHeld 32 (withTable s vs w).mem (State.addr (0x300000 : BitVec 32))
      (FnTable.words isa (withTable s vs w) (tableOf w)) := by
  rw [show State.addr (0x300000 : BitVec 32) = 0x300000 by decide]
  exact put5w_held (ws := tw vs w) rfl

/-- Below `0x300000`, a word as in `s`. -/
theorem withTable_below (s : State) (vs : List TVar) (w : TVar) {a : Addr} (ha : a.toNat + 4 ≤ 0x300000) :
    (withTable s vs w).mem.readW a 32 = s.mem.readW a 32 :=
  put5w_below ha _ _ _ _ _

end VG.Proof.HashTable.Arm
