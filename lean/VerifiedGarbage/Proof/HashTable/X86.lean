module

public import VerifiedGarbage.Proof.RsaOaep.X86.Mgf
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha1
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha224
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha256
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha512
public import VerifiedGarbage.Spec.HashTable
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset

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
same name have the same code (`Coh`). In the state a function's entry
(`entered`) leaves, a table among its buffers only read holds what MGF1
needs of it (`tabFacts_entered`); and the functions of `fnsOf vs` write `esp`
only through their frames (`fnsOf_noSp`). For the contracts'
satisfiability, a state holding the table of `w` at `0x300000`
(`withTable`).
-/

@[expose] public section

namespace VG.Proof.HashTable.X86

open VG VG.X86
open VG.Impl.RsaOaep.X86 (Fns)
open VG.Proof.RsaOaep.X86 (OHash TabOK TabMem TabFacts)
open VG.Proof.RsaPkcs1Sig.X86 (layOf entered save_eq)
open VG.Proof.HashTable (pw_ne find_name symsOf32 put5w put5w_held put5w_below)

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

/-- The functions of `fnsOf vs`, by kind, write `esp` only through their frames. -/
theorem fnsOf_noSp (vs : List TVar) :
    (∀ q ∈ (fnsOf vs).init, NoSp q.2) ∧ (∀ q ∈ (fnsOf vs).upd, NoSp q.2) ∧ (∀ q ∈ (fnsOf vs).fin, NoSp q.2) := by
  simp only [fnsOf, List.mem_map]
  refine ⟨?_, ?_, ?_⟩ <;> rintro _ ⟨w, -, rfl⟩
  exacts [w.g.ok.initSp, w.g.ok.updSp, w.g.ok.finSp]

section
variable {F C : Nat} {argv : List (BitVec 32)} {ro rw : List Region} {s : State}

/-- A word of a buffer only read, after the entry, as before it. -/
theorem entered_roW (hsp : 16 + F ≤ (s.gpr .esp).toNat) (h : (layOf F argv ro rw s C).Ok (entered F s))
    {R : Region} (hR : R ∈ ro) {a : Addr} (hc : R.Contains a 4) :
    (entered F s).mem.readW a 32 = s.mem.readW a 32 := by
  have hf : Frame [Proof.RsaPkcs1Sig.X86.saveRegion s] s.mem (entered F s).mem := by
    rw [Proof.RsaPkcs1Sig.X86.entered_mem]
    have := pushed_frame (s := s) Proof.RsaPkcs1Sig.X86.pushRegs_noSp
      (by simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega)
    simpa [Impl.RsaPkcs1Sig.X86.savedRegs, below] using this
  refine hf.readW hc (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [save_eq (argv := argv) (ro := ro) (rw := rw) (C := C) hsp]
  exact ((h.stk R (List.mem_append_left _ hR)).sub_left
    (Proof.RsaPkcs1Sig.X86.Lay.sub_stk (by simp only [layOf]; omega))).symm

/-- What MGF1 needs of the table of `w` at `p`, one of the buffers only
read, after the entry. -/
theorem tabFacts_entered (hsp : 16 + F ≤ (s.gpr .esp).toNat) (h : (layOf F argv ro rw s C).Ok (entered F s))
    {p : BitVec 32} (hR : Sig.tableRegion 32 (p.setWidth 64) 5 ∈ ro) (hp : p.toNat + 20 ≤ 2 ^ 32)
    {vs : List TVar} (hc : Coh vs)
    (hd64 : (names vs).Pairwise fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) {w : TVar}
    (hw : w ∈ vs) (hh : Abi.tableHeld 32 s.mem (p.setWidth 64) (FnTable.words isa s (tableOf w))) :
    TabFacts w.g.H (fnsOf vs) p (s.syms w.g.H.initN) (s.syms w.g.H.updN) (s.syms w.g.H.finN) (entered F s) := by
  have sy : (entered F s).syms = s.syms := pushRegs_syms s _
  have e : ∀ o, o + 4 ≤ 20 → (entered F s).mem.readW (VG.X86.addr p o) 32 = s.mem.readW (VG.X86.addr p o) 32 :=
    fun o ho => entered_roW hsp h hR (by
      show (⟨p.setWidth 64, 5 * (32 / 8)⟩ : Region).Contains (VG.X86.addr p o) 4
      rw [addr_eq (by omega)]
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

theorem withTable_arg (s : State) (vs : List TVar) (w : TVar) {j : Nat}
    (hj : (VG.X86.argAddr s j).toNat + 4 ≤ 0x300000) : VG.X86.arg (withTable s vs w) j = VG.X86.arg s j :=
  put5w_below hj _ _ _ _ _

/-- The table of `w`, at `0x300000`. -/
theorem withTable_held (s : State) (vs : List TVar) (w : TVar) :
    Abi.tableHeld 32 (withTable s vs w).mem ((0x300000 : BitVec 32).setWidth 64)
      (FnTable.words isa (withTable s vs w) (tableOf w)) := by
  rw [show ((0x300000 : BitVec 32).setWidth 64) = 0x300000 by decide]
  exact put5w_held (ws := tw vs w) rfl

end VG.Proof.HashTable.X86
