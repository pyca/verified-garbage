module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Impl.Mgf1.X86_64.Table
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.Proof.HashTable.Basic

/-!
# Tables of the interface `Hmac` on x86-64

The table of a hash function's variant (`tableOf`, `VG_HMAC_<HASH><SUFFIX>`):
the addresses of HMAC's `init` and `finalize` and of the streaming `update`,
in the forms that take their working space as an argument (`_scratch`, in
`r8`): HMAC's `init` for a key of any length (`Hash.hmacInitAny`), the
streaming `update` (`Hash.updC`) and HMAC's `finalize` (`Hash.hmacFin`); then its data
(`Spec.HmacTable.dataOf`: the hash function's index in `Mgf1.hashes`, its
digest length and HMAC's block size); the tables of a list of variants
(`tables`, one for each), which a function taking a table of `Hmac` lists
as those it may be given; and the functions an indirect call of each of a
table's functions may reach (`fnsOf`).

A function's proof runs the code of whichever of these the table holds
(`TabOK`): the first function of `fnsOf vs` at the address called, which is
the table's function of that name (`tabOK_of`), when the functions of
distinct names are at distinct addresses (as `Abi.withTables` says) and the
variants' functions of the same name have the same code (`Coh`, which the
registration checks). `held_tableOf` reads a table's words, and
`hashAt_tableOf` the hash function it names.
-/

@[expose] public section

namespace VG.Proof.HmacTable.X86_64

open VG VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.HashTable (pw_ne find_name)

/-- The table of `w`'s HMAC, `VG_HMAC_<HASH><SUFFIX>`. -/
def tableOf (w : MdHash) : FnTable where
  name := s!"VG_HMAC_{w.mgf.G.rust.toUpper}{w.suffix.toUpper}"
  iface := Spec.HmacTable.iface
  fns := [w.H.hmacInitAnyN, w.H.updN, w.H.hmacFinN]
  data := Spec.HmacTable.dataOf w.mgf.G

/-- The tables of the variants `vs`. -/
def tables (vs : List MdHash) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List MdHash) : Fns :=
  ⟨vs.map fun w => (w.H.hmacInitAnyN, w.H.hmacInitAny), vs.map fun w => (w.H.updN, w.H.updC),
    vs.map fun w => (w.H.hmacFinN, w.H.hmacFin)⟩

/-- The functions of `tables vs`. -/
def names (vs : List MdHash) : List String := ((tables vs).map (·.fns)).flatten

/-- The variants' functions of the same name have the same code. -/
def Coh (vs : List MdHash) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.H.hmacInitAnyN = w'.H.hmacInitAnyN → w.H.hmacInitAny = w'.H.hmacInitAny) ∧
    (w.H.updN = w'.H.updN → w.H.updC = w'.H.updC) ∧ (w.H.hmacFinN = w'.H.hmacFinN → w.H.hmacFin = w'.H.hmacFin)

instance (vs : List MdHash) : Decidable (Coh vs) := by unfold Coh; infer_instance

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `H`'s HMAC functions reaches it. -/
structure TabOK (H : Hash) (f : Fns) (sy : String → Addr) : Prop where
  i : f.init.find? (fun q => sy q.1 == sy H.hmacInitAnyN) = some (H.hmacInitAnyN, H.hmacInitAny)
  u : f.upd.find? (fun q => sy q.1 == sy H.updN) = some (H.updN, H.updC)
  f : f.fin.find? (fun q => sy q.1 == sy H.hmacFinN) = some (H.hmacFinN, H.hmacFin)

/-- At `p` in `m`, the addresses `sy` gives `H`'s HMAC `init`, the streaming
`update` and HMAC's `finalize`. -/
def TabMem (H : Hash) (sy : String → Addr) (p : Addr) (m : Mem) : Prop :=
  m.readW (p + BitVec.ofNat 64 0) 64 = sy H.hmacInitAnyN ∧ m.readW (p + BitVec.ofNat 64 8) 64 = sy H.updN ∧
    m.readW (p + BitVec.ofNat 64 16) 64 = sy H.hmacFinN

theorem mem_names {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) :
    w.H.hmacInitAnyN ∈ names vs ∧ w.H.updN ∈ names vs ∧ w.H.hmacFinN ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem tabOK_of {vs : List MdHash} (hc : Coh vs) {sy : String → Addr}
    (hd : (names vs).Pairwise fun f g => f ≠ g → sy f ≠ sy g) {w : MdHash} (hw : w ∈ vs) :
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

/-- The words of the table of `w`. -/
theorem words_tableOf (s : State) (w : MdHash) :
    FnTable.words isa s (tableOf w) = [s.syms w.H.hmacInitAnyN, s.syms w.H.updN, s.syms w.H.hmacFinN,
      BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G), BitVec.ofNat 64 w.mgf.G.len,
      BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G)] := rfl

/-- What the table of `w` at `p` holds: its functions' addresses, its index,
its digest length and HMAC's block size. -/
theorem held_tableOf {m : Mem} {p : Addr} {s : State} {w : MdHash}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (tableOf w))) :
    TabMem w.H s.syms p m ∧
      m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G) ∧
      m.readW (p + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
      m.readW (p + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G) := by
  rw [words_tableOf] at h
  refine ⟨⟨h 0 (by simp), h 1 (by simp), h 2 (by simp)⟩, h 3 (by simp), ?_, h 5 (by simp)⟩
  exact (h 4 (by simp)).trans (by rw [w.mgf.len]; rfl)

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : Addr} {w : MdHash}
    (h : m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)) :
    Spec.HmacTable.hashAt 64 m p = some w.mgf.G := by
  have hm := w.mgf.mem
  simp only [Spec.HmacTable.hashAt, Spec.HmacTable.fns]
  rw [show p + BitVec.ofNat 64 (64 / 8 * 3) = p + BitVec.ofNat 64 24 from rfl, h]
  simp only [Proof.Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e <;> rw [e] <;> rfl

/-! ## A state with a table

The words of a table at `0x300000`, and the functions of a list of variants
at distinct addresses: what proofs that a contract taking a table is
satisfiable build their state from. -/

open VG.Proof.HashTable (symsOf symsOf_distinct readW_sep64)

/-- Six words at `p`. -/
def put6 (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 64) : Mem :=
  (((((m.writeW (p + BitVec.ofNat 64 (8 * 0)) w₀).writeW (p + BitVec.ofNat 64 (8 * 1)) w₁).writeW
    (p + BitVec.ofNat 64 (8 * 2)) w₂).writeW (p + BitVec.ofNat 64 (8 * 3)) w₃).writeW
    (p + BitVec.ofNat 64 (8 * 4)) w₄).writeW (p + BitVec.ofNat 64 (8 * 5)) w₅

/-- The table `put6` writes at `0x300000`. -/
theorem put6_held {m : Mem} {ws : List (BitVec 64)} (hl : ws.length = 6) :
    Abi.tableHeld 64 (put6 m 0x300000 (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0) (ws.getD 4 0)
      (ws.getD 5 0)) 0x300000 ws := by
  intro i hi
  rw [hl] at hi
  simp only [put6]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [readW_sep64, readW_sep64, readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64,
      BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [Mem.readW_writeW_self64, BitVec.setWidth_eq]

/-- What `put6` keeps below the table. -/
theorem put6_below {m : Mem} {a : Addr} (ha : a.toNat + 8 ≤ 0x300000) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 64) :
    (put6 m 0x300000 w₀ w₁ w₂ w₃ w₄ w₅).readW a 64 = m.readW a 64 := by
  have h0 : (0x300000 + BitVec.ofNat 64 (8 * 0) : Addr).toNat = 0x300000 := by decide
  have h1 : (0x300000 + BitVec.ofNat 64 (8 * 1) : Addr).toNat = 0x300008 := by decide
  have h2 : (0x300000 + BitVec.ofNat 64 (8 * 2) : Addr).toNat = 0x300010 := by decide
  have h3 : (0x300000 + BitVec.ofNat 64 (8 * 3) : Addr).toNat = 0x300018 := by decide
  have h4 : (0x300000 + BitVec.ofNat 64 (8 * 4) : Addr).toNat = 0x300020 := by decide
  have h5 : (0x300000 + BitVec.ofNat 64 (8 * 5) : Addr).toNat = 0x300028 := by decide
  simp only [put6]
  rw [readW_sep64, readW_sep64, readW_sep64, readW_sep64, readW_sep64, readW_sep64]
  all_goals first | (simp only [h0, h1, h2, h3, h4, h5]; omega_arith) | omega_using [ha]

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List MdHash) (n : String) : Addr := if n ∈ names vs then symsOf (names vs) n else 0x100000

theorem symT_distinct {vs : List MdHash} (hl : (names vs).length < 2 ^ 32) :
    (names vs).Pairwise fun f g => f ≠ g → symT vs f ≠ symT vs g :=
  (symsOf_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne

end VG.Proof.HmacTable.X86_64
