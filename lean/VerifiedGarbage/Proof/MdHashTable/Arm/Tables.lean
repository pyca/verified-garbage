module

public import VerifiedGarbage.Proof.RsaPss.Arm.TabCall
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Md5
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha1
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha224
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha256
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha384
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512_224
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512_256
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.HashTable.Arm
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
public import VerifiedGarbage.Spec.MdHashTable
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Tables of the interface `MdHash` on ARMv7

The table of a hash function (`tableOf`): the addresses of its streaming
`init`, `update` and `finalize`, its compression function and the digest of
its hash value (`Impl.MdHashTable.Arm.digest`), then its data: its index in
`Mgf1.hashes`, its digest length, its block size, the size of its length
field, the size of its streaming state, and whether it is big-endian, each
word 32 bits wide. ARMv7 has one implementation of each hash function
(`vars`), whose shape is the one the functions taking a table choose by its
index (`MVar.shape`).

A function's proof runs the code of whichever of these the table holds:
an indirect call of the functions of every table (`fnsOf`) to one of them
reaches it (`htab_entered`), when the functions of distinct names are at
distinct addresses and those of the same name have the same code (`Coh`,
which the registration checks). The digest depends only on the digest code,
so it is named by the family of the streaming code (`digName`): SHA-224 and
SHA-256, and the SHA-512 family, share it.
-/

@[expose] public section

namespace VG.Proof.MdHashTable.Arm

open VG VG.Arm
open VG.Impl.RsaPss.Arm (MdFns ofIdx idxs)
open VG.Proof.RsaPss.Arm (PssHash HTab)
open VG.Proof.RsaOaep.Arm (tA)
open VG.Proof.RsaPkcs1Sig.Arm (layOf entered)
open VG.Proof.HashTable (pw_ne find_name)

/-- A hash function, with its place in `Spec.Mgf1.hashes` and its shape. -/
structure MVar where
  h : PssHash
  idx : Spec.Mgf1.hashes[Spec.HashTable.index h.G]? = some h.G
  shape : h.sh = ofIdx (Spec.HashTable.index h.G)

def md5M : MVar := ⟨Proof.RsaPss.Arm.md5, rfl, rfl⟩
def sha1M : MVar := ⟨Proof.RsaPss.Arm.sha1, rfl, rfl⟩
def sha224M : MVar := ⟨Proof.RsaPss.Arm.sha224, rfl, rfl⟩
def sha256M : MVar := ⟨Proof.RsaPss.Arm.sha256, rfl, rfl⟩
def sha384M : MVar := ⟨Proof.RsaPss.Arm.sha384, rfl, rfl⟩
def sha512M : MVar := ⟨Proof.RsaPss.Arm.sha512, rfl, rfl⟩
def sha512_224M : MVar := ⟨Proof.RsaPss.Arm.sha512_224, rfl, rfl⟩
def sha512_256M : MVar := ⟨Proof.RsaPss.Arm.sha512_256, rfl, rfl⟩

/-- Every hash function. -/
def vars : List MVar := [md5M, sha1M, sha224M, sha256M, sha384M, sha512M, sha512_224M, sha512_256M]

/-- The index of `w`'s hash function in `Mgf1.hashes`. -/
abbrev idx (w : MVar) : Nat := Spec.HashTable.index w.h.G

/-- The name of the streaming code's family of the hash function of index
`i`. -/
def family : Nat → String
  | 0 => "md5" | 1 => "sha1" | 2 | 3 => "sha256" | _ => "sha512"

/-- The name of `w`'s digest. -/
def digName (w : MVar) : String := s!"vg_{family (idx w)}_state_digest"

/-- 1 if `w`'s length field and words are big-endian. -/
def bigEndian (w : MVar) : Nat := if w.h.H.md.be then 1 else 0

/-- The table of `w`'s functions, `VG_MD_HASH_<HASH>`. -/
def tableOf (w : MVar) : FnTable where
  name := s!"VG_MD_HASH_{w.h.G.rust.toUpper}"
  iface := Spec.MdHashTable.iface
  fns := [w.h.H.md.st.initN, w.h.H.md.st.updN, w.h.H.md.st.finN, w.h.H.md.compN, digName w]
  data := Spec.MdHashTable.dataOf w.h.G ++
    [BitVec.ofNat 64 w.h.B, BitVec.ofNat 64 w.h.L, BitVec.ofNat 64 w.h.H.md.st.S, BitVec.ofNat 64 (bigEndian w)]

/-- The tables of `vs`. -/
def tables (vs : List MVar) : List FnTable := vs.map tableOf

/-- For each of the functions RSASSA-PSS calls through a table, that
function of each of `vs`. -/
def fnsOf (vs : List MVar) : MdFns :=
  ⟨vs.map fun w => (w.h.H.md.st.initN, w.h.H.md.st.initC), vs.map fun w => (w.h.H.md.compN, w.h.H.md.compC),
    vs.map fun w => (digName w, Impl.MdHashTable.Arm.digest w.h.H.md.out)⟩

/-- The functions of `tables vs`. -/
def names (vs : List MVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The functions of the same name have the same code. -/
def Coh (vs : List MVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.h.H.md.st.initN = w'.h.H.md.st.initN → w.h.H.md.st.initC = w'.h.H.md.st.initC) ∧
    (w.h.H.md.compN = w'.h.H.md.compN → w.h.H.md.compC = w'.h.H.md.compC) ∧
    (digName w = digName w' → w.h.H.md.out = w'.h.H.md.out)

instance (vs : List MVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

theorem mem_names {vs : List MVar} {w : MVar} (hw : w ∈ vs) :
    w.h.H.md.st.initN ∈ names vs ∧ w.h.H.md.compN ∈ names vs ∧ digName w ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- The words of `w`'s table in the state `s`. -/
theorem words_tableOf (s : State) (w : MVar) : FnTable.words isa s (tableOf w) =
    [(s.syms w.h.H.md.st.initN).setWidth 64, (s.syms w.h.H.md.st.updN).setWidth 64,
      (s.syms w.h.H.md.st.finN).setWidth 64, (s.syms w.h.H.md.compN).setWidth 64, (s.syms (digName w)).setWidth 64,
      BitVec.ofNat 64 (idx w), BitVec.ofNat 64 w.h.G.len, BitVec.ofNat 64 w.h.B, BitVec.ofNat 64 w.h.L,
      BitVec.ofNat 64 w.h.H.md.st.S, BitVec.ofNat 64 (bigEndian w)] := rfl

/-- What the table of `w` at `p` holds: the addresses of its `init`,
compression function and digest, and its index, 32 bits each. -/
theorem held_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 44 ≤ 2 ^ 32) {s : State} {w : MVar}
    (h : Abi.tableHeld 32 m (State.addr p) (FnTable.words isa s (tableOf w))) :
    m.readW (tA p 0) 32 = s.syms w.h.H.md.st.initN ∧ m.readW (tA p 12) 32 = s.syms w.h.H.md.compN ∧
      m.readW (tA p 16) 32 = s.syms (digName w) ∧ m.readW (tA p 20) 32 = BitVec.ofNat 32 (idx w) := by
  rw [words_tableOf] at h
  have a : ∀ i, i < 11 → tA p (4 * i) = State.addr p + BitVec.ofNat 64 (32 / 8 * i) := fun i hi => by
    rw [tA, VG.Arm.addr_add (by omega)]
  have e : ∀ i (hi : i < 11), m.readW (tA p (4 * i)) 32 = _ := fun i hi => (a i hi).symm ▸ h i (by simp; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := e 0 (by decide); simp only [Nat.mul_zero] at this; rw [this]; simp
  · have := e 3 (by decide); rw [show 4 * 3 = 12 by rfl] at this; rw [this]; simp
  · have := e 4 (by decide); rw [show 4 * 4 = 16 by rfl] at this; rw [this]; simp
  · have := e 5 (by decide); rw [show 4 * 5 = 20 by rfl] at this; rw [this]; simp

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 44 ≤ 2 ^ 32) {w : MVar}
    (h : m.readW (tA p 20) 32 = BitVec.ofNat 32 (idx w)) :
    Spec.MdHashTable.hashAt 32 m (State.addr p) = some w.h.G := by
  simp only [Spec.MdHashTable.hashAt, Spec.MdHashTable.fns]
  rw [show State.addr p + BitVec.ofNat 64 (32 / 8 * 5) = tA p 20 by rw [tA, VG.Arm.addr_add (by omega)], h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.h.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [idx, Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega)]
  exact w.idx

section
variable {F A C : Nat} {argv : List (BitVec 32)} {ro rw : List Region} {s : State}

/-- A word of a buffer only read, after the entry, as before it. -/
theorem entered_roW (h : (layOf F A argv ro rw s C).Ok (entered F s)) (hsp : 56 + F ≤ s.sp.toNat)
    {R : Region} (hR : R ∈ ro) {a : Addr} (hc : R.Contains a 4) :
    (entered F s).mem.readW a 32 = s.mem.readW a 32 := Proof.HashTable.Arm.entered_roW h hsp hR hc

/-- What `ctHash` needs of the table of `w` at `p`, one of the buffers only
read, after the entry. -/
theorem htab_entered (h : (layOf F A argv ro rw s C).Ok (entered F s)) (hsp : 56 + F ≤ s.sp.toNat)
    {p : BitVec 32} (hR : Sig.tableRegion 32 (State.addr p) 11 ∈ ro) (hp : p.toNat + 44 ≤ 2 ^ 32)
    {vs : List MVar} (hc : Coh vs)
    (hd64 : (names vs).Pairwise fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) {w : MVar}
    (hw : w ∈ vs) (hh : Abi.tableHeld 32 s.mem (State.addr p) (FnTable.words isa s (tableOf w))) :
    HTab w.h (digName w) (fnsOf vs) p (s.syms w.h.H.md.st.initN) (s.syms w.h.H.md.compN) (s.syms (digName w))
      (entered F s) := by
  have sy : (entered F s).syms = s.syms := rfl
  have e : ∀ o, o + 4 ≤ 44 → (entered F s).mem.readW (tA p o) 32 = s.mem.readW (tA p o) 32 :=
    fun o ho => entered_roW h hsp hR (by
      show (⟨State.addr p, 11 * (32 / 8)⟩ : Region).Contains (State.addr (p + BitVec.ofNat 32 o)) 4
      rw [VG.Arm.addr_add (by omega)]
      exact Offset.contains_base _ (by omega) (by omega))
  obtain ⟨m0, m3, m4, -⟩ := held_tableOf hp hh
  have hn := mem_names hw
  have fn : ∀ {β : Type} {ts : List (String × β)} {n : String} {c : β}, (n, c) ∈ ts → (∀ q ∈ ts, q.1 ∈ names vs) →
      (∀ q ∈ ts, q.1 = n → q.2 = c) → n ∈ names vs →
      ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.syms n).setWidth 64) = some (n, c) :=
    fun hm hin hcc hnn => find_name (sy := fun n => (s.syms n).setWidth 64) hm
      (fun q hq hne => pw_ne hd64 _ (hin q hq) _ hnn hne) hcc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sy]
    refine fn (List.mem_map_of_mem (f := fun w => (w.h.H.md.st.initN, w.h.H.md.st.initC)) hw) (fun q hq => ?_)
      (fun q hq he => ?_) hn.1
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq; exact (mem_names hw').1
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq; exact (hc w' hw' w hw).1 he
  · rw [sy]
    refine fn (List.mem_map_of_mem (f := fun w => (w.h.H.md.compN, w.h.H.md.compC)) hw) (fun q hq => ?_)
      (fun q hq he => ?_) hn.2.1
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq; exact (mem_names hw').2.1
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq; exact (hc w' hw' w hw).2.1 he
  · rw [sy]
    refine fn (List.mem_map_of_mem (f := fun w => (digName w, Impl.MdHashTable.Arm.digest w.h.H.md.out)) hw)
      (fun q hq => ?_) (fun q hq he => ?_) hn.2.2
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq; exact (mem_names hw').2.2
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq; exact congrArg Impl.MdHashTable.Arm.digest ((hc w' hw' w hw).2.2 he)
  · rw [e 0 (by decide), m0]
  · rw [e 12 (by decide), m3]
  · rw [e 16 (by decide), m4]

end

end VG.Proof.MdHashTable.Arm
