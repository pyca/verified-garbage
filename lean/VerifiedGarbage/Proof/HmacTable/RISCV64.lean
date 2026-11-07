module

public import VerifiedGarbage.Proof.HashTable.RISCV64
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.RISCV64
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Tables of the interface `Hmac` on RISC-V

A hash function with HMAC on RISC-V (`HVar`): its streaming functions as
RSAES-OAEP's proofs have them (`TVar`, with `Link`), the names of HMAC's
`init` and `finalize` over them (`vg_hmac_<h>_init`, `vg_hmac_<h>_finalize`,
`Impl/Hmac/Stream/RISCV64.lean`'s code), their constant time, and the HMAC
that `Spec.HmacTable.hmacOf` gives its hash function. Its table (`tableOf`,
`VG_HMAC_<HASH>`) holds the addresses of HMAC's `init`, the streaming
`update` and HMAC's `finalize`, then its data (`Spec.HmacTable.dataOf`); the
tables of a list of them (`tables`); and the functions an indirect call of
each of a table's functions may reach (`fnsOf`).

A function's proof runs the code of whichever of these the table holds
(`TabOK`): the first function of `fnsOf vs` at the address called, which is
the table's function of that name (`tabOK_of`), when the functions of
distinct names are at distinct addresses (as `Abi.withTables` says) and
those of the same name have the same code (`Coh`, which the registration
checks). `held_tableOf` reads a table's words, and `hashAt_tableOf` the hash
function it names.
-/

@[expose] public section

namespace VG.Proof.HmacTable.RISCV64

open VG VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Impl.Ecdsa.Rfc6979.RISCV64 (Fns)
open VG.Proof.Hmac.Stream.RISCV64 (initG finG)
open VG.Proof.HashTable (pw_ne find_name)
open VG.Proof.HashTable.RISCV64 (TVar)

/-- A hash function with HMAC on RISC-V. -/
structure HVar where
  t : TVar
  hiN : String
  hfN : String
  hiCt : ConstantTime isa (initG t.l.ok.SH (t.H.ibytes + t.H.F)).pre
    (initG t.l.ok.SH (t.H.ibytes + t.H.F)).pub t.H.init
  hfCt : ConstantTime isa (finG t.l.ok.SH (t.H.fbytes + t.H.F)).pre
    (finG t.l.ok.SH (t.H.fbytes + t.H.F)).pub t.H.finalize
  hmac : Spec.HmacTable.hmacOf t.l.G = some t.l.ok.SH.H

namespace HVar

variable (w : HVar)

abbrev H : Hash := w.t.H
abbrev G : Spec.Mgf1.Hash := w.t.l.G

end HVar

open VG.Proof.Hmac.Stream.RISCV64 in
def md5W : HVar :=
  ⟨Proof.HashTable.RISCV64.md5V, Spec.Hmac.md5I.initAnyKeyApi.name, Spec.Hmac.md5I.finalizeApi.name,
    Md5.init_ct, Md5.fin_ct, rfl⟩
open VG.Proof.Hmac.Stream.RISCV64 in
def sha1W : HVar :=
  ⟨Proof.HashTable.RISCV64.sha1V, Spec.Hmac.sha1I.initAnyKeyApi.name, Spec.Hmac.sha1I.finalizeApi.name,
    Sha1.init_ct, Sha1.fin_ct, rfl⟩
open VG.Proof.Hmac.Stream.RISCV64 in
def sha224W : HVar :=
  ⟨Proof.HashTable.RISCV64.sha224V, Spec.Hmac.sha224I.initAnyKeyApi.name, Spec.Hmac.sha224I.finalizeApi.name,
    Sha224.init_ct, Sha224.fin_ct, rfl⟩
open VG.Proof.Hmac.Stream.RISCV64 in
def sha256W : HVar :=
  ⟨Proof.HashTable.RISCV64.sha256V, Spec.Hmac.sha256I.initAnyKeyApi.name, Spec.Hmac.sha256I.finalizeApi.name,
    Sha256.init_ct, Sha256.fin_ct, rfl⟩
open VG.Proof.Hmac.Stream.RISCV64 in
def sha384W : HVar :=
  ⟨Proof.HashTable.RISCV64.sha384V, Spec.Hmac.sha384I.initAnyKeyApi.name, Spec.Hmac.sha384I.finalizeApi.name,
    Sha384.init_ct, Sha384.fin_ct, rfl⟩
open VG.Proof.Hmac.Stream.RISCV64 in
def sha512W : HVar :=
  ⟨Proof.HashTable.RISCV64.sha512V, Spec.Hmac.sha512I.initAnyKeyApi.name, Spec.Hmac.sha512I.finalizeApi.name,
    Sha512.init_ct, Sha512.fin_ct, rfl⟩
open VG.Proof.Hmac.Stream.RISCV64 in
def sha512_224W : HVar :=
  ⟨Proof.HashTable.RISCV64.sha512_224V, Spec.Hmac.sha512_224I.initAnyKeyApi.name,
    Spec.Hmac.sha512_224I.finalizeApi.name, Sha512_224.init_ct, Sha512_224.fin_ct, rfl⟩
open VG.Proof.Hmac.Stream.RISCV64 in
def sha512_256W : HVar :=
  ⟨Proof.HashTable.RISCV64.sha512_256V, Spec.Hmac.sha512_256I.initAnyKeyApi.name,
    Spec.Hmac.sha512_256I.finalizeApi.name, Sha512_256.init_ct, Sha512_256.fin_ct, rfl⟩

/-- The table of `w`'s HMAC, `VG_HMAC_<HASH>`. -/
def tableOf (w : HVar) : FnTable where
  name := s!"VG_HMAC_{w.G.rust.toUpper}"
  iface := Spec.HmacTable.iface
  fns := [w.hiN, w.H.updN, w.hfN]
  data := Spec.HmacTable.dataOf w.G

/-- The tables of `vs`. -/
def tables (vs : List HVar) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List HVar) : Fns :=
  ⟨vs.map fun w => (w.hiN, w.H.init), vs.map fun w => (w.H.updN, w.H.updC),
    vs.map fun w => (w.hfN, w.H.finalize)⟩

/-- The functions of `tables vs`. -/
def names (vs : List HVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The functions of the same name have the same code. -/
def Coh (vs : List HVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.hiN = w'.hiN → w.H.init = w'.H.init) ∧
    (w.H.updN = w'.H.updN → w.H.updC = w'.H.updC) ∧ (w.hfN = w'.hfN → w.H.finalize = w'.H.finalize)

instance (vs : List HVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `w`'s HMAC functions reaches it. -/
structure TabOK (w : HVar) (f : Fns) (sy : String → Addr) : Prop where
  i : f.init.find? (fun q => sy q.1 == sy w.hiN) = some (w.hiN, w.H.init)
  u : f.upd.find? (fun q => sy q.1 == sy w.H.updN) = some (w.H.updN, w.H.updC)
  f : f.fin.find? (fun q => sy q.1 == sy w.hfN) = some (w.hfN, w.H.finalize)

/-- At `p` in `m`, the addresses `sy` gives `w`'s HMAC `init`, the streaming
`update` and HMAC's `finalize`. -/
def TabMem (w : HVar) (sy : String → Addr) (p : Addr) (m : Mem) : Prop :=
  m.readW p 64 = sy w.hiN ∧ m.readW (p + BitVec.ofNat 64 8) 64 = sy w.H.updN ∧
    m.readW (p + BitVec.ofNat 64 16) 64 = sy w.hfN

theorem mem_names {vs : List HVar} {w : HVar} (hw : w ∈ vs) :
    w.hiN ∈ names vs ∧ w.H.updN ∈ names vs ∧ w.hfN ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem tabOK_of {vs : List HVar} (hc : Coh vs) {sy : String → Addr}
    (hd : (names vs).Pairwise fun f g => f ≠ g → sy f ≠ sy g) {w : HVar} (hw : w ∈ vs) :
    TabOK w (fnsOf vs) sy := by
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

/-- HMAC's block size, as the table holds it. -/
theorem blockSize_eq (w : HVar) : Spec.HmacTable.blockSize w.G = w.H.B := by
  simp only [Spec.HmacTable.blockSize, HVar.G, w.hmac, Option.map_some, Option.getD_some]
  exact w.t.l.ok.hB

/-- The words of the table of `w`. -/
theorem words_tableOf (s : State) (w : HVar) :
    FnTable.words isa s (tableOf w) = [s.syms w.hiN, s.syms w.H.updN, s.syms w.hfN,
      BitVec.ofNat 64 (Spec.HashTable.index w.G), BitVec.ofNat 64 w.G.len,
      BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)] := rfl

/-- What the table of `w` at `p` holds: its functions' addresses, its index,
its digest length and HMAC's block size. -/
theorem held_tableOf {m : Mem} {p : Addr} {s : State} {w : HVar}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (tableOf w))) :
    TabMem w s.syms p m ∧
      m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.G) ∧
      m.readW (p + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
      m.readW (p + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.B := by
  rw [words_tableOf] at h
  have h0 := h 0 (by simp)
  rw [show p + BitVec.ofNat 64 (64 / 8 * 0) = p by simp] at h0
  refine ⟨⟨h0, h 1 (by simp), h 2 (by simp)⟩, h 3 (by simp), ?_, ?_⟩
  · exact (h 4 (by simp)).trans (by rw [w.t.l.len]; rfl)
  · exact (h 5 (by simp)).trans (by rw [blockSize_eq]; rfl)

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : Addr} {w : HVar}
    (h : m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.G)) :
    Spec.HmacTable.hashAt 64 m p = some w.G := by
  simp only [Spec.HmacTable.hashAt, Spec.HmacTable.fns]
  rw [show p + BitVec.ofNat 64 (64 / 8 * 3) = p + BitVec.ofNat 64 24 from rfl, h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega)]
  exact w.t.idx

end VG.Proof.HmacTable.RISCV64
