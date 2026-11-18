module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.Arm
import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Instance
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Ecdsa.Rfc6979.Arm.Contract`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: the contract the proof is written against

The facts of the contract for an instance `I` of a curve of `len`-byte
scalars with a hash of `I.hashLen` bytes, for 32-bit ARM and `N` bytes of
stack, by name, as the code for that hash function sees them:
`vg_ecdsa_<curve>_sign(out = r0, d = r1, digest = r2, digest_len = r3,
scratch = [sp], hmac = [sp + 4])` (the table, 24 bytes, read-only, with what
`TabFacts` says of it), the result in `r0` (the low word of `r1:r0`), and
the tables of constants `cs` that `vg_ecdsa_<curve>_sign_k` reads
(`TablesOk`), at their statics; the public data include the addresses of
the functions `ns`, those of the tables. `Table.lean` shows
`TableInstance.signContract` gives it for the hash function of the table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Proof.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

/-- The `N` bytes of stack below `sp`. -/
abbrev stkR (sp : BitVec 32) (N : Nat) : Region := ⟨State.addr sp - BitVec.ofNat 64 N, N⟩

/-- Static tables are readable, held in memory, and apart from every write region. -/
def TablesOk (cs : List (String × List (BitVec 64))) (sy : String → BitVec 32) (m : Mem)
    (writes : List Region) : Prop :=
  ∀ c∈cs,(∀ i<c.2.length,m.readW (State.addr (sy c.1)+BitVec.ofNat 64 (8*i)) 64=c.2.getD i 0) ∧
    (sy c.1).toNat+8*c.2.length≤2^32 ∧
    (∀ r∈writes,Region.Disjoint ⟨State.addr (sy c.1),8*c.2.length⟩ r) ∧
    (State.addr (sy c.1)).toNat%64=0

def rfcArm (I : Proof.Ecdsa.Rfc6979.Instance) (N : Nat) (cs : List (String × List (BitVec 64)))
    (TabFacts : State → Prop) (ns : List String) : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨State.addr (s.gpr .r1), I.ecdsa.curve.len⟩
    let digest : Region := ⟨State.addr (s.gpr .r2), I.hashLen⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let tab : Region := ⟨State.addr (stackArg s 1), 24⟩
    let args : Region := ⟨State.addr s.sp, 8⟩
    let stk : Region := stkR s.sp N
    s.rd = [d, digest, tab, args] ++ Abi.constRegions (fun n => State.addr (s.syms n)) cs ∧
      s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .r0).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + I.ecdsa.curve.len ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + I.hashLen ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ N ≤ s.sp.toNat ∧
      s.sp.toNat + 8 ≤ 2 ^ 32 ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (stackArg s 1).toNat + 24 ≤ 2 ^ 32 ∧ tab.Disjoint out ∧ tab.Disjoint scratch ∧ tab.Disjoint stk ∧
      TablesOk cs s.syms s.mem [out,scratch,stk] ∧ TabFacts s
  post s s' :=
    match (result I s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * I.ecdsa.curve.len) = List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    (result I s₁.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2 =
      (result I s₂.mem (State.addr (s₂.gpr .r1)) (State.addr (s₂.gpr .r2))).2 ∧
    (∀ c∈cs,s₁.syms c.1=s₂.syms c.1) ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! ### `HmacTable.Arm`, which this module and modules that import it used -/

section

/-!
# Tables of the interface `Hmac` on ARMv7

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Regs.lean`), with every hash function that
has HMAC on ARMv7, each with one implementation (`vars`: MD5, SHA-1,
SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256, the
functions PBKDF2's code calls, `Proof.Pbkdf2.Whole.Arm`): the table of a
hash function (`tableOf`, `VG_HMAC_<HASH>`) holds the addresses of HMAC's
`init` and `finalize` and of the streaming `update`, in the forms that take
their working space as an argument (`_scratch`), then its data
(`Spec.HmacTable.dataOf`), each word 32 bits wide; an indirect call of the
functions of every table (`fnsOf`) to one of them reaches it (`tabOK_of`),
when the functions of distinct names are at distinct addresses and those of
the same name have the same code (`Coh`). `held_tableOf` reads a table's
words, and `hashAt_tableOf` the hash function it names.
-/

@[expose] public section

namespace VG.Proof.HmacTable.Arm

open VG VG.Arm
open VG.Impl.Ecdsa.Rfc6979.Arm (Fns)
open VG.Proof.HashTable (pw_ne find_name)

/-- A hash function with HMAC on ARMv7: the functions PBKDF2's code calls,
what is proven of them, and its place in `Spec.Mgf1.hashes`, whose HMAC is
theirs. -/
structure HVar where
  F : Impl.Pbkdf2.Whole.Arm.Fns
  ok : Proof.Pbkdf2.Whole.Arm.FnsOK F
  G : Spec.Mgf1.Hash
  idx : Spec.Mgf1.hashes[Spec.HashTable.index G]? = some G
  glen : G.len = F.H.D
  hmac : Spec.HmacTable.hmacOf G = some ok.hH.SH.H

open Proof.Pbkdf2.Whole.Arm in
def md5V : HVar := ⟨md5F, md5OKF, Spec.Mgf1.md5, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha1V : HVar := ⟨sha1F, sha1OKF, Spec.Mgf1.sha1, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha224V : HVar := ⟨sha224F, sha224OKF, Spec.Mgf1.sha224, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha256V : HVar := ⟨sha256F, sha256OKF, Spec.Mgf1.sha256, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha384V : HVar := ⟨sha384F, sha384OKF, Spec.Mgf1.sha384, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha512V : HVar := ⟨sha512F, sha512OKF, Spec.Mgf1.sha512, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha512_224V : HVar := ⟨sha512_224F, sha512_224OKF, Spec.Mgf1.sha512_224, rfl, rfl, rfl⟩
open Proof.Pbkdf2.Whole.Arm in
def sha512_256V : HVar := ⟨sha512_256F, sha512_256OKF, Spec.Mgf1.sha512_256, rfl, rfl, rfl⟩

/-- Every hash function with HMAC on ARMv7. -/
def vars : List HVar := [md5V, sha1V, sha224V, sha256V, sha384V, sha512V, sha512_224V, sha512_256V]

/-- The table of `w`'s HMAC, `VG_HMAC_<HASH>`. -/
def tableOf (w : HVar) : FnTable where
  name := s!"VG_HMAC_{w.G.rust.toUpper}"
  iface := Spec.HmacTable.iface
  fns := [w.F.hiN, w.F.H.updN, w.F.hfN]
  data := Spec.HmacTable.dataOf w.G

/-- The tables of `vs`. -/
def tables (vs : List HVar) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List HVar) : Fns :=
  ⟨vs.map fun w => (w.F.hiN, w.F.hiC), vs.map fun w => (w.F.H.updN, w.F.H.updC),
    vs.map fun w => (w.F.hfN, w.F.hfC)⟩

/-- The functions of `tables vs`. -/
def names (vs : List HVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The functions of the same name have the same code. -/
def Coh (vs : List HVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.F.hiN = w'.F.hiN → w.F.hiC = w'.F.hiC) ∧
    (w.F.H.updN = w'.F.H.updN → w.F.H.updC = w'.F.H.updC) ∧ (w.F.hfN = w'.F.hfN → w.F.hfC = w'.F.hfC)

instance (vs : List HVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

/-- The table's word at `p + o`. -/
abbrev tA (p : BitVec 32) (o : Nat) : Addr := State.addr (p + BitVec.ofNat 32 o)

/-- At `p` in `m`, the addresses `sy` gives `F`'s HMAC `init`, the streaming
`update` and HMAC's `finalize`. -/
def TabMem (F : Impl.Pbkdf2.Whole.Arm.Fns) (sy : String → BitVec 32) (p : BitVec 32) (m : Mem) : Prop :=
  m.readW (tA p 0) 32 = sy F.hiN ∧ m.readW (tA p 4) 32 = sy F.H.updN ∧ m.readW (tA p 8) 32 = sy F.hfN

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `F`'s HMAC functions reaches it. -/
structure TabOK (F : Impl.Pbkdf2.Whole.Arm.Fns) (f : Fns) (sy : String → BitVec 32) : Prop where
  i : f.init.find? (fun q => (sy q.1).setWidth 64 == (sy F.hiN).setWidth 64) = some (F.hiN, F.hiC)
  u : f.upd.find? (fun q => (sy q.1).setWidth 64 == (sy F.H.updN).setWidth 64) = some (F.H.updN, F.H.updC)
  f : f.fin.find? (fun q => (sy q.1).setWidth 64 == (sy F.hfN).setWidth 64) = some (F.hfN, F.hfC)

theorem mem_names {vs : List HVar} {w : HVar} (hw : w ∈ vs) :
    w.F.hiN ∈ names vs ∧ w.F.H.updN ∈ names vs ∧ w.F.hfN ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem tabOK_of {vs : List HVar} (hc : Coh vs) {sy : String → BitVec 32}
    (hd64 : (names vs).Pairwise fun f g => f ≠ g → (sy f).setWidth 64 ≠ (sy g).setWidth 64) {w : HVar}
    (hw : w ∈ vs) : TabOK w.F (fnsOf vs) sy := by
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

/-- HMAC's block size, as the table holds it. -/
theorem blockSize_eq (w : HVar) : Spec.HmacTable.blockSize w.G = w.F.H.B := by
  simp only [Spec.HmacTable.blockSize, w.hmac, Option.map_some, Option.getD_some]
  exact w.ok.hH.hB

/-- The words of the table of `w`. -/
theorem words_tableOf (s : State) (w : HVar) :
    FnTable.words isa s (tableOf w) = [(s.syms w.F.hiN).setWidth 64, (s.syms w.F.H.updN).setWidth 64,
      (s.syms w.F.hfN).setWidth 64, BitVec.ofNat 64 (Spec.HashTable.index w.G), BitVec.ofNat 64 w.G.len,
      BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)] := rfl

/-- What the table of `w` at `p` holds: its functions' addresses, its index,
its digest length and HMAC's block size, 32 bits each. -/
theorem held_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 24 ≤ 2 ^ 32) {s : State} {w : HVar}
    (h : Abi.tableHeld 32 m (State.addr p) (FnTable.words isa s (tableOf w))) :
    TabMem w.F s.syms p m ∧ m.readW (tA p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G) ∧
      m.readW (tA p 16) 32 = BitVec.ofNat 32 w.F.H.D ∧ m.readW (tA p 20) 32 = BitVec.ofNat 32 w.F.H.B := by
  rw [words_tableOf, blockSize_eq] at h
  have a : ∀ i, i < 6 → tA p (4 * i) = State.addr p + BitVec.ofNat 64 (32 / 8 * i) := fun i hi => by
    rw [tA, VG.Arm.addr_add (by omega_using [hp, hi])]
  have e : ∀ i (hi : i < 6), m.readW (tA p (4 * i)) 32 = _ := fun i hi => (a i hi).symm ▸ h i (by simp; omega_using [hi])
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have := e 0 (by decide); simp only [Nat.mul_zero] at this; rw [this]; simp
  · have := e 1 (by decide); simp only [Nat.mul_one] at this; rw [this]; simp
  · have := e 2 (by decide); rw [show 4 * 2 = 8 by rfl] at this; rw [this]; simp
  · have := e 3 (by decide); rw [show 4 * 3 = 12 by rfl] at this; rw [this]; simp
  · have := e 4 (by decide); rw [show 4 * 4 = 16 by rfl] at this; rw [this, w.glen]; simp
  · have := e 5 (by decide); rw [show 4 * 5 = 20 by rfl] at this; rw [this]; simp

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : BitVec 32} (hp : p.toNat + 24 ≤ 2 ^ 32) {w : HVar}
    (h : m.readW (tA p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G)) :
    Spec.HmacTable.hashAt 32 m (State.addr p) = some w.G := by
  simp only [Spec.HmacTable.hashAt, Spec.HmacTable.fns]
  rw [show State.addr p + BitVec.ofNat 64 (32 / 8 * 3) = tA p 12 by rw [tA, VG.Arm.addr_add (by omega_using [hp])], h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega_using [this])]
  exact w.idx

end VG.Proof.HmacTable.Arm

end

end

/-! ### `Ecdsa.Rfc6979.Arm.SymsInstr`, which only this module used -/

section

/-! Preserve symbol addresses alongside the existing instruction-update proofs. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm
open VG VG.Arm VG.Proof.X25519.Arm

structure UpdS (s t : State) (r : Reg) (v : BitVec 32) : Prop extends Upd s t r v where
  syms : t.syms=s.syms

structure MupdS (s t : State) (m : Mem) : Prop extends Mupd s t m where
  syms : t.syms=s.syms

structure FupdS (s t : State) : Prop extends Fupd s t where
  syms : t.syms=s.syms

instance {s t : State} {r : Reg} {v : BitVec 32} : Coe (UpdS s t r v) (Upd s t r v) := ⟨UpdS.toUpd⟩
instance {s t : State} {m : Mem} : Coe (MupdS s t m) (Mupd s t m) := ⟨MupdS.toMupd⟩
instance {s t : State} : Coe (FupdS s t) (Fupd s t) := ⟨FupdS.toFupd⟩

private theorem prefix_syms {i : Instr} {is : List Instr} {s : State} {P Q : State → Prop}
    (one : WP isa (.block [i]) s P)
    (k : ∀ t,P t → t.syms=s.syms → WP isa (.block is) t Q) :
    WP isa (.block (i::is)) s Q := by
  change WP isa (.block ([i]++is)) s Q
  rw [WP.block_append_iff]
  exact WP.mono_syms one k

variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movS {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s=some v)
    (k : ∀ t,UpdS s t d v → WP isa (.block is) t Q) :
    WP isa (.block (.mov d o::is)) s Q :=
  prefix_syms (wp_mov ho (fun _ u => WP.block_nil u)) (fun _ u sy => k _ ⟨u,sy⟩)

theorem wp_dpS {op : DpOp} {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s=some y)
    (k : ∀ t,UpdS s t d (dpVal op (s.gpr n) y) → WP isa (.block is) t Q) :
    WP isa (.block (.dp op d n o::is)) s Q :=
  prefix_syms (wp_dp ho (fun _ u => WP.block_nil u)) (fun _ u sy => k _ ⟨u,sy⟩)

theorem wp_movwS {d : Reg} {imm : BitVec 16}
    (k : ∀ t,UpdS s t d (imm.setWidth 32) → WP isa (.block is) t Q) :
    WP isa (.block (.movw d imm::is)) s Q :=
  prefix_syms (wp_movw (fun _ u => WP.block_nil u)) (fun _ u sy => k _ ⟨u,sy⟩)

theorem wp_strS {t n : Reg} {off : Nat} {a : Addr} (ho : off<4096)
    (ha : State.addr (s.gpr n+BitVec.ofNat 32 off)=a) (hw : InRegions s.wr a 4)
    (k : ∀ u,MupdS s u (s.mem.writeW a (s.gpr t)) → WP isa (.block is) u Q) :
    WP isa (.block (.str t n off::is)) s Q :=
  prefix_syms (wp_str ho ha hw (fun _ u => WP.block_nil u)) (fun _ u sy => k _ ⟨u,sy⟩)

theorem wp_cmpS {n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s=some y)
    (k : ∀ t,FupdS s t → t.z=(s.gpr n-y==0) → WP isa (.block is) t Q) :
    WP isa (.block (.cmp n o::is)) s Q := by
  refine prefix_syms (P := fun t => Fupd s t ∧ t.z=(s.gpr n-y==0))
    (wp_cmp ho (fun _ u z => WP.block_nil ⟨u,z⟩)) ?_
  exact fun _ ⟨u,z⟩ sy => k _ ⟨u,sy⟩ z

theorem wp_ldrS {t n : Reg} {off : Nat} {a : Addr} (ho : off<4096)
    (ha : State.addr (s.gpr n+BitVec.ofNat 32 off)=a) (hr : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ u,UpdS s u t (s.mem.readW a 32) → WP isa (.block is) u Q) :
    WP isa (.block (.ldr t n off::is)) s Q :=
  prefix_syms (wp_ldr ho ha hr (fun _ u => WP.block_nil u)) (fun _ u sy => k _ ⟨u,sy⟩)

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end


/-!
# Deterministic ECDSA on 32-bit ARM: where everything is

The function's buffers (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`scratch`, the table `hmac` of 24 bytes, the 8 bytes of stack arguments
above the stack pointer) and the 536 bytes of stack below the stack
pointer, from `B` up (`Lay dn`): the 24 bytes the calls use (their frames
and the 16 bytes HMAC's functions use below theirs), then the frame of 512
bytes, from `B + 24`: `K`, `V`, `h`, `X`, `core`'s digest, `T` and its
length (`LOW`, with the calls' 24 bytes), then our caller's `r4`–`r11` and
`lr` and the pointer `digest` (`TOP`). `Ctx` is what holds between the
prologue and the frame's release: the permissions, `sp`, the registers that
hold the pointers (`r4`–`r6`, `r8`, `r11`), our caller's registers and
`digest` in the frame, that memory changed only in `out`, `scratch` and the
stack, where the tables of constants `core` reads are, and that the table
holds the hash function `F`'s HMAC functions, which an indirect call of
`f`'s reaches. Code that writes only regions apart from `TOP` (`Safe`) keeps
it (`Ctx.keep`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm
open VG.Arm.FrameStack (addr_sub' sub_toNat')
open VG.Proof.X25519.Arm (Upd Mupd)
open VG.Impl.Ecdsa.Rfc6979.Arm (Fns)
open VG.Proof.HmacTable.Arm (TabOK TabMem tA)

/-- The stack the function uses: the frame and the calls' 24 bytes. -/
def stackT : Nat := 536

/-- The buffers, as the registers and stack arguments hold them, and the
stack pointer on entry, for a digest of `dn` bytes and scalars of `q`. -/
structure Lay (dn : Nat) where
  out : BitVec 32
  d : BitVec 32
  dg : BitVec 32
  scr : BitVec 32
  /-- The table of HMAC. -/
  tab : BitVec 32
  sp : BitVec 32
  q : Nat
  /-- The tables of constants `core` reads, and their statics' addresses. -/
  cs : List (String × List (BitVec 64)) := []
  sy : String → BitVec 32 := fun _ => 0
  /-- The hash function's functions, which the table holds, and the
  functions an indirect call of a table's functions may reach. -/
  F : Impl.Pbkdf2.Whole.Arm.Fns
  f : Fns
  /-- The addresses of `F`'s HMAC functions, public. -/
  fa : String → BitVec 32

namespace Lay

variable {dn : Nat} (L : Lay dn)

/-- The lowest byte of the stack used. -/
abbrev B : Addr := State.addr L.sp - BitVec.ofNat 64 536
/-- The frame's base, as `sp` and `r8` hold it. -/
abbrev fp : BitVec 32 := L.sp - BitVec.ofNat 32 512

abbrev OUT : Region := ⟨State.addr L.out, 2 * L.q⟩
abbrev D : Region := ⟨State.addr L.d, L.q⟩
abbrev DG : Region := ⟨State.addr L.dg, dn⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
/-- The table of HMAC. -/
abbrev TAB : Region := ⟨State.addr L.tab, 24⟩
/-- The stack arguments. -/
abbrev ARGS : Region := ⟨State.addr L.sp, 8⟩
abbrev TBLs : List Region := Abi.constRegions (fun n => State.addr (L.sy n)) L.cs
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 536⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 24, 512⟩
/-- The stack below the saved registers: the calls', and the frame's buffers. -/
abbrev LOW : Region := ⟨L.B, 492⟩

/-- What the contract says of where the buffers and the stack are (`d` and
`digest`, which are only read, may overlap, and the table with them). -/
structure Ok : Prop where
  od : L.OUT.Disjoint L.D
  og : L.OUT.Disjoint L.DG
  oc : L.OUT.Disjoint L.SCR
  dc : L.D.Disjoint L.SCR
  gc : L.DG.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  kd : L.STK.Disjoint L.D
  kg : L.STK.Disjoint L.DG
  kc : L.STK.Disjoint L.SCR
  no : L.out.toNat + 2 * L.q ≤ 2 ^ 32
  nd : L.d.toNat + L.q ≤ 2 ^ 32
  ng : L.dg.toNat + dn ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
  /-- The table does not wrap around, and is apart from what the code writes. -/
  nt : L.tab.toNat + 24 ≤ 2 ^ 32
  to : L.TAB.Disjoint L.OUT
  tc : L.TAB.Disjoint L.SCR
  tk : L.TAB.Disjoint L.STK
  /-- The stack arguments are apart from what the code writes. -/
  ao : L.ARGS.Disjoint L.OUT
  ac : L.ARGS.Disjoint L.SCR
  nB : 536 ≤ L.sp.toNat
  na : L.sp.toNat + 8 ≤ 2 ^ 32
  tables : ∀ r∈L.TBLs,r.base.toNat+r.len≤2^32 ∧ (∀ w∈[L.OUT,L.SCR,L.STK],r.Disjoint w) ∧ r.base.toNat%64=0

end Lay

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn} (h : L.Ok)
include h

theorem B_toNat : L.B.toNat = L.sp.toNat - 536 := by
  have := h.nB; have := L.sp.isLt
  simp only [Lay.B, BitVec.toNat_sub, BitVec.toNat_ofNat, toNat_addr]; omega_arith

theorem B_fit : L.B.toNat + 536 ≤ 2 ^ 32 := by
  have := L.sp.isLt; have := h.nB; rw [h.B_toNat]; omega_using []

omit h in
/-- The stack pointer on entry, from `B`. -/
theorem spA : State.addr L.sp = L.B + BitVec.ofNat 64 536 := by
  simp only [Lay.B, BitVec.sub_add_cancel]

/-- `fp + o`, as an address: `B + 24 + o`. -/
theorem fpA {o : Nat} (ho : o < 520) :
    State.addr (L.fp + BitVec.ofNat 32 o) = L.B + BitVec.ofNat 64 (24 + o) := by
  have hn := h.nB; have := L.sp.isLt
  have hfp : L.fp.toNat = L.sp.toNat - 512 := sub_toNat' (by omega_using [hn])
  rw [addr_add (by rw [hfp]; have := h.na; omega_using [ho, this]), Lay.fp, addr_sub' (by omega_using [hn]),
    Offset.sub_ofNat_eq _ (show 512 ≤ 536 by omega_using []), show 536 - 512 = 24 by omega_using [], Offset.add_add]

theorem fpA0 : State.addr L.fp = L.B + BitVec.ofNat 64 24 := by
  have := h.fpA (o := 0) (by decide)
  rwa [BitVec.add_zero] at this

theorem stk_scr {d n e k : Nat} (h₁ : d + n ≤ 536) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨State.addr L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_SCR {d n : Nat} (h₁ : d + n ≤ 536) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT {d n : Nat} (h₁ : d + n ≤ 536) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_DG {d n : Nat} (h₁ : d + n ≤ 536) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.DG := h.kg.sub_left (Offset.sub_base _ h₁)

end Lay.Ok

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A region of the frame. -/
theorem within_fr (B : Addr) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 536) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 24, 512⟩ :=
  ⟨d - 24, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega_using [h₁, h₂]⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below the saved registers. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 492) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (Offset.sub_base _ h))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) :
    Safe L ⟨State.addr L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

/-- The saved registers and `digest` are apart from every safe region. -/
theorem top_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 492, 44⟩ r := by
  have := h.B_fit
  rcases hs with hs | hs | hs
  · exact (h.stk_OUT (by omega_using [])).sub_right hs
  · exact (h.stk_SCR (by omega_using [])).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_using []) (by omega_using [])).sub_right hs

end Lay.Ok

/-! ## Between the prologue and the frame's release -/

/-- The registers that hold the pointers between the calls. -/
abbrev ptrRegs : List Reg := [.r4, .r5, .r6, .r8, .r11]

/-- The state between the prologue and the frame's release: `g` are the
registers on entry, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG, L.TAB, L.ARGS] ++ L.TBLs
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  sp : t.sp = L.fp
  r4 : t.gpr .r4 = L.out
  r5 : t.gpr .r5 = L.d
  r6 : t.gpr .r6 = L.tab
  r8 : t.gpr .r8 = L.fp
  r11 : t.gpr .r11 = L.scr
  saved : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, t.mem.readW (L.B + BitVec.ofNat 64 (24 + p.2)) 32 = g p.1
  /-- The pointer `digest`, at the frame's top. -/
  pDg : t.mem.readW (L.B + BitVec.ofNat 64 (24 + Impl.Ecdsa.Rfc6979.Arm.fDigest)) 32 = L.dg
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sy : ∀ c∈L.cs,t.syms c.1=L.sy c.1
  held : Abi.constsHeld m₀ (fun n => State.addr (L.sy n)) L.cs
  /-- The table: an indirect call reaches `F`'s functions, whose addresses
  it holds, then its digest length and HMAC's block size. -/
  tabOk : TabOK L.F L.f t.syms
  tabMem : TabMem L.F t.syms L.tab m₀
  tabD : m₀.readW (tA L.tab Impl.Ecdsa.Rfc6979.Arm.tD) 32 = BitVec.ofNat 32 L.F.H.D
  tabB : m₀.readW (tA L.tab Impl.Ecdsa.Rfc6979.Arm.tB) 32 = BitVec.ofNat 32 L.F.H.B
  fsy : ∀ n ∈ [L.F.hiN, L.F.H.updN, L.F.hfN], t.syms n = L.fa n

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega_using []) a (h a ha)⟩

theorem saved_off : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, 468 ≤ p.2 ∧ p.2 + 4 ≤ 504 := by decide

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions, `sp` and the registers that hold the
pointers, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hp : ∀ r ∈ ptrRegs, t'.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r) (hsy : t'.syms=t.syms) :
    Ctx L g m₀ t' := by
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hp _ (by decide)).trans hc.r4,
    (hp _ (by decide)).trans hc.r5, (hp _ (by decide)).trans hc.r6, (hp _ (by decide)).trans hc.r8,
    (hp _ (by decide)).trans hc.r11, fun p hp' => ?_, ?_, hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame),
    fun c hc' => by rw [hsy]; exact hc.sy c hc',hc.held, by rw [hsy]; exact hc.tabOk,
    by rw [hsy]; exact hc.tabMem, hc.tabD, hc.tabB, by rw [hsy]; exact hc.fsy⟩
  · have ho := saved_off p hp'
    rw [hf.readW (r := ⟨L.B + BitVec.ofNat 64 492, 44⟩) (Offset.contains _ (by omega_using [ho]) (by omega_using [ho])
      (by have := hL.B_fit; omega_using [])) (fun r hr => hL.top_safe (hs r hr)) (by decide)]
    exact hc.saved p hp'
  · rw [hf.readW (r := ⟨L.B + BitVec.ofNat 64 492, 44⟩) (Offset.contains _ (by decide) (by decide)
      (by have := hL.B_fit; omega_using [])) (fun r hr => hL.top_safe (hs r hr)) (by decide)]
    exact hc.pDg

/-- An update of one register, not one that holds a pointer. -/
theorem upd (hc : Ctx L g m₀ t) {d : Reg} {v : BitVec 32} (u : UpdS t t' d v) (hd : d ∉ ptrRegs) :
    Ctx L g m₀ t' :=
  ⟨u.rd.trans hc.rd, u.wr.trans hc.wr, u.sp.trans hc.sp,
    (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r4, (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r5,
    (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r6, (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r8,
    (u.other _ (fun e => hd (e ▸ by decide))).trans hc.r11, fun p hp => by rw [u.mem]; exact hc.saved p hp,
    by rw [u.mem]; exact hc.pDg, by rw [u.mem]; exact hc.frame,fun c hc' => by rw [u.syms]; exact hc.sy c hc',
    hc.held, by rw [u.syms]; exact hc.tabOk, by rw [u.syms]; exact hc.tabMem, hc.tabD, hc.tabB,
    by rw [u.syms]; exact hc.fsy⟩

/-- A byte of `d`, as on entry. -/
theorem d_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.q) :
    t.mem (State.addr L.d + BitVec.ofNat 64 i) = m₀ (State.addr L.d + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.D) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.od.symm
    · exact hL.dc
    · exact hL.kd.symm) (by show L.q ≤ 2 ^ 64; have := hL.nd; omega_using [this]) hi

/-- A byte of `digest`, as on entry. -/
theorem dg_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < dn) :
    t.mem (State.addr L.dg + BitVec.ofNat 64 i) = m₀ (State.addr L.dg + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.DG) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.og.symm
    · exact hL.gc
    · exact hL.kg.symm) (by show dn ≤ 2 ^ 64; have := hL.ng; omega_using [this]) hi

/-- A word of the table, as on entry. -/
theorem tabWord (hL : L.Ok) (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 4 ≤ 24) :
    t.mem.readW (tA L.tab o) 32 = m₀.readW (tA L.tab o) 32 := by
  rw [tA, addr_add (by have := hL.nt; omega_using [ho, this])]
  exact hc.frame.readW (r := L.TAB) (Offset.contains_base _ ho (by omega_using [ho]))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.to
      · exact hL.tc
      · exact hL.tk) (by decide)

theorem inFr (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 536) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩

theorem inFrW (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 536) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩

theorem inScrW (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (State.addr L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega_using [h])⟩

theorem inD (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ L.q) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (State.addr L.d + BitVec.ofNat 64 o) n :=
  ⟨L.D, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_using [ho])⟩

theorem inTab (hL : L.Ok) (hc : Ctx L g m₀ t) {o : Nat} (h : o + 4 ≤ 24) :
    InRegions (t.rd ++ t.wr) (tA L.tab o) 4 := by
  rw [tA, addr_add (by have := hL.nt; omega_using [h, this])]
  exact ⟨L.TAB, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_using [h])⟩

/-- Regions within the buffers and the frame are permitted. -/
theorem covers (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within r R) : Covers rs (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl <;> simp

theorem coversW (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.FR, L.OUT, L.SCR], Within r R) : Covers rs t.wr :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl <;> simp

end Ctx

end VG.Proof.Ecdsa.Rfc6979.Arm
