module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.CT
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.ByIdx
public import VerifiedGarbage.Proof.HashTable.X86_64
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Deterministic ECDSA on x86-64: the hash function of a table

`vg_ecdsa_<curve>_sign` (`signCode`) loads the index of the hash function
from the table `hash` (its word 3) and runs the code for that index's
digest length and block size (`cfgT`), which calls the table's functions.
For the variants `vs` of the hash functions that pass the registration's
checks (`OK`: their functions of the same name have the same code, and each
is of one of the hash functions with HMAC, of the sizes its index's code is
for), the table of each variant `w` makes it the code for `w`'s hash
function (`hashOf`, with `cfgT_eq`), which meets the contract with that
hash function fixed (`sign_ok`, `sign_ct`). `tabK` states that contract for
whichever of the tables `hash` holds, on entry; each curve's file shows
`TableInstance.signContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HashTable.X86_64 (tables fnsOf names Coh tableOf mem_names tabOK_of fnsGood_of)

/-! ## The code -/

/-- The code for the hash function of index `i`, on the curve `R`, with the
bound on candidates `tries` and the tables of `vs`. -/
def cfgT (R : RfcCurve) (tries : Nat) (vs : List MdHash) (i : Nat) : Cfg where
  D := (shapeOf i).1
  B := (shapeOf i).2
  f := fnsOf vs
  w := R.E.n
  len := R.E.C.len
  sh := R.sh
  hHigh := R.hHigh
  n := R.E.C.n
  tries := tries
  coreN := R.coreN
  coreC := R.coreC

/-- `vg_ecdsa_<curve>_sign`. -/
def signCode (R : RfcCurve) (tries : Nat) (vs : List MdHash) : Prog isa := signT (cfgT R tries vs)

/-- The stack it uses: the most of any hash function's. -/
def stackT : Nat := 520

/-! ## The variants -/

/-- What the code needs of a variant `w`: its hash function has HMAC (over
`w`'s block size), its index is one of the code's, and that index's code is
for `w`'s digest length and block size; and the working space of `w`'s
streaming functions fits the one in `scratch`. -/
def WOk (w : MdHash) : Prop :=
  (match Spec.Ecdsa.Rfc6979.hmacOf w.mgf.G with
    | some F => F.blockSize = w.H.P.B
    | none => False) ∧
  Spec.HashTable.index w.mgf.G < 8 ∧ shapeOf (Spec.HashTable.index w.mgf.G) = (w.H.D, w.H.P.B) ∧
  w.H.P.so + 48 ≤ 1408

instance (w : MdHash) : Decidable (WOk w) := by
  unfold WOk; cases Spec.Ecdsa.Rfc6979.hmacOf w.mgf.G <;> infer_instance

/-- What the registrations check of the variants whose tables the function
takes. -/
def OK (vs : List MdHash) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ [] ∧ ∀ w ∈ vs, WOk w

instance (vs : List MdHash) : Decidable (OK vs) := by unfold OK; infer_instance

theorem shapeOf_mem (i : Nat) : shapeOf i ∈ shapes := by
  unfold shapeOf; split <;> simp [shapes]

theorem mdHashes_sub {G : Spec.Mgf1.Hash} (h : G ∈ Proof.Pbkdf2.Md.X86_64.mdHashes) : G ∈ Spec.Mgf1.hashes := by
  simp only [Proof.Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Spec.Mgf1.hashes]

/-- The HMAC of `w`'s hash function. -/
theorem WOk.hmac {w : MdHash} (hw : WOk w) : Spec.Ecdsa.Rfc6979.hmacOf w.mgf.G = some w.ok.SH.H := by
  have h := hw.1
  revert h
  cases hF : Spec.Ecdsa.Rfc6979.hmacOf w.mgf.G with
  | none => intro h; exact h.elim
  | some F =>
    intro hb
    have hh := Spec.Ecdsa.Rfc6979.hmacOf_hash _ (mdHashes_sub w.mgf.mem) F hF
    congr 1
    cases F
    rw [Spec.Hmac.HashFunction.mk.injEq]
    exact ⟨hb.trans w.ok.hB.symm, funext fun x => (congrFun hh x).trans (w.mgf.hash x)⟩

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : MdHash) : Spec.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.ok.SH.H
  hashLen := w.H.D
  hashName := ""
  hashTitle := ""
  tries := T.tries

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = R.inst
  tries_pos : 0 < T.tries
  tries_lt : T.tries < 2 ^ 32

/-- The proof's hash function: `w`, the functions an indirect call of the
table's reaches those of `vs`. -/
def hashOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List MdHash)
    (w : MdHash) (hw : WOk w) : RfcHash where
  R := R
  I := instOf T w
  H := w.H
  ok := w.ok
  f := fnsOf vs
  fInit := (fnsGood_of vs).1
  fUpd := (fnsGood_of vs).2.1
  fFin := (fnsGood_of vs).2.2
  ecdsa := hC.ecdsa
  hash := rfl
  len := rfl
  tries_pos := hC.tries_pos
  tries_lt := hC.tries_lt
  hDB := hw.2.2.1 ▸ shapeOf_mem _
  hS := by have := w.ok.N_le; have := w.ok.B_le; show _ + _ ≤ 192; omega
  hWb := hw.2.2.2

theorem cfgT_eq {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List MdHash)
    {w : MdHash} (hw : WOk w) : cfgT R T.tries vs (Spec.HashTable.index w.mgf.G) = cfgOf (hashOf hC vs w hw) := by
  unfold cfgT cfgOf; rw [hw.2.2.1]; rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : MdHash) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.mgf.G w.ok.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.mgf.len]

/-! ## The contract on entry -/

/-- The state on entry with `scratch` in `rcx`, as `entry` leaves it. -/
def entryOf (s : State) : State := { s with gpr := fun r => if r = .rcx then s.gpr .r8 else s.gpr r }

/-- What the contract with the table of `w` says on entry: the contract the
proof is written against, of the state `entry` leaves, and the table's index. -/
def PreW (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) (w : MdHash) (s : State) :
    Prop :=
  (rfcX86_64 R.E.combConsts (instOf T w) stackT (tabFacts w.H.stream (fnsOf vs)) (names vs)).pre (entryOf s) ∧
    s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table at `r9` is. -/
def tabK (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW R T vs w s →
    match (T.result w.mgf.G w.ok.SH.H s.mem (s.gpr .rsi) (s.gpr .rdx)).1 with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .rdi) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .rdi) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s₁ ∧ PreW R T vs w s₂ ∧
    (rfcX86_64 R.E.combConsts (instOf T w) stackT (tabFacts w.H.stream (fnsOf vs)) (names vs)).pub
      (entryOf s₁) (entryOf s₂)

/-! ## From the entry to the frame -/

/-- The contract the proof is written against, for less stack. -/
theorem rfc_mono {cs : List (String × List (BitVec 64))} {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat}
    {F : State → Prop} {ns : List String} {s : State} (hS : S' ≤ S) (h : (rfcX86_64 cs I S F ns).pre s) :
    (rfcX86_64 cs I S' F ns).pre s := by
  obtain ⟨hsp, hrd, hwr, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd, ng, nc, ⟨held, ht⟩, n9,
    tout, tsc, tret, tstk, hF⟩ := h
  have hsub : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 S', S'⟩ ⟨s.gpr .rsp - BitVec.ofNat 64 S, S⟩ :=
    Offset.sub_below _ hS (by omega)
  refine ⟨by omega, hrd, hwr, od, og, oc, dc, gc, ro, rd, rg, rc, ko.sub_left hsub, kd.sub_left hsub,
    kg.sub_left hsub, kc.sub_left hsub, no, nd, ng, nc, ⟨held, fun t htm => ⟨(ht t htm).1, fun r hr => ?_⟩⟩, n9,
    tout, tsc, tret, tstk.sub_right hsub, hF⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (ht t htm).2 _ (by simp)
  · exact (ht t htm).2 _ (by simp)
  · exact (ht t htm).2 _ (by simp)
  · exact ((ht t htm).2 _ (by simp)).sub_right hsub

/-- The contract the proof is written against, of a state with the same
arguments, regions, memory and symbols. -/
theorem rfc_congr {cs : List (String × List (BitVec 64))} {I : Spec.Ecdsa.Rfc6979.Instance} {S : Nat}
    {G : Impl.Pbkdf2.Md.X86_64.Stream} {f : Impl.Mgf1.X86_64.Table.Fns} {ns : List String} {s t : State}
    (h : (rfcX86_64 cs I S (tabFacts G f) ns).pre s)
    (hg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .rsp], t.gpr r = s.gpr r) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hm : t.mem = s.mem) (hsy : t.syms = s.syms) : (rfcX86_64 cs I S (tabFacts G f) ns).pre t := by
  have e₁ := hg .rdi (by simp); have e₂ := hg .rsi (by simp); have e₃ := hg .rdx (by simp)
  have e₄ := hg .rcx (by simp); have e₅ := hg .r9 (by simp); have e₆ := hg .rsp (by simp)
  simp only [rfcX86_64, TblsOk, tabFacts] at h ⊢
  rw [e₁, e₂, e₃, e₄, e₅, e₆, hrd, hwr, hm, hsy]
  exact h


/-! ## Correctness -/

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List MdHash}

/-- A table's index names its hash function. -/
theorem index_inj {G G' : Spec.Mgf1.Hash} (hG : G ∈ Proof.Pbkdf2.Md.X86_64.mdHashes)
    (hG' : G' ∈ Proof.Pbkdf2.Md.X86_64.mdHashes) (h : Spec.HashTable.index G = Spec.HashTable.index G') : G = G' := by
  simp only [Proof.Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG hG'
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hG' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; revert h; decide)

/-- Two variants whose tables have the same index have the same hash function. -/
theorem same_hash {w w' : MdHash} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 64 (Spec.HashTable.index w'.mgf.G) = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)) :
    w'.mgf.G = w.mgf.G ∧ w'.ok.SH.H = w.ok.SH.H := by
  have e : Spec.HashTable.index w'.mgf.G = Spec.HashTable.index w.mgf.G := by
    have h₁ := hw.2.1; have h₂ := hw'.2.1
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hG := index_inj w'.mgf.mem w.mgf.mem e
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-- `entry`: `scratch` to `rcx`, the table's index to `r11`. -/
theorem entry_ok {w : MdHash} {s : State} (h : PreW R T vs w s) :
    WP isa (.block entry) s fun t => (∀ r, r ≠ .rcx → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.gpr .rcx = s.gpr .r8 ∧
      t.gpr .r11 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.syms = s.syms := by
  obtain ⟨⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, n9, -⟩, hi⟩ := h
  have ht : InRegions (s.rd ++ s.wr) (s.gpr .r9 + BitVec.ofNat 64 24) 8 :=
    ⟨⟨s.gpr .r9, 40⟩, by
      rw [show s.rd = (entryOf s).rd from rfl, hrd]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))),
      Offset.contains_base _ (by decide) (by have : (entryOf s).gpr .r9 = s.gpr .r9 := rfl; omega)⟩
  apply WP.of_runBlock
  simp only [entry, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, reduceCtorEq, ite_false, ht,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r h₁ h₂ => ?_, ?_, hi, trivial, trivial, trivial, rfl⟩
  · simp [h₁, h₂]
  · simp

end VG.Proof.Ecdsa.Rfc6979.X86_64
