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
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.CT
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.ByIdx
meta import VerifiedGarbage.Proof.HashTable.X86_64
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.Offset

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


theorem idx_mem {w : MdHash} (hw : WOk w) : Spec.HashTable.index w.mgf.G ∈ idxs := by
  have := hw.2.1
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- The frame of the hash function's code fits the stack. -/
theorem stack_le (P : RfcHash) : 248 + 8 * P.e ≤ stackT := by
  have : P.e ≤ 34 := by nums
  show _ ≤ 520; omega

/-- After `entry` and the comparisons: the contract with `w`'s hash function fixed. -/
theorem pre_at (hC : CurveT R T) {w : MdHash} (hw : WOk w) {s t : State} (hp : PreW R T vs w s)
    (hg : ∀ r, r ≠ .rcx → r ≠ .r11 → t.gpr r = s.gpr r) (hcx : t.gpr .rcx = s.gpr .r8) (hm : t.mem = s.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsy : t.syms = s.syms) :
    (rfcP (hashOf hC vs w hw) (names vs)).pre t :=
  rfc_mono (stack_le _) (rfc_congr hp.1 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by decide) (by decide)
    · exact hg _ (by decide) (by decide)
    · exact hg _ (by decide) (by decide)
    · exact hcx
    · exact hg _ (by decide) (by decide)
    · exact hg _ (by decide) (by decide)) hrd hwr hm hsy)

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers and its return address. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    WP isa (signCode R T.tries vs) s fun s' => gprPreserved s s' ∧ (tabK R T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCode signT
  refine WP.seq (WP.mono (entry_ok hp) fun t ⟨hg, hcx, h11, hm, hrd, hwr, hsy⟩ => ?_)
  refine byIdx_wp (idx_mem hw) cmpOk_idxs h11 fun t' k' hm' sy' _ => ?_
  rw [cfgT_eq hC vs hw]
  have hg' : ∀ r, r ≠ .rcx → r ≠ .r11 → t'.gpr r = s.gpr r := fun r h₁ h₂ =>
    (k'.gpr (by simp)).trans (hg r h₁ h₂)
  have hpre := pre_at hC hw hp hg' ((k'.gpr (by simp)).trans hcx) (hm'.trans hm) (k'.2.1.trans hrd)
    (k'.2.2.trans hwr) (sy'.trans hsy)
  refine WP.mono (sign_ok hpre) fun s' ⟨⟨hcs, hret⟩, hpost⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [hcs r hr, hg' r (ne_cs hr (by decide)) (ne_cs hr (by decide))]
  · rw [hg' .rsp (by decide) (by decide), hm'.trans hm] at hret; exact hret
  · intro w' _ hw' hp'
    obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.symm.trans hp.2)
    have e₁ := hg' .rsi (by decide) (by decide)
    have e₂ := hg' .rdx (by decide) (by decide)
    have e₃ := hg' .rdi (by decide) (by decide)
    rw [hG, hH]
    have hpost' : match ((instOf T w).result t'.mem (t'.gpr .rsi) (t'.gpr .rdx)).1 with
      | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (t'.gpr .rdi)
          (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (t'.gpr .rdi)
          (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
    rw [tresult_eq, e₁, e₂, e₃, hm'.trans hm] at hpost'
    exact hpost'


/-! ## Constant time -/

/-- Public data that agree. -/
theorem pub_trans {cs : List (String × List (BitVec 64))} {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h₁ : (rfcX86_64 cs I S F ns).pub a b)
    (h₂ : (rfcX86_64 cs I S F ns).pub a c) : (rfcX86_64 cs I S' F' ns).pub b c := by
  obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, p₉⟩ := h₁
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := h₂
  exact ⟨p₁.symm.trans q₁, p₂.symm.trans q₂, p₃.symm.trans q₃, p₄.symm.trans q₄, p₅.symm.trans q₅,
    p₆.symm.trans q₆, p₇.symm.trans q₇, fun c hc => (p₈ c hc).symm.trans (q₈ c hc),
    fun n hn => (p₉ n hn).symm.trans (q₉ n hn)⟩

theorem pub_refl {cs : List (String × List (BitVec 64))} {I : Spec.Ecdsa.Rfc6979.Instance} {S : Nat}
    {F : State → Prop} {ns : List String} (a : State) : (rfcX86_64 cs I S F ns).pub a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Public data of a state with the same arguments, memory and symbols. -/
theorem pub_congr {cs : List (String × List (BitVec 64))} {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h : (rfcX86_64 cs I S F ns).pub a b)
    (hg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .rsp], c.gpr r = b.gpr r) (hm : c.mem = b.mem)
    (hsy : c.syms = b.syms) : (rfcX86_64 cs I S' F' ns).pub a c := by
  have e₁ := hg .rdi (by simp); have e₂ := hg .rsi (by simp); have e₃ := hg .rdx (by simp)
  have e₄ := hg .rcx (by simp); have e₅ := hg .r9 (by simp); have e₆ := hg .rsp (by simp)
  simp only [rfcX86_64] at h ⊢
  rw [e₁, e₂, e₃, e₄, e₅, e₆, hm, hsy]
  exact h

/-- The proof's hash function and the public data: the variant `w` (by its
place in `vs`), and the state the other run agrees with. -/
abbrev Anc (vs : List MdHash) := Fin vs.length × State

/-- The variant of `a`. -/
abbrev Anc.w (a : Anc vs) : MdHash := vs.get a.1

theorem Anc.hv (a : Anc vs) : a.w ∈ vs := List.get_mem _ _

/-- After `entry`: the contract with `a.w`'s hash function fixed, public
data that agree with `a.2`'s, and the table's index in `r11`. -/
def PhiT (hC : CurveT R T) (hO : ∀ w ∈ vs, WOk w) (a : Anc vs) (t : State) : Prop :=
  (rfcP (hashOf hC vs a.w (hO _ a.hv)) (names vs)).pre t ∧
    (rfcP (hashOf hC vs a.w (hO _ a.hv)) (names vs)).pub a.2 t ∧
    t.gpr .r11 = BitVec.ofNat 64 (Spec.HashTable.index a.w.mgf.G)

/-- `entry`'s effect, from the state on entry `σ`. -/
def EntryF (σ u : State) : Prop :=
  (∀ r, r ≠ .rcx → r ≠ .r11 → u.gpr r = σ.gpr r) ∧ u.gpr .rcx = σ.gpr .r8 ∧
    u.gpr .r11 = σ.mem.readW (σ.gpr .r9 + BitVec.ofNat 64 24) 64 ∧ u.mem = σ.mem ∧ u.rd = σ.rd ∧ u.wr = σ.wr ∧
    u.syms = σ.syms

theorem entryF_ok {w : MdHash} {s : State} (h : PreW R T vs w s) : WP isa (.block entry) s (EntryF s) :=
  WP.mono (entry_ok h) fun _ ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c.trans h.2.symm, d, e, f, g⟩

theorem entry_taint : TaintOk [.r9] entry := ⟨_, by taint_decide⟩

/-- Runs whose public data agree: the same table, read at the same address. -/
theorem entry_ct :
    RelCT isa (fun s₁ s₂ => (tabK R T vs).pre s₁ ∧ (tabK R T vs).pre s₂ ∧ (tabK R T vs).pub s₁ s₂) (.block entry)
      fun u₁ u₂ => ∃ σ₁ σ₂, ((tabK R T vs).pre σ₁ ∧ (tabK R T vs).pre σ₂ ∧ (tabK R T vs).pub σ₁ σ₂) ∧
        EntryF σ₁ u₁ ∧ EntryF σ₂ u₂ := by
  obtain ⟨_, ht⟩ := entry_taint
  refine (RelCT.wpDep (F := EntryF) (RelCT.taint (A := taint) (Taint.ofRegs [.r9])
      (fun _ _ ⟨_, _, ⟨_, _, _, _, _, ⟨_, _, _, _, _, p₉, _⟩⟩⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact p₉) ht)
    fun _ _ ⟨⟨_, _, _, h₁⟩, ⟨_, _, _, h₂⟩, _⟩ => ⟨entryF_ok h₁, entryF_ok h₂⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

theorem cmp_taint (j : Nat) : TaintOk [] [.alu .cmp .r11 (.imm (BitVec.ofNat 32 j))] :=
  taintOk_erase (is₀ := [.alu .cmp .r11 (.imm (BitVec.ofNat 32 0))]) ⟨_, by taint_decide⟩ rfl

theorem phiT_keep (hC : CurveT R T) (hO : ∀ w ∈ vs, WOk w) (a : Anc vs) (t t' : State) (h : PhiT hC hO a t)
    (k : VG.Proof.MlKem.X86_64.Keep [] t t') (hm : t'.mem = t.mem) (hsy : t'.syms = t.syms) : PhiT hC hO a t' :=
  ⟨rfc_congr h.1 (fun r _ => k.gpr (by simp)) k.2.1 k.2.2 hm hsy,
    pub_congr h.2.1 (fun r _ => k.gpr (by simp)) hm hsy, (k.gpr (by simp)).trans h.2.2⟩

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table's branch, which is constant time for its hash function. -/
theorem signT_ct (hC : CurveT R T) (hO : ∀ w ∈ vs, WOk w) : ConstantTime isa (tabK R T vs).pre (tabK R T vs).pub (signCode R T.tries vs) := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold signCode signT
  refine entry_ct.seq ((byIdx_ct (α := Anc vs) (b := fun i => (cfgT R T.tries vs i).sign) (Q := fun _ _ => True)
    (fun a : Anc vs => Spec.HashTable.index a.w.mgf.G) (Φ := PhiT hC hO) (phiT_keep hC hO)
    (fun (a : Anc vs) _ h => ⟨idx_mem (hO _ a.hv), h.2.2⟩) cmpOk_idxs
    (fun j _ => let ⟨_, ht⟩ := cmp_taint j; RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs fun r hr => absurd hr (by simp)) ht)
    fun j _ => ?_).mono ?_ fun _ _ h => h)
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, ⟨h₁, e⟩, ⟨h₂, _⟩⟩ e₁ e₂
    subst e
    rw [cfgT_eq hC vs (hO _ a.hv)] at e₁ e₂
    have hns : ∀ n ∈ [(hashOf hC vs a.w (hO _ a.hv)).H.stream.initN, (hashOf hC vs a.w (hO _ a.hv)).H.stream.updN,
        (hashOf hC vs a.w (hO _ a.hv)).H.stream.finN], n ∈ names vs := by
      have := mem_names a.hv
      intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl
      · exact this.1
      · exact this.2.1
      · exact this.2.2
    exact ⟨sign_ct hns s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1 (pub_trans h₁.2.1 h₂.2.1) e₁ e₂, trivial⟩
  · rintro u₁ u₂ ⟨σ₁, σ₂, ⟨_, _, w, hv, hw, p₁, p₂, hpub⟩, f₁, f₂⟩
    have reg : ∀ {σ u : State}, EntryF σ u → ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .rsp],
        u.gpr r = (entryOf σ).gpr r := fun {σ u} f r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact f.1 _ (by decide) (by decide)
      · exact f.1 _ (by decide) (by decide)
      · exact f.1 _ (by decide) (by decide)
      · exact f.2.1
      · exact f.1 _ (by decide) (by decide)
      · exact f.1 _ (by decide) (by decide)
    have q₁ := pre_at hC hw p₁ f₁.1 f₁.2.1 f₁.2.2.2.1 f₁.2.2.2.2.1 f₁.2.2.2.2.2.1 f₁.2.2.2.2.2.2
    have q₂ := pre_at hC hw p₂ f₂.1 f₂.2.1 f₂.2.2.2.1 f₂.2.2.2.2.1 f₂.2.2.2.2.2.1 f₂.2.2.2.2.2.2
    obtain ⟨k, rfl⟩ := List.get_of_mem hv
    have pu : (rfcP (hashOf hC vs (vs.get k) (hO _ (List.get_mem _ _))) (names vs)).pub u₁ u₂ :=
      pub_trans (a := entryOf σ₁) (S := stackT) (F := tabFacts (vs.get k).H.stream (fnsOf vs))
        (pub_congr (pub_refl (S := stackT) (F := tabFacts (vs.get k).H.stream (fnsOf vs)) _) (reg f₁)
          f₁.2.2.2.1 f₁.2.2.2.2.2.2)
        (pub_congr hpub (reg f₂) f₂.2.2.2.1 f₂.2.2.2.2.2.2)
    exact ⟨(k, u₁), ⟨q₁, pub_refl _, f₁.2.2.1.trans p₁.2⟩, ⟨q₂, pu, f₂.2.2.1.trans p₂.2⟩⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64
