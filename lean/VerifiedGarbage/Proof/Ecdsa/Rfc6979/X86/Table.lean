module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CT
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Instrs
public import VerifiedGarbage.Proof.HmacTable.X86
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame

/-!
# Deterministic ECDSA on x86 (32-bit): the HMAC of a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`): `vg_ecdsa_<curve>_sign`
(`signCodeT`) is the one body (`cfgT`, the same for every hash function),
which loads `D` and `B`, the digest length and HMAC's block size, from the
table `hmac` (its words 4 and 5) and calls the table's functions. For the
variants `vs` of the hash functions that pass the registration's checks
(`OK`: their functions of the same name have the same code, and each is of
one of the hash functions with HMAC, of sizes the frame holds), the table of
each variant `w` makes the body the code for `w`'s hash function (`hashOf`,
with `cfgT_eq`, which holds by `rfl`), which meets the contract with that
hash function fixed (`sign_ok`, `sign_ct`). `tabK` states that contract for
whichever of the tables `hmac` holds; `TableSpec.lean` shows
`TableInstance.signContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.HmacTable.X86 (HVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)

/-! ## The code -/

/-- The body, on the curve `R`, with the bound on candidates `tries` and the
tables of `vs`: the same for every hash function. -/
def cfgT (R : RfcCurve) (tries : Nat) (vs : List HVar) : Cfg where
  f := fnsOf vs
  w := 2 * R.E.n - (if R.E.C.len = 28 then 1 else 0)
  len := R.E.C.len
  big := R.big
  sh := R.sh
  n := R.E.C.n
  tries := tries
  coreN := R.coreN
  coreC := R.coreC

/-- `vg_ecdsa_<curve>_sign`. -/
def signCodeT (R : RfcCurve) (tries : Nat) (vs : List HVar) : Prog isa := signCode (cfgT R tries vs)

/-- The stack it uses. -/
def stackT : Nat := 588

/-! ## The variants -/

/-- What the code needs of a variant `w`: its hash function has HMAC (over
`w`'s block size), of one of the digest lengths and block sizes the frame
holds, and the states and working space of `w`'s HMAC fit the frame and
`scratch`. -/
def WOk (w : HVar) : Prop :=
  (match Spec.HmacTable.hmacOf w.G with
    | some F => F.blockSize = w.F.H.B
    | none => False) ∧
  (w.F.H.D, w.F.H.B) ∈ shapes ∧ w.F.H.S ≤ 192 ∧ w.ok.Wi * 8 ≤ 1872 ∧ w.ok.Wf * 8 ≤ 1872 ∧ w.ok.hH.Wb ≤ 1872

instance (w : HVar) : Decidable (WOk w) := by
  unfold WOk; cases Spec.HmacTable.hmacOf w.G <;> infer_instance

/-- What the registrations check of the variants whose tables the function
takes. -/
def OK (vs : List HVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ [] ∧ ∀ w ∈ vs, WOk w

instance (vs : List HVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem hvar_mem (w : HVar) : w.G ∈ Spec.Mgf1.hashes := List.mem_of_getElem? w.idx

/-- The HMAC of `w`'s hash function. -/
theorem WOk.hmac {w : HVar} (hw : WOk w) : Spec.HmacTable.hmacOf w.G = some w.ok.hH.SH.H := by
  have h := hw.1
  revert h
  cases hF : Spec.HmacTable.hmacOf w.G with
  | none => intro h; exact h.elim
  | some F =>
    intro hb
    have hh := Spec.HmacTable.hmacOf_hash _ (hvar_mem w) F hF
    congr 1
    cases F
    rw [Spec.Hmac.HashFunction.mk.injEq]
    exact ⟨hb.trans w.ok.hH.hB.symm, funext fun x => (congrFun hh x).trans (w.hash x)⟩

/-- HMAC's block size, as the table holds it. -/
theorem WOk.blockSize {w : HVar} (hw : WOk w) : Spec.HmacTable.blockSize w.G = w.F.H.B := by
  simp only [Spec.HmacTable.blockSize, hw.hmac, Option.map_some, Option.getD_some]
  exact w.ok.hH.hB

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) : Spec.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.ok.hH.SH.H
  hashLen := w.F.H.D
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
def hashOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List HVar)
    (w : HVar) (hw : WOk w) : RfcHash where
  R := R
  I := instOf T w
  F := w.F
  ok := w.ok
  f := fnsOf vs
  ecdsa := hC.ecdsa
  hash := rfl
  len := rfl
  macLen := w.hlen
  tries_pos := hC.tries_pos
  tries_lt := hC.tries_lt
  hDB := hw.2.1
  hS := hw.2.2.1
  hWi := hw.2.2.2.1
  hWf := hw.2.2.2.2.1
  hWb := hw.2.2.2.2.2

/-- The body for `w`'s hash function is the same as for every other. -/
theorem cfgT_eq {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List HVar)
    {w : HVar} (hw : WOk w) : cfgT R T.tries vs = cfgOf (hashOf hC vs w hw) := rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.G w.ok.hH.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.glen]

/-! ## The contract -/

/-- What the contract with the table of `w` says: the contract the proof is
written against, and the table's index. -/
def PreW (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (w : HVar) (s : State) :
    Prop :=
  (rfcX86 R.E.combConsts (instOf T w) stackT (tabFacts w.F (fnsOf vs)) (names vs)).pre s ∧
    s.mem.readW (addr (arg s 5) 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table `hmac` is. -/
def tabK (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW R T vs w s →
    match (T.result w.G w.ok.hH.SH.H s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
        bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
        bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s₁ ∧ PreW R T vs w s₂ ∧
    (rfcX86 R.E.combConsts (instOf T w) stackT (tabFacts w.F (fnsOf vs)) (names vs)).pub s₁ s₂

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar}

theorem index_lt (w : HVar) : Spec.HashTable.index w.G < Spec.Mgf1.hashes.length :=
  (List.getElem?_eq_some_iff.mp w.idx).1

/-- Two variants whose tables have the same index have the same hash function. -/
theorem same_hash {w w' : HVar} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 32 (Spec.HashTable.index w'.G) = BitVec.ofNat 32 (Spec.HashTable.index w.G)) :
    w'.G = w.G ∧ w'.ok.hH.SH.H = w.ok.hH.SH.H := by
  have e : Spec.HashTable.index w'.G = Spec.HashTable.index w.G := by
    have h₁ := index_lt w; have h₂ := index_lt w'
    have h8 : Spec.Mgf1.hashes.length < 2 ^ 32 := by decide
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hG : w'.G = w.G := Option.some.inj (w'.idx.symm.trans (e ▸ w.idx))
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-! ## No instruction writes `esp` but the frame's -/

theorem okP_of_noSp {c : Prog isa} (h : NoSp c) : OkP c := by
  rw [OkP, Code.allInstrs_eq, List.all_eq_true]
  intro i hi; simp [h i hi]

theorem fnsOk_of (vs : List HVar) : FnsOk (fnsOf vs).init ∧ FnsOk (fnsOf vs).upd ∧ FnsOk (fnsOf vs).fin := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩ <;> obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
  · exact okP_of_noSp w.ok.hiSp
  · exact okP_of_noSp w.ok.hH.updSp
  · exact okP_of_noSp w.ok.hfSp

theorem body_okP_cfgT (R : RfcCurve) (tries : Nat) (vs : List HVar) : OkP (cfgT R tries vs).body :=
  body_okP (c := cfgT R tries vs) R.blk (fnsOk_of vs) (okP_of_noSp R.coreNs)

theorem body_noSp (R : RfcCurve) (tries : Nat) (vs : List HVar) : NoSp (cfgT R tries vs).body :=
  NoSp.of_all (body_okP_cfgT R tries vs)

/-- `esp` is written only by the frame's allocation and release. -/
theorem signCode_sp (R : RfcCurve) (tries : Nat) (vs : List HVar) :
    (signCodeT R tries vs).all (fun i => !isa.writesSp i) = true := by
  refine Code.all_of_allInstrs ?_
  have h := body_okP_cfgT R tries vs
  simp only [OkP, Proof.Pbkdf2.Whole.X86.clobbers_esp] at h
  simp only [signCodeT, signCode, Cfg.sign, Code.allInstrs, h]
  rfl

/-! ## Correct and constant time -/

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers and its return address. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    WP isa (signCodeT R T.tries vs) s fun s' => abiPreserved s s' ∧ (tabK R T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCodeT signCode
  rw [cfgT_eq hC vs hw]
  refine WP.mono (sign_ok (P := hashOf hC vs w hw) (body_noSp R T.tries vs) hp.1) fun s' ⟨hg, hpost⟩ =>
    ⟨hg, fun w' _ hw' hp' => ?_⟩
  obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.symm.trans hp.2)
  rw [hG, hH]
  have hpost' : match ((instOf T w).result s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧ Spec.Ecdsa.bytesAt s'.mem
        ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧ Spec.Ecdsa.bytesAt s'.mem
        ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
  rw [tresult_eq] at hpost'
  exact hpost'

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table, whose hash function's code is the body, constant time
for it. -/
theorem signT_ct (hC : CurveT R T) :
    ConstantTime isa (tabK R T vs).pre (tabK R T vs).pub (signCodeT R T.tries vs) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, hw, p₁, p₂, hpub⟩ e₁ e₂
  unfold signCodeT signCode at e₁ e₂
  rw [cfgT_eq hC vs hw] at e₁ e₂
  have hns : ∀ n ∈ [(hashOf hC vs w hw).F.hiN, (hashOf hC vs w hw).F.H.updN, (hashOf hC vs w hw).F.hfN],
      n ∈ names vs := by
    have := mem_names hv
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  exact sign_ct (P := hashOf hC vs w hw) hns s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

end VG.Proof.Ecdsa.Rfc6979.X86
