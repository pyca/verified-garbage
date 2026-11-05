module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.CT
public import VerifiedGarbage.Proof.HmacTable.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.CT
meta import VerifiedGarbage.Proof.HmacTable.PPC64LE
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on PPC64LE: the HMAC of a table

`vg_ecdsa_<curve>_sign` (`signCodeT`) is the one body (`cfgT`, the same for
every hash function), which saves `D` and `B`, the digest length and HMAC's
block size, from the table `hmac` (its words 4 and 5) and calls the table's
functions. For the variants `vs` of the hash functions that pass the
registration's checks (`OK`: their functions of the same name have the same
code, and each is of a hash function with HMAC, of sizes the frame holds),
the table of each variant `w` makes the body the code for `w`'s hash
function (`hashOf`, with `cfgT_eq`, which holds by `rfl`), which meets the
contract with that hash function fixed (`sign_ok`, `sign_ct`). `tabK` states
that contract for whichever of the tables `hmac` holds; `TableSpec.lean`
shows `TableInstance.signContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.HmacTable.PPC64LE (HVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf
  hashAt_tableOf)

/-! ## The code -/

/-- The body, on the curve `R`, with the bound on candidates `tries` and the
tables of `vs`: the same for every hash function. -/
def cfgT (R : RfcCurve) (tries : Nat) (vs : List HVar) : Cfg where
  f := fnsOf vs
  w := R.w
  len := R.Q
  big := R.big
  sh := R.sh
  n := R.C.E.curve.n
  tries := tries
  coreN := R.C.N
  coreC := R.C.C

/-- `vg_ecdsa_<curve>_sign`. -/
def signCodeT (R : RfcCurve) (tries : Nat) (vs : List HVar) : Prog isa := (cfgT R tries vs).sign

/-- The stack it uses. -/
def stackT : Nat := 736

/-! ## The variants -/

/-- What the code needs of a variant `w`: its hash function has HMAC (over
`w`'s block size), of one of the digest lengths and block sizes the frame
holds, and the states and working space of `w`'s HMAC fit those in `scratch`. -/
def WOk (w : HVar) : Prop :=
  (match Spec.HmacTable.hmacOf w.l.G with
    | some F => F.blockSize = w.H.B
    | none => False) ∧
  (w.H.D, w.H.B) ∈ shapes ∧ w.H.S ≤ 192 ∧ sWork + w.I.scratch * 8 ≤ sMsg ∧ sWork + w.H.W ≤ sMsg

instance (w : HVar) : Decidable (WOk w) := by
  unfold WOk; cases Spec.HmacTable.hmacOf w.l.G <;> infer_instance

/-- What the registrations check of the variants whose tables the function
takes. -/
def OK (vs : List HVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ [] ∧ ∀ w ∈ vs, WOk w

instance (vs : List HVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem _root_.VG.Proof.HmacTable.PPC64LE.HVar.mem (w : HVar) : w.l.G ∈ Spec.Mgf1.hashes := List.mem_of_getElem? w.idx

/-- The HMAC of `w`'s hash function. -/
theorem WOk.hmac {w : HVar} (hw : WOk w) : Spec.HmacTable.hmacOf w.l.G = some w.l.ok.SH.H := by
  have h := hw.1
  revert h
  cases hF : Spec.HmacTable.hmacOf w.l.G with
  | none => intro h; exact h.elim
  | some F =>
    intro hb
    have hh := Spec.HmacTable.hmacOf_hash _ w.mem F hF
    congr 1
    cases F
    rw [Spec.Hmac.HashFunction.mk.injEq]
    exact ⟨hb.trans w.l.ok.hB.symm, funext fun x => (congrFun hh x).trans (w.l.hash x)⟩

/-- HMAC's block size, as the table holds it. -/
theorem WOk.blockSize {w : HVar} (hw : WOk w) : Spec.HmacTable.blockSize w.l.G = w.H.B := by
  simp only [Spec.HmacTable.blockSize, hw.hmac, Option.map_some, Option.getD_some]
  exact w.l.ok.hB

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) : Spec.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.l.ok.SH.H
  hashLen := w.H.D
  hashName := ""
  hashTitle := ""
  tries := T.tries

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = R.C.E
  tries_pos : 0 < T.tries
  tries_lt : T.tries < 2 ^ 15

/-- The proof's hash function: `w`, the functions an indirect call of the
table's reaches those of `vs`. -/
def hashOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List HVar)
    (w : HVar) (hw : WOk w) : RfcHash where
  R := R
  I := instOf T w
  v := w
  f := fnsOf vs
  ecdsa := hC.ecdsa
  hash := rfl
  len := rfl
  tries_pos := hC.tries_pos
  tries_lt := hC.tries_lt
  hDB := hw.2.1
  hS := hw.2.2.1
  hScr := hw.2.2.2.1
  hW := hw.2.2.2.2

/-- The body for `w`'s hash function is the same as for every other. -/
theorem cfgT_eq {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List HVar)
    {w : HVar} (hw : WOk w) : cfgT R T.tries vs = cfgOf (hashOf hC vs w hw) := rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.l.G w.l.ok.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.l.len]

/-! ## The contract with whichever table `hmac` is -/

/-- What the contract with the table of `w` says: the contract the proof is
written against, and the table's index. -/
def PreW (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (rfcPPC (instOf T w) stackT (tabFacts w (fnsOf vs)) (names vs)).pre s ∧
    s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.l.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table at `r8` is. -/
def tabK (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW T vs w s →
    match (T.result w.l.G w.l.ok.SH.H s.mem (s.gpr .r4) (s.gpr .r5)).1 with
    | some rs => (s'.gpr .r3).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .r3) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .r3) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW T vs w s₁ ∧ PreW T vs w s₂ ∧
    (rfcPPC (instOf T w) stackT (tabFacts w (fnsOf vs)) (names vs)).pub s₁ s₂

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar}

/-- Two variants whose tables have the same index have the same hash function. -/
theorem same_hash {w w' : HVar} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 64 (Spec.HashTable.index w'.l.G) = BitVec.ofNat 64 (Spec.HashTable.index w.l.G)) :
    w'.l.G = w.l.G ∧ w'.l.ok.SH.H = w.l.ok.SH.H := by
  have hl : ∀ v : HVar, Spec.HashTable.index v.l.G < Spec.Mgf1.hashes.length := fun v =>
    (List.getElem?_eq_some_iff.mp v.idx).1
  have h₁ := hl w; have h₂ := hl w'
  have hlen : Spec.Mgf1.hashes.length < 2 ^ 64 := by decide
  have e : Spec.HashTable.index w'.l.G = Spec.HashTable.index w.l.G := by
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hG : w'.l.G = w.l.G := Option.some.inj (w'.idx.symm.trans (e ▸ w.idx))
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers, its stack pointer and its return address. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK T vs).pre s) :
    WP isa (signCodeT R T.tries vs) s fun s' => abiPreserved s s' ∧ (tabK T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCodeT
  rw [cfgT_eq hC vs hw]
  refine WP.mono (sign_ok (P := hashOf hC vs w hw) (ns := names vs) hp.1) fun s' ⟨hab, hpost⟩ => ⟨hab, ?_⟩
  intro w' _ hw' hp'
  obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.symm.trans hp.2)
  rw [hG, hH]
  have hpost' : match ((instOf T w).result s.mem (s.gpr .r4) (s.gpr .r5)).1 with
    | some rs => (s'.gpr .r3).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3)
        (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3)
        (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
  rw [tresult_eq] at hpost'
  exact hpost'

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table, whose hash function's code is the body, constant time
for it. -/
theorem signT_ct (hC : CurveT R T) (B : RfcT (cfgC R.w R.Q R.big R.sh R.C.E.curve.n)) :
    ConstantTime isa (tabK T vs).pre (tabK T vs).pub (signCodeT R T.tries vs) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, hw, p₁, p₂, hpub⟩ e₁ e₂
  unfold signCodeT at e₁ e₂
  rw [cfgT_eq hC vs hw] at e₁ e₂
  have hns : ∀ n ∈ [w.initN, w.H.updN, w.finN], n ∈ names vs := by
    have := mem_names hv
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  exact sign_ct (P := hashOf hC vs w hw) B hns s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
