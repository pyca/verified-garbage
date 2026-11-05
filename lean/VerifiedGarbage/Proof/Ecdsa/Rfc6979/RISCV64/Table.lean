module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.CT
public import VerifiedGarbage.Proof.HmacTable.RISCV64
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.RISCV64.Syms

/-!
# Deterministic ECDSA on RISC-V: the HMAC of a table

`vg_ecdsa_<curve>_sign` (`signCodeT`) is one body (`cfgT`, the same for
every hash function), which loads `D` and `B` from the table `hmac` and calls
the table's functions. For the hash functions `vs` whose tables it takes
(`OK`: their functions of the same name have the same code), the table of
each `w` makes the body the code for `w`'s hash function (`rfcOf`, whose
configuration is `cfgT` by `rfl`), which meets the contract with that hash
function fixed (`correct`, `ct`). `tabK` states that contract for whichever
of the tables `hmac` holds, on entry, which `TableSpec.lean` shows
`TableInstance.signContract` implies.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG VG.RISCV64 VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Proof.HmacTable.RISCV64 (HVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)

/-! ## The code -/

/-- What the code and the proof need of a curve: its kit, the name of the
signature with a given `k`, and whether its scalars are longer than every
digest. -/
structure CurveT where
  kit : Kit
  coreN : String
  big : Bool := false
  hbig : big = true ↔ 64 < kit.Q
  hGv : kit.G = if big then 64 else kit.Q
  hsh : big = false → kit.sh = 0

/-- The body, on the curve `R`, with the bound on candidates `tries` and the
tables of `vs`: the same for every hash function. -/
def cfgT (R : CurveT) (tries : Nat) (vs : List HVar) : Cfg where
  f := fnsOf vs
  FN := R.kit.FN
  coreN := R.coreN
  coreC := R.kit.coreC
  tries := tries
  nw := R.kit.nw
  Q := R.kit.Q
  big := R.big
  G := R.kit.G

/-- `vg_ecdsa_<curve>_sign`. -/
def signCodeT (R : CurveT) (tries : Nat) (vs : List HVar) : Prog isa := (cfgT R tries vs).sign

/-- The taint checks hold whatever the tables. -/
theorem checks_vs {R : CurveT} {tries : Nat} (h : Checks (cfgT R tries [])) (vs : List HVar) :
    Checks (cfgT R tries vs) :=
  ⟨h.pro, h.px, h.ph, h.kv, h.sep0, h.sep1, h.ia, h.uF, h.uV, h.uR, h.tc0, h.tc1, h.tc2, h.fF, h.fVc, h.fR,
    h.cnt, h.ti, h.ka, h.cl, h.ts, h.ca, h.go, h.ag, h.st, h.fin⟩

/-- What the registrations check of the hash functions whose tables the
function takes: the functions of the same name have the same code, there
are fewer than `2 ^ 32` names, and there is one. -/
def OK (vs : List HVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ []

instance (vs : List HVar) : Decidable (OK vs) := by unfold OK; infer_instance

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) : Spec.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.t.l.ok.SH.H
  hashLen := w.H.D
  hashName := ""
  hashTitle := ""
  tries := T.tries

/-- What each curve's file shows of its curve and instance. -/
structure CurveOk (R : CurveT) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = R.kit.E
  tries_pos : 1 ≤ T.tries
  tries_lt : T.tries < 2048

/-- The proof's instance: `w`'s hash function, the functions an indirect call
of the table's reaches those of `vs`. -/
def rfcOf {R : CurveT} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveOk R T) (vs : List HVar) (w : HVar) :
    Rfc where
  c := cfgT R T.tries vs
  w := w
  I := instOf T w
  kit := R.kit
  hE := hC.ecdsa
  hHash := rfl
  hD := rfl
  hnw := rfl
  hQ := rfl
  hG := rfl
  hbig := R.hbig
  hGv := R.hGv
  hsh := R.hsh
  hct := rfl
  hT := hC.tries_pos
  hT' := hC.tries_lt
  hFN := rfl
  hcC := rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.G w.t.l.ok.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, HVar.G,
    w.t.l.len]

/-! ## The contract on entry -/

/-- The contract with the table of `w`, and its index. -/
def PreW (R : CurveT) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (rfcRC R.kit.K (instOf T w) w (fnsOf vs) (names vs) stackT).pre s ∧
    s.mem.readW (s.gpr .a5 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table at `a5` is. -/
def tabK (R : CurveT) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, PreW R T vs w s
  post s s' := ∀ w ∈ vs, PreW R T vs w s →
    match (T.result w.G w.t.l.ok.SH.H s.mem (s.gpr .a1) (s.gpr .a2)).1 with
    | some rs => (s'.gpr .a0).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .a0) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => (s'.gpr .a0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .a0) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, PreW R T vs w s₁ ∧ PreW R T vs w s₂ ∧
    (rfcRC R.kit.K (instOf T w) w (fnsOf vs) (names vs) stackT).pub s₁ s₂

theorem index_lt (w : HVar) : Spec.HashTable.index w.G < 2 ^ 64 := by
  have h := w.t.idx
  have : Spec.HashTable.index w.G < Spec.Mgf1.hashes.length := by
    rcases Nat.lt_or_ge (Spec.HashTable.index w.G) Spec.Mgf1.hashes.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  exact Nat.lt_of_lt_of_le this (by decide)

/-- Two hash functions whose tables have the same index are the same, with
the same HMAC. -/
theorem same_hash {w w' : HVar}
    (h : BitVec.ofNat 64 (Spec.HashTable.index w'.G) = BitVec.ofNat 64 (Spec.HashTable.index w.G)) :
    w'.G = w.G ∧ w'.t.l.ok.SH.H = w.t.l.ok.SH.H := by
  have e : Spec.HashTable.index w'.G = Spec.HashTable.index w.G := by
    have h₁ := index_lt w; have h₂ := index_lt w'
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h₂, Nat.mod_eq_of_lt h₁] at this
    exact this
  have hG : w'.G = w.G := by
    have a := w'.t.idx; have b := w.t.idx
    simp only [HVar.G] at e
    rw [e, b] at a
    exact (Option.some.inj a).symm
  refine ⟨hG, ?_⟩
  have h₁ := w.hmac; have h₂ := w'.hmac
  have hG' : w'.t.l.G = w.t.l.G := hG
  rw [hG'] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

variable {R : CurveT} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar}

/-- `vg_ecdsa_<curve>_sign` meets `tabK`. -/
theorem signT_ok (hC : CurveOk R T) {s : State} (h : (tabK R T vs).pre s) :
    ∃ t s', Exec isa (signCodeT R T.tries vs) s t s' ∧ abiPreserved s s' ∧ (tabK R T vs).post s s' := by
  obtain ⟨w, -, hp, hix⟩ := h
  obtain ⟨t, s', he, ha, hpost⟩ := correct (P := rfcOf hC vs w) (ns := names vs) hp
  refine ⟨t, s', he, ha, fun w' _ hp' => ?_⟩
  obtain ⟨hG, hH⟩ := same_hash (hp'.2.symm.trans hix)
  rw [hG, hH]
  have hpost' : match ((instOf T w).result s.mem (s.gpr .a1) (s.gpr .a2)).1 with
      | some rs => (s'.gpr .a0).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0)
          (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
      | none => (s'.gpr .a0).setWidth 32 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0)
          (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
  rw [tresult_eq] at hpost'
  exact hpost'

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table, whose hash function's code is the body. -/
theorem signT_ct (hC : CurveOk R T) (hc : Checks (cfgT R T.tries [])) :
    ConstantTime isa (tabK R T vs).pre (tabK R T vs).pub (signCodeT R T.tries vs) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  have hns : ∀ n ∈ [w.hiN, w.H.updN, w.hfN], n ∈ names vs := by
    have := mem_names hv
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  exact ct (P := rfcOf hC vs w) (checks_vs hc vs) hns s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- `vg_ecdsa_<curve>_sign`, against any contract `tabK` implies. -/
theorem signT_verified (hC : CurveOk R T) (hc : Checks (cfgT R T.tries [])) {C : Contract isa}
    (himp : (tabK R T vs).Implies C) : Verified RISCV64.target (signCodeT R T.tries vs) C :=
  Verified.of_correct (fun _ h => signT_ok hC h) (signT_ct hC hc) himp

end VG.Proof.Ecdsa.Rfc6979.RISCV64
