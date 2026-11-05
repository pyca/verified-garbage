module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.CT
public import VerifiedGarbage.Proof.HmacTable.Arm
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.Md5.Md
import VerifiedGarbage.Proof.Sha1.Md
import VerifiedGarbage.Proof.Hmac.Generic.Common

/-!
# Deterministic ECDSA on 32-bit ARM: the HMAC of a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`):
`vg_ecdsa_<curve>_sign` (`signCodeT`) runs the one body (`cfgT`, the same
for every hash function), which reads `D` and `B`, the digest length and
HMAC's block size, from the table `hmac` (its words 4 and 5) and calls the
table's functions. For the hash functions `vs` whose tables it takes, of
sizes the frame holds (`OK`: their functions of the same name have the same
code, and each is of one of the hash functions with HMAC on ARMv7, `WOk`),
the table of each `w` makes the body the code for `w`'s hash function
(`hashOf`, with `cfgT_eq`, which holds by `rfl`), which meets the contract
with that hash function fixed (`sign_ok`, `sign_ct`). `tabK` states that
contract for whichever of the tables `hmac` holds, on entry;
`TableSpec.lean` shows `TableInstance.signContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.HmacTable.Arm (HVar vars tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf
  hashAt_tableOf tA)

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
def signCodeT (R : RfcCurve) (tries : Nat) (vs : List HVar) : Prog isa := (cfgT R tries vs).sign

/-! ## The hash functions -/

/-- What the code needs of a hash function `w`: digest length and block
size of one of the hash functions the frame holds, states and working
space no larger than SHA-512's, and digests of `D` bytes. -/
structure WOk (w : HVar) : Prop where
  db : (w.F.H.D, w.F.H.B) ∈ shapes
  hS : w.F.H.S ≤ 192
  hWi : w.ok.Wi * 8 ≤ 1872
  hWf : w.ok.Wf * 8 ≤ 1872
  hWb : w.ok.hH.Wb ≤ 1872
  macLen : ∀ x, (w.ok.hH.SH.H.hash x).length = w.F.H.D

/-- What the proof needs of the hash functions whose tables the function
takes. -/
def OK (vs : List HVar) : Prop := Coh vs ∧ ∀ w ∈ vs, WOk w

theorem sha512_len (iv : Spec.Sha512.HashValue) (n : Nat) (hn : n ≤ 64) (x : List Byte) :
    ((Spec.Sha512.finalHash iv x).take n).length = n := by
  rw [List.length_take, Proof.Hmac.Generic.Common.finalHash_length]; omega

/-- Every hash function with HMAC on ARMv7 meets `WOk`. -/
theorem vars_coh : Coh vars := by
  intro w hw w' hw'
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hw hw'
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> first | rfl | exact absurd h (by decide)

theorem vars_ok : OK vars := by
  refine ⟨vars_coh, fun w hw => ?_⟩
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show (Spec.Md5.hash x).length = 16
        rw [Proof.Md5.hash_eq]; exact Proof.Md5.md.digest_length _⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show (Spec.Sha1.hash x).length = 20
        rw [Proof.Sha1.hash_eq]; exact Proof.Sha1.md.digest_length _⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show (Spec.Sha256.sha224 x).length = 28
        simp [Spec.Sha256.sha224, Spec.Sha256.finalHash, Spec.Sha256.wordBytes, List.length_flatMap,
          List.map_const']⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show (Spec.Sha256.hash x).length = 32
        rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show ((Spec.Sha512.finalHash Spec.Sha512.H0_384 x).take 48).length = 48
        exact sha512_len _ 48 (by decide) x⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show (Spec.Sha512.finalHash Spec.Sha512.H0_512 x).length = 64
        exact Proof.Hmac.Generic.Common.finalHash_length _ _⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show ((Spec.Sha512.finalHash Spec.Sha512.H0_512_224 x).take 28).length = 28
        exact sha512_len _ 28 (by decide) x⟩
  · exact ⟨by decide, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, fun x => by
        show ((Spec.Sha512.finalHash Spec.Sha512.H0_512_256 x).take 32).length = 32
        exact sha512_len _ 32 (by decide) x⟩

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) : Spec.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.ok.hH.SH.H
  hashLen := w.F.H.D
  tries := T.tries

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = R.inst
  tries_pos : 0 < T.tries
  tries_lt : T.tries < 2 ^ 16

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
  macLen := hw.macLen
  tries_pos := hC.tries_pos
  tries_lt := hC.tries_lt
  hDB := hw.db
  hS := hw.hS
  hWi := hw.hWi
  hWf := hw.hWf
  hWb := hw.hWb

/-- The body for `w`'s hash function is the same as for every other. -/
theorem cfgT_eq {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List HVar)
    {w : HVar} (hw : WOk w) : cfgT R T.tries vs = cfgOf (hashOf hC vs w hw) := rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.G w.ok.hH.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.glen]

/-! ## The contract on entry -/

/-- What the contract with the table of `w` says on entry: the contract the
proof is written against, and the table's index. -/
def PreW (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (rfcArm (instOf T w) stackT R.coreConsts (tabFacts w.F (fnsOf vs)) (names vs)).pre s ∧
    s.mem.readW (tA (stackArg s 1) 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table `hmac` is. -/
def tabK (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW R T vs w s →
    match (T.result w.G w.ok.hH.SH.H s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s₁ ∧ PreW R T vs w s₂ ∧
    (rfcArm (instOf T w) stackT R.coreConsts (tabFacts w.F (fnsOf vs)) (names vs)).pub s₁ s₂

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar}

theorem index_lt (w : HVar) : Spec.HashTable.index w.G < Spec.Mgf1.hashes.length :=
  (List.getElem?_eq_some_iff.mp w.idx).1

/-- Two hash functions whose tables have the same index are the same. -/
theorem same_hash {w w' : HVar}
    (h : BitVec.ofNat 32 (Spec.HashTable.index w'.G) = BitVec.ofNat 32 (Spec.HashTable.index w.G)) :
    w'.G = w.G ∧ w'.ok.hH.SH.H = w.ok.hH.SH.H := by
  have e : Spec.HashTable.index w'.G = Spec.HashTable.index w.G := by
    have h₁ := index_lt w; have h₂ := index_lt w'
    have hl : Spec.Mgf1.hashes.length < 2 ^ 32 := by decide
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hG : w'.G = w.G := by
    have h₁ := w.idx; have h₂ := w'.idx
    rw [e, h₁] at h₂
    exact (Option.some.inj h₂).symm
  refine ⟨hG, ?_⟩
  have h₁ := w.hmac; have h₂ := w'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers and the stack pointer. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    WP isa (signCodeT R T.tries vs) s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (tabK R T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCodeT
  rw [cfgT_eq hC vs hw]
  refine WP.mono (sign_ok (P := hashOf hC vs w hw) (ns := names vs) hp.1) fun s' ⟨hpr, hpost⟩ => ⟨hpr, ?_⟩
  intro w' _ hw' hp'
  obtain ⟨hG, hH⟩ := same_hash (hp'.2.symm.trans hp.2)
  rw [hG, hH]
  have hpost' : match ((instOf T w).result s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧ Spec.Ecdsa.bytesAt s'.mem
        (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧ Spec.Ecdsa.bytesAt s'.mem
        (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
  rw [tresult_eq] at hpost'
  exact hpost'

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table, whose hash function's code is the body, constant time
for it. -/
theorem signT_ct (hC : CurveT R T) :
    ConstantTime isa (tabK R T vs).pre (tabK R T vs).pub (signCodeT R T.tries vs) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, hw, p₁, p₂, hpub⟩ e₁ e₂
  unfold signCodeT at e₁ e₂
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

end VG.Proof.Ecdsa.Rfc6979.Arm
