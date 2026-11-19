module

import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
import VerifiedGarbage.Proof.EcKey.Arm.Finish
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
import VerifiedGarbage.Proof.Ecdh.Arm.Peer
import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Spec.EcKey.Compressed
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Front
import VerifiedGarbage.Proof.Ecdh.Arm.Validate
public import VerifiedGarbage.Impl.Weierstrass.Arm
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Weierstrass.Arm.BytesLen
import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Ecdh.Arm.Main
public import VerifiedGarbage.Impl.EcKey.Compressed
public import VerifiedGarbage.Proof.EcKey.Compressed.Root
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Proof.Weierstrass.Layout

/-! ### `EcKey.Compressed.Arm.Candidate`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.Arm.RootPow`, which this module and modules that import it used -/

section

/-! # The root exponentiation's workspace layout -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG.Impl.Ecdsa.Arm VG.Impl.Ecdh.Arm
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm

/-- The square-root power uses the same accumulator and temporary as the
existing powers, and a table separate from Montgomery's temporary area. -/
theorem rootPow_lay {c : Cfg} (hc : CfgOk c) {j : Nat} (hj : j < 3)
    : PowLay (Impl.EcKey.Compressed.Arm.rootPow c j) size 8192 :=
  powLay_of hc (jm := MP) (by decide) _ hj (base := W2) (by decide) (by decide)
    (one := ONEP) (by decide) (by decide)

theorem rootPow_wk {c : Cfg} (hc : CfgOk c) {j : Nat} :
    PowWk (Impl.EcKey.Compressed.Arm.rootPow c j) size c.wk :=
  powWk_of hc (jm := MP) (by decide) _ (base := W2) (by decide)

/-- The precise writes of one root exponentiation. -/
abbrev rootPowerWrites (c : Cfg) (j : Nat) : List (Nat × Nat) :=
  [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
    powWx (Impl.EcKey.Compressed.Arm.rootPow c j) c.wk

theorem rootPower_apart {c : Cfg} (hc : CfgOk c) {i j : Nat} (hi : i < 45)
    (hw : i ∉ [EXPP, ACC, PT, TMP]) :
    ∀ w ∈ rootPowerWrites c j, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  change ∀ w ∈ [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
    (slW c [ACC, PT, TMP] ++ [(c.wk, 64 * c.n)]), _
  apply apart_append
  · intro w h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact sl_apart c (by intro h; exact hw (h ▸ (by simp)))
    · exact (apart_tbl hc.n10 hi j) _ (by simp)
  · exact apart_append (apart_slW (fun h => hw (List.mem_cons_of_mem _ h))) (apart_wk hc.n10 hi)

/-- Materializing an exponent and running the field power. -/
theorem rootPower_ok {c : Cfg} (hc : CfgOk c) {e j : Nat}
    (hj : j < 3) (he : e < 2 ^ (64 * c.n))
    {base : Addr} {s : State} (hs : Scr s base size) (hf : Far s base 8192)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.Arm.rootPower c e j) s fun s' =>
      Rest powClob s s' ∧
      Unch base ([(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
        powWx (Impl.EcKey.Compressed.Arm.rootPow c j) c.wk) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ e := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have h0 := hc.n0
  have hE := sl_le c h7 (i := EXPP) (by decide)
  rw [Impl.EcKey.Compressed.Arm.rootPower]
  change WP isa (.seq (.block (setConst c.n (c.sl EXPP) e))
    (.seq (bits (c.sl EXPP) (bitsAt c.n j) (8 * c.n))
      (pow (Impl.EcKey.Compressed.Arm.rootPow c j) c.SP c.umaal))) s _
  refine WP.seq (WP.mono (setConst_ok hs hE he) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_rest k₁ (by decide)
  refine WP.seq (WP.mono (bits_ok hs₁ (hf.of_rest k₁) h0 hE (bitsAt_le c h7 hj)
    (bitsAt_lt hc hj) (by simp [bitsAt, Nat.add_mod, Nat.mul_mod])
    (Or.inl (sl_below_bits c h7 (i := EXPP) (by decide) j 0)) (enc8n h7))
    fun s₂ ⟨bits₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_rest k₂ (by decide)
  have keep₂ {i : Nat} (hi : i < 45) (hiE : i ≠ EXPP) (hiT : i ≠ TMP) :
      sv c base s₂ i = sv c base s i := by
    have hsl := sl_le c h7 hi
    rw [sv, O₂.wordsVal (Or.inl (sl_below_bits c h7 hi j 0)) (by omega_using [hn, hsl]),
      O₁.wordsVal (sl_apart c hiE) (by omega_using [hn, hsl])]
  have hM₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = c.C.p
    rw [keep₂ (by decide) (by decide) (by decide)]
    exact hM.val)
  have B₂ : wordsVal s₂.mem base (c.sl W2) c.n < c.C.p := by
    rw [show wordsVal s₂.mem base (c.sl W2) c.n = sv c base s₂ W2 from rfl,
      keep₂ (by decide) (by decide) (by decide)]
    exact hB
  have O₂' : wordsVal s₂.mem base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p := by
    rw [show wordsVal s₂.mem base (c.sl ONEP) c.n = sv c base s₂ ONEP from rfl,
      keep₂ (by decide) (by decide) (by decide)]
    exact hO
  have henc : encodable (BitVec.ofNat 32 (64 * c.n)) = true := by
    have h : ∀ n < 10, encodable (BitVec.ofNat 32 (64 * n)) = true := by decide
    exact h _ h7
  refine WP.mono (pow_ok (rootPow_lay hc hj) (rootPow_wk hc) hc.fp
    (unitMod_pow_two hc.p_odd (64 * c.n)) (bitsAt_lt hc hj) hs₂ ((hf.of_rest k₁).of_rest k₂) hM₂ B₂ O₂'
    (by simpa only [e₁, Impl.EcKey.Compressed.Arm.rootPow] using bits₂) he henc) fun s₃ ⟨k₃, U₃, lt₃, v₃⟩ => ?_
  refine ⟨?_, (O₁.unch.trans O₂.unch).trans U₃, lt₃, ?_⟩
  · exact ((k₁.mono (by simp [powClob, clob])).trans (k₂.mono (by simp [powClob, clob]))).trans k₃
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ ACC) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ W2) ^ e at v₃
    rw [keep₂ (by decide) (by decide) (by decide)] at v₃
    exact v₃

/-- The three-mod-four candidate uses an exponent derived from the prime. -/
theorem rootThree_ok {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 = 3)
    {base : Addr} {s : State} (hs : Scr s base size) (hf : Far s base 8192)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.Arm.rootCandidate c) s fun s' =>
      Rest powClob s s' ∧
      Unch base ([(c.sl EXPP, 8 * c.n), (bitsAt c.n 2, 64 * c.n)] ++
        powWx (Impl.EcKey.Compressed.Arm.rootPow c 2) c.wk) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((c.C.p + 1) / 4) := by
  simp only [Impl.EcKey.Compressed.Arm.rootCandidate, hp, ↓reduceIte]
  exact rootPower_ok hc (by decide)
    (by have := hc.p_lt; have := hc.p_ge; omega_arith) hs hf hM hB hO

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! # The machine root candidate's shared refinement interface -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG VG.Arm VG.Impl.Ecdsa.Arm
open VG.Impl.Ecdh.Arm (W0 W2)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm

/-- Writes shared by exponentiation and the P-224 descent. -/
def candidateSlots : List Nat := [ACC, PT, TMP, EXPP, EXPN, T0, T1, T2, T3, T4, T5, W0]
def candidateWrites (c : Cfg) : List (Nat × Nat) := slWk c candidateSlots ++
  [(bitsAt c.n 1, 64 * c.n), (bitsAt c.n 2, 64 * c.n)]

structure CandidatePost (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (base : Addr) (s s' : State) : Prop where
  keep : Rest powClob s s'
  unch : Unch base (candidateWrites c) s.mem s'.mem
  lt : sv c base s' ACC < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
    root (toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2))

/-- This is discharged by the assembly proofs for each root method. -/
def CandidateCorrect (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) : Prop :=
  ∀ (base : Addr) (s : State), Scr s base size → Far s base 8192 →
    ModOkW c.MP' size c.C.p s.mem base → sv c base s W2 < c.C.p →
    sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p →
    WP isa (Impl.EcKey.Compressed.Arm.rootCandidate c) s (CandidatePost c root base s)

theorem candidate_fixed {c : Cfg} (hc : CfgOk c) : FixedOk c (candidateWrites c) :=
  (fixedOk_slWk hc.n10 (l := candidateSlots) (by decide)).append (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact fixedOk_tbl hc.n10 1 _ (by simp)
    · exact fixedOk_tbl hc.n10 2 _ (by simp))

theorem candidate_apart {c : Cfg} (hc : CfgOk c) {i : Nat} (hi : i < 45) (hw : i ∉ candidateSlots) :
    ∀ w ∈ candidateWrites c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  apply apart_append (apart_slWk hc.n10 hi hw)
  intro w h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact (apart_tbl hc.n10 hi 1) _ (by simp)
  · exact (apart_tbl hc.n10 hi 2) _ (by simp)

theorem candidateThree_correct {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 = 3) :
    CandidateCorrect c Impl.EcKey.Compressed.rootThreeModFour := by
  intro base s hs hf hM hB hO
  refine WP.mono (rootThree_ok hc hp hs hf hM hB hO) fun s' ⟨k, U, lt, v⟩ => ?_
  refine ⟨k, U.mono ?_, lt, ?_⟩
  · intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, powWx, powW,
      Impl.EcKey.Compressed.Arm.rootPow] at hw
    rcases hw with (rfl | rfl) | (rfl | rfl | rfl) | rfl
    all_goals simp [candidateWrites, candidateSlots, slWk, slW, MP'_n, MP'_tmp]
  · simpa only [Impl.EcKey.Compressed.rootThreeModFour, pow_eq_npow] using v

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.DecompressFront`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.Arm.Frame`, which this module and modules that import it used -/

section

/-! # Frames for the converter's scratch slots -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Ecdsa.Arm
open VG.Impl.Ecdsa.Arm

theorem unch_same {base : Addr} {W : List (Nat × Nat)} {a b c : Mem}
    (h₁ : Unch base W a b) (h₂ : Unch base W b c) : Unch base W a c :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem slot_frame {c : Cfg} {base : Addr} {a b : Mem} {i len : Nat} {slots : List Nat}
    (hi : i ∈ slots) (hlen : len ≤ 8 * c.n) (h : Outside base (c.sl i) len a b) :
    Unch base (slW c slots) a b :=
  (h.mono (o' := c.sl i) (n' := 8 * c.n) (Nat.le_refl _) (by omega_using [hlen])).unch.mono fun w hw => by
    obtain rfl := List.mem_singleton.mp hw
    exact List.mem_map_of_mem hi

theorem slots_widen {c : Cfg} {base : Addr} {a b : Mem} {slots slots' : List Nat}
    (h : Unch base (slW c slots) a b) (hsub : ∀ i ∈ slots, i ∈ slots') :
    Unch base (slW c slots') a b := h.mono fun w hw => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact List.mem_map_of_mem (hsub i hi)

theorem slotsWk_widen {c : Cfg} {base : Addr} {a b : Mem} {slots slots' : List Nat}
    (h : Unch base (slWk c slots) a b) (hsub : ∀ i ∈ slots, i ∈ slots') :
    Unch base (slWk c slots') a b := h.mono fun w hw => by
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact List.mem_append_left _ (List.mem_map_of_mem (hsub i hi))
  · exact List.mem_append_right _ hw

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.DecompressContract`, which the modules that import this one used -/

section

/-! # Decompression's signature obligations on ARMv7 -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm

def decompressContract (C : Spec.Weierstrass.Curve)
    (root : Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C) : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 2 * C.len + 1⟩
    let pk : Region := ⟨State.addr (s.gpr .r1), C.len + 1⟩
    let ws : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧
      pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .r0).toNat + 2 * C.len + 1 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + C.len + 1 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s s' :=
    match Impl.EcKey.Compressed.decode C root (Spec.EcKey.bytesAt s.mem (State.addr (s.gpr .r1)) (C.len + 1)) with
    | some Q => (s'.gpr .r1 ++ s'.gpr .r0).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * C.len + 1) = Spec.EcKey.encodePoint Q
    | none => (s'.gpr .r1 ++ s'.gpr .r0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * C.len + 1) = List.replicate (2 * C.len + 1) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧
    s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

theorem decompress_implies (I : Spec.EcKey.Instance)
    (root : Spec.Weierstrass.Fe I.curve → Spec.Weierstrass.Fe I.curve)
    (hf : RootFacts root)
    (hsat : ∃ s, (I.decompressPublicKeyContract abi 0).pre s) :
    (decompressContract I.curve root).Implies (I.decompressPublicKeyContract abi 0) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, reduceClassify, Loc.val, State.addr, decompressContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, reduceClassify, Loc.val, State.addr, decompressContract]
    cases he : Impl.EcKey.Compressed.decode I.curve root
        (Spec.EcKey.bytesAt s.mem (State.addr (s.gpr .r1)) (I.curve.len + 1)) with
    | none =>
      simp only [decompressContract, he] at h
      exact Or.inr ⟨h.1, (decode_none_iff hf _).mp he, h.2⟩
    | some Q =>
      simp only [decompressContract, he] at h
      exact Or.inl ⟨h.1, Q, decode_sound he, h.2⟩
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, reduceClassify, Loc.val, State.addr, decompressContract]
  sat := hsat

def decompressSatState (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x8000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, len + 1⟩]
  wr := [⟨0x1000, 2 * len + 1⟩, ⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.Rhs`, which only this module used -/

section

/-! # The curve polynomial used by coordinate recovery -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdh.Arm (R2P BP QXM QYM QY W0 W1 W2 W3)
open VG.Impl.EcKey.Compressed.Arm (rhsOps)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont.Arm VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Ecdh.Arm

abbrev rhsSlots : List Nat := [QXM, AP, BP, W1, W2, W3]

def rhsTail : List FOp :=
  [.mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM,
    .add W3 W2 W1, .add W2 W3 BP]

theorem rhsTail_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps rhsTail e W2 = e QXM * e QXM * e QXM + e AP * e QXM + e BP := by
  simp only [rhsTail, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W1, W2, W3, QXM, AP, BP, TT, SM, RM, XM, EM, Nat.reduceEqDiff, ↓reduceIte]

theorem rhsTail_reads : readsOk rhsTail [QXM, AP, BP] = true := by decide
theorem rhsTail_slots : ∀ op ∈ rhsTail, ∀ x ∈ op.out :: op.ins, x ∈ rhsSlots := by decide
theorem rhsTail_out : ∀ op ∈ rhsTail, op.out ∈ [W1, W2, W3, TMP] := by decide

structure RhsPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkW c.MP' size c.C.p s'.mem base
  rest : Rest Mont.callClob s s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slWk c [QXM, W1, W2, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W2 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W2) =
    let x := Fin.ofNat c.C.p (sv c base s E)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

theorem rhs_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (Impl.Weierstrass.Arm.fprog c.SP (rhsOps c) c.umaal) s (RhsPost c base s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  change WP isa (.seq (VG.Impl.Weierstrass.Arm.Mont.mulCall c.SP
    (c.sl QXM) (c.sl E) (c.sl R2P) c.umaal)
    (VG.Impl.Weierstrass.Arm.fprog c.SP (rhsTail.map (FOp.rename c.sl)) c.umaal)) s _
  refine WP.seq (WP.mono (slMul_ok hc.fp (MP'_n c) h7 hs hf (o := QXM) (a := E) (b := R2P)
    (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain hM₁ := hM.keepArm (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ QXM) = Fin.ofNat c.C.p (sv c base s E) :=
    toM_r2 hpR (by simpa only [hr2, Cfg.R] using e₁)
  obtain a₁ : sv c base s₁ AP = c.mont c.C.a :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hap
  obtain b₁ : sv c base s₁ BP = c.mont c.C.b :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hbp
  obtain hL : Lay c.MP' size (· ∈ rhsSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hW : WkOk c.MP' size c.wk (· ∈ rhsSlots.map c.sl) := by
    refine ⟨wk_le c h7 rfl, ?_, sl_below_wk c h7 (by decide), sl_below_wk c h7 (by decide)⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain H : ∀ i ∈ rhsSlots, i < 45 := by decide
    exact sl_below_wk c h7 (H i hi)
  obtain I : Inv c.MP' base size c.C.p (· ∈ rhsSlots.map c.sl) ([QXM, AP, BP].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base o c.n)) s₁ := by
    refine ⟨hs₁, hM₁, ?_, ?_, fun _ _ => rfl, hf.of_rest k₁.rest⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain sub : ∀ i ∈ [QXM, AP, BP], i ∈ rhsSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt₁
      · show sv c base s₁ AP < _
        rw [a₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [lt₁])
      · show sv c base s₁ BP < _
        rw [b₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [lt₁])
  refine WP.mono (fprog_ok hL hW hc.fp hpR _ I (fun op hop x hx => ?_)
    (readsOk_rename c.sl rhsTail_reads)) fun s₂ ⟨PK, I₂⟩ => ?_
  · obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
    obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (rhsTail_slots _ hop₀ _ hi)
  obtain hw : c.sl W2 ∈ validAfter (rhsTail.map (FOp.rename c.sl)) ([QXM, AP, BP].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [rhsTail, FOp.rename, FOp.out]))
  obtain v₂ := I₂.val _ hw
  rw [congrFun (runOps_rename c.sl rhsTail _ fun _ _ _ h =>
    sl_inj c hc.n0 h) W2, rhsTail_run] at v₂
  obtain U₁ : Unch base (slWk c [QXM, W1, W2, W3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  obtain U₂ : Unch base (slWk c [QXM, W1, W2, W3, TMP]) s₁.mem s₂.mem := PK.unch.mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_append_left _ (List.mem_map.mpr ⟨op₀.out, List.mem_cons_of_mem _ (rhsTail_out op₀ h₀), by
        rw [FOp.out_rename]; rfl⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact List.mem_append_left _ (List.mem_map_of_mem (by decide))
      · exact List.mem_append_right _ (by simp [MP'_n])
  refine ⟨PK.scr hs₁, I₂.mod, k₁.rest.trans PK.rest,
    PK.rest.rd.trans k₁.rest.rd, PK.rest.wr.trans k₁.rest.wr,
    (U₁.trans U₂).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw), I₂.lt _ hw, ?_⟩
  simpa only [sv, MP'_n, a₁, b₁, toM_cmont hc, v₁] using v₂

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.Peer`, which only this module used -/

section

/-! ### `EcKey.Compressed.Arm.TagCheck`, which only this module used -/

section

/-! # Accept precisely the compressed SEC 1 tags and retain their parity -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest wp_ldrb wp_str wp_dp wp_mov op2_imm op2_reg op2_lsr dpVal)

private theorem tagMask : ∀ b : Byte,
    0 - (((((b.setWidth 32 ||| 1) ^^^ 3) - 1) >>> 31)) = mask32 (b = 2 ∨ b = 3) := by
  decide

theorem decompressTag_ok {c : Cfg} {s : State} {base : Addr} {q : BitVec 32}
    (hs : Scr s base size) (hq : s.gpr .r1 = q)
    (hin : InRegions (s.rd ++ s.wr) (State.addr q) 1) (hD : c.sl D + 4 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.decompressTag c)) s fun t =>
      t.gpr .r5 = mask32 (s.mem (State.addr q) = 2 ∨ s.mem (State.addr q) = 3) ∧
      t.mem.readW (off base (c.sl D)) 32 = (s.mem (State.addr q)).setWidth 32 ∧
      Rest [.r4, .r5] s t ∧ Outside base (c.sl D) 4 s.mem t.mem := by
  unfold Impl.EcKey.Compressed.Arm.decompressTag
  refine wp_ldrb (by decide) (a := State.addr q) (by rw [hq]; simp) hin fun s₁ u₁ => ?_
  obtain hs₁ := hs.of_rest (u₁.rest (ws := [.r4]) (by simp)) (by decide)
  refine wp_str (hs₁.off_lt (by omega_using [hD])) (hs₁.ea (by omega_using [hD])) (hs₁.write hD) fun s₂ m₂ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₇ u₇ => ?_
  refine wp_dp (op2_reg _ _) fun t u₈ => WP.block_nil ?_
  obtain hm : t.mem = s.mem.writeW (off base (c.sl D)) ((s.mem (State.addr q)).setWidth 32) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem, u₁.gpr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u₈.gpr, dpVal, u₇.gpr, u₇.other .r4 (by decide), u₆.gpr, u₅.gpr, dpVal,
      u₄.gpr, dpVal, u₃.gpr, dpVal, m₂.gpr, u₁.gpr]
    exact tagMask _
  · rw [hm, Mem.readW_writeW_self32]
  · exact (u₁.rest (by simp)).trans ((m₂.rest _).trans ((u₃.rest (by simp)).trans
      ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans ((u₆.rest (by simp)).trans
      ((u₇.rest (by simp)).trans (u₈.rest (by simp))))))))
  · rw [hm]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega_using [hD, this])

end VG.Proof.EcKey.Compressed.Arm

end

end


@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm
open Spec.Weierstrass
open VG.Impl.Mont.Arm
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdh.Arm (R2P BP)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest wp_dp op2_imm dpVal ea toNat_add_lt toNat_imm)

theorem decompressPeer_eq (c : Cfg) : Impl.EcKey.Compressed.Arm.decompressPeer c =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++
    (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (.dp .add .r6 .r1 (.imm 1) ::
    (loadBytes c.C.len c.n (c.sl E) .r6 ++
    (Impl.EcKey.Compressed.Arm.decompressTag c ++
    (c.andFlag ++ Impl.Ecdh.Arm.Cfg.checkLtP c (c.sl E)))))) := by
  simp only [Impl.EcKey.Compressed.Arm.decompressPeer, Impl.Ecdh.Arm.Cfg.consts,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
    List.cons_append, List.nil_append]

theorem decompressPeer_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hqfit : (s.gpr .r1).toNat + (1 + c.C.len) ≤ 2 ^ 32)
    (hin : (⟨State.addr (s.gpr .r1), 1 + c.C.len⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨State.addr (s.gpr .r1), 1 + c.C.len⟩ ⟨base, size⟩)
    (hmp : sv c base s MP = c.C.p) (hf : flagW c base s = BitVec.allOnes 32) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.decompressPeer c)) s fun t =>
      Scr t base size ∧ Rest [.r3, .r4, .r5, .r6, .r7, .r8] s t ∧
      Unch base (slW c [R2P, BP, E, D, FLAG]) s.mem t.mem ∧
      sv c base t R2P = c.R * c.R % c.C.p ∧ sv c base t BP = c.mont c.C.b ∧
      sv c base t E = ofBytes (Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr .r1) + 1) c.C.len) ∧
      t.mem.readW (off base (c.sl D)) 32 = (s.mem (State.addr (s.gpr .r1))).setWidth 32 ∧
      flagW c base t = mask32 ((s.mem (State.addr (s.gpr .r1)) = 2 ∨
        s.mem (State.addr (s.gpr .r1)) = 3) ∧ sv c base t E < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  obtain hF : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  obtain hR2 := sl_le c h7 (i := R2P) (by decide)
  obtain hB := sl_le c h7 (i := BP) (by decide)
  obtain hE := sl_le c h7 (i := E) (by decide)
  obtain hM := sl_le c h7 (i := MP) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  obtain hq : Reg.r1 ∉ [Reg.r4, .r6] := by decide
  generalize hq32 : s.gpr .r1 = q32 at hqfit hin hd ⊢
  generalize hq64 : State.addr q32 = qa at hin hd ⊢
  rw [decompressPeer_eq]
  -- The constants.
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs hR2 (show c.R * c.R % c.C.p < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_rest k₁ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs₁ hB (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_rest k₂ (by decide)
  obtain W₂ : Outside base 0 size s.mem s₂.mem :=
    (O₁.mono (Nat.zero_le _) (by omega_arith)).trans (O₂.mono (Nat.zero_le _) (by omega_arith))
  obtain K₂ : Rest [.r4] s s₂ := k₁.trans k₂
  -- `peer + 1`
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  obtain K₃ : Rest [.r4, .r6] s s₃ := (K₂.mono (by simp)).trans (u₃.rest (by simp))
  obtain hs₃ := hs.of_rest K₃ (by decide)
  have hm₃ : s₃.mem = s₂.mem := u₃.mem
  obtain hrw₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [K₃.rd, K₃.wr]
  obtain hb₃ : s₃.gpr .r6 = q32 + BitVec.ofNat 32 1 := by
    rw [u₃.gpr, K₂.gpr _ (by decide), hq32]; rfl
  obtain ha₃ : State.addr (s₃.gpr .r6) = qa + BitVec.ofNat 64 1 := by
    rw [hb₃, ← hq64]; exact ea (by omega_arith)
  obtain ht₃ : (s₃.gpr .r6).toNat = q32.toNat + 1 := by
    rw [hb₃, toNat_add_lt (by rw [toNat_imm (by decide)]; omega_arith), toNat_imm (by decide)]
  -- `x`
  refine VG.Proof.X25519.Arm.WP.append (loadBytes_ok hs₃ (src := .r6) (by decide) hE (by omega_arith) (by omega_arith) hlhi
    (fun e he => ⟨_, by rw [hrw₃]; exact hin, by
      rw [ha₃, Offset.add_add]; exact Offset.contains_base qa (by omega_arith) (by omega_arith)⟩)
    (by rw [ha₃]; exact (hd.sub_left (Offset.sub_base qa (by omega_arith))).sub_right (Offset.sub_base base hE)))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [ha₃, hm₃] at e₄
  rw [hm₃] at O₄
  obtain hs₄ := hs₃.of_rest k₄ (by decide)
  obtain K₄ : Rest [.r4, .r6] s s₄ := K₃.trans (k₄.mono (by simp))
  obtain W₄ : Outside base 0 size s.mem s₄.mem := W₂.trans (O₄.mono (Nat.zero_le _) hE)
  obtain lead₄ : s₄.mem qa = s.mem qa := by
    obtain e := keep_of_disjoint' W₄ hd (by decide) (i := 0) (by omega_using []) (by omega_using [hqfit])
    simpa only [BitVec.add_zero] using e
  refine VG.Proof.X25519.Arm.WP.append (decompressTag_ok (q := q32) hs₄
    (by rw [K₄.gpr _ (by decide), hq32])
    (by rw [K₄.rd, K₄.wr, hq64]; exact ⟨_, hin, by simpa using Offset.contains_base qa (d := 0) (n := 1) (by omega_using []) (by decide)⟩)
    (by have := sl_le c h7 (i := D) (by decide); omega_using [h0, hD])) fun s₅ ⟨mask₅, tag₅, k₅, O₅⟩ => ?_
  rw [hq64, lead₄] at mask₅ tag₅
  obtain hs₅ := hs₄.of_rest k₅ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (andFlag_ok c hs₅ hF) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  obtain hs₆ := hs₅.of_rest k₆ (by decide)
  refine WP.mono (checkLtP_ok c hs₆ hE hM hF) fun t ⟨f₇, k₇, O₇⟩ => ?_
  obtain U₄ : Unch base (slW c [R2P, BP, E, D]) s.mem s₄.mem :=
    unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (Nat.le_refl _) O₄)
  obtain U₅ := unch_same U₄ (slot_frame (by simp) (by omega_using [h0]) O₅)
  have v₅ {i : Nat} (hi : i < 45) (hw : i ∉ [R2P, BP, E, D]) :
      sv c base s₅ i = sv c base s i := sv_unch U₅ h7 hn hi (apart_slW hw)
  obtain x₅ : sv c base s₅ E = ofBytes (Spec.Ecdsa.bytesAt s.mem (qa + 1) c.C.len) := by
    change wordsVal s₅.mem base (c.sl E) c.n = _
    rw [sv_out (O₅.mono (Nat.le_refl _) (by omega_using [h0] : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide), e₄]
    congr 1
    exact bytesAt_keep W₂ (hd.sub_left (Offset.sub_base qa (d := 1) (by omega_using []))) (by decide) (by omega_using [hqfit])
  obtain flag₅ : flagW c base s₅ = BitVec.allOnes 32 := by
    rw [flagW, ← hf]
    exact Unch.readW32 U₅ (fun w hw => by have := (apart_slW (c := c) (by decide : FLAG ∉ [R2P, BP, E, D])) w hw; omega_using [h0, this]) (by omega_using [hn, hF])
  refine ⟨hs₆.of_rest k₇ (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (K₄.mono (by simp)).trans ((k₅.mono (by simp)).trans ((k₆.mono (by simp)).trans (k₇.mono (by simp))))
  · exact unch_same (unch_same (slots_widen U₅ (slots' := [R2P, BP, E, D, FLAG]) (by decide)) (slot_frame (by simp) (by omega_using [h0]) O₆)) (slot_frame (by simp) (by omega_using [h0]) O₇)
  · simp only [sv] at *
    rw [sv_flag O₇ h0 h7 hn (by decide) (by decide), sv_flag O₆ h0 h7 hn (by decide) (by decide),
      sv_out (O₅.mono (Nat.le_refl _) (by omega_using [h0] : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₄ h7 hn (by decide) (by decide), sv_out O₂ h7 hn (by decide) (by decide)]
    exact e₁
  · simp only [sv] at *
    rw [sv_flag O₇ h0 h7 hn (by decide) (by decide), sv_flag O₆ h0 h7 hn (by decide) (by decide),
      sv_out (O₅.mono (Nat.le_refl _) (by omega_using [h0] : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₄ h7 hn (by decide) (by decide)]
    exact e₂
  · simp only [sv] at *
    rw [sv_flag O₇ h0 h7 hn (by decide) (by decide), sv_flag O₆ h0 h7 hn (by decide) (by decide), x₅]
  · rw [BitVec.eq_of_toNat_eq (O₇.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [hn, hD])),
      BitVec.eq_of_toNat_eq (O₆.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [hn, hD]))]
    exact tag₅
  · simp only [sv] at *
    rw [f₇, f₆, flag₅, mask₅, BitVec.allOnes_and,
      show wordsVal s₆.mem base (c.sl E) c.n = sv c base s₆ E from rfl,
      show wordsVal s₆.mem base (c.sl MP) c.n = sv c base s₆ MP from rfl]
    simp only [sv]
    simp only [mask32, sv_flag O₆ h0 h7 hn (i := E) (by decide) (by decide),
      sv_flag O₆ h0 h7 hn (i := MP) (by decide) (by decide),
      v₅ (i := MP) (by decide) (by decide), hmp,
      sv_flag O₇ h0 h7 hn (i := E) (by decide) (by decide)]
    exact mask32_and _ _

end VG.Proof.EcKey.Compressed.Arm

end

end


/-! # Prepare the curve polynomial and retain the input checks on ARMv7 -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Impl.Ecdh.Arm (R2P BP W2)
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm

abbrev CompressedPrefix (c : Cfg) (s : State) : Prop :=
  (s.mem (ptr s .r1) = 2 ∨ s.mem (ptr s .r1) = 3) ∧ keyX c s < c.C.p

structure DecompressFront (c : Cfg) (s₀ s : State) : Prop where
  scr : Scr s (ptr s₀ .r2) size
  far : Far s (ptr s₀ .r2) 8192
  fixed : Fixed c (ptr s₀ .r2) s₀.gpr s.mem
  out : s.gpr .lr = s₀.gpr .r0
  x : sv c (ptr s₀ .r2) s E = keyX c s₀
  tag : s.mem.readW (off (ptr s₀ .r2) (c.sl D)) 32 = (s₀.mem (ptr s₀ .r1)).setWidth 32
  r2 : sv c (ptr s₀ .r2) s R2P = c.R * c.R % c.C.p
  rhs_lt : sv c (ptr s₀ .r2) s W2 < c.C.p
  rhs : toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ .r2) s W2) =
    let x := Fin.ofNat c.C.p (keyX c s₀)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b
  flag : flagW c (ptr s₀ .r2) s = mask32 (CompressedPrefix c s₀)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem DecompressFront.frame {c : Cfg} (hc : CfgOk c) {s₀ s t : State}
    (F : DecompressFront c s₀ s) (K : VG.Proof.X25519.Arm.Rest powClob s t)
    {W : List (Nat × Nat)} (U : Unch (ptr s₀ .r2) W s.mem t.mem) (hW : FixedOk c W)
    (ha : ∀ i ∈ [E, D, R2P, W2, FLAG], ∀ w ∈ W,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) : DecompressFront c s₀ t := by
  have hn := F.scr.nowrap
  have h0 := hc.n0
  have h7 := hc.n10
  have e {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      sv c (ptr s₀ .r2) t i = sv c (ptr s₀ .r2) s i := sv_unch U h7 hn hi (ha i hm)
  have ew {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      t.mem.readW (off (ptr s₀ .r2) (c.sl i)) 32 = s.mem.readW (off (ptr s₀ .r2) (c.sl i)) 32 :=
    Unch.readW32 U (fun w hw => by have := ha i hm w hw; omega_using [h0, this])
      (by have := sl_le c h7 hi; omega_using [hn, this])
  refine ⟨F.scr.of_rest K (by decide), F.far.of_rest K, F.fixed.unch h7 hn hW U,
    (K.gpr _ (by decide)).trans F.out, (e (by decide) (by simp)).trans F.x,
    (ew (by decide) (by simp)).trans F.tag, (e (by decide) (by simp)).trans F.r2,
    ?_, ?_, ?_, K.sp.trans F.sp, K.rd.trans F.rd, K.wr.trans F.wr⟩
  · rw [e (by decide) (by simp)]; exact F.rhs_lt
  · rw [e (by decide) (by simp)]; exact F.rhs
  · rw [flagW, ew (by decide) (by simp), ← flagW]; exact F.flag

theorem decompressFront_ok {c : Cfg} (hc : CfgOk c) {s₀ : State}
    (hp : InputPre c (1 + c.C.len) s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, DecompressFront c s₀ s → WP isa rest s Q) :
    WP isa (.seq (.block (c.setupWith Impl.EcKey.Compressed.Arm.args))
      (.seq (.block (Impl.EcKey.Compressed.Arm.decompressPeer c))
      (.seq (Impl.Weierstrass.Arm.fprog c.SP (Impl.EcKey.Compressed.Arm.rhsOps c) c.umaal) rest))) s₀ Q := by
  have h7 := hc.n10
  have h0 := hc.n0
  obtain hd : Region.Disjoint ⟨ptr s₀ .r1, 1 + c.C.len⟩ ⟨ptr s₀ .r2, size⟩ :=
    hp.disjoint.sub_right (by simpa using Region.sub_prefix (by decide : size ≤ 8192))
  refine WP.seq (WP.mono (setup_ok hc (input_setup hp (by omega_using []))) fun s₁ S => ?_)
  change SetupPost c Impl.EcKey.Compressed.Arm.args s₀ (ptr s₀ .r2) s₁ at S
  obtain F₁ := setup_fixed S
  have hn := S.scr.nowrap
  obtain hr1 : s₁.gpr .r1 = s₀.gpr .r1 := S.keep.gpr _ (by decide)
  obtain W₁ : Outside (ptr s₀ .r2) 0 size s₀.mem s₁.mem := S.unch.outside (by simp)
  refine WP.seq (WP.mono (decompressPeer_ok hc S.scr
    (by rw [hr1]; exact hp.pk_fit)
    (by rw [hr1, S.keep.rd, S.keep.wr]; exact hp.pk)
    (by rw [hr1]; exact hd) F₁.mp S.flag) fun s₂ ⟨hs₂, K₂, U₂, r2₂, bp₂, x₂, tag₂, flag₂⟩ => ?_)
  obtain F₂ := F₁.unch h7 hn (fixedOk_slW (l := [R2P, BP, E, D, FLAG]) (by decide)) U₂
  obtain lead : s₁.mem (ptr s₀ .r1) = s₀.mem (ptr s₀ .r1) := by
    obtain e := keep_of_disjoint' W₁ hd (by decide) (i := 0) (by omega_using []) (by have := hc.len_hi; omega_using [h7, this])
    simpa only [BitVec.add_zero] using e
  obtain x₂' : sv c (ptr s₀ .r2) s₂ E = keyX c s₀ := by
    rw [x₂, hr1]
    congr 1
    exact bytesAt_keep W₁ (hd.sub_left (Offset.sub_base _ (d := 1) (by omega_using []))) (by decide)
      (by have := hc.len_hi; omega_using [h7, this])
  rw [hr1, lead] at tag₂ flag₂
  refine WP.seq (WP.mono (rhs_ok hc hs₂ (S.far.of_rest K₂) (modP_of hc F₂.mp) r2₂ F₂.ap bp₂)
    fun s₃ R => ?_)
  obtain F₃ := F₂.unch h7 hn (fixedOk_slWk h7 (l := [Impl.Ecdh.Arm.QXM, Impl.Ecdh.Arm.W1,
    W2, Impl.Ecdh.Arm.W3, TMP]) (by decide)) R.unch
  have e {i : Nat} (hi : i < 45) (hw : i ∉ [Impl.Ecdh.Arm.QXM, Impl.Ecdh.Arm.W1, W2, Impl.Ecdh.Arm.W3, TMP]) :
      sv c (ptr s₀ .r2) s₃ i = sv c (ptr s₀ .r2) s₂ i :=
    sv_unch R.unch h7 hn hi (apart_slWk h7 hi hw)
  have ew {i : Nat} (hi : i < 45) (hw : i ∉ [Impl.Ecdh.Arm.QXM, Impl.Ecdh.Arm.W1, W2, Impl.Ecdh.Arm.W3, TMP]) :
      s₃.mem.readW (off (ptr s₀ .r2) (c.sl i)) 32 = s₂.mem.readW (off (ptr s₀ .r2) (c.sl i)) 32 :=
    Unch.readW32 R.unch (fun w hw' => by have := apart_slWk h7 hi hw w hw'; omega_using [h0, this])
      (by have := sl_le c h7 hi; omega_using [hn, this])
  apply h s₃
  refine ⟨R.scr, (S.far.of_rest K₂).of_rest R.rest, F₃,
    (R.rest.gpr _ (by decide)).trans ((K₂.gpr _ (by decide)).trans S.lr),
    (e (by decide) (by decide)).trans x₂', (ew (by decide) (by decide)).trans tag₂,
    (e (by decide) (by decide)).trans r2₂, R.lt, ?_, ?_,
    R.rest.sp.trans (K₂.sp.trans S.keep.sp), R.rd.trans (K₂.rd.trans S.keep.rd),
    R.wr.trans (K₂.wr.trans S.keep.wr)⟩
  · simpa only [x₂'] using R.val
  · rw [flagW, ew (by decide) (by decide), ← flagW, flag₂, x₂']

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.DecompressMiddle`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.Arm.Parity`, which only this module used -/

section

/-! # Choose the canonical root matching the SEC 1 parity bit -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov op2_imm op2_reg dpVal)

theorem xor_low_mask32 (x y : BitVec 32) :
    0 - ((x ^^^ y) &&& 1) = mask32 (x.toNat % 2 ≠ y.toNat % 2) := by
  have hlow : (x ^^^ y) &&& 1 = if x.toNat % 2 = y.toNat % 2 then 0 else 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_xor, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, show 2 = 2 ^ 1 from rfl, Nat.xor_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> simp [hx, hy]
  rw [hlow]
  by_cases h : x.toNat % 2 = y.toNat % 2 <;> simp [h, mask32]

theorem parityMask_ok {c : Cfg} {s : State} {base : Addr}
    (hs : Scr s base size) (hn : 0 < c.n)
    (hy : c.sl Impl.Ecdh.Arm.QY + 4 ≤ size) (ht : c.sl D + 4 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.parityMask c)) s fun t =>
      t.gpr .r10 = mask32 (sv c base s Impl.Ecdh.Arm.QY % 2 ≠
        (s.mem.readW (off base (c.sl D)) 32).toNat % 2) ∧
      Rest [.r4, .r5, .r10] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.Arm.parityMask
  refine wp_ldr (hs.off_lt (by omega_using [hy])) (hs.ea (by omega_using [hy])) (hs.read hy) fun s₁ u₁ => ?_
  have hs₁ := hs.of_rest (u₁.rest (ws := [.r4]) (by simp)) (by decide)
  refine wp_ldr (hs₁.off_lt (by omega_using [ht])) (hs₁.ea (by omega_using [ht])) (hs₁.read ht) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun t u₆ => WP.block_nil ?_
  refine ⟨?_, (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans
      ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))))), ?_⟩
  · rw [u₆.gpr, dpVal, u₅.gpr, u₅.other .r5 (by decide), u₄.gpr, dpVal, u₃.gpr, dpVal,
      u₂.gpr, u₂.other .r4 (by decide), u₁.gpr, u₁.mem, BitVec.xor_comm, xor_low_mask32]
    rw [slot32_parity _ _ _ _ hn]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem invertMask_ok (s : State) (P : Prop) [Decidable P] (h : s.gpr .r10 = mask32 P) :
    WP isa (.block Impl.EcKey.Compressed.Arm.invertMask) s fun t =>
      t.gpr .r5 = mask32 (¬ P) ∧ Rest [.r4, .r5] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.Arm.invertMask
  refine wp_dp (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun t u₃ => WP.block_nil ?_
  refine ⟨?_, (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans (u₃.rest (by simp))), ?_⟩
  · rw [u₃.gpr, dpVal, u₂.gpr, u₂.other .r5 (by decide), u₁.gpr, dpVal, h]
    by_cases hp : P <;> simp [mask32, hp]
  · rw [u₃.mem, u₂.mem, u₁.mem]

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.Select`, which only this module used -/

section

/-! # Leave Montgomery form and choose between the two canonical roots -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdh.Arm (QY W0)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm

structure SelectPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkW c.MP' size c.C.p s'.mem base
  keep : Rest Mont.callClob s s'
  unch : Unch base (slWk c [QY, W0, TMP]) s.mem s'.mem
  lt : sv c base s' QY < c.C.p
  val : Fin.ofNat c.C.p (sv c base s' QY) =
    let y := toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
    if y.val % 2 = (s.mem.readW (off base (c.sl D)) 32).toNat % 2 then y else -y

theorem selectRoot_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONE = 1) (hZero : sv c base s ZERO = 0) :
    WP isa (Impl.EcKey.Compressed.Arm.selectRoot c) s (SelectPost c base s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  obtain hY := sl_le c h7 (i := QY) (by decide)
  obtain hZ := sl_le c h7 (i := ZERO) (by decide)
  obtain hW := sl_le c h7 (i := W0) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  obtain hMP := sl_le c h7 (i := MP) (by decide)
  change WP isa (.seq (Mont.mulCall c.SP (c.sl QY) (c.sl ACC) (c.sl ONE) c.umaal)
    (.seq (Mont.subCall c.SP (c.sl W0) (c.sl ZERO) (c.sl QY) c.umaal)
      (.block (Impl.EcKey.Compressed.Arm.parityMask c ++ sel (2 * c.n) (c.sl QY) (c.sl QY) (c.sl W0))))) s _
  refine WP.seq (WP.mono (slMul_ok hc.fp (MP'_n c) h7 hs hf (o := QY) (a := ACC) (b := ONE)
    (by decide) (by decide) (by decide) (by rw [hOne]; omega_using [hp3]))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain hM₁ := hM.keepArm (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain normal : Fin.ofNat c.C.p (sv c base s₁ QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) :=
    toM_one_mul (unitMod_pow_two hc.p_odd (64 * c.n)) (by simpa only [hOne] using e₁)
  obtain normalVal : sv c base s₁ QY =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₁] using congrArg Fin.val normal
  obtain zero₁ : sv c base s₁ ZERO = 0 :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hZero
  refine WP.seq (WP.mono (slSub_ok hc.fp (MP'_n c) h7 hs₁ (hf.of_rest k₁.rest)
    (o := W0) (a := ZERO) (b := QY) (by decide) (by decide) (by decide)
    (by rw [zero₁]; omega_using [hp3]) lt₁) fun s₂ ⟨k₂, e₂⟩ => ?_)
  change sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p at e₂
  obtain hs₂ := k₂.scr hs₁
  obtain hM₂ := hM₁.keepArm (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain y₂ : sv c base s₂ QY = sv c base s₁ QY :=
    sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  obtain negLt : sv c base s₂ W0 < c.C.p := by
    rw [e₂]
    exact Nat.mod_lt _ (by omega_using [hp3])
  obtain negVal : Fin.ofNat c.C.p (sv c base s₂ W0) = -(Fin.ofNat c.C.p (sv c base s₁ QY)) := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.neg_def]
    rw [show sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p from e₂,
      zero₁, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt lt₁]
  obtain U₁₂ : Unch base (slWk c [QY, W0, TMP]) s.mem s₂.mem :=
    unch_same (unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp))
      (unch_slots (MP'_n c) rfl k₂.unch (by simp) (by simp))
  obtain tag₂ : s₂.mem.readW (off base (c.sl D)) 32 = s.mem.readW (off base (c.sl D)) 32 :=
    Unch.readW32 U₁₂ (fun w hw => by
      have := apart_slWk h7 (i := D) (by decide) (by decide) w hw
      omega_using [h0, this]) (by omega_using [hn, hD])
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega_using [h0, hY]) (by omega_using [h0, hD])) fun s₃ ⟨mask₃, k₃, m₃⟩ => ?_
  obtain hs₃ := hs₂.of_rest k₃ (by decide)
  refine WP.mono (sel_ok (decide (sv c base s₂ QY % 2 ≠ (s₂.mem.readW (off base (c.sl D)) 32).toNat % 2)) (2 * c.n) hs₃
    (by simpa only [mask32, decide_eq_true_eq] using mask₃)
    (by omega_using [hY]) (by omega_using [hY]) (by omega_using [hW]) (Or.inl (Nat.le_refl _))
    (by have := sl_apart c (i := QY) (j := W0) (by decide); omega_using [this])) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₄
  obtain hs₄ := hs₃.of_rest k₄ (by decide)
  obtain hM₄ : ModOkW c.MP' size c.C.p s₄.mem base := modP_of hc (by
    rw [O₄.wordsVal (d := c.sl MP) (k := c.n)
      (sl_apart c (i := MP) (j := QY) (by decide)) (by omega_using [hn, hMP]), m₃]
    exact hM₂.val)
  obtain e₄' : sv c base s₄ QY =
      if sv c base s₂ QY % 2 ≠ (s₂.mem.readW (off base (c.sl D)) 32).toNat % 2 then
        sv c base s₂ W0 else sv c base s₂ QY := by
    simpa only [sv, wordsVal_eq_val32, m₃, decide_eq_true_eq] using e₄
  refine ⟨hs₄, hM₄, ?_, ?_, ?_, ?_⟩
  · exact (k₁.rest.trans k₂.rest).trans ((k₃.mono (by decide)).trans (k₄.mono (by decide)))
  · apply unch_same U₁₂
    rw [← m₃]
    exact (slot_frame (slots := [QY, W0, TMP]) (by simp) (by omega_using []) O₄).mono
      (fun w hw => List.mem_append_left _ hw)
  · rw [e₄']
    split
    · exact negLt
    · rw [y₂]
      exact lt₁
  · change Fin.ofNat c.C.p (sv c base s₄ QY) =
      if (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (s.mem.readW (off base (c.sl D)) 32).toNat % 2 then _ else _
    rw [y₂, tag₂, normalVal] at e₄'
    by_cases hm : (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (s.mem.readW (off base (c.sl D)) 32).toNat % 2
    · rw [ite_eq_left hm]
      rw [ite_eq_right (not_not_intro hm)] at e₄'
      rw [e₄']
      exact Fin.ext (Nat.mod_eq_of_lt (toM _ _ _).isLt)
    · rw [ite_eq_right hm]
      rw [ite_eq_left hm] at e₄'
      rw [e₄', negVal, normal]

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.Check`, which only this module used -/

section

/-! # Check the recovered root's square and parity -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdh.Arm (QY QYM R2P W1 W2 W3)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest)

def checkN : List FOp := [.mul QYM QY R2P, .mul W1 QYM QYM, .sub W3 W1 W2]
abbrev checkSlots : List Nat := [QY, R2P, W2, QYM, W1, W3]

theorem checkOps_eq (c : Cfg) : Impl.EcKey.Compressed.Arm.checkRootOps c =
    checkN.map (FOp.rename c.sl) := rfl

theorem checkN_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps checkN e W3 = (e QY * e R2P) * (e QY * e R2P) - e W2 := by
  simp only [checkN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [QYM, QY, R2P, W1, W2, X, RR, DM, TT, SM, Nat.reduceEqDiff, ↓reduceIte]

theorem checkN_reads : readsOk checkN [QY, R2P, W2] = true := by decide
theorem checkN_slots : ∀ op ∈ checkN, ∀ x ∈ op.out :: op.ins, x ∈ checkSlots := by decide
theorem checkN_out : ∀ op ∈ checkN, op.out ∈ [QYM, W1, W3, TMP] := by decide

theorem raw_r2_mul {c : Cfg} (hc : CfgOk c) (a : Nat) :
    toM c.C.p (2 ^ (64 * c.n)) a *
      toM c.C.p (2 ^ (64 * c.n)) (c.R * c.R % c.C.p) = Fin.ofNat c.C.p a := by
  change toM c.C.p (2 ^ (64 * c.n)) a * toM c.C.p (2 ^ (64 * c.n)) (c.mont c.R) = _
  rw [toM_cmont hc]
  unfold toM
  obtain hu := mul_rinv (unitMod_pow_two hc.p_odd (64 * c.n))
  change Fin.ofNat c.C.p c.R * rinv c.C.p (2 ^ (64 * c.n)) = 1 at hu
  grind

structure CheckPolyPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : Rest Mont.callClob s s'
  unch : Unch base (slWk c [QYM, W1, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W3) =
    Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)

theorem checkPoly_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hfar : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) :
    WP isa (Impl.Weierstrass.Arm.fprog c.SP
      (Impl.EcKey.Compressed.Arm.checkRootOps c) c.umaal) s (CheckPolyPost c base s) := by
  have h7 := hc.n10
  obtain hL : Lay c.MP' size (· ∈ checkSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hW : WkOk c.MP' size c.wk (· ∈ checkSlots.map c.sl) := by
    refine ⟨wk_le c h7 rfl, ?_, sl_below_wk c h7 (by decide), sl_below_wk c h7 (by decide)⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain H : ∀ i ∈ checkSlots, i < 45 := by decide
    exact sl_below_wk c h7 (H i hi)
  obtain I : Inv c.MP' base size c.C.p (· ∈ checkSlots.map c.sl) ([QY, R2P, W2].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, ?_, ?_, fun _ _ => rfl, hfar⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain sub : ∀ i ∈ [QY, R2P, W2], i ∈ checkSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hy
      · show sv c base s R2P < _
        rw [hr2]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [hy])
      · exact hr
  rw [checkOps_eq]
  refine WP.mono (fprog_ok hL hW hc.fp (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => ?_)
    (readsOk_rename c.sl checkN_reads)) fun t ⟨PK, IT⟩ => ?_
  · obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (checkN_slots _ h₀ _ hi)
  obtain hw : c.sl W3 ∈ validAfter (checkN.map (FOp.rename c.sl)) ([QY, R2P, W2].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [checkN, FOp.rename, FOp.out]))
  obtain vt := IT.val _ hw
  rw [congrFun (runOps_rename c.sl checkN _ fun _ _ _ h => sl_inj c hc.n0 h) W3, checkN_run] at vt
  refine ⟨PK.scr hs, PK.rest, ?_, IT.lt _ hw, ?_⟩
  · apply PK.unch.mono
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_append_left _ (List.mem_map.mpr ⟨op₀.out, checkN_out _ h₀, by rw [FOp.out_rename]; rfl⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact List.mem_append_left _ (List.mem_map_of_mem (by decide))
      · exact List.mem_append_right _ (by simp [MP'_n])
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base t W3) =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) *
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) at vt
    simpa only [hr2, raw_r2_mul hc] using vt

structure CheckRootPost (c : Cfg) (base : Addr) (P : Prop) [Decidable P] (s s' : State) : Prop where
  scr : Scr s' base size
  keep : Rest Mont.callClob s s'
  unch : Unch base (slWk c [QYM, W1, W3, TMP, FLAG]) s.mem s'.mem
  flag : flagW c base s' = mask32
    ((P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) ∧
      sv c base s QY % 2 = (s.mem.readW (off base (c.sl D)) 32).toNat % 2)

theorem checkRoot_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hfar : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) {P : Prop} [Decidable P]
    (hf : flagW c base s = mask32 P) :
    WP isa (Impl.EcKey.Compressed.Arm.checkRoot c) s (CheckRootPost c base P s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 4096 := rfl
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  obtain hW := sl_le c h7 (i := W3) (by decide)
  obtain hY := sl_le c h7 (i := QY) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  change WP isa (.seq
    (Impl.Weierstrass.Arm.fprog c.SP (Impl.EcKey.Compressed.Arm.checkRootOps c) c.umaal)
    (.block (Impl.EcKey.Compressed.Arm.checkRootChecks c))) s _
  refine WP.seq (WP.mono (checkPoly_ok hc hs hfar hM hy hr hr2) fun s₁ I => ?_)
  obtain flag₁ : flagW c base s₁ = mask32 P := by
    rw [flagW, Unch.readW32 I.unch (fun w hw => by have := apart_slWk h7 (i := FLAG) (by decide) (by decide) w hw; omega_using [h0, this]) (by omega_using [hn, hF]), ← flagW, hf]
  obtain hz : sv c base s₁ W3 = 0 ↔
      Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) := by
    rw [← toM_eq_zero_iff (unitMod_pow_two hc.p_odd (64 * c.n)) I.lt, I.val]
    constructor <;> intro h <;> grind
  rw [Impl.EcKey.Compressed.Arm.checkRootChecks, WP.block_append_iff]
  refine WP.mono (checkZero_ok c I.scr h0 hW (by omega_using [h0, hF])) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  obtain hs₂ := I.scr.of_rest k₂ (by decide)
  obtain flag₂ : flagW c base s₂ = mask32
      (P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) := by
    rw [f₂, flag₁, show wordsVal s₁.mem base (c.sl W3) c.n = sv c base s₁ W3 from rfl, mask32_and]
    simp only [mask32, hz]
  obtain y₂ : sv c base s₂ QY = sv c base s QY := by
    rw [sv, sv_flag O₂ h0 h7 hn (by decide) (by decide)]
    exact sv_unch I.unch h7 hn (by decide) (apart_slWk h7 (by decide) (by decide))
  obtain tag₂ : s₂.mem.readW (off base (c.sl D)) 32 = s.mem.readW (off base (c.sl D)) 32 := by
    rw [BitVec.eq_of_toNat_eq (O₂.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [hn, hD]))]
    exact Unch.readW32 I.unch (fun w hw => by
      have := apart_slWk h7 (i := D) (by decide) (by decide) w hw
      omega_using [h0, this]) (by omega_using [hn, hD])
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega_using [h0, hY]) (by omega_using [h0, hD])) fun s₃ ⟨mask₃, k₃, m₃⟩ => ?_
  rw [y₂, tag₂] at mask₃
  rw [WP.block_append_iff]
  refine WP.mono (invertMask_ok s₃ _ mask₃) fun s₄ ⟨mask₄, k₄, m₄⟩ => ?_
  obtain hs₄ := (hs₂.of_rest k₃ (by decide)).of_rest k₄ (by decide)
  refine WP.mono (andFlag_ok c hs₄ (by omega_using [h0, hF])) fun s₅ ⟨flag₅, k₅, O₅⟩ => ?_
  refine ⟨hs₄.of_rest k₅ (by decide), ?_, ?_, ?_⟩
  · exact (((I.keep.trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (k₅.mono (by decide))
  · have U₁ : Unch base (slWk c [QYM, W1, W3, TMP, FLAG]) s.mem s₁.mem := I.unch.mono (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_append_left [FLAG] hi))
      · exact List.mem_append_right _ hw)
    obtain U₂ : Unch base (slWk c [QYM, W1, W3, TMP, FLAG]) s₁.mem s₄.mem := by
      rw [m₄, m₃]
      exact (slot_frame (slots := [QYM, W1, W3, TMP, FLAG]) (by simp) (by omega_using [h0]) O₂).mono
        (fun w hw => List.mem_append_left _ hw)
    exact unch_same (unch_same U₁ U₂) ((slot_frame (slots := [QYM, W1, W3, TMP, FLAG])
      (by simp) (by omega_using [h0]) O₅).mono (fun w hw => List.mem_append_left _ hw))
  · rw [flag₅, mask₄]
    change s₄.mem.readW (off base (c.sl FLAG)) 32 &&& _ = _
    rw [m₄, m₃, ← flagW, flag₂]
    simp only [not_not]
    exact mask32_and _ _

end VG.Proof.EcKey.Compressed.Arm

end

end


/-! # Coordinate recovery and final checks preserve the parsed encoding -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm
open VG.Impl.Ecdh.Arm (QY QYM R2P W0 W1 W2 W3)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Impl.EcKey.Compressed (chooseRoot)

def keyRhs (c : Cfg) (s : State) : Spec.Weierstrass.Fe c.C :=
  let x := Fin.ofNat c.C.p (keyX c s)
  x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

def keyRoot (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :=
  chooseRoot (root (keyRhs c s)) ((s.mem (ptr s .r1)).toNat % 2)

def CompressedAccept (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s : State) : Prop := CompressedPrefix c s ∧
  (keyRoot c root s * keyRoot c root s = keyRhs c s ∧
    (keyRoot c root s).val % 2 = (s.mem (ptr s .r1)).toNat % 2)

instance (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :
    Decidable (CompressedAccept c root s) := inferInstanceAs (Decidable (_ ∧ (_ ∧ _)))

structure DecompressChecked (c : Cfg)
    (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s₀ : State) (s : State) : Prop where
  scr : Scr s (ptr s₀ .r2) size
  saved : ∀ rd ∈ Cfg.saved, s.mem.readW (off (ptr s₀ .r2) rd.2) 32 = s₀.gpr rd.1
  out : s.gpr .lr = s₀.gpr .r0
  x : sv c (ptr s₀ .r2) s E = keyX c s₀
  y : sv c (ptr s₀ .r2) s QY = (keyRoot c root s₀).val
  flag : flagW c (ptr s₀ .r2) s = mask32 (CompressedAccept c root s₀)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressMiddle_ok {c : Cfg} (hc : CfgOk c)
    {root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C} (hroot : CandidateCorrect c root)
    {s₀ s : State} (F : DecompressFront c s₀ s) :
    WP isa (.seq (Impl.EcKey.Compressed.Arm.rootCandidate c)
      (.seq (Impl.EcKey.Compressed.Arm.selectRoot c)
        (Impl.EcKey.Compressed.Arm.checkRoot c))) s (DecompressChecked c root s₀) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := F.scr.nowrap
  refine WP.seq (WP.mono (hroot _ s F.scr F.far (modP_of hc F.fixed.mp) F.rhs_lt F.fixed.onep)
    fun s₁ C => ?_)
  obtain F₁ := F.frame hc C.keep C.unch (candidate_fixed hc) (by
    intro i hi
    obtain h : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 ∧ i ∉ candidateSlots := by decide
    exact candidate_apart hc (h i hi).1 (h i hi).2)
  obtain root₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ .r2) s₁ ACC) = root (keyRhs c s₀) := by
    rw [C.val, F.rhs]; rfl
  refine WP.seq (WP.mono (selectRoot_ok hc F₁.scr F₁.far (modP_of hc F₁.fixed.mp)
    F₁.fixed.one F₁.fixed.zero) fun s₂ S => ?_)
  obtain F₂ := F₁.frame hc (S.keep.mono (by decide)) S.unch
    (fixedOk_slWk h7 (l := [QY, W0, TMP]) (by decide)) (by
      intro i hi
      obtain h : ∀ i ∈ [E, D, R2P, W2, FLAG], i ∉ [QY, W0, TMP] := by decide
      exact apart_slWk h7 (by
        obtain H : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 := by decide
        exact H i hi) (h i hi))
  obtain y₂ : Fin.ofNat c.C.p (sv c (ptr s₀ .r2) s₂ QY) = keyRoot c root s₀ := by
    rw [S.val, root₁, F₁.tag]
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
      (s₀.mem (ptr s₀ .r1)).toNat < 2 ^ 32 from Nat.lt_trans (BitVec.isLt _) (by decide))]
    rfl
  obtain yval₂ : sv c (ptr s₀ .r2) s₂ QY = (keyRoot c root s₀).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt S.lt] using congrArg Fin.val y₂
  refine WP.mono (checkRoot_ok hc F₂.scr F₂.far (modP_of hc F₂.fixed.mp) S.lt
    F₂.rhs_lt F₂.r2 F₂.flag) fun s₃ K => ?_
  obtain F₃ := F₂.fixed.unch h7 hn
    (fixedOk_slWk h7 (l := [QYM, W1, W3, TMP, FLAG]) (by decide)) K.unch
  have e₃ {i : Nat} (hi : i < 45) (hw : i ∉ [QYM, W1, W3, TMP, FLAG]) :
      sv c (ptr s₀ .r2) s₃ i = sv c (ptr s₀ .r2) s₂ i :=
    sv_unch K.unch h7 hn hi (apart_slWk h7 hi hw)
  refine ⟨K.scr, F₃.saved, (K.keep.gpr _ (by decide)).trans F₂.out,
    (e₃ (by decide) (by decide)).trans F₂.x,
    (e₃ (by decide) (by decide)).trans yval₂, ?_, K.keep.sp.trans F₂.sp,
    K.keep.rd.trans F₂.rd, K.keep.wr.trans F₂.wr⟩
  rw [K.flag, y₂, yval₂, F₂.rhs, F₂.tag]
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
    (s₀.mem (ptr s₀ .r1)).toNat < 2 ^ 32 from Nat.lt_trans (BitVec.isLt _) (by decide))]
  simp only [mask32, CompressedAccept, keyRhs, and_assoc]

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! # Decompression meets the merged API contract -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/Arm/DecompressFinish.lean`, which only this module imported.
section

section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.Mont VG.Proof.Mont.Arm
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.EcKey.Arm (pointFinish_ok)

variable {c : Cfg}

theorem decompressFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {o32 : BitVec 32}
    (hlr : s.gpr .lr = o32) (hofit : o32.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 32)
    (hw : (⟨State.addr o32, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨State.addr o32, 1 + 2 * c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.decompressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (State.addr o32) (1 + 2 * c.C.len) =
        (if b then 4 :: (toBytes c.C.len (sv c base s E) ++ toBytes c.C.len (sv c base s Impl.Ecdh.Arm.QY))
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      s'.gpr .r0 = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
      Rest [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' ∧
      Outside (State.addr o32) 0 (1 + 2 * c.C.len) s.mem s'.mem :=
  pointFinish_ok hc (by decide) (by decide) hs hlr hofit hw hd hsv b hf

end VG.Proof.EcKey.Compressed.Arm
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm Spec.Weierstrass

theorem decompress_key (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) :
    Impl.EcKey.Compressed.decode c.C root
      (Spec.EcKey.bytesAt s.mem (ptr s .r1) (c.C.len + 1)) =
    if CompressedAccept c root s then
      some (.affine (Fin.ofNat c.C.p (keyX c s)) (keyRoot c root s)) else none := by
  have hb : Spec.Ecdsa.bytesAt s.mem (ptr s .r1) (c.C.len + 1) =
      s.mem (ptr s .r1) :: Spec.Ecdsa.bytesAt s.mem (ptr s .r1 + 1) c.C.len := by
    rw [Nat.add_comm c.C.len 1, bytesAt_add]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
      List.cons_append, List.nil_append]
    rfl
  apply decode_checked_eq root (length_bytesAt _ _ _)
    (by change (Spec.Ecdsa.bytesAt _ _ _).head? = _; rw [hb]; rfl)
    (by change ofBytes ((Spec.Ecdsa.bytesAt _ _ _).drop 1) = _; rw [hb]; rfl)

theorem decompress_correct (c : Cfg) (hc : CfgOk c)
    (root : Fe c.C → Fe c.C) (hroot : CandidateCorrect c root)
    (s : State) (hs : (decompressContract c.C root).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.Arm.decompress c) s t s' ∧
      abiPreserved s s' ∧ (decompressContract c.C root).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfit, hpkfit, hwfit⟩ := hs
  have hp : InputPre c (1 + c.C.len) s :=
    ⟨by rw [hrd]; simp [Nat.add_comm], by rw [hwr]; simp,
      by simpa only [Nat.add_comm] using hpw, by omega_using [hpkfit], hwfit⟩
  have hrun : WP isa (Impl.EcKey.Compressed.Arm.decompress c) s fun s' =>
      (decompressContract c.C root).post s s' ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s.gpr rd.1) ∧ s'.sp = s.sp := by
    apply decompressFront_ok hc hp
    intro t F
    refine WP.seq (WP.mono (decompressMiddle_ok hc hroot F) fun u U => ?_)
    refine WP.mono (decompressFinish_ok hc U.scr U.out (by omega_using [hfit])
      (by rw [U.wr, hwr, show 1 + 2 * c.C.len = 2 * c.C.len + 1 by omega_using []]; simp)
      (by simpa only [Nat.add_comm] using how.sub_right (Region.sub_prefix (by decide : size ≤ 8192)))
      U.saved (decide (CompressedAccept c root s)) (by simp only [U.flag, decide_eq_true_eq]))
      fun s' ⟨hout, hret, hsave, K, _⟩ => ?_
    refine ⟨?_, hsave, K.sp.trans U.sp⟩
    dsimp only [decompressContract]
    rw [decompress_key]
    rw [U.x, U.y] at hout
    change Spec.EcKey.bytesAt s'.mem (ptr s .r0) (1 + 2 * c.C.len) = _ at hout
    simp only [decide_eq_true_eq] at hret hout
    simp only [BitVec.setWidth_append_eq_right]
    by_cases hk : CompressedAccept c root s
    · rw [ite_eq_left hk] at hret hout ⊢
      refine ⟨hret, ?_⟩
      change Spec.EcKey.bytesAt s'.mem (ptr s .r0) (2 * c.C.len + 1) =
        4 :: (toBytes c.C.len (Fin.ofNat c.C.p (keyX c s)).val ++ toBytes c.C.len (keyRoot c root s).val)
      simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt hk.1.2, Nat.add_comm] using hout
    · rw [ite_eq_right hk] at hret hout ⊢
      exact ⟨hret, by simpa only [Nat.add_comm] using hout⟩
  obtain ⟨t, s', he, hpost, hsave, hsp⟩ := hrun
  refine ⟨t, s', he, ⟨?_, hsp⟩, hpost⟩
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsave (.r4, 0) (by decide)
  · exact hsave (.r5, 4) (by decide)
  · exact hsave (.r6, 8) (by decide)
  · exact hsave (.r7, 12) (by decide)
  · exact hsave (.r8, 16) (by decide)
  · exact hsave (.r9, 20) (by decide)
  · exact hsave (.r10, 24) (by decide)
  · exact hsave (.r11, 28) (by decide)
  · exact hsave (.lr, 32) (by decide)

end VG.Proof.EcKey.Compressed.Arm
