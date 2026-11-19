module

public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Front
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
import VerifiedGarbage.Proof.EcKey.X86.Finish
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Spec.EcKey.Compressed
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
public import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Ecdh.X86.Validate
public import VerifiedGarbage.Impl.Weierstrass.X86
public import VerifiedGarbage.Proof.Mont.X86.Loop
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Weierstrass.X86.Pow
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Ecdh.X86.Main
public import VerifiedGarbage.Impl.EcKey.Compressed
public import VerifiedGarbage.Proof.EcKey.Compressed.Root
import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Proof.Weierstrass.Layout
import VerifiedGarbage.Proof.Weierstrass.X86.Bits
public import VerifiedGarbage.Proof.Framework.X86.Exec

/-! ### `EcKey.Compressed.X86.DecompressMain`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.X86.SlotOps`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.X86.Frame`, which the modules that import this one used -/

section

/-! # Frames for the converter's scratch slots -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Ecdsa.X86
open VG.Impl.Ecdsa.X86

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

end VG.Proof.EcKey.Compressed.X86

end

end

/-! ### `EcKey.Compressed.X86.Candidate`, which the modules that import this one used -/

section

/-! ### `EcKey.Compressed.X86.RootPow`, which this module and modules that import it used -/

section

/-! # The root exponentiation's workspace layout -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG.Impl.Ecdsa.X86 VG.Impl.Ecdh.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86

/-- The square-root power uses the same accumulator and temporary as the
existing powers, and a table separate from Montgomery's temporary area. -/
theorem rootPow_lay {c : Cfg} (hc : CfgOk c) {j : Nat} (hj : j < 3)
    : PowLay (Impl.EcKey.Compressed.X86.rootPow c j) size :=
  powLay_of hc (jm := MP) (by decide) _ hj (base := W2) (by decide) (by decide)
    (one := ONEP) (by decide) (by decide)

theorem rootPow_wk {c : Cfg} (hc : CfgOk c) {j : Nat} (hj : j < 3) :
    PowWk (Impl.EcKey.Compressed.X86.rootPow c j) c.SP c.C.p size c.wk :=
  powWk_of hc hc.fp (jm := MP) (by decide) _ hj (base := W2) (by decide)

/-- The precise writes of one root exponentiation. -/
abbrev rootPowerWrites (c : Cfg) (j : Nat) : List (Nat × Nat) :=
  [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
    powWx (Impl.EcKey.Compressed.X86.rootPow c j) c.wk

theorem rootPower_apart {c : Cfg} (hc : CfgOk c) {i j : Nat} (hi : i < 45)
    (hw : i ∉ [EXPP, ACC, PT, TMP]) :
    ∀ w ∈ rootPowerWrites c j, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  change ∀ w ∈ [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
    (slW c [ACC, PT, TMP] ++ wkW c), _
  apply apart_append
  · intro w h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact sl_apart c (by intro h; exact hw (h ▸ (by simp)))
    · exact (apart_tbl hi j) _ (by simp)
  · exact apart_append (apart_slW (fun h => hw (List.mem_cons_of_mem _ h))) (apart_wk hi)

/-- Materializing an exponent and running the field power. -/
theorem rootPower_ok {c : Cfg} (hc : CfgOk c) {e j : Nat}
    (hj : j < 3) (he : e < 2 ^ (64 * c.n))
    {base : Addr} {s : State} (hs : Scr s base size)
    (_hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86.rootPower c e j) s fun s' =>
      Keeps powClob s s' ∧
      Unch base ([(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
        powWx (Impl.EcKey.Compressed.X86.rootPow c j) c.wk) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ e := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have h0 := hc.n0
  have hE := sl_le c h7 (i := EXPP) (by decide)
  rw [Impl.EcKey.Compressed.X86.rootPower]
  change WP isa (.seq (.block (setConst c.n (c.sl EXPP) e))
    (.seq (bits (c.sl EXPP) (bitsAt c.n j) (8 * c.n))
      (pow (Impl.EcKey.Compressed.X86.rootPow c j) c.SP))) s _
  refine WP.seq (WP.mono (setConst_ok hs hE he) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.seq (WP.mono (bits_ok hs₁ h0 hE (bitsAt_le c h7 hj)
    (Or.inl (sl_below_bits c (i := EXPP) (by decide) j 0)))
    fun s₂ ⟨bits₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have keep₂ {i : Nat} (hi : i < 45) (hiE : i ≠ EXPP) (hiT : i ≠ TMP) :
      sv c base s₂ i = sv c base s i := by
    have hsl := sl_le c h7 hi
    rw [sv, O₂.wordsVal (Or.inl (sl_below_bits c hi j 0)) (by omega_using [hn, hsl]),
      O₁.wordsVal (sl_apart c hiE) (by omega_using [hn, hsl])]
  have B₂ : wordsVal s₂.mem base (c.sl W2) c.n < c.C.p := by
    rw [show wordsVal s₂.mem base (c.sl W2) c.n = sv c base s₂ W2 from rfl,
      keep₂ (by decide) (by decide) (by decide)]
    exact hB
  have O₂' : wordsVal s₂.mem base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p := by
    rw [show wordsVal s₂.mem base (c.sl ONEP) c.n = sv c base s₂ ONEP from rfl,
      keep₂ (by decide) (by decide) (by decide)]
    exact hO
  refine WP.mono (pow_ok (rootPow_lay hc hj) (rootPow_wk hc hj)
    (unitMod_pow_two hc.p_odd (64 * c.n)) hs₂ B₂ O₂'
    (by simpa only [e₁, Impl.EcKey.Compressed.X86.rootPow] using bits₂) he) fun s₃ ⟨k₃, U₃, lt₃, v₃⟩ => ?_
  refine ⟨?_, (O₁.unch.trans O₂.unch).trans U₃, lt₃, ?_⟩
  · exact ((k₁.mono (by simp [powClob, clob])).trans (k₂.mono (by simp [powClob, clob]))).trans k₃
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ ACC) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ W2) ^ e at v₃
    rw [keep₂ (by decide) (by decide) (by decide)] at v₃
    exact v₃

/-- The three-mod-four candidate uses an exponent derived from the prime. -/
theorem rootThree_ok {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 = 3)
    {base : Addr} {s : State} (hs : Scr s base size)
    (_hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86.rootCandidate c) s fun s' =>
      Keeps powClob s s' ∧
      Unch base ([(c.sl EXPP, 8 * c.n), (bitsAt c.n 2, 64 * c.n)] ++
        powWx (Impl.EcKey.Compressed.X86.rootPow c 2) c.wk) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((c.C.p + 1) / 4) := by
  simp only [Impl.EcKey.Compressed.X86.rootCandidate, hp, ↓reduceIte]
  exact rootPower_ok hc (by decide)
    (by have := hc.p_lt; have := hc.p_ge; omega_arith) hs _hM hB hO

end VG.Proof.EcKey.Compressed.X86

end

end

/-! # The machine root candidate's shared refinement interface -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86


open VG VG.X86 VG.Impl.Ecdsa.X86
open VG.Impl.Ecdh.X86 (W0 W2)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

/-- Writes shared by exponentiation and the P-224 descent. -/
def candidateSlots : List Nat := [ACC, PT, TMP, EXPP, EXPN, T0, T1, T2, T3, T4, T5, W0]
def candidateWrites (c : Cfg) : List (Nat × Nat) := slWk c candidateSlots ++
  [(bitsAt c.n 1, 64 * c.n), (bitsAt c.n 2, 64 * c.n)]

structure CandidatePost (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (base : Addr) (s s' : State) : Prop where
  keep : Keeps powClob s s'
  unch : Unch base (candidateWrites c) s.mem s'.mem
  lt : sv c base s' ACC < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
    root (toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2))

/-- This is discharged by the assembly proofs for each root method. -/
def CandidateCorrect (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) : Prop :=
  ∀ (base : Addr) (s : State), Scr s base size →
    ModOkW c.MP' size c.C.p s.mem base → sv c base s W2 < c.C.p →
    sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p →
    WP isa (Impl.EcKey.Compressed.X86.rootCandidate c) s (CandidatePost c root base s)

theorem candidate_fixed {c : Cfg} (hc : CfgOk c) : FixedOk c (candidateWrites c) :=
  (fixedOk_slWk (l := candidateSlots) (by decide)).append (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact (fixedOk_tbl 1 hc.n10) _ (by simp)
    · exact (fixedOk_tbl 2 hc.n10) _ (by simp))

theorem candidate_apart {c : Cfg} (hc : CfgOk c) {i : Nat} (hi : i < 45) (hw : i ∉ candidateSlots) :
    ∀ w ∈ candidateWrites c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  apply apart_append (apart_slWk hi hw)
  intro w h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact (apart_tbl hi 1) _ (by simp)
  · exact (apart_tbl hi 2) _ (by simp)

theorem candidateThree_correct {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 = 3) :
    CandidateCorrect c Impl.EcKey.Compressed.rootThreeModFour := by
  intro base s hs hM hB hO
  refine WP.mono (rootThree_ok hc hp hs hM hB hO) fun s' ⟨k, U, lt, v⟩ => ?_
  refine ⟨k, U.mono ?_, lt, ?_⟩
  · intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, powWx, powW,
      Impl.EcKey.Compressed.X86.rootPow] at hw
    rcases hw with (rfl | rfl) | (rfl | rfl | rfl) | rfl | rfl
    all_goals simp [candidateWrites, candidateSlots, slWk, wkW, slW, MP'_n, MP'_tmp]
  · simpa only [Impl.EcKey.Compressed.rootThreeModFour, pow_eq_npow] using v

end VG.Proof.EcKey.Compressed.X86

end

end

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86

theorem slSub_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45)
    (hA : sv c base s a < c.C.p) (hB : sv c base s b < c.C.p) :
    WP isa (Mont.subCall c.SP (c.sl o) (c.sl a) (c.sl b)) s fun t =>
      CKeep c.MP' base c.wk (c.sl o) s t ∧
      sv c base t o = (sv c base s a + c.C.p - sv c base s b) % c.C.p :=
  subC_ok (slCall (MP'_n c) hc.fp) hs (sl_below_wk c ho) (sl_below_wk c ha) (sl_below_wk c hb) hA hB

end VG.Proof.EcKey.Compressed.X86

end

end

/-! ### `EcKey.Compressed.X86.DecompressContract`, which this module and modules that import it used -/

section

/-! # Decompression's signature obligations on 32-bit x86 -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86

def decompressContract (C : Spec.Weierstrass.Curve)
    (root : Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C) (wide : Bool := false) : Contract isa where
  pre := codecPre (C.len + 1) (2 * C.len + 1) wide
  post s s' :=
    match Impl.EcKey.Compressed.decode C root (Spec.EcKey.bytesAt s.mem ((arg s 1).setWidth 64) (C.len + 1)) with
    | some Q => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * C.len + 1) = Spec.EcKey.encodePoint Q
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * C.len + 1) = List.replicate (2 * C.len + 1) 0
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

theorem decompress_implies (I : Spec.EcKey.Instance)
    (root : Spec.Weierstrass.Fe I.curve → Spec.Weierstrass.Fe I.curve)
    (hf : RootFacts root)
    (hsat : ∃ s, (I.decompressPublicKeyContract abi 28).pre s) :
    (decompressContract I.curve root true).Implies (I.decompressPublicKeyContract abi 28) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argSlots, argVal, argBytes, stackBelow, decompressContract, codecPre]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argSlots, argVal, argBytes, stackBelow, decompressContract, codecPre]
    cases he : Impl.EcKey.Compressed.decode I.curve root
        (Spec.EcKey.bytesAt s.mem ((arg s 1).setWidth 64) (I.curve.len + 1)) with
    | none =>
      simp only [decompressContract, he] at h
      exact Or.inr ⟨h.1, (decode_none_iff hf _).mp he, h.2⟩
    | some Q =>
      simp only [decompressContract, he] at h
      exact Or.inl ⟨h.1, Q, decode_sound he, h.2⟩
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argSlots, argVal, argBytes, stackBelow, decompressContract, codecPre]
  sat := hsat

end VG.Proof.EcKey.Compressed.X86

end

end

/-! ### `EcKey.Compressed.X86.DecompressMiddle`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.X86.Parity`, which only this module used -/

section

/-! # Match the recovered root's low bit on 32-bit x86 -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

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
    (hy : c.sl Impl.Ecdh.X86.QY + 4 ≤ size) (ht : c.sl D + 4 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.X86.parityMask c)) s fun t =>
      t.gpr .ecx = mask32 (sv c base s Impl.Ecdh.X86.QY % 2 ≠
        (s.mem.readW (off base (c.sl D)) 32).toNat % 2) ∧
      Keeps [.eax, .ecx, .edx] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.X86.parityMask
  refine wp_movS (readSrc_sc hs hy) fun s₁ u₁ _ => ?_
  have hs₁ := hs.of_keeps (u₁.keeps) (by decide)
  refine wp_movS (readSrc_sc hs₁ ht) fun s₂ u₂ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₃ u₃ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  refine wp_movi fun s₅ u₅ => ?_
  refine wp_subS rfl fun s₆ u₆ _ => ?_
  refine wp_mov fun t u₇ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [u₇.gpr, u₆.gpr, u₅.gpr, u₅.other .ecx (by decide), u₄.gpr, u₃.gpr,
      u₂.gpr, u₂.other .eax (by decide), u₁.gpr, u₁.mem]
    simp only [ite_true, reduceCtorEq, ite_false]
    rw [BitVec.xor_comm, xor_low_mask32, slot32_parity _ _ _ _ hn]
  · exact (u₁.keeps.mono (by simp)).trans ((u₂.keeps.mono (by simp)).trans
      ((u₃.keeps.mono (by simp)).trans ((u₄.keeps.mono (by simp)).trans
      ((u₅.keeps.mono (by simp)).trans ((u₆.keeps.mono (by simp)).trans (u₇.keeps.mono (by simp)))))))
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem invertMask_ok (s : State) (P : Prop) [Decidable P] (h : s.gpr .ecx = mask32 P) :
    WP isa (.block Impl.EcKey.Compressed.X86.invertMask) s fun t =>
      t.gpr .edx = mask32 (¬ P) ∧ Keeps [.eax, .edx] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.X86.invertMask
  refine wp_mov fun s₁ u₁ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => ?_
  refine wp_movi fun s₃ u₃ => ?_
  refine wp_subS rfl fun s₄ u₄ _ => ?_
  refine wp_mov fun t u₅ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other .edx (by decide), u₂.gpr, u₁.gpr, h]
    by_cases hp : P <;> simp [mask32, hp]
  · exact (u₁.keeps.mono (by simp)).trans ((u₂.keeps.mono (by simp)).trans
      ((u₃.keeps.mono (by simp)).trans ((u₄.keeps.mono (by simp)).trans (u₅.keeps.mono (by simp)))))
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

end VG.Proof.EcKey.Compressed.X86

end

end

/-! ### `EcKey.Compressed.X86.DecompressFront`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.X86.Rhs`, which only this module used -/

section

/-! # The curve polynomial used by coordinate recovery -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdh.X86 (R2P BP QXM QYM QY W0 W1 W2 W3)
open VG.Impl.EcKey.Compressed.X86 (rhsOps)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Ecdh.X86

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
  rest : Keeps clob s s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slWk c [QXM, W1, W2, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W2 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W2) =
    let x := Fin.ofNat c.C.p (sv c base s E)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

theorem rhs_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (Impl.Weierstrass.X86.fprog c.SP (rhsOps c)) s (RhsPost c base s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  change WP isa (.seq (VG.Impl.Weierstrass.X86.Mont.mulCall c.SP
    (c.sl QXM) (c.sl E) (c.sl R2P))
    (VG.Impl.Weierstrass.X86.fprog c.SP (rhsTail.map (FOp.rename c.sl)))) s _
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) hc.fp h7 hs (o := QXM) (a := E) (b := R2P)
    (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain hM₁ := hM.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ QXM) = Fin.ofNat c.C.p (sv c base s E) :=
    toM_r2 hpR (by simpa only [hr2, Cfg.R] using e₁)
  obtain a₁ : sv c base s₁ AP = c.mont c.C.a :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hap
  obtain b₁ : sv c base s₁ BP = c.mont c.C.b :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hbp
  obtain hL : Lay c.MP' size (· ∈ rhsSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hW : WkOk c.SP c.MP' c.C.p size c.wk (· ∈ rhsSlots.map c.sl) := by
    refine ⟨slCall (MP'_n c) hc.fp, ?_, sl_below_wk c (by decide), sl_below_wk c (by decide)⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain H : ∀ i ∈ rhsSlots, i < 45 := by decide
    exact sl_below_wk c (H i hi)
  obtain I : Inv c.MP' base size c.C.p (· ∈ rhsSlots.map c.sl) ([QXM, AP, BP].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base o c.n)) s₁ := by
    refine ⟨hs₁, hM₁, ?_, ?_, fun _ _ => rfl⟩
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
  refine WP.mono (fprog_ok hL hW hpR _ I (fun op hop x hx => ?_)
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
      rcases hw with rfl | rfl | rfl
      · exact List.mem_append_left _ (List.mem_map_of_mem (by decide))
      · exact List.mem_append_right _ (by simp [MP'_n, wkW])
      · exact List.mem_append_right _ (by simp [wkW])
  refine ⟨PK.scr hs₁, I₂.mod, Keeps.trans ⟨k₁.gpr, k₁.rd, k₁.wr⟩ ⟨PK.gpr, PK.rd, PK.wr⟩,
    PK.rd.trans k₁.rd, PK.wr.trans k₁.wr,
    (U₁.trans U₂).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw), I₂.lt _ hw, ?_⟩
  simpa only [sv, MP'_n, a₁, b₁, toM_cmont hc, v₁] using v₂

end VG.Proof.EcKey.Compressed.X86

end

end

/-! ### `EcKey.Compressed.X86.Peer`, which only this module used -/

section

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86/TagCheck.lean`, which only this module imported.
section

/-! # Accept exactly SEC 1 tags 02 and 03 on 32-bit x86 -/

section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Ecdh.X86

private theorem tag_key (b : Byte) :
    (((b.setWidth 32 ||| 1) ^^^ 3).toNat < (1 : BitVec 32).toNat) ↔ b = 2 ∨ b = 3 := by
  revert b; decide +kernel

theorem decompressTag_ok {c : Cfg} {s : State} {base : Addr} {q : BitVec 32}
    (hs : Scr s base size) (hq : readSrc s (.mem (Cfg.argOp 1)) = some q)
    (hin : InRegions (s.rd ++ s.wr) (q.setWidth 64) 1) (hD : c.sl D + 4 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.X86.decompressTag c)) s fun t =>
      t.gpr .edx = mask32 (s.mem (q.setWidth 64) = 2 ∨ s.mem (q.setWidth 64) = 3) ∧
      t.mem.readW (off base (c.sl D)) 32 = (s.mem (q.setWidth 64)).setWidth 32 ∧
      Keeps [.ebx, .edx] s t ∧ Outside base (c.sl D) 4 s.mem t.mem := by
  unfold Impl.EcKey.Compressed.X86.decompressTag
  refine wp_movS hq fun s₁ u₁ _ => ?_
  refine wp_movzx8S (a := q.setWidth 64)
    (by show (s₁.gpr .ebx + BitVec.ofNat 32 0).setWidth 64 = _; rw [u₁.gpr, BitVec.add_zero])
    (by rw [u₁.rd, u₁.wr]; exact hin) fun s₂ u₂ _ => ?_
  obtain K₂ : Keeps [.ebx, .edx] s s₂ := (u₁.keeps.mono (by simp)).trans (u₂.keeps.mono (by simp))
  obtain hs₂ := hs.of_keeps K₂ (by decide)
  refine wp_storeS (hs₂.ea (by omega)) (hs₂.write hD) fun s₃ m₃ => ?_
  refine wp_orS rfl fun s₄ u₄ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₅ u₅ => ?_
  refine wp_subS rfl fun s₆ u₆ cf₆ => ?_
  refine wp_sbbS rfl cf₆ fun t u₇ _ => WP.block_nil ?_
  obtain hm : t.mem = s.mem.writeW (off base (c.sl D)) ((s.mem (q.setWidth 64)).setWidth 32) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.mem]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u₇.gpr, sbb_mask]
    simp only [u₅.gpr, u₄.gpr, m₃.gpr, u₂.gpr, u₁.mem, reduceCtorEq, ite_false, decide_eq_true_eq, tag_key]
  · rw [hm, Mem.readW_writeW_self32]
  · exact K₂.trans ((m₃.keeps _).trans ((u₄.keeps.mono (by simp)).trans
      ((u₅.keeps.mono (by simp)).trans ((u₆.keeps.mono (by simp)).trans (u₇.keeps.mono (by simp))))))
  · rw [hm]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.EcKey.Compressed.X86
end

end

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86 VG.Impl.Ecdsa.X86
open VG.Impl.Ecdh.X86 (R2P BP)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Ecdh.X86 Spec.Weierstrass

theorem decompressPeer_eq (c : Cfg) : Impl.EcKey.Compressed.X86.decompressPeer c =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++
    (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (([.mov .ebx (.mem (Cfg.argOp 1)), .alu .add .ebx (.imm 1)] : List Instr) ++
    (loadBytes c.C.len c.n (c.sl E) .ebx ++
    (Impl.EcKey.Compressed.X86.decompressTag c ++
    (c.andFlag ++ Impl.Ecdh.X86.Cfg.checkLtP c (c.sl E)))))) := by
  simp only [Impl.EcKey.Compressed.X86.decompressPeer, Impl.Ecdh.X86.Cfg.consts,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem decompressPeer_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} {q32 : BitVec 32}
    (hs : Scr s base size)
    (hq : ∀ t : State, t.gpr .esp = s.gpr .esp → t.rd ++ t.wr = s.rd ++ s.wr →
      Outside base 0 size s.mem t.mem → readSrc t (.mem (Cfg.argOp 1)) = some q32)
    (hqfit : q32.toNat + (1 + c.C.len) ≤ 2 ^ 32)
    (hin : (⟨q32.setWidth 64, 1 + c.C.len⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨q32.setWidth 64, 1 + c.C.len⟩ ⟨base, size⟩)
    (hmp : sv c base s MP = c.C.p) (hf : flagW c base s = BitVec.allOnes 32) :
    WP isa (.block (Impl.EcKey.Compressed.X86.decompressPeer c)) s fun t =>
      Scr t base size ∧ Keeps [.eax, .ebx, .edx] s t ∧
      Unch base (slW c [R2P, BP, E, D, FLAG]) s.mem t.mem ∧
      sv c base t R2P = c.R * c.R % c.C.p ∧ sv c base t BP = c.mont c.C.b ∧
      sv c base t E = ofBytes (Spec.Ecdsa.bytesAt s.mem (q32.setWidth 64 + 1) c.C.len) ∧
      t.mem.readW (off base (c.sl D)) 32 = (s.mem (q32.setWidth 64)).setWidth 32 ∧
      flagW c base t = mask32 ((s.mem (q32.setWidth 64) = 2 ∨ s.mem (q32.setWidth 64) = 3) ∧
        sv c base t E < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  obtain hF : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_using [hl8, hlhi, this]
  obtain hR2 := sl_le c h7 (i := R2P) (by decide)
  obtain hB := sl_le c h7 (i := BP) (by decide)
  obtain hE := sl_le c h7 (i := E) (by decide)
  obtain hM := sl_le c h7 (i := MP) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  generalize hq64 : q32.setWidth 64 = q at hin hd ⊢
  rw [decompressPeer_eq]
  -- The constants.
  refine WP.block_append (WP.mono (setConst_ok hs hR2 (show c.R * c.R % c.C.p < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp3])) hpl)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.block_append (WP.mono (setConst_ok hs₁ hB (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp3])) hpl)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  obtain W₂ : Outside base 0 size s.mem s₂.mem :=
    (O₁.mono (Nat.zero_le _) (by omega_using [hR2])).trans (O₂.mono (Nat.zero_le _) (by omega_using [hB]))
  obtain k₂' : Keeps [.eax] s s₂ := k₁.trans k₂
  -- `peer + 1`
  refine WP.block_append ?_
  refine wp_movS (hq s₂ (k₂'.1 _ (by decide)) (by rw [k₂'.2.1, k₂'.2.2]) W₂) fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => WP.block_nil ?_
  obtain k₄ : Keeps [.eax, .ebx] s s₄ := ((k₂'.mono (by decide)).widen u₃.keeps).widen u₄.keeps
  obtain hs₄ := hs.of_keeps k₄ (by decide)
  obtain hm₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  obtain hrw₄ : s₄.rd ++ s₄.wr = s.rd ++ s.wr := by rw [k₄.2.1, k₄.2.2]
  obtain hb₄ : s₄.gpr .ebx = q32 + BitVec.ofNat 32 1 := by rw [u₄.gpr, u₃.gpr]; rfl
  obtain hb₄' : (s₄.gpr .ebx).setWidth 64 = q + BitVec.ofNat 64 1 := by
    rw [hb₄, ← hq64]; exact addr_eq (by omega_using [hqfit, hl8])
  obtain hbt₄ : (s₄.gpr .ebx).toNat = q32.toNat + 1 := by
    rw [hb₄, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hqfit, hl8])]
  -- `x`
  refine WP.block_append (WP.mono (loadBytes_ok hs₄ (src := .ebx) (by decide) hE (by omega_using [hqfit, hbt₄]) (by omega_using [hl8]) hlhi
    (fun e he => ⟨_, by rw [hrw₄]; exact hin, by
      rw [hb₄', Offset.add_add]; exact Offset.contains_base q (by omega_using [he]) (by omega_using [hsz, hlhi, hM, he])⟩)
    (by rw [hb₄']; exact (hd.sub_left (Offset.sub_base q (by omega_using []))).sub_right (Offset.sub_base base hE)))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  rw [hb₄', hm₄] at e₅
  rw [hm₄] at O₅
  obtain hs₅ := hs₄.of_keeps k₅ (by decide)
  obtain K₅ : Keeps [.eax, .ebx] s s₅ := k₄.widen k₅
  obtain W₅ : Outside base 0 size s.mem s₅.mem := W₂.trans (O₅.mono (Nat.zero_le _) hE)
  obtain lead₅ : s₅.mem q = s.mem q := by
    obtain e := keep_of_disjoint' W₅ hd (by decide) (i := 0) (by omega_arith) (by omega_arith)
    simpa only [BitVec.add_zero] using e
  refine WP.block_append (WP.mono (decompressTag_ok hs₅
    (hq s₅ (K₅.1 _ (by decide)) (by rw [K₅.2.1, K₅.2.2]) W₅)
    (by rw [hq64, K₅.2.1, K₅.2.2]; exact ⟨_, hin, by simpa using Offset.contains_base q (d := 0) (n := 1) (by omega_arith) (by decide)⟩)
    (by have := sl_le c h7 (i := D) (by decide); omega_arith)) fun s₆ ⟨mask₆, tag₆, k₆, O₆⟩ => ?_)
  rw [hq64, lead₅] at mask₆ tag₆
  obtain hs₆ := hs₅.of_keeps k₆ (by decide)
  refine WP.block_append (WP.mono (andFlag_ok c hs₆ hF) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_)
  obtain hs₇ := hs₆.of_keeps k₇ (by decide)
  refine WP.mono (checkLtP_ok c hs₇ h0 hE hM hF) fun t ⟨f₈, k₈, O₈⟩ => ?_
  obtain U₅ : Unch base (slW c [R2P, BP, E, D]) s.mem s₅.mem :=
    unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (Nat.le_refl _) O₅)
  obtain U₆ := unch_same U₅ (slot_frame (by simp) (by omega_arith) O₆)
  have v₆ {i : Nat} (hi : i < 45) (hw : i ∉ [R2P, BP, E, D]) :
      sv c base s₆ i = sv c base s i := sv_unch U₆ h7 hn hi (apart_slW hw)
  obtain x₆ : sv c base s₆ E = ofBytes (Spec.Ecdsa.bytesAt s.mem (q + 1) c.C.len) := by
    change wordsVal s₆.mem base (c.sl E) c.n = _
    rw [sv_out (O₆.mono (Nat.le_refl _) (by omega_arith : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide), e₅]
    congr 1
    exact bytesAt_keep W₂ (hd.sub_left (Offset.sub_base q (d := 1) (by omega_arith))) (by decide) (by omega_arith)
  obtain flag₆ : flagW c base s₆ = BitVec.allOnes 32 := by
    rw [flagW, ← hf]
    exact Unch.readW32 U₆ (fun w hw => by have := (apart_slW (c := c) (by decide : FLAG ∉ [R2P, BP, E, D])) w hw; omega_arith) (by omega_arith)
  refine ⟨hs₇.of_keeps k₈ (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (K₅.mono (by decide)).trans ((k₆.mono (by decide)).trans ((k₇.mono (by decide)).trans (k₈.mono (by decide))))
  · exact unch_same (unch_same (slots_widen U₆ (slots' := [R2P, BP, E, D, FLAG]) (by decide)) (slot_frame (by simp) (by omega_arith) O₇)) (slot_frame (by simp) (by omega_arith) O₈)
  · simp only [sv] at *
    rw [sv_flag O₈ h0 h7 hn (by decide) (by decide), sv_flag O₇ h0 h7 hn (by decide) (by decide),
      sv_out (O₆.mono (Nat.le_refl _) (by omega_arith : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₅ h7 hn (by decide) (by decide), sv_out O₂ h7 hn (by decide) (by decide)]
    exact e₁
  · simp only [sv] at *
    rw [sv_flag O₈ h0 h7 hn (by decide) (by decide), sv_flag O₇ h0 h7 hn (by decide) (by decide),
      sv_out (O₆.mono (Nat.le_refl _) (by omega_arith : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₅ h7 hn (by decide) (by decide)]
    exact e₂
  · simp only [sv] at *
    rw [sv_flag O₈ h0 h7 hn (by decide) (by decide), sv_flag O₇ h0 h7 hn (by decide) (by decide), x₆]
  · rw [BitVec.eq_of_toNat_eq (O₈.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_arith) (by omega_arith)),
      BitVec.eq_of_toNat_eq (O₇.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_arith) (by omega_arith))]
    exact tag₆
  · simp only [sv] at *
    rw [f₈, f₇, flag₆, mask₆, BitVec.allOnes_and,
      show wordsVal s₇.mem base (c.sl E) c.n = sv c base s₇ E from rfl,
      show wordsVal s₇.mem base (c.sl MP) c.n = sv c base s₇ MP from rfl]
    simp only [sv]
    simp only [mask32, sv_flag O₇ h0 h7 hn (i := E) (by decide) (by decide),
      sv_flag O₇ h0 h7 hn (i := MP) (by decide) (by decide),
      v₆ (i := MP) (by decide) (by decide), hmp,
      sv_flag O₈ h0 h7 hn (i := E) (by decide) (by decide)]
    exact mask32_and _ _

end VG.Proof.EcKey.Compressed.X86

end

end


/-! # Prepare the curve polynomial and retain the input checks on 32-bit x86 -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Impl.Ecdh.X86 (R2P BP W2)
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

abbrev CompressedPrefix (c : Cfg) (s : State) : Prop :=
  (s.mem (ptr s 1) = 2 ∨ s.mem (ptr s 1) = 3) ∧ keyX c s < c.C.p

structure DecompressFront (c : Cfg) (s₀ s : State) : Prop where
  scr : Scr s (ptr s₀ 2) size
  fixed : Fixed c (ptr s₀ 2) s₀.gpr s.mem
  x : sv c (ptr s₀ 2) s E = keyX c s₀
  tag : s.mem.readW (off (ptr s₀ 2) (c.sl D)) 32 = (s₀.mem (ptr s₀ 1)).setWidth 32
  r2 : sv c (ptr s₀ 2) s R2P = c.R * c.R % c.C.p
  rhs_lt : sv c (ptr s₀ 2) s W2 < c.C.p
  rhs : toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ 2) s W2) =
    let x := Fin.ofNat c.C.p (keyX c s₀)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b
  flag : flagW c (ptr s₀ 2) s = mask32 (CompressedPrefix c s₀)
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem DecompressFront.frame {c : Cfg} (hc : CfgOk c) {s₀ s t : State}
    (F : DecompressFront c s₀ s) (K : Keeps powClob s t)
    {W : List (Nat × Nat)} (U : Unch (ptr s₀ 2) W s.mem t.mem) (hW : FixedOk c W)
    (ha : ∀ i ∈ [E, D, R2P, W2, FLAG], ∀ w ∈ W,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) : DecompressFront c s₀ t := by
  have hn := F.scr.nowrap
  have h0 := hc.n0
  have h7 := hc.n10
  have e {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      sv c (ptr s₀ 2) t i = sv c (ptr s₀ 2) s i := sv_unch U h7 hn hi (ha i hm)
  have ew {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      t.mem.readW (off (ptr s₀ 2) (c.sl i)) 32 = s.mem.readW (off (ptr s₀ 2) (c.sl i)) 32 :=
    Unch.readW32 U (fun w hw => by have := ha i hm w hw; omega_using [h0, this])
      (by have := sl_le c h7 hi; omega_using [hn, this])
  refine ⟨F.scr.of_keeps K (by decide), F.fixed.unch h7 hn hW U,
     (e (by decide) (by simp)).trans F.x,
    (ew (by decide) (by simp)).trans F.tag, (e (by decide) (by simp)).trans F.r2,
    ?_, ?_, ?_, (K.1 _ (by decide)).trans F.esp, K.2.1.trans F.rd, K.2.2.trans F.wr⟩
  · rw [e (by decide) (by simp)]; exact F.rhs_lt
  · rw [e (by decide) (by simp)]; exact F.rhs
  · rw [flagW, ew (by decide) (by simp), ← flagW]; exact F.flag

theorem decompressFront_ok {c : Cfg} (hc : CfgOk c) {s₀ : State}
    (hp : InputPre c (1 + c.C.len) s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, DecompressFront c s₀ s → WP isa rest s Q) :
    WP isa (.seq (.block (c.setupWith Impl.EcKey.Compressed.X86.args))
      (.seq (.block (Impl.EcKey.Compressed.X86.decompressPeer c))
      (.seq (Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.rhsOps c)) rest))) s₀ Q := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hd : Region.Disjoint ⟨ptr s₀ 1, 1 + c.C.len⟩ ⟨ptr s₀ 2, size⟩ :=
    hp.disjoint
  refine WP.seq (WP.mono (setup_ok hc (input_setup hp (by omega_using []))) fun s₁ S => ?_)
  change SetupPost c Impl.EcKey.Compressed.X86.args s₀ (ptr s₀ 2) s₁ at S
  obtain F₁ := setup_fixed S
  have hn := S.scr.nowrap
  obtain W₁ : Outside (ptr s₀ 2) 0 size s₀.mem s₁.mem := S.unch.outside (by simp)
  refine WP.seq (WP.mono (decompressPeer_ok hc S.scr (q32 := arg s₀ 1)
    (by
      intro t hesp hrw W
      apply argLoad_ok (s₀ := s₀) (i := 1)
      · exact ⟨_, hp.args, arg_containsN (k := 3) (by have := hp.sp_fit; omega_using [this]) (by decide)⟩
      · exact hp.args_sc.sub_left (arg_subN (k := 3) (by have := hp.sp_fit; omega_using [this]) (by decide))
      · exact hesp.trans (S.keep.1 _ (by decide))
      · rw [hrw, S.keep.2.1, S.keep.2.2]
      · exact W₁.trans W)
    hp.pk_fit (by rw [S.keep.2.1, S.keep.2.2]; exact hp.pk) hd F₁.mp S.flag)
    fun s₂ ⟨hs₂, K₂, U₂, r2₂, bp₂, x₂, tag₂, flag₂⟩ => ?_)
  obtain F₂ := F₁.unch h7 hn (fixedOk_slW (l := [R2P, BP, E, D, FLAG]) (by decide)) U₂
  obtain lead : s₁.mem (ptr s₀ 1) = s₀.mem (ptr s₀ 1) := by
    obtain e := keep_of_disjoint' W₁ hd (by decide) (i := 0) (by omega_using []) (by have := hc.len_hi; omega_using [h7, this])
    simpa only [BitVec.add_zero] using e
  obtain x₂' : sv c (ptr s₀ 2) s₂ E = keyX c s₀ := by
    rw [x₂]
    congr 1
    exact bytesAt_keep W₁ (hd.sub_left (Offset.sub_base _ (d := 1) (by omega_using []))) (by decide)
      (by have := hc.len_hi; omega_using [h7, this])
  rw [lead] at tag₂ flag₂
  refine WP.seq (WP.mono (rhs_ok hc hs₂ (modP_of hc F₂.mp) r2₂ F₂.ap bp₂)
    fun s₃ R => ?_)
  obtain F₃ := F₂.unch h7 hn (fixedOk_slWk (l := [Impl.Ecdh.X86.QXM, Impl.Ecdh.X86.W1,
    W2, Impl.Ecdh.X86.W3, TMP]) (by decide)) R.unch
  have e {i : Nat} (hi : i < 45) (hw : i ∉ [Impl.Ecdh.X86.QXM, Impl.Ecdh.X86.W1, W2, Impl.Ecdh.X86.W3, TMP]) :
      sv c (ptr s₀ 2) s₃ i = sv c (ptr s₀ 2) s₂ i :=
    sv_unch R.unch h7 hn hi (apart_slWk hi hw)
  have ew {i : Nat} (hi : i < 45) (hw : i ∉ [Impl.Ecdh.X86.QXM, Impl.Ecdh.X86.W1, W2, Impl.Ecdh.X86.W3, TMP]) :
      s₃.mem.readW (off (ptr s₀ 2) (c.sl i)) 32 = s₂.mem.readW (off (ptr s₀ 2) (c.sl i)) 32 :=
    Unch.readW32 R.unch (fun w hw' => by have := (apart_slWk hi hw h7) w hw'; omega_using [h0, this])
      (by have := sl_le c h7 hi; omega_using [hn, this])
  apply h s₃
  refine ⟨R.scr, F₃,
    (e (by decide) (by decide)).trans x₂', (ew (by decide) (by decide)).trans tag₂,
    (e (by decide) (by decide)).trans r2₂, R.lt, ?_, ?_,
    (R.rest.1 _ (by decide)).trans ((K₂.1 _ (by decide)).trans (S.keep.1 _ (by decide))),
    R.rd.trans (K₂.2.1.trans S.keep.2.1), R.wr.trans (K₂.2.2.trans S.keep.2.2)⟩
  · simpa only [x₂'] using R.val
  · rw [flagW, ew (by decide) (by decide), ← flagW, flag₂, x₂']

end VG.Proof.EcKey.Compressed.X86

end

end

/-! ### `EcKey.Compressed.X86.Check`, which only this module used -/

section

/-! # Check the recovered root's square and parity -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdh.X86 (QY QYM R2P W1 W2 W3)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.Proof.Ecdh.X86


def checkN : List FOp := [.mul QYM QY R2P, .mul W1 QYM QYM, .sub W3 W1 W2]
abbrev checkSlots : List Nat := [QY, R2P, W2, QYM, W1, W3]

theorem checkOps_eq (c : Cfg) : Impl.EcKey.Compressed.X86.checkRootOps c =
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
  keep : Keeps clob s s'
  unch : Unch base (slWk c [QYM, W1, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W3) =
    Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)

theorem checkPoly_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) :
    WP isa (Impl.Weierstrass.X86.fprog c.SP
      (Impl.EcKey.Compressed.X86.checkRootOps c)) s (CheckPolyPost c base s) := by
  have h7 := hc.n10
  obtain hL : Lay c.MP' size (· ∈ checkSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hW : WkOk c.SP c.MP' c.C.p size c.wk (· ∈ checkSlots.map c.sl) := by
    refine ⟨slCall (MP'_n c) hc.fp, ?_, sl_below_wk c (by decide), sl_below_wk c (by decide)⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain H : ∀ i ∈ checkSlots, i < 45 := by decide
    exact sl_below_wk c (H i hi)
  obtain I : Inv c.MP' base size c.C.p (· ∈ checkSlots.map c.sl) ([QY, R2P, W2].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, ?_, ?_, fun _ _ => rfl⟩
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
  refine WP.mono (fprog_ok hL hW (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
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
  refine ⟨PK.scr hs, ⟨PK.gpr, PK.rd, PK.wr⟩, ?_, IT.lt _ hw, ?_⟩
  · apply PK.unch.mono
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_append_left _ (List.mem_map.mpr ⟨op₀.out, checkN_out _ h₀, by rw [FOp.out_rename]; rfl⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact List.mem_append_left _ (List.mem_map_of_mem (by decide))
      · exact List.mem_append_right _ (by simp [MP'_n, wkW])
      · exact List.mem_append_right _ (by simp [wkW])
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base t W3) =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) *
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) at vt
    simpa only [hr2, raw_r2_mul hc] using vt

structure CheckRootPost (c : Cfg) (base : Addr) (P : Prop) [Decidable P] (s s' : State) : Prop where
  scr : Scr s' base size
  keep : Keeps clob s s'
  unch : Unch base (slWk c [QYM, W1, W3, TMP, FLAG]) s.mem s'.mem
  flag : flagW c base s' = mask32
    ((P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) ∧
      sv c base s QY % 2 = (s.mem.readW (off base (c.sl D)) 32).toNat % 2)

theorem checkRoot_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) {P : Prop} [Decidable P]
    (hf : flagW c base s = mask32 P) :
    WP isa (Impl.EcKey.Compressed.X86.checkRoot c) s (CheckRootPost c base P s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  obtain hW := sl_le c h7 (i := W3) (by decide)
  obtain hY := sl_le c h7 (i := QY) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  change WP isa (.seq
    (Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.checkRootOps c))
    (.block (Impl.EcKey.Compressed.X86.checkRootChecks c))) s _
  refine WP.seq (WP.mono (checkPoly_ok hc hs hM hy hr hr2) fun s₁ I => ?_)
  obtain flag₁ : flagW c base s₁ = mask32 P := by
    rw [flagW, Unch.readW32 I.unch (fun w hw => by have := (apart_slWk (c := c) (l := [QYM, W1, W3, TMP]) (i := FLAG) (by decide) (by decide) h7) w hw; omega_using [h0, this]) (by omega_using [hn, hF]), ← flagW, hf]
  obtain hz : sv c base s₁ W3 = 0 ↔
      Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) := by
    rw [← toM_eq_zero_iff (unitMod_pow_two hc.p_odd (64 * c.n)) I.lt, I.val]
    constructor <;> intro h <;> grind
  rw [Impl.EcKey.Compressed.X86.checkRootChecks, WP.block_append_iff]
  refine WP.mono (checkZero_ok c I.scr h0 hW (by omega_using [h0, hF])) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  obtain hs₂ := I.scr.of_keeps k₂ (by decide)
  obtain flag₂ : flagW c base s₂ = mask32
      (P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) := by
    rw [f₂, flag₁, show wordsVal s₁.mem base (c.sl W3) c.n = sv c base s₁ W3 from rfl, mask32_and]
    simp only [mask32, hz]
  obtain y₂ : sv c base s₂ QY = sv c base s QY := by
    rw [sv, sv_flag O₂ h0 h7 hn (by decide) (by decide)]
    exact sv_unch I.unch h7 hn (by decide) (apart_slWk (by decide) (by decide))
  obtain tag₂ : s₂.mem.readW (off base (c.sl D)) 32 = s.mem.readW (off base (c.sl D)) 32 := by
    rw [BitVec.eq_of_toNat_eq (O₂.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [hn, hD]))]
    exact Unch.readW32 I.unch (fun w hw => by
      have := (apart_slWk (c := c) (l := [QYM, W1, W3, TMP]) (i := D) (by decide) (by decide) h7) w hw
      omega_using [h0, this]) (by omega_using [hn, hD])
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega_using [h0, hY]) (by omega_using [h0, hD])) fun s₃ ⟨mask₃, k₃, m₃⟩ => ?_
  rw [y₂, tag₂] at mask₃
  rw [WP.block_append_iff]
  refine WP.mono (invertMask_ok s₃ _ mask₃) fun s₄ ⟨mask₄, k₄, m₄⟩ => ?_
  obtain hs₄ := (hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  refine WP.mono (andFlag_ok c hs₄ (by omega_using [h0, hF])) fun s₅ ⟨flag₅, k₅, O₅⟩ => ?_
  refine ⟨hs₄.of_keeps k₅ (by decide), ?_, ?_, ?_⟩
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

end VG.Proof.EcKey.Compressed.X86

end

end

/-! # Coordinate recovery and final checks preserve the parsed encoding -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86/Select.lean`, which only this module imported.
section

/-! # Leave Montgomery form and choose between the two canonical roots -/

section

namespace VG.Proof.EcKey.Compressed.X86


open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Impl.Ecdh.X86 (QY W0)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

structure SelectPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkW c.MP' size c.C.p s'.mem base
  keep : Keeps clob s s'
  unch : Unch base (slWk c [QY, W0, TMP]) s.mem s'.mem
  lt : sv c base s' QY < c.C.p
  val : Fin.ofNat c.C.p (sv c base s' QY) =
    let y := toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
    if y.val % 2 = (s.mem.readW (off base (c.sl D)) 32).toNat % 2 then y else -y

theorem selectRoot_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONE = 1) (hZero : sv c base s ZERO = 0) :
    WP isa (Impl.EcKey.Compressed.X86.selectRoot c) s (SelectPost c base s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  obtain hY := sl_le c h7 (i := QY) (by decide)
  obtain hZ := sl_le c h7 (i := ZERO) (by decide)
  obtain hW := sl_le c h7 (i := W0) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  obtain hMP := sl_le c h7 (i := MP) (by decide)
  change WP isa (.seq (Mont.mulCall c.SP (c.sl QY) (c.sl ACC) (c.sl ONE))
    (.seq (Mont.subCall c.SP (c.sl W0) (c.sl ZERO) (c.sl QY))
      (.block (Impl.EcKey.Compressed.X86.parityMask c ++ sel (2 * c.n) (c.sl QY) (c.sl QY) (c.sl W0))))) s _
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) hc.fp h7 hs (o := QY) (a := ACC) (b := ONE)
    (by decide) (by decide) (by decide) (by rw [hOne]; omega))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain hM₁ := hM.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain normal : Fin.ofNat c.C.p (sv c base s₁ QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) :=
    toM_one_mul (unitMod_pow_two hc.p_odd (64 * c.n)) (by simpa only [hOne] using e₁)
  obtain normalVal : sv c base s₁ QY =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₁] using congrArg Fin.val normal
  obtain zero₁ : sv c base s₁ ZERO = 0 :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hZero
  refine WP.seq (WP.mono (slSub_ok hc hs₁
    (o := W0) (a := ZERO) (b := QY) (by decide) (by decide) (by decide)
    (by rw [zero₁]; omega) lt₁) fun s₂ ⟨k₂, e₂⟩ => ?_)
  change sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p at e₂
  obtain hs₂ := k₂.scr hs₁
  obtain hM₂ := hM₁.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain y₂ : sv c base s₂ QY = sv c base s₁ QY :=
    sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  obtain negLt : sv c base s₂ W0 < c.C.p := by
    rw [e₂]
    exact Nat.mod_lt _ (by omega)
  obtain negVal : Fin.ofNat c.C.p (sv c base s₂ W0) = -(Fin.ofNat c.C.p (sv c base s₁ QY)) := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.neg_def]
    rw [show sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p from e₂,
      zero₁, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt lt₁]
  obtain U₁₂ : Unch base (slWk c [QY, W0, TMP]) s.mem s₂.mem :=
    unch_same (unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp))
      (unch_slots (MP'_n c) rfl k₂.unch (by simp) (by simp))
  obtain tag₂ : s₂.mem.readW (off base (c.sl D)) 32 = s.mem.readW (off base (c.sl D)) 32 :=
    VG.Proof.Ecdsa.X86.Unch.readW32 U₁₂ (fun w hw => by
      have := (apart_slWk (c := c) (l := [QY, W0, TMP]) (i := D) (by decide) (by decide) h7) w hw
      omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega) (by omega)) fun s₃ ⟨mask₃, k₃, m₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (sel_ok (decide (sv c base s₂ QY % 2 ≠ (s₂.mem.readW (off base (c.sl D)) 32).toNat % 2)) (2 * c.n) hs₃
    (by simpa only [mask32, decide_eq_true_eq] using mask₃)
    (by omega) (by omega) (by omega) (Or.inl (Nat.le_refl _))
    (by have := sl_apart c (i := QY) (j := W0) (by decide); omega)) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [show 4 * (2 * c.n) = 8 * c.n by omega] at O₄
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  obtain hM₄ : ModOkW c.MP' size c.C.p s₄.mem base := modP_of hc (by
    rw [O₄.wordsVal (d := c.sl MP) (k := c.n)
      (sl_apart c (i := MP) (j := QY) (by decide)) (by omega), m₃]
    exact hM₂.val)
  obtain e₄' : sv c base s₄ QY =
      if sv c base s₂ QY % 2 ≠ (s₂.mem.readW (off base (c.sl D)) 32).toNat % 2 then
        sv c base s₂ W0 else sv c base s₂ QY := by
    simpa only [sv, wordsVal_eq_val32, m₃, decide_eq_true_eq] using e₄
  refine ⟨hs₄, hM₄, ?_, ?_, ?_, ?_⟩
  · exact (k₁.keeps.trans k₂.keeps).trans ((k₃.mono (by decide)).trans (k₄.mono (by decide)))
  · apply unch_same U₁₂
    rw [← m₃]
    exact (slot_frame (slots := [QY, W0, TMP]) (by simp) (by omega) O₄).mono
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

end VG.Proof.EcKey.Compressed.X86
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86
open VG.Impl.Ecdh.X86 (QY QYM R2P W0 W1 W2 W3)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.Impl.EcKey.Compressed (chooseRoot)

def keyRhs (c : Cfg) (s : State) : Spec.Weierstrass.Fe c.C :=
  let x := Fin.ofNat c.C.p (keyX c s)
  x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

def keyRoot (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :=
  chooseRoot (root (keyRhs c s)) ((s.mem (ptr s 1)).toNat % 2)

def CompressedAccept (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s : State) : Prop := CompressedPrefix c s ∧
  (keyRoot c root s * keyRoot c root s = keyRhs c s ∧
    (keyRoot c root s).val % 2 = (s.mem (ptr s 1)).toNat % 2)

instance (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :
    Decidable (CompressedAccept c root s) := inferInstanceAs (Decidable (_ ∧ (_ ∧ _)))

structure DecompressChecked (c : Cfg)
    (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s₀ : State) (s : State) : Prop where
  scr : Scr s (ptr s₀ 2) size
  saved : ∀ rd ∈ Cfg.saved, s.mem.readW (off (ptr s₀ 2) rd.2) 32 = s₀.gpr rd.1
  x : sv c (ptr s₀ 2) s E = keyX c s₀
  y : sv c (ptr s₀ 2) s QY = (keyRoot c root s₀).val
  flag : flagW c (ptr s₀ 2) s = mask32 (CompressedAccept c root s₀)
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressMiddle_ok {c : Cfg} (hc : CfgOk c)
    {root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C} (hroot : CandidateCorrect c root)
    {s₀ s : State} (F : DecompressFront c s₀ s) :
    WP isa (.seq (Impl.EcKey.Compressed.X86.rootCandidate c)
      (.seq (Impl.EcKey.Compressed.X86.selectRoot c)
        (Impl.EcKey.Compressed.X86.checkRoot c))) s (DecompressChecked c root s₀) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := F.scr.nowrap
  refine WP.seq (WP.mono (hroot _ s F.scr (modP_of hc F.fixed.mp) F.rhs_lt F.fixed.onep)
    fun s₁ C => ?_)
  obtain F₁ := F.frame hc C.keep C.unch (candidate_fixed hc) (by
    intro i hi
    obtain h : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 ∧ i ∉ candidateSlots := by decide
    exact candidate_apart hc (h i hi).1 (h i hi).2)
  obtain root₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ 2) s₁ ACC) = root (keyRhs c s₀) := by
    rw [C.val, F.rhs]; rfl
  refine WP.seq (WP.mono (selectRoot_ok hc F₁.scr (modP_of hc F₁.fixed.mp)
    F₁.fixed.one F₁.fixed.zero) fun s₂ S => ?_)
  obtain F₂ := F₁.frame hc (S.keep.mono (by decide)) S.unch
    (fixedOk_slWk (l := [QY, W0, TMP]) (by decide)) (by
      intro i hi
      obtain h : ∀ i ∈ [E, D, R2P, W2, FLAG], i ∉ [QY, W0, TMP] := by decide
      exact apart_slWk (by
        obtain H : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 := by decide
        exact H i hi) (h i hi))
  obtain y₂ : Fin.ofNat c.C.p (sv c (ptr s₀ 2) s₂ QY) = keyRoot c root s₀ := by
    rw [S.val, root₁, F₁.tag]
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
      (s₀.mem (ptr s₀ 1)).toNat < 2 ^ 32 from Nat.lt_trans (BitVec.isLt _) (by decide))]
    rfl
  obtain yval₂ : sv c (ptr s₀ 2) s₂ QY = (keyRoot c root s₀).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt S.lt] using congrArg Fin.val y₂
  refine WP.mono (checkRoot_ok hc F₂.scr (modP_of hc F₂.fixed.mp) S.lt
    F₂.rhs_lt F₂.r2 F₂.flag) fun s₃ K => ?_
  obtain F₃ := F₂.fixed.unch h7 hn
    (fixedOk_slWk (l := [QYM, W1, W3, TMP, FLAG]) (by decide)) K.unch
  have e₃ {i : Nat} (hi : i < 45) (hw : i ∉ [QYM, W1, W3, TMP, FLAG]) :
      sv c (ptr s₀ 2) s₃ i = sv c (ptr s₀ 2) s₂ i :=
    sv_unch K.unch h7 hn hi (apart_slWk hi hw)
  refine ⟨K.scr, F₃.saved,
    (e₃ (by decide) (by decide)).trans F₂.x,
    (e₃ (by decide) (by decide)).trans yval₂, ?_, (K.keep.1 _ (by decide)).trans F₂.esp,
    K.keep.2.1.trans F₂.rd, K.keep.2.2.trans F₂.wr⟩
  rw [K.flag, y₂, yval₂, F₂.rhs, F₂.tag]
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
    (s₀.mem (ptr s₀ 1)).toNat < 2 ^ 32 from Nat.lt_trans (BitVec.isLt _) (by decide))]
  simp only [mask32, CompressedAccept, keyRhs, and_assoc]

end VG.Proof.EcKey.Compressed.X86

end

end

/-! # Decompression meets the merged API contract -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86/DecompressFinish.lean`, which only this module imported.
section

section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 Spec.Weierstrass
open VG.Proof.EcKey.X86 (pointFinish_ok)
variable {c : Cfg}

theorem decompressFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {o32 : BitVec 32}
    (hout : readSrc s (.mem (Cfg.argOp 0)) = some o32) (hofit : o32.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 32)
    (hw : (⟨o32.setWidth 64, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨o32.setWidth 64, 1 + 2 * c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.EcKey.Compressed.X86.decompressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (o32.setWidth 64) (1 + 2 * c.C.len) =
        (if b then 4 :: (toBytes c.C.len (sv c base s E) ++ toBytes c.C.len (sv c base s Impl.Ecdh.X86.QY))
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      s'.gpr .eax = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] → s'.gpr r = s.gpr r) ∧
      Outside (o32.setWidth 64) 0 (1 + 2 * c.C.len) s.mem s'.mem :=
  pointFinish_ok hc (by decide) (by decide) hs hout hofit hw hd hsv b hf

end VG.Proof.EcKey.Compressed.X86
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG.Proof.Ecdh.X86
open VG VG.X86 VG.Impl.Ecdsa.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 Spec.Weierstrass

theorem decompress_key (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) :
    Impl.EcKey.Compressed.decode c.C root
      (Spec.EcKey.bytesAt s.mem (ptr s 1) (c.C.len + 1)) =
    if CompressedAccept c root s then
      some (.affine (Fin.ofNat c.C.p (keyX c s)) (keyRoot c root s)) else none := by
  have hb : Spec.Ecdsa.bytesAt s.mem (ptr s 1) (c.C.len + 1) =
      s.mem (ptr s 1) :: Spec.Ecdsa.bytesAt s.mem (ptr s 1 + 1) c.C.len := by
    rw [Nat.add_comm c.C.len 1, bytesAt_add]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
      List.cons_append, List.nil_append]
    rfl
  apply decode_checked_eq root (length_bytesAt _ _ _)
    (by change (Spec.Ecdsa.bytesAt _ _ _).head? = _; rw [hb]; rfl)
    (by change ofBytes ((Spec.Ecdsa.bytesAt _ _ _).drop 1) = _; rw [hb]; rfl)

def decompressBody (c : Cfg) : Prog isa :=
  .seq (.block (c.setupWith Impl.EcKey.Compressed.X86.args))
    (.seq (.block (Impl.EcKey.Compressed.X86.decompressPeer c))
      (.seq (Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.rhsOps c))
        (Impl.EcKey.Compressed.X86.recoverCoordinate c)))

theorem decompressBody_ok {c : Cfg} (hc : CfgOk c)
    {root : Fe c.C → Fe c.C} (hroot : CandidateCorrect c root) {s : State}
    (hp : InputPre c (1 + c.C.len) s) :
    WP isa (decompressBody c) s (DecompressChecked c root s) :=
  decompressFront_ok hc hp (fun _ F => decompressMiddle_ok hc hroot F)

theorem decompress_correct (c : Cfg) (hc : CfgOk c)
    (root : Fe c.C → Fe c.C) (hroot : CandidateCorrect c root)
    (hsp : SpOk (Impl.EcKey.Compressed.X86.decompress c) 28)
    (s : State) (hs : (decompressContract c.C root).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.X86.decompress c) s t s' ∧
      abiPreserved s s' ∧ (decompressContract c.C root).post s s' := by
  have hp := codec_input (c := c) hs
  obtain ⟨hrd, hwr, how, hpo, hpw, hao, haw, hro, hrw, hfit, hpk, hws, hsf, hlo, hso, hsw⟩ := hs
  simp only [Bool.false_eq_true, ite_false] at hrd hwr
  have hbody : SpOk (decompressBody c) 28 :=
    hsp.left.seq (hsp.right.left.seq (hsp.right.right.left.seq hsp.right.right.right.left))
  have hrun : WP isa (Impl.EcKey.Compressed.X86.decompress c) s fun u =>
      (decompressContract c.C root).post s u ∧
      (∀ rd ∈ Cfg.saved, u.gpr rd.1 = s.gpr rd.1) ∧ u.gpr .esp = s.gpr .esp := by
    change WP isa ([.block (c.setupWith Impl.EcKey.Compressed.X86.args),
      .block (Impl.EcKey.Compressed.X86.decompressPeer c),
      Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.rhsOps c)].foldr .seq
      (.seq (Impl.EcKey.Compressed.X86.recoverCoordinate c)
        (.block (Impl.EcKey.Compressed.X86.decompressFinish c)))) s _
    rw [WP.split]
    refine WP.seq (WP.mono (WP.spFrame hbody hlo (decompressBody_ok hc hroot
      (by simpa only [Nat.add_comm] using hp))) fun t ⟨F, W⟩ => ?_)
    have hin : InRegions (s.rd ++ s.wr) (argAddr s 0) 4 :=
      ⟨_, by rw [hrd, hwr]; simp, arg_containsN (k := 3) (by omega_using [hsf]) (by decide)⟩
    have hdarg : ∀ r ∈ s.wr ++ [below (s.gpr .esp) 28], Region.Disjoint ⟨argAddr s 0, 4⟩ r := by
      intro r hr
      rw [hwr] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hao.sub_left (arg_subN (k := 3) (by omega_using [hsf]) (by decide))
      · exact haw.sub_left (arg_subN (k := 3) (by omega_using [hsf]) (by decide))
      · exact (below_disjoint_args hlo (by omega_using [hsf]) (by decide)).symm
    have hout := argLoad_frame hin hdarg F.esp (by rw [F.rd, F.wr]) W
    refine WP.mono (decompressFinish_ok hc F.scr hout (by omega_using [hfit])
      (by rw [F.wr, hwr]; simp [Nat.add_comm]) (by simpa only [Nat.add_comm] using how)
      F.saved (decide (CompressedAccept c root s)) (by simp only [F.flag, decide_eq_true_eq]))
      fun u ⟨bytes, ret, saved, esp, _⟩ => ?_
    refine ⟨?_, saved, (esp _ (by decide)).trans F.esp⟩
    dsimp only [decompressContract]
    rw [decompress_key, BitVec.setWidth_append_eq_right]
    rw [F.x, F.y] at bytes
    change Spec.EcKey.bytesAt u.mem ((arg s 0).setWidth 64) (1 + 2 * c.C.len) = _ at bytes
    simp only [decide_eq_true_eq] at ret bytes
    by_cases hk : CompressedAccept c root s
    · rw [ite_eq_left hk] at ret bytes ⊢
      refine ⟨ret, ?_⟩
      change Spec.EcKey.bytesAt u.mem (ptr s 0) (2 * c.C.len + 1) =
        4 :: (toBytes c.C.len (Fin.ofNat c.C.p (keyX c s)).val ++ toBytes c.C.len (keyRoot c root s).val)
      simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt hk.1.2, Nat.add_comm] using bytes
    · rw [ite_eq_right hk] at ret bytes ⊢
      exact ⟨ret, by simpa only [Nat.add_comm] using bytes⟩
  obtain ⟨t, u, he, ⟨hpost, saved, esp⟩, W⟩ := WP.spFrame hsp hlo hrun
  refine ⟨t, u, he, ⟨?_, ?_⟩, hpost⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact saved (.ebx, 0) (by decide)
    · exact saved (.esi, 4) (by decide)
    · exact saved (.edi, 8) (by decide)
    · exact saved (.ebp, 12) (by decide)
    · exact esp
  · refine W.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rw [hwr] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hro
    · exact hrw
    · exact (below_disjoint_ret hlo).symm

end VG.Proof.EcKey.Compressed.X86

end

end

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86

theorem decompress_verified {c : Cfg} (hc : CfgOk c) (I : Spec.EcKey.Instance) (hC : c.C = I.curve)
    (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (hroot : CandidateCorrect c root)
    (facts : RootFacts (hC ▸ root))
    (hsp : SpOk (Impl.EcKey.Compressed.X86.decompress c) 28)
    (hct : ConstantTime isa (decompressContract c.C root).pre (decompressContract c.C root).pub
      (Impl.EcKey.Compressed.X86.decompress c))
    (hsig : ∃ s, (I.decompressPublicKeyContract abi 28).pre s) :
    Verified target (Impl.EcKey.Compressed.X86.decompress c) (I.decompressPublicKeyContract abi 28) := by
  have heq : decompressContract c.C root = decompressContract I.curve (hC ▸ root) := by
    rcases I with ⟨C, name, title⟩
    cases hC
    rfl
  have himp := decompress_implies I (hC ▸ root) facts hsig
  have hsat := himp.sat_left
  have localSat : ∃ s, (decompressContract c.C root).pre s := by
    obtain ⟨s, hs⟩ := hsat
    refine ⟨s.withRegions (codecRd (I.curve.len + 1) s) (codecWr (2 * I.curve.len + 1) s), ?_⟩
    rw [heq]
    exact codecWide_pre hs
  have localVerified : Verified target (Impl.EcKey.Compressed.X86.decompress c) (decompressContract I.curve (hC ▸ root)) := by
    rw [← heq]
    exact Verified.of_correct (decompress_correct c hc root hroot hsp) hct (.refl localSat)
  apply Verified.of_implies (Verified.narrowTo localVerified
    (codecRd (I.curve.len + 1)) (codecWr (2 * I.curve.len + 1))
    (fun _ h => codecWide_pre h) ?_ ?_ ?_ ?_ hsat) himp
  · intro s h a n ⟨r, hr, hcontains⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hcontains⟩
    simp only [codecRd, codecWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · intro s h a n ⟨r, hr, hcontains⟩
    rw [h.2.1]
    refine ⟨r, ?_, hcontains⟩
    simp only [codecWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [decompressContract, arg_withRegions, State.withRegions_mem, State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [decompressContract, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.EcKey.Compressed.X86
