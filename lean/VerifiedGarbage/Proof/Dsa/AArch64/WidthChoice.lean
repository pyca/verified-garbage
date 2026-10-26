module
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.AArch64.WidthMask
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract

/-! # Public selection of supported DSA modulus widths -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem sub_beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == (0#64)) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
  constructor
  · intro h
    have hv := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv
  · intro h; rw [h]

theorem widthCompare_ok {s : State} {value n : Nat}
    (hv : value < 2 ^ 64) (hn : n < 4096) (hd : s.gpr .x2 = BitVec.ofNat 64 value) :
    WP isa (.block [.subImm .x .x6 .x2 n]) s fun t =>
      (t.gpr .x6 == (0#64)) = decide (value = n) ∧ t.gpr .x2 = BitVec.ofNat 64 value ∧ t.mem = s.mem ∧ Keep [.x2, .x6] s t := by
  refine WP.mono (WP.keep [.x2, .x6] (Q := fun t =>
    (t.gpr .x6 == (0#64)) = decide (value = n) ∧ t.gpr .x2 = BitVec.ofNat 64 value ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hz, ht, hm⟩, hk⟩ => ⟨hz, ht, hm, hk⟩
  brun [hd, hn]
  exact sub_beq_ofNat hv (by omega)

/-- Recover the saved p width and prepare the first public branch. -/
theorem readWidth_ok {s : State} {B : Addr} {Z p : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .x0 = B) (hZ : 184 ≤ Z) (hp : p < 2 ^ 64)
    (hw : word s.mem B 176 = BitVec.ofNat 64 p) :
    WP isa (.block [ldh .x2 22, .subImm .x .x6 .x2 128]) s fun t =>
      (t.gpr .x6 == (0#64)) = decide (p = 128) ∧ t.gpr .x2 = BitVec.ofNat 64 p ∧ t.mem = s.mem ∧ Keep [.x2, .x6] s t := by
  refine WP.mono (WP.keep [.x2, .x6] (Q := fun t =>
    (t.gpr .x6 == (0#64)) = decide (p = 128) ∧ t.gpr .x2 = BitVec.ofNat 64 p ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hz, ht, hm⟩, hk⟩ => ⟨hz, ht, hm, hk⟩
  brun [hdi, hdr_enc (show 22 < 32 by decide), hw, hs.ld hZ]
  exact sub_beq_ofNat hp (by decide)

theorem mask_union (a b : Bool) : mask a ||| mask b = mask (a || b) := by
  cases a <;> cases b <;> decide

/-- The 2048-bit modulus supports both 224- and 256-bit subgroups. -/
theorem widthEither_ok {s : State} {q : Nat} (hq : q < 2 ^ 64)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 q) :
    WP isa (.block (Checks.widthMask 28 ++ ([mov .x11 .x3] : List Instr) ++ Checks.widthMask 32 ++
      ([.logic .orr .x .x3 .x3 .x11] : List Instr))) s fun t =>
      t.gpr .x3 = mask (decide (q = 28 ∨ q = 32)) ∧ t.mem = s.mem ∧ Keep [.x3, .x4, .x11] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (widthMask_ok (by decide) hq h8) fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x11] (Q := fun v => v.gpr .x11 = mask (decide (q = 28)) ∧ v.mem = u.mem)
    (by brun [hua]) rfl rfl rfl) fun v ⟨⟨hv10, hvm⟩, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hv8 := ((hku.trans hkv).gpr .x8 (show Reg.x8 ∉ _ by decide)).trans h8
  refine WP.mono (widthMask_ok (by decide) hq hv8) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hz10 := (hkz.gpr .x11 (show Reg.x11 ∉ [Reg.x3, Reg.x4] by decide)).trans hv10
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.gpr .x3 = mask (decide (q = 28 ∨ q = 32)) ∧ t.mem = z.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨ht, htm⟩, hkt⟩ =>
      ⟨ht, htm.trans (hzm.trans (hvm.trans hum)), (((hku.trans hkv).trans hkz).trans hkt).mono (by decide)⟩
  brun [hza, hz10, mask_union]
  rw [← Bool.decide_or]
  exact congrArg mask (decide_eq_decide.mpr or_comm)

/-- The legacy 160-bit subgroup extends the two FIPS 2048-bit cases. -/
theorem width2048_ok {s : State} {q : Nat} (hq : q < 2 ^ 64)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 q) :
    WP isa (.block Checks.width2048) s fun t =>
      t.gpr .x3 = mask (decide (q = 20 ∨ q = 28 ∨ q = 32)) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4, .x11] s t := by
  unfold Checks.width2048
  rw [show Checks.widthMask 28 ++ ([mov .x11 .x3] : List Instr) ++ Checks.widthMask 32 ++
      ([.logic .orr .x .x3 .x3 .x11] : List Instr) ++ ([mov .x11 .x3] : List Instr) ++ Checks.widthMask 20 ++
      ([.logic .orr .x .x3 .x3 .x11] : List Instr) =
      (Checks.widthMask 28 ++ ([mov .x11 .x3] : List Instr) ++ Checks.widthMask 32 ++
        ([.logic .orr .x .x3 .x3 .x11] : List Instr)) ++
      (([mov .x11 .x3] : List Instr) ++ Checks.widthMask 20 ++ ([.logic .orr .x .x3 .x3 .x11] : List Instr)) by
        simp only [List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (widthEither_ok hq h8) fun u ⟨hua, hum, hku⟩ => ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.x11] (Q := fun v =>
    v.gpr .x11 = mask (decide (q = 28 ∨ q = 32)) ∧ v.mem = u.mem)
    (by brun [hua]) rfl rfl rfl) fun v ⟨⟨hvs, hvm⟩, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hv8 := ((hku.trans hkv).gpr .x8 (show Reg.x8 ∉ _ by decide)).trans h8
  refine WP.mono (widthMask_ok (by decide) hq hv8) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hzs := (hkz.gpr .x11 (show Reg.x11 ∉ [Reg.x3, Reg.x4] by decide)).trans hvs
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.gpr .x3 = mask (decide (q = 20 ∨ q = 28 ∨ q = 32)) ∧ t.mem = z.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨ht, htm⟩, hkt⟩ =>
      ⟨ht, htm.trans (hzm.trans (hvm.trans hum)),
        (((hku.trans hkv).trans hkz).trans hkt).mono (by decide)⟩
  brun [hza, hzs, mask_union, ← Bool.decide_or]

abbrev widthChoice : Prog isa :=
  .ite (.zero .x .x6) (.block (Checks.widthMask 20))
    (.seq (.block [.subImm .x .x6 .x2 256])
      (.ite (.zero .x .x6)
        (.block Checks.width2048)
        (.seq (.block [.subImm .x .x6 .x2 384])
          (.ite (.zero .x .x6) (.block (Checks.widthMask 32)) (.block [movi .x3 0])))))

/-- The supported-width switch returns exactly the spec's (L,N) predicate. -/
theorem widthChoice_ok {s : State} {p q : Nat} (hp : p < 2 ^ 64) (hq : q < 2 ^ 64)
    (hd : s.gpr .x2 = BitVec.ofNat 64 p) (h8 : s.gpr .x8 = BitVec.ofNat 64 q)
    (hz : (s.gpr .x6 == (0#64)) = decide (p = 128)) :
    WP isa widthChoice s fun t =>
      t.gpr .x3 = mask (decide (Spec.Dsa.supportedSizes (8 * p) (8 * q))) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4, .x2, .x6, .x11] s t := by
  unfold widthChoice
  by_cases h128 : p = 128
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
    · change some (s.gpr .x6 == (0#64)) = some true
      simp only [hz, h128, decide_true]
    · have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 20 := by
        unfold Spec.Dsa.supportedSizes; omega
      rw [decide_eq_decide.mpr he]
      exact WP.mono (widthMask_ok (by decide) hq h8) fun t ⟨ht, hm, hk⟩ => ⟨ht, hm, hk.mono (by decide)⟩
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change some (s.gpr .x6 == (0#64)) = some false
      simp only [hz, h128, decide_false]
    · refine WP.seq (WP.mono (widthCompare_ok hp (show 256 < 4096 by decide) hd)
        fun u ⟨huz, hud, hum, hku⟩ => ?_)
      have hu8 := (hku.gpr .x8 (show Reg.x8 ∉ [Reg.x2, Reg.x6] by decide)).trans h8
      by_cases h256 : p = 256
      · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
        · change some (u.gpr .x6 == (0#64)) = some true
          simp only [huz, h256, decide_true]
        · have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 20 ∨ q = 28 ∨ q = 32 := by
            unfold Spec.Dsa.supportedSizes; omega
          rw [decide_eq_decide.mpr he]
          exact WP.mono (width2048_ok hq hu8) fun t ⟨ht, hm, hk⟩ =>
            ⟨ht, hm.trans hum, (hku.trans hk).mono (by decide)⟩
      · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
        · change some (u.gpr .x6 == (0#64)) = some false
          simp only [huz, h256, decide_false]
        · refine WP.seq (WP.mono (widthCompare_ok hp (show 384 < 4096 by decide) hud)
            fun v ⟨hvz, _, hvm, hkv⟩ => ?_)
          have hv8 := (hkv.gpr .x8 (show Reg.x8 ∉ [Reg.x2, Reg.x6] by decide)).trans hu8
          by_cases h384 : p = 384
          · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
            · change some (v.gpr .x6 == (0#64)) = some true
              simp only [hvz, h384, decide_true]
            · have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 32 := by
                unfold Spec.Dsa.supportedSizes; omega
              rw [decide_eq_decide.mpr he]
              exact WP.mono (widthMask_ok (by decide) hq hv8) fun t ⟨ht, hm, hk⟩ =>
                ⟨ht, hm.trans (hvm.trans hum), ((hku.trans hkv).trans hk).mono (by decide)⟩
          · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
            · change some (v.gpr .x6 == (0#64)) = some false
              simp only [hvz, h384, decide_false]
            · have he : ¬ Spec.Dsa.supportedSizes (8 * p) (8 * q) := by
                unfold Spec.Dsa.supportedSizes; omega
              rw [decide_eq_false he]
              refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = mask false ∧ t.mem = v.mem)
                (by brun) rfl rfl rfl) fun t ⟨⟨ht, hm⟩, hk⟩ =>
                  ⟨ht, hm.trans (hvm.trans hum), ((hku.trans hkv).trans hk).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
