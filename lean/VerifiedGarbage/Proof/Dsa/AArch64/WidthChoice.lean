module

public import VerifiedGarbage.Proof.Dsa.AArch64.WidthMask
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Public selection of supported DSA modulus widths -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem widthCompare_ok {s : State} {value n : Nat}
    (hv : value < 2 ^ 64) (hn : n < 4096) (hd : s.gpr .x10 = BitVec.ofNat 64 value) :
    WP isa (.block [.subImm .x .x5 .x10 n]) s fun t =>
      isa.eval (.zero .x .x5) t = some (decide (value = n)) ∧ t.gpr .x10 = BitVec.ofNat 64 value ∧
        t.mem = s.mem ∧ Keep [.x5] s t := by
  refine WP.mono (WP.keep [.x5] (Q := fun t =>
    t.gpr .x5 = BitVec.ofNat 64 value - BitVec.ofNat 64 n ∧ t.gpr .x10 = BitVec.ofNat 64 value ∧
      t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨h5, ht, hm⟩, hk⟩ => ⟨?_, ht, hm, hk⟩
  · brun [hd, hn]
  · rw [eval_zero, h5, VG.Offset.ofNat_sub_ofNat_beq hv (by omega)]

/-- Recover the saved p width for the public branches. -/
theorem readWidth_ok {s : State} {B : Addr} {Z p : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .x0 = B) (hZ : 184 ≤ Z)
    (hw : word s.mem B 176 = BitVec.ofNat 64 p) :
    WP isa (.block [ldh .x10 22]) s fun t =>
      t.gpr .x10 = BitVec.ofNat 64 p ∧ t.mem = s.mem ∧ Keep [.x10] s t := by
  refine WP.mono (WP.keep [.x10] (Q := fun t =>
    t.gpr .x10 = BitVec.ofNat 64 p ∧ t.mem = s.mem) ?_ (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  have hw' : s.mem.readW (off B (8 * 22)) 64 = BitVec.ofNat 64 p := hw
  brun [hdi, hdr_enc (show 22 < 32 by decide), hs.ld (show 8 * 22 + 8 ≤ Z by omega), hw']

theorem mask_union (a b : Bool) : mask a ||| mask b = mask (a || b) := by
  cases a <;> cases b <;> decide

/-- The 2048-bit modulus supports both 224- and 256-bit subgroups. -/
theorem widthEither_ok {s : State} {q : Nat} (hq : q < 2 ^ 64)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 q) :
    WP isa (.block (Checks.widthMask 28 ++ ([mov .x11 .x15] : List Instr) ++ Checks.widthMask 32 ++
      ([.logic .orr .x .x15 .x15 .x11] : List Instr))) s fun t =>
      t.gpr .x15 = mask (decide (q = 28 ∨ q = 32)) ∧ t.mem = s.mem ∧
        Keep [.x3, .x4, .x7, .x11, .x15] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (widthMask_ok (by decide) hq h8) fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x11] (Q := fun v => v.gpr .x11 = mask (decide (q = 28)) ∧ v.mem = u.mem)
    (by brun [hua]) (by decide) (by decide) (by decide +kernel)) fun v ⟨⟨hv11, hvm⟩, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hv8 := ((hku.trans hkv).gpr .x8 (by decide)).trans h8
  refine WP.mono (widthMask_ok (by decide) hq hv8) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hz11 := (hkz.gpr .x11 (by decide)).trans hv11
  refine WP.mono (WP.keep [.x15] (Q := fun t =>
    t.gpr .x15 = mask (decide (q = 28 ∨ q = 32)) ∧ t.mem = z.mem) ?_ (by decide) (by decide)
      (by decide +kernel))
    fun t ⟨⟨ht, htm⟩, hkt⟩ =>
      ⟨ht, htm.trans (hzm.trans (hvm.trans hum)), (((hku.trans hkv).trans hkz).trans hkt).mono (by decide)⟩
  brun [hza, hz11, mask_union]
  rw [← Bool.decide_or]
  exact congrArg mask (decide_eq_decide.mpr or_comm)

/-- The supported-width switch returns exactly the spec's (L,N) predicate. -/
theorem widthChoice_ok {s : State} {p q : Nat} (hp : p < 2 ^ 64) (hq : q < 2 ^ 64)
    (hd : s.gpr .x10 = BitVec.ofNat 64 p) (h8 : s.gpr .x8 = BitVec.ofNat 64 q) :
    WP isa Checks.widthChoice s fun t =>
      t.gpr .x15 = mask (decide (Spec.Dsa.supportedSizes (8 * p) (8 * q))) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4, .x5, .x7, .x11, .x15] s t := by
  unfold Checks.widthChoice
  refine WP.seq (WP.mono (widthCompare_ok hp (show 128 < 4096 by decide) hd)
    fun u ⟨huz, hud, hum, hku⟩ => ?_)
  have hu8 := (hku.gpr .x8 (by decide)).trans h8
  by_cases h128 : p = 128
  · refine WP.ite true (by rw [huz, h128]; rfl) (fun _ => ?_) (fun h => Bool.noConfusion h)
    have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 20 := by
      unfold Spec.Dsa.supportedSizes; omega
    rw [decide_eq_decide.mpr he]
    exact WP.mono (widthMask_ok (by decide) hq hu8) fun t ⟨ht, hm, hk⟩ =>
      ⟨ht, hm.trans hum, (hku.trans hk).mono (by decide)⟩
  refine WP.ite false (by rw [huz, decide_eq_false h128]) (fun h => Bool.noConfusion h) (fun _ => ?_)
  refine WP.seq (WP.mono (widthCompare_ok hp (show 256 < 4096 by decide) hud)
    fun v ⟨hvz, hvd, hvm, hkv⟩ => ?_)
  have hv8 := (hkv.gpr .x8 (by decide)).trans hu8
  by_cases h256 : p = 256
  · refine WP.ite true (by rw [hvz, h256]; rfl) (fun _ => ?_) (fun h => Bool.noConfusion h)
    have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 28 ∨ q = 32 := by
      unfold Spec.Dsa.supportedSizes; omega
    rw [decide_eq_decide.mpr he]
    exact WP.mono (widthEither_ok hq hv8) fun t ⟨ht, hm, hk⟩ =>
      ⟨ht, hm.trans (hvm.trans hum), ((hku.trans hkv).trans hk).mono (by decide)⟩
  refine WP.ite false (by rw [hvz, decide_eq_false h256]) (fun h => Bool.noConfusion h) (fun _ => ?_)
  refine WP.seq (WP.mono (widthCompare_ok hp (show 384 < 4096 by decide) hvd)
    fun w ⟨hwz, _, hwm, hkw⟩ => ?_)
  have hw8 := (hkw.gpr .x8 (by decide)).trans hv8
  have hkuw := (hku.trans hkv).trans hkw
  by_cases h384 : p = 384
  · refine WP.ite true (by rw [hwz, h384]; rfl) (fun _ => ?_) (fun h => Bool.noConfusion h)
    have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 32 := by
      unfold Spec.Dsa.supportedSizes; omega
    rw [decide_eq_decide.mpr he]
    exact WP.mono (widthMask_ok (by decide) hq hw8) fun t ⟨ht, hm, hk⟩ =>
      ⟨ht, hm.trans (hwm.trans (hvm.trans hum)), (hkuw.trans hk).mono (by decide)⟩
  refine WP.ite false (by rw [hwz, decide_eq_false h384]) (fun h => Bool.noConfusion h) (fun _ => ?_)
  have he : ¬ Spec.Dsa.supportedSizes (8 * p) (8 * q) := by
    unfold Spec.Dsa.supportedSizes; omega
  rw [decide_eq_false he]
  refine WP.mono (WP.keep [.x15] (Q := fun t => t.gpr .x15 = mask false ∧ t.mem = w.mem)
    (by brun) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨ht, hm⟩, hk⟩ =>
      ⟨ht, hm.trans (hwm.trans (hvm.trans hum)), (hkuw.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
