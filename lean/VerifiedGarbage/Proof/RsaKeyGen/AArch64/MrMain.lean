module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Front
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# A candidate on AArch64: Miller–Rabin's loop

The loop's remaining witnesses from `(i, uniform)` at the offset `used` of
`rand` (`mrRest`), `kStat` against 4 (`statCmp_ok`), and the test of the
octets of `rand` left (`iterHead_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep eval_zero eq_zero_iff)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY sCnt sK)

/-- The witnesses' loop from `(i, uniform)` at offset `used`. -/
abbrev mrRest (c ch : Nat) (r : List Byte) (i uni used : Nat) : Option (Bool × List Byte) :=
  Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2)
    (i, uni) (r.drop used)

theorem sub4_beq {v : Nat} (hv : v < 2 ^ 63) :
    (BitVec.ofNat 64 v - BitVec.ofNat 64 4 == 0) = decide (v = 4) := by
  rw [eq_zero_iff, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact decide_eq_decide.mpr (by omega_arith)

/-- `kStat` against 4. -/
theorem statCmp_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {v : Nat} (hv : v < 2 ^ 63) (hS : word s.mem B (8 * kStat) = BitVec.ofNat 64 v) :
    WP isa (.block [ldh .x3 kStat, .subImm .x .x3 .x3 4]) s fun t =>
      isa.eval (.zero .x .x3) t = some (decide (v = 4)) ∧ t.mem = s.mem ∧ Keep [.x3] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hS' : s.mem.readW (B + BitVec.ofNat 64 (8 * kStat)) 64 = BitVec.ofNat 64 v := hS
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 v - BitVec.ofNat 64 4 ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kStat < 32 by decide), h.scr.ld (d := 8 * kStat) (by simp only [kStat, sFn]; omega_arith),
      hS']) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ?_
  exact ⟨by rw [eval_zero, h3, sub4_beq hv], hm, k⟩

theorem ofNat_sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega_arith)]
  omega_arith

/-- The test of `rand`'s octets left: `x5 = 0` iff fewer than `8 w`. -/
theorem iterHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {r : List Byte} {used : Nat}
    (hw128 : w ≤ 128) (hrl : r.length < 2 ^ 64) (hul : used ≤ r.length)
    (hlen : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) :
    WP isa (.block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag)) s fun t =>
      isa.eval (.zero .x .x5) t = some (decide (r.length < used + 8 * w)) ∧ t.mem = s.mem ∧
        Keep [.x3, .x4, .x5, .x7] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have e1 : BitVec.ofNat 64 r.length - BitVec.ofNat 64 used = BitVec.ofNat 64 (r.length - used) :=
    ofNat_sub_ofNat' hul hrl
  have r1 : s.mem.readW (B + BitVec.ofNat 64 (8 * kRandLen)) 64 = BitVec.ofNat 64 r.length := hrlen
  have r2 : s.mem.readW (B + BitVec.ofNat 64 (8 * kUsed)) 64 = BitVec.ofNat 64 used := hus
  have r3 : s.mem.readW (B + BitVec.ofNat 64 (8 * kLen)) 64 = BitVec.ofNat 64 (8 * w) := hlen
  refine (WP.block_append_iff (M := isa)
    (l₁ := ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] : List Instr))).mpr ?_
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (r.length - used) ∧
      t.gpr .x4 = BitVec.ofNat 64 (8 * w) ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kRandLen < 32 by decide), hdr_enc (show kUsed < 32 by decide),
      hdr_enc (show kLen < 32 by decide), h.scr.ld (d := 8 * kRandLen) (by simp only [kRandLen, sFn]; omega_arith),
      h.scr.ld (d := 8 * kUsed) (by simp only [kUsed, sFn]; omega_arith),
      h.scr.ld (d := 8 * kLen) (by simp only [kLen, sK, sFn]; omega_arith), r1, r2, r3, e1]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h3, h4, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (geFlag_ok s₁) fun t ⟨⟨h5, hm⟩, k⟩ => ⟨?_, hm.trans hm₁, (k₁.trans k).mono (by decide)⟩
  rw [eval_zero, h5, h3, h4, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 8 * w < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show r.length - used < 2 ^ 64 by omega_arith)]
  rcases Nat.lt_or_ge r.length (used + 8 * w) with hl | hl
  · rw [decide_eq_false (show ¬(8 * w ≤ r.length - used) by omega_arith), decide_eq_true hl]; rfl
  · rw [decide_eq_true (show 8 * w ≤ r.length - used by omega_arith), decide_eq_false (show ¬(r.length < used + 8 * w) by omega_arith)]
    rfl

end VG.Proof.RsaKeyGen.AArch64
