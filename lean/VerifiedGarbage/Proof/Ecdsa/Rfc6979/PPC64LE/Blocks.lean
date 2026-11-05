module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Cand
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step

/-!
# Deterministic ECDSA on PPC64LE: the blocks between the calls

`V = 0x01…` and `K = 0x00…` (`initKV_ok`), the number of candidates
(`initCnt_ok`), the arguments of `core` (`coreArgs_ok`), whether to go on
(`goOn_ok`, `again_ok`, `stop_ok`), and the wiping of the frame (`wipe_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)
open VG.Proof.Hmac.Common (bytesAt_add)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- Four bytes of a 32-bit word stored: its little-endian bytes. -/
theorem bytesAt_word (m : Mem) (a : Addr) (v : BitVec 32) :
    Spec.Sha256.bytesAt (m.writeW a v) a 4 = [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8,
      v.extractLsb' 24 8] := by
  have : ∀ i < 4, (m.writeW a v) (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 := by
    intro i hi
    simp only [Mem.writeW, Mem.write, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), show 32 / 8 = 4 from rfl, hi, ite_true]
    rfl
  simp only [Spec.Sha256.bytesAt, show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil]
  rw [this 0 (by decide), this 1 (by decide), this 2 (by decide), this 3 (by decide)]

/-- The pairs of stores of `initKV`, `j` of them. -/
theorem initKV_eq : Cfg.initKV =
    ([.addSp .r11 0, .lis .r9 0x0101, .ori .r9 .r9 0x0101, .li .r10 0] : List Instr) ++
      (List.range 16).flatMap fun j => [.store .w .r9 .r11 (fV + 4 * j), .store .w .r10 .r11 (fK + 4 * j)] := rfl

theorem kv_pairs (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) (K : Nat) (hK : K ≤ 16) :
    ∀ k ≤ K, ∀ u : State, u.wr = t.wr → u.gpr .r11 = L.B + BitVec.ofNat 64 96 →
      u.gpr .r9 = BitVec.ofNat 64 0x01010101 → u.gpr .r10 = 0 →
      WP isa (.block ((List.range k).flatMap fun j =>
          [.store .w .r9 .r11 (fV + 4 * j), .store .w .r10 .r11 (fK + 4 * j)])) u fun u' =>
        Kp [] u u' ∧ u'.gpr = u.gpr ∧ Frame [⟨L.B + BitVec.ofNat 64 128, 128⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 192) (4 * k) = List.replicate (4 * k) 1 ∧
        Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 128) (4 * k) = List.replicate (4 * k) 0
  | 0, _, u, _, _, _, _ => wp_nil ⟨Kp.refl _ _, rfl, Frame.refl _ _, rfl, rfl⟩
  | k + 1, hk, u, hw, h11, h9, h10 => by
    have hnB := hL.nB
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (kv_pairs hL hc K hK k (by omega) u hw h11 h9 h10) fun u₁ ⟨k₁, g₁, f₁, v₁, kk₁⟩ => ?_
    refine stepStw (a := L.B + BitVec.ofNat 64 (192 + 4 * k)) (by decide) (by simp only [fV]; omega)
      (by rw [g₁, h11, fr_add, show 96 + (fV + 4 * k) = 192 + 4 * k by simp only [fV]; omega])
      (by rw [k₁.wr, hw]; exact hc.inFrW (by omega) (by omega)) fun u₂ k₂ g₂ m₂ => ?_
    refine stepStw (a := L.B + BitVec.ofNat 64 (128 + 4 * k)) (by decide) (by simp only [fK]; omega)
      (by rw [g₂, g₁, h11, fr_add, show 96 + (fK + 4 * k) = 128 + 4 * k by simp only [fK]; omega])
      (by rw [k₂.wr, k₁.wr, hw]; exact hc.inFrW (by omega) (by omega)) fun u₃ k₃ g₃ m₃ => wp_nil ?_
    have f₂ : Frame [⟨L.B + BitVec.ofNat 64 (192 + 4 * k), 4⟩] u₁.mem u₂.mem := by
      rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have f₃ : Frame [⟨L.B + BitVec.ofNat 64 (128 + 4 * k), 4⟩] u₂.mem u₃.mem := by
      rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have fr : ∀ {o : Nat}, 128 ≤ o → o + 4 ≤ 256 → ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 o, 4⟩ : Region)],
        ∃ r' ∈ [(⟨L.B + BitVec.ofNat 64 128, 128⟩ : Region)], Region.Sub r r' := fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ h₁ (by omega)⟩
    have keep : ∀ {u u' : State} {o n o' : Nat}, Frame [⟨L.B + BitVec.ofNat 64 o', 4⟩] u.mem u'.mem →
        o + n ≤ o' ∨ o' + 4 ≤ o → o' + 4 ≤ 736 → o + n ≤ 736 →
        Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 o) n = Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 o) n :=
      fun f h h₁ h₂ => bytesAt_frame f (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ h (by omega) (by omega)) (by omega)
    have w9 : (u₁.gpr .r9).setWidth 32 = 0x01010101#32 := by rw [g₁, h9]; rfl
    have w10 : (u₂.gpr .r10).setWidth 32 = 0#32 := by rw [g₂, g₁, h10]; rfl
    refine ⟨(k₁.trans k₂).trans k₃, by rw [g₃, g₂, g₁], f₁.trans ((f₂.sub (fr (by omega) (by omega))).trans
      (f₃.sub (fr (by omega) (by omega)))), ?_, ?_⟩
    · rw [show 4 * (k + 1) = 4 * k + 4 by omega, bytesAt_add, Offset.add_add,
        keep (o := 192) (n := 4 * k) f₃ (by omega) (by omega) (by omega),
        keep (o := 192) (n := 4 * k) f₂ (by omega) (by omega) (by omega), v₁,
        keep (o := 192 + 4 * k) (n := 4) f₃ (by omega) (by omega) (by omega), m₂, bytesAt_word, w9,
        ← List.replicate_append_replicate]
      rfl
    · rw [show 4 * (k + 1) = 4 * k + 4 by omega, bytesAt_add, Offset.add_add,
        keep (o := 128) (n := 4 * k) f₃ (by omega) (by omega) (by omega),
        keep (o := 128) (n := 4 * k) f₂ (by omega) (by omega) (by omega), kk₁, m₃, bytesAt_word, w10,
        ← List.replicate_append_replicate]
      rfl

/-- `V = 0x01…` and `K = 0x00…`, all 64 bytes of each. -/
theorem initKV_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.initKV) t fun u => Ctx L g lr m₀ u ∧ Frame [⟨L.B + BitVec.ofNat 64 128, 128⟩] t.mem u.mem ∧
      ∀ D ≤ 64, Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 192) D = List.replicate D 1 ∧
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 128) D = List.replicate D 0 := by
  rw [initKV_eq, WP.block_append_iff]
  refine WP.of_syms (stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  refine stepLis fun t₂ k₂ m₂ v₂ => ?_
  refine stepOri fun t₃ k₃ m₃ v₃ => ?_
  refine stepLi (by decide) fun t₄ k₄ m₄ v₄ => wp_nil fun hsy₄ => ?_
  have K : Kp [.r11, .r9, .r10] t t₄ := ((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono
  refine WP.of_syms <| WP.mono (kv_pairs hL hc 16 (Nat.le_refl _) 16 (Nat.le_refl _) t₄ K.wr
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), v₁, hc.sp, BitVec.add_zero])
    (by rw [k₄.gpr _ (by decide), v₃, v₂]; decide) v₄) fun u ⟨ku, _, fu, vu, kku⟩ hsy => ?_
  have hm : t₄.mem = t.mem := by rw [m₄, m₃, m₂, m₁]
  have K' : Kp [.r11, .r9, .r10] t u := K.trans ku.mono
  refine ⟨hc.keep hL K'.rd K'.wr K'.sp (fun r hr => K'.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl | rfl <;> simp [preserved] at hr)) (hm ▸ fu)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega))
    (hsy.trans hsy₄), hm ▸ fu, fun D hD => ⟨?_, ?_⟩⟩
  · rw [← bytesAt_take _ _ (show D ≤ 4 * 16 by omega), vu, List.take_replicate, Nat.min_eq_left (by omega)]
  · rw [← bytesAt_take _ _ (show D ≤ 4 * 16 by omega), kku, List.take_replicate, Nat.min_eq_left (by omega)]

/-- The count of candidates left. -/
abbrev cnt (L : Lay dn) (m : Mem) : BitVec 64 := m.readW (L.B + BitVec.ofNat 64 264) 64

/-- The candidates left. -/
theorem initCnt_ok (hL : L.Ok) {c : Cfg} (ht : c.tries < 2 ^ 15) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block c.initCnt) t fun u => Ctx L g lr m₀ u ∧ Frame [⟨L.B + BitVec.ofNat 64 264, 8⟩] t.mem u.mem ∧
      cnt L u.mem = BitVec.ofNat 64 c.tries := by
  refine WP.of_syms (stepLi ht fun t₁ k₁ m₁ v₁ => ?_)
  refine stepAddSp (by decide) fun t₂ k₂ m₂ v₂ => ?_
  refine stepStd (a := L.B + BitVec.ofNat 64 264) (by decide) (by decide)
    (by rw [v₂, k₁.sp, hc.sp, BitVec.add_zero, fr_add]; rfl)
    (by rw [k₂.wr, k₁.wr]; exact hc.inFrW (by omega) (by omega)) fun t₃ k₃ g₃ m₃ => wp_nil fun hsy => ?_
  have K : Kp [.r9, .r11] t t₃ := (k₁.mono.trans k₂.mono).trans k₃.mono
  have hf : Frame [⟨L.B + BitVec.ofNat 64 264, 8⟩] t.mem t₃.mem := by
    rw [m₃, m₂, m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL K.rd K.wr K.sp (fun r hr => K.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl <;> simp [preserved] at hr)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)) hsy, hf, ?_⟩
  show Mem.readW _ _ 64 = _
  rw [m₃, Mem.readW_writeW_self64, k₂.gpr _ (by decide), v₁]

variable {P : RfcHash}

/-- The digest `core` reads: `X` (or, if `big`, the digest shifted left by
`sh` bits, at `fXc`). -/
abbrev dgArg (P : RfcHash) (L : Lay dn) : Addr :=
  if P.R.big then L.B + BitVec.ofNat 64 (96 + fXc) else L.B + BitVec.ofNat 64 (96 + fX)

/-- The arguments of `core`: `out`, `d`, its digest, `k = T` and `scratch`. -/
theorem coreArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block (cfgOf P).coreArgs) t fun u => Ctx L g lr m₀ u ∧ u.mem = t.mem ∧
      Kp [.r11, .r3, .r4, .r5, .r6, .r7] t u ∧ u.gpr .r3 = L.out ∧ u.gpr .r4 = L.d ∧
      u.gpr .r5 = dgArg P L ∧ u.gpr .r6 = kArg P L ∧ u.gpr .r7 = L.scr := by
  simp only [Cfg.coreArgs]
  refine WP.of_syms (stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 296) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc.inFrK k₁ (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 288) (by decide) (by decide)
    (by rw [k₂.gpr _ (by decide), hb, fr_add]; rfl) (hc.inFrK (k₁.mono.trans k₂.mono (rs := [.r11, .r3]))
      (by omega) (by omega)) fun t₃ k₃ m₃ v₃ => ?_
  refine stepAddSp (show (cfgOf P).fDg < 2 ^ 15 by simp only [Cfg.fDg]; split <;> decide)
    fun t₄ k₄ m₄ v₄ => ?_
  refine stepAddSp (by decide) fun t₅ k₅ m₅ v₅ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 272) (by decide) (by decide)
    (by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb,
      fr_add]; rfl)
    (hc.inFrK ((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono
      (rs := [.r11, .r3, .r4, .r5, .r6])) (by omega) (by omega)) fun t₆ k₆ m₆ v₆ => wp_nil fun hsy => ?_
  have K : Kp [.r11, .r3, .r4, .r5, .r6, .r7] t t₆ :=
    ((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono
  have hm : t₆.mem = t.mem := by rw [m₆, m₅, m₄, m₃, m₂, m₁]
  refine ⟨hc.kp hL K hm hsy, hm, K, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), v₂, m₁,
      hc.pOut]
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), v₃, m₂, m₁, hc.pD]
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), v₄, k₃.sp, k₂.sp, k₁.sp, hc.sp, fr_add]
    simp only [dgArg, Cfg.fDg, show (cfgOf P).big = P.R.big from rfl]
    split <;> rfl
  · rw [k₆.gpr _ (by decide), v₅, k₄.sp, k₃.sp, k₂.sp, k₁.sp, hc.sp, fr_add]
  · rw [v₆, m₅, m₄, m₃, m₂, m₁, hc.pScr]

/-- One candidate fewer, and whether to try another: `r12` is zero if
`core` succeeded (bit 0 of `r3`) or no candidates are left. -/
theorem goOn_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.goOn) t fun u => Ctx L g lr m₀ u ∧ Kp [.r11, .r9, .r10, .r8, .r12] t u ∧
      Frame [⟨L.B + BitVec.ofNat 64 264, 8⟩] t.mem u.mem ∧ cnt L u.mem = cnt L t.mem - 1 ∧
      u.gpr .r12 = (((t.gpr .r3 &&& 1) - 1) &&& (cnt L t.mem - 1)) := by
  refine WP.of_syms (stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 264) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc.inFrK k₁ (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => ?_
  refine stepSubi (by decide) (by decide) fun t₃ k₃ m₃ v₃ => ?_
  refine stepStd (a := L.B + BitVec.ofNat 64 264) (by decide) (by decide)
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb, fr_add]; rfl)
    (by rw [k₃.wr, k₂.wr, k₁.wr]; exact hc.inFrW (by omega) (by omega)) fun t₄ k₄ g₄ m₄ => ?_
  refine stepLi (by decide) fun t₅ k₅ m₅ v₅ => ?_
  refine stepAnd fun t₆ k₆ m₆ v₆ => ?_
  refine stepSub fun t₇ k₇ m₇ v₇ => ?_
  refine stepAnd fun t₈ k₈ m₈ v₈ => wp_nil fun hsy => ?_
  have K : Kp [.r11, .r9, .r10, .r8, .r12] t t₈ :=
    ((((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono).trans
      k₇.mono).trans k₈.mono
  have c9 : t₃.gpr .r9 = cnt L t.mem - 1 := by rw [v₃, v₂, m₁]; rfl
  have hm : t₈.mem = t₃.mem.writeW (L.B + BitVec.ofNat 64 264) (t₃.gpr .r9) := by rw [m₈, m₇, m₆, m₅, m₄]
  have hm₃ : t₃.mem = t.mem := by rw [m₃, m₂, m₁]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 264, 8⟩] t.mem t₈.mem := by
    rw [hm, hm₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL K.rd K.wr K.sp (fun r hr => K.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [preserved] at hr)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)) hsy, K, hf,
    by show Mem.readW _ _ 64 = _; rw [hm, Mem.readW_writeW_self64, c9], ?_⟩
  have h9 : t₇.gpr .r9 = cnt L t.mem - 1 := by
    rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide), g₄, c9]
  have h10 : t₆.gpr .r10 = BitVec.ofNat 64 1 := by rw [k₆.gpr _ (by decide), v₅]
  have h3 : t₅.gpr .r3 = t.gpr .r3 := by
    rw [k₅.gpr _ (by decide), g₄, k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  rw [v₈, v₇, v₆, h9, h10, h3, v₅]
  rfl

theorem again_ok {t : State} {Q : State → Prop} (k : ∀ u, Kp [.r12] t u → u.mem = t.mem → u.gpr .r12 = 1 →
    u.syms = t.syms → Q u) :
    WP isa (.block Cfg.again) t Q :=
  WP.of_syms (stepLi (by decide) fun u k₁ m₁ v₁ => wp_nil (k u k₁ m₁ (by rw [v₁]; rfl)))

theorem stop_ok {t : State} {Q : State → Prop} (k : ∀ u, Kp [.r12] t u → u.mem = t.mem → u.gpr .r12 = 0 →
    u.syms = t.syms → Q u) :
    WP isa (.block Cfg.stop) t Q :=
  WP.of_syms (stepLi (by decide) fun u k₁ m₁ v₁ => wp_nil (k u k₁ m₁ (by rw [v₁]; rfl)))

/-- `k` doublewords of zeros from `o` (`r12 = 0`), within `[B + 96 + o, B + 96 + o + 8 k')`. -/
theorem wipe_stores {t : State} (hc : Ctx L g lr m₀ t) {o K : Nat} (ho : 128 ≤ 96 + o) (hK : 96 + o + 8 * K ≤ 688)
    (ho4 : o % 4 = 0) :
    ∀ k ≤ K, ∀ u : State, u.wr = t.wr → u.gpr .r11 = L.B + BitVec.ofNat 64 96 →
      WP isa (.block ((List.range k).map fun j => .store .d .r12 .r11 (o + 8 * j))) u fun u' =>
        Kp [] u u' ∧ Frame [⟨L.B + BitVec.ofNat 64 (96 + o), 8 * K⟩] u.mem u'.mem
  | 0, _, u, _, _ => wp_nil ⟨Kp.refl _ _, Frame.refl _ _⟩
  | k + 1, hk, u, hw, h11 => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (wipe_stores hc ho hK ho4 k (by omega) u hw h11) fun u₁ ⟨g₁, f₁⟩ => ?_
    refine stepStd (a := L.B + BitVec.ofNat 64 (96 + o + 8 * k)) (by decide) ⟨by omega, by omega⟩
      (by rw [g₁.gpr _ (by simp), h11, fr_add, Nat.add_assoc])
      (by rw [g₁.wr, hw]; exact hc.inFrW (by omega) (by omega)) fun u₂ k₂ g₂ m₂ => wp_nil ?_
    have f₂ : Frame [⟨L.B + BitVec.ofNat 64 (96 + o + 8 * k), 8⟩] u₁.mem u₂.mem := by
      rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    exact ⟨g₁.trans k₂, f₁.trans (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩)⟩

/-- The frame's `K` and `V`, and everything above its pointers, wiped. -/
theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.wipe) t fun u => Ctx L g lr m₀ u ∧ Kp [.r11, .r12] t u ∧
      Frame [⟨L.B + BitVec.ofNat 64 128, 128⟩, ⟨L.B + BitVec.ofNat 64 328, 360⟩] t.mem u.mem := by
  rw [Cfg.wipe, List.append_assoc, WP.block_append_iff]
  refine WP.of_syms (stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  refine stepLi (by decide) fun t₂ k₂ m₂ v₂ => wp_nil fun hsy₂ => ?_
  have K : Kp [.r11, .r12] t t₂ := k₁.mono.trans k₂.mono
  have b₂ : t₂.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [k₂.gpr _ (by decide), v₁, hc.sp, BitVec.add_zero]
  rw [WP.block_append_iff]
  refine WP.of_syms <| WP.mono (wipe_stores hc (o := fK) (K := 16) (by decide) (by decide) (by decide) 16 (Nat.le_refl _) t₂
    K.wr b₂) fun u ⟨gu, fu⟩ hsyu => ?_
  refine WP.of_syms <| WP.mono (wipe_stores hc (o := fH) (K := 45) (by decide) (by decide) (by decide) 45 (Nat.le_refl _) u
    (by rw [gu.wr, K.wr]) (by rw [gu.gpr _ (by simp), b₂])) fun u' ⟨gu', fu'⟩ hsy => ?_
  have K' : Kp [.r11, .r12] t u' := (K.trans gu.mono).trans gu'.mono
  have hf : Frame [⟨L.B + BitVec.ofNat 64 128, 128⟩, ⟨L.B + BitVec.ofNat 64 328, 360⟩] t.mem u'.mem := by
    rw [← m₁, ← m₂]
    exact (fu.sub fun r hr => ⟨r, by simp at hr; simp [hr, fK], fun _ h => h⟩).trans
      (fu'.sub fun r hr => ⟨r, by simp at hr; simp [hr, fH], fun _ h => h⟩)
  refine ⟨hc.keep hL K'.rd K'.wr K'.sp (fun r hr => K'.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl <;> simp [preserved] at hr)) hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact safe_low L (by omega)
      · exact safe_high L (by omega) (by omega)) ((hsy.trans hsyu).trans hsy₂), K', hf⟩

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
