module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Cand
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
import VerifiedGarbage.Proof.Framework.WriteBytes
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
open VG.Impl.RsaOaep.PPC64LE (zeroLoop)
open VG.Proof.Mont.PPC64LE (Kp)
open VG.Proof.Hmac.Common (bytesAt_add)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

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

/-- The frame's `n` bytes at `o` set to `b`, by the byte loop. -/
theorem fill_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {o n b : Nat} {c : Byte} (hn : 0 < n)
    (hn' : n < 2 ^ 15) (ho : o < 2 ^ 15) (hb : b < 2 ^ 15) (hbc : (BitVec.ofNat 64 b).setWidth 8 = c)
    (h₁ : 128 ≤ 96 + o) (h₂ : 96 + o + n ≤ 688) (hs : Safe L ⟨L.B + BitVec.ofNat 64 (96 + o), n⟩) :
    WP isa (Cfg.fill o n b) t fun u => Ctx L g lr m₀ u ∧ Kp [.r4, .r5, .r6] t u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (96 + o), n⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + o)) n = List.replicate n c := by
  have hnB := hL.nB
  refine WP.seq (WP.of_syms (stepAddSp ho fun t₁ k₁ m₁ v₁ => stepLi hn' fun t₂ k₂ m₂ v₂ =>
    stepLi hb fun u k₃ m₃ v₃ => wp_nil fun hsy₀ => ?_))
  have K : Kp [.r4, .r5, .r6] t u := (k₁.mono.trans k₂.mono).trans k₃.mono
  have hm : u.mem = t.mem := by rw [m₃, m₂, m₁]
  have hu := hc.kp hL K hm hsy₀
  have h4 : u.gpr .r4 = L.B + BitVec.ofNat 64 (96 + o) := by
    rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), v₁, hc.sp, fr_add]
  have h5 : u.gpr .r5 = BitVec.ofNat 64 n := by rw [k₃.gpr _ (by decide), v₂]
  have h6 : (u.gpr .r6).setWidth 8 = c := by rw [v₃]; exact hbc
  refine WP.mono_syms (Proof.RsaOaep.PPC64LE.zero_ok hn (by omega) h4 h5 h6
    (fun i hi => by rw [Offset.add_add]; exact hu.inFrW (n := 1) (by omega) (by omega)))
    fun u' ⟨hk, hm'⟩ hsy => ?_
  have K' : Kp [.r4, .r5] u u' := ⟨fun r hr => hk.gpr r (by simp_all), hk.rd, hk.wr, hk.sp, hk.lr⟩
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (96 + o), n⟩] u.mem u'.mem := by
    rw [hm']; exact WriteBytes.writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
  refine ⟨hu.keep hL K'.rd K'.wr K'.sp (fun r hr => K'.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl <;> simp [preserved] at hr)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs) hsy, K.trans K'.mono, hm ▸ hf, ?_⟩
  rw [hm']
  have := Proof.Hmac.Common.bytesAt_writeBytes_self u.mem (L.B + BitVec.ofNat 64 (96 + o)) (List.replicate n c)
    (by rw [List.length_replicate]; omega)
  rw [List.length_replicate] at this
  exact this

/-- `V = 0x01…` and `K = 0x00…`, all 64 bytes of each. -/
theorem initKV_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa Cfg.initKV t fun u => Ctx L g lr m₀ u ∧ Frame [⟨L.B + BitVec.ofNat 64 128, 128⟩] t.mem u.mem ∧
      ∀ D ≤ 64, Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 192) D = List.replicate D 1 ∧
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 128) D = List.replicate D 0 := by
  have hnB := hL.nB
  refine WP.seq (WP.mono (fill_ok (o := fV) (n := 64) (b := 1) (c := 1) hL hc (by decide) (by decide)
    (by decide) (by decide) rfl (by decide) (by decide) (safe_low L (by decide))) fun u ⟨hu, _, hf, hv⟩ => ?_)
  refine WP.mono (fill_ok (o := fK) (n := 64) (b := 0) (c := 0) hL hu (by decide) (by decide) (by decide)
    (by decide) rfl (by decide) (by decide) (safe_low L (by decide))) fun u' ⟨hu', _, hf', hk⟩ => ?_
  simp only [fV, fK, Nat.reduceAdd] at hf hv hf' hk
  have hv' : Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 192) 64 = List.replicate 64 1 := by
    rw [bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by decide)) (by omega) (by omega)) (by decide)]
    exact hv
  refine ⟨hu', (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by omega)⟩).trans
    (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by omega)⟩),
    fun D hD => ⟨?_, ?_⟩⟩
  · rw [← bytesAt_take _ _ hD, hv', List.take_replicate, Nat.min_eq_left hD]
  · rw [← bytesAt_take _ _ hD, hk, List.take_replicate, Nat.min_eq_left hD]

/-- The frame's `K` and `V`, and everything above its pointers, wiped. -/
theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa Cfg.wipe t fun u => Ctx L g lr m₀ u ∧ Kp [.r4, .r5, .r6] t u ∧
      Frame [⟨L.B + BitVec.ofNat 64 128, 128⟩, ⟨L.B + BitVec.ofNat 64 328, 360⟩] t.mem u.mem := by
  refine WP.seq (WP.mono (fill_ok (o := fK) (n := 128) (b := 0) (c := 0) hL hc (by decide) (by decide) (by decide)
    (by decide) rfl (by decide) (by decide) (safe_low L (by decide))) fun u ⟨hu, K, hf, _⟩ => ?_)
  refine WP.mono (fill_ok (o := fH) (n := 360) (b := 0) (c := 0) hL hu (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) (by decide) (safe_high L (by decide) (by decide))) fun u' ⟨hu', K', hf', _⟩ => ⟨hu', K.trans K', ?_⟩
  exact (hf.sub fun r hr => ⟨r, by simp at hr; simp [hr, fK], fun _ h => h⟩).trans
    (hf'.sub fun r hr => ⟨r, by simp at hr; simp [hr, fH], fun _ h => h⟩)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
