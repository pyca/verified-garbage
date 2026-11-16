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
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Prep
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Mont.PPC64LE.Step

/-! ### `Ecdsa.Rfc6979.PPC64LE.Loop`, which only this module used -/

section

/-! ### `Ecdsa.Rfc6979.PPC64LE.Blocks`, which only this module used -/

section

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
    (by rw [k₂.wr, k₁.wr]; exact hc.inFrW (by omega_using []) (by omega_using [])) fun t₃ k₃ g₃ m₃ => wp_nil fun hsy => ?_
  obtain K : Kp [.r9, .r11] t t₃ := (k₁.mono.trans k₂.mono).trans k₃.mono
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 264, 8⟩] t.mem t₃.mem := by
    rw [m₃, m₂, m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL K.rd K.wr K.sp (fun r hr => K.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl <;> simp [preserved] at hr)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_using [])) hsy, hf, ?_⟩
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
  obtain hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 296) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc.inFrK k₁ (by omega_using []) (by omega_using [])) fun t₂ k₂ m₂ v₂ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 288) (by decide) (by decide)
    (by rw [k₂.gpr _ (by decide), hb, fr_add]; rfl) (hc.inFrK (k₁.mono.trans k₂.mono (rs := [.r11, .r3]))
      (by omega_using []) (by omega_using [])) fun t₃ k₃ m₃ v₃ => ?_
  refine stepAddSp (show (cfgOf P).fDg < 2 ^ 15 by simp only [Cfg.fDg]; split <;> decide)
    fun t₄ k₄ m₄ v₄ => ?_
  refine stepAddSp (by decide) fun t₅ k₅ m₅ v₅ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 272) (by decide) (by decide)
    (by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb,
      fr_add]; rfl)
    (hc.inFrK ((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono
      (rs := [.r11, .r3, .r4, .r5, .r6])) (by omega_using []) (by omega_using [])) fun t₆ k₆ m₆ v₆ => wp_nil fun hsy => ?_
  obtain K : Kp [.r11, .r3, .r4, .r5, .r6, .r7] t t₆ :=
    ((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono
  obtain hm : t₆.mem = t.mem := by rw [m₆, m₅, m₄, m₃, m₂, m₁]
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
  obtain hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 264) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc.inFrK k₁ (by omega_using []) (by omega_using [])) fun t₂ k₂ m₂ v₂ => ?_
  refine stepSubi (by decide) (by decide) fun t₃ k₃ m₃ v₃ => ?_
  refine stepStd (a := L.B + BitVec.ofNat 64 264) (by decide) (by decide)
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb, fr_add]; rfl)
    (by rw [k₃.wr, k₂.wr, k₁.wr]; exact hc.inFrW (by omega_using []) (by omega_using [])) fun t₄ k₄ g₄ m₄ => ?_
  refine stepLi (by decide) fun t₅ k₅ m₅ v₅ => ?_
  refine stepAnd fun t₆ k₆ m₆ v₆ => ?_
  refine stepSub fun t₇ k₇ m₇ v₇ => ?_
  refine stepAnd fun t₈ k₈ m₈ v₈ => wp_nil fun hsy => ?_
  obtain K : Kp [.r11, .r9, .r10, .r8, .r12] t t₈ :=
    ((((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono).trans
      k₇.mono).trans k₈.mono
  obtain c9 : t₃.gpr .r9 = cnt L t.mem - 1 := by rw [v₃, v₂, m₁]; rfl
  obtain hm : t₈.mem = t₃.mem.writeW (L.B + BitVec.ofNat 64 264) (t₃.gpr .r9) := by rw [m₈, m₇, m₆, m₅, m₄]
  obtain hm₃ : t₃.mem = t.mem := by rw [m₃, m₂, m₁]
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 264, 8⟩] t.mem t₈.mem := by
    rw [hm, hm₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL K.rd K.wr K.sp (fun r hr => K.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [preserved] at hr)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_using [])) hsy, K, hf,
    by show Mem.readW _ _ 64 = _; rw [hm, Mem.readW_writeW_self64, c9], ?_⟩
  obtain h9 : t₇.gpr .r9 = cnt L t.mem - 1 := by
    rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide), g₄, c9]
  obtain h10 : t₆.gpr .r10 = BitVec.ofNat 64 1 := by rw [k₆.gpr _ (by decide), v₅]
  obtain h3 : t₅.gpr .r3 = t.gpr .r3 := by
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
  obtain K : Kp [.r4, .r5, .r6] t u := (k₁.mono.trans k₂.mono).trans k₃.mono
  obtain hm : u.mem = t.mem := by rw [m₃, m₂, m₁]
  obtain hu := hc.kp hL K hm hsy₀
  obtain h4 : u.gpr .r4 = L.B + BitVec.ofNat 64 (96 + o) := by
    rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), v₁, hc.sp, fr_add]
  obtain h5 : u.gpr .r5 = BitVec.ofNat 64 n := by rw [k₃.gpr _ (by decide), v₂]
  obtain h6 : (u.gpr .r6).setWidth 8 = c := by rw [v₃]; exact hbc
  refine WP.mono_syms (Proof.RsaOaep.PPC64LE.zero_ok hn (by omega_using [hn']) h4 h5 h6
    (fun i hi => by rw [Offset.add_add]; exact hu.inFrW (n := 1) (by omega_using [h₁]) (by omega_using [h₂, hi])))
    fun u' ⟨hk, hm'⟩ hsy => ?_
  obtain K' : Kp [.r4, .r5] u u' := ⟨fun r hr => hk.gpr r (by simp_all), hk.rd, hk.wr, hk.sp, hk.lr⟩
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 (96 + o), n⟩] u.mem u'.mem := by
    rw [hm']; exact WriteBytes.writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
  refine ⟨hu.keep hL K'.rd K'.wr K'.sp (fun r hr => K'.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl <;> simp [preserved] at hr)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs) hsy, K.trans K'.mono, hm ▸ hf, ?_⟩
  rw [hm']
  have := Proof.Hmac.Common.bytesAt_writeBytes_self u.mem (L.B + BitVec.ofNat 64 (96 + o)) (List.replicate n c)
    (by rw [List.length_replicate]; omega_using [hn'])
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
  obtain hv' : Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 192) 64 = List.replicate 64 1 := by
    rw [bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by decide)) (by omega_using []) (by omega_using [])) (by decide)]
    exact hv
  refine ⟨hu', (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by omega_using [])⟩).trans
    (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by omega_using [])⟩),
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

end

end


/-!
# Deterministic ECDSA on PPC64LE: the candidates

The values of a run, as RFC 6979 computes them from the private key and the
digest on entry (`kvI`, `candI`, `sigI`), with candidates of `nV` `V`s; the
call of `core` with the candidate (`core_ok`); the loop's invariant before
candidate `i` (`LoopInv`): `K` and `V` are those before it, the count is
`tries - i`, every earlier candidate was unsuitable, and `core`'s digest is
the digest's (`DgOk`). One iteration either moves to candidate `i + 1` or
leaves the loop with the signature of candidate `i`, which is suitable or
the last (`tryOne_ok`, `loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-! ## The run's values -/

/-- The private key, the digest and its integer. -/
abbrev xOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : Nat :=
  Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.d P.Q)
abbrev hBOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.dg P.v.H.D
abbrev eOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  Spec.Ecdsa.hashToInt P.R.C.E.curve (hBOf P L m₀)

/-- `K` and `V` after steps b–g. -/
abbrev kv0 (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init P.R.C.E.curve P.v.ok.SH.H P.v.H.D (xOf P L m₀) (hBOf P L m₀)

/-- `K` and `V` before candidate `i`, candidate `i`'s `T`, and its signature. -/
abbrev kvI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte × List Byte :=
  kvAtB P.v.ok.SH.H P.nV (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev candI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte :=
  candAtB P.v.ok.SH.H P.nV (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev sigI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.R.C.E.curve (xOf P L m₀) (eOf P L m₀)
    (Spec.Ecdsa.Rfc6979.bits2int P.R.C.E.curve (candI P L m₀ i))

/-- `core`'s digest is the digest's integer. -/
def DgOk (P : RfcHash) (L : Lay P.I.hashLen) (m₀ m : Mem) : Prop :=
  Spec.Ecdsa.hashToInt P.R.C.E.curve (Spec.Sha256.bytesAt m (dgArg P L) P.Q) = eOf P L m₀

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (P : RfcHash) {dn : Nat} (L : Lay dn) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => (t.gpr .r3).setWidth 32 = (1 : BitVec 32) ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * P.Q) = Spec.Ecdsa.encode P.R.C.E.curve rs
  | none => (t.gpr .r3).setWidth 32 = (0 : BitVec 32) ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * P.Q) = List.replicate (2 * P.Q) 0

/-- Before candidate `i`. -/
structure LoopInv (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L t.mem = (kvI P L m₀ i).1
  v : vOf P L t.mem = (kvI P L m₀ i).2
  cnt : cnt L t.mem = BitVec.ofNat 64 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ t.mem
  saved : SavedK P L t.mem (kOf P L t.mem)

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.I.tries
  fails : ∀ j < i, sigI P L m₀ j = none
  last : sigI P L m₀ i ≠ none ∨ i + 1 = P.I.tries
  res : ResultIs P L (sigI P L m₀ i) t

/-! ## Facts kept -/

theorem Q_le (P : RfcHash) : P.Q ≤ 66 := P.sizes.2.2.2.2.2.2.2.2.2.2.1

theorem Ctx.dBytes (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g lr m₀ t) :
    Spec.Sha256.bytesAt t.mem L.d P.Q = Spec.Sha256.bytesAt m₀ L.d P.Q := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.d_byte hL (by have := List.mem_range.mp hi; omega_using [hq, this])

/-- The count, kept by memory that changed elsewhere. -/
theorem cnt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 264, 8⟩ r) : cnt L m' = cnt L m :=
  hf.readW (r := ⟨L.B + BitVec.ofNat 64 264, 8⟩) (w := 64)
    (by simpa only [Nat.reduceDiv] using Region.contains_self (L.B + BitVec.ofNat 64 264) 8) hd (by decide)

/-- What `core` changes: `out`, `scratch` and the calls' 96 bytes of stack. -/
abbrev CoreW {dn : Nat} (L : Lay dn) : List Region := [L.OUT, L.SCR, ⟨L.B, 96⟩]

/-- The regions the loop writes but the count. -/
def Away {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  r = L.SCR ∨ r = L.OUT ∨ r = ⟨L.B, 96⟩ ∨ r = ⟨L.B, 256⟩ ∨ r = ⟨L.B, 264⟩ ∨
    r = ⟨L.B + BitVec.ofNat 64 (96 + fT), 136⟩

/-- The regions the loop writes. -/
def Apart {dn : Nat} (L : Lay dn) (r : Region) : Prop := Away L r ∨ r = ⟨L.B + BitVec.ofNat 64 264, 8⟩

/-- What the loop writes is apart from the frame between `B + 272` and
`B + 544`, where the digest `core` reads is. -/
theorem apart_disj (hL : L.Ok) {r : Region} (h : Apart L r) {d n : Nat} (h₁ : 272 ≤ d) (h₂ : d + n ≤ 544) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := hL.nB
  rcases h with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  · exact hL.stk_SCR (by omega_using [h₂])
  · exact hL.stk_OUT (by omega_using [h₂])
  · exact Offset.disjoint_base _ (by omega_using [h₁]) (by omega_using [h₂])
  · exact Offset.disjoint_base _ (by omega_using [h₁]) (by omega_using [h₂])
  · exact Offset.disjoint_base _ (by omega_using [h₁]) (by omega_using [h₂])
  · exact Offset.disjoint _ (.inl (by simp only [fT]; omega_using [h₂])) (by omega_using [h₂]) (by simp only [fT]; omega_using [])
  · exact Offset.disjoint _ (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by omega_using [])

theorem dgArg_off (P : RfcHash) (L : Lay P.I.hashLen) :
    ∃ d, dgArg P L = L.B + BitVec.ofNat 64 d ∧ 272 ≤ d ∧ d + P.Q ≤ 544 := by
  have := Q_le P
  simp only [dgArg]
  split
  · exact ⟨96 + fXc, rfl, by decide, by simp only [fXc]; omega_using [this]⟩
  · exact ⟨96 + fX, rfl, by decide, by simp only [fX]; omega_using [this]⟩

theorem DgOk.frame (hL : L.Ok) {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Apart L r) : DgOk P L m₀ m' := by
  have := Q_le P
  obtain ⟨d, hd', h₁, h₂⟩ := dgArg_off P L
  unfold DgOk
  rw [bytesAt_frame hf (fun r hr => by rw [hd']; exact apart_disj hL (hd r hr) h₁ h₂) (by omega_using [this])]
  exact h

theorem DgOk.frameA (hL : L.Ok) {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Away L r) : DgOk P L m₀ m' := h.frame hL hf fun r hr => .inl (hd r hr)

theorem cnt_away (hL : L.Ok) {ws : List Region} (hd : ∀ r ∈ ws, Away L r) {m m' : Mem} (hf : Frame ws m m') :
    cnt L m' = cnt L m := by
  have := hL.nB
  refine cnt_frame hf fun r hr => ?_
  rcases hd r hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hL.stk_SCR (by omega_using [])
  · exact hL.stk_OUT (by omega_using [])
  · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
  · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
  · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
  · exact Offset.disjoint _ (.inl (by simp only [fT]; omega_using [])) (by omega_using []) (by simp only [fT]; omega_using [])

theorem kvw_away : ∀ r ∈ KVW L, Away L r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> simp [Away]

theorem cw_away : ∀ r ∈ CW L, Away L r := by
  simp only [CW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [Away]

theorem corew_away : ∀ r ∈ CoreW L, Away L r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [Away]

/-- `K` and `V`, kept by memory that changed elsewhere than `[B + 128, B + 256)`. -/
theorem kv_keep {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 256 → Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r) :
    kOf P L m' = kOf P L m ∧ vOf P L m' = vOf P L m := by
  have hD := P.sizes.2.2.2.2.1
  exact ⟨bytesAt_frame hf (fun r hr => hd r hr (d := 128) (n := P.v.H.D) (by omega_using []) (by omega_using [hD])) (by omega_using [hD]),
    bytesAt_frame hf (fun r hr => hd r hr (d := 192) (n := P.v.H.D) (by omega_using []) (by omega_using [hD])) (by omega_using [hD])⟩

theorem corew_kv (hL : L.Ok) : ∀ r ∈ CoreW L, ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 256 →
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := hL.nB
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) d n h₁ h₂
  · exact hL.stk_OUT (by omega_using [h₂])
  · exact hL.stk_SCR (by omega_using [h₂])
  · exact Offset.disjoint_base _ (by omega_using [h₁]) (by omega_using [h₂])

theorem cntw_kv (hL : L.Ok) : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 264, 8⟩ : Region)], ∀ {d n : Nat}, 128 ≤ d →
    d + n ≤ 256 → Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := hL.nB
  simp only [List.mem_singleton]
  rintro r rfl d n h₁ h₂
  exact Offset.disjoint _ (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by omega_using [])

/-- `out`, kept by memory that changed elsewhere. -/
theorem out_keep {ws : List Region} {m m' : Mem} (hL : L.Ok) (hq : L.q = P.Q) (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint L.OUT r) :
    Spec.Sha256.bytesAt m' L.out (2 * P.Q) = Spec.Sha256.bytesAt m L.out (2 * P.Q) :=
  bytesAt_frame hf (fun r hr => by have := hd r hr; simp only [Lay.OUT, hq] at this; exact this)
    (by have := Q_le P; have := hL.no; rw [hq] at this; omega_arith)

theorem ResultIs.keep {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs P L r t)
    (ha : (t'.gpr .r3).setWidth 32 = (t.gpr .r3).setWidth 32)
    (hm : Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = Spec.Sha256.bytesAt t.mem L.out (2 * P.Q)) :
    ResultIs P L r t' := by
  cases r with
  | none => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩
  | some rs => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

/-! ## `core` -/

/-- The signature `core` computes from the private key, its digest and `k`. -/
abbrev coreSig (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.R.C.E.curve (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m L.d P.Q))
    (Spec.Ecdsa.hashToInt P.R.C.E.curve (Spec.Sha256.bytesAt m (dgArg P L) P.Q))
    (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m (kArg P L) P.Q))

theorem kArg_off (P : RfcHash) (L : Lay P.I.hashLen) :
    kArg P L = L.B + BitVec.ofNat 64 (96 + fT) ∧ 128 ≤ 96 + fT ∧ 96 + fT + P.Q ≤ 688 := by
  have := Q_le P; exact ⟨rfl, by decide, by simp only [fT]; omega_using [this]⟩

/-- `core`'s tables, as its contract asks. -/
theorem core_tables (hL : L.Ok) (hq : L.q = P.Q) (hcs : L.cs = P.R.C.cs) {t : State} (hc : Ctx L g lr m₀ t) :
    CoreTables P.R.C.cs t ⟨L.out, 2 * P.R.C.E.curve.len⟩ L.scr := by
  have eQ : P.R.C.E.curve.len = L.q := hq.symm
  obtain eO : (⟨L.out, 2 * P.R.C.E.curve.len⟩ : Region) = L.OUT := by rw [eQ]
  rw [eO, ← hcs]
  refine ⟨hc.held_now hL, fun T hT => ?_⟩
  rw [hc.tbls] at hT
  obtain ⟨hn, tO, tS, -, al⟩ := hL.tables T hT
  exact ⟨hn, tO, tS, al⟩

/-- The call of `core`: it writes the signature of the private key, its
digest and `k`, or zeros, and changes only `out`, `scratch` and the calls'
stack. -/
theorem core_ok (hL : L.Ok) (hq : L.q = P.Q) (hcs : L.cs = P.R.C.cs) {t : State} (hc : Ctx L g lr m₀ t)
    (h3 : t.gpr .r3 = L.out) (h4 : t.gpr .r4 = L.d) (h5 : t.gpr .r5 = dgArg P L) (h6 : t.gpr .r6 = kArg P L)
    (h7 : t.gpr .r7 = L.scr) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun u => Ctx L g lr m₀ u ∧ Frame (CoreW L) t.mem u.mem ∧
      ResultIs P L (coreSig P L t.mem) u := by
  have hnB := hL.nB
  obtain hQ := Q_le P
  obtain ⟨dd, hdd, d₁, d₂⟩ := dgArg_off P L
  obtain ⟨hkk, k₁, k₂⟩ := kArg_off P L
  have eQ : P.R.C.E.curve.len = L.q := hq.symm
  obtain stk : ∀ {d : Nat}, 128 ≤ d → d + P.Q ≤ 688 → (L.B + BitVec.ofNat 64 d).toNat + P.Q ≤ 2 ^ 64 ∧
      Region.Disjoint L.OUT ⟨L.B + BitVec.ofNat 64 d, P.Q⟩ ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, P.Q⟩ L.SCR ∧
      ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨L.B + BitVec.ofNat 64 d, P.Q⟩ R := fun h₁ h₂ =>
    ⟨by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega_using [hnB, h₂] : _ < 2 ^ 64), Nat.mod_eq_of_lt (by omega_using [h₂])]; omega_using [hnB, h₂],
      (hL.stk_OUT (by omega_using [h₂])).symm, hL.stk_SCR (by omega_using [h₂]), L.FR, by simp, within_fr _ h₁ h₂⟩
  obtain ⟨gn, go, gs, gw⟩ := stk (by omega_using [d₁]) (by omega_using [d₂] : dd + P.Q ≤ 688)
  obtain ⟨kn, ko, ks, kw⟩ := stk k₁ k₂
  rw [← hdd] at gn go gs gw
  rw [← hkk] at kn ko ks kw
  obtain eO : (⟨L.out, 2 * P.R.C.E.curve.len⟩ : Region) = L.OUT := by rw [eQ]
  obtain eD : (⟨L.d, P.R.C.E.curve.len⟩ : Region) = L.D := by rw [eQ]
  refine WP.of_syms (coreCall P.R.C h3 h4 h5 h6 h7 (by rw [eO, eD]; exact hL.od) (by rw [eO]; exact go)
    (by rw [eO]; exact ko) (by rw [eO]; exact hL.oc) (by rw [eD]; exact hL.dc) gs ks
    (by rw [eQ]; exact hL.no) (by rw [eQ]; exact hL.nd) gn kn hL.nc ?_ ?_ ?_ ?_)
  · exact core_tables hL hq hcs hc
  · rw [eO, eD, ← hcs, hc.tbls]
    refine hc.coversT fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ((rfl | rfl | rfl) | hT) | (rfl | rfl)
    · exact .inl ⟨L.D, by simp, within_base _ (Nat.le_refl _)⟩
    · exact .inl gw
    · exact .inl kw
    · exact .inr hT
    · exact .inl ⟨L.OUT, by simp, within_base _ (Nat.le_refl _)⟩
    · exact .inl ⟨L.SCR, by simp, within_base _ (Nat.le_refl _)⟩
  · rw [eO]
    refine hc.coversW fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (Nat.le_refl _)⟩
    · exact ⟨L.SCR, by simp, within_base _ (Nat.le_refl _)⟩
  · intro s' hrd hwr hsp hf hcs hres hsy
    rw [hc.sp, Lay.below96, eO] at hf
    have hf' : Frame (CoreW L) t.mem s'.mem := hf
    refine ⟨hc.keep hL hrd hwr hsp hcs hf' (by
      simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact .inl fun _ h => h
      · exact .inr (.inl fun _ h => h)
      · exact .inr (.inr (.inl (Region.sub_prefix (by omega_using []))))) hsy, hf', ?_⟩
    simp only [Proof.Ecdsa.Rfc6979.ecdsa_bytesAt] at hres
    unfold ResultIs
    exact hres

/-! ## One candidate -/

/-- After the candidate: `k` for `core`. -/
structure P₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 64 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  kk : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kArg P L) P.Q) =
    Spec.Ecdsa.Rfc6979.bits2int P.R.C.E.curve (candI P L m₀ i)

/-- `core`'s arguments. -/
structure Args (P : RfcHash) {dn : Nat} (L : Lay dn) (u : State) : Prop where
  r3 : u.gpr .r3 = L.out
  r4 : u.gpr .r4 = L.d
  r5 : u.gpr .r5 = dgArg P L
  r6 : u.gpr .r6 = kArg P L
  r7 : u.gpr .r7 = L.scr

/-- After `core`: its result. -/
structure P₃ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 64 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u

/-- After the decision: whether to go on. -/
structure Mid (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 64 (P.I.tries - (i + 1))
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u
  dec : isa.eval (.nonzero .d .r12) u = some (decide (sigI P L m₀ i = none ∧ i + 1 < P.I.tries))

theorem try₁_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g lr m₀ u ∧ P₁ P L m₀ i u :=
  WP.mono (cand_ok hL hq.2.1 hc hi.saved) fun _ ⟨hc₁, hf₁, hk₁, hv₁, hb₁, _⟩ => ⟨hc₁, hi.lt, hk₁.trans hi.k,
    by rw [hv₁, hi.k, hi.v], (cnt_away hL cw_away hf₁).trans hi.cnt, hi.fails,
    hi.dg.frameA hL hf₁ cw_away, by rw [hb₁, hi.k, hi.v]; rfl⟩

theorem try₂_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat} (hi : P₁ P L m₀ i t) :
    WP isa (.block (cfgOf P).coreArgs) t fun u => Ctx L g lr m₀ u ∧ P₁ P L m₀ i u ∧ Args P L u :=
  WP.mono (coreArgs_ok hL hc) fun _ ⟨hc₂, hm₂, _, h3, h4, h5, h6, h7⟩ =>
    ⟨hc₂, ⟨hi.lt, hm₂ ▸ hi.k, hm₂ ▸ hi.v, hm₂ ▸ hi.cnt, hi.fails, hm₂ ▸ hi.dg, hm₂ ▸ hi.kk⟩, h3, h4, h5, h6, h7⟩

/-- `core`'s signature is the candidate's. -/
theorem coreSig_eq (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g lr m₀ t) (hdg : DgOk P L m₀ t.mem)
    {i : Nat} (hkv : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (kArg P L) P.Q) =
      Spec.Ecdsa.Rfc6979.bits2int P.R.C.E.curve (candI P L m₀ i)) : coreSig P L t.mem = sigI P L m₀ i := by
  simp only [coreSig, sigI, xOf]
  rw [hc.dBytes hL hq, hkv]
  exact congrArg (fun e => Spec.Ecdsa.signWith _ _ e _) hdg

theorem try₃_ok (hL : L.Ok) (hq : L.q = P.Q) (hcs : L.cs = P.R.C.cs) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : P₁ P L m₀ i t) (ha : Args P L t) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun u => Ctx L g lr m₀ u ∧ P₃ P L m₀ i u := by
  refine WP.mono (core_ok hL hq hcs hc ha.r3 ha.r4 ha.r5 ha.r6 ha.r7) fun u₃ ⟨hc₃, hf₃, hr₃⟩ => ?_
  rw [coreSig_eq hL hq hc hi.dg hi.kk] at hr₃
  obtain ⟨ek, ev⟩ := kv_keep (P := P) hf₃ (corew_kv hL)
  exact ⟨hc₃, hi.lt, ek.trans hi.k, ev.trans hi.v, (cnt_away hL corew_away hf₃).trans hi.cnt, hi.fails,
    hi.dg.frameA hL hf₃ corew_away, hr₃⟩

theorem and_one_of {x : BitVec 64} {b : BitVec 32} (h : x.setWidth 32 = b) (hb : b.toNat ≤ 1) :
    x &&& 1 = BitVec.ofNat 64 b.toNat :=
  BitVec.eq_of_toNat_eq (by
    obtain e := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth] at e
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega_using [hb, e])

theorem cnt_sub {T i : Nat} (hi : i < T) :
    BitVec.ofNat 64 (T - i) - 1 = BitVec.ofNat 64 (T - (i + 1)) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega_using [hi])

theorem try₄_ok (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat} (hi : P₃ P L m₀ i t) :
    WP isa (.block Cfg.goOn) t fun u => Ctx L g lr m₀ u ∧ Mid P L m₀ i u := by
  have hT := P.tries_lt
  refine WP.mono (goOn_ok hL hc) fun u ⟨hcu, K, hf, hcnt, h12⟩ => ?_
  obtain ⟨ek, ev⟩ := kv_keep (P := P) hf (cntw_kv hL)
  obtain hc3 : (u.gpr .r3).setWidth 32 = (t.gpr .r3).setWidth 32 := by rw [K.gpr _ (by decide)]
  obtain hout := out_keep (P := P) hL hq hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_OUT (by omega_using [])).symm)
  refine ⟨hcu, hi.lt, ek.trans hi.k, ev.trans hi.v, by rw [hcnt, hi.cnt, cnt_sub hi.lt], hi.fails,
    hi.dg.frame hL hf (fun r hr => by simp only [List.mem_singleton] at hr; exact .inr hr),
    hi.res.keep hc3 hout, ?_⟩
  rw [eval_nonzero, h12, hi.cnt, cnt_sub hi.lt]
  have hres := hi.res
  unfold ResultIs at hres
  cases hs : sigI P L m₀ i <;> rw [hs] at hres
  · rw [and_one_of hres.1 (by decide)]
    have : (BitVec.ofNat 64 (BitVec.toNat (0 : BitVec 32)) - 1 &&& BitVec.ofNat 64 (P.I.tries - (i + 1))) =
        BitVec.ofNat 64 (P.I.tries - (i + 1)) := by
      rw [show BitVec.ofNat 64 (BitVec.toNat (0 : BitVec 32)) - 1 = BitVec.allOnes 64 from rfl, BitVec.allOnes_and]
    rw [this, bne, ofNat_beq_zero (by omega_using [hT])]
    simp only [true_and, Option.some.injEq]
    rw [← decide_not]
    exact decide_eq_decide.mpr ⟨fun h => by omega_using [h], fun h => by omega_using [h]⟩
  · rw [and_one_of hres.1 (by decide)]
    simp

/-- The branch: step h.3 and the next candidate, or the end. -/
theorem branch_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : Mid P L m₀ i t) :
    WP isa (.ite (.nonzero .d .r12) (.seq (cfgOf P).rekey (.block Cfg.again)) (.block Cfg.stop)) t fun t' =>
      Ctx L g lr m₀ t' ∧
      ((isa.eval (.nonzero .d .r12) t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval (.nonzero .d .r12) t' = some true ∧ LoopInv P L m₀ (i + 1) t')) := by
  by_cases hgo : sigI P L m₀ i = none ∧ i + 1 < P.I.tries
  · refine WP.ite true (by rw [hi.dec, decide_eq_true hgo]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono (rekey_ok hL hq hc) fun u₅ ⟨hc₅, hf₅, hk₅, hv₅, hS₅⟩ => ?_)
    refine again_ok fun u₆ k₆ m₆ v₆ s₆ => ⟨hc₅.kp hL k₆ m₆ s₆, .inr ⟨by rw [eval_nonzero, v₆]; rfl, ?_⟩⟩
    have hkv : kvI P L m₀ (i + 1) = stepB P.v.ok.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2 := rfl
    refine ⟨hgo.2, ?_, ?_, ?_, fun j hj => ?_, ?_, by rw [m₆]; exact hS₅⟩
    · rw [m₆, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [m₆, hv₅, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [m₆, cnt_away hL kvw_away hf₅, hi.cnt]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hi.fails j hj
      · exact hgo.1
    · rw [m₆]; exact hi.dg.frameA hL hf₅ kvw_away
  · refine WP.ite false (by rw [hi.dec, decide_eq_false hgo]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine stop_ok fun u₅ k₅ m₅ v₅ s₅ => ⟨hc.kp hL k₅ m₅ s₅, .inl ⟨by rw [eval_nonzero, v₅]; rfl,
      ⟨hi.lt, hi.fails, ?_, hi.res.keep (by rw [k₅.gpr _ (by decide)]) (by rw [m₅])⟩⟩⟩
    by_cases hs : sigI P L m₀ i = none
    · exact .inr (by have := hi.lt; have : ¬ i + 1 < P.I.tries := fun h => hgo ⟨hs, h⟩; omega_arith)
    · exact .inl hs

theorem tryOne_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).tryOne t fun t' => Ctx L g lr m₀ t' ∧
      ((isa.eval (.nonzero .d .r12) t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval (.nonzero .d .r12) t' = some true ∧ LoopInv P L m₀ (i + 1) t')) :=
  WP.seq (WP.mono (try₁_ok hL hq hc hi) fun _ ⟨h₁, p₁⟩ =>
    WP.seq (WP.mono (try₂_ok hL h₁ p₁) fun _ ⟨h₂, p₂, a₂⟩ =>
      WP.seq (WP.mono (try₃_ok hL hq.1 hq.2.2 h₂ p₂ a₂) fun _ ⟨h₃, p₃⟩ =>
        WP.seq (WP.mono (try₄_ok hL hq.1 h₃ p₃) fun _ ⟨h₄, p₄⟩ => branch_ok hL hq h₄ p₄))))

theorem tries_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne (.nonzero .d .r12)) t fun t' => Ctx L g lr m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g lr m₀ s ∧ LoopInv P L m₀ (P.I.tries - n) s ∧
    n ≤ P.I.tries) ?_ P.I.tries t ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  obtain hn1 : 1 ≤ n := by have := hi.lt; omega_using [this]
  refine WP.mono (tryOne_ok hL hq hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega_using [hn1], hc', ?_, by omega_using [hn]⟩
    rwa [show P.I.tries - (n - 1) = P.I.tries - n + 1 by omega_using [hn, hn1]]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE

end

end


/-!
# Deterministic ECDSA on PPC64LE: correctness

The loop leaves it at a candidate that is suitable or the last
(`tries_ok`); before it, `h`, `K`, `V`, `core`'s digest and the count are
as RFC 6979's steps a–g make them (`stageX_ok` … `stageE_ok`); and the
signature of that candidate is RFC 6979's (`result_eq`), for the hash
function `P`'s instance of the contract, with the frames pushed and popped
around the body (`sign_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp wp_step)
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB rlenR hashToInt_takeQ hashToInt_short hashToInt_takeR
  bits2octets_short ofBytes_zeros ofBytes_lt ofBytes_toBytes toBytes_ofBytes)
open VG.Proof.Hmac.Common (bytesAt_length)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-! ## Steps a–g -/

theorem RfcCurve.n_ne (R : RfcCurve) : R.C.E.curve.n ≠ 0 := Nat.pos_iff_ne_zero.mp R.n_pos

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.C.E.curve = P.Q :=
  rlenR (nBits_len P).2 (nBits_len P).1

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : RfcHash) {x : Nat} {dB hB h : List Byte} (hd : dB.length = P.Q)
    (hx : x = Spec.Weierstrass.ofBytes dB) (hh : Spec.Ecdsa.Rfc6979.bits2octets P.R.C.E.curve hB = h) :
    Spec.Ecdsa.Rfc6979.init P.R.C.E.curve P.v.ok.SH.H P.v.H.D x hB =
      let K₁ := P.mac (List.replicate P.v.H.D 0) (List.replicate P.v.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.v.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  obtain hi : Spec.Ecdsa.Rfc6979.int2octets P.R.C.E.curve x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_eq, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.C.E.curve (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.v.H.D 0) (List.replicate P.v.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (K₁ P L m₀) (List.replicate P.v.H.D 1)

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (bytesAt_length _ _ _) rfl rfl

/-- The digest's integer is `X`'s, `Q - m` zero bytes then the digest's first
`m = min(D, Q)`, if the scalars have `8 Q` bits. -/
theorem x_eq {C : Spec.Weierstrass.Curve} {Q D : Nat} (hq : Spec.Ecdsa.nBits C = 8 * Q) (hn : C.n ≠ 0)
    {hB : List Byte} (hl : hB.length = D) :
    Spec.Weierstrass.ofBytes (List.replicate (Q - min D Q) 0 ++ hB.take (min D Q)) = Spec.Ecdsa.hashToInt C hB := by
  by_cases h : Q ≤ D
  · rw [Nat.min_eq_right h, Nat.sub_self, List.replicate_zero, List.nil_append,
      hashToInt_takeQ hq (by rw [hl]; exact h)]
  · rw [Nat.min_eq_left (by omega_using [h]), List.take_of_length_le (by rw [hl]), ofBytes_zeros,
      (hashToInt_short (by rw [hl, hq]; omega_using [h]) hn).1]

theorem Ctx.dgBytes (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {n : Nat} (hn : n ≤ P.I.hashLen) :
    Spec.Sha256.bytesAt t.mem L.dg n = Spec.Sha256.bytesAt m₀ L.dg n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (by have := List.mem_range.mp hi; omega_using [hn, this])

/-- `h`, kept by memory that changed apart from it. -/
theorem hOf_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, ∀ {d n : Nat}, 328 ≤ d → d + n ≤ 472 → Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r) :
    hOf P L m' = hOf P L m := by
  have := fHo_le P
  exact bytesAt_frame hf (fun r hr => hd r hr (by omega_using [this]) (by omega_using [this])) (by have := Q_le P; omega_arith)

/-- `core`'s digest, kept by memory that changed apart from it. -/
theorem DgOk.frameD {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, ∀ {d n : Nat}, 272 ≤ d → d + n ≤ 544 → Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r) :
    DgOk P L m₀ m' := by
  have := Q_le P
  obtain ⟨d, hd', h₁, h₂⟩ := dgArg_off P L
  unfold DgOk
  rw [bytesAt_frame hf (fun r hr => by rw [hd']; exact hd r hr h₁ h₂) (by omega_using [this])]
  exact h

/-- After `X` and `h`: `h`, and `core`'s digest. -/
structure QA (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  dg : DgOk P L m₀ u.mem

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.v.H.D 0
  v : vOf P L u.mem = List.replicate P.v.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)
  /-- `d ‖ h`, after the message's first byte. -/
  tail : tailOf P L u.mem = Spec.Sha256.bytesAt m₀ L.d P.Q ++ hSpec P L m₀

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)

/-- After `X`: `Q - m` zero bytes, then the digest's first `m = min(D, Q)`. -/
abbrev QX (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop :=
  Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + fX)) P.Q =
    List.replicate (P.Q - min P.v.H.D P.Q) 0 ++ (hBOf P L m₀).take (min P.v.H.D P.Q)

theorem stageX_ok (hL : L.Ok) (hq : HOk P L) {u : State} (hc : Ctx L g lr m₀ u) :
    WP isa (cfgOf P).prepX u fun u' => Ctx L g lr m₀ u' ∧ QX P L m₀ u' := by
  have hD : P.v.H.D = P.I.hashLen := P.len.symm
  obtain hdg : Spec.Sha256.bytesAt u.mem L.dg (min P.v.H.D P.Q) = (hBOf P L m₀).take (min P.v.H.D P.Q) := by
    rw [hc.dgBytes hL (by rw [← hD]; omega_using []), hBOf, ← bytesAt_take _ _ (Nat.min_le_left _ _)]
  exact WP.mono (prepX_ok hL hq.2.1 (by rw [← hD]) hc) fun u₁ ⟨hc₁, _, hx₁⟩ =>
    ⟨hc₁, by show Spec.Sha256.bytesAt _ _ _ = _; rw [hx₁, hdg]⟩

theorem fHo_small (h : P.R.big = false) : (cfgOf P).fHo = fH := by
  simp only [Cfg.fHo, show (cfgOf P).big = false from h, Bool.false_eq_true, ite_false]

theorem fHo_big (h : P.R.big = true) : (cfgOf P).fHo = fX := by
  simp only [Cfg.fHo, show (cfgOf P).big = true from h, ite_true]

/-- `h` (step c's `h1` as `bits2octets`), and `core`'s digest. -/
theorem stageH_ok (hL : L.Ok) (hq : HOk P L) {u₁ : State} (hc₁ : Ctx L g lr m₀ u₁) (hx₁ : QX P L m₀ u₁) :
    WP isa (cfgOf P).prepH u₁ fun u' => Ctx L g lr m₀ u' ∧ QA P L m₀ u' := by
  have hD : P.v.H.D = P.I.hashLen := P.len.symm
  obtain hl := nBits_len P
  have hs := P.sizes
  obtain hlB : (hBOf P L m₀).length = P.v.H.D := bytesAt_length _ _ _
  have hnB := hL.nB
  unfold QX at hx₁
  cases hb : P.R.big
  · obtain ⟨hQ5, -, hq8, hn2⟩ := P.R.sizesA hb
    have hq' : Spec.Ecdsa.nBits P.R.C.E.curve = 8 * P.Q := hq8
    obtain hk4 : (cfgOf P).len = 4 * (P.Q / 4) := by
      show P.R.Q = _; simp only [RfcHash.Q] at *; omega_using [hQ5]
    obtain hk16 : P.Q / 4 ≤ 16 := by simp only [RfcHash.Q] at *; omega_using [hs]
    obtain e32 : 32 * (P.Q / 4) = 8 * P.Q := by simp only [RfcHash.Q] at *; omega_using [hQ5]
    obtain hn₁ : (cfgOf P).n < 2 ^ (32 * (P.Q / 4)) := by
      show P.R.C.E.curve.n < _
      rw [e32, ← hq', Spec.Ecdsa.nBits]; exact Nat.lt_log2_self
    obtain hn₂ : 2 ^ (32 * (P.Q / 4)) < 2 * (cfgOf P).n := by rw [e32]; exact hn2
    obtain hX : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (xA L) P.Q) = eOf P L m₀ := by
      rw [show xA L = L.B + BitVec.ofNat 64 (96 + fX) from rfl, hx₁, x_eq hq' P.R.n_ne hlB]
    rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by
      simp only [Cfg.prepH, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    refine WP.mono (reduce_ok hL hk4 hk16 hn₁ hn₂ hc₁) fun u₂ ⟨hc₂, hf₂, hh₂⟩ => ⟨hc₂, ?_, ?_⟩
    · have e4 : 4 * (P.Q / 4) = P.Q := by simp only [RfcHash.Q] at *; omega_using [hQ5]
      rw [e4, show (cfgOf P).n = P.R.C.E.curve.n from rfl, hX] at hh₂
      show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (96 + (cfgOf P).fHo)) P.Q = _
      rw [fHo_small hb, ← toBytes_ofBytes (Spec.Sha256.bytesAt u₂.mem _ P.Q), bytesAt_length, hh₂, hSpec,
        Spec.Ecdsa.Rfc6979.bits2octets, Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlen_eq]
    · unfold DgOk
      simp only [dgArg, hb, Bool.false_eq_true, ite_false]
      obtain hQ64 : P.Q ≤ 64 := by simp only [RfcHash.Q] at *; omega_using [hQ5]
      rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (.inr (by simp only [fX]; omega_using [])) (by simp only [fX]; omega_using [hs]) (by omega_using [])
          · exact Offset.disjoint _ (.inr (by simp only [fX]; omega_using [])) (by simp only [fX]; omega_using [hs])
              (by omega_using [])) (by omega_using [hs]),
        hashToInt_takeQ hq' (by rw [bytesAt_length]), List.take_of_length_le (by rw [bytesAt_length])]
      exact hX
  · obtain ⟨-, hQ66', hQD⟩ := P.R.sizesW hb
    have hQ66 : P.Q = 66 := hQ66'
    obtain hN : 8 * P.v.H.D < Spec.Ecdsa.nBits P.R.C.E.curve := by rw [hQD]; omega_using [hs]
    obtain hm : min P.v.H.D P.Q = P.v.H.D := Nat.min_eq_left (by omega_using [hs, hQ66])
    rw [hm, List.take_of_length_le (by rw [hlB])] at hx₁
    rw [show (cfgOf P).prepH = (cfgOf P).prepC by
      simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true]]
    refine WP.mono (prepC_ok hL hq.2.1 hb (by rw [← hD]) hc₁) fun u₂ ⟨hc₂, hf₂, hx₂⟩ => ⟨hc₂, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (96 + (cfgOf P).fHo)) P.Q = _
      rw [fHo_big hb, bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_scr (by simp only [fX]; omega_using [hs]) (by decide)
          · exact Offset.disjoint _ (.inl (by simp only [fX, fXc]; omega_using [hs])) (by simp only [fX]; omega_using [hs])
              (by simp only [fXc]; omega_using [])) (by omega_using [hs]),
        hx₁, hSpec, bits2octets_short (R := P.Q) hl.2 hl.1 (by rw [hlB]; exact hN) P.R.n_ne, hlB]
    · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
      obtain e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (hBOf P L m₀) :=
        (hashToInt_short (by rw [hlB]; exact hN) P.R.n_ne).1
      rw [hc₁.dgBytes hL (by rw [← hD])] at hx₂
      obtain hsh : P.R.sh = 7 := P.R.sh7 hb
      obtain hlt : Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh < 2 ^ (8 * P.Q) := by
        have := ofBytes_lt (hBOf P L m₀)
        rw [hlB] at this
        calc _ < 2 ^ (8 * P.v.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by
            rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega_using []) (by omega_using [hs, hQ66, hsh])
      obtain hl₁ : (Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh)).length =
          P.Q := by simp [Spec.Weierstrass.toBytes]
      unfold DgOk
      simp only [dgArg, hb, ite_true]
      rw [hx₂, hashToInt_takeR (R := P.Q) hl.2 (by rw [hl₁]),
        List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.C.E.curve = P.R.sh from P.R.sh_eq.symm, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _), e₂]

theorem kvw_h (hL : L.Ok) : ∀ r ∈ KVW L, ∀ {d n : Nat}, 328 ≤ d → d + n ≤ 472 →
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := hL.nB
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) d n h₁ h₂
  · exact hL.stk_SCR (by omega_using [h₂])
  · exact Offset.disjoint_base _ (by omega_using [h₁]) (by omega_using [h₂])

/-- `V = 0x01…` and `K = 0x00…`. -/
theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g lr m₀ u) (hq : QA P L m₀ u) :
    WP isa Cfg.initKV u fun u' => Ctx L g lr m₀ u' ∧ QB P L m₀ u' := by
  have hs := P.sizes
  have := hL.nB
  obtain kv : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 128, 128⟩ : Region)], ∀ {d n : Nat}, 256 ≤ d → d + n ≤ 736 →
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := fun r hr d n h₁ h₂ => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by omega_using [])
  exact WP.mono (initKV_ok hL hc) fun u₂ ⟨hc₂, hf₂, hkv₂⟩ =>
    ⟨hc₂, ⟨(hOf_frame hf₂ fun r hr _ _ h₁ h₂ => kv r hr (by omega_using [h₁]) (by omega_using [h₂])).trans hq.h,
      (hkv₂ _ (by omega_using [hs])).2, (hkv₂ _ (by omega_using [hs])).1,
      hq.dg.frameD hf₂ fun r hr _ _ h₁ h₂ => kv r hr (by omega_using [h₁]) (by omega_using [h₂])⟩⟩

theorem stageC_ok (hL : L.Ok) (hq : HOk P L) {u : State} (hc : Ctx L g lr m₀ u) (hb : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g lr m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hq hc 0 (by decide) (fun h => absurd rfl h) fun h => absurd rfl h)
    fun u' ⟨hc', hf', hk', hv', hS', ht'⟩ =>
    ⟨hc', (hOf_frame hf' (kvw_h hL)).trans hb.h,
      by rw [hk', hb.k, hb.v, hb.h, hc.dBytes hL hq.1],
      by rw [hv', hk', hb.k, hb.v, hb.h, hc.dBytes hL hq.1], hb.dg.frameA hL hf' kvw_away, hS',
      by rw [ht', hb.h, hc.dBytes hL hq.1]⟩

theorem stageD_ok (hL : L.Ok) (hq : HOk P L) {u : State} (hc : Ctx L g lr m₀ u) (hb : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g lr m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hq hc 1 (by decide) (fun _ => hb.saved)
    fun _ => by rw [hb.tail, hb.h, hc.dBytes hL hq.1]) fun u' ⟨hc', hf', hk', hv', hS', _⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hb.k, hb.v, hb.h, hc.dBytes hL hq.1],
      by rw [kv0_eq', hv', hk', hb.k, hb.v, hb.h, hc.dBytes hL hq.1], hb.dg.frameA hL hf' kvw_away, hS'⟩

theorem stageE_ok (hL : L.Ok) {u : State} (hc : Ctx L g lr m₀ u) (hb : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g lr m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL P.tries_lt hc) fun u' ⟨hc', hf', hn'⟩ => by
    obtain ⟨ek, ev⟩ := kv_keep (P := P) hf' (cntw_kv hL)
    refine ⟨hc', P.tries_pos, ek.trans hb.k, ev.trans hb.v, by rw [hn', Nat.sub_zero]; rfl,
      fun j hj => absurd hj (Nat.not_lt_zero _), hb.dg.frame hL hf' (fun r hr => by
        simp only [List.mem_singleton] at hr; exact .inr hr), ?_⟩
    rw [ek]
    exact hb.saved.frame (blockKey_length (bytesAt_length _ _ _)) hf' fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_scr (by omega_using []) (by decide)).symm

theorem stageG_ok (hL : L.Ok) (hq : HOk P L) {u : State} (hc : Ctx L g lr m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa Cfg.wipe u fun u' => Ctx L g lr m₀ u' ∧ Exit P L m₀ i u' :=
  WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, K₇, hf₇⟩ => ⟨hc₇, hx.lt, hx.fails, hx.last,
    hx.res.keep (by rw [K₇.gpr _ (by decide)]) (out_keep (P := P) hL hq.1 hf₇ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega_using [])).symm
      · exact (hL.stk_OUT (by omega_using [])).symm)⟩

/-- The body after the arguments are saved. -/
theorem rest_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.seq (cfgOf P).prepX (.seq (cfgOf P).prepH (.seq Cfg.initKV (.seq ((cfgOf P).rekeyFull 0)
      (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne (.nonzero .d .r12)) Cfg.wipe))))))) t
      fun t' => Ctx L g lr m₀ t' ∧ ∃ i, Exit P L m₀ i t' :=
  WP.seq (WP.mono (stageX_ok hL hq hc) fun _ ⟨h₀, q₀⟩ =>
    WP.seq (WP.mono (stageH_ok hL hq h₀ q₀) fun _ ⟨h₁, q₁⟩ =>
    WP.seq (WP.mono (stageB_ok hL h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
      WP.seq (WP.mono (stageC_ok hL hq h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
        WP.seq (WP.mono (stageD_ok hL hq h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
          WP.seq (WP.mono (stageE_ok hL h₄ q₄) fun _ ⟨h₅, q₅⟩ =>
            WP.seq (WP.mono (tries_ok hL hq h₅ q₅) fun _ ⟨h₆, i, q₆⟩ =>
              WP.mono (stageG_ok hL hq h₆ q₆) fun _ ⟨h₇, q₇⟩ => ⟨h₇, i, q₇⟩)))))))

/-! ## RFC 6979's result -/

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.C.E.curve.n then
        Spec.Ecdsa.Rfc6979.search P.R.C.E.curve P.v.ok.SH.H P.v.H.D (xOf P L m₀) (eOf P L m₀)
          (kv0 P L m₀).1 (kv0 P L m₀).2 P.I.tries
      else (none, 0) := by
  simp only [result, Proof.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.sign, P.ecdsa, P.hash, P.len,
    Proof.Ecdsa.Rfc6979.ecdsa_bytesAt]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.C.E.curve.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (nV_eq P) i P.I.tries (by have := hx.lt; omega_using [this]) hx.fails,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by have := hx.lt; omega_using [this]]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (nV_eq P) hs]
    | none =>
      obtain h7 : i + 1 = P.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (nV_eq P) hs, show P.I.tries - 1 - i = 0 by omega_using [h7]]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-! ## The whole function -/

/-- The contract the code for `P`'s hash function is proven against, with
`P`'s table and the functions `ns`' addresses public. -/
abbrev rfcP (P : RfcHash) (ns : List String) : Contract isa :=
  rfcPPC P.I 736 (tabFacts P.v P.f) ns P.R.C.cs

/-- The layout of a call from `s`. -/
abbrev layOf (P : RfcHash) (s : State) : Lay P.I.hashLen := lay P.I.hashLen P.I.ecdsa.curve.len P.v P.f s P.R.C.cs

theorem hok_lay (P : RfcHash) (s : State) : HOk P (layOf P s) :=
  ⟨show P.I.ecdsa.curve.len = P.R.C.E.curve.len by rw [P.ecdsa], ⟨rfl, rfl⟩, rfl⟩

theorem freed_mem (n : Nat) (u : State) : (freed n u).mem = u.mem := rfl
theorem freed_sp (n : Nat) (u : State) : (freed n u).sp = u.sp + BitVec.ofNat 64 n := rfl
theorem freed_gpr (n : Nat) (u : State) : (freed n u).gpr = u.gpr := rfl
theorem popped_mem (r : Reg) (u : State) : (popped r u).mem = u.mem := rfl
theorem popped_sp (r : Reg) (u : State) : (popped r u).sp = u.sp + 48 := rfl
theorem popped_gpr (r r' : Reg) (u : State) :
    (popped r u).gpr r' = (u.write r (u.mem.read (u.sp + 32) 8)).gpr r' := rfl

/-- The signature, with the frames: the return address saved in the outer
one, the arguments in the inner one, and both popped. -/
theorem sign_ok {ns : List String} {s : State} (h : (rfcP P ns).pre s) :
    WP isa (cfgOf P).sign s fun s' => abiPreserved s s' ∧ (rfcP P ns).post s s' := by
  obtain hL : (layOf P s).Ok := lay_ok h
  obtain hq := hok_lay P s
  have hsp : 736 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨L, hl⟩ : ∃ L, layOf P s = L := ⟨_, rfl⟩
  obtain hB : s.sp = L.B + BitVec.ofNat 64 736 := by
    rw [← hl]
    show s.sp = s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 736
    rw [BitVec.sub_add_cancel]
  obtain hnB : L.B.toNat + 736 ≤ 2 ^ 64 := by rw [← hl]; exact hL.nB
  rw [Cfg.sign, frameBytes]
  refine WP.seq (wp_step exec_mflr (wp_nil ?_))
  refine WP.seq (WP.frame (by show 48 ≤ s.sp.toNat; omega_using [hsp]) (WP.alloc (by omega_using [])
    (by show 592 ≤ (s.sp - 48).toNat; rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 48 ≤ s.sp.toNat; omega_using [hsp])]
        show 592 ≤ s.sp.toNat - 48; omega_using [hsp]) ?_))
  rw [Cfg.body]
  obtain hent := entry_ok h
  refine WP.seq (WP.mono hent fun t (hc : Ctx (layOf P s) s.gpr s.lr s.mem t) => ?_)
  rw [hl] at hL hq hc
  refine WP.mono (rest_ok hL hq hc) fun u ⟨hcu, i, hx⟩ => ?_
  refine wp_step exec_mtlr (wp_nil ?_)
  have hsu := hcu.sp
  obtain hfm : (freed 592 u).mem = u.mem := freed_mem _ _
  obtain hfs : (freed 592 u).sp = L.B + BitVec.ofNat 64 688 := by rw [freed_sp, hsu, fr_add]
  obtain hpm : (popped .r0 (freed 592 u)).mem = u.mem := by rw [popped_mem, hfm]
  obtain hpg : ∀ r, r ≠ .r0 → (popped .r0 (freed 592 u)).gpr r = u.gpr r := fun r h0 => by
    rw [popped_gpr, Proof.Mont.PPC64LE.write_gpr, freed_gpr]; simp only [h0, ↓reduceIte]
  -- The return address and the stack pointer, as on entry.
  obtain hr0 : (popped .r0 (freed 592 u)).gpr .r0 = s.lr := by
    rw [popped_gpr, Proof.Mont.PPC64LE.write_gpr]; simp only [↓reduceIte]
    rw [hfm, hfs,
      show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, fr_add, read8]
    exact hcu.lr
  refine ⟨⟨fun r hr => ?_, ?_, hr0⟩, ?_⟩
  · rw [hpg r fun e => by subst e; exact absurd hr (by decide)]
    exact hcu.cs r hr
  · rw [popped_sp, hfs, hB, show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, fr_add]
  · have hr := result_eq hx
    obtain h3 : (popped .r0 (freed 592 u)).gpr .r3 = u.gpr .r3 := hpg _ (by decide)
    obtain hd : s.gpr .r4 = L.d := by rw [← hl]; rfl
    obtain hg : s.gpr .r5 = L.dg := by rw [← hl]; rfl
    obtain ho : s.gpr .r3 = L.out := by rw [← hl]; rfl
    obtain hlq : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa]
    generalize popped .r0 (freed 592 u) = v at h3 hpm ⊢
    show match (result P.I s.mem (s.gpr .r4) (s.gpr .r5)).1 with
      | some rs => (v.gpr .r3).setWidth 32 = 1 ∧
          Spec.Ecdsa.bytesAt v.mem (s.gpr .r3) (2 * P.I.ecdsa.curve.len) =
            Spec.Ecdsa.encode P.I.ecdsa.curve rs
      | none => (v.gpr .r3).setWidth 32 = 0 ∧
          Spec.Ecdsa.bytesAt v.mem (s.gpr .r3) (2 * P.I.ecdsa.curve.len) =
            List.replicate (2 * P.I.ecdsa.curve.len) 0
    rw [hd, hg, hr, hpm, h3, ho, hlq, P.ecdsa]
    have := hx.res
    unfold ResultIs at this
    exact this

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
