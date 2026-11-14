module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdCT2
import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
public import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
import VerifiedGarbage.Proof.Rsa.AArch64.RdSqrt
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCT2
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdSqrt
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_recover_primes_det` on AArch64: constant time, from `a` to `b² - 4 n`

`product_ct`: the products' loop, then `aProd`, `divA`, `divB`, `square`
and `minus4n`, each from and to `GC` with no facts.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- No facts about the public data's state. -/
abbrev XN : DP → State → Prop := fun _ _ => True

/-- `setWid`, then `ws` and code the taint analysis checks from `x0`, `x12` and `x11`. -/
theorem setWid_ws_rel {w : Nat → Nat} {X : Pub → State → Prop} {Φ : Pub → State → Prop}
    (hΦ : ∀ a s, Φ a s → GC w X a s) {rest : List Instr} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block rest) hc).isSome = true) :
    RelCT isa (Two Φ) (.block (setWid ++ (ws ++ rest))) fun _ _ => True :=
  RelCT.block_append (RelCT.seq (two_post (Ψ := GC Wk XT) (two_taint [.x0] (pins_GC' hΦ) (by taint_decide))
    fun ⟨P, i⟩ s h => (hΦ _ s h).elim fun I m₀ c e g L _ => by
      subst e
      exact WP.mono (g.setWid_ok L.1) fun t ⟨g', _, _⟩ => ⟨I, m₀, c, rfl, g', L, trivial⟩)
    (ws_blk0 (fun a => a.1.B) (fun a => a.1.Z) (fun a => Wk a.1.k) (fun _ _ h => h.ws) ht))

/-- `setNar`, then `ws` and code the taint analysis checks from `x0`, `x12` and `x11`. -/
theorem setNar_ws_rel {w : Nat → Nat} {X : Pub → State → Prop} {Φ : Pub → State → Prop}
    (hΦ : ∀ a s, Φ a s → GC w X a s) {rest : List Instr} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block rest) hc).isSome = true) :
    RelCT isa (Two Φ) (.block (setNar ++ (ws ++ rest))) fun _ _ => True :=
  RelCT.block_append (RelCT.seq (two_post (Ψ := GC vk XT) (two_taint [.x0] (pins_GC' hΦ) (by taint_decide))
    fun ⟨P, i⟩ s h => (hΦ _ s h).elim fun I m₀ c e g L _ => by
      subst e
      exact WP.mono (g.setNar_ok L.1) fun t ⟨g', _, _⟩ => ⟨I, m₀, c, rfl, g', L, trivial⟩)
    (ws_blk0 (fun a => a.1.B) (fun a => a.1.Z) (fun a => vk a.1.k) (fun _ _ h => h.ws) ht))

/-! ## `a` -/

/-- The accumulator `a` zero. -/
def zA (P : DP) (s : State) : Prop := wv s.mem P.B (slot (Wk P.k) wA) (Wk P.k + 2) = 0

/-- The pins of `aProd`'s rows. -/
def fA (a : Pub) (r : Reg) : BitVec 64 :=
  if r = .x0 then a.1.B else if r = .x8 then off a.1.B (slot (Wk a.1.k) wA)
  else if r = .x9 then off a.1.B (slot (Wk a.1.k) wX) else if r = .x11 then off a.1.B (slot (vk a.1.k) gT)
  else if r = .x12 then BitVec.ofNat 64 (Wk a.1.k) else if r = .x13 then BitVec.ofNat 64 (vk a.1.k) else 0

/-- `aProd`'s rows' head. -/
abbrev apHead : List Instr := setNar ++ ws ++ base gT .x5 ++ setWid ++ ws ++ base wX .x9 ++ base wA .x8 ++
  [mov .x11 .x5, .lsr .x .x13 .x12 1, .subImm .x .x13 .x13 1, movi .x7 0]

theorem apHead_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (g : G I m₀ (Wk I.k) c s) (L : RpLens I)
    (z : zA (dpub I) s) :
    WP isa (.block apHead) s fun t => G I m₀ (Wk I.k) c t ∧ zA (dpub I) t ∧
      ∀ r ∈ [Reg.x0, .x7, .x8, .x9, .x11, .x12, .x13], t.gpr r = fA (dpub I, 0) r := by
  have hk1 := L.k1
  have hk2 := L.k2
  rw [apHead, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (g.setNar_ok L) fun t₃ ⟨g₃, f₃, k₃⟩ => ?_
  refine WP.mono (ws_ok g₃.ws.scr g₃.ws.x0 g₃.ws.h256 g₃.ws.hw g₃.ws.hS) fun t₄ ⟨⟨_, h11₄, m₄, _⟩, k₄⟩ => ?_
  refine WP.mono (base_ok gT .x5 ((k₄.gpr .x0 (by decide)).trans g₃.ws.x0) h11₄) fun t₅ ⟨⟨h5₅, m₅, _⟩, k₅⟩ => ?_
  have g₅ := g₃.same (by rw [m₅, m₄]) (k₄.trans k₅) (by decide)
  refine WP.mono (g₅.setWid_ok L) fun t₆ ⟨g₆, f₆, k₆⟩ => ?_
  refine WP.mono (ws_ok g₆.ws.scr g₆.ws.x0 g₆.ws.h256 g₆.ws.hw g₆.ws.hS) fun t₇ ⟨⟨h12₇, h11₇, m₇, _⟩, k₇⟩ => ?_
  refine WP.mono (base_ok wX .x9 ((k₇.gpr .x0 (by decide)).trans g₆.ws.x0) h11₇) fun t₈ ⟨⟨h9₈, m₈, _⟩, k₈⟩ => ?_
  refine WP.mono (base_ok wA .x8 ((k₈.gpr .x0 (by decide)).trans ((k₇.gpr .x0 (by decide)).trans g₆.ws.x0))
    ((k₈.gpr .x11 (by decide)).trans h11₇)) fun t₉ ⟨⟨h8₉, m₉, _⟩, k₉⟩ => ?_
  have h5₉ : t₉.gpr .x5 = off I.B (slot (vk I.k) gT) := by
    rw [k₉.gpr .x5 (by decide), k₈.gpr .x5 (by decide), k₇.gpr .x5 (by decide), k₆.gpr .x5 (by decide), h5₅]
  have h12₉ : t₉.gpr .x12 = BitVec.ofNat 64 (Wk I.k) := by rw [k₉.gpr .x12 (by decide), k₈.gpr .x12 (by decide), h12₇]
  refine WP.mono (WP.keep [.x7, .x11, .x13] (Q := fun t => t.gpr .x11 = off I.B (slot (vk I.k) gT) ∧
      t.gpr .x13 = BitVec.ofNat 64 (vk I.k) ∧ t.gpr .x7 = 0 ∧ t.mem = t₉.mem) (by
    brun [h5₉, h12₉]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    simp only [Wk, vk] at *
    omega_using [hk2]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h11, h13, h7, mt⟩, kt⟩ => ?_
  have hm : t.mem = t₆.mem := by rw [mt, m₉, m₈, m₇]
  refine ⟨g₆.same hm (((k₇.trans k₈).trans k₉).trans kt) (by decide), ?_, fun r hr => ?_⟩
  · have hn := g₆.ws.scr.nowrap
    have zA' := g₆.ws.sl (j := wA) (by decide)
    show wv t.mem I.B (slot (Wk I.k) wA) (Wk I.k + 2) = 0
    rw [hm, Frm.hdrW_wv f₆ (slot_ge _ _) (by omega_using [hn, zA']), m₅, m₄, Frm.hdrW_wv f₃ (slot_ge _ _) (by omega_using [hn, zA'])]
    exact z
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [kt.get .x0, k₉.get .x0, k₈.get .x0, k₇.get .x0, g₆.ws.x0]; rfl
    · rw [h7]; rfl
    · rw [kt.get .x8, h8₉]; rfl
    · rw [kt.get .x9, k₉.get .x9, h9₈]; rfl
    · rw [h11]; rfl
    · rw [kt.get .x12, h12₉]; rfl
    · rw [h13]; rfl

theorem aProd_ct : CTW (GC vk XT) (GC vk XT) aProd := by
  refine ⟨?_, fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => ?_⟩
  · unfold aProd
    simp only [seqs]
    refine RelCT.seq (setWid_w (Y := XT) (by intros; trivial)).ct (RelCT.seq (zeroA_w (Y := fun a s => zA a.1 s)
      (by decide) (fun _ _ _ _ _ _ z => z) (by taint_decide)).ct ?_)
    refine rel_pin (Ψ := GC Wk fun a s => zA a.1 s) [.x0, .x7, .x8, .x9, .x11, .x12, .x13] fA pins_GC
      (by taint_decide) (fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L z => ?_) ?_
    · subst e
      exact WP.mono (apHead_ok g L.1 z) fun t ⟨g', z', hp⟩ => ⟨⟨I, m₀, c, rfl, g', L, z'⟩, fun r hr => by
        rw [hp r hr]; simp only [fA]⟩
    refine RelCT.seq (two_post (Ψ := GC Wk XT) (two_taint _ pins_of (by taint_decide))
      fun ⟨P, i⟩ s ⟨h, hp⟩ => h.elim fun I m₀ c e g L z => ?_) ?_
    · subst e
      have hk1 := L.1.k1
      have hk2 := L.1.k2
      have hn := g.ws.scr.nowrap
      have zA := g.ws.sl (j := wA) (by decide)
      have zX := g.ws.sl (j := wX) (by decide)
      have zg := g.ws.sl (j := gT) (by decide)
      have pin : ∀ r ∈ [Reg.x0, .x7, .x8, .x9, .x11, .x12, .x13], s.gpr r = fA (dpub I, i) r := hp
      refine WP.mono (mulRowsLow_ok (ea := slot (vk I.k) gT) (eb := slot (Wk I.k) wX) (eA := slot (Wk I.k) wA)
        (wa := vk I.k) (W := Wk I.k) g.ws.scr (by rw [pin .x11 (by simp)]; rfl) (by rw [pin .x9 (by simp)]; rfl)
        (by rw [pin .x13 (by simp)]; rfl) (by rw [pin .x12 (by simp)]; rfl) (by rw [pin .x8 (by simp)]; rfl)
        (by rw [pin .x7 (by simp)]; rfl) (by simp only [vk]; omega_using []) (by simp only [Wk]; omega_using [])
        (by simp only [Wk, vk]; omega_using [hk2]) zA (by have := g.ws.hZ; simp only [slot, hdrBytes, gT, Wk] at *; omega_using [zg])
        (by omega_using [zX]) (by simp only [slot, hdrBytes, gT, wA, Wk]; omega_using [])
        (by simp only [slot, hdrBytes, wX, wA, Wk]; omega_using []) z) fun t ⟨_, o, k⟩ =>
        ⟨I, m₀, c, rfl, g.out (by decide) (Nat.le_refl _) o k (by decide), L, trivial⟩
    rw [show clearTop wA ++ setNar = setWid ++ (ws ++ (base wA .x16 ++ [.lsl .x .x3 .x12 3, .add .x .x16 .x16 .x3,
      movi .x7 0, st .x7 .x16, st .x7 .x16 8] ++ setNar)) by simp only [clearTop, List.append_assoc]]
    exact setWid_ws_rel (fun _ _ h => h) (by taint_decide)
  · subst e
    exact WP.mono (aProd_ok g L.1) fun t ⟨g', _, _⟩ => ⟨I, m₀, c, rfl, g', L, trivial⟩

/-! ## Long division -/

open VG.Impl.Bignum.Public (sCnt)

/-- The registers `divQN` starts from. -/
def dqv (B : Addr) (eU eR eM eT L wm : Nat) (r : Reg) : BitVec 64 :=
  if r = .x0 then B else if r = .x8 then off B eU else if r = .x13 then BitVec.ofNat 64 L
  else if r = .x11 then off B eR else if r = .x12 then BitVec.ofNat 64 wm else if r = .x9 then off B eM
  else if r = .x6 then off B eT else 0

theorem DQH.pins {s : State} {B : Addr} {Z eU eR eM eT L wm : Nat} (h : DQH s B Z eU eR eM eT L wm) :
    ∀ r ∈ [Reg.x0, .x6, .x7, .x8, .x9, .x11, .x12, .x13], s.gpr r = dqv B eU eR eM eT L wm r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h.h0, h.h6, h.h7, h.h8, h.h9, h.h11, h.h12, h.h13]

/-- At step `j` of `divQN`'s loop, from a start `s` that met `DQH`. -/
def DQL (B : Addr) (Z eU eR eM eT L wm : Nat) (j : Nat) (t : State) : Prop :=
  ∃ s s₀ z, DQH s B Z eU eR eM eT L wm ∧ Keep dqRegs s s₀ ∧ z ≤ 63 ∧
    2 ^ 63 ≤ wv s.mem B eM wm * 2 ^ z / 2 ^ (64 * (wm - 1)) ∧
    (∀ i < L - wm + 1, (word s₀.mem B (eU + 8 * i)).toNat = wv s.mem B eU L / 2 ^ (64 * i) % 2 ^ 64) ∧
    DQInv s₀ B Z eU eR eM eT wm (L - wm + 1) (wv s.mem B eM wm) z (wv s.mem B eU L) j t

/-- The registers of `divQN`'s step. -/
def dqf (B : Addr) (eU eR eM eT L wm j : Nat) (r : Reg) : BitVec 64 :=
  if r = .x8 then off B (eU + 8 * (L - wm + 1 - j) - 8) else if r = .x12 then BitVec.ofNat 64 wm
  else dqv B eU eR eM eT L wm r

theorem DQL.pins {B : Addr} {Z eU eR eM eT L wm j : Nat} {t : State} (h : DQL B Z eU eR eM eT L wm j t) :
    ∀ r ∈ [Reg.x0, .x6, .x7, .x8, .x9, .x11, .x12], t.gpr r = dqf B eU eR eM eT L wm j r := by
  obtain ⟨s, s₀, z, hh, k, -, -, -, hI⟩ := h
  have kk := k.trans hI.keep
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [kk.gpr .x0 (by decide), hh.h0]; rfl
  · rw [kk.gpr .x6 (by decide), hh.h6]; rfl
  · rw [kk.gpr .x7 (by decide), hh.h7]; rfl
  · rw [hI.x8]; rfl
  · rw [kk.gpr .x9 (by decide), hh.h9]; rfl
  · rw [kk.gpr .x11 (by decide), hh.h11]; rfl
  · rw [hI.x12]; rfl

/-- `divQN` leaks the same from states that meet `DQH` at the same public layout. -/
theorem divQN_rel {α : Type} {Φ : α → State → Prop} (B : α → Addr) (Z eU eR eM eT L wm : α → Nat)
    (hΦ : ∀ a s, Φ a s → DQH s (B a) (Z a) (eU a) (eR a) (eM a) (eT a) (L a) (wm a)) :
    RelCT isa (Two Φ) divQN fun _ _ => True := by
  rw [divQN_eq]
  have hN : ∀ a s, Φ a s → 0 < L a - wm a + 1 := fun _ _ _ => by omega_using []
  refine VG.Proof.Bignum.AArch64.RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post (Ψ := fun a t =>
      0 < L a - wm a + 1 ∧ DQL (B a) (Z a) (eU a) (eR a) (eM a) (eT a) (L a) (wm a) 0 t)
    (two_taint [.x0, .x6, .x7, .x8, .x9, .x11, .x12, .x13]
      (fun a s₁ s₂ h₁ h₂ r hr => ((hΦ a s₁ h₁).pins r hr).trans ((hΦ a s₂ h₂).pins r hr).symm) (by taint_decide))
    fun a s h => ?_) ?_)
  · have hh := hΦ a s h
    exact WP.mono (dqHead_ok hh.hs hh.h0 hh.h8 hh.h13 hh.h11 hh.h12 hh.h9 hh.h6 hh.h7 hh.hw hh.hL hh.hL' hh.hU8 hh.hH
      hh.hHR hh.hHM hh.hHT hh.hUZ hh.hRZ hh.hMZ hh.hTZ hh.sUR hh.sUM hh.sUT hh.sRM hh.sRT hh.sMT hh.hR0 hh.hR1 hh.htop)
      fun s₀ ⟨z, hz, hd, hUw, h₀, k, _, _⟩ => ⟨hN a s h, s, s₀, z, hh, k, hz, hd, hUw, h₀⟩
  simp only [seqs]
  refine (two_loop (Φ := fun a j t => DQL (B a) (Z a) (eU a) (eR a) (eM a) (eT a) (L a) (wm a) j t)
    (Ψ := fun _ _ => True) (fun a => L a - wm a + 1) ?_ ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
  · exact two_taint [.x0, .x6, .x7, .x8, .x9, .x11, .x12] (fun p s₁ s₂ h₁ h₂ r hr =>
      (h₁.2.pins r hr).trans (h₂.2.pins r hr).symm) (by taint_decide)
  · intro a j t hj ⟨s, s₀, z, hh, k, hz, hd, hUw, hI⟩
    have hn := hh.hs.nowrap
    have := hh.hw; have := hh.hL; have := hh.hL'; have := hh.hU8; have := hh.hUZ; have := hh.hRZ
    have := hh.sUR; have := hh.sUM; have := hh.sUT
    have hM0 : 0 < wv s.mem (B a) (eM a) (wm a) := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hh.htop
    have h₀ := hI.scr
    refine WP.mono (dqStep_ok (hh.hs.congr k.wr) ((k.gpr .x0 (by decide)).trans hh.h0)
      ((k.gpr .x11 (by decide)).trans hh.h11) ((k.gpr .x9 (by decide)).trans hh.h9)
      ((k.gpr .x6 (by decide)).trans hh.h6) ((k.gpr .x7 (by decide)).trans hh.h7)
      hh.hw (by have := hh.hL'; omega_arith) (by have := hh.hL'; omega_arith) hh.hU8 (Nat.le_trans (Nat.le_add_left 8 _) hh.hHR) hh.hH hh.hHR hh.hHM
      hh.hHT (by have := hh.hUZ; omega_arith) hh.hRZ hh.hMZ hh.hTZ (by have := hh.sUR; omega_arith) (by have := hh.sUM; omega_arith)
      (by have := hh.sUT; omega_arith) hh.sRM hh.sRT hh.sMT hz hd hM0 hUw hj hI) fun t' ⟨hI', hc⟩ => ?_
    refine ⟨?_, fun _ => ⟨s, s₀, z, hh, k, hz, hd, hUw, hI'⟩, fun _ => trivial⟩
    rw [VG.Proof.MlKem.AArch64.eval_nonzero, VG.Proof.MlKem.AArch64.ne_zero_iff]
    exact congrArg some (decide_eq_decide.mpr (hc.trans (by omega_using [hj])))

/-- `m < n`, and'ed into the mask. -/
theorem cmpTail_w : CTW (GC Wk XT) (GC Wk XT) (seqs [.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++
    base wA .x16 ++ base wN .x17), cmpLoop, .block (borrowMask ++ andMask)]) :=
  wsop (rest := [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base wA .x16 ++ base wN .x17)
    (body := .seq cmpLoop (.block (borrowMask ++ andMask)))
    (by simp only [seqs, List.append_assoc]) (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    have sA := g.ws.sl (j := wA) (by decide)
    have sN := g.ws.sl (j := wN) (by decide)
    have hw1 := g.ws.w1
    have hw2 := g.ws.w2
    simp only [seqs]
    refine WP.seq (WP.mono (cmpSet_ok' g.ws wA wN) fun s₇ ⟨⟨h16, h17, h14, _, _, h7, hc, m₇⟩, k₇⟩ => ?_)
    refine WP.seq (WP.mono (cmpLoop_ok (g.ws.scr.congr k₇.wr) h16 h17 h14 hc (by omega_using [hw1]) (by omega_using [hw2]) (by omega_using [sA])
      (by omega_using [sN])) fun s₈ ⟨_, m₈, k₈⟩ => ?_)
    have g₈ := (g.same m₇ k₇ (by decide)).same m₈ k₈ (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (borrowMask_ok s₈ ((k₈.gpr .x7 (by decide)).trans h7)) fun s₉ ⟨⟨h15, m₉, _⟩, k₉⟩ => ?_
    exact WP.mono (andMask_ok (g₈.same m₉ k₉ (by decide)) h15) fun t ⟨gt, _, _⟩ => ⟨I, m₀, _, rfl, gt, L, trivial⟩

/-- `nOne` holds 1. -/
def XO (a : Pub) (s : State) : Prop := wv s.mem a.1.B (slot (vk a.1.k) nOne) (vk a.1.k + 2) = 1

/-- `XO`, and `n` (narrow array 0) of `k` bytes, its top byte not zero. -/
def XA (a : Pub) (s : State) : Prop :=
  XO a s ∧ ∃ N, wv s.mem a.1.B (slot (vk a.1.k) 0) (vk a.1.k) = N ∧ 256 ^ (a.1.k - 1) ≤ N ∧ N < 2 ^ (8 * a.1.k)

/-- The quotient's top words cleared. -/
theorem clrTop_w : CTW (GC Wk XT) (GC Wk XT) (seqs [.block (ws ++ base wA .x16 ++ ([.lsr .x .x14 .x12 1,
    .addImm .x .x3 .x14 3, .lsl .x .x3 .x3 3, .add .x .x16 .x16 .x3, .subImm .x .x14 .x14 3, movi .x7 0] : List Instr)), clearN]) :=
  wsop (rest := base wA .x16 ++ [.lsr .x .x14 .x12 1, .addImm .x .x3 .x14 3, .lsl .x .x3 .x3 3, .add .x .x16 .x16 .x3,
      .subImm .x .x14 .x14 3, movi .x7 0]) (body := clearN)
    (by simp only [seqs, List.append_assoc]) (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    have hk1 := L.1.k1
    have hk2 := L.1.k2
    have hn := g.ws.scr.nowrap
    have hZW := g.ws.hZ
    have qA : slot (Wk I.k) wA = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
    have qW16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
    have hv9 : 9 ≤ vk I.k := by simp only [vk]; omega_using [hk1]
    have hv2 : vk I.k ≤ 200 := by simp only [vk]; omega_using [hk2]
    have hW : Wk I.k = 2 * vk I.k + 2 := rfl
    simp only [seqs]
    refine WP.seq ?_
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (ws_ok g.ws.scr g.ws.x0 g.ws.h256 g.ws.hw g.ws.hS) fun s₁₀ ⟨⟨h12₁₀, h11₁₀, m₁₀, _⟩, k₁₀⟩ => ?_
    refine WP.mono (base_ok wA .x16 ((k₁₀.gpr .x0 (by decide)).trans g.ws.x0) h11₁₀) fun s₁₁ ⟨⟨h16₁₁, m₁₁, _⟩, k₁₁⟩ => ?_
    have h12₁₁ : s₁₁.gpr .x12 = BitVec.ofNat 64 (Wk I.k) := (k₁₁.gpr .x12 (by decide)).trans h12₁₀
    refine WP.mono (WP.keep [.x3, .x7, .x14, .x16] (Q := fun t => t.gpr .x16 = off I.B (slot (Wk I.k) wA + 8 * (vk I.k + 4)) ∧
        t.gpr .x14 = BitVec.ofNat 64 (vk I.k - 2) ∧ t.gpr .x7 = 0 ∧ t.mem = s₁₁.mem) (by
      have e1 : BitVec.ofNat 64 (Wk I.k) >>> 1 = BitVec.ofNat 64 (vk I.k + 1) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
        simp only [Wk, vk] at *; omega_using [hk2]
      have e2 : (BitVec.ofNat 64 (vk I.k + 1) + BitVec.ofNat 64 3) <<< 3 = BitVec.ofNat 64 (8 * (vk I.k + 4)) := by
        rw [BitVec.ofNat_add_ofNat, shl_ofNat (show (vk I.k + 1 + 3) * 2 ^ 3 < 2 ^ 64 by omega_using [hv2])]; congr 1; omega_using []
      brun [h16₁₁, h12₁₁, e1, e2, off_add, ofNat_sub_ofNat (show 3 ≤ vk I.k + 1 by omega_using [hv9]) (by omega_using [hv2])]
      congr 1) (by decide) (by decide) (by decide +kernel)) fun s₁₂ ⟨⟨h16₁₂, h14₁₂, h7₁₂, m₁₂⟩, k₁₂⟩ => ?_
    have g₁₂ : G I m₀ (Wk I.k) c s₁₂ := g.same (by rw [m₁₂, m₁₁, m₁₀]) ((k₁₀.trans k₁₁).trans k₁₂) (by decide)
    refine WP.mono (clearN_ok g₁₂.ws.scr h16₁₂ h14₁₂ h7₁₂ (by omega_using [hv9]) (by omega_using [hv2]) (by omega_using [hZW, qA, qW16, hW]))
      fun s₁₃ ⟨_, o₁₃, k₁₃⟩ => ⟨I, m₀, c, rfl, g₁₂.out (j := wA) (n := 8 * (Wk I.k + 2)) (by decide) (Nat.le_refl _)
        (o₁₃.mono (by omega_using []) (by omega_using [hW])) k₁₃ (by decide), L, trivial⟩

/-- `divA`'s state at the division. -/
def DQC (a : Pub) (s : State) : Prop :=
  GC Wk XO a s ∧ DQH s a.1.B a.1.Z (slot (Wk a.1.k) wA) (slot (Wk a.1.k) wX) (slot (vk a.1.k) 0)
    (slot (Wk a.1.k) wT) (Wk a.1.k) (vk a.1.k - 1)

theorem divA_ct : CTW (GC vk XA) (GC Wk XO) divA := by
  refine ⟨?_, fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L ⟨xo, N, hN, hlo, hNk⟩ => ?_⟩
  · rw [divA_eq]
    refine VG.Proof.Bignum.AArch64.RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post (Ψ := DQC) ?_
      fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L ⟨xo, N, hN, hlo, hNk⟩ => ?_) ?_)
    · rw [show divAP = [.block setWid, zeroA wN, .block setNar, copyA nN Public.aN, .block setWid, zeroA wX, zeroA wT] ++
        [.block (setNar ++ (ws ++ (base Public.aN .x9 ++ setWid ++ ws ++ base wT .x6 ++ base wA .x8 ++ base wX .x5 ++
          [mov .x11 .x5, mov .x13 .x12, .lsr .x .x12 .x12 1, .subImm .x .x12 .x12 2, movi .x7 0])))] by
        simp only [divAP, List.append_assoc, List.cons_append, List.nil_append]]
      refine VG.Proof.Bignum.AArch64.RelCT.seqs_append (by simp) (by simp) (RelCT.seq ?_
        (setNar_ws_rel (w := Wk) (X := XT) (Φ := GC Wk XT) (fun _ _ h => h) (by taint_decide)))
      refine CTW.ct (Ψ := GC Wk XT) ?_
      refine CTW.cons (by simp) (setWid_w (Y := XT) (by intros; trivial)) ?_
      refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
      refine CTW.cons (by simp) (setNar_w (Y := XT) (by intros; trivial)) ?_
      refine CTW.cons (by simp) (copyA_w (Y := XT) (by decide) (by decide) (by decide) (by intros; trivial)
        (by taint_decide)) ?_
      refine CTW.cons (by simp) (setWid_w (Y := XT) (by intros; trivial)) ?_
      refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
      exact CTW.one (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide))
    · subst e
      have hk1 := L.1.k1
      exact WP.mono (divA1_ok g L.1 rfl hN hlo hNk) fun t ⟨gt, hh, _, _, _, _, kS⟩ =>
        ⟨⟨I, m₀, c, rfl, gt, L, by
          show wv t.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1
          rw [kS _ _ (slot_ge _ _) (by simp only [slot, hdrBytes, nOne, nN, wN]; omega_using [])]; exact xo⟩, hh⟩
    simp only [seqs]
    refine RelCT.seq (two_post (Ψ := GC Wk XO) (divQN_rel (Φ := DQC) (fun a => a.1.B) (fun a => a.1.Z)
      (fun a => slot (Wk a.1.k) wA) (fun a => slot (Wk a.1.k) wX) (fun a => slot (vk a.1.k) 0)
      (fun a => slot (Wk a.1.k) wT) (fun a => Wk a.1.k) (fun a => vk a.1.k - 1) fun _ _ h => h.2)
      fun ⟨P, i⟩ s ⟨h, hh⟩ => h.elim fun I m₀ c e g L xo => ?_) ?_
    · subst e
      have hk1 := L.1.k1
      have hk2 := L.1.k2
      have hn := g.ws.scr.nowrap
      have hZW := g.ws.hZ
      have hv9 : 9 ≤ vk I.k := by simp only [vk]; omega_using [hk1]
      have hv2 : vk I.k ≤ 200 := by simp only [vk]; omega_using [hk2]
      have qN : slot (Wk I.k) wN = 256 + 4 * (8 * (Wk I.k + 2)) := rfl
      have qX : slot (Wk I.k) wX = 256 + 6 * (8 * (Wk I.k + 2)) := rfl
      have qA : slot (Wk I.k) wA = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
      have qT : slot (Wk I.k) wT = 256 + 9 * (8 * (Wk I.k + 2)) := rfl
      have qW16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
      have hsC : 8 * sCnt + 8 ≤ 256 := by decide
      have hW : Wk I.k = 2 * vk I.k + 2 := rfl
      refine WP.mono hh.ok fun s₉ ⟨_, _, _, f₉', _, k₉'⟩ => ?_
      have f₉ : Frm I.B [(slot (Wk I.k) wA, 8 * (Wk I.k - (vk I.k - 1) + 1)), (slot (Wk I.k) wX, 8 * (vk I.k - 1 + 1)),
        (slot (Wk I.k) wT, 32), (8 * sCnt, 8)] s.mem s₉.mem := f₉'
      rw [show vk I.k - 1 + 1 = vk I.k by omega_using [hv9], show Wk I.k - (vk I.k - 1) + 1 = vk I.k + 4 by omega_using [hv9, hW]] at f₉
      refine ⟨I, m₀, c, rfl, g.frmOwn (sl := sCnt) ⟨by decide, by decide, by decide⟩
        (rs := [(slot (Wk I.k) wA, 8 * (vk I.k + 4)), (slot (Wk I.k) wX, 8 * vk I.k), (slot (Wk I.k) wT, 32)]) f₉
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_arith)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_arith)
        k₉' (by decide), L, ?_⟩
      have xo' : wv s.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1 := xo
      show wv s₉.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1
      rw [f₉.wv_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> simp only [slot, hdrBytes, nOne, wA, wX, wT] <;> omega_arith)
        (by simp only [slot, hdrBytes, nOne]; omega_using [hv2])]
      exact xo'
    exact ((CTW.app (by simp) (by simp) clrTop_w cmpTail_w).mono (fun _ _ h => h.map fun _ => trivial)
      fun _ _ h => h).1
  · subst e
    exact WP.mono (divA_ok g L.1 rfl hN hlo hNk) fun t ⟨gt, _, _, _, k⟩ => ⟨I, m₀, _, rfl, gt, L, by
      show wv t.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1
      rw [k nOne _ (by decide) (Nat.le_refl _)]; exact xo⟩

/-! ## `(n - r) / (m + 1)` -/

/-- A count in slot `sl`, kept by a piece that writes outside the header. -/
theorem XS_out {w : Nat → Nat} {X : Pub → State → Prop} {a : Pub} {s t : State} (_h : GC w X a s) {sl : Nat}
    (hsl : sl < 32) {bnd : DP → Nat} {j n : Nat} (o : Outside a.1.B (slot (w a.1.k) j) n s.mem t.mem)
    (x : XS sl bnd a s) : XS sl bnd a t := by
  obtain ⟨T, hT, hb, hT'⟩ := x
  exact ⟨T, (o.word (.inl (by have := slot_ge (w a.1.k) j; omega_using [hsl, this])) (by omega_using [hsl])).trans hT, hb, hT'⟩

/-- A count in slot `sl`, kept by `setNar` and `setWid`. -/
theorem XS_hdr {w : Nat → Nat} {X : Pub → State → Prop} {a : Pub} {s t : State} (h : GC w X a s) {sl : Nat}
    (hsl : 16 ≤ sl) (hsl' : sl < 32) (hslS : sl ≠ sStride) {bnd : DP → Nat} (f : Frm a.1.B hdrW s.mem t.mem)
    (x : XS sl bnd a s) : XS sl bnd a t :=
  stable_XS (N := fun P => vk P.k) (j := 0) hsl hsl' hslS a s t w X h (f.mono fun _ hr => List.mem_append_left _ hr) x

/-- A list of pairs of pieces, each keeping `Ψ`. -/
theorem CTW.pairs {f g : Nat → Prog isa} {Ψ : Pub → State → Prop} :
    ∀ {M : Nat}, 1 ≤ M → (∀ m < M, CTW Ψ Ψ (f m)) → (∀ m < M, CTW Ψ Ψ (g m)) →
      CTW Ψ Ψ (seqs ((List.range M).flatMap fun k => [f k, g k]))
  | 0, h, _, _ => absurd h (by decide)
  | 1, _, hf, hg => CTW.cons (by simp) (hf 0 (by decide)) (CTW.one (hg 0 (by decide)))
  | M + 2, _, hf, hg => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact CTW.app (List.ne_nil_of_mem (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by omega_using []), List.mem_cons_self⟩))
      (by simp) (CTW.pairs (M := M + 1) (by omega_using []) (fun m hm => hf m (by omega_using [hm])) fun m hm => hg m (by omega_using [hm]))
      (CTW.cons (by simp) (hf (M + 1) (by omega_using [])) (CTW.one (hg (M + 1) (by omega_using []))))

/-- The divisor's leading zero words' count's bound. -/
abbrev bV (P : DP) : Nat := vk P.k

/-- The taint checks of every stage `k < 8`. -/
macro "taints8" : tactic => `(tactic| (intro k hk; rcases k with _|_|_|_|_|_|_|_|k <;>
  first | exact absurd hk (by omega) | exact ⟨_, by taint_decide⟩))

/-- A word stage of `divB`'s, by words (`words = false`). -/
theorem dstage_ct {w : Nat → Nat} (wide : Bool) {j : Nat} (hj : j < 16) {k : Nat} (hk : k < 8)
    (h1 : ∃ hc, (taint.check (Taint.ofRegs [.x0]) (.block (wGuard wide k)) hc).isSome = true)
    (h2 : ∃ hc, (taint.check (Taint.ofRegs [.x0]) (.block (wHeadU wide j sCnt false k)) hc).isSome = true)
    (h3 : ∃ hc, (taint.check (Taint.ofRegs [.x0, .x13, .x16, .x17]) (wRest true k) hc).isSome = true) :
    CTW (GC w fun a s => XS sCnt bV a s ∧ True) (GC vk fun a s => XS sCnt bV a s ∧ True)
      (wstage j wide true sCnt false k) := by
  obtain ⟨_, h1⟩ := h1
  obtain ⟨_, h2⟩ := h2
  obtain ⟨_, h3⟩ := h3
  exact wstage_ct wide true stable_true hj (by decide) (by decide) (by decide) false (by omega_using [hk])
    (fun P T h => by cases wide <;> simp only [nw, bV, Bool.false_eq_true, ↓reduceIte, Wk] at * <;> omega_using [h]) h1 h2 h3

/-- `divB`'s pieces up to the division. -/
abbrev dbA : List (Prog isa) := [.block (setNar ++ ones), zeroA nM1, addA nM1 (2 * wA) nOne, zeroA nD,
  subA nD Public.aN (2 * wX)]
abbrev dbS : List (Prog isa) := [.block (ws ++ base nM1 .x16 ++ [movi .x7 0, movi .x5 0, movi .x6 0, mov .x14 .x12]),
  countLoop .x14 hiScan, .block [.sub .x .x10 .x12 .x5, .subImm .x .x10 .x10 1, sth .x10 sCnt]]
abbrev dbM : List (Prog isa) := [.block setWid, zeroA wM, zeroA wT, .block setNar, copyA (2 * wM) nD]
abbrev dbF : List (Prog isa) :=
  (List.range 8).flatMap (fun k => [wstage nM1 false true sCnt false k, wstage wM true true sCnt false k])
abbrev dbC : List (Prog isa) :=
  [.block (setNar ++ (ws ++ (topAt nM1 .x16 ++ [.subImm .x .x16 .x16 8, ld .x3 .x16, movi .x4 1, movi .x7 0,
    .subs .x .x5 .x3 .x4, .adc .x .x5 .x7 .x7, .add .x .x3 .x3 .x4, .sub .x .x3 .x3 .x5, st .x3 .x16]))), zeroA nRem]
abbrev dbL : Prog isa := .block (ws ++ (base nM1 .x9 ++ base nRem .x5 ++ setWid ++ ws ++ base wT .x6 ++ base wM .x8 ++
  [mov .x11 .x5, .subImm .x .x13 .x12 2, .lsr .x .x12 .x12 1, .subImm .x .x12 .x12 1, movi .x7 0]))

theorem divBP_eq : divBP = (dbA ++ (dbS ++ (dbM ++ (dbF ++ dbC)))) ++ [dbL] := by
  simp only [divBP, dbA, dbS, dbM, dbF, dbC, dbL, List.append_assoc, List.cons_append, List.nil_append]

/-- `XS` of `divB`'s count. -/
abbrev XB : Pub → State → Prop := fun a s => XS sCnt bV a s ∧ True

/-- `divB` up to the division: what the taint analysis and the pins give, with no facts. -/
theorem divBP_rel : RelCT isa (Two (GC Wk XO)) (seqs divBP) fun _ _ => True := by
  rw [divBP_eq]
  refine VG.Proof.Bignum.AArch64.RelCT.seqs_append (by simp) (by simp) (RelCT.seq (CTW.ct (Ψ := GC vk XT) ?_)
    (ws_blk0 (fun a => a.1.B) (fun a => a.1.Z) (fun a => vk a.1.k) (fun _ _ h => h.ws) (by taint_decide)))
  refine CTW.mono (Φ := GC Wk XT) ?_ (fun _ _ h => h.map fun _ => trivial) fun _ _ h => h
  refine CTW.app (Ψ := GC vk XT) (by simp) (by simp) ?_ (CTW.app (Ψ := GC vk XB) (by simp) (by simp) ?_
    (CTW.app (Ψ := GC vk XB) (by simp) (by simp) ?_ (CTW.app (Ψ := GC vk XB) (by simp; exact ⟨0, by decide⟩)
      (by simp) ?_ ?_)))
  · -- `m + 1` and `n - r`.
    refine CTW.cons (by simp) (blk (w' := vk) (Y := fun _ s => MR .x15 s) (by taint_decide)
      fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
        subst e
        rw [WP.block_append_iff]
        exact WP.mono (g.setNar_ok L.1) fun t₁ ⟨g₁, _, _⟩ => WP.mono (ones_ok t₁) fun t ⟨⟨h15, _, hm⟩, k⟩ =>
          ⟨I, m₀, c, rfl, g₁.same hm k (by decide), L, _, h15⟩) ?_
    refine CTW.cons (by simp) (zeroA_w (Y := fun _ s => MR .x15 s) (by decide)
      (fun _ _ _ h _ k _ => h.x.keep k (by decide)) (by taint_decide)) ?_
    refine CTW.cons (by simp) (addA_w (Y := XT) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun _ _ h => h.x) (by intros; trivial) (by taint_decide)) ?_
    refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
    exact CTW.one (subA_w (Y := XT) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intros; trivial) (by taint_decide))
  · -- The count of the divisor's leading zero words.
    refine wsop (rest := base nM1 .x16 ++ [movi .x7 0, movi .x5 0, movi .x6 0, mov .x14 .x12])
      (body := .seq (countLoop .x14 hiScan) (.block [.sub .x .x10 .x12 .x5, .subImm .x .x10 .x10 1, sth .x10 sCnt]))
      (by simp only [seqs, List.append_assoc]) (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => ?_
    subst e
    have hk1 := L.1.k1
    refine WP.mono (hiZ_ok g L.1) fun t ⟨g', _, hz, _⟩ => ⟨I, m₀, c, rfl, g', L, ⟨_, hz, ?_, ?_⟩, trivial⟩
    · show _ < vk I.k
      have : 1 ≤ vk I.k := by simp only [vk]; omega_using []
      omega_using [this]
    · have := L.1.k2
      have : vk I.k < 200 := by simp only [vk]; omega_using [this]
      omega_using [this]
  · -- `x` into wide array `wM`.
    refine CTW.cons (by simp) (setWid_w (Y := XB) fun _ _ _ h f _ => ⟨XS_hdr h (by decide) (by decide) (by decide) f
      h.x.1, trivial⟩) ?_
    refine CTW.cons (by simp) (zeroA_w (Y := XB) (by decide) (fun _ _ _ h o _ _ => ⟨XS_out h (by decide) o h.x.1,
      trivial⟩) (by taint_decide)) ?_
    refine CTW.cons (by simp) (zeroA_w (Y := XB) (by decide) (fun _ _ _ h o _ _ => ⟨XS_out h (by decide) o h.x.1,
      trivial⟩) (by taint_decide)) ?_
    refine CTW.cons (by simp) (setNar_w (Y := XB) fun _ _ _ h f _ => ⟨XS_hdr h (by decide) (by decide) (by decide) f
      h.x.1, trivial⟩) ?_
    exact CTW.one (copyA_w (Y := XB) (by decide) (by decide) (by decide) (fun _ _ _ h o _ => ⟨XS_out h (by decide) o
      h.x.1, trivial⟩) (by taint_decide))
  · -- The stages.
    have hf : ∀ k < 8, ∃ hc, (taint.check (Taint.ofRegs [.x0]) (.block (wGuard false k)) hc).isSome = true := by taints8
    have hf2 : ∀ k < 8, ∃ hc, (taint.check (Taint.ofRegs [.x0]) (.block (wHeadU false nM1 sCnt false k)) hc).isSome =
      true := by taints8
    have hg : ∀ k < 8, ∃ hc, (taint.check (Taint.ofRegs [.x0]) (.block (wGuard true k)) hc).isSome = true := by taints8
    have hg2 : ∀ k < 8, ∃ hc, (taint.check (Taint.ofRegs [.x0]) (.block (wHeadU true wM sCnt false k)) hc).isSome =
      true := by taints8
    have hr : ∀ k < 8, ∃ hc, (taint.check (Taint.ofRegs [.x0, .x13, .x16, .x17]) (wRest true k) hc).isSome = true := by
      taints8
    exact CTW.pairs (by decide) (fun m hm => dstage_ct false (by decide) hm (hf m hm) (hf2 m hm) (hr m hm))
      fun m hm => dstage_ct true (by decide) hm (hg m hm) (hg2 m hm) (hr m hm)
  · -- The divisor's top word not zero, and the remainder's array cleared.
    refine CTW.cons (Ψ := GC vk XT) (by simp) ⟨setNar_ws_rel (fun _ _ h => h) (by taint_decide), fun ⟨P, i⟩ s h => h.elim
      fun I m₀ c e g L _ => ?_⟩ (CTW.one (zeroA_w (X := XT) (Y := XT) (by decide) (by intros; trivial) (by taint_decide)))
    subst e
    have hf := fixTop_ok g L.1
    simp only [List.append_assoc] at hf
    exact WP.mono hf fun t ⟨g', _⟩ => ⟨I, m₀, c, rfl, g', L, trivial⟩

/-- `divB`'s state at the division. -/
def DQB (a : Pub) (s : State) : Prop :=
  GC Wk XO a s ∧ DQH s a.1.B a.1.Z (slot (Wk a.1.k) wM) (slot (vk a.1.k) nRem) (slot (vk a.1.k) nM1)
    (slot (Wk a.1.k) wT) (2 * vk a.1.k) (vk a.1.k)

theorem divB_ct : CTW (GC Wk XO) (GC vk XO) divB := by
  refine ⟨?_, fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L xo => ?_⟩
  · rw [divB_eq]
    refine VG.Proof.Bignum.AArch64.RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post (Ψ := DQB) divBP_rel
      fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L xo => ?_) ?_)
    · subst e
      have hb32 := hb32_of g L.1
      exact WP.mono (divB1_ok g L.1 rfl rfl rfl xo) fun t ⟨_, _, _, gt, hh, _, _, _, F⟩ =>
        ⟨⟨I, m₀, c, rfl, gt, L, by
          show wv t.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1
          rw [rbB_wv F (.inl (by decide)) (Nat.le_refl _) hb32]; exact xo⟩, hh⟩
    refine RelCT.seq (two_post (Ψ := GC Wk XT) (divQN_rel (Φ := DQB) (fun a => a.1.B) (fun a => a.1.Z)
      (fun a => slot (Wk a.1.k) wM) (fun a => slot (vk a.1.k) nRem) (fun a => slot (vk a.1.k) nM1)
      (fun a => slot (Wk a.1.k) wT) (fun a => 2 * vk a.1.k) (fun a => vk a.1.k) fun _ _ h => h.2)
      fun ⟨P, i⟩ s ⟨h, hh⟩ => h.elim fun I m₀ c e g L _ => ?_) ?_
    · subst e
      have hk1 := L.1.k1
      have hk2 := L.1.k2
      have hn := g.ws.scr.nowrap
      have hZW := g.ws.hZ
      have hW : Wk I.k = 2 * vk I.k + 2 := rfl
      have hv9 : 9 ≤ vk I.k := by simp only [vk]; omega_using [hk1]
      have hv2 : vk I.k ≤ 200 := by simp only [vk]; omega_using [hk2]
      have qM : slot (Wk I.k) wM = 256 + 5 * (8 * (Wk I.k + 2)) := rfl
      have qT : slot (Wk I.k) wT = 256 + 9 * (8 * (Wk I.k + 2)) := rfl
      have q4 : slot (vk I.k) nRem = 256 + 4 * (8 * (vk I.k + 2)) := rfl
      have qW16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
      have hsC : 8 * sCnt + 8 ≤ 256 := by decide
      refine WP.mono hh.ok fun s₁₇ ⟨_, _, _, f₁₇', _, k₁₇⟩ => ?_
      have f₁₇ : Frm I.B [(slot (Wk I.k) wM, 8 * (2 * vk I.k - vk I.k + 1)), (slot (vk I.k) nRem, 8 * (vk I.k + 1)),
        (slot (Wk I.k) wT, 32), (8 * sCnt, 8)] s.mem s₁₇.mem := f₁₇'
      rw [show 2 * vk I.k - vk I.k + 1 = vk I.k + 1 by omega_using []] at f₁₇
      exact ⟨I, m₀, c, rfl, g.frmOwn (sl := sCnt) ⟨by decide, by decide, by decide⟩
        (rs := [(slot (Wk I.k) wM, 8 * (vk I.k + 1)), (slot (vk I.k) nRem, 8 * (vk I.k + 1)), (slot (Wk I.k) wT, 32)]) f₁₇
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_arith)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_arith)
        k₁₇ (by decide), L, trivial⟩
    refine (?_ : CTW (GC Wk XT) (GC vk XT) (seqs divBT)).1
    refine CTW.cons (by simp) (setNar_w (Y := XT) (by intros; trivial)) ?_
    refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
    refine CTW.cons (by simp) (copyA_w (Y := XT) (by decide) (by decide) (by decide) (by intros; trivial)
      (by taint_decide)) ?_
    refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
    refine CTW.app (a := eqA nRem nZ) (by simp [eqA]) (by simp) (eqA_w (Y := XT) (by decide) (by decide)
      (by intros; trivial) (by taint_decide)) ?_
    exact CTW.one (andZero_w (Y := XT) (by intros; trivial))
  · subst e
    have hb32 := hb32_of g L.1
    exact WP.mono (divB_ok g L.1 rfl rfl rfl xo) fun t ⟨_, _, gt, _, _, k⟩ => ⟨I, m₀, _, rfl, gt, L, by
      show wv t.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1
      rw [k nOne _ (.inl (by decide)) (Nat.le_refl _)]; exact xo⟩

/-! ## `b²` -/

/-- The square's accumulator zero. -/
def zSq (P : DP) (s : State) : Prop := wv s.mem P.B (slot (Wk P.k) wSq) (Wk P.k + 2) = 0

/-- The pins of `square`'s rows. -/
def fS (a : Pub) (r : Reg) : BitVec 64 :=
  if r = .x0 then a.1.B else if r = .x8 then off a.1.B (slot (Wk a.1.k) wSq)
  else if r = .x9 then off a.1.B (slot (vk a.1.k) nB) else if r = .x11 then off a.1.B (slot (vk a.1.k) nB)
  else if r = .x12 then BitVec.ofNat 64 (vk a.1.k) else if r = .x13 then BitVec.ofNat 64 (vk a.1.k) else 0

/-- `square`'s rows' head. -/
abbrev sqHead : List Instr := ws ++ base wSq .x8 ++ setNar ++ ws ++ base nB .x9 ++ [mov .x11 .x9, mov .x13 .x12, movi .x7 0]

theorem sqHead_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (g : G I m₀ (Wk I.k) c s) (L : RpLens I)
    (z : zSq (dpub I) s) :
    WP isa (.block sqHead) s fun t => G I m₀ (vk I.k) c t ∧ zSq (dpub I) t ∧
      ∀ r ∈ [Reg.x0, .x7, .x8, .x9, .x11, .x12, .x13], t.gpr r = fS (dpub I, 0) r := by
  have hk1 := L.k1
  have hk2 := L.k2
  rw [sqHead, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ws_ok g.ws.scr g.ws.x0 g.ws.h256 g.ws.hw g.ws.hS) fun s₆ ⟨⟨_, h11₆, m₆, _⟩, k₆⟩ => ?_
  refine WP.mono (base_ok wSq .x8 ((k₆.gpr .x0 (by decide)).trans g.ws.x0) h11₆) fun s₇ ⟨⟨h8₇, m₇, _⟩, k₇⟩ => ?_
  have g₇ := g.same (by rw [m₇, m₆]) (k₆.trans k₇) (by decide)
  refine WP.mono (g₇.setNar_ok L) fun s₈ ⟨g₈, f₈, k₈⟩ => ?_
  refine WP.mono (ws_ok g₈.ws.scr g₈.ws.x0 g₈.ws.h256 g₈.ws.hw g₈.ws.hS) fun s₉ ⟨⟨h12₉, h11₉, m₉, _⟩, k₉⟩ => ?_
  refine WP.mono (base_ok nB .x9 ((k₉.gpr .x0 (by decide)).trans g₈.ws.x0) h11₉) fun s₁₀ ⟨⟨h9₁₀, m₁₀, _⟩, k₁₀⟩ => ?_
  have h12₁₀ : s₁₀.gpr .x12 = BitVec.ofNat 64 (vk I.k) := (k₁₀.gpr .x12 (by decide)).trans h12₉
  refine WP.mono (WP.keep [.x7, .x11, .x13] (Q := fun t => t.gpr .x11 = off I.B (slot (vk I.k) nB) ∧
      t.gpr .x13 = BitVec.ofNat 64 (vk I.k) ∧ t.gpr .x7 = 0 ∧ t.mem = s₁₀.mem) (by brun [h9₁₀, h12₁₀])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h11, h13, h7, mt⟩, kt⟩ => ?_
  have hm : t.mem = s₈.mem := by rw [mt, m₁₀, m₉]
  refine ⟨g₈.same hm ((k₉.trans k₁₀).trans kt) (by decide), ?_, fun r hr => ?_⟩
  · have hn := g.ws.scr.nowrap
    have := g.ws.sl (j := wSq) (by decide)
    show wv t.mem I.B (slot (Wk I.k) wSq) (Wk I.k + 2) = 0
    rw [hm, Frm.hdrW_wv f₈ (slot_ge _ _) (by omega_using [hn, this]), m₇, m₆]
    exact z
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [kt.get .x0, k₁₀.get .x0, k₉.get .x0, g₈.ws.x0]; rfl
    · rw [h7]; rfl
    · rw [kt.get .x8, k₁₀.get .x8, k₉.get .x8, k₈.get .x8, h8₇]; rfl
    · rw [kt.get .x9, h9₁₀]; rfl
    · rw [h11]; rfl
    · rw [kt.get .x12, h12₁₀]; rfl
    · rw [h13]; rfl

theorem square_ct : CTW (GC vk XO) (GC vk XT) square := by
  refine ⟨?_, fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L xo => ?_⟩
  · unfold square
    simp only [seqs]
    refine RelCT.seq (regs_w (X := XO) (Y := fun _ s => MR .x15 s) (by taint_decide) (rs := [.x7, .x15]) (by decide)
      fun a s h => WP.mono (ones_ok s) fun t ⟨⟨h15, _, hm⟩, k⟩ => ⟨⟨hm, _, h15⟩, k⟩).ct ?_
    refine RelCT.seq (zeroA_w (Y := fun _ s => MR .x15 s) (by decide)
      (fun _ _ _ h _ k _ => h.x.keep k (by decide)) (by taint_decide)).ct ?_
    refine RelCT.seq (addA_w (Y := XT) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun _ _ h => h.x) (by intros; trivial) (by taint_decide)).ct ?_
    refine RelCT.seq (setWid_w (Y := XT) (by intros; trivial)).ct ?_
    refine RelCT.seq (zeroA_w (Y := fun a s => zSq a.1 s) (by decide) (fun _ _ _ _ _ _ z => z)
      (by taint_decide)).ct ?_
    refine rel_pin (Ψ := GC vk XT) [.x0, .x7, .x8, .x9, .x11, .x12, .x13] fS pins_GC
      (by taint_decide) (fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L z => ?_) (two_taint _ pins_of (by taint_decide))
    subst e
    exact WP.mono (sqHead_ok g L.1 z) fun t ⟨g', _, hp⟩ => ⟨⟨I, m₀, c, rfl, g', L, trivial⟩, fun r hr => by
      rw [hp r hr]; simp only [fS]⟩
  · subst e
    exact WP.mono (square_ok g L.1 rfl xo) fun t ⟨gt, _⟩ => ⟨I, m₀, c, rfl, gt, L, trivial⟩

theorem minus4n_ct : CTW (GC vk XT) (GC Wk XT) minus4n := by
  unfold minus4n oneA
  simp only [List.cons_append, List.nil_append]
  refine CTW.cons (by simp) (setWid_w (Y := XT) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (dblA_w (Y := XT) (by decide) (fun _ s _ => cin_c0 s) (by intros; trivial)
    (by taint_decide)) ?_
  refine CTW.cons (by simp) (dblA_w (Y := XT) (by decide) (fun _ s _ => cin_c0 s) (by intros; trivial)
    (by taint_decide)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XM) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ hm _ => hm) (by taint_decide)) ?_
  refine CTW.cons (by simp) (andMask_w (Y := XT) (fun _ _ h => h.x) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (setOneA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XM) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ hm _ => hm) (by taint_decide)) ?_
  exact CTW.one (andMask_w (Y := XT) (fun _ _ h => h.x) (by intros; trivial))

end VG.Proof.Rsa.AArch64.Rd
