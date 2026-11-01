module

public import VerifiedGarbage.Proof.Rsa.AArch64.InvLoop
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Rsa.AArch64.InvEnd
import VerifiedGarbage.Proof.Rsa.AArch64.InvPieces
import VerifiedGarbage.Proof.Rsa.AArch64.InvStage
import VerifiedGarbage.Proof.Rsa.Divstep.InvResult64
import VerifiedGarbage.Proof.Divstep.MredWords
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# RSA private keys on AArch64: the end of the batched inverse

After the batches (`LInv` after `3 n + 2` of them), `batchFinish`: `f` and
`a` negated if `f < 0` (`|f| = gcd(p, x)`), `p` added twice to `a` if
negative and `a mod p` (now in `[0, 2p)`), then `15 n + 10` modular
doublings (`dblLoop_ok`), the `2^5` each batch's Montgomery reductions took
off, and `x1`, `x2` restored (`finish_ok`; `Rsa.Divstep.invRunS59_result`
for the result).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Divstep (sgn)

/-- The doublings' registers. -/
abbrev dblRegs : List Reg := [.x3, .x4, .x5, .x6, .x8, .x10, .x13, .x14, .x16, .x17, .x7, .x15]

/-- After `j` doublings from `s₀`. -/
structure DInv (s₀ : State) (B : Addr) (Z w n iA iM iT iS : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  x0 : t.gpr .x0 = B
  x11 : t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))
  x12 : t.gpr .x12 = BitVec.ofNat 64 n
  val : wv s₀.mem B (slot w iA) n < wv s₀.mem B (slot w iM) n →
    wv t.mem B (slot w iA) n = wv s₀.mem B (slot w iA) n * 2 ^ j % wv s₀.mem B (slot w iM) n
  frm : Frm B [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)] s₀.mem t.mem
  keep : Keep dblRegs s₀ t
  v : t.v = s₀.v

/-- `K` modular doublings of `[a]` (`n` words, below `m`), counted by `x15`. -/
theorem dblLoop_ok {s : State} {B : Addr} {Z w n K : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iM iT iS : Nat} (hA : iA < 16) (hM : iM < 16)
    (hT : iT < 16) (hS : iS < 16) (dAM : iA ≠ iM) (dAT : iA ≠ iT) (dAS : iA ≠ iS) (dMT : iM ≠ iT)
    (dMS : iM ≠ iS) (dTS : iT ≠ iS) (hK : 0 < K) (hK' : K < 2 ^ 64) (h15 : s.gpr .x15 = BitVec.ofNat 64 K) :
    WP isa (.loop (.seq (dblP iA iM iT iS) (.block [.subImm .x .x15 .x15 1])) (.nonzero .x .x15)) s
      (DInv s B Z w n iA iM iT iS K) := by
  have hn' := hs.nowrap
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have apM : ∀ r ∈ [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)],
      slot w iM + 8 * n ≤ r.1 ∨ r.1 + r.2 ≤ slot w iM := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact slot_apart (w := w) dAM.symm (by omega) (by omega)
    · exact slot_apart (w := w) dMT (by omega) (by omega)
    · exact slot_apart (w := w) dMS (by omega) (by omega)
  refine wp_countdown (N := K) hK' hK (DInv s B Z w n iA iM iT iS) (fun j _ t hI _ => ?_)
    ⟨hs, h0, h11, h12, fun h => by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt h], Frm.refl _ _ _,
      Keep.refl _ _, rfl⟩ h15
  have fM : wv t.mem B (slot w iM) n = wv s.mem B (slot w iM) n := hI.frm.wv_eq apM (by omega)
  refine WP.seq (WP.mono (dblP_ok hI.scr hI.x0 hI.x11 hI.x12 hn1 hn hw hZ hA hM hT hS dAM dAT dAS dMT dMS dTS)
    fun t₁ ⟨v₁, f₁, k₁, vv₁⟩ => WP.mono (WP.vfix (dec_ok t₁ .x15) (by decide)) fun t' ⟨⟨⟨c', m', _⟩, k'⟩, vv'⟩ =>
      ⟨?_, ?_⟩)
  · have k1' := k₁.trans k'
    refine ⟨hI.scr.congr k1'.wr, (k1'.gpr .x0 (by decide)).trans hI.x0, (k1'.gpr .x11 (by decide)).trans hI.x11,
      (k1'.gpr .x12 (by decide)).trans hI.x12, fun h => ?_, ?_, (hI.keep.trans k1').mono (by decide), ?_⟩
    · have hv := hI.val h
      have hlt : wv t.mem B (slot w iA) n < wv t.mem B (slot w iM) n := by
        rw [hv, fM]; exact Nat.mod_lt _ (by omega)
      rw [m', v₁ hlt, hv, fM, Nat.mul_mod_mod, Nat.pow_succ]; congr 1; ac_rfl
    · rw [← m'] at f₁; exact hI.frm.trans f₁
    · rw [vv', vv₁, hI.v]
  · rw [c', k₁.gpr .x15 (by decide)]


/-- `addIfNeg`'s step on signed numbers: the top word's top bit is the sign. -/
theorem addIfNeg_step {n X Y W top p : Nat} (hX : X = W + 2 ^ (64 * n) * top) (hW : W < 2 ^ (64 * n))
    (htop : top < 2 ^ 64) (hY : Y = (X + if 2 ^ 63 ≤ top then p else 0) % 2 ^ (64 * (n + 1)))
    (r₀ : -2 ^ (64 * (n + 1) - 1) ≤ sgn (n + 1) X + if sgn (n + 1) X < 0 then (p : Int) else 0)
    (r₁ : sgn (n + 1) X + (if sgn (n + 1) X < 0 then (p : Int) else 0) < 2 ^ (64 * (n + 1) - 1)) :
    sgn (n + 1) Y = sgn (n + 1) X + if sgn (n + 1) X < 0 then (p : Int) else 0 := by
  have hiff := Divstep.sgn_neg_iff hW htop
  rw [← hX] at hiff
  have hXR : X < 2 ^ (64 * (n + 1)) := by
    have : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
      rw [← Nat.pow_add, show 64 * n + 64 = 64 * (n + 1) by omega]
    have := Nat.mul_le_mul_left (2 ^ (64 * n)) (show top + 1 ≤ 2 ^ 64 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  refine Divstep.sgn_addIfNeg (by omega) hXR ?_ r₀ r₁
  rw [hY]
  by_cases h : sgn (n + 1) X < 0
  · rw [ite_eq_left (hiff.mp h), ite_eq_left h]; push_cast; rfl
  · rw [ite_eq_right (fun h' => h (hiff.mpr h')), ite_eq_right h]; push_cast; rfl

/-- A number of `n + 1` words whose signed value is below `2^(64 n)` and not
negative: that value, and its top word zero. -/
theorem small_of_sgn {n X W top : Nat} {v : Int} (hX : X = W + 2 ^ (64 * n) * top) (hW : W < 2 ^ (64 * n))
    (htop : top < 2 ^ 64) (h : sgn (n + 1) X = v) (h0 : 0 ≤ v) (h1 : v < 2 ^ (64 * n)) :
    (X : Int) = v ∧ (W : Int) = v := by
  have hiff := Divstep.sgn_neg_iff hW htop
  rw [← hX, h] at hiff
  have ht : top < 2 ^ 63 := Nat.lt_of_not_le fun h' => absurd (hiff.mpr h') (by omega)
  have := Divstep.top_sign hW htop
  rw [← hX] at this
  have hx : X < 2 ^ (64 * (n + 1) - 1) := this.mpr ht
  unfold sgn at h
  rw [ite_eq_left hx] at h
  refine ⟨h, ?_⟩
  have : top = 0 := by
    rcases Nat.eq_zero_or_pos top with h' | h'
    · exact h'
    · have := Nat.mul_le_mul_left (2 ^ (64 * n)) h'
      have : (X : Int) < 2 ^ (64 * n) := by rw [h]; exact h1
      have : X < 2 ^ (64 * n) := by exact_mod_cast this
      omega
  subst this
  rw [hX, Nat.mul_zero, Nat.add_zero] at h
  exact h

/-- The end of the batched inverse, after the `3 n + 2` batches: for a good
`p`, `[v] = gcd(p, a)` and `[x₂] a ≡ gcd(p, a) (mod p)`, `[x₂] < p`. -/
theorem finish_ok {C : ICfg} (hC : C.Ok) {s₀ s : State} (hI : LInv C s₀ (3 * C.n + 2) s) :
    WP isa (seqs (batchFinish C.iV C.iU C.iX₂ C.iM C.iT)) s fun t =>
      Scr t C.B C.Z ∧ t.gpr .x0 = C.B ∧ t.gpr .x1 = s₀.gpr .x1 ∧ t.gpr .x2 = s₀.gpr .x2 ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (C.w + 2)) ∧ t.gpr .x12 = BitVec.ofNat 64 C.n ∧
      Frm C.B C.ranges s₀.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s₀ t ∧
      (C.Good → ∀ a, a < 2 ^ (64 * C.n) → C.x = Rsa.Divstep.oddInput C.p a →
        wv t.mem C.B (slot C.w C.iV) C.n = Nat.gcd C.p a ∧
        (C.p : Int) ∣ (wv t.mem C.B (slot C.w C.iX₂) C.n : Int) * a - Nat.gcd C.p a ∧
        wv t.mem C.B (slot C.w C.iX₂) C.n < C.p) := by
  have hn' := hI.scr.nowrap
  have hn1 := hC.n1; have hnw := hC.nw; have hw := hC.w24; have hZ := hC.hZ
  have hZ' : slot C.w 16 + C.B.toNat ≤ 2 ^ 64 := by omega
  have sl : ∀ j < 16, slot C.w j + 8 * (C.w + 2) ≤ C.Z := fun j hj => Nat.le_trans (slot_lt (w := C.w) hj) hZ
  have sV := sl _ hC.hV; have sX₂ := sl _ hC.hX₂; have sM := sl _ hC.hM
  have rg : ∀ {j : Nat} {len : Nat}, (slot C.w j, 8 * (C.w + 2)) ∈ C.ranges → len ≤ 8 * (C.w + 2) →
      ∀ {m m' : Mem}, Outside C.B (slot C.w j) len m m' → Frm C.B C.ranges m m' := fun {j len} hr hl {m m'} o =>
    Frm.of_outside (Outside.mono (o' := slot C.w j) (n' := 8 * (C.w + 2)) o (Nat.le_refl _) (by omega)) hr
  have rV : (slot C.w C.iV, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  have rX₂ : (slot C.w C.iX₂, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  have rT : (slot C.w C.iT, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  have rU : (slot C.w C.iU, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  unfold batchFinish
  rw [show ([Code.block (signMask C.iV), cnegP C.iV, cnegP C.iX₂] ++ addIfNeg C.iX₂ C.iM ++ addIfNeg C.iX₂ C.iM ++
      csubP C.iX₂ C.iM C.iT ++ [.seq (.block dblCount) (.loop (.seq (dblP C.iX₂ C.iM C.iT C.iU)
        (.block [.subImm .x .x15 .x15 1])) (.nonzero .x .x15)), .block [.umov .x .x1 .v19 0, .umov .x .x2 .v19 1]] :
      List (Prog isa)) = [Code.block (signMask C.iV), cnegP C.iV, cnegP C.iX₂] ++ (addIfNeg C.iX₂ C.iM ++
      (addIfNeg C.iX₂ C.iM ++ (csubP C.iX₂ C.iM C.iT ++ [.seq (.block dblCount) (.loop (.seq (dblP C.iX₂ C.iM C.iT C.iU)
        (.block [.subImm .x .x15 .x15 1])) (.nonzero .x .x15)), .block [.umov .x .x1 .v19 0, .umov .x .x2 .v19 1]])))
      by simp only [List.append_assoc]]
  refine wp_seqs_append (by simp) (by simp [addIfNeg]) ?_
  simp only [seqs]
  -- The sign of `f` into `x15`.
  refine WP.seq (WP.mono (signMask_ok hI.scr C.iV hI.x0 hI.x11 hI.x12 hnw hw hC.hV hZ)
    fun s₁ ⟨⟨h15, h7, m₁, v₁⟩, k₁⟩ => ?_)
  rw [signMask_mask] at h15
  have k01 := k₁
  -- `f := |f|`, `a := ±a`.
  refine WP.seq (WP.mono (cnegP_ok (hI.scr.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans hI.x0)
    ((k₁.gpr .x11 (by decide)).trans hI.x11) ((k₁.gpr .x12 (by decide)).trans hI.x12) hnw hw hZ hC.hV h15)
    fun s₂ ⟨e₂, o₂, k₂, v₂⟩ => ?_)
  have k02 := k01.trans k₂
  refine WP.mono (cnegP_ok (hI.scr.congr (k₁.trans k₂).wr) ((k02.gpr .x0 (by decide)).trans hI.x0)
    ((k02.gpr .x11 (by decide)).trans hI.x11) ((k02.gpr .x12 (by decide)).trans hI.x12) hnw hw hZ hC.hX₂
    ((k₂.gpr .x15 (by decide)).trans h15)) fun s₃ ⟨e₃, o₃, k₃, v₃⟩ => ?_
  have k03 := k02.trans k₃
  have sc₃ : Scr s₃ C.B C.Z := hI.scr.congr ((k₁.trans k₂).trans k₃).wr
  -- `p` added to `a` twice if negative.
  refine wp_seqs_append (by simp [addIfNeg]) (by simp [addIfNeg]) (WP.mono (addIfNeg_ok sc₃
    ((k03.gpr .x0 (by decide)).trans hI.x0) ((k03.gpr .x11 (by decide)).trans hI.x11)
    ((k03.gpr .x12 (by decide)).trans hI.x12) hn1 hnw hw hZ hC.hX₂ hC.hM hC.dX₂M) fun s₄ ⟨e₄, o₄, k₄, v₄⟩ => ?_)
  have k04 := k03.trans k₄
  have sc₄ : Scr s₄ C.B C.Z := sc₃.congr k₄.wr
  refine wp_seqs_append (by simp [addIfNeg]) (by simp [csubP]) (WP.mono (addIfNeg_ok sc₄
    ((k04.gpr .x0 (by decide)).trans hI.x0) ((k04.gpr .x11 (by decide)).trans hI.x11)
    ((k04.gpr .x12 (by decide)).trans hI.x12) hn1 hnw hw hZ hC.hX₂ hC.hM hC.dX₂M) fun s₅ ⟨e₅, o₅, k₅, v₅⟩ => ?_)
  have k05 := k04.trans k₅
  have sc₅ : Scr s₅ C.B C.Z := sc₄.congr k₅.wr
  -- `a mod p`.
  refine wp_seqs_append (by simp [csubP]) (by simp) (WP.mono (csubP_ok sc₅
    ((k05.gpr .x0 (by decide)).trans hI.x0) ((k05.gpr .x11 (by decide)).trans hI.x11)
    ((k05.gpr .x12 (by decide)).trans hI.x12) hn1 hnw hw hZ hC.hX₂ hC.hM hC.hT hC.dX₂M hC.dX₂T hC.dMT)
    fun s₆ ⟨e₆, f₆, k₆, v₆⟩ => ?_)
  have k06 := k05.trans k₆
  have sc₆ : Scr s₆ C.B C.Z := sc₅.congr k₆.wr
  simp only [seqs]
  -- The doublings.
  refine WP.seq (WP.seq (WP.mono (WP.vfix (WP.keep [.x15] (Q := fun t =>
      t.gpr .x15 = BitVec.ofNat 64 (15 * C.n + 10) ∧ t.mem = s₆.mem)
      (by
        unfold dblCount
        brun [(k06.gpr .x12 (by decide)).trans hI.x12, shl_ofNat (show C.n * 2 ^ 4 < 2 ^ 64 by omega)]
        apply BitVec.eq_of_toNat_eq
        have := hC.n21
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega)
      (by decide) (by decide) (by decide +kernel)) (by decide +kernel))
    fun s₇ ⟨⟨⟨h15₇, m₇⟩, k₇⟩, v₇⟩ => WP.mono (dblLoop_ok (K := 15 * C.n + 10) (sc₆.congr k₇.wr)
      ((k₇.gpr .x0 (by decide)).trans ((k06.gpr .x0 (by decide)).trans hI.x0))
      ((k₇.gpr .x11 (by decide)).trans ((k06.gpr .x11 (by decide)).trans hI.x11))
      ((k₇.gpr .x12 (by decide)).trans ((k06.gpr .x12 (by decide)).trans hI.x12)) hn1 hnw hw hZ hC.hX₂ hC.hM hC.hT
      hC.hU hC.dX₂M hC.dX₂T hC.dUX₂.symm hC.dMT hC.dUM.symm hC.dUT.symm (by omega) (by omega) h15₇)
    fun s₈ hD => ?_))
  have k07 := k06.trans k₇
  have k08 := k07.trans hD.keep
  -- `x1`, `x2` back.
  refine WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = (s₈.v .v19).extractLsb' 0 64 ∧
      t.gpr .x2 = (s₈.v .v19).extractLsb' 64 64 ∧ t.mem = s₈.mem)
    (by brun [exec_umov_x, RegUpd.v_write, Nat.mul_zero, Nat.mul_one]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨t1, t2, mt⟩, kt⟩ => ?_
  have k0t := hI.keep.trans (k08.trans kt)
  have vv : s₈.v = s.v := by rw [hD.v, v₇, v₆, v₅, v₄, v₃, v₂, v₁]
  refine ⟨hD.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hD.x0, ?_, ?_, (kt.gpr .x11 (by decide)).trans hD.x11,
    (kt.gpr .x12 (by decide)).trans hD.x12, ?_, k0t.mono (by decide), ?_⟩
  · rw [t1, vv]; exact hI.x1s
  · rw [t2, vv]; exact hI.x2s
  · have w6 : Frm C.B C.ranges s₅.mem s₆.mem := Frm.widen f₆ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, rX₂, Nat.le_refl _, by dsimp only; omega⟩
      · exact ⟨_, rT, Nat.le_refl _, by dsimp only; omega⟩
    have w8 : Frm C.B C.ranges s₇.mem s₈.mem := Frm.widen hD.frm fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, rX₂, Nat.le_refl _, by dsimp only; omega⟩
      · exact ⟨_, rT, Nat.le_refl _, by dsimp only; omega⟩
      · exact ⟨_, rU, Nat.le_refl _, by dsimp only; omega⟩
    rw [mt]
    refine hI.frm.trans ?_
    rw [m₁] at o₂
    rw [m₇] at w8
    exact (((((rg rV (by omega) o₂).trans (rg rX₂ (by omega) o₃)).trans (rg rX₂ (by omega) o₄)).trans
      (rg rX₂ (by omega) o₅)).trans w6).trans w8
  · intro G a ha hx
    have hL : 1 ≤ C.n + 1 := by omega
    have hpf : C.pf = C.p := by unfold ICfg.pf; have := G.1; omega
    have hm' : ((C.p : Int) * C.mi.toNat + 1) % 2 ^ 64 = 0 := by
      have := hC.hm; rw [show C.p + (1 - C.p % 2) = C.p by have := G.1; omega] at this; exact this
    have hp1 : (1 : Int) < C.p := by exact_mod_cast G.2
    have est : C.st (3 * C.n + 2) =
        Divstep.invRunS 59 C.p C.mi.toNat (Rsa.Divstep.oddInput C.p a) (3 * C.n + 2) := by
      unfold ICfg.st; rw [hpf, hx]
    obtain ⟨-, rf0, rr⟩ := Rsa.Divstep.invRunS59_result (mi := C.mi.toNat) G.1 G.2 hm' hC.pC ha
    obtain ⟨ra0, ra1, -, -⟩ := Divstep.invRunS_range (N := 59) (p := C.p) (m := C.mi.toNat)
      (x := Rsa.Divstep.oddInput C.p a) (by decide) hp1 hm' (3 * C.n + 2)
    rw [← est] at rf0 rr ra0 ra1
    have hf := hI.f
    have hav := hI.a G
    set f := (C.st (3 * C.n + 2)).f with hfdef
    set av := (C.st (3 * C.n + 2)).a with hadef
    have gp : Nat.gcd C.p a ≤ C.p := Nat.gcd_le_left _ (by omega)
    have pC := hC.pC
    have half : (2 : Int) ^ (64 * C.n) * 2 ≤ 2 ^ (64 * (C.n + 1) - 1) := by
      have : 2 ^ (64 * C.n) * 2 ≤ 2 ^ (64 * (C.n + 1) - 1) := by
        rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
      exact_mod_cast this
    have pC' : (C.p : Int) < 2 ^ (64 * C.n) := by exact_mod_cast pC
    have fabs : |f| = (Nat.gcd C.p a : Int) := by rw [← Int.natCast_natAbs, rf0]
    have fabs' : |f| < 2 ^ (64 * C.n) := by rw [fabs]; omega
    -- Memory between the stages.
    have M₀ := hI.m
    have wsucc : ∀ (m : Mem) (j : Nat), wv m C.B (slot C.w j) (C.n + 1) =
        wv m C.B (slot C.w j) C.n + 2 ^ (64 * C.n) * (word m C.B (slot C.w j + 8 * C.n)).toNat := fun m j => by
      rw [wv]
    have M₃ : wv s₃.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [wv_out o₃ hC.dX₂M (by omega) (by omega) hZ' hC.hM, wv_out o₂ hC.dVM (by omega) (by omega) hZ' hC.hM, m₁, M₀]
    have M₄ : wv s₄.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [wv_out o₄ hC.dX₂M (by omega) (by omega) hZ' hC.hM, M₃]
    have M₅ : wv s₅.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [wv_out o₅ hC.dX₂M (by omega) (by omega) hZ' hC.hM, M₄]
    have apM6 : ∀ r ∈ [(slot C.w C.iX₂, 8 * (C.n + 1)), (slot C.w C.iT, 8 * C.n)],
        slot C.w C.iM + 8 * C.n ≤ r.1 ∨ r.1 + r.2 ≤ slot C.w C.iM := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slot_apart (w := C.w) hC.dX₂M.symm (by omega) (by omega)
      · exact slot_apart (w := C.w) hC.dMT (by omega) (by omega)
    have M₇ : wv s₇.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [m₇, f₆.wv_eq apM6 (by omega), M₅]
    -- `|f|` in `v`.
    have hneg : (2 ^ 63 ≤ (word s.mem C.B (slot C.w C.iV + 8 * C.n)).toNat) ↔ f < 0 := by
      rw [← hf, wsucc]
      exact (Divstep.sgn_neg_iff (wv_lt _ _ _ _) (BitVec.isLt _)).symm
    rw [m₁] at e₂
    have V₂ := Divstep.sgn_cneg hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (by rw [hf]; omega) e₂
    rw [hf] at V₂
    have V₂' : sgn (C.n + 1) (wv s₂.mem C.B (slot C.w C.iV) (C.n + 1)) = |f| := by
      rw [V₂]
      by_cases h : f < 0
      · rw [ite_eq_left (decide_eq_true (hneg.mpr h)), abs_of_neg h]
      · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact fun h' => h (hneg.mp h')), abs_of_nonneg (by omega)]
    obtain ⟨-, V₂n⟩ := small_of_sgn (wsucc _ _) (wv_lt _ _ _ _) (BitVec.isLt _) V₂' (abs_nonneg _) fabs'
    have apV6 : ∀ r ∈ [(slot C.w C.iX₂, 8 * (C.n + 1)), (slot C.w C.iT, 8 * C.n)],
        slot C.w C.iV + 8 * C.n ≤ r.1 ∨ r.1 + r.2 ≤ slot C.w C.iV := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slot_apart (w := C.w) hC.dVX₂ (by omega) (by omega)
      · exact slot_apart (w := C.w) hC.dVT (by omega) (by omega)
    have apV8 : ∀ r ∈ [(slot C.w C.iX₂, 8 * C.n), (slot C.w C.iT, 8 * (C.n + 1)), (slot C.w C.iU, 8 * C.n)],
        slot C.w C.iV + 8 * C.n ≤ r.1 ∨ r.1 + r.2 ≤ slot C.w C.iV := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact slot_apart (w := C.w) hC.dVX₂ (by omega) (by omega)
      · exact slot_apart (w := C.w) hC.dVT (by omega) (by omega)
      · exact slot_apart (w := C.w) hC.dUV.symm (by omega) (by omega)
    have Vt : wv t.mem C.B (slot C.w C.iV) C.n = Nat.gcd C.p a := by
      rw [mt, hD.frm.wv_eq apV8 (by omega), m₇, f₆.wv_eq apV6 (by omega),
        wv_out o₅ hC.dVX₂.symm (by omega) (by omega) hZ' hC.hV, wv_out o₄ hC.dVX₂.symm (by omega) (by omega) hZ' hC.hV,
        wv_out o₃ hC.dVX₂.symm (by omega) (by omega) hZ' hC.hV]
      have := V₂n.trans fabs
      exact_mod_cast this
    refine ⟨Vt, ?_⟩
    -- `±a` in `x₂`.
    have A₂ : wv s₂.mem C.B (slot C.w C.iX₂) (C.n + 1) = wv s.mem C.B (slot C.w C.iX₂) (C.n + 1) := by
      rw [wv_out o₂ hC.dVX₂ (by omega) (by omega) hZ' hC.hX₂, m₁]
    rw [A₂] at e₃
    have A₃ := Divstep.sgn_cneg hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (by rw [hav]; omega) e₃
    rw [hav] at A₃
    set b0 := if f < 0 then -av else av with hb0
    have A₃' : sgn (C.n + 1) (wv s₃.mem C.B (slot C.w C.iX₂) (C.n + 1)) = b0 := by
      rw [A₃]
      by_cases h : f < 0
      · rw [ite_eq_left (decide_eq_true (hneg.mpr h)), hb0, ite_eq_left h]
      · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact fun h' => h (hneg.mp h')), hb0, ite_eq_right h]
    have b0r : -2 * (C.p : Int) < b0 ∧ b0 < 2 * C.p := by
      rw [hb0]; split <;> omega
    -- `p` added if negative, twice.
    rw [M₃] at e₄
    have A₄ := addIfNeg_step (wsucc _ _) (wv_lt _ _ _ _) (BitVec.isLt _) e₄ (by rw [A₃']; split <;> omega)
      (by rw [A₃']; split <;> omega)
    rw [A₃'] at A₄
    set b1 := b0 + if b0 < 0 then (C.p : Int) else 0 with hb1
    have b1r : -(C.p : Int) < b1 ∧ b1 < 2 * C.p := by rw [hb1]; split <;> omega
    rw [M₄] at e₅
    have A₅ := addIfNeg_step (wsucc _ _) (wv_lt _ _ _ _) (BitVec.isLt _) e₅ (by rw [A₄]; split <;> omega)
      (by rw [A₄]; split <;> omega)
    rw [A₄] at A₅
    set b2 := b1 + if b1 < 0 then (C.p : Int) else 0 with hb2
    have b2r : 0 ≤ b2 ∧ b2 < 2 * C.p := by rw [hb2]; split <;> omega
    -- `a mod p`.
    have A₅v : (wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) : Int) = b2 := by
      unfold sgn at A₅
      split at A₅
      · exact A₅
      · have := wv_lt s₅.mem C.B (slot C.w C.iX₂) (C.n + 1)
        have : ((wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) : Nat) : Int) < 2 ^ (64 * (C.n + 1)) := by
          exact_mod_cast this
        omega
    have hlt5 : wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) < 2 * wv s₅.mem C.B (slot C.w C.iM) C.n := by
      rw [M₅]; have := b2r.2; rw [← A₅v] at this; exact_mod_cast this
    have e₆' := e₆ hlt5
    rw [M₅] at e₆'
    set r := wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) % C.p with hr
    have rp : r < C.p := Nat.mod_lt _ (by omega)
    have r6 : wv s₆.mem C.B (slot C.w C.iX₂) C.n = r := by
      have h6 := wsucc s₆.mem C.iX₂
      rw [e₆'] at h6
      have := wv_lt s₆.mem C.B (slot C.w C.iX₂) C.n
      have : 2 ^ (64 * C.n) * (word s₆.mem C.B (slot C.w C.iX₂ + 8 * C.n)).toNat = 0 := by
        rcases Nat.eq_zero_or_pos (word s₆.mem C.B (slot C.w C.iX₂ + 8 * C.n)).toNat with h | h
        · rw [h, Nat.mul_zero]
        · have := Nat.mul_le_mul_left (2 ^ (64 * C.n)) h; omega
      omega
    -- The doublings.
    have r7 : wv s₇.mem C.B (slot C.w C.iX₂) C.n = r := by rw [m₇, r6]
    have x₂t : wv t.mem C.B (slot C.w C.iX₂) C.n = r * 2 ^ (15 * C.n + 10) % C.p := by
      rw [mt, hD.val (by rw [r7, M₇]; exact rp), r7, M₇]
    rw [x₂t, show 15 * C.n + 10 = 5 * (3 * C.n + 2) by omega]
    refine ⟨rr r ?_, Nat.mod_lt _ (by omega)⟩
    -- `r ≡ ±a (mod p)`.
    have : (r : Int) = b2 % C.p := by rw [hr, Int.natCast_emod, A₅v]
    rw [this]
    refine (Int.mod_modEq _ _).trans ?_
    have e : b2 ≡ b0 [ZMOD (C.p : Int)] := by
      rw [hb2, hb1]
      split <;> split <;> simp [Int.ModEq, Int.add_emod_right]
    exact e

end VG.Proof.Rsa.AArch64
