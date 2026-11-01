module

public import VerifiedGarbage.Proof.Rsa.AArch64.InvLoop
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Rsa.AArch64.InvPieces
import VerifiedGarbage.Proof.Rsa.AArch64.InvStage
import VerifiedGarbage.Proof.Divstep.MredWords
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# RSA private keys on AArch64: the start of the batched inverse

`batchInit_ok`: `Keys.batchInit` leaves `LInv` before any batch: `f = m`
(its word `n` cleared), `g = a + (m if a is even)` (`Divstep.oddInput`,
the masked addition in place), `a = 0` and `b = 1` (`n + 2` words),
`d = 1`, `-m⁻¹ mod 2^64` (unique: `minv_unique`) in the lanes of `v18`,
`x1`, `x2` in those of `v19`, and the batches counted in `x15`.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Divstep (sgn)

/-- `x | 1` adds the missing low bit. -/
theorem or_one_eq (x : Nat) : x ||| 1 = x + (1 - x % 2) := by
  have h1 : (x ||| 1) / 2 = x / 2 := by rw [Nat.or_div_two]; simp
  have h2 : (x ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.mpr (.inr rfl)
  omega

/-- Word 0 of a number or'ed with 1. -/
theorem wv_or1 (m : Mem) (B : Addr) {d k : Nat} (h : d + 8 * (k + 1) ≤ 2 ^ 64) :
    wv (m.writeW (off B d) (word m B d ||| 1#64)) B d (k + 1) =
      wv m B d (k + 1) + (1 - wv m B d (k + 1) % 2) := by
  rw [Nat.add_comm k 1, wv_add, wv_add m]
  rw [(writeW_outside m B _ (by omega)).wv (d := d + 8 * 1) (k := k) (Or.inr (by omega)) (by omega)]
  have e1 : ∀ m' : Mem, wv m' B d 1 = (word m' B d).toNat := fun m' => by simp [wv]
  rw [e1, e1, word_writeW_self, BitVec.toNat_or, BitVec.toNat_ofNat, show 1 % 2 ^ 64 = 1 from rfl, or_one_eq]
  have := (word m B d).isLt
  omega

/-- `-p⁻¹ mod 2^64` is unique. -/
theorem minv_unique {p a b : Nat} (hp : p % 2 = 1) (ha : (p * a + 1) % 2 ^ 64 = 0) (hb : (p * b + 1) % 2 ^ 64 = 0)
    (ha' : a < 2 ^ 64) (hb' : b < 2 ^ 64) : a = b := by
  have hc : Nat.Coprime (2 ^ 64) p := Nat.Coprime.pow_left _ (by
    show Nat.gcd 2 p = 1
    rw [Nat.gcd_rec, hp]; rfl)
  wlog h : a ≤ b
  · exact (this hp hb ha hb' ha' hc (by omega)).symm
  have hd : 2 ^ 64 ∣ p * (b - a) := by
    rw [Nat.mul_sub]
    have := Nat.sub_mod_eq_zero_of_mod_eq (show (p * b + 1) % 2 ^ 64 = (p * a + 1) % 2 ^ 64 by omega)
    rw [show p * b + 1 - (p * a + 1) = p * b - p * a by omega] at this
    exact Nat.dvd_of_mod_eq_zero this
  obtain ⟨k, hk⟩ := hc.dvd_of_dvd_mul_left hd
  rcases k with _ | k
  · omega
  · have : 2 ^ 64 * (k + 1) ≥ 2 ^ 64 := Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- Word `n` of an array is apart from the first `n` words of each. -/
theorem top_apart {w n : Nat} (j X : Nat) (hn : n ≤ w) :
    slot w j + 8 * n ≤ slot w X + 8 * n ∨ slot w X + 8 * n + 8 ≤ slot w j := by
  by_cases h : j = X
  · subst h; exact .inl (Nat.le_refl _)
  · rcases slot_apart (w := w) (a := 8 * n) (b := 8 * n + 8) h (by omega) (by omega) with h' | h' <;> omega

/-- A prefix of a zero number is zero. -/
theorem wv_zero_prefix {m : Mem} {B : Addr} {d k j : Nat} (h : wv m B d (k + j) = 0) : wv m B d k = 0 := by
  rw [wv_add] at h; omega

/-- A signed number of `n + 1` words below `2^(64 n + 1)` is its value. -/
theorem sgn_small {n x : Nat} (hx : x < 2 ^ (64 * n + 1)) : sgn (n + 1) x = x := by
  unfold sgn
  rw [ite_eq_left (show x < 2 ^ (64 * (n + 1) - 1) from Nat.lt_of_lt_of_le hx
    (Nat.pow_le_pow_right (by decide) (by omega)))]

/-- The start: `f = m`, `g = a + (m if a is even)`, `a = 0`, `b = 1`,
`d = 1`, `-m⁻¹`, `x1`, `x2` saved, and the batches counted. -/
theorem batchInit_ok {C : ICfg} (hC : C.Ok) {s : State} {a : Nat} (hs : Scr s C.B C.Z) (h0 : s.gpr .x0 = C.B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (C.w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 C.n)
    (hV : wv s.mem C.B (slot C.w C.iV) C.n = C.p) (hM : wv s.mem C.B (slot C.w C.iM) C.n = C.p)
    (hU : wv s.mem C.B (slot C.w C.iU) C.n = a) (hx : C.x = Rsa.Divstep.oddInput C.p a) :
    WP isa (seqs (batchInit C.iV C.iU C.iX₂ C.iX₁ C.iM)) s fun t =>
      LInv C s 0 t ∧ t.gpr .x15 = BitVec.ofNat 64 (3 * C.n + 2) := by
  have hn' := hs.nowrap
  have hn1 := hC.n1; have hnw := hC.nw; have hw := hC.w24; have hZ := hC.hZ
  have sl : ∀ j < 16, slot C.w j + 8 * (C.w + 2) ≤ C.Z := fun j hj => Nat.le_trans (slot_lt (w := C.w) hj) hZ
  have sV := sl _ hC.hV; have sU := sl _ hC.hU; have sM := sl _ hC.hM; have sX₁ := sl _ hC.hX₁
  have sX₂ := sl _ hC.hX₂
  simp only [batchInit, seqs]
  refine WP.seq (WP.mono (initHead_ok hs h0 h11 h12 hn1 hnw hw hZ hC.hV hC.hU hC.dUV.symm)
    fun s₁ ⟨⟨m₁, l0, l1, lv, h8, h5, h10, h15, h7, h14, hc⟩, k₁⟩ => ?_)
  -- The first `n` words of `g` and `m` as on entry.
  have sepUM := slot_apart (w := C.w) (a := 8 * C.n) (b := 8 * C.n) hC.dUM (by omega) (by omega)
  have o₁ : ∀ {j : Nat}, j < 16 → wv s₁.mem C.B (slot C.w j) C.n = wv s.mem C.B (slot C.w j) C.n := fun {j} hj => by
    rw [m₁, (writeW_outside _ C.B _ (by omega)).wv (top_apart j C.iU hnw) (by have := sl _ hj; omega),
      (writeW_outside _ C.B _ (by omega)).wv (top_apart j C.iV hnw) (by have := sl _ hj; omega)]
  have k1 := k₁
  -- `g += m` if `a` is even.
  refine WP.seq (WP.mono (WP.vfix (addMIP_ok (N := C.n) (hs.congr k₁.wr) h10 h8 h5 h14 h15 hc hn1 (by omega)
    (by omega) (by omega) (by omega) (by rcases sepUM with h | h <;> omega) (.inl (Nat.le_refl _))) (by decide +kernel))
    fun s₂ ⟨⟨e₂, h5', o₂, k₂⟩, v₂⟩ => ?_)
  rw [o₁ hC.hM, o₁ hC.hU, hM, hU] at e₂
  have k12 := k₁.trans k₂
  have g7 : s₂.gpr .x7 = 0 := (k₂.gpr .x7 (by decide)).trans h7
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₂.mem.writeW (off C.B (slot C.w C.iU + 8 * C.n))
      (BitVec.ofNat 64 s₂.c.toNat) ∧ t.v = s₂.v)
    (by brun [g7, h5', (hs.congr k12.wr).st (show slot C.w C.iU + 8 * C.n + 8 ≤ C.Z by omega), RegUpd.v_write]
        rw [zero_add64, zero_add64])
    (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨m₃, v₃⟩, k₃⟩ => ?_)
  have par : (word s.mem C.B (slot C.w C.iU)).toNat % 2 = a % 2 := by
    rw [← wv_mod64 _ _ _ hn1, hU, Nat.mod_mod_of_dvd _ (by decide)]
  have gU : wv s₃.mem C.B (slot C.w C.iU) (C.n + 1) = C.x := by
    rw [m₃, wv_writeW_top _ _ _ _ _ (by omega), hx, Rsa.Divstep.oddInput, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by cases s₂.c <;> decide)]
    rw [par] at e₂
    by_cases h : a % 2 = 0
    · simp only [h, decide_true, ite_true] at e₂ ⊢
      rw [e₂, Nat.add_comm]
    · simp only [h, decide_false, Bool.false_eq_true, ite_false, Nat.zero_add, Nat.add_zero] at e₂ ⊢
      exact e₂
  have k13 := k12.trans k₃
  have zA : ∀ {j : Nat} {s' : State}, j < 16 → Scr s' C.B C.Z → s'.gpr .x0 = C.B →
      s'.gpr .x11 = BitVec.ofNat 64 (8 * (C.w + 2)) → s'.gpr .x12 = BitVec.ofNat 64 C.n →
      WP isa (.seq (.block (base j .x8 ++ ([movi .x7 0] : List Instr))) zeroAcc) s' fun t =>
        wv t.mem C.B (slot C.w j) (C.n + 2) = 0 ∧ Outside C.B (slot C.w j) (8 * (C.n + 2)) s'.mem t.mem ∧
        Keep [.x7, .x8, .x14, .x16] s' t ∧ t.v = s'.v := fun {j s'} hj hs' g0 g11 g12 => by
    refine WP.mono (WP.vfix (Q := fun t => wv t.mem C.B (slot C.w j) (C.n + 2) = 0 ∧
      Outside C.B (slot C.w j) (8 * (C.n + 2)) s'.mem t.mem ∧ Keep [.x7, .x8, .x14, .x16] s' t) ?_
      (by simp only [Code.allInstrs_eq, instrs, List.all_append, base_vnone, zeroAcc, countLoop]; decide))
      fun t ⟨a, v⟩ => ⟨a.1, a.2.1, a.2.2, v⟩
    refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok j .x8 g0 g11) fun t₁ ⟨⟨h8', m₁', _⟩, k₁'⟩ =>
      WP.mono (WP.keep [.x7] (Q := fun t => t.gpr .x7 = 0 ∧ t.mem = t₁.mem) (by brun) (by decide) (by decide)
        (by decide +kernel)) fun t₂ ⟨⟨h7', m₂'⟩, k₂'⟩ => ?_))
    have k12' := k₁'.trans k₂'
    refine WP.mono (zeroAcc_ok (hs'.congr k12'.wr) ((k₂'.gpr .x8 (by decide)).trans h8') ((k12'.gpr .x12 (by decide)).trans g12)
      h7' (by omega) (by have := sl _ hj; omega)) fun t ⟨z, o, k⟩ => ⟨z, by rw [m₂', m₁'] at o; exact o,
        (k12'.trans k).mono (by decide)⟩
  refine WP.seq (WP.mono (zA hC.hX₂ (hs.congr k13.wr) ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11) ((k13.gpr .x12 (by decide)).trans h12)) fun s₄ ⟨z₄, o₄, k₄, v₄⟩ => ?_)
  have k14 := k13.trans k₄
  refine WP.seq (WP.mono (zA hC.hX₁ (hs.congr k14.wr) ((k14.gpr .x0 (by decide)).trans h0)
    ((k14.gpr .x11 (by decide)).trans h11) ((k14.gpr .x12 (by decide)).trans h12)) fun s₅ ⟨z₅, o₅, k₅, v₅⟩ => ?_)
  have k15 := k14.trans k₅
  have hp := wv_lt s.mem C.B (slot C.w C.iM) C.n
  rw [hM] at hp
  -- From `s₁` on, only `g`, `a` and `b` change.
  have f2 : Frm C.B [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iX₂, 8 * (C.w + 2)),
      (slot C.w C.iX₁, 8 * (C.w + 2))] s₁.mem s₂.mem :=
    Frm.of_outside (Outside.mono (o' := slot C.w C.iU) (n' := 8 * (C.w + 2)) o₂ (Nat.le_refl _) (by omega)) (by simp)
  have f3 : Frm C.B [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iX₂, 8 * (C.w + 2)),
      (slot C.w C.iX₁, 8 * (C.w + 2))] s₂.mem s₃.mem := by
    rw [m₃]; exact Frm.of_outside (Outside.mono (o' := slot C.w C.iU) (n' := 8 * (C.w + 2))
      (writeW_outside _ C.B _ (by omega)) (by omega) (by omega)) (by simp)
  have f4 : Frm C.B [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iX₂, 8 * (C.w + 2)),
      (slot C.w C.iX₁, 8 * (C.w + 2))] s₃.mem s₄.mem :=
    Frm.of_outside (Outside.mono (o' := slot C.w C.iX₂) (n' := 8 * (C.w + 2)) o₄ (Nat.le_refl _) (by omega)) (by simp)
  have f5 : Frm C.B [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iX₂, 8 * (C.w + 2)),
      (slot C.w C.iX₁, 8 * (C.w + 2))] s₄.mem s₅.mem :=
    Frm.of_outside (Outside.mono (o' := slot C.w C.iX₁) (n' := 8 * (C.w + 2)) o₅ (Nat.le_refl _) (by omega)) (by simp)
  have f15 := ((f2.trans f3).trans f4).trans f5
  have apM := apart3 (w := C.w) (L := C.n) hC.dUM.symm hC.dX₂M.symm hC.dX₁M.symm (by omega) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _)
  have M₅ : wv s₅.mem C.B (slot C.w C.iM) C.n = C.p := by
    rw [f15.wv_eq apM (by omega), o₁ hC.hM, hM]
  refine WP.mono (initLast_ok (hs.congr k15.wr) ((k15.gpr .x0 (by decide)).trans h0)
    ((k15.gpr .x11 (by decide)).trans h11) ((k15.gpr .x12 (by decide)).trans h12) hnw hw hZ hC.hX₁ hC.hM hC.hV
    hC.dX₁M hC.dVX₁) fun t ⟨⟨m₆, l0', lmi, lv', h15'⟩, k₆⟩ => ?_
  have k16 := k15.trans k₆
  have hZ' : slot C.w 16 + C.B.toNat ≤ 2 ^ 64 := by omega
  set mid := s₅.mem.writeW (off C.B (slot C.w C.iX₁)) 1#64 with hmid
  have o₆a : Outside C.B (slot C.w C.iX₁) 8 s₅.mem mid := writeW_outside _ C.B _ (by omega)
  have sVX := slot_apart (w := C.w) (a := 8) (b := 8) hC.dVX₁ (by omega) (by omega)
  have wVm : word s₅.mem C.B (slot C.w C.iV) = word mid C.B (slot C.w C.iV) :=
    (o₆a.word (by rcases sVX with h | h <;> omega) (by omega)).symm
  rw [wVm] at m₆
  have o₆b : Outside C.B (slot C.w C.iV) 8 mid t.mem := by rw [m₆]; exact writeW_outside _ C.B _ (by omega)
  have f6 : Frm C.B C.ranges s₅.mem t.mem :=
    (Frm.of_outside (Outside.mono (o' := slot C.w C.iX₁) (n' := 8 * (C.w + 2)) o₆a (by omega) (by omega))
      (by simp [ICfg.ranges])).trans
    (Frm.of_outside (Outside.mono (o' := slot C.w C.iV) (n' := 8 * (C.w + 2)) o₆b (by omega) (by omega))
      (by simp [ICfg.ranges]))
  -- Arrays other than `f`, `a` and `b` from `s₃` on.
  have late : ∀ {j : Nat} {L : Nat}, j ≠ C.iX₂ → j ≠ C.iX₁ → j ≠ C.iV → L ≤ C.w + 2 → j < 16 →
      wv t.mem C.B (slot C.w j) L = wv s₃.mem C.B (slot C.w j) L := fun {j L} a b c hL hj => by
    rw [wv_out o₆b c.symm (by omega) hL hZ' hj, wv_out o₆a b.symm (by omega) hL hZ' hj,
      wv_out o₅ b.symm (by omega) hL hZ' hj, wv_out o₄ a.symm (by omega) hL hZ' hj]
  have sVU := slot_apart (w := C.w) (a := 8 * (C.n + 1)) (b := 8 * C.n + 8) hC.dUV.symm (by omega) (by omega)
  have sVU0 := slot_apart (w := C.w) (a := 8 * (C.n + 1)) (b := 8 * C.n) hC.dUV.symm (by omega) (by omega)
  have V21 : wv s₂.mem C.B (slot C.w C.iV) (C.n + 1) = wv s₁.mem C.B (slot C.w C.iV) (C.n + 1) :=
    o₂.wv (by rcases sVU0 with h | h <;> omega) (by omega)
  -- `f = m` before its low bit is set.
  have fV₃ : wv s₃.mem C.B (slot C.w C.iV) (C.n + 1) = C.p := by
    rw [m₃, (writeW_outside _ C.B _ (by omega)).wv
      (by rcases sVU with h | h <;> omega) (by omega), V21, m₁,
      (writeW_outside _ C.B _ (by omega)).wv (by rcases sVU with h | h <;> omega) (by omega),
      wv_writeW_top _ _ _ _ _ (by omega), hV]
    rfl
  have fVm : wv mid C.B (slot C.w C.iV) (C.n + 1) = C.p := by
    rw [wv_out o₆a hC.dVX₁.symm (by omega) (by omega) hZ' hC.hV,
      wv_out o₅ hC.dVX₁.symm (by omega) (by omega) hZ' hC.hV, wv_out o₄ hC.dVX₂.symm (by omega) (by omega) hZ' hC.hV,
      fV₃]
  have fV : wv t.mem C.B (slot C.w C.iV) (C.n + 1) = C.pf := by
    rw [m₆, wv_or1 _ _ (by omega), fVm]; rfl
  -- `g`.
  have gU' : wv t.mem C.B (slot C.w C.iU) (C.n + 1) = C.x := by
    rw [late hC.dUX₂ hC.dUX₁ hC.dUV (by omega) hC.hU, gU]
  have aX : wv t.mem C.B (slot C.w C.iX₂) (C.n + 1) = 0 := by
    rw [wv_out o₆b hC.dVX₂ (by omega) (by omega) hZ' hC.hX₂, wv_out o₆a hC.dX (by omega) (by omega) hZ' hC.hX₂,
      wv_out o₅ hC.dX (by omega) (by omega) hZ' hC.hX₂]
    exact wv_zero_prefix (j := 1) z₄
  have bX : wv t.mem C.B (slot C.w C.iX₁) (C.n + 1) = 1 := by
    rw [wv_out o₆b hC.dVX₁ (by omega) (by omega) hZ' hC.hX₁]
    have e := wv_add mid C.B (slot C.w C.iX₁) 1 C.n
    have z := wv_add s₅.mem C.B (slot C.w C.iX₁) 1 (C.n + 1)
    rw [show 1 + (C.n + 1) = C.n + 2 by omega, z₅] at z
    have z' : wv s₅.mem C.B (slot C.w C.iX₁ + 8 * 1) C.n = 0 := wv_zero_prefix (j := 1) (by omega)
    rw [Nat.add_comm 1 C.n] at e
    rw [e, hmid, (writeW_outside _ C.B _ (by omega)).wv (d := slot C.w C.iX₁ + 8 * 1) (k := C.n) (by omega) (by omega), z']
    simp only [wv, Nat.mul_zero, Nat.add_zero, word_writeW_self, Nat.zero_add, Nat.pow_zero, Nat.one_mul]; rfl
  have hpN : C.pf < 2 ^ (64 * C.n + 1) := by have := hC.pC; unfold ICfg.pf; rw [Nat.pow_succ]; omega
  have v15 : t.v .v19 = s₁.v .v19 := by rw [lv' _ (by decide), v₅, v₄, v₃, v₂]
  have hw0 : (word s₅.mem C.B (slot C.w C.iM) ||| 1#64).toNat = C.pf % 2 ^ 64 := by
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, show 1 % 2 ^ 64 = 1 from rfl, or_one_eq, ← wv_mod64 _ _ _ hn1, M₅]
    have := hC.pC
    unfold ICfg.pf
    have h64 : C.p % 2 ^ 64 % 2 = C.p % 2 := Nat.mod_mod_of_dvd _ (by decide)
    have : C.p % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    rw [h64]
    omega
  refine ⟨⟨hs.congr k16.wr, (k16.gpr .x0 (by decide)).trans h0, (k16.gpr .x11 (by decide)).trans h11,
    (k16.gpr .x12 (by decide)).trans h12,
    by rw [fV, sgn_small hpN]; simp only [ICfg.st, Divstep.invRunS],
    by rw [gU', sgn_small hC.xC]; simp only [ICfg.st, Divstep.invRunS],
    fun _ => by rw [aX, sgn_small (Nat.two_pow_pos (64 * C.n + 1))]; simp only [ICfg.st, Divstep.invRunS]; rfl,
    fun _ => by rw [bX, sgn_small (Nat.one_lt_two_pow (by omega))]; simp only [ICfg.st, Divstep.invRunS]; rfl,
    by rw [l0']; simp only [ICfg.st, Divstep.invRunS]; decide, ?_, ?_, ?_, k16.mono (by decide),
    by rw [laneOf, v15, ← laneOf, l0], by rw [laneOf, v15, ← laneOf, l1]⟩, h15'⟩
  · apply BitVec.eq_of_toNat_eq
    refine minv_unique (p := C.pf % 2 ^ 64) (by unfold ICfg.pf; omega) (by rw [← hw0]; exact lmi) ?_
      (BitVec.isLt _) (BitVec.isLt _)
    have := hC.hm
    have h' : (C.pf * C.mi.toNat + 1) % 2 ^ 64 = 0 := by unfold ICfg.pf; exact_mod_cast this
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]; exact h'
  · rw [wv_out o₆b hC.dVM (by omega) (by omega) hZ' hC.hM, wv_out o₆a hC.dX₁M (by omega) (by omega) hZ' hC.hM,
      M₅]
  · have f01 : Frm C.B C.ranges s.mem s₁.mem := by
      rw [m₁]
      exact (Frm.of_outside (Outside.mono (o' := slot C.w C.iV) (n' := 8 * (C.w + 2))
        (writeW_outside _ C.B _ (by omega)) (by omega) (by omega)) (by simp [ICfg.ranges])).trans
        (Frm.of_outside (Outside.mono (o' := slot C.w C.iU) (n' := 8 * (C.w + 2))
        (writeW_outside _ C.B _ (by omega)) (by omega) (by omega)) (by simp [ICfg.ranges]))
    exact (f01.trans (Frm.widen f15 (fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [ICfg.ranges], Nat.le_refl _, Nat.le_refl _⟩))).trans f6
end VG.Proof.Rsa.AArch64