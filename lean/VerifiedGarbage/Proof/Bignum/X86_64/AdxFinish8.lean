import VerifiedGarbage.Impl.Bignum.X86_64.AdxFinish8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock

/-!
# Clearing the window and the final subtraction, eight words at a time

`zeroWin8_ok` is `zeroWin_ok`, and `finish8V_ok` `AdxSquare.finishV_ok`, for
`w` a multiple of 8. Each loop's iteration runs eight steps proved once
for any word `k` of the iteration (`zst_ok`, `sst_ok`, `cst_ok`) and
composed by induction on `k`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- `[b + 8 j + 8 k]`, as `xrun` leaves it. -/
theorem addrDk {p : Addr} {e j : Nat} (k : Nat) :
    off p e + BitVec.ofNat 64 j * BitVec.ofNat 64 8 + BitVec.ofInt 64 (8 * (k : Int)) =
      off p (e + 8 * j + 8 * k) := by
  rw [show (8 * (k : Int)) = ((8 * k : Nat) : Int) by push_cast; rfl]
  exact addrD (8 * k)

/-- `add r14, 8; cmp r14, r` from `8 i`, for `r` holding `8 N`. -/
theorem count8_ok (s : State) {r : Reg} (hr : r ≠ .r14) {i N : Nat}
    (hj : s.gpr .r14 = BitVec.ofNat 64 (8 * i)) (hN : s.gpr r = BitVec.ofNat 64 (8 * N))
    (hiN : 8 * (i + 1) < 2 ^ 64) (hN' : 8 * N < 2 ^ 64) :
    WP isa (.block [.alu .add .r14 (.imm 8), .alu .cmp .r14 (.reg r)]) s fun s' =>
      s'.zf = some (decide (i + 1 = N)) ∧ s'.gpr .r14 = BitVec.ofNat 64 (8 * (i + 1)) ∧
      s'.mem = s.mem ∧ Keep [.r14] s s' := by
  have h8 : BitVec.ofNat 64 (8 * i) + 8 = BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
    congr 1
  have he : decide (8 * (i + 1) = 8 * N) = decide (i + 1 = N) := by
    by_cases h : i + 1 = N <;> simp [h] <;> omega_using [h]
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.zf = some (decide (i + 1 = N)) ∧
    s'.gpr .r14 = BitVec.ofNat 64 (8 * (i + 1)) ∧ s'.mem = s.mem) ?_ rfl) fun s' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [hj, hN, hr, h8, ofNat_sub_beq hiN hN', he]

/-! ## Clearing the window -/

/-- `j` words cleared from `A`, nothing else written. -/
structure Zw (s₀ : State) (B : Addr) (Z A : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rcx, .r14] s₀ t
  out : Outside B A (8 * j) s₀.mem t.mem
  val : ∀ k < j, word t.mem B (A + 8 * k) = 0

/-- The store of word `k` of iteration `i`. -/
theorem zst_ok {s₀ t : State} {B : Addr} {Z A i k : Nat} (hax : t.gpr .rax = 0)
    (h8 : t.gpr .r8 = off B A) (h14 : t.gpr .r14 = BitVec.ofNat 64 (8 * i))
    (hI : Zw s₀ B Z A (8 * i + k) t) (hk : A + 8 * (8 * i + k) + 8 ≤ Z) :
    WP isa (.block [.store (ix .r8 .r14 (8 * k)) .rax]) t fun t' =>
      Zw s₀ B Z A (8 * i + k + 1) t' ∧ t'.gpr = t.gpr := by
  have hn := hI.scr.nowrap
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (off B (A + 8 * (8 * i + k))) (0 : BitVec 64) ∧
      t'.gpr = t.gpr) ?_ rfl) fun t' ⟨⟨hm, hg⟩, k'⟩ => ⟨?_, hg⟩
  · have ha : off B (A + 8 * (8 * i) + 8 * k) = off B (A + 8 * (8 * i + k)) := by congr 1; omega_using []
    xrun [State.ea, ix, h8, h14, addrDk, ha, hI.scr.st hk, hax]
  have o' := writeW_outside t.mem B (0 : BitVec 64) (d := A + 8 * (8 * i + k)) (by omega_arith)
  refine ⟨hI.scr.congr k'.2.2, (hI.keep.trans k').mono (by decide), ?_, fun j hj => ?_⟩
  · rw [hm]
    exact (hI.out.mono (o' := A) (n' := 8 * (8 * i + k + 1)) (Nat.le_refl _) (by omega_using [])).trans
      (o'.mono (o' := A) (n' := 8 * (8 * i + k + 1)) (by omega_using []) (by omega_using []))
  · rw [hm]
    by_cases hj' : j = 8 * i + k
    · subst hj'; exact word_writeW_self _ _ _ _
    · rw [o'.word (by omega_using [hj']) (by omega_using [hk, hn, hj])]; exact hI.val j (by omega_using [hj, hj'])

/-- The first `n` stores of iteration `i`. -/
theorem zsts_ok {s₀ : State} {B : Addr} {Z A i : Nat} : ∀ n ≤ 8, ∀ {t : State}, t.gpr .rax = 0 →
    t.gpr .r8 = off B A → t.gpr .r14 = BitVec.ofNat 64 (8 * i) → Zw s₀ B Z A (8 * i) t →
    A + 8 * (8 * i + n) ≤ Z →
    WP isa (.block ((List.range n).map fun (k : Nat) => .store (ix .r8 .r14 (8 * (k : Int))) .rax)) t fun t' =>
      Zw s₀ B Z A (8 * i + n) t' ∧ t'.gpr = t.gpr
  | 0, _, t, _, _, _, hI, _ => WP.block_nil_iff.mpr ⟨hI, rfl⟩
  | n + 1, hn, t, hax, h8, h14, hI, hZ => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zsts_ok n (by omega_using [hn]) hax h8 h14 hI (by omega_using [hZ])) fun t₁ ⟨h₁, g₁⟩ => ?_
    refine WP.mono (zst_ok (k := n) (by rw [g₁]; exact hax) (by rw [g₁]; exact h8) (by rw [g₁]; exact h14) h₁
      (by omega_using [hZ])) fun t' ⟨h', g'⟩ => ⟨h', g'.trans g₁⟩

/-- `zeroWin8`: `zeroWin`'s result, for `w` a multiple of 8. -/
theorem zeroWin8_ok {s : State} {B : Addr} {Z w n A : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B A)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w) (hwN : w = 8 * n) (hn : 0 < n) (hw : w < 2 ^ 60)
    (hA : A + 8 * (2 * w + 2) ≤ Z) :
    WP isa zeroWin8 s fun t => (∀ k < 2 * w + 2, word t.mem B (A + 8 * k) = 0) ∧
      Outside B A (8 * (2 * w + 2)) s.mem t.mem ∧ Keep [.rax, .rcx, .r14] s t := by
  have hnw := hs.nowrap
  unfold zeroWin8
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx, .r14] (Q := fun t => t.gpr .rax = 0 ∧
      t.gpr .rcx = BitVec.ofNat 64 (8 * (2 * n)) ∧ t.gpr .r14 = BitVec.ofNat 64 (8 * 0) ∧ t.mem = s.mem) ?_ rfl)
    fun s₁ ⟨⟨hax, hcx, h14, hm₁⟩, k₁⟩ => ?_)
  · have : BitVec.ofNat 64 w + BitVec.ofNat 64 w = BitVec.ofNat 64 (8 * (2 * n)) := by
      rw [← BitVec.ofNat_add]; congr 1; omega_using [hwN]
    xrun [hbx, this]
  have s₁8 : s₁.gpr .r8 = off B A := (k₁.gpr (by decide)).trans h8
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := 2 * n) (by omega_using [hn])
    (fun i t => Zw s B Z A (8 * i) t ∧ t.gpr .r14 = BitVec.ofNat 64 (8 * i) ∧ t.gpr .rax = 0 ∧
      t.gpr .rcx = BitVec.ofNat 64 (8 * (2 * n)) ∧ t.gpr .r8 = off B A) ?_ (fun _ h => h)
    ⟨⟨hs.congr k₁.2.2, k₁, by rw [hm₁]; exact Outside.refl _ _ _ _, fun k hk => absurd hk (by omega_using [])⟩,
      h14, hax, hcx, s₁8⟩)
    fun t ⟨hI, h14', tax, tcx, t8⟩ => ?_)
  · intro i _ hi t ⟨hI, h14', tax, tcx, t8⟩
    rw [WP.block_append_iff]
    refine WP.mono (zsts_ok 8 (Nat.le_refl _) tax t8 h14' hI (by omega_using [hwN, hA, hi])) fun t₁ ⟨h₁, g₁⟩ => ?_
    refine WP.mono (count8_ok t₁ (r := .rcx) (by decide) (by rw [g₁]; exact h14') (by rw [g₁]; exact tcx)
      (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14'', hm', k'⟩ => ⟨hz, ?_, h14'', ?_, ?_, ?_⟩
    · refine ⟨h₁.scr.congr k'.2.2, (h₁.keep.trans k').mono (by decide), hm' ▸ ?_, fun j hj => hm' ▸ h₁.val j ?_⟩
      · rw [show 8 * (i + 1) = 8 * i + 8 by omega_using []]; exact h₁.out
      · omega_using [hj]
    · rw [k'.gpr (by decide), g₁]; exact tax
    · rw [k'.gpr (by decide), g₁]; exact tcx
    · rw [k'.gpr (by decide), g₁]; exact t8
  -- The last two words.
  refine WP.mono (zsts_ok (i := 2 * n) 2 (by omega_using []) tax t8 h14' hI (by omega_arith)) fun t' ⟨h', g'⟩ => ?_
  rw [show 8 * (2 * n) + 2 = 2 * w + 2 by omega_using [hwN]] at h'
  exact ⟨h'.val, h'.out, h'.keep⟩

/-! ## `T - m` -/

/-- Within an iteration: `j` words of `T - m` at `eT`, the borrow in the
carry flag. -/
structure Sb (s₀ : State) (B : Addr) (Z eA eN eT : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  out : Outside B eT (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.cf = some c ∧
    wv t.mem B eT j + wv s₀.mem B eN j = wv s₀.mem B eA j + 2 ^ (64 * j) * c.toNat

/-- Word `k` of iteration `i` of `T - m`. -/
theorem sst_ok {s₀ t : State} {B : Addr} {Z eA eN eT i k : Nat}
    (h8 : t.gpr .r8 = off B eA) (h10 : t.gpr .r10 = off B eN) (hsi : t.gpr .rsi = off B eT)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 (8 * i)) (hI : Sb s₀ B Z eA eN eT (8 * i + k) t)
    (hA : eA + 8 * (8 * i + k) + 8 ≤ Z) (hN : eN + 8 * (8 * i + k) + 8 ≤ Z) (hT : eT + 8 * (8 * i + k) + 8 ≤ Z)
    (sA : eT + 8 * (8 * i + k) + 8 ≤ eA ∨ eA + 8 * (8 * i + k) + 8 ≤ eT)
    (sN : eT + 8 * (8 * i + k) + 8 ≤ eN ∨ eN + 8 * (8 * i + k) + 8 ≤ eT) :
    WP isa (.block (subWord8 k)) t fun t' => Sb s₀ B Z eA eN eT (8 * i + k + 1) t' ∧
      t'.gpr .r8 = t.gpr .r8 ∧ t'.gpr .r10 = t.gpr .r10 ∧ t'.gpr .rsi = t.gpr .rsi ∧ t'.gpr .r14 = t.gpr .r14 := by
  have hn := hI.scr.nowrap
  obtain ⟨c, hc, hval⟩ := hI.val
  have ea : ∀ e, off B (e + 8 * (8 * i) + 8 * k) = off B (e + 8 * (8 * i + k)) := fun e => by congr 1; omega_using []
  unfold subWord8
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.cf = some c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (eT + 8 * (8 * i + k))) r ∧
        r.toNat + (word t.mem B (eN + 8 * (8 * i + k))).toNat + c.toNat =
          (word t.mem B (eA + 8 * (8 * i + k))).toNat + 2 ^ 64 * c'.toNat) ?_ rfl) fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · xrun [State.ea, ix, h8, h10, hsi, h14, addrDk, ea, hc,
      hI.scr.ld hA, hI.scr.ld hN, hI.scr.st hT]
    exact ⟨_, rfl, sbb_toNat _ _ _⟩
  have hx : word t.mem B (eA + 8 * (8 * i + k)) = word s₀.mem B (eA + 8 * (8 * i + k)) := hI.out.word
      (by omega_using [sA]) (by omega_using [hA, hn])
  have hy : word t.mem B (eN + 8 * (8 * i + k)) = word s₀.mem B (eN + 8 * (8 * i + k)) := hI.out.word (by omega_using [sN]) (by omega_arith)
  rw [hx, hy] at hr
  refine ⟨⟨hI.scr.congr k₁.2.2, (hI.keep.trans k₁).mono (by decide), ?_, ⟨c', h₁, ?_⟩⟩,
    k₁.gpr (by decide), k₁.gpr (by decide), k₁.gpr (by decide), k₁.gpr (by decide)⟩
  · rw [hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega_using [hT, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hm, wv_writeW_top _ _ _ _ _ (by omega_using [hT, hn])]
    simp only [wv]
    rw [pow64_succ]
    grind

/-- The first `n` words of iteration `i` of `T - m`. -/
theorem ssts_ok {s₀ : State} {B : Addr} {Z eA eN eT i : Nat} : ∀ n ≤ 8, ∀ {t : State},
    t.gpr .r8 = off B eA → t.gpr .r10 = off B eN → t.gpr .rsi = off B eT →
    t.gpr .r14 = BitVec.ofNat 64 (8 * i) → Sb s₀ B Z eA eN eT (8 * i) t →
    eA + 8 * (8 * i + n) ≤ Z → eN + 8 * (8 * i + n) ≤ Z → eT + 8 * (8 * i + n) ≤ Z →
    (eT + 8 * (8 * i + n) ≤ eA ∨ eA + 8 * (8 * i + n) ≤ eT) →
    (eT + 8 * (8 * i + n) ≤ eN ∨ eN + 8 * (8 * i + n) ≤ eT) →
    WP isa (.block ((List.range n).flatMap subWord8)) t fun t' => Sb s₀ B Z eA eN eT (8 * i + n) t' ∧
      t'.gpr .r8 = t.gpr .r8 ∧ t'.gpr .r10 = t.gpr .r10 ∧ t'.gpr .rsi = t.gpr .rsi ∧ t'.gpr .r14 = t.gpr .r14
  | 0, _, t, _, _, _, _, hI, _, _, _, _, _ => WP.block_nil_iff.mpr ⟨hI, rfl, rfl, rfl, rfl⟩
  | n + 1, hn, t, h8, h10, hsi, h14, hI, hA, hN, hT, sA, sN => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ssts_ok n (by omega_using [hn]) h8 h10 hsi h14 hI (by omega_using [hA]) (by omega_using [hN])
        (by omega_using [hT]) (by omega_using [sA]) (by omega_using [sN]))
      fun t₁ ⟨h₁, g8, g10, gsi, g14⟩ => ?_
    refine WP.mono (sst_ok (k := n) (g8.trans h8) (g10.trans h10) (gsi.trans hsi) (g14.trans h14) h₁
      (by omega_using [hA]) (by omega_using [hN]) (by omega_using [hT]) (by omega_using [sA])
          (by omega_using [sN])) fun t' ⟨h', e8, e10, esi, e14⟩ =>
      ⟨h', e8.trans g8, e10.trans g10, esi.trans gsi, e14.trans g14⟩

/-- `subMod8`: `subMod`'s result, for `w` a multiple of 8. -/
theorem subMod8_ok {s : State} {B : Addr} {Z w n eA eN eT : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (h10 : s.gpr .r10 = off B eN) (hsi : s.gpr .rsi = off B eT)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hwN : w = 8 * n) (hn : 0 < n) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 1) ≤ Z) (hN : eN + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z)
    (sA : eT + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ eT) (sN : eT + 8 * w ≤ eN ∨ eN + 8 * w ≤ eT) :
    WP isa subMod8 s fun t => ∃ c lt : Bool, t.gpr .rbp = mask lt ∧
      lt = decide ((word s.mem B (eA + 8 * w)).toNat < c.toNat) ∧
      wv t.mem B eT w + wv s.mem B eN w = wv s.mem B eA w + 2 ^ (64 * w) * c.toNat ∧
      Outside B eT (8 * w) s.mem t.mem ∧ Keep [.rax, .rbp, .r14] s t := by
  have hnw := hs.nowrap
  subst hwN
  unfold subMod8
  refine WP.seq (WP.mono (WP.keep [.rbp, .r14] (Q := fun t => t.gpr .rbp = mask false ∧
      t.gpr .r14 = BitVec.ofNat 64 (8 * 0) ∧ t.mem = s.mem) (by xrun) rfl)
    fun s₁ ⟨⟨hbp, h14, hm₁⟩, k₁⟩ => ?_)
  have s₁8 : s₁.gpr .r8 = off B eA := (k₁.gpr (by decide)).trans h8
  have s₁10 : s₁.gpr .r10 = off B eN := (k₁.gpr (by decide)).trans h10
  have s₁si : s₁.gpr .rsi = off B eT := (k₁.gpr (by decide)).trans hsi
  have s₁12 : s₁.gpr .r12 = BitVec.ofNat 64 (8 * n) := (k₁.gpr (by decide)).trans h12
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := n) hn
    (fun i t => SubInv s₁ B Z eA eN eT (8 * i) t) ?_ (fun _ h => h)
    ⟨hs.congr k₁.2.2, Keep.refl _ _, h14, Outside.refl _ _ _ _, ⟨false, hbp, rfl⟩⟩)
    fun t hI => ?_)
  · intro i _ hi t hI
    have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans s₁8
    have t10 : t.gpr .r10 = off B eN := (hI.keep.gpr (by decide)).trans s₁10
    have tsi : t.gpr .rsi = off B eT := (hI.keep.gpr (by decide)).trans s₁si
    have t12 : t.gpr .r12 = BitVec.ofNat 64 (8 * n) := (hI.keep.gpr (by decide)).trans s₁12
    obtain ⟨c, hc, hval⟩ := hI.val
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (WP.keep [.rbp] (Q := fun t₁ => t₁.cf = some c ∧ t₁.mem = t.mem) (by
      unfold cfFromRbp; xrun [hc, cf_mask]) rfl) fun t₁ ⟨⟨c₁, m₁⟩, k₁'⟩ => ?_
    have hS : Sb s₁ B Z eA eN eT (8 * i) t₁ :=
      ⟨hI.scr.congr k₁'.2.2, (hI.keep.trans k₁').mono (by decide), m₁ ▸ hI.out, ⟨c, c₁, m₁ ▸ hval⟩⟩
    refine WP.mono (ssts_ok (i := i) 8 (Nat.le_refl _) ((k₁'.gpr (by decide)).trans t8)
      ((k₁'.gpr (by decide)).trans t10) ((k₁'.gpr (by decide)).trans tsi)
      ((k₁'.gpr (by decide)).trans hI.r14) hS (by omega_using [hA, hi]) (by omega_using [hN, hi])
          (by omega_using [hT, hi]) (by omega_using [sA, hi]) (by omega_using [sN, hi]))
      fun t₂ ⟨h₂, e8, e10, esi, e14⟩ => ?_
    obtain ⟨c₂, hc₂, hval₂⟩ := h₂.val
    rw [show ([cfToRbp, .alu .add .r14 (.imm 8), .alu .cmp .r14 (.reg .r12)] : List Instr) =
      [cfToRbp] ++ [.alu .add .r14 (.imm 8), .alu .cmp .r14 (.reg .r12)] from rfl, WP.block_append_iff]
    refine WP.mono (WP.keep [.rbp] (Q := fun t₃ => t₃.gpr .rbp = mask c₂ ∧ t₃.mem = t₂.mem) (by
      unfold cfToRbp; xrun [hc₂]; rfl) rfl) fun t₃ ⟨⟨b₃, m₃⟩, k₃⟩ => ?_
    have t₃14 : t₃.gpr .r14 = BitVec.ofNat 64 (8 * i) :=
      (k₃.gpr (by decide)).trans (e14.trans ((k₁'.gpr (by decide)).trans hI.r14))
    have t₃12 : t₃.gpr .r12 = BitVec.ofNat 64 (8 * n) :=
      (k₃.gpr (by decide)).trans ((h₂.keep.gpr (by decide)).trans s₁12)
    refine WP.mono (count8_ok t₃ (r := .r12) (by decide) t₃14 t₃12 (by omega_using [hw', hi]) (by omega_using [hw']))
      fun t' ⟨hz, h14', hm', k'⟩ => ⟨hz, ?_⟩
    rw [show 8 * i + 8 = 8 * (i + 1) by omega_using []] at hval₂
    refine ⟨h₂.scr.congr (k'.2.2.trans k₃.2.2), ((h₂.keep.trans k₃).trans k').mono (by decide), h14',
      ?_, ⟨c₂, (k'.gpr (by decide)).trans b₃, by rw [hm', m₃]; exact hval₂⟩⟩
    rw [hm', m₃, show 8 * (i + 1) = 8 * i + 8 by omega_using []]; exact h₂.out
  obtain ⟨c, hc, hval⟩ := hI.val
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans s₁8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 (8 * n) := (hI.keep.gpr (by decide)).trans s₁12
  have hX : word t.mem B (eA + 8 * (8 * n)) = word s.mem B (eA + 8 * (8 * n)) := by
    rw [hI.out.word (by omega_using [sA]) (by omega_using [hnw, hA]), hm₁]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rbp = mask (decide ((word s.mem B (eA + 8 * (8 * n))).toNat < c.toNat)))
    (by
      unfold cfFromRbp cfToRbp
      xrun [State.ea, ix, addr0 t8 t12, hc, cf_mask, hI.scr.ld (show eA + 8 * (8 * n) + 8 ≤ Z by omega_using [hA]), hX, sx0]
      simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add]
      rfl) rfl) fun t' ⟨⟨hm', hbp'⟩, k'⟩ => ?_
  refine ⟨c, _, hbp', rfl, ?_, ?_, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · rw [hm', ← hm₁]; exact hval
  · rw [hm', ← hm₁]; exact hI.out

/-! ## The selection -/

/-- Within an iteration: `j` words selected into `eo`, the mask's bit in the
carry flag. -/
structure Sl (s₀ : State) (B : Addr) (Z eA eT eo : Nat) (lt : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  cf : t.cf = some lt
  out : Outside B eo (8 * j) s₀.mem t.mem
  val : wv t.mem B eo j = if lt then wv s₀.mem B eA j else wv s₀.mem B eT j

/-- Word `k` of iteration `i` of the selection. -/
theorem cst_ok {s₀ t : State} {B : Addr} {Z eA eT eo i k : Nat} {lt : Bool}
    (h8 : t.gpr .r8 = off B eA) (hsi : t.gpr .rsi = off B eT) (hbx : t.gpr .rbx = off B eo)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 (8 * i)) (hI : Sl s₀ B Z eA eT eo lt (8 * i + k) t)
    (hA : eA + 8 * (8 * i + k) + 8 ≤ Z) (hT : eT + 8 * (8 * i + k) + 8 ≤ Z) (ho : eo + 8 * (8 * i + k) + 8 ≤ Z)
    (sA : eo + 8 * (8 * i + k) + 8 ≤ eA ∨ eA + 8 * (8 * i + k) + 8 ≤ eo)
    (sT : eo + 8 * (8 * i + k) + 8 ≤ eT ∨ eT + 8 * (8 * i + k) + 8 ≤ eo) :
    WP isa (.block (selWord8 k)) t fun t' => Sl s₀ B Z eA eT eo lt (8 * i + k + 1) t' ∧
      t'.gpr .r8 = t.gpr .r8 ∧ t'.gpr .rsi = t.gpr .rsi ∧ t'.gpr .rbx = t.gpr .rbx ∧ t'.gpr .r14 = t.gpr .r14 := by
  have hn := hI.scr.nowrap
  have ea : ∀ e, off B (e + 8 * (8 * i) + 8 * k) = off B (e + 8 * (8 * i + k)) := fun e => by congr 1; omega_using []
  have hx : word t.mem B (eA + 8 * (8 * i + k)) = word s₀.mem B (eA + 8 * (8 * i + k)) := hI.out.word
      (by omega_using [sA]) (by omega_using [hA, hn])
  have hy : word t.mem B (eT + 8 * (8 * i + k)) = word s₀.mem B (eT + 8 * (8 * i + k)) := hI.out.word
      (by omega_using [sT]) (by omega_using [hT, hn])
  unfold selWord8
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ => t₁.cf = t.cf ∧ t₁.mem = t.mem.writeW (off B (eo + 8 * (8 * i + k)))
      (if lt then word s₀.mem B (eA + 8 * (8 * i + k)) else word s₀.mem B (eT + 8 * (8 * i + k)))) ?_ rfl)
    fun t₁ ⟨⟨c₁, hm⟩, k₁⟩ => ?_
  · have hcf := hI.cf
    cases lt <;>
    xrun [State.ea, ix, h8, hsi, hbx, h14, addrDk, ea, execCmov, eval, hcf,
      hI.scr.ld hA, hI.scr.ld hT, hI.scr.st ho]
    · rw [← hy]
    · rw [← hx]
  refine ⟨⟨hI.scr.congr k₁.2.2, (hI.keep.trans k₁).mono (by decide), c₁.trans hI.cf, ?_, ?_⟩,
    k₁.gpr (by decide), k₁.gpr (by decide), k₁.gpr (by decide), k₁.gpr (by decide)⟩
  · rw [hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [ho, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hm, wv_writeW_top _ _ _ _ _ (by omega_using [ho, hn]), hI.val]
    cases lt <;> simp [wv]

/-- The first `n` words of iteration `i` of the selection. -/
theorem csts_ok {s₀ : State} {B : Addr} {Z eA eT eo i : Nat} {lt : Bool} : ∀ n ≤ 8, ∀ {t : State},
    t.gpr .r8 = off B eA → t.gpr .rsi = off B eT → t.gpr .rbx = off B eo →
    t.gpr .r14 = BitVec.ofNat 64 (8 * i) → Sl s₀ B Z eA eT eo lt (8 * i) t →
    eA + 8 * (8 * i + n) ≤ Z → eT + 8 * (8 * i + n) ≤ Z → eo + 8 * (8 * i + n) ≤ Z →
    (eo + 8 * (8 * i + n) ≤ eA ∨ eA + 8 * (8 * i + n) ≤ eo) →
    (eo + 8 * (8 * i + n) ≤ eT ∨ eT + 8 * (8 * i + n) ≤ eo) →
    WP isa (.block ((List.range n).flatMap selWord8)) t fun t' => Sl s₀ B Z eA eT eo lt (8 * i + n) t' ∧
      t'.gpr .r8 = t.gpr .r8 ∧ t'.gpr .rsi = t.gpr .rsi ∧ t'.gpr .rbx = t.gpr .rbx ∧ t'.gpr .r14 = t.gpr .r14
  | 0, _, t, _, _, _, _, hI, _, _, _, _, _ => WP.block_nil_iff.mpr ⟨hI, rfl, rfl, rfl, rfl⟩
  | n + 1, hn, t, h8, hsi, hbx, h14, hI, hA, hT, ho, sA, sT => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (csts_ok n (by omega_using [hn]) h8 hsi hbx h14 hI (by omega_using [hA]) (by omega_using [hT])
        (by omega_using [ho]) (by omega_using [sA]) (by omega_using [sT]))
      fun t₁ ⟨h₁, g8, gsi, gbx, g14⟩ => ?_
    refine WP.mono (cst_ok (k := n) (g8.trans h8) (gsi.trans hsi) (gbx.trans hbx) (g14.trans h14) h₁
      (by omega_using [hA]) (by omega_using [hT]) (by omega_using [ho]) (by omega_using [sA])
          (by omega_using [sT])) fun t' ⟨h', e8, esi, ebx, e14⟩ =>
      ⟨h', e8.trans g8, esi.trans gsi, ebx.trans gbx, e14.trans g14⟩

structure Sel8Inv (s₀ : State) (B : Addr) (Z eA eT eo : Nat) (lt : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eo (8 * j) s₀.mem t.mem
  val : wv t.mem B eo j = if lt then wv s₀.mem B eA j else wv s₀.mem B eT j

/-- `select8`: `selectAcc`'s result, for `w` a multiple of 8. -/
theorem select8_ok {s : State} {B : Addr} {Z w n eA eT eo : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (hsi : s.gpr .rsi = off B eT) (hbx : s.gpr .rbx = off B eo)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) {lt : Bool} (hbp : s.gpr .rbp = mask lt)
    (hwN : w = 8 * n) (hn : 0 < n) (hw' : w < 2 ^ 31) (hA : eA + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z)
    (ho : eo + 8 * w ≤ Z) (sA : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo) (sT : eo + 8 * w ≤ eT ∨ eT + 8 * w ≤ eo) :
    WP isa select8 s fun t =>
      wv t.mem B eo w = (if lt then wv s.mem B eA w else wv s.mem B eT w) ∧
      Outside B eo (8 * w) s.mem t.mem ∧ Keep [.rax, .r14] s t := by
  have hnw := hs.nowrap
  subst hwN
  unfold select8
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = BitVec.ofNat 64 (8 * 0) ∧ t.mem = s.mem)
    (by xrun) rfl) fun s₁ ⟨⟨h14, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_upto (a := 0) (N := n) hn (fun i t => Sel8Inv s B Z eA eT eo lt (8 * i) t) ?_ (fun _ h => h)
    ⟨hs.congr k₁.2.2, k₁.mono (by decide), h14, by rw [hm₁]; exact Outside.refl _ _ _ _, by cases lt <;> rfl⟩)
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩
  intro i _ hi t hI
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have tsi : t.gpr .rsi = off B eT := (hI.keep.gpr (by decide)).trans hsi
  have tbx : t.gpr .rbx = off B eo := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 (8 * n) := (hI.keep.gpr (by decide)).trans h12
  have tbp : t.gpr .rbp = mask lt := (hI.keep.gpr (by decide)).trans hbp
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rbp] (Q := fun t₁ => t₁.cf = some lt ∧ t₁.mem = t.mem) (by
    unfold cfFromRbp; xrun [tbp, cf_mask]) rfl) fun t₁ ⟨⟨c₁, m₁⟩, k₁'⟩ => ?_
  have hS : Sl s B Z eA eT eo lt (8 * i) t₁ :=
    ⟨hI.scr.congr k₁'.2.2, ((hI.keep.trans k₁').mono (by decide)), c₁, m₁ ▸ hI.out, m₁ ▸ hI.val⟩
  refine WP.mono (csts_ok (i := i) 8 (Nat.le_refl _) ((k₁'.gpr (by decide)).trans t8)
    ((k₁'.gpr (by decide)).trans tsi) ((k₁'.gpr (by decide)).trans tbx)
    ((k₁'.gpr (by decide)).trans hI.r14) hS (by omega_using [hA, hi]) (by omega_using [hT, hi])
        (by omega_using [ho, hi]) (by omega_using [sA, hi]) (by omega_using [sT, hi]))
    fun t₂ ⟨h₂, e8, esi, ebx, e14⟩ => ?_
  rw [show ([cfToRbp, .alu .add .r14 (.imm 8), .alu .cmp .r14 (.reg .r12)] : List Instr) =
    [cfToRbp] ++ [.alu .add .r14 (.imm 8), .alu .cmp .r14 (.reg .r12)] from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rbp] (Q := fun t₃ => t₃.gpr .rbp = mask lt ∧ t₃.mem = t₂.mem) (by
    unfold cfToRbp; xrun [h₂.cf]; rfl) rfl) fun t₃ ⟨⟨b₃, m₃⟩, k₃⟩ => ?_
  have t₃14 : t₃.gpr .r14 = BitVec.ofNat 64 (8 * i) :=
    (k₃.gpr (by decide)).trans (e14.trans ((k₁'.gpr (by decide)).trans hI.r14))
  have t₃12 : t₃.gpr .r12 = BitVec.ofNat 64 (8 * n) :=
    (k₃.gpr (by decide)).trans ((h₂.keep.gpr (by decide)).trans h12)
  refine WP.mono (count8_ok t₃ (r := .r12) (by decide) t₃14 t₃12 (by omega_using [hw', hi]) (by omega_using [hw']))
    fun t' ⟨hz, h14', hm', k'⟩ => ⟨hz, ?_⟩
  have kk : Keep [.rax, .rbp, .r14] s t' := (h₂.keep.trans k₃).trans k' |>.mono (by decide)
  refine ⟨h₂.scr.congr (k'.2.2.trans k₃.2.2), ⟨fun r hr => ?_, kk.2⟩, h14', ?_, ?_⟩
  · by_cases hrb : r = .rbp
    · subst hrb; rw [k'.gpr (by decide), b₃, hbp]
    · exact kk.gpr (by simp_all)
  · rw [hm', m₃, show 8 * (i + 1) = 8 * i + 8 by omega_using []]; exact h₂.out
  · rw [hm', m₃, show 8 * (i + 1) = 8 * i + 8 by omega_using []]; exact h₂.val

/-! ## The final subtraction -/

/-- `finish8 co`: `AdxSquare.finishV_ok`'s result, for `w` a multiple of 8. -/
theorem finish8V_ok {s : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z)
    (hwN : w = 8 * n) (hn : 0 < n) (hw : w < 2 ^ 31) (h10 : s.gpr .r10 = off B (slot w aN))
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {co o : Nat} (po : (co, o) ∈ ps)
    (ho : o < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (hTlt : wv s.mem B (slot w aTmp) (w + 2) < 2 * wv s.mem B (slot w aN) w) :
    WP isa (Adx.finish8 co) s fun t =>
      wv t.mem B (slot w o) w = wv s.mem B (slot w aTmp) (w + 2) % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega_using []
  have hTs := sl aTmp (by decide)
  have sNX : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega_using []
  have soX : slot w o + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w o := by
    have := slot_sep (w := w) ho1; have := slot_sep (w := w) ho2; unfold slot aAcc aTmp at *; omega_arith
  unfold Adx.finish8
  refine WP.seq (WP.mono (finishBasesV_ok hs hdi hH hZ (hv.at po) (hv.lt po)) fun s₁ ⟨h12, h8, hsi, hbx, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (subMod8_ok (hs.congr k₁.2.2) h8 ((k₁.gpr (by decide)).trans h10) hsi h12 hwN hn hw
    (by omega_using [hTs]) (by have := sl aN (by decide); omega_using [this]) (by omega_using [hAT, hTs])
        (by omega_using [hAT]) (by omega_using [sNX]))
    fun s₂ ⟨c, lt, hbp, hlt, hD, ho₂, k₂⟩ => ?_)
  rw [hm₁] at hlt hD ho₂
  have k12 := k₁.trans k₂
  refine WP.mono (select8_ok (hs.congr k12.2.2) ((k₂.gpr (by decide)).trans h8) ((k₂.gpr (by decide)).trans hsi)
    ((k₂.gpr (by decide)).trans hbx) ((k₂.gpr (by decide)).trans h12) hbp hwN hn hw (by omega_using [hTs]) (by omega_using [hAT, hTs])
    (by have := sl o ho; omega_using [this]) (by omega_using [hAT, soX]) (by omega_using [hAT, soX])) fun t ⟨hv, hot, kt⟩ => ?_
  have hT₂ : wv s₂.mem B (slot w aTmp) w = wv s.mem B (slot w aTmp) w := ho₂.wv (by omega_using [hAT]) (by omega_using [hnw, hTs])
  refine ⟨?_, ?_, (k12.trans (kt.mono (rs' := [.rax, .rdx, .r14]) (by decide))).mono (by decide)⟩
  · rw [hv, hT₂, hlt, wv_top2]
    have h := VG.Proof.Bignum.csub_result (Tl := wv s.mem B (slot w aTmp) w)
      (Tw := (word s.mem B (slot w aTmp + 8 * w)).toNat)
      (Tw1 := (word s.mem B (slot w aTmp + 8 * w + 8)).toNat) (D := wv s₂.mem B (slot w aAcc) w)
      (m := wv s.mem B (slot w aN) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      (by have := wv_lt s.mem B (slot w aN) w; omega_using [this]) (wv_lt _ _ _ _) (Bool.toNat_le c) (wv_lt _ _ _ _)
      (by rw [← wv_top2]; exact hTlt) hD
    rw [← h]
    by_cases h : (word s.mem B (slot w aTmp + 8 * w)).toNat < c.toNat <;> simp [h]
  · intro x hx
    have h1 := hx aAcc (by simp)
    have h2 := hx o (by simp)
    exact (hot x (by omega_using [h2])).trans (ho₂ x (by omega_using [h1]))

end VG.Proof.Bignum.X86_64
