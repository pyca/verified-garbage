import VerifiedGarbage.Proof.Rc4.Arm.Lookup

/-! # RC4 on ARMv7: replacing a secret-indexed byte of the table -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Proof.Rc4

/-! ## Moving the difference to the byte's lane -/

theorem spread_step (s : State) (idx c : Byte) {j : Nat} (hj : j < 4)
    (h6 : s.gpr .r6 = idx.setWidth 32) (h10 : s.gpr .r10 = BitVec.allOnes 32)
    (h7 : s.gpr .r7 = c.setWidth 32) (h8 : s.gpr .r8 = spread c (idx.toNat % 4) (j + 1)) :
    WP isa (.block (spreadStep j)) s fun t =>
      t.gpr .r8 = spread c (idx.toNat % 4) j ∧ t.mem = s.mem := by
  have he : encodable (BitVec.ofNat 32 j) = true := encodable_lt (by omega)
  unfold spreadStep laneMask
  arun [h6, h10, h7, h8, he]
  rw [lane_mask idx hj, spread_succ c (Nat.mod_lt _ (by decide))]

theorem spread_steps (s₀ : State) (idx c : Byte) (h6 : s₀.gpr .r6 = idx.setWidth 32)
    (h10 : s₀.gpr .r10 = BitVec.allOnes 32) (h7 : s₀.gpr .r7 = c.setWidth 32) :
    ∀ n ≤ 4, ∀ s, s.gpr .r8 = spread c (idx.toNat % 4) n → Keep [.r8, .r9] s₀ s →
      s.mem = s₀.mem →
      WP isa (.block ((List.range n).reverse.flatMap spreadStep)) s fun t =>
        t.gpr .r8 = spread c (idx.toNat % 4) 0 ∧ Keep [.r8, .r9] s₀ t ∧ t.mem = s₀.mem := by
  intro n hn
  induction n with
  | zero => intro s h8 hk hm; exact WP.block_nil ⟨h8, hk, hm⟩
  | succ n ih =>
    intro s h8 hk hm
    rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (WP.keep [.r8, .r9] (spread_step s idx c (by omega)
      ((hk.gpr (by decide)).trans h6) ((hk.gpr (by decide)).trans h10)
      ((hk.gpr (by decide)).trans h7) h8) rfl) fun t ⟨⟨t8, tm⟩, tk⟩ => ?_
    exact ih (by omega) t t8 ((hk.trans tk).mono (by decide)) (tm.trans hm)

theorem lanesDown_eq : lanesDown = (List.range 4).reverse := rfl

/-! ## Storing back every word -/

theorem scatter_step (s : State) (idx : Byte) {k : Nat} (hk : k < 64)
    (h6 : s.gpr .r6 = idx.setWidth 32) (h10 : s.gpr .r10 = BitVec.allOnes 32)
    (hfit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (scatterStep k)) s fun t =>
      t.mem = s.mem.writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * k))
        ((if idx.toNat / 4 = k then s.gpr .r8 else 0) ^^^
          s.mem.readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * k)) 32) := by
  have he : encodable (BitVec.ofNat 32 (4 * k)) = true := encodable_lt (by omega)
  have ho : 4 * k < 4096 := by omega
  have hr := region_in (rs := s.rd) hw
  rw [← row_addr hfit hk] at hw hr
  unfold scatterStep rowMask
  arun [h6, h10, he, ho, hr, hw]
  rw [row_addr hfit hk, row_mask idx hk]

theorem scatter_steps (s₀ : State) (idx : Byte) (d : BitVec 32) (h : TableEnv s₀ idx) :
    ∀ n ≤ 64, ∀ s, s.gpr .r8 = d → Keep [.r9, .r11] s₀ s → s.mem = s₀.mem →
      WP isa (.block ((List.range n).flatMap scatterStep)) s fun t =>
        t.mem = scatter s₀.mem (State.addr (s₀.gpr .r12)) idx.toNat d n ∧ t.gpr .r8 = d ∧
        Keep [.r9, .r11] s₀ t := by
  intro n hn
  induction n with
  | zero =>
    intro s h8 hk hm
    refine WP.block_nil ⟨?_, h8, hk⟩
    rw [hm]; unfold scatter; rw [ite_eq_right (Nat.not_lt_zero _)]
  | succ n ih =>
    intro s h8 hk hm
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h8 hk hm) fun t ⟨tm, t8, tk⟩ => ?_
    have t12 : t.gpr .r12 = s₀.gpr .r12 := tk.gpr (by decide)
    have hq : InRegions t.wr (State.addr (t.gpr .r12) + BitVec.ofNat 64 (4 * n)) 4 := by
      rw [tk.2.2.1, t12]
      exact region_offset _ _ _ _ _ (by omega) (by omega) h.table
    refine WP.mono (WP.keep [.r9, .r11] (scatter_step t idx (by omega)
      ((tk.gpr (by decide)).trans h.idx) ((tk.gpr (by decide)).trans h.ones)
      (by rw [t12]; exact h.fit) hq) rfl) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, (uk.gpr (by decide)).trans t8, (tk.trans uk).mono (by decide)⟩
    rw [um, tm, t8, t12, scatter_succ]

/-! ## The replacement -/

theorem loadI_ok (s : State) (ii : Byte) (h4 : s.gpr .r4 = ii.setWidth 32)
    (hfit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12)) 256) :
    WP isa (.block loadI) s fun t =>
      t.gpr .r11 = (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 ii.toNat)).setWidth 32 ∧
      Keep [.r9, .r11] s t ∧ t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + ii.setWidth 32 + BitVec.ofNat 32 0)) 1 := by
    rw [idx_addr hfit ii]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) hr
  refine WP.mono (WP.keep (Q := fun t =>
      t.gpr .r11 = (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 ii.toNat)).setWidth 32 ∧
      t.mem = s.mem) [.r9, .r11] ?_ (by decide)) fun t ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold loadI
  arun [h4, hi]
  rw [idx_addr hfit ii]

theorem replace_core (s : State) (idx ii : Byte) (h : TableEnv s idx)
    (h4 : s.gpr .r4 = ii.setWidth 32) :
    WP isa (.block replace) s fun t =>
      t.gpr .r7 = (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 idx.toNat)).setWidth 32 ∧
      t.mem = s.mem.write (State.addr (s.gpr .r12) + BitVec.ofNat 64 idx.toNat) 1
        (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 ii.toNat)) ∧
      Keep [.r7, .r8, .r9, .r11] s t := by
  have hn := idx.isLt
  let p := State.addr (s.gpr .r12)
  let b := s.mem (p + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (p + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r7, .r8, .r9, .r11] (lookup_core s idx h) (by decide +kernel))
    fun t ⟨⟨t7, tm⟩, tk⟩ => ?_
  have t12 : t.gpr .r12 = s.gpr .r12 := tk.gpr (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok t ii ((tk.gpr (by decide)).trans h4) (by rw [t12]; exact h.fit)
    (by rw [tk.2.1, tk.2.2.1, t12]; exact h.read)) fun t' ⟨t'11, t'k, t'm⟩ => ?_
  rw [t12, tm] at t'11
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.dp .eor .r7 .r7 (.reg .r11), .mov .r8 (imm 0)]) t' fun u =>
      u.gpr .r7 = (b ^^^ v).setWidth 32 ∧ u.gpr .r8 = 0 ∧ u.mem = s.mem := by
    have t'7 : t'.gpr .r7 = b.setWidth 32 := (t'k.gpr (by decide)).trans t7
    arun [t'7, t'11, t'm, tm, BitVec.ofNat_eq_ofNat]
    rw [xor_byte32]
  refine WP.mono (WP.keep [.r7, .r8] h1 (by decide)) fun u ⟨⟨u7, u8, um⟩, uk⟩ => ?_
  have k₁ : Keep [.r7, .r8, .r9, .r11] s u := ((tk.trans t'k).trans uk).mono (by decide)
  rw [WP.block_append_iff]
  have hsp := spread_steps u idx (b ^^^ v) ((k₁.gpr (by decide)).trans h.idx)
    ((k₁.gpr (by decide)).trans h.ones) u7 4 (by decide) u
    (by rw [u8]; unfold spread; rw [ite_eq_right (by omega)]) (Keep.refl _ _) rfl
  rw [← lanesDown_eq] at hsp
  refine WP.mono hsp fun w ⟨w8, wk, wm⟩ => ?_
  have w11 : w.gpr .r11 = v.setWidth 32 :=
    (wk.gpr (by decide)).trans ((uk.gpr (by decide)).trans t'11)
  have w7 : w.gpr .r7 = (b ^^^ v).setWidth 32 := (wk.gpr (by decide)).trans u7
  rw [WP.block_append_iff]
  have h2 : WP isa (.block [.dp .eor .r7 .r7 (.reg .r11)]) w fun x =>
      x.gpr .r7 = b.setWidth 32 ∧ x.mem = s.mem := by
    arun [w7, w11, wm, um]
    rw [xor_byte32, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine WP.mono (WP.keep [.r7] h2 (by decide)) fun x ⟨⟨x7, xm⟩, xk⟩ => ?_
  have k₂ : Keep [.r7, .r8, .r9, .r11] s x := ((k₁.trans wk).trans xk).mono (by decide)
  have x12 : x.gpr .r12 = s.gpr .r12 := k₂.gpr (by decide)
  have hx : TableEnv x idx := ⟨(k₂.gpr (by decide)).trans h.idx, (k₂.gpr (by decide)).trans h.ones,
    by rw [x12]; exact h.fit, by rw [k₂.2.2.1, x12]; exact h.table⟩
  have x8 : x.gpr .r8 = spread (b ^^^ v) (idx.toNat % 4) 0 := (xk.gpr (by decide)).trans w8
  refine WP.mono (scatter_steps x idx _ hx 64 (by decide) x x8 (Keep.refl _ _) rfl)
    fun y ⟨ym, _, yk⟩ => ?_
  refine ⟨(yk.gpr (by decide)).trans x7, ?_, (k₂.trans yk).mono (by decide)⟩
  rw [ym, xm, x12]
  unfold scatter spread
  rw [ite_eq_left (by omega), ite_eq_left (Nat.zero_le _), Nat.sub_zero, writeW_byte32,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Rc4.Arm
