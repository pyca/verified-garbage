import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pair

/-!
# Interleaved counter mode and GHASH with AVX-512: the powers of 48 blocks

`pow48_ok`: `StitchZ.pow48` multiplies, lane by lane, the sixteen powers at
`scratch` by the first (`H'¹⁶`) into `scratch + 256`, and those by the first
of them (`H'³²`) into `scratch + 512` (each product reduced, `Pclmul.reduceB`
of `Prod.zero.acc`, `powLoad_ok`), and saves the reduction constant at
`scratch + 832`; what the products are in the field is in `StitchZ/Ok.lean`.
-/

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only ea_at reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchZ (accInit reduceZ powLoad pow48)
open VG.Proof.Aes.X86_64.VaesZ (zmm_lane)

/-- The SSE block of `accInit zmm7 zmm12` in each lane. -/
def mulSse : List Instr :=
  [.xop (.bin .movdqa .xmm8 .xmm7), .xop (.pclmulqdq .xmm8 .xmm12 0x00),
   .xop (.bin .movdqa .xmm10 .xmm7), .xop (.pclmulqdq .xmm10 .xmm12 0x11),
   .xop (.bin .movdqa .xmm9 .xmm7), .xop (.pclmulqdq .xmm9 .xmm12 0x01),
   .xop (.bin .movdqa .xmm11 .xmm7), .xop (.pclmulqdq .xmm11 .xmm12 0x10), .xop (.bin .pxor .xmm9 .xmm11)]

theorem lane_mul : zlaneSseBlock (accInit .xmm7 .xmm12 ++ reduceZ) = some (mulSse ++ redSse) := rfl

theorem mulSse_ok (t : State) :
    WP isa (.block mulSse) t fun t' =>
      prod t' = Prod.zero.acc (t.xmm .xmm7) (t.xmm .xmm12) ∧ Only [.xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  apply WP.of_runBlock
  simp only [mulSse, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, Pclmul.eval_pxor, eval_movdqa, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · simp only [prod, Prod.acc, Prod.zero, reduceCtorEq, ↓reduceIte, Stitch.zero_xor_b]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem mulRed_ok (t : State) (h1 : t.xmm .xmm1 = poly) :
    WP isa (.block (mulSse ++ redSse)) t fun t' =>
      t'.xmm .xmm10 = reduceB (Prod.zero.acc (t.xmm .xmm7) (t.xmm .xmm12)) ∧
      Only [.xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  rw [WP.block_append_iff]
  refine WP.mono (mulSse_ok t) fun t₁ ⟨p₁, o₁⟩ => ?_
  refine WP.mono (redSse_ok t₁ (by rw [o₁.xmm _ (by decide)]; exact h1)) fun t' ⟨e', o'⟩ =>
    ⟨by rw [e', p₁], (o₁.trans o').weaken fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h | h) | (h | h | h | h) <;> simp [h]⟩

/-- One load of powers, times `zmm12` in each lane, reduced, and stored
(`zmm7`–`zmm11` are written). -/
theorem powLoad_ok (d k : Nat) (s : State) (h1 : ∀ l < 4, s.zlane .xmm1 l = poly)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((64 * k : Nat) : Int)) 64)
    (hout : InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((d + 64 * k : Nat) : Int)) 64) :
    WP isa (.block (powLoad d k)) s fun s' =>
      (∃ v : BitVec 512, s'.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofInt 64 ((d + 64 * k : Nat) : Int)) v ∧
        ∀ l < 4, v.extractLsb' (128 * l) 128 = reduceB (Prod.zero.acc
          (s.mem.readW (s.gpr .r11 + BitVec.ofInt 64 ((64 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)
          (s.zlane .xmm12 l))) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → ∀ l < 4,
        s'.zlane r l = s.zlane r l) := by
  let a := s.gpr .r11 + BitVec.ofInt 64 ((64 * k : Nat) : Int)
  let t₁ := ldZ s .xmm7 a
  rw [powLoad, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load512, ea_at, hin, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.zlanes lane_mul fun l hl => mulRed_ok (t₁.zproj l) (by
      simp only [State.zproj_xmm, t₁]; rw [ldZ_zlane_ne _ _ (by decide) hl]; exact h1 l hl))
    fun t₂ ⟨hk₂, hq₂⟩ => ?_
  have g₂ : t₂.gpr = s.gpr := by rw [hk₂.gpr]; rfl
  have m₂ : t₂.mem = s.mem := by rw [hk₂.mem]; rfl
  have rd₂ : t₂.rd = s.rd := by rw [hk₂.rd]; rfl
  have wr₂ : t₂.wr = s.wr := by rw [hk₂.wr]; rfl
  have hst : isa.exec (.vmovdqu32Store (at_ .r11 (d + 64 * k)) .xmm10) t₂ =
      some (t₂.setMem (s.mem.writeW (s.gpr .r11 + BitVec.ofInt 64 ((d + 64 * k : Nat) : Int)) (t₂.zmm .xmm10))) := by
    simp only [isa, exec, State.store512_eq, ea_at, g₂, wr₂, m₂, hout, ite_true]
  rw [WP.block_cons_iff]
  refine ⟨_, hst, WP.block_nil ⟨⟨t₂.zmm .xmm10, by rw [State.setMem_mem], fun l hl => ?_⟩,
    by rw [State.setMem_gpr, g₂], by rw [State.setMem_rd, rd₂], by rw [State.setMem_wr, wr₂],
    fun r h7 h8 h9 h10 h11 l hl => ?_⟩⟩
  · rw [zmm_lane _ _ hl]
    have := (hq₂ l hl).1
    simp only [State.zproj_xmm] at this
    rw [this]
    simp only [t₁]
    rw [ldZ_zlane _ _ _ hl, ldZ_zlane_ne _ _ (by decide) hl]
  · have := (hq₂ l hl).2.xmm r (by simp [h8, h9, h10, h11])
    simp only [State.zproj_xmm] at this
    rw [State.setMem_zlane, this]
    simp only [t₁]; rw [ldZ_zlane_ne _ _ h7 hl]

theorem ofInt_add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofInt 64 ((a : Nat) : Int) + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- A lane of a 64-byte write. -/
theorem readW_lane (m : Mem) (q : Addr) (v : BitVec 512) {l : Nat} (hl : l < 4) :
    (m.writeW q v).readW (q + BitVec.ofNat 64 (16 * l)) 128 = v.extractLsb' (128 * l) 128 := by
  have e := readW_writeW_inside m q v (k := 16 * l) (n := 16) (by omega) (by decide)
  rwa [show 8 * (16 * l) = 128 * l by omega] at e

/-- The first `n` loads of powers, times `zmm12`, stored at `scratch + d`. -/
theorem powRun_ok (d : Nat) (hd : 256 ≤ d) (hdl : d + 256 ≤ 1024) :
    ∀ n, n ≤ 4 → ∀ s, InRegions s.wr (s.gpr .r11) 1024 → (∀ l < 4, s.zlane .xmm1 l = poly) →
      WP isa (.block ((List.range n).flatMap (powLoad d))) s fun s' =>
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        Frame [⟨s.gpr .r11 + BitVec.ofNat 64 d, 256⟩] s.mem s'.mem ∧
        (∀ k < n, ∀ l < 4, s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (d + 64 * k + 16 * l)) 128 =
          reduceB (Prod.zero.acc (s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (64 * k + 16 * l)) 128)
            (s.zlane .xmm12 l))) ∧
        (∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → ∀ l < 4,
          s'.zlane r l = s.zlane r l)
  | 0, _, s, _, _ => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega), fun _ _ _ _ _ _ _ _ => rfl⟩
  | n + 1, hn, s, hin, h1 => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (powRun_ok d hd hdl n (by omega) s hin h1) fun s₁ ⟨g₁, rd₁, wr₁, f₁, e₁, x₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have p₁ : s₁.gpr .r11 = s.gpr .r11 := by rw [g₁]
    have h1₁ : ∀ l < 4, s₁.zlane .xmm1 l = poly := fun l hl => by
      rw [x₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl]; exact h1 l hl
    refine WP.mono (powLoad_ok d n s₁ h1₁
      (by rw [rd₁, wr₁, p₁]; exact Stitch.in_rdwr (Stitch.in_sub_int hin (by omega)))
      (by rw [wr₁, p₁]; exact Stitch.in_sub_int hin (by omega)))
      fun s' ⟨⟨v, m', ev⟩, g', rd', wr', x'⟩ => ?_
    rw [p₁, BitVec.ofInt_natCast] at m'
    simp only [p₁, ofInt_add_ofNat] at ev
    -- The source powers are outside the region written.
    have src : ∀ k < 4, ∀ l < 4, s₁.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (64 * k + 16 * l)) 128 =
        s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (64 * k + 16 * l)) 128 := fun k hk l hl =>
      f₁.readW (r := ⟨s.gpr .r11, 256⟩) (Offset.contains_base _ (by omega) (by omega))
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)) (by decide)
    refine ⟨by rw [g', g₁], by rw [rd', rd₁], by rw [wr', wr₁], ?_, fun k hk l hl => ?_,
      fun r h7 h8 h9 h10 h11 l hl => by rw [x' r h7 h8 h9 h10 h11 l hl, x₁ r h7 h8 h9 h10 h11 l hl]⟩
    · rw [m']
      exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
    · rw [m']
      by_cases hkn : k = n
      · subst hkn
        rw [show s.gpr .r11 + BitVec.ofNat 64 (d + 64 * k + 16 * l) =
            s.gpr .r11 + BitVec.ofNat 64 (d + 64 * k) + BitVec.ofNat 64 (16 * l) by
            rw [BitVec.add_assoc, ← BitVec.ofNat_add],
          readW_lane _ _ _ hl, ev l hl, src k (by omega) l hl,
          x₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl]
      · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := d + 64 * k + 16 * l) (n := 128 / 8)
          (e := d + 64 * n) (k := 512 / 8) (by omega) (by omega) (by omega)) (by decide)]
        exact e₁ k (by omega) l hl

/-- `vbroadcasti32x4 d, [b + o]`. -/
theorem bcast_exec (d : XReg) (b : Reg) (o : Nat) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 o) 16) :
    isa.exec (.vbroadcasti32x4 d (at_ b o)) s =
      some (s.setZ d (s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 128) (s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 128)
        (s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 128) (s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 128)) := by
  have e : s.gpr b + BitVec.ofInt 64 (o : Int) = s.gpr b + BitVec.ofNat 64 o := by rw [BitVec.ofInt_natCast]
  simp only [isa, exec, State.load128, ea_at, e, hin, ite_true, Option.map_some]

/-- A broadcast leaves the lanes it reads in all four. -/
theorem zlane_bcast (s : State) (d : XReg) (v : BitVec 128) {l : Nat} (hl : l < 4) : (s.setZ d v v v v).zlane d l = v := by
  rw [State.zlane_setZ _ _ _ _ _ _ _ hl]; simp only [ite_true]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The sixteen powers at `scratch`, as `pow48` reads them. -/
abbrev pw16 (s : State) (k l : Nat) : BitVec 128 := s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (64 * k + 16 * l)) 128

/-- A broadcast from `scratch + h` and a table of products at `scratch + d`. -/
theorem table_ok (d h : Nat) (hd : 256 ≤ d) (hdl : d + 256 ≤ 1024) (hh : h + 16 ≤ 1024) (s : State)
    (hin : InRegions s.wr (s.gpr .r11) 1024) (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) :
    WP isa (.block (.vbroadcasti32x4 .xmm12 (at_ .r11 h) :: (List.range 4).flatMap (powLoad d))) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨s.gpr .r11 + BitVec.ofNat 64 d, 256⟩] s.mem s'.mem ∧
      (∀ k < 4, ∀ l < 4, s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (d + 64 * k + 16 * l)) 128 =
        reduceB (Prod.zero.acc (pw16 s k l) (s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 h) 128))) ∧
      (∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → r ≠ .xmm12 → ∀ l < 4,
        s'.zlane r l = s.zlane r l) := by
  let v := s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 h) 128
  rw [WP.block_cons_iff]
  refine ⟨s.setZ .xmm12 v v v v, bcast_exec .xmm12 .r11 h s (Stitch.in_rdwr (Stitch.in_sub hin hh)), ?_⟩
  refine WP.mono (powRun_ok d hd hdl 4 (Nat.le_refl _) (s.setZ .xmm12 v v v v)
      (by simp only [State.setZ_gpr, State.setZ_wr]; exact hin)
      (fun l hl => by rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl]; exact h1 l hl))
    fun s' ⟨g', rd', wr', f', e', x'⟩ => ?_
  simp only [State.setZ_gpr, State.setZ_rd, State.setZ_wr, State.setZ_mem] at g' rd' wr' f' e'
  exact ⟨g', rd', wr', f', fun k hk l hl => by rw [e' k hk l hl, zlane_bcast _ _ _ hl],
    fun r h7 h8 h9 h10 h11 h12 l hl => by rw [x' r h7 h8 h9 h10 h11 l hl, State.zlane_setZ_ne _ h12 _ _ _ _ hl]⟩

/-- Reads below `scratch + o` are kept by a frame of 256 bytes at
`scratch + o`, and those above. -/
theorem keep256 {p : Addr} {m m' : Mem} {o : Nat} (f : Frame [⟨p + BitVec.ofNat 64 o, 256⟩] m m') {a : Nat}
    (ha : a + 16 ≤ o ∨ o + 256 ≤ a) (hl : o + 256 ≤ 2 ^ 64) (hal : a + 16 ≤ 2 ^ 64) :
    m'.readW (p + BitVec.ofNat 64 a) 128 = m.readW (p + BitVec.ofNat 64 a) 128 :=
  f.readW (r := ⟨p + BitVec.ofNat 64 a, 16⟩) (Region.contains_self _ _)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ ha hal hl) (by decide)

/-- `pow48`: the powers at `scratch` times `H'¹⁶` (their first) at
`scratch + 256`, times `H'³²` (the first of those) at `scratch + 512`, and
the reduction constant at `scratch + 832`. -/
theorem pow48_ok (s : State) (hin : InRegions s.wr (s.gpr .r11) 1024) (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) :
    WP isa (.block pow48) s fun s' =>
      (∀ k < 4, ∀ l < 4, s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = pw16 s k l) ∧
      (∀ k < 4, ∀ l < 4, s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (256 + 64 * k + 16 * l)) 128 =
        reduceB (Prod.zero.acc (pw16 s k l) (pw16 s 0 0))) ∧
      (∀ k < 4, ∀ l < 4, s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (512 + 64 * k + 16 * l)) 128 =
        reduceB (Prod.zero.acc (pw16 s k l) (reduceB (Prod.zero.acc (pw16 s 0 0) (pw16 s 0 0))))) ∧
      (∀ l < 4, s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) ∧
      Frame [⟨s.gpr .r11, 1024⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → r ≠ .xmm12 → ∀ l < 4,
        s'.zlane r l = s.zlane r l) := by
  rw [pow48, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (table_ok 256 0 (by decide) (by decide) (by decide) s hin h1) fun s₂ ⟨g₂, rd₂, wr₂, f₂, e₂, x₂⟩ => ?_
  rw [show s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 0) 128 = pw16 s 0 0 from rfl] at e₂
  rw [← List.append_assoc, WP.block_append_iff]
  have x₂1 : ∀ l < 4, s₂.zlane .xmm1 l = poly := fun l hl => by
    rw [x₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl]; exact h1 l hl
  refine WP.mono (table_ok 512 256 (by decide) (by decide) (by decide) s₂ (by rw [g₂, wr₂]; exact hin) x₂1)
    fun s₄ ⟨g₄, rd₄, wr₄, f₄, e₄, x₄⟩ => ?_
  rw [g₂] at f₄ e₄
  have h16 : ∀ k < 4, ∀ l < 4, s₂.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = pw16 s k l :=
    fun k hk l hl => keep256 f₂ (by omega) (by decide) (by omega)
  have hv : s₂.mem.readW (s.gpr .r11 + BitVec.ofNat 64 256) 128 = reduceB (Prod.zero.acc (pw16 s 0 0) (pw16 s 0 0)) :=
    e₂ 0 (by decide) 0 (by decide)
  -- The reduction constant, stored.
  have g₄' : s₄.gpr = s.gpr := by rw [g₄, g₂]
  have hst : isa.exec (.vmovdqu32Store (at_ .r11 832) .xmm1) s₄ =
      some (s₄.setMem (s₄.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 832) (s₄.zmm .xmm1))) := by
    have e : s₄.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int) = s.gpr .r11 + BitVec.ofNat 64 832 := by
      rw [g₄', BitVec.ofInt_natCast]
    have hin832 : InRegions s₄.wr (s₄.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int)) 64 := by
      rw [wr₄, wr₂, e]; exact Stitch.in_sub hin (by decide)
    simp only [isa, exec, State.store512_eq, ea_at, hin832, ite_true]
    rw [e]
  rw [WP.block_cons_iff]
  have k₅ : ∀ o, o + 16 ≤ 832 → (s₄.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 832) (s₄.zmm .xmm1)).readW (s.gpr .r11 + BitVec.ofNat 64 o) 128 =
      s₄.mem.readW (s.gpr .r11 + BitVec.ofNat 64 o) 128 := fun o ho =>
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := o) (n := 128 / 8) (e := 832) (k := 512 / 8) (by omega) (by omega)
      (by omega)) (by decide)
  refine ⟨_, hst, WP.block_nil ⟨fun k hk l hl => ?_, fun k hk l hl => ?_, fun k hk l hl => ?_, fun l hl => ?_, ?_,
    by rw [State.setMem_gpr, g₄'], by rw [State.setMem_rd, rd₄, rd₂], by rw [State.setMem_wr, wr₄, wr₂],
    fun r h7 h8 h9 h10 h11 h12 l hl => ?_⟩⟩
  · rw [State.setMem_mem, k₅ (64 * k + 16 * l) (by omega), keep256 f₄ (by omega) (by decide) (by omega)]
    exact h16 k hk l hl
  · rw [State.setMem_mem, k₅ (256 + 64 * k + 16 * l) (by omega), keep256 f₄ (by omega) (by decide) (by omega)]
    exact e₂ k hk l hl
  · rw [State.setMem_mem, k₅ (512 + 64 * k + 16 * l) (by omega), e₄ k hk l hl, hv,
      show pw16 s₂ k l = pw16 s k l by simp only [pw16, g₂]; exact h16 k hk l hl]
  · rw [State.setMem_mem, show s.gpr .r11 + BitVec.ofNat 64 (832 + 16 * l) = s.gpr .r11 + BitVec.ofNat 64 832 + BitVec.ofNat 64 (16 * l) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add], readW_lane _ _ _ hl, zmm_lane _ _ hl,
      x₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl]
    exact x₂1 l hl
  · rw [State.setMem_mem]
    have fs : ∀ o, o + 256 ≤ 1024 → ∀ {m m'}, Frame [⟨s.gpr .r11 + BitVec.ofNat 64 o, 256⟩] m m' → Frame [⟨s.gpr .r11, 1024⟩] m m' :=
      fun o ho m m' f => f.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ ho⟩
    exact ((fs 256 (by decide) f₂).trans (fs 512 (by decide) f₄)).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))
  · rw [State.setMem_zlane, x₄ r h7 h8 h9 h10 h11 h12 l hl, x₂ r h7 h8 h9 h10 h11 h12 l hl]

end VG.Proof.Gcm.X86_64.StitchZ
