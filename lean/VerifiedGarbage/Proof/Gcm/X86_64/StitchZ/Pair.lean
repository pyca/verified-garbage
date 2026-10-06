import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh

/-!
# Interleaved counter mode and GHASH with AVX-512: a pair of loads

`pair_ok`: `StitchZ.pair ka kb g first` loads blocks `4 ka`–`4 ka + 3` and
`4 kb`–`4 kb + 3` of group `g` (at `rdx + 256 g`) into the lanes of `zmm7`
and `zmm1`, their powers into `zmm12` and `zmm13`, and adds the products of
both to each lane's (`WP.zlanes` of `pairSse_ok`, the SSE code of each
lane); the first pair adds `Y` (`zmm2`) to the first load and writes the
products instead.
-/

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (zero_xor_b)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only ea_at)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZ (prodPair pairZ pair tab)
open VG.Spec.Gcm (Block blockAt)

/-- The SSE block of a pair's lane-wise instructions. -/
def pairSse (first : Bool) : List Instr :=
  [.xop (.bin .pshufb .xmm7 .xmm0)] ++ (if first then [.xop (.bin .pxor .xmm7 .xmm2)] else []) ++
  [.xop (.bin .pshufb .xmm1 .xmm0)] ++
  [.xop (.bin .movdqa .xmm11 .xmm7), .xop (.pclmulqdq .xmm11 .xmm12 0x00),
   .xop (.bin .movdqa .xmm2 .xmm1), .xop (.pclmulqdq .xmm2 .xmm13 0x00)] ++
  (if first then [.xop (.bin .movdqa .xmm8 .xmm11)] else [.xop (.bin .pxor .xmm8 .xmm11)]) ++
  [.xop (.bin .pxor .xmm8 .xmm2),
   .xop (.bin .movdqa .xmm11 .xmm7), .xop (.pclmulqdq .xmm11 .xmm12 0x11),
   .xop (.bin .movdqa .xmm2 .xmm1), .xop (.pclmulqdq .xmm2 .xmm13 0x11)] ++
  (if first then [.xop (.bin .movdqa .xmm10 .xmm11)] else [.xop (.bin .pxor .xmm10 .xmm11)]) ++
  [.xop (.bin .pxor .xmm10 .xmm2),
   .xop (.bin .movdqa .xmm11 .xmm7), .xop (.pclmulqdq .xmm11 .xmm12 0x01),
   .xop (.bin .movdqa .xmm2 .xmm7), .xop (.pclmulqdq .xmm2 .xmm12 0x10)] ++
  (if first then [.xop (.bin .movdqa .xmm9 .xmm11)] else [.xop (.bin .pxor .xmm9 .xmm11)]) ++
  [.xop (.bin .pxor .xmm9 .xmm2),
   .xop (.bin .movdqa .xmm11 .xmm1), .xop (.pclmulqdq .xmm11 .xmm13 0x01),
   .xop (.bin .movdqa .xmm2 .xmm1), .xop (.pclmulqdq .xmm2 .xmm13 0x10),
   .xop (.bin .pxor .xmm9 .xmm11), .xop (.bin .pxor .xmm9 .xmm2)]

theorem lane_pair (first : Bool) : zlaneSseBlock (pairZ first) = some (pairSse first) := by
  cases first <;> rfl

theorem pairSse_ok (first : Bool) (t : State) :
    WP isa (.block (pairSse first)) t fun t' =>
      prod t' = ((if first then Prod.zero else prod t).acc
        ((if first then t.xmm .xmm2 else 0) ^^^ XBinOp.eval .pshufb (t.xmm .xmm7) (t.xmm .xmm0)) (t.xmm .xmm12)).acc
        (XBinOp.eval .pshufb (t.xmm .xmm1) (t.xmm .xmm0)) (t.xmm .xmm13) ∧
      Only [.xmm7, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  apply WP.of_runBlock
  cases first <;>
  simp only [pairSse, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append,
    reduceCtorEq, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, Pclmul.eval_pxor, eval_movdqa, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · simp only [prod, Prod.acc, reduceCtorEq, ↓reduceIte, zero_xor_b]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]
  · simp only [prod, Prod.acc, Prod.zero, reduceCtorEq, ↓reduceIte, zero_xor_b, BitVec.xor_comm (t.xmm .xmm2)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

/-- `zmm` register `d` loaded from `a`. -/
abbrev ldZ (s : State) (d : XReg) (a : Addr) : State :=
  s.setZ d ((s.mem.readW a 512).extractLsb' 0 128) ((s.mem.readW a 512).extractLsb' 128 128)
    ((s.mem.readW a 512).extractLsb' 256 128) ((s.mem.readW a 512).extractLsb' 384 128)

theorem ldZ_zlane_ne (s : State) {d r : XReg} (a : Addr) (h : r ≠ d) {l : Nat} (hl : l < 4) :
    (ldZ s d a).zlane r l = s.zlane r l := State.zlane_setZ_ne _ h _ _ _ _ hl

theorem ldZ_zlane (s : State) (d : XReg) (a : Addr) {l : Nat} (hl : l < 4) :
    (ldZ s d a).zlane d l = s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := zlane_load s d a hl

/-- The products of a pair: blocks `4 ka + l` and `4 kb + l` of the group at
`rdx + 256 g` in lane `l`, times the powers at `scratch + tab g + 64 k`,
added to the lane's products (or written, for the first pair, with `Y`
added to the first block). -/
theorem pair_ok {ka kb g : Nat} (first : Bool) (t : State) (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask)
    (hina : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofInt 64 ((256 * g + 64 * ka : Nat) : Int)) 64)
    (hinb : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofInt 64 ((256 * g + 64 * kb : Nat) : Int)) 64)
    (hpa : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((tab g + 64 * ka : Nat) : Int)) 64)
    (hpb : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((tab g + 64 * kb : Nat) : Int)) 64) :
    WP isa (.block (pair ka kb g first)) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = ((if first then Prod.zero else prod (t.zproj l)).acc
        ((if first then t.zlane .xmm2 l else 0) ^^^
          blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((256 * g + 64 * ka : Nat) : Int) + BitVec.ofNat 64 (16 * l)))
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((tab g + 64 * ka : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)).acc
        (blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((256 * g + 64 * kb : Nat) : Int) + BitVec.ofNat 64 (16 * l)))
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((tab g + 64 * kb : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)) ∧
      ZFrame [.xmm12, .xmm7, .xmm13, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  let apa := t.gpr .r11 + BitVec.ofInt 64 ((tab g + 64 * ka : Nat) : Int)
  let aa := t.gpr .rdx + BitVec.ofInt 64 ((256 * g + 64 * ka : Nat) : Int)
  let apb := t.gpr .r11 + BitVec.ofInt 64 ((tab g + 64 * kb : Nat) : Int)
  let ab := t.gpr .rdx + BitVec.ofInt 64 ((256 * g + 64 * kb : Nat) : Int)
  let t₁ := ldZ t .xmm12 apa
  let t₂ := ldZ t₁ .xmm7 aa
  let t₃ := ldZ t₂ .xmm13 apb
  let t₄ := ldZ t₃ .xmm1 ab
  rw [pair, List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
    WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load512, ea_at, hpa, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨t₂, by simp only [isa, exec, State.load512, ea_at, t₁, State.setZ_gpr, State.setZ_rd, State.setZ_wr,
    State.setZ_mem, hina, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨t₃, by simp only [isa, exec, State.load512, ea_at, t₂, t₁, State.setZ_gpr, State.setZ_rd, State.setZ_wr,
    State.setZ_mem, hpb, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨t₄, by simp only [isa, exec, State.load512, ea_at, t₃, t₂, t₁, State.setZ_gpr, State.setZ_rd,
    State.setZ_wr, State.setZ_mem, hinb, ite_true, Option.map_some]; rfl, ?_⟩
  have keep : ∀ r, r ≠ .xmm12 → r ≠ .xmm7 → r ≠ .xmm13 → r ≠ .xmm1 → ∀ l < 4, t₄.zlane r l = t.zlane r l :=
    fun r h12 h7 h13 h1 l hl => by
      simp only [t₄, t₃, t₂, t₁]
      rw [ldZ_zlane_ne _ _ h1 hl, ldZ_zlane_ne _ _ h13 hl, ldZ_zlane_ne _ _ h7 hl, ldZ_zlane_ne _ _ h12 hl]
  have l12 : ∀ l < 4, t₄.zlane .xmm12 l = t.mem.readW (apa + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    simp only [t₄, t₃, t₂]
    rw [ldZ_zlane_ne _ _ (by decide) hl, ldZ_zlane_ne _ _ (by decide) hl, ldZ_zlane_ne _ _ (by decide) hl]
    exact ldZ_zlane t _ _ hl
  have l7 : ∀ l < 4, t₄.zlane .xmm7 l = t.mem.readW (aa + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    simp only [t₄, t₃]
    rw [ldZ_zlane_ne _ _ (by decide) hl, ldZ_zlane_ne _ _ (by decide) hl]
    exact ldZ_zlane t₁ _ _ hl
  have l13 : ∀ l < 4, t₄.zlane .xmm13 l = t.mem.readW (apb + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    simp only [t₄]
    rw [ldZ_zlane_ne _ _ (by decide) hl]
    exact ldZ_zlane t₂ _ _ hl
  have l1 : ∀ l < 4, t₄.zlane .xmm1 l = t.mem.readW (ab + BitVec.ofNat 64 (16 * l)) 128 := fun l hl =>
    ldZ_zlane t₃ _ _ hl
  refine WP.mono (WP.zlanes (lane_pair first) fun l _ => pairSse_ok first (t₄.zproj l))
    fun t' ⟨hk', hq⟩ => ⟨fun l hl => ?_, ?_⟩
  · rw [(hq l hl).1]
    have hp : prod (t₄.zproj l) = prod (t.zproj l) := by
      simp only [prod, State.zproj_xmm, keep .xmm8 (by decide) (by decide) (by decide) (by decide) l hl,
        keep .xmm9 (by decide) (by decide) (by decide) (by decide) l hl,
        keep .xmm10 (by decide) (by decide) (by decide) (by decide) l hl]
    simp only [hp, State.zproj_xmm, l7 l hl, l12 l hl, l13 l hl, l1 l hl,
      keep .xmm0 (by decide) (by decide) (by decide) (by decide) l hl, h0 l hl,
      keep .xmm2 (by decide) (by decide) (by decide) (by decide) l hl]
    rw [← blockAt_eq, ← blockAt_eq]
  · refine ⟨hk'.gpr, hk'.mem, hk'.rd, hk'.wr, fun r hr l hl => ?_⟩
    have := (hq l hl).2.xmm r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h | h | h | h | h <;> simp [h]))
    simp only [State.zproj_xmm] at this
    rw [this, keep r (fun h => hr (by simp [h])) (fun h => hr (by simp [h])) (fun h => hr (by simp [h]))
      (fun h => hr (by simp [h])) l hl]

end VG.Proof.Gcm.X86_64.StitchZ
