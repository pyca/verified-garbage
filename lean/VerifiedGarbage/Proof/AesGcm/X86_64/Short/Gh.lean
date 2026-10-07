import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Ks

/-!
# AES-GCM's short path on x86-64: GHASH of the buffer

Untrusted: everything here is checked by Lean. `ghash` multiplies the `g`
groups of four blocks of `G` (at `W + 512`) by their powers (group `j` by
the table's group `g - 1 - j`, at `W + 1536`), lane by lane, adding the
products (`StitchZ.ghLoad_ok`), and then reduces and adds the four lanes'
sums into `xmm2` (`StitchZ.fin_ok`): `ghash_ok`. What that is in the field
is in `Short/Field.lean`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The products of lane `l` after `n` of the `g` groups: block `4 j + l` of
`G` times lane `l` of the table's group `g - 1 - j`. -/
def gacc (m : Mem) (G T : Addr) (g l n : Nat) : Prod :=
  (List.range n).foldl (fun p j => p.acc (blockAt m (G + BitVec.ofNat 64 (64 * j + 16 * l)))
    (m.readW (T + BitVec.ofNat 64 (64 * (g - 1 - j) + 16 * l)) 128)) Prod.zero

theorem gacc_succ (m : Mem) (G T : Addr) (g l n : Nat) :
    gacc m G T g l (n + 1) = (gacc m G T g l n).acc (blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * l)))
      (m.readW (T + BitVec.ofNat 64 (64 * (g - 1 - n) + 16 * l)) 128) := by
  simp only [gacc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem prod_zproj_zero (t : State) (h8 : ∀ l < 4, t.zlane .xmm8 l = 0) (h9 : ∀ l < 4, t.zlane .xmm9 l = 0)
    (h10 : ∀ l < 4, t.zlane .xmm10 l = 0) : ∀ l < 4, prod (t.zproj l) = Prod.zero := fun l hl => by
  simp only [prod, State.zproj_xmm, h8 l hl, h9 l hl, h10 l hl, Prod.zero]

/-- The products cleared. -/
theorem clear3_ok (t : State) :
    WP isa (.block [.zop (.zbin .vpxord .xmm8 .xmm8 .xmm8), .zop (.zbin .vpxord .xmm9 .xmm9 .xmm9),
        .zop (.zbin .vpxord .xmm10 .xmm10 .xmm10)]) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = Prod.zero) ∧ ZFrame [.xmm8, .xmm9, .xmm10] t t' := by
  refine WP.mono (WP.zframe (rs := [.xmm8, .xmm9, .xmm10]) (by decide)
    (Q := fun t' => ∀ l < 4, prod (t'.zproj l) = Prod.zero) ?_) fun t' h => h
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil fun l hl => ?_⟩
  simp only [prod, State.zproj_xmm, zlane_zbin _ _ _ _ _ _ hl, reduceCtorEq, ite_true, ite_false, ZBinOp.sse,
    VG.Proof.Gcm.X86_64.Pclmul.eval_pxor, BitVec.xor_self, Prod.zero]
  rfl

/-- `ghSetup`: `rdx` 128 bytes before `G`, `r11` 128 bytes before the powers
of `G`'s first group, `r9` the `g` groups, the products cleared. -/
theorem ghSetup_ok {W : Addr} {g : Nat} (s : State) (h15 : s.gpr .r15 = W)
    (hmp : s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g)) (hg : g ≤ 8)
    (r288 : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 288) 8) :
    WP isa (.block ghSetup) s fun t =>
      t.gpr .rdx = W + BitVec.ofNat 64 384 ∧ t.gpr .r9 = BitVec.ofNat 64 g ∧
      t.gpr .r11 = W + BitVec.ofNat 64 (1344 + 64 * g) ∧ (∀ l < 4, prod (t.zproj l) = Prod.zero) ∧
      (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm8, .xmm9, .xmm10] s t := by
  rw [show ghSetup = (ptr .rdx .r15 (gO - 128) ++ [.mov .r9 (.mem (at_ .r15 mpO)), .shift .shr .r9 2,
      .mov .r11 (.reg .r9), .shift .shl .r11 6, .alu .add .r11 (.reg .r15), .alu .add .r11 (imm (tbO - 192))]) ++
      [.zop (.zbin .vpxord .xmm8 .xmm8 .xmm8), .zop (.zbin .vpxord .xmm9 .xmm9 .xmm9),
       .zop (.zbin .vpxord .xmm10 .xmm10 .xmm10)] from rfl, WP.block_append_iff]
  have e₁ : BitVec.ofNat 64 (4 * g) >>> 2 = BitVec.ofNat 64 g := by rw [shr2 _ (by omega)]; congr 1; omega
  have e₂ : BitVec.ofNat 64 g <<< 6 = BitVec.ofNat 64 (64 * g) := by
    rw [shl_ofNat (by omega)]; congr 1; omega
  apply WP.of_runBlock
  refine ⟨_, by xrun [execShift, h15, hmp, r288, mpO, gO, tbO, e₁, e₂], ?_⟩
  refine WP.mono (clear3_ok _) fun t ⟨p, f⟩ => ⟨?_, ?_, ?_, p, fun r h₁ h₂ h₃ => ?_, f.mem, f.rd, f.wr,
    fun r hr l hl => f.zlane r (by simpa using hr) l hl⟩
  · rw [f.gpr]; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h15]
  · rw [f.gpr]; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags]
  · rw [f.gpr]; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h15]
    rw [BitVec.add_comm (BitVec.ofNat 64 (64 * g)) W, BitVec.add_assoc, ofNat_add_ofNat, Nat.add_comm]
  · rw [f.gpr]; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h₁, h₂, h₃]

theorem add_ofNat_ofNat (W : Addr) (a b : Nat) :
    W + BitVec.ofNat 64 a + BitVec.ofNat 64 b = W + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]

/-- A step of the loop: group `j` of `G` times its powers, added to the products. -/
theorem ghStep_ok {W : Addr} {g j : Nat} (t : State) (hj : j < g)
    (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask)
    (hrdx : t.gpr .rdx = W + BitVec.ofNat 64 (384 + 64 * j))
    (hr11 : t.gpr .r11 = W + BitVec.ofNat 64 (1344 + 64 * (g - j)))
    (hin : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 (512 + 64 * j)) 64)
    (hpin : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 (1472 + 64 * (g - j))) 64)
    (hp : ∀ l < 4, prod (t.zproj l) = gacc t.mem (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l j) :
    WP isa (.block ghBody) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = gacc t.mem (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l (j + 1)) ∧
      t'.gpr .rdx = W + BitVec.ofNat 64 (384 + 64 * (j + 1)) ∧
      t'.gpr .r11 = W + BitVec.ofNat 64 (1344 + 64 * (g - (j + 1))) ∧ t'.gpr .r9 = t.gpr .r9 - 1 ∧
      t'.zf = some (t.gpr .r9 - 1 == 0) ∧ (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t'.gpr r = t.gpr r) ∧
      t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      ZKeep [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  have ea₁ : t.gpr .rdx + BitVec.ofInt 64 ((64 * 2 : Nat) : Int) = W + BitVec.ofNat 64 (512 + 64 * j) := by
    rw [hrdx, BitVec.ofInt_natCast, add_ofNat_ofNat, show 384 + 64 * j + 64 * 2 = 512 + 64 * j by omega]
  have ea₂ : t.gpr .r11 + BitVec.ofInt 64 ((64 * 2 : Nat) : Int) = W + BitVec.ofNat 64 (1472 + 64 * (g - j)) := by
    rw [hr11, BitVec.ofInt_natCast, add_ofNat_ofNat,
      show 1344 + 64 * (g - j) + 64 * 2 = 1472 + 64 * (g - j) by omega]
  rw [ghBody, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.ghLoad_ok (k := 2) (by decide) t h0 (by rw [ea₁]; exact hin) (by rw [ea₂]; exact hpin))
    fun t₁ ⟨p₁, f₁⟩ => ?_
  apply WP.of_runBlock
  refine ⟨_, by xrun [], ?_⟩
  refine ⟨fun l hl => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show prod (t₁.zproj l) = _
    rw [p₁ l hl, gacc_succ, ← hp l hl, ea₁, ea₂, add_ofNat_ofNat, add_ofNat_ofNat]
    simp only [show (2 : Nat) ≠ VG.Impl.Gcm.X86_64.StitchZ.ord 0 by decide, ite_false,
      show (2 : Nat) ≠ 0 by decide, VG.Proof.Gcm.X86_64.Stitch.zero_xor_b]
    rw [show 512 + 64 * j + 16 * l = 512 + (64 * j + 16 * l) by omega, ← add_ofNat_ofNat,
      show 1472 + 64 * (g - j) + 16 * l = 1536 + (64 * (g - 1 - j) + 16 * l) by omega, ← add_ofNat_ofNat W 1536]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rw [f₁.gpr, hrdx, add_ofNat_ofNat]; congr 1
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rw [f₁.gpr, hr11, show 1344 + 64 * (g - j) = (1344 + 64 * (g - (j + 1))) + 64 by omega,
      ← add_ofNat_ofNat]
    exact BitVec.add_sub_cancel _ _
  · simp [gpr_setReg, gpr_arithFlags, f₁.gpr]
  · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, f₁.gpr]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, f₁.gpr]
  · exact f₁.mem
  · exact f₁.rd
  · exact f₁.wr
  · intro r hr l hl; exact f₁.zlane r hr l hl

/-- GHASH's products of the `g` groups of `G`, each lane reduced, added into
`xmm2`. -/
theorem ghash_ok {W : Addr} {g : Nat} (s : State) (h15 : s.gpr .r15 = W)
    (hmp : s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g)) (hg1 : 1 ≤ g) (hg : g ≤ 8)
    (hw : Covers [⟨W, 2560⟩] s.wr) (h0 : ∀ l < 4, s.zlane .xmm0 l = revMask)
    (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) :
    WP isa ghash s fun t =>
      t.zlane .xmm2 0 =
        (reduceB (gacc s.mem (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g 0 g) ^^^
          reduceB (gacc s.mem (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g 2 g)) ^^^
        (reduceB (gacc s.mem (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g 1 g) ^^^
          reduceB (gacc s.mem (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g 3 g)) ∧
      (∀ l, 1 ≤ l → l < 4 → t.zlane .xmm2 l = 0) ∧
      (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm2, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s t := by
  have wR : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
    fun h => in_left (in_off hw h (by decide))
  refine WP.seq (WP.mono (ghSetup_ok s h15 hmp hg (wR (by decide)))
    fun s₁ ⟨dx₁, r9₁, r11₁, p₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (t : State) => (∀ l < 4, prod (t.zproj l) =
      gacc s.mem (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l g) ∧
      (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s t) ?_
    fun t ⟨pt, gt, mt, rdt, wrt, zt⟩ => ?_)
  · refine WP.loop (M := isa) (body := .block ghBody) (c := .ne)
      (fun (n : Nat) (t : State) => ∃ j, n = g - j ∧ j < g ∧
        t.gpr .rdx = W + BitVec.ofNat 64 (384 + 64 * j) ∧ t.gpr .r11 = W + BitVec.ofNat 64 (1344 + 64 * (g - j)) ∧
        t.gpr .r9 = BitVec.ofNat 64 (g - j) ∧
        (∀ l < 4, prod (t.zproj l) = gacc s.mem (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l j) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ ZKeep [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s t) ?_ (g - 0) s₁
      ⟨0, rfl, hg1, by rw [dx₁], by rw [r11₁, Nat.sub_zero], by rw [r9₁, Nat.sub_zero], fun l hl => by rw [p₁ l hl]; rfl, g₁, m₁, rd₁, wr₁,
        z₁.mono (by simp)⟩
    rintro n t ⟨j, rfl, hj, dxt, r11t, r9t, pt, gt, mt, rdt, wrt, zt⟩
    have h0t : ∀ l < 4, t.zlane .xmm0 l = revMask := fun l hl => by rw [zt _ (by decide) l hl, h0 l hl]
    refine WP.mono (ghStep_ok t hj h0t dxt r11t (by rw [rdt, wrt]; exact wR (by omega))
      (by rw [rdt, wrt]; exact wR (by omega)) (fun l hl => by rw [pt l hl, mt]))
      fun t' ⟨p', dx', r11', r9', zf', g', m', rd', wr', z'⟩ => ?_
    have hz : t'.zf = some (decide (g - j = 1)) := by
      rw [zf', r9t, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, sub_beq (a := g - j) (b := 1) (by omega)
        (by omega)]
    have gg : ∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t'.gpr r = s.gpr r := fun r a b c => by
      rw [g' r a b c, gt r a b c]
    have pp : ∀ l < 4, prod (t'.zproj l) =
        gacc s.mem (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l (j + 1) := fun l hl => by
      rw [p' l hl, mt]
    by_cases he : j + 1 = g
    · left
      exact ⟨by simp [eval, hz]; omega, fun l hl => by rw [pp l hl, he], gg, by rw [m', mt], by rw [rd', rdt],
        by rw [wr', wrt], zt.trans (z'.mono (by simp))⟩
    · right
      refine ⟨by simp [eval, hz]; omega, g - (j + 1), by omega, j + 1, rfl, by omega, dx', r11', ?_, pp, gg,
        by rw [m', mt], by rw [rd', rdt], by rw [wr', wrt], zt.trans (z'.mono (by simp))⟩
      rw [r9', r9t, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub (by omega) (by omega)]; congr 1
  · have h1t : ∀ l < 4, t.zlane .xmm1 l = poly := fun l hl => by rw [zt _ (by decide) l hl, h1 l hl]
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.fin_ok t h1t) fun t' ⟨y0, y1, f'⟩ => ⟨?_, y1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [y0, pt 0 (by decide), pt 1 (by decide), pt 2 (by decide), pt 3 (by decide)]
    · intro r a b c; rw [f'.gpr, gt r a b c]
    · rw [f'.mem, mt]
    · rw [f'.rd, rdt]
    · rw [f'.wr, wrt]
    · intro r hr l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨n2, n7, n8, n9, n10, n11, n12⟩ := hr
      rw [f'.zlane r (by simp [n2, n8, n9, n10, n11]) l hl, zt r (by simp [n7, n8, n9, n10, n11, n12]) l hl]

end VG.Proof.AesGcm.X86_64.Short
