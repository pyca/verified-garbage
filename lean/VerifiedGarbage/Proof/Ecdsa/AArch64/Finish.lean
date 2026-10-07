import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar

/-!
# ECDSA on AArch64: the result

`finish` writes `r ‖ s` big-endian (`len` bytes each) to `out`, or zeros,
by the flag's mask, restores `x19`–`x25`, and returns the flag's low bit (`finish_ok`). The
stores are outside the working space, so it keeps its numbers and the saved
registers (`Outside.unch_far`).
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

variable {c : Cfg}

/-- The bytes of a range apart from the one that changed. -/
theorem bytesAt_keep {q p : Addr} {len k : Nat} {m m' : Mem} (h : Outside q 0 len m m')
    (hd : Region.Disjoint ⟨p, k⟩ ⟨q, len⟩) (hl : len ≤ 2 ^ 64) (hk : k ≤ 2 ^ 64) :
    Spec.Ecdsa.bytesAt m' p k = Spec.Ecdsa.bytesAt m p k := by
  simp only [Spec.Ecdsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact keep_of_disjoint' h hd hl hi hk

/-- `x0 = x3 & 1`, through `x1`. -/
theorem retBit_ok (s : State) :
    WP isa (.block [.movz .x .x1 1 0, .logic .and .x .x0 .x3 .x1]) s fun s' =>
      s'.gpr .x0 = s.gpr .x3 &&& 1 ∧ Keeps [.x0, .x1] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨by rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem mask_bit (b : Bool) :
    ((if b then BitVec.allOnes 64 else 0) &&& 1 : BitVec 64).setWidth 32 = if b then 1 else 0 := by
  cases b <;> decide

theorem finish_eq (c : Cfg) : c.finish = ([ld .x3 (c.sl FLAG)] : List Instr) ++
    (storeBytes c.C.len c.n .x20 0 (c.sl RR) ++ (storeBytes c.C.len c.n .x20 c.C.len (c.sl SS) ++
    (Spill.restoreCode .x0 Cfg.saved ++
    ([.movz .x .x1 1 0, .logic .and .x .x0 .x3 .x1] : List Instr)))) := by
  simp only [Cfg.finish, List.append_assoc]; rfl

theorem saved_lt : ∀ p ∈ Cfg.saved, p.2 + 8 ≤ 64 := by decide

theorem Saved.unch {base : Addr} {g : Reg → BitVec 64} {m m' : Mem}
    (h : Spill.Saved base g Cfg.saved m) {W : List (Nat × Nat)} (hW : ∀ w ∈ W, 64 ≤ w.1)
    (hu : Unch base W m m') : Spill.Saved base g Cfg.saved m' := fun p hp => by
  have := saved_lt p hp
  exact (hu.word (d := p.2) (fun w hw => Or.inl (by have := hW w hw; omega)) (by omega)).trans (h p hp)

/-- The result, the return value and the callee-saved registers. -/
theorem finish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {out : Addr}
    (hx20 : s.gpr .x20 = out) (hfit : out.toNat + 2 * c.C.len ≤ 2 ^ 64)
    (hw : (⟨out, 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 2 * c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 64} (hsv : Spill.Saved base g Cfg.saved s.mem) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block c.finish) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (2 * c.C.len) =
        (if b then toBytes c.C.len (sv c base s RR) ++ toBytes c.C.len (sv c base s SS)
          else List.replicate (2 * c.C.len) 0) ∧
      (s'.gpr .x0).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧
      (∀ r, r ∉ [.x0, .x1, .x2, .x3, .x17, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x30] →
        s'.gpr r = s.gpr r) := by
  have h7 := hc.n10
  have hn0 := hc.n0
  have hn := hs.nowrap
  have hl8 := hc.len8
  have hlo := hc.len_lo
  have hhi := hc.len_hi
  have hRR := sl_le c h7 (i := RR) (by decide)
  have hSS := sl_le c h7 (i := SS) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have h0 : ∀ e, out + BitVec.ofNat 64 0 + BitVec.ofNat 64 e = out + BitVec.ofNat 64 e := fun e =>
    congrArg (· + BitVec.ofNat 64 e) (BitVec.add_zero out)
  have hL : ∀ e, out + BitVec.ofNat 64 c.C.len + BitVec.ofNat 64 e =
      out + BitVec.ofNat 64 (c.C.len + e) := fun e => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + c.C.len ≤ 2 * c.C.len →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, c.C.len⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  have hscd : ∀ {d : Nat}, d + c.C.len ≤ 2 * c.C.len →
      Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 d, c.C.len⟩ := fun hd' =>
    hd.symm.sub_right (Offset.sub_base out hd')
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := c.sl FLAG) (by omega) (sl_mod8 c FLAG) .x3) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.mem
  have hx20₁ : s₁.gpr .x20 = out := by rw [k₁.gpr _ (by decide), hx20]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₁ (dst := .x20) (d := 0) (a := c.sl RR) (by decide) (by decide) (by decide) b
    (by rw [e₁, hf]) hRR (sl_mod8 c RR) (by omega) hlo hhi (by omega)
    (by rw [hx20₁, BitVec.add_zero]; omega)
    (fun e m he => ⟨_, by rw [k₁.wr]; exact hw, by
      rw [hx20₁, h0]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hx20₁]; exact hdsc hRR (by omega))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  rw [hx20₁] at e₂ O₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have U₂ := O₂.unch_far (hscd (d := 0) (by omega))
  have hx20₂ : s₂.gpr .x20 = out := by rw [k₂.gpr _ (by decide), hx20₁]
  have hx3₂ : s₂.gpr .x3 = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂.gpr _ (by decide), e₁, hf]
  have ss₂ : wordsVal s₂.mem base (c.sl SS) c.n = sv c base s SS := by
    rw [U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₂ (dst := .x20) (d := c.C.len) (a := c.sl SS) (by decide) (by decide)
    (by decide) b hx3₂ hSS (sl_mod8 c SS) (by omega) hlo hhi (by omega)
    (by rw [hx20₂, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show c.C.len < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]; omega)
    (fun e m he => ⟨_, by rw [k₂.wr, k₁.wr]; exact hw, by
      rw [hx20₂, hL]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hx20₂]; exact hdsc hSS (by omega))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hx20₂] at e₃ O₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have U₃ := O₃.unch_far (hscd (d := c.C.len) (by omega))
  have hx3₃ : s₃.gpr .x3 = if b then BitVec.allOnes 64 else 0 := by
    rw [k₃.gpr _ (by decide), hx3₂]
  have first : Spec.Ecdsa.bytesAt s₃.mem out c.C.len =
      if b then toBytes c.C.len (sv c base s RR) else List.replicate c.C.len 0 := by
    rw [bytesAt_keep O₃ (Offset.base_disjoint out (Nat.le_refl _) (by omega)) (by omega) (by omega)]
    have e₂' := e₂
    rw [(BitVec.add_zero out : out + BitVec.ofNat 64 0 = out)] at e₂'
    rw [e₂', hm₁]
  have hsv₃ : Spill.Saved base g Cfg.saved s₃.mem := by
    have h16 : ∀ w ∈ [(size, 2 ^ 64)], 64 ≤ w.1 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; decide
    exact Saved.unch (Saved.unch (hm₁ ▸ hsv) h16 U₂) h16 U₃
  refine Spill.restore_ok hs₃.x0 (by decide) (by decide) (fun p hp => ?_) hsv₃ fun s₄ R₄ => ?_
  · have := saved_lt p hp
    exact ⟨_, List.mem_append_right _ hs₃.wr, hs₃.contains (by have : size = 8192 := rfl; omega) (by decide)⟩
  refine WP.mono (retBit_ok s₄) fun s₅ ⟨e₅, k₅⟩ => ?_
  refine ⟨?_, ?_, fun r hr => ?_, fun r hr => ?_⟩
  · rw [k₅.mem, R₄.mem, show 2 * c.C.len = c.C.len + c.C.len by omega, bytesAt_add, first, e₃, ss₂]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.replicate_append_replicate]
    · simp only [ite_true]
  · have hx3 : Reg.x3 ∉ Cfg.saved.map Prod.fst := by decide
    rw [e₅, R₄.other _ hx3, hx3₃, mask_bit]
  · have : r ∉ [Reg.x0, .x1] := by
      revert r; decide
    rw [k₅.gpr r this]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact R₄.gpr p hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2, h3, h17, h19, h20, h21, h22, h23, h24, h25, h30⟩ := hr
    rw [k₅.gpr r (by simp [h0, h1]), R₄.other r (by simp [Cfg.saved, h19, h20, h21, h22, h23, h24, h25, h30]),
      k₃.gpr r (by simp [h1, h2, h17]), k₂.gpr r (by simp [h1, h2, h17]), k₁.gpr r (by simp [h3])]

end VG.Proof.Ecdsa.AArch64
