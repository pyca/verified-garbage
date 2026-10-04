import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar

/-!
# ECDSA on 32-bit ARM: the result

`finish` writes `r ‖ s` big-endian to `out` (in `lr`), or zeros, by the
flag's mask, returns the flag's low bit and restores `r4`–`r11` and `lr`
(`finish_ok`). The stores are outside the working space, so it
keeps its numbers and the saved registers (`Outside.unch_far`).
-/

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_dp op2_imm dpVal)

variable {c : Cfg}

/-- The bytes of a range apart from the one that changed. -/
theorem bytesAt_keep {q p : Addr} {len k : Nat} {m m' : Mem} (h : Outside q 0 len m m')
    (hd : Region.Disjoint ⟨p, k⟩ ⟨q, len⟩) (hl : len ≤ 2 ^ 64) (hk : k ≤ 2 ^ 64) :
    Spec.Ecdsa.bytesAt m' p k = Spec.Ecdsa.bytesAt m p k := by
  simp only [Spec.Ecdsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact keep_of_disjoint' h hd hl hi hk

/-- A range changed at `p + d` is one changed at offset `d` of `p`. -/
theorem outside_shift {p : Addr} {d len : Nat} {m m' : Mem}
    (h : Outside (p + BitVec.ofNat 64 d) 0 len m m') (hd : d + len ≤ 2 ^ 64) : Outside p d len m m' :=
  fun x hx => h x (Or.inr (by
    show 0 + len ≤ (x - (p + BitVec.ofNat 64 d)).toNat
    rcases Nat.lt_or_ge (x - (p + BitVec.ofNat 64 d)).toNat len with hlt | hge
    · have := (Offset.lt_iff x p hd).mp hlt
      simp only [ofs] at hx
      omega
    · omega))

theorem mask_bit (b : Bool) : (mask32 (b = true) &&& 1 : BitVec 32) = if b then 1 else 0 := by
  cases b <;> decide

theorem restore_eq : Cfg.restore = Cfg.saved.map fun p => .ldr p.1 wb p.2 := rfl

theorem saved_nodup : (Cfg.saved.map Prod.fst).Nodup := by decide

theorem finish_eq (c : Cfg) : c.finish = .ldr .r10 wb (c.sl FLAG) ::
    (storeBE c.n .lr 0 (c.sl RR) ++ (storeBE c.n .lr (8 * c.n) (c.sl SS) ++
    (.dp .and .r0 .r10 (.imm 1) :: Cfg.restore))) := by
  simp only [Cfg.finish, List.append_assoc, List.cons_append, List.nil_append]

/-- The result, the return value and the callee-saved registers. -/
theorem finish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {o32 : BitVec 32}
    (hout : s.gpr .lr = o32) (hofit : o32.toNat + 16 * c.n ≤ 2 ^ 32)
    (hw : (⟨State.addr o32, 16 * c.n⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨State.addr o32, 16 * c.n⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block c.finish) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (State.addr o32) (16 * c.n) =
        (if b then toBytes (8 * c.n) (sv c base s RR) ++ toBytes (8 * c.n) (sv c base s SS)
          else List.replicate (16 * c.n) 0) ∧
      s'.gpr .r0 = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
      Rest [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' ∧
      Outside (State.addr o32) 0 (16 * c.n) s.mem s'.mem := by
  have h7 := hc.n7
  have hn0 := hc.n0
  have hn := hs.nowrap
  have hsz : size = 4096 := rfl
  have hRR := sl_le c h7 (i := RR) (by decide)
  have hSS := sl_le c h7 (i := SS) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  generalize hout64 : State.addr o32 = out at hw hd ⊢
  have h0 : ∀ e, out + BitVec.ofNat 64 0 + BitVec.ofNat 64 e = out + BitVec.ofNat 64 e := fun e =>
    congrArg (· + BitVec.ofNat 64 e) (BitVec.add_zero out)
  have h8 : ∀ e, out + BitVec.ofNat 64 (8 * c.n) + BitVec.ofNat 64 e =
      out + BitVec.ofNat 64 (8 * c.n + e) := fun e => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + 8 * c.n ≤ 16 * c.n →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, 8 * c.n⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  have hscd : ∀ {d : Nat}, d + 8 * c.n ≤ 16 * c.n →
      Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 d, 8 * c.n⟩ := fun hd' =>
    hd.symm.sub_right (Offset.sub_base out hd')
  rw [finish_eq]
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read (d := c.sl FLAG) (n := 4) (by omega))
    fun s₁ u₁ => ?_
  have k₂ : Rest [.r10] s s₁ := u₁.rest (by simp)
  have hs₂ := hs.of_rest k₂ (by decide)
  have hm₂ : s₁.mem = s.mem := u₁.mem
  have hc₂ : s₁.gpr .r10 = mask32 (b = true) := by rw [u₁.gpr, ← flagW, hf]
  have hr1 : s₁.gpr .lr = o32 := by rw [u₁.other _ (by decide), hout]
  refine VG.Proof.X25519.Arm.WP.append (storeBE_ok hs₂ (dst := .lr) (d := 0) (a := c.sl RR) (by decide) b
    hc₂ hRR (by rw [hr1]; omega) (by omega) (fun e he => ⟨_, by rw [k₂.wr]; exact hw, by
      rw [hr1, hout64, h0]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hr1, hout64]; exact hdsc hRR (by omega))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hr1, hout64] at e₃ O₃
  have hs₃ := hs₂.of_rest k₃ (by decide)
  have U₃ := O₃.unch_far (hscd (d := 0) (by omega))
  have hr1₃ : s₃.gpr .lr = o32 := by rw [k₃.gpr _ (by decide), hr1]
  have hc₃ : s₃.gpr .r10 = mask32 (b = true) := by rw [k₃.gpr _ (by decide), hc₂]
  have ss₃ : wordsVal s₃.mem base (c.sl SS) c.n = sv c base s SS := by
    rw [U₃.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₂]
  refine VG.Proof.X25519.Arm.WP.append (storeBE_ok hs₃ (dst := .lr) (d := 8 * c.n) (a := c.sl SS) (by decide) b
    hc₃ hSS (by rw [hr1₃]; omega) (by omega) (fun e he => ⟨_, by rw [k₃.wr, k₂.wr]; exact hw, by
      rw [hr1₃, hout64, h8]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hr1₃, hout64]; exact hdsc hSS (by omega))) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [hr1₃, hout64] at e₄ O₄
  have hs₄ := hs₃.of_rest k₄ (by decide)
  have U₄ := O₄.unch_far (hscd (d := 8 * c.n) (by omega))
  have first : Spec.Ecdsa.bytesAt s₄.mem out (8 * c.n) =
      if b then toBytes (8 * c.n) (sv c base s RR) else List.replicate (8 * c.n) 0 := by
    rw [bytesAt_keep O₄ (Offset.base_disjoint out (Nat.le_refl _) (by omega)) (by omega) (by omega)]
    have e₃' := e₃
    rw [(BitVec.add_zero out : out + BitVec.ofNat 64 0 = out)] at e₃'
    rw [e₃', hm₂]
  have hsv₄ : ∀ rd ∈ Cfg.saved, s₄.mem.readW (off base rd.2) 32 = g rd.1 := by
    intro rd hrd
    have := saved_lt rd hrd
    have h16 : ∀ w ∈ [(size, 2 ^ 64)], rd.2 + 4 ≤ w.1 ∨ w.1 + w.2 ≤ rd.2 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; exact .inl (by omega)
    rw [Unch.readW32 U₄ h16 (by omega), Unch.readW32 U₃ h16 (by omega), hm₂, hsv rd hrd]
  -- The return value.
  refine wp_dp (op2_imm (by decide)) fun s₅ u₅ => ?_
  have hs₅ := hs₄.of_rest (u₅.rest (ws := [.r0]) (by simp)) (by decide)
  have r0₅ : s₅.gpr .r0 = if b then 1 else 0 := by
    rw [u₅.gpr, dpVal, k₄.gpr _ (by decide), hc₃]; exact mask_bit b
  -- The callee-saved registers.
  rw [restore_eq]
  refine WP.mono (ldrs_ok hs₅ Cfg.saved (fun p hp => by have := saved_lt p hp; omega) saved_nodup
    (fun p hp => (saved_r12 p hp).1)) fun s' ⟨m', K', V'⟩ => ⟨?_, ?_, fun rd hrd => ?_, ?_, ?_⟩
  · rw [m', u₅.mem, show 16 * c.n = 8 * c.n + 8 * c.n by omega, bytesAt_add, first, e₄, ss₃]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.replicate_append_replicate]
    · simp only [ite_true]
  · rw [K'.gpr _ (by decide), r0₅]
  · rw [V' rd hrd, u₅.mem, hsv₄ rd hrd]
  · exact ((k₂.mono (by simp)).trans ((k₃.mono (by simp)).trans (k₄.mono (by simp)))).trans
      ((u₅.rest (by simp)).trans (K'.mono (by decide)))
  · rw [m', u₅.mem, ← hm₂]
    exact ((outside_shift O₃ (by omega)).mono (Nat.zero_le _) (by omega)).trans
      ((outside_shift O₄ (by omega)).mono (Nat.zero_le _) (by omega))

end VG.Proof.Ecdsa.Arm
