import VerifiedGarbage.Proof.AesSiv.AArch64.FinishShort
import VerifiedGarbage.Proof.AesSiv.Long

/-!
# AES-SIV on AArch64: finishing S2V with a string of a block or more

For a last string `P` of `L ≥ 16` bytes (`kOf`, `jOf`, `Proof/AesSiv/Long.lean`):
`longTail` computes `16 k` into `x28`, copies the last `T = L − 16 k` bytes
of `P` to the tail at `W + 32` and XORs `D` into its last 16 bytes, so the
tail is `P[16k..] xorend D` (`xorend_mem`); `longMac` chains the `k` blocks
of `P`, computes `j` into `x25`, chains the first `j` blocks of the tail,
and finalizes the rest of the tail (`long_spec`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64 VG.WriteBytes
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.AesSiv (kOf jOf kOf_lt kOf_ge kOf_tail jOf_rest jOf_le xorend_mem long_spec)
open VG.Proof.CmacAes.AArch64 (k0 mn xor2_ok)
open VG.Proof.CmacAes.Stream.AArch64 (UArgs FArgs Copied copy_ok toNat_ofNat toNat_add_lt upd_call
  bytesAt_writeBytes_self eval_zero mz0 mz16)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem mz1 : BitVec.setWidth 64 (1 : BitVec 16) <<< (16 * 0) = BitVec.ofNat 64 1 := by decide

/-- `(L − 1) >> 4`, the whole blocks before the last 1 to 16 bytes. -/
theorem nb_bv {L : Nat} (h : 0 < L) (hL : L < 2 ^ 64) :
    (BitVec.ofNat 64 L - BitVec.ofNat 64 1) >>> 4 = BitVec.ofNat 64 ((L - 1) / 16) := by
  rw [ofNat_sub (by omega_arith) hL, lsr4 (by omega_arith)]

/-- `16 k`, as the code computes it for `L ≥ 17`: `((L − 1) >> 4) − 1`, shifted left by 4. -/
theorem kOf_bv {L : Nat} (h : 17 ≤ L) (hL : L < 2 ^ 64) :
    (BitVec.ofNat 64 ((L - 1) / 16) - BitVec.ofNat 64 1) <<< 4 = BitVec.ofNat 64 (16 * kOf L) := by
  rw [kOf_ge (by omega_arith), ofNat_sub (by omega_arith) (by omega_arith)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show (L - 1) / 16 - 1 < 2 ^ 64 by omega_arith)]
  omega_arith

theorem lsl4 {j : Nat} (h : j ≤ 1) : BitVec.ofNat 64 j <<< 4 = BitVec.ofNat 64 (16 * j) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> decide

/-! ## The tail -/

/-- `16 k` in `x28`. -/
theorem kBlock_wp {s : State} (h23 : s.gpr .x23 = BitVec.ofNat 64 L) (hL16 : 16 ≤ L) (hL : L < 2 ^ 64) :
    WP isa kBlock s fun s' =>
      s'.gpr .x28 = BitVec.ofNat 64 (16 * kOf L) ∧ (∀ r, r ≠ .x9 → r ≠ .x28 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [kBlock]
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩)
  generalize ht : ((s.write .x .x9 (s.gpr .x23 - BitVec.ofNat 64 1)).write .x .x9
      ((s.gpr .x23 - BitVec.ofNat 64 1) >>> 4)).write .x .x28
      (BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0)) = t
  have x9 : t.gpr .x9 = BitVec.ofNat 64 ((L - 1) / 16) := by
    rw [← ht]; simp [gpr_write, h23, nb_bv (show 0 < L by omega_arith) hL]
  have x9t := x9
  have gt : ∀ r, r ≠ .x9 → r ≠ .x28 → t.gpr r = s.gpr r := fun r a b => by rw [← ht]; simp [gpr_write, a, b]
  have x28t : t.gpr .x28 = 0 := by rw [← ht]; simp [gpr_write]
  have ev := eval_zero (s := t) (r := .x9) (x := (L - 1) / 16) (by omega_arith) x9t
  by_cases h17 : L < 17
  · refine WP.ite true (by rw [ev]; simp; omega_arith) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [x28t, kOf_lt h17]; rfl, gt, by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl,
      by rw [← ht]; rfl⟩
  · refine WP.ite false (by rw [ev]; simp; omega_arith) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, gpr_write, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨by simp [gpr_write, x9t, kOf_bv (by omega_arith) hL], fun r a b => by simp [gpr_write, a, b, gt r a b],
      by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl⟩

/-- What `longTail` leaves: `16 k` in `x28`, and the tail `P[16k..] xorend D`
at `W + 32`. -/
structure LTail (s₀ : State) (C D P W : Addr) (R L : Nat) (s s' : State) : Prop where
  regs : Regs s₀ C D P W R L s'
  keep : ∀ r ∈ preserved, r ≠ .x28 → s'.gpr r = s.gpr r
  x28 : s'.gpr .x28 = BitVec.ofNat 64 (16 * kOf L)
  frame : Frame [⟨W + BitVec.ofNat 64 32, 32⟩] s.mem s'.mem
  tail : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 32) (L - 16 * kOf L) =
    Spec.Siv.xorend (Spec.Aes.bytesAt s.mem (P + BitVec.ofNat 64 (16 * kOf L)) (L - 16 * kOf L))
      (Spec.Aes.bytesAt s.mem D 16)

theorem longTail_wp (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) (hL16 : 16 ≤ L) :
    WP isa longTail s (LTail s₀ C D P W R L s) := by
  have hwW := h.wW
  have hlt := h.lt
  have hT := kOf_tail hL16
  have hD := h.hD
  refine WP.seq (WP.mono (kBlock_wp hr.x23 hL16 hlt) fun s₁ ⟨x28₁, g₁, sp₁, m₁, rd₁, wr₁⟩ => ?_)
  have hr₁ : Regs s₀ C D P W R L s₁ :=
    hr.keep' (fun r hr' => g₁ r (dec_ne (by decide) hr') (dec_ne (by decide) hr')) sp₁ rd₁ wr₁
  -- The arguments of the copy.
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, tailArgs, tailOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩)
  generalize hs₂ : ((s₁.write .x .x6 (s₁.gpr .x19 + BitVec.ofNat 64 32)).write .x .x7
      (s₁.gpr .x22 + s₁.gpr .x28)).write .x .x8 (s₁.gpr .x23 - s₁.gpr .x28) = s₂
  have g₂ (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x8) : s₂.gpr r = s₁.gpr r := by
    rw [← hs₂]; simp [gpr_write, a, b, c]
  have x6₂ : s₂.gpr .x6 = W + BitVec.ofNat 64 32 := by rw [← hs₂]; simp [gpr_write, hr₁.x19]
  have x7₂ : s₂.gpr .x7 = P + BitVec.ofNat 64 (16 * kOf L) := by rw [← hs₂]; simp [gpr_write, hr₁.x22, x28₁]
  have x8₂ : s₂.gpr .x8 = BitVec.ofNat 64 (L - 16 * kOf L) := by
    rw [← hs₂]; simp [gpr_write, hr₁.x23, x28₁, ofNat_sub (show 16 * kOf L ≤ L by omega_arith) hlt]
  have m₂ : s₂.mem = s₁.mem := by rw [← hs₂]; rfl
  have sp₂ : s₂.sp = s₁.sp := by rw [← hs₂]; rfl
  have rd₂ : s₂.rd = s₀.rd := by rw [← hs₂, rd_write, rd_write, rd_write, hr₁.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [← hs₂, wr_write, wr_write, wr_write, hr₁.wr]
  have dPT : (⟨P + BitVec.ofNat 64 (16 * kOf L), L - 16 * kOf L⟩ : Region).Disjoint
      ⟨W + BitVec.ofNat 64 32, L - 16 * kOf L⟩ :=
    (h.p_w.sub_left (h.sP (by omega_arith))).sub_right (h.sW (by omega_arith))
  refine WP.seq (WP.mono (copy_ok s₂ (by omega_arith) x7₂ x6₂ x8₂
    (fun i hi => by rw [Offset.add_add]; exact h.inRP rd₂ wr₂ (by omega_arith))
    (fun i hi => by rw [Offset.add_add]; exact h.inW wr₂ (by omega_arith)) dPT) fun s₃ h₃ => ?_)
  have g₃ (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x8) (d : r ≠ .x9) : s₃.gpr r = s₁.gpr r := by
    rw [h₃.other r a b c d, g₂ r a b c]
  have hlen : (Spec.Aes.bytesAt s₂.mem (P + BitVec.ofNat 64 (16 * kOf L)) (L - 16 * kOf L)).length =
      L - 16 * kOf L := Proof.Cmac.bytesAt_length _ _ _
  have f₃ : Frame [⟨W + BitVec.ofNat 64 32, 32⟩] s₂.mem s₃.mem := by
    rw [h₃.mem]; exact writeBytes_frame _ _ _ (by
      rw [hlen]; simpa using Offset.contains_base (W + BitVec.ofNat 64 32) (d := 0) (n := L - 16 * kOf L) (k := 32)
        (by omega_arith) (by decide))
  -- `D` into the last block of the tail.
  rw [tailXor, WP.block_append_iff]
  refine WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  generalize hs₄ : (s₃.write .x .x6 (s₃.gpr .x23 - s₃.gpr .x28)).write .x .x6
      (s₃.gpr .x19 + (s₃.gpr .x23 - s₃.gpr .x28)) = s₄
  have x6₄ : s₄.gpr .x6 = W + BitVec.ofNat 64 (L - 16 * kOf L) := by
    rw [← hs₄]
    simp [gpr_write, g₃ .x19 (by decide) (by decide) (by decide) (by decide),
      g₃ .x23 (by decide) (by decide) (by decide) (by decide), g₃ .x28 (by decide) (by decide) (by decide) (by decide),
      hr₁.x19, hr₁.x23, x28₁, ofNat_sub (show 16 * kOf L ≤ L by omega_arith) hlt]
  have g₄ (r : Reg) (a : r ≠ .x6) : s₄.gpr r = s₃.gpr r := by rw [← hs₄]; simp [gpr_write, a]
  have rd₄ : s₄.rd = s₀.rd := by rw [← hs₄, rd_write, rd_write, h₃.rd, rd₂]
  have wr₄ : s₄.wr = s₀.wr := by rw [← hs₄, wr_write, wr_write, h₃.wr, wr₂]
  have eT : W + BitVec.ofNat 64 (L - 16 * kOf L) + BitVec.ofNat 64 16 =
      W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (L - 16 * kOf L - 16) := by
    rw [Offset.add_add, Offset.add_add, show L - 16 * kOf L + 16 = 32 + (L - 16 * kOf L - 16) by omega_arith]
  have eT8 : W + BitVec.ofNat 64 (L - 16 * kOf L) + BitVec.ofNat 64 (16 + 8) =
      W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (L - 16 * kOf L - 16) + BitVec.ofNat 64 8 := by
    rw [Offset.add_add, Offset.add_add, Offset.add_add]
    exact congrArg (fun n => W + BitVec.ofNat 64 n) (by omega_arith)
  have iW (d : Nat) (hd : d + 8 ≤ 64) : InRegions s₄.wr (W + BitVec.ofNat 64 d) 8 := h.inW wr₄ (by omega_arith)
  have iRW (d : Nat) (hd : d + 8 ≤ 64) : InRegions (s₄.rd ++ s₄.wr) (W + BitVec.ofNat 64 d) 8 :=
    h.inRW rd₄ wr₄ (by omega_arith)
  have eA : W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (L - 16 * kOf L - 16) =
      W + BitVec.ofNat 64 (L - 16 * kOf L + 16) := by
    rw [Offset.add_add, show 32 + (L - 16 * kOf L - 16) = L - 16 * kOf L + 16 by omega_arith]
  have eA8 : W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (L - 16 * kOf L - 16) + BitVec.ofNat 64 8 =
      W + BitVec.ofNat 64 (L - 16 * kOf L + 24) := by
    rw [eA, Offset.add_add]
  have x19₄ : s₄.gpr .x19 = W := by
    rw [g₄ _ (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide), hr₁.x19]
  obtain ⟨s₅, run₅, m₅, g₅, sp₅, rd₅, wr₅⟩ := xor2_ok s₄ .x6 .x19 .x6 16 dOff 16
    (P := W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (L - 16 * kOf L - 16)) (Q := D)
    (C := W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (L - 16 * kOf L - 16))
    (by decide) (by decide) (by decide) (by rw [x6₄, eT]) (by rw [x6₄, eT8])
    (by rw [x19₄, hD]) (by rw [x19₄, hD, Offset.add_add]) (by rw [x6₄, eT]) (by rw [x6₄, eT8])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [eA]; exact iRW _ (by omega_arith)) (by rw [eA8]; exact iRW _ (by omega_arith))
    (by have := h.inRD rd₄ wr₄ (d := 0) (n := 8) (by decide); rwa [k0] at this)
    (h.inRD rd₄ wr₄ (by decide))
    (by rw [eA]; exact iW _ (by omega_arith)) (by rw [eA8]; exact iW _ (by omega_arith))
  refine WP.of_runBlock ⟨s₅, by rw [xor2_eq]; exact run₅, ?_⟩
  have f₅ : Frame [⟨W + BitVec.ofNat 64 32, 32⟩] s₄.mem s₅.mem := by
    rw [m₅]; exact (Proof.Cmac.xor2Mem_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 32, 32⟩, List.mem_singleton_self _,
        Offset.sub_base (W + BitVec.ofNat 64 32) (d := L - 16 * kOf L - 16) (n := 16) (k := 32) (by omega_arith)⟩
  have keep (r : Reg) (hr' : r ∈ preserved) (h28 : r ≠ .x28) : s₅.gpr r = s.gpr r := by
    have a : r ≠ .x6 := by rintro rfl; revert hr'; decide
    have b : r ≠ .x7 := by rintro rfl; revert hr'; decide
    have c : r ≠ .x8 := by rintro rfl; revert hr'; decide
    have d : r ≠ .x9 := by rintro rfl; revert hr'; decide
    have e : r ≠ .x10 := by rintro rfl; revert hr'; decide
    rw [g₅ r d e, g₄ r a, g₃ r a b c d, g₁ r d h28]
  refine ⟨hr.keep' (fun r hr' => keep r (dec_mem (by decide) hr') (dec_ne (by decide) hr'))
      (by rw [sp₅, ← hs₄]; simp only [sp_write]; rw [h₃.sp, sp₂, sp₁]) (by rw [rd₅, rd₄, hr.rd])
      (by rw [wr₅, wr₄, hr.wr]), keep,
    by rw [g₅ _ (by decide) (by decide), g₄ _ (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide),
      x28₁], ?_, ?_⟩
  · have m₄ : s₄.mem = s₃.mem := by rw [← hs₄]; rfl
    rw [← m₁, ← m₂]
    exact f₃.trans (by rw [← m₄]; exact f₅)
  · have tD : (⟨W + BitVec.ofNat 64 32, L - 16 * kOf L⟩ : Region).Disjoint ⟨D, 16⟩ :=
      (h.d_w.sub_right (h.sW (by omega_arith))).symm
    have dD (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 32, 32⟩ : Region)]) : (⟨D, 16⟩ : Region).Disjoint r := by
      simp only [List.mem_singleton] at hr; subst hr; exact h.d_w.sub_right (h.sW (by decide))
    have m₄ : s₄.mem = s₃.mem := by rw [← hs₄]; rfl
    have ws := bytesAt_writeBytes_self s₂.mem (W + BitVec.ofNat 64 32)
      (xs := Spec.Aes.bytesAt s₂.mem (P + BitVec.ofNat 64 (16 * kOf L)) (L - 16 * kOf L)) (by rw [hlen]; omega_arith)
    rw [hlen] at ws
    rw [m₅, xorend_mem _ hT.1 (by rw [toNat_add_lt W hwW (show 32 < 2560 by decide)]; omega_arith) tD, m₄,
      Proof.Cmac.bytesAt_frame f₃ dD (by decide), h₃.mem, ws, m₂, m₁]

/-! ## The calls -/

/-- The arguments of the update over the `k` blocks of `P`. -/
theorem m1_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) (hL16 : 16 ≤ L) (h28 : s.gpr .x28 = BitVec.ofNat 64 (16 * kOf L)) :
    ∃ s', runBlock isa (longArgs₁ out) s = some s' ∧ Regs s₀ C D P W R L s' ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      UArgs s' C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧
      s'.mem = Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 out) := by
  have hT := kOf_tail hL16
  have hlt := h.lt
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := h.zero16_ok hr.x19 hr.wr (d := out) (by omega_arith) (by omega_arith)
  have hout' : out < 4096 := by omega_arith
  refine ⟨_, by
    rw [longArgs₁, runBlock_append, run₁, Option.bind_some]
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, csOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq, hout']
    rfl, ?_⟩
  have g (r : Reg) (hr' : r ∈ preserved) : ((((((s₁.write .x .x4 (s₁.gpr .x28 >>> 4)).write .x .x0
      (s₁.gpr .x20 + BitVec.ofNat 64 0)).write .x .x1 (s₁.gpr .x21 + BitVec.ofNat 64 0)).write .x .x2
      (s₁.gpr .x19 + BitVec.ofNat 64 out)).write .x .x3 (s₁.gpr .x22 + BitVec.ofNat 64 0)).write .x .x5
      (s₁.gpr .x19 + BitVec.ofNat 64 256)).gpr r = s.gpr r := by
    rw [← g₁ r (by rintro rfl; revert hr'; decide)]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  have hr' := hr.keep' (fun r hr' => g r (dec_mem (by decide) hr')) sp₁ rd₁ wr₁
  have x19 : s₁.gpr .x19 = W := by rw [g₁ _ (by decide), hr.x19]
  refine ⟨hr', g, h.uargs hr'.rd hr'.wr (by omega_arith) (h.srcData₀ (by omega_arith) (by omega_arith)) (by omega_arith)
    (by simp [gpr_write, g₁ _ (by decide : Reg.x20 ≠ .x9), hr.x20])
    (by simp [gpr_write, g₁ _ (by decide : Reg.x21 ≠ .x9), hr.x21]) (by simp [gpr_write, x19])
    (by simp [gpr_write, g₁ _ (by decide : Reg.x22 ≠ .x9), hr.x22])
    (by simp [gpr_write, g₁ _ (by decide : Reg.x28 ≠ .x9), h28, lsr4 (show 16 * kOf L < 2 ^ 64 by omega_arith)])
    (by simp [gpr_write, x19]), by simp [mem_write, m₁]⟩

/-- `j` in `x25`. -/
theorem jBlock_wp {s : State} (h23 : s.gpr .x23 = BitVec.ofNat 64 L) (hL16 : 16 ≤ L) (hL : L < 2 ^ 64) :
    WP isa jBlock s fun s' =>
      s'.gpr .x25 = BitVec.ofNat 64 (jOf L) ∧ (∀ r, r ≠ .x9 → r ≠ .x25 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [jBlock]
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩)
  generalize ht : ((s.write .x .x9 (s.gpr .x23 - BitVec.ofNat 64 1)).write .x .x9
      ((s.gpr .x23 - BitVec.ofNat 64 1) >>> 4)).write .x .x25
      (BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0)) = t
  have x9t : t.gpr .x9 = BitVec.ofNat 64 ((L - 1) / 16) := by
    rw [← ht]; simp [gpr_write, h23, nb_bv (show 0 < L by omega_arith) hL]
  have gt : ∀ r, r ≠ .x9 → r ≠ .x25 → t.gpr r = s.gpr r := fun r a b => by rw [← ht]; simp [gpr_write, a, b]
  have x25t : t.gpr .x25 = 0 := by rw [← ht]; simp [gpr_write]
  have ev := eval_zero (s := t) (r := .x9) (x := (L - 1) / 16) (by omega_arith) x9t
  by_cases h17 : L < 17
  · refine WP.ite true (by rw [ev]; simp; omega_arith) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [x25t]; simp [jOf, h17], gt, by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl,
      by rw [← ht]; rfl⟩
  · refine WP.ite false (by rw [ev]; simp; omega_arith) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        ]
      rfl, ?_⟩
    refine ⟨by simp [gpr_write, jOf, h17], fun r a b => by simp [gpr_write, b, gt r a b],
      by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl⟩

/-- The arguments of the update over the first `j` blocks of the tail. -/
theorem m3_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) (h25 : s.gpr .x25 = BitVec.ofNat 64 (jOf L)) :
    ∃ s', runBlock isa (longArgs₂ out) s = some s' ∧ Regs s₀ C D P W R L s' ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      UArgs s' C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) := by
  have hj := jOf_le L
  have hout' : out < 4096 := by omega_arith
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, longArgs₂, mov, tailOff, csOff, runBlock_cons, runStep_some,
      runBlock_nil, exec, Size.bits, State.read, gpr_write, BitVec.setWidth_eq, hout']
    rfl, ?_⟩
  have g (r : Reg) (hr' : r ∈ preserved) : ((((((s.write .x .x4 (s.gpr .x25 + BitVec.ofNat 64 0)).write .x .x0
      (s.gpr .x20 + BitVec.ofNat 64 0)).write .x .x1 (s.gpr .x21 + BitVec.ofNat 64 0)).write .x .x2
      (s.gpr .x19 + BitVec.ofNat 64 out)).write .x .x3 (s.gpr .x19 + BitVec.ofNat 64 32)).write .x .x5
      (s.gpr .x19 + BitVec.ofNat 64 256)).gpr r = s.gpr r := by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  have hr' := hr.keep' (fun r hr' => g r (dec_mem (by decide) hr')) rfl rfl rfl
  exact ⟨hr', g, rfl, h.uargs hr'.rd hr'.wr (by omega_arith)
    (h.srcWork (o := out) (t := 32) (n := 16 * jOf L) (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
    (by simp [gpr_write, hr.x20]) (by simp [gpr_write, hr.x21]) (by simp [gpr_write, hr.x19])
    (by simp [gpr_write, hr.x19]) (by simp [gpr_write, h25]) (by simp [gpr_write, hr.x19])⟩

/-- The arguments of the finalization of the rest of the tail. -/
theorem m4_run (s : State) {out : Nat} (hout : out < 4096) :
    ∃ s', runBlock isa (longArgs₃ out) s = some s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.gpr .x0 = s.gpr .x20 ∧ s'.gpr .x1 = s.gpr .x21 ∧ s'.gpr .x2 = s.gpr .x19 + BitVec.ofNat 64 out ∧
      s'.gpr .x3 = s.gpr .x19 + BitVec.ofNat 64 32 + s.gpr .x25 <<< 4 ∧
      s'.gpr .x4 = s.gpr .x23 - s.gpr .x28 - s.gpr .x25 <<< 4 ∧ s'.gpr .x5 = s.gpr .x19 + BitVec.ofNat 64 256 ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, longArgs₃, mov, tailOff, csOff, runBlock_cons, runStep_some,
      runBlock_nil, exec, Size.bits, State.read, gpr_write, BitVec.setWidth_eq, hout]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

theorem m4_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) (hL16 : 16 ≤ L) (h28 : s.gpr .x28 = BitVec.ofNat 64 (16 * kOf L))
    (h25 : s.gpr .x25 = BitVec.ofNat 64 (jOf L)) :
    ∃ s', runBlock isa (longArgs₃ out) s = some s' ∧ Regs s₀ C D P W R L s' ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      FArgs s' C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R := by
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hj1 := jOf_le L
  have hlt := h.lt
  obtain ⟨s', run, g, x0, x1, x2, x3, x4, x5, sp, m, rd, wr⟩ := m4_run s (out := out) (by omega_arith)
  have hr' := hr.keep' (fun r hr' => g r (dec_mem (by decide) hr')) sp rd wr
  refine ⟨s', run, hr', g, m, h.fargs hr'.rd hr'.wr (by omega_arith)
    (h.srcWork (o := out) (t := 32 + 16 * jOf L) (n := L - 16 * kOf L - 16 * jOf L) (by omega_arith) (by omega_arith)
      (by omega_arith)) (by omega_arith) (by rw [x0, hr.x20]) (by rw [x1, hr.x21]) (by rw [x2, hr.x19])
    (by rw [x3, hr.x19, h25, lsl4 hj1, Offset.add_add]) ?_ (by rw [x5, hr.x19])⟩
  rw [x4, hr.x23, h28, h25, lsl4 hj1, ofNat_sub (show 16 * kOf L ≤ L by omega_arith) hlt,
    ofNat_sub (show 16 * jOf L ≤ L - 16 * kOf L by omega_arith) (by omega_arith)]

/-! ## The whole long case -/

/-- The regions `longMac` writes. -/
abbrev macRegions (W : Addr) (out : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩]

/-- What `longMac` leaves: CMAC's last step on the tail's last bytes, after the
`k` blocks of `P` and the first `j` blocks of the tail, all as they were. -/
structure LMac (s₀ : State) (C D P W : Addr) (R L out : Nat) (s s' : State) : Prop where
  regs : Regs s₀ C D P W R L s'
  hold : Hold2 s s'
  frame : Frame (macRegions W out) s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 out) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1)))
      (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 240) 16)
          (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 256) 16)
          (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (L - 16 * kOf L - 16 * jOf L)))
        (Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1))))
          (Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1)))) (Spec.Cmac.zeros 16)
            (Spec.Cmac.blocks 16 (Spec.Aes.bytesAt s.mem P (16 * kOf L))))
          (Spec.Cmac.blocks 16 (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 32) (16 * jOf L)))))

theorem longMac_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : Env s₀ C D P W R L) {s₁ : State}
    (hr₁ : Regs s₀ C D P W R L s₁) (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112)
    (h28 : s₁.gpr .x28 = BitVec.ofNat 64 (16 * kOf L)) :
    WP isa (longMac v.callee v.ctr.callee v.ctr.suffix out) s₁ (LMac s₀ C D P W R L out s₁) := by
  have hwW := h.wW
  have hlt := h.lt
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hj1 := jOf_le L
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_arith
  obtain ⟨s₂, run₂, hr₂, g₂, u₂, m₂⟩ := m1_ok h hr₁ hout hL16 h28
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.seq (WP.mono (upd_call v _ u₂) fun s₃ h₃ => ?_)
  have hr₃ := hr₂.keep h₃.saved h₃.sp h₃.rd h₃.wr
  refine WP.seq (WP.mono (jBlock_wp hr₃.x23 hL16 hlt) fun s₄ ⟨x25₄, g₄, sp₄, m₄, rd₄, wr₄⟩ => ?_)
  have hr₄ := hr₃.keep' (fun r hr' => g₄ r (dec_ne (by decide) hr') (dec_ne (by decide) hr')) sp₄ rd₄ wr₄
  obtain ⟨s₅, run₅, hr₅, g₅, m₅, u₅⟩ := m3_ok h hr₄ hout x25₄
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  refine WP.seq (WP.mono (upd_call v _ u₅) fun s₆ h₆ => ?_)
  have hr₆ := hr₅.keep h₆.saved h₆.sp h₆.rd h₆.wr
  have x28₆ : s₆.gpr .x28 = BitVec.ofNat 64 (16 * kOf L) := by
    rw [h₆.saved _ (by decide) (by decide), g₅ _ (by decide), g₄ _ (by decide) (by decide),
      h₃.saved _ (by decide) (by decide), g₂ _ (by decide), h28]
  have x25₆ : s₆.gpr .x25 = BitVec.ofNat 64 (jOf L) := by
    rw [h₆.saved _ (by decide) (by decide), g₅ _ (by decide), x25₄]
  obtain ⟨s₇, run₇, hr₇, g₇, m₇, fa₇⟩ := m4_ok h hr₆ hout hL16 x28₆ x25₆
  refine WP.seq (WP.of_runBlock ⟨s₇, run₇, ?_⟩)
  refine WP.mono (finr_call v.ctr _ fa₇) fun s₈ h₈ => ?_
  have f₂ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact Proof.Cmac.frame_store2 _ _ _
  have f₃ : Frame (macRegions W out) s₂.mem s₃.mem := h₃.frame
  have f₆ : Frame (macRegions W out) s₅.mem s₆.mem := h₆.frame
  have f₈ : Frame (macRegions W out) s₇.mem s₈.mem := h₈.frame
  have F₂ : Frame (macRegions W out) s₁.mem s₂.mem := f₂.mono (by simp)
  have g₂₅ : Frame (macRegions W out) s₁.mem s₅.mem := by
    rw [m₅, m₄]; exact F₂.trans f₃
  have g₂₇ : Frame (macRegions W out) s₁.mem s₇.mem := by rw [m₇]; exact g₂₅.trans f₆
  refine ⟨hr₇.keep h₈.saved h₈.sp h₈.rd h₈.wr, Hold2.of fun r hr h25 h28 h30 => ?_, g₂₇.trans f₈, ?_⟩
  · have n9 : r ≠ .x9 := by rintro rfl; revert hr; decide
    rw [h₈.saved r hr h30, g₇ r hr, h₆.saved r hr h30, g₅ r hr, g₄ r n9 h25, h₃.saved r hr h30, g₂ r hr]
  have dC {m : Mem} (hm : Frame (macRegions W out) s₁.mem m) {d n : Nat} (hd : d + n ≤ 512) :
      Spec.Aes.bytesAt m (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 d) n :=
    Proof.Cmac.bytesAt_frame hm (fun r hr => by
      have hc := h.c_w.sub_left (h.sC hd)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hc.sub_right (h.sW (by omega_arith))
      · exact hc.sub_right (h.sW (by decide))) (by omega_arith)
  have dP {m : Mem} (hm : Frame (macRegions W out) s₁.mem m) {d n : Nat} (hd : d + n ≤ L) :
      Spec.Aes.bytesAt m (P + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₁.mem (P + BitVec.ofNat 64 d) n :=
    Proof.Cmac.bytesAt_frame hm (fun r hr => by
      have hc := h.p_w.sub_left (h.sP hd)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hc.sub_right (h.sW (by omega_arith))
      · exact hc.sub_right (h.sW (by decide))) (by omega_arith)
  have dT {m : Mem} (hm : Frame (macRegions W out) s₁.mem m) {d n : Nat} (hd : 32 ≤ d) (hd' : d + n ≤ 64) :
      Spec.Aes.bytesAt m (W + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 d) n :=
    Proof.Cmac.bytesAt_frame hm (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
      · exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
  have hz : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂]; exact Proof.Cmac.zero2_bytes _ _
  have sch₂ := dC F₂ (d := 0) (n := 16 * (R + 1)) (by omega_arith)
  have sch₅ := dC g₂₅ (d := 0) (n := 16 * (R + 1)) (by omega_arith)
  have sch₇ := dC g₂₇ (d := 0) (n := 16 * (R + 1)) (by omega_arith)
  rw [k0] at sch₂ sch₅ sch₇
  have k1 := dC g₂₇ (d := 240) (n := 16) (by decide)
  have k2 := dC g₂₇ (d := 256) (n := 16) (by decide)
  have pk := dP F₂ (d := 0) (n := 16 * kOf L) (by omega_arith)
  rw [k0] at pk
  have t₅ := dT g₂₅ (d := 32) (n := 16 * jOf L) (by decide) (by omega_arith)
  have t₇ := dT g₂₇ (d := 32 + 16 * jOf L) (n := L - 16 * kOf L - 16 * jOf L) (by omega_arith) (by omega_arith)
  rw [h₈.out, mn, sch₇, k1, k2, t₇, m₇, h₆.out, Proof.Cmac.Stream.blocksAt_eq, sch₅, t₅, m₅, m₄, h₃.out,
    Proof.Cmac.Stream.blocksAt_eq, sch₂, pk, hz]

theorem finishLong_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : Env s₀ C D P W R L) {s : State}
    (hr : Regs s₀ C D P W R L s) (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (.seq longTail (longMac v.callee v.ctr.callee v.ctr.suffix out)) s (FinPost s₀ C D P W R L out s) := by
  have hwW := h.wW
  have hlt := h.lt
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_arith
  refine WP.seq (WP.mono (longTail_wp h hr hL16) fun s₁ h₁ => ?_)
  refine WP.mono (longMac_wp v h h₁.regs hL16 hout h₁.x28) fun s₂ h₂ => ?_
  have f₁ : Frame (finRegions W out) s.mem s₁.mem := h₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have f₂ : Frame (finRegions W out) s₁.mem s₂.mem := h₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨h₂.regs, (Hold2.of fun r hr _ h28 _ => h₁.keep r hr h28).trans h₂.hold, f₁.trans f₂, ?_⟩
  have dC {d n : Nat} (hd : d + n ≤ 512) :
      Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 d) n :=
    Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))) (by omega_arith)
  have sch := dC (d := 0) (n := 16 * (R + 1)) (by omega_arith)
  have k1 := dC (d := 240) (n := 16) (by decide)
  have k2 := dC (d := 256) (n := 16) (by decide)
  rw [k0] at sch
  have pk : Spec.Aes.bytesAt s₁.mem P (16 * kOf L) = Spec.Aes.bytesAt s.mem P (16 * kOf L) :=
    Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.p_w.sub_left (Region.sub_prefix (by omega_arith))).sub_right (h.sW (by decide))) (by omega_arith)
  -- The tail, as the calls read it.
  have hTsplit : L - 16 * kOf L = 16 * jOf L + (L - 16 * kOf L - 16 * jOf L) := by omega_arith
  have tk := Proof.AesSiv.take_bytesAt s₁.mem (W + BitVec.ofNat 64 32) (a := 16 * jOf L)
    (b := L - 16 * kOf L - 16 * jOf L)
  have dr := Proof.AesSiv.drop_bytesAt s₁.mem (W + BitVec.ofNat 64 32) (a := 16 * jOf L)
    (b := L - 16 * kOf L - 16 * jOf L)
  rw [← hTsplit, h₁.tail] at tk dr
  rw [Offset.add_add] at dr
  have hLsplit : L = 16 * kOf L + (L - 16 * kOf L) := by omega_arith
  have pt := Proof.AesSiv.take_bytesAt s.mem P (a := 16 * kOf L) (b := L - 16 * kOf L)
  have pd := Proof.AesSiv.drop_bytesAt s.mem P (a := 16 * kOf L) (b := L - 16 * kOf L)
  rw [← hLsplit] at pt pd
  have hlP : (Spec.Aes.bytesAt s.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
  have hs := long_spec (Spec.Siv.schedCiph s.mem C R) (Spec.Aes.bytesAt s.mem (C + 240) 16)
    (Spec.Aes.bytesAt s.mem (C + 256) 16) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L)
    (Proof.Cmac.bytesAt_length _ _ _) (by rw [hlP]; exact hL16)
  rw [hlP, pt, pd] at hs
  rw [h₂.out, sch, k1, k2, ← dr, ← tk, pk, Spec.Siv.ctxMac, ← hs]
  rfl

end VG.Proof.AesSiv.AArch64
