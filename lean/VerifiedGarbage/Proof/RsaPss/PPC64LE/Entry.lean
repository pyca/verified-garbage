module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Pre
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base

/-!
# RSASSA-PSS verification on PPC64LE: the entry

Untrusted: everything here is checked by Lean. `entry_ok`: from the state
after the frame's push, the saves and the prologue leave `Base` with `e`,
`e_len`, the signature and `scratch_len` in `r24`–`r27` and `n₀` in `r9`
(`Entered`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (frameBytes saved oLr arg oEm oSt oDig oW oRsa copyLoop zeroLoop mgfXor save restore)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off fx kR fb fr frameR_eq save_ok Saves stackArgAddr_fb
  stackArgAddr_eq frame_contains allocated_sp allocated_rd allocated_wr allocated_gpr allocated_lr
  allocated_mem)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_ld wp_mov wp_nil wp_lsrw wp_lbz wp_lsr wp_or wp_subi wp_li
  wp_sub wp_and)

/-- The stack arguments are in `aR`. -/
theorem in_aR {s : State} {j : Nat} (hj : j < 5) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-- After the saves and the prologue. -/
structure Entered (D : Nat) (s t : State) : Prop where
  base : Base Sp (vP D) s t
  r24 : t.gpr .r24 = s.gpr .r5
  r25 : t.gpr .r25 = s.gpr .r6
  r26 : t.gpr .r26 = s.gpr .r8
  r27 : t.gpr .r27 = stackArg s 2
  r9 : t.gpr .r9 = n0 s

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

/-- A load of our stack argument `j` through `r12`, the frame's base. -/
theorem wp_arg {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 5)
    (h12 : t.gpr .r12 = fb s) (hrd : t.rd = s.rd) (hm : Frame [kR s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : arg j < 2 ^ 15 ∧ arg j % 4 = 0 := by decide) :
    WP isa (.block (.load .d r .r12 (arg j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h12, stackArgAddr_fb]) ?_ (fun t' o e => k t' o ?_) (by decide) ho
  · rw [hrd, P.hrd]; exact ⟨aR s, by simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact P.ka.symm) (by decide)]

theorem entry_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD64 : D ≤ 64) :
    WP isa (.block (save ++ prologue H)) (allocated frameBytes s) (Entered D s) := by
  have hm0 : Frame [kR s] s.mem (allocated frameBytes s).mem := by
    rw [allocated_mem]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (by
      have := frame_contains s (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
  refine save_ok (allocated_sp _ _) (by rw [allocated_wr, frameR_eq]) hm0 (fun r _ => by rw [allocated_gpr])
    (allocated_lr _ _) fun v kv h12 hm hsv hls => ?_
  have hrd : v.rd = s.rd := kv.rd.trans (allocated_rd _ _)
  have gs : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r10], v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r (by revert r; decide), allocated_gpr]
  simp only [Impl.RsaPss.PPC64LE.prologue]
  -- The stack arguments.
  refine wp_arg P (j := 0) (by decide) h12 hrd hm fun v₁ o₁ e₁ => wp_lsrw fun v₂ o₂ e₂ => ?_
  have k₂ : Only [.r20] v v₂ := (o₁.trans o₂).mono
  refine wp_arg P (j := 1) (by decide) (by rw [k₂.get .r12]; exact h12) (k₂.rd.trans hrd) (by rw [k₂.mem]; exact hm)
    fun v₃ o₃ e₃ => ?_
  refine wp_arg P (j := 2) (by decide) (by rw [o₃.get .r12, k₂.get .r12]; exact h12) (o₃.rd.trans (k₂.rd.trans hrd))
    (by rw [o₃.mem, k₂.mem]; exact hm) fun v₄ o₄ e₄ => ?_
  have k₄ : Only [.r20, .r14, .r27] v v₄ := (k₂.trans (o₃.trans o₄)).mono
  refine wp_arg P (j := 3) (by decide) (by rw [k₄.get .r12]; exact h12) (k₄.rd.trans hrd) (by rw [k₄.mem]; exact hm)
    fun v₅ o₅ e₅ => ?_
  refine wp_arg P (j := 4) (by decide) (by rw [o₅.get .r12, k₄.get .r12]; exact h12) (o₅.rd.trans (k₄.rd.trans hrd))
    (by rw [o₅.mem, k₄.mem]; exact hm) fun v₆ o₆ e₆ => ?_
  have k₆ : Only [.r20, .r14, .r27, .r22, .r23] v v₆ := (k₄.trans (o₅.trans o₆)).mono
  -- The moves.
  refine wp_mov fun v₇ o₇ e₇ => wp_mov fun v₈ o₈ e₈ => wp_mov fun v₉ o₉ e₉ => wp_mov fun v₁₀ o₁₀ e₁₀ =>
    wp_mov fun v₁₁ o₁₁ e₁₁ => wp_mov fun v₁₂ o₁₂ e₁₂ => ?_
  have k₁₂ : Only [.r15, .r16, .r19, .r24, .r25, .r26] v₆ v₁₂ :=
    (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))))).mono
  have g12 : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r10], v₆.gpr r = s.gpr r := fun r hr => by
    rw [k₆.gpr r (by revert r; decide), gs r hr]
  -- `n₀`.
  have hn : (nR s).Contains (s.gpr .r3) 1 := by
    have := Offset.contains_base (s.gpr .r3) (d := 0) (n := 1) (k := (s.gpr .r4).toNat) (by have := P.k1; omega)
      (by decide)
    rwa [BitVec.add_zero] at this
  refine wp_lbz (a := s.gpr .r3) (by rw [k₁₂.get .r3, g12 .r3 (by decide), BitVec.add_zero])
    (by rw [k₁₂.rd, k₆.rd, hrd, P.hrd]; exact ⟨nR s, by simp, hn⟩) fun v₁₃ o₁₃ e₁₃ => ?_
  have hn0 : v₁₃.gpr .r9 = n0 s := by
    rw [e₁₃, k₁₂.mem, k₆.mem, hm _ fun r hr hc => P.kn _ (List.mem_singleton.mp hr ▸ hc) hn]; rfl
  refine wp_lsr fun v₁₄ o₁₄ e₁₄ => wp_lsr fun v₁₅ o₁₅ e₁₅ => wp_or fun v₁₆ o₁₆ e₁₆ => wp_lsr fun v₁₇ o₁₇ e₁₇ =>
    wp_or fun v₁₈ o₁₈ e₁₈ => wp_lsr fun v₁₉ o₁₉ e₁₉ => wp_or fun v₂₀ o₂₀ e₂₀ => wp_subi fun v₂₁ o₂₁ e₂₁ =>
    wp_lsr fun v₂₂ o₂₂ e₂₂ => wp_li (by decide) fun v₂₃ o₂₃ e₂₃ => wp_sub fun v₂₄ o₂₄ e₂₄ =>
    wp_li (by decide) fun v₂₅ o₂₅ e₂₅ => wp_and fun v₂₆ o₂₆ e₂₆ => wp_or fun v₂₇ o₂₇ e₂₇ =>
    wp_sub fun v₂₈ o₂₈ e₂₈ => wp_subi (h := by omega) fun w ow ew => wp_nil ?_
  have x16 : v₁₆.gpr .r10 = (n0 s >>> 1) ||| (n0 s >>> 1) >>> 1 := by
    rw [e₁₆, o₁₅.get .r10, e₁₅, e₁₄, hn0]
  have x18 : v₁₈.gpr .r10 = ((n0 s >>> 1) ||| (n0 s >>> 1) >>> 1) |||
      ((n0 s >>> 1) ||| (n0 s >>> 1) >>> 1) >>> 2 := by
    rw [e₁₈, o₁₇.get .r10, e₁₇, x16]
  have x20 : v₂₀.gpr .r10 = smear s := by
    rw [e₂₀, o₁₉.get .r10, e₁₉, x18]; rfl
  have x22 : v₂₂.gpr .r17 = lo s := by rw [e₂₂, e₂₁, x20]; rfl
  have x27 : v₂₇.gpr .r18 = cm s := by
    rw [e₂₇, o₂₆.get .r10, o₂₅.get .r10, o₂₄.get .r10, o₂₃.get .r10, o₂₂.get .r10, o₂₁.get .r10, x20, e₂₆,
      o₂₅.get .r11, e₂₄, e₂₃, e₂₅, o₂₃.get .r17, x22]; rfl
  have k₁₃ : Only [.r9] v₁₂ v₁₃ := o₁₃
  have kL : Only [.r10, .r11, .r17, .r8, .r18, .r21] v₁₃ w :=
    (o₁₄.trans (o₁₅.trans (o₁₆.trans (o₁₇.trans (o₁₈.trans (o₁₉.trans (o₂₀.trans (o₂₁.trans (o₂₂.trans
      (o₂₃.trans (o₂₄.trans (o₂₅.trans (o₂₆.trans (o₂₇.trans (o₂₈.trans ow))))))))))))))).mono
  have kA : Only [.r20, .r14, .r27, .r22, .r23, .r15, .r16, .r19, .r24, .r25, .r26, .r9, .r10, .r11, .r17, .r8, .r18,
      .r21] v w := (k₆.trans (k₁₂.trans (k₁₃.trans kL))).mono
  have sv : Saves s w := ⟨by rw [kA.sp, kv.sp, allocated_sp],
    by rw [kA.wr, kv.wr, allocated_wr, frameR_eq],
    fun r hr => by
      rw [kA.gpr r (by revert r; decide), kv.gpr r (by revert r; decide), allocated_gpr],
    by rw [kA.mem]; exact hsv,
    by rw [kA.mem]; exact hls⟩
  have lw : w.gpr .r17 = lo s := by
    rw [ow.get .r17, o₂₈.get .r17, o₂₇.get .r17, o₂₆.get .r17, o₂₅.get .r17, o₂₄.get .r17, o₂₃.get .r17, x22]
  have m15 : v₁₂.gpr .r15 = s.gpr .r4 := by
    rw [o₁₂.get .r15, o₁₁.get .r15, o₁₀.get .r15, o₉.get .r15, o₈.get .r15, e₇,
      g12 .r4 (by decide)]
  refine ⟨⟨sv, kA.rd.trans hrd, ?_, fun r hr => ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 2
  · rw [kA.mem]; exact hm.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  · rw [kL.get .r24, k₁₃.get .r24, o₁₂.get .r24, o₁₁.get .r24, e₁₀, o₉.get .r5, o₈.get .r5, o₇.get .r5, g12 .r5 (by decide)]
  · rw [kL.get .r25, k₁₃.get .r25, o₁₂.get .r25, e₁₁, o₁₀.get .r6, o₉.get .r6, o₈.get .r6, o₇.get .r6, g12 .r6 (by decide)]
  · rw [kL.get .r26, k₁₃.get .r26, e₁₂, o₁₁.get .r8, o₁₀.get .r8, o₉.get .r8, o₈.get .r8, o₇.get .r8, g12 .r8 (by decide)]
  · rw [kL.get .r27, k₁₃.get .r27, k₁₂.get .r27, o₆.get .r27, o₅.get .r27]; exact e₄
  · rw [kL.get .r9]; exact hn0
  · rw [kL.get .r14, k₁₃.get .r14, k₁₂.get .r14, o₆.get .r14, o₅.get .r14, o₄.get .r14]; exact e₃
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vP]
  · rw [kL.get .r15, k₁₃.get .r15, m15]
  · rw [kL.get .r16, k₁₃.get .r16, o₁₂.get .r16, o₁₁.get .r16, o₁₀.get .r16, o₉.get .r16, e₈, o₇.get .r7,
      g12 .r7 (by decide)]
  · exact lw
  · rw [ow.get .r18, o₂₈.get .r18, x27]
  · rw [kL.get .r19, k₁₃.get .r19, o₁₂.get .r19, o₁₁.get .r19, o₁₀.get .r19, e₉, o₈.get .r10, o₇.get .r10,
      g12 .r10 (by decide)]
  · rw [kL.get .r20, k₁₃.get .r20, k₁₂.get .r20, o₆.get .r20, o₅.get .r20, o₄.get .r20, o₃.get .r20, e₂, e₁]; rfl
  · rw [ew, e₂₈, o₂₇.get .r15, o₂₆.get .r15, o₂₅.get .r15, o₂₄.get .r15, o₂₃.get .r15, o₂₂.get .r15, o₂₁.get .r15,
      o₂₀.get .r15, o₁₉.get .r15, o₁₈.get .r15, o₁₇.get .r15, o₁₆.get .r15, o₁₅.get .r15, o₁₄.get .r15, k₁₃.get .r15,
      m15, o₂₇.get .r17, o₂₆.get .r17, o₂₅.get .r17, o₂₄.get .r17, o₂₃.get .r17, x22, hD]; rfl
  · rw [kL.get .r22, k₁₃.get .r22, k₁₂.get .r22, o₆.get .r22]; exact e₅
  · rw [kL.get .r23, k₁₃.get .r23, k₁₂.get .r23]; exact e₆

end

end VG.Proof.RsaPss.PPC64LE
