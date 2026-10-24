module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Pre
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP encryption on PPC64LE: the entry

Untrusted: everything here is checked by Lean. `entry_ok`: from the state
after the frame's push, the saves and the prologue leave `Base` with `msg`,
`msg_len` and `seed` in `r9`, `r10` and `r11` (`Entered`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_ld wp_mov wp_nil)

theorem allocated_sp (n : Nat) (s : State) : (allocated n s).sp = s.sp - BitVec.ofNat 64 n := rfl
theorem allocated_rd (n : Nat) (s : State) : (allocated n s).rd = s.rd := rfl
theorem allocated_wr (n : Nat) (s : State) : (allocated n s).wr = frameR n s :: s.wr := rfl
theorem allocated_gpr (n : Nat) (s : State) : (allocated n s).gpr = s.gpr := rfl
theorem allocated_lr (n : Nat) (s : State) : (allocated n s).lr = s.lr := rfl
theorem allocated_mem (n : Nat) (s : State) :
    (allocated n s).mem = s.mem.write (s.sp - BitVec.ofNat 64 n) 8 s.sp := rfl

theorem freed_lr (n : Nat) (s : State) : (freed n s).lr = s.lr := rfl
theorem freed_gpr (n : Nat) (s : State) : (freed n s).gpr = s.gpr := rfl
theorem freed_mem (n : Nat) (s : State) : (freed n s).mem = s.mem := rfl

/-- The stack arguments are in `aR`. -/
theorem in_aR {s : State} {j : Nat} (hj : j < 7) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-- After the saves and the prologue. -/
structure Entered (s t : State) : Prop where
  base : Base S vO s t
  r9 : t.gpr .r9 = stackArg s 0
  r10 : t.gpr .r10 = stackArg s 1
  r11 : t.gpr .r11 = stackArg s 2

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

/-- A load of our stack argument `j` through `r12`, the frame's base. -/
theorem wp_arg {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 7)
    (h12 : t.gpr .r12 = fb s) (hrd : t.rd = s.rd) (hm : Frame [kR s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : arg j < 2 ^ 15 ∧ arg j % 4 = 0 := by decide) :
    WP isa (.block (.load .d r .r12 (arg j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h12, stackArgAddr_fb]) ?_ (fun t' o e => k t' o ?_) (by decide) ho
  · rw [hrd, P.hrd]; exact ⟨aR s, by simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact P.ka.symm) (by decide)]

theorem entry_ok : WP isa (.block (save ++ prologue)) (allocated frameBytes s) (Entered s) := by
  have hm0 : Frame [kR s] s.mem (allocated frameBytes s).mem := by
    rw [allocated_mem]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (by
      have := frame_contains s (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
  refine save_ok (allocated_sp _ _) (by rw [allocated_wr, frameR_eq]) hm0 (fun r _ => by rw [allocated_gpr])
    (allocated_lr _ _) fun v kv h12 hm hsv hls => ?_
  have hrd : v.rd = s.rd := kv.rd.trans (allocated_rd _ _)
  simp only [prologue]
  refine wp_arg P (j := 3) (by decide) h12 hrd hm fun v₁ o₁ e₁ => ?_
  refine wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ => wp_mov fun v₅ o₅ e₅ =>
    wp_mov fun v₆ o₆ e₆ => wp_mov fun v₇ o₇ e₇ => ?_
  have k₇ : Only [.r14, .r15, .r16, .r17, .r18, .r19, .r20] v v₇ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono
  have g7 : v₇.gpr .r12 = fb s := by rw [k₇.get .r12]; exact h12
  have r7 : v₇.rd = s.rd := k₇.rd.trans hrd
  have m7 : Frame [kR s] s.mem v₇.mem := by rw [k₇.mem]; exact hm
  refine wp_arg P (j := 5) (by decide) g7 r7 m7 fun v₈ o₈ e₈ => ?_
  have g8 : v₈.gpr .r12 = fb s := by rw [o₈.get .r12]; exact g7
  have r8 : v₈.rd = s.rd := o₈.rd.trans r7
  have m8 : Frame [kR s] s.mem v₈.mem := by rw [o₈.mem]; exact m7
  refine wp_arg P (j := 6) (by decide) g8 r8 m8 fun v₉ o₉ e₉ => ?_
  have g9 : v₉.gpr .r12 = fb s := by rw [o₉.get .r12]; exact g8
  have r9 : v₉.rd = s.rd := o₉.rd.trans r8
  have m9 : Frame [kR s] s.mem v₉.mem := by rw [o₉.mem]; exact m8
  refine wp_arg P (j := 4) (by decide) g9 r9 m9 fun v₁₀ o₁₀ e₁₀ => ?_
  have g10 : v₁₀.gpr .r12 = fb s := by rw [o₁₀.get .r12]; exact g9
  have r10 : v₁₀.rd = s.rd := o₁₀.rd.trans r9
  have m10 : Frame [kR s] s.mem v₁₀.mem := by rw [o₁₀.mem]; exact m9
  refine wp_arg P (j := 0) (by decide) g10 r10 m10 fun v₁₁ o₁₁ e₁₁ => ?_
  have g11 : v₁₁.gpr .r12 = fb s := by rw [o₁₁.get .r12]; exact g10
  have r11 : v₁₁.rd = s.rd := o₁₁.rd.trans r10
  have m11 : Frame [kR s] s.mem v₁₁.mem := by rw [o₁₁.mem]; exact m10
  refine wp_arg P (j := 1) (by decide) g11 r11 m11 fun v₁₂ o₁₂ e₁₂ => ?_
  have g12 : v₁₂.gpr .r12 = fb s := by rw [o₁₂.get .r12]; exact g11
  have r12 : v₁₂.rd = s.rd := o₁₂.rd.trans r11
  have m12 : Frame [kR s] s.mem v₁₂.mem := by rw [o₁₂.mem]; exact m11
  refine wp_arg P (j := 2) (by decide) g12 r12 m12 fun w ow ew => wp_nil ?_
  have kw : Only [.r23, .r9, .r10, .r11] v₁₀ w := (o₁₁.trans (o₁₂.trans ow)).mono
  have k10 : Only [.r21, .r22, .r23] v₇ v₁₀ := (o₈.trans (o₉.trans o₁₀)).mono
  have gs : ∀ r ∈ [Reg.r3, .r6, .r7, .r8, .r9, .r10], v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r (by revert r; decide), allocated_gpr]
  have sv : Saves s w := ⟨by rw [ow.sp, o₁₂.sp, o₁₁.sp, k10.sp, k₇.sp, kv.sp, allocated_sp],
    by rw [ow.wr, o₁₂.wr, o₁₁.wr, k10.wr, k₇.wr, kv.wr, allocated_wr, frameR_eq],
    fun r hr => by
      rw [ow.gpr r (by revert r; decide), o₁₂.gpr r (by revert r; decide), o₁₁.gpr r (by revert r; decide),
        k10.gpr r (by revert r; decide), k₇.gpr r (by revert r; decide), kv.gpr r (by revert r; decide),
        allocated_gpr],
    by rw [ow.mem, o₁₂.mem, o₁₁.mem, k10.mem, k₇.mem]; exact hsv,
    by rw [ow.mem, o₁₂.mem, o₁₁.mem, k10.mem, k₇.mem]; exact hls⟩
  refine ⟨⟨sv, ow.rd.trans r12, ?_, fun r hr => ?_, ?_⟩, ?_, ?_, ?_⟩
  rotate_left 2
  · rw [ow.mem, o₁₂.mem, o₁₁.mem]
    exact m10.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  · rw [ow.get .r9, o₁₂.get .r9]; exact e₁₁
  · rw [ow.get .r10]; exact e₁₂
  · exact ew
  · rw [kw.get .r14, k10.get .r14, o₇.get .r14, o₆.get .r14, o₅.get .r14, o₄.get .r14, o₃.get .r14,
      o₂.get .r14]; exact e₁
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vO]
  · rw [kw.get .r15, k10.get .r15, o₇.get .r15, o₆.get .r15, o₅.get .r15, o₄.get .r15, o₃.get .r15, e₂,
      o₁.get .r6, gs .r6 (by decide)]
  · rw [kw.get .r16, k10.get .r16, o₇.get .r16, o₆.get .r16, o₅.get .r16, o₄.get .r16, e₃, o₂.get .r3,
      o₁.get .r3, gs .r3 (by decide)]
  · rw [kw.get .r17, k10.get .r17, o₇.get .r17, o₆.get .r17, o₅.get .r17, e₄, o₃.get .r7, o₂.get .r7,
      o₁.get .r7, gs .r7 (by decide)]
  · rw [kw.get .r18, k10.get .r18, o₇.get .r18, o₆.get .r18, e₅, o₄.get .r8, o₃.get .r8, o₂.get .r8,
      o₁.get .r8, gs .r8 (by decide)]
  · rw [kw.get .r19, k10.get .r19, o₇.get .r19, e₆, o₅.get .r9, o₄.get .r9, o₃.get .r9, o₂.get .r9,
      o₁.get .r9, gs .r9 (by decide)]
  · rw [kw.get .r20, k10.get .r20, e₇, o₆.get .r10, o₅.get .r10, o₄.get .r10, o₃.get .r10, o₂.get .r10,
      o₁.get .r10, gs .r10 (by decide)]
  · rw [kw.get .r21, o₁₀.get .r21, o₉.get .r21, e₈]
  · rw [kw.get .r22, o₁₀.get .r22, e₉]
  · rw [ow.get .r23, o₁₂.get .r23, o₁₁.get .r23]; exact e₁₀

end

end VG.Proof.RsaOaep.PPC64LE
