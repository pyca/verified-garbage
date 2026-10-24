module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Pre
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS signing on PPC64LE: the entry

Untrusted: everything here is checked by Lean. `entry_ok`: from the state
after the frame's push, the saves and the prologue leave `Base` with `n₀` in
`r9` (`Entered`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (frameBytes saved oLr arg save restore)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off fx kR fb fr frameR_eq save_ok Saves stackArgAddr_fb
  stackArgAddr_eq frame_contains allocated_sp allocated_rd allocated_wr allocated_gpr allocated_lr
  allocated_mem)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_ld wp_mov wp_nil wp_lbz wp_lsr wp_or wp_subi)

/-- The stack arguments are in `aR`. -/
theorem in_aR {s : State} {j : Nat} (hj : j < 13) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-- The modulus' first byte. -/
abbrev n0 (s : State) : BitVec 64 := (s.mem (s.gpr .r5)).setWidth 64

/-- After the saves and the prologue. -/
structure Entered (s t : State) : Prop where
  base : Base Ss vS s t
  r9 : t.gpr .r9 = n0 s

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

/-- A load of our stack argument `j` through `r12`, the frame's base. -/
theorem wp_arg {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 13)
    (h12 : t.gpr .r12 = fb s) (hrd : t.rd = s.rd) (hm : Frame [kR s, SC Ss s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : arg j < 2 ^ 15 ∧ arg j % 4 = 0 := by decide) :
    WP isa (.block (.load .d r .r12 (arg j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h12, stackArgAddr_fb]) ?_ (fun t' o e => k t' o ?_) (by decide) ho
  · rw [hrd, P.hrd]; exact ⟨aR s, by simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (P.ka.sub_left kR_sub).symm
      · exact (P.sa.sub_left (sc_sub P)).symm) (by decide)]

theorem n_contains : (nR s).Contains (s.gpr .r5) 1 := by
  have := Offset.contains_base (s.gpr .r5) (d := 0) (n := 1) (k := (s.gpr .r6).toNat) (by have := P.k1; omega)
    (by decide)
  rwa [BitVec.add_zero] at this

theorem entry_ok : WP isa (.block (save ++ prologue)) (allocated frameBytes s) (Entered s) := by
  have hm0 : Frame [kR s] s.mem (allocated frameBytes s).mem := by
    rw [allocated_mem]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (by
      have := frame_contains s (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
  refine save_ok (allocated_sp _ _) (by rw [allocated_wr, frameR_eq]) hm0 (fun r _ => by rw [allocated_gpr])
    (allocated_lr _ _) fun v kv h12 hm₀ hsv hls => ?_
  have hm : Frame [kR s, SC Ss s] s.mem v.mem := hm₀.mono fun r hr => by simp at hr ⊢; exact .inl hr
  have hrd : v.rd = s.rd := kv.rd.trans (allocated_rd _ _)
  have gs : ∀ r ∈ [Reg.r3, .r5, .r6, .r7, .r8, .r9, .r10], v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r (by revert r; decide), allocated_gpr]
  simp only [prologue, smear, List.cons_append, List.nil_append]
  refine wp_arg P (j := 11) (by decide) h12 hrd hm fun v₁ o₁ e₁ => ?_
  refine wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ => wp_mov fun v₅ o₅ e₅ => ?_
  have k₅ : Only [.r14, .r15, .r16, .r17, .r18] v v₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  refine wp_arg P (j := 10) (by decide) (by rw [k₅.get .r12]; exact h12) (k₅.rd.trans hrd) (by rw [k₅.mem]; exact hm)
    fun v₆ o₆ e₆ => ?_
  refine wp_mov fun v₇ o₇ e₇ => wp_mov fun v₈ o₈ e₈ => wp_mov fun v₉ o₉ e₉ => ?_
  have k₉ : Only [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22] v v₉ :=
    (k₅.trans (o₆.trans (o₇.trans (o₈.trans o₉)))).mono
  have g9 : ∀ r ∈ [Reg.r3, .r5, .r6, .r7, .r8, .r9, .r10], v₉.gpr r = s.gpr r := fun r hr => by
    rw [k₉.gpr r (by revert r; decide), gs r hr]
  -- `n₀`.
  have hn := n_contains P
  refine wp_lbz (a := s.gpr .r5) (by rw [g9 .r5 (by decide), BitVec.add_zero])
    (by rw [k₉.rd, hrd, P.hrd]; exact ⟨nR s, by simp, hn⟩) fun v₁₀ o₁₀ e₁₀ => ?_
  have hn0 : v₁₀.gpr .r9 = n0 s := by
    rw [e₁₀, k₉.mem, hm₀ _ fun r hr hc => (P.kn.sub_left kR_sub) _ (List.mem_singleton.mp hr ▸ hc) hn]
  refine wp_lsr fun v₁₁ o₁₁ e₁₁ => wp_lsr fun v₁₂ o₁₂ e₁₂ => wp_or fun v₁₃ o₁₃ e₁₃ => wp_lsr fun v₁₄ o₁₄ e₁₄ =>
    wp_or fun v₁₅ o₁₅ e₁₅ => wp_lsr fun v₁₆ o₁₆ e₁₆ => wp_or fun v₁₇ o₁₇ e₁₇ => wp_subi fun v₁₈ o₁₈ e₁₈ =>
    wp_lsr fun v₁₉ o₁₉ e₁₉ => wp_mov fun w ow ew => wp_nil ?_
  have x13 : v₁₃.gpr .r10 = (n0 s >>> 1) ||| (n0 s >>> 1) >>> 1 := by
    rw [e₁₃, o₁₂.get .r10, e₁₂, e₁₁, hn0]
  have x15 : v₁₅.gpr .r10 = ((n0 s >>> 1) ||| (n0 s >>> 1) >>> 1) |||
      ((n0 s >>> 1) ||| (n0 s >>> 1) >>> 1) >>> 2 := by
    rw [e₁₅, o₁₄.get .r10, e₁₄, x13]
  have x23 : w.gpr .r23 = loS s := by
    rw [ew, e₁₉, e₁₈, e₁₇, o₁₆.get .r10, e₁₆, x15]; rfl
  have kL : Only [.r9, .r10, .r11, .r23] v₉ w :=
    (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans (o₁₇.trans (o₁₈.trans
      (o₁₉.trans ow)))))))))).mono
  have kA : Only [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r9, .r10, .r11, .r23] v w :=
    (k₉.trans kL).mono
  have sv : Saves s w := ⟨by rw [kA.sp, kv.sp, allocated_sp],
    by rw [kA.wr, kv.wr, allocated_wr, frameR_eq],
    fun r hr => by
      rw [kA.gpr r (by revert r; decide), kv.gpr r (by revert r; decide), allocated_gpr],
    by rw [kA.mem]; exact hsv,
    by rw [kA.mem]; exact hls⟩
  refine ⟨⟨sv, kA.rd.trans hrd, ?_, fun r hr => ?_, ?_⟩, ?_⟩
  · rw [kL.get .r14, o₉.get .r14, o₈.get .r14, o₇.get .r14, o₆.get .r14, o₅.get .r14, o₄.get .r14, o₃.get .r14,
      o₂.get .r14]; exact e₁
  · simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [kL.get .r15, o₉.get .r15, o₈.get .r15, o₇.get .r15, o₆.get .r15, o₅.get .r15, o₄.get .r15, o₃.get .r15, e₂,
        o₁.get .r6, gs .r6 (by decide)]; rfl
    · rw [kL.get .r16, o₉.get .r16, o₈.get .r16, o₇.get .r16, o₆.get .r16, o₅.get .r16, o₄.get .r16, e₃,
        o₂.get .r3, o₁.get .r3, gs .r3 (by decide)]; rfl
    · rw [kL.get .r17, o₉.get .r17, o₈.get .r17, o₇.get .r17, o₆.get .r17, o₅.get .r17, e₄,
        o₃.get .r9, o₂.get .r9, o₁.get .r9, gs .r9 (by decide)]; rfl
    · rw [kL.get .r18, o₉.get .r18, o₈.get .r18, o₇.get .r18, o₆.get .r18, e₅,
        o₄.get .r10, o₃.get .r10, o₂.get .r10, o₁.get .r10, gs .r10 (by decide)]; rfl
    · rw [kL.get .r19, o₉.get .r19, o₈.get .r19, o₇.get .r19, e₆]; rfl
    · rw [kL.get .r20, o₉.get .r20, o₈.get .r20, e₇, o₆.get .r5, k₅.get .r5, gs .r5 (by decide)]; rfl
    · rw [kL.get .r21, o₉.get .r21, e₈, o₇.get .r7, o₆.get .r7, k₅.get .r7, gs .r7 (by decide)]; rfl
    · rw [kL.get .r22, e₉, o₈.get .r8, o₇.get .r8, o₆.get .r8, k₅.get .r8, gs .r8 (by decide)]; rfl
    · exact x23
  · rw [kA.mem]; exact hm
  · rw [ow.get .r9, o₁₉.get .r9, o₁₈.get .r9, o₁₇.get .r9, o₁₆.get .r9, o₁₅.get .r9, o₁₄.get .r9, o₁₃.get .r9,
      o₁₂.get .r9, o₁₁.get .r9]; exact hn0

end

end VG.Proof.RsaPss.PPC64LE.Sg
