import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr

/-!
# X25519 on x86-64: `b + a24 · a` with BMI2 and ADX, and `adx_ok`

`a24addX o b a`: `r8–r12 = [b] + a24 · [a]` (as a row of a product, added to
`[b]`), then `r12` folded as 38; and the field multiplications `adx` satisfy
`FieldOk`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem a24addX_eq (o b a : Nat) : a24addX o b a = ([.mov32 .rdx (.imm a24)] : List Instr) ++
    (loads b .r8 .r9 .r10 .r11 ++ (maddRow a .r8 .r9 .r10 .r11 .r12 ++
      (([.mov32 .rdx (.imm 38)] : List Instr) ++ (([.mulx .rcx .rax (.reg .r12)] : List Instr) ++
        (carry38 ++ store4 o))))) := by
  simp only [a24addX, maddRow, List.append_assoc]; rfl

/-- `[o] = [b] + a24 · [a]`. -/
theorem a24addX_ok {s : State} {base : Addr} (hs : Scr s base) {o b a : Nat} (ho : Slot o)
    (hb : Slot b) (ha : Slot a) :
    WP isa (.block (a24addX o b a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base b + Spec.X25519.a24 * F s.mem base a := by
  rw [a24addX_eq, WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s a24) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads4_ok hs1 hb) fun s2 ⟨l2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (maddRow_ok hs2 (by omega) (by decide)) fun s3 ⟨e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s3 38) fun s4 ⟨d4, _, _, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s4 rfl (noImm_reg _) (by decide)) fun s5 ⟨e5, _, _, k5⟩ => ?_
  have M1 : s1.mem = s.mem := k1.2.1
  have M2 : s2.mem = s.mem := k2.2.1.trans M1
  rw [M1] at l2
  rw [M2, l2, k2.1 .rdx (by decide), d1, show (a24 : BitVec 32).toNat = 121665 from rfl] at e3
  rw [show (s4.gpr .rdx).toNat = 38 from d4, k4.1 .r12 (by decide)] at e5
  -- `r8–r11 + 2²⁵⁶ r12 = [b] + a24 · [a]`, so `r12 ≤ a24` and `rax = 38 r12`.
  have h12 : (s3.gpr .r12).toNat < 121666 := by
    have hA := fe_lt s.mem base a
    have hB := fe_lt s.mem base b
    omega_using [e3, hA, hB]
  have hax : (s5.gpr .rax).toNat = 38 * (s3.gpr .r12).toNat := by
    have := (s5.gpr .rax).isLt
    omega_using [e5, h12, this]
  have hs5 := (hs3.of_keeps k4 (by decide)).of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carry38_ok s5 (by omega_using [hax, h12])) fun s6 ⟨e6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  refine WP.mono (store4_ok hs6 ho) fun s7 ⟨m7, g7, rd7, wr7⟩ => ?_
  have K : Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s6 :=
    (((((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide))).trans (k5.mono (by decide))).trans (k6.mono (by decide))
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g7, K.1 r (by simp [hr])]
  · rw [rd7, K.2.2.1]
  · rw [wr7, K.2.2.2]
  · rw [m7, K.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_addA24
    rw [m7, fe_st4 _ _ (by omega), e6, hax, k5.1 .r8 (by decide), k5.1 .r9 (by decide),
      k5.1 .r10 (by decide), k5.1 .r11 (by decide), k4.1 .r8 (by decide), k4.1 .r9 (by decide),
      k4.1 .r10 (by decide), k4.1 .r11 (by decide), ← fold256, e3]

/-- The field multiplications with BMI2 and ADX. -/
theorem adx_ok : FieldOk adx where
  mul hs _ _ _ ho ha hb := mulX_ok hs ho ha hb
  sqr hs _ _ ho ha := sqrX_ok hs ho ha
  a24add hs _ _ _ ho hb ha := a24addX_ok hs ho hb ha
  mul2 hs _ _ _ ho ha hb := mul2X_ok hs ho ha hb
  sqr2 hs _ _ ho ha := sqr2X_ok hs ho ha
  mulB hs _ _ _ ho ha hb := mulXBnd_ok hs ho ha hb
  sqrB hs _ _ ho ha := sqrXBnd_ok hs ho ha

end VG.Proof.X25519.X86_64
