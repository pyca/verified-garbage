module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PreparedReduction
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RuntimeWord
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Reduce
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Mont.OutsFrame

/-! Initialize the divisor and reuse the complete verified RSA reduction chain. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (num arr S slot)

theorem prepared_reduction {s : State} {base : Addr} {bytes len count x q : Nat}
    (h : RtWs arithmeticLay s base bytes len count) (arrays : 6 ≤ count) (positive : 0 < q)
    (candidate : num s.mem base (kw len) 0 = x) (subgroup : num s.mem base (kw len) 2 = q)
    (bound : 2 * q < 2 ^ (32 * kw len)) :
    WP isa (preparedReduction (kw len)) s fun t =>
      RtWs arithmeticLay t base bytes len count ∧ num t.mem base (kw len) 5 = x + 1 - x % (2 * q) ∧
      num t.mem base (kw len) 0 = 2 * (x / (2 * q)) ∧ Frame [⟨base, bytes⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have header := h.ws.hdr_le
  have fit0 := h.ws.arr_fit (j := 0) (by omega)
  have fit2 := h.ws.arr_fit (j := 2) (by omega)
  have nw := h.ws.workspace.nowrap
  have topEq : divisorTop (kw len) = arr (kw len) 2 + 4 * kw len := rfl
  have topFit : divisorTop (kw len) + 4 ≤ bytes := by rw [topEq]; unfold S at fit2; omega
  unfold preparedReduction
  refine WP.seq (WP.mono (runtime_word (d := reductionOne) (value := 1) h
    (by unfold reductionOne VG.Impl.Rsa.X86.Keys.hdr at *; omega)) fun a ⟨A, ma, OA, KA⟩ => ?_)
  have xa : num a.mem base (kw len) 0 = x := by
    change val32 a.mem base (arr (kw len) 0) (kw len) = x
    rw [OA.val32 (d := arr (kw len) 0) (k := kw len) (.inr (by unfold reductionOne arr VG.Impl.Rsa.X86.Keys.hdr; omega)) (by unfold S at fit0; omega)]
    exact candidate
  have qa : num a.mem base (kw len) 2 = q := by
    change val32 a.mem base (arr (kw len) 2) (kw len) = q
    rw [OA.val32 (d := arr (kw len) 2) (k := kw len) (.inr (by unfold reductionOne arr VG.Impl.Rsa.X86.Keys.hdr; omega)) (by unfold S at fit2; omega)]
    exact subgroup
  have oneA : slot a.mem base reductionOne = 1 := by
    change (a.mem.readW (off base reductionOne) 32).toNat = 1
    rw [ma, Mem.readW_writeW_self32]
    rfl
  refine WP.seq (WP.mono (double_array A (j := 2) (by omega) (by rw [qa]; exact bound))
    fun b ⟨B, FB, doubled, KB⟩ => ?_)
  have xb := (FB.num (j := 0) (by simp) (by simp) (h.ws.fit64 (by omega))).trans xa
  have qb : num b.mem base (kw len) 2 = 2 * q := by rw [doubled, qa]
  have oneB := (FB.slot (e := reductionOne) (by decide) (by simp)).trans oneA
  refine WP.seq (WP.mono (runtime_word (d := divisorTop (kw len)) (value := 0) B topFit)
    fun c ⟨C, mc, OC, KC⟩ => ?_)
  have xc : num c.mem base (kw len) 0 = x := by
    change val32 c.mem base (arr (kw len) 0) (kw len) = x
    rw [OC.val32 (d := arr (kw len) 0) (k := kw len) (.inl (by rw [topEq]; unfold arr S VG.Impl.Rsa.X86.Keys.hdr; omega))
      (by unfold S at fit0; omega)]
    exact xb
  have qc : num c.mem base (kw len) 2 = 2 * q := by
    change val32 c.mem base (arr (kw len) 2) (kw len) = 2 * q
    rw [OC.val32 (d := arr (kw len) 2) (k := kw len) (.inl (by rw [topEq])) (by unfold S at fit2; omega)]
    exact qb
  have top : w32 c.mem base (arr (kw len) 2 + 4 * kw len) = 0 := by
    change (c.mem.readW (off base (arr (kw len) 2 + 4 * kw len)) 32).toNat = 0
    rw [← topEq, mc, Mem.readW_writeW_self32]
    rfl
  have oneC : slot c.mem base reductionOne = 1 := by
    change w32 c.mem base reductionOne = 1
    rw [OC.w32 (d := reductionOne) (.inl (by rw [topEq]; unfold reductionOne arr VG.Impl.Rsa.X86.Keys.hdr; omega))
      (by unfold reductionOne; decide)]
    exact oneB
  refine WP.mono (reduce_candidate C arrays positive xc qc top oneC) fun t ⟨T, p, e, FT, KT⟩ => ?_
  have outsideB := keep_outside h.ws FB (by simp; omega) (by simp)
  have outsideT := keep_outside h.ws FT (by simp; omega) (by simp [VG.Impl.Rsa.X86.Keys.hdr, VG.Impl.Rsa.X86.KeyRt.sCy, VG.Impl.Rsa.X86.KeyRt.sQb])
  have outside : Outside base 0 bytes s.mem t.mem :=
    ((OA.mono (by omega) (by change 144 + 4 ≤ 0 + bytes; unfold VG.Impl.Rsa.X86.Keys.hdr at header; omega)).trans outsideB).trans
      ((OC.mono (by omega) (by omega)).trans outsideT)
  have frame := outside.frameAt (by omega)
  simp only [off, BitVec.add_zero] at frame
  exact ⟨T, p, e, frame, (((KA.mono (by decide)).trans (KB.mono (by decide))).trans (KC.mono (by decide))).trans KT⟩

end VG.Proof.Dsa.X86.Generation
