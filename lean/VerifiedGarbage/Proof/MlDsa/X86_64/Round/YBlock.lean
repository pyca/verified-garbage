import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YLane
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLanes

/-!
# ML-DSA on x86-64: the SSE2 code of the AVX2 rounding, on a register

`hbX` and `lbX` compute `hbL` and `lbL` in each doubleword of `xmm0`
(`hbX_ok`, `lbX_ok`), with the constants in `xmm8`, `xmm9`, `xmm10` (and `q`
in `xmm15`).
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Proof.MlDsa.X86_64.Arith (dword_psubd dword_pand dword_psrad caddL caddV dword_caddV qV
  dword_qV)
open VG.Proof.MlKem.X86_64 (XOnly)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (gamma2s)

/-- Each doubleword of `x` is `v`. -/
def Bc (x : BitVec 128) (v : BitVec 32) : Prop := ∀ e < 4, dword x e = v

theorem bc_ofDwords (v : BitVec 32) : Bc (ofDwords v v v v) v := fun e he => by
  rcases cases4 he with rfl | rfl | rfl | rfl <;> simp

/-- The constants of `hbX`. -/
structure HbC (g : Nat) (s : State) : Prop where
  c8 : Bc (s.xmm .xmm8) (BitVec.ofNat 32 127)
  c9 : Bc (s.xmm .xmm9) (BitVec.ofNat 32 (dAdd g))
  c10 : Bc (s.xmm .xmm10) (BitVec.ofNat 32 (dMod g))

theorem dSh_32 : dSh g32 = [10] := rfl
theorem dSh_88 : dSh g88 = [1, 3, 10, 11, 13] := rfl
theorem dShift_32 : dShift g32 = 22 := rfl
theorem dShift_88 : dShift g88 = 24 := rfl

theorem hbX_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (hc : HbC g s) :
    WP isa (.block (hbX g)) s fun s' => (∀ e < 4, dword (s'.xmm .xmm0) e = hbL g (dword (s.xmm .xmm0) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm2] s s' := by
  rcases hg with rfl | rfl <;>
  · simp only [hbX, hfX, mulX, dSh_32, dSh_88, dShift_32, dShift_88, xmov, xb, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    vrun [VG.X86_64.eval_movdqa]
    refine ⟨fun e he => ?_, by xonly⟩
    simp (disch := first | decide | with_reducible assumption) only [dword_pand, dword_psrad, dword_psubd, dword_psrld,
      dword_pslld, dword_paddd, hc.c8 e he, hc.c9 e he, hc.c10 e he, BitVec.toNat_ofNat]
    rfl

/-- `hfX` computes `hbFL` in each doubleword. -/
theorem hfX_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (hc8 : Bc (s.xmm .xmm8) (BitVec.ofNat 32 127))
    (hc9 : Bc (s.xmm .xmm9) (BitVec.ofNat 32 (dAdd g))) :
    WP isa (.block (hfX g)) s fun s' => (∀ e < 4, dword (s'.xmm .xmm0) e = hbFL g (dword (s.xmm .xmm0) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm2] s s' := by
  rcases hg with rfl | rfl <;>
  · simp only [hfX, mulX, dSh_32, dSh_88, dShift_32, dShift_88, xmov, xb, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    vrun [VG.X86_64.eval_movdqa]
    refine ⟨fun e he => ?_, by xonly⟩
    simp (disch := first | decide | with_reducible assumption) only [dword_psrld, dword_pslld, dword_paddd,
      hc8 e he, hc9 e he, BitVec.toNat_ofNat]
    rfl

theorem mul2X_32 : mul2X g32 = [xmov .xmm1 .xmm0, .xop (.shift .pslld .xmm1 19), xmov .xmm2 .xmm0,
    .xop (.shift .pslld .xmm2 9), xb .psubd .xmm1 .xmm2] := rfl

theorem mul2X_88 : mul2X g88 = [xmov .xmm1 .xmm0, .xop (.shift .pslld .xmm1 11)] ++ [13, 14, 15, 17].flatMap fun k =>
    [xmov .xmm2 .xmm0, .xop (.shift .pslld .xmm2 (BitVec.ofNat 8 k)), xb .paddd .xmm1 .xmm2] := rfl

/-- `mul2X` computes `mul2L` in each doubleword. -/
theorem mul2X_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) :
    WP isa (.block (mul2X g)) s fun s' =>
      (∀ e < 4, dword (s'.xmm .xmm1) e = mul2L g (dword (s.xmm .xmm0) e)) ∧ XOnly [.xmm1, .xmm2] s s' := by
  rcases hg with rfl | rfl <;>
  · simp only [mul2X_32, mul2X_88, xmov, xb, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    vrun [VG.X86_64.eval_movdqa]
    refine ⟨fun e he => ?_, by xonly⟩
    simp (disch := first | decide | with_reducible assumption) only [dword_psubd, dword_pslld,
      dword_paddd, BitVec.toNat_ofNat]
    rfl

/-- `lbX` as its parts, `hbX_ok` and `mul2X_ok`: unfolding `lbL` into the doublewords
the whole block computes repeats `hbL` in a term the kernel took 20 s to check. -/
theorem lbX_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (hc : HbC g s) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block (lbX g)) s fun s' => (∀ e < 4, dword (s'.xmm .xmm3) e = lbL g (dword (s.xmm .xmm0) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3] s s' := by
  rw [show lbX g = [xmov .xmm3 .xmm0] ++ (hbX g ++ (mul2X g ++
      ([xb .psubd .xmm3 .xmm1] ++ VG.Impl.MlDsa.X86_64.Arith.vcadd .xmm3 .xmm1))) by
    simp only [lbX, List.cons_append, List.nil_append, List.append_assoc], WP.block_append_iff]
  simp only [xmov, xb]
  vrun [VG.X86_64.eval_movdqa]
  rw [WP.block_append_iff]
  refine WP.mono (hbX_ok hg _ ⟨?_, ?_, ?_⟩) fun s1 ⟨h1, k1⟩ => ?_
  · rw [RegUpd.xmm_setXmm_of_ne _ _ (by decide)]; exact hc.c8
  · rw [RegUpd.xmm_setXmm_of_ne _ _ (by decide)]; exact hc.c9
  · rw [RegUpd.xmm_setXmm_of_ne _ _ (by decide)]; exact hc.c10
  rw [WP.block_append_iff]
  refine WP.mono (mul2X_ok hg s1) fun s2 ⟨h2, k2⟩ => ?_
  have k : XOnly [.xmm0, .xmm1, .xmm2, .xmm3] s s2 :=
    (((XOnly.refl [.xmm3] s).setXmm (List.mem_singleton_self _) _).trans (k1.trans k2)).mono
      (by decide)
  have h3 : s2.xmm .xmm3 = s.xmm .xmm0 := by
    rw [k2.xmm _ (by decide), k1.xmm _ (by decide), RegUpd.xmm_setXmm_self]
  have h15 : s2.xmm .xmm15 = qV := by
    rw [k.xmm _ (by decide), hq]
  simp only [xb, VG.Impl.MlDsa.X86_64.Arith.vcadd, xmov, List.cons_append, List.nil_append]
  vrun [VG.X86_64.eval_movdqa]
  refine ⟨fun e he => ?_, by (repeat (refine XOnly.setXmm (by simp) ?_ _)) <;> exact k⟩
  rw [h15, show ∀ d, XBinOp.paddd.eval d (XBinOp.pand.eval (XShiftOp.psrad.eval d 31) qV) = caddV d from
    fun _ => rfl, dword_caddV _ he, dword_psubd _ _ he, h3, h2 e he, h1 e he, RegUpd.xmm_setXmm_of_ne _ _ (by decide)]
  rfl

end VG.Proof.MlDsa.X86_64.Round
