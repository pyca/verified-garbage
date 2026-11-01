module
public import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
public import VerifiedGarbage.Proof.MlKem.X86_64.VMem
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract

import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: a polynomial of `u16`s as `u32`s (`vunpack`)

`vunpack` (`Impl/MlKem/X86_64/Vec.lean`) stores the 256 words at `rdx` as
`u32`s at `r9`, eight at a time. `widen_ok`: of a polynomial of `u16`s
anywhere the code may read (`PolyIsW 16`), the polynomial of `u32`s
(`PolyIs`), as `vunpack_ok` does for the words of the NTT's working space.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Proof.MlKem VG.Spec.MlKem

theorem s16_of_polyIsW {m : Mem} {p : Addr} {F : Poly} (h : PolyIsW 16 m p F) : S16 m p F :=
  fun i hi => polyIsW_toNat h (by rw [n_eq]; exact hi)

/-- `vunpack`: the polynomial `F` of `u16`s at `src` as `u32`s at `dP`. -/
theorem widen_ok {dP src : Addr} {F : Poly} {s : State} (hS : PolyIsW 16 s.mem src F)
    (h9 : s.gpr .r9 = dP) (hdx : s.gpr .rdx = src) (hwf : pR dP ∈ s.wr)
    (hin : InRegions (s.rd ++ s.wr) src 512) (hd : (pR dP).Disjoint ⟨src, 512⟩) :
    WP isa vunpack s fun s' => PolyIs s'.mem dP F ∧ Frame [pR dP] s.mem s'.mem ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm4 → s'.xmm r = s.xmm r) ∧ Keep [.r9, .rdx, .rcx] s s' ∧
      s'.mxcsr = s.mxcsr := by
  have hS16 := s16_of_polyIsW hS
  refine WP.seq (WP.mono (Q := fun (w : State) => w.xmm .xmm4 = 0 ∧ XOnly [.xmm4] s w)
    (by vrunm; exact ⟨by simp only [XBinOp.eval, BitVec.xor_self]; rfl, by xonly⟩) fun w0 ⟨hz, o0⟩ => ?_)
  refine WP.mono (wp_rcxLoop (N := 32) (by decide) (by decide)
    (fun u w => PolyP w.mem dP F (8 * u) ∧ w.gpr .r9 = coeffAddr dP (8 * u) ∧
      w.gpr .rdx = wAddr src (8 * u) ∧ Frame [pR dP] s.mem w.mem ∧ w.xmm .xmm4 = 0 ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm4 → w.xmm r = s.xmm r) ∧ Keep [.r9, .rdx, .rcx] s w ∧
      w.mxcsr = s.mxcsr)
    (fun w o hcx => ⟨fun _ h => absurd h (by bdd_omega),
      by rw [o.keep.gpr (by decide), o0.gpr, h9, coeffAddr]; simp,
      by rw [o.keep.gpr (by decide), o0.gpr, hdx, wAddr]; simp, by rw [o.mem, o0.mem]; exact Frame.refl _ _,
      by rw [o.xmm, hz], fun r h0 h1 h4 => by rw [o.xmm, o0.xmm r (by simp [h4])],
      Keep.trans (⟨fun r _ => by rw [o0.gpr], o0.rd, o0.wr⟩ : Keep [] s w0) (o.keep) |>.mono (by simp),
      by rw [o.mxcsr, o0.mxcsr]⟩)
    (fun u hu w ⟨hP, h9', hdx', hf, hz', hx', hk', hm'⟩ => ?_))
    fun w ⟨hP, _, _, hf, _, hx', hk', hm'⟩ => ⟨polyIs_of_toNat fun i hi => hP i (by rw [n_eq] at hi; omega),
      hf, hx', hk', hm'⟩
  have hS' : S16 w.mem src F := hS16.frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.symm
  have hwf' : pR dP ∈ w.wr := by rw [hk'.2.2]; exact hwf
  have r0 : InRegions (w.rd ++ w.wr) (wAddr src (8 * u)) 16 := by
    rw [hk'.2.1, hk'.2.2, wAddr]; exact CallLay.inRegions_sub hin (by bdd_omega) (by bdd_omega)
  have w0 : InRegions w.wr (coeffAddr dP (8 * u)) 16 := ⟨_, hwf', polyR_contains dP (by bdd_omega)⟩
  have w1 : InRegions w.wr (coeffAddr dP (8 * u + 4)) 16 := ⟨_, hwf', polyR_contains dP (by bdd_omega)⟩
  have a1 : coeffAddr dP (8 * u) + BitVec.ofNat 64 16 = coeffAddr dP (8 * u + 4) := coeffAddr_off _ _ 4
  have ll := lanes_load hS' (j := 8 * u) (by bdd_omega)
  vrunm [h9', hdx', r0, w0, w1, a1, sx32, hz']
  refine ⟨fun j hj => ?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_off,
      Nat.mul_succ],
    by rw [show (16 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl, wAddr_add, Nat.mul_succ], ?_, ?_, ?_, ?_⟩
  · rw [coeffAt_write128 _ _ (by bdd_omega) _ (by bdd_omega), coeffAt_write128 _ _ (by bdd_omega) _ (by bdd_omega)]
    split
    · rw [dword_punpckhwd0 _ (by bdd_omega), word_movdqa, ll _ (by bdd_omega)]; dsimp only
      rw [show 8 * u + (4 + (j - (8 * u + 4))) = j by bdd_omega]
    · split
      · rw [dword_punpcklwd0 _ (by bdd_omega), ll _ (by bdd_omega)]; dsimp only
        rw [show 8 * u + (j - 8 * u) = j by bdd_omega]
      · exact hP j (by bdd_omega)
  · exact hf.trans (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (polyR_contains dP (by bdd_omega))).writeW
      (List.mem_singleton_self _) _ (polyR_contains dP (by bdd_omega)))
  · intro r h0 h1 h4
    simp only [h0, h1, ite_false]
    exact hx' r h0 h1 h4
  · refine ⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hk'.2.1,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hk'.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
    exact hk'.gpr (by simp [hr])
  · exact hm'

end VG.Proof.MlKem.X86_64
