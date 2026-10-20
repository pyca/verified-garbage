module

public import VerifiedGarbage.Proof.Rsa.X86.RvAddressTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvPair
import VerifiedGarbage.Proof.Rsa.X86.RvProductCount
import VerifiedGarbage.Proof.Rsa.X86.RvSetTop
import VerifiedGarbage.Proof.Rsa.X86.MulModTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Rsa.X86.RvRestFacts

/-! # The exponent product uses the public exponent's byte length -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem prodSet_count_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {live liveW ls : List Nat}
    {eLen : Nat} (h : KS g s0 A live AW liveW V ls s)
    (arg : CallArgument s g.B g.Z 7 (BitVec.ofNat 32 eLen)) :
    WP isa (.block (prodSet g.n)) s fun t => t.gpr .esi = BitVec.ofNat 32 (8 * eLen) ∧
      Keeps opRegs s t := by
  unfold prodSet
  refine WP.block_append (WP.mono (setTop_ok h.wsW (j := wMod) (by decide))
    fun u ⟨_, keep, _, rest⟩ => ?_)
  have frame := h.keepBody keep (fun j hj => h.wsW.arr_fit
    (by simp only [List.mem_singleton] at hj; subst j; decide)) (by simp)
  have argU := arg.keep rest (by decide) (frame.mono (by omega)
    (by have := h.ws.hdr_le; unfold VG.Impl.Rsa.X86.Keys.hdr at this; omega))
  refine WP.mono (prodCount_ok argU) fun t ⟨count, _, rt⟩ => ?_
  exact ⟨count, (rest.mono (by decide)).trans (rt.mono (by decide))⟩

theorem prodSet_address (n : Nat) : AddressPublic (.block (prodSet n)) := by
  let reference := Code.erase (.block (prodSet 1))
  let hint := VG.Taint.hintOf taint argumentTaint reference
  let out := (VG.Taint.check taint argumentTaint reference hint).getD argumentTaint
  refine ⟨hint, out, ?_, by decide +kernel⟩
  exact (check_of_erase_eq (.block (prodSet n)) reference argumentTaint hint rfl rfl rfl).trans (by rfl)

theorem prod_relCT (g : CallGeometry) (s0 t0 : State)
    (A B AW BW V W : Nat → Nat) (al bl aw bw sl tl : List Nat) :
    RelCT isa (fun s t => Pair g s t ∧
      KS g.toGeo s0 A al AW aw V sl s ∧ KS g.toGeo t0 B bl BW bw W tl t)
      (prod g.n) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  intro s t tr ur sf tf ⟨pair, hs, ht⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := ((prodSet_address g.n).trace _ _ _ _ _ _ pair.agree e1 f1).1
      have argS : CallArgument s g.B g.Z 7 (BitVec.ofNat 32 (g.args 7).toNat) := by
        simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using pair.left.arguments 7 (by decide)
      have argT : CallArgument t g.B g.Z 7 (BitVec.ofNat 32 (g.args 7).toNat) := by
        simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using pair.right.arguments 7 (by decide)
      obtain ⟨cs, ks⟩ := wp_result (prodSet_count_ok hs argS) e1
      obtain ⟨ct, kt⟩ := wp_result (prodSet_count_ok ht argT) f1
      have agree : VG.X86.Taint.Agree (workspaceTaint true) u v := by
        apply agree_regs (rs := [.edi, .esi])
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (ks.1 _ (by decide)).trans ((pair.workspace.rf.1 _ (by decide)).trans (kt.1 _ (by decide)).symm)
        · exact cs.trans ct.symm
      obtain ⟨hint, out, checked, kept⟩ := mulMod_public (wide g.n) wZ wE wD wM wMod wT
      obtain ⟨eq2, final⟩ := VG.Taint.check_sound checked agree e2 f2
      have common := taint.le_sound kept final
      exact ⟨by rw [eq1, eq2], taint.le_sound (by decide) common⟩

end VG.Proof.Rsa.X86.Recover
