module

public import VerifiedGarbage.Proof.Rsa.X86.RvProductCore
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
import VerifiedGarbage.Proof.Rsa.X86.RvProductCount
import VerifiedGarbage.Proof.Rsa.X86.RvSetTop
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.TCB.X86.Target

/-! # Setting up and computing the exact exponent product -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys VG.Proof.Bignum.X86

theorem prod_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {e d eLen dLen : Nat}
    (h : KS g s0 A [aN] (AW1 e d) [wZ, wE, wD, wM, wMod] (fun _ => 0) [] s)
    (arg : CallArgument s g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ePos : 0 < eLen) (eBound : eLen ≤ 8 * g.n) (dBound : dLen ≤ 8 * g.n)
    (eFits : e < 2 ^ (8 * eLen)) (dFits : d < 2 ^ (8 * dLen)) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.prod s fun t =>
      KS g s0 A [aN] (AWp g e d) [wM, wMod, wZ] (fun _ => 0) [] t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.prod
  refine WP.seq (WP.block_append (WP.mono (setTop_ok h.rtW (by decide))
    fun u ⟨_, k, value, r⟩ => ?_))
  rw [kw_wid] at k value
  have zero : num s.mem g.B g.W wMod = 0 := by
    rw [h.arrsW wMod (by simp)]; simp [AW1, upd, wMod, wD, wE]
  have low : val32 s.mem g.B (arr g.W wMod) (g.W - 1) = 0 := by
    have expand := val32_succ s.mem g.B (arr g.W wMod) (g.W - 1)
    rw [show g.W - 1 + 1 = g.W by have := h.wsW.wpos; omega] at expand
    change val32 _ _ _ _ = 0 at zero
    omega
  have newValue : num u.mem g.B g.W wMod = mTop g := by
    rw [value, low, Nat.zero_add, ← Nat.pow_add]
    congr 1
  have hu := h.write_W k (by decide) (by simp) (r.mono (by decide)) newValue
    (by simp only [List.mem_singleton]; rintro j rfl; decide) (by simp)
  have frame := h.keepBody k (fun j hj => h.wsW.arr_fit (by simp only [List.mem_singleton] at hj; subst j; decide)) (by simp)
  have argU := arg.keep r (by decide) (frame.mono (by omega) (by have := h.ws.hdr_le; unfold hdr at this; omega))
  refine WP.mono (prodCount_ok argU) fun v ⟨count, mem, rv⟩ => ?_
  exact product_core_ok (hu.of_rest rv (by decide) mem) ePos eBound dBound eFits dFits count

end VG.Proof.Rsa.X86.Recover
