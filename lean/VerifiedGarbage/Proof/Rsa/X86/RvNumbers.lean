module

public import VerifiedGarbage.Proof.Rsa.X86.RvLoads

import VerifiedGarbage.Proof.Rsa.X86.RvArguments
import VerifiedGarbage.Proof.Rsa.X86.RvSubWrap
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Bignum.X86.PublicCall
import VerifiedGarbage.Impl.Rsa.X86.Recover
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Rsa.X86.RvProductCore
import VerifiedGarbage.Proof.Rsa.X86.RvSetTop
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.KeyBits32
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.PlainSimp
/-! # Exact exponent product and the positive-even precondition for recovery -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvProductCount.lean`, which only this module imported.
section

/-! # The public iteration count for the exponent product -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys VG.Proof.Bignum.X86

theorem prodCount_ok {s : State} {base : Addr} {size eLen : Nat}
    (h : CallArgument s base size 7 (BitVec.ofNat 32 eLen)) :
    WP isa (.block prodCount) s fun t => t.gpr .esi = BitVec.ofNat 32 (8 * eLen) ∧
      t.mem = s.mem ∧ Keeps [.esi] s t := by
  unfold prodCount
  refine wp_movS h.readSrc fun u U _ => ?_
  refine wp_addS rfl fun v V _ => ?_
  refine wp_addS rfl fun w W _ => ?_
  refine wp_addS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (W.mem.trans (V.mem.trans U.mem)),
    U.keeps.trans (V.keeps.trans (W.keeps.trans T.keeps))⟩
  rw [T.gpr, W.gpr, V.gpr, U.gpr]
  simp only [← BitVec.ofNat_add]
  congr 1
  omega

end VG.Proof.Rsa.X86.Recover
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvProduct.lean`, which only this module imported.
section

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
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvSkip.lean`, which only this module imported.
section

/-! # The initial recovery validity test -/

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys VG.Proof.Rsa.KeyBits32

theorem KS.skipTest_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) (hb : sBit ∈ ls)
    (bit : V sBit ≤ 1) (borrow : (s.gpr .ebx).toNat ≤ 1) :
    WP isa (.block skipTest) s fun t => KS g s0 A live AW liveW V ls t ∧
      t.zf = some (decide (V sBit = 1 ∧ (s.gpr .ebx).toNat = 1)) := by
  unfold skipTest
  refine wp_movS (h.readSlot hb) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_logicS (.inl rfl) rfl fun v D => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have value : v.gpr .eax = BitVec.ofNat 32 (if V sBit = 1 ∧ (s.gpr .ebx).toNat = 1 then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [D.gpr, ite_eq_left rfl, U.gpr, U.other .ebx (by decide),
      bv_and_bits (by rw [BitVec.toNat_ofNat]; omega) borrow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : V sBit < 2 ^ 32)]
    split <;> rfl
  refine wp_cmpS rfl fun t T Z => WP.block_nil ⟨hv.of_rest (T.keeps []) (by simp) T.mem, ?_⟩
  rw [Z, value]
  by_cases cond : V sBit = 1 ∧ (s.gpr .ebx).toNat = 1 <;> simp [cond]

end VG.Proof.Rsa.X86.Recover
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

def product (g : CallGeometry) (m : Mem) : Nat := inputValue g m 2 * inputValue g m 1
def GoOn (p : Nat) : Prop := ¬(p < 2 ∨ (p - 1) % 2 = 1)
instance (p : Nat) : Decidable (GoOn p) := inferInstanceAs (Decidable (¬(p < 2 ∨ (p - 1) % 2 = 1)))

theorem numbers_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.numbers s fun t =>
      KS g.toGeo s (fun _ => inputValue g s.mem 0) [aN]
        (fun _ => 2 * (product g s.mem / 2)) [wM] (fun _ => 0) [] t ∧
      t.zf = some (decide (GoOn (product g s.mem))) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.numbers
  simp only [seqs]
  refine WP.seq (WP.mono (loads_ok h len) fun s1 h1 => ?_)
  have arg : CallArgument s1 g.B g.Z 7 (BitVec.ofNat 32 ((g.args 7).toNat)) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      h1.argument (h.arguments 7 (by decide)) (h.stageApart (by decide))
  refine WP.seq (WP.mono (prod_ok h1 arg (h.inputPositive 1) (h.inputBound 1) (h.inputBound 2)
    (inputValue_lt g s.mem 1) (inputValue_lt g s.mem 2)) fun s2 h2 => ?_)
  unfold VG.Impl.Rsa.X86.RecoverRt.skipBits
  refine WP.seq (WP.block_append (WP.mono (h2.bitOf_W (j := wM) (sl := sBit) (by simp) (by decide))
    fun s3 ⟨h3, _⟩ => ?_))
  refine WP.mono (h3.clrLow_W (j := wM) (by simp) (by decide)) fun s4 ⟨h4, _⟩ => ?_
  simp only [AWp, upd_self] at h4
  refine WP.seq (WP.mono (h4.subWrap_W (o := wT) (a := wZ) (b := wM)
    (by decide) (by simp) (by simp) (by decide) (by decide) (by decide)) fun s5 ⟨h5, borrow⟩ => ?_)
  have flag : (s5.gpr .ebx).toNat = b2n (decide (0 < 2 * (product g s.mem / 2))) := by
    simp only [upd_self, upd_ne _ _ (by decide : wZ ≠ wM), upd_ne _ _ (by decide : wZ ≠ wMod),
      AW1, upd_ne _ _ (by decide : wZ ≠ wD), upd_ne _ _ (by decide : wZ ≠ wE)] at borrow
    exact borrow
  refine WP.mono (h5.skipTest_ok (by simp) (by rw [upd_self]; omega)
    (by rw [flag]; exact VG.Proof.Rsa.b2n_le _)) fun t ⟨hout, zt⟩ => ?_
  refine ⟨hout.mono (fun j hj => ⟨hj, rfl⟩) ?_ (by simp), ?_⟩
  · intro j hj
    simp only [List.mem_singleton] at hj
    subst j
    exact ⟨by simp, by rw [upd_ne _ _ (by decide : wM ≠ wT), upd_self]; rfl⟩
  · simp only [upd_self] at zt
    rw [flag] at zt
    have valid : (product g s.mem % 2 = 1 ∧ b2n (decide (0 < 2 * (product g s.mem / 2))) = 1) ↔
        GoOn (product g s.mem) := by
      simp only [b2n, GoOn, decide_eq_true_eq]
      split <;> omega
    change t.zf = some (decide (product g s.mem % 2 = 1 ∧
      b2n (decide (0 < 2 * (product g s.mem / 2))) = 1)) at zt
    simpa only [valid] using zt

end VG.Proof.Rsa.X86.Recover
