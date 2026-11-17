module

import VerifiedGarbage.Proof.Dsa.Arm.Compute
public import VerifiedGarbage.Proof.Dsa.Arm.Body
public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace
public import VerifiedGarbage.Proof.Dsa.Arm.SigningKey

/-! ### `Dsa.Arm.ScheduleTrace`, which this module and modules that import it used -/

section

/-!
# DSA on 32-bit ARM: the traces of signing's and verification's arithmetic

As `KeyTrace.lean`, following `sign_ok` and `verify_ok`. The only values the
traces need are the bounds of the sum's operands, which its correctness
assumes.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest)

variable {umaal : Bool}

theorem local_ptrOk (o : Nat) (h : o < 2 ^ 16) : PtrOk (.local o) := h

/-- A product's or reduction's result is below the modulus. -/
theorem result_lt {base : Addr} {t : State} {o qLen Q x : Nat} (hQ : 0 < Q) (hQl : Q ≤ 256 ^ qLen)
    (B : Spec.Rsa.bytesAt t.mem (off base o) qLen = Spec.Dsa.encodeBE qLen (x % Q)) :
    localVal base t o qLen < Q := by
  rw [localVal_of_bytes B (Nat.lt_of_lt_of_le (Nat.mod_lt _ hQ) hQl)]
  exact Nat.mod_lt _ hQ

theorem sign_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ c : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (mx : (.input .x, qLen) ∈ ins) (mk : (.input .nonce, qLen) ∈ ins) (md : (.input .digest, c) ∈ ins)
    (hc₁ : countValue base s₁ Core.digestPrefix = c) (hc₂ : countValue base s₂ Core.digestPrefix = c)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Core.sign umaal pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  obtain Q₁ := operand_lt_of (X.C₁.inp mq)
  obtain Q₂ := operand_lt_of (X.C₂.inp mq)
  have hQ₁ := D₁.hQ
  have hQ₂ := D₂.hQ
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  have Li : Impl.Dsa.Layout.inverse = 14784 := rfl
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  have Lv : Impl.Dsa.Layout.v = 14848 := rfl
  have Lz : Impl.Dsa.Layout.z = 14880 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  have ok : ∀ o, o < 2 ^ 16 → PtrOk (.local o) := local_ptrOk
  simp only [Core.sign, Core.signStart, Core.signFinish, Core.sequence, List.foldr]
  -- `t = g^k mod p`
  refine SameTrace.assoc_left (SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t)
      (X.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo) (X.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X.C₁.inp mg).toReady
      (X.C₂.inp mg).toReady (X.C₁.inp mk).toReady (X.E _ mp) (X.E _ mg) (X.E _ mk)
      (X.C₂.inp mk).toReady q4 qp qw)
    (power_ok (output := Impl.Dsa.Layout.t) X.C₁.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X.C₁.inp mp).toReady
      (X.C₁.inp mg).toReady (X.C₁.inp mk).toReady (X.C₁.inp mp).value D₁.hP D₁.hPo (by omega_arith) (by omega_arith) (by omega_arith))
    (power_ok (output := Impl.Dsa.Layout.t) X.C₂.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X.C₂.inp mp).toReady
      (X.C₂.inp mg).toReady (X.C₂.inp mk).toReady (X.C₂.inp mp).value D₂.hP D₂.hPo (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  obtain A₁ := St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain A₂ := St₂.run (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain X₁ := X.run A₁ A₂
  -- `r = t mod q`
  refine SameTrace.assoc_left (SameTrace.seq (reduce_trace (output := Impl.Dsa.Layout.r) (count := .imm pLen)
      (X₁.C₁.opPre mq X.C₁.S.wq (by omega_arith) D₁.hQo) (X₁.C₂.opPre mq X.C₁.S.wq (by omega_arith) D₂.hQo)
      (ok _ (by omega_arith)) (show pLen < 2 ^ 16 by omega_arith) (X₁.E _ mq) (ptrEq_local X₁.C₁.S.ws X₁.C₂.S.ws _) rfl
      (localReady (o := Impl.Dsa.Layout.t) X₁.C₁.S.ws (by omega_arith) (by simp only [countValue]; omega_arith) (by omega_arith)) (localReady (o := Impl.Dsa.Layout.t) X₁.C₂.S.ws (by omega_arith) (by simp only [countValue]; omega_arith) (by omega_arith)) D₁.hQ D₂.hQ)
    (reduce_ok (output := Impl.Dsa.Layout.r) X₁.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₁.C₁.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
      (localReady (o := Impl.Dsa.Layout.t) X₁.C₁.S.ws (by omega_arith) (by simp only [countValue]; omega_arith) (by omega_arith))
      (X₁.C₁.inp mq).value D₁.hQ D₁.hQo (by omega_arith) (by omega_arith) (by omega_arith))
    (reduce_ok (output := Impl.Dsa.Layout.r) X₁.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₁.C₂.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
      (localReady (o := Impl.Dsa.Layout.t) X₁.C₂.S.ws (by omega_arith) (by simp only [countValue]; omega_arith) (by omega_arith))
      (X₁.C₂.inp mq).value D₂.hQ D₂.hQo (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  obtain A₁ := A₁.trans (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩))
  obtain A₂ := A₂.trans (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  obtain X₂ := X.run A₁ A₂
  -- `k^(q-2) mod q`
  refine SameTrace.assoc_left (SameTrace.seq (power_trace (output := Impl.Dsa.Layout.inverse)
      (X₂.C₁.opPre mq X.C₁.S.wq (by omega_arith) D₁.hQo) (X₂.C₂.opPre mq X.C₁.S.wq (by omega_arith) D₂.hQo)
      (X₂.C₁.inp mk).toReady (X₂.C₂.inp mk).toReady
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X₂.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₂.E _ mq) (X₂.E _ mk) (ptrEq_local X₂.C₁.S.ws X₂.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X₂.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith)) q4 (Nat.le_refl _) qw)
    (power_ok (output := Impl.Dsa.Layout.inverse) X₂.C₁.S.ws (by omega_arith) X.C₁.S.wq q4 (Nat.le_refl _) qw
      (X₂.C₁.inp mq).toReady (X₂.C₁.inp mk).toReady
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X₂.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₂.C₁.inp mq).value (by omega_arith) D₁.hQo (by omega_arith) (by omega_arith) (by omega_arith))
    (power_ok (output := Impl.Dsa.Layout.inverse) X₂.C₂.S.ws (by omega_arith) X.C₁.S.wq q4 (Nat.le_refl _) qw
      (X₂.C₂.inp mq).toReady (X₂.C₂.inp mk).toReady
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X₂.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₂.C₂.inp mq).value (by omega_arith) D₂.hQo (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  obtain A₁ := A₁.trans (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩))
  obtain A₂ := A₂.trans (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  obtain X₃ := X.run A₁ A₂
  refine SameTrace.nil_seq ?_
  -- `u = x r mod q`
  refine SameTrace.seq (productMod_trace (output := Impl.Dsa.Layout.u)
      (X₃.C₁.opPre mq X.C₁.S.wq (by omega_arith) D₁.hQo) (X₃.C₂.opPre mq X.C₁.S.wq (by omega_arith) D₂.hQo)
      (X₃.C₁.inp mx).toReady (X₃.C₂.inp mx).toReady
      (localReady (o := Impl.Dsa.Layout.r) X₃.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₃.E _ mq) (X₃.E _ mx) (ptrEq_local X₃.C₁.S.ws X₃.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.r) X₃.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith)))
    (productMod_ok (output := Impl.Dsa.Layout.u) X₃.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₃.C₁.inp mq).toReady
      (X₃.C₁.inp mx).toReady (localReady (o := Impl.Dsa.Layout.r) X₃.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₃.C₁.inp mq).value (by omega_arith) D₁.hQo (by omega_arith) (by omega_arith) (by omega_arith))
    (productMod_ok (output := Impl.Dsa.Layout.u) X₃.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₃.C₂.inp mq).toReady
      (X₃.C₂.inp mx).toReady (localReady (o := Impl.Dsa.Layout.r) X₃.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₃.C₂.inp mq).value (by omega_arith) D₂.hQo (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨B₁, St₁⟩ ⟨B₂, St₂⟩ => ?_
  obtain U₁ := result_lt (by omega_arith) (Nat.le_of_lt Q₁) B₁
  obtain U₂ := result_lt (by omega_arith) (Nat.le_of_lt Q₂) B₂
  obtain A₁ := A₁.trans (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩))
  obtain A₂ := A₂.trans (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  obtain X₄ := X.run A₁ A₂
  -- `z = digest mod q`
  obtain I₁ := X₄.C₁.inp md
  obtain I₂ := X₄.C₂.inp md
  rw [← (countValue_run A₁).trans hc₁] at I₁
  rw [← (countValue_run A₂).trans hc₂] at I₂
  refine SameTrace.seq (reduce_trace (output := Impl.Dsa.Layout.z) (count := Core.digestPrefix)
      (X₄.C₁.opPre mq X.C₁.S.wq (by omega_arith) D₁.hQo) (X₄.C₂.opPre mq X.C₁.S.wq (by omega_arith) D₂.hQo)
      (by decide : Impl.Dsa.Layout.Field.digest ≠ .mask) (by simp only [CountOk, Core.digestPrefix]; decide)
      (X₄.E _ mq) (X₄.E _ md) (((countValue_run A₁).trans hc₁).trans ((countValue_run A₂).trans hc₂).symm)
      I₁.toReady I₂.toReady D₁.hQ D₂.hQ)
    (reduce_ok (output := Impl.Dsa.Layout.z) X₄.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₄.C₁.inp mq).toReady
      (by simp only [CountOk, Core.digestPrefix]; decide) I₁.toReady (X₄.C₁.inp mq).value D₁.hQ D₁.hQo
      (by omega_arith) (by omega_arith) (by omega_arith))
    (reduce_ok (output := Impl.Dsa.Layout.z) X₄.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₄.C₂.inp mq).toReady
      (by simp only [CountOk, Core.digestPrefix]; decide) I₂.toReady (X₄.C₂.inp mq).value D₂.hQ D₂.hQo
      (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨B₁, St₁⟩ ⟨B₂, St₂⟩ => ?_
  obtain Z₁ := result_lt (by omega_arith) (Nat.le_of_lt Q₁) B₁
  obtain Z₂ := result_lt (by omega_arith) (Nat.le_of_lt Q₂) B₂
  obtain U₁' : localVal base v₁ Impl.Dsa.Layout.u qLen < val₁ (.input .q) := by
    rw [St₁.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]; exact U₁
  obtain U₂' : localVal base v₂ Impl.Dsa.Layout.u qLen < val₂ (.input .q) := by
    rw [St₂.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]; exact U₂
  obtain A₁ := A₁.trans (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩))
  obtain A₂ := A₂.trans (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  obtain X₅ := X.run A₁ A₂
  -- `v = z + u mod q`
  refine SameTrace.seq (sum_trace (output := Impl.Dsa.Layout.v)
      (X₅.C₁.opPre mq X.C₁.S.wq (by omega_arith) D₁.hQo) (X₅.C₂.opPre mq X.C₁.S.wq (by omega_arith) D₂.hQo)
      (localReady (o := Impl.Dsa.Layout.z) X₅.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.z) X₅.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.u) X₅.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₅.E _ mq) (ptrEq_local X₅.C₁.S.ws X₅.C₂.S.ws _) (ptrEq_local X₅.C₁.S.ws X₅.C₂.S.ws _))
    (sum_ok (output := Impl.Dsa.Layout.v) X₅.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₅.C₁.inp mq).toReady
      (localReady (o := Impl.Dsa.Layout.z) X₅.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.u) X₅.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₅.C₁.inp mq).value (by omega_arith) D₁.hQo (by rw [local_operand X₅.C₁.S.ws (by omega_arith)]; exact Z₁)
      (by rw [local_operand X₅.C₁.S.ws (by omega_arith)]; exact U₁') (by omega_arith) (by omega_arith) (by omega_arith))
    (sum_ok (output := Impl.Dsa.Layout.v) X₅.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₅.C₂.inp mq).toReady
      (localReady (o := Impl.Dsa.Layout.z) X₅.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.u) X₅.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₅.C₂.inp mq).value (by omega_arith) D₂.hQo (by rw [local_operand X₅.C₂.S.ws (by omega_arith)]; exact Z₂)
      (by rw [local_operand X₅.C₂.S.ws (by omega_arith)]; exact U₂') (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain A₁ := A₁.trans (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩))
  obtain A₂ := A₂.trans (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  obtain X₆ := X.run A₁ A₂
  -- `s = k^(q-2) v mod q`
  exact SameTrace.seq (productMod_trace (output := Impl.Dsa.Layout.s)
      (X₆.C₁.opPre mq X.C₁.S.wq (by omega_arith) D₁.hQo) (X₆.C₂.opPre mq X.C₁.S.wq (by omega_arith) D₂.hQo)
      (localReady (o := Impl.Dsa.Layout.inverse) X₆.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.inverse) X₆.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.v) X₆.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₆.E _ mq) (ptrEq_local X₆.C₁.S.ws X₆.C₂.S.ws _) (ptrEq_local X₆.C₁.S.ws X₆.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.v) X₆.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith)))
    (F₁ := fun _ => True) (F₂ := fun _ => True) (WP.mono (productMod_ok (output := Impl.Dsa.Layout.s) X₆.C₁.S.ws (by omega_arith) X.C₁.S.wq
      (X₆.C₁.inp mq).toReady (localReady (o := Impl.Dsa.Layout.inverse) X₆.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.v) X₆.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₆.C₁.inp mq).value (by omega_arith) D₁.hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun _ _ => trivial)
    (WP.mono (productMod_ok (output := Impl.Dsa.Layout.s) X₆.C₂.S.ws (by omega_arith) X.C₁.S.wq
      (X₆.C₂.inp mq).toReady (localReady (o := Impl.Dsa.Layout.inverse) X₆.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.v) X₆.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₆.C₂.inp mq).value (by omega_arith) D₂.hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun _ _ => trivial)
    fun _ _ _ _ => SameTrace.block_nil

theorem verify_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ c : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins) (mr : (.input .signature, qLen) ∈ ins) (ms : (.signatureS, qLen) ∈ ins)
    (md : (.input .digest, c) ∈ ins)
    (hc₁ : countValue base s₁ Core.digestPrefix = c) (hc₂ : countValue base s₂ Core.digestPrefix = c)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Core.verify umaal pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have hQ₁ := D₁.hQ
  have hQ₂ := D₂.hQ
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have Lt2 : Impl.Dsa.Layout.t2 = 15328 := rfl
  have Li : Impl.Dsa.Layout.inverse = 14784 := rfl
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  have Lv : Impl.Dsa.Layout.v = 14848 := rfl
  have Lz : Impl.Dsa.Layout.z = 14880 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  have ok : ∀ o, o < 2 ^ 16 → PtrOk (.local o) := local_ptrOk
  obtain ws : ∀ {a b : State} {s₁' s₂' : Nat}, Ws a base s₁' → Ws b base s₂' → ∀ o, PtrEq base a b (.local o) :=
    fun h₁ h₂ o => ptrEq_local h₁ h₂ o
  simp only [Core.verify, Core.verifyScalars, Core.verifyPowers, Core.sequence, List.foldr]
  -- `w = s^(q-2) mod q`
  refine SameTrace.assoc_left (SameTrace.seq (power_trace (output := Impl.Dsa.Layout.inverse)
      (X.C₁.opPre mq X.C₁.S.wq (by omega_arith) D₁.hQo) (X.C₂.opPre mq X.C₁.S.wq (by omega_arith) D₂.hQo)
      (X.C₁.inp ms).toReady (X.C₂.inp ms).toReady
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X.E _ mq) (X.E _ ms) (ws X.C₁.S.ws X.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith)) q4 (Nat.le_refl _) qw)
    (power_ok (output := Impl.Dsa.Layout.inverse) X.C₁.S.ws (by omega_arith) X.C₁.S.wq q4 (Nat.le_refl _) qw
      (X.C₁.inp mq).toReady (X.C₁.inp ms).toReady
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X.C₁.inp mq).value (by omega_arith) D₁.hQo (by omega_arith) (by omega_arith) (by omega_arith))
    (power_ok (output := Impl.Dsa.Layout.inverse) X.C₂.S.ws (by omega_arith) X.C₁.S.wq q4 (Nat.le_refl _) qw
      (X.C₂.inp mq).toReady (X.C₂.inp ms).toReady
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X.C₂.inp mq).value (by omega_arith) D₂.hQo (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  obtain A₁ := St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain A₂ := St₂.run (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain X₁ := X.run A₁ A₂
  -- `z = digest mod q`
  obtain I₁ := X₁.C₁.inp md
  obtain I₂ := X₁.C₂.inp md
  rw [← (countValue_run A₁).trans hc₁] at I₁
  rw [← (countValue_run A₂).trans hc₂] at I₂
  refine SameTrace.assoc_left (SameTrace.seq (reduce_trace (output := Impl.Dsa.Layout.z) (count := Core.digestPrefix)
      (X₁.C₁.opPre mq X.C₁.S.wq (by omega_arith) D₁.hQo) (X₁.C₂.opPre mq X.C₁.S.wq (by omega_arith) D₂.hQo)
      (by decide : Impl.Dsa.Layout.Field.digest ≠ .mask) (by simp only [CountOk, Core.digestPrefix]; decide)
      (X₁.E _ mq) (X₁.E _ md) (((countValue_run A₁).trans hc₁).trans ((countValue_run A₂).trans hc₂).symm)
      I₁.toReady I₂.toReady D₁.hQ D₂.hQ)
    (reduce_ok (output := Impl.Dsa.Layout.z) X₁.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₁.C₁.inp mq).toReady
      (by simp only [CountOk, Core.digestPrefix]; decide) I₁.toReady (X₁.C₁.inp mq).value D₁.hQ D₁.hQo
      (by omega_arith) (by omega_arith) (by omega_arith))
    (reduce_ok (output := Impl.Dsa.Layout.z) X₁.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₁.C₂.inp mq).toReady
      (by simp only [CountOk, Core.digestPrefix]; decide) I₂.toReady (X₁.C₂.inp mq).value D₂.hQ D₂.hQo
      (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  obtain X₂ := X₁.run (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)) (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  -- `u₁ = z w mod q`
  refine SameTrace.assoc_left (SameTrace.seq (productMod_trace (output := Impl.Dsa.Layout.u)
      (X₂.C₁.opPre mq X.C₁.S.wq (by omega_arith) D₁.hQo) (X₂.C₂.opPre mq X.C₁.S.wq (by omega_arith) D₂.hQo)
      (localReady (o := Impl.Dsa.Layout.z) X₂.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.z) X₂.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.inverse) X₂.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₂.E _ mq) (ws X₂.C₁.S.ws X₂.C₂.S.ws _) (ws X₂.C₁.S.ws X₂.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.inverse) X₂.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith)))
    (productMod_ok (output := Impl.Dsa.Layout.u) X₂.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₂.C₁.inp mq).toReady
      (localReady (o := Impl.Dsa.Layout.z) X₂.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.inverse) X₂.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₂.C₁.inp mq).value (by omega_arith) D₁.hQo (by omega_arith) (by omega_arith) (by omega_arith))
    (productMod_ok (output := Impl.Dsa.Layout.u) X₂.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₂.C₂.inp mq).toReady
      (localReady (o := Impl.Dsa.Layout.z) X₂.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.inverse) X₂.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₂.C₂.inp mq).value (by omega_arith) D₂.hQo (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  obtain X₃ := X₂.run (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)) (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  -- `u₂ = r w mod q`
  refine SameTrace.assoc_left (SameTrace.seq (productMod_trace (output := Impl.Dsa.Layout.v)
      (X₃.C₁.opPre mq X.C₁.S.wq (by omega_arith) D₁.hQo) (X₃.C₂.opPre mq X.C₁.S.wq (by omega_arith) D₂.hQo)
      (X₃.C₁.inp mr).toReady (X₃.C₂.inp mr).toReady
      (localReady (o := Impl.Dsa.Layout.inverse) X₃.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₃.E _ mq) (X₃.E _ mr) (ws X₃.C₁.S.ws X₃.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.inverse) X₃.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith)))
    (productMod_ok (output := Impl.Dsa.Layout.v) X₃.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₃.C₁.inp mq).toReady
      (X₃.C₁.inp mr).toReady (localReady (o := Impl.Dsa.Layout.inverse) X₃.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₃.C₁.inp mq).value (by omega_arith) D₁.hQo (by omega_arith) (by omega_arith) (by omega_arith))
    (productMod_ok (output := Impl.Dsa.Layout.v) X₃.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₃.C₂.inp mq).toReady
      (X₃.C₂.inp mr).toReady (localReady (o := Impl.Dsa.Layout.inverse) X₃.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₃.C₂.inp mq).value (by omega_arith) D₂.hQo (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  obtain X₄ := X₃.run (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)) (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  refine SameTrace.nil_seq ?_
  -- `g^u₁ mod p`
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t)
      (X₄.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo) (X₄.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo)
      (X₄.C₁.inp mg).toReady (X₄.C₂.inp mg).toReady
      (localReady (o := Impl.Dsa.Layout.u) X₄.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₄.E _ mp) (X₄.E _ mg) (ws X₄.C₁.S.ws X₄.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.u) X₄.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith)) q4 qp qw)
    (power_ok (output := Impl.Dsa.Layout.t) X₄.C₁.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X₄.C₁.inp mp).toReady
      (X₄.C₁.inp mg).toReady (localReady (o := Impl.Dsa.Layout.u) X₄.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₄.C₁.inp mp).value D₁.hP D₁.hPo (by omega_arith) (by omega_arith) (by omega_arith))
    (power_ok (output := Impl.Dsa.Layout.t) X₄.C₂.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X₄.C₂.inp mp).toReady
      (X₄.C₂.inp mg).toReady (localReady (o := Impl.Dsa.Layout.u) X₄.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₄.C₂.inp mp).value D₂.hP D₂.hPo (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain X₅ := X₄.run (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)) (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  -- `y^u₂ mod p`
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t2)
      (X₅.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo) (X₅.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo)
      (X₅.C₁.inp my).toReady (X₅.C₂.inp my).toReady
      (localReady (o := Impl.Dsa.Layout.v) X₅.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₅.E _ mp) (X₅.E _ my) (ws X₅.C₁.S.ws X₅.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.v) X₅.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith)) q4 qp qw)
    (power_ok (output := Impl.Dsa.Layout.t2) X₅.C₁.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X₅.C₁.inp mp).toReady
      (X₅.C₁.inp my).toReady (localReady (o := Impl.Dsa.Layout.v) X₅.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₅.C₁.inp mp).value D₁.hP D₁.hPo (by omega_arith) (by omega_arith) (by omega_arith))
    (power_ok (output := Impl.Dsa.Layout.t2) X₅.C₂.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X₅.C₂.inp mp).toReady
      (X₅.C₂.inp my).toReady (localReady (o := Impl.Dsa.Layout.v) X₅.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₅.C₂.inp mp).value D₂.hP D₂.hPo (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain X₆ := X₅.run (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)) (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  -- their product mod p
  refine SameTrace.seq (productMod_trace (output := Impl.Dsa.Layout.t)
      (X₆.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo) (X₆.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo)
      (localReady (o := Impl.Dsa.Layout.t) X₆.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.t) X₆.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.t2) X₆.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₆.E _ mp) (ws X₆.C₁.S.ws X₆.C₂.S.ws _) (ws X₆.C₁.S.ws X₆.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.t2) X₆.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith)))
    (productMod_ok (output := Impl.Dsa.Layout.t) X₆.C₁.S.ws (by omega_arith) X.C₁.S.wp (X₆.C₁.inp mp).toReady
      (localReady (o := Impl.Dsa.Layout.t) X₆.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.t2) X₆.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₆.C₁.inp mp).value D₁.hP D₁.hPo (by omega_arith) (by omega_arith) (by omega_arith))
    (productMod_ok (output := Impl.Dsa.Layout.t) X₆.C₂.S.ws (by omega_arith) X.C₁.S.wp (X₆.C₂.inp mp).toReady
      (localReady (o := Impl.Dsa.Layout.t) X₆.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.t2) X₆.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₆.C₂.inp mp).value D₂.hP D₂.hPo (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain X₇ := X₆.run (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)) (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  -- mod q
  exact SameTrace.seq (reduce_trace (output := Impl.Dsa.Layout.u) (count := .imm pLen)
      (X₇.C₁.opPre mq X.C₁.S.wq (by omega_arith) D₁.hQo) (X₇.C₂.opPre mq X.C₁.S.wq (by omega_arith) D₂.hQo)
      (ok _ (by omega_arith)) (show pLen < 2 ^ 16 by omega_arith) (X₇.E _ mq) (ws X₇.C₁.S.ws X₇.C₂.S.ws _) rfl
      (localReady X₇.C₁.S.ws (by omega_arith) (by simp only [countValue]; omega_arith) (by omega_arith)) (localReady X₇.C₂.S.ws (by omega_arith) (by simp only [countValue]; omega_arith) (by omega_arith)) D₁.hQ D₂.hQ)
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    (WP.mono (reduce_ok (output := Impl.Dsa.Layout.u) X₇.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₇.C₁.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
      (localReady X₇.C₁.S.ws (by omega_arith) (by simp only [countValue]; omega_arith) (by omega_arith))
      (X₇.C₁.inp mq).value D₁.hQ D₁.hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun _ _ => trivial)
    (WP.mono (reduce_ok (output := Impl.Dsa.Layout.u) X₇.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₇.C₂.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
      (localReady X₇.C₂.S.ws (by omega_arith) (by simp only [countValue]; omega_arith) (by omega_arith))
      (X₇.C₂.inp mq).value D₂.hQ D₂.hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun _ _ => trivial)
    fun _ _ _ _ => SameTrace.block_nil

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.SigningKeyTrace`, which this module and modules that import it used -/

section

/-! # Fixed pointer schedules for the signer's reduced public checks -/

@[expose] public section
namespace VG.Proof.Dsa.Arm
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout

variable {umaal : Bool}

theorem signingSubgroup_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Validate.signingSubgroup umaal pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have ho : 11232 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by omega_arith
  have pt : PtrOk (.local Impl.Dsa.Layout.t) := (by decide : Impl.Dsa.Layout.t < 2 ^ 16)
  unfold Validate.signingSubgroup
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t) (X.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo)
      (X.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X.C₁.inp mg).toReady (X.C₂.inp mg).toReady (X.C₁.inp mq).toReady
      (X.E _ mp) (X.E _ mg) (X.E _ mq)
      (X.C₂.inp mq).toReady q4 qp qw)
    (power_ok (output := Impl.Dsa.Layout.t) X.C₁.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X.C₁.inp mp).toReady
      (X.C₁.inp mg).toReady (X.C₁.inp mq).toReady (X.C₁.inp mp).value D₁.hP D₁.hPo ho.1 (by omega_arith) (by decide))
    (power_ok (output := Impl.Dsa.Layout.t) X.C₂.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X.C₂.inp mp).toReady
      (X.C₂.inp mg).toReady (X.C₂.inp mq).toReady (X.C₂.inp mp).value D₂.hP D₂.hPo ho.1 (by omega_arith) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₁ := X.run (St₁.run (.inr ho)) (St₂.run (.inr ho))
  exact isOne_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega_arith) (by omega_arith) pt
    (ptrEq_local X₁.C₁.S.ws X₁.C₂.S.ws _)

theorem signingKey_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Validate.signingKey umaal pLen qLen) s₁ s₂ :=
  SameTrace.seq (domain_trace X mp mq mg my D₁ D₂)
    (domain_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my) D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (domain_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my) D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun _ _ ⟨_, _, Rn₁⟩ ⟨_, _, Rn₂⟩ => signingSubgroup_trace (X.run Rn₁ Rn₂) mp mq mg D₁ D₂

end VG.Proof.Dsa.Arm

end

end

/-!
# DSA on 32-bit ARM: the bodies' traces

The checks and the arithmetic (`KeyTrace.lean`, `ScheduleTrace.lean`), then
the signature's words, written through the output's pointer, which is the
same in both runs, under each run's flag, which only masks them.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_dp wp_movw op2_reg dpVal)
open VG.Proof.Ecdsa.Arm (mask32)

variable {umaal : Bool}

theorem signCompute_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ c : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins) (mx : (.input .x, qLen) ∈ ins) (mk : (.input .nonce, qLen) ∈ ins)
    (md : (.input .digest, c) ∈ ins)
    (hc₁ : countValue base s₁ Core.digestPrefix = c) (hc₂ : countValue base s₂ Core.digestPrefix = c)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (SignVerify.signCompute umaal pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  simp only [SignVerify.signCompute, Core.sequence, List.foldr]
  refine SameTrace.seq (signingKey_trace X mp mq mg my D₁ D₂)
    (signingKey_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my) D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (signingKey_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my) D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun u₁ u₂ ⟨_, L₁, A₁⟩ ⟨_, L₂, A₂⟩ => ?_
  have X₁ := X.run A₁ A₂
  refine SameTrace.seq (privateKey_trace X₁ mp mq mg my mx mk D₁ D₂)
    (privateKey_ok X₁.C₁.S (X₁.C₁.inp mp) (X₁.C₁.inp mq) (X₁.C₁.inp mg) (X₁.C₁.inp my) (X₁.C₁.inp mx)
      (X₁.C₁.inp mk) D₁.hP D₁.hPo)
    (privateKey_ok X₁.C₂.S (X₁.C₂.inp mp) (X₁.C₂.inp mq) (X₁.C₂.inp mg) (X₁.C₂.inp my) (X₁.C₂.inp mx)
      (X₁.C₂.inp mk) D₂.hP D₂.hPo)
    fun u₁ u₂ ⟨_, K₁, B₁⟩ ⟨_, K₂, B₂⟩ => ?_
  have X₂ := X₁.run B₁ B₂
  have M₁ : localVal base u₁ Impl.Dsa.Layout.qMinusTwo qLen = val₁ (.input .q) - 2 := by
    rw [K₁ _ _ (by decide) (by dsimp only; omega_arith), L₁]
  have M₂ : localVal base u₂ Impl.Dsa.Layout.qMinusTwo qLen = val₂ (.input .q) - 2 := by
    rw [K₂ _ _ (by decide) (by dsimp only; omega_arith), L₂]
  have c₁ := ((countValue_run B₁).trans (countValue_run A₁)).trans hc₁
  have c₂ := ((countValue_run B₂).trans (countValue_run A₂)).trans hc₂
  refine SameTrace.seq (sign_trace X₂ mp mq mg mx mk md c₁ c₂ D₁ D₂)
    (sign_ok X₂.C₁.S (X₂.C₁.inp mp) (X₂.C₁.inp mq) (X₂.C₁.inp mg) (X₂.C₁.inp mx) (X₂.C₁.inp mk) (X₂.C₁.inp md)
      c₁ M₁ D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (sign_ok X₂.C₂.S (X₂.C₂.inp mp) (X₂.C₂.inp mq) (X₂.C₂.inp mg) (X₂.C₂.inp mx) (X₂.C₂.inp mk) (X₂.C₂.inp md)
      c₂ M₂ D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun u₁ u₂ ⟨_, _, _, A₁⟩ ⟨_, _, _, A₂⟩ => ?_
  have X₃ := X₂.run A₁ A₂
  have ok : ∀ o, o < 2 ^ 16 → PtrOk (.local o) := local_ptrOk
  refine SameTrace.assoc_left (SameTrace.seq (zero_trace X₃.C₁.S.ws X₃.C₂.S.ws (by omega_arith) (by omega_arith)
      (ok _ (by omega_arith)) (ptrEq_local X₃.C₁.S.ws X₃.C₂.S.ws _) true)
    (zero_ok X₃.C₁.S.ws (by omega_arith) X.C₁.S.wq
      (localReady (o := Impl.Dsa.Layout.r) (len := qLen) X₃.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith)) true)
    (zero_ok X₃.C₂.S.ws (by omega_arith) X.C₁.S.wq
      (localReady (o := Impl.Dsa.Layout.r) (len := qLen) X₃.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith)) true)
    fun u₁ u₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  have w₁ := St₁.ws X₃.C₁.S.ws
  have w₂ := St₂.ws X₃.C₂.S.ws
  exact SameTrace.seq (zero_trace w₁ w₂ (by omega_arith) (by omega_arith) (ok _ (by omega_arith)) (ptrEq_local w₁ w₂ _) true)
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    (WP.mono (zero_ok w₁ (by omega_arith) X.C₁.S.wq
      (localReady (o := Impl.Dsa.Layout.s) (len := qLen) w₁ (by omega_arith) (by omega_arith) (by omega_arith)) true) fun _ _ => trivial)
    (WP.mono (zero_ok w₂ (by omega_arith) X.C₁.S.wq
      (localReady (o := Impl.Dsa.Layout.s) (len := qLen) w₂ (by omega_arith) (by omega_arith) (by omega_arith)) true) fun _ _ => trivial)
    fun _ _ _ _ => SameTrace.block_nil

/-- The checks after the public key's, given q − 2 in both runs. -/
theorem verifyTail_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ c : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins) (mr : (.input .signature, qLen) ∈ ins) (ms : (.signatureS, qLen) ∈ ins)
    (md : (.input .digest, c) ∈ ins)
    (hc₁ : countValue base s₁ Core.digestPrefix = c) (hc₂ : countValue base s₂ Core.digestPrefix = c)
    (L₁ : localVal base s₁ Impl.Dsa.Layout.qMinusTwo qLen = val₁ (.input .q) - 2)
    (L₂ : localVal base s₂ Impl.Dsa.Layout.qMinusTwo qLen = val₂ (.input .q) - 2)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Core.sequence [
      .seq (Validate.range qLen .q (.input .signature)) (Validate.range qLen .q .signatureS),
      Core.verify umaal pLen qLen,
      Validate.equalValues qLen (.local Impl.Dsa.Layout.u) (.input .signature)]) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  simp only [Core.sequence, List.foldr]
  refine SameTrace.assoc_left (SameTrace.seq (range_trace X.C₁.S.ws X.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wq
      (X.C₁.inp mq).toReady (X.C₂.inp mq).toReady (X.C₁.inp mr).toReady (X.E _ mq) (X.E _ mr) false)
    (range_ok X.C₁.S.ws (by omega_arith) X.C₁.S.wq (X.C₁.inp mq).toReady (X.C₁.inp mr).toReady false)
    (range_ok X.C₂.S.ws (by omega_arith) X.C₁.S.wq (X.C₂.inp mq).toReady (X.C₂.inp mr).toReady false)
    fun v₁ v₂ ⟨_, Sa₁⟩ ⟨_, Sa₂⟩ => ?_)
  have R₁ := Sa₁.run (.inl ⟨rfl, rfl⟩)
  have R₂ := Sa₂.run (.inl ⟨rfl, rfl⟩)
  have X₂ := X.run R₁ R₂
  refine SameTrace.seq (range_trace X₂.C₁.S.ws X₂.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wq
      (X₂.C₁.inp mq).toReady (X₂.C₂.inp mq).toReady (X₂.C₁.inp ms).toReady (X₂.E _ mq) (X₂.E _ ms) false)
    (range_ok X₂.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₂.C₁.inp mq).toReady (X₂.C₁.inp ms).toReady false)
    (range_ok X₂.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₂.C₂.inp mq).toReady (X₂.C₂.inp ms).toReady false)
    fun w₁ w₂ ⟨_, Sb₁⟩ ⟨_, Sb₂⟩ => ?_
  have R₁' := Sb₁.run (.inl ⟨rfl, rfl⟩)
  have R₂' := Sb₂.run (.inl ⟨rfl, rfl⟩)
  have X₃ := X₂.run R₁' R₂'
  have M₁ : localVal base w₁ Impl.Dsa.Layout.qMinusTwo qLen = val₁ (.input .q) - 2 := by
    rw [Sb₁.localVal_eq (by decide) (by omega_arith) (by omega_arith) (by omega_arith),
      Sa₁.localVal_eq (by decide) (by omega_arith) (by omega_arith) (by omega_arith), L₁]
  have M₂ : localVal base w₂ Impl.Dsa.Layout.qMinusTwo qLen = val₂ (.input .q) - 2 := by
    rw [Sb₂.localVal_eq (by decide) (by omega_arith) (by omega_arith) (by omega_arith),
      Sa₂.localVal_eq (by decide) (by omega_arith) (by omega_arith) (by omega_arith), L₂]
  have c₁ := ((countValue_run R₁').trans (countValue_run R₁)).trans hc₁
  have c₂ := ((countValue_run R₂').trans (countValue_run R₂)).trans hc₂
  refine SameTrace.seq (verify_trace X₃ mp mq mg my mr ms md c₁ c₂ D₁ D₂)
    (verify_ok X₃.C₁.S (X₃.C₁.inp mp) (X₃.C₁.inp mq) (X₃.C₁.inp mg) (X₃.C₁.inp my) (X₃.C₁.inp mr)
      (X₃.C₁.inp ms) (X₃.C₁.inp md) c₁ M₁ D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (verify_ok X₃.C₂.S (X₃.C₂.inp mp) (X₃.C₂.inp mq) (X₃.C₂.inp mg) (X₃.C₂.inp my) (X₃.C₂.inp mr)
      (X₃.C₂.inp ms) (X₃.C₂.inp md) c₂ M₂ D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun u₁ u₂ ⟨_, _, B₁⟩ ⟨_, _, B₂⟩ => ?_
  have X₄ := X₃.run B₁ B₂
  exact SameTrace.seq (equalValues_trace X₄.C₁.S.ws X₄.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wq
      (localReady (o := Impl.Dsa.Layout.u) X₄.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (localReady (o := Impl.Dsa.Layout.u) X₄.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith))
      (X₄.C₁.inp mr).toReady (ptrEq_local X₄.C₁.S.ws X₄.C₂.S.ws _) (X₄.E _ mr))
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    (WP.mono (equalValues_ok X₄.C₁.S.ws (by omega_arith) X.C₁.S.wq
      (localReady (o := Impl.Dsa.Layout.u) X₄.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith)) (X₄.C₁.inp mr).toReady)
      fun _ _ => trivial)
    (WP.mono (equalValues_ok X₄.C₂.S.ws (by omega_arith) X.C₁.S.wq
      (localReady (o := Impl.Dsa.Layout.u) X₄.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith)) (X₄.C₂.inp mr).toReady)
      fun _ _ => trivial)
    fun _ _ _ _ => SameTrace.block_nil

/-- The output's pointer, and the flag in `r3`. -/
theorem outBlock_ok {u : State} {base : Addr} {size qLen : Nat} (wu : Ws u base size) (hz : 120 ≤ size)
    (hq : qLen < 2 ^ 16) (second : Bool) :
    WP isa (.block (SignVerify.outputPointer qLen second ++
      ([.ldr .r3 .r12 (Impl.Dsa.Arm.Layout.field .mask)] : List Instr))) u
      fun w => w.gpr .r11 = pointerValue base u (.input .out) + BitVec.ofNat 32 (if second then qLen else 0) ∧
        Rest [.r3, .r4, .r11] u w ∧ w.mem = u.mem := by
  have fm : Impl.Dsa.Arm.Layout.field .mask = 116 := rfl
  simp only [SignVerify.outputPointer, List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (pointer_ok wu hz (p := .input .out)
    (by decide : Impl.Dsa.Layout.Field.out ≠ .mask)) fun w₁ ⟨P₁, R₁, M₁⟩ => ?_
  have w₁s := wu.of_rest R₁ (by decide)
  cases second
  · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    exact wp_ldr (by decide) (w₁s.ea12 (by omega_arith)) (w₁s.read (by omega_arith)) fun w u₂ => WP.block_nil
      ⟨by rw [u₂.other .r11 (by decide), P₁]; exact (BitVec.add_zero _).symm,
        (R₁.mono (by decide)).trans (u₂.rest (by decide)), by rw [u₂.mem, M₁]⟩
  · simp only [↓reduceIte, List.cons_append, List.nil_append]
    refine wp_movw fun w₂ u₂ => wp_dp (op2_reg _ _) fun w₃ u₃ => ?_
    have w₃s := (w₁s.of_upd u₂ (by decide)).of_upd u₃ (by decide)
    exact wp_ldr (by decide) (w₃s.ea12 (by omega_arith)) (w₃s.read (by omega_arith)) fun w u₄ => WP.block_nil
      ⟨by rw [u₄.other .r11 (by decide), u₃.gpr, dpVal, u₂.other .r11 (by decide), u₂.gpr, P₁, movw_ofNat hq],
        (((R₁.mono (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans (u₄.rest (by decide)),
        by rw [u₄.mem, u₃.mem, u₂.mem, M₁]⟩

theorem writeScalar_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ qLen nQ input : Nat}
    (hs₁ : Ws s₁ base size₁) (hs₂ : Ws s₂ base size₂) (hz₁ : 11232 ≤ size₁) (hz₂ : 11232 ≤ size₂) (wq : Width qLen nQ)
    (q32 : qLen ≤ 32) (hin : 11232 ≤ input) (hin₁ : input + qLen < size₁) (hin₂ : input + qLen < size₂)
    (h16 : input < 2 ^ 16) (heo : PtrEq base s₁ s₂ (.input .out)) (second : Bool) :
    SameTrace isa (SignVerify.writeScalar qLen input second) s₁ s₂ := by
  obtain ⟨n0, n48, hl, hl'⟩ := wq.bounds
  unfold SignVerify.writeScalar
  dsimp only
  rw [← wq.n_eq]
  refine SameTrace.seq (load_trace hs₁ hs₂ (by omega_arith) (by omega_arith) (local_ptrOk _ h16) (ptrEq_local hs₁ hs₂ _))
    (loadSlot_ok (i := 8) hs₁ hz₁ wq (by decide) (localReady (o := input) (len := qLen) hs₁ hin (by omega_arith) (by omega_arith)))
    (loadSlot_ok (i := 8) hs₂ hz₂ wq (by decide) (localReady (o := input) (len := qLen) hs₂ hin (by omega_arith) (by omega_arith)))
    fun u₁ u₂ ⟨wu₁, _, Ru₁, Ou₁⟩ ⟨wu₂, _, Ru₂, Ou₂⟩ => ?_
  have pe := ptrEq_slot (p := .input .out) (by decide : Impl.Dsa.Layout.Field.out ≠ .mask) heo (by decide) n48 Ru₁ Ou₁ Ru₂ Ou₂
  refine SameTrace.seq (SameTrace.of_relCT (outBlock_relCT qLen second) (agree0 wu₁ wu₂))
    (outBlock_ok wu₁ (by omega_arith) (by omega_arith) second) (outBlock_ok wu₂ (by omega_arith) (by omega_arith) second)
    fun w₁ w₂ ⟨P₁, R₁, _⟩ ⟨P₂, R₂, _⟩ => ?_
  exact SameTrace.of_relCT (storeComponent_relCT qLen (baseS nQ))
    (agreeWs true false (wu₁.of_rest R₁ (by decide)) (wu₂.of_rest R₂ (by decide)) (fun _ => by rw [P₁, P₂, pe])
      (fun h => nomatch h))

theorem signBody_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ c : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins) (mx : (.input .x, qLen) ∈ ins) (mk : (.input .nonce, qLen) ∈ ins)
    (md : (.input .digest, c) ∈ ins)
    (hc₁ : countValue base s₁ Core.digestPrefix = c) (hc₂ : countValue base s₂ Core.digestPrefix = c)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q)))
    (hm₁ : maskW base s₁ = BitVec.allOnes 32) (hm₂ : maskW base s₂ = BitVec.allOnes 32)
    (O₁ : Output s₁ base size₁ (2 * qLen)) (O₂ : Output s₂ base size₂ (2 * qLen))
    (heo : PtrEq base s₁ s₂ (.input .out)) :
    SameTrace isa (SignVerify.signBody umaal pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Q₁ := operand_lt_of (X.C₁.inp mq)
  have Q₂ := operand_lt_of (X.C₂.inp mq)
  have hQ₁ := D₁.hQ
  have hQ₂ := D₂.hQ
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  unfold SignVerify.signBody
  refine SameTrace.seq (signCompute_trace X mp mq mg my mx mk md hc₁ hc₂ D₁ D₂)
    (signCompute_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my) (X.C₁.inp mx) (X.C₁.inp mk)
      (X.C₁.inp md) hc₁ D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (signCompute_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my) (X.C₂.inp mx) (X.C₂.inp mk)
      (X.C₂.inp md) hc₂ D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun u₁ u₂ ⟨F₁, Ru₁, Su₁, A₁⟩ ⟨F₂, Ru₂, Su₂, A₂⟩ => ?_
  have X₁ := X.run A₁ A₂
  have hO : ∀ r ∈ runRanges, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1 := by decide
  have pe : PtrEq base u₁ u₂ (.input .out) := by
    unfold PtrEq
    rw [pointerValue_keep (A₁.rest.gpr .r12 (by decide)) A₁.mem hO (p := .input .out) (by decide : Impl.Dsa.Layout.Field.out ≠ .mask),
      pointerValue_keep (A₂.rest.gpr .r12 (by decide)) A₂.mem hO (p := .input .out) (by decide : Impl.Dsa.Layout.Field.out ≠ .mask)]
    exact heo
  have mu₁ : maskW base u₁ = mask32 (signChecks (val₁ (.input .p)) (val₁ (.input .q)) (val₁ (.input .g))
      (val₁ (.input .y)) (val₁ (.input .x)) (val₁ (.input .nonce)) (val₁ (.input .digest))) := by
    rw [F₁, hm₁, BitVec.allOnes_and]
  have mu₂ : maskW base u₂ = mask32 (signChecks (val₂ (.input .p)) (val₂ (.input .q)) (val₂ (.input .g))
      (val₂ (.input .y)) (val₂ (.input .x)) (val₂ (.input .nonce)) (val₂ (.input .digest))) := by
    rw [F₂, hm₂, BitVec.allOnes_and]
  have qlt₁ : ∀ x, x % val₁ (.input .q) < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Q₁
  have qlt₂ : ∀ x, x % val₂ (.input .q) < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Q₂
  refine SameTrace.seq (writeScalar_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wq q32 (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) pe false)
    (writeScalar_ok X₁.C₁.S.ws b₁ X.C₁.S.wq q32 (by omega_arith) (by omega_arith) Ru₁ (by simp only [rValue]; exact qlt₁ _)
      _ mu₁ (O₁.run A₁) false)
    (writeScalar_ok X₁.C₂.S.ws b₂ X.C₁.S.wq q32 (by omega_arith) (by omega_arith) Ru₂ (by simp only [rValue]; exact qlt₂ _)
      _ mu₂ (O₂.run A₂) false)
    fun v₁ v₂ ⟨_, mv₁, Pv₁, Wv₁, Kv₁, _, Bdv₁⟩ ⟨_, mv₂, Pv₂, Wv₂, Kv₂, _, Bdv₂⟩ => ?_
  have wv₁ := X₁.C₁.S.ws.of_rest Bdv₁.rest (by decide)
  have wv₂ := X₁.C₂.S.ws.of_rest Bdv₂.rest (by decide)
  refine SameTrace.seq (writeScalar_trace wv₁ wv₂ (by omega_arith) (by omega_arith) X.C₁.S.wq q32 (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (by unfold PtrEq; rw [Pv₁, Pv₂]; exact pe) true)
    (writeScalar_ok (v := sValue (val₁ (.input .p)) (val₁ (.input .q)) (val₁ (.input .g)) (val₁ (.input .x))
      (val₁ (.input .nonce)) (val₁ (.input .digest))) wv₁ b₁ X.C₁.S.wq q32 (by omega_arith) (by omega_arith)
      (by rw [Kv₁ _ _ (by omega_arith) (by omega_arith)]; exact Su₁) (by simp only [sValue]; exact qlt₁ _) _ (mv₁.trans mu₁)
      ((O₁.run A₁).keep Pv₁ Wv₁) true)
    (writeScalar_ok (v := sValue (val₂ (.input .p)) (val₂ (.input .q)) (val₂ (.input .g)) (val₂ (.input .x))
      (val₂ (.input .nonce)) (val₂ (.input .digest))) wv₂ b₂ X.C₁.S.wq q32 (by omega_arith) (by omega_arith)
      (by rw [Kv₂ _ _ (by omega_arith) (by omega_arith)]; exact Su₂) (by simp only [sValue]; exact qlt₂ _) _ (mv₂.trans mu₂)
      ((O₂.run A₂).keep Pv₂ Wv₂) true)
    fun w₁ w₂ ⟨_, _, _, _, _, _, Bdw₁⟩ ⟨_, _, _, _, _, _, Bdw₂⟩ => ?_
  exact SameTrace.of_relCT result_relCT
    (agree0 (wv₁.of_rest Bdw₁.rest (by decide)) (wv₂.of_rest Bdw₂.rest (by decide)))

end VG.Proof.Dsa.Arm
