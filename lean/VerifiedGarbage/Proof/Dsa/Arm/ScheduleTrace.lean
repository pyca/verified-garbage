module

public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace
import VerifiedGarbage.Proof.Dsa.Arm.Compute
import VerifiedGarbage.Proof.Framework.Omega

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
    SameTrace isa (Core.sign pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Q₁ := operand_lt_of (X.C₁.inp mq)
  have Q₂ := operand_lt_of (X.C₂.inp mq)
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
    (power_ok (output := Impl.Dsa.Layout.t) X.C₁.S.ws (by omega) X.C₁.S.wp q4 qp qw (X.C₁.inp mp).toReady
      (X.C₁.inp mg).toReady (X.C₁.inp mk).toReady (X.C₁.inp mp).value D₁.hP D₁.hPo (by omega) (by omega) (by omega))
    (power_ok (output := Impl.Dsa.Layout.t) X.C₂.S.ws (by omega) X.C₁.S.wp q4 qp qw (X.C₂.inp mp).toReady
      (X.C₂.inp mg).toReady (X.C₂.inp mk).toReady (X.C₂.inp mp).value D₂.hP D₂.hPo (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  have A₁ := St₁.run (.inr ⟨by omega, by omega⟩)
  have A₂ := St₂.run (.inr ⟨by omega, by omega⟩)
  have X₁ := X.run A₁ A₂
  -- `r = t mod q`
  refine SameTrace.assoc_left (SameTrace.seq (reduce_trace (output := Impl.Dsa.Layout.r) (count := .imm pLen)
      (X₁.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X₁.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo)
      (ok _ (by omega)) (show pLen < 2 ^ 16 by omega) (X₁.E _ mq) (ptrEq_local X₁.C₁.S.ws X₁.C₂.S.ws _) rfl
      (localReady (o := Impl.Dsa.Layout.t) X₁.C₁.S.ws (by omega) (by simp only [countValue]; omega) (by omega)) (localReady (o := Impl.Dsa.Layout.t) X₁.C₂.S.ws (by omega) (by simp only [countValue]; omega) (by omega)) D₁.hQ D₂.hQ)
    (reduce_ok (output := Impl.Dsa.Layout.r) X₁.C₁.S.ws (by omega) X.C₁.S.wq (X₁.C₁.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega)
      (localReady (o := Impl.Dsa.Layout.t) X₁.C₁.S.ws (by omega) (by simp only [countValue]; omega) (by omega))
      (X₁.C₁.inp mq).value D₁.hQ D₁.hQo (by omega) (by omega) (by omega))
    (reduce_ok (output := Impl.Dsa.Layout.r) X₁.C₂.S.ws (by omega) X.C₁.S.wq (X₁.C₂.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega)
      (localReady (o := Impl.Dsa.Layout.t) X₁.C₂.S.ws (by omega) (by simp only [countValue]; omega) (by omega))
      (X₁.C₂.inp mq).value D₂.hQ D₂.hQo (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  have A₁ := A₁.trans (St₁.run (.inr ⟨by omega, by omega⟩))
  have A₂ := A₂.trans (St₂.run (.inr ⟨by omega, by omega⟩))
  have X₂ := X.run A₁ A₂
  -- `k^(q-2) mod q`
  refine SameTrace.assoc_left (SameTrace.seq (power_trace (output := Impl.Dsa.Layout.inverse)
      (X₂.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X₂.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo)
      (X₂.C₁.inp mk).toReady (X₂.C₂.inp mk).toReady
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X₂.C₁.S.ws (by omega) (by omega) (by omega))
      (X₂.E _ mq) (X₂.E _ mk) (ptrEq_local X₂.C₁.S.ws X₂.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X₂.C₂.S.ws (by omega) (by omega) (by omega)) q4 (Nat.le_refl _) qw)
    (power_ok (output := Impl.Dsa.Layout.inverse) X₂.C₁.S.ws (by omega) X.C₁.S.wq q4 (Nat.le_refl _) qw
      (X₂.C₁.inp mq).toReady (X₂.C₁.inp mk).toReady
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X₂.C₁.S.ws (by omega) (by omega) (by omega))
      (X₂.C₁.inp mq).value (by omega) D₁.hQo (by omega) (by omega) (by omega))
    (power_ok (output := Impl.Dsa.Layout.inverse) X₂.C₂.S.ws (by omega) X.C₁.S.wq q4 (Nat.le_refl _) qw
      (X₂.C₂.inp mq).toReady (X₂.C₂.inp mk).toReady
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X₂.C₂.S.ws (by omega) (by omega) (by omega))
      (X₂.C₂.inp mq).value (by omega) D₂.hQo (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  have A₁ := A₁.trans (St₁.run (.inr ⟨by omega, by omega⟩))
  have A₂ := A₂.trans (St₂.run (.inr ⟨by omega, by omega⟩))
  have X₃ := X.run A₁ A₂
  refine SameTrace.nil_seq ?_
  -- `u = x r mod q`
  refine SameTrace.seq (productMod_trace (output := Impl.Dsa.Layout.u)
      (X₃.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X₃.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo)
      (X₃.C₁.inp mx).toReady (X₃.C₂.inp mx).toReady
      (localReady (o := Impl.Dsa.Layout.r) X₃.C₁.S.ws (by omega) (by omega) (by omega))
      (X₃.E _ mq) (X₃.E _ mx) (ptrEq_local X₃.C₁.S.ws X₃.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.r) X₃.C₂.S.ws (by omega) (by omega) (by omega)))
    (productMod_ok (output := Impl.Dsa.Layout.u) X₃.C₁.S.ws (by omega) X.C₁.S.wq (X₃.C₁.inp mq).toReady
      (X₃.C₁.inp mx).toReady (localReady (o := Impl.Dsa.Layout.r) X₃.C₁.S.ws (by omega) (by omega) (by omega))
      (X₃.C₁.inp mq).value (by omega) D₁.hQo (by omega) (by omega) (by omega))
    (productMod_ok (output := Impl.Dsa.Layout.u) X₃.C₂.S.ws (by omega) X.C₁.S.wq (X₃.C₂.inp mq).toReady
      (X₃.C₂.inp mx).toReady (localReady (o := Impl.Dsa.Layout.r) X₃.C₂.S.ws (by omega) (by omega) (by omega))
      (X₃.C₂.inp mq).value (by omega) D₂.hQo (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨B₁, St₁⟩ ⟨B₂, St₂⟩ => ?_
  have U₁ := result_lt (by omega) (Nat.le_of_lt Q₁) B₁
  have U₂ := result_lt (by omega) (Nat.le_of_lt Q₂) B₂
  have A₁ := A₁.trans (St₁.run (.inr ⟨by omega, by omega⟩))
  have A₂ := A₂.trans (St₂.run (.inr ⟨by omega, by omega⟩))
  have X₄ := X.run A₁ A₂
  -- `z = digest mod q`
  have I₁ := X₄.C₁.inp md
  have I₂ := X₄.C₂.inp md
  rw [← (countValue_run A₁).trans hc₁] at I₁
  rw [← (countValue_run A₂).trans hc₂] at I₂
  refine SameTrace.seq (reduce_trace (output := Impl.Dsa.Layout.z) (count := Core.digestPrefix)
      (X₄.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X₄.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo)
      (by decide : Impl.Dsa.Layout.Field.digest ≠ .mask) (by simp only [CountOk, Core.digestPrefix]; decide)
      (X₄.E _ mq) (X₄.E _ md) (((countValue_run A₁).trans hc₁).trans ((countValue_run A₂).trans hc₂).symm)
      I₁.toReady I₂.toReady D₁.hQ D₂.hQ)
    (reduce_ok (output := Impl.Dsa.Layout.z) X₄.C₁.S.ws (by omega) X.C₁.S.wq (X₄.C₁.inp mq).toReady
      (by simp only [CountOk, Core.digestPrefix]; decide) I₁.toReady (X₄.C₁.inp mq).value D₁.hQ D₁.hQo
      (by omega) (by omega) (by omega))
    (reduce_ok (output := Impl.Dsa.Layout.z) X₄.C₂.S.ws (by omega) X.C₁.S.wq (X₄.C₂.inp mq).toReady
      (by simp only [CountOk, Core.digestPrefix]; decide) I₂.toReady (X₄.C₂.inp mq).value D₂.hQ D₂.hQo
      (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨B₁, St₁⟩ ⟨B₂, St₂⟩ => ?_
  have Z₁ := result_lt (by omega) (Nat.le_of_lt Q₁) B₁
  have Z₂ := result_lt (by omega) (Nat.le_of_lt Q₂) B₂
  have U₁' : localVal base v₁ Impl.Dsa.Layout.u qLen < val₁ (.input .q) := by
    rw [St₁.localVal_eq (by omega) (by omega) (by omega) (by omega)]; exact U₁
  have U₂' : localVal base v₂ Impl.Dsa.Layout.u qLen < val₂ (.input .q) := by
    rw [St₂.localVal_eq (by omega) (by omega) (by omega) (by omega)]; exact U₂
  have A₁ := A₁.trans (St₁.run (.inr ⟨by omega, by omega⟩))
  have A₂ := A₂.trans (St₂.run (.inr ⟨by omega, by omega⟩))
  have X₅ := X.run A₁ A₂
  -- `v = z + u mod q`
  refine SameTrace.seq (sum_trace (output := Impl.Dsa.Layout.v)
      (X₅.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X₅.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo)
      (localReady (o := Impl.Dsa.Layout.z) X₅.C₁.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.z) X₅.C₂.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.u) X₅.C₁.S.ws (by omega) (by omega) (by omega))
      (X₅.E _ mq) (ptrEq_local X₅.C₁.S.ws X₅.C₂.S.ws _) (ptrEq_local X₅.C₁.S.ws X₅.C₂.S.ws _))
    (sum_ok (output := Impl.Dsa.Layout.v) X₅.C₁.S.ws (by omega) X.C₁.S.wq (X₅.C₁.inp mq).toReady
      (localReady (o := Impl.Dsa.Layout.z) X₅.C₁.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.u) X₅.C₁.S.ws (by omega) (by omega) (by omega))
      (X₅.C₁.inp mq).value (by omega) D₁.hQo (by rw [local_operand X₅.C₁.S.ws (by omega)]; exact Z₁)
      (by rw [local_operand X₅.C₁.S.ws (by omega)]; exact U₁') (by omega) (by omega) (by omega))
    (sum_ok (output := Impl.Dsa.Layout.v) X₅.C₂.S.ws (by omega) X.C₁.S.wq (X₅.C₂.inp mq).toReady
      (localReady (o := Impl.Dsa.Layout.z) X₅.C₂.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.u) X₅.C₂.S.ws (by omega) (by omega) (by omega))
      (X₅.C₂.inp mq).value (by omega) D₂.hQo (by rw [local_operand X₅.C₂.S.ws (by omega)]; exact Z₂)
      (by rw [local_operand X₅.C₂.S.ws (by omega)]; exact U₂') (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have A₁ := A₁.trans (St₁.run (.inr ⟨by omega, by omega⟩))
  have A₂ := A₂.trans (St₂.run (.inr ⟨by omega, by omega⟩))
  have X₆ := X.run A₁ A₂
  -- `s = k^(q-2) v mod q`
  exact SameTrace.seq (productMod_trace (output := Impl.Dsa.Layout.s)
      (X₆.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X₆.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo)
      (localReady (o := Impl.Dsa.Layout.inverse) X₆.C₁.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.inverse) X₆.C₂.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.v) X₆.C₁.S.ws (by omega) (by omega) (by omega))
      (X₆.E _ mq) (ptrEq_local X₆.C₁.S.ws X₆.C₂.S.ws _) (ptrEq_local X₆.C₁.S.ws X₆.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.v) X₆.C₂.S.ws (by omega) (by omega) (by omega)))
    (F₁ := fun _ => True) (F₂ := fun _ => True) (WP.mono (productMod_ok (output := Impl.Dsa.Layout.s) X₆.C₁.S.ws (by omega) X.C₁.S.wq
      (X₆.C₁.inp mq).toReady (localReady (o := Impl.Dsa.Layout.inverse) X₆.C₁.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.v) X₆.C₁.S.ws (by omega) (by omega) (by omega))
      (X₆.C₁.inp mq).value (by omega) D₁.hQo (by omega) (by omega) (by omega)) fun _ _ => trivial)
    (WP.mono (productMod_ok (output := Impl.Dsa.Layout.s) X₆.C₂.S.ws (by omega) X.C₁.S.wq
      (X₆.C₂.inp mq).toReady (localReady (o := Impl.Dsa.Layout.inverse) X₆.C₂.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.v) X₆.C₂.S.ws (by omega) (by omega) (by omega))
      (X₆.C₂.inp mq).value (by omega) D₂.hQo (by omega) (by omega) (by omega)) fun _ _ => trivial)
    fun _ _ _ _ => SameTrace.block_nil

theorem verify_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ c : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins) (mr : (.input .signature, qLen) ∈ ins) (ms : (.signatureS, qLen) ∈ ins)
    (md : (.input .digest, c) ∈ ins)
    (hc₁ : countValue base s₁ Core.digestPrefix = c) (hc₂ : countValue base s₂ Core.digestPrefix = c)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Core.verify pLen qLen) s₁ s₂ := by
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
  have ws : ∀ {a b : State} {s₁' s₂' : Nat}, Ws a base s₁' → Ws b base s₂' → ∀ o, PtrEq base a b (.local o) :=
    fun h₁ h₂ o => ptrEq_local h₁ h₂ o
  simp only [Core.verify, Core.verifyScalars, Core.verifyPowers, Core.sequence, List.foldr]
  -- `w = s^(q-2) mod q`
  refine SameTrace.assoc_left (SameTrace.seq (power_trace (output := Impl.Dsa.Layout.inverse)
      (X.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo)
      (X.C₁.inp ms).toReady (X.C₂.inp ms).toReady
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X.C₁.S.ws (by omega) (by omega) (by omega))
      (X.E _ mq) (X.E _ ms) (ws X.C₁.S.ws X.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X.C₂.S.ws (by omega) (by omega) (by omega)) q4 (Nat.le_refl _) qw)
    (power_ok (output := Impl.Dsa.Layout.inverse) X.C₁.S.ws (by omega) X.C₁.S.wq q4 (Nat.le_refl _) qw
      (X.C₁.inp mq).toReady (X.C₁.inp ms).toReady
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X.C₁.S.ws (by omega) (by omega) (by omega))
      (X.C₁.inp mq).value (by omega) D₁.hQo (by omega) (by omega) (by omega))
    (power_ok (output := Impl.Dsa.Layout.inverse) X.C₂.S.ws (by omega) X.C₁.S.wq q4 (Nat.le_refl _) qw
      (X.C₂.inp mq).toReady (X.C₂.inp ms).toReady
      (localReady (o := Impl.Dsa.Layout.qMinusTwo) X.C₂.S.ws (by omega) (by omega) (by omega))
      (X.C₂.inp mq).value (by omega) D₂.hQo (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  have A₁ := St₁.run (.inr ⟨by omega, by omega⟩)
  have A₂ := St₂.run (.inr ⟨by omega, by omega⟩)
  have X₁ := X.run A₁ A₂
  -- `z = digest mod q`
  have I₁ := X₁.C₁.inp md
  have I₂ := X₁.C₂.inp md
  rw [← (countValue_run A₁).trans hc₁] at I₁
  rw [← (countValue_run A₂).trans hc₂] at I₂
  refine SameTrace.assoc_left (SameTrace.seq (reduce_trace (output := Impl.Dsa.Layout.z) (count := Core.digestPrefix)
      (X₁.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X₁.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo)
      (by decide : Impl.Dsa.Layout.Field.digest ≠ .mask) (by simp only [CountOk, Core.digestPrefix]; decide)
      (X₁.E _ mq) (X₁.E _ md) (((countValue_run A₁).trans hc₁).trans ((countValue_run A₂).trans hc₂).symm)
      I₁.toReady I₂.toReady D₁.hQ D₂.hQ)
    (reduce_ok (output := Impl.Dsa.Layout.z) X₁.C₁.S.ws (by omega) X.C₁.S.wq (X₁.C₁.inp mq).toReady
      (by simp only [CountOk, Core.digestPrefix]; decide) I₁.toReady (X₁.C₁.inp mq).value D₁.hQ D₁.hQo
      (by omega) (by omega) (by omega))
    (reduce_ok (output := Impl.Dsa.Layout.z) X₁.C₂.S.ws (by omega) X.C₁.S.wq (X₁.C₂.inp mq).toReady
      (by simp only [CountOk, Core.digestPrefix]; decide) I₂.toReady (X₁.C₂.inp mq).value D₂.hQ D₂.hQo
      (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  have X₂ := X₁.run (St₁.run (.inr ⟨by omega, by omega⟩)) (St₂.run (.inr ⟨by omega, by omega⟩))
  -- `u₁ = z w mod q`
  refine SameTrace.assoc_left (SameTrace.seq (productMod_trace (output := Impl.Dsa.Layout.u)
      (X₂.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X₂.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo)
      (localReady (o := Impl.Dsa.Layout.z) X₂.C₁.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.z) X₂.C₂.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.inverse) X₂.C₁.S.ws (by omega) (by omega) (by omega))
      (X₂.E _ mq) (ws X₂.C₁.S.ws X₂.C₂.S.ws _) (ws X₂.C₁.S.ws X₂.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.inverse) X₂.C₂.S.ws (by omega) (by omega) (by omega)))
    (productMod_ok (output := Impl.Dsa.Layout.u) X₂.C₁.S.ws (by omega) X.C₁.S.wq (X₂.C₁.inp mq).toReady
      (localReady (o := Impl.Dsa.Layout.z) X₂.C₁.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.inverse) X₂.C₁.S.ws (by omega) (by omega) (by omega))
      (X₂.C₁.inp mq).value (by omega) D₁.hQo (by omega) (by omega) (by omega))
    (productMod_ok (output := Impl.Dsa.Layout.u) X₂.C₂.S.ws (by omega) X.C₁.S.wq (X₂.C₂.inp mq).toReady
      (localReady (o := Impl.Dsa.Layout.z) X₂.C₂.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.inverse) X₂.C₂.S.ws (by omega) (by omega) (by omega))
      (X₂.C₂.inp mq).value (by omega) D₂.hQo (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  have X₃ := X₂.run (St₁.run (.inr ⟨by omega, by omega⟩)) (St₂.run (.inr ⟨by omega, by omega⟩))
  -- `u₂ = r w mod q`
  refine SameTrace.assoc_left (SameTrace.seq (productMod_trace (output := Impl.Dsa.Layout.v)
      (X₃.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X₃.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo)
      (X₃.C₁.inp mr).toReady (X₃.C₂.inp mr).toReady
      (localReady (o := Impl.Dsa.Layout.inverse) X₃.C₁.S.ws (by omega) (by omega) (by omega))
      (X₃.E _ mq) (X₃.E _ mr) (ws X₃.C₁.S.ws X₃.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.inverse) X₃.C₂.S.ws (by omega) (by omega) (by omega)))
    (productMod_ok (output := Impl.Dsa.Layout.v) X₃.C₁.S.ws (by omega) X.C₁.S.wq (X₃.C₁.inp mq).toReady
      (X₃.C₁.inp mr).toReady (localReady (o := Impl.Dsa.Layout.inverse) X₃.C₁.S.ws (by omega) (by omega) (by omega))
      (X₃.C₁.inp mq).value (by omega) D₁.hQo (by omega) (by omega) (by omega))
    (productMod_ok (output := Impl.Dsa.Layout.v) X₃.C₂.S.ws (by omega) X.C₁.S.wq (X₃.C₂.inp mq).toReady
      (X₃.C₂.inp mr).toReady (localReady (o := Impl.Dsa.Layout.inverse) X₃.C₂.S.ws (by omega) (by omega) (by omega))
      (X₃.C₂.inp mq).value (by omega) D₂.hQo (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  have X₄ := X₃.run (St₁.run (.inr ⟨by omega, by omega⟩)) (St₂.run (.inr ⟨by omega, by omega⟩))
  refine SameTrace.nil_seq ?_
  -- `g^u₁ mod p`
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t)
      (X₄.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo) (X₄.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo)
      (X₄.C₁.inp mg).toReady (X₄.C₂.inp mg).toReady
      (localReady (o := Impl.Dsa.Layout.u) X₄.C₁.S.ws (by omega) (by omega) (by omega))
      (X₄.E _ mp) (X₄.E _ mg) (ws X₄.C₁.S.ws X₄.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.u) X₄.C₂.S.ws (by omega) (by omega) (by omega)) q4 qp qw)
    (power_ok (output := Impl.Dsa.Layout.t) X₄.C₁.S.ws (by omega) X.C₁.S.wp q4 qp qw (X₄.C₁.inp mp).toReady
      (X₄.C₁.inp mg).toReady (localReady (o := Impl.Dsa.Layout.u) X₄.C₁.S.ws (by omega) (by omega) (by omega))
      (X₄.C₁.inp mp).value D₁.hP D₁.hPo (by omega) (by omega) (by omega))
    (power_ok (output := Impl.Dsa.Layout.t) X₄.C₂.S.ws (by omega) X.C₁.S.wp q4 qp qw (X₄.C₂.inp mp).toReady
      (X₄.C₂.inp mg).toReady (localReady (o := Impl.Dsa.Layout.u) X₄.C₂.S.ws (by omega) (by omega) (by omega))
      (X₄.C₂.inp mp).value D₂.hP D₂.hPo (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₅ := X₄.run (St₁.run (.inr ⟨by omega, by omega⟩)) (St₂.run (.inr ⟨by omega, by omega⟩))
  -- `y^u₂ mod p`
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t2)
      (X₅.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo) (X₅.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo)
      (X₅.C₁.inp my).toReady (X₅.C₂.inp my).toReady
      (localReady (o := Impl.Dsa.Layout.v) X₅.C₁.S.ws (by omega) (by omega) (by omega))
      (X₅.E _ mp) (X₅.E _ my) (ws X₅.C₁.S.ws X₅.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.v) X₅.C₂.S.ws (by omega) (by omega) (by omega)) q4 qp qw)
    (power_ok (output := Impl.Dsa.Layout.t2) X₅.C₁.S.ws (by omega) X.C₁.S.wp q4 qp qw (X₅.C₁.inp mp).toReady
      (X₅.C₁.inp my).toReady (localReady (o := Impl.Dsa.Layout.v) X₅.C₁.S.ws (by omega) (by omega) (by omega))
      (X₅.C₁.inp mp).value D₁.hP D₁.hPo (by omega) (by omega) (by omega))
    (power_ok (output := Impl.Dsa.Layout.t2) X₅.C₂.S.ws (by omega) X.C₁.S.wp q4 qp qw (X₅.C₂.inp mp).toReady
      (X₅.C₂.inp my).toReady (localReady (o := Impl.Dsa.Layout.v) X₅.C₂.S.ws (by omega) (by omega) (by omega))
      (X₅.C₂.inp mp).value D₂.hP D₂.hPo (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₆ := X₅.run (St₁.run (.inr ⟨by omega, by omega⟩)) (St₂.run (.inr ⟨by omega, by omega⟩))
  -- their product mod p
  refine SameTrace.seq (productMod_trace (output := Impl.Dsa.Layout.t)
      (X₆.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo) (X₆.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo)
      (localReady (o := Impl.Dsa.Layout.t) X₆.C₁.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.t) X₆.C₂.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.t2) X₆.C₁.S.ws (by omega) (by omega) (by omega))
      (X₆.E _ mp) (ws X₆.C₁.S.ws X₆.C₂.S.ws _) (ws X₆.C₁.S.ws X₆.C₂.S.ws _)
      (localReady (o := Impl.Dsa.Layout.t2) X₆.C₂.S.ws (by omega) (by omega) (by omega)))
    (productMod_ok (output := Impl.Dsa.Layout.t) X₆.C₁.S.ws (by omega) X.C₁.S.wp (X₆.C₁.inp mp).toReady
      (localReady (o := Impl.Dsa.Layout.t) X₆.C₁.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.t2) X₆.C₁.S.ws (by omega) (by omega) (by omega))
      (X₆.C₁.inp mp).value D₁.hP D₁.hPo (by omega) (by omega) (by omega))
    (productMod_ok (output := Impl.Dsa.Layout.t) X₆.C₂.S.ws (by omega) X.C₁.S.wp (X₆.C₂.inp mp).toReady
      (localReady (o := Impl.Dsa.Layout.t) X₆.C₂.S.ws (by omega) (by omega) (by omega))
      (localReady (o := Impl.Dsa.Layout.t2) X₆.C₂.S.ws (by omega) (by omega) (by omega))
      (X₆.C₂.inp mp).value D₂.hP D₂.hPo (by omega) (by omega) (by omega))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₇ := X₆.run (St₁.run (.inr ⟨by omega, by omega⟩)) (St₂.run (.inr ⟨by omega, by omega⟩))
  -- mod q
  exact SameTrace.seq (reduce_trace (output := Impl.Dsa.Layout.u) (count := .imm pLen)
      (X₇.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X₇.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo)
      (ok _ (by omega)) (show pLen < 2 ^ 16 by omega) (X₇.E _ mq) (ws X₇.C₁.S.ws X₇.C₂.S.ws _) rfl
      (localReady X₇.C₁.S.ws (by omega) (by simp only [countValue]; omega) (by omega)) (localReady X₇.C₂.S.ws (by omega) (by simp only [countValue]; omega) (by omega)) D₁.hQ D₂.hQ)
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    (WP.mono (reduce_ok (output := Impl.Dsa.Layout.u) X₇.C₁.S.ws (by omega) X.C₁.S.wq (X₇.C₁.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega)
      (localReady X₇.C₁.S.ws (by omega) (by simp only [countValue]; omega) (by omega))
      (X₇.C₁.inp mq).value D₁.hQ D₁.hQo (by omega) (by omega) (by omega)) fun _ _ => trivial)
    (WP.mono (reduce_ok (output := Impl.Dsa.Layout.u) X₇.C₂.S.ws (by omega) X.C₁.S.wq (X₇.C₂.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega)
      (localReady X₇.C₂.S.ws (by omega) (by simp only [countValue]; omega) (by omega))
      (X₇.C₂.inp mq).value D₂.hQ D₂.hQo (by omega) (by omega) (by omega)) fun _ _ => trivial)
    fun _ _ _ _ => SameTrace.block_nil

end VG.Proof.Dsa.Arm
