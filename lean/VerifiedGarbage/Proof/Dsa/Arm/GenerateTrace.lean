module

public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace
public import VerifiedGarbage.Proof.Dsa.Arm.OpTrace
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCompute
import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
public import VerifiedGarbage.Proof.Dsa.SameTrace
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
import Mathlib.Tactic.ToDual

/-!
# DSA domain checks and key derivation on 32-bit ARM: the traces

As the key checks' (`KeyTrace.lean`): the dispatch compares the public
widths (`genDispatch_trace`), and each operation reads its operands through
pointers that are the same in both runs (`parameters_trace`,
`deriveCompute_trace`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest eval_eq)

theorem genDispatch_trace (sized : Nat → Nat → Prog isa) (widths : List (Nat × Nat))
    {s₁ s₂ : State} {base : Addr} {size₁ size₂ pLen qLen : Nat}
    (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂) (hz₁ : 120 ≤ size₁) (hz₂ : 120 ≤ size₂)
    (member : (pLen, qLen) ∈ widths) (bound : ∀ w ∈ widths, w.1 < 2 ^ 16 ∧ w.2 < 2 ^ 16)
    (hp₁ : (hdr base s₁ 100).toNat = pLen) (hq₁ : (hdr base s₁ 104).toNat = qLen)
    (hp₂ : (hdr base s₂ 100).toNat = pLen) (hq₂ : (hdr base s₂ 104).toNat = qLen)
    (body : ∀ t₁ t₂, Rest [.r4, .r5] s₁ t₁ → t₁.mem = s₁.mem → Rest [.r4, .r5] s₂ t₂ → t₂.mem = s₂.mem →
      SameTrace isa (.seq (sized pLen qLen) Tail) t₁ t₂) :
    SameTrace isa (.seq (Generate.dispatch sized widths) Tail) s₁ s₂ := by
  induction widths generalizing s₁ s₂ with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    obtain ⟨wp, wq⟩ := w
    have B := bound (wp, wq) List.mem_cons_self
    unfold Generate.dispatch
    refine SameTrace.assoc_left (SameTrace.seq (widthMatch_trace h₁ h₂ hz₁ hz₂ hp₁ hp₂ B.1)
      (widthMatch_ok h₁ hz₁ hp₁ hq₁ B.1 B.2) (widthMatch_ok h₂ hz₂ hp₂ hq₂ B.1 B.2)
      fun t₁ t₂ ⟨Z₁, R₁, M₁⟩ ⟨Z₂, R₂, M₂⟩ => ?_)
    refine SameTrace.seq_ite (by rw [eval_eq, eval_eq, Z₁, Z₂]) (fun ht => ?_) (fun hf => ?_)
    · have Both : pLen = wp ∧ qLen = wq := of_decide_eq_true (by rw [eval_eq, Z₁] at ht; exact Option.some.inj ht)
      rw [← Both.1, ← Both.2]
      exact body t₁ t₂ R₁ M₁ R₂ M₂
    · have Both : ¬ (pLen = wp ∧ qLen = wq) :=
        of_decide_eq_false (by rw [eval_eq, Z₁] at hf; exact Option.some.inj hf)
      exact ih (h₁.of_rest R₁ (by decide)) (h₂.of_rest R₂ (by decide))
        (by simpa only [List.mem_cons, Prod.mk.injEq, Both, false_or] using member)
        (fun w hw => bound w (List.mem_cons_of_mem _ hw))
        (by simp only [hdr, M₁]; exact hp₁) (by simp only [hdr, M₁]; exact hq₁)
        (by simp only [hdr, M₂]; exact hp₂) (by simp only [hdr, M₂]; exact hq₂)
        fun u₁ u₂ Ru₁ Mu₁ Ru₂ Mu₂ => body u₁ u₂ (R₁.trans Ru₁) (Mu₁.trans M₁) (R₂.trans Ru₂) (Mu₂.trans M₂)

theorem domain_gen_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Generate.domain pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  simp only [Generate.domain, Core.sequence, List.foldr]
  refine SameTrace.seq (range_trace X.C₁.S.ws X.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wp
      (X.C₁.inp mp).toReady (X.C₂.inp mp).toReady (X.C₁.inp mg).toReady (X.E _ mp) (X.E _ mg) true)
    (range_ok X.C₁.S.ws (by omega_arith) X.C₁.S.wp (X.C₁.inp mp).toReady (X.C₁.inp mg).toReady true)
    (range_ok X.C₂.S.ws (by omega_arith) X.C₁.S.wp (X.C₂.inp mp).toReady (X.C₂.inp mg).toReady true)
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₂ := X.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  -- `p - 1`
  refine SameTrace.seq (minus_trace (amount := 1) (output := Impl.Dsa.Layout.t)
      (X₂.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo) (X₂.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X₂.E _ mp))
    (minus_ok (output := Impl.Dsa.Layout.t) X₂.C₁.S.ws (by omega_arith) X.C₁.S.wp (X₂.C₁.inp mp).toReady
      (X₂.C₁.inp mp).value D₁.hP D₁.hPo (by have := D₁.hP; omega_arith) (by decide) (by decide) (by omega_arith) (by decide))
    (minus_ok (output := Impl.Dsa.Layout.t) X₂.C₂.S.ws (by omega_arith) X.C₁.S.wp (X₂.C₂.inp mp).toReady
      (X₂.C₂.inp mp).value D₂.hP D₂.hPo (by have := D₂.hP; omega_arith) (by decide) (by decide) (by omega_arith) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₃ := X₂.run (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)) (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  -- `(p - 1) mod q`
  refine SameTrace.seq (reduce_trace (output := Impl.Dsa.Layout.u) (count := .imm pLen)
      (X₃.C₁.opPre mq X.C₁.S.wq (by have := D₁.hQ; omega_arith) D₁.hQo)
      (X₃.C₂.opPre mq X.C₁.S.wq (by have := D₂.hQ; omega_arith) D₂.hQo)
      (show PtrOk (.local Impl.Dsa.Layout.t) from (by decide : Impl.Dsa.Layout.t < 2 ^ 16))
      (show pLen < 2 ^ 16 by omega_arith) (X₃.E _ mq) (ptrEq_local X₃.C₁.S.ws X₃.C₂.S.ws _) rfl
      (localReady X₃.C₁.S.ws (by decide) (by simp only [countValue]; omega_arith) (by decide))
      (localReady X₃.C₂.S.ws (by decide) (by simp only [countValue]; omega_arith) (by decide)) D₁.hQ D₂.hQ)
    (reduce_ok (output := Impl.Dsa.Layout.u) X₃.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₃.C₁.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
      (localReady X₃.C₁.S.ws (by decide) (by simp only [countValue]; omega_arith) (by decide))
      (X₃.C₁.inp mq).value D₁.hQ D₁.hQo (by decide) (by omega_arith) (by decide))
    (reduce_ok (output := Impl.Dsa.Layout.u) X₃.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₃.C₂.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
      (localReady X₃.C₂.S.ws (by decide) (by simp only [countValue]; omega_arith) (by decide))
      (X₃.C₂.inp mq).value D₂.hQ D₂.hQo (by decide) (by omega_arith) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₄ := X₃.run (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)) (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  -- `q ∣ p - 1`
  refine SameTrace.seq (zero_trace X₄.C₁.S.ws X₄.C₂.S.ws (by omega_arith) (by omega_arith)
      (show PtrOk (.local Impl.Dsa.Layout.u) from (by decide : Impl.Dsa.Layout.u < 2 ^ 16))
      (ptrEq_local X₄.C₁.S.ws X₄.C₂.S.ws _) false)
    (zero_ok X₄.C₁.S.ws (by omega_arith) X.C₁.S.wq
      (localReady (len := qLen) X₄.C₁.S.ws (by decide) (by omega_arith) (by decide)) false)
    (zero_ok X₄.C₂.S.ws (by omega_arith) X.C₁.S.wq
      (localReady (len := qLen) X₄.C₂.S.ws (by decide) (by omega_arith) (by decide)) false)
    fun _ _ _ _ => SameTrace.block_nil

theorem subgroup_gen_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Generate.subgroup pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have ho : 4960 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by omega_arith
  have pt : PtrOk (.local Impl.Dsa.Layout.t) := (by decide : Impl.Dsa.Layout.t < 2 ^ 16)
  unfold Generate.subgroup
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
  exact isOne_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega_arith) (by omega_arith) pt (ptrEq_local X₁.C₁.S.ws X₁.C₂.S.ws _)

theorem parameters_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Generate.parameters pLen qLen) s₁ s₂ :=
  SameTrace.seq (domain_gen_trace X mp mq mg D₁ D₂)
    (domain_gen_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (domain_gen_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun _ _ ⟨_, Rn₁⟩ ⟨_, Rn₂⟩ => subgroup_gen_trace (X.run Rn₁ Rn₂) mp mq mg D₁ D₂

theorem deriveCompute_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (mx : (.input .nonce, qLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Generate.deriveCompute pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have L2 : Impl.Dsa.Layout.t2 = 15328 := rfl
  have ho : 4960 ≤ Impl.Dsa.Layout.t2 ∧ Impl.Dsa.Layout.t2 + pLen ≤ 15712 := by omega_arith
  simp only [Generate.deriveCompute, Core.sequence, List.foldr]
  refine SameTrace.seq (parameters_trace X mp mq mg D₁ D₂)
    (parameters_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (parameters_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun v₁ v₂ ⟨_, Rn₁⟩ ⟨_, Rn₂⟩ => ?_
  have X₁ := X.run Rn₁ Rn₂
  refine SameTrace.seq (range_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wq
      (X₁.C₁.inp mq).toReady (X₁.C₂.inp mq).toReady (X₁.C₁.inp mx).toReady (X₁.E _ mq) (X₁.E _ mx) false)
    (range_ok X₁.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₁.C₁.inp mq).toReady (X₁.C₁.inp mx).toReady false)
    (range_ok X₁.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₁.C₂.inp mq).toReady (X₁.C₂.inp mx).toReady false)
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₂ := X₁.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t2) (X₂.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo)
      (X₂.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X₂.C₁.inp mg).toReady (X₂.C₂.inp mg).toReady (X₂.C₁.inp mx).toReady
      (X₂.E _ mp) (X₂.E _ mg) (X₂.E _ mx)
      (X₂.C₂.inp mx).toReady q4 qp qw)
    (power_ok (output := Impl.Dsa.Layout.t2) X₂.C₁.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X₂.C₁.inp mp).toReady
      (X₂.C₁.inp mg).toReady (X₂.C₁.inp mx).toReady (X₂.C₁.inp mp).value D₁.hP D₁.hPo ho.1 (by omega_arith) (by decide))
    (power_ok (output := Impl.Dsa.Layout.t2) X₂.C₂.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X₂.C₂.inp mp).toReady
      (X₂.C₂.inp mg).toReady (X₂.C₂.inp mx).toReady (X₂.C₂.inp mp).value D₂.hP D₂.hPo ho.1 (by omega_arith) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₃ := X₂.run (St₁.run (.inr ho)) (St₂.run (.inr ho))
  refine SameTrace.seq (range_trace X₃.C₁.S.ws X₃.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wp
      (X₃.C₁.inp mp).toReady (X₃.C₂.inp mp).toReady (localReady X₃.C₁.S.ws ho.1 (by omega_arith) (by decide))
      (X₃.E _ mp) (ptrEq_local X₃.C₁.S.ws X₃.C₂.S.ws _) true)
    (range_ok X₃.C₁.S.ws (by omega_arith) X.C₁.S.wp (X₃.C₁.inp mp).toReady
      (localReady X₃.C₁.S.ws ho.1 (by omega_arith) (by decide)) true)
    (range_ok X₃.C₂.S.ws (by omega_arith) X.C₁.S.wp (X₃.C₂.inp mp).toReady
      (localReady X₃.C₂.S.ws ho.1 (by omega_arith) (by decide)) true)
    fun _ _ _ _ => SameTrace.block_nil

end VG.Proof.Dsa.Arm
