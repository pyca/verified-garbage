module

import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace
public import VerifiedGarbage.Proof.Dsa.Arm.PublicKey
public import VerifiedGarbage.Proof.Dsa.Arm.CoreTrace
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on 32-bit ARM: the key checks' traces

Two runs of a schedule of operations (`Pair`): each has its schedule and the
caller's operands (`Ctx`), with the same pointers in both. Each operation's
correctness in each run keeps them (`Pair.run`), and its trace is the same
(`ValidateTrace.lean`, `CoreTrace.lean`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest)

/-- One run: its schedule, and the caller's operands `ins` with values `val`. -/
structure Ctx (base : Addr) (size pLen qLen nP nQ : Nat) (ins : List (Pointer × Nat)) (val : Pointer → Nat)
    (s : State) : Prop where
  S : Sched s base size pLen qLen nP nQ
  I : ∀ i ∈ ins, Input s base size i.1 i.2 (val i.1)

theorem Ctx.inp {base : Addr} {size pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)} {val : Pointer → Nat}
    {s : State} (C : Ctx base size pLen qLen nP nQ ins val s) {p : Pointer} {len : Nat} (h : (p, len) ∈ ins) :
    Input s base size p len (val p) :=
  C.I _ h

theorem Ctx.run {base : Addr} {size pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)} {val : Pointer → Nat}
    {s t : State} (C : Ctx base size pLen qLen nP nQ ins val s) (Rn : Run base s t) :
    Ctx base size pLen qLen nP nQ ins val t :=
  ⟨C.S.run Rn, fun i hi => (C.I i hi).run Rn (by have := C.S.big; omega) C.S.fits⟩

/-- Two runs, with the same pointers to the caller's operands. -/
structure Pair (base : Addr) (size₁ size₂ pLen qLen nP nQ : Nat) (ins : List (Pointer × Nat))
    (val₁ val₂ : Pointer → Nat) (s₁ s₂ : State) : Prop where
  C₁ : Ctx base size₁ pLen qLen nP nQ ins val₁ s₁
  C₂ : Ctx base size₂ pLen qLen nP nQ ins val₂ s₂
  E : ∀ i ∈ ins, PtrEq base s₁ s₂ i.1

theorem Pair.run {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ t₁ t₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (Rn₁ : Run base s₁ t₁) (Rn₂ : Run base s₂ t₂) : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ t₁ t₂ := by
  refine ⟨X.C₁.run Rn₁, X.C₂.run Rn₂, fun i hi => ?_⟩
  have hO : ∀ r ∈ runRanges, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1 := by decide
  unfold PtrEq
  rw [pointerValue_keep (Rn₁.rest.gpr .r12 (by decide)) Rn₁.mem hO (X.C₁.I i hi).ok,
    pointerValue_keep (Rn₂.rest.gpr .r12 (by decide)) Rn₂.mem hO (X.C₁.I i hi).ok]
  exact X.E i hi

theorem ptrEq_local {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂)
    (o : Nat) : PtrEq base s₁ s₂ (.local o) := by
  unfold PtrEq
  simp only [pointerValue, Ws.r12_eq h₁ h₂]

/-- The run's operation's hypotheses, for a modulus among its operands. -/
theorem Ctx.opPre {base : Addr} {size pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)} {val : Pointer → Nat}
    {s : State} (C : Ctx base size pLen qLen nP nQ ins val s) {f : Field} {len n : Nat}
    (hf : (.input f, len) ∈ ins) (w : Width len n) (h1 : 1 < val (.input f)) (h2 : val (.input f) % 2 = 1) :
    OpPre s base size len n (val (.input f)) f :=
  ⟨C.S.ws, by have := C.S.big; omega, w, (C.inp hf).toReady, (C.inp hf).value, h1, h2⟩

/-- The usual bounds of a domain. -/
structure DomainOk (P Q : Nat) : Prop where
  hP : 1 < P
  hPo : P % 2 = 1
  hQ : 255 < Q
  hQo : Q % 2 = 1

theorem domain_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Validate.domain pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have f₁ := X.C₁.S.fits
  have f₂ := X.C₂.S.fits
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  simp only [Validate.domain, Core.sequence, List.foldr]
  refine SameTrace.assoc_left (SameTrace.seq (range_trace X.C₁.S.ws X.C₂.S.ws (by omega) (by omega) X.C₁.S.wp
      (X.C₁.inp mp).toReady (X.C₂.inp mp).toReady (X.C₁.inp mg).toReady (X.E _ mp) (X.E _ mg) true)
    (range_ok X.C₁.S.ws (by omega) X.C₁.S.wp (X.C₁.inp mp).toReady (X.C₁.inp mg).toReady true)
    (range_ok X.C₂.S.ws (by omega) X.C₁.S.wp (X.C₂.inp mp).toReady (X.C₂.inp mg).toReady true)
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  have X₁ := X.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  refine SameTrace.seq (range_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega) (by omega) X.C₁.S.wp
      (X₁.C₁.inp mp).toReady (X₁.C₂.inp mp).toReady (X₁.C₁.inp my).toReady (X₁.E _ mp) (X₁.E _ my) true)
    (range_ok X₁.C₁.S.ws (by omega) X.C₁.S.wp (X₁.C₁.inp mp).toReady (X₁.C₁.inp my).toReady true)
    (range_ok X₁.C₂.S.ws (by omega) X.C₁.S.wp (X₁.C₂.inp mp).toReady (X₁.C₂.inp my).toReady true)
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₂ := X₁.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  -- `p - 1`
  refine SameTrace.seq (minus_trace (amount := 1) (output := Impl.Dsa.Layout.t)
      (X₂.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo) (X₂.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X₂.E _ mp))
    (minus_ok (output := Impl.Dsa.Layout.t) X₂.C₁.S.ws (by omega) X.C₁.S.wp (X₂.C₁.inp mp).toReady
      (X₂.C₁.inp mp).value D₁.hP D₁.hPo (by have := D₁.hP; omega) (by decide) (by decide) (by omega) (by decide))
    (minus_ok (output := Impl.Dsa.Layout.t) X₂.C₂.S.ws (by omega) X.C₁.S.wp (X₂.C₂.inp mp).toReady
      (X₂.C₂.inp mp).value D₂.hP D₂.hPo (by have := D₂.hP; omega) (by decide) (by decide) (by omega) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₃ := X₂.run (St₁.run (.inr ⟨by omega, by omega⟩)) (St₂.run (.inr ⟨by omega, by omega⟩))
  -- `(p - 1) mod q`
  refine SameTrace.seq (reduce_trace (output := Impl.Dsa.Layout.u) (count := .imm pLen)
      (X₃.C₁.opPre mq X.C₁.S.wq (by have := D₁.hQ; omega) D₁.hQo)
      (X₃.C₂.opPre mq X.C₁.S.wq (by have := D₂.hQ; omega) D₂.hQo) (show PtrOk (.local Impl.Dsa.Layout.t) from (by decide : Impl.Dsa.Layout.t < 2 ^ 16))
      (show pLen < 2 ^ 16 by omega) (X₃.E _ mq) (ptrEq_local X₃.C₁.S.ws X₃.C₂.S.ws _) rfl
      (localReady X₃.C₁.S.ws (by decide) (by simp only [countValue]; omega) (by decide)) (localReady X₃.C₂.S.ws (by decide) (by simp only [countValue]; omega) (by decide)) D₁.hQ D₂.hQ)
    (reduce_ok (output := Impl.Dsa.Layout.u) X₃.C₁.S.ws (by omega) X.C₁.S.wq (X₃.C₁.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega)
      (localReady X₃.C₁.S.ws (by decide) (by simp only [countValue]; omega) (by decide))
      (X₃.C₁.inp mq).value D₁.hQ D₁.hQo (by decide) (by omega) (by decide))
    (reduce_ok (output := Impl.Dsa.Layout.u) X₃.C₂.S.ws (by omega) X.C₁.S.wq (X₃.C₂.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega)
      (localReady X₃.C₂.S.ws (by decide) (by simp only [countValue]; omega) (by decide))
      (X₃.C₂.inp mq).value D₂.hQ D₂.hQo (by decide) (by omega) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₄ := X₃.run (St₁.run (.inr ⟨by omega, by omega⟩)) (St₂.run (.inr ⟨by omega, by omega⟩))
  -- `q ∣ p - 1`
  refine SameTrace.seq (zero_trace X₄.C₁.S.ws X₄.C₂.S.ws (by omega) (by omega)
      (show PtrOk (.local Impl.Dsa.Layout.u) from (by decide : Impl.Dsa.Layout.u < 2 ^ 16)) (ptrEq_local X₄.C₁.S.ws X₄.C₂.S.ws _) false)
    (zero_ok X₄.C₁.S.ws (by omega) X.C₁.S.wq
      (localReady (len := qLen) X₄.C₁.S.ws (by decide) (by omega) (by decide)) false)
    (zero_ok X₄.C₂.S.ws (by omega) X.C₁.S.wq
      (localReady (len := qLen) X₄.C₂.S.ws (by decide) (by omega) (by decide)) false)
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₅ := X₄.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  -- `q - 2`
  refine SameTrace.seq (minus_trace (amount := 2) (output := Impl.Dsa.Layout.qMinusTwo)
      (X₅.C₁.opPre mq X.C₁.S.wq (by have := D₁.hQ; omega) D₁.hQo)
      (X₅.C₂.opPre mq X.C₁.S.wq (by have := D₂.hQ; omega) D₂.hQo) (X₅.E _ mq))
    (WP.mono (minus_ok (output := Impl.Dsa.Layout.qMinusTwo)
      X₅.C₁.S.ws (by omega) X.C₁.S.wq (X₅.C₁.inp mq).toReady (X₅.C₁.inp mq).value (by have := D₁.hQ; omega) D₁.hQo
      (by have := D₁.hQ; omega) (by decide) (by decide) (by omega) (by decide)) fun _ _ => trivial)
    (WP.mono (minus_ok (output := Impl.Dsa.Layout.qMinusTwo)
      X₅.C₂.S.ws (by omega) X.C₁.S.wq (X₅.C₂.inp mq).toReady (X₅.C₂.inp mq).value (by have := D₂.hQ; omega) D₂.hQo
      (by have := D₂.hQ; omega) (by decide) (by decide) (by omega) (by decide)) fun _ _ => trivial)
    fun _ _ _ _ => SameTrace.block_nil

theorem subgroup_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Validate.subgroup pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have ho : 4960 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by omega
  have pt : PtrOk (.local Impl.Dsa.Layout.t) := (by decide : Impl.Dsa.Layout.t < 2 ^ 16)
  simp only [Validate.subgroup, Core.sequence, List.foldr]
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t) (X.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo)
      (X.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X.C₁.inp mg).toReady (X.C₂.inp mg).toReady (X.C₁.inp mq).toReady
      (X.E _ mp) (X.E _ mg) (X.E _ mq)
      (X.C₂.inp mq).toReady q4 qp qw)
    (power_ok (output := Impl.Dsa.Layout.t) X.C₁.S.ws (by omega) X.C₁.S.wp q4 qp qw (X.C₁.inp mp).toReady
      (X.C₁.inp mg).toReady (X.C₁.inp mq).toReady (X.C₁.inp mp).value D₁.hP D₁.hPo ho.1 (by omega) (by decide))
    (power_ok (output := Impl.Dsa.Layout.t) X.C₂.S.ws (by omega) X.C₁.S.wp q4 qp qw (X.C₂.inp mp).toReady
      (X.C₂.inp mg).toReady (X.C₂.inp mq).toReady (X.C₂.inp mp).value D₂.hP D₂.hPo ho.1 (by omega) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₁ := X.run (St₁.run (.inr ho)) (St₂.run (.inr ho))
  refine SameTrace.seq (isOne_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega) (by omega) pt
      (ptrEq_local X₁.C₁.S.ws X₁.C₂.S.ws _))
    (isOne_ok X₁.C₁.S.ws (by omega) X.C₁.S.wp (localReady X₁.C₁.S.ws ho.1 (by omega) (by decide)))
    (isOne_ok X₁.C₂.S.ws (by omega) X.C₁.S.wp (localReady X₁.C₂.S.ws ho.1 (by omega) (by decide)))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₂ := X₁.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t) (X₂.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo)
      (X₂.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X₂.C₁.inp my).toReady (X₂.C₂.inp my).toReady (X₂.C₁.inp mq).toReady
      (X₂.E _ mp) (X₂.E _ my) (X₂.E _ mq)
      (X₂.C₂.inp mq).toReady q4 qp qw)
    (power_ok (output := Impl.Dsa.Layout.t) X₂.C₁.S.ws (by omega) X.C₁.S.wp q4 qp qw (X₂.C₁.inp mp).toReady
      (X₂.C₁.inp my).toReady (X₂.C₁.inp mq).toReady (X₂.C₁.inp mp).value D₁.hP D₁.hPo ho.1 (by omega) (by decide))
    (power_ok (output := Impl.Dsa.Layout.t) X₂.C₂.S.ws (by omega) X.C₁.S.wp q4 qp qw (X₂.C₂.inp mp).toReady
      (X₂.C₂.inp my).toReady (X₂.C₂.inp mq).toReady (X₂.C₂.inp mp).value D₂.hP D₂.hPo ho.1 (by omega) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₃ := X₂.run (St₁.run (.inr ho)) (St₂.run (.inr ho))
  refine SameTrace.seq (isOne_trace X₃.C₁.S.ws X₃.C₂.S.ws (by omega) (by omega) pt
      (ptrEq_local X₃.C₁.S.ws X₃.C₂.S.ws _))
    (isOne_ok X₃.C₁.S.ws (by omega) X.C₁.S.wp (localReady X₃.C₁.S.ws ho.1 (by omega) (by decide)))
    (isOne_ok X₃.C₂.S.ws (by omega) X.C₁.S.wp (localReady X₃.C₂.S.ws ho.1 (by omega) (by decide)))
    fun _ _ _ _ => SameTrace.block_nil

theorem publicKey_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Validate.publicKey pLen qLen) s₁ s₂ :=
  SameTrace.seq (domain_trace X mp mq mg my D₁ D₂)
    (domain_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my) D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (domain_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my) D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun _ _ ⟨_, _, Rn₁⟩ ⟨_, _, Rn₂⟩ => subgroup_trace (X.run Rn₁ Rn₂) mp mq mg my D₁ D₂

theorem privateKey_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins) (mx : (.input .x, qLen) ∈ ins) (mk : (.input .nonce, qLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Validate.privateKey pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have ho : 4960 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by omega
  simp only [Validate.privateKey, Core.sequence, List.foldr]
  refine SameTrace.assoc_left (SameTrace.seq (range_trace X.C₁.S.ws X.C₂.S.ws (by omega) (by omega) X.C₁.S.wq
      (X.C₁.inp mq).toReady (X.C₂.inp mq).toReady (X.C₁.inp mx).toReady (X.E _ mq) (X.E _ mx) false)
    (range_ok X.C₁.S.ws (by omega) X.C₁.S.wq (X.C₁.inp mq).toReady (X.C₁.inp mx).toReady false)
    (range_ok X.C₂.S.ws (by omega) X.C₁.S.wq (X.C₂.inp mq).toReady (X.C₂.inp mx).toReady false)
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  have X₁ := X.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  refine SameTrace.seq (range_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega) (by omega) X.C₁.S.wq
      (X₁.C₁.inp mq).toReady (X₁.C₂.inp mq).toReady (X₁.C₁.inp mk).toReady (X₁.E _ mq) (X₁.E _ mk) false)
    (range_ok X₁.C₁.S.ws (by omega) X.C₁.S.wq (X₁.C₁.inp mq).toReady (X₁.C₁.inp mk).toReady false)
    (range_ok X₁.C₂.S.ws (by omega) X.C₁.S.wq (X₁.C₂.inp mq).toReady (X₁.C₂.inp mk).toReady false)
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₂ := X₁.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t) (X₂.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo)
      (X₂.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X₂.C₁.inp mg).toReady (X₂.C₂.inp mg).toReady (X₂.C₁.inp mx).toReady
      (X₂.E _ mp) (X₂.E _ mg) (X₂.E _ mx)
      (X₂.C₂.inp mx).toReady q4 qp qw)
    (power_ok (output := Impl.Dsa.Layout.t) X₂.C₁.S.ws (by omega) X.C₁.S.wp q4 qp qw (X₂.C₁.inp mp).toReady
      (X₂.C₁.inp mg).toReady (X₂.C₁.inp mx).toReady (X₂.C₁.inp mp).value D₁.hP D₁.hPo ho.1 (by omega) (by decide))
    (power_ok (output := Impl.Dsa.Layout.t) X₂.C₂.S.ws (by omega) X.C₁.S.wp q4 qp qw (X₂.C₂.inp mp).toReady
      (X₂.C₂.inp mg).toReady (X₂.C₂.inp mx).toReady (X₂.C₂.inp mp).value D₂.hP D₂.hPo ho.1 (by omega) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  have X₃ := X₂.run (St₁.run (.inr ho)) (St₂.run (.inr ho))
  refine SameTrace.seq (equalValues_trace X₃.C₁.S.ws X₃.C₂.S.ws (by omega) (by omega) X.C₁.S.wp
      (localReady X₃.C₁.S.ws ho.1 (by omega) (by decide)) (localReady X₃.C₂.S.ws ho.1 (by omega) (by decide))
      (X₃.C₁.inp my).toReady (ptrEq_local X₃.C₁.S.ws X₃.C₂.S.ws _) (X₃.E _ my))
    (equalValues_ok X₃.C₁.S.ws (by omega) X.C₁.S.wp (localReady X₃.C₁.S.ws ho.1 (by omega) (by decide))
      (X₃.C₁.inp my).toReady)
    (equalValues_ok X₃.C₂.S.ws (by omega) X.C₁.S.wp (localReady X₃.C₂.S.ws ho.1 (by omega) (by decide))
      (X₃.C₂.inp my).toReady)
    fun _ _ _ _ => SameTrace.block_nil

end VG.Proof.Dsa.Arm
