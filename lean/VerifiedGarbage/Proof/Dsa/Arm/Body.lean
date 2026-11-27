module

import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.ValidateOps
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.Arm.SignVerify
public import VerifiedGarbage.Proof.Dsa.Arm.PublicKey
public import VerifiedGarbage.Impl.Dsa.Arm.PublicValidation
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace

/-! ### `Dsa.Arm.Compute`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.SigningKey`, which this module and modules that import it used -/

section

/-! # Signing reuses the private/public consistency equation

The generator's subgroup equation and g^x = y imply y's subgroup equation,
even for composite domain integers. The signer therefore needs one public
subgroup exponentiation; verification still checks both independently.
-/

@[expose] public section
namespace VG.Proof.Dsa.Arm
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)

variable {umaal : Bool}

def signingPublicChecks (P Q G Y : Nat) : Prop :=
  ((1 < G ∧ G < P) ∧ (1 < Y ∧ Y < P)) ∧ (P - 1) % Q = 0 ∧ G ^ Q % P = 1

instance (P Q G Y : Nat) : Decidable (signingPublicChecks P Q G Y) := by
  unfold signingPublicChecks
  infer_instance

theorem public_subgroup_of_consistency {P Q G Y X : Nat} (hp : 1 < P)
    (hg : G ^ Q % P = 1) (he : G ^ X % P = Y) : Y ^ Q % P = 1 := by
  rw [← he, ← Nat.pow_mod, ← Nat.pow_mul, Nat.mul_comm X Q, Nat.pow_mul, Nat.pow_mod, hg]
  simp [Nat.mod_eq_of_lt hp]

theorem signingPublicChecks_consistent {P Q G Y X : Nat} {A : Prop} (hp : 1 < P) :
    (signingPublicChecks P Q G Y ∧ A ∧ G ^ X % P = Y) ↔
      (publicChecks P Q G Y ∧ A ∧ G ^ X % P = Y) := by
  constructor
  · rintro ⟨⟨hr, hd, hg⟩, ha, he⟩
    exact ⟨⟨hr, hd, hg, public_subgroup_of_consistency hp hg he⟩, ha, he⟩
  · rintro ⟨⟨hr, hd, hg, _⟩, ha, he⟩
    exact ⟨⟨hr, hd, hg⟩, ha, he⟩

theorem signingSubgroup_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (hP : 1 < P) (hPo : P % 2 = 1) :
    WP isa (Validate.signingSubgroup umaal pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (G ^ Q % P = 1) ∧
      KeepsLocals base s t scalars.1 scalars.2 ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have Plt := operand_lt_of Ip
  have ho : 12016 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.t]; omega_arith
  have ht : Impl.Dsa.Layout.t + pLen < size := by omega_arith
  unfold Validate.signingSubgroup
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S.ws (by omega_arith) S.wp q4 qp qw Ip.toReady
    Ig.toReady Iq.toReady Ip.value hP hPo ho.1 (by omega_arith) (by decide)) fun v₁ ⟨B₁, St₁⟩ => ?_)
  rw [Ig.value, Iq.value] at B₁
  have S₁ := S.stage St₁
  refine WP.mono (isOne_ok S₁.ws (by omega_arith) S.wp (localReady S₁.ws ho.1 ht (by decide)))
    fun v₂ ⟨F₂, St₂⟩ => ⟨?_, ?_, ?_⟩
  · rw [local_operand S₁.ws (by omega_arith), localVal_of_bytes B₁ (Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Plt)] at F₂
    rw [F₂, St₁.maskW (by decide)]
  · exact (St₁.keepsScalars (by omega_arith) (by simp only [Impl.Dsa.Layout.t]; omega_arith)).trans
      (St₂.keepsScalars (by decide) (by decide))
  · exact (St₁.run (.inr ho)).trans (St₂.run (.inl ⟨rfl, rfl⟩))

theorem signingKey_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Validate.signingKey umaal pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (signingPublicChecks P Q G Y) ∧
      localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 ∧ Run base s t := by
  have big := S.big
  have fits := S.fits
  unfold Validate.signingKey
  refine WP.seq (WP.mono (domain_ok S Ip Iq Ig Iy hP hPo hQ hQo) fun u ⟨Fu, Lu, Ru⟩ =>
    WP.mono (signingSubgroup_ok (S.run Ru) (Ip.run Ru (by omega_arith) fits) (Iq.run Ru (by omega_arith) fits)
      (Ig.run Ru (by omega_arith) fits) hP hPo) fun t ⟨Ft, Kt, Rt⟩ => ?_)
  have L : localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [Kt _ _ (by decide) (by simp only [Impl.Dsa.Layout.qMinusTwo, Impl.Dsa.Layout.t]; have := S.q32; omega_arith)]
    exact Lu
  refine ⟨?_, L, Ru.toRun.trans Rt⟩
  rw [Ft, Fu, BitVec.and_assoc, mask32_and]
  exact congrArg _ (mask32_iff (by simp only [signingPublicChecks, and_assoc]))

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.KeyTrace`, which this module and modules that import it used -/

section

/-!
# DSA on 32-bit ARM: the key checks' traces

Two runs of a schedule of operations (`Pair`): each has its schedule and the
caller's operands (`Ctx`), with the same pointers and moduli in both. Each operation's
correctness in each run keeps them (`Pair.run`), and its trace is the same
(`ValidateTrace.lean`, `CoreTrace.lean`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest)

variable {umaal : Bool}

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
  ⟨C.S.run Rn, fun i hi => (C.I i hi).run Rn (by have := C.S.big; omega_arith) C.S.fits⟩

/-- Two runs, with the same pointers to the caller's operands, and the same
moduli p and q: they are public, and bits of each choose how its Montgomery
context is set up (`Context.body_trace`). -/
structure Pair (base : Addr) (size₁ size₂ pLen qLen nP nQ : Nat) (ins : List (Pointer × Nat))
    (val₁ val₂ : Pointer → Nat) (s₁ s₂ : State) : Prop where
  C₁ : Ctx base size₁ pLen qLen nP nQ ins val₁ s₁
  C₂ : Ctx base size₂ pLen qLen nP nQ ins val₂ s₂
  E : ∀ i ∈ ins, PtrEq base s₁ s₂ i.1
  P : val₁ (.input .p) = val₂ (.input .p)
  Q : val₁ (.input .q) = val₂ (.input .q)

theorem Pair.run {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ t₁ t₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (Rn₁ : Run base s₁ t₁) (Rn₂ : Run base s₂ t₂) : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ t₁ t₂ := by
  refine ⟨X.C₁.run Rn₁, X.C₂.run Rn₂, fun i hi => ?_, X.P, X.Q⟩
  obtain hO : ∀ r ∈ runRanges, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1 := by decide
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
  ⟨C.S.ws, by have := C.S.big; omega_arith, w, (C.inp hf).toReady, (C.inp hf).value, h1, h2⟩

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
  refine SameTrace.assoc_left (SameTrace.seq (range_trace X.C₁.S.ws X.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wp
      (X.C₁.inp mp).toReady (X.C₂.inp mp).toReady (X.C₁.inp mg).toReady (X.E _ mp) (X.E _ mg) true)
    (range_ok X.C₁.S.ws (by omega_arith) X.C₁.S.wp (X.C₁.inp mp).toReady (X.C₁.inp mg).toReady true)
    (range_ok X.C₂.S.ws (by omega_arith) X.C₁.S.wp (X.C₂.inp mp).toReady (X.C₂.inp mg).toReady true)
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  obtain X₁ := X.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  refine SameTrace.seq (range_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wp
      (X₁.C₁.inp mp).toReady (X₁.C₂.inp mp).toReady (X₁.C₁.inp my).toReady (X₁.E _ mp) (X₁.E _ my) true)
    (range_ok X₁.C₁.S.ws (by omega_arith) X.C₁.S.wp (X₁.C₁.inp mp).toReady (X₁.C₁.inp my).toReady true)
    (range_ok X₁.C₂.S.ws (by omega_arith) X.C₁.S.wp (X₁.C₂.inp mp).toReady (X₁.C₂.inp my).toReady true)
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain X₂ := X₁.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  -- `p - 1`
  refine SameTrace.seq (minus_trace (amount := 1) (output := Impl.Dsa.Layout.t)
      (X₂.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo) (X₂.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X₂.E _ mp))
    (minus_ok (output := Impl.Dsa.Layout.t) X₂.C₁.S.ws (by omega_arith) X.C₁.S.wp (X₂.C₁.inp mp).toReady
      (X₂.C₁.inp mp).value D₁.hP D₁.hPo (by have := D₁.hP; omega_arith) (by decide) (by decide) (by omega_arith) (by decide))
    (minus_ok (output := Impl.Dsa.Layout.t) X₂.C₂.S.ws (by omega_arith) X.C₁.S.wp (X₂.C₂.inp mp).toReady
      (X₂.C₂.inp mp).value D₂.hP D₂.hPo (by have := D₂.hP; omega_arith) (by decide) (by decide) (by omega_arith) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain X₃ := X₂.run (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)) (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  -- `(p - 1) mod q`
  refine SameTrace.seq (reduce_trace (output := Impl.Dsa.Layout.u) (count := .imm pLen)
      (X₃.C₁.opPre mq X.C₁.S.wq (by have := D₁.hQ; omega_arith) D₁.hQo)
      (X₃.C₂.opPre mq X.C₁.S.wq (by have := D₂.hQ; omega_arith) D₂.hQo) (show PtrOk (.local Impl.Dsa.Layout.t) from (by decide : Impl.Dsa.Layout.t < 2 ^ 16))
      (show pLen < 2 ^ 16 by omega_arith) (X₃.E _ mq) (ptrEq_local X₃.C₁.S.ws X₃.C₂.S.ws _) rfl
      (localReady X₃.C₁.S.ws (by decide) (by simp only [countValue]; omega_arith) (by decide)) (localReady X₃.C₂.S.ws (by decide) (by simp only [countValue]; omega_arith) (by decide)) D₁.hQ D₂.hQ)
    (reduce_ok (output := Impl.Dsa.Layout.u) X₃.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₃.C₁.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
      (localReady X₃.C₁.S.ws (by decide) (by simp only [countValue]; omega_arith) (by decide))
      (X₃.C₁.inp mq).value D₁.hQ D₁.hQo (by decide) (by omega_arith) (by decide))
    (reduce_ok (output := Impl.Dsa.Layout.u) X₃.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₃.C₂.inp mq).toReady
      (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
      (localReady X₃.C₂.S.ws (by decide) (by simp only [countValue]; omega_arith) (by decide))
      (X₃.C₂.inp mq).value D₂.hQ D₂.hQo (by decide) (by omega_arith) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain X₄ := X₃.run (St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)) (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))
  -- `q ∣ p - 1`
  refine SameTrace.seq (zero_trace X₄.C₁.S.ws X₄.C₂.S.ws (by omega_arith) (by omega_arith)
      (show PtrOk (.local Impl.Dsa.Layout.u) from (by decide : Impl.Dsa.Layout.u < 2 ^ 16)) (ptrEq_local X₄.C₁.S.ws X₄.C₂.S.ws _) false)
    (zero_ok X₄.C₁.S.ws (by omega_arith) X.C₁.S.wq
      (localReady (len := qLen) X₄.C₁.S.ws (by decide) (by omega_arith) (by decide)) false)
    (zero_ok X₄.C₂.S.ws (by omega_arith) X.C₁.S.wq
      (localReady (len := qLen) X₄.C₂.S.ws (by decide) (by omega_arith) (by decide)) false)
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain X₅ := X₄.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  -- `q - 2`
  refine SameTrace.seq (minus_trace (amount := 2) (output := Impl.Dsa.Layout.qMinusTwo)
      (X₅.C₁.opPre mq X.C₁.S.wq (by have := D₁.hQ; omega_arith) D₁.hQo)
      (X₅.C₂.opPre mq X.C₁.S.wq (by have := D₂.hQ; omega_arith) D₂.hQo) (X₅.E _ mq))
    (WP.mono (minus_ok (output := Impl.Dsa.Layout.qMinusTwo)
      X₅.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₅.C₁.inp mq).toReady (X₅.C₁.inp mq).value (by have := D₁.hQ; omega_arith) D₁.hQo
      (by have := D₁.hQ; omega_arith) (by decide) (by decide) (by omega_arith) (by decide)) fun _ _ => trivial)
    (WP.mono (minus_ok (output := Impl.Dsa.Layout.qMinusTwo)
      X₅.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₅.C₂.inp mq).toReady (X₅.C₂.inp mq).value (by have := D₂.hQ; omega_arith) D₂.hQo
      (by have := D₂.hQ; omega_arith) (by decide) (by decide) (by omega_arith) (by decide)) fun _ _ => trivial)
    fun _ _ _ _ => SameTrace.block_nil

theorem subgroup_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Validate.subgroup umaal pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  obtain ho : 12016 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by omega_arith
  obtain pt : PtrOk (.local Impl.Dsa.Layout.t) := (by decide : Impl.Dsa.Layout.t < 2 ^ 16)
  simp only [Validate.subgroup, Core.sequence, List.foldr]
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t) (X.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo)
      (X.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X.C₁.inp mg).toReady (X.C₂.inp mg).toReady (X.C₁.inp mq).toReady
      (X.E _ mp) (X.E _ mg) (X.E _ mq)
      (X.C₂.inp mq).toReady q4 qp qw X.P)
    (power_ok (output := Impl.Dsa.Layout.t) X.C₁.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X.C₁.inp mp).toReady
      (X.C₁.inp mg).toReady (X.C₁.inp mq).toReady (X.C₁.inp mp).value D₁.hP D₁.hPo ho.1 (by omega_arith) (by decide))
    (power_ok (output := Impl.Dsa.Layout.t) X.C₂.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X.C₂.inp mp).toReady
      (X.C₂.inp mg).toReady (X.C₂.inp mq).toReady (X.C₂.inp mp).value D₂.hP D₂.hPo ho.1 (by omega_arith) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain X₁ := X.run (St₁.run (.inr ho)) (St₂.run (.inr ho))
  refine SameTrace.seq (isOne_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega_arith) (by omega_arith) pt
      (ptrEq_local X₁.C₁.S.ws X₁.C₂.S.ws _))
    (isOne_ok X₁.C₁.S.ws (by omega_arith) X.C₁.S.wp (localReady X₁.C₁.S.ws ho.1 (by omega_arith) (by decide)))
    (isOne_ok X₁.C₂.S.ws (by omega_arith) X.C₁.S.wp (localReady X₁.C₂.S.ws ho.1 (by omega_arith) (by decide)))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain X₂ := X₁.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t) (X₂.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo)
      (X₂.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X₂.C₁.inp my).toReady (X₂.C₂.inp my).toReady (X₂.C₁.inp mq).toReady
      (X₂.E _ mp) (X₂.E _ my) (X₂.E _ mq)
      (X₂.C₂.inp mq).toReady q4 qp qw X.P)
    (power_ok (output := Impl.Dsa.Layout.t) X₂.C₁.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X₂.C₁.inp mp).toReady
      (X₂.C₁.inp my).toReady (X₂.C₁.inp mq).toReady (X₂.C₁.inp mp).value D₁.hP D₁.hPo ho.1 (by omega_arith) (by decide))
    (power_ok (output := Impl.Dsa.Layout.t) X₂.C₂.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X₂.C₂.inp mp).toReady
      (X₂.C₂.inp my).toReady (X₂.C₂.inp mq).toReady (X₂.C₂.inp mp).value D₂.hP D₂.hPo ho.1 (by omega_arith) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain X₃ := X₂.run (St₁.run (.inr ho)) (St₂.run (.inr ho))
  refine SameTrace.seq (isOne_trace X₃.C₁.S.ws X₃.C₂.S.ws (by omega_arith) (by omega_arith) pt
      (ptrEq_local X₃.C₁.S.ws X₃.C₂.S.ws _))
    (isOne_ok X₃.C₁.S.ws (by omega_arith) X.C₁.S.wp (localReady X₃.C₁.S.ws ho.1 (by omega_arith) (by decide)))
    (isOne_ok X₃.C₂.S.ws (by omega_arith) X.C₁.S.wp (localReady X₃.C₂.S.ws ho.1 (by omega_arith) (by decide)))
    fun _ _ _ _ => SameTrace.block_nil

theorem publicKey_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Validate.publicKey umaal pLen qLen) s₁ s₂ :=
  SameTrace.seq (domain_trace X mp mq mg my D₁ D₂)
    (domain_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my) D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (domain_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my) D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun _ _ ⟨_, _, Rn₁⟩ ⟨_, _, Rn₂⟩ => subgroup_trace (X.run Rn₁ Rn₂) mp mq mg my D₁ D₂

theorem privateKey_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins) (mx : (.input .x, qLen) ∈ ins) (mk : (.input .nonce, qLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Validate.privateKey umaal pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  obtain ho : 12016 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by omega_arith
  simp only [Validate.privateKey, Core.sequence, List.foldr]
  refine SameTrace.assoc_left (SameTrace.seq (range_trace X.C₁.S.ws X.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wq
      (X.C₁.inp mq).toReady (X.C₂.inp mq).toReady (X.C₁.inp mx).toReady (X.E _ mq) (X.E _ mx) false)
    (range_ok X.C₁.S.ws (by omega_arith) X.C₁.S.wq (X.C₁.inp mq).toReady (X.C₁.inp mx).toReady false)
    (range_ok X.C₂.S.ws (by omega_arith) X.C₁.S.wq (X.C₂.inp mq).toReady (X.C₂.inp mx).toReady false)
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  obtain X₁ := X.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  refine SameTrace.seq (range_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wq
      (X₁.C₁.inp mq).toReady (X₁.C₂.inp mq).toReady (X₁.C₁.inp mk).toReady (X₁.E _ mq) (X₁.E _ mk) false)
    (range_ok X₁.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₁.C₁.inp mq).toReady (X₁.C₁.inp mk).toReady false)
    (range_ok X₁.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₁.C₂.inp mq).toReady (X₁.C₂.inp mk).toReady false)
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain X₂ := X₁.run (St₁.run (.inl ⟨rfl, rfl⟩)) (St₂.run (.inl ⟨rfl, rfl⟩))
  refine SameTrace.seq (power_trace (output := Impl.Dsa.Layout.t) (X₂.C₁.opPre mp X.C₁.S.wp D₁.hP D₁.hPo)
      (X₂.C₂.opPre mp X.C₁.S.wp D₂.hP D₂.hPo) (X₂.C₁.inp mg).toReady (X₂.C₂.inp mg).toReady (X₂.C₁.inp mx).toReady
      (X₂.E _ mp) (X₂.E _ mg) (X₂.E _ mx)
      (X₂.C₂.inp mx).toReady q4 qp qw X.P)
    (power_ok (output := Impl.Dsa.Layout.t) X₂.C₁.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X₂.C₁.inp mp).toReady
      (X₂.C₁.inp mg).toReady (X₂.C₁.inp mx).toReady (X₂.C₁.inp mp).value D₁.hP D₁.hPo ho.1 (by omega_arith) (by decide))
    (power_ok (output := Impl.Dsa.Layout.t) X₂.C₂.S.ws (by omega_arith) X.C₁.S.wp q4 qp qw (X₂.C₂.inp mp).toReady
      (X₂.C₂.inp mg).toReady (X₂.C₂.inp mx).toReady (X₂.C₂.inp mp).value D₂.hP D₂.hPo ho.1 (by omega_arith) (by decide))
    fun v₁ v₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_
  obtain X₃ := X₂.run (St₁.run (.inr ho)) (St₂.run (.inr ho))
  refine SameTrace.seq (equalValues_trace X₃.C₁.S.ws X₃.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wp
      (localReady X₃.C₁.S.ws ho.1 (by omega_arith) (by decide)) (localReady X₃.C₂.S.ws ho.1 (by omega_arith) (by decide))
      (X₃.C₁.inp my).toReady (ptrEq_local X₃.C₁.S.ws X₃.C₂.S.ws _) (X₃.E _ my))
    (equalValues_ok X₃.C₁.S.ws (by omega_arith) X.C₁.S.wp (localReady X₃.C₁.S.ws ho.1 (by omega_arith) (by decide))
      (X₃.C₁.inp my).toReady)
    (equalValues_ok X₃.C₂.S.ws (by omega_arith) X.C₁.S.wp (localReady X₃.C₂.S.ws ho.1 (by omega_arith) (by decide))
      (X₃.C₂.inp my).toReady)
    fun _ _ _ _ => SameTrace.block_nil

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.Sign`, which this module and modules that import it used -/

section

/-!
# DSA on 32-bit ARM: the signature's arithmetic

`sign_ok`: `r = (g^k mod p) mod q` and
`s = k^(q-2) ((z mod q + x r mod q) mod q) mod q` for the value `z` of the
digest's saved prefix, from `q - 2` stored by the domain's check.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)

variable {umaal : Bool}

theorem countValue_stage {base : Addr} {s t : State} {o l : Nat} (St : Stage base s t o l) (ho : 116 ≤ o) :
    countValue base t Core.digestPrefix = countValue base s Core.digestPrefix :=
  countValue_keep St.mem (fun r hr => by
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) (by simp only [CountOk, Core.digestPrefix]; decide)

/-- The value of the first scalar. -/
abbrev rValue (P Q G K : Nat) : Nat := G ^ K % P % Q

/-- The value of the second. -/
abbrev sValue (P Q G X K D : Nat) : Nat := K ^ (Q - 2) % Q * ((D % Q + X * rValue P Q G K % Q) % Q) % Q

theorem sign_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G X K D c : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Ix : Input s base size (.input .x) qLen X)
    (Ik : Input s base size (.input .nonce) qLen K) (Id : Input s base size (.input .digest) c D)
    (hc : countValue base s Core.digestPrefix = c)
    (hq2 : localVal base s Impl.Dsa.Layout.qMinusTwo qLen = Q - 2)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Core.sign umaal pLen qLen) s fun t =>
      localVal base t Impl.Dsa.Layout.r qLen = rValue P Q G K ∧
      localVal base t Impl.Dsa.Layout.s qLen = sValue P Q G X K D ∧
      maskW base t = maskW base s ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have fits := S.fits
  obtain Plt := operand_lt_of Ip
  obtain Qlt := operand_lt_of Iq
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  have Li : Impl.Dsa.Layout.inverse = 14784 := rfl
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  have Lv : Impl.Dsa.Layout.v = 14848 := rfl
  have Lz : Impl.Dsa.Layout.z = 14880 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  obtain qlt : ∀ x, x % Q < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Qlt
  simp only [Core.sign, Core.signStart, Core.signFinish, Core.sequence, List.foldr]
  -- `t = g^k mod p`
  refine WP.seq (WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S.ws (by omega_arith) S.wp q4 qp qw Ip.toReady
    Ig.toReady Ik.toReady Ip.value hP hPo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₁ ⟨B₁, St₁⟩ => ?_))
  rw [Ig.value, Ik.value] at B₁
  obtain S₁ := S.stage St₁
  obtain n₁ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₁ base size p len v :=
    fun I => I.next S St₁ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain T₁ : localVal base v₁ Impl.Dsa.Layout.t pLen = G ^ K % P :=
    localVal_of_bytes B₁ (Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Plt)
  -- `r = t mod q`
  refine WP.seq (WP.mono (reduce_ok (output := Impl.Dsa.Layout.r) S₁.ws (by omega_arith) S.wq (n₁ Iq).toReady
    (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
    (localReady (o := Impl.Dsa.Layout.t) S₁.ws (by omega_arith) (by simp only [countValue]; omega_arith) (by omega_arith))
    (n₁ Iq).value hQ hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₂ ⟨B₂, St₂⟩ => ?_)
  rw [countValue, local_operand S₁.ws (by omega_arith), T₁] at B₂
  obtain S₂ := S₁.stage St₂
  obtain n₂ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₂ base size p len v :=
    fun I => (n₁ I).next S₁ St₂ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain R₂ : localVal base v₂ Impl.Dsa.Layout.r qLen = rValue P Q G K := localVal_of_bytes B₂ (qlt _)
  obtain M₂ : localVal base v₂ Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [St₂.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      St₁.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), hq2]
  -- `k^(q-2) mod q`
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.inverse) S₂.ws (by omega_arith) S.wq q4 (Nat.le_refl _) qw
    (n₂ Iq).toReady (n₂ Ik).toReady (localReady (o := Impl.Dsa.Layout.qMinusTwo) S₂.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₂ Iq).value
    (by omega_arith) hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₃ ⟨B₃, St₃⟩ => ?_)
  rw [(n₂ Ik).value, local_operand S₂.ws (by omega_arith), M₂] at B₃
  obtain S₃ := S₂.stage St₃
  obtain n₃ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₃ base size p len v :=
    fun I => (n₂ I).next S₂ St₃ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain I₃ : localVal base v₃ Impl.Dsa.Layout.inverse qLen = K ^ (Q - 2) % Q := localVal_of_bytes B₃ (qlt _)
  obtain R₃ : localVal base v₃ Impl.Dsa.Layout.r qLen = rValue P Q G K := by
    rw [St₃.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), R₂]
  -- `u = x r mod q`
  refine WP.block_nil ?_
  refine WP.seq (WP.mono (productMod_ok (output := Impl.Dsa.Layout.u) S₃.ws (by omega_arith) S.wq (n₃ Iq).toReady
    (n₃ Ix).toReady (localReady (o := Impl.Dsa.Layout.r) S₃.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₃ Iq).value (by omega_arith) hQo
    (by omega_arith) (by omega_arith) (by omega_arith)) fun v₄ ⟨B₄, St₄⟩ => ?_)
  rw [(n₃ Ix).value, local_operand S₃.ws (by omega_arith), R₃] at B₄
  obtain S₄ := S₃.stage St₄
  obtain n₄ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₄ base size p len v :=
    fun I => (n₃ I).next S₃ St₄ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain U₄ : localVal base v₄ Impl.Dsa.Layout.u qLen = X * rValue P Q G K % Q := localVal_of_bytes B₄ (qlt _)
  -- `z = digest mod q`
  obtain C₃ : countValue base v₄ Core.digestPrefix = c := by
    rw [countValue_stage St₄ (by omega_arith), countValue_stage St₃ (by omega_arith), countValue_stage St₂ (by omega_arith),
      countValue_stage St₁ (by omega_arith), hc]
  obtain Id₄ := n₄ Id
  rw [← C₃] at Id₄
  refine WP.seq (WP.mono (reduce_ok (output := Impl.Dsa.Layout.z) S₄.ws (by omega_arith) S.wq (n₄ Iq).toReady
    (by simp only [CountOk, Core.digestPrefix]; decide) Id₄.toReady (n₄ Iq).value hQ hQo (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₅ ⟨B₅, St₅⟩ => ?_)
  rw [Id₄.value] at B₅
  obtain S₅ := S₄.stage St₅
  obtain n₅ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₅ base size p len v :=
    fun I => (n₄ I).next S₄ St₅ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain Z₅ : localVal base v₅ Impl.Dsa.Layout.z qLen = D % Q := localVal_of_bytes B₅ (qlt _)
  obtain U₅ : localVal base v₅ Impl.Dsa.Layout.u qLen = X * rValue P Q G K % Q := by
    rw [St₅.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), U₄]
  -- `v = z + u mod q`
  refine WP.seq (WP.mono (sum_ok (output := Impl.Dsa.Layout.v) S₅.ws (by omega_arith) S.wq (n₅ Iq).toReady
    (localReady (o := Impl.Dsa.Layout.z) S₅.ws (by omega_arith) (by omega_arith) (by omega_arith)) (localReady (o := Impl.Dsa.Layout.u) S₅.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (n₅ Iq).value (by omega_arith) hQo (by rw [local_operand S₅.ws (by omega_arith), Z₅]; exact Nat.mod_lt _ (by omega_arith))
    (by rw [local_operand S₅.ws (by omega_arith), U₅]; exact Nat.mod_lt _ (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₆ ⟨B₆, St₆⟩ => ?_)
  rw [local_operand S₅.ws (by omega_arith), local_operand S₅.ws (by omega_arith), Z₅, U₅] at B₆
  obtain S₆ := S₅.stage St₆
  obtain n₆ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₆ base size p len v :=
    fun I => (n₅ I).next S₅ St₆ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain V₆ : localVal base v₆ Impl.Dsa.Layout.v qLen = (D % Q + X * rValue P Q G K % Q) % Q :=
    localVal_of_bytes B₆ (qlt _)
  obtain I₆ : localVal base v₆ Impl.Dsa.Layout.inverse qLen = K ^ (Q - 2) % Q := by
    rw [St₆.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), St₅.localVal_eq (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith), St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), I₃]
  -- `s = k^(q-2) v mod q`
  refine WP.seq (WP.mono (productMod_ok (output := Impl.Dsa.Layout.s) S₆.ws (by omega_arith) S.wq (n₆ Iq).toReady
    (localReady (o := Impl.Dsa.Layout.inverse) S₆.ws (by omega_arith) (by omega_arith) (by omega_arith)) (localReady (o := Impl.Dsa.Layout.v) S₆.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (n₆ Iq).value (by omega_arith) hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₇ ⟨B₇, St₇⟩ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩)
  · rw [St₇.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), St₆.localVal_eq (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith), St₅.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      St₃.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), R₂]
  · rw [local_operand S₆.ws (by omega_arith), local_operand S₆.ws (by omega_arith), I₆, V₆] at B₇
    exact localVal_of_bytes B₇ (qlt _)
  · rw [St₇.maskW (by omega_arith), St₆.maskW (by omega_arith), St₅.maskW (by omega_arith), St₄.maskW (by omega_arith),
      St₃.maskW (by omega_arith), St₂.maskW (by omega_arith), St₁.maskW (by omega_arith)]
  · exact ((((((St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)).trans (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans
      (St₃.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans (St₄.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans
      (St₅.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans (St₆.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans
      (St₇.run (.inr ⟨by omega_arith, by omega_arith⟩))

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.PublicValidationCall`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.PublicValidationBody`, which only this module used -/

section

/-! # Register saves around shared ARM public-key validation -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.PublicValidation
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.PublicValidation
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

variable {umaal : Bool}

theorem slots_fit {size : Nat} (hz : 204 ≤ size) : Pow.Fit size slots := by
  intro x hx
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by omega_using [hz]⟩

theorem slots_words : ∀ r ∈ Pow.words slots, 168 ≤ r.1 ∧ r.1 + r.2 ≤ 204 := by decide

theorem input_mem {s t : State} {base : Addr} {size len v : Nat} {f : Impl.Dsa.Layout.Field}
    (I : Input s base size (.input f) len v) (M : t.mem = s.mem) (R : t.rd = s.rd) (W : t.wr = s.wr) :
    Input t base size (.input f) len v := by
  have P : pointerValue base t (.input f) = pointerValue base s (.input f) := by simp only [pointerValue, M]
  exact ⟨⟨I.ok, by rw [P]; exact I.fits, by rw [P, R, W]; exact I.reads,
    by rw [P]; exact I.apart⟩, by rw [P]; exact I.outside, by rw [operand, P, M]; exact I.value⟩

theorem input_stores {s t : State} {base : Addr} {size len v : Nat} {p : Impl.Dsa.Layout.Pointer}
    (I : Input s base size p len v) (R : Rest [] s t) (O : Outs base (Pow.words slots) s.mem t.mem) :
    Input t base size p len v := by
  have H : ∀ r ∈ Pow.words slots, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1 := by decide
  have P := pointerValue_keep (R.gpr .r12 (by decide)) O H I.ok
  refine ⟨I.toReady.keep_rest R (O := O) (hO := H), by rw [P]; exact I.outside, ?_⟩
  rw [operand, P, I.toReady.bytes O (by decide)]
  exact I.value

theorem words_scratch : ∀ r ∈ Pow.words slots,
    ∃ r' ∈ scratch, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := by
  intro r hr
  have H := slots_words r hr
  exact ⟨(168, 36), by simp [scratch], by omega_using [H], by omega_using [H]⟩

theorem run_scratch : ∀ r ∈ runRanges,
    ∃ r' ∈ scratch, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩

theorem body_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y : Nat}
    (E : Pow.Entry s base size) (big : 15712 < size)
    (wp : Width pLen nP) (wq : Width qLen nQ) (qp : qLen ≤ pLen) (q32 : qLen ≤ 32)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (body umaal pLen qLen) s fun t =>
      maskW base t = maskW base s &&& VG.Proof.Ecdsa.Arm.mask32 (publicChecks P Q G Y) ∧
      localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 ∧
      Outs base scratch s.mem t.mem ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold body save
  refine WP.seq (wp_mov (op2_reg s .r0) fun s₁ U => ?_)
  have W₁ : Ws s₁ base size := ⟨by rw [U.gpr]; exact E.wb, U.wr ▸ E.wr, E.nowrap⟩
  refine WP.mono (Pow.stores_ok slots W₁ (slots_fit (by omega_using [big])) (by unfold Pow.Apart; decide)) fun s₂ ⟨Saved, O, R⟩ => ?_
  have S₂ : Sched s₂ base size pLen qLen nP nQ := ⟨W₁.of_rest R (by decide), big, wp, wq, qp, q32⟩
  refine WP.seq (WP.mono (publicKey_ok S₂
    (input_stores (input_mem Ip U.mem U.rd U.wr) R O)
    (input_stores (input_mem Iq U.mem U.rd U.wr) R O)
    (input_stores (input_mem Ig U.mem U.rd U.wr) R O)
    (input_stores (input_mem Iy U.mem U.rd U.wr) R O) hP hPo hQ hQo) fun s₃ ⟨F, V, Run⟩ => ?_)
  refine WP.mono (Pow.loads_ok slots (Run.ws S₂.ws) (slots_fit (by omega_using [big])) (by decide) (by decide))
    fun t ⟨L, R₄, M⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have K := maskW_keep O (by
      intro r hr
      have H := slots_words r hr
      exact .inr (by omega_using [H]))
    rw [show maskW base t = maskW base s₃ from congrArg (fun m => m.readW (off base 116) 32) M,
      F, K]
    rw [show maskW base s₁ = maskW base s from congrArg (fun m => m.readW (off base 116) 32) U.mem]
  · rw [localVal, M]; exact V
  · rw [M, ← U.mem]
    exact (Pow.outs_within O words_scratch).trans (Pow.outs_within Run.mem run_scratch)
  · intro r hr
    have hr' : r ∈ slots.map (·.1) := hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr'
    have H := slots_words _ (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
    rw [L x hx, Run.saved x.2 (by omega) (by omega), Saved x hx, U.other _ (by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  · rw [R₄.sp, Run.rest.sp, R.sp, U.sp]
  · rw [R₄.rd, Run.rest.rd, R.rd, U.rd]
  · rw [R₄.wr, Run.rest.wr, R.wr, U.wr]

end VG.Proof.Dsa.Arm.PublicValidation

end

end

/-! ### `Dsa.Arm.PublicValidationTrace`, which only this module used -/

section

/-! # Constant-time traces of the callable public-key checks -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.PublicValidation
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.PublicValidation
open VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (wp_mov op2_reg)

variable {umaal : Bool}

theorem save_ok {s : State} {base : Addr} {size : Nat}
    (E : Pow.Entry s base size) (big : 204 ≤ size) :
    WP isa (.block save) s fun t => Ws t base size ∧
      (∀ f, f ≠ Field.mask → pointerValue base t (.input f) = pointerValue base s (.input f)) ∧
      (∀ f len v, Input s base size (.input f) len v → Input t base size (.input f) len v) := by
  unfold save
  refine wp_mov (op2_reg s .r0) fun s₁ U => ?_
  have W : Ws s₁ base size := ⟨by rw [U.gpr]; exact E.wb, U.wr ▸ E.wr, E.nowrap⟩
  refine WP.mono (Pow.stores_ok slots W (slots_fit big) (by unfold Pow.Apart; decide)) fun t ⟨_, O, R⟩ => ?_
  refine ⟨W.of_rest R (by decide), ?_, fun f len v I => input_stores (input_mem I U.mem U.rd U.wr) R O⟩
  intro f hf
  rw [pointerValue_keep (p := .input f) (R.gpr .r12 (by decide)) O (by decide) hf]
  simp only [pointerValue, U.mem]

def inputs (pLen qLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .y, pLen)]

theorem body_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat}
    {val₁ val₂ : Pointer → Nat}
    (E₁ : Pow.Entry s₁ base size₁) (E₂ : Pow.Entry s₂ base size₂)
    (b₁ : 15712 < size₁) (b₂ : 15712 < size₂)
    (wp : Width pLen nP) (wq : Width qLen nQ) (qp : qLen ≤ pLen) (q32 : qLen ≤ 32)
    (I₁ : ∀ i ∈ inputs pLen qLen, Input s₁ base size₁ i.1 i.2 (val₁ i.1))
    (I₂ : ∀ i ∈ inputs pLen qLen, Input s₂ base size₂ i.1 i.2 (val₂ i.1))
    (PE : ∀ i ∈ inputs pLen qLen, PtrEq base s₁ s₂ i.1)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q)))
    (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q)))
    (eP : val₁ (.input .p) = val₂ (.input .p)) (eQ : val₁ (.input .q) = val₂ (.input .q)) :
    SameTrace isa (body umaal pLen qLen) s₁ s₂ := by
  have R0 : s₁.gpr .r0 = s₂.gpr .r0 := by
    apply BitVec.eq_of_toNat_eq
    have H := E₁.wb.trans E₂.wb.symm
    have H' := congrArg BitVec.toNat H
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using H'
  unfold body
  refine SameTrace.seq (SameTrace.of_relCT
    (relCT_of_check (τ := Taint.ofRegs [.r0]) (σ := wsT false false) (h := .block []) (by decide))
    (Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact R0))
    (save_ok E₁ (by omega_using [b₁])) (save_ok E₂ (by omega_using [b₂])) fun t₁ t₂ ⟨W₁, P₁, J₁⟩ ⟨W₂, P₂, J₂⟩ => ?_
  have X : Pair base size₁ size₂ pLen qLen nP nQ (inputs pLen qLen) val₁ val₂ t₁ t₂ := by
    refine ⟨⟨⟨W₁, b₁, wp, wq, qp, q32⟩, ?_⟩, ⟨⟨W₂, b₂, wp, wq, qp, q32⟩, ?_⟩, ?_, eP, eQ⟩
    · intro i hi
      simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact J₁ _ _ _ (I₁ (.input .p, pLen) (by simp [inputs]))
      · exact J₁ _ _ _ (I₁ (.input .q, qLen) (by simp [inputs]))
      · exact J₁ _ _ _ (I₁ (.input .g, pLen) (by simp [inputs]))
      · exact J₁ _ _ _ (I₁ (.input .y, pLen) (by simp [inputs]))
    · intro i hi
      simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact J₂ _ _ _ (I₂ (.input .p, pLen) (by simp [inputs]))
      · exact J₂ _ _ _ (I₂ (.input .q, qLen) (by simp [inputs]))
      · exact J₂ _ _ _ (I₂ (.input .g, pLen) (by simp [inputs]))
      · exact J₂ _ _ _ (I₂ (.input .y, pLen) (by simp [inputs]))
    · intro i hi
      have H := PE i hi
      simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> unfold PtrEq at * <;>
        rw [P₁ _ (by decide), P₂ _ (by decide)] <;> exact H
  have mp : (.input .p, pLen) ∈ inputs pLen qLen := by simp [inputs]
  have mq : (.input .q, qLen) ∈ inputs pLen qLen := by simp [inputs]
  have mg : (.input .g, pLen) ∈ inputs pLen qLen := by simp [inputs]
  have my : (.input .y, pLen) ∈ inputs pLen qLen := by simp [inputs]
  refine SameTrace.seq (publicKey_trace X mp mq mg my D₁ D₂)
    (publicKey_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my) D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (publicKey_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my) D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun u₁ u₂ ⟨_, _, R₁⟩ ⟨_, _, R₂⟩ => ?_
  exact SameTrace.of_relCT
    (relCT_of_check (τ := wsT false false) (σ := Taint.ofRegs []) (h := .block []) (by decide))
    (Taint.agree_ofRegs fun r hr => by
      simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_singleton] at hr
      subst r
      exact Ws.r12_eq (R₁.ws W₁) (R₂.ws W₂))

end VG.Proof.Dsa.Arm.PublicValidation

end

end


/-! # Calls of the shared public-key validator -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.PublicValidation
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.PublicValidation
open VG.Proof.X25519.Arm (Rest wp_mov wp_movw wp_ldr op2_reg)

variable {umaal : Bool}

theorem head_ok {s : State} {base : Addr} {size : Nat} (W : Ws s base size) (big : 68 ≤ size)
    (pLen qLen : Nat) :
    WP isa (.block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 2048,
      .ldr .r2 .r12 (Impl.Dsa.Arm.Layout.field .p), .movw .r3 (BitVec.ofNat 16 (3 * pLen + qLen))]) s
      fun u => u.gpr .r11 = s.gpr .r12 ∧ u.gpr .r0 = s.gpr .r12 ∧
        Rest [.r0, .r1, .r2, .r3, .r11] s u ∧ u.mem = s.mem := by
  refine wp_mov (op2_reg s .r12) fun s₁ U₁ => wp_mov (op2_reg s₁ .r12) fun s₂ U₂ =>
    wp_movw fun s₃ U₃ => ?_
  have W₃ := ((W.of_upd U₁ (by decide)).of_upd U₂ (by decide)).of_upd U₃ (by decide)
  refine wp_ldr (by decide) (W₃.ea12 (by change 64 < size; omega_using [big])) (W₃.read (by exact big)) fun s₄ U₄ => wp_movw fun u U₅ => WP.block_nil ?_
  exact ⟨by rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide), U₁.gpr],
    by rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), U₂.gpr, U₁.other _ (by decide)],
    ((((U₁.rest (by decide)).trans (U₂.rest (by decide))).trans (U₃.rest (by decide))).trans
      (U₄.rest (by decide))).trans (U₅.rest (by decide)), by rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]⟩

theorem call_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Impl.Dsa.Arm.PublicValidation.call umaal pLen qLen) s fun t =>
      maskW base t = maskW base s &&& VG.Proof.Ecdsa.Arm.mask32 (publicChecks P Q G Y) ∧
      localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 ∧ Run base s t := by
  unfold Impl.Dsa.Arm.PublicValidation.call
  refine WP.seq (WP.mono (head_ok S.ws (by have := S.big; omega_using [this]) pLen qLen) fun u ⟨h11, h0, R, M⟩ => ?_)
  have E : Pow.Entry u.callEntry base size :=
    ⟨by rw [State.callEntry_gpr _ (by decide), h0, S.ws.wb], by rw [State.callEntry_wr, R.wr]; exact S.ws.wr,
      S.ws.nowrap⟩
  have Mu : u.callEntry.mem = s.mem := M
  have Ru : u.callEntry.rd = s.rd := R.rd
  have Wu : u.callEntry.wr = s.wr := R.wr
  obtain ⟨tr, v, Ex, F, V, O, Regs, SP, RD, WR⟩ := body_ok E S.big S.wp S.wq S.qp S.q32
    (input_mem Ip Mu Ru Wu) (input_mem Iq Mu Ru Wu) (input_mem Ig Mu Ru Wu) (input_mem Iy Mu Ru Wu)
    hP hPo hQ hQo
  have Ret : isa.ret u.callEntry v = some v := by
    have L := Regs .lr (by decide)
    simp only [isa, ret, L, ite_true]
  have v11 : v.gpr .r11 = s.gpr .r12 := by rw [Regs _ (by decide), State.callEntry_gpr _ (by decide), h11]
  refine WP.seq ⟨_, v, .call (call_callEntry u) Ex Ret,
    wp_mov (op2_reg v .r11) fun t U => WP.block_nil ⟨?_, ?_, ?_⟩⟩
  · rw [show maskW base t = maskW base v from congrArg (fun m => m.readW (off base 116) 32) U.mem, F]
    rw [show maskW base u.callEntry = maskW base s from congrArg (fun m => m.readW (off base 116) 32) Mu]
  · rw [localVal, U.mem]; exact V
  · refine ⟨⟨fun r hr => ?_, by rw [U.rd, RD, Ru], by rw [U.wr, WR, Wu], by rw [U.sp, SP, State.callEntry_sp, R.sp]⟩, ?_⟩
    · have hr12 : r = .r12 := by revert hr; cases r <;> decide
      subst r
      rw [U.gpr, v11]
    · rw [U.mem, ← Mu]
      exact O

/-- The same pointer schedule gives the same trace, including nested calls. -/
theorem call_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat}
    {ins : List (Impl.Dsa.Layout.Pointer × Nat)} {val₁ val₂ : Impl.Dsa.Layout.Pointer → Nat}
    {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Impl.Dsa.Arm.PublicValidation.call umaal pLen qLen) s₁ s₂ := by
  have w₁ := X.C₁.S.ws
  have w₂ := X.C₂.S.ws
  unfold Impl.Dsa.Arm.PublicValidation.call
  refine SameTrace.seq (SameTrace.of_relCT (erased_relCT (τ := wsT false false)
      (σ := Taint.ofRegs [])
      (c₀ := .block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 0,
        .ldr .r2 .r12 (Impl.Dsa.Arm.Layout.field .p), .movw .r3 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide))
      (Taint.agree_ofRegs fun r hr => by
        simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_singleton] at hr
        subst r; exact Ws.r12_eq w₁ w₂))
    (head_ok w₁ (by have := X.C₁.S.big; omega_using [this]) pLen qLen)
    (head_ok w₂ (by have := X.C₂.S.big; omega_using [this]) pLen qLen)
    fun u₁ u₂ ⟨_, h0₁, R₁, M₁⟩ ⟨_, h0₂, R₂, M₂⟩ => ?_
  have E₁ : Pow.Entry u₁.callEntry base size₁ :=
    ⟨by rw [State.callEntry_gpr _ (by decide), h0₁, w₁.wb], by rw [State.callEntry_wr, R₁.wr]; exact w₁.wr, w₁.nowrap⟩
  have E₂ : Pow.Entry u₂.callEntry base size₂ :=
    ⟨by rw [State.callEntry_gpr _ (by decide), h0₂, w₂.wb], by rw [State.callEntry_wr, R₂.wr]; exact w₂.wr, w₂.nowrap⟩
  have subset : ∀ i ∈ inputs pLen qLen, i ∈ ins := by
    intro i hi
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> with_reducible assumption
  have I₁ : ∀ i ∈ inputs pLen qLen, Input u₁.callEntry base size₁ i.1 i.2 (val₁ i.1) := by
    intro i hi
    have I := X.C₁.I i (subset i hi)
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact input_mem I M₁ R₁.rd R₁.wr
  have I₂ : ∀ i ∈ inputs pLen qLen, Input u₂.callEntry base size₂ i.1 i.2 (val₂ i.1) := by
    intro i hi
    have I := X.C₂.I i (subset i hi)
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact input_mem I M₂ R₂.rd R₂.wr
  have PE : ∀ i ∈ inputs pLen qLen, PtrEq base u₁.callEntry u₂.callEntry i.1 := by
    intro i hi
    have H := X.E i (subset i hi)
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simpa only [PtrEq, pointerValue, State.callEntry_mem, M₁, M₂] using H
  have T := body_trace (umaal := umaal) E₁ E₂ X.C₁.S.big X.C₂.S.big X.C₁.S.wp X.C₁.S.wq X.C₁.S.qp X.C₁.S.q32 I₁ I₂ PE D₁ D₂
    X.P X.Q
  intro tr₁ tr₂ t₁ t₂ Ex₁ Ex₂
  cases Ex₁ with
  | seq C₁ B₁ =>
    cases Ex₂ with
    | seq C₂ B₂ =>
      cases C₁ with
      | call A₁ H₁ Ret₁ =>
        cases C₂ with
        | call A₂ H₂ Ret₂ =>
          rw [call_callEntry, Option.some.injEq] at A₁ A₂
          subst A₁; subst A₂
          have HT := T _ _ _ _ H₁ H₂
          have BT := SameTrace.of_relCT
            (relCT_of_check (τ := Taint.ofRegs []) (σ := Taint.ofRegs []) (h := .block []) (by decide))
            (Taint.agree_ofRegs fun _ h => nomatch h) _ _ _ _ B₁ B₂
          simp only [List.map_nil, List.nil_append, List.append_nil, HT, BT]

end VG.Proof.Dsa.Arm.PublicValidation

end

end

/-! ### `Dsa.Arm.Verify`, which only this module used -/

section

/-!
# DSA on 32-bit ARM: the verification's arithmetic

`verify_ok`: `((g^u₁ mod p)(y^u₂ mod p) mod p) mod q` for
`w = s^(q-2) mod q`, `u₁ = (z mod q) w mod q` and `u₂ = r w mod q`, from
`q - 2` stored by the domain's check.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm

variable {umaal : Bool}

/-- The value the verification compares with `r`. -/
abbrev verifyValue (P Q G Y R S D : Nat) : Nat :=
  (G ^ (D % Q * (S ^ (Q - 2) % Q) % Q) % P * (Y ^ (R * (S ^ (Q - 2) % Q) % Q) % P) % P) % Q

theorem verify_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y R S D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ir : Input s base size (.input .signature) qLen R) (Is : Input s base size .signatureS qLen S)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (hq2 : localVal base s Impl.Dsa.Layout.qMinusTwo qLen = Q - 2)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Core.verify umaal pLen qLen) s fun t =>
      localVal base t Impl.Dsa.Layout.u qLen = verifyValue P Q G Y R S D ∧
      maskW base t = maskW base s ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := Sc.lens
  have big := Sc.big
  have fits := Sc.fits
  obtain Plt := operand_lt_of Ip
  obtain Qlt := operand_lt_of Iq
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have Lt2 : Impl.Dsa.Layout.t2 = 15328 := rfl
  have Li : Impl.Dsa.Layout.inverse = 14784 := rfl
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  have Lv : Impl.Dsa.Layout.v = 14848 := rfl
  have Lz : Impl.Dsa.Layout.z = 14880 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  obtain qlt : ∀ x, x % Q < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Qlt
  obtain plt : ∀ x, x % P < 256 ^ pLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Plt
  simp only [Core.verify, Core.verifyScalars, Core.verifyPowers, Core.sequence, List.foldr]
  -- `w = s^(q-2) mod q`
  refine WP.seq (WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.inverse) Sc.ws (by omega_arith) Sc.wq q4
    (Nat.le_refl _) qw Iq.toReady Is.toReady (localReady (o := Impl.Dsa.Layout.qMinusTwo) Sc.ws (by omega_arith)
    (by omega_arith) (by omega_arith)) Iq.value (by omega_arith) hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₁ ⟨B₁, St₁⟩ => ?_))
  rw [Is.value, local_operand Sc.ws (by omega_arith), hq2] at B₁
  obtain S₁ := Sc.stage St₁
  obtain n₁ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₁ base size p len v :=
    fun I => I.next Sc St₁ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain W₁ : localVal base v₁ Impl.Dsa.Layout.inverse qLen = S ^ (Q - 2) % Q := localVal_of_bytes B₁ (qlt _)
  -- `z = digest mod q`
  obtain C₁ : countValue base v₁ Core.digestPrefix = c := by rw [countValue_stage St₁ (by omega_arith), hc]
  obtain Id₁ := n₁ Id
  rw [← C₁] at Id₁
  refine WP.seq (WP.mono (reduce_ok (output := Impl.Dsa.Layout.z) S₁.ws (by omega_arith) Sc.wq (n₁ Iq).toReady
    (by simp only [CountOk, Core.digestPrefix]; decide) Id₁.toReady (n₁ Iq).value hQ hQo (by omega_arith) (by omega_arith)
    (by omega_arith)) fun v₂ ⟨B₂, St₂⟩ => ?_)
  rw [Id₁.value] at B₂
  obtain S₂ := S₁.stage St₂
  obtain n₂ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₂ base size p len v :=
    fun I => (n₁ I).next S₁ St₂ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain Z₂ : localVal base v₂ Impl.Dsa.Layout.z qLen = D % Q := localVal_of_bytes B₂ (qlt _)
  obtain W₂ : localVal base v₂ Impl.Dsa.Layout.inverse qLen = S ^ (Q - 2) % Q := by
    rw [St₂.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), W₁]
  -- `u₁ = z w mod q`
  refine WP.seq (WP.mono (productMod_ok (output := Impl.Dsa.Layout.u) S₂.ws (by omega_arith) Sc.wq (n₂ Iq).toReady
    (localReady (o := Impl.Dsa.Layout.z) S₂.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (localReady (o := Impl.Dsa.Layout.inverse) S₂.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₂ Iq).value (by omega_arith) hQo
    (by omega_arith) (by omega_arith) (by omega_arith)) fun v₃ ⟨B₃, St₃⟩ => ?_)
  rw [local_operand S₂.ws (by omega_arith), local_operand S₂.ws (by omega_arith), Z₂, W₂] at B₃
  obtain S₃ := S₂.stage St₃
  obtain n₃ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₃ base size p len v :=
    fun I => (n₂ I).next S₂ St₃ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain U₃ : localVal base v₃ Impl.Dsa.Layout.u qLen = D % Q * (S ^ (Q - 2) % Q) % Q := localVal_of_bytes B₃ (qlt _)
  obtain W₃ : localVal base v₃ Impl.Dsa.Layout.inverse qLen = S ^ (Q - 2) % Q := by
    rw [St₃.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), W₂]
  -- `u₂ = r w mod q`
  refine WP.seq (WP.mono (productMod_ok (output := Impl.Dsa.Layout.v) S₃.ws (by omega_arith) Sc.wq (n₃ Iq).toReady
    (n₃ Ir).toReady (localReady (o := Impl.Dsa.Layout.inverse) S₃.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (n₃ Iq).value (by omega_arith) hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₄ ⟨B₄, St₄⟩ => ?_)
  rw [(n₃ Ir).value, local_operand S₃.ws (by omega_arith), W₃] at B₄
  obtain S₄ := S₃.stage St₄
  obtain n₄ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₄ base size p len v :=
    fun I => (n₃ I).next S₃ St₄ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain V₄ : localVal base v₄ Impl.Dsa.Layout.v qLen = R * (S ^ (Q - 2) % Q) % Q := localVal_of_bytes B₄ (qlt _)
  obtain U₄ : localVal base v₄ Impl.Dsa.Layout.u qLen = D % Q * (S ^ (Q - 2) % Q) % Q := by
    rw [St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), U₃]
  refine WP.block_nil ?_
  -- `g^u₁ y^u₂ mod p`
  refine WP.seq (WP.mono (power2_ok (output := Impl.Dsa.Layout.t) S₄.ws (by omega_arith) Sc.wp q4 qp qw (n₄ Ip).toReady
    (n₄ Ig).toReady (localReady (o := Impl.Dsa.Layout.u) S₄.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (n₄ Iy).toReady (localReady (o := Impl.Dsa.Layout.v) S₄.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (n₄ Ip).value hP hPo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₇ ⟨B₇, St₇⟩ => ?_)
  rw [(n₄ Ig).value, (n₄ Iy).value, local_operand S₄.ws (by omega_arith), local_operand S₄.ws (by omega_arith),
    U₄, V₄] at B₇
  obtain S₇ := S₄.stage St₇
  obtain n₇ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₇ base size p len v :=
    fun I => (n₄ I).next S₄ St₇ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain T₇ := localVal_of_bytes B₇ (plt _)
  rw [Nat.mul_mod (G ^ (D % Q * (S ^ (Q - 2) % Q) % Q)) (Y ^ (R * (S ^ (Q - 2) % Q) % Q)) P] at T₇
  -- mod q
  refine WP.seq (WP.mono (reduce_ok (output := Impl.Dsa.Layout.u) S₇.ws (by omega_arith) Sc.wq (n₇ Iq).toReady
    (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
    (localReady S₇.ws (by omega_arith) (by simp only [countValue]; omega_arith) (by omega_arith))
    (n₇ Iq).value hQ hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₈ ⟨B₈, St₈⟩ => WP.block_nil ⟨?_, ?_, ?_⟩)
  · rw [countValue, local_operand S₇.ws (by omega_arith), T₇] at B₈
    exact localVal_of_bytes B₈ (qlt _)
  · rw [St₈.maskW (by omega_arith), St₇.maskW (by omega_arith),
      St₄.maskW (by omega_arith), St₃.maskW (by omega_arith), St₂.maskW (by omega_arith), St₁.maskW (by omega_arith)]
  · exact (((((St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)).trans (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans
      (St₃.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans (St₄.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans
      (St₇.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans (St₈.run (.inr ⟨by omega_arith, by omega_arith⟩))

end VG.Proof.Dsa.Arm

end

end


/-!
# DSA on 32-bit ARM: the computations of signing and verifying

`signCompute_ok`: the flag `&=` every check of a signature (the domain,
the keys, the nonce, and nonzero r and s), with r and s computed;
`verifyCompute_ok`: the flag `&=` every check of a verification, the last
the comparison of the computed value with r.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)

variable {umaal : Bool}

theorem countValue_run {base : Addr} {s t : State} (Rn : Run base s t) :
    countValue base t Core.digestPrefix = countValue base s Core.digestPrefix :=
  countValue_keep Rn.mem (by decide) (by simp only [CountOk, Core.digestPrefix]; decide)

/-- Every check of a signature. -/
abbrev signChecks (P Q G Y X K D : Nat) : Prop :=
  publicChecks P Q G Y ∧ ((0 < X ∧ X < Q) ∧ (0 < K ∧ K < Q)) ∧ G ^ X % P = Y ∧
    rValue P Q G K ≠ 0 ∧ sValue P Q G X K D ≠ 0

theorem signCompute_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y X K D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ix : Input s base size (.input .x) qLen X) (Ik : Input s base size (.input .nonce) qLen K)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (SignVerify.signCompute umaal pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (signChecks P Q G Y X K D) ∧
      localVal base t Impl.Dsa.Layout.r qLen = rValue P Q G K ∧
      localVal base t Impl.Dsa.Layout.s qLen = sValue P Q G X K D ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := Sc.lens
  have big := Sc.big
  have fits := Sc.fits
  obtain Qlt := operand_lt_of Iq
  obtain qlt : ∀ x, x % Q < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Qlt
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  simp only [SignVerify.signCompute, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (signingKey_ok Sc Ip Iq Ig Iy hP hPo hQ hQo) fun u₁ ⟨F₁, L₁, Rn₁⟩ => ?_)
  obtain r₁ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₁ base size p len v :=
    fun I => I.run Rn₁ (by omega_arith) fits
  refine WP.seq (WP.mono (privateKey_ok (Sc.run Rn₁) (r₁ Ip) (r₁ Iq) (r₁ Ig) (r₁ Iy) (r₁ Ix) (r₁ Ik) hP hPo)
    fun u₂ ⟨F₂, K₂, Rn₂⟩ => ?_)
  obtain r₂ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₂ base size p len v :=
    fun I => (r₁ I).run Rn₂ (by omega_arith) fits
  obtain L₂ : localVal base u₂ Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [K₂ _ _ (by decide) (by simp only [Impl.Dsa.Layout.qMinusTwo, Impl.Dsa.Layout.t]; omega_arith), L₁]
  refine WP.seq (WP.mono (sign_ok (Sc.run (Rn₁.trans Rn₂)) (r₂ Ip) (r₂ Iq) (r₂ Ig) (r₂ Ix) (r₂ Ik) (r₂ Id)
    (by rw [countValue_run Rn₂, countValue_run Rn₁, hc]) L₂ hP hPo hQ hQo) fun u₃ ⟨R₃, S₃, M₃, Rn₃⟩ => ?_)
  obtain Sc₃ := Sc.run ((Rn₁.trans Rn₂).trans Rn₃)
  refine WP.seq (WP.seq (WP.mono (zero_ok Sc₃.ws (by omega_arith) Sc.wq
    (localReady (o := Impl.Dsa.Layout.r) (len := qLen) Sc₃.ws (by omega_arith) (by omega_arith) (by omega_arith)) true)
    fun u₄ ⟨F₄, St₄⟩ => WP.mono (zero_ok (St₄.ws Sc₃.ws) (by omega_arith) Sc.wq
      (localReady (o := Impl.Dsa.Layout.s) (len := qLen) (St₄.ws Sc₃.ws) (by omega_arith) (by omega_arith) (by omega_arith)) true)
    fun u₅ ⟨F₅, St₅⟩ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩))
  · rw [local_operand Sc₃.ws (by omega_arith), R₃] at F₄
    rw [local_operand (St₄.ws Sc₃.ws) (by omega_arith), St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      S₃] at F₅
    rw [F₅, F₄, M₃, F₂, F₁, BitVec.and_assoc, BitVec.and_assoc, BitVec.and_assoc, mask32_and, mask32_and,
      mask32_and]
    apply congrArg _ (mask32_iff ?_)
    obtain H := signingPublicChecks_consistent (P := P) (Q := Q) (G := G) (Y := Y) (X := X)
      (A := ((0 < X ∧ X < Q) ∧ (0 < K ∧ K < Q))) hP
    obtain H' := and_congr H (Iff.rfl :
      (rValue P Q G K ≠ 0 ∧ sValue P Q G X K D ≠ 0) ↔
        (rValue P Q G K ≠ 0 ∧ sValue P Q G X K D ≠ 0))
    simpa only [↓reduceIte, signChecks, and_assoc] using H'
  · rw [St₅.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), R₃]
  · rw [St₅.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), S₃]
  · exact (((Rn₁.trans Rn₂).trans Rn₃).trans (St₄.run (.inl ⟨rfl, rfl⟩))).trans (St₅.run (.inl ⟨rfl, rfl⟩))

/-- Every check of a verification. -/
abbrev verifyChecks (P Q G Y R S D : Nat) : Prop :=
  publicChecks P Q G Y ∧ (0 < R ∧ R < Q) ∧ (0 < S ∧ S < Q) ∧ verifyValue P Q G Y R S D = R

/-- The checks of a verification after the public key's: the signature's
ranges, and the comparison of the computed value with r, given q − 2. -/
theorem verifyTail_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y R S D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ir : Input s base size (.input .signature) qLen R) (Is : Input s base size .signatureS qLen S)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (L : localVal base s Impl.Dsa.Layout.qMinusTwo qLen = Q - 2)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Core.sequence [
      .seq (Validate.range qLen .q (.input .signature)) (Validate.range qLen .q .signatureS),
      Core.verify umaal pLen qLen,
      Validate.equalValues qLen (.local Impl.Dsa.Layout.u) (.input .signature)]) s fun t =>
      maskW base t = maskW base s &&& mask32 ((0 < R ∧ R < Q) ∧ (0 < S ∧ S < Q) ∧ verifyValue P Q G Y R S D = R) ∧
        Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := Sc.lens
  have big := Sc.big
  have fits := Sc.fits
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  simp only [Core.sequence, List.foldr]
  refine WP.seq (WP.seq (WP.mono (range_ok Sc.ws (by omega_arith) Sc.wq Iq.toReady Ir.toReady false)
    fun u₂ ⟨F₂, St₂⟩ => WP.mono (range_ok (St₂.ws Sc.ws) (by omega_arith) Sc.wq
      (Iq.next Sc St₂ (.inl ⟨rfl, rfl⟩)).toReady (Is.next Sc St₂ (.inl ⟨rfl, rfl⟩)).toReady false)
    fun u₃ ⟨F₃, St₃⟩ => ?_))
  rw [Iq.value, Ir.value] at F₂
  rw [(Iq.next Sc St₂ (.inl ⟨rfl, rfl⟩)).value, (Is.next Sc St₂ (.inl ⟨rfl, rfl⟩)).value] at F₃
  obtain Sc₃ := (Sc.stage St₂).stage St₃
  obtain r₃ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₃ base size p len v :=
    fun I => (I.next Sc St₂ (.inl ⟨rfl, rfl⟩)).next (Sc.stage St₂) St₃ (.inl ⟨rfl, rfl⟩)
  obtain L₃ : localVal base u₃ Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [St₃.localVal_eq (by decide) (by omega_arith) (by omega_arith) (by omega_arith),
      St₂.localVal_eq (by decide) (by omega_arith) (by omega_arith) (by omega_arith), L]
  obtain C₃ : countValue base u₃ Core.digestPrefix = c := by
    rw [countValue_stage St₃ (by omega_arith), countValue_stage St₂ (by omega_arith), hc]
  refine WP.seq (WP.mono (verify_ok Sc₃ (r₃ Ip) (r₃ Iq) (r₃ Ig) (r₃ Iy) (r₃ Ir) (r₃ Is) (r₃ Id) C₃ L₃ hP hPo hQ hQo)
    fun u₄ ⟨V₄, M₄, Rn₄⟩ => ?_)
  obtain Sc₄ := Sc₃.run Rn₄
  refine WP.seq (WP.mono (equalValues_ok Sc₄.ws (by omega_arith) Sc.wq
    (localReady (o := Impl.Dsa.Layout.u) Sc₄.ws (by omega_arith) (by omega_arith) (by omega_arith)) ((r₃ Ir).run Rn₄ (by omega_arith) fits).toReady)
    fun u₅ ⟨F₅, St₅⟩ => WP.block_nil ⟨?_, ?_⟩)
  · rw [local_operand Sc₄.ws (by omega_arith), V₄, ((r₃ Ir).run Rn₄ (by omega_arith) fits).value] at F₅
    rw [F₅, M₄, F₃, F₂, BitVec.and_assoc, BitVec.and_assoc, mask32_and, mask32_and]
    exact congrArg _ (mask32_iff (by simp only [Bool.false_eq_true, ↓reduceIte]))
  · exact (((St₂.run (.inl ⟨rfl, rfl⟩)).trans (St₃.run (.inl ⟨rfl, rfl⟩))).trans Rn₄).trans
      (St₅.run (.inl ⟨rfl, rfl⟩))

end VG.Proof.Dsa.Arm

end

end

/-!
# DSA on 32-bit ARM: the bodies of signing and verifying

After the computation, signing writes r and s to the caller's output under
the flag (`writeScalar_ok`: zeros unless every check passed), and both
return the flag's low bit (`result_ok`). `signBody_ok` and `verifyBody_ok`
start from a flag of all ones, as the public checks of the domain's shape
leave it when they pass.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg dpVal)

variable {umaal : Bool}

/-- The caller's output, of `len` bytes, apart from the working space. -/
structure Output (s : State) (base : Addr) (size len : Nat) : Prop where
  fits : (pointerValue base s (.input .out)).toNat + len ≤ 2 ^ 32
  writes : ∀ e k, e + k ≤ len → InRegions s.wr (State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 e) k
  apart : Region.Disjoint ⟨State.addr (pointerValue base s (.input .out)), len⟩ ⟨base, size⟩

/-- What a body keeps: the registers but `coreClob`, and the memory but the
working space's computed values and the output. -/
structure Body (base P : Addr) (L : Nat) (s t : State) : Prop where
  rest : Rest coreClob s t
  mem : ∀ x, (∀ r ∈ runRanges, ofs base x < r.1 ∨ r.1 + r.2 ≤ ofs base x) → L ≤ ofs P x → t.mem x = s.mem x

theorem Body.of_run {base P : Addr} {L : Nat} {s t : State} (Rn : Run base s t) : Body base P L s t :=
  ⟨Rn.rest, fun x h _ => Rn.mem x h⟩

theorem Body.trans {base P : Addr} {L : Nat} {s t u : State} (h₁ : Body base P L s t) (h₂ : Body base P L t u) :
    Body base P L s u :=
  ⟨h₁.rest.trans h₂.rest, fun x h h' => (h₂.mem x h h').trans (h₁.mem x h h')⟩

theorem Output.run {s t : State} {base : Addr} {size len : Nat} (O : Output s base size len) (Rn : Run base s t) :
    Output t base size len := by
  obtain P := pointerValue_keep (Rn.rest.gpr .r12 (by decide)) Rn.mem (by decide) (p := .input .out) (by decide : Impl.Dsa.Layout.Field.out ≠ .mask)
  exact ⟨by rw [P]; exact O.fits, by rw [P, Rn.rest.wr]; exact O.writes, by rw [P]; exact O.apart⟩

theorem Outs.arith_run {base : Addr} {m m' : Mem} (O : Outs base arithRanges m m') : Outs base runRanges m m' :=
  fun x hx => O x fun r hr => by
    obtain h₁ := hx (0, 64) (by simp [runRanges])
    obtain h₃ := hx (256, 15456) (by simp [runRanges])
    simp only [arithRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only at h₁ h₃
    rcases hr with rfl | rfl <;> simp only <;> omega_arith

/-- The flag's low bit. -/
theorem result_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    (acc : Prop) [Decidable acc] (hm : maskW base s = mask32 acc) :
    WP isa (.block SignVerify.result) s fun t =>
      t.gpr .r0 = (if acc then 1 else 0) ∧ Rest [.r0] s t ∧ t.mem = s.mem := by
  have fm : Impl.Dsa.Arm.Layout.field .mask = 116 := rfl
  refine wp_ldr (by decide) (hs.ea12 (by omega_arith)) (hs.read (by omega_arith)) fun t₁ u₁ => wp_dp (op2_imm (by decide))
    fun t u₂ => WP.block_nil ⟨?_, (u₁.rest (by decide)).trans (u₂.rest (by decide)), by rw [u₂.mem, u₁.mem]⟩
  have m : s.mem.readW (off base 116) 32 = mask32 acc := hm
  rw [u₂.gpr, dpVal, u₁.gpr, show Impl.Dsa.Arm.Layout.field .mask = 116 from rfl, m]
  by_cases h : acc <;> simp only [mask32, h, ↓reduceIte] <;> decide

/-- Bytes at a pointer apart from a range that alone changed. -/
theorem bytes_keep {m m' : Mem} {q p : Addr} {len k : Nat} (h : Outside q 0 len m m')
    (hd : Region.Disjoint ⟨p, k⟩ ⟨q, len⟩) (hl : len ≤ 2 ^ 64) (hk : k ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p k = Spec.Rsa.bytesAt m p k := by
  unfold Spec.Rsa.bytesAt
  exact List.map_congr_left fun i hi => VG.Proof.Weierstrass.keep_of_disjoint' h hd hl (List.mem_range.mp hi) hk

/-- A part of the output that alone changed keeps the rest of memory. -/
theorem Body.of_out {base P : Addr} {L e l : Nat} {s t : State} (R : Rest coreClob s t)
    (O : Outside (P + BitVec.ofNat 64 e) 0 l s.mem t.mem) (he : e + l ≤ L) (hL : L ≤ 2 ^ 64) :
    Body base P L s t :=
  ⟨R, fun x _ h' => O x (.inr (by
    obtain H := Offset.lt_iff x P (d := e) (n := l) (by omega_arith)
    have : ¬ (x - (P + BitVec.ofNat 64 e)).toNat < l := fun h => by have := H.mp h; simp only [ofs] at h'; omega_arith
    simp only [ofs]
    omega_arith))⟩

theorem writeScalar_ok {s : State} {base : Addr} {size qLen nQ input v : Nat} (hs : Ws s base size)
    (hz : 15712 < size) (wq : Width qLen nQ) (q32 : qLen ≤ 32) (hin : 12016 ≤ input) (hin' : input + qLen ≤ 15712)
    (hv : localVal base s input qLen = v) (hvl : v < 256 ^ qLen)
    (acc : Prop) [Decidable acc] (hm : maskW base s = mask32 acc) (O : Output s base size (2 * qLen)) (second : Bool) :
    WP isa (SignVerify.writeScalar qLen input second) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr (pointerValue base s (.input .out)) +
          BitVec.ofNat 64 (if second then qLen else 0)) qLen =
        (if acc then Spec.Dsa.encodeBE qLen v else List.replicate qLen 0) ∧
      maskW base t = maskW base s ∧
      pointerValue base t (.input .out) = pointerValue base s (.input .out) ∧ t.wr = s.wr ∧
      KeepsLocals base s t 12016 15712 ∧
      (∀ e k, e + k ≤ 2 * qLen → (e + k ≤ (if second then qLen else 0) ∨ (if second then qLen else 0) + qLen ≤ e) →
        Spec.Rsa.bytesAt t.mem (State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 e) k =
          Spec.Rsa.bytesAt s.mem (State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 e) k) ∧
      Body base (State.addr (pointerValue base s (.input .out))) (2 * qLen) s t := by
  obtain ⟨n0, n48, hl, hl'⟩ := wq.bounds
  obtain s8 := slot_lt (i := 8) n48 (by decide)
  have nw := hs.nowrap
  have q4 := wq.four
  have fm : Impl.Dsa.Arm.Layout.field .mask = 116 := rfl
  unfold SignVerify.writeScalar
  dsimp only
  rw [← wq.n_eq]
  refine WP.seq (WP.mono (loadSlot_ok (i := 8) hs (by omega_arith) wq (by decide)
    (localReady (o := input) (len := qLen) hs hin (by omega_arith) (by omega_arith))) fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  rw [local_operand hs (by omega_arith), hv] at Vu
  obtain Ku : Outs base arithRanges s.mem u.mem := Outs.of_slot (i := 8) Ou (by decide) n48
  obtain Pu : pointerValue base u (.input .out) = pointerValue base s (.input .out) :=
    pointerValue_keep (Ru.gpr .r12 (by decide)) Ku arith_hdr (by decide : Impl.Dsa.Layout.Field.out ≠ .mask)
  obtain mu : maskW base u = maskW base s := maskW_arith Ku
  have hP32 : (pointerValue base s (.input .out)).toNat + 2 * qLen ≤ 2 ^ 32 := O.fits
  -- The pointer: `out`, or `out + qLen`.
  obtain ptr : WP isa (.block (SignVerify.outputPointer qLen second ++ [.ldr .r3 .r12 (Impl.Dsa.Arm.Layout.field .mask)])) u
      fun w => w.gpr .r11 = pointerValue base s (.input .out) + BitVec.ofNat 32 (if second then qLen else 0) ∧ w.gpr .r3 = mask32 acc ∧
        Rest [.r3, .r4, .r11] u w ∧ w.mem = u.mem := by
    simp only [SignVerify.outputPointer, List.append_assoc]
    refine VG.Proof.X25519.Arm.WP.append (pointer_ok wu (by omega_arith) (p := .input .out)
      (by decide : Impl.Dsa.Layout.Field.out ≠ .mask))
      fun w₁ ⟨P₁, R₁, M₁⟩ => ?_
    rw [Pu] at P₁
    obtain w₁s := wu.of_rest R₁ (by decide)
    cases second
    · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
      refine wp_ldr (by decide) (w₁s.ea12 (by omega_arith)) (w₁s.read (by omega_arith)) fun w u₂ => WP.block_nil
        ⟨by rw [u₂.other .r11 (by decide), P₁]; exact (BitVec.add_zero _).symm, ?_,
          (R₁.mono (by decide)).trans (u₂.rest (by decide)), by rw [u₂.mem, M₁]⟩
      rw [u₂.gpr, M₁, fm]; exact mu.trans hm
    · simp only [↓reduceIte, List.cons_append, List.nil_append]
      refine wp_movw fun w₂ u₂ => wp_dp (op2_reg _ _) fun w₃ u₃ => ?_
      obtain w₃s := (w₁s.of_upd u₂ (by decide)).of_upd u₃ (by decide)
      refine wp_ldr (by decide) (w₃s.ea12 (by omega_arith)) (w₃s.read (by omega_arith)) fun w u₄ => WP.block_nil
        ⟨?_, ?_, (((R₁.mono (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
          (u₄.rest (by decide)),
          by rw [u₄.mem, u₃.mem, u₂.mem, M₁]⟩
      · rw [u₄.other .r11 (by decide), u₃.gpr, dpVal, u₂.other .r11 (by decide), u₂.gpr, P₁, movw_ofNat (by omega_arith)]
      · rw [u₄.gpr, u₃.mem, u₂.mem, M₁, fm]; exact mu.trans hm
  refine WP.seq (WP.mono ptr fun w ⟨Pw, Cw, Rw, Mw⟩ => ?_)
  obtain ww := wu.of_rest Rw (by decide)
  obtain off32 : (if second then qLen else 0) + qLen ≤ 2 * qLen := by split <;> omega_arith
  obtain addr : State.addr (w.gpr .r11) = State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 (if second then qLen else 0) := by
    rw [Pw, VG.Arm.addr_add (by omega_arith)]
  obtain hc : w.gpr .r3 = if decide acc then BitVec.allOnes 32 else 0 := by
    rw [Cw]; by_cases h : acc <;> simp [mask32, h]
  obtain wr : w.wr = s.wr := by rw [Rw.wr, Ru.wr]
  refine WP.mono (storeComponent_ok (input := baseS nQ) (len := qLen) ww (decide acc) hc
    (by simp only [baseS]; omega_arith) (by simp only [baseS]; omega_arith) q4 wq.word
    (by rw [Pw, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by split <;> omega_arith : (if second then qLen else 0) < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith)
    (fun e k hek => by rw [addr, Offset.add_add, wr]; exact O.writes _ _ (by omega_arith))
    (by
      rw [addr]
      exact ((O.apart.sub_left (Offset.sub_base (State.addr (pointerValue base s (.input .out))) off32)).sub_right
        (Offset.sub_base base (by simp only [baseS]; omega_arith))).symm)) fun t ⟨wt, Vt, Rt, Ot⟩ => ?_
  rw [addr] at Vt Ot
  obtain dis : ∀ d k, d + k ≤ size → Region.Disjoint ⟨off base d, k⟩
      ⟨State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 (if second then qLen else 0), qLen⟩ :=
    fun d k h => ((O.apart.sub_left (Offset.sub_base (State.addr (pointerValue base s (.input .out))) off32)).sub_right
      (Offset.sub_base base h)).symm
  obtain rw32 : ∀ d, d + 4 ≤ size → t.mem.readW (off base d) 32 = u.mem.readW (off base d) 32 := fun d h => by
    rw [← Mw]
    exact (Mem.readW_congr fun i hi =>
      (VG.Proof.Weierstrass.keep_of_disjoint' Ot (dis d 4 h) (by omega_arith) hi (by decide)).symm).symm
  refine ⟨?_, ?_, ?_, by rw [Rt.wr, wr], ?_, ?_, ?_⟩
  · rw [Vt, Mw]
    obtain e : val32 u.mem base (baseS nQ) (qLen / 4) = v := by
      rw [val32_prefix_of_lt (n := 2 * nQ) (by omega_arith) (by
        rw [show baseS nQ = slot nQ 8 from rfl, Vu, ← pow256_words wq.word]; exact hvl)]
      exact Vu
    rw [e]
    by_cases h : acc <;> simp [h]
  · exact (rw32 116 (by omega_arith)).trans mu
  · exact (rw32 96 (by omega_arith)).trans Pu
  · intro o len h₁ h₂
    rw [Arm.localVal, Arm.localVal, bytes_keep Ot (dis o len (by omega_arith)) (by omega_arith) (by omega_arith), Mw,
      outs_bytes Ku (by omega_arith) (by decide) fun r hr => by
        simp only [arithRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint base (.inr (by omega_arith)) (by omega_arith) (by omega_arith)]
  · intro e k hek hsep
    have Pf := O.fits
    rw [bytes_keep Ot (Offset.disjoint _ hsep (by omega_arith) (by omega_arith)) (by omega_arith) (by omega_arith), Mw,
      outs_bytes Ku (by omega_arith) (by decide) fun r hr => by
        simp only [arithRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;>
          exact (O.apart.sub_left (Offset.sub_base _ hek)).sub_right (Offset.sub_base base (by omega_arith))]
  · exact (Body.of_run (Run.mk Ru (Outs.arith_run Ku))).trans
      (Body.of_out ((Rw.mono (by decide)).trans (Rt.mono (by decide))) (by rw [Mw] at Ot; exact Ot) off32 (by omega_arith))

theorem Output.keep {s t : State} {base : Addr} {size len : Nat} (O : Output s base size len)
    (hp : pointerValue base t (.input .out) = pointerValue base s (.input .out)) (hw : t.wr = s.wr) :
    Output t base size len :=
  ⟨by rw [hp]; exact O.fits, by rw [hp, hw]; exact O.writes, by rw [hp]; exact O.apart⟩

theorem signBody_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y X K D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ix : Input s base size (.input .x) qLen X) (Ik : Input s base size (.input .nonce) qLen K)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1)
    (hm : maskW base s = BitVec.allOnes 32) (O : Output s base size (2 * qLen)) :
    WP isa (SignVerify.signBody umaal pLen qLen) s fun t =>
      t.gpr .r0 = (if signChecks P Q G Y X K D then 1 else 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr (pointerValue base s (.input .out))) (2 * qLen) =
        (if signChecks P Q G Y X K D then
          Spec.Dsa.encodeBE qLen (rValue P Q G K) ++ Spec.Dsa.encodeBE qLen (sValue P Q G X K D)
        else List.replicate (2 * qLen) 0) ∧
      Body base (State.addr (pointerValue base s (.input .out))) (2 * qLen) s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := Sc.lens
  have big := Sc.big
  obtain Qlt := operand_lt_of Iq
  obtain qlt : ∀ x, x % Q < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Qlt
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  unfold SignVerify.signBody
  refine WP.seq (WP.mono (signCompute_ok Sc Ip Iq Ig Iy Ix Ik Id hc hP hPo hQ hQo) fun u ⟨Fu, Ru, Su, Rn⟩ => ?_)
  obtain mu : maskW base u = mask32 (signChecks P Q G Y X K D) := by
    rw [Fu, hm, BitVec.allOnes_and]
  obtain Pu : pointerValue base u (.input .out) = pointerValue base s (.input .out) :=
    pointerValue_keep (Rn.rest.gpr .r12 (by decide)) Rn.mem (by decide) (by decide : Impl.Dsa.Layout.Field.out ≠ .mask)
  obtain Ou := O.run Rn
  obtain wu := Rn.ws Sc.ws
  refine WP.seq (WP.mono (writeScalar_ok wu big Sc.wq q32 (by omega_arith) (by omega_arith) Ru (by simp only [rValue]; exact qlt _)
    _ mu Ou false) fun v ⟨Bv, mv, Pv, Wv, Kv, _, Bdv⟩ => ?_)
  obtain wv := wu.of_rest Bdv.rest (by decide)
  refine WP.seq (WP.mono (writeScalar_ok (v := sValue P Q G X K D) wv big Sc.wq q32 (by omega_arith) (by omega_arith)
    (by rw [Kv _ _ (by omega_arith) (by omega_arith)]; exact Su) (by simp only [sValue]; exact qlt _) _ (mv.trans mu)
    (Ou.keep Pv Wv) true) fun w ⟨Bw, mw, Pw, Ww, Kw, Ew, Bdw⟩ => ?_)
  obtain ww := wv.of_rest Bdw.rest (by decide)
  refine WP.mono (result_ok ww (by omega_arith) _ ((mw.trans mv).trans mu)) fun t ⟨r0, Rt, Mt⟩ => ⟨r0, ?_, ?_⟩
  · rw [Pu] at Bv
    rw [Pv, Pu] at Bw
    simp only [Bool.false_eq_true, ↓reduceIte] at Bv Bw
    rw [Mt]
    refine VG.Proof.Dsa.signatureBytes _ ?_ Bw
    obtain E := Ew 0 qLen (by omega_arith) (.inl (by simp only [↓reduceIte]; omega_arith))
    rw [Pv, Pu, BitVec.add_zero] at E
    rw [E]
    simpa only [BitVec.add_zero] using Bv
  · rw [Pu] at Bdv
    rw [Pv, Pu] at Bdw
    exact ((Body.of_run Rn).trans Bdv).trans (Bdw.trans ⟨Rt.mono (by decide), fun x _ _ => by rw [Mt]⟩)

end VG.Proof.Dsa.Arm
