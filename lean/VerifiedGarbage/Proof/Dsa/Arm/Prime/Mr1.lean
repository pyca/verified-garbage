module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont10
public import VerifiedGarbage.Proof.RsaKeyGen.MrIter
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont8
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Instr
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Vals

/-! ### `Dsa.Generation.MrIter`, which only this module used -/

section

/-!
# DSA's probable-prime test: Miller–Rabin, witness by witness

As `Proof/RsaKeyGen/MrIter.lean` for RSA's candidate, but with the witnesses
drawn from the start of the tape, the `k`-th at offset `D k`: DSA's test
reads no candidate from the tape. `dmrS c D r k`: the counts `(i, uniform)`
of the loop after `k` witnesses passed. `DMrAt … k n`: the loop from the
start is the loop from there, it draws again, and `n + 1` iterations of an
implementation that also counts the last, failing, draw are left
(`itersOf`). A witness that is drawn and passes leads to `DMrAt … (k + 1)
(n − 1)` if more are needed (`dmrAt_next`); otherwise the loop's result is
known and `n = 0` (`dmrAt_done`, `dmrAt_fail`, `dmrAt_short`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Generation

open VG.Spec.RsaKeyGen VG.Spec.Rsa
open VG.Proof.RsaKeyGen (seg goS itersOf shapeOf mrLoop_step mrLoop_done iters_cont ite_t ite_f)

/-- The witness drawn at offset `u`. -/
def dwit (c D : Nat) (r : Rand) (u : Nat) : Nat × Bool := witness (c - 1) (os2ip (seg r u D))

/-- The counts after `k` witnesses passed. -/
def dmrS (c D : Nat) (r : Rand) : Nat → Nat × Nat
  | 0 => (1, 0)
  | k + 1 => ((dmrS c D r k).1 + 1, (dmrS c D r k).2 + if (dwit c D r (D * k)).2 then 1 else 0)

/-- The loop's result from the start of the tape. -/
abbrev dres (c ch a m : Nat) (r : Rand) : Option (Bool × Rand) := loop (mrStep c ch a m) (1, 0) r

/-- After `k` witnesses passed, with `n + 1` iterations left. -/
structure DMrAt (c ch a m D : Nat) (r : Rand) (k n : Nat) : Prop where
  loop : dres c ch a m r = loop (mrStep c ch a m) (dmrS c D r k) (r.drop (D * k))
  go : goS ch (dmrS c D r k)
  iters : itersOf D r.length (shapeOf (dres c ch a m r)) (D * k) = n + 1
  used : D * k ≤ r.length

section
variable {c ch a m D : Nat} {r : Rand} {k n : Nat}

/-- The witness passes and more are needed. -/
theorem dmrAt_next (h : DMrAt c ch a m D r k n) (hwb : witnessBytes c = D) (hD : 0 < D)
    (hav : D * k + D ≤ r.length) (hp : mrIteration c a m (dwit c D r (D * k)).1 = true)
    (hg : goS ch (dmrS c D r (k + 1))) : 0 < n ∧ DMrAt c ch a m D r (k + 1) (n - 1) := by
  have e := mrLoop_step c ch a m D r (dmrS c D r k).1 (dmrS c D r k).2 (D * k) h.go hwb hD
  rw [ite_t hav] at e
  unfold dwit at hp
  rw [ite_t hp] at e
  have hk : D * k + D = D * (k + 1) := (Nat.mul_succ D k).symm
  rw [hk] at e
  have l1 : dres c ch a m r = loop (mrStep c ch a m) (dmrS c D r (k + 1)) (r.drop (D * (k + 1))) := by
    rw [h.loop, e]; rfl
  have ic := iters_cont (c := c) (ch := ch) (a := a) (m := m) (r := r) (i := (dmrS c D r (k + 1)).1)
    (uni := (dmrS c D r (k + 1)).2) (u := D * (k + 1)) hg hwb hD (by rw [Nat.mul_succ]; omega_using []) (by omega_using [hav, hk])
  rw [← l1, show D * (k + 1) - D = D * k by rw [Nat.mul_succ]; omega_using [], h.iters] at ic
  exact ⟨by omega_using [ic], ⟨l1, hg, by omega_using [ic], by omega_using [hav, hk]⟩⟩

/-- The witness passes and no more are needed: `c` is probably prime. -/
theorem dmrAt_done (h : DMrAt c ch a m D r k n) (hwb : witnessBytes c = D) (hD : 0 < D)
    (hav : D * k + D ≤ r.length) (hp : mrIteration c a m (dwit c D r (D * k)).1 = true)
    (hg : ¬ goS ch (dmrS c D r (k + 1))) :
    n = 0 ∧ dres c ch a m r = some (true, r.drop (D * k + D)) := by
  have e := mrLoop_step c ch a m D r (dmrS c D r k).1 (dmrS c D r k).2 (D * k) h.go hwb hD
  rw [ite_t hav] at e
  unfold dwit at hp
  rw [ite_t hp] at e
  have d := mrLoop_done c ch a m (r.drop (D * k + D)) (dmrS c D r (k + 1)).1 (dmrS c D r (k + 1)).2 hg
  have l1 : dres c ch a m r = some (true, r.drop (D * k + D)) := by
    rw [h.loop, e]; exact d
  refine ⟨?_, l1⟩
  have := h.iters
  rw [l1] at this
  simp only [shapeOf, Option.map_some, itersOf, List.length_drop] at this
  rw [show r.length - (r.length - (D * k + D)) - D * k = D by omega_using [hav], Nat.div_self hD] at this
  omega_using [this]

/-- The witness fails: `c` is composite. -/
theorem dmrAt_fail (h : DMrAt c ch a m D r k n) (hwb : witnessBytes c = D) (hD : 0 < D)
    (hav : D * k + D ≤ r.length) (hp : mrIteration c a m (dwit c D r (D * k)).1 = false) :
    n = 0 ∧ dres c ch a m r = some (false, r.drop (D * k + D)) := by
  have e := mrLoop_step c ch a m D r (dmrS c D r k).1 (dmrS c D r k).2 (D * k) h.go hwb hD
  rw [ite_t hav] at e
  unfold dwit at hp
  rw [ite_f (by simp [hp])] at e
  have l1 : dres c ch a m r = some (false, r.drop (D * k + D)) := by rw [h.loop, e]
  refine ⟨?_, l1⟩
  have := h.iters
  rw [l1] at this
  simp only [shapeOf, Option.map_some, itersOf, List.length_drop] at this
  rw [show r.length - (r.length - (D * k + D)) - D * k = D by omega_using [hav], Nat.div_self hD] at this
  omega_using [this]

/-- Too few octets left for the witness. -/
theorem dmrAt_short (h : DMrAt c ch a m D r k n) (hwb : witnessBytes c = D) (hD : 0 < D)
    (hav : ¬ D * k + D ≤ r.length) : n = 0 ∧ dres c ch a m r = none := by
  have e := mrLoop_step c ch a m D r (dmrS c D r k).1 (dmrS c D r k).2 (D * k) h.go hwb hD
  rw [ite_f hav] at e
  have l1 : dres c ch a m r = none := by rw [h.loop, e]
  refine ⟨?_, l1⟩
  have := h.iters
  rw [l1] at this
  simp only [shapeOf, Option.map_none, itersOf] at this
  rw [Nat.div_eq_of_lt (by omega_using [hD, hav])] at this
  omega_using [this]

/-- The iterations from the start: at least one, the first draw's. -/
theorem iters_start (hwb : witnessBytes c = D) (hD : 0 < D) :
    1 ≤ itersOf D r.length (shapeOf (dres c ch a m r)) 0 := by
  have hg : goS ch ((1 : Nat), (0 : Nat)) := .inl (by simp [blindedChecks])
  let r' : Rand := List.replicate D 0 ++ r
  have hd : r'.drop D = r := by simp [r']
  have hl : r'.length = r.length + D := by simp [r', Nat.add_comm]
  have := (iters_cont (c := c) (ch := ch) (a := a) (m := m) (r := r') (i := 1) (uni := 0) (u := D) hg hwb hD
    (Nat.le_refl _) (by omega_using [hl])).2
  rw [hd, hl] at this
  unfold dres
  generalize loop (mrStep c ch a m) (1, 0) r = x at this ⊢
  rcases x with _ | ⟨b, rest⟩
  · simp only [shapeOf, Option.map_none, itersOf]; exact Nat.le_add_left 1 _
  · simp only [shapeOf, Option.map_some, itersOf] at this ⊢
    rw [show r.length + D - rest.length - D = r.length - rest.length - 0 by omega_using []] at this
    exact this

/-- The start. -/
theorem dmrAt_zero (hwb : witnessBytes c = D) (hD : 0 < D) :
    DMrAt c ch a m D r 0 (itersOf D r.length (shapeOf (dres c ch a m r)) 0 - 1) := by
  have hg : goS ch (dmrS c D r 0) := .inl (by simp [dmrS, blindedChecks])
  refine ⟨by simp [dmrS], hg, ?_, by simp⟩
  have := iters_start (ch := ch) (a := a) (m := m) (r := r) hwb hD
  rw [Nat.mul_zero]
  omega_using [this]

end

end VG.Proof.Dsa.Generation

end

end


/-! # DSA's probable-prime test on ARMv7: the stages of Miller–Rabin

`resP`: Miller–Rabin's result on the tape; under `EM` (the candidate is not
obviously composite), it is the test's (`mr_facts`). `Nt`: the iterations
of the witnesses' loop but one, public (`resQ`). `MRI P E j`: before an
iteration of the witnesses' loop, `j` of them left (`DMrAt`, the witness
`k = Nt P + 1 − j` next); `mrInit_vp` starts it.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP sub32)
open VG.Proof.RsaKeyGen (goS shapeOf itersOf)
open VG.Proof.Dsa.Generation (DMrAt dmrS dwit dres)

/-- The checks, `a` and `m` of `c − 1 = 2^a m`. -/
abbrev chP (P : CP) : Nat := Spec.Dsa.primeChecks P.bits
abbrev taP (P : CP) (σ : State) : Nat := (Spec.Rsa.splitTwos (cv P σ - 1)).1
abbrev tmP (P : CP) (σ : State) : Nat := (Spec.Rsa.splitTwos (cv P σ - 1)).2

/-- Miller–Rabin's result on the tape. -/
def resP (P : CP) (σ : State) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  dres (cv P σ) (chP P) (taP P σ) (tmP P σ) (rB P σ)

/-- The same, from the public candidate and tape. -/
def resQ (P : CP) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  dres P.cand (chP P) (Spec.Rsa.splitTwos (P.cand - 1)).1 (Spec.Rsa.splitTwos (P.cand - 1)).2 P.rnd

/-- The iterations of the witnesses' loop, but one. -/
def Nt (P : CP) : Nat := itersOf P.D P.rl (shapeOf (resQ P)) 0 - 1

/-- The candidate goes on to Miller–Rabin. -/
abbrev EM (P : CP) (σ : State) : Prop := compv P σ = false

/-- The header words before the iteration of witness `k`. -/
def VI (P : CP) (k : Nat) (σ : State) : Nat → Nat :=
  upd (upd (upd (upd (V3 P σ) sChk (chP P)) sUsed (P.D * k)) sI (dmrS (cv P σ) P.D (rB P σ) k).1)
    sUni (dmrS (cv P σ) P.D (rB P σ) k).2
abbrev LSI : List Nat := [sUni, sI, sUsed, sChk]

/-- Before an iteration, `j` left. -/
def MRI (P : CP) (E : State → Prop) (j : Nat) (σ s : State) : Prop :=
  1 ≤ j ∧ j ≤ Nt P + 1 ∧ DMrAt (cv P σ) (chP P) (taP P σ) (tmP P σ) P.D (rB P σ) (Nt P + 1 - j) (j - 1) ∧
    St P E (AB2 P) LB2 (VI P (Nt P + 1 - j)) LSI σ s ∧ MS P σ s

section
variable {P : CP}

theorem rB_length (P : CP) (σ : State) : (rB P σ).length = P.rl := bytesAt_length _ _ _

theorem resP_eq {σ : State} (pre : In P σ) : resP P σ = resQ P := by
  unfold resP resQ taP tmP; rw [pre.cand, pre.rnd]

/-- The facts of Miller–Rabin's loop for the candidate: the test's result is
the loop's, a witness takes `D` octets, and the count of iterations is that
of `resP`. -/
theorem mr_facts {σ : State} (pre : In P σ) (hm : EM P σ) :
    res P σ = resP P σ ∧ Spec.RsaKeyGen.witnessBytes (cv P σ) = P.D ∧
      Nt P = itersOf P.D P.rl (shapeOf (resP P σ)) 0 - 1 := by
  have sz := pre.sizes
  obtain ⟨hodd, hlo, -⟩ := cv_shape (σ := σ) pre
  have h3 : 3 < cv P σ := by
    have : 2 ^ 2 ≤ 2 ^ (P.bits - 1) := Nat.pow_le_pow_right (by decide) (by omega_using [sz])
    omega_using [hlo, this]
  refine ⟨?_, ?_, by unfold Nt; rw [resP_eq pre]⟩
  · unfold res resP
    rw [VG.Proof.Dsa.Generation.probablePrime_large h3 hodd, pre.bl]
    unfold EM compv at hm
    rw [hm]; rfl
  · rw [VG.Proof.Dsa.Generation.witness_width (n := P.bits) (by omega_using [sz]) hodd pre.bl]
    rfl

theorem lt_bit {x k : Nat} (hx : x < 2 ^ 31) (hk : k < 2 ^ 31) :
    ((BitVec.ofNat 32 x - BitVec.ofNat 32 k) >>> 31).toNat = VG.Proof.Rsa.b2n (decide (x < k)) := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := x) (by omega_using [hx]), Nat.mod_eq_of_lt (a := k) (by omega_using [hk])]
  unfold VG.Proof.Rsa.b2n
  by_cases h : x < k <;> simp [h] <;> omega_arith

/-- `str r, [r8, #d]` of a header word, keeping `MS`. -/
theorem KS.strM {σ s : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS P σ A live V ls s) (m : MS P σ s) (hw : Ws s P.B P.Z P.W nArr) {d : Nat} (hd : LsOk d) {r : Reg}
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live (upd V d (s.gpr r).toNat) (d :: ls) t → Ws t P.B P.Z P.W nArr → MS P σ t →
      t.gpr = s.gpr → WP isa (.block rest) t Q) :
    WP isa (.block (.str r .r8 d :: rest)) s Q :=
  h.str hw hd fun t ht hwt mt => k t ht hwt (m.of_keep h.pre (js := []) (ds := [d])
    (by rw [mt.mem]; exact keep_write _ _ (by simp) (by have := hd.1; simp only [hdr] at this; omega_using [this]))
    (by simp) (by simp; have := hd.1; omega_using [this]) mt.sp mt.rd mt.wr (h.sp.trans h.pre.sp)) mt.gpr

/-- `KS.ldr` with `MS`. -/
theorem KS.ldrM {σ s : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS P σ A live V ls s) (m : MS P σ s) (hw : Ws s P.B P.Z P.W nArr) {d : Nat} (hd : d ∈ ls) {r : Reg}
    (hr : r ∉ [.r7, .r8, .r9]) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live V ls t → Ws t P.B P.Z P.W nArr → MS P σ t → Upd s t r (BitVec.ofNat 32 (V d)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.ldr r .r8 d :: rest)) s Q :=
  h.ldr hw hd hr fun t ht hwt u => k t ht hwt ⟨m.toMSp.of_same u.mem u.sp u.rd u.wr, by rw [u.mem]; exact m.stride⟩ u

end

end VG.Proof.Dsa.Arm.Prime
