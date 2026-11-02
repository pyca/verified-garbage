module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont10
public import VerifiedGarbage.Proof.Dsa.Generation.MrIter
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont7
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Instr
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Vals

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
    have : 2 ^ 2 ≤ 2 ^ (P.bits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  refine ⟨?_, ?_, by unfold Nt; rw [resP_eq pre]⟩
  · unfold res resP
    rw [VG.Proof.Dsa.Generation.probablePrime_large h3 hodd, pre.bl]
    unfold EM compv at hm
    rw [hm]; rfl
  · rw [VG.Proof.Dsa.Generation.witness_width (n := P.bits) (by omega) hodd pre.bl]
    rfl

theorem lt_bit {x k : Nat} (hx : x < 2 ^ 31) (hk : k < 2 ^ 31) :
    ((BitVec.ofNat 32 x - BitVec.ofNat 32 k) >>> 31).toNat = VG.Proof.Rsa.b2n (decide (x < k)) := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := x) (by omega), Nat.mod_eq_of_lt (a := k) (by omega)]
  unfold VG.Proof.Rsa.b2n
  by_cases h : x < k <;> simp [h] <;> omega

/-- `ltAdd k`: `r1 +=` whether `W < k`. -/
theorem ltAdd_ok {u : State} {W x k : Nat} (r9 : u.gpr .r9 = BitVec.ofNat 32 W) (hW : W < 2 ^ 31) (hk : k < 256)
    (r1 : u.gpr .r1 = BitVec.ofNat 32 x) (hx : x < 2 ^ 30) {rest : List Instr} {Q : State → Prop}
    (kk : ∀ u', Rest [.r1, .r2] u u' → u'.mem = u.mem →
      u'.gpr .r1 = BitVec.ofNat 32 (x + VG.Proof.Rsa.b2n (decide (W < k))) → WP isa (.block rest) u' Q) :
    WP isa (.block (ltAdd k ++ rest)) u Q := by
  simp only [ltAdd, List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (VG.Proof.Rsa.Arm.Keys.encodable_lt hk)) fun u1 v1 => wp_mov (op2_lsr (by decide)) fun u2 v2 =>
    wp_dp (op2_reg _ _) fun u3 v3 => kk u3 ((v1.rest (by simp)).trans ((v2.rest (by simp)).trans (v3.rest (by simp))))
      (by rw [v3.mem, v2.mem, v1.mem]) ?_
  have x2 : u2.gpr .r1 = BitVec.ofNat 32 x := by rw [v2.other _ (by decide), v1.other _ (by decide), r1]
  have b2 : u2.gpr .r2 = (BitVec.ofNat 32 W - BitVec.ofNat 32 k) >>> 31 := by rw [v2.gpr, v1.gpr, dpVal, r9]
  rw [v3.gpr, dpVal, x2, b2]
  apply BitVec.eq_of_toNat_eq
  have hb := VG.Proof.Rsa.b2n_le (decide (W < k))
  rw [BitVec.toNat_add, lt_bit hW (by omega), ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- `str r, [r8, #d]` of a header word, keeping `MS`. -/
theorem KS.strM {σ s : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS P σ A live V ls s) (m : MS P σ s) (hw : Ws s P.B P.Z P.W nArr) {d : Nat} (hd : LsOk d) {r : Reg}
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live (upd V d (s.gpr r).toNat) (d :: ls) t → Ws t P.B P.Z P.W nArr → MS P σ t →
      t.gpr = s.gpr → WP isa (.block rest) t Q) :
    WP isa (.block (.str r .r8 d :: rest)) s Q :=
  h.str hw hd fun t ht hwt mt => k t ht hwt (m.of_keep h.pre (js := []) (ds := [d])
    (by rw [mt.mem]; exact keep_write _ _ (by simp) (by have := hd.1; simp only [hdr] at this; omega))
    (by simp) (by simp; have := hd.1; omega) mt.sp mt.rd mt.wr (h.sp.trans h.pre.sp)) mt.gpr

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
