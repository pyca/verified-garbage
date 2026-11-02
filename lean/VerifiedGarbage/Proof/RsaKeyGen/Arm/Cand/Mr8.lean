module
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mr1

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mr2
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint7
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Instr
import VerifiedGarbage.Proof.Rsa.Arm.RvLoads
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St

/-! # A candidate on ARMv7: the pieces of an iteration of Miller–Rabin

`avFlag_vp`: Z iff `rand` is too short for the witness of iteration `k`;
the header words set with `MS` kept (`St.psetSM`); `isOne` with `MS` kept
(`St.pisOneM`); the counts `mrS` (`mrS_fst`, `mrS_snd_le`); and the stage
after the loop (`QS`): `sStat` is 0 if `rand` was too short, 1 for a
probable prime and 3 for a composite, and `sUsed` the octets read.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Operand)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Proof.RsaKeyGen (MrAt mrS wit goS shapeOf itersOf)
open VG.Impl.RsaKeyGen.Arm.Key (isOne)

/-- The status after Miller–Rabin. -/
def statQ (P : CP) (σ : State) : Nat :=
  match resP P σ with
  | none => 0
  | some (true, _) => 1
  | some (false, _) => 3

/-- The octets read after Miller–Rabin. -/
def usedQ (P : CP) (σ : State) : Nat :=
  match resP P σ with
  | some (_, rest) => P.rl - rest.length
  | none => P.L * (Nt P + 1)

/-- After Miller–Rabin. -/
abbrev QS (P : CP) (E : State → Prop) : State → State → Prop :=
  St P E (AB2 P) LB2 (fun σ => upd (upd (V3 P σ) sUsed (usedQ P σ)) sStat (statQ P σ)) [sStat, sUsed]

/-- Before an iteration, at the witness `k`. -/
abbrev SI (P : CP) (E : State → Prop) (k : Nat) (σ s : State) : Prop :=
  St P E (AB2 P) LB2 (VI P k) LSI σ s ∧ MS P σ s

theorem avFlag_eq : avFlag = ([(Reg.r1, aoRl)].map fun p => Instr.ldrSp p.1 p.2) ++
    (([.ldr .r2 .r8 sUsed, .dp .sub .r1 .r1 (.reg .r2)] : List Instr) ++
      (([(Reg.r2, foL)].map fun p => Instr.ldrSp p.1 p.2) ++ carryTail)) := rfl

theorem mrS_fst (c L : Nat) (r : Spec.RsaKeyGen.Rand) : ∀ k, (mrS c L r k).1 = k + 1
  | 0 => rfl
  | k + 1 => by simp only [mrS, mrS_fst c L r k]

theorem mrS_snd_le (c L : Nat) (r : Spec.RsaKeyGen.Rand) : ∀ k, (mrS c L r k).2 ≤ k
  | 0 => Nat.le_refl _
  | k + 1 => by
    simp only [mrS]
    have := mrS_snd_le c L r k
    split <;> omega

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `setS d v`, keeping `MS`. -/
theorem St.psetSM {d v : Nat} (cert : Cert (.block (setS d v))) (hd : LsOk d)
    (hv : encodable (BitVec.ofNat 32 v) = true) (hv' : v < 2 ^ 32) :
    VP (fun σ s => St P E A L V LS σ s ∧ MS P σ s) (.block (setS d v))
      (fun σ s => St P E A L (fun σ => upd (V σ) d v) (d :: LS) σ s ∧ MS P σ s) :=
  VP.kv cert (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, m⟩ => by
    unfold setS
    refine wp_mov (op2_imm hv) fun s1 u1 => ?_
    have h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
    have hw1 := hw.of_upd u1 (by decide) (by decide) (by decide)
    refine h1.strM (m.of_upd u1) hw1 hd fun t ht hwt mt _ => WP.block_nil ⟨⟨e, ?_, hwt⟩, mt⟩
    rwa [u1.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv'] at ht

/-- `St.pisOne`, keeping `MS`. -/
theorem St.pisOneM {d : Nat} (cert : Cert (.block (isOne d))) (hd : d ∈ LS) (bit : ∀ σ, E σ → V σ d ≤ 1) :
    VP (fun σ s => St P E A L V LS σ s ∧ MS P σ s) (.block (isOne d))
      fun σ s => (St P E A L V LS σ s ∧ MS P σ s) ∧ s.z = decide (V σ d = 1) :=
  VP.kv cert (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, m⟩ => by
    unfold isOne
    refine h.ldrM m hw hd (r := .r1) (by decide) fun s1 h1 hw1 m1 u1 => ?_
    refine wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ⟨⟨⟨e, h1.of_rest (f.rest []) f.mem,
      hw1.of (by rw [f.gpr]) (by rw [f.gpr]) (by rw [f.gpr]) f.wr⟩, m1.of_rest (f.rest []) f.mem⟩, ?_⟩
    rw [z, u1.gpr]
    have := bit σ e
    rcases (by omega : V σ d = 0 ∨ V σ d = 1) with h0 | h0 <;> rw [h0] <;> decide

/-- `avFlag`: Z iff `rand` is too short for the witness of iteration `k`. -/
theorem avFlag_vp {k : Nat} (hk : ∀ σ, E σ → P.L * (k + 1) ≤ P.rl) :
    VP (SI P E k) (.block avFlag) (fun σ s => SI P E k σ s ∧ s.z = decide (¬ P.L * (k + 1) + P.L ≤ P.rl)) := by
  have vU : ∀ σ, VI P k σ sUsed = P.L * (k + 1) := fun σ => by
    simp (config := {decide := true}) only [VI, upd, ↓reduceIte]
  rw [avFlag_eq]
  refine VP.block_append (G := fun σ s => SI P E k σ s ∧ s.gpr .r1 = BitVec.ofNat 32 P.rl) ?_
    (VP.block_append (G := fun σ s => SI P E k σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (P.rl - P.L * (k + 1))) ?_
    (VP.block_append (G := fun σ s => SI P E k σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (P.rl - P.L * (k + 1)) ∧
      s.gpr .r2 = BitVec.ofNat 32 P.L) ?_ ?_))
  · refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [h₁.1.2.1.sp, h₁.1.2.1.pre.sp, h₂.1.2.1.sp, h₂.1.2.1.pre.sp]) fun σ s ⟨⟨e, h, hw⟩, m⟩ => ?_
    refine h.ldrSp (o := aoRl) (by decide) fun s1 u1 => WP.block_nil ?_
    have r1 := u1.rest (ws := [.r1]) (by simp)
    exact ⟨⟨⟨e, h.of_rest r1 u1.mem, hw.rest r1⟩, m.of_upd u1⟩, by rw [u1.gpr, h.pre.aRl]⟩
  · refine VP.kv avUsed_taint (fun _ _ h => h.1.1.2.2) fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, p1⟩ => ?_
    have pre := h.pre
    have rlt := pre.rlt
    have hk' := hk σ e
    refine h.ldrM m hw (d := sUsed) (by decide) (by decide) fun t ht hwt mt u => ?_
    refine wp_dp (op2_reg _ _) fun t2 u2 => WP.block_nil ?_
    have r2 := u2.rest (ws := [.r1]) (by simp)
    refine ⟨⟨⟨e, ht.of_rest r2 u2.mem, hwt.rest r2⟩, mt.of_upd u2⟩, ?_⟩
    rw [u2.gpr, dpVal, u.other _ (by decide), p1, u.gpr, vU]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [h₁.1.1.2.1.sp, h₁.1.1.2.1.pre.sp, h₂.1.1.2.1.sp, h₂.1.1.2.1.pre.sp])
      fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, p1⟩ => ?_
    refine h.ldrSp (o := foL) (by decide) fun s1 u1 => WP.block_nil ?_
    have r1 := u1.rest (ws := [.r2]) (by simp)
    exact ⟨⟨⟨e, h.of_rest r1 u1.mem, hw.rest r1⟩, m.of_upd u1⟩, by rw [u1.other _ (by decide), p1],
      by rw [u1.gpr, h.pre.wL]⟩
  · refine VP.taint [.r1, .r2] carryTail_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, p1, p2⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]
    have pre := h.pre
    have hr : P.rl < 2 ^ 32 := pre.rlt
    have hl : P.L < 2 ^ 32 := by have := pre.k2; omega
    have hk' := hk σ e
    refine carry_ok fun s1 r1' m1 v1 => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil
      ⟨⟨⟨e, (h.of_rest r1' m1).of_rest (f.rest []) f.mem,
        (hw.rest r1').of (by rw [f.gpr]) (by rw [f.gpr]) (by rw [f.gpr]) f.wr⟩,
        (m.of_rest r1' m1).of_rest (f.rest []) f.mem⟩, ?_⟩
    rw [z, v1, p1, p2, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show P.rl - P.L * (k + 1) < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt hl]
    by_cases hc : P.L ≤ P.rl - P.L * (k + 1)
    · simp [hc]; omega
    · simp [hc]; omega

end

end VG.Proof.RsaKeyGen.Arm.Cand
