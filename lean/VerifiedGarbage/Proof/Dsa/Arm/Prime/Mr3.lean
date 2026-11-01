module
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr1

import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr2
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint7
import VerifiedGarbage.Proof.Dsa.Arm.Prime.TaintD
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Vals

/-! # A candidate on ARMv7: a witness's octets (`witnessLoad_vp`)

In the iteration of witness `k` (`EK`: it is drawn, at offset `L (k + 1)`
of `rand`): its octets into `[aX]` (`xw`), and `used` advanced.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP sub32)
open VG.Proof.RsaKeyGen (goS shapeOf itersOf)
open VG.Proof.Dsa.Generation (DMrAt dmrS dwit dres)
open VG.Proof.Rsa (b2n)

/-- In the iteration of witness `k`, `n + 1` iterations left, the witness drawn. -/
abbrev EK (P : CP) (E : State → Prop) (k n : Nat) (σ : State) : Prop :=
  E σ ∧ DMrAt (cv P σ) (chP P) (taP P σ) (tmP P σ) P.D (rB P σ) k n ∧ P.D * k + P.D ≤ P.rl

/-- The offset of the witness's octets that are loaded: the last `len` of its `D`. -/
abbrev wo (P : CP) (k : Nat) : Nat := P.D * k + (P.D - P.len)

/-- The witness's number: its loaded octets. -/
def xw (P : CP) (σ : State) (k : Nat) : Nat := Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg (rB P σ) (wo P k) P.len)

section
variable {P : CP}

theorem xw_lt (P : CP) (σ : State) (k : Nat) : xw P σ k < 2 ^ (8 * P.len) := by
  have := VG.Proof.Rsa.lt_of_os2ip (VG.Proof.RsaKeyGen.seg (rB P σ) (wo P k) P.len)
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  have hl : (VG.Proof.RsaKeyGen.seg (rB P σ) (wo P k) P.len).length ≤ P.len := by
    simp [VG.Proof.RsaKeyGen.seg, Nat.min_le_left]
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))

/-- The witness's octets. -/
theorem xw_bytes {σ : State} (pre : In P σ) {u : Nat} (hu : u + P.len ≤ P.rl) :
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr (P.nP + BitVec.ofNat 32 u)) P.len) =
      Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg (rB P σ) u P.len) := by
  have := pre.fR; have := pre.sizes
  rw [addr_add (by omega), seg_bytesAt _ _ hu]

/-- The witness's octets are in `rand`. -/
theorem In.witIn {σ : State} (pre : In P σ) {u : Nat} (hu : u + P.len ≤ P.rl) :
    InRegions (σ.rd ++ σ.wr) (State.addr (P.nP + BitVec.ofNat 32 u)) P.len ∧
      (∀ r ∈ P.chg, Region.Disjoint ⟨State.addr (P.nP + BitVec.ofNat 32 u), P.len⟩ r) ∧
      (P.nP + BitVec.ofNat 32 u).toNat + P.len ≤ 2 ^ 32 ∧ 0 < P.len ∧ P.len ≤ P.L := by
  have fR := pre.fR; have sz := pre.sizes; have rlt := pre.rlt
  have ea : State.addr (P.nP + BitVec.ofNat 32 u) = State.addr P.nP + BitVec.ofNat 64 u := addr_add (by omega)
  refine ⟨?_, ?_, ?_, by omega, sz.2.2.2.1⟩
  · rw [ea]; exact CallLay.inRegions_sub (off := u) (l := P.len) pre.rdR hu (by omega)
  · have sub : Region.Sub ⟨State.addr (P.nP + BitVec.ofNat 32 u), P.len⟩ P.rR := by
      rw [ea]; exact Offset.sub_base (State.addr P.nP) (d := u) (n := P.len) (k := P.rl) hu
    intro r hr
    simp only [CP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact pre.sR.symm.sub_left sub
    · exact pre.uR.symm.sub_left sub
    · exact pre.rC.sub_left sub
    · exact (pre.rF.sub_right (Offset.sub_base _ (d := 0) (n := 4) (k := 56) (by decide) |> fun s => by
        simpa only [BitVec.add_zero] using s)).sub_left sub
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := u) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem wlBlock_eq : ([.ldrSp .r4 aoR, .ldr .r1 .r8 sUsed, .dp .add .r4 .r4 (.reg .r1), .ldrSp .r6 aoPl,
    .dp .add .r4 .r4 (.reg .r6), .dp .add .r1 .r1 (.reg .r6), .str .r1 .r8 sUsed, .ldrSp .r6 aoEl,
    .dp .sub .r4 .r4 (.reg .r6)] : List Instr) =
    ([(Reg.r4, aoR)].map fun p => Instr.ldrSp p.1 p.2) ++ (([.ldr .r1 .r8 sUsed, .dp .add .r4 .r4 (.reg .r1)] : List Instr) ++
      (([(Reg.r6, aoPl)].map fun p => Instr.ldrSp p.1 p.2) ++
        (([.dp .add .r4 .r4 (.reg .r6), .dp .add .r1 .r1 (.reg .r6), .str .r1 .r8 sUsed] : List Instr) ++
          (([(Reg.r6, aoEl)].map fun p => Instr.ldrSp p.1 p.2) ++ ([.dp .sub .r4 .r4 (.reg .r6)] : List Instr))))) :=
  rfl

/-- The witness's octets into `[aX]`, and `used` advanced by `D`. -/
theorem witnessLoad_vp {E : State → Prop} {k : Nat} (hE : ∀ σ, E σ → In P σ ∧ P.D * k + P.D ≤ P.rl) :
    VP (fun σ s => St P E (AB2 P) LB2 (VI P k) LSI σ s ∧ MS P σ s) (seqs Impl.Dsa.Arm.ProbablePrime.witnessLoad)
      (fun σ s => St P E (fun σ => upd (AB2 P σ) aX (xw P σ k)) (aX :: LB2)
        (fun σ => upd (VI P k σ) sUsed (P.D * k + P.D)) (sUsed :: LSI) σ s ∧ MS P σ s) := by
  simp only [Impl.Dsa.Arm.ProbablePrime.witnessLoad, seqs]
  rw [wlBlock_eq]
  have vU : ∀ σ, VI P k σ sUsed = P.D * k := fun σ => by
    simp (config := {decide := true}) only [VI, upd, ↓reduceIte]
  let S0 := fun σ s => St P E (AB2 P) LB2 (VI P k) LSI σ s ∧ MS P σ s
  let S1 := fun σ s => St P E (AB2 P) LB2 (fun σ => upd (VI P k σ) sUsed (P.D * k + P.D)) (sUsed :: LSI) σ s ∧
    MS P σ s
  refine VP.seq (VP.block_append (G := fun σ s => S0 σ s ∧ s.gpr .r4 = P.nP) ?_
    (VP.block_append (G := fun σ s => S0 σ s ∧
      s.gpr .r4 = P.nP + BitVec.ofNat 32 (P.D * k) ∧ s.gpr .r1 = BitVec.ofNat 32 (P.D * k)) ?_
    (VP.block_append (G := fun σ s => S0 σ s ∧
      s.gpr .r4 = P.nP + BitVec.ofNat 32 (P.D * k) ∧ s.gpr .r1 = BitVec.ofNat 32 (P.D * k) ∧
      s.gpr .r6 = BitVec.ofNat 32 P.D) ?_
    (VP.block_append (G := fun σ s => S1 σ s ∧ s.gpr .r4 = P.nP + BitVec.ofNat 32 (P.D * k + P.D)) ?_
    (VP.block_append (G := fun σ s => S1 σ s ∧ s.gpr .r4 = P.nP + BitVec.ofNat 32 (P.D * k + P.D) ∧
      s.gpr .r6 = BitVec.ofNat 32 P.len) ?_
      (H := fun σ s => S1 σ s ∧ s.gpr .r4 = P.nP + BitVec.ofNat 32 (wo P k) ∧
        s.gpr .r6 = BitVec.ofNat 32 P.len) ?_))))) ?_
  · refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [h₁.1.2.1.sp, h₁.1.2.1.pre.sp, h₂.1.2.1.sp, h₂.1.2.1.pre.sp]) fun σ s ⟨⟨e, h, hw⟩, m⟩ => ?_
    refine h.ldrSp (o := aoR) (by decide) fun s1 u1 => WP.block_nil ?_
    have r1 := u1.rest (ws := [.r4]) (by simp)
    exact ⟨⟨⟨e, h.of_rest r1 u1.mem, hw.rest r1⟩, m.of_upd u1⟩, by rw [u1.gpr, h.pre.aR]⟩
  · refine VP.kv wl1_taint (fun _ _ h => h.1.1.2.2) fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, p4⟩ => ?_
    refine h.ldrM m hw (d := sUsed) (by decide) (by decide) fun t ht hwt mt u => ?_
    refine wp_dp (op2_reg _ _) fun t2 u2 => WP.block_nil ?_
    have r2 := u2.rest (ws := [.r4]) (by simp)
    refine ⟨⟨⟨e, ht.of_rest r2 u2.mem, hwt.rest r2⟩, mt.of_upd u2⟩, ?_, ?_⟩
    · rw [u2.gpr, dpVal, u.other _ (by decide), p4, u.gpr, vU]
    · rw [u2.other _ (by decide), u.gpr, vU]
  · refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [h₁.1.1.2.1.sp, h₁.1.1.2.1.pre.sp, h₂.1.1.2.1.sp, h₂.1.1.2.1.pre.sp])
      fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, p4, p1⟩ => ?_
    refine h.ldrSp (o := aoPl) (by decide) fun s1 u1 => WP.block_nil ?_
    have r1 := u1.rest (ws := [.r6]) (by simp)
    exact ⟨⟨⟨e, h.of_rest r1 u1.mem, hw.rest r1⟩, m.of_upd u1⟩, by rw [u1.other _ (by decide), p4],
      by rw [u1.other _ (by decide), p1], by rw [u1.gpr, h.pre.aPl]⟩
  · refine VP.kv wl2d_taint (fun _ _ h => h.1.1.2.2) fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, p4, p1, p6⟩ => ?_
    have pre := h.pre
    have hu := (hE σ e).2; have rlt := pre.rlt
    refine wp_dp (op2_reg _ _) fun t0 u0 => wp_dp (op2_reg _ _) fun t u => ?_
    have r0 := u0.rest (ws := [.r4]) (by simp)
    have r := u.rest (ws := [.r1]) (by simp)
    have v1 : (t.gpr .r1).toNat = P.D * k + P.D := by
      rw [u.gpr, dpVal, u0.other _ (by decide), u0.other _ (by decide), p1, p6, BitVec.toNat_add,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := P.D * k) (by omega),
        Nat.mod_eq_of_lt (a := P.D) (by omega), Nat.mod_eq_of_lt (by omega)]
    have v4 : t.gpr .r4 = P.nP + BitVec.ofNat 32 (P.D * k + P.D) := by
      rw [u.other _ (by decide), u0.gpr, dpVal, p4, p6, BitVec.add_assoc, BitVec.ofNat_add]
    have h0 := (h.of_rest r0 u0.mem).of_rest r (by rw [u.mem])
    refine h0.strM ((m.of_upd u0).of_upd u) ((hw.of_upd u0 (by decide) (by decide) (by decide)).of_upd u
      (by decide) (by decide) (by decide)) (d := sUsed)
      (by decide) fun t2 h2 hw2 m2 g2 => WP.block_nil ⟨⟨⟨e, by rw [v1] at h2; exact h2, hw2⟩, m2⟩, ?_⟩
    rw [g2, v4]
  · refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [h₁.1.1.2.1.sp, h₁.1.1.2.1.pre.sp, h₂.1.1.2.1.sp, h₂.1.1.2.1.pre.sp])
      fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, p4⟩ => ?_
    refine h.ldrSp (o := aoEl) (by decide) fun s1 u1 => WP.block_nil ?_
    have r1 := u1.rest (ws := [.r6]) (by simp)
    exact ⟨⟨⟨e, h.of_rest r1 u1.mem, hw.rest r1⟩, m.of_upd u1⟩, by rw [u1.other _ (by decide), p4],
      by rw [u1.gpr, h.pre.aEl]⟩
  · refine VP.kv wl3d_taint (fun _ _ h => h.1.1.2.2) fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, p4, p6⟩ => ?_
    have pre := h.pre
    have hu := (hE σ e).2; have sz := pre.sizes
    refine wp_dp (op2_reg _ _) fun t u => WP.block_nil ?_
    have r := u.rest (ws := [.r4]) (by simp)
    refine ⟨⟨⟨e, h.of_rest r u.mem, hw.rest r⟩, m.of_upd u⟩, ?_, by rw [u.other _ (by decide), p6]⟩
    rw [u.gpr, dpVal, p4, p6, show P.D * k + P.D = wo P k + P.len by simp only [wo]; omega,
      BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]
  · refine ((VP.withMS (P := P) (St.pload (E := E) (A := AB2 P) (L := LB2)
      (V := fun σ => upd (VI P k σ) sUsed (P.D * k + P.D)) (LS := sUsed :: LSI)
      (src := fun P => P.nP + BitVec.ofNat 32 (wo P k)) (k := fun P => P.len) loadX_taint (by decide)
      fun σ e pre => pre.witIn (by have := (hE σ e).2; have := pre.sizes; simp only [wo]; omega))
      (fun σ s h => h.1.inSp) ?_).mono
      (fun σ s ⟨⟨h, m⟩, p4, p6⟩ => ⟨⟨h, p4, p6⟩, m⟩) fun σ s ⟨h, m⟩ => ⟨h.mono ?_ fun d hd => ⟨hd, rfl⟩, m⟩)
    · intro σ s ⟨⟨e, h, hw⟩, p4, p6⟩
      obtain ⟨rd, sC, fit, hk, hkL⟩ := h.pre.witIn (u := wo P k)
        (by have := (hE σ e).2; have := h.pre.sizes; simp only [wo]; omega)
      exact WP.mono (load_okC h.bk hw (by decide) rd sC fit hk hkL p4 p6) fun t ⟨_, _, kp, _, r⟩ =>
        ⟨[aX], [], kp, by simp only [List.mem_singleton, forall_eq]; decide, by simp, r.sp, r.rd, r.wr⟩
    · intro j hj
      refine ⟨hj, ?_⟩
      show upd (AB2 P σ) aX _ j = upd (AB2 P σ) aX _ j
      rw [xw_bytes h.2.1.pre (by have := (hE σ h.1).2; have := h.2.1.pre.sizes; simp only [wo]; omega)]
      rfl

end

end VG.Proof.Dsa.Arm.Prime
