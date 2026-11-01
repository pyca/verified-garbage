module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr1
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.TaintD
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont7
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Vals

/-! # A candidate on ARMv7: Miller–Rabin's start (`mrInit_vp`)

`i := 1`, `uniform := 0` and the checks `checksW w` (`checksC`, from the
comparisons of `W`): the stage before the first witness.
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

section
variable {P : CP}

theorem MS.of_upd {σ s t : State} (m : MS P σ s) {r : Reg} {v : BitVec 32} (u : Upd s t r v) : MS P σ t :=
  ⟨m.toMSp.of_same u.mem u.sp u.rd u.wr, by rw [u.mem]; exact m.stride⟩

theorem MS.of_rest {σ s t : State} (m : MS P σ s) {rs : List Reg} (r : Rest rs s t) (mem : t.mem = s.mem) :
    MS P σ t :=
  ⟨m.toMSp.of_same mem r.sp r.rd r.wr, by rw [mem]; exact m.stride⟩

theorem mrInit_vp {E : State → Prop} (hE : ∀ σ, E σ → In P σ ∧ EM P σ) :
    VP (SM P E) (.block Impl.Dsa.Arm.ProbablePrime.mrInit) (MRI P E (Nt P + 1)) := by
  have eI : Impl.Dsa.Arm.ProbablePrime.mrInit = (setS sI 1 ++ setS sUni 0) ++
      (([(Reg.r1, Impl.Dsa.Arm.ProbablePrime.aoChk)].map fun p => Instr.ldrSp p.1 p.2) ++
        ([.str .r1 .r8 sChk] : List Instr)) := rfl
  rw [eI]
  refine VP.block_append (G := fun σ s => St P E (AB2 P) LB2 (fun σ => upd (upd (V3 P σ) sI 1) sUni 0)
    [sUni, sI, sUsed] σ s ∧ MS P σ s) ?_ ?_
  · refine VP.kv mrInit1_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, m⟩ => ?_
    simp only [setS, List.cons_append, List.nil_append]
    refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
    refine (h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem).strM (m.of_upd u1)
      (hw.of_upd u1 (by decide) (by decide) (by decide)) (d := sI) (by decide) fun s2 h2 hw2 m2 g2 => ?_
    refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
    refine (h2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem).strM (m2.of_upd u3)
      (hw2.of_upd u3 (by decide) (by decide) (by decide)) (d := sUni) (by decide) fun s4 h4 hw4 m4 _ =>
        WP.block_nil ⟨⟨e, h4.mono (fun j hj => ⟨hj, rfl⟩) fun d hd => ⟨hd, ?_⟩, hw4⟩, m4⟩
    have v1 : (s1.gpr .r1).toNat = 1 := by rw [u1.gpr]; rfl
    have v3 : (s3.gpr .r1).toNat = 0 := by rw [u3.gpr]; rfl
    rw [v1, v3]
  refine VP.block_append (G := fun σ s => (St P E (AB2 P) LB2 (fun σ => upd (upd (V3 P σ) sI 1) sUni 0)
    [sUni, sI, sUsed] σ s ∧ MS P σ s) ∧ s.gpr .r1 = BitVec.ofNat 32 (chP P)) ?_ ?_
  · refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, hw⟩, m⟩ => ?_
    · rw [h₁.1.2.1.sp, h₁.1.2.1.pre.sp, h₂.1.2.1.sp, h₂.1.2.1.pre.sp]
    · refine h.ldrSp (o := Impl.Dsa.Arm.ProbablePrime.aoChk) (by decide) fun t u => WP.block_nil ?_
      have r := u.rest (ws := [.r1]) (by simp)
      exact ⟨⟨⟨e, h.of_rest r u.mem, hw.rest r⟩, m.of_upd u⟩, by rw [u.gpr, h.pre.aChk]⟩
  refine VP.kv strChk_taint (fun _ _ h => h.1.1.2.2) fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, r1⟩ => ?_
  have pre := h.pre
  obtain ⟨fr, fw, fn⟩ := mr_facts pre (hE σ e).2
  have sz := pre.sizes
  refine h.strM m hw (d := sChk) (by decide) fun t ht hwt mt _ => WP.block_nil ⟨by omega, Nat.le_refl _, ?_, ⟨e, ?_, hwt⟩, mt⟩
  · rw [Nat.sub_self, Nat.add_sub_cancel, fn, ← rB_length P σ]
    exact VG.Proof.Dsa.Generation.dmrAt_zero fw (by omega)
  · have hc : chP P < 2 ^ 32 := by simp only [chP, Spec.Dsa.primeChecks]; split <;> decide
    rw [r1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc] at ht
    refine ht.mono (fun j hj => ⟨hj, rfl⟩) fun j hj => ⟨by mem_sub, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · simp (config := {decide := true}) only [upd, ↓reduceIte, VI, Nat.sub_self, dmrS]
    · simp (config := {decide := true}) only [upd, ↓reduceIte, VI, Nat.sub_self, dmrS]
    · simp (config := {decide := true}) only [upd, ↓reduceIte, VI, V3, V2, V1, V0, Nat.sub_self, Nat.mul_zero]
    · simp (config := {decide := true}) only [upd, ↓reduceIte, VI]

end

end VG.Proof.Dsa.Arm.Prime
