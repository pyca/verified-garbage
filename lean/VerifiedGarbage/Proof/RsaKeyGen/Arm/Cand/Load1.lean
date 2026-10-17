module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Front
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Ops
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Vals
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the working space and the candidate (`loadC_vp`)

From the start of the body (`Bk`), once `rand` has `out_len` octets: every
array zeroed, the candidate `c` read and its bits set, the constants 1 and
2, and `used := out_len`: the stage `S0`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.RsaKeyGen.Arm.Key (setWd)

/-- The arrays after the loads and the constants. -/
def A0 (P : CP) (σ : State) : Nat → Nat := upd (upd (upd (fun _ => 0) aC (cv P σ)) aOne 1) aTwo 2

abbrev L0 : List Nat := [aTwo, aOne, aC, aZero, aBnd]

/-- The header words after the candidate. -/
def V0 (P : CP) : Nat → Nat := upd (fun _ => 0) sUsed P.L

/-- The first stage, after the candidate. -/
abbrev S0 (P : CP) (E : State → Prop) : State → State → Prop := St P E (A0 P) L0 (fun _ => V0 P) [sUsed]

section
variable {P : CP}

theorem setupC_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ Bk P σ s) (.block setupC) (fun σ s => E σ ∧ Bk P σ s ∧ Ws s P.B P.Z P.W nArr ∧
      slot s.mem P.B 16 = P.W ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 hdr ∧
      s.gpr .lr = BitVec.ofNat 32 (nArr * (P.W + 2)) ∧ s.gpr .r3 = 0) := by
  rw [setupC_eq]
  refine VP.block_append (G := fun σ s => (E σ ∧ Bk P σ s) ∧ s.gpr .r8 = P.B) ?_
    (VP.block_append (G := fun σ s => ((E σ ∧ Bk P σ s) ∧ s.gpr .r8 = P.B) ∧ s.gpr .r9 = BitVec.ofNat 32 P.L)
      ?_ ?_)
  · show VP _ (.block ([(Reg.r8, aoS)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h⟩ => ?_
    · rw [h₁.2.sp, h₁.2.pre.sp, h₂.2.sp, h₂.2.pre.sp]
    · exact h.ldrSp (o := aoS) (by decide) fun t u => WP.block_nil
        ⟨⟨e, h.of_rest (u.rest (ws := [.r8]) (by simp)) u.mem⟩, u.gpr.trans h.pre.aS⟩
  · show VP _ (.block ([(Reg.r9, foL)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h⟩, r8⟩ => ?_
    · rw [h₁.1.2.sp, h₁.1.2.pre.sp, h₂.1.2.sp, h₂.1.2.pre.sp]
    · exact h.ldrSp (o := foL) (by decide) fun t u => WP.block_nil
        ⟨⟨⟨e, h.of_rest (u.rest (ws := [.r9]) (by simp)) u.mem⟩, by rw [u.other _ (by decide), r8]⟩,
          u.gpr.trans h.pre.wL⟩
  · refine VP.taint [.r8, .r9] setupTail_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨⟨e, h⟩, r8⟩, r9⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.1.2, h₂.1.2]
      · rw [h₁.2, h₂.2]
    · exact WP.mono (setupTail_ok h r8 r9) fun t ⟨bt, wt, ct, p0, plr, r3⟩ => ⟨e, bt, wt, ct, p0, plr, r3⟩

theorem zero_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ Bk P σ s ∧ Ws s P.B P.Z P.W nArr ∧ slot s.mem P.B 16 = P.W ∧
      s.gpr .r0 = P.B + BitVec.ofNat 32 hdr ∧ s.gpr .lr = BitVec.ofNat 32 (nArr * (P.W + 2)) ∧
      s.gpr .r3 = 0) VG.Impl.Bignum.Arm.zero (fun σ s => E σ ∧ LS P σ (fun _ => 0) s) := by
  refine VP.taint [.r0, .lr] VG.Proof.RsaKeyGen.Arm.Key.zero_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨e, h, hw, cnt, p0, plr, r3⟩ => WP.mono (zero_ls h hw cnt p0 plr r3) fun t ht => ⟨e, ht⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.1]

/-- `[j] :=` the number whose pointer and length are the frame words `o1`
and `o2`. -/
theorem loadArg_vp {o1 o2 j : Nat} {E : State → Prop} {A : State → Nat → Nat} {src : CP → BitVec 32}
    {k : CP → Nat} (cert : LCert j) (hj : j < nArr) (h1 : FwOk o1) (h2 : FwOk o2)
    (hin : ∀ σ, E σ → In P σ → fw σ.mem P o1 = src P ∧ fw σ.mem P o2 = BitVec.ofNat 32 (k P) ∧
      InRegions (σ.rd ++ σ.wr) (State.addr (src P)) (k P) ∧
      (∀ r ∈ P.chg, Region.Disjoint ⟨State.addr (src P), k P⟩ r) ∧
      (src P).toNat + k P ≤ 2 ^ 32 ∧ 0 < k P ∧ k P ≤ P.L) :
    VP (fun σ s => E σ ∧ LS P σ (A σ) s)
      (.seq (.block [.ldrSp .r4 o1, .ldrSp .r6 o2]) (VG.Impl.Rsa.Arm.CrtValues.load j)) (fun σ s => E σ ∧
      LS P σ (upd (A σ) j (Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr (src P)) (k P)))) s) := by
  refine VP.seq (G := fun σ s => (E σ ∧ LS P σ (A σ) s) ∧ s.gpr .r4 = src P ∧
    s.gpr .r6 = BitVec.ofNat 32 (k P)) ?_ ?_
  · show VP _ (.block ([(Reg.r4, o1), (Reg.r6, o2)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h⟩ => ?_
    · rw [h₁.2.bk.sp, h₁.2.bk.pre.sp, h₂.2.bk.sp, h₂.2.bk.pre.sp]
    · obtain ⟨e1, e2, -⟩ := hin σ e h.bk.pre
      refine h.bk.ldrSp (o := o1) h1 fun s1 u1 => ?_
      have r1 := u1.rest (ws := [.r4]) (by simp)
      have b1 := h.bk.of_rest r1 u1.mem
      refine b1.ldrSp (o := o2) h2 fun t u2 => WP.block_nil ?_
      have r2 := u2.rest (ws := [.r6]) (by simp)
      refine ⟨⟨e, ⟨b1.of_rest r2 u2.mem, (h.ws.rest r1).rest r2, by rw [u2.mem, u1.mem]; exact h.cnt,
        by rw [u2.mem, u1.mem]; exact h.full⟩⟩, by rw [u2.other .r4 (by simp), u1.gpr, e1], by rw [u2.gpr, e2]⟩
  · refine VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h⟩, p4, p6⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl)
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]
      · rw [h₁.1.2.ws.r7, h₂.1.2.ws.r7]
      · rw [h₁.1.2.ws.r8, h₂.1.2.ws.r8]
      · rw [h₁.1.2.ws.r9, h₂.1.2.ws.r9]
    · obtain ⟨-, -, rd, sC, fit, hk, hkL⟩ := hin σ e h.bk.pre
      refine WP.mono (load_okC h.bk h.ws hj rd sC fit hk hkL p4 p6) fun t ⟨bt, wt, k, v, r⟩ => ⟨e, bt, wt, ?_, ?_⟩
      · rw [k.slot (e := 16) (by decide) (by simp)]; exact h.cnt
      · intro i hi
        by_cases e' : i = j
        · subst e'; rw [upd_self, v]
        · rw [upd_ne _ _ e', ← h.full i hi]
          refine k.full (fun x hx ex => e' (by simp at hx; rw [← ex, hx])) (by simp) (h.bk.pre.fit hi)

/-- The stage of the loads, as a stage of the body. -/
theorem LS.st {E : State → Prop} {σ s : State} {A : State → Nat → Nat} {L : List Nat} (h : LS P σ (A σ) s)
    (e : E σ) (hl : ∀ j ∈ L, j < nArr ∧ A σ j < 2 ^ (32 * P.W)) : St P E A L (fun _ _ => 0) [] σ s := by
  refine ⟨e, ⟨h.bk.pre, h.bk.sp, h.bk.rd, h.bk.wr, h.bk.frame, h.cnt, fun j hj => ?_,
    fun _ h => absurd h List.not_mem_nil, fun j hj => (hl j hj).1, fun _ h => absurd h List.not_mem_nil⟩, h.ws⟩
  have f := h.full j (hl j hj).1
  have lt := (hl j hj).2
  rw [← f] at lt ⊢
  exact VG.Proof.Rsa.Arm.CrtValues.val32_low2 lt

/-- The candidate's arrays after its load. -/
def AL (P : CP) (σ : State) : Nat → Nat := upd (fun _ => 0) aC (xv P σ)

/-- The bits of the candidate, the constants, and `used := out_len`. -/
theorem candBits_vp {E : State → Prop} :
    VP (St P E (AL P) [aTwo, aOne, aC, aZero, aBnd] (fun _ _ => 0) []) (.block candBits) (S0 P E) := by
  rw [candBits_eq]
  refine VP.block_append (G := fun σ s => St P E (AL P) [aTwo, aOne, aC, aZero, aBnd] (fun _ _ => 0) [] σ s ∧
    s.gpr .r1 = BitVec.ofNat 32 P.L) ?_ ?_
  · refine VP.ldrSp (c := [(Reg.r1, foL)]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
    · exact h.ldrSp (o := foL) (by decide) fun t u => WP.block_nil
        ⟨⟨e, h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, hw.of_upd u (by decide) (by decide) (by decide)⟩,
          u.gpr.trans h.pre.wL⟩
  have hu : VP (fun σ s => St P E (AL P) [aTwo, aOne, aC, aZero, aBnd] (fun _ _ => 0) [] σ s ∧
      s.gpr .r1 = BitVec.ofNat 32 P.L) (.block [.str .r1 .r8 sUsed])
      (St P E (AL P) [aTwo, aOne, aC, aZero, aBnd] (fun _ => V0 P) [sUsed]) := by
    refine VP.kv usedL_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, r1⟩ => ?_
    refine h.str hw (by decide) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
    have pre := h.pre
    rw [r1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := pre.k2; omega)] at ht
    exact ht
  refine VP.block_append hu ?_
  have gT : ∀ σ, (fun _ => True) σ → In P σ → AL P σ aC % 2 ^ (32 * (P.W - 3)) +
      2 ^ (32 * (P.W - 3)) * ((BitVec.ofNat 32 (AL P σ aC / 2 ^ (32 * (P.W - 3)) % 2 ^ 32)) ||| 0xC0000000#32).toNat +
      2 ^ (32 * (P.W - 3 + 1)) * (AL P σ aC / 2 ^ (32 * (P.W - 3 + 1))) =
        xv P σ % 2 ^ (8 * P.L - 2) + 3 * 2 ^ (8 * P.L - 2) := fun σ _ pre => by
    have wE := pre.W_eq; have lE := pre.L_eq; have w4 := pre.w4
    have hx : xv P σ < 2 ^ (32 * (P.W - 3) + 32) := by
      have := xv_lt P σ; rwa [show 32 * (P.W - 3) + 32 = 8 * P.L by omega]
    simp only [AL, upd_self]
    rw [topBits_val hx, show 32 * (P.W - 3) + 30 = 8 * P.L - 2 by omega]
  have ht : VP (St P E (AL P) [aTwo, aOne, aC, aZero, aBnd] (fun _ => V0 P) [sUsed]) (.block topBits)
      (St P E (fun σ => upd (AL P σ) aC (xv P σ % 2 ^ (8 * P.L - 2) + 3 * 2 ^ (8 * P.L - 2)))
        [aC, aTwo, aOne, aC, aZero, aBnd] (fun _ => V0 P) [sUsed]) := by
    rw [topBits_eq]
    exact (St.phiOp (i := fun P => P.W - 3) (f := fun x => x ||| 0xC0000000#32)
      (g := fun σ => xv P σ % 2 ^ (8 * P.L - 2) + 3 * 2 ^ (8 * P.L - 2))
      (by rw [← topBits_eq]; exact topBits_taint) (by simp) (by decide)
      (fun σ _ pre => by have := pre.wge; omega)
      (fun u R k' => wp_dp (op2_imm (by decide)) fun u' up => WP.block_nil (k' u' up))
      (fun σ _ pre => gT σ trivial pre))
  refine VP.block_append ht ?_
  refine VP.block_append (l₁ := orOne aC) (St.porOne orOneC_taint (by simp)) ?_
  refine VP.block_append (l₁ := setWd aOne 0 1) (St.psetWd one_taint (by simp) (by decide) (by decide)
    (by decide) fun σ _ => by simp (config := {decide := true}) only [AL, upd, ↓reduceIte]) ?_
  refine (St.psetWd two_taint (by simp) (by decide) (by decide)
    (by decide) fun σ _ => by simp (config := {decide := true}) only [AL, upd, ↓reduceIte]).mono (fun _ _ h => h)
    fun σ s h => h.mono (fun j hj => ⟨by mem_sub, ?_⟩) fun d hd => ⟨hd, rfl⟩
  have pre := h.2.1.pre
  have lE := pre.L_eq; have w4 := pre.w4
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [A0, AL, upd, ↓reduceIte, Nat.zero_add]
  rw [cv, candidate_eq (by omega) (xv_lt P σ)]

/-- The working space, the candidate, the constants and `used`. -/
theorem loadC_vp {E : State → Prop} (hE : ∀ σ, E σ → In P σ ∧ P.L ≤ P.rl) :
    VP (fun σ s => E σ ∧ Bk P σ s) (seqs loadC) (S0 P E) := by
  simp only [loadC, seqs]
  refine setupC_vp.seq (zero_vp.seq (VP.assoc ?_))
  refine (loadArg_vp (o1 := aoR) (o2 := foL) (A := fun _ _ => 0) (src := fun P => P.nP) (k := fun P => P.L)
    loadC_taint (by decide) (by decide) (by decide) fun σ e h => ⟨h.aR, h.wL, ?_, ?_, ?_, by have := h.k1; omega,
      Nat.le_refl _⟩).seq ?_
  · have := (hE σ e).2
    exact CallLay.inRegions_sub (off := 0) (l := P.L) h.rdR (by omega) (by have := h.rlt; omega) |> fun r => by
      simpa only [BitVec.add_zero] using r
  · have := (hE σ e).2
    have sub : Region.Sub ⟨State.addr P.nP, P.L⟩ P.rR := by
      have := Offset.sub_base (State.addr P.nP) (d := 0) (n := P.L) (k := P.rl) (by omega)
      simpa only [BitVec.add_zero] using this
    intro r hr
    simp only [CP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.sR.symm.sub_left sub
    · exact h.oR.symm.sub_left sub
    · exact h.uR.symm.sub_left sub
    · exact h.rC.sub_left sub
    · exact (h.rF.sub_right (Offset.sub_base _ (d := 0) (n := 4) (k := 56) (by decide) |> fun s => by
        simpa only [BitVec.add_zero] using s)).sub_left sub
  · have := (hE σ e).2; have := h.fR; omega
  refine candBits_vp.mono (fun σ s ⟨e, h⟩ => h.st e fun j hj => ⟨?_, ?_⟩) (fun _ _ h => h)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
  · have pre := h.bk.pre
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    have := xv_lt P σ
    have : 2 ^ (8 * P.L) ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by simp only [CP.W]; omega)
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) only [AL, upd, ↓reduceIte] <;>
      first | exact Nat.two_pow_pos _ | omega

end

end VG.Proof.RsaKeyGen.Arm.Cand
