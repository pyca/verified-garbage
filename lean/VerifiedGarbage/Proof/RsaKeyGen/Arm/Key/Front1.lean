module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Loads
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Half
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Vals
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Arm.RvNumbers

/-! # An RSA key on ARMv7: the loads and the constants (`loads_vp`)

From the start of the body (`Bk`): every array zeroed, `p`, `q` and `e`
read, and the constants 1, 2, 3, `2^(32 W − 1)`, `2^(16 p_len − 1)` and
`2^33` set: the stage `S0`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The arrays after the loads. -/
def Aload (P : KP) (σ : State) : Nat → Nat := upd (upd (upd (fun _ => 0) aP0 (P0 P σ)) aQ0 (Q0 P σ)) aE P.e

/-- The arrays after the constants. -/
def A0 (P : KP) (σ : State) : Nat → Nat :=
  upd (upd (upd (upd (upd (upd (Aload P σ) aOne 1) aTwo 2) aThree 3) aMod (2 ^ (32 * P.W - 1)))
    aTop (2 ^ (16 * P.K - 1))) aC33 (2 ^ 33)

/-- The arrays the first stage knows. -/
abbrev L0 : List Nat := [aC33, aTop, aMod, aThree, aTwo, aOne, aZero, aD, aE, aQ0, aP0]

/-- The first stage, after the loads and the constants. -/
abbrev S0 (P : KP) (E : State → Prop) : State → State → Prop := St P E (A0 P) L0 (fun _ _ => 0) []

section
variable {P : KP}

theorem setupK_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ Bk P σ s) (.block setupK) (fun σ s => E σ ∧ Bk P σ s ∧ Ws s P.B P.Z P.W nArr ∧
      slot s.mem P.B 16 = P.W ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 hdr ∧
      s.gpr .lr = BitVec.ofNat 32 (nArr * (P.W + 2)) ∧ s.gpr .r3 = 0) := by
  rw [setupK_eq]
  refine VP.block_append (G := fun σ s => (E σ ∧ Bk P σ s) ∧ s.gpr .r8 = P.B) ?_
    (VP.block_append (G := fun σ s => ((E σ ∧ Bk P σ s) ∧ s.gpr .r8 = P.B) ∧ s.gpr .r9 = BitVec.ofNat 32 P.K)
      ?_ ?_)
  · show VP _ (.block ([(Reg.r8, aoS)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h⟩ => ?_
    · rw [h₁.2.sp, h₁.2.pre.sp, h₂.2.sp, h₂.2.pre.sp]
    · exact h.ldrSp (o := aoS) (by decide) (by decide) fun t u => WP.block_nil
        ⟨⟨e, h.of_rest (u.rest (ws := [.r8]) (by simp)) u.mem⟩, u.gpr.trans h.pre.aS⟩
  · show VP _ (.block ([(Reg.r9, aoPl)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h⟩, r8⟩ => ?_
    · rw [h₁.1.2.sp, h₁.1.2.pre.sp, h₂.1.2.sp, h₂.1.2.pre.sp]
    · exact h.ldrSp (o := aoPl) (by decide) (by decide) fun t u => WP.block_nil
        ⟨⟨⟨e, h.of_rest (u.rest (ws := [.r9]) (by simp)) u.mem⟩, by rw [u.other _ (by decide), r8]⟩,
          u.gpr.trans h.pre.aPl⟩
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
  refine VP.taint [.r0, .lr] zero_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨e, h, hw, cnt, p0, plr, r3⟩ => WP.mono (zero_ls h hw cnt p0 plr r3) fun t ht => ⟨e, ht⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.1]

/-- `loadArg o j`: array `j` := the number whose pointer and length are the
frame words `o` and `o + 4`. -/
theorem loadArg_vp {o j : Nat} {E : State → Prop} {A : State → Nat → Nat} {src : BitVec 32} {k : Nat}
    (cert : LCert j) (hj : j < nArr) (ho' : o + 8 ≤ 112) (ho4 : o % 4 = 0)
    (hin : ∀ σ, In P σ → fw σ.mem P o = src ∧ fw σ.mem P (o + 4) = BitVec.ofNat 32 k ∧
      InRegions (σ.rd ++ σ.wr) (State.addr src) k ∧ Region.Disjoint ⟨State.addr src, k⟩ P.rS ∧
      src.toNat + k ≤ 2 ^ 32 ∧ 0 < k ∧ k ≤ P.K) :
    VP (fun σ s => E σ ∧ LS P σ (A σ) s) (seqs (loadArg o j)) (fun σ s => E σ ∧
      LS P σ (upd (A σ) j (Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr src) k))) s) := by
  simp only [loadArg, seqs]
  refine VP.seq (G := fun σ s => (E σ ∧ LS P σ (A σ) s) ∧ s.gpr .r4 = src ∧ s.gpr .r6 = BitVec.ofNat 32 k) ?_ ?_
  · show VP _ (.block ([(Reg.r4, o), (Reg.r6, o + 4)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h⟩ => ?_
    · rw [h₁.2.bk.sp, h₁.2.bk.pre.sp, h₂.2.bk.sp, h₂.2.bk.pre.sp]
    · obtain ⟨e1, e2, -⟩ := hin σ h.bk.pre
      refine h.bk.ldrSp (o := o) (by omega) ho4 fun s1 u1 => ?_
      have r1 := u1.rest (ws := [.r4]) (by simp)
      have b1 := h.bk.of_rest r1 u1.mem
      refine b1.ldrSp (o := o + 4) (by omega) (by omega) fun t u2 => WP.block_nil ?_
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
    · obtain ⟨-, -, rd, sS, fit, hk, hkK⟩ := hin σ h.bk.pre
      refine WP.mono (load_okK h.bk h.ws hj rd sS fit hk hkK p4 p6) fun t ⟨bt, wt, k, v, r⟩ => ⟨e, bt, wt, ?_, ?_⟩
      · rw [k.slot (e := 16) (by decide) (by simp)]; exact h.cnt
      · intro i hi
        by_cases e' : i = j
        · subst e'; rw [upd_self, v]
        · rw [upd_ne _ _ e', ← h.full i hi]
          refine k.full (fun x hx ex => e' (by simp at hx; rw [← ex, hx])) (by simp) (h.bk.pre.fit hi)

/-- The stage of the loads, as a stage of the body. -/
theorem LS.st {E : State → Prop} {σ s : State} {A : State → Nat → Nat} {L : List Nat} (h : LS P σ (A σ) s)
    (e : E σ) (hl : ∀ j ∈ L, j < nArr ∧ A σ j < 2 ^ (32 * P.W)) : St P E A L (fun _ _ => 0) [] σ s := by
  refine ⟨e, ⟨h.bk.pre, h.bk.sp, h.bk.rd, h.bk.wr, h.bk.frame, h.cnt, fun j hj => ?_, fun _ h => absurd h List.not_mem_nil,
    fun j hj => (hl j hj).1, fun _ h => absurd h List.not_mem_nil⟩, h.ws⟩
  have f := h.full j (hl j hj).1
  have lt := (hl j hj).2
  rw [← f] at lt ⊢
  exact VG.Proof.Rsa.Arm.CrtValues.val32_low2 lt

theorem pow_mod_top (a : Nat) : 2 ^ a * ((0x80000000 : Nat) % 2 ^ 32) = 2 ^ (a + 31) := by
  rw [Nat.pow_add]; rfl

/-- The constants. -/
theorem consts_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ LS P σ (Aload P σ) s) (.block consts) (S0 P E) := by
  have st : VP (St P E (Aload P) L0 (fun _ _ => 0) []) (.block consts) (S0 P E) := by
    show VP _ (.block (setWd aOne 0 1 ++ (setWd aTwo 0 2 ++ (setWd aThree 0 3 ++ (setHi aMod 2 4 0x80000000 ++
      (setHi aTop 2 20 0x80000000 ++ setWd aC33 4 2)))))) _
    have z : ∀ σ j, j ∈ [aOne, aTwo, aThree, aMod, aTop, aC33] → Aload P σ j = 0 := by
      intro σ j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) only [Aload, upd, ↓reduceIte]
    refine VP.block_append (l₁ := setWd aOne 0 1) (St.psetWd one_taint (by simp) (by decide) (by decide)
      (by decide) fun σ _ => by rw [z σ aOne (by simp)]; exact Nat.two_pow_pos _) ?_
    refine VP.block_append (l₁ := setWd aTwo 0 2) (St.psetWd two_taint (by simp) (by decide) (by decide)
      (by decide) fun σ _ => by simp (config := {decide := true}) only [Aload, upd, ↓reduceIte] <;> exact Nat.two_pow_pos _) ?_
    refine VP.block_append (l₁ := setWd aThree 0 3) (St.psetWd three_taint (by simp) (by decide) (by decide)
      (by decide) fun σ _ => by simp (config := {decide := true}) only [Aload, upd, ↓reduceIte] <;> exact Nat.two_pow_pos _) ?_
    refine VP.block_append (l₁ := setHi aMod 2 4 0x80000000) (St.psetHi (i := fun P => P.W - 1) mod_taint (by simp)
      (by decide) (by decide) (by decide) (fun σ _ pre => by have := pre.wge; omega)
      fun σ _ _ => by simp (config := {decide := true}) only [Aload, upd, ↓reduceIte] <;> exact Nat.two_pow_pos _) ?_
    refine VP.block_append (l₁ := setHi aTop 2 20 0x80000000) (St.psetHi (i := fun P => P.W - 5) top_taint (by simp)
      (by decide) (by decide) (by decide) (fun σ _ pre => by have := pre.wge; omega)
      fun σ _ _ => by simp (config := {decide := true}) only [Aload, upd, ↓reduceIte] <;> exact Nat.two_pow_pos _) ?_
    refine (St.psetWd c33_taint (by simp) (by decide) (by decide) (by decide)
      fun σ _ => by simp (config := {decide := true}) only [Aload, upd, ↓reduceIte] <;> exact Nat.two_pow_pos _).mono
      (fun _ _ h => h) fun σ s h => h.mono (fun j hj => ⟨by mem_sub, ?_⟩)
        (fun d hd => ⟨hd, rfl⟩)
    have k1 := h.2.1.pre.k1
    have k8 := h.2.1.pre.k8
    have wge := h.2.1.pre.wge
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [A0, Aload, upd, ↓reduceIte, Nat.zero_add, pow_mod_top]
    all_goals (refine congrArg (2 ^ ·) ?_; simp only [KP.W] at *; omega)
  refine st.mono (fun σ s ⟨e, h⟩ => h.st e fun j hj => ⟨?_, ?_⟩) (fun _ _ h => h)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have pre := h.bk.pre
    have p8 : 2 ^ (8 * P.K) ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by simp only [KP.W]; omega)
    have p64 : 2 ^ 64 ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by have := pre.wge; omega)
    have := P0_lt P σ; have := Q0_lt P σ; have := pre.e_lt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [Aload, upd, ↓reduceIte] <;> first | exact Nat.two_pow_pos _ | omega

/-- The loads and the constants. -/
theorem loads_vp {E : State → Prop} : VP (fun σ s => E σ ∧ Bk P σ s) loads (S0 P E) := by
  have eL : loads = .seq (.block setupK) (.seq VG.Impl.Bignum.Arm.zero
      (.seq (.block [.ldrSp .r4 aoP, .ldrSp .r6 (aoP + 4)]) (.seq (VG.Impl.Rsa.Arm.CrtValues.load aP0)
      (.seq (.block [.ldrSp .r4 aoQ, .ldrSp .r6 (aoQ + 4)]) (.seq (VG.Impl.Rsa.Arm.CrtValues.load aQ0)
      (.seq (.block [.ldrSp .r4 aoE, .ldrSp .r6 (aoE + 4)]) (.seq (VG.Impl.Rsa.Arm.CrtValues.load aE)
        (.block consts)))))))) := rfl
  rw [eL]
  refine setupK_vp.seq (zero_vp.seq (VP.assoc ?_))
  refine (loadArg_vp (o := aoP) (A := fun _ _ => 0) (src := P.pP) (k := P.K) loadP_taint (by decide) (by decide)
    (by decide) fun σ h => ⟨h.aP, h.aPl, ⟨P.rP, List.mem_append_right _ (by rw [h.wr]; simp), Region.contains_self _ _⟩,
      h.sP.symm, h.fP, by have := h.k1; omega, Nat.le_refl _⟩).seq (VP.assoc ?_)
  refine (loadArg_vp (o := aoQ) (src := P.qP) (k := P.K) loadQ_taint (by decide) (by decide)
    (by decide) fun σ h => ⟨h.aQ, h.aQl, ⟨P.rQ, List.mem_append_right _ (by rw [h.wr]; simp), Region.contains_self _ _⟩,
      h.sQ.symm, h.fQ, by have := h.k1; omega, Nat.le_refl _⟩).seq (VP.assoc ?_)
  refine (loadArg_vp (o := aoE) (src := P.eP) (k := P.el) loadE_taint (by decide) (by decide)
    (by decide) fun σ h => ⟨h.aE, h.aEl, h.rdE, h.sE.symm, h.fE, h.el1, by have := h.el2; have := h.k1; omega⟩).seq
    (consts_vp.mono (fun σ s ⟨e, h⟩ => ⟨e, ⟨h.bk, h.ws, h.cnt, fun j hj => ?_⟩⟩) fun _ _ h => h)
  rw [h.full j hj]
  simp only [Aload, h.bk.pre.eB]

end

end VG.Proof.RsaKeyGen.Arm.Key
