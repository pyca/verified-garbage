module

public import VerifiedGarbage.Proof.Rsa.Arm.RvCand1
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: `y = g^r` (`expLoop_vp`)

Each step takes the low bit of `r`'s copy, halves it, multiplies `y` by
`g^(2^i)` or 1 (in Montgomery form) and squares `g^(2^i)`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- A piece from a stage with a fact about the public parameters. -/
theorem VP.pure {F G : State → State → Prop} {c : Prog isa} {p : Prop} (h : p → VP F c G) :
    VP (fun σ s => p ∧ F σ s) c G :=
  ⟨fun σ s ⟨hp, hs⟩ => (h hp).wp σ s hs, fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, ⟨hp, h₁⟩, ⟨_, h₂⟩⟩ e₁ e₂ =>
    (h hp).ct s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, h₁, h₂⟩ e₁ e₂⟩

section
variable {P : RP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {AW : State → Nat → Nat}
  {LW : List Nat} {V : State → Nat → Nat} {LS : List Nat}

/-- The low bit of `r`'s copy into `sBit`, and `r11 := 0`. -/
theorem St.pexpTail (hj : wRc ∈ LW) :
    VP (St P E A L AW LW V LS P.W 22) (.block expTail) (fun σ s =>
      St P E A L AW LW (fun σ => upd (V σ) sBit (AW σ wRc % 2)) (sBit :: LS) P.W 22 σ s ∧
        (s.gpr .r11).toNat = 0) := by
  refine VP.ctx expTail_taint (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  refine h.bitOf_Wm hm hw hj (by decide) fun t ht mt hwt _ => wp_mov (op2_imm (by decide)) fun t' u => ?_
  obtain ⟨ht', hwt'⟩ := ht.reg hwt (u.rest (ws := [.r11]) (by simp)) u.mem
  exact WP.block_nil ⟨⟨e, ht', mt.of_rest (u.rest (ws := [.r11]) (by simp)) u.mem, hwt'⟩, by rw [u.gpr]; rfl⟩

/-- `r`'s copy halved. -/
theorem St.phalf (hj : wRc ∈ LW) (hl : ∀ i ∈ L, i / 2 ≠ wRc) :
    VP (fun σ s => St P E A L AW LW V LS P.W 22 σ s ∧ (s.gpr .r11).toNat = 0) (half wRc)
      (St P E A L (fun σ => upd (AW σ) wRc (AW σ wRc / 2)) (wRc :: LW) V LS P.W 22) :=
  VP.ctx halfRc_taint (fun _ _ h => h.1.2.2.2) fun _ _ ⟨⟨e, h, hm, hw⟩, r11⟩ =>
    WP.mono (h.half_Wm hm hw hj (by decide) r11 hl) fun _ ⟨ht, mt, hwt, _⟩ => ⟨e, ht, mt, hwt⟩

end

section
variable {P : RP}

/-- The arrays after the multiplicand of bit `i` is chosen. -/
def Am (P : RP) (σ : State) (j i : Nat) : Nat → Nat := upd (Ae P σ j i) mXm (gR P j (rv P σ / 2 ^ i % 2 * 2 ^ i))

theorem gR_lt (hn0 : 0 < P.n) (j e : Nat) : gR P j e < P.n := Nat.mod_lt _ hn0

/-- After the multiplicand of bit `i` is chosen. -/
abbrev Ms (P : RP) (E : State → Prop) (j i : Nat) : State → State → Prop :=
  St P E (fun σ => Am P σ j i) (mXm :: Le) (fun σ => AWe P σ (i + 1)) LWe
    (fun σ => upd (Vc P σ j (P.c - i)) sBit (rv P σ / 2 ^ i % 2)) (sBit :: LSe) P.w nArr

/-- After `y` is multiplied. -/
abbrev My (P : RP) (E : State → Prop) (j i : Nat) : State → State → Prop :=
  St P E (fun σ => upd (Am P σ j i) (mBase + iY) (gR P j (rv P σ % 2 ^ (i + 1)))) ((mBase + iY) :: mXm :: Le)
    (fun σ => AWe P σ (i + 1)) LWe (fun σ => upd (Vc P σ j (P.c - i)) sBit (rv P σ / 2 ^ i % 2)) (sBit :: LSe)
    P.w nArr

/-- After `g^(2^i)` is squared. -/
abbrev Mg (P : RP) (E : State → Prop) (j i : Nat) : State → State → Prop :=
  St P E (fun σ => upd (upd (Am P σ j i) (mBase + iY) (gR P j (rv P σ % 2 ^ (i + 1)))) (mBase + iG)
      (gR P j (2 ^ (i + 1))))
    ((mBase + iG) :: (mBase + iY) :: mXm :: Le)
    (fun σ => AWe P σ (i + 1)) LWe (fun σ => upd (Vc P σ j (P.c - i)) sBit (rv P σ / 2 ^ i % 2)) (sBit :: LSe)
    P.w nArr

/-- The bit `i` of `r` and the multiplicand. -/
theorem expA_vp {E : State → Prop} {j i : Nat} {R : Prog isa} {G : State → State → Prop}
    (hR : VP (Ms P E j i) R G) :
    VP (Xs P E j i) (.seq (.block (ctxW ++ bitOf sBit wRc ++ [.mov .r11 (.imm 0)]))
      (.seq (half wRc) (.seq (.block ctxw) (.seq (sel mXm aO mG sBit) R)))) G := by
  rw [expHead_eq]
  refine VP.seq (VP.block_append St.pctxW (St.pexpTail (by decide))) ?_
  refine VP.seq (St.phalf (by decide) (by decide)) ?_
  refine VP.seq St.pctxw ?_
  refine VP.seq ((St.psel selXm_taint (o := mXm) (a := aO) (b := mG) (sl := sBit) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (fun σ _ => by simp [upd]; omega)
    (by decide)).mono (fun _ _ h => h) fun σ s h => St.mono h ?_ ?_ ?_) hR
  · intro x hx
    refine ⟨hx, ?_⟩
    simp only [Le, liveM, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Am, upd_self]
      simp [upd, AWe, Ae, AM, aO, mG, mY, aNg]
      rw [gR, gR]
      exact bit_mont _ _ _ _ _
    all_goals simp [Am, upd, mXm, mY, mG, aNg, aO, mR2, aOne, aZ, aN]
  · intro x hx
    simp only [LWe, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · refine ⟨by simp, ?_⟩
      simp only [AWe, upd_self]
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    · simp [AWe, AWh, upd, wR, wRc]
  · intro x hx
    simp only [LSe, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [upd, AWe, sBit, sCnt, sCand, sTc]

theorem expY_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) {E : State → Prop} {j i : Nat} :
    VP (Ms P E j i) (seqs (mmul iY iY iXm)) (My P E j i) := by
  have hn0 : 0 < P.n := by omega
  refine St.pmmul (o := iY) (a := iY) (b := iXm) (by decide) hn.1 (by decide) (by decide) (by decide) (by decide)
    (by decide) fun σ _ => ?_
  have eY : Am P σ j i (mBase + iY) = gR P j (rv P σ % 2 ^ i) := by simp [Am, Ae, upd, mXm, mY, mBase, iY, mG]
  have eX : Am P σ j i (mBase + iXm) = gR P j (rv P σ / 2 ^ i % 2 * 2 ^ i) := by simp [Am, upd, mXm, mBase, iXm]
  rw [eY, eX]
  refine ⟨gR_lt hn0 _ _, gR_lt hn0 _ _, gR_lt hn0 _ _, ?_⟩
  simp only [gR]
  rw [mod_pow_succ']
  exact mont_prod_eq _ _ _ _ _

theorem expG_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) {E : State → Prop} {j i : Nat} :
    VP (My P E j i) (seqs (mmul iG iG iG)) (Mg P E j i) := by
  have hn0 : 0 < P.n := by omega
  refine St.pmmul (o := iG) (a := iG) (b := iG) (by decide) hn.1 (by decide) (by decide) (by decide) (by decide)
    (by decide) fun σ _ => ?_
  have eG : upd (Am P σ j i) (mBase + iY) (gR P j (rv P σ % 2 ^ (i + 1))) (mBase + iG) = gR P j (2 ^ i) := by
    simp [Am, Ae, upd, mXm, mBase, iY, mG, iG]
  rw [eG]
  refine ⟨gR_lt hn0 _ _, gR_lt hn0 _ _, gR_lt hn0 _ _, ?_⟩
  simp only [gR]
  rw [Nat.pow_succ, Nat.mul_two]
  exact mont_prod_eq _ _ _ _ _

theorem expN_vp (hcl : P.c < 2 ^ 31) {E : State → Prop} {j i : Nat} (hi : i < P.c) :
    VP (Mg P E j i) (.block cntNext)
      (fun σ s => isa.eval .ne s = some (decide (i + 1 < P.c)) ∧ Xs P E j (i + 1) σ s) := by
  refine (St.pcnt cntNext_taint (fun _ h => h) (by decide) (fun σ _ => ?_) (fun σ _ => ?_)).mono (fun _ _ h => h)
    fun σ s ⟨h, z⟩ => ⟨?_, St.mono h ?_ ?_ ?_⟩
  · simp [upd, Vc, sBit, sCnt]; omega
  · simp [upd, Vc, sBit, sCnt]; omega
  · show some (!s.z) = some (decide (i + 1 < P.c))
    rw [z]
    simp only [upd_self, upd_ne _ _ (show sCnt ≠ sBit by decide), Vc]
    simp only [Option.some.injEq, Bool.not_eq_eq_eq_not]
    by_cases h : i + 1 < P.c <;> simp [h] <;> omega
  · intro x hx
    refine ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)), ?_⟩
    simp only [Le, liveM, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Am, Ae, upd, mXm, mY, mG, mBase, iY, iG, aNg, aO, mR2, aOne, aZ, aN]
  · intro x hx; exact ⟨hx, rfl⟩
  · intro x hx
    refine ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx), ?_⟩
    simp only [LSe, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [upd, Vc, sBit, sCnt, sCand, sTc]
    omega

/-- The bit `i` of `r`. -/
theorem expStep_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hcl : P.c < 2 ^ 31) {E : State → Prop} {j i : Nat}
    (hi : i < P.c) :
    VP (Xs P E j i) expBody (fun σ s => isa.eval .ne s = some (decide (i + 1 < P.c)) ∧ Xs P E j (i + 1) σ s) := by
  simp only [expBody, seqs]
  exact expA_vp (VP.seq (expY_vp hn) (VP.seq (expG_vp hn) (expN_vp hcl hi)))

/-- `y = g^r` and `g^(2^c)`, after the `c` bits of `r`. -/
theorem expLoop_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hcl : P.c < 2 ^ 31) (hc0 : 0 < P.c) {E : State → Prop}
    {j : Nat} : VP (Xs P E j 0) expLoop (Xs P E j P.c) := by
  have hl := VP.loop (I := fun m σ s => m ≤ P.c ∧ Xs P E j (P.c - m) σ s) (body := expBody) (c := .ne)
    (Q := Xs P E j P.c) (fun n => VP.pure fun hle => (expStep_vp hn hcl (i := P.c - (n + 1)) (by omega)).mono
      (fun _ _ h => h) fun σ s ⟨ev, h⟩ => ⟨by rw [ev]; congr 1; simp only [decide_eq_decide]; omega,
        fun h0 => by subst h0; rwa [show P.c - (0 + 1) + 1 = P.c by omega] at h,
        fun _ => ⟨by omega, by rwa [show P.c - (n + 1) + 1 = P.c - n by omega] at h⟩⟩) (P.c - 1)
  exact hl.mono (fun σ s h => ⟨by omega, by rwa [show P.c - (P.c - 1 + 1) = 0 by omega]⟩) fun _ _ h => h

end

end VG.Proof.Rsa.Arm.Recover
