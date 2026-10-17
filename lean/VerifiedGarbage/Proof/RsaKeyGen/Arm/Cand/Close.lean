module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Load1
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Inv
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint2
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: too close to `p` (`closeCheck_vp`)

From `S0`: the header word `sCl` := whether the candidate is too close to
`p` (`clv`), and Z iff it is: the stage `S1`. Loads of arrays on a stage
(`St.pload`), and a difference with its borrow (`St.psubLt`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 sub32_of)
open VG.Proof.Rsa (b2n)
open VG.Impl.RsaKeyGen.Arm.Key (setHi notS isOne)
open VG.Proof.RsaKeyGen.Arm.Key (b2n_xor)

/-- The other prime, and whether the candidate is too close to it. -/
def pv (P : CP) (σ : State) : Nat := Spec.Rsa.os2ip (pB P σ)
def clv (P : CP) (σ : State) : Bool := Spec.RsaKeyGen.tooClose (8 * P.L) (Spec.RsaKeyGen.otherPrime (pB P σ)) (cv P σ)

/-- The header words after the check. -/
def V1 (P : CP) (σ : State) : Nat → Nat := upd (V0 P) sCl (b2n (clv P σ))

abbrev L1 : List Nat := [aTwo, aOne, aC, aZero]

/-- Whether the candidate is obviously composite, and the header words after
trial division. -/
def compv (P : CP) (σ : State) : Bool := Spec.RsaKeyGen.obviouslyComposite (8 * P.L) (cv P σ)
def V2 (P : CP) (σ : State) : Nat → Nat := upd (V1 P σ) sTr (b2n (compv P σ))

/-- After trial division. -/
abbrev S2 (P : CP) (E : State → Prop) : State → State → Prop := St P E (A0 P) L1 (V2 P) [sTr, sCl, sUsed]

abbrev S1 (P : CP) (E : State → Prop) : State → State → Prop := St P E (A0 P) L1 (V1 P) [sCl, sUsed]

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- The frame words `o1` and `o2` into `r4` and `r6`. -/
theorem St.pldPtr {o1 o2 : Nat} {v1 v2 : CP → BitVec 32} (h1 : FwOk o1) (h2 : FwOk o2)
    (hv : ∀ σ, In P σ → fw σ.mem P o1 = v1 P ∧ fw σ.mem P o2 = v2 P) :
    VP (St P E A L V LS) (.block [.ldrSp .r4 o1, .ldrSp .r6 o2])
      (fun σ s => St P E A L V LS σ s ∧ s.gpr .r4 = v1 P ∧ s.gpr .r6 = v2 P) := by
  show VP _ (.block ([(Reg.r4, o1), (Reg.r6, o2)].map fun p => Instr.ldrSp p.1 p.2)) _
  refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
  · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
  · obtain ⟨e1, e2⟩ := hv σ h.pre
    refine h.ldrSp (o := o1) h1 fun s1 u1 => ?_
    have r1 := u1.rest (ws := [.r4]) (by simp)
    have k1 := h.of_rest r1 u1.mem
    refine k1.ldrSp (o := o2) h2 fun t u2 => WP.block_nil ?_
    have r2 := u2.rest (ws := [.r6]) (by simp)
    exact ⟨⟨e, k1.of_rest r2 u2.mem, (hw.rest r1).rest r2⟩, by rw [u2.other .r4 (by simp), u1.gpr, e1],
      by rw [u2.gpr, e2]⟩

/-- `load j`: `[j] :=` the `k` octets at `r4` (`r6 = k`). -/
theorem St.pload {j : Nat} {src : CP → BitVec 32} {k : CP → Nat} (cert : LCert j) (hj : j < nArr)
    (hin : ∀ σ, E σ → In P σ → InRegions (σ.rd ++ σ.wr) (State.addr (src P)) (k P) ∧
      (∀ r ∈ P.chg, Region.Disjoint ⟨State.addr (src P), k P⟩ r) ∧
      (src P).toNat + k P ≤ 2 ^ 32 ∧ 0 < k P ∧ k P ≤ P.L) :
    VP (fun σ s => St P E A L V LS σ s ∧ s.gpr .r4 = src P ∧ s.gpr .r6 = BitVec.ofNat 32 (k P))
      (VG.Impl.Rsa.Arm.CrtValues.load j)
      (St P E (fun σ => upd (A σ) j (Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr (src P)) (k P))))
        (j :: L) V LS) := by
  refine VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, hw⟩, p4, p6⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
    · rw [h₁.1.2.2.r7, h₂.1.2.2.r7]
    · rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
    · rw [h₁.1.2.2.r9, h₂.1.2.2.r9]
  · obtain ⟨rd, sC, fit, hk, hkL⟩ := hin σ e h.pre
    refine WP.mono (load_okC h.bk hw hj rd sC fit hk hkL p4 p6) fun t ⟨_, wt, kp, v, r⟩ => ⟨e, ?_, wt⟩
    have hv : num t.mem P.B P.W j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr (src P)) (k P)) := by
      have lt : Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr (src P)) (k P)) < 2 ^ (32 * P.W) := by
        have := VG.Proof.Rsa.lt_of_os2ip (Spec.Rsa.bytesAt σ.mem (State.addr (src P)) (k P))
        rw [bytesAt_length, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
        exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by simp only [CP.W]; omega))
      rw [← v] at lt ⊢
      exact VG.Proof.Rsa.Arm.CrtValues.val32_low2 lt
    exact h.write1 kp hj (by simp) r.sp r.rd r.wr hv (by simp)

/-- `[o] := [a] − [b]`, the header word `d :=` its borrow. -/
theorem St.psubLt {o a b d : Nat} (cert : Cert (seqs [sub3 o a b, .block [.str .r11 .r8 d]])) (ho : o < nArr)
    (ha : a ∈ L) (hb : b ∈ L) (hoa : o ≠ a) (hob : o ≠ b) (hd : LsOk d) :
    VP (St P E A L V LS) (seqs [sub3 o a b, .block [.str .r11 .r8 d]])
      (St P E (fun σ => upd (A σ) o (sub32 P.W (A σ a) (A σ b))) (o :: L)
        (fun σ => upd (V σ) d (b2n (decide (A σ a < A σ b)))) (d :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    simp only [seqs]
    rw [WP.seq_iff]
    refine WP.mono (sub3_ok hw ho (h.live_lt a ha) (h.live_lt b hb) (by decide) hoa hob)
      fun t ⟨ht, k, v, bo, r⟩ => ?_
    obtain ⟨e1, e2⟩ := sub32_of (val32_lt _ _ _ _) (val32_lt _ _ _ _) v bo
    have ea : val32 s.mem (State.addr P.B) (arr P.W a) P.W = A σ a := h.arrs a ha
    have eb : val32 s.mem (State.addr P.B) (arr P.W b) P.W = A σ b := h.arrs b hb
    simp only [num, ea, eb] at e1 e2
    have h1 := h.write1 k ho (by simp) r.sp r.rd r.wr e1 (by simp)
    exact h1.str ht hd fun u hu hwu _ => WP.block_nil ⟨e, by rw [e2] at hu; exact hu, hwu⟩

end

/-! ## The check -/

section
variable {P : CP}

theorem sub32_val {W a b : Nat} (ha : a < 2 ^ (32 * W)) (hb : b < 2 ^ (32 * W)) :
    sub32 W a b = if a < b then a + 2 ^ (32 * W) - b else a - b := by
  unfold sub32
  split
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [show a + 2 ^ (32 * W) - b = a - b + 2 ^ (32 * W) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The selected difference is `|c − p|`. -/
theorem abs_val {W c p : Nat} (hc : c < 2 ^ (32 * W)) (hp : p < 2 ^ (32 * W)) :
    (if b2n (decide (c < p)) = 0 then sub32 W c p else sub32 W p c) = Spec.RsaKeyGen.absDiff c p := by
  unfold Spec.RsaKeyGen.absDiff
  by_cases h : c < p
  · rw [ite_eq_right (by simp [h, b2n]), sub32_val hp hc, ite_eq_right (by omega), ite_eq_left (by omega)]
  · rw [ite_eq_left (by simp [h, b2n]), sub32_val hc hp, ite_eq_right h]
    split <;> omega

theorem clv_none {σ : State} (h : P.pl = 0) : clv P σ = false := by
  unfold clv Spec.RsaKeyGen.otherPrime
  rw [show pB P σ = [] by simp [pB, h, Spec.Rsa.bytesAt]]
  rfl

theorem clv_some {σ : State} (h : P.pl = P.L) (hL : 0 < P.L) :
    clv P σ = decide (Spec.RsaKeyGen.absDiff (cv P σ) (pv P σ) ≤ 2 ^ (8 * P.L - 100)) := by
  unfold clv Spec.RsaKeyGen.otherPrime
  have : pB P σ ≠ [] := by
    intro e; have := congrArg List.length e; rw [bytesAt_length] at this; simp at this; omega
  rw [ite_eq_right this]
  rfl

theorem cmp0_vp {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
    {LS : List Nat} :
    VP (St P E A L V LS) (.block [.ldrSp .r1 aoPl, .cmp .r1 (.imm 0)])
      (fun σ s => St P E A L V LS σ s ∧ s.z = decide (P.pl = 0)) := by
  refine VP.block_append (l₁ := [.ldrSp .r1 aoPl]) (G := fun σ s => St P E A L V LS σ s ∧
    s.gpr .r1 = BitVec.ofNat 32 P.pl) ?_ ?_
  · refine VP.ldrSp (c := [(Reg.r1, aoPl)]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
    · exact h.ldrSp (o := aoPl) (by decide) fun t u => WP.block_nil
        ⟨⟨e, h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, hw.of_upd u (by decide) (by decide) (by decide)⟩,
          u.gpr.trans h.pre.aPl⟩
  · refine VP.taint [.r1] cmp0_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨e, h, hw⟩, r1⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h₁.2, h₂.2]
    · refine wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ⟨⟨e, h.of_rest (f.rest []) f.mem,
        hw.of (by rw [f.gpr]) (by rw [f.gpr]) (by rw [f.gpr]) f.wr⟩, ?_⟩
      have pre := h.pre
      have hl : P.pl < 2 ^ 32 := by have := pre.plv; have := pre.k2; omega
      rw [z, r1]
      by_cases h0 : P.pl = 0
      · simp [h0]
      · have hne : BitVec.ofNat 32 P.pl ≠ 0#32 := fun e => h0 (by
          have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl] at this)
        simp [hne, h0]

/-- `|c − p| ≤ 2^(8 out_len − 100)` into `sCl`, for `p` given. -/
theorem closeCalc_vp {E : State → Prop} (hE : ∀ σ, E σ → In P σ ∧ P.pl = P.L) :
    VP (S0 P E) (seqs closeCalc) (S1 P E) := by
  simp only [closeCalc, List.cons_append, List.nil_append, seqs]
  refine VP.seq (St.pldPtr (o1 := aoP) (o2 := aoPl) (v1 := fun P => P.pP) (v2 := fun P => BitVec.ofNat 32 P.pl)
    (by decide) (by decide) fun σ h => ⟨h.aP, h.aPl⟩) ?_
  refine VP.seq (St.pload (src := fun P => P.pP) (k := fun P => P.pl) loadP_taint (by decide) (fun σ e h => ?_)
    ) ?_
  · have hp := (hE σ e).2
    have := h.k1
    refine ⟨?_, ?_, h.fP, by omega, by omega⟩
    · rw [hp]; exact h.rdP |> fun r => by rwa [hp] at r
    · intro r hr
      simp only [CP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h.sP.symm
      · exact h.oP.symm
      · exact h.uP.symm
      · exact h.pC
      · exact h.pF.sub_right (Offset.sub_base _ (d := 0) (n := 4) (k := 56) (by decide) |> fun s => by
          simpa only [BitVec.add_zero] using s)
  refine VP.assoc (VP.seq (St.psubLt subD1_taint (by decide) (by simp) (by simp) (by decide) (by decide)
    (by decide)) ?_)
  refine VP.seq (St.psub3 subD2_taint (by decide) (by simp) (by simp) (by decide) (by decide)) ?_
  refine VP.seq (St.psel selAbs_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    fun σ _ => by simp only [upd_self]; exact VG.Proof.Rsa.b2n_le _) ?_
  refine VP.seq (St.psetHi (i := fun P => P.W - 6) bnd_taint (by simp) (by decide) (by decide) (by decide)
    (fun σ _ pre => by have := pre.wge; omega) fun σ _ _ => by
      simp (config := {decide := true}) only [upd, ↓reduceIte, A0]; exact Nat.two_pow_pos _) ?_
  refine VP.assoc (VP.seq (St.pltS ltCl_taint (by simp) (by simp) (by decide) (by decide) (by decide)) ?_)
  have vals : ∀ σ, E σ → In P σ → sub32 P.W (cv P σ) (pv P σ) = sub32 P.W (cv P σ) (pv P σ) ∧
      cv P σ < 2 ^ (32 * P.W) ∧ pv P σ < 2 ^ (32 * P.W) ∧ 2 ^ (32 * (P.W - 6)) * (0x10000000 % 2 ^ 32) =
        2 ^ (8 * P.L - 100) := fun σ e pre => by
    have wE := pre.W_eq; have lE := pre.L_eq; have w4 := pre.w4
    have p8 : 2 ^ (8 * P.L) ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by omega)
    refine ⟨rfl, ?_, ?_, ?_⟩
    · have := (cv_shape pre).2.2; omega
    · have := VG.Proof.Rsa.lt_of_os2ip (pB P σ)
      rw [bytesAt_length, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, (hE σ e).2] at this
      unfold pv; omega
    · rw [show (0x10000000 : Nat) % 2 ^ 32 = 2 ^ 28 from rfl, ← Nat.pow_add]; congr 1; omega
  refine (St.pnotS (X := fun σ => decide (2 ^ (8 * P.L - 100) < Spec.RsaKeyGen.absDiff (cv P σ) (pv P σ)))
    notCl_taint (by simp) (by decide) fun σ e => ?_).mono (fun _ _ h => h) fun σ s h => h.mono
      (fun j hj => ⟨by mem_sub, ?_⟩) fun j hj => ⟨by mem_sub, ?_⟩
  · have pre : In P σ := (hE σ e).1
    obtain ⟨-, hc, hp, hb⟩ := vals σ e pre
    simp (config := {decide := true}) only [upd, ↓reduceIte, A0]
    rw [hb, show Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr P.pP) P.pl) = pv P σ from rfl, abs_val hc hp,
      Nat.zero_add]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) only [upd, ↓reduceIte, A0]
  · have pre := h.2.1.pre
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> simp (config := {decide := true}) only [upd, ↓reduceIte, V1, V0]
    rw [clv_some (hE σ h.1).2 (by have := pre.k1; omega), ← decide_not]
    exact congrArg b2n (decide_eq_decide.mpr Nat.not_lt)

theorem St.weaken {E E' : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
    {LS : List Nat} {σ s : State} (h : St P E A L V LS σ s) (he : E σ → E' σ) : St P E' A L V LS σ s :=
  ⟨he h.1, h.2⟩

theorem isa_eq (s : State) : isa.eval .eq s = some s.z := rfl

/-- Whether the candidate is too close to `p`: Z iff it is. -/
theorem closeCheck_vp {E : State → Prop} (hE : ∀ σ, E σ → In P σ) :
    VP (S0 P E) (seqs closeCheck) (fun σ s => S1 P E σ s ∧ s.z = decide (V1 P σ sCl = 1)) := by
  simp only [closeCheck, seqs]
  refine VP.seq cmp0_vp (VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [isa_eq, isa_eq, h₁.2, h₂.2]) ?_ ?_)
    (St.pisOne isCl_taint (by simp) fun σ _ => by simp only [V1, upd_self]; exact VG.Proof.Rsa.b2n_le _))
  · refine (St.psetS (E := fun σ => E σ ∧ P.pl = 0) clZero_taint (by decide) (by decide) (by decide)).mono
      (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e, ?_⟩) fun σ s h => (h.mono (fun j hj => ⟨by mem_sub, rfl⟩)
        fun j hj => ⟨hj, ?_⟩).weaken (·.1)
    · rw [isa_eq, z] at t; simpa using t
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · simp only [V1, upd_self, clv_none h.1.2]; rfl
      · simp (config := {decide := true}) only [V1, upd, ↓reduceIte]
  · refine (closeCalc_vp (E := fun σ => E σ ∧ P.pl = P.L) fun σ e => ⟨hE σ e.1, e.2⟩).mono
      (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e, ?_⟩) fun σ s h => h.weaken (·.1)
    have pre := hE σ e
    rw [isa_eq, z] at t
    have : ¬ P.pl = 0 := by simpa using t
    rcases pre.plv with h0 | h0
    · exact absurd h0 this
    · exact h0

end

end VG.Proof.RsaKeyGen.Arm.Cand
