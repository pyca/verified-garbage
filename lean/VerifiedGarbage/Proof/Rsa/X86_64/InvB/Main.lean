module

public import VerifiedGarbage.Proof.Rsa.X86_64.InvB.Finish
import VerifiedGarbage.Proof.Divstep.TcSBounds
import VerifiedGarbage.Proof.Rsa.Divstep.Bound
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Loop
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.CrtFrame

/-!
# RSA's inverse by divsteps on x86-64: the contract

The batches as a loop (`loop_ok`), and the inverse at the width `n` in
`r13` (`inverseN_ok`) and at `w` (`inverse_ok`): for an odd `m`,
`[v] = gcd(a, m)`, `m ∣ [x₂] a - [v]` and `[x₂] < m`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.InvB

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Inv
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- The `3 n + 2` batches, from `invRunS 0` to `invRunS (3 n + 2)`. -/
theorem loop_ok {s : State} {B : Addr} {Z w n p mi x : Nat} (L : Lay B Z w n) (hn20 : n < 2 ^ 20)
    (hp : p % 2 = 1) (hpn : p < 2 ^ (64 * n)) (hx : x < 2 * 2 ^ (64 * n)) (hm : (p * mi + 1) % 2 ^ 64 = 0)
    (hb : BS B Z w n p mi (Divstep.invRunS 59 p mi x 0) s) (hrsi : s.gpr .rsi = BitVec.ofNat 64 (3 * n + 2)) :
    WP isa (.loop batch .ne) s fun t => BS B Z w n p mi (Divstep.invRunS 59 p mi x (3 * n + 2)) t ∧
      Frm B [(slot w 16, 72 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s t := by
  have hmi : ((p : Int) * (mi : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hm
  refine VG.Proof.X25519.X86_64.cntLoop_ok (n := 3 * n + 2)
    (Inv := fun j t => BS B Z w n p mi (Divstep.invRunS 59 p mi x (3 * n + 2 - j)) t ∧
      t.gpr .rsi = BitVec.ofNat 64 j ∧ Frm B [(slot w 16, 72 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s t)
    (fun j t hj1 hjB ⟨bt, rt, ft, kt⟩ => ?_) (fun t ⟨bt, _, ft, kt⟩ => ⟨by simpa using bt, ft, kt⟩) (by omega)
    ⟨by rw [Nat.sub_self]; exact hb, hrsi, Frm.refl _ _ _, Keep.refl _ _⟩
  obtain ⟨bd, bf1, bf, bg, ba0, ba1, bb0, bb1⟩ := Divstep.invRunS_bounds (N := 59) (by decide) (p := p) (m := mi)
    (x := x) (M := 2 * 2 ^ (64 * n)) (by exact_mod_cast hp) (by omega) hmi (Int.natCast_nonneg _)
    (by have : p ≤ 2 * 2 ^ (64 * n) := by omega
        exact_mod_cast this)
    (by have : x ≤ 2 * 2 ^ (64 * n) := by omega
        exact_mod_cast this) (3 * n + 2 - j)
  have hM8 : (2 * 2 ^ (64 * n) : Int) ≤ 2 ^ (64 * n) * 2 ^ 3 := by
    have : 2 * 2 ^ (64 * n) ≤ 2 ^ (64 * n) * 2 ^ 3 := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by decide)
    exact_mod_cast this
  refine WP.mono (batch_ok L bt rt hj1 (by omega)
    (by
      have : 59 * (3 * n + 2 - j) ≤ 59 * (3 * 2 ^ 20 + 2) := Nat.mul_le_mul_left _ (by omega)
      have h2 : ((59 * (3 * n + 2 - j) : Nat) : Int) ≤ 59 * (3 * 2 ^ 20 + 2) := by exact_mod_cast this
      omega)
    bf1 (le_trans bf hM8) (le_trans bg hM8) ⟨ba0, ba1⟩ ⟨bb0, bb1⟩ (by omega) hpn hm)
    fun u ⟨bu, ru, zu, fu, ku⟩ => ⟨⟨?_, ru, ft.trans fu, (kt.trans ku).mono (by decide)⟩, zu⟩
  rw [show 3 * n + 2 - (j - 1) = (3 * n + 2 - j) + 1 by omega]
  exact bu

theorem pOf_odd (m : Nat) : pOf m % 2 = 1 := by unfold pOf; split <;> omega

theorem pOf_lt {m n : Nat} (hn : 1 ≤ n) (hm : m < 2 ^ (64 * n)) : pOf m < 2 ^ (64 * n) := by
  unfold pOf; split
  · exact hm
  · have : 2 ^ (64 * n) = 2 * 2 ^ (64 * n - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    omega

theorem keep_drop {rs : List Reg} {r : Reg} {s t : State} (k : Keep (r :: rs) s t) (h : t.gpr r = s.gpr r) :
    Keep rs s t :=
  ⟨fun x hx => by
    by_cases e : x = r
    · subst e; exact h
    · exact k.1 x (by simp [e, hx]), k.2⟩

theorem finish_eq (iV iX₂ : Nat) : finish iV iX₂ = fin1L ++ fin2L ++ fin3L iV iX₂ := rfl

/-- The inverse at the width `n` in `r13`: from `a` in `[u]` and `m` in `[m]`, both below
`2^(64 n)`, `[v] = gcd(a, m)`, `m ∣ [x₂] a - [v]` and `[x₂] < m` for an odd `m`. -/
theorem inverseN_ok {s : State} {B : Addr} {Z w n iU iV iX₂ iM : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (h13 : s.gpr .r13 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) (hn20 : n < 2 ^ 20)
    (hU : iU < 16) (hV : iV < 16) (hX : iX₂ < 16) (hM : iM < 16) (hVX : iV ≠ iX₂)
    (hu : wv s.mem B (slot w iU) w < 2 ^ (64 * n)) (hm : wv s.mem B (slot w iM) w < 2 ^ (64 * n)) :
    WP isa (inverseN iU iV iX₂ iM) s fun t => t.gpr .rdi = B ∧
      Frm B [(slot w iV, 8 * w), (slot w iX₂, 8 * w), (slot w 16, 80 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t ∧
      (wv s.mem B (slot w iM) w % 2 = 1 →
        wv t.mem B (slot w iV) w = Nat.gcd (wv s.mem B (slot w iU) w) (wv s.mem B (slot w iM) w) ∧
        ((wv s.mem B (slot w iM) w : Nat) : Int) ∣
          (wv t.mem B (slot w iX₂) w : Int) * wv s.mem B (slot w iU) w - wv t.mem B (slot w iV) w ∧
        wv t.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w) := by
  have hN := h.scr.nowrap
  have e16 := slot_eq w 16; have e25 := slot_eq w 25; have e26 := slot_eq w 26
  generalize hu' : wv s.mem B (slot w iU) w = u at hu
  generalize hm' : wv s.mem B (slot w iM) w = m at hm
  have hpo := pOf_odd m
  have hpn := pOf_lt hn1 hm
  generalize hp : pOf m = p at hpo hpn
  have hp0 : 0 < p := by omega
  have hx : (if u % 2 = 0 then p else 0) + u = Rsa.Divstep.oddInput p u := by
    unfold Rsa.Divstep.oddInput; omega
  unfold inverseN
  rw [finish_eq, show start iU iM ++ [.loop batch .ne] ++ (fin1L ++ fin2L ++ fin3L iV iX₂) =
    start iU iM ++ ([.loop batch .ne] ++ (fin1L ++ (fin2L ++ fin3L iV iX₂))) by simp only [List.append_assoc],
    seqs_append_iff _ _ (by simp [start]) (by simp)]
  refine WP.mono (start_ok h hZ h9 h13 hn1 hnw hU hM (by rw [hu']; exact hu) (by rw [hm']; exact hm))
    fun s₁ ⟨mi, hb₁, hmi, hP₁, hrsi₁, F₁, k₁⟩ => ?_
  rw [hu', hm', hp, hx] at hb₁
  rw [hm', hp] at hmi hP₁
  rw [seqs_append_iff _ _ (by simp) (by simp [fin1L])]
  have L : Lay B Z w n := ⟨hn1, hnw, h.w1, h.w2, hZ, hN⟩
  have hxlt : Rsa.Divstep.oddInput p u < 2 * 2 ^ (64 * n) := by
    unfold Rsa.Divstep.oddInput; split <;> omega
  refine WP.mono (loop_ok L hn20 hpo hpn hxlt hmi hb₁ hrsi₁) fun s₂ ⟨hb₂, F₂, k₂⟩ => ?_
  have hS := Nat.le_trans (slot_lt (show 25 < 26 by decide)) hZ
  have P₂ : wv s₂.mem B (slot w aP) (n + 1) = p := by
    rw [F₂.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; dsimp only; unfold aP; omega) (by unfold aP; omega), hP₁]
  have hmiI : ((p : Int) * (mi : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hmi
  set I := Divstep.invRunS 59 p mi (Rsa.Divstep.oddInput p u) (3 * n + 2) with hI
  obtain ⟨-, -, -, -, ba0, ba1, -, -⟩ := Divstep.invRunS_bounds (N := 59) (by decide) (p := p) (m := mi)
    (x := Rsa.Divstep.oddInput p u) (M := 2 * 2 ^ (64 * n)) (by exact_mod_cast hpo) (by omega) hmiI
    (Int.natCast_nonneg _) (by have : p ≤ 2 * 2 ^ (64 * n) := by omega
                               exact_mod_cast this)
    (by have : Rsa.Divstep.oddInput p u ≤ 2 * 2 ^ (64 * n) := by omega
        exact_mod_cast this) (3 * n + 2)
  -- The divsteps are done.
  have h32 : 2 ^ (64 * n + 1) ≤ 2 ^ (32 * (2 * n + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  have h64 : 2 * 2 ^ (64 * n) = 2 ^ (64 * n + 1) := by rw [Nat.pow_succ]; ring
  have hdone := Rsa.Divstep.done_words (w := 2 * n + 1) (steps := 59 * (3 * n + 2)) (p := p)
    (x := Rsa.Divstep.oddInput p u) (by omega) (by exact_mod_cast hpo) (Int.natCast_nonneg _)
    (Int.natCast_nonneg _) (Or.inr (by exact_mod_cast Rsa.Divstep.oddInput_odd (x := u) hpo))
    (by have : p ≤ 2 ^ (32 * (2 * n + 1)) := by omega
        exact_mod_cast this)
    (by have : Rsa.Divstep.oddInput p u ≤ 2 ^ (32 * (2 * n + 1)) := by omega
        exact_mod_cast this) (by omega)
  rw [Int.gcd_natCast_natCast, Rsa.Divstep.oddInput_gcd] at hdone
  obtain ⟨-, hfI, hcong⟩ := Divstep.invRunS_done (N := 59) (B := 3 * n + 2) (by decide) hpo hmiI hdone
  have hfp : I.f.natAbs ≤ p := by rw [hfI]; exact Nat.gcd_le_left _ hp0
  have hf1 : -(p : Int) ≤ I.f := by omega
  have hf2 : I.f ≤ p := by omega
  -- The end.
  have F₂' : Frm B [(slot w 16, 80 * (w + 2))] s.mem s₂.mem :=
    F₁.trans (F₂.widen fun r hr => ⟨_, List.mem_singleton.mpr rfl, by
      rw [List.mem_singleton.mp hr]; dsimp only; omega⟩)
  rw [seqs_append_iff _ _ (by simp [fin1L]) (by simp [fin2L])]
  refine WP.mono (fin1_ok h hZ F₂' hb₂ hn1 hnw P₂ hpn ⟨ba0, ba1⟩) fun s₃ ⟨h₃, r12₃, t₁, T₃, ht₁, c₃, z₃, P₃, F₃,
    Fr₃, k₃⟩ => ?_
  rw [seqs_append_iff _ _ (by simp [fin2L]) (by simp [fin3L])]
  refine WP.mono (fin2_ok h₃ r12₃ T₃ ht₁ z₃ P₃ hpn (f := I.f) (by rw [F₃]; exact hb₂.f) hf1 hf2)
    fun s₄ ⟨h₄, _, x₂, T₄, hx₂, c₄, z₄, _, F₄, Fr₄, k₄⟩ => ?_
  refine WP.mono (fin3_ok h₄ hV hX hVX T₄ hx₂ z₄ hpn (f := I.f) (by rw [F₄, F₃]; exact hb₂.f) hf1 hf2)
    fun t ⟨dt, vt, xt, Frt, kt⟩ => ⟨dt, ?_, keep_drop (r := .rdi)
      (((((k₁.trans k₂).trans k₃).trans k₄).trans kt).mono (by decide)) (dt.trans h.rdi.symm), ?_⟩
  · exact ((Fr₃.trans Fr₄).mono (by simp)).trans Frt
  · intro hmo
    have hpm : p = m := by rw [← hp]; unfold pOf; simp [hmo]
    subst hpm
    refine ⟨by rw [vt, hfI, Nat.gcd_comm], ?_, by rw [xt]; exact hx₂⟩
    rw [vt, xt]
    have e : (x₂ : Int) * u ≡ (I.f.natAbs : Int) [ZMOD p] := by
      rw [hfI]
      refine Int.ModEq.trans ?_ hcong
      have hK : (64 - 59) * (3 * n + 2) = 15 * n + 10 := by omega
      rw [hK]
      have := (c₄.mul_right (u : Int)).trans (Int.ModEq.refl _)
      refine this.trans ?_
      have hsgn : (if 0 ≤ I.f then (t₁ : Int) else -t₁) ≡ (if 0 ≤ I.f then 1 else -1) * I.a [ZMOD p] := by
        split
        · rw [Int.one_mul]; exact c₃
        · rw [neg_one_mul]; exact c₃.neg
      have := (hsgn.mul_right ((2 : Int) ^ (15 * n + 10))).mul_right (u : Int)
      refine this.trans (Int.ModEq.refl _ |>.trans ?_)
      rw [show (u : Int) * ((if 0 ≤ I.f then 1 else -1) * I.a) * 2 ^ (15 * n + 10) =
        (if 0 ≤ I.f then 1 else -1) * I.a * 2 ^ (15 * n + 10) * u by ring]
    exact e.symm.dvd

/-- The inverse at the width `w`. -/
theorem inverse_ok {s : State} {B : Addr} {Z w iU iV iX₂ iM : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (hw20 : w < 2 ^ 20) (hU : iU < 16) (hV : iV < 16) (hX : iX₂ < 16) (hM : iM < 16) (hVX : iV ≠ iX₂) :
    WP isa (inverse iU iV iX₂ iM) s fun t => t.gpr .rdi = B ∧
      Frm B [(slot w iV, 8 * w), (slot w iX₂, 8 * w), (slot w 16, 80 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t ∧
      (wv s.mem B (slot w iM) w % 2 = 1 →
        wv t.mem B (slot w iV) w = Nat.gcd (wv s.mem B (slot w iU) w) (wv s.mem B (slot w iM) w) ∧
        ((wv s.mem B (slot w iM) w : Nat) : Int) ∣
          (wv t.mem B (slot w iX₂) w : Int) * wv s.mem B (slot w iU) w - wv t.mem B (slot w iV) w ∧
        wv t.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w) := by
  unfold inverse
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9₁, m₁, k₁⟩ => ?_))
  refine WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 w ∧ t.mem = s₁.mem) (by xrun [h12]) rfl)
    fun s₂ ⟨⟨r13₂, m₂⟩, k₂⟩ => ?_
  have hm : s₂.mem = s.mem := by rw [m₂, m₁]
  have h₂ : Ws s₂ B Z w := h.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (k₁.trans k₂) (by decide)
  refine WP.mono (inverseN_ok h₂ hZ ((k₂.gpr (by decide)).trans h9₁) r13₂ (by have := h.w1; omega) (Nat.le_refl _) hw20 hU hV hX hM hVX (wv_lt _ _ _ _) (wv_lt _ _ _ _))
    fun t ⟨dt, ft, kt, ht⟩ => ⟨dt, by rw [← hm]; exact ft, keep_drop (r := .rdi) (((k₁.trans k₂).trans kt).mono
      (by decide)) (dt.trans h.rdi.symm), by
      rw [← hm]; exact ht⟩

end VG.Proof.Rsa.X86_64.InvB
