module

public import VerifiedGarbage.Proof.Rsa.X86_64.CvCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.WordGuard
public import VerifiedGarbage.Proof.Rsa.X86_64.WordFast
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Loop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# `vg_rsa_crt_values` on x86-64: `qInv`'s scaling on the guarded path

On the path the public guard of `wordChoice` takes, the inverse leaves out its
`K = 15 n + 10` modular doublings (`inverseNS`), and `qTail` multiplies `[x₂]`
by `2^K` modulo `p` instead: `T = (K - 1) mod 64 + 1` doublings of its low
`n + 1` words (`tailLoop_ok`), then `[x₂] 2^T` placed `Q = ⌊(K - 1) / 64⌋`
words up in `WordDivide`'s dividend `[d]` (`placeCopy_ok`), whose remainder
modulo `p` is `[x₂] 2^K mod p` (`cvQTail_ok`); `d` is kept in `[aSv]`
meanwhile.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The doublings, `(K - 1) mod 64 + 1` for `K = 15 (w / 2) + 10`. -/
def tailT (W : Nat) : Nat := (15 * (W / 2) + 9) % 64 + 1

/-- The words `[x₂] 2^T` is placed up, `⌊(K - 1) / 64⌋`. -/
def tailQ (W : Nat) : Nat := (15 * (W / 2) + 9) / 64

theorem tail_split (W : Nat) : 15 * (W / 2) + 10 = 64 * tailQ W + tailT W := by
  unfold tailQ tailT; omega

theorem tailK_ok {s : State} {W : Nat} (h12 : s.gpr .r12 = BitVec.ofNat 64 W) (hW : W < 2 ^ 24) :
    WP isa (.block tailK) s fun t => t.gpr .r13 = BitVec.ofNat 64 (W / 2) ∧
      t.gpr .rax = BitVec.ofNat 64 (15 * (W / 2) + 9) ∧ t.mem = s.mem ∧ Keep [.r13, .rax] s t := by
  refine WP.mono (WP.keep [.r13, .rax] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 (W / 2) ∧
    t.gpr .rax = BitVec.ofNat 64 (15 * (W / 2) + 9) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  unfold tailK
  xrun [h12]
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      show (BitVec.signExtend 64 (9 : BitVec 32)).toNat = 9 from rfl] <;> omega

/-- `dblSetup`: `w` and the stride, `r11 := T` and `r12 := n + 1`. -/
theorem dblSetup_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W) :
    WP isa (.block dblSetup) s fun t => t.gpr .r11 = BitVec.ofNat 64 (tailT W) ∧
      t.gpr .r12 = BitVec.ofNat 64 (W / 2 + 1) ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (W + 2)) ∧
      t.mem = s.mem ∧ Keep [.r12, .r9, .r13, .rax, .r11] s t := by
  have hW := h.w2
  unfold dblSetup
  rw [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (tailK_ok h12 hW) fun s₂ ⟨h13, hax, m₂, k₂⟩ => ?_)
  refine WP.mono (WP.keep [.r11, .r12] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (tailT W) ∧
    t.gpr .r12 = BitVec.ofNat 64 (W / 2 + 1) ∧ t.mem = s₂.mem) ?_ rfl) fun t ⟨⟨a, b, c⟩, k⟩ =>
    ⟨a, b, ((k₂.trans k).gpr (by decide)).trans h9, by rw [c, m₂, m₁],
      ((k₁.trans k₂).trans k).mono (by decide)⟩
  xrun [h13, hax]
  have e63 : ∀ x : Nat, x &&& 63 = x % 64 := fun x => Nat.and_two_pow_sub_one_eq_mod x 6
  have m1 : (15 * (W / 2) + 9) % 2 ^ 64 = 15 * (W / 2) + 9 := Nat.mod_eq_of_lt (by omega)
  have m2 : ((15 * (W / 2) + 9) % 64 + 1) % 2 ^ 64 = (15 * (W / 2) + 9) % 64 + 1 := Nat.mod_eq_of_lt (by omega)
  have m3 : (W / 2 % 2 ^ 64 + 1) % 2 ^ 64 = W / 2 + 1 := by
    rw [Nat.mod_eq_of_lt (show W / 2 < 2 ^ 64 by omega)]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      show (BitVec.signExtend 64 (63 : BitVec 32)).toNat = 63 from rfl,
      show (1 : BitVec 64).toNat = 1 from rfl, e63, m1]
    unfold tailT; rw [m2]
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    rw [m3, Nat.mod_eq_of_lt (by omega)]

theorem tailDec_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hb : s.gpr .r11 = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .sub .r11 (.imm 1)]) s fun s' =>
      s'.gpr .r11 = BitVec.ofNat 64 (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) ∧ s'.mem = s.mem ∧
        Keep [.r11] s s' := by
  have e := VG.Proof.X25519.X86_64.ofNat_sub_one hj hj'
  have ez := VG.Proof.X25519.X86_64.ofNat_eq_zero (j := j - 1) (by omega)
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (j - 1) ∧
    t.zf = some (decide (j - 1 = 0)) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  have e' : BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) := e
  xrun [hb]
  rw [e']; exact ⟨rfl, ez⟩

/-- `tailDbl`: `[x₂] := 2 [x₂]` over `N` words, and the count less one. -/
theorem tailDbl_ok {s : State} {B : Addr} {Z W N j : Nat} (h : Ws s B Z W)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (W + 2))) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hNw : N ≤ W + 2) (h11 : s.gpr .r11 = BitVec.ofNat 64 j) (hj : 1 ≤ j) (hj' : j < 2 ^ 64) :
    WP isa tailDbl s fun t => (∃ c : Bool,
      wv t.mem B (slot W aX₂) N + 2 ^ (64 * N) * c.toNat = 2 * wv s.mem B (slot W aX₂) N) ∧
      t.gpr .r11 = BitVec.ofNat 64 (j - 1) ∧ t.zf = some (decide (j - 1 = 0)) ∧
      Outside B (slot W aX₂) (8 * N) s.mem t.mem ∧ Keep [.rax, .rbp, .r14, .rbx, .r11] s t := by
  have hn := h.scr.nowrap
  have sX := h.sl (j := aX₂) (by decide)
  have hw := h.w2
  unfold tailDbl
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧
    t.mem = s.mem) (by xrun) rfl) fun s₁ ⟨⟨bp₁, m₁⟩, k₁⟩ =>
    WP.mono (base_ok aX₂ (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi)
      ((k₁.gpr (by decide)).trans h9)) fun s₂ ⟨bx, m₂, k₂⟩ => ?_))
  refine WP.seq (WP.mono (shl_ok (h.scr.congr (k₁.trans k₂).2.2) bx (((k₁.trans k₂).gpr (by decide)).trans h12)
    ((k₂.gpr (by decide)).trans bp₁) hN (by omega_arith) (by omega_arith)) fun s₃ ⟨c₃, _, hv₃, o₃, k₃⟩ => ?_)
  rw [m₂, m₁] at hv₃ o₃
  simp only [Bool.toNat_false, Nat.add_zero] at hv₃
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (tailDec_ok s₃ hj hj' ((k13.gpr (by decide)).trans h11)) fun t ⟨r11, zt, mt, kt⟩ =>
    ⟨⟨c₃, by rw [mt]; exact hv₃⟩, r11, zt, by rw [mt]; exact o₃, (k13.trans kt).mono (by decide)⟩

/-- `T` doublings of `[x₂]`'s low `n + 1` words, `x 2^T` when that fits. -/
theorem tailLoop_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (wk I.k + 2))) (h12 : s.gpr .r12 = BitVec.ofNat 64 (wk I.k / 2 + 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (tailT (wk I.k))) :
    WP isa (.loop tailDbl .ne) s fun t => CvS I m₀ t ∧
      Outside I.B (slot (wk I.k) aX₂) (8 * (wk I.k / 2 + 1)) s.mem t.mem ∧
      (wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) * 2 ^ tailT (wk I.k) < 2 ^ (64 * (wk I.k / 2 + 1)) →
        wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) =
          wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) * 2 ^ tailT (wk I.k)) ∧
      Keep [.rax, .rbp, .r14, .rbx, .r11] s t := by
  have hw := h.ws.w2
  have hT1 : 1 ≤ tailT (wk I.k) := by unfold tailT; omega
  have hT2 : tailT (wk I.k) ≤ 64 := by unfold tailT; omega
  generalize hx : wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) = x
  refine VG.Proof.X25519.X86_64.cntLoop_ok (n := tailT (wk I.k))
    (Inv := fun j u => CvS I m₀ u ∧ u.gpr .r9 = BitVec.ofNat 64 (8 * (wk I.k + 2)) ∧
      u.gpr .r12 = BitVec.ofNat 64 (wk I.k / 2 + 1) ∧ u.gpr .r11 = BitVec.ofNat 64 j ∧
      Outside I.B (slot (wk I.k) aX₂) (8 * (wk I.k / 2 + 1)) s.mem u.mem ∧
      (x * 2 ^ tailT (wk I.k) < 2 ^ (64 * (wk I.k / 2 + 1)) →
        wv u.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) = x * 2 ^ (tailT (wk I.k) - j)) ∧
      Keep [.rax, .rbp, .r14, .rbx, .r11] s u)
    (fun j u hj1 hjT ⟨hu, u9, u12, u11, ou, vu, ku⟩ => ?_)
    (fun u ⟨hu, _, _, _, ou, vu, ku⟩ => ⟨hu, ou, fun hf => by simpa using vu hf, ku⟩) hT1
    ⟨h, h9, h12, h11, Outside.refl _ _ _ _, fun _ => by rw [hx, Nat.sub_self, pow_zero, Nat.mul_one], Keep.refl _ _⟩
  refine WP.mono (tailDbl_ok hu.ws u9 u12 (by omega) (by omega) u11 hj1 (by omega))
    fun v ⟨⟨c, hv⟩, v11, vz, ov, kv⟩ => ⟨⟨hu.arr (by decide) (by omega) ov kv (by decide),
      (kv.gpr (by decide)).trans u9, (kv.gpr (by decide)).trans u12, v11, ou.trans ov, fun hf => ?_,
      (ku.trans kv).mono (by decide)⟩, vz⟩
  have e := vu hf
  rw [e] at hv
  have hp : 2 * (x * 2 ^ (tailT (wk I.k) - j)) = x * 2 ^ (tailT (wk I.k) - (j - 1)) := by
    rw [show tailT (wk I.k) - (j - 1) = (tailT (wk I.k) - j) + 1 by omega, pow_succ]; ring
  have hle : x * 2 ^ (tailT (wk I.k) - (j - 1)) ≤ x * 2 ^ tailT (wk I.k) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  cases c
  · simpa [hp] using hv
  · simp only [Bool.toNat_true, Nat.mul_one] at hv; omega

/-- `place`'s arithmetic: `r13 := 8 Q`, `r12 := w - Q`. -/
theorem qSplit_ok {s : State} {W : Nat} (hW : W < 2 ^ 24) (h12 : s.gpr .r12 = BitVec.ofNat 64 W)
    (hax : s.gpr .rax = BitVec.ofNat 64 (15 * (W / 2) + 9)) :
    WP isa (.block [.shift .shr .rax 6, .mov .r13 (.reg .rax), .alu .sub .r12 (.reg .r13), .shift .shl .r13 3]) s
      fun t => t.gpr .r13 = BitVec.ofNat 64 (8 * tailQ W) ∧ t.gpr .r12 = BitVec.ofNat 64 (W - tailQ W) ∧
        t.mem = s.mem ∧ Keep [.rax, .r13, .r12] s t := by
  have hq : tailQ W ≤ W := by unfold tailQ; omega
  refine WP.mono (WP.keep [.rax, .r13, .r12] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 (8 * tailQ W) ∧
    t.gpr .r12 = BitVec.ofNat 64 (W - tailQ W) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  xrun [h12, hax]
  have m1 : (15 * (W / 2) + 9) % 2 ^ 64 = 15 * (W / 2) + 9 := Nat.mod_eq_of_lt (by omega)
  have m2 : W % 2 ^ 64 = W := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, m1]
    unfold tailQ; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, m1, m2]
    unfold tailQ
    rw [show (2 : Nat) ^ 6 = 64 from rfl, show 2 ^ 64 - (15 * (W / 2) + 9) / 64 + W =
      (W - (15 * (W / 2) + 9) / 64) + 2 ^ 64 by omega, Nat.add_mod_right]

/-- `place` and `copyWords`: `[x₂]`'s low `w - Q` words at word `Q` of `[d]`. -/
theorem placeCopy_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) :
    WP isa (.seq (.block place) copyWords) s fun t => CvS I m₀ t ∧
      wv t.mem I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k)) (wk I.k - tailQ (wk I.k)) =
        wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k - tailQ (wk I.k)) ∧
      Outside I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k)) (8 * (wk I.k - tailQ (wk I.k))) s.mem t.mem := by
  have hn := h.ws.scr.nowrap
  have hw := h.ws.w2
  have hw1 := h.ws.w1
  have sD := h.ws.sl (j := aD) (by decide)
  have sX := h.ws.sl (j := aX₂) (by decide)
  have hq : tailQ (wk I.k) + 1 ≤ wk I.k := by unfold tailQ; omega
  have far := slot_far (w := wk I.k) (show aX₂ ≠ aD by decide)
  unfold place
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_))
  refine WP.block_append_iff.mpr (WP.mono (tailK_ok h12 hw) fun s₂ ⟨h13, hax, m₂, k₂⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (qSplit_ok hw ((k₂.gpr (by decide)).trans h12) hax)
    fun s₃ ⟨r13, r12, m₃, k₃⟩ => ?_)
  rw [← List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (base2_ok aX₂ aD (r₁ := .rsi) (r₂ := .rbx) (by decide) (by decide)
    (by decide) (((k₁.trans k₂).trans k₃).gpr (by decide) |>.trans h.ws.rdi)
    (((k₂.trans k₃)).gpr (by decide) |>.trans h9) (by decide)) fun s₄ ⟨hsi, hbx, m₄, k₄⟩ => ?_)
  refine WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = off I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k)) ∧
    t.mem = s₄.mem) (by
      xrun [hbx, (k₄.gpr (by decide)).trans r13]
      rw [← off_off]) rfl) fun s₅ ⟨⟨bx₅, m₅⟩, k₅⟩ => ?_
  have k15 := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  have hs₅ := h.ws.scr.congr k15.2.2
  refine WP.mono (copyWords_ok ((k₅.gpr (by decide)).trans hsi) bx₅ (((k₄.trans k₅).gpr (by decide)).trans r12)
    (by omega) (by omega_arith) (by omega_arith) (fun i hi => hs₅.ld (by omega_arith))
    (fun i hi => hs₅.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off I.B (by omega_arith)]; omega_arith)) fun t ⟨hv, _, o', kt⟩ => ?_
  have mm : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂, m₁]
  rw [mm] at hv o'
  refine ⟨h.step (Frm.of_outside o' (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_)
    (k15.trans kt) (by decide), hv, o'⟩
  · rw [List.mem_singleton.mp hr]; exact Or.inl (by have := slot_lin (wk I.k) aD; dsimp only; omega_arith)
  · rw [List.mem_singleton.mp hr]; dsimp only; omega_arith

/-- `qTail`: on a `p` of `n = w / 2` words with its top bit set, `[x₂] := [x₂] 2^K mod p`
for `[x₂] < p`; it keeps `p`, `q`, `d` and the mask. -/
theorem cvQTail_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) :
    WP isa (seqs qTail) s fun t => CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (∀ j, j = aP ∨ j = aQ ∨ j = aD →
        wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k)) ∧
      (2 ^ (64 * (wk I.k / 2) - 1) ≤ wv s.mem I.B (slot (wk I.k) aP) (wk I.k) →
        wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 2 ^ (64 * (wk I.k / 2)) →
        wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k) < wv s.mem I.B (slot (wk I.k) aP) (wk I.k) →
        wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) =
          wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k) * 2 ^ (15 * (wk I.k / 2) + 10) %
            wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have hw := h.ws.w2
  have hk1 := L.k1
  have hW6 : 6 ≤ wk I.k := by unfold wk; omega_using [hk1]
  have hZ17 : slot (wk I.k) 17 ≤ I.Z := by
    have hz := L.z
    simp only [slot, Impl.Bignum.hdrBytes, wk]
    omega_using [hk1, hz]
  have hq : tailQ (wk I.k) + (wk I.k / 2 + 1) ≤ wk I.k := by unfold tailQ; omega
  have hT : tailT (wk I.k) ≤ 64 := by unfold tailT; omega
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega_arith) hi hZ hn
  have hmw : ∀ {m m' : Mem} {j L' : Nat}, Outside I.B (slot (wk I.k) j) L' m m' →
      mword m' I.B = mword m I.B := fun {_ _ j _} o =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
      (by change 8 * 22 + 8 ≤ 2 ^ 64; decide)
  simp only [qTail, seqs]
  -- `[aSv] := d`.
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aSv) (by decide)) fun s₁ ⟨_, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁.ws (o := aSv) (a := aD) (by decide) (by decide) (by decide))
    fun s₂ ⟨c₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (by omega_arith) o₂ k₂ (by decide)
  rw [ot o₁ (Nat.le_refl _) (by decide) (by decide)] at c₂
  have u₂ : ∀ i, i < 16 → i ≠ aSv → wv s₂.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) :=
    fun i hi hne => by rw [ot o₂ (by omega_arith) hne hi, ot o₁ (Nat.le_refl _) hne hi]
  -- The doublings.
  refine WP.seq (WP.seq (WP.mono (dblSetup_ok h₂.ws) fun s₃ ⟨r11, r12, r9, m₃, k₃⟩ => ?_))
  have h₃ := h₂.step (rs := []) (by rw [m₃]; exact Frm.refl _ _ _) (by simp) (by simp) k₃ (by decide)
  refine WP.mono (tailLoop_ok h₃ r9 r12 r11) fun s₄ ⟨h₄, o₄, v₄, k₄⟩ => ?_
  rw [m₃] at o₄ v₄
  -- `[d] := [x₂] 2^(64 Q)`.
  refine WP.seq (WP.mono (zeroA_ok h₄.ws (j := aD) (by decide)) fun s₅ ⟨z₅, o₅, k₅⟩ => ?_)
  have h₅ := h₄.arr (by decide) (Nat.le_refl _) o₅ k₅ (by decide)
  refine WP.seq (WP.mono (placeCopy_ok h₅) fun s₆ ⟨h₆, c₆, o₆⟩ => ?_)
  -- `[c] := p`.
  refine WP.seq (WP.mono (zeroA_ok h₆.ws (j := aC) (by decide)) fun s₇ ⟨_, o₇, k₇⟩ => ?_)
  have h₇ := h₆.arr (by decide) (Nat.le_refl _) o₇ k₇ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₇.ws (o := aC) (a := aP) (by decide) (by decide) (by decide))
    fun s₈ ⟨c₈, o₈, k₈⟩ => ?_)
  have h₈ := h₇.arr (by decide) (by omega_arith) o₈ k₈ (by decide)
  -- The reduction.
  refine WP.seq (WP.mono (WordDivide.fast_ok h₈.ws hZ17 hW6) fun s₉ ⟨v₉, f₉, k₉⟩ => ?_)
  have bound : ∀ r ∈ WordDivide.normRanges (wk I.k), r.1 + r.2 ≤ I.Z := by
    intro r hr
    simp only [WordDivide.normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact h.ws.sl (by decide)
    · exact WordDivide.all_bound h.ws hZ17 hr
  have h₉ := h₈.step f₉ (by
    intro r hr
    simp only [WordDivide.normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact Mut.ofSlot _ _ _
    · exact WordDivide.all_mut hr) bound k₉ (by decide)
  have f9 : ∀ i, i = aP ∨ i = aQ ∨ i = aD ∨ i = aX₂ ∨ i = aSv →
      wv s₉.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₈.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi => by
    apply f₉.wv_eq _ (by have := h.ws.sl (j := i) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide); omega_arith)
    intro r hr
    simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [VG.Impl.Rsa.X86_64.WordDivide.aM, VG.Impl.Rsa.X86_64.WordDivide.aR, VG.Impl.Rsa.X86_64.WordDivide.aT,
        VG.Impl.Rsa.X86_64.WordDivide.aV, VG.Impl.Rsa.X86_64.Keys.CrtValues.aP,
        VG.Impl.Rsa.X86_64.Keys.CrtValues.aQ, VG.Impl.Rsa.X86_64.Keys.CrtValues.aD, aX₂, aSv, slot] <;> omega_arith
  have mw9 : mword s₉.mem I.B = mword s₈.mem I.B := f₉.word_eq (by
    intro r hr
    simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [VG.Impl.Rsa.X86_64.WordDivide.aM, VG.Impl.Rsa.X86_64.WordDivide.aR,
        VG.Impl.Rsa.X86_64.WordDivide.aT, VG.Impl.Rsa.X86_64.WordDivide.aV, slot, Public.sMask, sFn,
        Impl.Bignum.hdrBytes] <;> omega_arith) (by change 8 * 22 + 8 ≤ 2 ^ 64; decide)
  -- `[x₂] :=` the remainder, `[d] := [aSv]`.
  refine WP.seq (WP.mono (zeroA_ok h₉.ws (j := aX₂) (by decide)) fun s₁₀ ⟨_, o₁₀, k₁₀⟩ => ?_)
  have h₁₀ := h₉.arr (by decide) (Nat.le_refl _) o₁₀ k₁₀ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁₀.ws (o := aX₂) (a := aV) (by decide) (by decide) (by decide))
    fun s₁₁ ⟨c₁₁, o₁₁, k₁₁⟩ => ?_)
  have h₁₁ := h₁₀.arr (by decide) (by omega_arith) o₁₁ k₁₁ (by decide)
  refine WP.mono (copyA_ok h₁₁.ws (o := aD) (a := aSv) (by decide) (by decide) (by decide))
    fun t ⟨ct, ot', kt⟩ => ?_
  have ht := h₁₁.arr (by decide) (by omega_arith) ot' kt (by decide)
  -- What each piece leaves.
  have o6 : ∀ i, i < 16 → i ≠ aD → wv s₆.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₅.mem I.B (slot (wk I.k) i) (wk I.k) :=
    fun i hi hne => o₆.wv (by have := slot_far (w := wk I.k) hne; omega_arith)
      (by have := h.ws.sl hi; omega_arith)
  have pre : ∀ i, i < 16 → i ≠ aSv → i ≠ aX₂ → i ≠ aD → i ≠ aC → i ≠ aV → i ≠ 8 →
      wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi h1 h2 h3 h4 h5 h6 => by
    have e9 : wv s₉.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₈.mem I.B (slot (wk I.k) i) (wk I.k) := by
      apply f₉.wv_eq _ (by have := h.ws.sl hi; omega_arith)
      intro r hr
      simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have a1 := slot_far (w := wk I.k) (show i ≠ 9 from h4)
      have a2 := slot_far (w := wk I.k) (show i ≠ 3 from h5)
      have a3 := slot_far (w := wk I.k) h6
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp only [VG.Impl.Rsa.X86_64.WordDivide.aM, VG.Impl.Rsa.X86_64.WordDivide.aR,
          VG.Impl.Rsa.X86_64.WordDivide.aT, VG.Impl.Rsa.X86_64.WordDivide.aV] at a1 a2 a3 ⊢
      · omega_arith
      · omega_arith
      · omega_arith
      · have := slot_lt (w := wk I.k) hi; have := slot_lin (wk I.k) 16; omega_arith
    rw [ot ot' (by omega_arith) h3 hi, ot o₁₁ (by omega_arith) h2 hi, ot o₁₀ (Nat.le_refl _) h2 hi, e9,
      ot o₈ (by omega_arith) h4 hi, ot o₇ (Nat.le_refl _) h4 hi, o6 i hi h3, ot o₅ (Nat.le_refl _) h3 hi,
      ot o₄ (by omega_arith) h2 hi, u₂ i hi h1]
  have aSvT : wv s₁₁.mem I.B (slot (wk I.k) aSv) (wk I.k) = wv s.mem I.B (slot (wk I.k) aD) (wk I.k) := by
    rw [ot o₁₁ (by omega_arith) (by decide) (by decide), ot o₁₀ (Nat.le_refl _) (by decide) (by decide),
      f9 aSv (by simp), ot o₈ (by omega_arith) (by decide) (by decide), ot o₇ (Nat.le_refl _) (by decide) (by decide),
      o6 aSv (by decide) (by decide), ot o₅ (Nat.le_refl _) (by decide) (by decide),
      ot o₄ (by omega_arith) (by decide) (by decide), c₂]
  have sD := h.ws.sl (j := aD) (by decide)
  have sX := h.ws.sl (j := aX₂) (by decide)
  refine ⟨ht, ?_, ?_, ?_⟩
  · have mw6 : mword s₆.mem I.B = mword s₅.mem I.B :=
      o₆.word (Or.inl (by have := hdr_lt_slot (wk I.k) aD (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
        (by change 8 * 22 + 8 ≤ 2 ^ 64; decide)
    rw [hmw ot', hmw o₁₁, hmw o₁₀, mw9, hmw o₈, hmw o₇, mw6, hmw o₅, hmw o₄, hmw o₂, hmw o₁]
  · intro j hj
    rcases hj with rfl | rfl | rfl
    · exact pre aP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact pre aQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [ct, aSvT]
  · intro hPt hPlt hx
    have hn1 : 1 ≤ wk I.k / 2 := by omega
    generalize hP : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) = P at hPt hPlt hx
    generalize hX : wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k) = x at hx
    have hP1 : 2 ^ (64 * (wk I.k / 2)) * 2 ^ 64 = 2 ^ (64 * (wk I.k / 2 + 1)) := by
      rw [← pow_add]; congr 1
    have hxT : x * 2 ^ tailT (wk I.k) < 2 ^ (64 * (wk I.k / 2 + 1)) := by
      rw [← hP1]
      exact Nat.mul_lt_mul_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by decide) hT) (by positivity)
    have hxn : x < 2 ^ (64 * (wk I.k / 2 + 1)) := by
      have : 2 ^ (64 * (wk I.k / 2)) ≤ 2 ^ (64 * (wk I.k / 2 + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have x2 : wv s₂.mem I.B (slot (wk I.k) aX₂) (wk I.k) = x := by rw [u₂ aX₂ (by decide) (by decide), hX]
    have xl2 : wv s₂.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) = x :=
      (wv_low_of_lt (by omega) (by rw [x2]; exact hxn)).trans x2
    have v4 := v₄ (by rw [xl2]; exact hxT)
    rw [xl2] at v4
    have e2 := wv_add s₂.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) (wk I.k - (wk I.k / 2 + 1))
    have e4 := wv_add s₄.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) (wk I.k - (wk I.k / 2 + 1))
    rw [show wk I.k / 2 + 1 + (wk I.k - (wk I.k / 2 + 1)) = wk I.k by omega] at e2 e4
    have hi4 : wv s₄.mem I.B (slot (wk I.k) aX₂ + 8 * (wk I.k / 2 + 1)) (wk I.k - (wk I.k / 2 + 1)) =
        wv s₂.mem I.B (slot (wk I.k) aX₂ + 8 * (wk I.k / 2 + 1)) (wk I.k - (wk I.k / 2 + 1)) :=
      o₄.wv (Or.inr (by omega)) (by omega_arith)
    have hi2 : wv s₂.mem I.B (slot (wk I.k) aX₂ + 8 * (wk I.k / 2 + 1)) (wk I.k - (wk I.k / 2 + 1)) = 0 := by
      rw [x2, xl2] at e2
      have : 2 ^ (64 * (wk I.k / 2 + 1)) *
          wv s₂.mem I.B (slot (wk I.k) aX₂ + 8 * (wk I.k / 2 + 1)) (wk I.k - (wk I.k / 2 + 1)) = 0 := by omega
      exact (Nat.mul_eq_zero.mp this).resolve_left (by positivity)
    have x4 : wv s₄.mem I.B (slot (wk I.k) aX₂) (wk I.k) = x * 2 ^ tailT (wk I.k) := by
      rw [e4, v4, hi4, hi2, Nat.mul_zero, Nat.add_zero]
    have x5 : wv s₅.mem I.B (slot (wk I.k) aX₂) (wk I.k) = x * 2 ^ tailT (wk I.k) := by
      rw [ot o₅ (Nat.le_refl _) (by decide) (by decide), x4]
    have hxQ : x * 2 ^ tailT (wk I.k) < 2 ^ (64 * (wk I.k - tailQ (wk I.k))) :=
      Nat.lt_of_lt_of_le hxT (Nat.pow_le_pow_right (by decide) (by omega))
    have x5' : wv s₅.mem I.B (slot (wk I.k) aX₂) (wk I.k - tailQ (wk I.k)) = x * 2 ^ tailT (wk I.k) :=
      (wv_low_of_lt (by omega) (by rw [x5]; exact hxQ)).trans x5
    have z5Q : wv s₅.mem I.B (slot (wk I.k) aD) (tailQ (wk I.k)) = 0 := by
      have e := wv_add s₅.mem I.B (slot (wk I.k) aD) (tailQ (wk I.k)) (wk I.k + 2 - tailQ (wk I.k))
      rw [show tailQ (wk I.k) + (wk I.k + 2 - tailQ (wk I.k)) = wk I.k + 2 by omega, z₅] at e
      omega
    have dlow : wv s₆.mem I.B (slot (wk I.k) aD) (tailQ (wk I.k)) = 0 := by
      rw [o₆.wv (Or.inl (by omega)) (by omega_arith), z5Q]
    have d6 : wv s₆.mem I.B (slot (wk I.k) aD) (wk I.k) = 2 ^ (64 * tailQ (wk I.k)) * (x * 2 ^ tailT (wk I.k)) := by
      have e := wv_add s₆.mem I.B (slot (wk I.k) aD) (tailQ (wk I.k)) (wk I.k - tailQ (wk I.k))
      rw [show tailQ (wk I.k) + (wk I.k - tailQ (wk I.k)) = wk I.k by omega] at e
      rw [e, dlow, c₆, x5', Nat.zero_add]
    have d8 : wv s₈.mem I.B (slot (wk I.k) aD) (wk I.k) = 2 ^ (64 * tailQ (wk I.k)) * (x * 2 ^ tailT (wk I.k)) := by
      rw [ot o₈ (by omega_arith) (by decide) (by decide), ot o₇ (Nat.le_refl _) (by decide) (by decide), d6]
    have p8 : wv s₈.mem I.B (slot (wk I.k) aC) (wk I.k) = P := by
      rw [c₈, ot o₇ (Nat.le_refl _) (by decide) (by decide), o6 aP (by decide) (by decide),
        ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega_arith) (by decide) (by decide),
        u₂ aP (by decide) (by decide), hP]
    have pn : wv s₈.mem I.B (slot (wk I.k) aC) (wk I.k / 2) = P :=
      (wv_low_of_lt (by omega) (by rw [p8]; exact hPlt)).trans p8
    have top := WordDivide.top_of_bound (m := s₈.mem) (B := I.B) (e := slot (wk I.k) aC) (n := wk I.k / 2) hn1
      (by rw [pn]; exact hPt)
    have r9 := v₉ top
    change wv s₉.mem I.B (slot (wk I.k) aV) (wk I.k + 1) =
      wv s₈.mem I.B (slot (wk I.k) aD) (wk I.k) % wv s₈.mem I.B (slot (wk I.k) aC) (wk I.k / 2) at r9
    rw [d8, pn] at r9
    have hlt : 2 ^ (64 * tailQ (wk I.k)) * (x * 2 ^ tailT (wk I.k)) % P < 2 ^ (64 * wk I.k) :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega))
        (Nat.le_trans hPlt.le (Nat.pow_le_pow_right (by decide) (by omega)))
    have r9' : wv s₉.mem I.B (slot (wk I.k) aV) (wk I.k) = 2 ^ (64 * tailQ (wk I.k)) * (x * 2 ^ tailT (wk I.k)) % P :=
      (wv_low_of_lt (by omega) (by rw [r9]; exact hlt)).trans r9
    rw [ot ot' (by omega_arith) (by decide) (by decide), c₁₁, ot o₁₀ (Nat.le_refl _) (by decide) (by decide), r9',
      tail_split, pow_add, pow_mul]
    congr 1; ring


/-- The public guard of `wordChoice` and `guarded` holds. -/
def cvGuard (I : CvIn) : Prop := WordDivide.guardVal (wk I.k) I.k I.pl I.ql ((I.nb[0]?).getD 0) = 0

instance (I : CvIn) : Decidable (cvGuard I) := by unfold cvGuard; infer_instance

theorem cvGuard_iff {I : CvIn} (L : CvLens I) :
    cvGuard I ↔ WordDivide.guardVal (wk I.k) I.k I.pl I.ql (I.nb[0]'(by rw [L.nl]; have := L.k1; omega)) = 0 := by
  have hnl : 0 < I.nb.length := by rw [L.nl]; have := L.k1; omega
  simp only [cvGuard, List.getElem?_eq_getElem hnl, Option.getD_some]

/-- `guarded a b` runs `a` where the guard holds, else `b`, from the state after
the guard (which keeps the memory). -/
theorem cvGuarded_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {a b : Prog isa}
    {Q : State → Prop}
    (ha : ∀ s₂, CvS I m₀ s₂ → s₂.mem = s.mem → cvGuard I → WP isa a s₂ Q)
    (hb : ∀ s₂, CvS I m₀ s₂ → s₂.mem = s.mem → ¬ cvGuard I → WP isa b s₂ Q) :
    WP isa (guarded a b) s Q := by
  unfold guarded
  refine WP.seq (WP.mono (WordDivide.guardHead_ok h) fun s₁ ⟨h₁, m₁, h12, hdx⟩ => ?_)
  refine WP.seq (WP.mono (WordDivide.guardTail_ok h₁ L h12 hdx) fun s₂ ⟨h₂, m₂, hz⟩ => ?_)
  refine WP.ite (WordDivide.guardVal (wk I.k) I.k I.pl I.ql (I.nb[0]'(by rw [L.nl]; have := L.k1; omega)) == 0)
    (by simp only [eval, hz]) (fun hg => ha s₂ h₂ (m₂.trans m₁) ((cvGuard_iff L).mpr (by simpa using hg)))
    (fun hg => hb s₂ h₂ (m₂.trans m₁) (fun g => by simp [(cvGuard_iff L).mp g] at hg))

/-- The guarded `qTail`: `[x₂] 2^K mod p` where the guard holds, for a `p` of
`n` words with its top bit set and `[x₂] < p`; `[x₂]` unchanged elsewhere. -/
theorem cvTailG_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) :
    WP isa (guarded (seqs qTail) (.block [])) s fun t => CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (∀ j, j = aP ∨ j = aQ ∨ j = aD →
        wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k)) ∧
      (cvGuard I → 2 ^ (64 * (wk I.k / 2) - 1) ≤ wv s.mem I.B (slot (wk I.k) aP) (wk I.k) →
        wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 2 ^ (64 * (wk I.k / 2)) →
        wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k) < wv s.mem I.B (slot (wk I.k) aP) (wk I.k) →
        wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) =
          wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k) * 2 ^ (15 * (wk I.k / 2) + 10) %
            wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
      (¬ cvGuard I → wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) = wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k)) := by
  refine cvGuarded_ok h L (fun s₂ h₂ m₂ g => ?_) (fun s₂ h₂ m₂ g => ?_)
  · refine WP.mono (cvQTail_ok h₂ L) fun t ⟨ht, mt, pt, vt⟩ => ⟨ht, by rw [mt, m₂], fun j hj => by rw [pt j hj, m₂],
      fun _ a b c => by rw [m₂] at vt; exact vt a b c, fun ng => absurd g ng⟩
  · exact WP.block_nil ⟨h₂, by rw [m₂], fun j _ => by rw [m₂], fun g' => absurd g' g, fun _ => by rw [m₂]⟩

end VG.Proof.Rsa.X86_64
