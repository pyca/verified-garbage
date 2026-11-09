module
-- separate module: its proofs (the linear blocks) build in parallel with those of `Fns`, which `Steps` also imports

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521F.Lin
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86_64.Chain

/-!
# P-521 on x86-64: `C [a] - D [b] mod p` (`cmsF`)

`N = C [a] + D (p - [b])` in `CW` by shifts (`shlCW_ok`), complements
(`negLoads_ok`), `sbb` (`addNeg_ok`) and `mulx` (`addMulC_ok`), then
`[o] = N mod p` by s2n-bignum's ending of `cmsub_p521` (`cmsTail_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P521F

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.P521F
open VG.Impl.Weierstrass.X86_64.Mont (fnTmp)
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono add_carry adc_carry mulx_arith execMulx_eq of_setReg of_setFlags)

variable {Z : Nat}

theorem p7 : (2 : Nat) ^ (64 * 7) = (2 ^ 64) ^ 7 := Nat.pow_mul 2 64 7

theorem cons_split (x : Instr) (l : List Instr) : x :: l = [x] ++ l := rfl

theorem keepsIn {r : Reg} {rs : List Reg} {s s' : State} (h : r ∈ rs) (k : Keeps [r] s s') : Keeps rs s s' :=
  k.mono fun q hq => by rw [List.mem_singleton] at hq; exact hq ▸ h

/-- The words of `N`, from the bottom. -/
theorem regsCW (s : State) : regsVal s CW = (s.gpr .r8).toNat + 2 ^ 64 * ((s.gpr .r9).toNat +
    2 ^ 64 * ((s.gpr .r10).toNat + 2 ^ 64 * ((s.gpr .r11).toNat + 2 ^ 64 * ((s.gpr .r12).toNat +
    2 ^ 64 * ((s.gpr .r13).toNat + 2 ^ 64 * ((s.gpr .r14).toNat + 2 ^ 64 * ((s.gpr .r15).toNat +
    2 ^ 64 * (s.gpr .rbx).toNat))))))) := by
  simp only [regsVal, CW, Nat.mul_zero, Nat.add_zero]

/-! ## Shifts -/

theorem shl_word {w n : Nat} (hn : n ≤ 64) :
    w * 2 ^ n = w * 2 ^ n % 2 ^ 64 + 2 ^ 64 * (w / 2 ^ (64 - n)) := by
  have e : (2 : Nat) ^ 64 = 2 ^ (64 - n) * 2 ^ n := by rw [← Nat.pow_add, Nat.sub_add_cancel hn]
  have h := Nat.div_add_mod (w * 2 ^ n) (2 ^ 64)
  have hq : w * 2 ^ n / 2 ^ 64 = w / 2 ^ (64 - n) := by
    rw [e, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos n)]
  rw [hq] at h
  omega

theorem shlStep {x l h hin X V c : Nat} (w : x * c = l + 2 ^ 64 * h) (v : V = X * c + h) :
    l + hin + 2 ^ 64 * V = (x + 2 ^ 64 * X) * c + hin := by
  rw [v, Nat.add_mul, w, Nat.mul_assoc]
  omega

theorem shl9 {c x0 x1 x2 x3 x4 x5 x6 x7 x8 l0 l1 l2 l3 l4 l5 l6 l7 l8 h0 h1 h2 h3 h4 h5 h6 h7 : Nat}
    (w0 : x0 * c = l0 + 2 ^ 64 * h0) (w1 : x1 * c = l1 + 2 ^ 64 * h1)
    (w2 : x2 * c = l2 + 2 ^ 64 * h2) (w3 : x3 * c = l3 + 2 ^ 64 * h3)
    (w4 : x4 * c = l4 + 2 ^ 64 * h4) (w5 : x5 * c = l5 + 2 ^ 64 * h5)
    (w6 : x6 * c = l6 + 2 ^ 64 * h6) (w7 : x7 * c = l7 + 2 ^ 64 * h7)
    (w8 : x8 * c = l8 + 2 ^ 64 * 0) :
    l0 + 2 ^ 64 * (l1 + h0 + 2 ^ 64 * (l2 + h1 + 2 ^ 64 * (l3 + h2 + 2 ^ 64 * (l4 + h3 +
      2 ^ 64 * (l5 + h4 + 2 ^ 64 * (l6 + h5 + 2 ^ 64 * (l7 + h6 + 2 ^ 64 * (l8 + h7)))))))) =
    (x0 + 2 ^ 64 * (x1 + 2 ^ 64 * (x2 + 2 ^ 64 * (x3 + 2 ^ 64 * (x4 + 2 ^ 64 * (x5 + 2 ^ 64 * (x6 +
      2 ^ 64 * (x7 + 2 ^ 64 * x8)))))))) * c := by
  have v8 : l8 + h7 = x8 * c + h7 := by rw [w8, Nat.mul_zero, Nat.add_zero]
  have v0 := shlStep (hin := 0) w0 (shlStep (hin := h0) w1 (shlStep (hin := h1) w2
    (shlStep (hin := h2) w3 (shlStep (hin := h3) w4 (shlStep (hin := h4) w5 (shlStep (hin := h5) w6
    (shlStep (hin := h6) w7 v8)))))))
  rw [Nat.add_zero, Nat.add_zero] at v0
  exact v0

/-- `N 2^n` by `shld` from the top word down, for `N`'s top word below `2^(64 - n)`. -/
theorem shlCW_ok (s : State) {n : Nat} (hn : n = 2 ∨ n = 3) (htop : (s.gpr .rbx).toNat < 2 ^ 61) :
    WP isa (.block (shlChain CWr n)) s fun s' => regsVal s' CW = regsVal s CW * 2 ^ n ∧ Keeps CW s s' := by
  have hn' : 1 ≤ n ∧ n ≤ 63 := by omega
  simp only [shlChain, CWr]
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (shldS_ok s .rbx .r15 hn') fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (shldS_ok s₁ .r15 .r14 hn') fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (shldS_ok s₂ .r14 .r13 hn') fun s₃ ⟨e₃, k₃⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (shldS_ok s₃ .r13 .r12 hn') fun s₄ ⟨e₄, k₄⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (shldS_ok s₄ .r12 .r11 hn') fun s₅ ⟨e₅, k₅⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (shldS_ok s₅ .r11 .r10 hn') fun s₆ ⟨e₆, k₆⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (shldS_ok s₆ .r10 .r9 hn') fun s₇ ⟨e₇, k₇⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (shldS_ok s₇ .r9 .r8 hn') fun s₈ ⟨e₈, k₈⟩ => ?_
  refine WP.mono (shlS_ok s₈ .r8 hn') fun s₉ ⟨e₉, k₉⟩ => ⟨?_, ?_⟩
  · rw [regsCW, regsCW]
    have f_rbx : s₉.gpr .rbx = s₁.gpr .rbx := ((((((((k₉.1 .rbx (by decide)).trans (k₈.1 .rbx (by decide))).trans (k₇.1 .rbx (by decide))).trans (k₆.1 .rbx (by decide))).trans (k₅.1 .rbx (by decide))).trans (k₄.1 .rbx (by decide))).trans (k₃.1 .rbx (by decide))).trans (k₂.1 .rbx (by decide)))
    have f_r15 : s₉.gpr .r15 = s₂.gpr .r15 := (((((((k₉.1 .r15 (by decide)).trans (k₈.1 .r15 (by decide))).trans (k₇.1 .r15 (by decide))).trans (k₆.1 .r15 (by decide))).trans (k₅.1 .r15 (by decide))).trans (k₄.1 .r15 (by decide))).trans (k₃.1 .r15 (by decide)))
    have f_r14 : s₉.gpr .r14 = s₃.gpr .r14 := ((((((k₉.1 .r14 (by decide)).trans (k₈.1 .r14 (by decide))).trans (k₇.1 .r14 (by decide))).trans (k₆.1 .r14 (by decide))).trans (k₅.1 .r14 (by decide))).trans (k₄.1 .r14 (by decide)))
    have f_r13 : s₉.gpr .r13 = s₄.gpr .r13 := (((((k₉.1 .r13 (by decide)).trans (k₈.1 .r13 (by decide))).trans (k₇.1 .r13 (by decide))).trans (k₆.1 .r13 (by decide))).trans (k₅.1 .r13 (by decide)))
    have f_r12 : s₉.gpr .r12 = s₅.gpr .r12 := ((((k₉.1 .r12 (by decide)).trans (k₈.1 .r12 (by decide))).trans (k₇.1 .r12 (by decide))).trans (k₆.1 .r12 (by decide)))
    have f_r11 : s₉.gpr .r11 = s₆.gpr .r11 := (((k₉.1 .r11 (by decide)).trans (k₈.1 .r11 (by decide))).trans (k₇.1 .r11 (by decide)))
    have f_r10 : s₉.gpr .r10 = s₇.gpr .r10 := ((k₉.1 .r10 (by decide)).trans (k₈.1 .r10 (by decide)))
    have f_r9 : s₉.gpr .r9 = s₈.gpr .r9 := (k₉.1 .r9 (by decide))
    have f_r8 : s₉.gpr .r8 = s₉.gpr .r8 := rfl
    have q_rbx : s.gpr .r15 = s.gpr .r15 := rfl
    have p_r15 : s₁.gpr .r15 = s.gpr .r15 := (k₁.1 .r15 (by decide))
    have q_r15 : s₁.gpr .r14 = s.gpr .r14 := (k₁.1 .r14 (by decide))
    have p_r14 : s₂.gpr .r14 = s.gpr .r14 := ((k₂.1 .r14 (by decide)).trans (k₁.1 .r14 (by decide)))
    have q_r14 : s₂.gpr .r13 = s.gpr .r13 := ((k₂.1 .r13 (by decide)).trans (k₁.1 .r13 (by decide)))
    have p_r13 : s₃.gpr .r13 = s.gpr .r13 := (((k₃.1 .r13 (by decide)).trans (k₂.1 .r13 (by decide))).trans (k₁.1 .r13 (by decide)))
    have q_r13 : s₃.gpr .r12 = s.gpr .r12 := (((k₃.1 .r12 (by decide)).trans (k₂.1 .r12 (by decide))).trans (k₁.1 .r12 (by decide)))
    have p_r12 : s₄.gpr .r12 = s.gpr .r12 := ((((k₄.1 .r12 (by decide)).trans (k₃.1 .r12 (by decide))).trans (k₂.1 .r12 (by decide))).trans (k₁.1 .r12 (by decide)))
    have q_r12 : s₄.gpr .r11 = s.gpr .r11 := ((((k₄.1 .r11 (by decide)).trans (k₃.1 .r11 (by decide))).trans (k₂.1 .r11 (by decide))).trans (k₁.1 .r11 (by decide)))
    have p_r11 : s₅.gpr .r11 = s.gpr .r11 := (((((k₅.1 .r11 (by decide)).trans (k₄.1 .r11 (by decide))).trans (k₃.1 .r11 (by decide))).trans (k₂.1 .r11 (by decide))).trans (k₁.1 .r11 (by decide)))
    have q_r11 : s₅.gpr .r10 = s.gpr .r10 := (((((k₅.1 .r10 (by decide)).trans (k₄.1 .r10 (by decide))).trans (k₃.1 .r10 (by decide))).trans (k₂.1 .r10 (by decide))).trans (k₁.1 .r10 (by decide)))
    have p_r10 : s₆.gpr .r10 = s.gpr .r10 := ((((((k₆.1 .r10 (by decide)).trans (k₅.1 .r10 (by decide))).trans (k₄.1 .r10 (by decide))).trans (k₃.1 .r10 (by decide))).trans (k₂.1 .r10 (by decide))).trans (k₁.1 .r10 (by decide)))
    have q_r10 : s₆.gpr .r9 = s.gpr .r9 := ((((((k₆.1 .r9 (by decide)).trans (k₅.1 .r9 (by decide))).trans (k₄.1 .r9 (by decide))).trans (k₃.1 .r9 (by decide))).trans (k₂.1 .r9 (by decide))).trans (k₁.1 .r9 (by decide)))
    have p_r9 : s₇.gpr .r9 = s.gpr .r9 := (((((((k₇.1 .r9 (by decide)).trans (k₆.1 .r9 (by decide))).trans (k₅.1 .r9 (by decide))).trans (k₄.1 .r9 (by decide))).trans (k₃.1 .r9 (by decide))).trans (k₂.1 .r9 (by decide))).trans (k₁.1 .r9 (by decide)))
    have q_r9 : s₇.gpr .r8 = s.gpr .r8 := (((((((k₇.1 .r8 (by decide)).trans (k₆.1 .r8 (by decide))).trans (k₅.1 .r8 (by decide))).trans (k₄.1 .r8 (by decide))).trans (k₃.1 .r8 (by decide))).trans (k₂.1 .r8 (by decide))).trans (k₁.1 .r8 (by decide)))
    have p_r8 : s₈.gpr .r8 = s.gpr .r8 := ((((((((k₈.1 .r8 (by decide)).trans (k₇.1 .r8 (by decide))).trans (k₆.1 .r8 (by decide))).trans (k₅.1 .r8 (by decide))).trans (k₄.1 .r8 (by decide))).trans (k₃.1 .r8 (by decide))).trans (k₂.1 .r8 (by decide))).trans (k₁.1 .r8 (by decide)))
    rw [f_rbx, f_r15, f_r14, f_r13, f_r12, f_r11, f_r10, f_r9, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉,
      p_r15, p_r14, p_r13, p_r12, p_r11, p_r10, p_r9, p_r8, q_rbx, q_r15, q_r14, q_r13, q_r12, q_r11,
      q_r10, q_r9]
    have hn64 : n ≤ 64 := by omega
    have w0 := shl_word (w := (s.gpr .r8).toNat) hn64
    have w1 := shl_word (w := (s.gpr .r9).toNat) hn64
    have w2 := shl_word (w := (s.gpr .r10).toNat) hn64
    have w3 := shl_word (w := (s.gpr .r11).toNat) hn64
    have w4 := shl_word (w := (s.gpr .r12).toNat) hn64
    have w5 := shl_word (w := (s.gpr .r13).toNat) hn64
    have w6 := shl_word (w := (s.gpr .r14).toNat) hn64
    have w7 := shl_word (w := (s.gpr .r15).toNat) hn64
    have w8 := shl_word (w := (s.gpr .rbx).toNat) hn64
    have h8 : (s.gpr .rbx).toNat / 2 ^ (64 - n) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le htop (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [h8] at w8
    generalize (s.gpr .r8).toNat * 2 ^ n % 2 ^ 64 = l0 at *
    generalize (s.gpr .r9).toNat * 2 ^ n % 2 ^ 64 = l1 at *
    generalize (s.gpr .r10).toNat * 2 ^ n % 2 ^ 64 = l2 at *
    generalize (s.gpr .r11).toNat * 2 ^ n % 2 ^ 64 = l3 at *
    generalize (s.gpr .r12).toNat * 2 ^ n % 2 ^ 64 = l4 at *
    generalize (s.gpr .r13).toNat * 2 ^ n % 2 ^ 64 = l5 at *
    generalize (s.gpr .r14).toNat * 2 ^ n % 2 ^ 64 = l6 at *
    generalize (s.gpr .r15).toNat * 2 ^ n % 2 ^ 64 = l7 at *
    generalize (s.gpr .rbx).toNat * 2 ^ n % 2 ^ 64 = l8 at *
    generalize (s.gpr .r8).toNat / 2 ^ (64 - n) = h0 at *
    generalize (s.gpr .r9).toNat / 2 ^ (64 - n) = h1 at *
    generalize (s.gpr .r10).toNat / 2 ^ (64 - n) = h2 at *
    generalize (s.gpr .r11).toNat / 2 ^ (64 - n) = h3 at *
    generalize (s.gpr .r12).toNat / 2 ^ (64 - n) = h4 at *
    generalize (s.gpr .r13).toNat / 2 ^ (64 - n) = h5 at *
    generalize (s.gpr .r14).toNat / 2 ^ (64 - n) = h6 at *
    generalize (s.gpr .r15).toNat / 2 ^ (64 - n) = h7 at *
    exact shl9 w0 w1 w2 w3 w4 w5 w6 w7 w8
  · exact (keepsIn (by decide) k₁).trans ((keepsIn (by decide) k₂).trans ((keepsIn (by decide) k₃).trans
      ((keepsIn (by decide) k₄).trans ((keepsIn (by decide) k₅).trans ((keepsIn (by decide) k₆).trans
      ((keepsIn (by decide) k₇).trans ((keepsIn (by decide) k₈).trans (keepsIn (by decide) k₉))))))))

/-! ## Complements -/

theorem xor_low {x k : Nat} (h : x < 2 ^ k) : x ^^^ (2 ^ k - 1) = 2 ^ k - 1 - x := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, show 2 ^ k - 1 - x = 2 ^ k - (x + 1) by omega,
    Nat.testBit_two_pow_sub_succ h]
  by_cases hi : i < k
  · simp [hi]
  · have : x < 2 ^ i := Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega))
    simp [hi, Nat.testBit_lt_two_pow this]

theorem xorImm_ok (s : State) (t : Reg) (i : BitVec 32) :
    WP isa (.block [.alu .xor t (.imm i)]) s fun s' =>
      s'.gpr t = s.gpr t ^^^ i.signExtend 64 ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem negStep {x V X k : Nat} (hx : x < 2 ^ 64) (h : V + X = 2 ^ k - 1) :
    2 ^ 64 - 1 - x + 2 ^ 64 * V + (x + 2 ^ 64 * X) = 2 ^ (k + 64) - 1 := by
  have := Nat.pow_add 2 k 64
  have := Nat.two_pow_pos k
  omega

/-- A word complemented. -/
theorem negW_ok {s : State} {base : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (t : Reg) {d : Nat}
    (hd : d + 8 ≤ 4096) :
    WP isa (.block [.mov t (.mem (sc d)), .alu .xor t (.imm (BitVec.ofInt 32 (-1)))]) s fun s' =>
      (s'.gpr t).toNat = 2 ^ 64 - 1 - (word s.mem base d).toNat ∧ Keeps [t] s s' := by
  rw [show ∀ x y : Instr, [x, y] = [x] ++ [y] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (movR_ok s t (sc_ok hZ hs hd)) fun s₁ ⟨r₁, _, _, k₁⟩ =>
    WP.mono (xorImm_ok s₁ t _) fun s₂ ⟨r₂, k₂⟩ => ⟨?_, k₁.trans k₂⟩
  rw [r₂, r₁, show (BitVec.ofInt 32 (-1)).signExtend 64 = BitVec.allOnes 64 by decide,
    BitVec.xor_allOnes, BitVec.toNat_not]

/-- The top word's nine bits complemented. -/
theorem negT_ok {s : State} {base : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (t : Reg) {d : Nat}
    (hd : d + 8 ≤ 4096) (h9 : (word s.mem base d).toNat < 512) :
    WP isa (.block [.mov t (.mem (sc d)), .alu .xor t (.imm 511)]) s fun s' =>
      (s'.gpr t).toNat = 511 - (word s.mem base d).toNat ∧ Keeps [t] s s' := by
  rw [show ∀ x y : Instr, [x, y] = [x] ++ [y] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (movR_ok s t (sc_ok hZ hs hd)) fun s₁ ⟨r₁, _, _, k₁⟩ =>
    WP.mono (xorImm_ok s₁ t _) fun s₂ ⟨r₂, k₂⟩ => ⟨?_, k₁.trans k₂⟩
  rw [r₂, r₁, show ((511 : BitVec 32).signExtend 64) = BitVec.ofNat 64 (2 ^ 9 - 1) by decide,
    BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide), xor_low (k := 9) h9]

/-- `N = p - [b]` for `[b]`'s top word below `2⁹`. -/
theorem negLoads_ok {s : State} {base : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) {b : Nat}
    (hb : b + 72 ≤ 4096) (h9 : (word s.mem base (b + 64)).toNat < 512) :
    WP isa (.block (negLoads CW b)) s fun s' =>
      regsVal s' CW + wordsVal s.mem base b 9 = 2 ^ 521 - 1 ∧ Keeps CW s s' := by
  simp only [negLoads, CW]
  rw [WP.block_append_iff]
  refine WP.mono (negW_ok hZ hs .r8 (d := b) (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (negW_ok hZ hs₁ .r9 (d := b + 8) (by omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [m₁] at e₂
  have m₂ : s₂.mem = s.mem := k₂.2.1.trans m₁
  rw [WP.block_append_iff]
  refine WP.mono (negW_ok hZ hs₂ .r10 (d := b + 8 + 8) (by omega)) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [m₂] at e₃
  have m₃ : s₃.mem = s.mem := k₃.2.1.trans m₂
  rw [WP.block_append_iff]
  refine WP.mono (negW_ok hZ hs₃ .r11 (d := b + 8 + 8 + 8) (by omega)) fun s₄ ⟨e₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [m₃] at e₄
  have m₄ : s₄.mem = s.mem := k₄.2.1.trans m₃
  rw [WP.block_append_iff]
  refine WP.mono (negW_ok hZ hs₄ .r12 (d := b + 8 + 8 + 8 + 8) (by omega)) fun s₅ ⟨e₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  rw [m₄] at e₅
  have m₅ : s₅.mem = s.mem := k₅.2.1.trans m₄
  rw [WP.block_append_iff]
  refine WP.mono (negW_ok hZ hs₅ .r13 (d := b + 8 + 8 + 8 + 8 + 8) (by omega)) fun s₆ ⟨e₆, k₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  rw [m₅] at e₆
  have m₆ : s₆.mem = s.mem := k₆.2.1.trans m₅
  rw [WP.block_append_iff]
  refine WP.mono (negW_ok hZ hs₆ .r14 (d := b + 8 + 8 + 8 + 8 + 8 + 8) (by omega)) fun s₇ ⟨e₇, k₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  rw [m₆] at e₇
  have m₇ : s₇.mem = s.mem := k₇.2.1.trans m₆
  rw [WP.block_append_iff]
  refine WP.mono (negW_ok hZ hs₇ .r15 (d := b + 8 + 8 + 8 + 8 + 8 + 8 + 8) (by omega)) fun s₈ ⟨e₈, k₈⟩ => ?_
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  rw [m₇] at e₈
  have m₈ : s₈.mem = s.mem := k₈.2.1.trans m₇
  refine WP.mono (negT_ok hZ hs₈ .rbx (d := b + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8) (by omega)
    (by rw [m₈, show b + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 = b + 64 by omega]; exact h9)) fun s₉ ⟨e₉, k₉⟩ => ⟨?_, ?_⟩
  · rw [show [Reg.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rbx] = CW from rfl, regsCW]
    have f_r8 : s₉.gpr .r8 = s₁.gpr .r8 := ((((((((k₉.1 .r8 (by decide)).trans (k₈.1 .r8 (by decide))).trans (k₇.1 .r8 (by decide))).trans (k₆.1 .r8 (by decide))).trans (k₅.1 .r8 (by decide))).trans (k₄.1 .r8 (by decide))).trans (k₃.1 .r8 (by decide))).trans (k₂.1 .r8 (by decide)))
    have f_r9 : s₉.gpr .r9 = s₂.gpr .r9 := (((((((k₉.1 .r9 (by decide)).trans (k₈.1 .r9 (by decide))).trans (k₇.1 .r9 (by decide))).trans (k₆.1 .r9 (by decide))).trans (k₅.1 .r9 (by decide))).trans (k₄.1 .r9 (by decide))).trans (k₃.1 .r9 (by decide)))
    have f_r10 : s₉.gpr .r10 = s₃.gpr .r10 := ((((((k₉.1 .r10 (by decide)).trans (k₈.1 .r10 (by decide))).trans (k₇.1 .r10 (by decide))).trans (k₆.1 .r10 (by decide))).trans (k₅.1 .r10 (by decide))).trans (k₄.1 .r10 (by decide)))
    have f_r11 : s₉.gpr .r11 = s₄.gpr .r11 := (((((k₉.1 .r11 (by decide)).trans (k₈.1 .r11 (by decide))).trans (k₇.1 .r11 (by decide))).trans (k₆.1 .r11 (by decide))).trans (k₅.1 .r11 (by decide)))
    have f_r12 : s₉.gpr .r12 = s₅.gpr .r12 := ((((k₉.1 .r12 (by decide)).trans (k₈.1 .r12 (by decide))).trans (k₇.1 .r12 (by decide))).trans (k₆.1 .r12 (by decide)))
    have f_r13 : s₉.gpr .r13 = s₆.gpr .r13 := (((k₉.1 .r13 (by decide)).trans (k₈.1 .r13 (by decide))).trans (k₇.1 .r13 (by decide)))
    have f_r14 : s₉.gpr .r14 = s₇.gpr .r14 := ((k₉.1 .r14 (by decide)).trans (k₈.1 .r14 (by decide)))
    have f_r15 : s₉.gpr .r15 = s₈.gpr .r15 := (k₉.1 .r15 (by decide))
    rw [m₈] at e₉
    rw [f_r8, f_r9, f_r10, f_r11, f_r12, f_r13, f_r14, f_r15, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉]
    simp only [wordsVal]
    have t := (negStep (Mont.word s.mem base (b)).isLt
      (negStep (Mont.word s.mem base (b + 8)).isLt
      (negStep (Mont.word s.mem base (b + 8 + 8)).isLt
      (negStep (Mont.word s.mem base (b + 8 + 8 + 8)).isLt
      (negStep (Mont.word s.mem base (b + 8 + 8 + 8 + 8)).isLt
      (negStep (Mont.word s.mem base (b + 8 + 8 + 8 + 8 + 8)).isLt
      (negStep (Mont.word s.mem base (b + 8 + 8 + 8 + 8 + 8 + 8)).isLt
      (negStep (Mont.word s.mem base (b + 8 + 8 + 8 + 8 + 8 + 8 + 8)).isLt
      (show 511 - (Mont.word s.mem base (b + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)).toNat + ((Mont.word s.mem base (b + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)).toNat + 2 ^ 64 * 0) =
        2 ^ 9 - 1 by rw [show b + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 = b + 64 by omega]; omega)))))))))
    rw [show 9 + 64 + 64 + 64 + 64 + 64 + 64 + 64 + 64 = 521 from rfl] at t
    exact t
  · exact (keepsIn (by decide) k₁).trans ((keepsIn (by decide) k₂).trans ((keepsIn (by decide) k₃).trans
      ((keepsIn (by decide) k₄).trans ((keepsIn (by decide) k₅).trans ((keepsIn (by decide) k₆).trans
      ((keepsIn (by decide) k₇).trans ((keepsIn (by decide) k₈).trans (keepsIn (by decide) k₉))))))))

/-! ## Products by `C` -/

/-- `maddStepsS`: `maddStepsM` from the working space. -/
theorem maddStepsS_ok (hZ : 4096 ≤ Z) : ∀ (k : Nat) (ts : List Reg) {s : State} {base : Addr}
    {d : Nat} {c o : Bool}, Scr s base Z → d + 8 * k ≤ 4096 →
    k + 1 ≤ ts.length → FreshX ts → s.cf = some c → s.of = some o →
    WP isa (.block (maddStepsS k ts d)) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      regsVal s' (ts.take (k + 1)) + 2 ^ (64 * k) * c'.toNat + 2 ^ (64 * (k + 1)) * o'.toNat =
        regsVal s (ts.take (k + 1)) + c.toNat + 2 ^ 64 * o.toNat +
          (s.gpr .rdx).toNat * wordsVal s.mem base d k ∧
      Keeps (.rcx :: .rax :: ts.take (k + 1)) s s'
  | 0, ts, s, _, _, c, o, _, _, _, _, hc, ho => by
    show WP isa (.block []) s _
    exact WP.block_nil ⟨c, o, hc, ho, by simp [wordsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | _ + 1, [], _, _, _, _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | _ + 1, [_], _, _, _, _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | k + 1, x :: y :: rest, s, base, d, c, o, hs, hd, hl, hf, hc, ho => by
    obtain ⟨hxn, hxa, hxc, hxd, hxi⟩ := hf.head
    obtain ⟨hyn, hya, hyc, hyd, hyi⟩ := hf.tail.head
    have hxy : x ≠ y := fun h => hxn (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons] at hl
    rw [maddStepsS, WP.block_append_iff]
    refine WP.mono (maddM_ok s (v := word s.mem base d) (sc_ok hZ hs (d := d) (by omega))
      (fun _ h => nomatch h) hc ho
      hxc hxa hyc hya hxy) fun s₁ ⟨c₁, o₁, cf₁, of₁, e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, by decide, Ne.symm hxi, Ne.symm hyi⟩)
    refine WP.mono (maddStepsS_ok hZ k (y :: rest) hs₁ (d := d + 8) (by omega)
      (by simp only [List.length_cons]; omega) hf.tail cf₁ of₁) fun s₂ ⟨c', o', cf₂, of₂, e₂, k₂⟩ =>
      ⟨c', o', cf₂, of₂, ?_, ?_⟩
    · have hdx : s₁.gpr .rdx = s.gpr .rdx := k₁.1 .rdx (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, by decide, Ne.symm hxd, Ne.symm hyd⟩)
      have hx₂ : s₂.gpr x = s₁.gpr x := k₂.1 x (by
        simp only [List.mem_cons, not_or]
        exact ⟨hxc, hxa, fun h => hxn (List.mem_of_mem_take h)⟩)
      have hR : regsVal s₁ (rest.take k) = regsVal s (rest.take k) := regsVal_congr fun q hq => k₁.1 q (by
        have hq' := List.mem_of_mem_take hq
        have := hf.2 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq'))
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨this.2.1, this.1, fun h => hxn (h ▸ List.mem_cons_of_mem _ hq'),
          fun h => hyn (h ▸ hq')⟩)
      rw [k₁.2.1, hdx] at e₂
      simp only [List.take_succ_cons, regsVal, hR] at e₂ ⊢
      simp only [wordsVal]
      rw [hx₂]
      rw [pow64_succ (k + 1), pow64_succ k] at *
      simp only [Nat.mul_assoc] at e₂ ⊢
      rw [Nat.mul_add (s.gpr .rdx).toNat, Nat.mul_left_comm (s.gpr .rdx).toNat (2 ^ 64)]
      omega_arith
    · simp only [List.take_succ_cons] at k₂ ⊢
      exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

/-- `x += lo (rdx v)` with the carry CF. -/
theorem mulxAdcx_ok (s : State) {x : Reg} {src : Src} {v : BitVec 64} {c : Bool}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hc : s.cf = some c)
    (hxh : x ≠ .rcx) (hxl : x ≠ .rax) :
    WP isa (.block [.mulx .rcx .rax src, .adcx x (.reg .rax)]) s fun s' =>
      ∃ c', s'.cf = some c' ∧
        (s'.gpr x).toNat + 2 ^ 64 * c'.toNat = (s.gpr x).toNat + (s.gpr .rdx).toNat * v.toNat % 2 ^ 64 + c.toNat ∧
        Keeps [.rcx, .rax, x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, execMulx_eq hsrc himm, runStep_some]
  simp only [runStep_some, runBlock_nil, execAdcx, readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hxh,
    RegUpd.gpr_setReg_of_ne _ _ hxl, RegUpd.gpr_setReg_of_ne _ _ (by decide : Reg.rax ≠ .rcx),
    RegUpd.cf_setReg, hc, Option.some.injEq, exists_eq_left']
  refine ⟨_, (by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have e1 := adc_carry (s.gpr x) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat)) c
    rw [BitVec.toNat_ofNat] at e1 ⊢
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2.2, RegUpd.gpr_setFlags, RegUpd.gpr_setReg_of_ne _ _ hr.1,
      RegUpd.gpr_setReg_of_ne _ _ hr.2.1]

theorem movImm32_ok (s : State) (t : Reg) {C : Nat} (hC : C < 2 ^ 32) :
    WP isa (.block [.mov32 t (.imm (BitVec.ofNat 32 C))]) s fun s' =>
      (s'.gpr t).toNat = C ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, of_setReg, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hC, Nat.mod_eq_of_lt (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

theorem maddStepsS8_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} {a : Nat} {c o : Bool} (hs : Scr s base Z)
    (ha : a + 64 ≤ 4096) (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (maddStepsS 8 CW a)) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      regsVal s' CW + (2 ^ 64) ^ 8 * c'.toNat + (2 ^ 64) ^ 9 * o'.toNat =
        regsVal s CW + c.toNat + 2 ^ 64 * o.toNat + (s.gpr .rdx).toNat * wordsVal s.mem base a 8 ∧
      Keeps (.rcx :: .rax :: CW) s s' :=
  WP.mono (maddStepsS_ok hZ 8 CW hs (d := a) (by omega) (by decide) ⟨by decide, by decide⟩ hc ho)
    fun _ ⟨c', o', h₁, h₂, e, k⟩ => ⟨c', o', h₁, h₂, by
      rw [p8, show 8 + 1 = 9 from rfl, p9, show CW.take 9 = CW from rfl] at e; exact e, k⟩

theorem mulC_arith {L R3 R4 N X Y c3 o3 c4 f0 f1 : Nat} (hl : L < (2 ^ 64) ^ 8) (h4 : R4 < 2 ^ 64)
    (h0 : f0 = 0) (h1 : f1 = 0)
    (e3 : L + (2 ^ 64) ^ 8 * R3 + (2 ^ 64) ^ 8 * c3 + (2 ^ 64) ^ 9 * o3 = N + f0 + 2 ^ 64 * f1 + X)
    (e4 : R4 + 2 ^ 64 * c4 = R3 + Y + c3) :
    L + (2 ^ 64) ^ 8 * R4 = (N + (X + (2 ^ 64) ^ 8 * Y)) % 2 ^ 576 := by
  omega

theorem regsCW8 (s : State) :
    regsVal s CW = regsVal s (CW.take 8) + (2 ^ 64) ^ 8 * (s.gpr .rbx).toNat := by
  have h := regsVal_append s (CW.take 8) (CW.drop 8)
  rw [List.take_append_drop] at h
  rw [h, show (CW.take 8).length = 8 from rfl, show CW.drop 8 = [.rbx] from rfl, p8]
  simp only [regsVal, Nat.mul_zero, Nat.add_zero]

/-- `N += C [a]` for `C [a]`'s top word below `2⁶⁴`, modulo `2⁵⁷⁶`. -/
theorem addMulC_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {C a : Nat}
    (hC : C < 2 ^ 32) (ha : a + 72 ≤ 4096) (h8 : C * (word s.mem base (a + 64)).toNat < 2 ^ 64) :
    WP isa (.block (addMulC C a)) s fun s' =>
      regsVal s' CW = (regsVal s CW + C * wordsVal s.mem base a 9) % 2 ^ 576 ∧
      Keeps (.rcx :: .rax :: .rdx :: CW) s s' := by
  rw [addMulC, List.append_assoc, show ∀ x y : Instr, [x, y] = [x] ++ [y] from fun _ _ => rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (xorZ_ok s .rax) fun s₁ ⟨_, cf₁, of₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movImm32_ok s₁ .rdx hC) fun s₂ ⟨d₂, cf₂, of₂, k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (maddStepsS8_ok hZ hs₂ (a := a) (by omega)
    (cf₂.trans cf₁) (of₂.trans of₁)) fun s₃ ⟨c₃, o₃, cf₃, _, e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (mulxAdcx_ok s₃ (x := .rbx) (sc_ok hZ hs₃ (d := a + 64) (by omega)) (fun _ h => nomatch h)
    cf₃ (by decide) (by decide)) fun s₄ ⟨c₄, _, e₄, k₄⟩ => ⟨?_, ?_⟩
  · have m₃ : s₃.mem = s.mem := k₃.2.1.trans (k₂.2.1.trans k₁.2.1)
    have g₃ : s₃.gpr .rdx = s₂.gpr .rdx := k₃.1 _ (by decide)
    have cwr : ∀ q ∈ CW, q ≠ .rax ∧ q ≠ .rdx := by decide
    have cw8 : ∀ q ∈ CW.take 8, q ∉ [Reg.rcx, .rax, .rbx] := by decide
    have hN : regsVal s₂ CW = regsVal s CW :=
      regsVal_congr fun q hq => (k₂.1 q (by rw [List.mem_singleton]; exact (cwr q hq).2)).trans
        (k₁.1 q (by rw [List.mem_singleton]; exact (cwr q hq).1))
    have hL : regsVal s₄ (CW.take 8) = regsVal s₃ (CW.take 8) :=
      regsVal_congr fun q hq => k₄.1 q (cw8 q hq)
    rw [hN] at e₃
    rw [regsCW8 s₃] at e₃
    rw [d₂] at e₃
    rw [k₂.2.1, k₁.2.1] at e₃
    rw [g₃, d₂, m₃, Nat.mod_eq_of_lt h8] at e₄
    rw [regsCW8 s₄, hL, wordsVal_succ_last, Nat.mul_add, Nat.mul_left_comm C ((2 ^ 64) ^ 8)]
    have hl := regsVal_lt s₃ (CW.take 8)
    have h4 := (s₄.gpr .rbx).isLt
    rw [show (CW.take 8).length = 8 from rfl, p8] at hl
    rw [show a + 8 * 8 = a + 64 from rfl]
    exact mulC_arith hl h4 rfl rfl e₃ e₄
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans ((k₃.mono (by decide)).trans
      (k₄.mono (by decide))))

/-! ## `N += p - [b]` -/

theorem chainSbbCW_ok {s : State} {base : Addr} (hs : Scr s base Z) {b : Nat} {c : Bool} (hc : s.cf = some c)
    (hb : b + 72 ≤ Z) :
    WP isa (.block (chain .sbb .sbb CW b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' CW + wordsVal s.mem base b 9 + c.toNat = regsVal s CW + (2 ^ 64) ^ 9 * c'.toNat ∧
      Keeps CW s s' :=
  WP.mono (chainSbb_ok CW hs hc (b := b) (by rw [show CW.length = 9 from rfl]; omega) ⟨by decide, by decide⟩)
    fun _ ⟨c', h, e, k⟩ => ⟨c', h, by rw [show CW.length = 9 from rfl, p9] at e; exact e, k⟩

theorem addImm_ok (s : State) (t : Reg) (i : BitVec 32) :
    WP isa (.block [.alu .add t (.imm i)]) s fun s' =>
      (s'.gpr t).toNat = ((s.gpr t).toNat + (i.signExtend 64).toNat) % 2 ^ 64 ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨BitVec.toNat_add _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem addNeg_arith {L R3 R4 N B c f : Nat} (hl : L < (2 ^ 64) ^ 8) (hNB : B < N + 2 ^ 521)
    (hf : f = 1) (e3 : L + (2 ^ 64) ^ 8 * R3 + B + f = N + (2 ^ 64) ^ 9 * c) (e4 : R4 = (R3 + 512) % 2 ^ 64) :
    L + (2 ^ 64) ^ 8 * R4 = (N + 2 ^ 521 - 1 - B) % 2 ^ 576 := by
  omega

/-- `N += p - [b]`, modulo `2⁵⁷⁶`. -/
theorem addNeg_ok {s : State} {base : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) {b : Nat} (hb : b + 72 ≤ 4096)
    (hNB : wordsVal s.mem base b 9 < regsVal s CW + 2 ^ 521) :
    WP isa (.block (addNeg b)) s fun s' =>
      regsVal s' CW = (regsVal s CW + 2 ^ 521 - 1 - wordsVal s.mem base b 9) % 2 ^ 576 ∧
      Keeps (.rax :: CW) s s' := by
  rw [addNeg, List.append_assoc, show ∀ x y : Instr, [x, y] = [x] ++ [y] from fun _ _ => rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (xorZ_ok s .rax) fun s₁ ⟨z₁, _, _, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmpM1_ok s₁ .rax z₁) fun s₂ ⟨cf₂, _, k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chainSbbCW_ok hs₂ cf₂ (b := b) (by omega)) fun s₃ ⟨c₃, _, e₃, k₃⟩ => ?_
  refine WP.mono (addImm_ok s₃ .rbx 512) fun s₄ ⟨e₄, k₄⟩ => ⟨?_, ?_⟩
  · have cw8 : ∀ q ∈ CW.take 8, q ∉ [Reg.rbx] := by decide
    have hN : regsVal s₂ CW = regsVal s CW :=
      regsVal_congr fun q hq => (k₂.1 q (by simp)).trans (k₁.1 q (by
        rw [List.mem_singleton]; rintro rfl; exact absurd hq (by decide)))
    have hL : regsVal s₄ (CW.take 8) = regsVal s₃ (CW.take 8) :=
      regsVal_congr fun q hq => k₄.1 q (cw8 q hq)
    rw [hN, k₂.2.1, k₁.2.1, regsCW8 s₃] at e₃
    rw [show ((512 : BitVec 32).signExtend 64).toNat = 512 by decide] at e₄
    have hl := regsVal_lt s₃ (CW.take 8)
    rw [show (CW.take 8).length = 8 from rfl, p8] at hl
    rw [regsCW8 s₄, hL]
    exact addNeg_arith (N := regsVal s CW) (B := wordsVal s.mem base b 9) hl hNB rfl e₃ e₄
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans ((k₃.mono (by decide)).trans
      (k₄.mono (by decide))))

/-! ## The ending (`cmsTail`) -/

theorem addS_ok (s : State) (x : Reg) {src : Src} {v : BitVec 64} (hsrc : readSrc s src = some v) :
    WP isa (.block [.alu .add x src]) s fun s' => ∃ c', s'.cf = some c' ∧
      (s'.gpr x).toNat + 2 ^ 64 * c'.toNat = (s.gpr x).toNat + v.toNat ∧ Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, hsrc, Option.bind_some,
    RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq, exists_eq_left']
  refine ⟨add_carry _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem andR_ok (s : State) (x r : Reg) :
    WP isa (.block [.alu .and x (.reg r)]) s fun s' =>
      s'.gpr x = s.gpr x &&& s.gpr r ∧ Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem foldl_and_congr {f g : Reg → BitVec 64} : ∀ {rs : List Reg}, (∀ q ∈ rs, f q = g q) → ∀ a,
    rs.foldl (fun a r => a &&& f r) a = rs.foldl (fun a r => a &&& g r) a
  | [], _, _ => rfl
  | r :: rs, h, a => by
    rw [List.foldl_cons, List.foldl_cons, h r (List.mem_cons_self ..)]
    exact foldl_and_congr (fun q hq => h q (List.mem_cons_of_mem _ hq)) _

/-- `x &&&` the registers `rs` in turn. -/
theorem andChain_ok (x : Reg) : ∀ (rs : List Reg) (s : State), x ∉ rs →
    WP isa (.block (rs.map fun r => .alu .and x (.reg r))) s fun s' =>
      s'.gpr x = rs.foldl (fun a r => a &&& s.gpr r) (s.gpr x) ∧ Keeps [x] s s'
  | [], s, _ => WP.block_nil ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | r :: rs, s, hx => by
    rw [List.map_cons, cons_split, WP.block_append_iff]
    have hxr : x ≠ r := fun h => hx (h ▸ List.mem_cons_self ..)
    have hxs : x ∉ rs := fun h => hx (List.mem_cons_of_mem _ h)
    refine WP.mono (andR_ok s x r) fun s₁ ⟨e₁, k₁⟩ =>
      WP.mono (andChain_ok x rs s₁ hxs) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, k₁.trans k₂⟩
    have hR : ∀ q ∈ rs, s₁.gpr q = s.gpr q := fun q hq => k₁.1 q (by
      rw [List.mem_singleton]; rintro rfl; exact hxs hq)
    rw [e₂, e₁, List.foldl_cons]
    exact foldl_and_congr hR _

theorem foldl_and_allOnes {s : State} : ∀ (rs : List Reg) (a : BitVec 64),
    rs.foldl (fun a r => a &&& s.gpr r) a = BitVec.allOnes 64 ↔
      a = BitVec.allOnes 64 ∧ ∀ r ∈ rs, s.gpr r = BitVec.allOnes 64
  | [], a => by simp
  | r :: rs, a => by
    rw [List.foldl_cons, foldl_and_allOnes rs, BitVec.and_eq_allOnes_iff]
    simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

theorem regsVal_max {s : State} : ∀ (ts : List Reg),
    regsVal s ts = 2 ^ (64 * ts.length) - 1 ↔ ∀ t ∈ ts, s.gpr t = BitVec.allOnes 64
  | [] => by simp [regsVal]
  | t :: ts => by
    rw [regsVal, List.length_cons, pow64_succ]
    have := regsVal_lt s ts
    have := (s.gpr t).isLt
    have := Nat.two_pow_pos (64 * ts.length)
    have ih := regsVal_max (s := s) ts
    simp only [List.mem_cons, forall_eq_or_imp, ← BitVec.toNat_inj, BitVec.toNat_allOnes] at ih ⊢
    constructor
    · intro h
      have h1 : (s.gpr t).toNat = 2 ^ 64 - 1 := by omega
      exact ⟨h1, ih.mp (by omega)⟩
    · rintro ⟨h1, h2⟩
      have := ih.mpr h2
      omega

/-- The top word's bits from 9 set. -/
theorem or_high (x : Nat) (hx : x < 2 ^ 64) : x ||| (2 ^ 64 - 512) = x % 512 + (2 ^ 64 - 512) := by
  have e : 2 ^ 64 - 512 = 2 ^ 9 * (2 ^ 55 - 1) + 0 := by decide
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, show x % 512 + (2 ^ 64 - 512) = 2 ^ 9 * (2 ^ 55 - 1) + x % 2 ^ 9 by omega, e,
    Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos 9), Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos 9)),
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 9
  · rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · by_cases h64 : i < 64
    · simp [hi, show i - 9 < 55 by omega]
    · have : x < 2 ^ i := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))
      simp [hi, Nat.testBit_lt_two_pow this, show ¬ i - 9 < 55 by omega]

theorem orHigh_ok (s : State) (t : Reg) :
    WP isa (.block [.alu .or t (.imm (BitVec.ofInt 32 (-512)))]) s fun s' =>
      (s'.gpr t).toNat = (s.gpr t).toNat % 512 + (2 ^ 64 - 512) ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [show (BitVec.ofInt 32 (-512)).signExtend 64 = BitVec.ofNat 64 (2 ^ 64 - 512) by decide,
      BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide), or_high _ (s.gpr t).isLt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `adcSt ts o`: the carry `c` added along `ts` (`rcx = 0`), each word stored at `[o + 8k]`. -/
theorem adcSt_ok (hZ : 4096 ≤ Z) : ∀ (ts : List Reg) {s : State} {base : Addr} {o : Nat} {c : Bool},
    Scr s base Z → LinRegs ts → .rcx ∉ ts → s.gpr .rcx = 0 → o + 8 * ts.length ≤ 4096 → s.cf = some c →
    WP isa (.block (adcSt ts o)) s fun s' => ∃ c', s'.cf = some c' ∧
      wordsVal s'.mem base o ts.length + 2 ^ (64 * ts.length) * c'.toNat = regsVal s ts + c.toNat ∧
      KeepRegs ts s s' ∧ Outside base o (8 * ts.length) s.mem s'.mem
  | [], s, _, _, c, _, _, _, _, _, hc => WP.block_nil ⟨c, hc, by simp [regsVal, wordsVal],
      ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | t :: ts, s, base, o, c, hs, hr, hrc, h0, ho, hc => by
    have hnw := hs.nowrap
    simp only [List.length_cons] at ho
    obtain ⟨htn, htr⟩ := List.nodup_cons.mp hr.1
    have ht := hr.2 t (List.mem_cons_self ..)
    have htc : t ≠ .rcx := fun h => hrc (h ▸ List.mem_cons_self ..)
    rw [adcSt, pair_append, WP.block_append_iff]
    refine WP.mono (adcS_ok s t (src := .reg .rcx) rfl hc) fun s₁ ⟨c₁, cf₁, e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simpa using ht.symm)
    rw [WP.block_append_iff]
    refine WP.mono (storeX_ok hs₁ t (d := o) (by omega)) fun s₂ ⟨m₂, g₂, cf₂, _, rd₂, wr₂⟩ => ?_
    have hs₂ : Scr s₂ base Z := ⟨by rw [g₂]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hnw⟩
    have O₂ : Outside base o 8 s.mem s₂.mem := by rw [m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega)
    have h0₂ : s₂.gpr .rcx = 0 := by rw [g₂, k₁.1 .rcx (by simpa using Ne.symm htc)]; exact h0
    refine WP.mono (adcSt_ok hZ ts hs₂ hr.tail (fun h => hrc (List.mem_cons_of_mem _ h)) h0₂ (o := o + 8)
      (by omega) (cf₂.trans cf₁)) fun s₃ ⟨c₃, cf₃, e₃, k₃, O₃⟩ => ⟨c₃, cf₃, ?_, ?_, ?_⟩
    · have hw : word s₃.mem base o = s₁.gpr t := by
        rw [O₃.word (by omega) (by omega), m₂, word_writeW_self]
      have hR : regsVal s₂ ts = regsVal s ts := regsVal_congr fun q hq => by
        rw [g₂, k₁.1 q (by simp only [List.mem_singleton]; rintro rfl; exact htn hq)]
      rw [hR] at e₃
      rw [h0, show (0 : BitVec 64).toNat = 0 from rfl] at e₁
      simp only [regsVal, wordsVal, List.length_cons, hw]
      rw [pow64_succ]
      rw [show 2 ^ 64 * 2 ^ (64 * ts.length) * c₃.toNat = 2 ^ 64 * (2 ^ (64 * ts.length) * c₃.toNat) by
        rw [Nat.mul_assoc]]
      omega
    · exact ⟨fun r hr => by
        simp only [List.mem_cons, not_or] at hr
        rw [k₃.gpr r hr.2, g₂, k₁.1 r (by simpa using hr.1)],
        by rw [k₃.rd, rd₂, k₁.2.2.1], by rw [k₃.wr, wr₂, k₁.2.2.2]⟩
    · simp only [List.length_cons]
      rw [show 8 * (ts.length + 1) = 8 + 8 * ts.length by omega]
      exact (O₂.mono (Nat.le_refl _) (by omega)).trans (O₃.mono (by omega) (by omega))

theorem tail_c2 {m w0 M t h A7 c0 c1 c2 x0 x1 x2 : Nat}
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hw0 : w0 < 2 ^ 64) (hM : M < (2 ^ 64) ^ 7) (ht : t < 512)
    (hh : h < 2 ^ 55) (hA : A7 = 2 ^ 64 - 1 ↔ M = (2 ^ 64) ^ 7 - 1) (hA7 : A7 < 2 ^ 64)
    (hx0 : x0 < 2 ^ 64) (hx1 : x1 < 2 ^ 64) (hx2 : x2 < 2 ^ 64)
    (e0 : x0 + 2 ^ 64 * c0 = h + 1 + w0) (e1 : x1 + 2 ^ 64 * c1 = A7 + c0)
    (e2 : x2 + 2 ^ 64 * c2 = t + (2 ^ 64 - 512) + c1) :
    (c2 = 1 ↔ m ≤ w0 + 2 ^ 64 * M + (2 ^ 64) ^ 8 * t + h) ∧ c2 ≤ 1 := by
  have hc0 : c0 ≤ 1 := by omega
  have hc1 : c1 ≤ 1 := by omega
  by_cases hmm : M = (2 ^ 64) ^ 7 - 1
  · have := hA.mpr hmm
    subst hmm
    omega
  · have : A7 ≠ 2 ^ 64 - 1 := fun h => hmm (hA.mp h)
    have : M + 1 ≤ (2 ^ 64) ^ 7 - 1 := by omega
    omega

theorem tail_val {m L h c2 d0 d7 d8 o0 O7 rb w0 M t : Nat}
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hL : L = w0 + 2 ^ 64 * M + (2 ^ 64) ^ 8 * t)
    (hw0 : w0 < 2 ^ 64) (hM : M < (2 ^ 64) ^ 7) (ht : t < 512) (hh : h < 2 ^ 55)
    (hc : c2 = 1 ↔ m ≤ L + h) (hc2 : c2 ≤ 1)
    (e3 : o0 + 2 ^ 64 * d0 = w0 + h + c2) (ho0 : o0 < 2 ^ 64)
    (e4 : O7 + (2 ^ 64) ^ 7 * d7 = M + d0) (hO7 : O7 < (2 ^ 64) ^ 7)
    (e5 : rb + 2 ^ 64 * d8 = t + (2 ^ 64 - 512) + d7) (hrb : rb < 2 ^ 64) :
    o0 + 2 ^ 64 * O7 + (2 ^ 64) ^ 8 * (rb % 512) = (L + h) % m := by
  have hd0 : d0 ≤ 1 := by omega
  have hd7 : d7 ≤ 1 := by omega
  have hsum : o0 + 2 ^ 64 * O7 + (2 ^ 64) ^ 8 * rb + (2 ^ 64) ^ 9 * d8 + (m + 1) =
      L + h + c2 + (2 ^ 64) ^ 9 := by
    subst hL; omega
  have hLt : L < m + 1 := by subst hL; omega
  have hlow : o0 + 2 ^ 64 * O7 < (2 ^ 64) ^ 8 := by omega
  by_cases h2 : c2 = 1
  · have hle := hc.mp h2
    subst h2
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (show L + h - m < m by omega)]
    have hd8 : d8 = 1 := by omega
    subst hd8
    have hrb' : rb < 512 := by omega
    rw [Nat.mod_eq_of_lt hrb']
    omega
  · have hlt : L + h < m := Nat.lt_of_not_le fun h' => h2 (hc.mpr h')
    have : c2 = 0 := by omega
    subst this
    rw [Nat.mod_eq_of_lt hlt]
    have hd8 : d8 = 0 := by omega
    subst hd8
    have hq : rb = (2 ^ 64 - 512) + (L + h) / (2 ^ 64) ^ 8 := by omega
    rw [hq]
    omega

theorem tail_split {m a b w : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8) :
    a + 2 ^ 64 * b + (2 ^ 64) ^ 8 * w = (a + 2 ^ 64 * b + (2 ^ 64) ^ 8 * (w % 512) + w / 512) + m * (w / 512) := by
  obtain rfl : m = 512 * (2 ^ 64) ^ 8 - 1 := by omega
  omega

theorem tail_dist (a b c : Nat) : a + 2 ^ 64 * (b + (2 ^ 64) ^ 7 * c) = a + 2 ^ 64 * b + (2 ^ 64) ^ 8 * c := by
  omega

/-- The words `r9 … r15`. -/
def CM : List Reg := [.r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem regsCW_M (s : State) :
    regsVal s CW = (s.gpr .r8).toNat + 2 ^ 64 * regsVal s CM + (2 ^ 64) ^ 8 * (s.gpr .rbx).toNat := by
  have h := regsVal_append s CM [.rbx]
  rw [show CM.length = 7 from rfl] at h
  rw [show CW = .r8 :: (CM ++ [.rbx]) from rfl, regsVal, h]
  simp only [regsVal, Nat.mul_zero, Nat.add_zero, Nat.mul_add, Nat.pow_mul, ← Nat.mul_assoc, ← Nat.pow_succ']
  omega

/-- `cmsCarry`: CF is whether `L + h ≥ p` (`L` the low 521 bits of `N`, `h` the others). -/
theorem cmsCarry_ok (s : State) {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8) :
    WP isa (.block cmsCarry) s fun s' => ∃ c2 : Bool, s'.cf = some c2 ∧
      (c2.toNat = 1 ↔ m ≤ (s.gpr .r8).toNat + 2 ^ 64 * regsVal s CM + (2 ^ 64) ^ 8 * ((s.gpr .rbx).toNat % 512) +
        (s.gpr .rbx).toNat / 512) ∧
      s'.gpr .r8 = s.gpr .r8 ∧ (s'.gpr .rdx).toNat = (s.gpr .rbx).toNat / 512 ∧
      (s'.gpr .rbx).toNat = (s.gpr .rbx).toNat % 512 + (2 ^ 64 - 512) ∧ s'.gpr .rcx = 0 ∧
      Keeps [.rax, .rdx, .rbx, .rcx] s s' := by
  rw [cmsCarry]
  simp only [List.cons_append, List.nil_append]
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (movR_ok s .rax (src := .reg .r9) rfl) fun s₁ ⟨a₁, _, _, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (andChain_ok .rax _ s₁ (by decide)) fun s₂ ⟨a₂, k₂⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (movR_ok s₂ .rdx (src := .reg .rbx) rfl) fun s₃ ⟨d₃, _, _, k₃⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (shrS_ok s₃ .rdx (n := 9) (by decide)) fun s₄ ⟨d₄, k₄⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (orHigh_ok s₄ .rbx) fun s₅ ⟨b₅, k₅⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (movR_ok s₅ .rcx (src := .reg .rdx) rfl) fun s₆ ⟨c₆, _, _, k₆⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (addImm_ok s₆ .rcx 1) fun s₇ ⟨c₇, k₇⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (addS_ok s₇ .rcx (src := .reg .r8) rfl) fun s₈ ⟨q₈, cf₈, e₈, k₈⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (movImm32_ok s₈ .rcx (C := 0) (by decide)) fun s₉ ⟨c₉, cf₉, _, k₉⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (adcS_ok s₉ .rax (src := .reg .rcx) rfl (cf₉.trans cf₈)) fun s₁₀ ⟨q₁₀, cf₁₀, e₁₀, k₁₀⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (movR_ok s₁₀ .rax (src := .reg .rbx) rfl) fun s₁₁ ⟨a₁₁, cf₁₁, _, k₁₁⟩ => ?_
  refine WP.mono (adcS_ok s₁₁ .rax (src := .reg .rcx) rfl (cf₁₁.trans cf₁₀)) fun s₁₂ ⟨q₁₂, cf₁₂, e₁₂, k₁₂⟩ =>
    ⟨q₁₂, cf₁₂, ?_⟩
  have hA7 : s₂.gpr .rax = [Reg.r10, .r11, .r12, .r13, .r14, .r15].foldl (fun a r => a &&& s.gpr r)
      (s.gpr .r9) := by
    have mem : ∀ q ∈ [Reg.r10, .r11, .r12, .r13, .r14, .r15], q ∉ [Reg.rax] := by decide
    rw [a₂, a₁]; exact foldl_and_congr (fun q hq => k₁.1 q (mem q hq)) _
  have hA : (s₂.gpr .rax).toNat = 2 ^ 64 - 1 ↔ regsVal s CM = (2 ^ 64) ^ 7 - 1 := by
    have h1 := regsVal_max (s := s) CM
    rw [show CM.length = 7 from rfl, p7] at h1
    rw [h1, show (2 : Nat) ^ 64 - 1 = (BitVec.allOnes 64).toNat from rfl, BitVec.toNat_inj, hA7,
      foldl_and_allOnes]
    simp only [CM, List.mem_cons, forall_eq_or_imp, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  have r8₇ : s₇.gpr .r8 = s.gpr .r8 := by
    rw [k₇.1 _ (by decide), k₆.1 _ (by decide), k₅.1 _ (by decide), k₄.1 _ (by decide), k₃.1 _ (by decide),
      k₂.1 _ (by decide), k₁.1 _ (by decide)]
  have rcx₇ : (s₇.gpr .rcx).toNat = (s.gpr .rbx).toNat / 512 + 1 := by
    rw [c₇, c₆, k₅.1 _ (by decide), d₄, d₃, k₂.1 _ (by decide), k₁.1 _ (by decide),
      show ((1 : BitVec 32).signExtend 64).toNat = 1 by decide]
    have := (s.gpr .rbx).isLt
    omega
  have rax₉ : s₉.gpr .rax = s₂.gpr .rax := by
    rw [k₉.1 _ (by decide), k₈.1 _ (by decide), k₇.1 _ (by decide), k₆.1 _ (by decide), k₅.1 _ (by decide),
      k₄.1 _ (by decide), k₃.1 _ (by decide)]
  have rbx₅ : (s₅.gpr .rbx).toNat = (s.gpr .rbx).toNat % 512 + (2 ^ 64 - 512) := by
    rw [b₅, k₄.1 _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide), k₁.1 _ (by decide)]
  have rax₁₁ : s₁₁.gpr .rax = s₅.gpr .rbx := by
    rw [a₁₁, k₁₀.1 _ (by decide), k₉.1 _ (by decide), k₈.1 _ (by decide), k₇.1 _ (by decide), k₆.1 _ (by decide)]
  have rcx₁₁ : s₁₁.gpr .rcx = 0 := by
    rw [k₁₁.1 _ (by decide), k₁₀.1 _ (by decide)]; exact BitVec.eq_of_toNat_eq c₉
  rw [rax₉, c₉] at e₁₀
  rw [rcx₇, r8₇] at e₈
  rw [rax₁₁, rcx₁₁, rbx₅, show (0 : BitVec 64).toNat = 0 from rfl] at e₁₂
  have hMl := regsVal_lt s CM
  rw [show CM.length = 7 from rfl, p7] at hMl
  have hw8 := (s.gpr .rbx).isLt
  have ⟨hc, _⟩ := tail_c2 (m := m) (w0 := (s.gpr .r8).toNat) (M := regsVal s CM)
    (t := (s.gpr .rbx).toNat % 512) (h := (s.gpr .rbx).toNat / 512) (A7 := (s₂.gpr .rax).toNat)
    hm (s.gpr .r8).isLt hMl (Nat.mod_lt _ (by decide)) (by omega) hA (s₂.gpr .rax).isLt (s₈.gpr .rcx).isLt
    (s₁₀.gpr .rax).isLt (s₁₂.gpr .rax).isLt e₈ e₁₀ e₁₂
  refine ⟨hc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₁₂.1 _ (by decide), k₁₁.1 _ (by decide), k₁₀.1 _ (by decide), k₉.1 _ (by decide), k₈.1 _ (by decide), r8₇]
  · rw [k₁₂.1 _ (by decide), k₁₁.1 _ (by decide), k₁₀.1 _ (by decide), k₉.1 _ (by decide), k₈.1 _ (by decide),
      k₇.1 _ (by decide), k₆.1 _ (by decide), k₅.1 _ (by decide), d₄, d₃, k₂.1 _ (by decide), k₁.1 _ (by decide)]
  · rw [k₁₂.1 _ (by decide), k₁₁.1 _ (by decide), k₁₀.1 _ (by decide), k₉.1 _ (by decide), k₈.1 _ (by decide),
      k₇.1 _ (by decide), k₆.1 _ (by decide), rbx₅]
  · rw [k₁₂.1 _ (by decide), rcx₁₁]
  · have K : ∀ {a b : State} {rs : List Reg}, (∀ r ∈ rs, r ∈ [Reg.rax, .rdx, .rbx, .rcx]) → Keeps rs a b →
        Keeps [Reg.rax, .rdx, .rbx, .rcx] a b := fun h k => k.mono h
    exact (K (by decide) k₁).trans ((K (by decide) k₂).trans ((K (by decide) k₃).trans
      ((K (by decide) k₄).trans ((K (by decide) k₅).trans ((K (by decide) k₆).trans
      ((K (by decide) k₇).trans ((K (by decide) k₈).trans ((K (by decide) k₉).trans
      ((K (by decide) k₁₀).trans ((K (by decide) k₁₁).trans (K (by decide) k₁₂)))))))))))

/-- `cmsTail`: `[o] = N mod p` for `N` in `CW`. -/
theorem cmsTail_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {o : Nat}
    (ho : o + 72 ≤ 4096) {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8) :
    WP isa (.block (cmsTail o)) s fun s' =>
      wordsVal s'.mem base o 9 = regsVal s CW % m ∧ KeepRegs (.rax :: .rcx :: .rdx :: CW) s s' ∧
      Outside base o 72 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [cmsTail, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (cmsCarry_ok s hm) fun s₁₂ ⟨q₁₂, cf₁₂, hc, r8₁₂, rdx₁₂, rbx₁₂, rcx₁₂, k₁₂⟩ => ?_
  rw [pair_append, WP.block_append_iff]
  refine WP.mono (adcS_ok s₁₂ .r8 (src := .reg .rdx) rfl cf₁₂) fun s₁₃ ⟨q₁₃, cf₁₃, e₁₃, k₁₃⟩ => ?_
  have k₁₃' : Keeps [Reg.rax, .rdx, .rbx, .rcx, .r8] s s₁₃ :=
    (k₁₂.mono (by decide)).trans (k₁₃.mono (by decide))
  have hs₁₃ : Scr s₁₃ base Z := hs.of_keeps k₁₃' (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeX_ok hs₁₃ .r8 (d := o) (by omega)) fun s₁₄ ⟨m₁₄, g₁₄, cf₁₄, _, rd₁₄, wr₁₄⟩ => ?_
  have hs₁₄ : Scr s₁₄ base Z := ⟨by rw [g₁₄]; exact hs₁₃.rdi, by rw [wr₁₄]; exact hs₁₃.wr, hnw⟩
  have hc0 : s₁₄.gpr .rcx = 0 := by rw [g₁₄, k₁₃.1 _ (by decide), rcx₁₂]
  rw [WP.block_append_iff, show (CW.drop 1).take 7 = CM from rfl]
  refine WP.mono (adcSt_ok hZ CM hs₁₄ ⟨by decide, by decide⟩ (by decide) hc0 (o := o + 8) (by
    rw [show CM.length = 7 from rfl]; omega) (cf₁₄.trans cf₁₃)) fun s₁₅ ⟨d₁₅, cf₁₅, e₁₅, k₁₅, O₁₅⟩ => ?_
  have hs₁₅ := hs₁₄.of_keepRegs k₁₅ (by decide)
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (adcS_ok s₁₅ .rbx (src := .reg .rcx) rfl cf₁₅) fun s₁₆ ⟨d₁₆, _, e₁₆, k₁₆⟩ => ?_
  rw [cons_split, WP.block_append_iff]
  refine WP.mono (and511_ok s₁₆ .rbx) fun s₁₇ ⟨t₁₇, k₁₇⟩ => ?_
  have hs₁₇ := (hs₁₅.of_keeps k₁₆ (by decide)).of_keeps k₁₇ (by decide)
  refine WP.mono (storeX_ok hs₁₇ .rbx (d := o + 64) (by omega)) fun s₁₈ ⟨m₁₈, g₁₈, _, _, rd₁₈, wr₁₈⟩ => ?_
  have r8₁₂ : s₁₂.gpr .r8 = s.gpr .r8 := r8₁₂
  have hM : regsVal s₁₄ CM = regsVal s CM := regsVal_congr fun q hq => by
    have mem : ∀ q ∈ CM, q ∉ [Reg.rax, .rdx, .rbx, .rcx, .r8] := by decide
    rw [g₁₄, k₁₃'.1 q (mem q hq)]
  have rbx₁₅ : s₁₅.gpr .rbx = s₁₂.gpr .rbx := by
    rw [k₁₅.gpr _ (by decide), g₁₄, k₁₃.1 _ (by decide)]
  have rcx₁₅ : s₁₅.gpr .rcx = 0 := by rw [k₁₅.gpr _ (by decide)]; exact hc0
  rw [r8₁₂, rdx₁₂] at e₁₃
  rw [show CM.length = 7 from rfl, p7, hM] at e₁₅
  rw [rbx₁₅, rcx₁₅, rbx₁₂, show (0 : BitVec 64).toNat = 0 from rfl] at e₁₆
  have m₁₇ : s₁₇.mem = s₁₅.mem := k₁₇.2.1.trans k₁₆.2.1
  have hW : wordsVal s₁₈.mem base o 9 = (s₁₃.gpr .r8).toNat + 2 ^ 64 * (wordsVal s₁₅.mem base (o + 8) 7 +
      (2 ^ 64) ^ 7 * (s₁₇.gpr .rbx).toNat) := by
    have hw0 : word s₁₈.mem base o = s₁₃.gpr .r8 := by
      rw [m₁₈, (writeW_outside s₁₇.mem base _ (by omega)).word (by omega) (by omega), m₁₇,
        O₁₅.word (by rw [show CM.length = 7 from rfl]; omega) (by omega), m₁₄, word_writeW_self]
    have hw7 : wordsVal s₁₈.mem base (o + 8) 7 = wordsVal s₁₅.mem base (o + 8) 7 := by
      rw [m₁₈, (writeW_outside s₁₇.mem base _ (by omega)).wordsVal (by omega) (by omega), m₁₇]
    rw [show wordsVal s₁₈.mem base o 9 = (word s₁₈.mem base o).toNat + 2 ^ 64 * wordsVal s₁₈.mem base (o + 8) 8
      from rfl, wordsVal_succ_last, hw0, hw7, m₁₈, show o + 8 + 8 * 7 = o + 64 by omega, word_writeW_self]
  have hO := wordsVal_lt s₁₅.mem base (o + 8) 7
  rw [p7] at hO
  have hMl := regsVal_lt s CM
  rw [show CM.length = 7 from rfl, p7] at hMl
  have hw8 := (s.gpr .rbx).isLt
  have hc2 : q₁₂.toNat ≤ 1 := Bool.toNat_le _
  have hv := tail_val (m := m) (L := (s.gpr .r8).toNat + 2 ^ 64 * regsVal s CM + (2 ^ 64) ^ 8 * ((s.gpr .rbx).toNat % 512))
    (h := (s.gpr .rbx).toNat / 512) hm rfl (s.gpr .r8).isLt hMl (Nat.mod_lt _ (by decide)) (by omega) hc hc2
    e₁₃ (s₁₃.gpr .r8).isLt e₁₅ hO e₁₆ (s₁₆.gpr .rbx).isLt
  refine ⟨?_, ?_, ?_⟩
  · rw [hW, t₁₇, regsCW_M]
    rw [tail_split hm, Nat.add_mul_mod_self_left, ← hv, tail_dist]
  · refine ⟨fun r hr => ?_, by rw [rd₁₈, k₁₇.2.2.1, k₁₆.2.2.1, k₁₅.rd, rd₁₄, k₁₃'.2.2.1],
      by rw [wr₁₈, k₁₇.2.2.2, k₁₆.2.2.2, k₁₅.wr, wr₁₄, k₁₃'.2.2.2]⟩
    have h1 : r ∉ [Reg.rbx] := fun h => hr (by rw [List.mem_singleton] at h; subst h; decide)
    have u2 : ∀ q ∈ CM, q ∈ Reg.rax :: .rcx :: .rdx :: CW := by decide
    have u3 : ∀ q ∈ [Reg.rax, .rdx, .rbx, .rcx, .r8], q ∈ Reg.rax :: .rcx :: .rdx :: CW := by decide
    have h2 : r ∉ CM := fun h => hr (u2 r h)
    have h3 : r ∉ [Reg.rax, .rdx, .rbx, .rcx, .r8] := fun h => hr (u3 r h)
    rw [g₁₈, k₁₇.1 r h1, k₁₆.1 r h1, k₁₅.gpr r h2, g₁₄, k₁₃'.1 r h3]
  · have O₁₄ : Outside base o 72 s.mem s₁₄.mem := by
      rw [m₁₄, k₁₃'.2.1]; exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)
    have O₁₅' : Outside base o 72 s₁₄.mem s₁₅.mem := by
      rw [show CM.length = 7 from rfl] at O₁₅; exact O₁₅.mono (by omega) (by omega)
    have O₁₈ : Outside base o 72 s₁₅.mem s₁₈.mem := by
      rw [m₁₈, m₁₇]; exact (writeW_outside (d := o + 64) _ _ _ (by omega)).mono (by omega) (by omega)
    exact (O₁₄.trans O₁₅').trans O₁₈

/-! ## `cmsF` -/

theorem top_lt {N L w : Nat} {k : Nat} (hN : N = L + (2 ^ 64) ^ 8 * w) (h : N < 2 ^ k * (2 ^ 64) ^ 8) : w < 2 ^ k := by
  rw [hN] at h
  exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt (by rw [Nat.mul_comm]; exact Nat.le_add_left _ _) h)

/-- `N = 4 [a]`. -/
theorem loadShl_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {a m : Nat} (ha : a + 72 ≤ 4096)
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hA : wordsVal s.mem base a 9 < 2 * m) :
    WP isa (.block (loadShl a 2)) s fun s' => regsVal s' CW = wordsVal s.mem base a 9 * 2 ^ 2 ∧ Keeps CW s s' := by
  rw [loadShl, WP.block_append_iff]
  refine WP.mono (loads_ok CW hs (a := a) (by rw [show CW.length = 9 from rfl]; omega) ⟨by decide, by decide⟩)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [show CW.length = 9 from rfl] at e₁
  have ht : (s₁.gpr .rbx).toNat < 2 ^ 61 :=
    Nat.lt_trans (top_lt (k := 10) ((regsCW8 s₁).symm.trans e₁).symm (by omega)) (by decide)
  refine WP.mono (shlCW_ok s₁ (Or.inl rfl) ht) fun s₂ ⟨e₂, k₂⟩ => ⟨by rw [e₂, e₁], k₁.trans k₂⟩

/-- `N = 8 (p - [b])`. -/
theorem loadNegShl_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {b m : Nat} (hb : b + 72 ≤ 4096)
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hB : wordsVal s.mem base b 9 < m) :
    WP isa (.block (loadNegShl b 3)) s fun s' =>
      regsVal s' CW = (m - wordsVal s.mem base b 9) * 2 ^ 3 ∧ Keeps CW s s' := by
  rw [loadNegShl, WP.block_append_iff]
  have h9 : (word s.mem base (b + 64)).toNat < 512 := by
    have e : wordsVal s.mem base b 9 = wordsVal s.mem base b 8 + (2 ^ 64) ^ 8 * (word s.mem base (b + 64)).toNat :=
      wordsVal_succ_last s.mem base b 8
    exact top_lt (k := 9) e (by omega)
  refine WP.mono (negLoads_ok hZ hs (b := b) hb h9) fun s₁ ⟨e₁, k₁⟩ => ?_
  have ht : (s₁.gpr .rbx).toNat < 2 ^ 61 :=
    Nat.lt_trans (top_lt (k := 9) (regsCW8 s₁) (by omega)) (by decide)
  refine WP.mono (shlCW_ok s₁ (Or.inr rfl) ht) fun s₂ ⟨e₂, k₂⟩ =>
    ⟨by rw [e₂, show regsVal s₁ CW = m - wordsVal s.mem base b 9 by omega], k₁.trans k₂⟩

/-- The registers `cmsF` writes. -/
def cmsRegs : List Reg := .rax :: .rcx :: .rdx :: CW

theorem keepRegs_cms {rs : List Reg} {s s' : State} (h : ∀ r ∈ rs, r ∈ cmsRegs) (k : Keeps rs s s') :
    KeepRegs cmsRegs s s' := keepRegs_of_keeps (k.mono h)

/-- The ending after `N` is in `CW`. -/
theorem cmsEnd {s₁ : State} {base : Addr} {o m N : Nat} (hZ : 4096 ≤ Z) (hs₁ : Scr s₁ base Z) (ho : o + 72 ≤ 4096)
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) {s : State} (k : KeepRegs cmsRegs s s₁) (hmem : s₁.mem = s.mem)
    (hN : regsVal s₁ CW = N) :
    WP isa (.block (cmsTail o)) s₁ fun s' => wordsVal s'.mem base o 9 = N % m ∧ KeepRegs cmsRegs s s' ∧
      Outside base o 72 s.mem s'.mem :=
  WP.mono (cmsTail_ok hZ hs₁ ho hm) fun _ ⟨e, k', O⟩ => ⟨by rw [e, hN], k.trans k', hmem ▸ O⟩

theorem cms1_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {o a b m : Nat}
    (ho : o + 72 ≤ 4096) (ha : a + 72 ≤ 4096) (hb : b + 72 ≤ 4096) (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hA : wordsVal s.mem base a 9 < 2 * m) (hB : wordsVal s.mem base b 9 < m) :
    WP isa (.block (loadShl a 2 ++ addNeg b ++ cmsTail o)) s fun s' =>
      wordsVal s'.mem base o 9 = (4 * wordsVal s.mem base a 9 + 1 * (m - wordsVal s.mem base b 9)) % m ∧
      KeepRegs cmsRegs s s' ∧ Outside base o 72 s.mem s'.mem := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadShl_ok hZ hs ha hm hA) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addNeg_ok hZ hs₁ hb (by rw [e₁, k₁.2.1]; omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine cmsEnd hZ hs₂ ho hm ((keepRegs_cms (by decide) k₁).trans (keepRegs_cms (by decide) k₂))
    (k₂.2.1.trans k₁.2.1) ?_
  rw [e₂, e₁, k₁.2.1]
  omega

theorem cms9_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {o a b m : Nat}
    (ho : o + 72 ≤ 4096) (ha : a + 72 ≤ 4096) (hb : b + 72 ≤ 4096) (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hA : wordsVal s.mem base a 9 < 2 * m) (hB : wordsVal s.mem base b 9 < m) :
    WP isa (.block (loadNegShl b 3 ++ addNeg b ++ addMulC 12 a ++ cmsTail o)) s fun s' =>
      wordsVal s'.mem base o 9 = (12 * wordsVal s.mem base a 9 + 9 * (m - wordsVal s.mem base b 9)) % m ∧
      KeepRegs cmsRegs s s' ∧ Outside base o 72 s.mem s'.mem := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadNegShl_ok hZ hs hb hm hB) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addNeg_ok hZ hs₁ hb (by rw [e₁, k₁.2.1]; omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have m₂ : s₂.mem = s.mem := k₂.2.1.trans k₁.2.1
  have h8 : 12 * (word s₂.mem base (a + 64)).toNat < 2 ^ 64 := by
    have e : wordsVal s.mem base a 9 = wordsVal s.mem base a 8 + (2 ^ 64) ^ 8 * (word s.mem base (a + 64)).toNat :=
      wordsVal_succ_last s.mem base a 8
    have := top_lt (k := 10) e (by omega)
    rw [m₂]; omega
  rw [WP.block_append_iff]
  refine WP.mono (addMulC_ok hZ hs₂ (by decide) ha h8) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine cmsEnd hZ hs₃ ho hm ((keepRegs_cms (by decide) k₁).trans ((keepRegs_cms (by decide) k₂).trans
    (keepRegs_cms (by decide) k₃))) (k₃.2.1.trans m₂) ?_
  rw [e₃, e₂, e₁, k₁.2.1, m₂]
  omega

theorem cms8_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {o a b m : Nat}
    (ho : o + 72 ≤ 4096) (ha : a + 72 ≤ 4096) (hb : b + 72 ≤ 4096) (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hA : wordsVal s.mem base a 9 < 2 * m) (hB : wordsVal s.mem base b 9 < m) :
    WP isa (.block (loadNegShl b 3 ++ addMulC 3 a ++ cmsTail o)) s fun s' =>
      wordsVal s'.mem base o 9 = (3 * wordsVal s.mem base a 9 + 8 * (m - wordsVal s.mem base b 9)) % m ∧
      KeepRegs cmsRegs s s' ∧ Outside base o 72 s.mem s'.mem := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadNegShl_ok hZ hs hb hm hB) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  have h8 : 3 * (word s₁.mem base (a + 64)).toNat < 2 ^ 64 := by
    have e : wordsVal s.mem base a 9 = wordsVal s.mem base a 8 + (2 ^ 64) ^ 8 * (word s.mem base (a + 64)).toNat :=
      wordsVal_succ_last s.mem base a 8
    have := top_lt (k := 10) e (by omega)
    rw [m₁]; omega
  rw [WP.block_append_iff]
  refine WP.mono (addMulC_ok hZ hs₁ (by decide) ha h8) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₁.of_keeps k₃ (by decide)
  refine cmsEnd hZ hs₃ ho hm ((keepRegs_cms (by decide) k₁).trans (keepRegs_cms (by decide) k₃))
    (k₃.2.1.trans m₁) ?_
  rw [e₃, e₁, m₁]
  omega

/-- `cmsF`: `[o] = (C [a] + D (p - [b])) mod p` for `[a] < 2p` and `[b] < p`. -/
theorem cmsF_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {o C a D b m : Nat}
    (ho : o + 72 ≤ 4096) (ha : a + 72 ≤ 4096) (hb : b + 72 ≤ 4096) (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hCD : (C = 4 ∧ D = 1) ∨ (C = 12 ∧ D = 9) ∨ (C = 3 ∧ D = 8))
    (hA : wordsVal s.mem base a 9 < 2 * m) (hB : wordsVal s.mem base b 9 < m) :
    WP isa (.block (cmsF o C a D b)) s fun s' =>
      wordsVal s'.mem base o 9 = (C * wordsVal s.mem base a 9 + D * (m - wordsVal s.mem base b 9)) % m ∧
      KeepRegs cmsRegs s s' ∧ Outside base o 72 s.mem s'.mem := by
  rcases hCD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cms1_ok hZ hs ho ha hb hm hA hB
  · exact cms9_ok hZ hs ho ha hb hm hA hB
  · exact cms8_ok hZ hs ho ha hb hm hA hB

end VG.Proof.Weierstrass.X86_64.P521F
