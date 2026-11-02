module

-- separate module: P-256's and P-384's joint ladders share it

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
public import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder

/-!
# ECDSA verification on RISC-V: the joint ladder's table and window

What the joint ladder (`Impl/Ecdsa/RISCV64/Verify.lean`) does for any curve
of `n` words:

* `copyTo_ok`, `storePt_ok`: a point's slots to an entry of the table, through
  `a6 = s0 + c.jt` (`wp_addAt`);
* `jstep`, `jp_zero`, `jp_top`: the points of the steps, `[u >>> 2 j]G +
  [v >>> 2 j]Q`;
* `window_ok`: the window's entry number `4 u_j + v_j`;
* `treeAt_ok`, `scanWordJ_ok`, `scansJ_ok`, `masks4_ok`: the entry to `E`, by
  the comb's tree of masks with its loads by `ldAt`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Joint

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point mul onCurve)

/-! ## The table's stores -/

/-- `rd = base + v` (`addAt`). -/
theorem wp_addAt {s : State} {is : List Instr} {Q : State → Prop} {rd base : Reg} {v : Nat} (hv : v < 6141)
    (k : ∀ s', Upd s s' rd (s.gpr base + BitVec.ofNat 64 v) → WP isa (.block is) s' Q) :
    WP isa (.block (addAt rd base v ++ is)) s Q := by
  unfold addAt
  split
  · exact wp_addi (by omega) k
  · split
    · rw [List.cons_append, List.singleton_append]
      refine wp_addi (imm := 2047) (by decide) fun s₁ u₁ => wp_addi (by omega) fun s₂ u₂ => k s₂ ?_
      have u := u₁.twice u₂
      rwa [u₁.gpr, add_2047_add _ (by omega)] at u
    · rw [List.cons_append, List.cons_append, List.singleton_append]
      refine wp_addi (imm := 2047) (by decide) fun s₁ u₁ => wp_addi (imm := 2047) (by decide) fun s₂ u₂ =>
        wp_addi (by omega) fun s₃ u₃ => k s₃ ?_
      have u := (u₁.twice u₂).twice u₃
      rwa [u₂.gpr, u₁.gpr, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat,
        show 2047 + (2047 + (v - 4094)) = v by omega] at u

/-- `[a6 + o] = [s0 + a]`, through `t0`, for `a6 = s0 + J`. -/
theorem copyTo_ok : ∀ (k : Nat) {s : State} {base : Addr} {J o a : Nat},
    WsReg s base → s.gpr .a6 = base + BitVec.ofNat 64 J → o % 8 = 0 → a % 8 = 0 → J % 8 = 0 →
    J + o + 8 * k ≤ 8192 → o + 8 * k ≤ 4095 → a + 8 * k ≤ 4095 → a + 8 * k ≤ J →
    WP isa (.block (Cfg.copyTo k o a)) s fun s' =>
      wordsVal s'.mem base (J + o) k = wordsVal s.mem base a k ∧ Rest [.t0] s s' ∧
      Outside base (J + o) (8 * k) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Rest.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, s, base, J, o, a, hw, h6, ho8, ha8, hJ8, hJ, ho, ha, haJ => by
    have hn := hw.nowrap
    have hal := hw.al
    rw [Cfg.copyTo, List.append_assoc]
    refine ldAt_ws hw (by omega) ha8 fun s₁ u₁ => ?_
    have K₁ := u₁.rest (ws := [.t0]) (by decide)
    have hw₁ := hw.of_rest K₁
    refine wp_sdAt (a := off base (J + o)) (by omega) (by decide)
      (by rw [u₁.other _ (by decide), h6, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat])
      (by simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      ⟨_, hw₁.wr, Offset.contains_base base (by omega) (by omega)⟩ fun s₂ u₂ => ?_
    have K₂ : Rest [.t0] s s₂ := K₁.trans ((u₂.rest []).mono (by simp))
    have O₂ : Outside base (J + o) 8 s.mem s₂.mem := by
      rw [u₂.mem, u₁.mem]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (copyTo_ok k (hw.of_rest K₂) (J := J) (o := o + 8) (a := a + 8)
      (by rw [K₂.gpr _ (by decide), h6]) (by omega) (by omega) hJ8 (by omega) (by omega) (by omega) (by omega))
      fun s₃ ⟨e₃, K₃, O₃⟩ => ⟨?_, K₂.trans K₃,
        (O₂.mono (Nat.le_refl _) (by omega)).trans (O₃.mono (by omega) (by omega))⟩
    rw [show J + (o + 8) = J + o + 8 by omega] at e₃ O₃
    rw [wordsVal, wordsVal, O₃.word (by omega) (by omega), e₃, u₂.mem, u₁.mem, u₁.gpr,
      word_writeW_self]
    rw [(writeW_outside s.mem base (d := J + o) (word s.mem base a) (by omega)).wordsVal (d := a + 8) (k := k)
      (by omega) (by omega)]

/-- Entry `e` of the table from the point `p` in slots below byte 4095. -/
theorem storePt_ok (c : Cfg) {s : State} {base : Addr} (hw : WsReg s base) {e : Nat} {p : Pt}
    (hJ : c.jt % 8 = 0 ∧ c.jt < 6141) (he : c.jt + Cfg.jb c * e + 24 * c.n ≤ 8192)
    (ho : Cfg.jb c * e + 24 * c.n ≤ 4095)
    (hx : p.x % 8 = 0 ∧ p.x + 8 * c.n ≤ 4095 ∧ p.x + 8 * c.n ≤ c.jt)
    (hy : p.y % 8 = 0 ∧ p.y + 8 * c.n ≤ 4095 ∧ p.y + 8 * c.n ≤ c.jt)
    (hz : p.z % 8 = 0 ∧ p.z + 8 * c.n ≤ 4095 ∧ p.z + 8 * c.n ≤ c.jt) :
    WP isa (.block (Cfg.storePt c e p)) s fun s' =>
      wordsVal s'.mem base (c.jt + Cfg.jb c * e) c.n = wordsVal s.mem base p.x c.n ∧
      wordsVal s'.mem base (c.jt + Cfg.jb c * e + 8 * c.n) c.n = wordsVal s.mem base p.y c.n ∧
      wordsVal s'.mem base (c.jt + Cfg.jb c * e + 16 * c.n) c.n = wordsVal s.mem base p.z c.n ∧
      Rest [.t0, .a6] s s' ∧ Outside base (c.jt + Cfg.jb c * e) (Cfg.jb c) s.mem s'.mem := by
  have hn := hw.nowrap
  have hjb : Cfg.jb c = 24 * c.n := rfl
  rw [Cfg.storePt]
  simp only [List.append_assoc]
  refine wp_addAt hJ.2 fun s₂ u₂ => ?_
  have r₂ : Rest [.t0, .a6] s s₂ := u₂.rest (by decide)
  have hw₂ := hw.of_rest r₂
  have h6 : s₂.gpr .a6 = base + BitVec.ofNat 64 c.jt := by rw [u₂.gpr, hw.s0]
  have m₂ : s₂.mem = s.mem := u₂.mem
  rw [hjb] at he ho ⊢
  have hE8 : 24 * c.n * e % 8 = 0 := by
    rw [show 24 = 8 * 3 from rfl, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_mod_right]
  refine WP.block_append (WP.mono (copyTo_ok c.n hw₂ (J := c.jt) (o := 24 * c.n * e) (a := p.x) h6 (by omega)
    hx.1 hJ.1 (by omega) (by omega) (by omega) (by omega)) fun s₃ ⟨e₃, r₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  refine WP.block_append (WP.mono (copyTo_ok c.n hw₃ (J := c.jt) (o := 24 * c.n * e + 8 * c.n) (a := p.y)
    (by rw [r₃.gpr _ (by decide), h6]) (by omega) hy.1 hJ.1 (by omega) (by omega) (by omega) (by omega))
    fun s₄ ⟨e₄, r₄, O₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  refine WP.mono (copyTo_ok c.n hw₄ (J := c.jt) (o := 24 * c.n * e + 16 * c.n) (a := p.z)
    (by rw [r₄.gpr _ (by decide), r₃.gpr _ (by decide), h6]) (by omega) hz.1 hJ.1 (by omega) (by omega)
      (by omega) (by omega))
    fun s₅ ⟨e₅, r₅, O₅⟩ => ⟨?_, ?_, ?_, r₂.trans ((r₃.trans (r₄.trans r₅)).mono (by simp)), ?_⟩
  · rw [O₅.wordsVal (by omega) (by omega), O₄.wordsVal (by omega) (by omega), e₃, m₂]
  · rw [show c.jt + 24 * c.n * e + 8 * c.n = c.jt + (24 * c.n * e + 8 * c.n) by omega,
      O₅.wordsVal (by omega) (by omega), e₄, O₃.wordsVal (by omega) (by omega), m₂]
  · rw [show c.jt + 24 * c.n * e + 16 * c.n = c.jt + (24 * c.n * e + 16 * c.n) by omega, e₅,
      O₄.wordsVal (by omega) (by omega), O₃.wordsVal (by omega) (by omega), m₂]
  · rw [← m₂]
    exact ((O₃.mono (by omega) (by omega)).trans (O₄.mono (by omega) (by omega))).trans
      (O₅.mono (by omega) (by omega))

/-! ## The points -/

section
variable {C : Spec.Weierstrass.Curve}

/-- Entry `4 a + b`: `[a]G + [b]Q`. -/
def ent (G Q : Point C) (a b : Nat) : Point C := Spec.Weierstrass.add (mul a G) (mul b Q)

/-- `R` before window `j - 1`: `[u >>> 2 j]G + [v >>> 2 j]Q`. -/
def jp (G Q : Point C) (u v j : Nat) : Point C := ent G Q (u >>> (2 * j)) (v >>> (2 * j))

theorem ent_curve (hL : Law C) {G Q : Point C} (hG : onCurve C G = true) (hQ : onCurve C Q = true)
    (a b : Nat) : onCurve C (ent G Q a b) = true :=
  hL.onCurve_add (hL.onCurve_mul hG _) (hL.onCurve_mul hQ _)

theorem shr_two (u j : Nat) : u >>> (2 * j) = 4 * (u >>> (2 * (j + 1))) + (u >>> (2 * j)) % 4 := by
  rw [show 2 * (j + 1) = 2 * j + 2 by omega, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (u >>> (2 * j)) 2]
  omega

/-- A step: `4 R + E`, for `R` before the window and `E` its entry, is `R`
after it. -/
theorem jstep (hL : Law C) {G Q : Point C} (hG : onCurve C G = true) (hQ : onCurve C Q = true) (u v j : Nat) :
    Spec.Weierstrass.add
      (Spec.Weierstrass.add (Spec.Weierstrass.add (jp G Q u v (j + 1)) (jp G Q u v (j + 1)))
        (Spec.Weierstrass.add (jp G Q u v (j + 1)) (jp G Q u v (j + 1))))
      (ent G Q ((u >>> (2 * j)) % 4) ((v >>> (2 * j)) % 4)) = jp G Q u v j := by
  have eu := shr_two u j
  have ev := shr_two v j
  generalize (u >>> (2 * j)) % 4 = a at eu ⊢
  generalize (v >>> (2 * j)) % 4 = b at ev ⊢
  rw [show jp G Q u v j = ent G Q (u >>> (2 * j)) (v >>> (2 * j)) from rfl, eu, ev]
  simp only [jp]
  generalize u >>> (2 * (j + 1)) = m
  generalize v >>> (2 * (j + 1)) = n
  have hX := ent_curve hL hG hQ m n
  have hE := ent_curve hL hG hQ a b
  have h2 := hL.onCurve_add hX hX
  have h4 := hL.onCurve_add h2 h2
  obtain ⟨M, _, f, hf⟩ := hL.group
  apply hf.inj (hL.onCurve_add h4 hE) (ent_curve hL hG hQ _ _)
  simp only [ent] at *
  rw [hf.add h4 hE, hf.add h2 h2, hf.add hX hX, hf.add (hL.onCurve_mul hG _) (hL.onCurve_mul hQ _),
    hf.add (hL.onCurve_mul hG _) (hL.onCurve_mul hQ _), hf.add (hL.onCurve_mul hG _) (hL.onCurve_mul hQ _),
    hf.mul hG, hf.mul hQ, hf.mul hG, hf.mul hQ, hf.mul hG, hf.mul hQ]
  have hu : ((4 * m + a : Nat) : Int) = m + m + m + m + a := by omega
  have hv : ((4 * n + b : Nat) : Int) = n + n + n + n + b := by omega
  rw [hu, hv]
  simp only [Lean.Grind.IntModule.add_zsmul]
  grind

/-- After the last window: `[u]G + [v]Q`. -/
theorem jp_zero (G Q : Point C) (u v : Nat) : jp G Q u v 0 = Spec.Weierstrass.add (mul u G) (mul v Q) := by
  simp only [jp, ent, Nat.mul_zero, Nat.shiftRight_zero]

/-- Before the first: `O`. -/
theorem jp_top (G Q : Point C) {n u v : Nat} (hu : u < 2 ^ (64 * n)) (hv : v < 2 ^ (64 * n)) :
    jp G Q u v (32 * n) = .infinity := by
  have h0 : ∀ (k : Nat) (X : Point C), k < 2 ^ (64 * n) → mul (k >>> (2 * (32 * n))) X = .infinity := fun k X hk => by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by rw [show 2 * (32 * n) = 64 * n by omega]; exact hk),
      Spec.Weierstrass.mul]; rfl
  simp only [jp, ent, h0 u G hu, h0 v Q hv]
  rfl

end

/-! ## The window -/

/-- Two bits of `u` at `r = 2 j mod 64` in `x`: `(u >>> 2 j) mod 4`. -/
theorem two_bits (x : BitVec 64) (u : Nat) {j : Nat} (h0 : x.getLsbD (2 * j % 64) = u.testBit (2 * j))
    (h1 : x.getLsbD (2 * j % 64 + 1) = u.testBit (2 * j + 1)) :
    (x >>> (2 * j % 64)) &&& BitVec.ofInt 64 3 = BitVec.ofNat 64 ((u >>> (2 * j)) % 4) := by
  rw [show (u >>> (2 * j)) % 4 = (u >>> (2 * j)) % 2 ^ 2 from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, show (BitVec.ofInt 64 3) = BitVec.ofNat 64 (2 ^ 2 - 1) from rfl,
    BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  have : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
  rcases this with rfl | rfl | h
  · simp only [Nat.add_zero, h0]; simp
  · simp only [h1]; simp [Nat.add_comm]
  · simp [show ¬ i < 2 by omega]

theorem combine4 : ∀ a < 4, ∀ b < 4, (BitVec.ofNat 64 a <<< 2) ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (4 * a + b) := by
  decide

/-- The window's entry number, `4 u_j + v_j`, into `t2`, for `j` in `s1`. -/
theorem window_ok (c : Cfg) {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 32 * c.n)
    (hU : c.sl UU + 8 * c.n ≤ 2048) (hV : c.sl VV + 8 * c.n ≤ 2048)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) :
    WP isa (.block (Cfg.window c)) s fun s' =>
      s'.gpr .t2 = BitVec.ofNat 64 (4 * ((wordsVal s.mem base (c.sl UU) c.n >>> (2 * j)) % 4) +
        (wordsVal s.mem base (c.sl VV) c.n >>> (2 * j)) % 4) ∧
      Rest [.t0, .t1, .t2, .t3] s s' ∧ s'.mem = s.mem := by
  have hn := hw.nowrap
  have hal := hw.al
  have hq : j / 32 < c.n := by omega
  have hU8 : c.sl UU % 8 = 0 := by simp only [Cfg.sl, slot, UU]; omega
  have hV8 : c.sl VV % 8 = 0 := by simp only [Cfg.sl, slot, VV]; omega
  rw [Cfg.window]
  refine wp_srl (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  have e₃' : s₃.gpr .t1 = base + BitVec.ofNat 64 (8 * (j / 32)) := by
    rw [u₃.gpr, u₂.gpr, u₂.other .s0 (by decide), u₁.gpr, u₁.other .s0 (by decide), hw.s0, h1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega : j < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : j / 32 * 8 < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : 8 * (j / 32) < 18446744073709551616)]
    omega
  have e₃ : ∀ d, s₃.gpr .t1 + BitVec.ofNat 64 d = off base (d + 8 * (j / 32)) := by
    intro d
    rw [e₃', BitVec.add_assoc, BitVec.ofNat_add_ofNat, off, Nat.add_comm]
  have r₃ : Rest [.t1] s s₃ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have inr : ∀ d, d + 8 ≤ 8192 → InRegions (s₃.rd ++ s₃.wr) (off base d) 8 := fun d hd =>
    ⟨_, List.mem_append_right _ (r₃.wr ▸ hw.wr), Offset.contains_base base hd (by omega)⟩
  have alg : ∀ d, d % 8 = 0 → d < 8192 → (off base d).toNat % 8 = 0 := fun d h8 hd => by
    simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine wp_ld (by omega) (e₃ (c.sl UU)) (alg _ (by omega) (by omega))
    (inr _ (by omega)) fun s₄ u₄ => ?_
  refine wp_ld (by omega) (by rw [u₄.other .t1 (by decide)]; exact e₃ (c.sl VV))
    (alg _ (by omega) (by omega)) (by rw [u₄.rd, u₄.wr]; exact inr _ (by omega))
    fun s₅ u₅ => ?_
  refine wp_sll (by decide) fun s₆ u₆ => wp_srlReg fun s₇ u₇ => wp_srlReg fun s₈ u₈ => ?_
  refine wp_andi (by decide) fun s₉ u₉ => wp_andi (by decide) fun s₁₀ u₁₀ => wp_sll (by decide) fun s₁₁ u₁₁ => ?_
  refine wp_or fun s₁₂ u₁₂ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have t0₆ : (s₆.gpr .t0).toNat % 64 = 2 * j % 64 := by
      rw [u₆.gpr, u₅.other .s1 (by decide), u₄.other .s1 (by decide), r₃.gpr .s1 (by decide), h1,
        BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      simp only [Nat.shiftLeft_eq, Nat.reducePow]
      omega
    have t0₇ : (s₇.gpr .t0).toNat % 64 = 2 * j % 64 := by rw [u₇.other .t0 (by decide)]; exact t0₆
    have hu := two_bits (s₄.gpr .t2) (wordsVal s.mem base (c.sl UU) c.n) (j := j)
      (by
        rw [u₄.gpr, m₃, BitVec.getLsbD, ← testBit_wordsVal s.mem base c.n (c.sl UU) (2 * j) (by omega),
          show 2 * j / 64 = j / 32 by omega, Nat.add_comm])
      (by
        rw [u₄.gpr, m₃, BitVec.getLsbD, show 2 * j % 64 + 1 = (2 * j + 1) % 64 by omega,
          ← testBit_wordsVal s.mem base c.n (c.sl UU) (2 * j + 1) (by omega),
          show (2 * j + 1) / 64 = j / 32 by omega, Nat.add_comm])
    have hv := two_bits (s₅.gpr .t3) (wordsVal s.mem base (c.sl VV) c.n) (j := j)
      (by
        rw [u₅.gpr, u₄.mem, m₃, BitVec.getLsbD, ← testBit_wordsVal s.mem base c.n (c.sl VV) (2 * j) (by omega),
          show 2 * j / 64 = j / 32 by omega, Nat.add_comm])
      (by
        rw [u₅.gpr, u₄.mem, m₃, BitVec.getLsbD, show 2 * j % 64 + 1 = (2 * j + 1) % 64 by omega,
          ← testBit_wordsVal s.mem base c.n (c.sl VV) (2 * j + 1) (by omega),
          show (2 * j + 1) / 64 = j / 32 by omega, Nat.add_comm])
    have a₁₀ : s₁₀.gpr .t2 = BitVec.ofNat 64 ((wordsVal s.mem base (c.sl UU) c.n >>> (2 * j)) % 4) := by
      rw [u₁₀.other .t2 (by decide), u₉.gpr, u₈.other .t2 (by decide), u₇.gpr, t0₆, u₆.other .t2 (by decide),
        u₅.other .t2 (by decide), hu]
    have b₁₀ : s₁₀.gpr .t3 = BitVec.ofNat 64 ((wordsVal s.mem base (c.sl VV) c.n >>> (2 * j)) % 4) := by
      rw [u₁₀.gpr, u₉.other .t3 (by decide), u₈.gpr, t0₇, u₇.other .t3 (by decide), u₆.other .t3 (by decide), hv]
    rw [u₁₂.gpr, u₁₁.gpr, u₁₁.other .t3 (by decide), a₁₀, b₁₀]
    exact combine4 _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))
  · exact (r₃.mono (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans
      ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans ((u₈.rest (by decide)).trans
        ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans ((u₁₁.rest (by decide)).trans
          (u₁₂.rest (by decide))))))))))
  · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃]

/-! ## The entry -/

open VG.Proof.Ecdsa.RISCV64.Comb (wp_pick mod_two_pow_succ' maskOfBit_ok upd_keep)
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs treeAt)

/-- `tree_ok` for `treeAt`, whose loads reach offsets up to 4094. -/
theorem treeAt_ok (base : Reg) (stride : Nat) (t : Nat) (L : Nat) :
    ∀ (o : Nat) (a : Reg) (rs : List Reg) (s : State),
    L ≤ rs.length → (a :: rs).Nodup → (∀ r ∈ a :: rs, r ≠ base ∧ ∀ c < L, r ≠ maskReg c) →
    (∀ c < L, s.gpr (maskReg c) = maskOf (t.testBit c)) →
    o + stride * (2 ^ L - 1) < 4095 →
    (∀ e < 2 ^ L, (s.gpr base + BitVec.ofNat 64 (o + stride * e)).toNat % 8 = 0 ∧
      InRegions (s.rd ++ s.wr) (s.gpr base + BitVec.ofNat 64 (o + stride * e)) 8) →
    WP isa (.block (treeAt base stride L o (a :: rs))) s fun s' =>
      s'.gpr a = s.mem.readW (s.gpr base + BitVec.ofNat 64 (o + stride * (t % 2 ^ L))) 64 ∧
      Keep (a :: rs) s s' ∧ s'.mem = s.mem := by
  induction L with
  | zero =>
    intro o a rs s _ _ hne _ ho hal
    have h0 := hal 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    unfold treeAt
    rw [← List.append_nil (ldAt a base o)]
    refine wp_ldAt (by omega) rfl h0.1 h0.2 fun s' u => WP.block_nil ⟨?_, (upd_keep u).mono (by simp), u.mem⟩
    rw [u.gpr, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.add_zero]
  | succ L ih =>
    intro o a rs s hlen hnd hne hm ho hal
    obtain ⟨b, rs, rfl⟩ : ∃ b rs', rs = b :: rs' := by
      cases rs with
      | nil => simp at hlen
      | cons b rs' => exact ⟨b, rs', rfl⟩
    simp only [List.length_cons] at hlen
    have hab : a ≠ b := fun e => by subst e; simp at hnd
    have hb := hne b (by simp)
    have hp : stride * 2 ^ L ≤ stride * (2 ^ (L + 1) - 1) := by
      apply Nat.mul_le_mul_left; rw [Nat.pow_succ]; have := Nat.two_pow_pos L; omega
    have hp' : stride * (2 ^ L - 1) ≤ stride * 2 ^ L := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    unfold treeAt
    rw [WP.block_append_iff, WP.block_append_iff]
    -- The low half, into `a`.
    refine WP.mono (ih o a (b :: rs) s (by simp; omega) hnd
      (fun r hr => ⟨(hne r hr).1, fun c hc => (hne r hr).2 c (by omega)⟩)
      (fun c hc => hm c (by omega)) (by omega)
      (fun e he => hal e (by rw [Nat.pow_succ]; omega))) fun s₁ ⟨ta, tk, tm⟩ => ?_
    have tep : s₁.gpr base = s.gpr base := tk.gpr (by simpa using fun h => (hne base h).1 rfl)
    have tmk (c : Nat) (hc : c < L + 1) : s₁.gpr (maskReg c) = s.gpr (maskReg c) :=
      tk.gpr fun h => (hne _ h).2 c hc rfl
    -- The high half, into `b`.
    have hp2 : stride * 2 ^ L + stride * (2 ^ L - 1) = stride * (2 ^ (L + 1) - 1) := by
      rw [← Nat.mul_add, Nat.pow_succ]; congr 1; have := Nat.two_pow_pos L; omega
    refine WP.mono (ih (o + stride * 2 ^ L) b rs s₁ (by omega) (List.nodup_cons.mp hnd).2
      (fun r hr => ⟨(hne r (by simp [hr])).1, fun c hc => (hne r (by simp [hr])).2 c (by omega)⟩)
      (fun c hc => by rw [tmk c (by omega)]; exact hm c (by omega)) (by omega)
      (fun e he => by
        rw [tep, tk.2.1, tk.2.2, show o + stride * 2 ^ L + stride * e = o + stride * (2 ^ L + e) by
          rw [Nat.mul_add, Nat.add_assoc]]
        exact hal _ (by rw [Nat.pow_succ]; omega))) fun s₂ ⟨ub, uk, um⟩ => ?_
    have ua : s₂.gpr a = s₁.gpr a := uk.gpr (List.nodup_cons.mp hnd).1
    have umk : s₂.gpr (maskReg L) = maskOf (t.testBit L) := by
      rw [uk.gpr fun h => (hne _ (by simp [h])).2 L (by omega) rfl, tmk L (by omega), hm L (by omega)]
    have hbm : b ≠ maskReg L := hb.2 L (by omega)
    -- The selection by bit `L`.
    refine wp_pick hab hbm umk fun s₃ va vk vm => WP.block_nil ⟨?_, ?_, by rw [vm, um, tm]⟩
    · rw [va, ub, ua, ta, tep, tm, mod_two_pow_succ']
      split
      · rw [Nat.mul_add, Nat.add_assoc]
      · rw [Nat.zero_add]
    · exact ((tk.trans uk).trans vk).mono (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with ((h | h | h) | h | h) | h | h <;> simp only [h, true_or, or_true])

/-- Quadword `q` of entry `t % 16`, to `E`'s word `q`. -/
theorem scanWordJ_ok (c : Cfg) {s : State} {base : Addr} (hw : WsReg s base) {q t : Nat} (hq : q < 3 * c.n)
    (hJ : c.jt % 8 = 0) (hJ8 : c.jt + 24 * c.n * 16 ≤ 8192) (hT : 24 * c.n * 15 + 8 * q < 4095)
    (hE : c.sl EX + 8 * q < 4095)
    (hm : ∀ c < 4, s.gpr (maskReg c) = maskOf (t.testBit c)) (h0 : s.gpr .a0 = base + BitVec.ofNat 64 c.jt) :
    WP isa (.block (Cfg.scanWord c q)) s fun s' =>
      s'.mem = s.mem.writeW (off base (c.sl EX + 8 * q)) (word s.mem base (c.jt + 8 * q + 24 * c.n * (t % 16))) ∧
      Keep treeRegs s s' := by
  have hn := hw.nowrap
  have hal := hw.al
  have hjb : Cfg.jb c = 24 * c.n := rfl
  have hEX8 : c.sl EX % 8 = 0 := by simp only [Cfg.sl, slot, EX]; omega
  unfold Cfg.scanWord
  rw [hjb]
  have hne : ∀ r ∈ treeRegs, r ≠ .a0 ∧ ∀ c < 4, r ≠ maskReg c := by
    intro r hr
    simp only [treeRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨?_, fun c hc => ?_⟩
    · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have ea : ∀ e, s.gpr .a0 + BitVec.ofNat 64 (8 * q + 24 * c.n * e) = off base (c.jt + 8 * q + 24 * c.n * e) := by
    intro e; rw [h0, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
  refine WP.block_append (WP.mono (treeAt_ok .a0 (24 * c.n) t 4 (8 * q) .t0 [.t1, .t2, .t3, .t4, .t5, .t6] s
    (by decide) (by decide) hne hm (by omega)
    (fun e he => by
      rw [ea]
      have : 24 * c.n * e ≤ 24 * c.n * 15 := Nat.mul_le_mul_left _ (by omega)
      have : 24 * c.n * e % 8 = 0 := by
        rw [show 24 = 8 * 3 from rfl, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_mod_right]
      refine ⟨by simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
        ⟨_, List.mem_append_right _ hw.wr, Offset.contains_base base (by omega) (by omega)⟩⟩))
    fun s₁ ⟨v₁, k₁, m₁⟩ => ?_)
  have hw₁ : WsReg s₁ base := ⟨by rw [k₁.gpr (by decide), hw.s0], by rw [k₁.2.2]; exact hw.wr, hw.nowrap, hw.al⟩
  rw [← List.append_nil (sdAt .t0 wb _)]
  refine sdAt_ws hw₁ (by decide) (by omega) (by omega) fun s₂ u₂ => WP.block_nil ⟨?_, ?_⟩
  · rw [u₂.mem, m₁, v₁, ea]
  · exact ⟨fun r hr => by
      rw [u₂.gpr, k₁.gpr (by simpa only [treeRegs] using hr)],
      by rw [u₂.rd, k₁.2.1], by rw [u₂.wr, k₁.2.2]⟩

/-- The entry's `n` first quadwords to `E`. -/
theorem scansJ_ok (c : Cfg) {base : Addr} {t : Nat} (hJ : c.jt % 8 = 0) (hJ8 : c.jt + 24 * c.n * 16 ≤ 8192)
    (hT : 24 * c.n * 15 + 8 * (3 * c.n) ≤ 4095) (hE : c.sl EX + 8 * (3 * c.n) ≤ 4095)
    (hEJ : c.sl EX + 8 * (3 * c.n) ≤ c.jt) :
    ∀ n ≤ 3 * c.n, ∀ {s : State}, WsReg s base →
    s.gpr .a0 = base + BitVec.ofNat 64 c.jt → (∀ c < 4, s.gpr (maskReg c) = maskOf (t.testBit c)) →
    WP isa (.block ((List.range n).flatMap (Cfg.scanWord c))) s fun s' =>
      (∀ q < n, word s'.mem base (c.sl EX + 8 * q) = word s.mem base (c.jt + 8 * q + 24 * c.n * (t % 16))) ∧
      Outside base (c.sl EX) (8 * n) s.mem s'.mem ∧ Keep treeRegs s s'
  | 0, _, s, _, _, _ => WP.block_nil ⟨fun q hq => absurd hq (by omega), Outside.refl _ _ _ _, Keep.refl _ _⟩
  | n + 1, hn, s, hw, h0, hm => by
    have hnw := hw.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (scansJ_ok c hJ hJ8 hT hE hEJ n (by omega) hw h0 hm) fun s₁ ⟨v₁, O₁, k₁⟩ => ?_)
    have ne : ∀ r ∈ [Reg.s0, .a0, .a1, .a2, .a3, .a4], r ∉ treeRegs := by decide
    have e0 : s₁.gpr .a0 = s.gpr .a0 := k₁.gpr (ne _ (by simp))
    have hw₁ : WsReg s₁ base := ⟨by rw [k₁.gpr (ne _ (by simp)), hw.s0], by rw [k₁.2.2]; exact hw.wr, hw.nowrap, hw.al⟩
    have hm₁ : ∀ c < 4, s₁.gpr (maskReg c) = maskOf (t.testBit c) := fun c hc => by
      rw [k₁.gpr (by
        have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> decide)]
      exact hm c hc
    refine WP.mono (scanWordJ_ok c hw₁ (q := n) (by omega) hJ hJ8 (by omega) (by omega) hm₁ (by rw [e0, h0]))
      fun s₂ ⟨m₂, k₂⟩ => ?_
    have ht := Nat.mod_lt t (show 16 > 0 by decide)
    have hr : word s₁.mem base (c.jt + 8 * n + 24 * c.n * (t % 16)) =
        word s.mem base (c.jt + 8 * n + 24 * c.n * (t % 16)) := by
      have : 24 * c.n * (t % 16) ≤ 24 * c.n * 15 := Nat.mul_le_mul_left _ (by omega)
      exact O₁.word (by omega) (by omega)
    have O₂ : Outside base (c.sl EX + 8 * n) 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun q hq => ?_, ?_, k₁.trans k₂ |>.mono (by simp [treeRegs])⟩
    · by_cases hqn : q < n
      · rw [O₂.word (by omega) (by omega), v₁ q hqn]
      · obtain rfl : q = n := by omega
        rw [m₂, word_writeW_self, hr]
    · exact (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))

/-- Numbers of words equal word by word. -/
theorem wordsVal_of_words {m m' : Mem} {base : Addr} : ∀ (k : Nat) {d d' : Nat},
    (∀ q < k, word m' base (d' + 8 * q) = word m base (d + 8 * q)) → wordsVal m' base d' k = wordsVal m base d k
  | 0, _, _, _ => rfl
  | k + 1, d, d', h => by
    rw [wordsVal, wordsVal, show d' = d' + 8 * 0 from rfl, show d = d + 8 * 0 from rfl, h 0 (by omega),
      wordsVal_of_words k (d := d + 8 * 0 + 8) (d' := d' + 8 * 0 + 8) fun q hq => by
        rw [show d' + 8 * 0 + 8 + 8 * q = d' + 8 * (q + 1) by omega, show d + 8 * 0 + 8 + 8 * q = d + 8 * (q + 1) by omega]
        exact h (q + 1) (by omega)]

/-- The masks of the four bits of `t2`. -/
theorem masks4_ok {s : State} :
    WP isa (.block ((List.range 4).flatMap Impl.Ecdsa.RISCV64.Comb.Cfg.maskOfBit)) s fun s' =>
      (∀ c < 4, s'.gpr (maskReg c) = maskOf ((s.gpr .t2).getLsbD c)) ∧
        Rest [.a1, .a2, .a3, .a4] s s' ∧ s'.mem = s.mem := by
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine maskOfBit_ok (b := 0) (by decide) fun s₁ v₁ r₁ m₁ => ?_
  refine maskOfBit_ok (b := 1) (by decide) fun s₂ v₂ r₂ m₂ => ?_
  refine maskOfBit_ok (b := 2) (by decide) fun s₃ v₃ r₃ m₃ => ?_
  refine maskOfBit_ok (b := 3) (by decide) fun s₄ v₄ r₄ m₄ => WP.block_nil ⟨?_, ?_, ?_⟩
  · simp only [maskReg] at v₁ v₂ v₃ v₄ r₁ r₂ r₃ r₄
    have t1 : s₁.gpr .t2 = s.gpr .t2 := r₁.gpr .t2 (by decide)
    have t2 : s₂.gpr .t2 = s.gpr .t2 := (r₂.gpr .t2 (by decide)).trans t1
    have t3 : s₃.gpr .t2 = s.gpr .t2 := (r₃.gpr .t2 (by decide)).trans t2
    intro c hc
    have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp only [maskReg]
    · rw [r₄.gpr _ (by decide), r₃.gpr _ (by decide), r₂.gpr _ (by decide), v₁]
    · rw [r₄.gpr _ (by decide), r₃.gpr _ (by decide), v₂, t1]
    · rw [r₄.gpr _ (by decide), v₃, t2]
    · rw [v₄, t3]
  · simp only [maskReg] at r₁ r₂ r₃ r₄
    exact (r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₃.mono (by decide)).trans (r₄.mono (by decide))))
  · rw [m₄, m₃, m₂, m₁]

end VG.Proof.Ecdsa.RISCV64.Joint
