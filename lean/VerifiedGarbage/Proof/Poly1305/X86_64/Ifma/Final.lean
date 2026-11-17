module

import VerifiedGarbage.Proof.Framework.Lit
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Group
public import Mathlib.Data.Nat.ModEq
public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Gpr

/-! ### `Poly1305.X86_64.Ifma.Group`, which only this module used -/

section

/-! ### `Poly1305.X86_64.Ifma.Powers`, which only this module used -/

section

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: the powers of `r`

`powers` loads the clamped `r` (into `r10` and `r11`), stores the mask and
the pad bit in the state, and squares `r` three times, every quadword alike:
`r²` and `r⁴` are stored in the state, and `r⁸` is left in `Y` (with `S`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Ifma
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Proof.Poly1305.X86_64 (off off_eq M0 M1 wR wR_contains sep_off readW_writeW_off)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_gpr vec_mem vec_rd vec_wr)
open VG.Proof.Poly1305.X86_64.Avx512 (qz envOf_v VKeep)
open VG.Spec.Poly1305 (P)

/-- The value of quadword `k` of `H` and of `Y`. -/
def hval (s : State) (k : Nat) : Nat := Limbs44.val (hv s k)
def yval (s : State) (k : Nat) : Nat := Limbs44.val (yv s k)

theorem mul_val {s s' : State} (hp : MulPre s) (h : MulPost s s') {k : Nat} (hk : k < 8) :
    hval s' k ≡ hval s k * yval s k [MOD P] := by
  obtain e : hv s' k = Limbs44.mul (hv s k) (yv s k) (sv s k) := by
    funext i
    rcases (by omega_arith : i < 3 ∨ 3 ≤ i) with hi | hi
    · exact h.h k hk i hi
    · have e : ∀ {j}, 2 ≤ j → hreg j = hreg 2 := fun {j} hj => by match j, hj with | _ + 2, _ => rfl
      obtain e2 := h.h k hk 2 (by decide)
      simp only [hv] at e2 ⊢
      rw [e (by omega_arith), e2]
      show Limbs44.carry _ _ 2 = Limbs44.carry _ _ i
      match i, hi with | _ + 3, _ => rfl
  simp only [hval, yval]
  rw [e]
  exact hp.mul_mod hk

theorem Ctx.of_eq {s s' : State} (h : Ctx s) (hsi : s'.gpr .rsi = s.gpr .rsi) (hdi : s'.gpr .rdi = s.gpr .rdi)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ctx s' :=
  ⟨fun i hi => by rw [hrd, hwr, hsi]; exact h.ld i hi, fun d h₁ h₂ => by rw [hrd, hwr, hdi]; exact h.mb d h₁ h₂⟩

theorem VKeep.hv {s s' : State} (h : VKeep s s') : hv s' = hv s := by
  funext k i; exact congrArg BitVec.toNat (h.qz_eq _ _)
theorem VKeep.yv {s s' : State} (h : VKeep s s') : yv s' = yv s := by
  funext k i; exact congrArg BitVec.toNat (h.qz_eq _ _)
theorem VKeep.sv {s s' : State} (h : VKeep s s') : sv s' = sv s := by
  funext k i; exact congrArg BitVec.toNat (h.qz_eq _ _)

/-! ## The state's working space -/

/-- What the code keeps in the state: the mask, the pad bit, and the limbs of
`r²` and `r⁴` (each at most `2⁴⁴`), for `r = R`. -/
structure MemR (p : Addr) (R : Nat) (m : Mem) : Prop where
  mask : m.readW (off p 104) 64 = 0xfffffffffff
  pad : m.readW (off p 112) 64 = 0x10000000000
  r2 : ∀ i < 3, (m.readW (off p (56 + 8 * i)) 64).toNat ≤ 2 ^ 44
  r2v : Limbs44.val (fun i => (m.readW (off p (56 + 8 * i)) 64).toNat) ≡ R ^ 2 [MOD P]
  r4 : ∀ i < 3, (m.readW (off p (80 + 8 * i)) 64).toNat ≤ 2 ^ 44
  r4v : Limbs44.val (fun i => (m.readW (off p (80 + 8 * i)) 64).toNat) ≡ R ^ 4 [MOD P]

theorem MemR.consts {p : Addr} {R : Nat} {s : State} (h : MemR p R s.mem) (hp : s.gpr .rdi = p) :
    Consts s :=
  ⟨by simp only [envOf, Avx512.envOf, hp]; rw [← off, h.mask]; rfl,
   by simp only [envOf, Avx512.envOf, hp]; rw [← off, h.pad]; rfl⟩

theorem hMem_frame {p : Addr} {d : Nat} (h₁ : 56 ≤ d) (h₂ : d + 24 ≤ 128) (x : XReg → BitVec 128) :
    ∀ {m m' : Mem}, Frame [wR p] m m' → Frame [wR p] m (hMem m' p d x) := by
  intro m m' hf
  exact ((hf.writeW (List.mem_singleton_self _) _ (wR_contains p h₁ (by omega_arith))).writeW
    (List.mem_singleton_self _) _ (wR_contains p (by omega_arith) (by omega_arith))).writeW
    (List.mem_singleton_self _) _ (wR_contains p (by omega_arith) (by omega_arith))

theorem hMem_self (m : Mem) (p : Addr) {d : Nat} (hd : d + 24 < 2 ^ 32) (x : XReg → BitVec 128) :
    ∀ i < 3, (hMem m p d x).readW (off p (d + 8 * i)) 64 = (x (hreg i)).extractLsb' 0 64 := by
  intro i hi
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp only [hMem]
  · rw [readW_writeW_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      readW_writeW_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), Nat.mul_zero, Nat.add_zero,
      Mem.readW_writeW_self64]
  · rw [readW_writeW_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_self64]

theorem rd_sep (m : Mem) (p : Addr) {w n : Nat} (v : BitVec w) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (hn : n / 8 ≤ 16) (hk : w / 8 ≤ 16) (h : d + n / 8 ≤ e ∨ e + w / 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) n = m.readW (off p d) n :=
  Mem.readW_writeW_sep (sep_off p hd he hn hk h) (by omega_arith)

theorem hMem_other (m : Mem) (p : Addr) {d e n : Nat} (hd : d + 24 < 2 ^ 32) (he : e < 2 ^ 32) (hn : n / 8 ≤ 8)
    (h : e + n / 8 ≤ d ∨ d + 24 ≤ e) (x : XReg → BitVec 128) :
    (hMem m p d x).readW (off p e) n = m.readW (off p e) n := by
  simp only [hMem]
  rw [rd_sep _ _ _ he (by omega_arith) (by omega_arith) (by decide) (by omega_arith),
    rd_sep _ _ _ he (by omega_arith) (by omega_arith) (by decide) (by omega_arith),
    rd_sep _ _ _ he (by omega_arith) (by omega_arith) (by decide) (by omega_arith)]

/-! ## `r` into `Y` -/

/-- The limbs of `r` (in `r10` and `r11`, mask in `r8`) from `splitG`. -/
theorem split_limbs {s s' : State} (hm : s.gpr .r8 = 0xfffffffffff)
    (h₁ : s'.gpr .rax = s.gpr .r10 &&& s.gpr .r8)
    (h₂ : s'.gpr .rcx = (s.gpr .r11 <<< 20 ||| s.gpr .r10 >>> 44) &&& s.gpr .r8)
    (h₃ : s'.gpr .r9 = s.gpr .r11 >>> 24) :
    Limbs44.val (fun i => (s'.gpr (lg i)).toNat) = (s.gpr .r10).toNat + 2 ^ 64 * (s.gpr .r11).toNat ∧
      ∀ i < 3, (s'.gpr (lg i)).toNat ≤ 2 ^ 44 := by
  obtain hl := (s.gpr .r10).isLt
  obtain hh := (s.gpr .r11).isLt
  obtain e₀ : (s'.gpr .rax).toNat = (s.gpr .r10).toNat % 2 ^ 44 := by
    rw [h₁, hm, BitVec.toNat_and]; exact Limbs44.and_mask _
  obtain e₁ : (s'.gpr .rcx).toNat = (s.gpr .r10).toNat / 2 ^ 44 + 2 ^ 20 * ((s.gpr .r11).toNat % 2 ^ 24) := by
    rw [h₂, hm, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.or_comm]
    exact Limbs44.split1 hl _
  obtain e₂ : (s'.gpr .r9).toNat = (s.gpr .r11).toNat / 2 ^ 24 := by
    rw [h₃, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  refine ⟨?_, fun i hi => ?_⟩
  · show (s'.gpr .rax).toNat + 2 ^ 44 * (s'.gpr .rcx).toNat + 2 ^ 88 * (s'.gpr .r9).toNat = _
    rw [e₀, e₁, e₂]; omega_arith
  · rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · show (s'.gpr .rax).toNat ≤ _; rw [e₀]; omega_arith
    · show (s'.gpr .rcx).toNat ≤ _; rw [e₁]; omega_arith
    · show (s'.gpr .r9).toNat ≤ _; rw [e₂]; omega_arith

/-! ## `powers` -/

theorem mR2_eq : mR2 = fun i => at_ .rdi (56 + 8 * i) := rfl
theorem mR4_eq : mR4 = fun i => at_ .rdi (80 + 8 * i) := rfl

theorem powers_eq : powers = loadR ++ (splitG ++ ((bc3 ++ twenty) ++ (hOfY ++ (mul ++
    (storeH (fun i => at_ .rdi (56 + 8 * i)) ++ (((yOfH ++ twenty) ++ mul) ++
    (storeH (fun i => at_ .rdi (80 + 8 * i)) ++ (((yOfH ++ twenty) ++ mul) ++ (yOfH ++ twenty))))))))) := by
  simp only [powers, splitRg_eq, mR2_eq, mR4_eq, List.append_assoc]


/-- What `powers` leaves, from `s`. -/
structure PowPost (s s' : State) : Prop where
  r10 : s'.gpr .r10 = s.mem.readW (off (s.gpr .rdi) 24) 64 &&& M0
  r11 : s'.gpr .r11 = s.mem.readW (off (s.gpr .rdi) 32) 64 &&& M1
  r8 : s'.gpr .r8 = 0xfffffffffff
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r
  frame : Frame [wR (s.gpr .rdi)] s.mem s'.mem
  mx : s'.mem.readW (off (s.gpr .rdi) 120) 32 = s.mem.readW (off (s.gpr .rdi) 120) 32
  m : MemR (s.gpr .rdi) ((s'.gpr .r10).toNat + 2 ^ 64 * (s'.gpr .r11).toNat) s'.mem
  y : ∀ k < 8, yval s' k ≡ ((s'.gpr .r10).toNat + 2 ^ 64 * (s'.gpr .r11).toNat) ^ 8 [MOD P]
  yb : ∀ k < 8, ∀ i < 3, yv s' k i ≤ 2 ^ 44
  sr : ∀ k < 8, sv s' k 1 = 20 * yv s' k 1 ∧ sv s' k 2 = 20 * yv s' k 2
  mxcsr : s'.mxcsr = s.mxcsr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem hreg_ge : ∀ {j : Nat}, 2 ≤ j → hreg j = hreg 2
  | _ + 2, _ => rfl
theorem yreg_ge : ∀ {j : Nat}, 2 ≤ j → yreg j = yreg 2
  | _ + 2, _ => rfl
theorem sreg_ge : ∀ {j : Nat}, j ≠ 1 → sreg j = sreg 2
  | 0, _ => rfl
  | _ + 2, _ => rfl

theorem hv_of {s s' : State} (h : ∀ i < 3, ∀ k < 8, qz s' (hreg i) k = qz s (hreg i) k) :
    ∀ k < 8, hv s' k = hv s k := by
  intro k hk; funext i
  simp only [hv]
  rcases (by omega_arith : i < 3 ∨ 2 ≤ i) with hi | hi
  · rw [h i hi k hk]
  · rw [hreg_ge hi, h 2 (by decide) k hk]

theorem yv_of {s s' : State} (h : ∀ i < 3, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k) :
    ∀ k < 8, yv s' k = yv s k := by
  intro k hk; funext i
  simp only [yv]
  rcases (by omega_arith : i < 3 ∨ 2 ≤ i) with hi | hi
  · rw [h i hi k hk]
  · rw [yreg_ge hi, h 2 (by decide) k hk]

theorem sv_of {s s' : State} (h : ∀ i < 3, ∀ k < 8, qz s' (sreg i) k = qz s (sreg i) k) :
    ∀ k < 8, sv s' k = sv s k := by
  intro k hk; funext i
  simp only [sv]
  rcases (by omega_arith : i = 1 ∨ i ≠ 1) with rfl | hi
  · rw [h 1 (by decide) k hk]
  · rw [sreg_ge hi, h 2 (by decide) k hk]

theorem Ctx.of_vec {s s' : State} (h : Ctx s) (hv : vec s s' = s') : Ctx s' :=
  Ctx.of_eq h (by rw [vec_gpr hv]) (by rw [vec_gpr hv]) (vec_rd hv) (vec_wr hv)

theorem mb_of_vec {s s' : State} (h : vec s s' = s') : (envOf s').mb = (envOf s).mb := by
  funext d; simp only [envOf, Avx512.envOf, vec_gpr h, vec_mem h]

/-- A product by `Y`, with its precondition from the state it follows. -/
theorem mulY_ok {s : State} (hc : Ctx s) (hm : (envOf s).mb 104 = 0xfffffffffff)
    (hh : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 45) (hy : ∀ k < 8, ∀ i < 3, yv s k i ≤ 2 ^ 44)
    (hs : ∀ k < 8, sv s k 1 = 20 * yv s k 1 ∧ sv s k 2 = 20 * yv s k 2) :
    WP isa (.block mul) s fun s' => vec s s' = s' ∧
      (∀ k < 8, hval s' k ≡ hval s k * yval s k [MOD P]) ∧ (∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 44) ∧
      (∀ k < 8, yv s' k = yv s k) ∧ ∀ k < 8, sv s' k = sv s k := by
  obtain hp : MulPre s := ⟨hc, hm, hh, hy, fun k hk => (hs k hk).1, fun k hk => (hs k hk).2⟩
  exact WP.mono (mul_ok hp) fun s' M =>
    ⟨M.vec, fun k hk => mul_val hp M hk, M.hb, yv_of M.y, sv_of M.sr⟩

/-- Squaring: `yOfH ++ twenty`, then `mul`, with the mask in the state. -/
theorem sq_ok {s : State} (hc : Ctx s) (hm : (envOf s).mb 104 = 0xfffffffffff)
    (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44) :
    WP isa (.block ((yOfH ++ twenty) ++ mul)) s fun s' => vec s s' = s' ∧
      (∀ k < 8, hval s' k ≡ hval s k * hval s k [MOD P]) ∧ (∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 44) ∧
      (∀ k < 8, yv s' k = hv s k) ∧ ∀ k < 8, sv s' k 1 = 20 * yv s' k 1 ∧ sv s' k 2 = 20 * yv s' k 2 := by
  refine WP.block_append (WP.mono (yOfH_ok hb) fun s₁ ⟨v₁, y₁, s₁', h₁⟩ => ?_)
  obtain hh := hv_of h₁
  refine WP.mono (mulY_ok (Ctx.of_vec hc v₁) (by rw [mb_of_vec v₁, hm])
    (fun k hk i hi => by rw [hh k hk]; exact Nat.le_trans (hb k hk i hi) (by decide))
    (fun k hk i hi => by rw [y₁ k hk]; exact hb k hk i hi) s₁') fun s₂ ⟨v₂, e₂, b₂, y₂, z₂⟩ =>
    ⟨Avx2.vec_trans v₁ v₂, fun k hk => ?_, b₂, fun k hk => by rw [y₂ k hk, y₁ k hk],
      fun k hk => by rw [z₂ k hk, y₂ k hk]; exact s₁' k hk⟩
  obtain e := e₂ k hk
  simp only [hval, yval] at e ⊢
  rwa [y₁ k hk, hh k hk] at e

theorem sq_mod {a b R : Nat} {n : Nat} (h₁ : a ≡ b * b [MOD P]) (h₂ : b ≡ R ^ n [MOD P]) :
    a ≡ R ^ (n + n) [MOD P] := by
  rw [Nat.pow_add]; exact h₁.trans (h₂.mul h₂)

theorem powers_ok {s : State} (hc : Ctx s) (hw : VG.Proof.Poly1305.X86_64.sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block powers) s (PowPost s) := by
  obtain o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, VG.Proof.Poly1305.X86_64.contains_off hd (by omega_arith)⟩
  obtain i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, VG.Proof.Poly1305.X86_64.contains_off hd (by omega_arith)⟩
  rw [powers_eq]
  -- `r` and the constants.
  refine WP.block_append (WP.mono (loadR_ok s (i 24 (by decide)) (i 32 (by decide)) (o 104 (by decide))
    (o 112 (by decide))) fun s₁ ⟨r10₁, r11₁, r8₁, g₁, m₁, k₁⟩ => ?_)
  obtain rdi₁ : s₁.gpr .rdi = s.gpr .rdi := g₁ _ (by decide) (by decide) (by decide) (by decide)
  obtain rsi₁ : s₁.gpr .rsi = s.gpr .rsi := g₁ _ (by decide) (by decide) (by decide) (by decide)
  refine WP.block_append (WP.mono (splitG_ok s₁) fun s₂ ⟨a₂, c₂, n₂, g₂, m₂, k₂⟩ => ?_)
  obtain ⟨V₂, B₂⟩ := split_limbs r8₁ a₂ c₂ n₂
  refine WP.block_append (WP.mono (setY0_ok s₂) fun s₃ Y₃ => ?_)
  refine WP.block_append (WP.mono (hOfY_ok s₃) fun s₄ ⟨v₄, e₄⟩ => ?_)
  have v₃ := Y₃.vec
  -- The gpr, memory and regions through the vector code.
  obtain gv : ∀ {a b : State}, vec a b = b → b.gpr = a.gpr := fun h => vec_gpr h
  obtain rdi₄ : s₄.gpr .rdi = s.gpr .rdi := by
    rw [gv v₄, gv v₃, g₂ _ (by decide) (by decide) (by decide), rdi₁]
  obtain rsi₄ : s₄.gpr .rsi = s.gpr .rsi := by
    rw [gv v₄, gv v₃, g₂ _ (by decide) (by decide) (by decide), rsi₁]
  obtain rd₄ : s₄.rd = s.rd := by rw [vec_rd v₄, vec_rd v₃, k₂.rd, k₁.rd]
  obtain wr₄ : s₄.wr = s.wr := by rw [vec_wr v₄, vec_wr v₃, k₂.wr, k₁.wr]
  obtain mem₄ : s₄.mem = s₁.mem := by rw [vec_mem v₄, vec_mem v₃, m₂]
  obtain hc₄ : Ctx s₄ := Ctx.of_eq hc rsi₄ rdi₄ rd₄ wr₄
  obtain mask₁ : s₁.mem.readW (off (s.gpr .rdi) 104) 64 = 0xfffffffffff := by
    rw [m₁, rd_sep _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  obtain hm₄ : (envOf s₄).mb 104 = 0xfffffffffff := by
    simp only [envOf, Avx512.envOf, rdi₄, mem₄]; rw [← off, mask₁]; rfl
  -- `r` in every quadword of `H` and `Y`.
  obtain y₃ : ∀ k < 8, yv s₃ k = fun i => (s₂.gpr (lg i)).toNat := by
    intro k hk; funext i
    rcases (by omega_arith : i < 3 ∨ 2 ≤ i) with hi | hi
    · rw [Y₃.y i hi k hk]; rfl
    · have e := Y₃.y 2 (by decide) k hk
      simp only [yv] at e ⊢
      rw [yreg_ge hi, e]
      match i, hi with | _ + 2, _ => rfl
  obtain h₄ : ∀ k < 8, hv s₄ k = yv s₃ k := by
    intro k hk; funext i
    simp only [hv, yv]
    rcases (by omega_arith : i < 3 ∨ 2 ≤ i) with hi | hi
    · rw [(e₄ i hi k hk).1]
    · rw [hreg_ge hi, yreg_ge hi, (e₄ 2 (by decide) k hk).1]
  obtain yy₄ := yv_of fun i hi k hk => (e₄ i hi k hk).2.1
  obtain ss₄ := sv_of fun i hi k hk => (e₄ i hi k hk).2.2
  -- `r²`.
  refine WP.block_append (WP.mono (mulY_ok hc₄ hm₄
    (fun k hk i hi => by rw [h₄ k hk, y₃ k hk]; exact Nat.le_trans (B₂ i hi) (by decide))
    (fun k hk i hi => by rw [yy₄ k hk, y₃ k hk]; exact B₂ i hi)
    (fun k hk => by rw [ss₄ k hk, yy₄ k hk]; exact ⟨Y₃.s1 B₂ hk, Y₃.s2 B₂ hk⟩))
    fun s₅ ⟨v₅, E₅, b₅, _, _⟩ => ?_)
  obtain R₅ : ∀ k < 8, hval s₅ k ≡ ((s₁.gpr .r10).toNat + 2 ^ 64 * (s₁.gpr .r11).toNat) ^ (1 + 1) [MOD P] := by
    intro k hk
    obtain e := E₅ k hk
    simp only [hval, yval] at e
    rw [h₄ k hk, yy₄ k hk, y₃ k hk, V₂] at e
    rw [Nat.pow_add, Nat.pow_one]; exact e
  obtain rdi₅ : s₅.gpr .rdi = s.gpr .rdi := by rw [gv v₅, rdi₄]
  obtain wr₅ : s₅.wr = s.wr := by rw [vec_wr v₅, wr₄]
  refine WP.block_append (WP.mono (storeH_ok s₅ 56 fun j hj => by
    rw [wr₅, rdi₅]; exact o _ (by omega_arith)) fun s₆ ⟨g₆, m₆, k₆⟩ => ?_)
  obtain hv₆ := VKeep.hv k₆
  obtain rdi₆ : s₆.gpr .rdi = s.gpr .rdi := by rw [g₆ _ (by decide), rdi₅]
  obtain hc₆ : Ctx s₆ := Ctx.of_eq hc (by rw [g₆ _ (by decide), gv v₅, rsi₄]) rdi₆
    (by rw [k₆.rd, vec_rd v₅, rd₄]) (by rw [k₆.wr, wr₅])
  obtain mem₆ : s₆.mem = hMem s₁.mem (s.gpr .rdi) 56 s₅.xmm := by rw [m₆, vec_mem v₅, mem₄, rdi₅]
  obtain hm₆ : (envOf s₆).mb 104 = 0xfffffffffff := by
    simp only [envOf, Avx512.envOf, rdi₆, mem₆]
    rw [← off, hMem_other _ _ (by decide) (by decide) (by decide) (by decide), mask₁]; rfl
  -- `r⁴`.
  refine WP.block_append (WP.mono (sq_ok hc₆ hm₆ (fun k hk i hi => by rw [hv₆]; exact b₅ k hk i hi))
    fun s₇ ⟨v₇, E₇, b₇, _, _⟩ => ?_)
  obtain R₇ : ∀ k < 8, hval s₇ k ≡ ((s₁.gpr .r10).toNat + 2 ^ 64 * (s₁.gpr .r11).toNat) ^ (2 + 2) [MOD P] :=
    fun k hk => sq_mod (E₇ k hk) (by simp only [hval, hv₆]; exact R₅ k hk)
  obtain rdi₇ : s₇.gpr .rdi = s.gpr .rdi := by rw [gv v₇, rdi₆]
  obtain wr₇ : s₇.wr = s.wr := by rw [vec_wr v₇, k₆.wr, wr₅]
  refine WP.block_append (WP.mono (storeH_ok s₇ 80 fun j hj => by
    rw [wr₇, rdi₇]; exact o _ (by omega_arith)) fun s₈ ⟨g₈, m₈, k₈⟩ => ?_)
  obtain hv₈ := VKeep.hv k₈
  obtain rdi₈ : s₈.gpr .rdi = s.gpr .rdi := by rw [g₈ _ (by decide), rdi₇]
  obtain hc₈ : Ctx s₈ := Ctx.of_eq hc (by rw [g₈ _ (by decide), gv v₇, g₆ _ (by decide), gv v₅, rsi₄]) rdi₈
    (by rw [k₈.rd, vec_rd v₇, k₆.rd, vec_rd v₅, rd₄]) (by rw [k₈.wr, wr₇])
  obtain mem₈ : s₈.mem = hMem (hMem s₁.mem (s.gpr .rdi) 56 s₅.xmm) (s.gpr .rdi) 80 s₇.xmm := by
    rw [m₈, vec_mem v₇, mem₆, rdi₇]
  obtain hm₈ : (envOf s₈).mb 104 = 0xfffffffffff := by
    simp only [envOf, Avx512.envOf, rdi₈, mem₈]
    rw [← off, hMem_other _ _ (by decide) (by decide) (by decide) (by decide),
      hMem_other _ _ (by decide) (by decide) (by decide) (by decide), mask₁]; rfl
  -- `r⁸`, into `Y`.
  refine WP.block_append (WP.mono (sq_ok hc₈ hm₈ (fun k hk i hi => by rw [hv₈]; exact b₇ k hk i hi))
    fun s₉ ⟨v₉, E₉, b₉, _, _⟩ => ?_)
  refine WP.mono (yOfH_ok b₉) fun s₁₀ ⟨v₁₀, y₁₀, z₁₀, _⟩ => ?_
  obtain gk : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s₁₀.gpr r = s₁.gpr r := by
    intro r a c n
    rw [gv v₁₀, gv v₉, g₈ r a, gv v₇, g₆ r a, gv v₅, gv v₄, gv v₃, g₂ r a c n]
  obtain r10 : s₁₀.gpr .r10 = s₁.gpr .r10 := gk _ (by decide) (by decide) (by decide)
  obtain r11 : s₁₀.gpr .r11 = s₁.gpr .r11 := gk _ (by decide) (by decide) (by decide)
  obtain mem₁₀ : s₁₀.mem = s₈.mem := by rw [vec_mem v₁₀, vec_mem v₉]
  obtain R : ∀ k < 8, yval s₁₀ k ≡ ((s₁.gpr .r10).toNat + 2 ^ 64 * (s₁.gpr .r11).toNat) ^ (4 + 4) [MOD P] := by
    intro k hk
    simp only [yval]; rw [y₁₀ k hk]
    exact sq_mod (E₉ k hk) (by simp only [hval, hv₈]; exact R₇ k hk)
  obtain vm : ∀ {a b : State}, vec a b = b → b.mxcsr = a.mxcsr := fun h => by rw [← h]; rfl
  obtain pad₁ : s₁.mem.readW (off (s.gpr .rdi) 112) 64 = 0x10000000000 := by
    rw [m₁, Mem.readW_writeW_self64]
  obtain M2 : ∀ j < 3, ((hMem (hMem s₁.mem (s.gpr .rdi) 56 s₅.xmm) (s.gpr .rdi) 80 s₇.xmm).readW
      (off (s.gpr .rdi) (56 + 8 * j)) 64).toNat = hv s₅ 0 j := by
    intro j hj
    rw [hMem_other _ _ (by decide) (by omega_arith) (by decide) (by omega_arith), hMem_self _ _ (by decide) _ j hj]
    rfl
  obtain M4 : ∀ j < 3, ((hMem (hMem s₁.mem (s.gpr .rdi) 56 s₅.xmm) (s.gpr .rdi) 80 s₇.xmm).readW
      (off (s.gpr .rdi) (80 + 8 * j)) 64).toNat = hv s₇ 0 j := by
    intro j hj
    rw [hMem_self _ _ (by decide) _ j hj]
    rfl
  obtain F₁ : Frame [wR (s.gpr .rdi)] s.mem s₁.mem := by
    rw [m₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (wR_contains _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (wR_contains _ (by decide) (by decide))
  refine ⟨by rw [r10, r10₁], by rw [r11, r11₁], by rw [gk _ (by decide) (by decide) (by decide), r8₁],
    fun r a c e n t u => by rw [gk r a c n, g₁ r a e t u], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem₁₀, mem₈]
    exact hMem_frame (by decide) (by decide) _ (hMem_frame (by decide) (by decide) _ F₁)
  · rw [mem₁₀, mem₈, hMem_other _ _ (by decide) (by decide) (by decide) (by decide),
      hMem_other _ _ (by decide) (by decide) (by decide) (by decide), m₁,
      rd_sep _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      rd_sep _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [r10, r11, mem₁₀, mem₈]
    refine ⟨?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_, ?_⟩
    · rw [hMem_other _ _ (by decide) (by decide) (by decide) (by decide),
        hMem_other _ _ (by decide) (by decide) (by decide) (by decide), mask₁]
    · rw [hMem_other _ _ (by decide) (by decide) (by decide) (by decide),
        hMem_other _ _ (by decide) (by decide) (by decide) (by decide), pad₁]
    · rw [M2 j hj]; exact b₅ 0 (by decide) j hj
    · have e : Limbs44.val (fun i => ((hMem (hMem s₁.mem (s.gpr .rdi) 56 s₅.xmm) (s.gpr .rdi) 80 s₇.xmm).readW
          (off (s.gpr .rdi) (56 + 8 * i)) 64).toNat) = hval s₅ 0 := by
        simp only [Limbs44.val, hval]
        rw [M2 0 (by decide), M2 1 (by decide), M2 2 (by decide)]
      rw [e]; exact R₅ 0 (by decide)
    · rw [M4 j hj]; exact b₇ 0 (by decide) j hj
    · have e : Limbs44.val (fun i => ((hMem (hMem s₁.mem (s.gpr .rdi) 56 s₅.xmm) (s.gpr .rdi) 80 s₇.xmm).readW
          (off (s.gpr .rdi) (80 + 8 * i)) 64).toNat) = hval s₇ 0 := by
        simp only [Limbs44.val, hval]
        rw [M4 0 (by decide), M4 1 (by decide), M4 2 (by decide)]
      rw [e]; exact R₇ 0 (by decide)
  · intro k hk; rw [r10, r11]; exact R k hk
  · intro k hk i hi; rw [y₁₀ k hk]; exact b₉ k hk i hi
  · exact z₁₀
  · rw [vm v₁₀, vm v₉, k₈.mxcsr, vm v₇, k₆.mxcsr, vm v₅, vm v₄, vm v₃, k₂.mxcsr, k₁.mxcsr]
  · rw [vec_rd v₁₀, vec_rd v₉, k₈.rd, vec_rd v₇, k₆.rd, vec_rd v₅, rd₄]
  · rw [vec_wr v₁₀, vec_wr v₉, k₈.wr, wr₇]

end VG.Proof.Poly1305.X86_64.Ifma

end

end

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: groups of eight blocks

Each group of eight blocks but the last is added to the quadwords of `H`
(block `π k` to quadword `k`) and multiplied by `r⁸`, in `Y` (Horner's rule
in eight lanes, `Horner8.lean`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr vec_mem vec_rd vec_wr)
open VG.Proof.Poly1305.X86_64.Avx512 (qz envOf_v VKeep pi blk blk_mv blk_length group_bytes pi_0 pi_1 pi_2 pi_3
  pi_4 pi_5 pi_6 pi_7)
open VG.Spec.Poly1305 (P leNum bytesAt)
open VG.Proof.Poly1305 (mv lanes8 absorbAll)

/-- `Y` holds `R⁸` in every quadword, with `S`. -/
structure YInv (R : Nat) (s : State) : Prop where
  val : ∀ k < 8, yval s k ≡ R ^ 8 [MOD P]
  b : ∀ k < 8, ∀ i < 3, yv s k i ≤ 2 ^ 44
  sr : ∀ k < 8, sv s k 1 = 20 * yv s k 1 ∧ sv s k 2 = 20 * yv s k 2

theorem YInv.of_ys {R : Nat} {s s' : State} (h : YInv R s) (hy : ∀ k < 8, yv s' k = yv s k)
    (hs : ∀ k < 8, sv s' k = sv s k) : YInv R s' :=
  ⟨fun k hk => by simp only [yval]; rw [hy k hk]; exact h.val k hk,
   fun k hk => by rw [hy k hk]; exact h.b k hk,
   fun k hk => by rw [hs k hk, hy k hk]; exact h.sr k hk⟩

/-- The lanes of `H` weighted by the powers of `R` of the last group, in the
order of their blocks (block `j` is in quadword `2 j` for `j < 4`, else
`2 (j - 4) + 1`). -/
def wsum (R : Nat) (s : State) : Nat :=
  lanes8 R (hval s 0) (hval s 2) (hval s 4) (hval s 6) (hval s 1) (hval s 3) (hval s 5) (hval s 7)

/-- Between groups: `Y` holds `R⁸`, and the quadwords of `H` (limbs at most
`2⁴⁴`) the accumulator `X`, after Horner's rule in eight lanes. -/
structure LaneInv (R X : Nat) (s : State) : Prop where
  y : YInv R s
  hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44
  acc : wsum R s ≡ R ^ 8 * X [MOD P]

theorem LaneInv.of_vk {R X : Nat} {s s' : State} (h : LaneInv R X s) (hk : VKeep s s') : LaneInv R X s' := by
  have eh := VKeep.hv hk
  refine ⟨h.y.of_ys (fun k _ => by rw [VKeep.yv hk]) (fun k _ => by rw [VKeep.sv hk]),
    by rw [eh]; exact h.hb, ?_⟩
  simp only [wsum, hval, eh]; exact h.acc

theorem hval_add {a b c : Nat → Nat} (h : ∀ i < 3, a i = b i + c i) :
    Limbs44.val a = Limbs44.val b + Limbs44.val c := by
  simp only [Limbs44.val, h 0 (by decide), h 1 (by decide), h 2 (by decide)]
  omega_using []

/-- `addGroup`, then `mul` by `Y`: quadword `k` becomes `(V_k + m_(π k)) · Y`. -/
theorem addMul_ok {s : State} (hc : Ctx s) (hm : Consts s) (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44)
    (hy : ∀ k < 8, ∀ i < 3, yv s k i ≤ 2 ^ 44) (hs : ∀ k < 8, sv s k 1 = 20 * yv s k 1 ∧ sv s k 2 = 20 * yv s k 2) :
    WP isa (.block (addGroup ++ mul)) s fun s' => vec s s' = s' ∧
      (∀ k < 8, yv s' k = yv s k) ∧ (∀ k < 8, sv s' k = sv s k) ∧ (∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 44) ∧
      ∀ k < 8, hval s' k ≡ (hval s k + mv (blk s (pi k))) * yval s k [MOD P] := by
  refine WP.block_append (WP.mono (addGroup_ok ⟨hc, hm, hb⟩) fun s₁ A => ?_)
  have ey := yv_of A.y
  have es := sv_of A.sr
  refine WP.mono (mulY_ok (Ctx.of_vec hc A.vec) (by rw [mb_of_vec A.vec, hm.mask]) A.hb
    (fun k hk => by rw [ey k hk]; exact hy k hk) (fun k hk => by rw [es k hk, ey k hk]; exact hs k hk))
    fun s₂ ⟨v₂, E₂, b₂, y₂, z₂⟩ => ⟨vec_trans A.vec v₂, fun k hk => by rw [y₂ k hk, ey k hk],
      fun k hk => by rw [z₂ k hk, es k hk], b₂, fun k hk => ?_⟩
  have e := E₂ k hk
  simp only [hval, yval] at e ⊢
  rw [A.h k hk, ey k hk, ← blk_mv] at e
  exact e

/-- A group before the last: the invariant for the blocks so far and the group. -/
theorem group_ok {R X : Nat} {s : State} (hc : Ctx s) (hm : Consts s) (hI : LaneInv R X s) :
    WP isa (.block (addGroup ++ mul)) s fun s' => vec s s' = s' ∧
      LaneInv R (absorbAll R X (bytesAt s.mem (s.gpr .rsi) 128)) s' := by
  refine WP.mono (addMul_ok hc hm hI.hb hI.y.b hI.y.sr) fun s' ⟨hv', hy, hs, hb, he⟩ =>
    ⟨hv', hI.y.of_ys hy hs, hb, ?_⟩
  have e : ∀ k < 8, hval s' k ≡ (hval s k + mv (blk s (pi k))) * R ^ 8 [MOD P] := fun k hk =>
    (he k hk).trans (Nat.ModEq.mul_left _ (hI.y.val k hk))
  rw [group_bytes]
  have L := blk_length s
  exact Poly1305.horner8_step (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) (L 6) (L 7) hI.acc
    (by simpa only [pi_0] using e 0 (by decide)) (by simpa only [pi_2] using e 2 (by decide))
    (by simpa only [pi_4] using e 4 (by decide)) (by simpa only [pi_6] using e 6 (by decide))
    (by simpa only [pi_1] using e 1 (by decide)) (by simpa only [pi_3] using e 3 (by decide))
    (by simpa only [pi_5] using e 5 (by decide)) (by simpa only [pi_7] using e 7 (by decide))

end VG.Proof.Poly1305.X86_64.Ifma

end

end

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: the last group

The last group of eight blocks is added to `H`, and the quadwords folded in
three steps (`Impl/Poly1305/X86_64/Ifma.lean`), after which quadword 0 of `H`
is the accumulator, modulo `p`, with limbs at most `2⁴⁴`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Ifma
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Proof.Poly1305.X86_64 (off)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr vec_mem vec_rd vec_wr)
open VG.Proof.Poly1305.X86_64.Avx512 (qz envOf_v VKeep pi blk blk_mv blk_length group_bytes pi_0 pi_1 pi_2
  pi_3 pi_4 pi_5 pi_6 pi_7)
open VG.Spec.Poly1305 (P leNum bytesAt)
open VG.Proof.Poly1305 (mv absorbAll)

/-- What the blocks of the end keep: the general-purpose registers but
`rax`, `rcx` and `r9`, memory, MXCSR and the regions. -/
structure GK (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  mxcsr : s'.mxcsr = s.mxcsr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem GK.trans {s₁ s₂ s₃ : State} (h₁ : GK s₁ s₂) (h₂ : GK s₂ s₃) : GK s₁ s₃ :=
  ⟨fun r a c n => by rw [h₂.gpr r a c n, h₁.gpr r a c n], h₂.mem.trans h₁.mem, h₂.mxcsr.trans h₁.mxcsr,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem GK.of_vec {s s' : State} (h : vec s s' = s') : GK s s' :=
  ⟨fun r _ _ _ => by rw [vec_gpr h], vec_mem h, by rw [← h]; rfl, vec_rd h, vec_wr h⟩

theorem GK.of_vk {s s' : State} (hk : VKeep s s') (hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) : GK s s' :=
  ⟨hg, hm, hk.mxcsr, hk.rd, hk.wr⟩

theorem GK.ctx {s s' : State} (h : GK s s') (hc : Ctx s) : Ctx s' :=
  Ctx.of_eq hc (h.gpr _ (by decide) (by decide) (by decide)) (h.gpr _ (by decide) (by decide) (by decide))
    h.rd h.wr

/-- The value of `Y` that a block setting it leaves. -/
theorem YSet.yv_val {sel : Nat → Bool} {s s' : State} (h : YSet sel s s') {k : Nat} (hk : k < 8) :
    yval s' k = if sel k then Limbs44.val (fun i => (s.gpr (lg i)).toNat) else 1 := by
  rw [show yval s' k = yv s' k 0 + 2 ^ 44 * yv s' k 1 + 2 ^ 88 * yv s' k 2 from rfl,
    h.y 0 (by decide) k hk, h.y 1 (by decide) k hk, h.y 2 (by decide) k hk]
  split
  · rfl
  · rfl

/-- A block setting `Y` (from limbs `g` in `rax`, `rcx`, `r9`), then `mul`. -/
theorem setMul_ok {seg : List Instr} {sel : Nat → Bool} {s : State}
    (hseg : WP isa (.block seg) s (YSet sel s)) (hc : Ctx s) (hm : Consts s)
    (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 45) (hg : ∀ i < 3, (s.gpr (lg i)).toNat ≤ 2 ^ 44) :
    WP isa (.block (seg ++ mul)) s fun s' => GK s s' ∧ (∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 44) ∧
      ∀ k < 8, hval s' k ≡ hval s k * (if sel k then Limbs44.val (fun i => (s.gpr (lg i)).toNat) else 1)
        [MOD P] := by
  refine WP.block_append (WP.mono hseg fun s₁ Y => ?_)
  have eh := hv_of Y.h
  refine WP.mono (mulY_ok (Ctx.of_vec hc Y.vec) (by rw [mb_of_vec Y.vec, hm.mask])
    (fun k hk => by rw [eh k hk]; exact hb k hk) (Y.yb hg) (fun k hk => ⟨Y.s1 hg hk, Y.s2 hg hk⟩))
    fun s₂ ⟨v₂, E₂, b₂, _, _⟩ => ⟨GK.of_vec (vec_trans Y.vec v₂), b₂, fun k hk => ?_⟩
  have e := E₂ k hk
  rw [Y.yv_val hk] at e
  simp only [hval] at e ⊢
  rwa [eh k hk] at e

/-! ## The steps -/

theorem step1_eq : step1 = loadYG (fun i => at_ .rdi (80 + 8 * i)) ++
    ((bc3 ++ zeroOne ++ unpY ++ twenty) ++ mul ++ fold1) := by
  simp only [step1, loadY_eq, mR4_eq, unpY, fold1, List.append_assoc]
theorem step2_eq : step2 = splitG ++ ((bc3 ++ zeroOne ++ shY2 ++ twenty) ++ mul ++ fold2) := by
  simp only [step2, splitRg_eq, shY2, fold2, List.append_assoc]
theorem step3_eq : step3 = loadYG (fun i => at_ .rdi (56 + 8 * i)) ++
    ((bc3 ++ zeroOne ++ shY3 ++ twenty) ++ mul ++ (fold3 ++ (splitG ++ ((bc3 ++ twenty) ++ mul)))) := by
  simp only [step3, loadY_eq, mR2_eq, splitRg_eq, shY3, fold3, List.append_assoc]

/-- The registers and memory the end reads: the state at `rdi` (with `R²`
and `R⁴`), `R` in `r10` and `r11`, the mask in `r8`. -/
structure EndCtx (R : Nat) (s : State) : Prop where
  ctx : Ctx s
  m : MemR (s.gpr .rdi) R s.mem
  r : (s.gpr .r10).toNat + 2 ^ 64 * (s.gpr .r11).toNat = R
  r8 : s.gpr .r8 = 0xfffffffffff

theorem EndCtx.of_gk {R : Nat} {s s' : State} (h : EndCtx R s) (hg : GK s s') : EndCtx R s' := by
  have rdi := hg.gpr .rdi (by decide) (by decide) (by decide)
  refine ⟨hg.ctx h.ctx, by rw [rdi, hg.mem]; exact h.m, ?_, ?_⟩
  · rw [hg.gpr .r10 (by decide) (by decide) (by decide), hg.gpr .r11 (by decide) (by decide) (by decide), h.r]
  · rw [hg.gpr .r8 (by decide) (by decide) (by decide), h.r8]

theorem EndCtx.consts {R : Nat} {s : State} (h : EndCtx R s) : Consts s := h.m.consts rfl

/-- `loadYG` of `R^n`'s limbs at `rdi + d`. -/
theorem loadR_val {R n : Nat} {s : State} (d : Nat)
    (hb : ∀ i < 3, (s.mem.readW (off (s.gpr .rdi) (d + 8 * i)) 64).toNat ≤ 2 ^ 44)
    (hv : Limbs44.val (fun i => (s.mem.readW (off (s.gpr .rdi) (d + 8 * i)) 64).toNat) ≡ R ^ n [MOD P])
    {s' : State} (hg : ∀ i < 3, s'.gpr (lg i) = s.mem.readW (off (s.gpr .rdi) (d + 8 * i)) 64) :
    (∀ i < 3, (s'.gpr (lg i)).toNat ≤ 2 ^ 44) ∧
      Limbs44.val (fun i => (s'.gpr (lg i)).toNat) ≡ R ^ n [MOD P] := by
  refine ⟨fun i hi => by rw [hg i hi]; exact hb i hi, ?_⟩
  have e : Limbs44.val (fun i => (s'.gpr (lg i)).toNat) =
      Limbs44.val (fun i => (s.mem.readW (off (s.gpr .rdi) (d + 8 * i)) 64).toNat) := by
    simp only [Limbs44.val]; rw [hg 0 (by decide), hg 1 (by decide), hg 2 (by decide)]
  rw [e]; exact hv

theorem region_ok {s : State} (hc : Ctx s) (d : Nat) (h₁ : 56 ≤ d) (h₂ : d + 24 ≤ 120) :
    ∀ i < 3, InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) (d + 8 * i)) 8 := fun i hi =>
  hc.mb _ (by omega_using [h₁]) (by omega_using [h₂, hi])

/-- Step 1: quadword `2 j` becomes `H_(2j) R⁴ + H_(2j+1)`. -/
theorem step1_ok {R : Nat} {s : State} (hE : EndCtx R s) (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 45) :
    WP isa (.block step1) s fun s' => GK s s' ∧ (∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 45) ∧
      ∀ j < 4, hval s' (2 * j) ≡ hval s (2 * j) * R ^ 4 + hval s (2 * j + 1) [MOD P] := by
  rw [step1_eq]
  refine WP.block_append (WP.mono (loadYG_ok s 80 (region_ok hE.ctx 80 (by decide) (by decide)))
    fun s₁ ⟨g₁, o₁, m₁, k₁⟩ => ?_)
  have G₁ : GK s s₁ := GK.of_vk k₁ o₁ m₁
  obtain ⟨lb, lv⟩ := loadR_val 80 hE.m.r4 hE.m.r4v g₁
  have E₁ := hE.of_gk G₁
  refine WP.block_append (WP.mono (setMul_ok (setY1_ok E₁.ctx E₁.consts) E₁.ctx E₁.consts
    (fun k hk => by rw [VKeep.hv k₁]; exact hb k hk) lb) fun s₂ ⟨G₂, b₂, e₂⟩ => ?_)
  refine WP.mono (fold1_ok b₂) fun s₃ ⟨F, f⟩ => ⟨G₁.trans (G₂.trans (GK.of_vec F.vec)), F.hb, fun j hj => ?_⟩
  have a := e₂ (2 * j) (by omega_using [hj])
  have b := e₂ (2 * j + 1) (by omega_using [hj])
  rw [ite_eq_left (by simp)] at a
  rw [ite_eq_right (by simp)] at b
  simp only [hval, VKeep.hv k₁] at a b ⊢
  rw [hval_add (f j hj)]
  exact a.add (b.trans (by rw [Nat.mul_one])) |>.trans (Nat.ModEq.add_right _ (Nat.ModEq.mul_left _ lv))

/-- `splitG`'s limbs of `R`. -/
theorem splitR_val {R : Nat} {s : State} (hE : EndCtx R s) {s' : State}
    (h₁ : s'.gpr .rax = s.gpr .r10 &&& s.gpr .r8)
    (h₂ : s'.gpr .rcx = (s.gpr .r11 <<< 20 ||| s.gpr .r10 >>> 44) &&& s.gpr .r8)
    (h₃ : s'.gpr .r9 = s.gpr .r11 >>> 24) :
    (∀ i < 3, (s'.gpr (lg i)).toNat ≤ 2 ^ 44) ∧ Limbs44.val (fun i => (s'.gpr (lg i)).toNat) = R := by
  obtain ⟨v, b⟩ := split_limbs hE.r8 h₁ h₂ h₃
  exact ⟨b, by rw [v, hE.r]⟩

/-- Step 2: quadword `4 j` becomes `H_(4j) R + H_(4j+2)`. -/
theorem step2_ok {R : Nat} {s : State} (hE : EndCtx R s) (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 45) :
    WP isa (.block step2) s fun s' => GK s s' ∧ (∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 45) ∧
      ∀ j < 2, hval s' (4 * j) ≡ hval s (4 * j) * R + hval s (4 * j + 2) [MOD P] := by
  rw [step2_eq]
  refine WP.block_append (WP.mono (splitG_ok s) fun s₁ ⟨a₁, c₁, n₁, o₁, m₁, k₁⟩ => ?_)
  have G₁ : GK s s₁ := GK.of_vk k₁ o₁ m₁
  obtain ⟨lb, lv⟩ := splitR_val hE a₁ c₁ n₁
  have E₁ := hE.of_gk G₁
  refine WP.block_append (WP.mono (setMul_ok (setY2_ok E₁.ctx E₁.consts) E₁.ctx E₁.consts
    (fun k hk => by rw [VKeep.hv k₁]; exact hb k hk) lb) fun s₂ ⟨G₂, b₂, e₂⟩ => ?_)
  refine WP.mono (fold2_ok b₂) fun s₃ ⟨F, f⟩ => ⟨G₁.trans (G₂.trans (GK.of_vec F.vec)), F.hb, fun j hj => ?_⟩
  have a := e₂ (4 * j) (by omega_using [hj])
  have b := e₂ (4 * j + 2) (by omega_using [hj])
  have c₀ : ((fun k => k / 2 % 2 == 0) (4 * j)) = true := by
    rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  have c₂ : ¬((fun k => k / 2 % 2 == 0) (4 * j + 2)) = true := by
    rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl <;> decide
  rw [ite_eq_left c₀, lv] at a
  rw [ite_eq_right c₂] at b
  simp only [hval, VKeep.hv k₁] at a b ⊢
  rw [hval_add (f j hj)]
  exact a.add (b.trans (by rw [Nat.mul_one]))

/-- Step 3: quadword 0 becomes `(H₀ R² + H₄) R`. -/
theorem step3_ok {R : Nat} {s : State} (hE : EndCtx R s) (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 45) :
    WP isa (.block step3) s fun s' => GK s s' ∧ (∀ i < 3, hv s' 0 i ≤ 2 ^ 44) ∧
      hval s' 0 ≡ (hval s 0 * R ^ 2 + hval s 4) * R [MOD P] := by
  rw [step3_eq]
  refine WP.block_append (WP.mono (loadYG_ok s 56 (region_ok hE.ctx 56 (by decide) (by decide)))
    fun s₁ ⟨g₁, o₁, m₁, k₁⟩ => ?_)
  have G₁ : GK s s₁ := GK.of_vk k₁ o₁ m₁
  obtain ⟨lb, lv⟩ := loadR_val 56 hE.m.r2 hE.m.r2v g₁
  have E₁ := hE.of_gk G₁
  refine WP.block_append (WP.mono (setMul_ok (setY3_ok E₁.ctx E₁.consts) E₁.ctx E₁.consts
    (fun k hk => by rw [VKeep.hv k₁]; exact hb k hk) lb) fun s₂ ⟨G₂, b₂, e₂⟩ => ?_)
  refine WP.block_append (WP.mono (fold3_ok b₂) fun s₃ ⟨F, f⟩ => ?_)
  have G₃ : GK s s₃ := G₁.trans (G₂.trans (GK.of_vec F.vec))
  refine WP.block_append (WP.mono (splitG_ok s₃) fun s₄ ⟨a₄, c₄, n₄, o₄, m₄, k₄⟩ => ?_)
  have G₄ : GK s s₄ := G₃.trans (GK.of_vk k₄ o₄ m₄)
  obtain ⟨rb, rv⟩ := splitR_val (hE.of_gk G₃) a₄ c₄ n₄
  have E₄ := hE.of_gk G₄
  refine WP.mono (setMul_ok (setY0_ok s₄) E₄.ctx E₄.consts
    (fun k hk => by rw [VKeep.hv k₄]; exact F.hb k hk) rb) fun s₅ ⟨G₅, b₅, e₅⟩ =>
    ⟨G₄.trans G₅, b₅ 0 (by decide), ?_⟩
  have a := e₂ 0 (by decide)
  have b := e₂ 4 (by decide)
  rw [ite_eq_left (by decide)] at a
  replace a := a.trans (Nat.ModEq.mul_left _ lv)
  rw [ite_eq_right (by decide)] at b
  have c := e₅ 0 (by decide)
  rw [ite_eq_left rfl, rv] at c
  simp only [hval, VKeep.hv k₁, VKeep.hv k₄] at a b c ⊢
  rw [hval_add f] at c
  exact c.trans ((a.add (b.trans (by rw [Nat.mul_one]))).mul_right _)

/-! ## The last group -/

/-- The end's vector code: the last group added, the quadwords folded. -/
theorem last_ok {R X : Nat} {s : State} (hE : EndCtx R s) (hI : LaneInv R X s) :
    WP isa (.block (addGroup ++ step1 ++ step2 ++ step3)) s fun s' => GK s s' ∧
      (∀ i < 3, hv s' 0 i ≤ 2 ^ 44) ∧
      hval s' 0 ≡ absorbAll R X (bytesAt s.mem (s.gpr .rsi) 128) [MOD P] := by
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (addGroup_ok ⟨hE.ctx, hE.consts, hI.hb⟩) fun s₁ A => ?_)
  have G₁ : GK s s₁ := GK.of_vec A.vec
  refine WP.block_append (WP.mono (step1_ok (hE.of_gk G₁) A.hb) fun s₂ ⟨G₂, b₂, e₂⟩ => ?_)
  refine WP.block_append (WP.mono (step2_ok (hE.of_gk (G₁.trans G₂)) b₂) fun s₃ ⟨G₃, b₃, e₃⟩ => ?_)
  refine WP.mono (step3_ok (hE.of_gk ((G₁.trans G₂).trans G₃)) b₃) fun s₄ ⟨G₄, b₄, e₄⟩ =>
    ⟨((G₁.trans G₂).trans G₃).trans G₄, b₄, ?_⟩
  -- The values of the quadwords after the last group is added.
  have U : ∀ k < 8, hval s₁ k = hval s k + mv (blk s (pi k)) := fun k hk => by
    simp only [hval]; rw [A.h k hk, ← blk_mv]
  have W := e₄.trans ((((e₃ 0 (by decide)).mul_right (R ^ 2)).add (e₃ 1 (by decide))).mul_right R)
  have B := fun j hj => e₂ j hj
  have W' := W.trans (((((((B 0 (by decide)).mul_right R).add (B 1 (by decide))).mul_right (R ^ 2)).add
    (((B 2 (by decide)).mul_right R).add (B 3 (by decide)))).mul_right R))
  simp only [Nat.mul_zero, Nat.zero_add, show 2 * 2 = 4 from rfl, show 2 * 3 = 6 from rfl,
    show 2 * 1 = 2 from rfl, U 0 (by decide), U 1 (by decide), U 2 (by decide), U 3 (by decide), U 4 (by decide), U 5 (by decide),
    U 6 (by decide), U 7 (by decide), pi_0, pi_1, pi_2, pi_3, pi_4, pi_5, pi_6, pi_7] at W'
  refine W'.trans ?_
  rw [group_bytes]
  have L := blk_length s
  have H := Poly1305.horner8_last (r := R) (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) (L 6) (L 7) hI.acc
    (Nat.ModEq.refl ((hval s 0 + mv (blk s 0)) * R ^ 8)) (Nat.ModEq.refl ((hval s 2 + mv (blk s 1)) * R ^ 7))
    (Nat.ModEq.refl ((hval s 4 + mv (blk s 2)) * R ^ 6)) (Nat.ModEq.refl ((hval s 6 + mv (blk s 3)) * R ^ 5))
    (Nat.ModEq.refl ((hval s 1 + mv (blk s 4)) * R ^ 4)) (Nat.ModEq.refl ((hval s 3 + mv (blk s 5)) * R ^ 3))
    (Nat.ModEq.refl ((hval s 5 + mv (blk s 6)) * R ^ 2)) (Nat.ModEq.refl ((hval s 7 + mv (blk s 7)) * R))
  refine Nat.ModEq.trans ?_ H
  unfold Nat.ModEq
  congr 1
  ring

end VG.Proof.Poly1305.X86_64.Ifma
