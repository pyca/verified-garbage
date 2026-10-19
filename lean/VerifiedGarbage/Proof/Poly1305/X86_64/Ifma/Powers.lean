module

public import Mathlib.Data.Nat.ModEq
public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Gpr
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Mul

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
  have e : hv s' k = Limbs44.mul (hv s k) (yv s k) (sv s k) := by
    funext i
    rcases (by omega : i < 3 ∨ 3 ≤ i) with hi | hi
    · exact h.h k hk i hi
    · have e : ∀ {j}, 2 ≤ j → hreg j = hreg 2 := fun {j} hj => by match j, hj with | _ + 2, _ => rfl
      have e2 := h.h k hk 2 (by decide)
      simp only [hv] at e2 ⊢
      rw [e (by omega), e2]
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
  exact ((hf.writeW (List.mem_singleton_self _) _ (wR_contains p h₁ (by omega))).writeW
    (List.mem_singleton_self _) _ (wR_contains p (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (wR_contains p (by omega) (by omega))

theorem hMem_self (m : Mem) (p : Addr) {d : Nat} (hd : d + 24 < 2 ^ 32) (x : XReg → BitVec 128) :
    ∀ i < 3, (hMem m p d x).readW (off p (d + 8 * i)) 64 = (x (hreg i)).extractLsb' 0 64 := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp only [hMem]
  · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Nat.mul_zero, Nat.add_zero,
      Mem.readW_writeW_self64]
  · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_self64]

theorem rd_sep (m : Mem) (p : Addr) {w n : Nat} (v : BitVec w) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (hn : n / 8 ≤ 16) (hk : w / 8 ≤ 16) (h : d + n / 8 ≤ e ∨ e + w / 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) n = m.readW (off p d) n :=
  Mem.readW_writeW_sep (sep_off p hd he hn hk h) (by omega)

theorem hMem_other (m : Mem) (p : Addr) {d e n : Nat} (hd : d + 24 < 2 ^ 32) (he : e < 2 ^ 32) (hn : n / 8 ≤ 8)
    (h : e + n / 8 ≤ d ∨ d + 24 ≤ e) (x : XReg → BitVec 128) :
    (hMem m p d x).readW (off p e) n = m.readW (off p e) n := by
  simp only [hMem]
  rw [rd_sep _ _ _ he (by omega) (by omega) (by decide) (by omega),
    rd_sep _ _ _ he (by omega) (by omega) (by decide) (by omega),
    rd_sep _ _ _ he (by omega) (by omega) (by decide) (by omega)]

/-! ## `r` into `Y` -/

/-- The limbs of `r` (in `r10` and `r11`, mask in `r8`) from `splitG`. -/
theorem split_limbs {s s' : State} (hm : s.gpr .r8 = 0xfffffffffff)
    (h₁ : s'.gpr .rax = s.gpr .r10 &&& s.gpr .r8)
    (h₂ : s'.gpr .rcx = (s.gpr .r11 <<< 20 ||| s.gpr .r10 >>> 44) &&& s.gpr .r8)
    (h₃ : s'.gpr .r9 = s.gpr .r11 >>> 24) :
    Limbs44.val (fun i => (s'.gpr (lg i)).toNat) = (s.gpr .r10).toNat + 2 ^ 64 * (s.gpr .r11).toNat ∧
      ∀ i < 3, (s'.gpr (lg i)).toNat ≤ 2 ^ 44 := by
  have hl := (s.gpr .r10).isLt
  have hh := (s.gpr .r11).isLt
  have e₀ : (s'.gpr .rax).toNat = (s.gpr .r10).toNat % 2 ^ 44 := by
    rw [h₁, hm, BitVec.toNat_and]; exact Limbs44.and_mask _
  have e₁ : (s'.gpr .rcx).toNat = (s.gpr .r10).toNat / 2 ^ 44 + 2 ^ 20 * ((s.gpr .r11).toNat % 2 ^ 24) := by
    rw [h₂, hm, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.or_comm]
    exact Limbs44.split1 hl _
  have e₂ : (s'.gpr .r9).toNat = (s.gpr .r11).toNat / 2 ^ 24 := by
    rw [h₃, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  refine ⟨?_, fun i hi => ?_⟩
  · show (s'.gpr .rax).toNat + 2 ^ 44 * (s'.gpr .rcx).toNat + 2 ^ 88 * (s'.gpr .r9).toNat = _
    rw [e₀, e₁, e₂]; omega
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · show (s'.gpr .rax).toNat ≤ _; rw [e₀]; omega
    · show (s'.gpr .rcx).toNat ≤ _; rw [e₁]; omega
    · show (s'.gpr .r9).toNat ≤ _; rw [e₂]; omega

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
  rcases (by omega : i < 3 ∨ 2 ≤ i) with hi | hi
  · rw [h i hi k hk]
  · rw [hreg_ge hi, h 2 (by decide) k hk]

theorem yv_of {s s' : State} (h : ∀ i < 3, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k) :
    ∀ k < 8, yv s' k = yv s k := by
  intro k hk; funext i
  simp only [yv]
  rcases (by omega : i < 3 ∨ 2 ≤ i) with hi | hi
  · rw [h i hi k hk]
  · rw [yreg_ge hi, h 2 (by decide) k hk]

theorem sv_of {s s' : State} (h : ∀ i < 3, ∀ k < 8, qz s' (sreg i) k = qz s (sreg i) k) :
    ∀ k < 8, sv s' k = sv s k := by
  intro k hk; funext i
  simp only [sv]
  rcases (by omega : i = 1 ∨ i ≠ 1) with rfl | hi
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
  have hp : MulPre s := ⟨hc, hm, hh, hy, fun k hk => (hs k hk).1, fun k hk => (hs k hk).2⟩
  exact WP.mono (mul_ok hp) fun s' M =>
    ⟨M.vec, fun k hk => mul_val hp M hk, M.hb, yv_of M.y, sv_of M.sr⟩

/-- Squaring: `yOfH ++ twenty`, then `mul`, with the mask in the state. -/
theorem sq_ok {s : State} (hc : Ctx s) (hm : (envOf s).mb 104 = 0xfffffffffff)
    (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44) :
    WP isa (.block ((yOfH ++ twenty) ++ mul)) s fun s' => vec s s' = s' ∧
      (∀ k < 8, hval s' k ≡ hval s k * hval s k [MOD P]) ∧ (∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 44) ∧
      (∀ k < 8, yv s' k = hv s k) ∧ ∀ k < 8, sv s' k 1 = 20 * yv s' k 1 ∧ sv s' k 2 = 20 * yv s' k 2 := by
  refine WP.block_append (WP.mono (yOfH_ok hb) fun s₁ ⟨v₁, y₁, s₁', h₁⟩ => ?_)
  have hh := hv_of h₁
  refine WP.mono (mulY_ok (Ctx.of_vec hc v₁) (by rw [mb_of_vec v₁, hm])
    (fun k hk i hi => by rw [hh k hk]; exact Nat.le_trans (hb k hk i hi) (by decide))
    (fun k hk i hi => by rw [y₁ k hk]; exact hb k hk i hi) s₁') fun s₂ ⟨v₂, e₂, b₂, y₂, z₂⟩ =>
    ⟨Avx2.vec_trans v₁ v₂, fun k hk => ?_, b₂, fun k hk => by rw [y₂ k hk, y₁ k hk],
      fun k hk => by rw [z₂ k hk, y₂ k hk]; exact s₁' k hk⟩
  have e := e₂ k hk
  simp only [hval, yval] at e ⊢
  rwa [y₁ k hk, hh k hk] at e

theorem qz_0 (s : State) (r : XReg) : qz s r 0 = (s.xmm r).extractLsb' 0 64 := rfl

theorem sq_mod {a b R : Nat} {n : Nat} (h₁ : a ≡ b * b [MOD P]) (h₂ : b ≡ R ^ n [MOD P]) :
    a ≡ R ^ (n + n) [MOD P] := by
  rw [Nat.pow_add]; exact h₁.trans (h₂.mul h₂)

theorem powers_ok {s : State} (hc : Ctx s) (hw : VG.Proof.Poly1305.X86_64.sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block powers) s (PowPost s) := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, VG.Proof.Poly1305.X86_64.contains_off hd (by omega)⟩
  have i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, VG.Proof.Poly1305.X86_64.contains_off hd (by omega)⟩
  rw [powers_eq]
  -- `r` and the constants.
  refine WP.block_append (WP.mono (loadR_ok s (i 24 (by decide)) (i 32 (by decide)) (o 104 (by decide))
    (o 112 (by decide))) fun s₁ ⟨r10₁, r11₁, r8₁, g₁, m₁, k₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = s.gpr .rdi := g₁ _ (by decide) (by decide) (by decide) (by decide)
  have rsi₁ : s₁.gpr .rsi = s.gpr .rsi := g₁ _ (by decide) (by decide) (by decide) (by decide)
  refine WP.block_append (WP.mono (splitG_ok s₁) fun s₂ ⟨a₂, c₂, n₂, g₂, m₂, k₂⟩ => ?_)
  obtain ⟨V₂, B₂⟩ := split_limbs r8₁ a₂ c₂ n₂
  refine WP.block_append (WP.mono (setY0_ok s₂) fun s₃ Y₃ => ?_)
  refine WP.block_append (WP.mono (hOfY_ok s₃) fun s₄ ⟨v₄, e₄⟩ => ?_)
  have v₃ := Y₃.vec
  -- The gpr, memory and regions through the vector code.
  have gv : ∀ {a b : State}, vec a b = b → b.gpr = a.gpr := fun h => vec_gpr h
  have rdi₄ : s₄.gpr .rdi = s.gpr .rdi := by
    rw [gv v₄, gv v₃, g₂ _ (by decide) (by decide) (by decide), rdi₁]
  have rsi₄ : s₄.gpr .rsi = s.gpr .rsi := by
    rw [gv v₄, gv v₃, g₂ _ (by decide) (by decide) (by decide), rsi₁]
  have rd₄ : s₄.rd = s.rd := by rw [vec_rd v₄, vec_rd v₃, k₂.rd, k₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [vec_wr v₄, vec_wr v₃, k₂.wr, k₁.wr]
  have mem₄ : s₄.mem = s₁.mem := by rw [vec_mem v₄, vec_mem v₃, m₂]
  have hc₄ : Ctx s₄ := Ctx.of_eq hc rsi₄ rdi₄ rd₄ wr₄
  have mask₁ : s₁.mem.readW (off (s.gpr .rdi) 104) 64 = 0xfffffffffff := by
    rw [m₁, rd_sep _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  have hm₄ : (envOf s₄).mb 104 = 0xfffffffffff := by
    simp only [envOf, Avx512.envOf, rdi₄, mem₄]; rw [← off, mask₁]; rfl
  -- `r` in every quadword of `H` and `Y`.
  have y₃ : ∀ k < 8, yv s₃ k = fun i => (s₂.gpr (lg i)).toNat := by
    intro k hk; funext i
    rcases (by omega : i < 3 ∨ 2 ≤ i) with hi | hi
    · rw [Y₃.y i hi k hk]; rfl
    · have e := Y₃.y 2 (by decide) k hk
      simp only [yv] at e ⊢
      rw [yreg_ge hi, e]
      match i, hi with | _ + 2, _ => rfl
  have h₄ : ∀ k < 8, hv s₄ k = yv s₃ k := by
    intro k hk; funext i
    simp only [hv, yv]
    rcases (by omega : i < 3 ∨ 2 ≤ i) with hi | hi
    · rw [(e₄ i hi k hk).1]
    · rw [hreg_ge hi, yreg_ge hi, (e₄ 2 (by decide) k hk).1]
  have yy₄ := yv_of fun i hi k hk => (e₄ i hi k hk).2.1
  have ss₄ := sv_of fun i hi k hk => (e₄ i hi k hk).2.2
  -- `r²`.
  refine WP.block_append (WP.mono (mulY_ok hc₄ hm₄
    (fun k hk i hi => by rw [h₄ k hk, y₃ k hk]; exact Nat.le_trans (B₂ i hi) (by decide))
    (fun k hk i hi => by rw [yy₄ k hk, y₃ k hk]; exact B₂ i hi)
    (fun k hk => by rw [ss₄ k hk, yy₄ k hk]; exact ⟨Y₃.s1 B₂ hk, Y₃.s2 B₂ hk⟩))
    fun s₅ ⟨v₅, E₅, b₅, _, _⟩ => ?_)
  have R₅ : ∀ k < 8, hval s₅ k ≡ ((s₁.gpr .r10).toNat + 2 ^ 64 * (s₁.gpr .r11).toNat) ^ (1 + 1) [MOD P] := by
    intro k hk
    have e := E₅ k hk
    simp only [hval, yval] at e
    rw [h₄ k hk, yy₄ k hk, y₃ k hk, V₂] at e
    rw [Nat.pow_add, Nat.pow_one]; exact e
  have rdi₅ : s₅.gpr .rdi = s.gpr .rdi := by rw [gv v₅, rdi₄]
  have wr₅ : s₅.wr = s.wr := by rw [vec_wr v₅, wr₄]
  refine WP.block_append (WP.mono (storeH_ok s₅ 56 fun j hj => by
    rw [wr₅, rdi₅]; exact o _ (by omega)) fun s₆ ⟨g₆, m₆, k₆⟩ => ?_)
  have hv₆ := VKeep.hv k₆
  have rdi₆ : s₆.gpr .rdi = s.gpr .rdi := by rw [g₆ _ (by decide), rdi₅]
  have hc₆ : Ctx s₆ := Ctx.of_eq hc (by rw [g₆ _ (by decide), gv v₅, rsi₄]) rdi₆
    (by rw [k₆.rd, vec_rd v₅, rd₄]) (by rw [k₆.wr, wr₅])
  have mem₆ : s₆.mem = hMem s₁.mem (s.gpr .rdi) 56 s₅.xmm := by rw [m₆, vec_mem v₅, mem₄, rdi₅]
  have hm₆ : (envOf s₆).mb 104 = 0xfffffffffff := by
    simp only [envOf, Avx512.envOf, rdi₆, mem₆]
    rw [← off, hMem_other _ _ (by decide) (by decide) (by decide) (by decide), mask₁]; rfl
  -- `r⁴`.
  refine WP.block_append (WP.mono (sq_ok hc₆ hm₆ (fun k hk i hi => by rw [hv₆]; exact b₅ k hk i hi))
    fun s₇ ⟨v₇, E₇, b₇, _, _⟩ => ?_)
  have R₇ : ∀ k < 8, hval s₇ k ≡ ((s₁.gpr .r10).toNat + 2 ^ 64 * (s₁.gpr .r11).toNat) ^ (2 + 2) [MOD P] :=
    fun k hk => sq_mod (E₇ k hk) (by simp only [hval, hv₆]; exact R₅ k hk)
  have rdi₇ : s₇.gpr .rdi = s.gpr .rdi := by rw [gv v₇, rdi₆]
  have wr₇ : s₇.wr = s.wr := by rw [vec_wr v₇, k₆.wr, wr₅]
  refine WP.block_append (WP.mono (storeH_ok s₇ 80 fun j hj => by
    rw [wr₇, rdi₇]; exact o _ (by omega)) fun s₈ ⟨g₈, m₈, k₈⟩ => ?_)
  have hv₈ := VKeep.hv k₈
  have rdi₈ : s₈.gpr .rdi = s.gpr .rdi := by rw [g₈ _ (by decide), rdi₇]
  have hc₈ : Ctx s₈ := Ctx.of_eq hc (by rw [g₈ _ (by decide), gv v₇, g₆ _ (by decide), gv v₅, rsi₄]) rdi₈
    (by rw [k₈.rd, vec_rd v₇, k₆.rd, vec_rd v₅, rd₄]) (by rw [k₈.wr, wr₇])
  have mem₈ : s₈.mem = hMem (hMem s₁.mem (s.gpr .rdi) 56 s₅.xmm) (s.gpr .rdi) 80 s₇.xmm := by
    rw [m₈, vec_mem v₇, mem₆, rdi₇]
  have hm₈ : (envOf s₈).mb 104 = 0xfffffffffff := by
    simp only [envOf, Avx512.envOf, rdi₈, mem₈]
    rw [← off, hMem_other _ _ (by decide) (by decide) (by decide) (by decide),
      hMem_other _ _ (by decide) (by decide) (by decide) (by decide), mask₁]; rfl
  -- `r⁸`, into `Y`.
  refine WP.block_append (WP.mono (sq_ok hc₈ hm₈ (fun k hk i hi => by rw [hv₈]; exact b₇ k hk i hi))
    fun s₉ ⟨v₉, E₉, b₉, _, _⟩ => ?_)
  refine WP.mono (yOfH_ok b₉) fun s₁₀ ⟨v₁₀, y₁₀, z₁₀, _⟩ => ?_
  have gk : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s₁₀.gpr r = s₁.gpr r := by
    intro r a c n
    rw [gv v₁₀, gv v₉, g₈ r a, gv v₇, g₆ r a, gv v₅, gv v₄, gv v₃, g₂ r a c n]
  have r10 : s₁₀.gpr .r10 = s₁.gpr .r10 := gk _ (by decide) (by decide) (by decide)
  have r11 : s₁₀.gpr .r11 = s₁.gpr .r11 := gk _ (by decide) (by decide) (by decide)
  have mem₁₀ : s₁₀.mem = s₈.mem := by rw [vec_mem v₁₀, vec_mem v₉]
  have R : ∀ k < 8, yval s₁₀ k ≡ ((s₁.gpr .r10).toNat + 2 ^ 64 * (s₁.gpr .r11).toNat) ^ (4 + 4) [MOD P] := by
    intro k hk
    simp only [yval]; rw [y₁₀ k hk]
    exact sq_mod (E₉ k hk) (by simp only [hval, hv₈]; exact R₇ k hk)
  have vm : ∀ {a b : State}, vec a b = b → b.mxcsr = a.mxcsr := fun h => by rw [← h]; rfl
  have pad₁ : s₁.mem.readW (off (s.gpr .rdi) 112) 64 = 0x10000000000 := by
    rw [m₁, Mem.readW_writeW_self64]
  have M2 : ∀ j < 3, ((hMem (hMem s₁.mem (s.gpr .rdi) 56 s₅.xmm) (s.gpr .rdi) 80 s₇.xmm).readW
      (off (s.gpr .rdi) (56 + 8 * j)) 64).toNat = hv s₅ 0 j := by
    intro j hj
    rw [hMem_other _ _ (by decide) (by omega) (by decide) (by omega), hMem_self _ _ (by decide) _ j hj]
    rfl
  have M4 : ∀ j < 3, ((hMem (hMem s₁.mem (s.gpr .rdi) 56 s₅.xmm) (s.gpr .rdi) 80 s₇.xmm).readW
      (off (s.gpr .rdi) (80 + 8 * j)) 64).toNat = hv s₇ 0 j := by
    intro j hj
    rw [hMem_self _ _ (by decide) _ j hj]
    rfl
  have F₁ : Frame [wR (s.gpr .rdi)] s.mem s₁.mem := by
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
