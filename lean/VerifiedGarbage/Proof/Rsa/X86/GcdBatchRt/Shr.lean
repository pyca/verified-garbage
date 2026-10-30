module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatchRt
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Shr
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Linear
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Abs
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Group.Int.Defs
public import VerifiedGarbage.Proof.Weierstrass.Unch

/-! # The GCD's shift right by 30 and its matrix rows, for an odd `n`

`shr30o_ok`: `InvBatchRt.shr30_ok`'s statement for `shr30o`, its pairs then one word then the
top word; `fgRowO_ok`: a matrix row of `f` and `g`, `(u f + v g) / 2 ^ 30` (`InvBatchRt.fgRow_ok`
with `shr30o`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.GcdBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Impl.Rsa.X86.GcdBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)
open VG.Proof.Weierstrass.X86.Inv (sext32 shr_word32 wordClob)

variable {is : List Instr} {Q : State → Prop}

/-- The last low word and the top word: `shrWord 0`, both pointers up a word, then the top word
from the sign. -/
theorem shrLast_ok {s : State} {W : Addr} {Z sp dp : Nat} (hw : Ws s W Z)
    (ps : PtrAt s W .ebp sp) (pd : PtrAt s W .edi dp) (hs : sp + 8 ≤ Z) (hd : dp + 8 ≤ Z)
    (sep : dp + 8 ≤ sp ∨ sp + 8 ≤ dp)
    (k : ∀ u, w32 u.mem W dp = (w32 s.mem W sp / 2 ^ 30 + 4 * w32 s.mem W (sp + 4)) % 2 ^ 32 →
      w32 u.mem W (dp + 4) = (w32 s.mem W (sp + 4) / 2 ^ 30 +
        4 * (if 2 ^ 31 ≤ w32 s.mem W (sp + 4) then 2 ^ 32 - 1 else 0)) % 2 ^ 32 →
      Keeps [.eax, .ebx, .ecx, .ebp, .edi] s u → Outside W dp 8 s.mem u.mem → WP isa (.block is) u Q) :
    WP isa (.block (shrWord 0 ++ ([.alu .add .ebp (.imm 4), .alu .add .edi (.imm 4)] : List Instr) ++
      (([.mov .eax (.mem (at_ .ebp 0)), .shift .shr .eax 31, .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax),
      .mov .eax (.mem (at_ .ebp 0)), .mov .ebx (.reg .ecx), .shift .shr .eax 30, .alu .add .ebx (.reg .ebx),
      .alu .add .ebx (.reg .ebx), .alu .add .eax (.reg .ebx), .store (at_ .edi 0) .eax] : List Instr) ++ is))) s Q := by
  have hn := hw.nowrap
  refine shrWord_ok hw ps pd (d := 0) (by omega) (by omega) fun v₁ W₁ K₁ O₁ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_addS rfl fun v₂ U₂ _ => wp_addS rfl fun v₃ U₃ _ => ?_
  have K₃ : Keeps [.eax, .ebx, .ebp, .edi] s v₃ :=
    (K₁.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans (U₃.keeps.mono (by decide)))
  have m₃ : v₃.mem = v₁.mem := by rw [U₃.mem, U₂.mem]
  have pe₃ : PtrAt v₃ W .ebp (sp + 4) := by
    rw [PtrAt, U₃.other _ (by decide), U₂.gpr, K₁.1 _ (by decide), ptr_add ps,
      show (4 : BitVec 32).toNat = 4 from rfl]
  have pi₃ : PtrAt v₃ W .edi (dp + 4) := by
    rw [PtrAt, U₃.gpr, U₂.other _ (by decide), K₁.1 _ (by decide), ptr_add pd,
      show (4 : BitVec 32).toNat = 4 from rfl]
  have T : w32 v₃.mem W (sp + 4) = w32 s.mem W (sp + 4) := by
    rw [m₃]; exact O₁.w32 (by omega) (by omega)
  refine shrTop_ok (hw.of_keeps K₃) pe₃ pi₃ (by omega) (by omega) fun v Wv Kv Ov => ?_
  rw [T] at Wv
  refine k v ?_ Wv ((K₃.mono (by decide)).trans (Kv.mono (by decide))) ?_
  · rw [Ov.w32 (d := dp) (.inl (Nat.le_refl _)) (by omega), m₃]
    simpa only [Nat.add_zero] using W₁
  · rw [m₃] at Ov
    exact (O₁.mono (Nat.le_refl _) (by omega)).trans (Ov.mono (by omega) (by omega))

/-- The value of the shifted number from its low `k` words, one more and the top word. -/
theorem shr_close {m₀ m : Mem} {W : Addr} {dst src k : Nat}
    (V : val32 m W dst k = val32 m₀ W src (k + 1) / 2 ^ 30 % 2 ^ (32 * k))
    (Wd : w32 m W (dst + 4 * k) =
      (w32 m₀ W (src + 4 * k) / 2 ^ 30 + 4 * w32 m₀ W (src + 4 * k + 4)) % 2 ^ 32)
    (Wt : w32 m W (dst + 4 * k + 4) = (w32 m₀ W (src + 4 * k + 4) / 2 ^ 30 +
        4 * (if 2 ^ 31 ≤ w32 m₀ W (src + 4 * k + 4) then 2 ^ 32 - 1 else 0)) % 2 ^ 32) :
    val32 m W dst (k + 2) = sext32 m₀ W src (k + 2) / 2 ^ 30 % 2 ^ (32 * (k + 2)) := by
  have V₁ : val32 m W dst (k + 1) = val32 m₀ W src (k + 2) / 2 ^ 30 % 2 ^ (32 * (k + 1)) :=
    shr_succ V Wd rfl
  rw [val32_succ m W dst (k + 1), V₁, show dst + 4 * (k + 1) = dst + 4 * k + 4 by omega, Wt]
  simp only [sext32, show k + 2 - 1 = k + 1 by omega, show k + 2 = k + 1 + 1 by omega]
  rw [show src + 4 * k + 4 = src + 4 * (k + 1) by omega]
  generalize k + 1 = n
  rw [val32_succ m₀ W src n, pow32_succ, Nat.mul_comm (2 ^ 32) (2 ^ (32 * n))]
  have := VG.Proof.Weierstrass.X86.Inv.shr_arith32 n (val32 m₀ W src n) (w32 m₀ W (src + 4 * n))
    (if 2 ^ 31 ≤ w32 m₀ W (src + 4 * n) then 2 ^ 32 - 1 else 0) (val32_lt _ _ _ _)
  rw [show (2 : Nat) ^ 2 = 4 from rfl] at this
  rw [this]

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- `shr30o dst src`: `[dst] = [src] >> 30`, signed, `n + 1` words for an odd `n`. -/
theorem shr30o_ok {s : State} (h : Bx L s B Z len N) {dst src : Ref} (hdh : dst.half = 0)
    (hodd : nw len % 2 = 1) (h3 : 3 ≤ nw len) (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z)
    (hdz : rv (kw len) dst + 4 * (nw len + 1) ≤ Z)
    (sep : rv (kw len) dst + 4 * (nw len + 1) ≤ rv (kw len) src ∨ rv (kw len) src + 4 * (nw len + 1) ≤ rv (kw len) dst) :
    WP isa (shr30o L dst src) s fun u =>
      Bx L u B Z len N ∧
      val32 u.mem B (rv (kw len) dst) (nw len + 1) = sext32 s.mem B (rv (kw len) src) (nw len + 1) / 2 ^ 30 %
        2 ^ (32 * (nw len + 1)) ∧
      Keeps wordClob s u ∧ Outside B (rv (kw len) dst) (4 * (nw len + 1)) s.mem u.mem := by
  have hn := h.nowrap
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have hZ := h.halfZ
  have rd := rv_ge (kw len) dst
  unfold shr30o
  rw [show ptr L .edi dst .edx = ptr L .edi dst .edx ++ [] from (List.append_nil _).symm]
  simp only [List.append_assoc]
  refine WP.seq (ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega_arith) fun u₁ K₁ m₁ p₁ => ?_)
  have h₁ : Bx L u₁ B Z len N := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _) rd hdz
  refine nBytesLess_ok h₁.ws.ws.workspace h₁.slots hZ (by omega_arith) (by omega_arith) fun u₂ K₂ m₂ c₂ => ?_
  have h₂ : Bx L u₂ B Z len N := h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _) rd hdz
  refine ptr_ok h₂.ws h₂.slots hZ (by decide) (by decide) (by decide) (by decide) (fun _ => hdh)
    (by omega_arith) fun u K₃ m₃ p₃ => WP.block_nil ?_
  have K : Keeps [.ebx, .edx, .ebp, .edi, .esi] s u :=
    ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))
  have m : u.mem = s.mem := by rw [m₃, m₂, m₁]
  have hwu := h.ws.rt.of_keeps K
  refine WP.seq (WP.mono (shrPairs_ok hwu (sp := rv (kw len) src) (dp := rv (kw len) dst) (n := nw len - 1) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by rw [PtrAt, K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁) p₃
    (by rw [K₃.1 _ (by decide), c₂]; omega)) fun t ⟨Kt, pe, pi, _, Ot, Vt⟩ => ?_)
  rw [show 2 * ((nw len - 1) / 2) = nw len - 1 by omega_arith, show 8 * ((nw len - 1) / 2) = 4 * (nw len - 1) by omega_arith,
    show nw len - 1 + 1 = nw len by omega_arith] at *
  have ht := hwu.of_keeps Kt
  -- The last low word and the top word.
  refine shrLast_ok ht pe pi (by omega_arith) (by omega_arith) (by omega_arith) fun v Wd Wt Kv Ov => ?_
  -- `edi` back.
  have KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s v :=
    ((K.mono (by decide)).trans (Kt.mono (by decide))).trans (Kv.mono (by decide))
  have Ofull : Outside B (rv (kw len) dst) (4 * (nw len + 1)) s.mem v.mem := by
    rw [← m]
    exact (Ot.mono (Nat.le_refl _) (by omega_arith)).trans (Ov.mono (by omega_arith) (by omega_arith))
  have O0 : Outside B 0 Z s.mem v.mem := Ofull.mono (Nat.zero_le _) (by omega_arith)
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  have K' : Keeps wordClob s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := wordClob)
      ((KK.mono (by decide)).trans (U.keeps.mono (by decide))) (U.gpr.trans (RtWs.edi_eq h.ws).symm)
  refine ⟨h.keep K' (by decide) (by decide) (by rw [U.mem]; exact Ofull) rd hdz, ?_, K', by rw [U.mem]; exact Ofull⟩
  -- The value.
  have S : ∀ d, rv (kw len) src ≤ d → d + 4 ≤ rv (kw len) src + 4 * (nw len + 1) →
      w32 t.mem B d = w32 s.mem B d :=
    fun d h₁ h₂ => by rw [Ot.w32 (by omega_arith) (by omega_arith), m]
  rw [S _ (by omega_arith) (by omega_arith), S _ (by omega_arith) (by omega_arith)] at Wd
  rw [S _ (by omega_arith) (by omega_arith)] at Wt
  rw [U.mem]
  have V' : val32 v.mem B (rv (kw len) dst) (nw len - 1) =
      val32 s.mem B (rv (kw len) src) (nw len - 1 + 1) / 2 ^ 30 % 2 ^ (32 * (nw len - 1)) := by
    rw [Ov.val32 (.inl (Nat.le_refl _)) (by omega_arith), ← m, show nw len - 1 + 1 = nw len by omega_arith]
    exact Vt
  have E := shr_close V' Wd Wt
  rwa [show nw len - 1 + 2 = nw len + 1 by omega_arith] at E

/-- `shr30o` of a signed value divisible by `2 ^ 30`. -/
theorem shrSignedO_ok {s : State} (h : Bx L s B Z len N) {dst src : Ref} (hdh : dst.half = 0)
    (hodd : nw len % 2 = 1) (h3 : 3 ≤ nw len) (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z)
    (hdz : rv (kw len) dst + 4 * (nw len + 1) ≤ Z)
    (sep : rv (kw len) dst + 4 * (nw len + 1) ≤ rv (kw len) src ∨ rv (kw len) src + 4 * (nw len + 1) ≤ rv (kw len) dst)
    {y z : Int}
    (hy : (val32 s.mem B (rv (kw len) src) (nw len + 1) : Int) % ((2 ^ (32 * (nw len + 1)) : Nat) : Int) =
      y % ((2 ^ (32 * (nw len + 1)) : Nat) : Int))
    (hy1 : -((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) ≤ y)
    (hy2 : y < ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int)) (hz : y = 2 ^ 30 * z) :
    WP isa (shr30o L dst src) s fun u =>
      Bx L u B Z len N ∧
      (val32 u.mem B (rv (kw len) dst) (nw len + 1) : Int) % ((2 ^ (32 * (nw len + 1)) : Nat) : Int) =
        z % ((2 ^ (32 * (nw len + 1)) : Nat) : Int) ∧
      Keeps wordClob s u ∧ Outside B (rv (kw len) dst) (4 * (nw len + 1)) s.mem u.mem := by
  refine WP.mono (shr30o_ok h hdh hodd h3 hsz hdz sep) fun u ⟨Bu, V, K, O⟩ => ⟨Bu, ?_, K, O⟩
  have Q : 2 ^ (32 * (nw len + 1)) = 2 * (2 ^ (32 * nw len) * 2 ^ 31) := by
    rw [pow32_succ]; omega
  simp only [sext32, Nat.add_sub_cancel, VG.Proof.Weierstrass.X86.Inv.sign32, Q] at V
  rw [Q] at hy ⊢
  exact Divstep.W32.shr_nat (c := 2 ^ 30) (B := 2 ^ 32) rfl rfl
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (by have := val32_lt s.mem B (rv (kw len) src) (nw len + 1); rw [Q] at this; exact this) hy hy1 hy2 hz V


/-- A matrix row of `f` and `g`: `[a j] = (u f + v g) / 2 ^ 30`, `n + 1` words. -/
theorem fgRowO_ok {s : State} (h : Bx L s B Z len N) (hodd : nw len % 2 = 1) (h3 : 3 ≤ nw len) {u v j : Nat}
    (hu4 : u + 4 ≤ 160) (hv4 : v + 4 ≤ 160) (hj : j < 11) {cu cv f g : Int} {p : Nat}
    (hu : s.mem.readW (off B u) 32 = BitVec.ofInt 32 cu) (hv : s.mem.readW (off B v) 32 = BitVec.ofInt 32 cv)
    (huv : |cu| + |cv| ≤ 2 ^ 30)
    (hf : (val32 s.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      f % 2 ^ (32 * (nw len + 1)))
    (hg : (val32 s.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      g % 2 ^ (32 * (nw len + 1)))
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ (32 * nw len + 1)) (hdiv : 2 ^ 30 ∣ cu * f + cv * g) :
    WP isa (.seq (linear L u v (a 11) (a 4) (a 5) (a 12) 1) (shr30o L (a j) (a 11))) s fun z =>
      Bx L z B Z len N ∧
      (val32 z.mem B (rv (kw len) (a j)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
        ((cu * f + cv * g) / 2 ^ 30) % 2 ^ (32 * (nw len + 1)) ∧
      Keeps wordClob s z ∧
      Unch B [(rv (kw len) (a 11), 4 * (nw len + 3)), (rv (kw len) (a 12), 4 * nw len),
        (rv (kw len) (a j), 4 * (nw len + 1))] s.mem z.mem := by
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  have r4 := rv_a len 4; have r5 := rv_a len 5; have r11 := rv_a len 11; have r12 := rv_a len 12
  have rj := rv_a len j
  have hjb := Nat.mul_le_mul_right (8 * nw len + 8) (show j ≤ 10 by omega)
  refine WP.seq (WP.mono (linear_ok h (e := 1) (tmp := a 12) hu4 hv4 (by decide) rfl rfl rfl
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₁ ⟨H₁, U₁, K₁, V₁⟩ => ?_)
  rw [hu, hv, Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv),
    Divstep.W32.cong_comb hf hg] at V₁
  have hcomb := Divstep.W32.comb_le huv hfb hgb
  have hpI : (p : Int) < 2 ^ (32 * nw len) * 2 := by
    exact_mod_cast (by simpa only [Nat.pow_succ] using hp)
  have cap : ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) = (2 : Int) ^ (32 * nw len) * 2 ^ 31 := by
    push_cast; rfl
  have lo : -((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) ≤ cu * f + cv * g := by
    rw [cap]; have := neg_abs_le (cu * f + cv * g); linarith
  have hi : cu * f + cv * g < ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) := by
    rw [cap]; have := le_abs_self (cu * f + cv * g); linarith
  refine WP.mono (shrSignedO_ok H₁ (dst := a j) (src := a 11) rfl hodd h3 (by omega) (by omega) (by omega)
    (by exact_mod_cast V₁) lo hi (Int.mul_ediv_cancel' hdiv).symm)
    fun z ⟨Hz, V, K, O⟩ => ⟨Hz, by exact_mod_cast V, (K₁.mono (by decide)).trans (K.mono (by decide)), ?_⟩
  intro x hx
  rw [O x (hx (rv (kw len) (a j), 4 * (nw len + 1)) (by simp)), U₁ x (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hx (rv (kw len) (a 11), 4 * (nw len + 3)) (by simp)
    · exact hx (rv (kw len) (a 12), 4 * nw len) (by simp))]

end VG.Proof.Rsa.X86.GcdBatchRt
