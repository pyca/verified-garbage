module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatchRt
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Shr
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.RowOp
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Weierstrass.X86.InvLinear
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Abs
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedMath
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Group.Int.Defs

/-! ### `Rsa.X86.InvBatchRt.Linear`, which only this module used -/

section

/-! # The signed linear combination at a run-time width

`correction_ok`: `[acc + 4] -= [src]`, `n` words, if the coefficient at a header
word is negative, as the difference into `[tmp]` selected into place, with
`InvMemory.correction`'s statement; `linear_ok`: `InvMemory.linear`'s signed
combination modulo `n + 1` words, with its statement.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- The correction: `[acc + 4] -= [src]` (`n` words) if the coefficient at `c` is negative. -/
theorem correction_ok {s : State} (h : Bx L s B Z len N) {c : Nat} (hc : c + 4 ≤ 160)
    {acc src tmp : Ref} (hth : tmp.half = 0)
    (haz : rv (kw len) acc + 4 * (nw len + 1) ≤ Z) (hsz : rv (kw len) src + 4 * nw len ≤ Z)
    (htz : rv (kw len) tmp + 4 * nw len ≤ Z)
    (ta : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + 1) ≤ rv (kw len) tmp)
    (ts : rv (kw len) tmp ≤ rv (kw len) src ∨ rv (kw len) src + 4 * nw len ≤ rv (kw len) tmp) :
    WP isa (correction L c acc src tmp) s fun u =>
      Bx L u B Z len N ∧ Unch B [(rv (kw len) acc, 4 * (nw len + 1)), (rv (kw len) tmp, 4 * nw len)] s.mem u.mem ∧
      Keeps wordClob s u ∧
      ∃ cb : Bool, val32 u.mem B (rv (kw len) acc) (nw len + 1) +
          2 ^ 32 * (if 2 ^ 31 ≤ w32 s.mem B c then val32 s.mem B (rv (kw len) src) (nw len) else 0) =
        val32 s.mem B (rv (kw len) acc) (nw len + 1) + 2 ^ (32 * (nw len + 1)) * cb.toNat := by
  have hn := h.nowrap
  obtain ke := kw_eq len
  obtain ra := rv_ge (kw len) acc
  obtain rt := rv_ge (kw len) tmp
  obtain e4 := rv_byte (kw len) acc 4
  unfold correction
  -- The difference.
  refine WP.seq (WP.mono (chainSub_ok h (o := tmp) (a := { acc with byte := acc.byte + 4 }) (b := src) (e := 0)
    (by decide) hth (by simpa using htz) (by rw [e4]; simpa using (by omega_using [haz] : rv (kw len) acc + 4 + 4 * nw len ≤ Z))
    (by simpa using hsz) (by rw [e4]; simp only [Nat.add_zero]; omega_using [ta, ke]) (by simpa using ts))
    fun s₁ ⟨H₁, O₁, ⟨cb, _, V₁⟩, K₁⟩ => ?_)
  rw [e4] at V₁
  simp only [Nat.add_zero] at O₁ V₁
  obtain C₁ : w32 s₁.mem B c = w32 s.mem B c := O₁.w32 (.inl (by omega_using [hc, rt])) (by omega_using [hc])
  -- The coefficient's sign, then the selection.
  refine WP.seq (WP.mono (VG.Proof.Weierstrass.X86.Inv.maskOf_ok H₁.ws.ws.workspace (coefficient := c) (by omega_using [hc, haz, ra]))
    fun s₂ ⟨M₂, K₂, m₂⟩ => ?_)
  obtain H₂ : Bx L s₂ B Z len N := H₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
    (rv_ge _ acc) haz
  rw [C₁] at M₂
  refine WP.mono (selIn_ok H₂ (o := { acc with byte := acc.byte + 4 }) (a := tmp) (e := 0)
    (k := decide (2 ^ 31 ≤ w32 s.mem B c)) (by rw [M₂]; simp [cmask]) (by decide)
    (by rw [e4]; omega_using [haz, ke]) (by simpa using htz) (by rw [e4]; omega_using [ta, ke])) fun u ⟨H, O, V, K⟩ => ?_
  rw [e4, m₂] at O V
  simp only [Nat.add_zero] at O V
  refine ⟨H, ?_, ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K.mono (by decide)), ?_⟩
  · intro x hx
    rw [O x (by have := hx _ (List.mem_cons_self ..); omega_using [ke, this]), O₁ x (hx (rv (kw len) tmp, 4 * nw len) (by simp))]
  · -- Word 0 is kept; words 1 to `n` are the selected ones.
    obtain w0 : w32 u.mem B (rv (kw len) acc) = w32 s.mem B (rv (kw len) acc) := by
      rw [O.w32 (.inl (by omega_using [])) (by omega_using [haz, hn]), O₁.w32 (by omega_using [ta, ke]) (by omega_using [haz, hn])]
    obtain A₁ : val32 s₁.mem B (rv (kw len) acc + 4) (nw len) = val32 s.mem B (rv (kw len) acc + 4) (nw len) :=
      O₁.val32 (by omega_using [ta, ke]) (by omega_using [haz, hn])
    refine ⟨if 2 ^ 31 ≤ w32 s.mem B c then cb else false, ?_⟩
    rw [val32, val32, w0]
    by_cases hk : 2 ^ 31 ≤ w32 s.mem B c
    · simp only [hk, decide_true, ite_true] at V ⊢
      rw [V, show 32 * (nw len + 1) = 32 + 32 * nw len by omega_using [], Nat.pow_add, Nat.mul_assoc]
      have := congrArg (2 ^ 32 * ·) V₁
      simp only [Nat.mul_add] at this
      simp only [nw] at this ⊢
      omega_using [V₁]
    · simp only [hk, decide_false, Bool.false_eq_true, ite_false] at V ⊢
      rw [V, A₁]
      simp

/-- `linear u v acc a b tmp e`: `InvMemory.linear`'s signed combination of the `n + e`-word inputs
`[a]` and `[b]` with the coefficients at the header words `u` and `v`, modulo `n + 1` words. -/
theorem linear_ok {s : State} (h : Bx L s B Z len N) {u v : Nat} (hu : u + 4 ≤ 160) (hv : v + 4 ≤ 160)
    {acc a b tmp : Ref} {e : Nat} (he : e ≤ 1) (hah : a.half = 0) (hbh : b.half = 0) (hth : tmp.half = 0)
    (haccz : rv (kw len) acc + 4 * (nw len + e + 2) ≤ Z)
    (haz : rv (kw len) a + 4 * (nw len + e) ≤ Z) (hbz : rv (kw len) b + 4 * (nw len + e) ≤ Z)
    (htz : rv (kw len) tmp + 4 * nw len ≤ Z)
    (sa : rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) a)
    (sb : rv (kw len) b + 4 * (nw len + e) ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) b)
    (ta : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) tmp)
    (tsa : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) a ∨ rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) tmp)
    (tsb : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) b ∨ rv (kw len) b + 4 * (nw len + e) ≤ rv (kw len) tmp) :
    WP isa (linear L u v acc a b tmp e) s fun z =>
      Bx L z B Z len N ∧ Unch B [(rv (kw len) acc, 4 * (nw len + e + 2)), (rv (kw len) tmp, 4 * nw len)] s.mem z.mem ∧
      Keeps wordClob s z ∧
      (val32 z.mem B (rv (kw len) acc) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
        ((s.mem.readW (off B u) 32).toInt * val32 s.mem B (rv (kw len) a) (nw len + e) +
         (s.mem.readW (off B v) 32).toInt * val32 s.mem B (rv (kw len) b) (nw len + e)) % 2 ^ (32 * (nw len + 1)) := by
  have hn := h.nowrap
  obtain ke := kw_eq len
  obtain ra := rv_ge (kw len) acc
  obtain rt := rv_ge (kw len) tmp
  unfold linear
  refine WP.seq (WP.mono (linearUnsigned_ok h hu hv (by omega_using [he]) hah hbh haccz haz hbz sa sb)
    fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  obtain U₁ : w32 s₁.mem B u = w32 s.mem B u := O₁.w32 (.inl (by omega_using [hu, ra])) (by omega_using [hu])
  obtain W₁ : w32 s₁.mem B v = w32 s.mem B v := O₁.w32 (.inl (by omega_using [hv, ra])) (by omega_using [hv])
  obtain A₁ : val32 s₁.mem B (rv (kw len) a) (nw len) = val32 s.mem B (rv (kw len) a) (nw len) :=
    O₁.val32 (by omega_using [sa]) (by omega_using [he, haccz, haz, hbz, htz, sa, sb, ta, tsa, tsb, hn, ra, rt])
  obtain B₁ : val32 s₁.mem B (rv (kw len) b) (nw len) = val32 s.mem B (rv (kw len) b) (nw len) :=
    O₁.val32 (by omega_using [sb]) (by omega_using [he, haccz, haz, hbz, htz, sa, sb, ta, tsa, tsb, hn, ra, rt])
  obtain H₀ : val32 s₁.mem B (rv (kw len) acc) (nw len + 1) =
      (w32 s.mem B u * val32 s.mem B (rv (kw len) a) (nw len + e) +
        w32 s.mem B v * val32 s.mem B (rv (kw len) b) (nw len + e)) % 2 ^ (32 * (nw len + 1)) := by
    rw [VG.Proof.Weierstrass.X86.Inv.prefix_mod s₁.mem B _ (nw len + 1) (nw len + e + 2) (by omega_using []), V₁]
  refine WP.seq (WP.mono (correction_ok H₁ (c := u) (src := a) (tmp := tmp) hu hth (by omega_using [haccz]) (by omega_using [haz]) htz
    (by omega_using [ta]) (by omega_using [tsa])) fun s₂ ⟨H₂, O₂, K₂, c₁, V₂⟩ => ?_)
  rw [U₁, A₁] at V₂
  obtain W₂ : w32 s₂.mem B v = w32 s₁.mem B v := VG.Proof.Weierstrass.X86.Inv.word_unch O₂
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> omega)
    (by omega_using [hv])
  obtain B₂ : val32 s₂.mem B (rv (kw len) b) (nw len) = val32 s₁.mem B (rv (kw len) b) (nw len) :=
    Outs.val32 O₂
      (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> omega_arith)
      (by omega_using [he, haccz, haz, hbz, htz, sa, sb, ta, tsa, tsb, hn, ra, rt])
  refine WP.mono (correction_ok H₂ (c := v) (src := b) (tmp := tmp) hv hth (by omega_using [haccz]) (by omega_using [hbz]) htz
    (by omega_using [ta]) (by omega_using [tsb])) fun z ⟨H₃, O₃, K₃, c₂, V₃⟩ => ?_
  rw [W₂, W₁, B₂, B₁] at V₃
  obtain H := VG.Proof.Weierstrass.X86.Inv.corrections_mod H₀ V₂ V₃
  refine ⟨H₃, ?_, (K₁.trans K₂).trans K₃, ?_⟩
  · intro x hx
    obtain hacc := hx (rv (kw len) acc, 4 * (nw len + e + 2)) (by simp)
    obtain htmp := hx (rv (kw len) tmp, 4 * nw len) (by simp)
    obtain small : ∀ w ∈ [(rv (kw len) acc, 4 * (nw len + 1)), (rv (kw len) tmp, 4 * nw len)],
        ofs B x < w.1 ∨ w.1 + w.2 ≤ ofs B x := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only at hacc htmp ⊢ <;> omega_arith
    rw [O₃ x small, O₂ x small, O₁ x hacc]
  · have HX := VG.Proof.Weierstrass.X86.Inv.shifted_prefix_mod s.mem B (rv (kw len) a) (nw len) (nw len + e) (by omega_using [])
    obtain HY := VG.Proof.Weierstrass.X86.Inv.shifted_prefix_mod s.mem B (rv (kw len) b) (nw len) (nw len + e) (by omega_using [])
    have E := VG.Proof.Divstep.W32.lin_words
      (M := (2 : Int) ^ (32 * (nw len + 1)))
      (V := val32 z.mem B (rv (kw len) acc) (nw len + 1))
      (X := val32 s.mem B (rv (kw len) a) (nw len + e)) (X' := val32 s.mem B (rv (kw len) a) (nw len))
      (Y := val32 s.mem B (rv (kw len) b) (nw len + e)) (Y' := val32 s.mem B (rv (kw len) b) (nw len))
      (W := w32 s.mem B u) (W' := w32 s.mem B v)
      (c := 2 ^ 31 ≤ w32 s.mem B u) (c' := 2 ^ 31 ≤ w32 s.mem B v)
      (by exact_mod_cast HX) (by exact_mod_cast HY) (by exact_mod_cast H)
    simpa only [w32, VG.Proof.Divstep.W32.toInt_sgn] using E

end VG.Proof.Rsa.X86.InvBatchRt

end

end


/-! # The GCD's shift right by 30 and its matrix rows, for an odd `n`

`shr30o_ok`: `InvBatchRt.shr30_ok`'s statement for `shr30o`, its pairs then one word then the
top word; `fgRowO_ok`: a matrix row of `f` and `g`, `(u f + v g) / 2 ^ 30` by
`shr30o`.
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
  refine shrWord_ok hw ps pd (d := 0) (by omega_using [hs]) (by omega_using [hd]) fun v₁ W₁ K₁ O₁ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_addS rfl fun v₂ U₂ _ => wp_addS rfl fun v₃ U₃ _ => ?_
  obtain K₃ : Keeps [.eax, .ebx, .ebp, .edi] s v₃ :=
    (K₁.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans (U₃.keeps.mono (by decide)))
  obtain m₃ : v₃.mem = v₁.mem := by rw [U₃.mem, U₂.mem]
  obtain pe₃ : PtrAt v₃ W .ebp (sp + 4) := by
    rw [PtrAt, U₃.other _ (by decide), U₂.gpr, K₁.1 _ (by decide), ptr_add ps,
      show (4 : BitVec 32).toNat = 4 from rfl]
  obtain pi₃ : PtrAt v₃ W .edi (dp + 4) := by
    rw [PtrAt, U₃.gpr, U₂.other _ (by decide), K₁.1 _ (by decide), ptr_add pd,
      show (4 : BitVec 32).toNat = 4 from rfl]
  obtain T : w32 v₃.mem W (sp + 4) = w32 s.mem W (sp + 4) := by
    rw [m₃]; exact O₁.w32 (by omega_using [sep]) (by omega_using [hs, hn])
  refine shrTop_ok (hw.of_keeps K₃) pe₃ pi₃ (by omega_using [hs]) (by omega_using [hd]) fun v Wv Kv Ov => ?_
  rw [T] at Wv
  refine k v ?_ Wv ((K₃.mono (by decide)).trans (Kv.mono (by decide))) ?_
  · rw [Ov.w32 (d := dp) (.inl (Nat.le_refl _)) (by omega_using [hd, hn]), m₃]
    simpa only [Nat.add_zero] using W₁
  · rw [m₃] at Ov
    exact (O₁.mono (Nat.le_refl _) (by omega_using [])).trans (Ov.mono (by omega_using []) (by omega_using []))

/-- The value of the shifted number from its low `k` words, one more and the top word. -/
theorem shr_close {m₀ m : Mem} {W : Addr} {dst src k : Nat}
    (V : val32 m W dst k = val32 m₀ W src (k + 1) / 2 ^ 30 % 2 ^ (32 * k))
    (Wd : w32 m W (dst + 4 * k) =
      (w32 m₀ W (src + 4 * k) / 2 ^ 30 + 4 * w32 m₀ W (src + 4 * k + 4)) % 2 ^ 32)
    (Wt : w32 m W (dst + 4 * k + 4) = (w32 m₀ W (src + 4 * k + 4) / 2 ^ 30 +
        4 * (if 2 ^ 31 ≤ w32 m₀ W (src + 4 * k + 4) then 2 ^ 32 - 1 else 0)) % 2 ^ 32) :
    val32 m W dst (k + 2) = sext32 m₀ W src (k + 2) / 2 ^ 30 % 2 ^ (32 * (k + 2)) := by
  obtain V₁ : val32 m W dst (k + 1) = val32 m₀ W src (k + 2) / 2 ^ 30 % 2 ^ (32 * (k + 1)) :=
    shr_succ V Wd rfl
  rw [val32_succ m W dst (k + 1), V₁, show dst + 4 * (k + 1) = dst + 4 * k + 4 by omega_using [], Wt]
  simp only [sext32, show k + 2 - 1 = k + 1 by omega_using [], show k + 2 = k + 1 + 1 by omega_using []]
  rw [show src + 4 * k + 4 = src + 4 * (k + 1) by omega_using []]
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
  obtain hw := kw_bound h.ws.lenLe
  obtain ke := kw_eq len
  have hZ := h.halfZ
  obtain rd := rv_ge (kw len) dst
  unfold shr30o
  rw [show ptr L .edi dst .edx = ptr L .edi dst .edx ++ [] from (List.append_nil _).symm]
  simp only [List.append_assoc]
  refine WP.seq (ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega_arith) fun u₁ K₁ m₁ p₁ => ?_)
  obtain h₁ : Bx L u₁ B Z len N := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _) rd hdz
  refine nBytesLess_ok h₁.ws.ws.workspace h₁.slots hZ (by omega_arith) (by omega_arith) fun u₂ K₂ m₂ c₂ => ?_
  obtain h₂ : Bx L u₂ B Z len N := h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _) rd hdz
  refine ptr_ok h₂.ws h₂.slots hZ (by decide) (by decide) (by decide) (by decide) (fun _ => hdh)
    (by omega_arith) fun u K₃ m₃ p₃ => WP.block_nil ?_
  obtain K : Keeps [.ebx, .edx, .ebp, .edi, .esi] s u :=
    ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))
  obtain m : u.mem = s.mem := by rw [m₃, m₂, m₁]
  obtain hwu := h.ws.rt.of_keeps K
  refine WP.seq (WP.mono (shrPairs_ok hwu (sp := rv (kw len) src) (dp := rv (kw len) dst) (n := nw len - 1) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by rw [PtrAt, K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁) p₃
    (by rw [K₃.1 _ (by decide), c₂]; omega_using [ke])) fun t ⟨Kt, pe, pi, _, Ot, Vt⟩ => ?_)
  obtain e1 : 2 * ((nw len - 1) / 2) = nw len - 1 := by omega_arith
  obtain e2 : 8 * ((nw len - 1) / 2) = 4 * (nw len - 1) := by omega_arith
  obtain e3 : nw len - 1 + 1 = nw len := by omega_arith
  simp only [e1, e2, e3] at pe pi Ot Vt ⊢
  clear e1 e2 e3
  obtain ht := hwu.of_keeps Kt
  -- The last low word and the top word.
  refine shrLast_ok ht pe pi (by omega_arith) (by omega_arith) (by omega_arith) fun v Wd Wt Kv Ov => ?_
  -- `edi` back.
  obtain KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s v :=
    ((K.mono (by decide)).trans (Kt.mono (by decide))).trans (Kv.mono (by decide))
  obtain Ofull : Outside B (rv (kw len) dst) (4 * (nw len + 1)) s.mem v.mem := by
    rw [← m]
    exact (Ot.mono (Nat.le_refl _) (by omega_arith)).trans (Ov.mono (by omega_arith) (by omega_arith))
  obtain O0 : Outside B 0 Z s.mem v.mem := Ofull.mono (Nat.zero_le _) (by omega_arith)
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  obtain K' : Keeps wordClob s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := wordClob)
      ((KK.mono (by decide)).trans (U.keeps.mono (by decide))) (U.gpr.trans (RtWs.edi_eq h.ws).symm)
  refine ⟨h.keep K' (by decide) (by decide) (by rw [U.mem]; exact Ofull) rd hdz, ?_, K', by rw [U.mem]; exact Ofull⟩
  -- The value.
  obtain S : ∀ d, rv (kw len) src ≤ d → d + 4 ≤ rv (kw len) src + 4 * (nw len + 1) →
      w32 t.mem B d = w32 s.mem B d :=
    fun d h₁ h₂ => by rw [Ot.w32 (by omega_arith) (by omega_arith), m]
  rw [S _ (by omega_arith) (by omega_arith), S _ (by omega_arith) (by omega_arith)] at Wd
  rw [S _ (by omega_arith) (by omega_arith)] at Wt
  rw [U.mem]
  obtain V' : val32 v.mem B (rv (kw len) dst) (nw len - 1) =
      val32 s.mem B (rv (kw len) src) (nw len - 1 + 1) / 2 ^ 30 % 2 ^ (32 * (nw len - 1)) := by
    rw [Ov.val32 (.inl (Nat.le_refl _)) (by omega_arith), ← m, show nw len - 1 + 1 = nw len by omega_arith]
    exact Vt
  obtain E := shr_close V' Wd Wt
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
  obtain Q : 2 ^ (32 * (nw len + 1)) = 2 * (2 ^ (32 * nw len) * 2 ^ 31) := by
    rw [pow32_succ]; omega_using []
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
  obtain ke := kw_eq len
  obtain r4 := rv_a len 4; have r5 := rv_a len 5; have r11 := rv_a len 11; have r12 := rv_a len 12
  obtain rj := rv_a len j
  obtain hjb := Nat.mul_le_mul_right (8 * nw len + 8) (show j ≤ 10 by omega_using [hj])
  refine WP.seq (WP.mono (linear_ok h (e := 1) (tmp := a 12) hu4 hv4 (by decide) rfl rfl rfl
    (by omega_using [hf16, r11]) (by omega_using [hf16, r4]) (by omega_using [hf16, r5]) (by omega_using [hf16, r12]) (by omega_using [r4, r11]) (by omega_using [r5, r11]) (by omega_using [hodd, r11, r12]) (by omega_using [r4, r12]) (by omega_using [r5, r12]))
    fun s₁ ⟨H₁, U₁, K₁, V₁⟩ => ?_)
  rw [hu, hv, Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv),
    Divstep.W32.cong_comb hf hg] at V₁
  obtain hcomb := Divstep.W32.comb_le huv hfb hgb
  obtain hpI : (p : Int) < 2 ^ (32 * nw len) * 2 := by
    exact_mod_cast (by simpa only [Nat.pow_succ] using hp)
  obtain cap : ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) = (2 : Int) ^ (32 * nw len) * 2 ^ 31 := by
    push_cast; rfl
  obtain lo : -((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) ≤ cu * f + cv * g := by
    rw [cap]; have := neg_abs_le (cu * f + cv * g); linarith only [this, hcomb, hpI]
  obtain hi : cu * f + cv * g < ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) := by
    rw [cap]; have := le_abs_self (cu * f + cv * g); linarith only [this, hcomb, hpI]
  refine WP.mono (shrSignedO_ok H₁ (dst := a j) (src := a 11) rfl hodd h3 (by omega_using [hf16, r11]) (by omega_using [hf16, rj, hjb]) (by omega_using [r11, rj, hjb])
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
