module

public import VerifiedGarbage.Proof.Divstep.Steps
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
public import VerifiedGarbage.Proof.Mont.Words32
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Int
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedMath
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.BitVec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.Divstep.Absolute
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
import VerifiedGarbage.Proof.Divstep.Tc32
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.Instr
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.NormNum.Abs
import VerifiedGarbage.Proof.Rsa.X86.GcdBatchRt.Shr
public import VerifiedGarbage.Proof.Rsa.X86.GcdBatchRt.Writes
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Slots
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.InitWords
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.SelectX
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
public import Mathlib.Algebra.Group.Int.Defs
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatchRt
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ops
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Batch
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Count
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.BatchBasic

/-! ### `Rsa.X86.GcdBatch.Encoding`, which only this module used -/

section

/-! # Low words and sign of a bounded signed GCD value -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.Proof.Mont

theorem encoding_low {m : Mem} {base : Addr} {d n : Nat} {f : Int}
    (h : (val32 m base d (n+1) : Int)%2^(32*(n+1))=f%2^(32*(n+1))) :
    (val32 m base d n : Int)%2^(32*n)=f%2^(32*n) := by
  obtain D : (2:Int)^(32*n) ∣ 2^(32*(n+1)) := pow_dvd_pow 2 (by omega_using [])
  obtain E : (val32 m base d n : Int)%2^(32*n)=(val32 m base d (n+1) : Int)%2^(32*n) := by
    rw [val32_succ,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Int.add_mul_emod_self_left]
  rw [E,← Int.emod_emod_of_dvd _ D,h,Int.emod_emod_of_dvd _ D]

theorem encoding_sign {m : Mem} {base : Addr} {d n : Nat} {f : Int}
    (h : (val32 m base d (n+1) : Int)%2^(32*(n+1))=f%2^(32*(n+1))) (hb : |f|<2^(32*n)) :
    (2^31 ≤ w32 m base (d+4*n)) ↔ f<0 := by
  obtain grow : (2:Int)^(32*n) ≤ (2:Int)^(32*n)*2^31 := by
    obtain hp : (0:Int)<2^(32*n) := by positivity
    nlinarith
  obtain hb' := abs_lt.mp hb
  obtain lo : -((2:Int)^(32*n)*2^31) ≤ f := by omega_using [hb']
  obtain hi : f<(2:Int)^(32*n)*2^31 := by omega_using [hb']
  obtain Q : (2:Int)^(32*(n+1))=2*((2:Int)^(32*n)*2^31) := by
    rw [show 32*(n+1)=32*n+32 by omega_using [],pow_add]
    ring
  obtain hV : (val32 m base d (n+1) : Int)<2*((2:Int)^(32*n)*2^31) := by
    rw [← Q]
    exact_mod_cast val32_lt m base d (n+1)
  rw [Q] at h
  obtain T := Divstep.W32.tc_eq (by positivity) lo hi (Int.natCast_nonneg _) hV h
  obtain sign := Divstep.W32.tc_neg lo hi T
  rw [VG.Proof.Weierstrass.X86.Inv.sign32]
  obtain H : ((2^(32*n)*2^31 : Nat) : Int)=(2:Int)^(32*n)*2^31 := by push_cast; rfl
  rw [← H] at sign
  exact_mod_cast sign

end VG.Proof.Rsa.X86.GcdBatch

end

end

/-! ### `Rsa.X86.GcdBatchRt.Init`, which only this module used -/

section

/-! # The GCD's start

`copyC_ok`: `InvBatchRt.copy_ok` for any count; `extend_ok`: a number of `n - 1` words
(a narrow array), zero-extended to `n + 1`; `init_ok`: `f = m`, `g = oddInput m x`, `δ = 1`
and the batch count.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.GcdBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Impl.Rsa.X86.GcdBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.Divstep (oddInput)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- `selIn o a cnt`: `[o] = [a]` where the mask `ecx` is all ones, else kept, `n + e`
words. -/
theorem selInC_ok {s : State} (h : Bx L s B Z len N) {o a : Ref} {cnt : List Instr} {c : Nat} {k : Bool}
    (hk : s.gpr .ecx = cmask k) (hc : CountSpec cnt .edi B Z (kw len) c) (hc0 : 0 < c)
    (hoz : rv (kw len) o + 4 * c ≤ Z) (haz : rv (kw len) a + 4 * c ≤ Z)
    (sep : rv (kw len) o + 4 * c ≤ rv (kw len) a ∨ rv (kw len) a + 4 * c ≤ rv (kw len) o) :
    WP isa (selIn L o a cnt) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) o) (4 * c) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) o) c =
        (if k then val32 s.mem B (rv (kw len) a) c else val32 s.mem B (rv (kw len) o) c) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  have hn := h.nowrap
  obtain hw := kw_bound h.ws.lenLe
  have hpos := h.ws.kw_pos
  obtain ke := kw_eq len
  have hZ := h.halfZ
  unfold selIn
  rw [show cnt = cnt ++ [] from (List.append_nil _).symm]
  simp only [List.append_assoc]
  refine WP.seq (ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega_using [hc0, haz, hn]) fun u₁ K₁ m₁ p₁ => ?_)
  obtain h₁ : Bx L u₁ B Z len N := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine ptr_ok h₁.ws h₁.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega_using [hc0, hoz, hn]) fun u₂ K₂ m₂ p₂ => ?_
  obtain h₂ : Bx L u₂ B Z len N := h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine hc u₂ _ _ h₂.ws.ws.workspace h₂.slots fun u K₃ m₃ c₃ => WP.block_nil ?_
  obtain K : Keeps [.ebx, .edx, .ebp, .edi] s u :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide)))
  obtain m : u.mem = s.mem := by rw [m₃, m₂, m₁]
  obtain ecx : u.gpr .ecx = cmask k := by rw [K.1 _ (by decide)]; exact hk
  refine WP.seq (WP.mono (selectLoopX_ok (h.ws.rt.of_keeps K) (x := rv (kw len) a) (d := rv (kw len) o)
    (N := c) k (by omega_using [haz]) (by omega_using [hoz]) sep
    (by rw [PtrAt, K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁)
    (by rw [PtrAt, K₃.1 _ (by decide)]; exact p₂) (by rw [c₃]) ecx) fun t ⟨O, V, _, Kt⟩ => ?_)
  rw [m] at O V
  obtain KK : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  obtain O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega_using [hoz])
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  obtain K' : Keeps [.eax, .ebx, .edx, .ebp] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp])
      (KK.trans (U.keeps.mono (by decide))) (U.gpr.trans (RtWs.edi_eq h.ws).symm)
  exact ⟨h.keep K' (by decide) (by decide) (by rw [U.mem]; exact O) (rv_ge _ o) hoz,
    by rw [U.mem]; exact O, by rw [U.mem]; exact V, K'⟩

/-- `copy o a cnt`: `[o] = [a]`, `n + e` words. -/
theorem copyC_ok {s : State} (h : Bx L s B Z len N) {o a : Ref} {cnt : List Instr} {c : Nat}
    (hc : CountSpec cnt .edi B Z (kw len) c) (hc0 : 0 < c)
    (hoz : rv (kw len) o + 4 * c ≤ Z) (haz : rv (kw len) a + 4 * c ≤ Z)
    (sep : rv (kw len) o + 4 * c ≤ rv (kw len) a ∨ rv (kw len) a + 4 * c ≤ rv (kw len) o) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.copy L o a cnt) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) o) (4 * c) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) o) c = val32 s.mem B (rv (kw len) a) c ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Rsa.X86.InvBatchRt.copy
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  obtain hu : Bx L u B Z len N := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine WP.mono (selInC_ok hu (k := true) (by rw [U.gpr]; rfl) hc hc0 hoz haz sep) fun t ⟨H, O, V, K⟩ =>
    ⟨H, by rw [U.mem] at O; exact O, by rw [V, U.mem]; rfl, (U.keeps.mono (by decide)).trans (K.mono (by decide))⟩

/-- `nBytesLess r` counts `n - 1` words. -/
theorem countLess {r : Reg} {s : State} (hb : Bx L s B Z len N) (h2 : 2 ≤ nw len) :
    CountSpec (nBytesLess r) r B Z (kw len) (nw len - 1) :=
  fun _ _ _ hs hsl k => nBytesLess_ok hs hsl hb.halfZ (by have := kw_bound hb.ws.lenLe; omega_using [this])
    (by have := kw_eq len; omega_using [h2, this]) fun v K m c => k v K m (by rw [c]; have := kw_eq len; omega_using [this])

/-- `nBytes r 1` counts `n + 1` words. -/
theorem countN1 {r : Reg} {s : State} (hb : Bx L s B Z len N) :
    CountSpec (nBytes r 1) r B Z (kw len) (nw len + 1) := by
  have := nBytes_spec (r := r) (e := 1) (B := B) hb.halfZ (w := kw len) (by have := kw_bound hb.ws.lenLe; omega_using [this])
    (by decide) (by have := kw_eq len; omega_using [this])
  rwa [show kw len / 2 + 1 = nw len + 1 by have := kw_eq len; omega_using [this]] at this

/-- `nBytes r 0` counts `n` words. -/
theorem countN0 {r : Reg} {s : State} (hb : Bx L s B Z len N) :
    CountSpec (nBytes r 0) r B Z (kw len) (nw len) := by
  have := nBytes_spec (r := r) (e := 0) (B := B) hb.halfZ (w := kw len) (by have := kw_bound hb.ws.lenLe; omega_using [this])
    (by decide) (by have := kw_eq len; omega_using [this])
  rwa [show kw len / 2 + 0 = nw len by have := kw_eq len; omega_using [this]] at this

/-- A number of `k` words followed by two words of zeros, from the zeros of `k + 2` words and
the number's words. -/
theorem val32_extend {m m' : Mem} {d k v : Nat} (Z0 : val32 m B d (k + 2) = 0) (C : val32 m' B d k = v)
    (O : Outside B d (4 * k) m m') (hd : d + 4 * (k + 2) ≤ 2 ^ 64) : val32 m' B d (k + 2) = v := by
  obtain hi : val32 m' B (d + 4 * k) 2 = val32 m B (d + 4 * k) 2 := O.val32 (.inr (Nat.le_refl _)) (by omega_using [hd])
  rw [val32_append] at Z0 ⊢
  obtain p := Nat.two_pow_pos (32 * k)
  obtain z : val32 m B (d + 4 * k) 2 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * k) 2) with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ (32 * k)) e; omega_using [Z0, p, this]
  rw [hi, z, C]; omega_using []

/-- A number of `k + 1` words below `2 ^ (32 k)`: its low `k` words, and its top word zero. -/
theorem low_eq {mm : Mem} {d k v : Nat} (h : val32 mm B d (k + 1) = v) (hv : v < 2 ^ (32 * k)) :
    val32 mm B d k = v ∧ w32 mm B (d + 4 * k) = 0 := by
  rw [val32_succ] at h
  obtain p := Nat.two_pow_pos (32 * k)
  rcases Nat.eq_zero_or_pos (w32 mm B (d + 4 * k)) with e | e
  · rw [e, Nat.mul_zero, Nat.add_zero] at h; exact ⟨h, e⟩
  · have := Nat.mul_le_mul_left (2 ^ (32 * k)) e; omega_using [h, hv, this]

/-- `[o]` the `n - 1` words of `[src]` zero-extended to `n + 1`. -/
theorem extend_ok {s : State} (h : Bx L s B Z len N) (h3 : 3 ≤ nw len) {o src : Ref}
    (hoz : rv (kw len) o + 4 * (nw len + 1) ≤ Z) (hsz : rv (kw len) src + 4 * (nw len - 1) ≤ Z)
    (sep : rv (kw len) o + 4 * (nw len + 1) ≤ rv (kw len) src ∨ rv (kw len) src + 4 * (nw len - 1) ≤ rv (kw len) o)
    {rest : Prog isa} {Q : State → Prop}
    (k : ∀ u, Bx L u B Z len N → Outside B (rv (kw len) o) (4 * (nw len + 1)) s.mem u.mem →
      val32 u.mem B (rv (kw len) o) (nw len + 1) = val32 s.mem B (rv (kw len) src) (nw len - 1) →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u → WP isa rest u Q) :
    WP isa (.seq (VG.Impl.Rsa.X86.InvBatchRt.zeros L o (nBytes .ecx 1))
      (.seq (VG.Impl.Rsa.X86.InvBatchRt.copy L o src (nBytesLess .edi)) rest)) s Q := by
  have hn := h.nowrap
  refine WP.seq (WP.mono (zeros_ok h (o := o) (countN1 h) (by omega_using []) hoz) fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  obtain S₁ : val32 s₁.mem B (rv (kw len) src) (nw len - 1) = val32 s.mem B (rv (kw len) src) (nw len - 1) :=
    O₁.val32 (by omega_using [sep]) (by omega_using [hsz, hn])
  refine WP.seq (WP.mono (copyC_ok H₁ (o := o) (a := src) (countLess H₁ (by omega_using [h3])) (by omega_using [h3]) (by omega_using [hoz])
    (by omega_using [hsz]) (by omega_using [sep])) fun u ⟨Hu, Ou, Vu, Ku⟩ => ?_)
  refine k u Hu ((O₁.mono (Nat.le_refl _) (Nat.le_refl _)).trans (Ou.mono (Nat.le_refl _) (by omega_using []))) ?_
    ((K₁.mono (by decide)).trans Ku)
  rw [show nw len + 1 = nw len - 1 + 2 by omega_using [h3]] at V₁ ⊢
  exact val32_extend V₁ (Vu.trans S₁) Ou (by omega_using [hoz, hn])

/-- The GCD's state between batches: `δ` in the window, `f` and `g` in arrays 4 and 5. -/
structure GState (len : Nat) (B : Addr) (I : Int × Int × Int) (s : State) : Prop where
  d : s.mem.readW (off B win) 32 = BitVec.ofInt 32 I.1
  f : (val32 s.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
    I.2.1 % 2 ^ (32 * (nw len + 1))
  g : (val32 s.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
    I.2.2 % 2 ^ (32 * (nw len + 1))

/-- The operands: `[4] = m`, `[5] = oddInput m x`, `n + 1` words each. -/
theorem operands_ok {s : State} (h : Bx L s B Z len N) (h3 : 3 ≤ nw len) {m x : Nat}
    (hm : val32 s.mem B (rv (kw len) (a 4)) (nw len - 1) = m)
    (hx : val32 s.mem B (rv (kw len) (a 0)) (nw len - 1) = x)
    {rest : Prog isa} {Q : State → Prop}
    (k : ∀ u, Bx L u B Z len N → val32 u.mem B (rv (kw len) (a 4)) (nw len + 1) = m →
      val32 u.mem B (rv (kw len) (a 5)) (nw len + 1) = oddInput m x → Keeps wordClob s u →
      Unch B [(rv (kw len) (a 4), 2 * (8 * nw len + 8)), (rv (kw len) (a 12), 8 * nw len + 8)] s.mem u.mem →
      WP isa rest u Q) :
    WP isa (.seq (VG.Impl.Rsa.X86.InvBatchRt.zeros L (a 12) (nBytes .ecx 1)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.copy L (a 12) (a 4) (nBytesLess .edi)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.copy L (a 4) (a 12) (nBytes .edi 1)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.zeros L (a 5) (nBytes .ecx 1)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.copy L (a 5) (a 0) (nBytesLess .edi)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.zeros L (a 12) (nBytes .ecx 1)) <|
      .seq (.block (VG.Impl.Rsa.X86.GcdBatch.evenMask (VG.Impl.Rsa.X86.InvBatchRt.offset 0 0))) <|
      .seq (selIn L (a 12) (a 4) (nBytes .edi 0)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.chain L .adc (a 5) (a 5) (a 12) (nBytes .edx 1)) rest) s Q := by
  have hn := h.nowrap
  have hf16 := h.fits16
  obtain r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r12 := rv_a len 12
  obtain r11 := rv_a len 11
  obtain ke' := kw_eq len
  -- `[12] = m`, then `[4] = m`.
  refine extend_ok h h3 (o := a 12) (src := a 4) (by omega_arith) (by omega_arith) (by omega_arith)
    fun s₁ H₁ O₁ V₁ K₁ => ?_
  rw [hm] at V₁
  refine WP.seq (WP.mono (copy_ok H₁ (o := a 4) (a := a 12) (e := 1) (by decide) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₂ ⟨H₂, O₂, V₂, K₂⟩ => ?_)
  rw [V₁] at V₂
  obtain X₂ : val32 s₂.mem B (rv (kw len) (a 0)) (nw len - 1) = x := by
    rw [O₂.val32 (by omega_arith) (by omega_arith), O₁.val32 (by omega_arith) (by omega_arith), hx]
  -- `[5] = x`.
  refine extend_ok H₂ h3 (o := a 5) (src := a 0) (by omega_arith) (by omega_arith) (by omega_arith)
    fun s₃ H₃ O₃ V₃ K₃ => ?_
  rw [X₂] at V₃
  -- `[12] = 0`, then `m` where `x` is even.
  refine WP.seq (WP.mono (zeros_ok H₃ (o := a 12) (countN1 H₃) (by omega_arith) (by omega_arith))
    fun s₄ ⟨H₄, O₄, V₄, K₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.GcdBatch.evenMask_ok H₄.ws.ws.workspace
    (src := VG.Impl.Rsa.X86.InvBatchRt.offset 0 0) (by simp only [VG.Impl.Rsa.X86.InvBatchRt.offset]; omega_arith))
    fun s₅ ⟨C₅, K₅, m₅⟩ => ?_)
  obtain H₅ : Bx L s₅ B Z len N := H₄.keep K₅ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₅]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega_arith)
  obtain o00 : VG.Impl.Rsa.X86.InvBatchRt.offset 0 0 = rv (kw len) (a 0) := by
    simp only [VG.Impl.Rsa.X86.InvBatchRt.offset]; omega_arith
  rw [o00, O₄.w32 (by omega_arith) (by omega_arith), O₃.w32 (by omega_arith) (by omega_arith),
    O₂.w32 (by omega_arith) (by omega_arith), O₁.w32 (by omega_arith) (by omega_arith)] at C₅
  obtain even : x % 2 = w32 s.mem B (rv (kw len) (a 0)) % 2 := by
    obtain ⟨j, hj⟩ : ∃ j, nw len - 1 = j + 1 := ⟨nw len - 2, by omega_arith⟩
    rw [← hx, hj, val32]
    omega_arith
  obtain mlt : m < 2 ^ (32 * (nw len - 1)) := hm ▸ val32_lt _ _ _ _
  obtain xlt : x < 2 ^ (32 * (nw len - 1)) := hx ▸ val32_lt _ _ _ _
  obtain grow : 2 ^ (32 * (nw len - 1)) * 2 ^ 32 = 2 ^ (32 * nw len) := by
    rw [← Nat.pow_add]; congr 1; omega_arith
  obtain g2 : 2 ^ 32 * 2 ^ (32 * nw len) = 2 ^ (32 * (nw len + 1)) := (pow32_succ _).symm
  obtain M₅ : val32 s₅.mem B (rv (kw len) (a 4)) (nw len) = m := by
    obtain A₃ : val32 s₃.mem B (rv (kw len) (a 4)) (nw len + 1) = m := by
      rw [O₃.val32 (by omega_arith) (by omega_arith), V₂]
    rw [m₅, O₄.val32 (by omega_arith) (by omega_arith)]
    exact (low_eq A₃ (lt_of_lt_of_le mlt (Nat.pow_le_pow_right (by decide) (by omega_arith)))).1
  refine WP.seq (WP.mono (selIn_ok H₅ (o := a 12) (a := a 4) (e := 0) (k := decide (x % 2 = 0))
    (by rw [C₅, even]; by_cases he : w32 s.mem B (rv (kw len) (a 0)) % 2 = 0 <;> simp [cmask])
    (by decide) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₆ ⟨H₆, O₆, V₆, K₆⟩ => ?_)
  simp only [Nat.add_zero] at O₆ V₆
  rw [M₅] at V₆
  obtain T₆ : val32 s₆.mem B (rv (kw len) (a 12)) (nw len + 1) = if x % 2 = 0 then m else 0 := by
    obtain p := Nat.two_pow_pos (32 * nw len)
    obtain top4 : w32 s₄.mem B (rv (kw len) (a 12) + 4 * nw len) = 0 := by
      have := val32_succ s₄.mem B (rv (kw len) (a 12)) (nw len)
      rw [V₄] at this
      rcases Nat.eq_zero_or_pos (w32 s₄.mem B (rv (kw len) (a 12) + 4 * nw len)) with e | e
      · exact e
      · have := Nat.mul_le_mul_left (2 ^ (32 * nw len)) e; omega_arith
    obtain low4 : val32 s₄.mem B (rv (kw len) (a 12)) (nw len) = 0 := by
      have := val32_succ s₄.mem B (rv (kw len) (a 12)) (nw len)
      rw [V₄] at this; omega_arith
    rw [val32_succ, V₆, O₆.w32 (by omega_arith) (by omega_arith), m₅, top4, Nat.mul_zero, Nat.add_zero, low4]
    by_cases he : x % 2 = 0 <;> simp [he]
  -- `[5] += [12]`.
  refine WP.seq (WP.mono (chainAdd_ok H₆ (o := a 5) (a := a 5) (b := a 12) (e := 1) (by decide) rfl
    (by omega_arith) (by omega_arith) (by omega_arith) (.inl (Nat.le_refl _)) (by omega_arith))
    fun u ⟨Hu, Ou, ⟨c, _, Vu⟩, Ku⟩ => ?_)
  obtain G₆ : val32 s₆.mem B (rv (kw len) (a 5)) (nw len + 1) = x := by
    rw [O₆.val32 (by omega_arith) (by omega_arith), m₅, O₄.val32 (by omega_arith) (by omega_arith), V₃]
  rw [G₆, T₆] at Vu
  obtain sum : x + (if x % 2 = 0 then m else 0) < 2 ^ (32 * (nw len + 1)) := by
    rw [← g2, ← grow]; have := Nat.two_pow_pos (32 * (nw len - 1)); split <;> omega_arith
  obtain Gu : val32 u.mem B (rv (kw len) (a 5)) (nw len + 1) = oddInput m x := by
    unfold oddInput
    cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at Vu <;>
      (simp only [nw] at *; omega_arith)
  refine k u Hu ?_ Gu ?_ ?_
  · rw [Ou.val32 (by omega_arith) (by omega_arith), O₆.val32 (by omega_arith) (by omega_arith), m₅,
      O₄.val32 (by omega_arith) (by omega_arith), O₃.val32 (by omega_arith) (by omega_arith), V₂]
  · exact ((((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))).trans (K₅.mono (by decide))).trans (K₆.mono (by decide))).trans (Ku.mono (by decide))
  · intro y hy
    obtain hA := hy (rv (kw len) (a 4), 2 * (8 * nw len + 8)) (by simp)
    obtain hT := hy (rv (kw len) (a 12), 8 * nw len + 8) (by simp)
    rw [Ou y (by omega_arith), O₆ y (by omega_arith), m₅, O₄ y (by omega_arith), O₃ y (by omega_arith),
      O₂ y (by omega_arith), O₁ y (by omega_arith)]

/-- `init`. -/
theorem init_ok {s : State} (h : RtWs L s B Z len N) (room : 16 ≤ N) (h3 : 3 ≤ nw len) {m x : Nat}
    (hm : val32 s.mem B (rv (kw len) (a 4)) (nw len - 1) = m)
    (hx : val32 s.mem B (rv (kw len) (a 0)) (nw len - 1) = x) :
    WP isa (VG.Impl.Rsa.X86.GcdBatchRt.init L) s fun z => Bx L z B Z len N ∧ GState len B (1, m, oddInput m x) z ∧
      w32 z.mem B 100 = 3 * (nw len + 1) ∧ Keeps wordClob s z ∧ Unch B (gcdWrites len) s.mem z.mem := by
  have hn := h.ws.workspace.nowrap
  obtain hw := kw_bound h.lenLe
  obtain ke := kw_eq len
  have e16 : win = 16 := rfl
  have e52 : slotBase = 52 := rfl
  have e96 : halfSlot = 96 := rfl
  unfold VG.Impl.Rsa.X86.GcdBatchRt.init
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  -- The slots.
  rw [show slots L = slots L ++ [] from (List.append_nil _).symm]
  refine WP.seq (slots_ok h room fun s₀ H₀ K₀ O₀ => WP.block_nil ?_)
  have hZ := H₀.halfZ
  have hf16 := H₀.fits16
  obtain r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r12 := rv_a len 12
  obtain r11 := rv_a len 11
  obtain hm₀ : val32 s₀.mem B (rv (kw len) (a 4)) (nw len - 1) = m := by
    rw [O₀.val32 (by omega_arith) (by omega_arith), hm]
  obtain hx₀ : val32 s₀.mem B (rv (kw len) (a 0)) (nw len - 1) = x := by
    rw [O₀.val32 (by omega_arith) (by omega_arith), hx]
  refine operands_ok H₀ h3 hm₀ hx₀ fun u Hu F₄ G₅ Ku Uu => ?_
  -- `δ = 1`.
  refine WP.seq (wp_movS rfl fun u₁ V₁ _ => ?_)
  obtain hs₁ := Hu.ws.ws.workspace.of_keeps V₁.keeps (by decide)
  refine wp_storeS (hs₁.ea (by omega_arith)) (hs₁.write (d := win) (n := 4) (by omega_arith)) fun u₂ V₂ => WP.block_nil ?_
  obtain O₂ : Outside B win 4 u.mem u₂.mem := by rw [V₂.mem, V₁.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  obtain H₂ : Bx L u₂ B Z len N := Hu.keepLow (V₁.keeps.trans (V₂.keeps _)) (by decide) (by decide) O₂ (by decide)
  obtain D₂ : u₂.mem.readW (off B win) 32 = 1 := by
    apply BitVec.eq_of_toNat_eq
    change w32 u₂.mem B win = _
    rw [V₂.mem, w32_write_self, V₁.gpr]
  -- The batch count.
  unfold batches
  refine nBytes_ok H₂.ws.ws.workspace H₂.slots hZ (by omega_arith) (e := 1) (by decide) fun u₁₂ K₁₂ m₁₂ c₁₂ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₁₃ V₁₃ => ?_
  refine wp_movS rfl fun u₁₄ V₁₄ _ => wp_addS rfl fun u₁₅ V₁₅ _ => wp_addS rfl fun u₁₆ V₁₆ _ => ?_
  obtain K₁₆ : Keeps [.eax, .ecx] u₂ u₁₆ :=
    ((((K₁₂.mono (by decide)).trans (V₁₃.keeps.mono (by decide))).trans (V₁₄.keeps.mono (by decide))).trans
      (V₁₅.keeps.mono (by decide))).trans (V₁₆.keeps.mono (by decide))
  obtain hs₁₆ := H₂.ws.ws.workspace.of_keeps K₁₆ (by decide)
  refine wp_storeS (hs₁₆.ea (by omega_arith)) (hs₁₆.write (d := 100) (n := 4) (by omega_arith)) fun z Vz => WP.block_nil ?_
  obtain m₁₆ : u₁₆.mem = u₂.mem := by rw [V₁₆.mem, V₁₅.mem, V₁₄.mem, V₁₃.mem, m₁₂]
  obtain Oz : Outside B 100 4 u₂.mem z.mem := by rw [Vz.mem, m₁₆]; exact writeW32_outside _ _ _ (by omega_arith)
  obtain Hz : Bx L z B Z len N := H₂.keepHigh (K₁₆.trans (Vz.keeps _)) (by decide) (by decide) Oz (by decide)
    (by omega_arith)
  obtain count : w32 z.mem B 100 = 3 * (nw len + 1) := by
    rw [Vz.mem, w32_write_self, V₁₆.gpr, V₁₅.gpr, V₁₅.other .ecx (by decide), V₁₄.gpr, V₁₄.other _ (by decide),
      V₁₃.gpr]
    obtain e₁₂ : (u₁₂.gpr .eax).toNat = 4 * (nw len + 1) := by rw [c₁₂]; omega_arith
    obtain e₁₃ : (u₁₂.gpr .eax >>> 2).toNat = nw len + 1 := by
      rw [BitVec.toNat_ushiftRight, e₁₂, Nat.shiftRight_eq_div_pow]; omega_arith
    simp only [BitVec.toNat_add, e₁₃]
    omega_arith
  refine ⟨Hz, ⟨?_, ?_, ?_⟩, count, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    change w32 z.mem B win = (BitVec.ofInt 32 1).toNat
    rw [Oz.w32 (by omega_arith) (by omega_arith)]
    exact congrArg BitVec.toNat D₂
  · rw [Oz.val32 (by omega_arith) (by omega_arith), O₂.val32 (by omega_arith) (by omega_arith), F₄]
  · rw [Oz.val32 (by omega_arith) (by omega_arith), O₂.val32 (by omega_arith) (by omega_arith), G₅]
  · exact (((K₀.mono (by decide)).trans Ku).trans ((V₁.keeps.trans (V₂.keeps _)).mono (by decide))).trans
      ((K₁₆.trans (Vz.keeps _)).mono (by decide))
  · intro y hy
    obtain h1 := hy (win, 88) (by simp [gcdWrites])
    obtain h2 := hy (rv (kw len) (a 0), 6 * (8 * nw len + 8)) (by simp [gcdWrites])
    obtain h3 := hy (rv (kw len) (a 11), 2 * (8 * nw len + 8)) (by simp [gcdWrites])
    simp only at h1 h2 h3
    rw [Oz y (by omega_using [e16, h1]), O₂ y (by omega_using [h1]), Uu y (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega_arith), O₀ y (by omega_using [e16, e52, h1])]

end VG.Proof.Rsa.X86.GcdBatchRt

end

end


-- separate module: its proofs cost more than its imports; `BatchInstance` binds it, as it binds
-- `InvBatchRt.Body`
/-! # The batched GCD of prime recovery

`update_ok`: both rows of the matrix, `f` and `g` replaced; `batch_ok`: the window's thirty
divsteps, the update and the count down by one, which take the state `I` to `divsteps 30 I`;
`loop_ok`: the counted batches; `finish_ok`: `|f|` into narrow array 1 and array 5 zeroed;
`body_ok`: `gcd(m, x)` for `m` odd, from narrow arrays 8 and 0, `w = n - 1` words each.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.GcdBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Impl.Rsa.X86.GcdBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.Divstep (oddInput)
open VG.Proof.Divstep (divsteps)
open VG.Proof.Weierstrass.X86.Inv (read32_unch)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem seq_assoc' {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff, WP.seq_iff] at h
  exact WP.seq_iff.mpr (WP.mono h fun _ hu => WP.seq_iff.mpr hu)

/-- The arrays the update writes. -/
def arrWrites (len : Nat) : List (Nat × Nat) :=
  [(rv (kw len) (a 0), 6 * (8 * nw len + 8)), (rv (kw len) (a 11), 2 * (8 * nw len + 8))]

/-- The update: `f = (u f + v g) / 2 ^ 30` and `g = (q f + r g) / 2 ^ 30`. -/
theorem update_ok {s : State} (h : Bx L s B Z len N) (hodd : nw len % 2 = 1) (h3 : 3 ≤ nw len)
    {T : Divstep.MSt} {f g : Int} {p : Nat} (hm : MatrixAt B T s)
    (hf : (val32 s.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      f % 2 ^ (32 * (nw len + 1)))
    (hg : (val32 s.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      g % 2 ^ (32 * (nw len + 1)))
    (huv : |T.u| + |T.v| ≤ 2 ^ 30) (hqr : |T.q| + |T.r| ≤ 2 ^ 30)
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ (32 * nw len + 1))
    (divF : 2 ^ 30 ∣ T.u * f + T.v * g) (divG : 2 ^ 30 ∣ T.q * f + T.r * g) :
    WP isa (VG.Impl.Rsa.X86.GcdBatchRt.update L) s fun z => Bx L z B Z len N ∧
      (val32 z.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
        ((T.u * f + T.v * g) / 2 ^ 30) % 2 ^ (32 * (nw len + 1)) ∧
      (val32 z.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
        ((T.q * f + T.r * g) / 2 ^ 30) % 2 ^ (32 * (nw len + 1)) ∧
      Keeps wordClob s z ∧ Unch B (arrWrites len) s.mem z.mem := by
  have hnw : nw len = kw len / 2 := rfl
  obtain hke := kw_eq len
  have hn := h.nowrap
  have hf16 := h.fits16
  obtain r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r11 := rv_a len 11
  obtain r12 := rv_a len 12
  have e16 : win = 16 := rfl
  unfold VG.Impl.Rsa.X86.GcdBatchRt.update
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  -- The first row, into `[0]`.
  refine seq_assoc' (WP.seq (WP.mono (fgRowO_ok h hodd h3 (j := 0) (by decide) (by decide) (by decide)
    hm.u hm.v huv hf hg hfb hgb hp divF) fun s₁ ⟨H₁, F₁, K₁, U₁⟩ => ?_))
  obtain apart₁ : ∀ d, (d + 4 ≤ rv (kw len) (a 0) ∨ rv (kw len) (a 0) + 4 * (nw len + 1) ≤ d) →
      d + 4 ≤ rv (kw len) (a 11) → s₁.mem.readW (off B d) 32 = s.mem.readW (off B d) 32 :=
    fun d h₁ h₂ => read32_unch U₁ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega_arith) (by omega_using [hn, hf16, r11, h₂])
  obtain val₁ : ∀ d k, rv (kw len) (a 0) + 4 * (nw len + 1) ≤ d → d + 4 * k ≤ rv (kw len) (a 11) →
      val32 s₁.mem B d k = val32 s.mem B d k :=
    fun d k h₁ h₂ => Outs.val32 U₁ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega_arith) (by omega_using [hn, hf16, r11, h₂])
  -- The second, into `[5]`.
  refine seq_assoc' (WP.seq (WP.mono (fgRowO_ok H₁ hodd h3 (j := 5) (by decide) (by decide) (by decide)
    (by rw [apart₁ _ (by omega_using [r0, e16]) (by omega_using [r11, e16])]; exact hm.q) (by rw [apart₁ _ (by omega_using [r0, e16]) (by omega_using [r11, e16])]; exact hm.r)
    hqr (by rw [val₁ _ _ (by omega_using [r0, r4]) (by omega_using [r4, r11])]; exact hf) (by rw [val₁ _ _ (by omega_using [r0, r5]) (by omega_using [r5, r11])]; exact hg)
    hfb hgb hp divG) fun s₂ ⟨H₂, G₂, K₂, U₂⟩ => ?_))
  obtain A₂ : val32 s₂.mem B (rv (kw len) (a 0)) (nw len + 1) = val32 s₁.mem B (rv (kw len) (a 0)) (nw len + 1) :=
    Outs.val32 U₂ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega_arith) (by omega_using [hn, hf16, r0])
  -- `[4] = [0]`.
  refine WP.mono (copy_ok H₂ (o := a 4) (a := a 0) (e := 1) (by decide) (by omega_using [hke, hf16, r4]) (by omega_using [hke, hf16, r0]) (by omega_using [hke, r0, r4]))
    fun z ⟨Hz, Oz, Vz, Kz⟩ => ⟨Hz, by rw [Vz, A₂]; exact F₁, ?_, ?_, ?_⟩
  · rw [Oz.val32 (by omega_using [hnw, r4, r5]) (by omega_using [hn, hf16, r5])]; exact G₂
  · exact ((K₁.trans K₂).trans (Kz.mono (by decide)))
  · intro y hy
    obtain h0 := hy (rv (kw len) (a 0), 6 * (8 * nw len + 8)) (by simp [arrWrites])
    obtain h11 := hy (rv (kw len) (a 11), 2 * (8 * nw len + 8)) (by simp [arrWrites])
    simp only at h0 h11
    rw [Oz y (by omega_using [hnw, r0, r4, h0]), U₂ y (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega_arith), U₁ y (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega_arith)]

/-- The loop body. -/
abbrev batchCode (L : Lay) : Prog isa :=
  VG.Impl.Rsa.X86.Keys.seqs [.block (start L), VG.Impl.Weierstrass.X86.Inv.wordSteps win 30, VG.Impl.Rsa.X86.GcdBatchRt.update L,
    .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter]]

/-- A counted batch. -/
theorem batch_ok {s : State} (h : Bx L s B Z len N) (hodd : nw len % 2 = 1) (h3 : 3 ≤ nw len)
    {p j : Nat} {I : Int × Int × Int} (hI : GState len B I s) (hdb : |I.1| + 64 < 2 ^ 30) (hfo : I.2.1 % 2 = 1)
    (hfb : |I.2.1| ≤ p) (hgb : |I.2.2| ≤ p) (hp : p < 2 ^ (32 * nw len + 1))
    (jp : 1 ≤ j) (jl : j < 2 ^ 32) (counter : w32 s.mem B 100 = j) :
    WP isa (batchCode L) s fun z => Bx L z B Z len N ∧ GState len B (Divstep.divsteps 30 I) z ∧
      w32 z.mem B 100 = j - 1 ∧ z.zf = some (decide (j - 1 = 0)) ∧
      Keeps wordClob s z ∧ Unch B (gcdWrites len) s.mem z.mem := by
  have hnw : nw len = kw len / 2 := rfl
  obtain hke := kw_eq len
  have hn := h.nowrap
  have hf16 := h.fits16
  have e16 : win = 16 := rfl
  obtain r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r11 := rv_a len 11
  generalize hT : Divstep.msteps 30 (Divstep.MSt.init I.1 I.2.1 I.2.2) = T
  obtain mat := Divstep.msteps_mat (d := I.1) (g := I.2.2) hfo 30
  obtain bound := Divstep.msteps_bnd I.1 I.2.1 I.2.2 30
  rw [hT] at mat bound
  change 2 ^ 30 * T.f = T.u * I.2.1 + T.v * I.2.2 ∧ 2 ^ 30 * T.g = T.q * I.2.1 + T.r * I.2.2 at mat
  change |T.u| + |T.v| ≤ 2 ^ 30 ∧ |T.q| + |T.r| ≤ 2 ^ 30 at bound
  obtain df : (T.d, T.f, T.g) = Divstep.divsteps 30 I := by
    obtain D := Divstep.msteps_dfg 30 (Divstep.MSt.init I.1 I.2.1 I.2.2)
    rw [hT] at D
    simpa only [Divstep.MSt.init, Prod.eta] using D
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine seq_assoc' (WP.seq (WP.mono (words_ok h hI.d hI.f hI.g hdb hfo) fun u ⟨Hu, M, K, O⟩ => ?_))
  rw [hT] at M
  refine WP.seq (WP.mono (update_ok Hu hodd h3 M (by rw [O.val32 (by omega_using [e16, r4]) (by omega_using [hn, hf16, r4])]; exact hI.f)
    (by rw [O.val32 (by omega_using [e16, r5]) (by omega_using [hn, hf16, r5])]; exact hI.g) bound.1 bound.2 hfb hgb hp
    ⟨T.f, mat.1.symm⟩ ⟨T.g, mat.2.symm⟩) fun v ⟨Hv, Fv, Gv, Kv, Ov⟩ => ?_)
  obtain cv : w32 v.mem B 100 = j := by
    rw [VG.Proof.Weierstrass.X86.Inv.word_unch Ov (by
      intro r hr; simp only [arrWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using []),
      O.w32 (by omega_using [e16]) (by omega_using []), counter]
  refine WP.mono (VG.Proof.Rsa.X86.GcdBatch.countDown_ok Hv.ws.ws.workspace (d := 100) (by omega_using [hf16]) jp jl cv)
    fun z ⟨c, zf, Kz, Oz⟩ => ?_
  refine ⟨Hv.keepHigh Kz (by decide) (by decide) Oz (by decide) (by omega_using [hf16]), ?_, c, zf,
    (K.trans Kv).trans (Kz.mono (by decide)), ?_⟩
  · rw [← df]
    refine ⟨?_, ?_, ?_⟩
    · rw [read32_unch Oz.unch (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp only; omega_using [e16])
        (by omega_using [e16]), read32_unch Ov (by
        intro r hr; simp only [arrWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [e16])]
      exact M.d
    · rw [Oz.val32 (by omega_using [r4]) (by omega_using [hn, hf16, r4]), Fv, ← mat.1, Int.mul_ediv_cancel_left _ (by decide)]
    · rw [Oz.val32 (by omega_using [r5]) (by omega_using [hn, hf16, r5]), Gv, ← mat.2, Int.mul_ediv_cancel_left _ (by decide)]
  · intro x hx
    obtain h1 := hx (win, 88) (by simp [gcdWrites])
    obtain h2 := hx (rv (kw len) (a 0), 6 * (8 * nw len + 8)) (by simp [gcdWrites])
    obtain h3 := hx (rv (kw len) (a 11), 2 * (8 * nw len + 8)) (by simp [gcdWrites])
    simp only at h1 h2 h3
    rw [Oz x (by omega_using [e16, h1]), Ov x (by
      intro r hr; simp only [arrWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith), O x (by omega_using [h1])]


/-- What a batch needs of the state it starts from. -/
structure Facts (I : Int × Int × Int) (p : Nat) : Prop where
  delta : |I.1| + 64 < 2 ^ 30
  odd : I.2.1 % 2 = 1
  f : |I.2.1| ≤ p
  g : |I.2.2| ≤ p

theorem runFacts {n m x p i : Nat} (hn : n ≤ 1024) (hi : i < 3 * (n + 1))
    (hm : m % 2 = 1) (mp : m ≤ p) (xp : x ≤ p) :
    Facts (divsteps (30 * i) (1, m, x)) p := by
  obtain d := Divstep.W32.divsteps_d (1, m, x) (30 * i)
  obtain ho := Divstep.divsteps_odd (d := 1) (f := m) (g := x) (by decide) (by exact_mod_cast hm) (30 * i)
  obtain fg := Divstep.W32.divsteps_le (M := p) (d := 1) (f := m) (g := x) (by decide) (by exact_mod_cast hm)
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using (show (m : Int) ≤ p by exact_mod_cast mp))
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using (show (x : Int) ≤ p by exact_mod_cast xp)) (30 * i)
  refine ⟨?_, ho.2, fg.1, fg.2⟩
  norm_num only [abs_one, Nat.cast_mul, Nat.cast_ofNat] at d
  omega_using [hn, hi, d]

/-- The counted batches, `K` of them. -/
theorem loop_ok {s : State} (h : Bx L s B Z len N) (hodd : nw len % 2 = 1) (h3 : 3 ≤ nw len)
    {p K : Nat} {m x : Int} (hK : 0 < K) (hK32 : K < 2 ^ 32) (hp : p < 2 ^ (32 * nw len + 1))
    (hI : GState len B (1, m, x) s) (hc : w32 s.mem B 100 = K)
    (facts : ∀ i < K, Facts (divsteps (30 * i) (1, m, x)) p) :
    WP isa (.loop (batchCode L) .ne) s fun z => Bx L z B Z len N ∧
      GState len B (divsteps (30 * K) (1, m, x)) z ∧ Keeps wordClob s z ∧ Unch B (gcdWrites len) s.mem z.mem := by
  have hnw : nw len = kw len / 2 := rfl
  obtain hke := kw_eq len
  let J := fun j u => Bx L u B Z len N ∧ GState len B (divsteps (30 * (K - j)) (1, m, x)) u ∧
    w32 u.mem B 100 = j ∧ Keeps wordClob s u ∧ Unch B (gcdWrites len) s.mem u.mem
  refine VG.Proof.Weierstrass.X86.countLoop_ok (Inv := J) (n := K) ?_ ?_ hK ?_
  · intro j u hj hjK ⟨Hu, Iu, Cu, Ku, Ou⟩
    obtain F := facts (K - j) (by omega_using [hK, hj])
    refine WP.mono (batch_ok Hu hodd h3 Iu F.delta F.odd F.f F.g hp hj (by omega_using [hK32, hjK]) Cu)
      fun z ⟨Hz, Iz, Cz, Zz, Kz, Oz⟩ => ⟨⟨Hz, ?_, Cz, Ku.trans Kz, fun y hy => (Oz y hy).trans (Ou y hy)⟩, Zz⟩
    rw [show 30 * (K - (j - 1)) = 30 * (K - j) + 30 by omega_using [hj, hjK], Divstep.divsteps_add]
    exact Iz
  · intro u ⟨Hu, Iu, _, Ku, Ou⟩
    exact ⟨Hu, by simpa only [Nat.sub_zero] using Iu, Ku, Ou⟩
  · exact ⟨h, by simpa only [Nat.sub_self, Nat.mul_zero, divsteps] using hI, hc, Keeps.refl _ _,
      Unch.refl _ _ _⟩

/-- What `finish` writes. -/
def finishWrites (len : Nat) : List (Nat × Nat) :=
  [(rv (kw len) (a 12), 4 * nw len), (rv (kw len) res, 4 * nw len), (rv (kw len) (a 5), 4 * nw len)]

/-- `finish`: `|f|` into `res` and `[5] = 0`, `n` words each. -/
theorem finish_ok {s : State} (h : Bx L s B Z len N) {f : Int}
    (hb : |f| < 2 ^ (32 * nw len))
    (hc : (val32 s.mem B (rv (kw len) (a 4)) (nw len) : Int) % (2 ^ (32 * nw len) : Int) =
      f % (2 ^ (32 * nw len) : Int))
    (sign : (2 ^ 31 ≤ w32 s.mem B (rv (kw len) (a 4) + 4 * nw len)) ↔ f < 0) :
    WP isa (VG.Impl.Rsa.X86.GcdBatchRt.finish L) s fun z =>
      Bx L z B Z len N ∧ val32 z.mem B (rv (kw len) res) (nw len) = f.natAbs ∧
      val32 z.mem B (rv (kw len) (a 5)) (nw len) = 0 ∧ Keeps wordClob s z ∧
      Unch B (finishWrites len) s.mem z.mem := by
  have hnw : nw len = kw len / 2 := rfl
  obtain hke := kw_eq len
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  obtain ke := kw_eq len
  obtain r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r12 := rv_a len 12
  obtain rr := rv_res len
  obtain h41 := rv_half1' len 4
  unfold VG.Impl.Rsa.X86.GcdBatchRt.finish
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  -- `[12] = 0`, then `-[4]`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.zeros_ok h (o := a 12) (countN0 h) (by omega_using [hke, hpos]) (by omega_using [hf16, r12]))
    fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  refine WP.seq (WP.mono (chainSub_ok H₁ (o := a 12) (a := a 12) (b := a 4) (e := 0) (by decide) rfl
    (by omega_using [hke, hf16, r12]) (by omega_using [hke, hf16, r12]) (by omega_using [hke, hf16, r4]) (.inl (Nat.le_refl _)) (by omega_using [hke, r4, r12])) fun s₂ ⟨H₂, O₂, ⟨c, _, V₂⟩, K₂⟩ => ?_)
  simp only [Nat.add_zero] at O₂ V₂
  rw [V₁, Nat.zero_add, O₁.val32 (by omega_using [hnw, r4, r12]) (by omega_using [hnw, hn, hf16, r4])] at V₂
  -- The selection of `[4]` where `f` is not negative.
  refine WP.seq (maskAt_ok H₂ (x := { arr := 4, half := 1 }) (by omega_using [hf16, r4, h41]) fun s₃ K₃ m₃ c₃ => ?_)
  rw [h41, O₂.w32 (by omega_using [r4, r12]) (by omega_using [hn, hf16, r4]), O₁.w32 (by omega_using [r4, r12]) (by omega_using [hn, hf16, r4])] at c₃
  refine wp_logicS (.inr rfl) rfl fun s₄ U₄ => WP.block_nil ?_
  obtain K₄ : Keeps [.eax, .ebx, .ecx, .edx] s₂ s₄ := K₃.trans (U₄.keeps.mono (by decide))
  obtain m₄ : s₄.mem = s₂.mem := by rw [U₄.mem, m₃]
  obtain H₄ : Bx L s₄ B Z len N := H₂.keep K₄ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₄]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega_using [hf16])
  obtain mask : s₄.gpr .ecx = cmask (!decide (f < 0)) := by
    rw [U₄.gpr, ite_eq_right (by decide), c₃]
    simp only [cmask]
    by_cases hf : f < 0
    · rw [ite_eq_left (sign.mpr hf)]; simp only [hf, decide_true, Bool.not_true]; decide
    · rw [ite_eq_right (fun e => hf (sign.mp e))]; simp only [hf, decide_false, Bool.not_false]; decide
  refine WP.seq (WP.mono (selIn_ok H₄ (o := a 12) (a := a 4) (e := 0) mask (by decide) (by omega_using [hke, hf16, r12]) (by omega_using [hke, hf16, r4])
    (by omega_using [hke, r4, r12])) fun s₅ ⟨H₅, O₅, V₅, K₅⟩ => ?_)
  simp only [Nat.add_zero] at O₅ V₅
  rw [m₄, O₂.val32 (d := rv (kw len) (a 4)) (by omega_using [hke, r4, r12]) (by omega_using [hnw, hn, hf16, r4]),
    O₁.val32 (d := rv (kw len) (a 4)) (by omega_using [hnw, r4, r12]) (by omega_using [hnw, hn, hf16, r4])] at V₅
  obtain abs5 : val32 s₅.mem B (rv (kw len) (a 12)) (nw len) = f.natAbs := by
    rw [V₅]
    have := VG.Proof.Rsa.Divstep.abs_select (Nat.two_pow_pos _) hb (val32_lt _ _ _ _) (by exact_mod_cast hc) ⟨c, V₂⟩
    rw [← this]
    by_cases hf : f < 0 <;> simp [hf]
  -- `res = [12]`, then `[5] = 0`.
  refine WP.seq (WP.mono (copy_ok H₅ (o := res) (a := a 12) (e := 0) (by decide) (by omega_using [hnw, hf16, r0, rr]) (by omega_using [hke, hf16, r12])
    (by omega_using [hnw, r0, r12, rr])) fun s₆ ⟨H₆, O₆, V₆, K₆⟩ => ?_)
  simp only [Nat.add_zero] at O₆ V₆
  refine WP.mono (VG.Proof.Rsa.X86.InvBatchRt.zeros_ok H₆ (o := a 5) (countN0 H₆) (by omega_using [hke, hpos]) (by omega_using [hf16, r5]))
    fun z ⟨Hz, O₇, V₇, K₇⟩ => ⟨Hz, ?_, V₇, ?_, ?_⟩
  · rw [O₇.val32 (by omega_using [r0, r5, rr]) (by omega_using [hn, hf16, r0, rr]), V₆, abs5]
  · exact ((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₄.mono (by decide))).trans
      (K₅.mono (by decide))).trans ((K₆.mono (by decide)).trans (K₇.mono (by decide)))
  · intro x hx
    obtain h1 := hx (rv (kw len) (a 12), 4 * nw len) (by simp [finishWrites])
    obtain h2 := hx (rv (kw len) res, 4 * nw len) (by simp [finishWrites])
    obtain h3 := hx (rv (kw len) (a 5), 4 * nw len) (by simp [finishWrites])
    simp only at h1 h2 h3
    rw [O₇ x h3, O₆ x h2, O₅ x h1, m₄, O₂ x h1, O₁ x h1]

/-- The batched GCD: `gcd(m, x)` into `res` and `[5] = 0`, `n - 1` words each. -/
theorem body_ok {s : State} (h : RtWs L s B Z len N) (room : 16 ≤ N) (hodd : nw len % 2 = 1)
    (h3 : 3 ≤ nw len) (hmax : nw len ≤ 1024) {m x : Nat}
    (hm : val32 s.mem B (rv (kw len) (a 4)) (nw len - 1) = m)
    (hx : val32 s.mem B (rv (kw len) (a 0)) (nw len - 1) = x) (odd : m % 2 = 1) :
    WP isa (VG.Impl.Rsa.X86.GcdBatchRt.body L) s fun z => Bx L z B Z len N ∧
      val32 z.mem B (rv (kw len) res) (nw len - 1) = Nat.gcd m x ∧
      val32 z.mem B (rv (kw len) (a 5)) (nw len - 1) = 0 ∧
      Keeps wordClob s z ∧ Unch B (gcdWrites len) s.mem z.mem := by
  have hnw : nw len = kw len / 2 := rfl
  obtain hke := kw_eq len
  have hn := h.ws.workspace.nowrap
  obtain mlt : m < 2 ^ (32 * (nw len - 1)) := hm ▸ val32_lt _ _ _ _
  obtain xlt : x < 2 ^ (32 * (nw len - 1)) := hx ▸ val32_lt _ _ _ _
  obtain up : 2 ^ (32 * (nw len - 1)) ≤ 2 ^ (32 * nw len) := Nat.pow_le_pow_right (by decide) (by omega_using [])
  obtain mp : m < 2 ^ (32 * nw len) := by omega_using [mlt, up]
  obtain xp : x < 2 ^ (32 * nw len) := by omega_using [xlt, up]
  let y := oddInput m x
  let K := 3 * (nw len + 1)
  obtain done := VG.Proof.Rsa.Divstep.oddInput_done odd mp xp
  obtain yl := VG.Proof.Rsa.Divstep.oddInput_lt mp xp
  obtain hp : max m y < 2 ^ (32 * nw len + 1) := by
    have := Nat.two_pow_pos (32 * nw len); rw [Nat.pow_succ]; omega_using [mlt, up, yl]
  unfold VG.Impl.Rsa.X86.GcdBatchRt.body
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (init_ok h room h3 hm hx) fun s₁ ⟨H₁, I₁, C₁, K₁, O₁⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok H₁ hodd h3 (K := K) (by omega_using []) (by omega) hp I₁ C₁
    (fun i hi => runFacts hmax hi odd (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
    fun s₂ ⟨H₂, I₂, K₂, O₂⟩ => ?_)
  let f := (divsteps (30 * K) (1, (m : Int), (y : Int))).2.1
  obtain gl : Nat.gcd m x < 2 ^ (32 * (nw len - 1)) := (Nat.gcd_le_left x (by omega_using [odd])).trans_lt mlt
  obtain absBound : |f| < (2 : Int) ^ (32 * nw len) := by
    obtain hNat : f.natAbs < 2 ^ (32 * nw len) := by rw [done.2]; omega_using [up, gl]
    obtain hInt : (f.natAbs : Int) < (2 : Int) ^ (32 * nw len) := by exact_mod_cast hNat
    simpa only [Int.natCast_natAbs] using hInt
  refine WP.mono (finish_ok H₂ absBound (VG.Proof.Rsa.X86.GcdBatch.encoding_low I₂.f)
    (VG.Proof.Rsa.X86.GcdBatch.encoding_sign I₂.f absBound)) fun z ⟨Hz, Gz, Zz, Kz, Oz⟩ => ?_
  have hf16 := Hz.fits16
  obtain r0 := rv_a len 0; have r5 := rv_a len 5; have r11 := rv_a len 11; have r12 := rv_a len 12
  obtain rr := rv_res len
  refine ⟨Hz, ?_, ?_, (K₁.trans K₂).trans Kz, ?_⟩
  · rw [show nw len = nw len - 1 + 1 by omega_using [hodd], done.2] at Gz
    exact (low_eq Gz gl).1
  · rw [show nw len = nw len - 1 + 1 by omega_using [hodd]] at Zz
    exact (low_eq Zz (Nat.two_pow_pos _)).1
  · intro y hy
    obtain h1 := hy (win, 88) (by simp [gcdWrites])
    obtain h2 := hy (rv (kw len) (a 0), 6 * (8 * nw len + 8)) (by simp [gcdWrites])
    obtain h3 := hy (rv (kw len) (a 11), 2 * (8 * nw len + 8)) (by simp [gcdWrites])
    simp only at h1 h2 h3
    rw [Oz y (by
      intro w hw; simp only [finishWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega_arith), O₂ y hy, O₁ y hy]

end VG.Proof.Rsa.X86.GcdBatchRt
