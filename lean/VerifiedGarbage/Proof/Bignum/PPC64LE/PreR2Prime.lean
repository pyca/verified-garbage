module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Fast
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreDouble
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# The precomputed values of an RSA modulus on PPC64LE: `R² mod n` for any odd `n`

`r2Prime_ok`: `x := 2^(128 w) mod n`, for any odd `n > 1` of `w` words:
`x := 1`, `64 w + w` doublings to `2^w R mod n`, then six Montgomery squares
(`r2Sq_ok`, counted by `r24`), each doubling the exponent of `2^e R mod n`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute
open VG.Proof.Bignum.PPC64LE

/-- The registers `r2Prime` writes. -/
def r2PrimeRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24]

/-- What holds between the squares, with `x ≡ 2^e R (mod N)`. -/
structure SqP (s : State) (B : Addr) (Z w N e : Nat) (t : State) : Prop where
  scr : Scr t B Z
  r10 : t.gpr .r10 = off B (slot w 0)
  r11 : t.gpr .r11 = BitVec.ofNat 64 (2 * w)
  r12 : (t.gpr .r12).toNat < 2 ^ 32
  inv : (w32 t.mem B (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  n : val32 t.mem B (slot w 0) (2 * w) = N
  lt : val32 t.mem B (slot w 1) (2 * w) < N
  x : val32 t.mem B (slot w 1) (2 * w) % N = 2 ^ e * 2 ^ (64 * w) % N
  out : Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem
  keep : Keep r2PrimeRegs s t

theorem sqP_step {s t : State} {B : Addr} {Z w N e : Nat} (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hodd : N % 2 = 1) (h : SqP s B Z w N e t) :
    WP isa r2Sq t fun u => SqP s B Z w N (2 * e) u ∧ u.gpr .r24 = t.gpr .r24 := by
  have hnw := h.scr.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  refine WP.mono (r2Sq_ok h.scr hw2 hw' hZ h.r10 h.r11 h.r12 h.inv (by rw [h.n]; exact h.lt))
    fun u ⟨⟨ul, ue, uo⟩, k⟩ => ?_
  rw [h.n] at ul ue
  have uo' : Mont.Outside B (slot w 1) (24 * (w + 2)) t.mem u.mem := fun x hx => uo x fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [Mont.ofs] at hx
    rcases hr with rfl | rfl | rfl <;> simp only [Mont.ofs] <;> omega
  have n0 : val32 u.mem B (slot w 0) (2 * w) = N := by rw [uo'.val32 (by omega) (by omega), h.n]
  have w0 : w32 u.mem B (slot w 0) = w32 t.mem B (slot w 0) := by
    have := uo'.val32 (d := slot w 0) (k := 1) (by omega) (by omega)
    simpa [val32] using this
  have g : ∀ r ∈ [Reg.r10, .r11, .r12], u.gpr r = t.gpr r := fun r hr => k.gpr r (by revert r hr; decide)
  exact ⟨⟨h.scr.congr k.wr, (g .r10 (by decide)).trans h.r10, (g .r11 (by decide)).trans h.r11,
    by rw [g .r12 (by decide)]; exact h.r12, by rw [g .r12 (by decide), w0]; exact h.inv, n0, ul,
    Pub.sq_step hR h.x ue, h.out.trans uo', (h.keep.trans k).mono⟩, k.gpr .r24 (by decide)⟩

theorem SqP.of_keep {s t u : State} {B : Addr} {Z w N e : Nat} (h : SqP s B Z w N e t) (k : Keep [.r24] t u)
    (hm : u.mem = t.mem) : SqP s B Z w N e u :=
  ⟨h.scr.congr k.wr, (k.gpr _ (by decide)).trans h.r10, (k.gpr _ (by decide)).trans h.r11,
    by rw [k.gpr .r12 (by decide)]; exact h.r12, by rw [k.gpr .r12 (by decide), hm]; exact h.inv,
    by rw [hm]; exact h.n, by rw [hm]; exact h.lt, by rw [hm]; exact h.x, by rw [hm]; exact h.out,
    (h.keep.trans k).mono⟩

/-- `r2Prime`, with an odd `n > 1` in array 0, `-n⁻¹ mod 2³²` in `r12` and the
bases of arrays 1–3 in `r5`, `r8`, `r9`: `x := 2^(128 w) mod n` in array 1,
changing only arrays 1–3. -/
theorem r2Prime_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (slot w 2)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hN : 2 ≤ val32 s.mem B (slot w 0) (2 * w)) (hodd : val32 s.mem B (slot w 0) (2 * w) % 2 = 1) :
    WP isa r2Prime s fun t =>
      val32 t.mem B (slot w 1) (2 * w) = 2 ^ (128 * w) % val32 s.mem B (slot w 0) (2 * w) ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep r2PrimeRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  generalize hNd : val32 s.mem B (slot w 0) (2 * w) = N at hN hodd ⊢
  have hN0 : 0 < N := by omega
  unfold r2Prime
  -- `x := 1`.
  refine WP.seq (WP.mono (one_ok hs h5 h11 (by omega) hw' (by omega)) fun s₁ ⟨x1, o1, k1⟩ => ?_)
  have O1 : Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem s₁.mem := o1.mono (Nat.le_refl _) (by omega)
  -- The count.
  refine WP.seq (WP.mono (WP.keep [.r4, .r3] (Q := fun t => t.gpr .r4 = BitVec.ofNat 64 (64 * w + w) ∧
    t.mem = s₁.mem)
    (by
      prun [(k1.gpr .r11 (by decide)).trans h11]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
        Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.reducePow]
      rw [Nat.mod_eq_of_lt (show 2 * w < 18446744073709551616 by omega),
        Nat.mod_eq_of_lt (show 2 * w * 32 < 18446744073709551616 by omega)]
      omega) (by decide)) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  -- The doublings.
  have O2 : Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem s₂.mem := by rw [m2]; exact O1
  refine WP.seq (WP.mono (r2Dbl_ok (N := N) (a := 0) (M := 64 * w + w) (hs.congr k12.wr)
    ((k12.gpr _ (by decide)).trans h8) ((k12.gpr _ (by decide)).trans h9) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h5) ((k12.gpr _ (by decide)).trans h11) (by omega) hw' (by omega)
    (by rw [O2.val32 (by omega) (by omega), hNd]) hN0
    (by rw [m2, x1, Nat.pow_zero, Nat.mod_eq_of_lt (by omega)]) a4 (by omega) (by omega))
    fun s₃' ⟨x3', o3', k3'⟩ => ?_)
  have x3 : val32 s₃'.mem B (slot w 1) (2 * w) = 2 ^ (64 * w + w) % N := by rw [x3', Nat.zero_add]
  have o3 := O2.trans o3'
  have k3 : Keep [.r0, .r14, .r17, .r4, .r3, .r15, .r16, .r20] s s₃' := (k12.trans k3').mono (by decide)
  generalize s₃' = s₃ at x3 o3 k3
  -- Six squares.
  have n3 : val32 s₃.mem B (slot w 0) (2 * w) = N := by rw [o3.val32 (by omega) (by omega), hNd]
  have I0 : SqP s B Z w N w s₃ := by
    have w3 : w32 s₃.mem B (slot w 0) = w32 s.mem B (slot w 0) := by
      have := o3.val32 (d := slot w 0) (k := 1) (by omega) (by omega)
      simpa [val32] using this
    refine ⟨hs.congr k3.wr, (k3.gpr _ (by decide)).trans h10, (k3.gpr _ (by decide)).trans h11,
      by rw [k3.gpr .r12 (by decide)]; exact h12, by rw [k3.gpr .r12 (by decide), w3]; exact hinv, n3, ?_, ?_, o3,
      k3.mono⟩
    · rw [x3]; exact Nat.mod_lt _ hN0
    · rw [x3, Nat.mod_mod, show 64 * w + w = w + 64 * w by omega, Nat.pow_add]
  refine WP.seq (WP.mono (WP.keep [.r24] (Q := fun u => u.gpr .r24 = BitVec.ofNat 64 6 ∧ u.mem = s₃.mem)
    (by prun) (by decide)) fun s₄ ⟨⟨a24, m4⟩, k4⟩ => ?_)
  let Inv : Nat → State → Prop := fun j u => SqP s B Z w N (w * 2 ^ j) u
  refine WP.mono (wp_countdown (cnt := .r24) (N := 6) (by decide) (by decide) Inv
    (fun j _ u I _ => ?_) (by simp only [Inv, Nat.pow_zero, Nat.mul_one]; exact I0.of_keep k4 m4) a24)
    fun t I6 => ?_
  · refine WP.seq (WP.mono (sqP_step hw hw' hZ hodd I) fun u₁ ⟨I1, g24⟩ => ?_)
    refine WP.mono (subi_ok u₁ .r24 (by decide)) fun u₂ e2 => ?_
    subst e2
    have he : w * 2 ^ (j + 1) = 2 * (w * 2 ^ j) := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2]
    refine ⟨?_, by simp only [gpr_write, ↓reduceIte, g24]⟩
    show SqP s B Z w N (w * 2 ^ (j + 1)) _
    rw [he]
    exact I1.of_keep (Keep.write _ _ _) (mem_write _ _ _)
  refine ⟨?_, I6.out, I6.keep⟩
  have h6 : w * 2 ^ 6 = 64 * w := by rw [show (2 : Nat) ^ 6 = 64 from rfl, Nat.mul_comm]
  rw [← Nat.mod_eq_of_lt I6.lt, I6.x, h6, ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega]

end VG.Proof.Bignum.PPC64LE.Pre
