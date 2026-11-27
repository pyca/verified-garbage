module

public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRows
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightInternal
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath

/-! ### `Bignum.AArch64.SquareEightOffDiagonal`, which the modules that import this one used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Bignum.AArch64
open VG.Proof.Bignum.AArch64.ProductEight
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)

private theorem pending_power (i j : Nat) :
    2 ^ (64*i) * 2 ^ (64*i) * (2 ^ 64) ^ j = 2 ^ (64*(2*i+j)) := by
  rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
  congr 1
  omega_using []

private theorem pending_scale {w r p c a b term : Nat}
    (hp : w*w*r = p) (hl : a+w*(w*r*c) = b+w*term+w*0) : a+p*c = b+w*term := by
  grind

/-- The first triangular row has no earlier tiles. Later rows retain the
pending carry in the existing eight-limb product invariant. -/
theorem offDiagonal_ok {s : State} {B : Addr} {Z eQ eT eN k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (h10 : s.gpr .x10 = 0) (h16 : s.gpr .x16 = off B eT)
    (h17 : s.gpr .x17 = off B eN) (h15 : s.gpr .x15 = BitVec.ofNat 64 k)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64*(k+1) ≤ Z) (hN : eN+64*k ≤ Z)
    (hQT : eQ+64 ≤ eT ∨ eT+64*(k+1) ≤ eQ)
    (hNT : eN+64*k ≤ eT ∨ eT+64*(k+1) ≤ eN) (hk : k < 2 ^ 64) :
    WP isa (.ite (.nonzero .x .x15)
      (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) (.block [])) s
      (ProductColumnInv s B eQ eT eN k k) := by
  by_cases hz : k = 0
  · subst k
    refine WP.ite false (by rw [eval_nonzero, h15]; rfl) (by simp) (fun _ => ?_)
    apply WP.block_nil
    refine ⟨?_, ?_, ?_, ?_, Outside.refl _ _ _ _, Keep.refl _ _⟩
    · simp only [h10, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, show wv s.mem B eN 0 = 0 from rfl]
    · rw [h10]; exact Nat.zero_le 1
    · simpa only [Nat.mul_zero, Nat.add_zero] using h16
    · simpa only [Nat.mul_zero, Nat.add_zero] using h17
  · refine WP.ite true (by
      rw [eval_nonzero, h15, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
      simp [hz]) (fun _ => ?_) (by simp)
    exact productColumns_ok hs h8 h7 h10 h16 h17 h15 hQ hT hN hQT hNT (by omega_using [hz]) hk

/-- Lift the off-diagonal products and their pending carry to the full
square buffer, including every untouched word. -/
theorem offDiagonal_full {s : State} {B : Addr} {Z eQ eT eN i n : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (h10 : s.gpr .x10 = 0) (h16 : s.gpr .x16 = off B (eT+64*i))
    (h17 : s.gpr .x17 = off B eN) (h15 : s.gpr .x15 = BitVec.ofNat 64 i)
    (hQ : eQ+64 ≤ Z) (hT : eT+8*n ≤ Z) (hN : eN+64*i ≤ Z)
    (hQT : eQ+64 ≤ eT ∨ eT+8*n ≤ eQ)
    (hNT : eN+64*i ≤ eT ∨ eT+8*n ≤ eN) (hi : i < 2 ^ 64) (hin : 16*i+8 ≤ n) :
    WP isa (.ite (.nonzero .x .x15)
      (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) (.block [])) s fun t =>
      wv t.mem B eT n + 2 ^ (64*(16*i+8))*(t.gpr .x10).toNat =
        wv s.mem B eT n + 2 ^ (64*(8*i))*(wv s.mem B eQ 8 * wv s.mem B eN (8*i)) ∧
      Outside B (eT+64*i) (64*(i+1)) s.mem t.mem ∧ Keep productColumnRegs s t := by
  have hn := hs.nowrap
  refine WP.mono (offDiagonal_ok hs h8 h7 h10 h16 h17 h15 hQ (by omega_using [hT, hin]) hN
    (by omega_using [hQT, hin]) (by omega_using [hNT, hin]) hi) fun t ht => ?_
  have hf := ProductEight.wv_window_delta (n := n) (j := 8*i) (k := 8*(i+1))
    (by omega_using [hT, hn] : eT+8*n ≤ 2 ^ 64) (by omega_using [hin])
    (by simpa only [show 8*(8*i) = 64*i by omega_using [], show 8*(8*(i+1)) = 64*(i+1) by omega_using []] using ht.frame)
  simp only [show 8*(8*i) = 64*i by omega_using []] at hf
  have hv := ht.value
  have heq : wv t.mem B (eT+64*i) (8*(i+1)) +
      (2 ^ (64*(8*i)) * (2 ^ 64) ^ 8) * (t.gpr .x10).toNat =
        wv s.mem B (eT+64*i) (8*(i+1)) + wv s.mem B eQ 8 * wv s.mem B eN (8*i) + 0 :=
    hv.trans (Nat.add_zero _).symm
  have hl := ProductEight.window_lift hf heq
  have hp : (2 ^ (64*(8*i)) * 2 ^ (64*(8*i))) * (2 ^ 64) ^ 8 = 2 ^ (64*(16*i+8)) := by
    simpa only [show 2*(8*i) = 16*i by omega_using []] using pending_power (8*i) 8
  exact ⟨pending_scale hp hl, ht.frame, ht.keep⟩

end VG.Proof.Bignum.AArch64.SquareEight

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.ProductEight (productBase)

abbrev headRegs := codeRegs ++ [.x13, .x16, .x17, .x15, .x10]

theorem rowHead_ok {s : State} {B : Addr} {Z k i a : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0)
    (hH : Hdr s.mem B (8*k) minv) (hZ : slot (8*k) 8 ≤ Z) (ha : a < 8)
    (hk : k < 2 ^ 56) (hi : i < k)
    (h8 : s.gpr .x8 = off B (slot (8*k) a+64*i))
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (k-i))
    (hv : wv s.mem B (productBase k) (16*k+2) < 2 ^ (64*(16*i))) :
    WP isa (.block (SquareEightRaw.rowHead a)) s fun t =>
      (wv t.mem B (productBase k) (16*k+2) = wv s.mem B (productBase k) (16*k+2) +
        2 ^ (64*(16*i))*Square.crossValue s.mem B (slot (8*k) a+64*i) 8 ∧
       t.gpr .x16 = off B (productBase k+64*i) ∧ t.gpr .x17 = off B (slot (8*k) a) ∧
       t.gpr .x15 = BitVec.ofNat 64 i ∧ t.gpr .x10 = 0 ∧
       Outside B (productBase k) (8*(16*k+2)) s.mem t.mem) ∧ Keep headRegs s t := by
  have hP : productBase k+8*(16*k+2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega_using [hZ]
  have hA : slot (8*k) a+64*k ≤ Z := by
    have := slot_le (w := 8*k) ha
    omega_using [hZ, this]
  unfold SquareEightRaw.rowHead
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine WP.mono (outputPtr_ok hs h0 hH hZ ha (by omega_using [hk, hi]) h8 true) fun u ⟨⟨hu16, _, hum⟩, ku⟩ => ?_
  apply WP.block_append
  refine WP.mono (internal_ok (hs.congr ku.wr) ((ku.gpr _ (by decide)).trans h8) hu16
    ((ku.gpr _ (by decide)).trans h7) (by omega_using [hi, hA]) hP (by omega_using [hi])
    (by simpa only [hum] using hv)) fun v ⟨hvv, hvo, kv⟩ => ?_
  have huv := ku.trans kv
  have ho : Outside B (productBase k) (8*(16*k+2)) s.mem v.mem := by
    intro x hx
    exact ((hvo.mono (by omega_using []) (by omega_using [hi])) x hx).trans (congrArg (fun m : Mem => m x) hum)
  have hHv : Hdr v.mem B (8*k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2*(8*k) = 16*k by omega_using []] using ho)).hdr hH
  have hval : wv v.mem B (productBase k) (16*k+2) = wv s.mem B (productBase k) (16*k+2) +
      2 ^ (64*(16*i))*Square.crossValue s.mem B (slot (8*k) a+64*i) 8 := by
    simpa only [hum] using hvv
  apply WP.block_append
  refine WP.mono (clearPending_ok v) fun v' ⟨⟨hv10, hvm⟩, kc⟩ => ?_
  have kvc := huv.trans kc
  apply WP.block_append
  refine WP.mono (outputPtr_ok (hs.congr kvc.wr) ((kvc.gpr _ (by decide)).trans h0)
    (hvm ▸ hHv) hZ ha (by omega_using [hk, hi]) ((kvc.gpr _ (by decide)).trans h8) false)
    fun b ⟨⟨hb16, hb17, hbm⟩, kb⟩ => ?_
  have kab := kvc.trans kb
  have hbH : Hdr b.mem B (8*k) minv := (hbm.trans hvm) ▸ hHv
  refine WP.mono (rowCount_ok (hs.congr kab.wr) ((kab.gpr _ (by decide)).trans h0)
    hbH hZ hk (by omega_using [hi]) ((kab.gpr _ (by decide)).trans h12))
    fun t ⟨⟨ht15, htm⟩, kt⟩ => ?_
  have hm := htm.trans (hbm.trans hvm)
  refine ⟨⟨?_, (kt.gpr _ (by decide)).trans hb16, (kt.gpr _ (by decide)).trans hb17,
    ht15, (kt.gpr _ (by decide)).trans ((kb.gpr _ (by decide)).trans hv10), ?_⟩,
    (kab.trans kt).mono (by decide)⟩
  · exact (congrArg (fun m : Mem => wv m B (productBase k) (16*k+2)) hm).trans hval
  · intro x hx
    exact (congrArg (fun m : Mem => m x) hm).trans (ho x hx)

end VG.Proof.Bignum.AArch64.SquareEight
