module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductState

public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductStart
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.WideProduct
import VerifiedGarbage.Proof.Bignum.Arm.WideProductState
import VerifiedGarbage.Proof.Bignum.Arm.WideProductBody
/-! # Exact factor multiplication, including buffer initialization -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/WideProduct.lean`, which only this module imported.
section

/-! # Exact wide multiplication terminates after the public number of source words -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem wideProduct_ok (s : State) {base : BitVec 32} {size o a b m n : Nat}
    (ctx : WideProductCtx s base size o a b m n)
    (ptr : s.gpr .r0 = base)
    (aPtr : s.mem.readW (off (State.addr base) 128) 32 = base + BitVec.ofNat 32 a)
    (bPtr : s.mem.readW (off (State.addr base) 132) 32 = base + BitVec.ofNat 32 b)
    (oPtr : s.mem.readW (off (State.addr base) 136) 32 = base + BitVec.ofNat 32 o)
    (count : s.mem.readW (off (State.addr base) 140) 32 = BitVec.ofNat 32 m)
    (width : s.mem.readW (off (State.addr base) 144) 32 = BitVec.ofNat 32 n)
    (zero : val32 s.mem (State.addr base) o (m + n + 2) = 0) :
    WP isa wideProduct s fun t =>
      val32 t.mem (State.addr base) o (m + n + 2) =
        val32 s.mem (State.addr base) a m * val32 s.mem (State.addr base) b n ∧
      Outs (State.addr base) [(128, 16), (o, 4 * (m + n + 2))] s.mem t.mem ∧
      t.gpr .r0 = base ∧ Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => ∃ i, i + k = m ∧ 0 < k ∧ WideProductInv s base o a b m n i t
  unfold wideProduct
  refine WP.loop (M := isa) I ?_ m s ?_
  · intro k t inv
    obtain ⟨i, ik, hk, hi⟩ := inv
    refine WP.mono (wideProductBody_ok t ctx hi (by omega)) ?_
    rintro u ⟨next, zero⟩
    by_cases last : i + 1 = m
    · left
      refine ⟨?_, ?_, next.outside, next.ptr, ctx.frame next.outside, next.rest⟩
      · change some (!u.z) = some false
        simp only [zero, last, decide_true, Bool.not_true]
      · simpa only [last] using next.value
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, next⟩
      change some (!u.z) = some true
      simp only [zero, last, decide_false, Bool.not_false]
  · refine ⟨0, by omega, ctx.positiveA, ?_⟩
    refine ⟨by omega, ptr, ?_, bPtr, ?_, ?_, width, Outs.refl _ _ _, ?_, Rest.refl _ _⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using aPtr
    · simpa only [Nat.mul_zero, Nat.add_zero] using oPtr
    · simpa only [Nat.sub_zero] using count
    · simp only [val32, Nat.zero_mul]; exact zero

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- The first `k` of `n` zero words. -/
theorem val32_zero_prefix {mem : Mem} {B : Addr} {d n k : Nat} (h : val32 mem B d n = 0) (hk : k ≤ n) :
    val32 mem B d k = 0 := by
  have a := val32_append mem B d k (n - k)
  rw [show k + (n - k) = n by omega_using [hk], h] at a
  omega_using [a]

/-- The product of the first `m` words of `a` and `n` of `b`, its output of
`4 w + 2` words cleared first, by `count`'s counts. -/
theorem crt_factorProductWith_ok (s : State) {base : BitVec 32} {size o a b cp cq w m n : Nat} {coefficient : Bool}
    {count : List Instr} (h : CrtProductInput base size o a b cp cq w s coefficient)
    (hc : CountFrom count base size m n s) (hm : 0 < m) (hm' : m ≤ 2 * w) (hn : 0 < n) (hn' : n ≤ 2 * w) :
    WP isa (factorProductWith coefficient count) s fun t =>
      val32 t.mem (State.addr base) o (2 * w + 2 * w + 2) =
        val32 s.mem (State.addr base) a m * val32 s.mem (State.addr base) b n ∧
      Outs (State.addr base) [(128, 20), (o, 4 * (2 * w + 2 * w + 2))] s.mem t.mem ∧
      t.gpr .r0 = base ∧ Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have nowrap := h.workspace.nowrap
  have aFits := h.aFits
  have bFits := h.bFits
  have aHeader := h.aHeader
  have bHeader := h.bHeader
  have outFits := h.outFits
  have sepA := h.separateA
  have sepB := h.separateB
  have oHeader := h.oHeader
  rw [factorProductWith, WP.seq_iff]
  refine WP.mono (crt_productClear_ready s h) ?_
  rintro u ⟨inputU, zeroU, outsideU, frameU, restU⟩
  have aU := outsideU.val32 (d := a) (k := m) (by omega_using [hm', sepA]) (by omega_using [hm', nowrap, aFits])
  have bU := outsideU.val32 (d := b) (k := n) (by omega_using [hn', sepB]) (by omega_using [hn', nowrap, bFits])
  -- The cleared output: its first `m + n + 2` words, and those above them.
  have split := val32_append u.mem (State.addr base) o (m + n + 2) (2 * w + 2 * w + 2 - (m + n + 2))
  rw [show m + n + 2 + (2 * w + 2 * w + 2 - (m + n + 2)) = 2 * w + 2 * w + 2 by omega_using [hm', hn'], zeroU] at split
  have pos := Nat.two_pow_pos (32 * (m + n + 2))
  have zeroLo : val32 u.mem (State.addr base) o (m + n + 2) = 0 := by omega_using [split]
  have zeroHi : val32 u.mem (State.addr base) (o + 4 * (m + n + 2)) (2 * w + 2 * w + 2 - (m + n + 2)) = 0 := by
    rcases Nat.eq_zero_or_pos (val32 u.mem (State.addr base) (o + 4 * (m + n + 2))
      (2 * w + 2 * w + 2 - (m + n + 2))) with z | z
    · exact z
    · have := Nat.le_mul_of_pos_right (2 ^ (32 * (m + n + 2))) z; omega_using [split, pos, this]
  have hcU : CountFrom count base size m n u := hc.after restU.sp restU.rd restU.wr frameU
    (outside_read32 outsideU (d := 48) (by omega_using [oHeader]) (by omega_using []))
  rw [WP.seq_iff]
  refine WP.mono (crt_productArgsWith_ready u inputU hcU hm hm' hn hn' zeroLo) ?_
  rintro v ⟨start, outsideV, frameV, restV⟩
  have aV := outsideV.val32 (d := a) (k := m) (by omega_using [aHeader]) (by omega_using [hm', nowrap, aFits])
  have bV := outsideV.val32 (d := b) (k := n) (by omega_using [bHeader]) (by omega_using [hn', nowrap, bFits])
  have hiV := outsideV.val32 (d := o + 4 * (m + n + 2)) (k := 2 * w + 2 * w + 2 - (m + n + 2)) (by omega_using [oHeader])
    (by omega_using [hm, hm', hn, hn', nowrap, aFits, bFits, aHeader, bHeader, outFits, sepA, sepB, oHeader])
  have initial := start.initial
  have p := initial.aPtr
  have out := initial.oPtr
  have count := initial.count
  have zero := initial.value
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, val32, Nat.zero_mul] at p out count zero
  refine WP.mono (wideProduct_ok v start.context initial.ptr p initial.bPtr out count initial.width zero) ?_
  rintro t ⟨value, outsideT, ptrT, frameT, restT⟩
  rw [aV, bV, aU, bU] at value
  have hiT := outsideT.val32 (d := o + 4 * (m + n + 2)) (k := 2 * w + 2 * w + 2 - (m + n + 2))
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [hm, hm', hn, hn', nowrap, aFits, bFits, aHeader, bHeader, outFits, sepA, sepB, oHeader])
  have widened : Outs (State.addr base) [(128, 20), (o, 4 * (2 * w + 2 * w + 2))] v.mem t.mem := by
    intro x hx
    apply outsideT x
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hfirst := hx (128, 20) (by simp)
      omega_using [hfirst]
    · have hsecond := hx (o, 4 * (2 * w + 2 * w + 2)) (by simp)
      simp only at hsecond ⊢
      omega_using [hm', hn', hsecond]
  refine ⟨?_, (Outs.of_outside outsideU (by simp)).trans ((Outs.of_outside outsideV (by simp)).trans widened),
    ptrT, frameU.trans (frameV.trans frameT), restU.trans ((restV.mono (by decide)).trans restT)⟩
  rw [show 2 * w + 2 * w + 2 = m + n + 2 + (2 * w + 2 * w + 2 - (m + n + 2)) by omega_using [hm', hn'], val32_append, value, hiT,
    hiV, zeroHi, Nat.mul_zero, Nat.add_zero]

theorem crt_factorProduct_ok (s : State) {base : BitVec 32} {size o a b cp cq w : Nat} {coefficient : Bool}
    (h : CrtProductInput base size o a b cp cq w s coefficient) :
    WP isa (factorProduct coefficient) s fun t =>
      val32 t.mem (State.addr base) o (2 * w + 2 * w + 2) =
        val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) ∧
      Outs (State.addr base) [(128, 20), (o, 4 * (2 * w + 2 * w + 2))] s.mem t.mem ∧
      t.gpr .r0 = base ∧ Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t :=
  crt_factorProductWith_ok s h (countFrom_productCount h.headerFit h.count) h.positiveA (Nat.le_refl _)
    h.positiveB (Nat.le_refl _)

end VG.Proof.Bignum.Arm
