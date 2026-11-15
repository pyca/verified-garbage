module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.VecR
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubVec
public import VerifiedGarbage.Impl.Ffdh.X86_64.Ifma
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Vec
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.VecR
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubVec
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Ifma
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Vec
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH's exponentiation with AVX512_IFMA on x86-64: the vector code

`vec_ok`: `Ifma.vec`, one lane of `CrtIfma.expLoop` from the digit at `oSt`
(`expLoopFrom_ok`), then `vzeroupper`, with no MXCSR of its own (its
dispatcher's `vg_mcdt_enter` sets it: `Ifma.withVzu`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Impl.Ffdh.X86_64.Ifma
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Bignum.X86_64.Ifma
open VG.Proof.Bignum.X86_64.AmmSym (limbN limbN_lt pow2_le cop2 writeW32_outside)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The first digit, from `rbp`. -/
theorem start_ok {t : State} {i₀ : Nat} (hv : t.gpr .rbp = BitVec.ofNat 64 i₀) :
    WP isa (.block [.mov .r13 (.reg .rbp)]) t fun u => u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
      u.mxcsr = t.mxcsr ∧ u.gpr .r13 = BitVec.ofNat 64 i₀ ∧ ∀ r, r ≠ .r13 → u.gpr r = t.gpr r := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun u =>
    u.gpr .r13 = BitVec.ofNat 64 i₀ ∧ u.mem = t.mem ∧ u.mxcsr = t.mxcsr) (by
    xrun [hv]; rfl) rfl)
    fun u ⟨⟨a, b, c⟩, k⟩ => ⟨b, k.2.1, k.2.2, c, a, fun r hr => k.gpr (by simp [hr])⟩

/-- A word above the lanes' regions, through a frame of them. -/
theorem Out2.word_hi (hl : AmmOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m') {c : Nat}
    (hoD : o + n ≤ l.D) (hc : l.nl * l.D ≤ c) (hz : c + 8 ≤ 2 ^ 64) : word m' B c = word m B c := by
  refine (Mem.readW_congr fun i hi => (h _ fun p hp => ?_).symm).symm
  rw [ofs_off B (by omega_using [hz, hi])]
  have := lane_end hl hp
  exact .inr (by omega_using [hoD, hc, this])

/-- The vector code, from what the region holds (as `vecR_ok`), from the
digit `i₀` at `oSt`, before which the exponents' digits are zero. -/
theorem vec_ok (hl : AmmOk l) (hz0 : l.z = false) {s : State} {F : Addr} {M K1 Xc Y Fin x e : Nat → Nat}
    {mi : Nat → BitVec 64} {Q : Prop} {w R i₀ : Nat}
    (hw : w = l.W) (hR : R = 2 ^ (64 * w)) (hB : s.gpr .rbx = F) (hs : Scr s F (oSt l + 8))
    (hM : LimbsAt l s.mem F oM M) (hK : LimbsAt l s.mem F l.oK1 K1) (hX : LimbsAt l s.mem F l.oX Xc)
    (hY : LimbsAt l s.mem F l.oY Y) (hF : LimbsAt l s.mem F l.oFin Fin)
    (hk0 : ∀ p < l.nl, ∀ t < 4, word s.mem F (l.D * p + l.oK0 + 8 * t) = mi p &&& mask52)
    (hinv : ∀ p < l.nl, (M p % 2 ^ 64 * (mi p).toNat + 1) % 2 ^ 64 = 0)
    (hMlt : ∀ p < l.nl, M p < 2 ^ (64 * w)) (hModd : ∀ p < l.nl, M p % 2 = 1)
    (hKlt : ∀ p < l.nl, K1 p < M p) (hXlt : ∀ p < l.nl, Xc p < M p) (hYlt : ∀ p < l.nl, Y p < M p)
    (hFlt : ∀ p < l.nl, Fin p < 2 * M p)
    (vx : Q → ∀ p < l.nl, Xc p % M p = x p * R % M p)
    (vy : Q → ∀ p < l.nl, Y p % M p = R % M p)
    (vk : Q → ∀ p < l.nl, K1 p % M p = 2 ^ l.dbls * R % M p)
    (hi₀ : i₀ ≤ l.ND) (hst : s.gpr .rbp = BitVec.ofNat 64 i₀)
    (hz : ∀ p < l.nl, e p / l.T ^ (l.ND - i₀) = 0)
    (hd : ∀ p < l.nl, ∀ i < l.ND, dig l s.mem F p i = digit l (e p) i) :
    WP isa (Impl.Ffdh.X86_64.Ifma.vec l) s fun s' =>
      (∀ p < l.nl, GoodS l s'.mem F M l.oY p ∧
        (Q → val52 l s'.mem F (l.D * p + l.oY) % M p = x p ^ e p * Fin p % M p)) ∧
      Outside F 0 (l.nl * l.D + 8) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  subst hR hw
  obtain ⟨cb1, cb2, cb3, cb4, cb5, cb6⟩ := conv_boundsN hl
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hSt : oSt l = l.nl * l.D + 8 := rfl
  have hnD := nlD_le hl
  have hv : ∀ {c} {v : Nat → Nat}, LimbsAt l s.mem F c v → ∀ p < l.nl, v p < 2 * M p →
      val52 l s.mem F (l.D * p + c) = v p :=
    fun h p hp hlt => val52_of hl (h p hp) (by have := two_mul_lt (hMlt p hp); omega_arith)
  have ar : Ar0 l s.mem F M (fun p => (mi p &&& mask52).toNat) := by
    refine ⟨fun p hp j hj => ?_, fun p hp => hv hM p hp (by have := hModd p hp; omega_arith), fun p hp t ht => ?_,
      fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
    · rw [limb_of (hM p hp) hj]; exact limbN_lt _ _
    · rw [hk0 p hp t ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [BitVec.toNat_and, show mask52.toNat = 2 ^ 52 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by decide)
    · rw [limb_of (hM p hp) (by simp only [Lay.L]; have := hl.bounds; omega_arith)]; exact k0_of (hinv p hp)
    · have h4 : 4 * M p ≤ 2 ^ (64 * l.W + 2) := by
        have := hMlt p hp
        rw [Nat.pow_succ, Nat.pow_succ]; omega_arith
      exact Nat.le_trans h4 (pow2_le (by omega_arith))
  have e2 := dbls_eq hl hz0
  have ge : ∀ p, M p ≤ gb l (M p) := fun p => Nat.le_of_eq (gb_eq hz0 _).symm
  unfold Impl.Ffdh.X86_64.Ifma.vec withVzu
  have gx := fun p hp => (good_of hl (hX p hp) (by have := hXlt p hp; omega_arith) (hMlt p hp)).good (ge p)
  have gy := fun p hp => (good_of hl (hY p hp) (by have := hYlt p hp; omega_arith) (hMlt p hp)).good (ge p)
  have gk := fun p hp => (good_of hl (hK p hp) (by have := hKlt p hp; omega_arith) (hMlt p hp)).good (ge p)
  have gf := fun p hp => (good_of hl (hF p hp) (hFlt p hp) (hMlt p hp)).good (ge p)
  refine WP.seq (WP.mono (expLoopFrom_ok hl (st := [.mov .r13 (.reg .rbp)]) (x := x) (e := e) (Q := Q)
    ⟨hB, VG.Proof.Bignum.X86_64.AmmSym.Scr.mono hs (by omega_using [hSt]), ⟨ar, fun h => absurd h (by rw [hz0]; decide)⟩,
      fun p hp => cop2 (hModd p hp) _, gx, gy, gk,
      fun q p hp => by
        rw [cv_eq hz0, hv hX p hp (by have := hXlt p hp; omega_arith)]
        exact vx q p hp,
      fun q p hp => by
        rw [cv_eq hz0, Nat.one_mul, ← vy q p hp, hv hY p hp (by have := hYlt p hp; omega_arith)],
      fun q p hp => by
        rw [cv_eq hz0, e2, ← vk q p hp, hv hK p hp (by have := hKlt p hp; omega_arith)]⟩ gf hi₀ hz hd
    fun t _ hpt _ _ _ => start_ok (hpt.trans hst))
    fun s₂ ⟨v₂, O₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ⟨fun p hp => ⟨(v₂ p hp).1.strong hz0, fun hq => ?_⟩,
    (O₂.toOutside hl).mono (by omega_using []) (by omega_using []),
    fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 _ r12 => g₂ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12, rd₂, wr₂, x₂⟩⟩
  exact ((v₂ p hp).2 hq).trans (by rw [hv hF p hp (hFlt p hp)])

end VG.Proof.Ffdh.X86_64.Ifma
