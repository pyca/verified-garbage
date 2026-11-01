module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Twos
import VerifiedGarbage.Proof.Rsa.X86.Rd.Gcd
import VerifiedGarbage.Proof.Rsa.X86.Rd.Stages
import VerifiedGarbage.Proof.Rsa.X86.Rd.Stages2
import VerifiedGarbage.Proof.Rsa.X86.Rd.Sqrt
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Appendix C.2 on i686, from `d e` to the factors and the mask

`det_ok`: from the modulus `n` (narrow) and `d e` (wide), `RecoverDetRt.det`
leaves the factors in narrow arrays 5 and 6 and the mask in `sMask`, as
`RecoverDet.result` gives them for the quotient and remainder of the second
division (which `RecoverDet.model_correct` relates to the specification).
-/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.RecoverDet
open VG.Proof.Rsa (b2n b2n_le sub32)

theorem det_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n de : Nat}
    (h : KS g s0 A [VG.Impl.Rsa.X86.Recover.aN] AW [VG.Impl.Rsa.X86.Recover.wM, VG.Impl.Rsa.X86.Recover.wZ] V [] s)
    (hn : A VG.Impl.Rsa.X86.Recover.aN = n) (hde : AW VG.Impl.Rsa.X86.Recover.wM = de)
    (hz : AW VG.Impl.Rsa.X86.Recover.wZ = 0) (odd : n % 2 = 1) (three : 3 ≤ n) (small : n < 2 ^ (32 * g.w)) :
    WP isa det s fun t => ∃ A' V' q rem,
      KS g s0 A' [5, 6, aZero] AW [] V' [VG.Impl.Rsa.X86.Recover.sMask] t ∧
      (0 < m1Of (32 * g.w) (32 * g.W) n de →
        q = dOf (32 * g.w) (32 * g.W) n de / m1Of (32 * g.w) (32 * g.W) n de ∧
        rem = dOf (32 * g.w) (32 * g.W) n de % m1Of (32 * g.w) (32 * g.W) n de) ∧
      A' 5 = (stage2 (32 * g.w) (32 * g.W) n q rem).2.1 ∧ A' 6 = (stage2 (32 * g.w) (32 * g.W) n q rem).2.2 ∧
      A' aZero = 0 ∧
      V' VG.Impl.Rsa.X86.Recover.sMask =
        b2n (okDE (32 * g.W) de && ltOf (32 * g.w) (32 * g.W) n de && (stage2 (32 * g.w) (32 * g.W) n q rem).1) := by
  have up := h.upper
  have lo := h.lower
  have wpos : 64 ≤ 32 * g.w := by change 64 ≤ 32 * (2 * g.n + 2); omega
  have nbW : 2 * (32 * g.w) ≤ 32 * g.W := by change 2 * (32 * (2 * g.n + 2)) ≤ 32 * (2 * (2 * g.n + 2) + 2); omega
  unfold det
  simp only [seqs]
  -- `d e - 1`.
  have hn' : A 32 = n := hn
  refine WP.seq (WP.mono (deMinus_ok h hde hz) fun s1 ⟨AW1, h1, x1, z1⟩ => ?_)
  have x1' : AW1 10 = deX (32 * g.W) de := x1
  have z1' : AW1 0 = 0 := z1
  have h1v := (h1.view (j := VG.Impl.Rsa.X86.Recover.wZ) (by simp)).view (j := wX) (by simp)
  have h1t := h1v.mono (live' := [aZ0, aX2, VG.Impl.Rsa.X86.Recover.aN]) (liveW' := [wX])
    (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩)
    (fun d hd => ⟨hd, rfl⟩)
  -- The halvings.
  refine WP.seq (WP.mono (twos_ok h1t (n := n) (x := deX (32 * g.W) de % 2 ^ (32 * g.w))
      (X := deX (32 * g.W) de)
      (by simp [upd, aZ0, wX, VG.Impl.Rsa.X86.Recover.wZ, z1'])
      (by simp [upd, wX, VG.Impl.Rsa.X86.Recover.wZ, VG.Impl.Rsa.X86.RecoverDetRt.aN, VG.Impl.Rsa.X86.Recover.aN, hn'])
      (by simp [upd, aX2, wX, x1']) x1)
    fun s2 ⟨A2, AW2, V2, h2, u2, x2, x32, n2, v2⟩ => ?_)
  -- `u` is odd.
  have nm1 : sub32 g.w n 1 = n - 1 := wsub_of_le small (by omega)
  have xlt : deX (32 * g.W) de % 2 ^ (32 * g.w) < 2 ^ (32 * g.W) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))
  have uodd : ((twoStep (32 * g.W))^[32 * g.w] (sub32 g.w n 1, deX (32 * g.W) de % 2 ^ (32 * g.w),
      deX (32 * g.W) de)).1 % 2 = 1 := by
    rw [(twos_proj _ _ _ _ _ (deX (32 * g.W) de % 2 ^ (32 * g.w))).1, nm1]
    exact (twos_iter (by omega) (by omega) xlt).1
  have tw : twosOut (32 * g.w) (32 * g.W) n de = (twoStep (32 * g.W))^[32 * g.w] (sub32 g.w n 1,
      deX (32 * g.W) de % 2 ^ (32 * g.w), deX (32 * g.W) de) := rfl
  generalize (twoStep (32 * g.W))^[32 * g.w] (sub32 g.w n 1, deX (32 * g.W) de % 2 ^ (32 * g.w),
    deX (32 * g.W) de) = st at u2 x2 x32 uodd tw
  -- The GCD.
  refine WP.seq (WP.mono (gcdSet_ok h2 u2 x2) fun s3 ⟨A3, h3, m3, x3, n3⟩ => ?_)
  refine WP.seq (WP.mono (gcdDet_ok h3 m3 x3 uodd) fun s4 h4 => ?_)
  -- The product.
  refine WP.seq (WP.mono (aProduct_ok h4 (g1 := Nat.gcd st.1 st.2.1)
    (by rw [upd_ne _ _ (show (1 : Nat) ≠ aZero by decide), upd_self]) x32)
    fun s5 ⟨A5, AW5, V5, h5, a5, z25, zz5, n5, v5⟩ => ?_)
  have ha : AW5 wA = aOf (32 * g.w) (32 * g.W) n de := by rw [a5, aOf, tw]
  have hn5 : A5 VG.Impl.Rsa.X86.Recover.aN = n := by
    rw [n5]; simp only [upd, show VG.Impl.Rsa.X86.Recover.aN ≠ aZero by decide,
      show VG.Impl.Rsa.X86.Recover.aN ≠ 1 by decide, ↓reduceIte]; rw [n3]; exact n2
  have hz5 : A5 aZero = 0 := by rw [zz5]; simp [upd]
  -- `m` and `r`.
  refine WP.seq (WP.mono (divA_ok h5 ha z25 hn5 (by omega)) fun s6 ⟨AW6, h6, m6, r6, n6, z6⟩ => ?_)
  refine WP.seq (WP.mono (divB_ok h6 hz5 hn5 m6 r6 n6 z6)
    fun s7 ⟨Q, R, A7, AW7, h7, cond, q7, one7, z7, nn7, nW7, z27⟩ => ?_)
  -- `b` and `b²`.
  refine WP.seq (WP.mono (square_ok h7 q7 one7 z7 nn7 nW7 z27)
    fun s8 ⟨A8, AW8, V8, h8, b8, z8, sq8, nW8, ex8, lt8, ok8⟩ => ?_)
  refine WP.seq (WP.mono (minus4n_ok h8 sq8 nW8) fun s9 ⟨AW9, h9, x9⟩ => ?_)
  refine WP.seq (WP.mono (sqrt_ok h9 z8 x9) fun s10 ⟨A10, AW10, h10, y10, d10, z10⟩ => ?_)
  -- The values `RecoverDet`'s model names.
  have hF : fourN (32 * g.W) n = ((n + n) % 2 ^ (32 * g.W) + (n + n) % 2 ^ (32 * g.W)) % 2 ^ (32 * g.W) := by
    unfold fourN; rw [Nat.two_mul n, Nat.two_mul]
  have hX : xOf (32 * g.w) (32 * g.W) n (bOf (32 * g.w) Q) = sub32 g.W
      (((prodStep (32 * g.W))^[32 * g.w] ((Q + 1) % 2 ^ (32 * g.w), (Q + 1) % 2 ^ (32 * g.w), 0)).2.2)
      (((n + n) % 2 ^ (32 * g.W) + (n + n) % 2 ^ (32 * g.W)) % 2 ^ (32 * g.W)) := by
    rw [xOf, hF]; rfl
  have K : 32 * g.W / 2 = 16 * g.W := by omega
  have hroot : rootOf (32 * g.w) (32 * g.W) n (bOf (32 * g.w) Q) =
      (sqrtStep (32 * g.w) (32 * g.W))^[16 * g.W] (sub32 g.W
        (((prodStep (32 * g.W))^[32 * g.w] ((Q + 1) % 2 ^ (32 * g.w), (Q + 1) % 2 ^ (32 * g.w), 0)).2.2)
        (((n + n) % 2 ^ (32 * g.W) + (n + n) % 2 ^ (32 * g.W)) % 2 ^ (32 * g.W)), 0, 0) := by
    rw [rootOf, hX, K]
  have hok4 : ok4Of (32 * g.w) (32 * g.W) n (bOf (32 * g.w) Q) =
      !(decide (((prodStep (32 * g.W))^[32 * g.w] ((Q + 1) % 2 ^ (32 * g.w), (Q + 1) % 2 ^ (32 * g.w), 0)).2.2 <
          ((n + n) % 2 ^ (32 * g.W) + (n + n) % 2 ^ (32 * g.W)) % 2 ^ (32 * g.W)) ||
        decide (sub32 g.W
          (((prodStep (32 * g.W))^[32 * g.w] ((Q + 1) % 2 ^ (32 * g.w), (Q + 1) % 2 ^ (32 * g.w), 0)).2.2)
          (((n + n) % 2 ^ (32 * g.W) + (n + n) % 2 ^ (32 * g.W)) % 2 ^ (32 * g.W)) < 1)) := by
    rw [ok4Of, hX, hF]; rfl
  -- The factors and the mask.
  refine WP.mono (factors_ok h10 (okde := okDE (32 * g.W) de) (lt := ltOf (32 * g.w) (32 * g.W) n de)
    (ex := decide (R = 0)) (ok4 := ok4Of (32 * g.w) (32 * g.W) n (bOf (32 * g.w) Q))
    (ok5 := decide ((rootOf (32 * g.w) (32 * g.W) n (bOf (32 * g.w) Q)).2.1 = 0)) y10 d10 z10
    ?_ ?_ ?_ ?_ ?_) fun t ⟨A', V', ht, p, q, z, mask⟩ => ?_
  · rw [upd_ne _ _ (show sOkDE ≠ sOk5 by decide), upd_ne _ _ (show sOkDE ≠ sK by decide), upd_ne _ _ (show sOkDE ≠ sOk4 by decide), ok8, upd_ne _ _ (show sOkDE ≠ sExact by decide), upd_ne _ _ (show sOkDE ≠ sLt by decide), v5, v2, upd_self]
  · rw [upd_ne _ _ (show sLt ≠ sOk5 by decide), upd_ne _ _ (show sLt ≠ sK by decide), upd_ne _ _ (show sLt ≠ sOk4 by decide), lt8, upd_ne _ _ (show sLt ≠ sExact by decide), upd_self]; rfl
  · rw [upd_ne _ _ (show sExact ≠ sOk5 by decide), upd_ne _ _ (show sExact ≠ sK by decide), upd_ne _ _ (show sExact ≠ sOk4 by decide), ex8, upd_self]
  · rw [upd_ne _ _ (show sOk4 ≠ sOk5 by decide), upd_ne _ _ (show sOk4 ≠ sK by decide), upd_self, hok4]
  · rw [upd_self, ite_b2n, hroot]
  · refine ⟨A', V', Q, R, ht.mono (AW' := AW) (fun j hj => ⟨hj, rfl⟩) (fun j hj => by simp at hj)
      (fun d hd => ⟨hd, rfl⟩), cond, ?_, ?_, z, ?_⟩
    · rw [p, b8]; simp only [stage2]; rw [hroot]; rfl
    · rw [q, b8]; simp only [stage2]; rw [hroot]; rfl
    · rw [mask]; simp only [stage2, Bool.and_assoc]

end VG.Proof.Rsa.X86.Recover
