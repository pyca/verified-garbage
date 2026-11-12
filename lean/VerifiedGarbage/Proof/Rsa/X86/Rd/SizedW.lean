module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.Frame
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Inputs
public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWBase
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.BoolNat
public import VerifiedGarbage.Proof.Rsa.Sub32
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Prep
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
import VerifiedGarbage.Proof.Rsa.X86.Rd.DetPartsW
import VerifiedGarbage.Proof.Rsa.X86.Rd.TwosW
public import VerifiedGarbage.Proof.Rsa.X86.Rd.GcdW
import VerifiedGarbage.Proof.Rsa.X86.Rd.ProdW
import VerifiedGarbage.Proof.Rsa.X86.Rd.DivAW
import VerifiedGarbage.Proof.Rsa.X86.Rd.DivBW
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtW
import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.RecoverDetWords
import VerifiedGarbage.Proof.Rsa.RecoverRoot
import VerifiedGarbage.Proof.Bignum.ShiftStages
import VerifiedGarbage.Proof.Framework.PlainSimp

-- separate module: det's run against the model, apart from its timing (`TimingW`) so a change to either rebuilds only it

/-! # Appendix C.2 by words on i686: `det`

`detW_ok`: the pieces in turn, each against `RecoverDet`'s model: the halvings in closed form
(`twos_closed`), the product (`prod_iter`), the divisions, `b²`, `b² - 4 n` and its integer square root
(modulo `2^(64 W')`), and the factors with the mask of every check.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM sB
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.RecoverDet
open VG.Spec.Rsa (isqrt)
open VG.Proof.Rsa (b2n sub32)
open VG.Proof.Rsa.X86.WordRt (wq)

theorem detW_ok [VG.Proof.Rsa.X86.Recover.G.GcdDone] {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n de a : Nat}
    (h : KS g s0 A [VG.Impl.Rsa.X86.Recover.aN] AW [VG.Impl.Rsa.X86.Recover.wM, VG.Impl.Rsa.X86.Recover.wZ] V [] s)
    (hn : A VG.Impl.Rsa.X86.Recover.aN = n) (hde : AW VG.Impl.Rsa.X86.Recover.wM = de)
    (hz : AW VG.Impl.Rsa.X86.Recover.wZ = 0) (odd : n % 2 = 1) (three : 3 ≤ n) (small : n < 2 ^ (32 * g.w))
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha0 : 64 ≤ a) (ha1 : a ≤ 1024)
    (haw : wq a ≤ g.w) (hn0 : 2 ^ (32 * (wq a - 1)) ≤ n) (hn' : n < 2 ^ (32 * wq a)) :
    WP isa det s fun t => ∃ A' V' q rem,
      KS g s0 A' [5, 6, VG.Impl.Rsa.X86.Keys.aZero] AW [] V' [VG.Impl.Rsa.X86.Recover.sMask] t ∧
      (ltOf (32 * g.w) (32 * g.W) n de = true → 0 < m1Of (32 * g.w) (32 * g.W) n de →
        q = dOf (32 * g.w) (32 * g.W) n de / m1Of (32 * g.w) (32 * g.W) n de ∧
        rem = dOf (32 * g.w) (32 * g.W) n de % m1Of (32 * g.w) (32 * g.W) n de) ∧
      A' VG.Impl.Rsa.X86.Keys.aZero = 0 ∧
      A' 5 = (bOf (32 * g.w) q + isqrt (xOf (32 * g.w) (32 * g.W) n (bOf (32 * g.w) q) % 2 ^ (64 * wq a))) %
        2 ^ (32 * g.w) / 2 ∧
      A' 6 = sub32 g.w (bOf (32 * g.w) q) (isqrt (xOf (32 * g.w) (32 * g.W) n (bOf (32 * g.w) q) % 2 ^ (64 * wq a))) / 2 ∧
      V' VG.Impl.Rsa.X86.Recover.sMask = b2n (okDE (32 * g.W) de && ltOf (32 * g.w) (32 * g.W) n de &&
        decide (rem = 0) && ok4Of (32 * g.w) (32 * g.W) n (bOf (32 * g.w) q) &&
        decide (isqrt (xOf (32 * g.w) (32 * g.W) n (bOf (32 * g.w) q) % 2 ^ (64 * wq a)) *
          isqrt (xOf (32 * g.w) (32 * g.W) n (bOf (32 * g.w) q) % 2 ^ (64 * wq a)) =
          xOf (32 * g.w) (32 * g.W) n (bOf (32 * g.w) q) % 2 ^ (64 * wq a))) := by
  have up := h.upper
  have lo := h.lower
  have wpos : 64 ≤ 32 * g.w := by change 64 ≤ 32 * (2 * g.n + 2); omega
  have nbW : 2 * (32 * g.w) ≤ 32 * g.W := by change 2 * (32 * (2 * g.n + 2)) ≤ 32 * (2 * (2 * g.n + 2) + 2); omega
  unfold det
  simp only [seqs]
  -- `d e - 1`.
  refine WP.seq (WP.mono (deMinus_ok h hde hz) fun s1 ⟨AW1, h1, x1, z1⟩ => ?_)
  have x1' : AW1 10 = deX (32 * g.W) de := x1
  have z1' : AW1 0 = 0 := z1
  have h1v := (h1.view (j := VG.Impl.Rsa.X86.Recover.wZ) (by simp)).view (j := wX) (by simp)
  have h1t := h1v.mono (live' := [aZ0, aX2, VG.Impl.Rsa.X86.Recover.aN]) (liveW' := [wX])
    (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩)
    (fun d hd => ⟨hd, rfl⟩)
  -- The halvings, in closed form.
  have deXlt : deX (32 * g.W) de < 2 ^ (32 * g.W) := by unfold deX wsub; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  refine WP.seq (WP.mono (twos_ok h1t (n := n) (x := deX (32 * g.W) de % 2 ^ (32 * g.w))
      (X := deX (32 * g.W) de)
      (by simp [upd, aZ0, wX, VG.Impl.Rsa.X86.Recover.wZ, z1'])
      (by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hn)
      (by simp [upd, aX2, wX, x1']) x1 three small
      (Nat.lt_of_lt_of_le (VG.Proof.Bignum.ShiftStages.tz_lt (by omega) (Nat.lt_of_le_of_lt (Nat.sub_le n 1) hn'))
        (by simp only [wq]; omega)))
    fun s2 ⟨A2, AW2, V2, h2, u2, x2, x32, n2, v2⟩ => ?_)
  have nm1 : wsub (32 * g.w) n 1 = n - 1 := wsub_of_le small (by omega)
  have tw : twosOut (32 * g.w) (32 * g.W) n de = ((n - 1) / 2 ^ VG.Proof.Bignum.ShiftStages.tz (n - 1),
      deX (32 * g.W) de % 2 ^ (32 * g.w) /
        2 ^ VG.Proof.Bignum.ShiftStages.tz (Nat.gcd (n - 1) (deX (32 * g.W) de % 2 ^ (32 * g.w))),
      deX (32 * g.W) de *
        2 ^ VG.Proof.Bignum.ShiftStages.tz (Nat.gcd (n - 1) (deX (32 * g.W) de % 2 ^ (32 * g.w))) %
        2 ^ (32 * g.W)) := by
    unfold twosOut; rw [nm1]; exact twos_closed (by omega) (by omega) deXlt
  have tw1 := congrArg Prod.fst tw
  have tw2 := congrArg (fun p => p.2.1) tw
  have tw3 := congrArg (fun p => p.2.2) tw
  simp only at tw1 tw2 tw3
  rw [← tw1] at u2
  rw [← tw2] at x2
  rw [← tw3] at x32
  have uodd : (twosOut (32 * g.w) (32 * g.W) n de).1 % 2 = 1 := by
    rw [tw]; exact (VG.Proof.Bignum.ShiftStages.tz_spec (n - 1) (by omega)).2
  have ule : (twosOut (32 * g.w) (32 * g.W) n de).1 ≤ n - 1 := by rw [tw]; exact Nat.div_le_self _ _
  have x3lt : (twosOut (32 * g.w) (32 * g.W) n de).2.2 < 2 ^ (32 * g.W) := by
    rw [tw]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have pnb : 2 ^ (32 * g.w) ≤ 2 ^ (32 * g.W) := Nat.pow_le_pow_right (by decide) (by omega)
  have hA : aOf (32 * g.w) (32 * g.W) n de = Nat.gcd (twosOut (32 * g.w) (32 * g.W) n de).1
      (twosOut (32 * g.w) (32 * g.W) n de).2.1 * (twosOut (32 * g.w) (32 * g.W) n de).2.2 % 2 ^ (32 * g.W) := by
    have hg : Nat.gcd (twosOut (32 * g.w) (32 * g.W) n de).1 (twosOut (32 * g.w) (32 * g.W) n de).2.1 <
        2 ^ (32 * g.w) := by
      have := Nat.gcd_le_left (twosOut (32 * g.w) (32 * g.W) n de).2.1
        (show 0 < (twosOut (32 * g.w) (32 * g.W) n de).1 by omega)
      omega
    unfold aOf
    rw [prod_iter _ _ _ x3lt]
    simp only
    rw [Nat.mod_eq_of_lt hg]
  generalize twosOut (32 * g.w) (32 * g.W) n de = st at u2 x2 x32 uodd ule x3lt hA
  -- The GCD.
  refine WP.seq (WP.mono (gcdSetW_ok h2 u2 x2) fun s3 ⟨A3, h3, m3, x3, n3⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Recover.G.gcdFused_ok h3 m3 x3 uodd)
    fun s4 ⟨A4, h4, g4, z4, n4⟩ => ?_)
  -- The product.
  refine WP.seq (WP.mono (aProduct_ok h4 g4 x32) fun s5 ⟨A5, AW5, V5, h5, a5, t5, z5, nn5, v5⟩ => ?_)
  rw [← hA] at a5
  have hz5 : A5 VG.Impl.Rsa.X86.Keys.aZero = 0 := by rw [z5, z4]
  have hn5 : A5 VG.Impl.Rsa.X86.Recover.aN = n := by rw [nn5]; exact n4.trans (n3.trans n2)
  -- `m` and `r`.
  refine WP.seq (WP.mono (divA_ok h5 hz5 hn5 a5 t5 ha ha0 ha1 haw hn0 hn')
    fun s6 ⟨AW6, V6, h6, m6, r6, nW6, lt6, ok6⟩ => ?_)
  refine WP.seq (WP.mono (divB_ok h6 hz5 hn5 m6 r6 nW6 ha ha0 ha1 haw hn')
    fun s7 ⟨Q, R, A7, AW7, V7, h7, ex7, lt7, ok7, cond7, q7, one7, z7, nn7, nW7⟩ => ?_)
  have cond : ltOf (32 * g.w) (32 * g.W) n de = true → 0 < m1Of (32 * g.w) (32 * g.W) n de →
      Q = dOf (32 * g.w) (32 * g.W) n de / m1Of (32 * g.w) (32 * g.W) n de ∧
      R = dOf (32 * g.w) (32 * g.W) n de % m1Of (32 * g.w) (32 * g.W) n de := fun hl _ => by
    have mlt : mOf (32 * g.w) (32 * g.W) n de < n := by simpa [ltOf] using hl
    have rlt : rOf (32 * g.w) (32 * g.W) n de < n := Nat.mod_lt _ (by omega)
    have hd : dOf (32 * g.w) (32 * g.W) n de = n - rOf (32 * g.w) (32 * g.W) n de := by
      unfold dOf; rw [Nat.mod_eq_of_lt (by omega), wsub_of_le small (by omega)]
    have hm1 : m1Of (32 * g.w) (32 * g.W) n de = mOf (32 * g.w) (32 * g.W) n de + 1 := by
      unfold m1Of; rw [Nat.mod_eq_of_lt (a := mOf _ _ _ _) (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hd, hm1]
    exact cond7 mlt rlt
  -- `b` and `b²`.
  refine WP.seq (WP.mono (square_ok h7 q7 one7 z7 nW7) fun s8 ⟨A8, AW8, h8, b8, z8, sq8, nW8⟩ => ?_)
  have bl : bOf (32 * g.w) Q < 2 ^ (32 * g.w) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have bb : bOf (32 * g.w) Q * bOf (32 * g.w) Q < 2 ^ (32 * g.W) := by
    have : 2 ^ (32 * g.w) * 2 ^ (32 * g.w) ≤ 2 ^ (32 * g.W) := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' bl bl) this
  have hsq : sqOf (32 * g.w) (32 * g.W) (bOf (32 * g.w) Q) = bOf (32 * g.w) Q * bOf (32 * g.w) Q := by
    unfold sqOf; rw [prod_iter _ _ _ (by omega)]; simp only
    rw [Nat.mod_eq_of_lt bl, Nat.mod_eq_of_lt bb]
  have sq8' : AW8 wA = sqOf (32 * g.w) (32 * g.W) (bOf (32 * g.w) Q) := by rw [hsq, sq8]; rfl
  -- `b² - 4 n`.
  refine WP.seq (WP.mono (minus4n_ok h8 sq8' nW8) fun s9 ⟨AW9, V9, h9, ok49, okde9, lt9, ex9, x9⟩ => ?_)
  have hF : fourN (32 * g.W) n = ((n + n) % 2 ^ (32 * g.W) + (n + n) % 2 ^ (32 * g.W)) % 2 ^ (32 * g.W) := by
    unfold fourN; rw [Nat.two_mul n, Nat.two_mul]
  rw [← hF] at ok49 x9
  have x9' : AW9 wR = xOf (32 * g.w) (32 * g.W) n (bOf (32 * g.w) Q) := x9
  have ok49' : V9 sOk4 = b2n (ok4Of (32 * g.w) (32 * g.W) n (bOf (32 * g.w) Q)) := ok49
  -- Its square root.
  refine WP.seq (WP.mono (sqrt_ok h9 z8 x9' ha (by omega) haw ha1) fun s10 ⟨A10, AW10, h10, y10, d10, z10⟩ => ?_)
  -- The factors and the mask.
  refine WP.mono (factorsW_ok h10 (b := bOf (32 * g.w) Q) (okde := okDE (32 * g.W) de) (lt := ltOf (32 * g.w) (32 * g.W) n de)
    (ex := decide (R = 0)) (ok4 := ok4Of (32 * g.w) (32 * g.W) n (bOf (32 * g.w) Q))
    (ok5 := decide (isqrt (xOf (32 * g.w) (32 * g.W) n (bOf (32 * g.w) Q) % 2 ^ (64 * wq a)) *
      isqrt (xOf (32 * g.w) (32 * g.W) n (bOf (32 * g.w) Q) % 2 ^ (64 * wq a)) =
      xOf (32 * g.w) (32 * g.W) n (bOf (32 * g.w) Q) % 2 ^ (64 * wq a))) y10 (by rw [d10, b8]; rfl) z10
    ?_ ?_ ?_ ?_ ?_) fun t ⟨A', V', ht, p, q, z, mask⟩ => ?_
  · rw [upd_ne _ _ (show sOkDE ≠ sOk5 by decide), okde9, ok7, ok6, v5, v2, upd_self]
  · rw [upd_ne _ _ (show sLt ≠ sOk5 by decide), lt9, lt7, lt6]; rfl
  · rw [upd_ne _ _ (show sExact ≠ sOk5 by decide), ex9, ex7]
  · rw [upd_ne _ _ (show sOk4 ≠ sOk5 by decide), ok49']
  · rw [upd_self, ite_b2n]
  · refine ⟨A', V', Q, R, ht.mono (AW' := AW) (fun j hj => ⟨hj, rfl⟩) (fun j hj => by simp at hj)
      (fun d hd => ⟨hd, rfl⟩), cond, z, ?_, ?_, ?_⟩
    · rw [p]
    · rw [q]
    · rw [mask]


/-- Where `m < n`, `q` is the quotient and `b² > 4 n`: `X = b² - 4 n < (n + 1)²`, within `2 W'` words. -/
theorem xOf_lt_words {nb wb n de q W' : Nat} (three : 3 ≤ n) (hn : 8 * (n + 2) ≤ 2 ^ nb) (hw : 2 * nb ≤ wb)
    (hlt : ltOf nb wb n de = true) (hq : q = dOf nb wb n de / m1Of nb wb n de)
    (h4 : ok4Of nb wb n (bOf nb q) = true) (hW : n < 2 ^ (32 * W')) :
    xOf nb wb n (bOf nb q) < 2 ^ (64 * W') := by
  have pnb : 2 ^ nb ≤ 2 ^ wb := Nat.pow_le_pow_right (by decide) (by omega)
  have p2 : 2 ^ nb * 2 ^ nb ≤ 2 ^ wb := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have rlt : rOf nb wb n de < n := Nat.mod_lt _ (by omega)
  have dv : dOf nb wb n de = n - rOf nb wb n de := by
    unfold dOf; rw [Nat.mod_eq_of_lt (by omega), wsub_of_le (by omega) (by omega)]
  have mlt : mOf nb wb n de < n := by simpa [ltOf] using hlt
  have m1 : m1Of nb wb n de = mOf nb wb n de + 1 := by
    unfold m1Of; rw [Nat.mod_eq_of_lt (a := mOf nb wb n de) (by omega), Nat.mod_eq_of_lt (by omega)]
  have qle : q ≤ n := by rw [hq, dv, m1]; exact Nat.le_trans (Nat.div_le_self _ _) (by omega)
  have hb : bOf nb q = q + 1 := by unfold bOf; exact Nat.mod_eq_of_lt (by omega)
  rw [hb] at h4 ⊢
  have hb1 : q + 1 ≤ n + 1 := by omega
  generalize q + 1 = b at *
  have blt : b < 2 ^ nb := by omega
  have bb : b * b < 2 ^ wb := Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' blt blt) p2
  have sq : sqOf nb wb b = b * b := by
    unfold sqOf; rw [prod_iter _ _ _ (by omega)]; simp only
    rw [Nat.mod_eq_of_lt blt, Nat.mod_eq_of_lt bb]
  have f4 : fourN wb n = 4 * n := by
    unfold fourN
    rw [Nat.mod_eq_of_lt (a := 2 * n) (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have big : ¬ (b * b < 4 * n) := by
    unfold ok4Of at h4; rw [sq, f4] at h4; simp only [Bool.not_eq_true', Bool.or_eq_false_iff,
      decide_eq_false_iff_not] at h4; exact h4.1
  have xv : xOf nb wb n b = b * b - 4 * n := by
    unfold xOf; rw [sq, f4, wsub_of_le bb (by omega)]
  rw [xv]
  have bW : b ≤ 2 ^ (32 * W') := by omega
  have : b * b ≤ 2 ^ (64 * W') := by
    rw [show 64 * W' = 32 * W' + 32 * W' by omega, Nat.pow_add]; exact Nat.mul_le_mul bW bW
  omega

end VG.Proof.Rsa.X86.Recover

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

def calculatedD (g : CallGeometry) (m : Mem) : Option (List Byte × List Byte) :=
  Spec.Rsa.primesKeyDet (inputBytes g m 0) (inputBytes g m 1) (inputBytes g m 2)

def outputBuffersD (g : CallGeometry) : List (Addr × Nat) :=
  [((g.buffer 0).base, (g.buffer 0).len), ((g.buffer 2).base, (g.buffer 2).len)]

def WrittenD (g : CallGeometry) (m : Mem) (t : State) : Prop :=
  Spec.Rsa.writtenAll t.mem (outputBuffersD g) (t.gpr .eax) ((calculatedD g m).map fun v => [v.1, v.2])

theorem writtenD_failure {g : CallGeometry} {m : Mem} {t : State}
    (none : calculatedD g m = none)
    (p : Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len = List.replicate (g.buffer 0).len 0)
    (q : Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len = List.replicate (g.buffer 2).len 0)
    (zero : t.gpr .eax = 0) : WrittenD g m t := by
  unfold WrittenD
  rw [none]
  refine ⟨zero, ?_⟩
  simp only [outputBuffersD, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨p, q⟩

end VG.Proof.Rsa.X86.Recover

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.RecoverDet
open VG.Proof.Rsa (b2n sub32)
open VG.Spec.Rsa (isqrt)
open VG.Proof.Rsa.X86.WordRt (wq)

/-- The model's result from `det`'s mask and factors: where `m < n`, `b² > 4 n` and the division is exact, the
model's root by bit pairs is `isqrt X` (`root_bridge`), and `X` is within `2 W'` words. -/
theorem result_words {nb wb n de q rem W' : Nat} (three : 3 ≤ n) (hn : 8 * (n + 2) ≤ 2 ^ nb) (hw : 2 * nb ≤ wb)
    (hwe : wb % 2 = 0) (hW : n < 2 ^ (32 * W'))
    (cond : ltOf nb wb n de = true → 0 < m1Of nb wb n de →
      q = dOf nb wb n de / m1Of nb wb n de ∧ rem = dOf nb wb n de % m1Of nb wb n de) :
    result nb wb n de q rem =
      if okDE wb de && ltOf nb wb n de && decide (rem = 0) && ok4Of nb wb n (bOf nb q) &&
          decide (isqrt (xOf nb wb n (bOf nb q) % 2 ^ (64 * W')) * isqrt (xOf nb wb n (bOf nb q) % 2 ^ (64 * W')) =
            xOf nb wb n (bOf nb q) % 2 ^ (64 * W')) then
        some ((bOf nb q + isqrt (xOf nb wb n (bOf nb q) % 2 ^ (64 * W'))) % 2 ^ nb / 2,
          wsub nb (bOf nb q) (isqrt (xOf nb wb n (bOf nb q) % 2 ^ (64 * W'))) / 2)
      else none := by
  unfold result stage2
  simp only [Bool.and_assoc]
  by_cases c : (okDE wb de && (ltOf nb wb n de && (decide (rem = 0) && ok4Of nb wb n (bOf nb q)))) = true
  · simp only [Bool.and_eq_true] at c
    obtain ⟨hk, hl, hr, h4⟩ := c
    have rlt : rOf nb wb n de < n := Nat.mod_lt _ (by omega)
    have mlt : mOf nb wb n de < n := by simpa [ltOf] using hl
    have m1pos : 0 < m1Of nb wb n de := by
      unfold m1Of; rw [Nat.mod_eq_of_lt (a := mOf nb wb n de) (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    have hq := (cond hl m1pos).1
    have xlt := xOf_lt_words three hn hw hl hq h4 hW
    obtain ⟨ry, rr, -⟩ := root_bridge three hn hw hwe hl hq h4
    rw [Nat.mod_eq_of_lt xlt, ry, hk, hl, hr, h4]
    simp only [Bool.true_and, decide_eq_true_eq]
    by_cases e : isqrt (xOf nb wb n (bOf nb q)) * isqrt (xOf nb wb n (bOf nb q)) = xOf nb wb n (bOf nb q)
    · simp only [e, rr.mpr e, ↓reduceIte]
    · have ne : ¬ (rootOf nb wb n (bOf nb q)).2.1 = 0 := fun h => e (rr.mp h)
      simp only [e, ne, ↓reduceIte]
  · simp only [Bool.not_eq_true] at c
    have c' : (okDE wb de && (ltOf nb wb n de && (decide (rem = 0) && (ok4Of nb wb n (bOf nb q) &&
        decide ((rootOf nb wb n (bOf nb q)).2.1 = 0))))) = false := by
      revert c; cases okDE wb de <;> cases ltOf nb wb n de <;> cases decide (rem = 0) <;>
        cases ok4Of nb wb n (bOf nb q) <;> simp
    have c'' : (okDE wb de && (ltOf nb wb n de && (decide (rem = 0) && (ok4Of nb wb n (bOf nb q) &&
        decide (isqrt (xOf nb wb n (bOf nb q) % 2 ^ (64 * W')) * isqrt (xOf nb wb n (bOf nb q) % 2 ^ (64 * W')) =
          xOf nb wb n (bOf nb q) % 2 ^ (64 * W')))))) = false := by
      revert c; cases okDE wb de <;> cases ltOf nb wb n de <;> cases decide (rem = 0) <;>
        cases ok4Of nb wb n (bOf nb q) <;> simp
    rw [c', c'']; rfl

end VG.Proof.Rsa.X86.Recover
end

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.RecoverDet
open VG.Proof.Rsa (b2n sub32)
open VG.Spec.Rsa (isqrt)
open VG.Proof.Rsa.X86.WordRt (wq)

/-- What `det` needs of a valid modulus `n` and its length `a` (argument `nl`). -/
theorem det_facts {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (valid : Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true) :
    inputValue g s.mem 0 % 2 = 1 ∧ 3 ≤ inputValue g s.mem 0 ∧ inputValue g s.mem 0 < 2 ^ (32 * g.toGeo.w) ∧
      g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 (g.args 5).toNat ∧
      64 ≤ (g.args 5).toNat ∧ (g.args 5).toNat ≤ 1024 ∧ wq (g.args 5).toNat ≤ g.toGeo.w ∧
      2 ^ (32 * (wq (g.args 5).toNat - 1)) ≤ inputValue g s.mem 0 ∧
      inputValue g s.mem 0 < 2 ^ (32 * wq (g.args 5).toNat) := by
  have facts := valid
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at facts
  have odd : inputValue g s.mem 0 % 2 = 1 := facts.1.1.1
  have large : 3 ≤ inputValue g s.mem 0 := by
    have lower := facts.1.1.2
    have power (k : Nat) (hk : 2 ≤ k) : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (n := 2) (by decide) hk
    have bigger := power 511 (by decide)
    omega
  have plen : (inputBytes g s.mem 0).length = (g.args 5).toNat := by
    simp [inputBytes, Spec.Rsa.bytesAt, CallGeometry.buffer]
  have hlo := facts.2
  rw [plen] at hlo
  have ab : (g.args 5).toNat ≤ 8 * g.n := by have := h.inputBound 0; exact this
  have nlt : inputValue g s.mem 0 < 2 ^ (8 * (g.args 5).toNat) := inputValue_lt g s.mem 0
  have nb : inputValue g s.mem 0 < 2 ^ (64 * g.n) :=
    Nat.lt_of_lt_of_le nlt (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨odd, large, Nat.lt_of_lt_of_le nb (Nat.pow_le_pow_right (by decide)
    (by change 64 * g.n ≤ 32 * (2 * g.n + 2); omega)),
    by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl, len.lower, len.upper,
    by simp only [wq, Geo.w, VG.Impl.Rsa.X86.Recover.width]; omega, ?_,
    Nat.lt_of_lt_of_le nlt (Nat.pow_le_pow_right (by decide) (by simp only [wq]; omega))⟩
  refine Nat.le_trans ?_ hlo
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by simp only [wq]; omega)

theorem sizedW_ok [VG.Proof.Rsa.X86.Recover.G.GcdDone] {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (valid : Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true)
    (pLen : (g.buffer 0).len = (inputBytes g s.mem 0).length)
    (qLen : (g.buffer 2).len = (inputBytes g s.mem 0).length)
    (eSmall : (g.buffer 6).len ≤ 8) :
    WP isa VG.Impl.Rsa.X86.RecoverDetRt.sized s fun t => Inputs g t ∧ WrittenD g s.mem t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps opRegs s t := by
  obtain ⟨odd, large, small, ha, ha0, ha1, haw, hn0, hn'⟩ := det_facts h len valid
  have up := h.upper
  set a := (g.args 5).toNat with ha_def
  have nb : inputValue g s.mem 0 < 2 ^ (64 * g.n) := by
    apply Nat.lt_of_lt_of_le (inputValue_lt g s.mem 0)
    apply Nat.pow_le_pow_right (by decide)
    have := h.inputBound 0
    omega
  have p64 : 2 ^ (32 * g.toGeo.w) = 2 ^ (64 * g.n) * 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; change 32 * (2 * g.n + 2) = _; omega
  have hn8 : 8 * (inputValue g s.mem 0 + 2) ≤ 2 ^ (32 * g.toGeo.w) := by
    rw [p64]
    have : 8 * (inputValue g s.mem 0 + 2) ≤ 2 ^ (64 * g.n) * 16 := by
      have := Nat.one_le_two_pow (n := 64 * g.n); omega
    exact Nat.le_trans this (Nat.mul_le_mul_left _ (by decide))
  have hde : inputValue g s.mem 2 * inputValue g s.mem 1 < 2 ^ (32 * g.toGeo.w) := by
    rw [p64]
    have dl := Nat.lt_of_lt_of_le (inputValue_lt g s.mem 2)
      (Nat.pow_le_pow_right (by decide) (show 8 * (g.buffer (4 + 2 * 2)).len ≤ 64 * g.n by
        have := h.inputBound 2; change (g.buffer (4 + 2 * 2)).len ≤ 8 * g.n at this; omega))
    have el := Nat.lt_of_lt_of_le (inputValue_lt g s.mem 1)
      (Nat.pow_le_pow_right (by decide) (show 8 * (g.buffer (4 + 2 * 1)).len ≤ 64 by
        change 8 * (g.buffer 6).len ≤ 64; omega))
    exact Nat.mul_lt_mul'' dl el
  have hw : 2 * (32 * g.toGeo.w) ≤ 32 * g.toGeo.W := by
    change 2 * (32 * (2 * g.n + 2)) ≤ 32 * (2 * (2 * g.n + 2) + 2); omega
  have hwe : 32 * g.toGeo.W % 2 = 0 := by change 32 * (2 * (2 * g.n + 2) + 2) % 2 = 0; omega
  unfold VG.Impl.Rsa.X86.RecoverDetRt.sized
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (loads_ok h len) fun s1 h1 => ?_)
  have arg : VG.Proof.Bignum.X86.CallArgument s1 g.B g.Z 7 (BitVec.ofNat 32 ((g.args 7).toNat)) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      h1.argument (h.arguments 7 (by decide)) (h.stageApart (by decide))
  refine WP.seq (WP.mono (prod_ok h1 arg (h.inputPositive 1) (h.inputBound 1) (h.inputBound 2)
    (inputValue_lt g s.mem 1) (inputValue_lt g s.mem 2)) fun s2 h2 => ?_)
  have h2' := h2.mono (liveW' := [wM, wZ]) (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩)
    (fun d hd => ⟨hd, rfl⟩)
  refine WP.seq (WP.mono (detW_ok h2' (n := inputValue g s.mem 0) (de := inputValue g s.mem 2 * inputValue g s.mem 1)
    rfl (by simp [AWp, upd]) (by simp [AWp, AW1, upd, wZ, wM, wMod, wE, wD]) odd large small ha ha0 ha1 haw hn0 hn')
    fun s3 ⟨A3, V3, q, rem, h3, cond, z3, p3, q3, m3⟩ => ?_)
  have input3 := h.of_KS h3
  have zero3 : num s3.mem g.B g.toGeo.w VG.Impl.Rsa.X86.Keys.aZero = 0 := by
    rw [h3.arrs VG.Impl.Rsa.X86.Keys.aZero (by simp), z3]
  have model := (result_words (W' := wq a) large hn8 hw hwe hn' cond).symm.trans
    (model_correct_lt (q := q) (rem := rem) (e := inputValue g s.mem 1) (d := inputValue g s.mem 2) odd large hn8 hde
      hw hwe cond)
  generalize hP : (bOf (32 * g.toGeo.w) q + isqrt (xOf (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0)
    (bOf (32 * g.toGeo.w) q) % 2 ^ (64 * wq a))) % 2 ^ (32 * g.toGeo.w) / 2 = P at p3 model
  have q3' : A3 6 = wsub (32 * g.toGeo.w) (bOf (32 * g.toGeo.w) q) (isqrt (xOf (32 * g.toGeo.w) (32 * g.toGeo.W)
    (inputValue g s.mem 0) (bOf (32 * g.toGeo.w) q) % 2 ^ (64 * wq a))) / 2 := q3
  generalize hQ : wsub (32 * g.toGeo.w) (bOf (32 * g.toGeo.w) q) (isqrt (xOf (32 * g.toGeo.w) (32 * g.toGeo.W)
    (inputValue g s.mem 0) (bOf (32 * g.toGeo.w) q) % 2 ^ (64 * wq a))) / 2 = Qf at q3' model
  generalize hacc : (okDE (32 * g.toGeo.W) (inputValue g s.mem 2 * inputValue g s.mem 1) &&
    ltOf (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0) (inputValue g s.mem 2 * inputValue g s.mem 1) &&
    decide (rem = 0) && ok4Of (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0) (bOf (32 * g.toGeo.w) q) &&
    decide (isqrt (xOf (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0) (bOf (32 * g.toGeo.w) q) %
      2 ^ (64 * wq a)) * isqrt (xOf (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0)
      (bOf (32 * g.toGeo.w) q) % 2 ^ (64 * wq a)) = xOf (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0)
      (bOf (32 * g.toGeo.w) q) % 2 ^ (64 * wq a))) = accept at m3 model
  have mask3 : slot s3.mem g.B sMask = if accept then 1 else 0 := by
    rw [h3.sl sMask (by simp), m3]; cases accept <;> rfl
  refine WP.mono (stores_ok input3 len zero3 accept mask3) fun t ⟨ht, pb, qb, status, frame, rest⟩ => ?_
  refine ⟨ht, ?_, ?_, h3.rest.trans (rest.mono (by decide))⟩
  · -- The result.
    have key : calculatedD g s.mem = if accept then
        some (Spec.Rsa.i2osp P (inputBytes g s.mem 0).length, Spec.Rsa.i2osp Qf (inputBytes g s.mem 0).length)
        else none := by
      unfold calculatedD Spec.Rsa.primesKeyDet
      dsimp only
      rw [show Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g s.mem 0)) (inputBytes g s.mem 0).length = true
        from valid]
      simp only [ite_true]
      change Option.map _ (Spec.Rsa.recoverDet (inputValue g s.mem 0) (inputValue g s.mem 1) (inputValue g s.mem 2)) = _
      rw [← model]
      cases accept <;> rfl
    unfold WrittenD
    rw [key]
    have plen4 : (inputBytes g s.mem 0).length = (g.buffer 4).len := by
      simp [inputBytes, Spec.Rsa.bytesAt]
    have nlt4 := inputValue_lt g s.mem 0
    change inputValue g s.mem 0 < 2 ^ (8 * (g.buffer 4).len) at nlt4
    cases accept with
    | false =>
      simp only [resultBytes, Bool.false_eq_true, ite_false, Nat.zero_mod, i2osp_zero', Fin.val_zero,
        Fin.val_one, Nat.mul_zero, Nat.mul_one] at pb qb
      simp only [Bool.false_eq_true, ite_false, Option.map_none]
      refine ⟨by rw [status]; rfl, ?_⟩
      simp only [outputBuffersD, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨pb, qb⟩
    | true =>
      simp only [ite_true] at model
      have mul := recoverDet_mul model.symm
      have npos : 0 < inputValue g s.mem 0 := by omega
      have pq : 0 < Qf := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.mul_zero] at mul; omega)
      have qp : 0 < P := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.zero_mul] at mul; omega)
      have ple : P ≤ inputValue g s.mem 0 := Nat.le_trans (Nat.le_mul_of_pos_right _ pq) (Nat.le_of_eq mul)
      have qle : Qf ≤ inputValue g s.mem 0 := Nat.le_trans (Nat.le_mul_of_pos_left _ qp) (Nat.le_of_eq mul)
      simp only [resultBytes, ite_true, h3.arrs 5 (by simp), h3.arrs 6 (by simp), p3, q3', Fin.val_zero,
        Fin.val_one, Nat.mul_zero, Nat.mul_one] at pb qb
      rw [Nat.mod_eq_of_lt (by rw [pLen, plen4]; omega)] at pb
      rw [Nat.mod_eq_of_lt (by rw [qLen, plen4]; omega)] at qb
      simp only [ite_true, Option.map_some]
      refine ⟨by rw [status]; rfl, ?_⟩
      simp only [outputBuffersD, List.map_cons, List.map_nil]
      change [Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len,
        Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len] = _
      rw [pb, qb, pLen, qLen]
  · refine (h3.frame.sub fun r hr => ⟨r, ?_, fun _ h => h⟩).trans frame
    simp only [stageR, VG.Proof.Bignum.X86.CrtRt.frameR, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [bodyWrites]

end VG.Proof.Rsa.X86.Recover
end
