module
-- separate module: its correctness proofs (`det_ok`, `sizedD_ok`) build in parallel with the timing's stages, `TimeSteps` and `TimeCheck`

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.RvStores
public import VerifiedGarbage.Proof.Rsa.X86.RvLoads
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.X86.RvNumbers
import VerifiedGarbage.Proof.Rsa.X86.RvArguments
import VerifiedGarbage.Proof.Rsa.X86.RvProductCore
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Twos
import VerifiedGarbage.Proof.Rsa.X86.Rd.Gcd
import VerifiedGarbage.Proof.Rsa.X86.Rd.Stages
import VerifiedGarbage.Proof.Rsa.X86.Rd.Stages2
import VerifiedGarbage.Proof.Rsa.X86.Rd.Sqrt

/-! # Prime recovery by Appendix C.2 on i686, for a valid modulus

`sizedD_ok`: the inputs loaded, `d e`, Appendix C.2 (`det_ok`) and the
factors stored under the mask write `primesKeyDet`'s result (`WrittenD`).
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
  refine WP.seq (WP.mono (gcdSetD_ok h2 u2 x2) fun s3 ⟨A3, h3, m3, x3, n3⟩ => ?_)
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
  refine WP.seq (WP.mono (square_ok h7 q7 one7 z7 nW7 z27)
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
  refine WP.mono (factorsD_ok h10 (okde := okDE (32 * g.W) de) (lt := ltOf (32 * g.w) (32 * g.W) n de)
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
end


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
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.RecoverDet
open VG.Proof.Rsa (b2n)

theorem sizedD_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (valid : Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true)
    (pLen : (g.buffer 0).len = (inputBytes g s.mem 0).length)
    (qLen : (g.buffer 2).len = (inputBytes g s.mem 0).length)
    (eSmall : (g.buffer 6).len ≤ 8) :
    WP isa VG.Impl.Rsa.X86.RecoverDetRt.sized s fun t => Inputs g t ∧ WrittenD g s.mem t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps opRegs s t := by
  have facts := valid
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at facts
  have odd : inputValue g s.mem 0 % 2 = 1 := facts.1.1.1
  have large : 3 ≤ inputValue g s.mem 0 := by
    have lower := facts.1.1.2
    have power (k : Nat) (hk : 2 ≤ k) : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (n := 2) (by decide) hk
    have bigger := power 511 (by decide)
    omega
  have up := h.upper
  have nb : inputValue g s.mem 0 < 2 ^ (64 * g.n) := by
    apply Nat.lt_of_lt_of_le (inputValue_lt g s.mem 0)
    apply Nat.pow_le_pow_right (by decide)
    have := h.inputBound 0
    omega
  have small : inputValue g s.mem 0 < 2 ^ (32 * g.toGeo.w) :=
    Nat.lt_of_lt_of_le nb (Nat.pow_le_pow_right (by decide) (by change 64 * g.n ≤ 32 * (2 * g.n + 2); omega))
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
  refine WP.seq (WP.mono (det_ok h2' (n := inputValue g s.mem 0) (de := inputValue g s.mem 2 * inputValue g s.mem 1)
    rfl (by simp [AWp, upd]) (by simp [AWp, AW1, upd, wZ, wM, wMod, wE, wD]) odd large small)
    fun s3 ⟨A3, V3, q, rem, h3, cond, p3, q3, z3, m3⟩ => ?_)
  have input3 := h.of_KS h3
  have zero3 : num s3.mem g.B g.toGeo.w VG.Impl.Rsa.X86.Keys.aZero = 0 := by
    rw [h3.arrs VG.Impl.Rsa.X86.Keys.aZero (by simp), z3]
  generalize hacc : (okDE (32 * g.toGeo.W) (inputValue g s.mem 2 * inputValue g s.mem 1) &&
    ltOf (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0) (inputValue g s.mem 2 * inputValue g s.mem 1) &&
    (stage2 (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0) q rem).1) = accept at m3
  have mask3 : slot s3.mem g.B sMask = if accept then 1 else 0 := by
    rw [h3.sl sMask (by simp), m3]; cases accept <;> rfl
  refine WP.mono (stores_ok input3 len zero3 accept mask3) fun t ⟨ht, pb, qb, status, frame, rest⟩ => ?_
  refine ⟨ht, ?_, ?_, h3.rest.trans (rest.mono (by decide))⟩
  · -- The result.
    have model := model_correct (nb := 32 * g.toGeo.w) (wb := 32 * g.toGeo.W) (q := q) (rem := rem)
      (e := inputValue g s.mem 1) (d := inputValue g s.mem 2) odd large hn8 hde
      (by change 2 * (32 * (2 * g.n + 2)) ≤ 32 * (2 * (2 * g.n + 2) + 2); omega)
      (by change 32 * (2 * (2 * g.n + 2) + 2) % 2 = 0; omega) cond
    rw [result, hacc] at model
    have key : calculatedD g s.mem = if accept then
        some (Spec.Rsa.i2osp (stage2 (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0) q rem).2.1
          (inputBytes g s.mem 0).length,
          Spec.Rsa.i2osp (stage2 (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0) q rem).2.2
          (inputBytes g s.mem 0).length) else none := by
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
    have plen : (inputBytes g s.mem 0).length = (g.buffer 4).len := by
      simp [inputBytes, Spec.Rsa.bytesAt]
    have nlt := inputValue_lt g s.mem 0
    change inputValue g s.mem 0 < 2 ^ (8 * (g.buffer 4).len) at nlt
    cases accept with
    | false =>
      simp only [resultBytes, Bool.false_eq_true, ite_false, Nat.zero_mod, i2osp_zero', Fin.val_zero,
        Fin.val_one, Nat.mul_zero, Nat.mul_one] at pb qb
      simp only [Bool.false_eq_true, ite_false, Option.map_none]
      refine ⟨by rw [status]; rfl, ?_⟩
      simp only [outputBuffersD, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨pb, qb⟩
    | true =>
      have mul := recoverDet_mul model.symm
      have npos : 0 < inputValue g s.mem 0 := by omega
      have pq : 0 < (stage2 (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0) q rem).2.2 := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.mul_zero] at mul; omega)
      have qp : 0 < (stage2 (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0) q rem).2.1 := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.zero_mul] at mul; omega)
      have ple : (stage2 (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0) q rem).2.1 ≤ inputValue g s.mem 0 := by
        exact Nat.le_trans (Nat.le_mul_of_pos_right _ pq) (Nat.le_of_eq mul)
      have qle : (stage2 (32 * g.toGeo.w) (32 * g.toGeo.W) (inputValue g s.mem 0) q rem).2.2 ≤ inputValue g s.mem 0 := by
        exact Nat.le_trans (Nat.le_mul_of_pos_left _ qp) (Nat.le_of_eq mul)
      simp only [resultBytes, ite_true, h3.arrs 5 (by simp), h3.arrs 6 (by simp), p3, q3, Fin.val_zero,
        Fin.val_one, Nat.mul_zero, Nat.mul_one] at pb qb
      rw [Nat.mod_eq_of_lt (by rw [pLen, plen]; omega)] at pb
      rw [Nat.mod_eq_of_lt (by rw [qLen, plen]; omega)] at qb
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
