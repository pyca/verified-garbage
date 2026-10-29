module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.RvRestFacts
public import VerifiedGarbage.Proof.Rsa.X86.RvStores
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep
public import VerifiedGarbage.Proof.Rsa.RecoverSubtract

import VerifiedGarbage.Proof.Rsa.X86.RvSearchLoop
import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
import VerifiedGarbage.Proof.Rsa.X86.RvHalving
import VerifiedGarbage.Proof.Rsa.X86.RvFinishY
import VerifiedGarbage.Proof.Rsa.X86.RvFactors
/-! # The complete recovery arithmetic after the initial validity test -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvFinish.lean`, which only this module imported.
section

/-! # The GCD, ordered factors, masked outputs and return value -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sub32 b2n)

def encoded (g : CallGeometry) (accept : Bool) (i : Fin 2) (x : Nat) : List Byte :=
  Spec.Rsa.i2osp ((if accept then x else 0) % 2 ^ (8 * (g.buffer (2 * i.val)).len))
    (g.buffer (2 * i.val)).len

def Finished (g : CallGeometry) (s0 : State) (m y : Nat) (accept : Bool) (t : State) : Prop :=
  let p := Nat.gcd (sub32 g.toGeo.w y 1) m
  let q := m / p
  Inputs g t ∧
    Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len = encoded g accept 0 (max p q) ∧
    Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len = encoded g accept 1 (min p q) ∧
    t.gpr .eax = BitVec.ofNat 32 accept.toNat ∧ Frame (bodyWrites g) s0.mem t.mem ∧
    Keeps opRegs s0 t

theorem fin_ok {g : CallGeometry} {s0 s : State} {A AW V : Nat → Nat} {m k c : Nat}
    {st : Nat × Bool × Bool} (inputs : Inputs g s0) (len : Lengths g) (h : SI g.toGeo s0 A AW V m k c st s)
    (value : A mBase = m) (modulus : A aN = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (hm : 1 < m)
    (zero : A aZ = 0) (one : A aOne = 1) (yl : st.1 < m) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fin s (Finished g s0 m st.1 st.2.2) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fin
  simp only [seqs]
  refine WP.seq (WP.mono (finY_ok h value bound inverse odd hm one yl) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (factors_ok h1
    (by simpa only [upd_ne _ _ (by decide : aN ≠ mY)] using modulus)
    (by rw [upd_self]) (by simpa only [upd_ne _ _ (by decide : aZ ≠ mY)] using zero)
    (by simpa only [upd_ne _ _ (by decide : aOne ≠ mY)] using one) odd hm) fun s2 h2 => ?_)
  have input2 := inputs.of_KS h2
  have zero2 : num s2.mem g.B g.toGeo.w aZero = 0 := by
    rw [h2.arrs aZero (by simp)]
    rfl
  have mask2 : slot s2.mem g.B sMask = if st.2.2 then 1 else 0 := h2.sl sMask (by simp)
  refine WP.mono (stores_ok input2 len zero2 st.2.2 mask2) fun t ⟨inputT, p, q, status, frame, rest⟩ => ?_
  refine ⟨inputT, ?_, ?_, status, ?_, h2.rest.trans rest⟩
  · change Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len = _
    simpa only [resultBytes, h2.arrs 5 (by simp), AF, upd_ne _ _ (by decide : 5 ≠ 6), upd_self, encoded] using p
  · change Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len = _
    simpa only [resultBytes, h2.arrs 6 (by simp), AF, upd_self, encoded] using q
  · refine (h2.frame.sub fun r hr => ⟨r, ?_, fun _ h => h⟩).trans frame
    simp only [stageR, VG.Proof.Bignum.X86.CrtRt.frameR, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [bodyWrites]

end VG.Proof.Rsa.X86.Recover
end

end

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (splitTwos recoverPrimes)
open VG.Proof.Rsa (pqOf)

def RestResult (g : CallGeometry) (s0 : State) (t : State) : Prop :=
  ∃ y ok tries, Finished g s0 (inputValue g s0.mem 0) y ok t ∧
    y < inputValue g s0.mem 0 ∧ (ok = true → 1 ≤ y) ∧
    ((if ok then some (pqOf (inputValue g s0.mem 0) y) else none), tries) =
      recoverPrimes (inputValue g s0.mem 0) (inputValue g s0.mem 1) (inputValue g s0.mem 2)

/-- What `fin` needs after either schedule's search: the squares' state over the modulus, its inverse and
the constants, and the root found with the attempts it took, as `recoverPrimes` gives them. -/
def FinIn (g : CallGeometry) (s0 : State) (t : State) : Prop :=
  ∃ (A AW V : Nat → Nat) (k c j : Nat) (st : Nat × Bool × Bool),
    SI g.toGeo s0 A AW V (inputValue g s0.mem 0) k c st t ∧ A mBase = inputValue g s0.mem 0 ∧
    A aN = inputValue g s0.mem 0 ∧ (inputValue g s0.mem 0 * V sInv + 1) % 2 ^ 32 = 0 ∧ A aZ = 0 ∧
    A aOne = 1 ∧ st.1 < inputValue g s0.mem 0 ∧ (st.2.2 = true → 1 ≤ st.1) ∧
    ((if st.2.2 then some (pqOf (inputValue g s0.mem 0) st.1) else none), j) =
      recoverPrimes (inputValue g s0.mem 0) (inputValue g s0.mem 1) (inputValue g s0.mem 2)

theorem finIn_ok {g : CallGeometry} {s0 s : State} (inputs : Inputs g s0) (len : Lengths g)
    (bound : inputValue g s0.mem 0 < 2 ^ (64 * g.n)) (odd : inputValue g s0.mem 0 % 2 = 1)
    (large : 101 < inputValue g s0.mem 0) (F : FinIn g s0 s) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fin s (RestResult g s0) := by
  obtain ⟨A, AW, V, k, c, j, st, h, value, modulus, inverse, zero, one, small, pos, found⟩ := F
  exact WP.mono (fin_ok inputs len h value modulus bound inverse odd (by omega) zero one small)
    fun t finished => ⟨st.1, st.2.2, j, finished, small, pos, found⟩

omit rsaBatchLaw in
theorem rest_ok {g : CallGeometry} {s0 s : State} (inputs : Inputs g s0)
    (h : KS g.toGeo s0 (fun _ => inputValue g s0.mem 0) [aN]
      (fun _ => 2 * (product g s0.mem / 2)) [wM] (fun _ => 0) [] s)
    (go : GoOn (product g s0.mem))
    (bound : inputValue g s0.mem 0 < 2 ^ (64 * g.n))
    (odd : inputValue g s0.mem 0 % 2 = 1) (large : 101 < inputValue g s0.mem 0) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.rest s (FinIn g s0) := by
  obtain ⟨ae, ad⟩ := inputArguments inputs
  obtain ⟨count, limit⟩ := inputs.countBounds
  obtain ⟨evenValue, positive, _, fit⟩ := exponent_facts go
  obtain ⟨tpos, tbound, rbound⟩ := split_facts go
  have halves : hvs (exponent g s0.mem) (countBits g) =
      ((splitTwos (exponent g s0.mem)).2, (splitTwos (exponent g s0.mem)).1) :=
    VG.Proof.Rsa.halve_done positive fit
  unfold VG.Impl.Rsa.X86.RecoverRt.rest
  simp only [seqs]
  refine WP.seq (WP.mono (halving_ok h (by simp) evenValue ae ad count limit) fun s1 h1 => ?_)
  change KS g.toGeo s0 (fun _ => inputValue g s0.mem 0) [aN]
    (AWh (exponent g s0.mem) (countBits g)) [wR]
    (Vh (countBits g) (exponent g s0.mem) (countBits g)) [sTc, sCnt] s1 at h1
  have aw : AWh (exponent g s0.mem) (countBits g) = fun _ => (splitTwos (exponent g s0.mem)).2 :=
    funext fun _ => congrArg Prod.fst halves
  rw [aw] at h1
  simp only [Vh, halves, Nat.sub_self] at h1
  refine WP.seq (WP.mono (mont_ok h1 rfl bound odd (by omega)) fun s2 ⟨h2, mr⟩ => ?_)
  obtain ⟨I, tracked, inverse⟩ := h2.trackInverse mr (by decide)
  refine (WP.mono (candLoop_ok
    (by simp [AM, upd, aZ, aNg, aO, mXm, mR2, mBase, aOne])
    (by simp [AM, upd, mBase, aNg, aO, mXm, mR2]) bound
    (by simpa only [upd_self] using inverse) odd large
    (by simp [AM, upd, aO, aNg]) (by simp [AM, upd])
    (by simp [AM, upd, mR2, aNg, aO, mXm]) ae ad
    (by simpa [countBits, upd, sTc, sInv, sCnt] using tbound) rbound count limit inputs.countWide tracked
    (by simp [upd, sCnt, sInv]) (by simpa [upd, sTc, sInv, sCnt] using tpos))
    fun s3 ⟨j, st, _, hs, small, pos, found⟩ => ?_)
  refine ⟨_, _, _, _, _, j + 1, st, hs,
    (by simp [AM, upd, mBase, aNg, aO, mXm, mR2]),
    (by simp [AM, upd, aN, aNg, aO, mXm, mR2, mBase, aOne, aZ]),
    (by simpa [VJ, upd, sInv, sCand, sCnt] using inverse),
    (by simp [AM, upd, aZ, aNg, aO, mXm, mR2, mBase, aOne]),
    (by simp [AM, upd, aOne, aNg, aO, mXm, mR2, mBase]), small, pos, ?_⟩
  rw [VG.Proof.Rsa.recoverPrimes_go go]
  simpa only [upd_ne _ _ (by decide : sTc ≠ sInv), upd_ne _ _ (by decide : sTc ≠ sCnt), upd_self,
    exponent, product, Spec.Rsa.recoverTries] using found

end VG.Proof.Rsa.X86.Recover
