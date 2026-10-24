module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

import VerifiedGarbage.Proof.Rsa.X86.RvFinishY
import VerifiedGarbage.Proof.Rsa.X86.RvFactors
public import VerifiedGarbage.Proof.Rsa.X86.RvStores
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep
public import VerifiedGarbage.Proof.Rsa.RecoverSubtract

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
