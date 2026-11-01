module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.RvStores
public import VerifiedGarbage.Proof.Rsa.X86.RvLoads
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.RecoverDetModel
import VerifiedGarbage.Proof.Rsa.X86.Rd.Det
import VerifiedGarbage.Proof.Rsa.X86.RvNumbers
import VerifiedGarbage.Proof.Rsa.X86.RvArguments
import VerifiedGarbage.Proof.Rsa.X86.RvProductCore
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Prime recovery by Appendix C.2 on i686, for a valid modulus

`sizedD_ok`: the inputs loaded, `d e`, Appendix C.2 (`det_ok`) and the
factors stored under the mask write `primesKeyDet`'s result (`WrittenD`).
-/

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
