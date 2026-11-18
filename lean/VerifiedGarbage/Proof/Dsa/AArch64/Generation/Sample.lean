module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TestWitness
public import VerifiedGarbage.Proof.Bignum.WorkFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ForceSample
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadWitness
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SampleRound
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PublicKernel
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerResult
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! ### `Dsa.AArch64.Generation.WitnessRound`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.Generation.WitnessMont`, which only this module used -/

section

/-! Convert a sampled witness to Montgomery form using the shared arithmetic. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

def witnessMontRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]

theorem witnessMont_ok (M : Mont) {s : State} {B : Addr} {Z w N b : Nat}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hodd : N % 2 = 1) (hN1 : 1 < N) (hx : wv s.mem B (slot w aX) w = b) :
    WP isa (M.mm aXm aX aR2) s fun t =>
      ModulusReady t B Z w N ∧ wv t.mem B (slot w aXm) w = b * 2 ^ (64 * w) % N ∧
      Frm B (witnessMontRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw := h.ws.w2
  have hn := h.ws.scr.nowrap
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  refine WP.mono (M.mm_ok h.ws.good.1 h.ws.good.2 h.ws.w1 (by omega)
    (o := aXm) (a := aX) (b := aR2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h.inverse
    (by rw [h.r2, h.modulus]; exact Nat.mod_lt _ (by omega))) fun t ⟨_, hlt, hy, ha, hk⟩ => ?_
  rw [h.modulus] at hlt hy
  rw [hx, h.r2] at hy
  have hXm : wv t.mem B (slot w aXm) w = b * 2 ^ (64 * w) % N := by
    rw [← Nat.mod_eq_of_lt hlt]
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [hy, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have hf : Frm B (witnessMontRanges w) s.mem t.mem := Frm.of_arrays ha (by simp [witnessMontRanges])
  refine ⟨h.of_frm hEZ hf ?_ hk (by decide) ?_ ?_ ?_, hXm, hf, hk⟩
  · intro r hr
    simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact KMut.ofSlot w _ _
  · intro a ha r hr
    simp only [modulusArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;>
      simp only [slot, hdrBytes, aN, aOne, aR2, aR1, aRm1, aAcc, aTmp, aXm] <;> omega_arith
  · intro r hr
    simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      left <;> simp only [slot, hdrBytes, aAcc, aTmp, aXm, sMinv] <;> omega_arith
  · intro r hr
    simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      right <;> simp only [slot, hdrBytes, aAcc, aTmp, aXm, aE] <;> omega_arith

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.KernelFrame`, which only this module used -/

section

/-! The callable round retains every constant needed for the next witness. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.MillerRabin

theorem kernel_preserves_modulus {s t : State} {B : Addr} {Z w N : Nat}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hf : Frm B (VG.Proof.MillerRabin.AArch64.Caller.callRanges w) s.mem t.mem)
    (hk : Keep mmRegs s t) : ModulusReady t B Z w N := by
  apply h.of_frm hEZ hf ?_ hk (by decide) ?_ ?_ ?_
  · simp only [VG.Proof.MillerRabin.AArch64.Caller.callRanges, mutRanges,
      Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      KMut, VG.Proof.MillerRabin.AArch64.Caller.pad, slot, hdrBytes, aOne,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, sW, sMinv, sArr, sStride, sFn]
    and_intros <;> omega_arith
  · intro a ha
    simp only [modulusArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [VG.Proof.MillerRabin.AArch64.Caller.callRanges, mutRanges,
        Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        VG.Proof.MillerRabin.AArch64.Caller.pad, slot, hdrBytes, aN, aOne, aR2, aR1, aRm1,
        Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
      and_intros <;> omega_arith
  · simp only [VG.Proof.MillerRabin.AArch64.Caller.callRanges, mutRanges,
      Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      VG.Proof.MillerRabin.AArch64.Caller.pad, slot, hdrBytes, aOne, sMinv,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    and_intros <;> omega_arith
  · simp only [VG.Proof.MillerRabin.AArch64.Caller.callRanges, mutRanges,
      Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      VG.Proof.MillerRabin.AArch64.Caller.pad, slot, hdrBytes, aOne, aE,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    and_intros <;> omega_arith

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! The chosen witness is tested by the shared callable windowed round. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.MillerRabin.AArch64

def witnessRoundRanges (w : Nat) : List (Nat × Nat) := witnessMontRanges w ++ Caller.callRanges w

theorem witnessRound_ok (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {s : State} {B : Addr} {Z w N b : Nat}
    (h : ModulusReady s B Z w N) (h4 : 4 ≤ w) (h128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hodd : N % 2 = 1) (h3 : 3 ≤ N)
    (hx : wv s.mem B (slot w aX) w = b) :
    WP isa (Impl.Dsa.AArch64.Generation.witnessRound M.mm K.run) s fun t =>
      ModulusReady t B Z w N ∧ word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round N b) ∧
      Frm B (witnessRoundRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.witnessRound
  refine WP.seq (WP.mono (witnessMont_ok M h hEZ hodd (by omega_using [h3]) hx)
    fun u ⟨hu, hxu, fu, ku⟩ => ?_)
  have hcu : MrCtx u B Z w N (wv u.mem B (slot w aB) w) :=
    ⟨hu.ws, hu.inverse, hu.modulus, rfl, hu.r1, hu.rm1⟩
  refine WP.mono (K.ok (b := b) hcu hu.exponent h4 h128 hEZ hodd h3
    (by simpa only [Nat.mod_mul_mod] using hxu))
    fun t ⟨_, _, hflag, ft, kt⟩ => ?_
  exact ⟨kernel_preserves_modulus hu hEZ ft kt, hflag,
    (fu.mono fun r hr => List.mem_append_left _ hr).trans
      (ft.mono fun r hr => List.mem_append_right _ hr), (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! Native witness selection agrees exactly with RSA's shared sampler. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.Dsa.Generation

theorem sampleWitness_ok {B p : Addr} {Z w N : Nat} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N bs s) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hodd : N % 2 = 1) (hlen : 2 ≤ bs.length) (hmax : bs.length < 4096)
    (hw : bs.length ≤ 8 * w) (hbits : Spec.RsaKeyGen.bitLength (N - 1) = 8 * bs.length) :
    WP isa (Impl.Dsa.AArch64.Generation.sampleWitness bs.length) s fun t =>
      ModulusReady t B Z w N ∧
      wv t.mem B (slot w aX) w = (Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs)).1 ∧
      word t.mem B (8 * kU) = mask (Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs)).2 ∧
      WorkFrame B (testRanges w) [⟨p, bs.length⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  have hz := h.ready.ws.scr.nowrap
  have hX := h.ready.ws.sl (show aX < 16 by decide)
  unfold Impl.Dsa.AArch64.Generation.sampleWitness
  refine WP.seq (WP.mono (testWitness_ok h hEZ hodd (by omega_using [hlen]) hw)
    fun u ⟨hu, hxu, huu, hu9, fu, ku⟩ => ?_)
  refine WP.ite (!decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1))
    (by rw [VG.Proof.MlKem.AArch64.eval_zero, hu9]; cases decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1) <;> decide)
    (fun hbad => ?_) (fun hgood => ?_)
  · have hb : ¬ (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1) := by
      simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hbad
    have hspec := forcedWitnessBytes_spec hlen hbits hb
    have hfl := forcedWitnessBytes_length hlen
    refine WP.seq (WP.mono (forceSample_ok hu hEZ hlen hmax) fun v ⟨hv, huv, fv, kv⟩ => ?_)
    refine WP.mono (loadWitness_ok hv.ready hEZ hv.ptr hv.len hv.source
      (by rw [hfl]; omega_using [hlen]) (by rwa [hfl])) fun t ⟨ht, hxt, ft, kt⟩ => ?_
    refine ⟨ht, ?_, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
    · simpa only [hspec] using hxt
    · rw [ft.word_eq (by intro r hr; rw [List.mem_singleton.mp hr]; left; simp only [kU, slot, hdrBytes, aX]; omega_arith)
        (by decide), huv, huu, hspec]
      simp [hb]
    · exact (fu.work.trans (fv.mono (by simp))).trans (ft.work.mono (by simp [testRanges]))
  · have hg : 2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1 := by simpa using hgood
    have hfit : Spec.Rsa.os2ip bs < 2 ^ (8 * bs.length) := by
      rw [← VG.Proof.Bignum.pow256_eq]
      exact VG.Proof.Rsa.lt_of_os2ip bs
    have hspec : Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs) = (Spec.Rsa.os2ip bs, true) := by
      simp only [Spec.RsaKeyGen.witness, hbits, Nat.mod_eq_of_lt hfit, ite_eq_left hg]
    refine WP.block_nil ⟨hu.ready, ?_, ?_, fu.work, ku⟩
    · simpa only [hspec] using hxu
    · rw [huu, hspec]; simp [hg]

end VG.Proof.Dsa.AArch64.Generation
