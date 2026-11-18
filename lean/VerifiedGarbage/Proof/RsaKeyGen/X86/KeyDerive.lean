module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEvenFrame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRetry
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Spec.Rsa
public import Init.Data.Nat.Coprime
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `RsaKeyGen.X86.KeyScratchFrame`, which the modules that import this one used -/

section

/-! ### `RsaKeyGen.X86.KeyInput`, which this module and modules that import it used -/

section

/-! # The retained header and buffer permissions survive scratch arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot

structure Input (E : Environment) (s : State) : Prop where
  valid : E.Valid
  ws : Ws s E.base E.size E.n 32
  arguments : ∀ i < 18, s.mem.readW (off E.base (4 * i)) 32 = E.argument i
  outWrite : ∀ i < 7, InRegions s.wr (E.outputRegion i).base (E.outputRegion i).len
  exponentRead : InRegions (s.rd ++ s.wr) E.exponentRegion.base E.exponentRegion.len

theorem Input.outputs {E : Environment} {s : State} (h : Input E s) : OutputInput E.outputs s := by
  refine ⟨h.ws, h.valid.outputs, fun i hi => h.arguments i (by omega_using [hi]), ?_⟩
  intro i hi
  rw [h.valid.outputRegion hi]
  exact h.outWrite i hi

theorem Input.keep {E : Environment} {s t : State} {rs : List Reg} (h : Input E s)
    (ws : Ws t E.base E.size E.n 32) (K : Keeps rs s t)
    (header : ∀ d, d + 4 ≤ 72 → t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32) : Input E t := by
  refine ⟨h.valid, ws, ?_, ?_, ?_⟩
  · intro i hi
    rw [header (4 * i) (by omega_using [hi])]
    exact h.arguments i hi
  · intro i hi
    rw [K.2.2]
    exact h.outWrite i hi
  · rw [K.2.1, K.2.2]
    exact h.exponentRead

theorem Input.afterOuts {E : Environment} {s t : State} {regs : List Reg} {rs : List (Nat × Nat)}
    (h : Input E s) (ws : Ws t E.base E.size E.n 32) (K : Keeps regs s t)
    (lower : ∀ r ∈ rs, 72 ≤ r.1) (O : Outs E.base rs s.mem t.mem) : Input E t := by
  apply h.keep ws K
  intro d hd
  apply BitVec.eq_of_toNat_eq
  have H : val32 t.mem E.base d 1 = val32 s.mem E.base d 1 :=
    O.val32 (d := d) (k := 1) (fun r hr => Or.inl (Nat.le_trans hd (lower r hr))) (by omega_using [hd])
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

theorem Input.afterStage {E : Environment} {s t : State} {regs : List Reg} {js : List Nat}
    (h : Input E s) (ws : Ws t E.base E.size E.n 32) (K : Keeps regs s t)
    (O : Outs E.base (stageRanges E.n js) s.mem t.mem) : Input E t := by
  apply h.keep ws K
  intro d hd
  apply BitVec.eq_of_toNat_eq
  have H := stage_preserves_header (n := E.n) (d := d) (count := 1)
    (by change d + 4 ≤ VG.Impl.RsaKeyGen.X86.Key.kOk; unfold VG.Impl.RsaKeyGen.X86.Key.kOk; omega_using [hd]) O
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Scratch-local steps preserve the encoded primes and public exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem outs_scratch_frame {B : Addr} {Z : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (size : Z ≤ 2 ^ 64) (O : Outs B rs m m') (fit : ∀ r ∈ rs, r.1 + r.2 ≤ Z) :
    Frame [⟨B, Z⟩] m m' := by
  have outside : Outside B 0 Z m m' := by
    intro a ha
    apply O a
    intro r hr
    have H := fit r hr
    omega_using [ha, H]
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    VG.Proof.Bignum.outside_frame outside (by simpa only [Nat.zero_add] using size)

theorem stage_scratch_frame {s : State} {B : Addr} {Z n : Nat} {js : List Nat} {m m' : Mem}
    (h : Ws s B Z n 32) (indices : ∀ j ∈ js, j < 32) (O : Outs B (stageRanges n js) m m') :
    Frame [⟨B, Z⟩] m m' := by
  have head := h.hdr_le
  apply outs_scratch_frame (by have := h.workspace.nowrap; omega_using [this]) O
  intro r hr
  rcases List.mem_append.mp hr with temp | output
  · simp only [exponentTemps, List.mem_cons, List.not_mem_nil, or_false] at temp
    rcases temp with rfl | rfl
    · unfold kOk hdr at *
      omega_using [head]
    · exact Nat.le_trans (arr_mono (by decide : 15 ≤ 32)) h.fits
  · simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at output
    obtain ⟨j, hj, rfl⟩ := output
    exact h.arr_fit (indices j hj)

theorem Input.output_preserved {E : Environment} {s : State} {m m' : Mem} {i : Nat}
    (h : Input E s) (hi : i < 7) (F : Frame [E.workspaceRegion] m m') :
    Spec.Rsa.bytesAt m' (E.outputRegion i).base (E.outputRegion i).len =
      Spec.Rsa.bytesAt m (E.outputRegion i).base (E.outputRegion i).len := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by change E.outputLength i < 2 ^ 64; have H := h.valid.outFit i hi; omega_using [H])
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact h.valid.outputScratch i hi

theorem Input.exponent_preserved {E : Environment} {s : State} {m m' : Mem}
    (h : Input E s) (F : Frame [E.workspaceRegion] m m') :
    Spec.Rsa.bytesAt m' E.exponentRegion.base E.exponentRegion.len =
      Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by change E.exponentLength < 2 ^ 64; have H := h.valid.exponentLength; omega_using [H])
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact h.valid.exponentScratch

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyPartOutcome`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyPartResult`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyCrtCorrect`, which this module and modules that import it used -/

section

/-! # Compute both CRT exponents with safe fixed-schedule division -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def crtArrays : List Nat := [aDen, aU, aDp, aDq]
def crtDivisor (x : Nat) : Nat := if x = 0 then 1 else x

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The computed key components before masked external export -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def keyPartArrays : List Nat := [aDen, aQi, aU, aDp, aDq, aN]

structure KeyPartResult (B : Addr) (n : Nat) (m : Mem) (t : State) : Prop where
  modulus : num t.mem B n aN = num m B n aPa * num m B n aQa
  dp : num t.mem B n aDp = num m B n aD % crtDivisor (num m B n aPm)
  dq : num t.mem B n aDq = num m B n aD % crtDivisor (num m B n aQm)
  qiBound : num t.mem B n aQi < safePrime (num m B n aPa)
  qiCongruence : (safePrime (num m B n aPa) : Int) ∣
    (num t.mem B n aQi : Int) * num m B n aQa - Nat.gcd (num m B n aQa) (safePrime (num m B n aPa))
  mask : slot t.mem B kOk = (if slot m B kOk = 1 ∧
    Nat.gcd (num m B n aQa) (safePrime (num m B n aPa)) = 1 ∧
    2 ^ (32 * n - 1) ≤ num m B n aPa * num m B n aQa ∧
    num m B n aPa % 2 = 1 ∧ num m B n aQa % 2 = 1 ∧
    Spec.Rsa.exponentValid (val32 m B kEv 2) = true then 1 else 0)
  status : slot t.mem B kStatus = slot t.mem B kOk

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The native post-retry arithmetic produces the shared key or failure -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

/-- The key part's outcome (`CoreOutcome`), from what it leaves of the factors, `d` and `e`. -/
theorem KeyReady.part_of {s t : State} {B : Addr} {n e p q : Nat}
    (lower : 16 ≤ n) (upper : n ≤ 256)
    (boundP : p < 2 ^ (16 * n)) (boundQ : q < 2 ^ (16 * n))
    (R : KeyReady B n e p q s.mem)
    (notSmall : ¬(slot s.mem B kOk = 1 ∧ num s.mem B n aD ≤ 2 ^ (16 * n)))
    (keptP : num t.mem B n aPa = num s.mem B n aPa) (keptQ : num t.mem B n aQa = num s.mem B n aQa)
    (keptD : num t.mem B n aD = num s.mem B n aD) (keptE : val32 t.mem B kEv 2 = val32 s.mem B kEv 2)
    (K : KeyPartResult B n s.mem t) :
    CoreOutcome B n e p q t.mem := by
  have boundE : e < 2 ^ 64 := by rw [← R.exponent]; exact val32_lt _ _ _ _
  have congruence := K.qiCongruence
  have boundX := K.qiBound
  rw [R.pValue, R.qValue] at congruence
  rw [R.pValue] at boundX
  have code := keyFromPrimes_native lower upper boundP boundQ boundE congruence boundX
  have mask := K.mask
  rw [R.pValue, R.qValue, R.exponent] at mask
  unfold CoreOutcome
  rw [code]
  by_cases empty : slot s.mem B kOk = 0
  · have inverse := R.inverse
    rw [empty, ite_eq_left rfl] at inverse
    rw [inverse]
    dsimp only
    have M : slot t.mem B kOk = 0 := by simpa only [empty, Nat.zero_ne_one, false_and, ite_false] using mask
    exact ⟨K.status.trans M, M⟩
  · have unit : slot s.mem B kOk = 1 := by have H := R.bit; omega_using [empty, H]
    have inverse := R.inverse
    rw [unit, ite_eq_right (by decide : ¬(1 : Nat) = 0)] at inverse
    have large : ¬num s.mem B n aD ≤ 2 ^ (16 * n) := fun small => notSmall ⟨unit, small⟩
    rw [inverse]
    dsimp only
    rw [ite_eq_right large]
    have M : slot t.mem B kOk = if nativeShape n e (max p q) (min p q) then 1 else 0 := by
      rw [unit] at mask
      simpa only [nativeShape, true_and, and_assoc, and_comm, and_left_comm] using mask
    by_cases shape : nativeShape n e (max p q) (min p q)
    · rw [ite_eq_left shape]
      have accepted : slot t.mem B kOk = 1 := by rw [M, ite_eq_left shape]
      refine ⟨K.status.trans accepted, accepted, ?_⟩
      have two : 2 ≤ 2 ^ (16 * n) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega_using [lower] : 1 ≤ 16 * n)
      have factors := VG.Proof.RsaKeyGen.primes_of_inverse
        (Nat.le_trans (Nat.min_le_left p q) (Nat.le_max_left p q)) inverse (by omega_using [boundP, notSmall, unit])
      have Pm : max p q - 1 ≠ 0 := by omega_using [factors]
      have Qm : min p q - 1 ≠ 0 := by omega_using [factors]
      have pFinal : num t.mem B n aPa = max p q := keptP.trans R.pValue
      have qFinal : num t.mem B n aQa = min p q := keptQ.trans R.qValue
      have dFinal : num t.mem B n aD = num s.mem B n aD := keptD
      have eFinal : val32 t.mem B kEv 2 = e := keptE.trans R.exponent
      have dp := K.dp
      have dq := K.dq
      rw [R.pm, crtDivisor, ite_eq_right Pm] at dp
      rw [R.qm, crtDivisor, ite_eq_right Qm] at dq
      unfold assembledKey
      rw [K.modulus, R.pValue, R.qValue, pFinal, qFinal, dFinal, eFinal, dp, dq]
    · rw [ite_eq_right shape]
      have rejected : slot t.mem B kOk = 0 := by rw [M, ite_eq_right shape]
      exact ⟨K.status.trans rejected, rejected⟩

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Complete native numeric RSA derivation, including all failure cases -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def deriveArrays : List Nat := prepareArrays ++ keyPartArrays

end VG.Proof.RsaKeyGen.X86.Key
