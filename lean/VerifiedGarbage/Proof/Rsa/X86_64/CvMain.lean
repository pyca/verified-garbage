module

public import VerifiedGarbage.Proof.Rsa.X86_64.CvCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_crt_values` on x86-64: `main`

From a valid modulus, `main` writes `dP`, `dQ` and `qInv` if `p q = n`
and `gcd(q, p) = 1`, and zeros otherwise (`cvMain_ok`, in `CvMainOk.lean`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- The inputs as numbers. -/
abbrev CvIn.N (I : CvIn) : Nat := Spec.Rsa.os2ip I.nb
abbrev CvIn.P (I : CvIn) : Nat := Spec.Rsa.os2ip I.pb
abbrev CvIn.Q (I : CvIn) : Nat := Spec.Rsa.os2ip I.qb
abbrev CvIn.D (I : CvIn) : Nat := Spec.Rsa.os2ip I.db

/-- Whether `main` writes the values: `p q = n` and `gcd(q, p) = 1`. -/
abbrev CvIn.ok (I : CvIn) : Bool := decide (I.P * I.Q = I.N ∧ Nat.gcd I.Q I.P = 1)

/-- What `main` needs on entry. -/
structure CvPre (I : CvIn) (s : State) : Prop where
  scr : Scr s I.B I.Z
  rdi : s.gpr .rdi = I.B
  args : CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD I.sv
  n : Src s I.B I.Z I.pN I.nb
  p : Src s I.B I.Z I.pP I.pb
  q : Src s I.B I.Z I.pQ I.qb
  d : Src s I.B I.Z I.pD I.db
  L : CvLens I
  oQi : OutOk s I.B I.Z I.pQi I.pl
  oDp : OutOk s I.B I.Z I.pDp I.pl
  oDq : OutOk s I.B I.Z I.pDq I.ql
  a1 : Apart I.pQi I.pl I.pDp I.pl
  a2 : Apart I.pQi I.pl I.pDq I.ql
  a3 : Apart I.pDp I.pl I.pDq I.ql
  wr : s.wr = I.W
  rsp : s.gpr .rsp = I.sp

theorem main_eq : main = seqs (([.block head] : List (Prog isa)) ++
    ((loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
      (loadA aP sP sPl ++ (loadA aQ sQ sQl ++ loadA aD sD sDl))) ++
    (pqCheck ++ (invPart ++ ((divisor aP ++ ([divmod aU aV aC aT] : List (Prog isa))) ++
    (([zeroA aX₁, copyA aX₁ aV] : List (Prog isa)) ++
    ((divisor aQ ++ ([divmod aU aV aC aT] : List (Prog isa))) ++
    (storeA aX₂ sQi sPl Impl.Bignum.X86_64.Public.sMask ++
      (storeA aX₁ sDp sPl Impl.Bignum.X86_64.Public.sMask ++
        (storeA aV sDq sQl Impl.Bignum.X86_64.Public.sMask ++ ([.block retMask] : List (Prog isa)))))))))))) := by
  simp only [main, List.append_assoc, List.cons_append, List.nil_append]

/-- A valid modulus is odd and at least `256^(k - 1)`. -/
theorem valid_lo {N k : Nat} (hv : Spec.Rsa.modulusValid N k = true) : N % 2 = 1 ∧ 256 ^ (k - 1) ≤ N := by
  rw [Spec.Rsa.modulusValid, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hv
  obtain ⟨⟨⟨h1, -⟩, -⟩, h4⟩ := hv
  exact ⟨by simpa using h1, of_decide_eq_true h4⟩

/-- Factors of a valid modulus, each shorter than it: odd and above 1. -/
theorem factors_of {N P Q k pl ql : Nat} (hN : N % 2 = 1) (hlo : 256 ^ (k - 1) ≤ N) (hP : P < 256 ^ pl)
    (hQ : Q < 256 ^ ql) (hpl : pl < k) (hql : ql < k) (h : P * Q = N) :
    P % 2 = 1 ∧ 1 < P ∧ Q % 2 = 1 ∧ 1 < Q := by
  have hp1 : 256 ^ pl ≤ 256 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hq1 : 256 ^ ql ≤ 256 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hpo := (pq_iff hN).mpr h
  have hqo := (pq_iff (P := Q) (Q := P) hN).mpr (by rw [Nat.mul_comm]; exact h)
  refine ⟨hpo.1, ?_, hqo.1, ?_⟩
  · rcases Nat.lt_or_ge 1 P with h1 | h1
    · exact h1
    · exfalso
      have : P * Q ≤ 1 * Q := Nat.mul_le_mul_right _ h1
      omega_arith
  · rcases Nat.lt_or_ge 1 Q with h1 | h1
    · exact h1
    · exfalso
      have : P * Q ≤ P * 1 := Nat.mul_le_mul_left _ h1
      omega_arith

theorem pow256_le_wk (len : Nat) : 256 ^ len ≤ 2 ^ (64 * ((len + 7) / 8)) := by
  rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)

theorem pow256_le_w {len k : Nat} (h : len < k) : 256 ^ len ≤ 2 ^ (64 * wk k) := by
  rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold wk; omega_arith)

/-- `head`: the working space, the mask all ones, and `CvS` from the
memory on entry to `main`. -/
theorem cvHeadS_ok {I : CvIn} {s : State} (h : CvPre I s) :
    WP isa (.block head) s fun t => CvS I s.mem t ∧ mword t.mem I.B = mask true := by
  have L := h.L
  have hZ := L.z
  refine WP.mono (cvHead_ok h.scr h.rdi L.k1 L.k2 hZ h.args.k) fun s₁ ⟨hw₁, hm₁, f₁, k₁⟩ => ⟨?_, hm₁⟩
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have k1 := L.k1
  have hi₁ : InScr I.B I.Z s.mem s₁.mem := InScr.of_frm f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith)
  exact ⟨hw₁, h.args.congr fun i hi => f₁.word_eq (fun r hr => by
      unfold argSlot at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by unfold argSlot at hi; omega_arith),
    h.n.congrK hi₁ k₁, h.p.congrK hi₁ k₁, h.q.congrK hi₁ k₁, h.d.congrK hi₁ k₁, hi₁, k₁.2.2.trans h.wr,
    (k₁.gpr (by decide)).trans h.rsp⟩

end VG.Proof.Rsa.X86_64
