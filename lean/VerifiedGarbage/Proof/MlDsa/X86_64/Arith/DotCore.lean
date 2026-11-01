module

import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.MontgomeryCore
public import VerifiedGarbage.Proof.MlDsa.Arith.DotSum
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Dot
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlDsa.FusedInverseContract
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLanes
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
public meta import Lean.Elab.Tactic.Basic

/-!
# ML-DSA on x86-64: a row's sum of products, in the doublewords of an SSE register

`dotMac` adds the products of the even doublewords of `xmm0` and `xmm1` to
the quadwords of `xmm5` (`macE`) and those of the odd ones to `xmm6`
(`macO`); `dotRed` reduces each quadword (`redV`, `dword_redV`) and merges
them. From quadword sums `dsum` of at most seven products of coefficients
below `3 q`, each doubleword of the result is the sum times `2⁻³²`, reduced
(`dot_lane`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (XOnly)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt PolyIs montgomeryRInv)

/-- The quadwords of `x` plus `m · q` (`vredc`). -/
def vredcV (x : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddq x (XBinOp.eval .pmuludq (XBinOp.eval .pmuludq x qinvV) qV)

/-- `dotRed`'s merge of the reductions of `e` (even) and `o` (odd). -/
def redV (e o : BitVec 128) : BitVec 128 := XBinOp.eval .por (XShiftOp.eval .psrlq (vredcV e) 32) (vredcV o)

/-- The products of the even doublewords of `a` and `b` added to `acc`. -/
def macE (acc a b : BitVec 128) : BitVec 128 := XBinOp.eval .paddq acc (XBinOp.eval .pmuludq a b)

/-- The products of the odd doublewords of `a` and `b` added to `acc`. -/
def macO (acc a b : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddq acc (XBinOp.eval .pmuludq (XShiftOp.eval .psrlq a 32) (XShiftOp.eval .psrlq b 32))

theorem dotZero_ok (s : State) :
    WP isa (.block dotZero) s fun s' => s'.xmm .xmm5 = 0 ∧ s'.xmm .xmm6 = 0 ∧ XOnly [.xmm5, .xmm6] s s' := by
  simp only [dotZero, xb]
  vrun
  exact ⟨by simp [XBinOp.eval], by simp [XBinOp.eval], by xonly⟩

theorem dotMac_ok (s : State) :
    WP isa (.block dotMac) s fun s' => s'.xmm .xmm5 = macE (s.xmm .xmm5) (s.xmm .xmm0) (s.xmm .xmm1) ∧
      s'.xmm .xmm6 = macO (s.xmm .xmm6) (s.xmm .xmm0) (s.xmm .xmm1) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm5, .xmm6] s s' := by
  simp only [dotMac, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨rfl, rfl, by xonly⟩

theorem dotRed_ok {s : State} (hc : VConsts s) :
    WP isa (.block dotRed) s fun s' => s'.xmm .xmm5 = csubV (redV (s.xmm .xmm5) (s.xmm .xmm6)) ∧
      XOnly [.xmm2, .xmm5, .xmm6] s s' := by
  simp only [dotRed, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv]
  exact ⟨rfl, by xonly⟩

theorem qword_macE {acc a b : BitVec 128} {k : Nat} (hk : k < 2)
    (h : (qword acc k).toNat + (dword a (2 * k)).toNat * (dword b (2 * k)).toNat < 2 ^ 64) :
    (qword (macE acc a b) k).toNat = (qword acc k).toNat + (dword a (2 * k)).toNat * (dword b (2 * k)).toNat := by
  rw [macE, qword_paddq _ _ hk, BitVec.toNat_add, toNat_qword_pmuludq _ _ hk, Nat.mod_eq_of_lt h]

theorem dword_psrlq32 (a : BitVec 128) {k : Nat} (hk : k < 2) :
    dword (XShiftOp.eval .psrlq a 32) (2 * k) = dword a (2 * k + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [dword_lo, dword_hi, qword_psrlq32 _ hk, lo_shr32]

theorem qword_macO {acc a b : BitVec 128} {k : Nat} (hk : k < 2)
    (h : (qword acc k).toNat + (dword a (2 * k + 1)).toNat * (dword b (2 * k + 1)).toNat < 2 ^ 64) :
    (qword (macO acc a b) k).toNat =
      (qword acc k).toNat + (dword a (2 * k + 1)).toNat * (dword b (2 * k + 1)).toNat := by
  rw [macO, qword_paddq _ _ hk, BitVec.toNat_add, toNat_qword_pmuludq _ _ hk, dword_psrlq32 _ hk,
    dword_psrlq32 _ hk, Nat.mod_eq_of_lt h]

theorem dword_redV {e o : BitVec 128} (he : ∀ k < 2, (qword e k).toNat < q * 2 ^ 32)
    (ho : ∀ k < 2, (qword o k).toNat < q * 2 ^ 32) {k : Nat} (hk : k < 2) :
    (dword (redV e o) (2 * k)).toNat = mont (qword e k).toNat ∧
      (dword (redV e o) (2 * k + 1)).toNat = mont (qword o k).toNat := by
  have hqi : (lo32 (qword qinvV k)).toNat = montQInv := lo32_qword_qinvV hk
  have hqq : (lo32 (qword qV k)).toNat = q := lo32_qword_qV hk
  have ve : qword (vredcV e) k = redc (qword e k) (qword qinvV k) (qword qV k) := qword_vredc _ hk
  have vo : qword (vredcV o) k = redc (qword o k) (qword qinvV k) (qword qV k) := qword_vredc _ hk
  constructor
  · rw [redV, dword_por, dword_lo, dword_lo, qword_psrlq32 _ hk, ve, vo, redc_lo hqi hqq (ho k hk),
      or_zero_toNat, lo_shr32, redc_hi hqi hqq (he k hk)]
  · rw [redV, dword_por, dword_hi, dword_hi, qword_psrlq32 _ hk, hi_shr32, zero_or_toNat, vo,
      redc_hi hqi hqq (ho k hk)]

/-- A sum of at most seven products of coefficients below `3 q`, reduced:
each doubleword of `dotRed`'s result from the sums in the quadwords. -/
theorem dot_lane {e o : BitVec 128} {A B : Nat → Nat → Nat} {c : Nat} (hc : c ≤ 7)
    (hA : ∀ j < c, ∀ i < 4, A j i < 3 * q) (hB : ∀ j < c, ∀ i < 4, B j i < 3 * q)
    (he : ∀ k < 2, (qword e k).toNat = dsum (fun j => A j (2 * k)) (fun j => B j (2 * k)) c)
    (ho : ∀ k < 2, (qword o k).toNat = dsum (fun j => A j (2 * k + 1)) (fun j => B j (2 * k + 1)) c)
    {i : Nat} (hi : i < 4) :
    (dword (csubV (redV e o)) i).toNat = (Fin.ofNat q (dsum (fun j => A j i) (fun j => B j i) c) * montgomeryRInv).val := by
  have hb : ∀ i < 4, dsum (fun j => A j i) (fun j => B j i) c < q * 2 ^ 32 := fun i hi => by
    have h1 := dsum_le (A := fun j => A j i) (B := fun j => B j i) (b := 3 * q * (3 * q)) (c := c)
      (fun j hj => Nat.mul_le_mul (Nat.le_of_lt (hA j hj i hi)) (Nat.le_of_lt (hB j hj i hi)))
    exact Nat.lt_of_le_of_lt (Nat.le_trans h1 (Nat.mul_le_mul_right _ hc)) (by decide)
  have he' : ∀ k < 2, (qword e k).toNat < q * 2 ^ 32 := fun k hk => by rw [he k hk]; exact hb _ (by omega)
  have ho' : ∀ k < 2, (qword o k).toNat < q * 2 ^ 32 := fun k hk => by rw [ho k hk]; exact hb _ (by omega)
  have fin : ∀ x : Nat, condSub (mont x) = mont x % q → mont x % q = x * 8265825 % q →
      condSub (mont x) = (Fin.ofNat q x * montgomeryRInv).val := fun x h1 h2 => by
    rw [h1, h2, Fin.val_mul, Fin.val_ofNat, Nat.mul_mod]; rfl
  obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 2, i = 2 * k ∨ i = 2 * k + 1 := ⟨i / 2, by omega, by omega⟩
  · rw [dword_csubV _ hi, csubL_toNat (by rw [(dword_redV he' ho' hk).1]; exact mont_lt (he' k hk)),
      (dword_redV he' ho' hk).1, he k hk]
    exact fin _ (condSub_mont (hb _ hi)) (mont_inverse _)
  · rw [dword_csubV _ hi, csubL_toNat (by rw [(dword_redV he' ho' hk).2]; exact mont_lt (ho' k hk)),
      (dword_redV he' ho' hk).2, ho k hk]
    exact fin _ (condSub_mont (hb _ hi)) (mont_inverse _)

/-! ## The function's contract, for every implementation -/

/-- Coefficient `k` of polynomial `j` of the family at `p`. -/
def famV (m : VG.Mem) (p : Addr) (j k : Nat) : Nat := (coeffAt m (p + BitVec.ofNat 64 (1024 * j)) k).toNat

theorem prod_bound {c T : Nat} (hc : c ≤ 7) {Av Bv : Nat → Nat → Nat} (hA : ∀ j < c, ∀ t < T, Av j t < 3 * q)
    (hB : ∀ j < c, ∀ t < T, Bv j t < 3 * q) {n : Nat} (hn : n < c) {t : Nat} (ht : t < T) :
    dsum (fun j => Av j t) (fun j => Bv j t) n + Av n t * Bv n t < 2 ^ 64 := by
  have h := dsum_le (A := fun j => Av j t) (B := fun j => Bv j t) (b := 3 * q * (3 * q)) (c := n + 1)
    (fun j hj => Nat.mul_le_mul (Nat.le_of_lt (hA j (by omega) t ht)) (Nat.le_of_lt (hB j (by omega) t ht)))
  rw [dsum] at h
  exact Nat.lt_of_le_of_lt (Nat.le_trans h (Nat.mul_le_mul_right _ (show n + 1 ≤ 8 by omega))) (by decide)

theorem addr_fam (p : Addr) (k j : Nat) :
    coeffAddr p k + BitVec.ofNat 64 (1024 * j) = coeffAddr (p + BitVec.ofNat 64 (1024 * j)) k := by
  simp only [coeffAddr]; rw [VG.Offset.add_add, VG.Offset.add_add, Nat.add_comm]

/-- A family of `c` polynomials. -/
abbrev famR (p : Addr) (c : Nat) : Region := ⟨p, 1024 * c⟩

/-- `vg_mldsa_dot_inverse{c}(out = rdi, a = rsi, b = rdx, scratch = rcx)`. -/
def dotK (c : Nat) : Contract isa where
  pre s :=
    s.rd = [famR (s.gpr .rsi) c, famR (s.gpr .rdx) c] ∧ s.wr = [pR (s.gpr .rdi), pR (s.gpr .rcx)] ∧
    (pR (s.gpr .rdi)).Disjoint (famR (s.gpr .rsi) c) ∧ (pR (s.gpr .rdi)).Disjoint (famR (s.gpr .rdx) c) ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rcx)).Disjoint (famR (s.gpr .rsi) c) ∧
    (pR (s.gpr .rcx)).Disjoint (famR (s.gpr .rdx) c) ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    (∀ j < c, Proof.MlDsa.PositiveReduced s.mem (s.gpr .rsi + BitVec.ofNat 64 (1024 * j))) ∧
    (∀ j < c, Proof.MlDsa.PositiveReduced s.mem (s.gpr .rdx + BitVec.ofNat 64 (1024 * j)))
  post s s' := PolyIs s'.mem (s.gpr .rdi) (Spec.MlDsa.nttInv (Proof.MlDsa.dotNTT
    (fun j => polyAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (1024 * j)))
    (fun j => polyAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (1024 * j))) c))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- A family's polynomial `j`, within it. -/
theorem fam_sub (p : Addr) {c j : Nat} (hj : j < c) : Region.Sub (pR (p + BitVec.ofNat 64 (1024 * j))) (famR p c) :=
  VG.Offset.sub_base p (by rw [show 1024 * c = 1024 * (c - 1) + 1024 by omega]; omega)

/-- The pointers and `rsp` are public. -/
def dotτ : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem dot_agree (c : Nat) (s₁ s₂ : State) (_ : (dotK c).pre s₁) (_ : (dotK c).pre s₂)
    (hp : (dotK c).pub s₁ s₂) : X86_64.Taint.Agree dotτ s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2]

/-- A state satisfying the precondition. -/
def dotSat (c : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x4000 | .rcx => 0x6000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 1024 * c⟩, ⟨0x4000, 1024 * c⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x6000, 1024⟩]

/-- The implication from `dotInverseContract c`, for a literal `c`. -/
tactic_template "dot_implies " w:term : tactic => `(tactic| exact
  { pre := by sig_implies_pre [Proof.MlDsa.dotInverseContract, Proof.MlDsa.dotInverseSig, dotK, X86_64.abi, X86_64.argRegs]
    post := by sig_implies_post [Proof.MlDsa.dotInverseContract, Proof.MlDsa.dotInverseSig, dotK, X86_64.abi, X86_64.argRegs]
    pub := by sig_implies_pub [Proof.MlDsa.dotInverseContract, Proof.MlDsa.dotInverseSig, dotK, X86_64.abi, X86_64.argRegs]
    sat := by
      refine ⟨$w, ?_⟩
      sig_pre [Proof.MlDsa.dotInverseContract, Proof.MlDsa.dotInverseSig, dotK, X86_64.abi, X86_64.argRegs]
      and_intros
      all_goals first
        | rfl
        | decide
        | exact Region.disjoint_of_sep (by decide)
        | (intro _ _ i hi; exact Nat.lt_trans (reduced_zero _ i hi) (by decide)) })

end VG.Proof.MlDsa.X86_64.Arith
