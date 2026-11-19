module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedContract
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.SharedCandidate
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedContract
meta import VerifiedGarbage.Impl.RsaKeyGen.X86_64.SharedCandidate
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import Mathlib.Data.Nat.Basic
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrRound
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrRound
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Basic.IsEmpty.Defs
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
meta import Mathlib.Algebra.GroupWithZero.Nat
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Code
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Code
meta import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KMain
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KMain
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `RsaKeyGen.X86_64.CTCode`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.CTFront`, which this module and modules that import it used -/

section

/-!
# A candidate on x86-64: the stages before Montgomery setup

After `loadC`, every stage keeps `KSt`: `Good`, the arguments' header words,
the candidate in `aN` and the buffers, for public data `FPub` that includes
the schedule (`schedOf`) the leak fixes. Each stage is proven constant time
with a weak postcondition, then `two_post` recovers `KSt` (and the flag the
branch after it tests) from its correctness.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen (Sched schedOf shapeOf)

theorem RelCT.assoc_r {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          exact ⟨by simpa only [List.append_assoc] using ht, hq⟩


/-! ## The public data and the stages -/

/-- What the stages may depend on: the layout, the arguments, `e`'s octets,
`p`'s and `rand`'s lengths, and the schedule. -/
structure FPub where
  B : Addr
  Z : Nat
  w : Nat
  wr : List Region
  op : Addr
  up : Addr
  eP : Addr
  eB : List Byte
  pP : Addr
  pl : Nat
  rP : Addr
  rl : Nat
  sch : Sched

/-- Montgomery setup's public data. -/
abbrev FPub.tp (q : FPub) : TPub := ⟨q.B, q.Z, q.w, q.wr, q.op, q.up, q.rP, q.rl, q.sch.mr⟩

/-- The arguments' header words, and `used`. -/
def avs (q : FPub) : List (Nat × BitVec 64) :=
  [(kOut, q.op), (kLen, BitVec.ofNat 64 (8 * q.w)), (kUsedP, q.up), (kE, q.eP),
    (kElen, BitVec.ofNat 64 q.eB.length), (kP, q.pP), (kPlen, BitVec.ofNat 64 q.pl), (kRand, q.rP),
    (kRandLen, BitVec.ofNat 64 q.rl), (kUsed, BitVec.ofNat 64 (8 * q.w))]

def aS : List Nat := [kOut, kLen, kUsedP, kE, kElen, kP, kPlen, kRand, kRandLen, kUsed]

/-- The header words every stage keeps. -/
def fvs (q : FPub) : List (Nat × BitVec 64) := avs q ++ gvs q.B q.w

def fS : List Nat := aS ++ gS

theorem fvs_fst (q : FPub) : (fvs q).map (·.1) = fS := rfl

theorem avs_le {q : FPub} : ∀ e ∈ avs q, e.1 ≤ 25 := by
  simp only [avs, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The public bounds. -/
structure FDims (q : FPub) : Prop where
  z : slot q.w aTab + 2048 ≤ q.Z
  zx : slot q.w aRm1 + 8 * (q.w + 2) ≤ q.Z
  w4 : 4 ≤ q.w
  w64 : q.w ≤ 64
  rl : q.rl < 2 ^ 64
  rk : 8 * q.w ≤ q.rl
  el1 : 1 ≤ q.eB.length
  el8 : q.eB.length ≤ 8
  pl : q.pl = 0 ∨ q.pl = 8 * q.w

theorem FDims.td {q : FPub} (h : FDims q) : TDims q.tp :=
  ⟨by have := h.z; unfold slot aTab at *; dsimp only; omega_arith, h.zx, h.w4, h.w64⟩

/-- Between the stages: `Good`, the header words, the candidate in `aN`, the
buffers, and the schedule. -/
def KSt (q : FPub) (s : State) : Prop :=
  KW q.B q.wr ∧ s.wr = q.wr ∧ FDims q ∧
    ∃ (mi : BitVec 64) (pB r : List Byte), Good s q.B q.Z q.w mi ∧ (∀ e ∈ avs q, word s.mem q.B (8 * e.1) = e.2) ∧
      wv s.mem q.B (slot q.w aN) q.w = Spec.RsaKeyGen.candidate (64 * q.w) (Spec.Rsa.os2ip (r.take (8 * q.w))) ∧
      Src s q.B q.Z q.pP pB ∧ Src s q.B q.Z q.eP q.eB ∧ Src s q.B q.Z q.rP r ∧ pB.length = q.pl ∧
      r.length = q.rl ∧ schedOf (8 * q.w) (Spec.Rsa.os2ip q.eB) (Spec.RsaKeyGen.otherPrime pB) r = q.sch

theorem KSt.hp {q : FPub} {s : State} (h : KSt q s) : KW q.B q.wr ∧ HP q.B q.wr (fvs q) s := by
  obtain ⟨hk, hw, -, mi, pB, r, hg, ha, -⟩ := h
  refine ⟨hk, hg.rdi, hw, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact ha e he
  · exact (good_hp hg hw).hdr e he

theorem KSt.gw {q : FPub} {s : State} (h : KSt q s) : GW q.tp s :=
  let ⟨hk, hw, hd, mi, _, _, hg, _⟩ := h; ⟨hk, hw, hd.td, mi, hg⟩

/-- `KSt` survives a stage that keeps `Good` and changes only memory past
the arguments, away from `aN`. -/
theorem KSt.step {q : FPub} {s t : State} {rs : List (Nat × Nat)} {regs : List Reg} (h : KSt q s)
    (hg : ∃ mi, Good t q.B q.Z q.w mi) (hf : Frm q.B rs s.mem t.mem) (h208 : ∀ r ∈ rs, 208 ≤ r.1)
    (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ q.Z) (hN : ∀ r ∈ rs, slot q.w aN + 8 * q.w ≤ r.1 ∨ r.1 + r.2 ≤ slot q.w aN)
    (k : Keep regs s t) : KSt q t := by
  obtain ⟨hk, hw, hd, mi, pB, r, hg₀, ha, hc, hp, he, hr, hpl, hrl, hS⟩ := h
  obtain ⟨mi', hg'⟩ := hg
  have hn := hg₀.scr.nowrap
  have sN := slot_le (w := q.w) (show aN < 8 by decide)
  have hz := hd.z
  have hin := InScr.of_frm hf hZ
  refine ⟨hk, k.2.2.trans hw, hd, mi', pB, r, hg', fun e he => ?_, ?_, hp.congrK hin k, he.congrK hin k,
    hr.congrK hin k, hpl, hrl, hS⟩
  · have := avs_le e he
    rw [hf.word_eq (fun r hr => Or.inl (by have := h208 r hr; omega_arith)) (by omega_arith)]; exact ha e he
  · rw [hf.wv_eq hN (by unfold slot aTab at *; omega_arith)]; exact hc

/-- The words of `avs`. -/
structure AvsW (q : FPub) (m : Mem) : Prop where
  out : word m q.B (8 * kOut) = q.op
  len : word m q.B (8 * kLen) = BitVec.ofNat 64 (8 * q.w)
  usedP : word m q.B (8 * kUsedP) = q.up
  e : word m q.B (8 * kE) = q.eP
  elen : word m q.B (8 * kElen) = BitVec.ofNat 64 q.eB.length
  p : word m q.B (8 * kP) = q.pP
  plen : word m q.B (8 * kPlen) = BitVec.ofNat 64 q.pl
  rand : word m q.B (8 * kRand) = q.rP
  rlen : word m q.B (8 * kRandLen) = BitVec.ofNat 64 q.rl
  used : word m q.B (8 * kUsed) = BitVec.ofNat 64 (8 * q.w)

theorem avsW_of {q : FPub} {m : Mem} (ha : ∀ e ∈ avs q, word m q.B (8 * e.1) = e.2) : AvsW q m := by
  simp only [avs, List.forall_mem_cons] at ha
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := ha
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem decide_gcd (g : Nat) : decide (g = 1) = !(!(g == 1)) := by
  cases h : g == 1 <;> simp_all

/-- The facts of a `KSt` the stages use. -/
theorem KSt.cand {q : FPub} {s : State} (h : KSt q s) :
    ∃ (mi : BitVec 64) (pB r : List Byte), Good s q.B q.Z q.w mi ∧ (∀ e ∈ avs q, word s.mem q.B (8 * e.1) = e.2) ∧
      wv s.mem q.B (slot q.w aN) q.w = Spec.RsaKeyGen.candidate (64 * q.w) (Spec.Rsa.os2ip (r.take (8 * q.w))) ∧
      Src s q.B q.Z q.pP pB ∧ Src s q.B q.Z q.eP q.eB ∧ Src s q.B q.Z q.rP r ∧ pB.length = q.pl ∧
      r.length = q.rl ∧ schedOf (8 * q.w) (Spec.Rsa.os2ip q.eB) (Spec.RsaKeyGen.otherPrime pB) r = q.sch :=
  h.2.2.2

theorem cand_shape {w : Nat} (hw : 4 ≤ w) (x : Nat) :
    VG.Proof.RsaKeyGen.PrimeShape (64 * w) (Spec.RsaKeyGen.candidate (64 * w) x) :=
  VG.Proof.RsaKeyGen.candidate_shape (by omega_arith) _

theorem cand_gt {w : Nat} (hw : 4 ≤ w) (x : Nat) : 8161 < Spec.RsaKeyGen.candidate (64 * w) x := by
  obtain ⟨_, hlo, _⟩ := cand_shape hw x
  have : 2 ^ 13 ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  omega_arith

/-- `closeCheck`, from `KSt`: ZF clear iff the candidate is too close. -/
theorem closeStage_ok {q : FPub} {s : State} (h : KSt q s) :
    WP isa (seqs closeCheck) s fun t => KSt q t ∧ t.zf = some (!q.sch.close) := by
  obtain ⟨mi, pB, r, hg, ha, hc, hp, -, -, hpl, -, hS⟩ := h.cand
  have hd := h.2.2.1
  have hz := hd.z
  have hw4 := hd.w4
  have hZ : slot q.w 8 ≤ q.Z := by unfold slot aTab at *; omega_arith
  have hsch : q.sch.close = Spec.RsaKeyGen.tooClose (64 * q.w) (Spec.RsaKeyGen.otherPrime pB)
      (Spec.RsaKeyGen.candidate (64 * q.w) (Spec.Rsa.os2ip (r.take (8 * q.w)))) := by
    rw [← hS, sched_close, show 8 * (8 * q.w) = 64 * q.w by omega_arith]
  have ha' := avsW_of ha
  refine WP.mono (closeCheck_ok hg hZ hw4 hd.w64 ha'.p ha'.len (by rw [hpl]; exact ha'.plen)
    (by rw [hpl]; exact hd.pl) hp) fun t ⟨hzf, hgt, hf, k⟩ => ⟨?_, ?_⟩
  · refine h.step ⟨mi, hgt⟩ hf (closeRanges_fr q.w).1 (fun r hr => ?_) (closeRanges_fr q.w).2.2.1 k
    have : r.1 + r.2 ≤ slot q.w aTab + 2048 := (closeRanges_fr q.w).2.2.2 r hr
    omega_arith
  · rw [hzf, hc, hsch]

/-- `trial`, from `KSt` and a candidate not too close: ZF clear iff it is
obviously composite. -/
theorem trialStage_ok {q : FPub} {s : State} (h : KSt q s) (hcl : q.sch.close = false) :
    WP isa (seqs trial) s fun t => KSt q t ∧ t.zf = some (!q.sch.comp) := by
  obtain ⟨mi, pB, r, hg, -, hc, -, -, -, -, -, hS⟩ := h.cand
  have hd := h.2.2.1
  have hz := hd.z
  have hw4 := hd.w4
  have hZ : slot q.w 8 ≤ q.Z := by unfold slot aTab at *; omega_arith
  have hcl' := hcl
  rw [← hS, sched_close] at hcl'
  have hsch : q.sch.comp = Spec.RsaKeyGen.obviouslyComposite (64 * q.w)
      (Spec.RsaKeyGen.candidate (64 * q.w) (Spec.Rsa.os2ip (r.take (8 * q.w)))) := by
    rw [← hS, sched_comp hcl', show 8 * (8 * q.w) = 64 * q.w by omega_arith]
  refine WP.mono (trial_ok hg hZ hz (by omega_arith) hd.w64) fun t ⟨hzf, hgt, hf, k⟩ => ⟨?_, ?_⟩
  · refine h.step ⟨mi, hgt⟩ hf (trialRanges_fr q.w).1 (fun r hr => ?_) (trialRanges_fr q.w).2.2 k
    have : r.1 + r.2 ≤ slot q.w aTab + 2048 := (trialRanges_fr q.w).2.1 r hr
    omega_arith
  · rw [hzf, hc, trialAny_eq (cand_gt hw4 _), hsch]

/-- `gcdCheck`, from `KSt` and a candidate neither too close nor obviously
composite: ZF set iff `gcd(c − 1, e) = 1`. -/
theorem gcdStage_ok {q : FPub} {s : State} (h : KSt q s) (hcl : q.sch.close = false) (hco : q.sch.comp = false) :
    WP isa (seqs gcdCheck) s fun t => KSt q t ∧ t.zf = some (!q.sch.gbad) := by
  obtain ⟨mi, pB, r, hg, ha, hc, -, he, -, -, -, hS⟩ := h.cand
  have hd := h.2.2.1
  have hz := hd.z
  have hw4 := hd.w4
  have hZ : slot q.w 8 ≤ q.Z := by unfold slot aTab at *; omega_arith
  have hcl' := hcl
  rw [← hS, sched_close] at hcl'
  have hco' := hco
  rw [← hS, sched_comp hcl'] at hco'
  have hsch : q.sch.gbad = !(Nat.gcd (Spec.RsaKeyGen.candidate (64 * q.w) (Spec.Rsa.os2ip (r.take (8 * q.w))) - 1)
      (Spec.Rsa.os2ip q.eB) == 1) := by
    rw [← hS, sched_gbad hcl' hco', show 8 * (8 * q.w) = 64 * q.w by omega_arith]
  obtain ⟨hodd, -, -⟩ := cand_shape hw4 (Spec.Rsa.os2ip (r.take (8 * q.w)))
  have h3 := cand_gt hw4 (Spec.Rsa.os2ip (r.take (8 * q.w)))
  have ha' := avsW_of ha
  have := hd.w64
  refine WP.mono (gcdCheck_ok hg hZ (by omega_arith) (by omega_arith) (by rw [hc]; exact hodd) (by rw [hc]; omega_arith)
    ha'.e ha'.elen hd.el1 hd.el8 he) fun t ⟨hzf, hgt, hf, k⟩ => ⟨?_, ?_⟩
  · refine h.step ⟨mi, hgt⟩ hf (gcdRanges_fr q.w).1 (fun r hr => ?_) (gcdRanges_fr q.w).2.2.1 k
    have : r.1 + r.2 ≤ slot q.w aTab + 2048 := (gcdRanges_fr q.w).2.2.2 r hr
    omega_arith
  · rw [hzf, hc, hsch, decide_gcd]

/-- Montgomery setup's precondition, from `KSt` and a candidate that passed
the first checks. -/
theorem tailPre {q : FPub} {s : State} (h : KSt q s) (hcl : q.sch.close = false) (hco : q.sch.comp = false)
    (hgb : q.sch.gbad = false) : MsPre q.tp s := by
  obtain ⟨mi, pB, r, hg, ha, hc, -, -, hr, -, hrl, hS⟩ := h.cand
  have hd := h.2.2.1
  have hw4 := hd.w4
  have hcl' := hcl
  rw [← hS, sched_close] at hcl'
  have hco' := hco
  rw [← hS, sched_comp hcl'] at hco'
  have hgb' := hgb
  rw [← hS, sched_gbad hcl' hco'] at hgb'
  have hsh := cand_shape hw4 (Spec.Rsa.os2ip (r.take (8 * q.w)))
  have hres : mrRest (Spec.RsaKeyGen.candidate (64 * q.w) (Spec.Rsa.os2ip (r.take (8 * q.w))))
      (Proof.RsaKeyGen.checksW q.w) r 1 0 (8 * q.w) = Spec.RsaKeyGen.primalityTest
        (Spec.RsaKeyGen.candidate (64 * q.w) (Spec.Rsa.os2ip (r.take (8 * q.w)))) (r.drop (8 * q.w)) := by
    rw [VG.Proof.RsaKeyGen.primalityTest_cand (by omega_arith) hsh, checksW_eq q.w (by have := hd.w64; omega_arith) hw4]
  have ha' := avsW_of ha
  refine ⟨h.gw, hd.rl, mi, _, r, hg, hc, hsh, ha'.out, ha'.usedP, ha'.rand, ha'.len, by rw [hrl]; exact ha'.rlen,
    ha'.used, hr, hrl,
    by rw [hrl]; exact hd.rk, ?_⟩
  rw [hres]
  have := sched_mr hcl' hco' hgb'
  rw [hS, show 8 * (8 * q.w) = 64 * q.w by omega_arith] at this
  exact this.symm

/-! ## `closeCheck` -/

theorem RelCT.seqs_app_seq {P Q : State → State → Prop} {a b : List (Prog isa)} {k : Prog isa} (ha : a ≠ [])
    (hb : b ≠ []) (h : RelCT isa P (.seq (seqs a) (.seq (seqs b) k)) Q) : RelCT isa P (.seq (seqs (a ++ b)) k) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq x₁ k₁ =>
    cases e₂ with
    | seq x₂ k₂ =>
      cases exec_seqs_app ha hb x₁ with
      | seq a₁ b₁ =>
        cases exec_seqs_app ha hb x₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ k₁)) (.seq a₂ (.seq b₂ k₂))
          exact ⟨by simpa only [List.append_assoc] using ht, hq⟩

theorem KSt.congr {q : FPub} {s t : State} {regs : List Reg} (h : KSt q s) (hm : t.mem = s.mem) (k : Keep regs s t)
    (hdi : t.gpr .rdi = s.gpr .rdi) : KSt q t := by
  obtain ⟨-, -, -, mi, -, -, hg, -⟩ := id h
  exact h.step (rs := []) ⟨mi, hg.scr.congr k.2.2, hdi.trans hg.rdi, by rw [hm]; exact hg.hdr⟩
    (fun x _ => by rw [hm]) (by simp) (by simp) (by simp) k

theorem GW.of_good {q : TPub} {s t : State} {mi : BitVec 64} (h : GW q s) (hg : Good t q.B q.Z q.w mi)
    (hw : t.wr = s.wr) : GW q t :=
  let ⟨hk, hw', hd, _⟩ := h; ⟨hk, hw.trans hw', hd, mi, hg⟩

/-- `p` into `aX`. -/
theorem closeLoad_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 4 ≤ w) (hw' : w ≤ 64) {pP : Addr} {pB : List Byte} (hP : word s.mem B (8 * kP) = pP)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) (hpl : pB.length = 8 * w) (hsrc : Src s B Z pP pB) :
    WP isa (seqs [.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr kP)), .mov .rcx (.mem (hdr kLen)),
        .mov .rbx (.mem (hdr (sArr aX)))], loadBE]) s fun t => Good t B Z w minv ∧ t.wr = s.wr := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hw8 : (8 * w + 7) / 8 = w := by omega_arith
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rcx, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = pP ∧ t.gpr .rcx = BitVec.ofNat 64 (8 * w) ∧ t.gpr .rbx = off B (slot w aX) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl kP (by decide), hl kLen (by decide),
      hl (sArr aX) (by decide), hg.hdr.hw, hP, hK, hg.hdr.harr aX (by decide)]) rfl)
    fun s₁ ⟨⟨_, hsi₁, hcx₁, hbx₁, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (loadArr_ok (j := aX) hs₁ (by decide) (by rw [hw8]; exact hZ)
    (hsrc.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hpl (by omega_arith) (by omega_arith) hsi₁ hcx₁
    (by rw [hw8]; exact hbx₁)) fun s₂ ⟨_, ha₂, k₂⟩ => ?_
  rw [hw8] at ha₂
  exact ⟨⟨hs₁.congr k₂.2.2, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi),
    ha₂.hdr (by rw [hm₁]; exact hg.hdr)⟩, k₂.2.2.trans k₁.2.2⟩

/-- `closeCheck` leaks the same in runs that agree on the public data. -/
theorem closeCheck_ct : RelCT isa (Two KSt) (seqs closeCheck) fun _ _ => True := by
  unfold closeCheck
  simp only [seqs]
  refine RelCT.seq (R := Two fun q s => KSt q s ∧ s.zf = some (BitVec.ofNat 64 q.pl == 0))
    (kt_piece (fun q : FPub => q.B) (fun q => q.wr) fS fvs [] (by decide) fvs_fst (fun _ _ h => h.hp) (pins_nil _)
      (by taint_decide) ?_)
    (two_ite_seq (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_
      (kt_ct (fun q : FPub => q.B) (fun q => q.wr) fS fvs [] (by decide) fvs_fst (fun _ _ h => h.1.1.hp) (pins_nil _)
        (by taint_decide)))
  · rintro q s h
    obtain ⟨mi, -, -, hg, ha, -⟩ := h.cand
    have hd := h.2.2.1
    have hn := hg.scr.nowrap
    have hl : InRegions (s.rd ++ s.wr) (off q.B (8 * kPlen)) 8 :=
      hg.scr.ld (by have := hdr_lt_slot q.w 8 (show kPlen < 32 by decide); have := hd.z; unfold slot aTab at *; omega_arith)
    refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.zf = some (BitVec.ofNat 64 q.pl == 0) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl, (avsW_of ha).plen, BitVec.and_self]) rfl)
      fun t ⟨⟨hz, hm⟩, k⟩ => ⟨h.congr hm k (k.gpr (by decide)), hz⟩
  · -- With `p`: `p` into `aX`, `c − p`, `|c − p|`, then the comparison.
    refine RelCT.seqs_app_seq (by simp) (by simp) ?_
    refine RelCT.seq (R := Two fun (q : FPub) s => GW q.tp s) ?_ (kt_ct (fun q : FPub => q.B) (fun q => q.wr) gS
      (fun q => gvs q.B q.w) [] (by decide) (fun _ => gvs_fst _ _) (fun _ _ h => h.hp) (pins_nil _) (by taint_decide))
    refine RelCT.seqs_app (by simp) (by simp [negLoop]) (RelCT.seq (R := Two fun (q : FPub) s => GW q.tp s ∧
      s.gpr .r12 = BitVec.ofNat 64 q.w ∧ ∃ b, s.gpr .rbp = mask b) ?_ ?_)
    · refine RelCT.seqs_app (by simp) (by simp [diffLoop]) (RelCT.seq (R := Two fun (q : FPub) s => GW q.tp s) ?_ ?_)
      · refine kt_piece (fun q : FPub => q.B) (fun q => q.wr) fS fvs [] (by decide) fvs_fst (fun _ _ h => h.1.1.hp)
          (pins_nil _) (by taint_decide) ?_
        rintro q s ⟨⟨h, hz⟩, he⟩
        obtain ⟨mi, pB, -, hg, ha, -, hp, -, -, hpl, -⟩ := h.cand
        have hd := h.2.2.1
        have hpl8 : q.pl = 8 * q.w := hd.pl.resolve_left fun h0 => by
          rw [h0] at hz; simp [eval, hz] at he
        exact WP.mono (closeLoad_ok hg (by have := hd.z; unfold slot aTab at *; omega_arith) hd.w4 hd.w64 (avsW_of ha).p
          (avsW_of ha).len (hpl.trans hpl8) hp) fun t ⟨hgt, hw⟩ => h.gw.of_good hgt hw
      · refine kt_piece (fun q : FPub => q.B) (fun q => q.wr) gS (fun q => gvs q.B q.w) [] (by decide)
          (fun _ => gvs_fst _ _) (fun _ _ h => h.hp) (pins_nil _) (by taint_decide) ?_
        rintro q s h
        obtain ⟨-, -, hd, mi, hg⟩ := id h
        exact WP.mono (diff_ok hg hd.z (by have := hd.w4; omega_arith) (by have := hd.w64; omega_arith))
          fun t ⟨b, hb, _, ho, h12, k⟩ => ⟨h.of_good ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
            Hdr.outside hg.hdr ho (by unfold slot; omega_arith)⟩ k.2.2, h12, b, hb⟩
    · refine kt_piece (fun q : FPub => q.B) (fun q => q.wr) gS (fun q => gvs q.B q.w) [.r12] (by decide)
        (fun _ => gvs_fst _ _) (fun _ _ h => h.1.hp)
        (fun _ _ _ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1])
        (by taint_decide) ?_
      rintro q s ⟨h, h12, b, hb⟩
      obtain ⟨-, -, hd, mi, hg⟩ := id h
      exact WP.mono (neg_ok hg hd.z (by have := hd.w4; omega_arith) (by have := hd.w64; omega_arith) hb h12)
        fun t ⟨_, ho, k⟩ => h.of_good ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
          Hdr.outside hg.hdr ho (by unfold slot; omega_arith)⟩ k.2.2

/-! ## `gcdCheck` -/

/-- `e` into `rbx` and `kG`, ZF from its low bit. -/
theorem gcdFront_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) {eP : Addr} {eB : List Byte} (hE : word s.mem B (8 * kE) = eP)
    (hEl : word s.mem B (8 * kElen) = BitVec.ofNat 64 eB.length) (hl1 : 1 ≤ eB.length) (hl8 : eB.length ≤ 8)
    (hsrc : Src s B Z eP eB) :
    WP isa (.seq (seqs loadE) (.block [.store (hdr kG) .rbx, .mov .rax (.reg .rbx), .alu .and .rax (.imm 1)])) s
      fun t => Good t B Z w minv ∧ t.wr = s.wr ∧ t.zf = some (decide (Spec.Rsa.os2ip eB % 2 = 0)) ∧
        (t.gpr .rbx).toNat = Spec.Rsa.os2ip eB := by
  have hn := hg.scr.nowrap
  refine WP.seq (WP.mono (loadE_ok hg hZ hE hEl hl1 hl8 hsrc) fun s₁ ⟨hbx₁, hm₁, k₁⟩ => ?_)
  have hg₁ : Good s₁ B Z w minv := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off B (8 * kG)) (s₁.gpr .rbx) ∧
      t.zf = some (decide (Spec.Rsa.os2ip eB % 2 = 0)) ∧ t.gpr .rbx = s₁.gpr .rbx) (by
    have hst : InRegions s₁.wr (off B (8 * kG)) 8 := by
      rw [k₁.2.2]; exact hg.scr.st (by have := hdr_lt_slot w 8 (show kG < 32 by decide); omega_arith)
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hst, sx1]
    rw [← hbx₁]
    refine Bool.eq_iff_iff.mpr ?_
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, and1_toNat]; rfl) rfl) fun t ⟨⟨hm, hz, hbx⟩, k⟩ => ⟨⟨hg₁.scr.congr k.2.2,
      (k.gpr (by decide)).trans hg₁.rdi, by rw [hm]; exact hg₁.hdr.store (by decide) (by decide) _⟩,
      k.2.2.trans k₁.2.2, hz, by rw [hbx, hbx₁]⟩

theorem os2ip_lt64 {eB : List Byte} (h : eB.length ≤ 8) : Spec.Rsa.os2ip eB < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (os2ip_lt eB) (by
    calc 256 ^ eB.length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) h
      _ = 2 ^ 64 := by decide)

/-- After `e`'s low bit: `Good`, and `e` in `rbx`. -/
def GPub (q : FPub) (s : State) : Prop :=
  GW q.tp s ∧ (s.gpr .rbx).toNat = Spec.Rsa.os2ip q.eB ∧ q.eB.length ≤ 8

/-- `gcdCheck` leaks the same in runs that agree on the public data. -/
theorem gcdCheck_ct {Φ : FPub → State → Prop} (hΦ : ∀ q s, Φ q s → KSt q s) :
    RelCT isa (Two Φ) (seqs gcdCheck) fun _ _ => True := by
  unfold gcdCheck loadE
  simp only [seqs, List.cons_append, List.nil_append]
  refine RelCT.assoc (RelCT.assoc (RelCT.seq (R := Two fun q s => GPub q s ∧
      s.zf = some (decide (Spec.Rsa.os2ip q.eB % 2 = 0))) ?_ ?_))
  · refine kt_piece (fun q : FPub => q.B) (fun q => q.wr) fS fvs [] (by decide) fvs_fst (fun _ _ h => (hΦ _ _ h).hp)
      (pins_nil _) (by taint_decide) ?_
    intro q s h
    have h := hΦ q s h
    obtain ⟨mi, -, -, hg, ha, -, -, he, -⟩ := h.cand
    have hd := h.2.2.1
    exact WP.mono (gcdFront_ok hg (by have := hd.z; unfold slot aTab at *; omega_arith) (avsW_of ha).e (avsW_of ha).elen
      hd.el1 hd.el8 he) fun t ⟨hgt, hw, hz, hbx⟩ => ⟨⟨h.gw.of_good hgt hw, hbx, hd.el8⟩, hz⟩
  refine two_ite_seq (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · exact kt_ct (fun q : FPub => q.B) (fun q => q.wr) gS (fun q => gvs q.B q.w) [] (by decide) (fun _ => gvs_fst _ _)
      (fun _ _ h => h.1.1.1.hp) (pins_nil _) (by taint_decide)
  refine RelCT.assoc_r ?_
  refine RelCT.seq (R := Two fun q s => GPub q s ∧ s.zf = some (decide (Spec.Rsa.os2ip q.eB = 1))) ?_ ?_
  · refine kt_piece (fun q : FPub => q.B) (fun q => q.wr) gS (fun q => gvs q.B q.w) [] (by decide)
      (fun _ => gvs_fst _ _) (fun _ _ h => h.1.1.1.hp) (pins_nil _) (by taint_decide) ?_
    rintro q s ⟨⟨⟨hgw, hbx, hl8⟩, -⟩, -⟩
    have hE := os2ip_lt64 hl8
    have hE64 : s.gpr .rbx = BitVec.ofNat 64 (Spec.Rsa.os2ip q.eB) := by
      rw [← hbx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine WP.mono (WP.keep [.rbx] (Q := fun t => t.zf = some (decide (Spec.Rsa.os2ip q.eB = 1)) ∧ t.mem = s.mem ∧
        t.gpr .rbx = s.gpr .rbx) (by
      xrun [sx1, hE64]
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub_beq hE (by decide)]) rfl)
      fun t ⟨⟨hz, hm, hb⟩, k⟩ => ⟨⟨?_, by rw [hb]; exact hbx, hl8⟩, hz⟩
    obtain ⟨hk, hw, hd, mi, hg⟩ := hgw
    exact ⟨hk, k.2.2.trans hw, hd, mi, hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  refine two_ite_seq (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · exact kt_ct (fun q : FPub => q.B) (fun q => q.wr) gS (fun q => gvs q.B q.w) [] (by decide) (fun _ => gvs_fst _ _)
      (fun _ _ h => h.1.1.1.hp) (pins_nil _) (by taint_decide)
  · exact kt_ct (fun q : FPub => q.B) (fun q => q.wr) gS (fun q => gvs q.B q.w) [] (by decide) (fun _ => gvs_fst _ _)
      (fun _ _ h => h.1.1.1.hp) (pins_nil _) (by taint_decide)

/-! ## After `loadC` -/

theorem ne_false {s : State} {b : Bool} (hz : s.zf = some (!b)) (he : isa.eval .ne s = some false) : b = false := by
  cases b <;> simp_all [eval]

theorem trial_ct {Φ : FPub → State → Prop} (hΦ : ∀ q s, Φ q s → KSt q s) :
    RelCT isa (Two Φ) (seqs trial) fun _ _ => True :=
  kt_ct (fun q : FPub => q.B) (fun q => q.wr) fS fvs [] (by decide) fvs_fst (fun _ _ h => (hΦ _ _ h).hp) (pins_nil _)
    (by taint_decide)

theorem finUsed2_ct {Φ : FPub → State → Prop} (hΦ : ∀ q s, Φ q s → KSt q s) :
    RelCT isa (Two Φ) (finUsed 2) fun _ _ => True :=
  kt_ct (fun q : FPub => q.B) (fun q => q.wr) fS fvs [] (by decide) fvs_fst (fun _ _ h => (hΦ _ _ h).hp) (pins_nil _)
    (by taint_decide)

theorem finUsed3_ct {Φ : FPub → State → Prop} (hΦ : ∀ q s, Φ q s → KSt q s) :
    RelCT isa (Two Φ) (finUsed 3) fun _ _ => True :=
  kt_ct (fun q : FPub => q.B) (fun q => q.wr) fS fvs [] (by decide) fvs_fst (fun _ _ h => (hΦ _ _ h).hp) (pins_nil _)
    (by taint_decide)

/-! ## `loadC` -/

/-- The arguments' header words. -/
def avs0 (q : FPub) : List (Nat × BitVec 64) :=
  [(kOut, q.op), (kLen, BitVec.ofNat 64 (8 * q.w)), (kUsedP, q.up), (kE, q.eP),
    (kElen, BitVec.ofNat 64 q.eB.length), (kP, q.pP), (kPlen, BitVec.ofNat 64 q.pl), (kRand, q.rP),
    (kRandLen, BitVec.ofNat 64 q.rl)]

def aS0 : List Nat := [kOut, kLen, kUsedP, kE, kElen, kP, kPlen, kRand, kRandLen]

/-- Before `loadC`: what `kMainWith` needs, for the public data. -/
def K0 (q : FPub) (s : State) : Prop :=
  KW q.B q.wr ∧ s.wr = q.wr ∧ FDims q ∧ ∃ pB r : List Byte,
    MainCtx s q.B q.Z (8 * q.w) q.op q.up q.eP q.pP q.rP q.eB pB r ∧ pB.length = q.pl ∧ r.length = q.rl ∧
      schedOf (8 * q.w) (Spec.Rsa.os2ip q.eB) (Spec.RsaKeyGen.otherPrime pB) r = q.sch

theorem K0.hp {q : FPub} {s : State} (h : K0 q s) : KW q.B q.wr ∧ HP q.B q.wr (avs0 q) s := by
  obtain ⟨hk, hw, -, pB, r, hm, hpl, hrl, -⟩ := h
  refine ⟨hk, hm.rdi, hw, fun e he => ?_⟩
  simp only [avs0, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hm.out
  · exact hm.len
  · exact hm.usedP
  · exact hm.e
  · exact hm.elen
  · exact hm.p
  · rw [← hpl]; exact hm.plen
  · exact hm.rand
  · rw [← hrl]; exact hm.rlen

theorem K0.src {q : FPub} {s : State} {pB r : List Byte}
    (h : MainCtx s q.B q.Z (8 * q.w) q.op q.up q.eP q.pP q.rP q.eB pB r) :
    Src s q.B q.Z q.rP (r.take (8 * q.w)) := by
  have := VG.Proof.RsaKeyGen.X86_64.Src.seg h.rsrc (a := 0) (n := 8 * q.w) (by have := h.rk; omega_arith)
  rwa [seg_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this

/-- `loadC`, from `K0`. -/
theorem loadCStage_ok {q : FPub} {s : State} (h : K0 q s) : WP isa (seqs loadC) s (KSt q) := by
  obtain ⟨hk, hw, hd, pB, r, hm, hpl, hrl, hS⟩ := id h
  have hn := hm.scr.nowrap
  have hz := hd.z
  have hw4 := hd.w4
  have hw64 := hd.w64
  have hw8 : 8 * q.w / 8 = q.w := by omega_arith
  refine WP.mono (loadC_ok hm.scr hm.rdi (by rw [hw8]; unfold slot aTab at *; omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    hm.len hm.rand (K0.src hm) (by simp; have := hm.rk; omega_arith)) fun t ⟨hc, hU, hW, hA, hf, hdi, _, k⟩ => ?_
  rw [hw8] at hc hW hA hf
  rw [show 8 * (8 * q.w) = 64 * q.w by omega_arith] at hc
  have hsl : ∀ r ∈ loadCRanges q.w, r.1 + r.2 ≤ q.Z := fun r hr => by
    have : r.1 + r.2 ≤ slot q.w aTab + 2048 := by revert r hr; simp only [loadCRanges]; rng_le
    omega_arith
  have hin := InScr.of_frm hf hsl
  have hh : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word t.mem q.B (8 * i) = word s.mem q.B (8 * i) := fun {i} hi => by
    have hi32 : i < 32 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine hf.word_eq ?_ (by omega_arith)
    exact loadCRanges_hdr q.w i (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hi)
  refine ⟨hk, k.2.2.trans hw, hd, word t.mem q.B (8 * sMinv), pB, r, ⟨hm.scr.congr k.2.2, hdi, ⟨hW, rfl, hA⟩⟩,
    fun e he => ?_, hc, hm.psrc.congrK hin k, hm.esrc.congrK hin k, hm.rsrc.congrK hin k, hpl, hrl, hS⟩
  simp only [avs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hh (by simp)]; exact hm.out
  · rw [hh (by simp)]; exact hm.len
  · rw [hh (by simp)]; exact hm.usedP
  · rw [hh (by simp)]; exact hm.e
  · rw [hh (by simp)]; exact hm.elen
  · rw [hh (by simp)]; exact hm.p
  · rw [hh (by simp), ← hpl]; exact hm.plen
  · rw [hh (by simp)]; exact hm.rand
  · rw [hh (by simp), ← hrl]; exact hm.rlen
  · exact hU

/-- After `loadC`'s octets: the header words its last block reads. -/
def lvs (q : FPub) : List (Nat × BitVec 64) :=
  [(sW, BitVec.ofNat 64 q.w), (sArr aN, off q.B (slot q.w aN)), (kLen, BitVec.ofNat 64 (8 * q.w))]

/-- `loadC` leaks the same in runs that agree on the public data. -/
theorem loadC_ct : RelCT isa (Two K0) (seqs loadC) fun _ _ => True := by
  unfold loadC
  simp only [seqs]
  refine RelCT.assoc (RelCT.seq (R := Two fun q s => KW q.B q.wr ∧ HP q.B q.wr (lvs q) s)
    (kt_piece (fun q : FPub => q.B) (fun q => q.wr) aS0 avs0 [] (by decide) (fun _ => rfl) (fun _ _ h => h.hp)
      (pins_nil _) (by taint_decide) ?_)
    (kt_ct (fun q : FPub => q.B) (fun q => q.wr) [sW, sArr aN, kLen] lvs [] (by decide) (fun _ => rfl)
      (fun _ _ h => h) (pins_nil _) (by taint_decide)))
  rintro q s h
  obtain ⟨hk, hw, hd, pB, r, hm, -, -, -⟩ := h
  have hz := hd.z
  have hw4 := hd.w4
  have hw64 := hd.w64
  have hw8 : 8 * q.w / 8 = q.w := by omega_arith
  refine WP.mono (loadCFront_ok hm.scr hm.rdi (by rw [hw8]; unfold slot aTab at *; omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) hm.len hm.rand (K0.src hm) (by simp; have := hm.rk; omega_arith)) fun t ⟨_, _, hdi, hW, hA, hhd, _, k⟩ => ?_
  rw [hw8] at hW hA
  refine ⟨hk, hdi, k.2.2.trans hw, fun e he => ?_⟩
  simp only [lvs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact hW
  · exact hA aN (by decide)
  · rw [hhd kLen (by decide) (by decide)]; exact hm.len

end VG.Proof.RsaKeyGen.X86_64

end

end

/-!
# A candidate on x86-64: constant time

For runs that agree on the arguments, `e` and `candidateLeak`: the entry,
the zeros to `out` and the length check depend on the arguments alone, and
`kMainWith` on the schedule the leak fixes (`schedOf_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen (Sched schedOf shapeOf)

/-- The public data of `vg_rsa_keygen_candidate`: the stages' and the stack
pointer. -/
structure CPub where
  f : FPub
  rsp : Addr

/-- A state the contract allows, with the public data `p`. -/
structure CRel (p : CPub) (s : State) : Prop where
  pre : candPre s
  rsp : s.gpr .rsp = p.rsp
  B : arg s 3 = p.f.B
  Z : (arg s 4).toNat * 8 = p.f.Z
  w : (s.gpr .rsi).toNat = 8 * p.f.w
  op : s.gpr .rdi = p.f.op
  up : s.gpr .rdx = p.f.up
  eP : s.gpr .rcx = p.f.eP
  eB : Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat = p.f.eB
  pP : s.gpr .r9 = p.f.pP
  pl : (arg s 0).toNat = p.f.pl
  rP : arg s 1 = p.f.rP
  rl : (arg s 2).toNat = p.f.rl
  wr : s.wr = p.f.wr
  sch : 8 * p.f.w ≤ p.f.rl → schedOf (8 * p.f.w) (Spec.Rsa.os2ip p.f.eB)
    (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (arg s 0).toNat))
    (Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat) = p.f.sch

theorem candPre_wr {s : State} (h : candPre s) :
    s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, 8⟩, ⟨arg s 3, (arg s 4).toNat * 8⟩] := h.2.2.1

/-- The writable regions the precondition gives. -/
theorem kw_of {s : State} (h : candPre s) : KW (arg s 3) s.wr := by
  have c := kctx_of h
  have hZ := c.hZ
  have hk1 := c.k1
  simp only [candPre] at h
  obtain ⟨-, -, hwr, dOu, -, -, -, dOs, -, -, -, -, dUs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, wS, -⟩ := h
  refine ⟨_, _, _, hwr, Nat.le_refl _, by omega_using [hZ, hk1], ?_, ?_⟩
  · rw [hwr]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil))
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl); exacts [dOu, dOs]
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; exact dUs
  · rw [hwr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl)
    · exact Nat.le_of_lt (s.gpr .rsi).isLt
    · dsimp only; decide
    · dsimp only; omega_using [wS]

/-- After the zeros to `out` and the length check. -/
def C3 (p : CPub) (t : State) : Prop := ∃ s t₁, CRel p s ∧ EntryPost s t₁ (arg s 3) ∧ Front s t₁ t

theorem WP.and' {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun t => Q₁ t ∧ Q₂ t := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

theorem kEntry_split : kEntry = ([.mov .r11 (.mem { base := .rsp, disp := 32 })] : List Instr) ++ kEntry.drop 1 := rfl

/-- What `kMainWith` needs, from a state past the length check with enough
octets. -/
theorem C3.k0 {p : CPub} {t : State} (h : C3 p t) (hlt : ¬ p.f.rl < 8 * p.f.w) : K0 p.f t := by
  obtain ⟨s, t₁, hs, he, hf⟩ := h
  have c := kctx_of hs.pre
  have hk1 := c.k1
  have hk2 := c.k2
  have hle : (s.gpr .rsi).toNat ≤ (arg s 2).toNat := by rw [hs.w, hs.rl]; omega_using [hlt]
  have hm := mainCtx_of c he hf hs.w hle
  have hw := hs.w
  have hsch := hs.sch (by omega_using [hlt])
  rw [hs.eB, hs.B, hs.Z, hs.op, hs.up, hs.eP, hs.pP, hs.rP] at hm
  rw [hs.pP, hs.rP] at hsch
  refine ⟨by rw [← hs.B, ← hs.wr]; exact kw_of hs.pre, (hf.keep.2.2.trans he.keep.2.2).trans hs.wr,
    ⟨by have := hm.z; rwa [show 8 * p.f.w / 8 = p.f.w by omega_using []] at this,
      by have := hm.zx; rwa [show 8 * p.f.w / 8 = p.f.w by omega_using []] at this, by omega_using [hk1, hw], by omega_using [hk2, hw],
      by rw [← hs.rl]; exact (arg s 2).isLt, by omega_using [hlt], ?_, ?_, ?_⟩, _, _, hm, by rw [bytesAt_length, hs.pl],
    by rw [bytesAt_length, hs.rl], hsch⟩
  · rw [← hs.eB, bytesAt_length]; exact c.el1
  · rw [← hs.eB, bytesAt_length]; exact c.el8
  · rw [← hs.pl, ← hs.w]; exact c.pl

/-- The public data of a state. -/
def cpubOf (s : State) : CPub :=
  ⟨⟨arg s 3, (arg s 4).toNat * 8, (s.gpr .rsi).toNat / 8, s.wr, s.gpr .rdi, s.gpr .rdx, s.gpr .rcx,
    Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat, s.gpr .r9, (arg s 0).toNat, arg s 1, (arg s 2).toNat,
    schedOf (8 * ((s.gpr .rsi).toNat / 8)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat))
      (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (arg s 0).toNat))
      (Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat)⟩, s.gpr .rsp⟩

theorem crel_self {s : State} (h : candPre s) : CRel (cpubOf s) s := by
  have := (kctx_of h).k8
  exact ⟨h, rfl, rfl, rfl, by dsimp only [cpubOf]; omega_using [this], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- Runs that agree on the arguments and the leak agree on the public data. -/
theorem crel_of {s₁ s₂ : State} (h₁ : candPre s₁) (h₂ : candPre s₂) (hp : candPub s₁ s₂) : CRel (cpubOf s₁) s₂ := by
  obtain ⟨hdi, hsi, hdx, hcx, hr8, hr9, hsp, ha, hl⟩ := hp
  have c := kctx_of h₁
  have hk8 := c.k8
  have hk1 := c.k1
  unfold candLeak at hl
  obtain ⟨he, hl'⟩ := List.append_inj hl (by simp only [List.length_map, bytesAt_length, hr8])
  have heB := VG.Proof.RsaKeyGen.map_toNat_inj he
  refine ⟨h₂, hsp.symm, (ha 3 (by decide)).symm, by rw [← ha 4 (by decide)]; rfl, by dsimp only [cpubOf]; rw [← hsi]; omega_using [hk8],
    hdi.symm, hdx.symm, hcx.symm, heB.symm, hr9.symm, by rw [← ha 0 (by decide)]; rfl, (ha 1 (by decide)).symm,
    by rw [← ha 2 (by decide)]; rfl, ?_, fun hk => ?_⟩
  · rw [candPre_wr h₂, ← hdi, ← hsi, ← hdx, ← ha 3 (by decide), ← ha 4 (by decide), ← candPre_wr h₁]; rfl
  · dsimp only [cpubOf] at hk ⊢
    rw [VG.Proof.RsaKeyGen.candidateLeak_eq, VG.Proof.RsaKeyGen.candidateLeak_eq] at hl'
    unfold Spec.RsaKeyGen.candidateOp at hl'
    rw [← heB, ← hsi] at hl'
    rw [show 8 * ((s₁.gpr .rsi).toNat / 8) = (s₁.gpr .rsi).toNat by omega_using [hk8]] at hk ⊢
    refine (VG.Proof.RsaKeyGen.schedOf_eq (by omega_using [hk1]) (by rw [bytesAt_length, bytesAt_length, ha 2 (by decide)])
      (by rw [bytesAt_length]; omega_using [hk]) hl').symm

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! ### `RsaKeyGen.X86_64.SharedCTFront`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.SharedCTMain`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.SharedCTRound`, which only this module used -/

section

/-! # Constant time of RSA's witness policy with the callable shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

private theorem hp_shared_used {p : MrPub} {i u u' : Nat} {s t : State} {sp : Addr} {mi : BitVec 64} {rs : List (Nat × Nat)}
    (h : HP p.B p.wr (p.vs i u) s) (hg : Good t p.B p.Z p.w mi) (hw : t.wr = s.wr)
    (hZ : slot p.w 28 ≤ p.Z) (henv : SharedEnv p.B p.Z sp s) (hf : SharedFrame p.B sp rs s.mem t.mem)
    (hd : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], ∀ r ∈ rs, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k)
    (hu : word t.mem p.B (8 * kUsed) = BitVec.ofNat 64 u') : HP p.B p.wr (p.vs i u') t := by
  have hm := (hp0 h).mrh
  have e : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], word t.mem p.B (8 * k) = word s.mem p.B (8 * k) :=
    fun k hk => SharedFrame.word hf henv (hd k hk) (by
      have hk32 : k < 32 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have := hdr_lt_slot p.w 28 hk32
      omega_arith) hg.scr.nowrap
  have := mr_hp (ex := []) hg (hw.trans h.wr) ⟨(e _ (by simp)).trans hm.out, (e _ (by simp)).trans hm.len,
    (e _ (by simp)).trans hm.usedP, (e _ (by simp)).trans hm.rand, (e _ (by simp)).trans hm.rlen,
    (e _ (by simp)).trans hm.chk, (e _ (by simp)).trans hm.ki, hu⟩ (by simp)
  rwa [List.append_nil] at this

def SharedR0 (q : RPub × Addr) (s : State) : Prop :=
  R0 q.1 s ∧ slot q.1.p.w 28 ≤ q.1.p.Z ∧ SharedEnv q.1.p.B q.1.p.Z q.2 s

private def roundPublic (q : RPub × Addr) : Caller.Public :=
  ⟨⟨q.1.p.B, q.1.p.Z, q.1.p.w⟩, q.2⟩

private def RoundReady (q : RPub × Addr) (s : State) : Prop := Caller.Before (roundPublic q) s

private theorem witness_run (M : Mont) {q : RPub × Addr} {s : State} (h : SharedR0 q s) :
    ∃ t s', Exec isa (seqs (mrWitness ++ [M.mm aXm aX aR2])) s t s' := by
  obtain ⟨⟨hk, hp, hd, mi, c, bm, r, uni, hc, he, hR2, hc1, hsh, hsrc, _, hlen, _⟩, hz, henv⟩ := h
  have hm := (hp0 hp).mrh
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by have := hd.w4; omega_arith) hsh
  obtain ⟨t, s', he, -⟩ := sharedWitness_ok M hd hc hR2 hsh.1 hc1 hb hm.rand hm.used hm.len hsrc hlen
  exact ⟨t, s', he⟩

private theorem prefix_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) : RelCT isa (Two SharedR0)
    (seqs (mrWitness ++ [mm aXm aX aR2])) (Two RoundReady) := by
  refine two_post ?_ ?_
  · have ht : RelCT isa (Two R0) (seqs (mrWitness ++ [M.mm aXm aX aR2])) (fun _ _ => True) := by
      refine RelCT.seqs_app (by simp [mrWitness]) (by simp) (RelCT.seq mrWitness_ct ?_)
      simp only [seqs]
      exact two_map (fun q : RPub => (⟨q.p.B, q.p.Z, q.p.w⟩ : Ws))
        (fun _ _ h => let ⟨_, hd, mi, _, _, hc, _⟩ := h; ⟨mi, hc.good, hd.z⟩)
        (M.ct (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))
    refine RelCT.of_inline (witness_inlineOk hmc.ok) ?_ ?_ ?_ ?_
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      rw [hmc.witness]
      exact ⟨witness_run M h₁, witness_run M h₂⟩
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      exact ⟨h₁.2.2.hole_clear, h₂.2.2.hole_clear⟩
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      exact h₁.2.2.rsp.trans h₂.2.2.rsp.symm
    · rw [hmc.witness]
      exact ht.mono (fun _ _ ⟨q, hs, ht⟩ => ⟨q.1, hs.1, ht.1⟩) (fun _ _ _ => trivial)
  · rintro q s ⟨⟨hk, hp, hd, mi, c, bm, r, uni, hc, he, hR2, hc1, hsh, hsrc, _, hlen, _⟩, hz, henv⟩
    have hm := (hp0 hp).mrh
    have hnw := hc.good.scr.nowrap
    obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by have := hd.w4; omega_arith) hsh
    refine WP.mono (sharedWitness_call_ok M hmc henv hd hc hR2 hsh.1 hc1 hb hm.rand hm.used hm.len hsrc hlen) ?_
    rintro t ⟨hct, hx, hr2, hu, hus, hf, ht⟩
    have hex : ∀ r ∈ witnessRanges q.1.p.w, slot q.1.p.w aE + 8 * (q.1.p.w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot q.1.p.w aE := by
      intro r hr
      refine Or.inr ?_
      simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | (rfl | rfl | rfl)
      all_goals simp only [slot, hdrBytes, aX, aAcc, aTmp, aXm, aE, kUsed, kU, sFn]; omega_arith
    have het : ECtx t.mem q.1.p.B q.1.p.w c :=
      ⟨by rw [SharedFrame.array hf henv (fun r hr => by have := hex r hr; omega_arith) (by have := aE_fits hd; omega_arith) hnw]; exact he.e,
        by rw [SharedFrame.word hf henv (fun r hr => by have := hex r hr; omega_arith) (by have := aE_fits hd; omega_arith) hnw]; exact he.l⟩
    exact ⟨mi, c, bm, (wtOf c q.1.p.w q.1.u r).1, hct, het, hd, hz,
      (henv.kept ht (by decide)).room, (henv.kept ht (by decide)).rsp, hsh.1, by have := hsh.1; omega_arith, hx⟩

private theorem mid_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) : RelCT isa (Two SharedR0)
    (seqs ((mrWitness ++ [mm aXm aX aR2]) ++ [R.run])) (Two fun (q : RPub × Addr) s => Rmid q.1 s) := by
  refine two_post (RelCT.seqs_app (by simp [mrWitness]) (by simp)
    (RelCT.seq (prefix_ct M hmc) ?_)) ?_
  · change RelCT isa (Two fun q => Caller.Before (roundPublic q)) R.run (fun _ _ => True)
    exact two_map roundPublic (fun _ _ h => h) R.ct
  · rintro q s ⟨⟨hk, hp, hd, mi, c, bm, r, uni, hc, he, hR2, hc1, hsh, hsrc, _, hlen,
        hun, _, huni, _, hpass⟩, hz, henv⟩
    have hm := (hp0 hp).mrh
    refine WP.mono (sharedMid_ok M hmc R hd hz henv hc he hR2 hc1 hsh hm.rand hm.used hm.len hsrc hlen
      hm.ki hun hm.chk) ?_
    rintro t ⟨⟨bm', hct⟩, het, hf, hi, huni', hchk, hu, hus, hr2, hfr, ht⟩
    refine ⟨hk, hp_shared_used hp hct.good ht.2.2 hz henv hfr ?_ hus, hd, mi, uni, _,
      hct.good, by rw [hf, hpass], huni', hu, huni⟩
    intro k hmem r hr
    rcases List.mem_append.mp hr with hw | hc
    · simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl)
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj
    · apply sharedKernel_hdr _ k ?_ r hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kE, kElen, sFn]

theorem sharedRound_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) :
    RelCT isa (Two SharedR0) (seqs (mrRoundWith mm R.run)) fun _ _ => True := by
  unfold mrRoundWith
  exact RelCT.seqs_app (by simp [mrWitness]) (by simp) (RelCT.seq (mid_ct M hmc R)
    (two_map Prod.fst (fun _ _ h => h) roundTail_ct))

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! # Constant time of RSA's loop with a callable shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen (shapeOf itersOf passS)

/-- `SharedMrSt` survives changes to registers Montgomery multiplication may
change, and none to memory. -/
theorem SharedMrSt.congr {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {c ch : Nat} {rp : Addr} {r : List Byte} {s₀ : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat} {s t : State} {rs : List Reg}
    (h : SharedMrSt B sp Z w mi c ch rp r s₀ res i uni used s) (hd : MrDims B Z w) (hm : t.mem = s.mem) (k : Keep rs s t)
    (hrs : ∀ r ∈ rs, r ∈ mmRegs) : SharedMrSt B sp Z w mi c ch rp r s₀ res i uni used t := by
  obtain ⟨⟨bm, hc⟩, hE, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, henv⟩ := h
  refine ⟨⟨bm, hc.of_frm hd (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (hc.good.scr.congr k.2.2)
    ((k.gpr (by intro h; have := hrs _ h; simp [mmRegs] at this)).trans hc.good.rdi) (by simp) (by simp) (by simp)
    (by simp) (by simp)⟩, by rw [hm]; exact hE, by rw [hm]; exact h1, by rw [hm]; exact h2, by rw [hm]; exact h3, by rw [hm]; exact h4,
    by rw [hm]; exact h5, h6.congrK (by rw [hm]; exact InScr.refl _ _ _) k, by rw [hm]; exact h7, by rw [hm]; exact h8,
    by rw [hm]; exact h9, h10, h11, h12, h13, h14, by rw [hm]; exact h15, (h16.trans k).mono (fun r hr => ?_), henv.kept k (fun h => by have := hrs _ h; simp [mmRegs] at this)⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact hr
  · exact hrs r hr

structure SharedLPub extends LPub where
  sp : Addr
  z28 : slot p.w 28 ≤ p.Z

abbrev SharedLPub.u (a : SharedLPub) (j : Nat) : Nat := a.toLPub.u j
abbrev SharedLPub.N (a : SharedLPub) : Nat := a.toLPub.N

/-- At the head of iteration `j`. -/
def SharedLoopI (a : SharedLPub) (j : Nat) (s : State) : Prop :=
  KW a.p.B a.p.wr ∧ MrDims a.p.B a.p.Z a.p.w ∧ a.p.ch < 2 ^ 62 ∧ a.p.rl < 2 ^ 64 ∧
    ∃ (mi : BitVec 64) (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte)) (uni : Nat),
      SharedMrSt a.p.B a.sp a.p.Z a.p.w mi c a.p.ch a.p.rP r s₀ res (j + 1) uni (a.u j) s ∧ shapeOf res = a.S ∧
      r.length = a.p.rl ∧ 1 < c ∧ VG.Proof.RsaKeyGen.PrimeShape (64 * a.p.w) c ∧
      word s₀.mem a.p.B (8 * kOut) = a.p.op ∧ word s₀.mem a.p.B (8 * kUsedP) = a.p.up ∧
      word s₀.mem a.p.B (8 * kLen) = BitVec.ofNat 64 (8 * a.p.w) ∧ s₀.wr = a.p.wr ∧
      itersOf (8 * a.p.w) a.p.rl a.S (a.u j) = a.N - j

/-- The header at the head of an iteration. -/
theorem SharedLoopI.hp {a : SharedLPub} {j : Nat} {s : State} (h : SharedLoopI a j s) :
    HP a.p.B a.p.wr (a.p.vs (j + 1) (a.u j)) s := by
  obtain ⟨-, hd, -, -, mi, c, r, s₀, res, uni, hI, -, hrl, -, -, hout, hup, -, hw, -⟩ := h
  obtain ⟨bm, hc⟩ := hI.ctx
  have hf := hI.frm
  have e : ∀ k, k = kOut ∨ k = kUsedP → word s.mem a.p.B (8 * k) = word s₀.mem a.p.B (8 * k) := fun k hk => by
    rcases hk with rfl | rfl
    · exact SharedFrame.word hf hI.env (sharedRoundRanges_hdr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (by have := hdr_lt_slot a.p.w 28 (show kOut < 32 by decide); have := a.z28; omega_arith) hc.good.scr.nowrap
    · exact SharedFrame.word hf hI.env (sharedRoundRanges_hdr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) (by have := hdr_lt_slot a.p.w 28 (show kUsedP < 32 by decide); have := a.z28; omega_arith) hc.good.scr.nowrap
  have := mr_hp (ex := []) (i := j + 1) (u := a.u j) hc.good (hI.keep.2.2.trans hw)
    ⟨(e _ (Or.inl rfl)).trans hout, hI.len, (e _ (Or.inr rfl)).trans hup, hI.rand, by rw [hI.rlen, hrl], hI.chk,
      hI.ki, hI.kused⟩ (by simp)
  rwa [List.append_nil] at this

/-- Before the branch on `rand`'s length. -/
def SharedAvI (p : SharedLPub × Nat) (s : State) : Prop :=
  SharedLoopI p.1 p.2 s ∧ s.cf = some (decide (p.1.p.rl < p.1.u p.2 + 8 * p.1.p.w))

/-- What a round needs, at the head of an iteration with the witness's octets. -/
theorem sharedAvI_r0 {p : SharedLPub × Nat} {s : State} (h : SharedAvI p s) (hb : isa.eval .b s = some false) :
    SharedR0 (⟨p.1.p, p.2 + 1, p.1.u p.2, passS (8 * p.1.p.w) p.1.p.rl p.1.S (p.1.u p.2)⟩, p.1.sp) s := by
  have hp := h.1.hp
  obtain ⟨⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, -⟩, hcf⟩ := h
  simp only [eval, hcf, Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at hb
  obtain ⟨bm, hc⟩ := hI.ctx
  have hw4 := hd.w4
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [hw4]) hsh
  have hiu := hI.iu
  have hul := hI.ul
  have hi : 32 * (p.2 + 1) ≤ 8 * p.1.p.w * (p.2 + 1) := Nat.mul_le_mul_right _ (by omega_using [hw4])
  have hj : p.2 + 1 < 2 ^ 59 := by omega_using [hrl, hb, hiu, hi]
  have hun := hI.unii
  refine ⟨⟨hk, hp, hd, mi, c, bm, r, uni, hc, hI.ex, hI.r2, hc1, hsh, hI.src, hrlen, by rw [hrlen]; exact hb, hI.kuni,
    show p.2 + 1 < 2 ^ 61 by omega_using [hj], by omega_using [hj, hun], hch, ?_⟩, p.1.z28, hI.env⟩
  rw [← hS, ← hI.rest, ← hrlen]
  exact (VG.Proof.RsaKeyGen.mr_pass hI.go hwb (by omega_using [hw4]) (by rw [hrlen]; exact hb)).symm

/-- Where the loop ends. -/
def SharedLoopEnd (a : SharedLPub) (s : State) : Prop :=
  KW a.p.B a.p.wr ∧ MrDims a.p.B a.p.Z a.p.w ∧
    ∃ (mi : BitVec 64) (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte)),
      SharedMrEnd a.p.B a.sp a.p.Z a.p.w mi c r s₀ res s ∧ shapeOf res = a.S ∧ r.length = a.p.rl ∧
      word s₀.mem a.p.B (8 * kOut) = a.p.op ∧ word s₀.mem a.p.B (8 * kUsedP) = a.p.up ∧
      word s₀.mem a.p.B (8 * kLen) = BitVec.ofNat 64 (8 * a.p.w) ∧ s₀.wr = a.p.wr ∧ SharedEnv a.p.B a.p.Z a.sp s₀

/-- Miller–Rabin's loop leaks the same in runs that agree on the public data
and on the shape of the result. -/
theorem sharedMrLoop_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) :
    RelCT isa (Two fun (a : SharedLPub) s => 0 < a.N ∧ SharedLoopI a 0 s)
      (.loop (seqs [
        .block [.mov .rcx (.mem (hdr kRandLen)), .mov .rax (.mem (hdr kUsed)), .alu .sub .rcx (.reg .rax),
          .mov .rax (.mem (hdr kLen)), .alu .cmp .rcx (.reg .rax)],
        .ite .b (.block [.mov32 .rax (.imm 0), .store (hdr kStat) .rax]) (seqs (mrRoundWith mm R.run)),
        .block [.mov .rax (.mem (hdr kStat)), .alu .cmp .rax (.imm 4)]]) .e) (Two SharedLoopEnd) := by
  refine two_loop (Φ := SharedLoopI) SharedLPub.N ?_ ?_
  · simp only [seqs]
    refine RelCT.seq (R := Two SharedAvI) (kt_piece (fun p : SharedLPub × Nat => p.1.p.B) (fun p => p.1.p.wr) mrS
      (fun p => p.1.p.vs (p.2 + 1) (p.1.u p.2)) [] (by decide) (fun p => vs_fst0 _ _ _)
      (fun _ _ h => ⟨h.2.1, h.2.hp⟩) (pins_nil _) (by taint_decide) ?_)
      (two_ite_seq (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_)
    · rintro ⟨a, j⟩ s ⟨hj, h⟩
      have h' := h
      obtain ⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, ho, hu, hl0, hw, hit⟩ := h'
      obtain ⟨bm, hc⟩ := hI.ctx
      refine WP.mono (availCmp_ok hc.good hd.z (hI.rlen.trans (by rw [hrlen])) hI.kused hI.len (by rw [← hrlen]; exact hI.ul)
        hrl (by have := hd.w128; omega_using [this])) fun t ⟨hcf, hm, k⟩ =>
          ⟨⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni, hI.congr hd hm k (by decide), hS, hrlen, hc1, hsh, ho, hu, hl0, hw,
            hit⟩, hcf⟩
    · exact kt_ct (fun p : SharedLPub × Nat => p.1.p.B) (fun p => p.1.p.wr) [] (fun _ => []) [] (by decide)
        (fun _ => rfl) (fun _ _ h => ⟨h.1.1.1, hp_nil h.1.1.hp⟩) (pins_nil _) (by taint_decide)
    · refine RelCT.seq (R := Two fun (p : SharedLPub × Nat) s => KW p.1.p.B p.1.p.wr ∧ HP p.1.p.B p.1.p.wr [] s)
        (two_post (two_map (fun p : SharedLPub × Nat =>
          ((⟨p.1.p, p.2 + 1, p.1.u p.2, passS (8 * p.1.p.w) p.1.p.rl p.1.S (p.1.u p.2)⟩ : RPub), p.1.sp))
          (fun _ _ h => sharedAvI_r0 h.1 h.2) (sharedRound_ct M hmc R)) ?_)
        (kt_ct (fun p : SharedLPub × Nat => p.1.p.B) (fun p => p.1.p.wr) [] (fun _ => []) [] (by decide)
          (fun _ => rfl) (fun _ _ h => h) (pins_nil _) (by taint_decide))
      rintro p s ⟨h, hb⟩
      have hr := sharedAvI_r0 h hb
      obtain ⟨⟨hk, hp, hd, mi, c, bm, r, uni, hc, hE, hR2, hc1, hsh, hsrc, -, hlen, hun, hi, huni, hch, -⟩, hz, henv⟩ := hr
      have hm := (hp0 hp).mrh
      exact WP.mono (sharedRound_ok M hmc R hd hz henv hc hE hR2 hc1 hsh hm.rand hm.used hm.len hsrc hlen hm.ki hun hm.chk hi huni hch)
        fun t ⟨⟨_, hc'⟩, _, _, _, _, _, _, k⟩ => ⟨hk, hc'.good.rdi, k.2.2.trans hp.wr, fun _ he => absurd he (List.not_mem_nil)⟩
  · rintro a j s hj ⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, ho, hu, hl0, hw, hit⟩
    have hw4 := hd.w4
    obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [hw4]) hsh
    refine WP.mono (sharedMrIter_ok M hmc R hd a.z28 hc1 hsh (by omega_using [hrl, hrlen]) hch s hI) fun t ht => ?_
    rcases ht with ⟨he, hend, hnone, hsome⟩ | ⟨he, uni', hI'⟩
    · have h1 : itersOf (8 * a.p.w) a.p.rl a.S (a.u j) = 1 := by
        rcases hres : res with _ | ⟨b, rest⟩
        · rw [← hS, hres]; exact VG.Proof.RsaKeyGen.iters_end_none (by omega_using [hw4]) (by rw [← hrlen]; exact hnone hres)
        · rw [← hS, hres]
          exact VG.Proof.RsaKeyGen.iters_end_some (by omega_using [hw4]) (by rw [← hrlen]; exact hsome b rest hres)
      refine ⟨by rw [he]; simp only [Option.some.injEq, Bool.false_eq, decide_eq_false_iff_not, Nat.not_lt]; omega,
        fun h => absurd h (by omega), fun _ => ⟨hk, hd, mi, c, r, s₀, res, hend, hS, hrlen, ho, hu, hl0, hw, hI.env.back hI.keep (by decide)⟩⟩
    · have hu' : a.u (j + 1) = a.u j + 8 * a.p.w := by simp only [SharedLPub.u, LPub.u]; rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      have hc := VG.Proof.RsaKeyGen.iters_cont (L := 8 * a.p.w) (r := r) (a := (Spec.Rsa.splitTwos (c - 1)).1)
        (m := (Spec.Rsa.splitTwos (c - 1)).2) hI'.go hwb (by omega_using [hw4]) (by omega_using []) hI'.ul
      have hr' : Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c a.p.ch (Spec.Rsa.splitTwos (c - 1)).1
          (Spec.Rsa.splitTwos (c - 1)).2) (j + 1 + 1, uni') (List.drop (a.u j + 8 * a.p.w) r) = res := hI'.rest
      rw [show a.u j + 8 * a.p.w - 8 * a.p.w = a.u j by omega_using [], hr', hS, hrlen] at hc
      refine ⟨by rw [he]; exact congrArg some (decide_eq_true (by omega)).symm, fun _ => ?_, fun h => absurd h (by omega)⟩
      rw [← hu'] at hI'
      exact ⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni', hI', hS, hrlen, hc1, hsh, ho, hu, hl0, hw, by rw [hu']; omega_using [hit, hc]⟩

/-- What `millerRabinWith` needs, for the shape
of its result. -/
def SharedMrPre (a : SharedLPub) (s : State) : Prop :=
  KW a.p.B a.p.wr ∧ HP a.p.B a.p.wr [] s ∧ MrDims a.p.B a.p.Z a.p.w ∧ a.p.ch < 2 ^ 62 ∧ a.p.rl < 2 ^ 64 ∧
    ∃ (mi : BitVec 64) (c bm : Nat) (r : List Byte), MrCtx s a.p.B a.p.Z a.p.w mi c bm ∧ ECtx s.mem a.p.B a.p.w c ∧
      wv s.mem a.p.B (slot a.p.w aR2) a.p.w = 2 ^ (64 * a.p.w) * 2 ^ (64 * a.p.w) % c ∧ 1 < c ∧
      VG.Proof.RsaKeyGen.PrimeShape (64 * a.p.w) c ∧ word s.mem a.p.B (8 * kOut) = a.p.op ∧
      word s.mem a.p.B (8 * kUsedP) = a.p.up ∧ word s.mem a.p.B (8 * kRand) = a.p.rP ∧
      word s.mem a.p.B (8 * kLen) = BitVec.ofNat 64 (8 * a.p.w) ∧
      word s.mem a.p.B (8 * kRandLen) = BitVec.ofNat 64 r.length ∧ r.length = a.p.rl ∧
      word s.mem a.p.B (8 * kChecks) = BitVec.ofNat 64 a.p.ch ∧ Src s a.p.B a.p.Z a.p.rP r ∧
      word s.mem a.p.B (8 * kUsed) = BitVec.ofNat 64 a.u0 ∧ 8 * a.p.w ≤ a.u0 ∧ a.u0 ≤ r.length ∧
      shapeOf (mrRest c a.p.ch r 1 0 a.u0) = a.S ∧ SharedEnv a.p.B a.p.Z a.sp s

/-- `millerRabinWith` leaks the same in runs that agree on the public data and on
the shape of the result. -/
theorem sharedMillerRabin_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) : RelCT isa (Two SharedMrPre) (seqs (millerRabinWith mm R.run)) (Two SharedLoopEnd) := by
  unfold millerRabinWith
  simp only [seqs]
  refine RelCT.seq (kt_piece (fun a : SharedLPub => a.p.B) (fun a => a.p.wr) [] (fun _ => []) [] (by decide)
    (fun _ => rfl) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) ?_) (sharedMrLoop_ct M hmc R)
  rintro a s ⟨hk, hp, hd, hch, hrl, mi, c, bm, r, hc, hE, hr2, hc1, hsh, ho, hup, hR, hK, hRL, hrlen, hC, hsrc, hU, hu1,
    hu2, hS, henv⟩
  have hw4 := hd.w4
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [hw4]) hsh
  have hN : 1 ≤ a.N := by
    have := (VG.Proof.RsaKeyGen.iters_cont (L := 8 * a.p.w) (r := r) (a := (Spec.Rsa.splitTwos (c - 1)).1)
      (m := (Spec.Rsa.splitTwos (c - 1)).2) (ch := a.p.ch) (i := 1) (uni := 0) (Or.inl (by decide)) hwb (by omega_using [hw4]) hu1
      hu2).2
    have hr' : Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c a.p.ch (Spec.Rsa.splitTwos (c - 1)).1
        (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (List.drop a.u0 r) = mrRest c a.p.ch r 1 0 a.u0 := rfl
    rwa [hr', hS, hrlen] at this
  refine WP.mono (sharedMrInit_ok hd a.z28 henv hc hE hr2 hR hK hRL hC hsrc hU hu1 hu2) fun t hI => ⟨hN, hk, hd, hch, hrl, mi, c, r, s,
    _, 0, by simpa [SharedLPub.u, LPub.u] using hI, hS, hrlen, hc1, hsh, ho, hup, hK, hp.wr, by simp [SharedLPub.u, LPub.u]⟩

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! ### `RsaKeyGen.X86_64.SharedCTTail`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.SharedCTResult`, which only this module used -/

section

/-! # Reuse the existing result routine's constant-time proof -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

/-- The result routine needs the final context and three public header
words. Its existential starting memory can be the final memory: it does
not use the history of the loop's workspace or private stack writes. -/
private theorem result_context {a : SharedLPub} {s : State} (h : SharedLoopEnd a s) :
    LoopEnd a.toLPub s := by
  obtain ⟨hk, hd, mi, c, r, s₀, res, ⟨hctx, h0, h1, hf, hkeep⟩, hS, hrl, ho, hu, hl, hw, henv⟩ := h
  obtain ⟨bm, hc⟩ := hctx
  have hh {k : Nat} (h32 : k < 32)
      (hdj : ∀ r ∈ sharedRoundRanges a.p.w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k) :
      word s.mem a.p.B (8 * k) = word s₀.mem a.p.B (8 * k) :=
    SharedFrame.word hf henv hdj (by
      have := hdr_lt_slot a.p.w 28 h32
      have := a.z28
      omega_arith) hc.good.scr.nowrap
  let u : State := { s₀ with mem := s.mem }
  refine ⟨hk, hd, mi, c, r, u, res, ⟨⟨bm, hc⟩, h0, h1, Frm.refl _ _ _, hkeep⟩,
    hS, hrl, ?_, ?_, ?_, hw⟩
  · exact (hh (by decide) (sharedRoundRanges_hdr _ (by simp))).trans ho
  · exact (hh (by decide) (sharedRoundRanges_hdr _ (by simp))).trans hu
  · exact (hh (by decide) (sharedRoundRanges_hdr _ (by simp))).trans hl

theorem sharedResult_ct : RelCT isa (Two SharedLoopEnd) mrResult fun _ _ => True :=
  two_map SharedLPub.toLPub (fun _ _ h => result_context h) mrResult_ct

end VG.Proof.RsaKeyGen.X86_64

end

end


/-! # Constant time of setup and the callable RSA witness loop -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen (shapeOf)

structure SharedTPub extends TPub where
  sp : Addr
  z28 : slot w 28 ≤ Z

abbrev SharedTPub.lp (q : SharedTPub) : SharedLPub := ⟨q.toTPub.lp, q.sp, q.z28⟩

def SharedMsPre (q : SharedTPub) (s : State) : Prop :=
  MsPre q.toTPub s ∧ SharedEnv q.B q.Z q.sp s

def SharedMrPre0 (a : SharedLPub) (s : State) : Prop :=
  MrPre0 a.toLPub s ∧ SharedEnv a.p.B a.p.Z a.sp s

private theorem setup_run (M : Mont) {q : TPub} {s : State} (h : MsPre q s) :
    ∃ t s', Exec isa (seqs (montSetup M.mm)) s t s' := by
  obtain ⟨⟨-, -, hd, -⟩, -, mi, c, r, hg, hn, hsh, -⟩ := h
  obtain ⟨hodd, hlo, -⟩ := hsh
  have htop : 2 ^ (64 * q.w - 1) ≤ c := by
    have : 2 ^ (64 * q.w - 1) = 2 ^ (64 * q.w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; have := hd.w4; omega_arith
    omega_arith
  obtain ⟨t, s', he, -⟩ := montSetup_ok M hg hd.z hd.x hd.w4 hd.w64 hn hodd htop
  exact ⟨t, s', he⟩

private theorem setup_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) : RelCT isa (Two SharedMsPre) (seqs (montSetup mm))
    (Two fun q : SharedTPub => SharedMrPre0 q.lp) := by
  refine two_post ?_ ?_
  · refine RelCT.of_inline (montSetup_inlineOk hmc.ok) ?_ ?_ ?_ ?_
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      rw [hmc.montSetup]
      exact ⟨setup_run M h₁.1, setup_run M h₂.1⟩
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      exact ⟨h₁.2.hole_clear, h₂.2.hole_clear⟩
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      exact h₁.2.rsp.trans h₂.2.rsp.symm
    · rw [hmc.montSetup]
      exact (two_map SharedTPub.toTPub (fun _ _ h => h.1) (montSetup_ct M)).mono
        (fun _ _ h => h) (fun _ _ _ => trivial)
  · rintro q s ⟨⟨⟨hk, hw, hd, -⟩, hrl, mi, c, r, hg, hn, hsh, hO, hU, hR, hK, hRL, hUs, hsrc, hrlen, hrk, hS⟩, henv⟩
    obtain ⟨hodd, hlo, hhi⟩ := hsh
    have hw4 := hd.w4
    have hnw := hg.scr.nowrap
    have htop : 2 ^ (64 * q.w - 1) ≤ c := by
      have : 2 ^ (64 * q.w - 1) = 2 ^ (64 * q.w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega_arith
      omega_arith
    refine WP.mono (montSetup_call_ok M hmc henv hg hd.z hd.x hw4 hd.w64 hn hodd htop)
      fun t ⟨mi', hg', hinv, hr2, hr1, hrm1, hchk, hf, k⟩ => ?_
    have e : ∀ x, x = kOut ∨ x = kUsedP ∨ x = kRand ∨ x = kLen ∨ x = kRandLen ∨ x = kUsed →
        word t.mem q.B (8 * x) = word s.mem q.B (8 * x) := fun x hx => SharedFrame.word hf henv (msRanges_hdr _ x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hx)) (by
          have := hd.z
          have hk32 : x < 32 := by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          have := hdr_lt_slot q.w 8 hk32
          omega_arith) hnw
    have hn' : wv t.mem q.B (slot q.w aN) q.w = c := by
      rw [SharedFrame.array hf henv (d := slot q.w aN) (k := q.w) (by simp only [msRanges]; rng_disj)
        (by have := slot_le (w := q.w) (show aN < 8 by decide); have := hd.z; omega_arith) hnw]; exact hn
    have hle : ∀ r ∈ msRanges q.w, r.1 + r.2 ≤ q.Z := fun r hr => by
      have : r.1 + r.2 ≤ slot q.w aRm1 + 8 * (q.w + 2) := by revert r hr; simp only [msRanges]; rng_le
      have := hd.x; omega_arith
    have hc1 : 1 < c := by have := Nat.two_pow_pos (64 * q.w - 2); omega_arith
    have hch : Proof.RsaKeyGen.checksW q.w < 2 ^ 62 := by
      unfold Proof.RsaKeyGen.checksW; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
        (try split) <;> decide
    exact ⟨⟨hk, ⟨hg'.rdi, k.2.2.trans hw, fun _ he => absurd he List.not_mem_nil⟩, hd.mr, hch, hrl, mi', c,
      wv t.mem q.B (slot q.w aB) q.w, r, ⟨hg', hinv, hn', rfl, hr1, hrm1⟩, hr2, hc1, ⟨hodd, hlo, hhi⟩,
      by rw [e _ (Or.inl rfl)]; exact hO, by rw [e _ (Or.inr (Or.inl rfl))]; exact hU,
      by rw [e _ (Or.inr (Or.inr (Or.inl rfl)))]; exact hR, by rw [e _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact hK,
      by rw [e _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact hRL, hrlen, hchk,
      hsrc.shared henv hf hle k, by rw [e _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]; exact hUs,
      Nat.le_refl _, hrk, hS⟩, henv.kept k (by decide)⟩

private theorem exponent_ct : RelCT isa (Two SharedMrPre0) (seqs expSetup) (Two SharedMrPre) := by
  refine two_post ?_ ?_
  · exact (two_map SharedLPub.toLPub (fun _ _ h => h.1) expSetup_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)
  · rintro a s ⟨h, henv⟩
    have ht := expSetup_pre h
    obtain ⟨hk, hp, hd, hch, hrl, mi, c, bm, r, hc, hr2, hc1, hsh, _⟩ := h
    refine WP.mono (WP.and' ht (WP.mono (expSetup_ok hc.good hd hc.n hsh.1 hc1)
      (fun t ⟨_, _, _, k⟩ => henv.kept k (by decide)))) ?_
    rintro t ⟨⟨hk, hp, hd, hch, hrl, mi, c, bm, r, hc, he, hr2, hc1, hsh, ho, hup, hR, hK, hRL, hrlen, hC,
      hsrc, hU, hu1, hu2, hS⟩, henv⟩
    exact ⟨hk, hp, hd, hch, hrl, mi, c, bm, r, hc, he, hr2, hc1, hsh, ho, hup, hR, hK, hRL, hrlen, hC,
      hsrc, hU, hu1, hu2, hS, henv⟩

theorem sharedTail_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) :
    RelCT isa (Two SharedMsPre)
      (seqs (montSetup mm ++ expSetup ++ millerRabinWith mm R.run ++ [mrResult]))
      (fun _ _ => True) :=
  RelCT.seqs_app (by simp [montSetup]) (List.cons_ne_nil _ _)
    (RelCT.seq (RelCT.seqs_app (by simp [montSetup]) (by simp [millerRabinWith])
      (RelCT.seq (RelCT.seqs_app (by simp [montSetup]) (by simp [expSetup, lowWord])
        (RelCT.seq (setup_ct M hmc) (two_map SharedTPub.lp (fun _ _ h => h) exponent_ct)))
        (sharedMillerRabin_ct M hmc R))) sharedResult_ct)

end VG.Proof.RsaKeyGen.X86_64

end

end


/-! # Public candidate checks before the callable shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

structure SharedFPub extends FPub where
  sp : Addr
  z28 : slot w 28 ≤ Z

abbrev SharedFPub.tp (q : SharedFPub) : SharedTPub := ⟨q.toFPub.tp, q.sp, q.z28⟩

def SharedKSt (q : SharedFPub) (s : State) : Prop :=
  KSt q.toFPub s ∧ SharedEnv q.B q.Z q.sp s

def SharedK0 (q : SharedFPub) (s : State) : Prop :=
  K0 q.toFPub s ∧ SharedEnv q.B q.Z q.sp s

private theorem close_ct : RelCT isa (Two SharedKSt) (seqs closeCheck) fun _ _ => True :=
  two_map SharedFPub.toFPub (fun _ _ h => h.1) closeCheck_ct

private theorem close_stage {q : SharedFPub} {s : State} (h : SharedKSt q s) :
    WP isa (seqs closeCheck) s fun t => SharedKSt q t ∧ t.zf = some (!q.sch.close) :=
  WP.mono (WP.keep mmRegs (closeStage_ok h.1) rfl) fun _ ⟨ht, hk⟩ =>
    ⟨⟨ht.1, h.2.kept hk (by decide)⟩, ht.2⟩

private theorem trial_stage {q : SharedFPub} {s : State} (h : SharedKSt q s) (hcl : q.sch.close = false) :
    WP isa (seqs trial) s fun t => SharedKSt q t ∧ t.zf = some (!q.sch.comp) :=
  WP.mono (WP.keep mmRegs (trialStage_ok h.1 hcl) (by decide +kernel)) fun _ ⟨ht, hk⟩ =>
    ⟨⟨ht.1, h.2.kept hk (by decide)⟩, ht.2⟩

private theorem gcd_stage {q : SharedFPub} {s : State} (h : SharedKSt q s)
    (hcl : q.sch.close = false) (hco : q.sch.comp = false) :
    WP isa (seqs gcdCheck) s fun t => SharedKSt q t ∧ t.zf = some (!q.sch.gbad) :=
  WP.mono (WP.keep mmRegs (gcdStage_ok h.1 hcl hco) rfl) fun _ ⟨ht, hk⟩ =>
    ⟨⟨ht.1, h.2.kept hk (by decide)⟩, ht.2⟩

private theorem tail_pre {q : SharedFPub} {s : State} (h : SharedKSt q s)
    (hcl : q.sch.close = false) (hco : q.sch.comp = false) (hg : q.sch.gbad = false) : SharedMsPre q.tp s :=
  ⟨tailPre h.1 hcl hco hg, h.2⟩

private theorem fin2_ct {Φ : SharedFPub → State → Prop} (hΦ : ∀ q s, Φ q s → SharedKSt q s) :
    RelCT isa (Two Φ) (finUsed 2) (fun _ _ => True) :=
  (finUsed2_ct (Φ := KSt) (fun _ _ h => h)).mono
    (fun _ _ ⟨q, hs, ht⟩ => ⟨q.toFPub, (hΦ _ _ hs).1, (hΦ _ _ ht).1⟩) (fun _ _ h => h)

private theorem fin3_ct {Φ : SharedFPub → State → Prop} (hΦ : ∀ q s, Φ q s → SharedKSt q s) :
    RelCT isa (Two Φ) (finUsed 3) (fun _ _ => True) :=
  (finUsed3_ct (Φ := KSt) (fun _ _ h => h)).mono
    (fun _ _ ⟨q, hs, ht⟩ => ⟨q.toFPub, (hΦ _ _ hs).1, (hΦ _ _ ht).1⟩) (fun _ _ h => h)

private theorem trial_ct' {Φ : SharedFPub → State → Prop} (hΦ : ∀ q s, Φ q s → SharedKSt q s) :
    RelCT isa (Two Φ) (seqs trial) (fun _ _ => True) :=
  (trial_ct (Φ := KSt) (fun _ _ h => h)).mono
    (fun _ _ ⟨q, hs, ht⟩ => ⟨q.toFPub, (hΦ _ _ hs).1, (hΦ _ _ ht).1⟩) (fun _ _ h => h)

private theorem gcd_ct {Φ : SharedFPub → State → Prop} (hΦ : ∀ q s, Φ q s → SharedKSt q s) :
    RelCT isa (Two Φ) (seqs gcdCheck) (fun _ _ => True) :=
  (gcdCheck_ct (Φ := KSt) (fun _ _ h => h)).mono
    (fun _ _ ⟨q, hs, ht⟩ => ⟨q.toFPub, (hΦ _ _ hs).1, (hΦ _ _ ht).1⟩) (fun _ _ h => h)

theorem sharedAfterLoad_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) : RelCT isa (Two SharedKSt) (seqs (closeCheck ++ ([.ite .ne (finUsed 2) (seqs (trial ++
    ([.ite .ne (finUsed 3) (seqs (gcdCheck ++
      ([.ite .ne (finUsed 3) (seqs (montSetup mm ++ expSetup ++ millerRabinWith mm R.run ++ [mrResult]))] : List (Prog isa))))] : List (Prog isa))))] : List (Prog isa)))) fun _ _ => True := by
  refine RelCT.seqs_app (by simp [closeCheck]) (by simp) (RelCT.seq (R := Two fun q s => SharedKSt q s ∧
    s.zf = some (!q.sch.close)) (two_post close_ct fun _ _ h => close_stage h) ?_)
  simp only [seqs]
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) (fin2_ct fun _ _ h => h.1.1) ?_
  refine RelCT.seqs_app (by simp [trial]) (by simp) (RelCT.seq (R := Two fun q s => (SharedKSt q s ∧
    s.zf = some (!q.sch.comp)) ∧ q.sch.close = false) (two_post (trial_ct' fun _ _ h => h.1.1) fun q s h => ?_) ?_)
  · have hcl := ne_false h.1.2 h.2
    exact WP.mono (trial_stage h.1.1 hcl) fun t ht => ⟨ht, hcl⟩
  simp only [seqs]
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2, h₂.1.2]) (fin3_ct fun _ _ h => h.1.1.1) ?_
  refine RelCT.seqs_app (by simp [gcdCheck, loadE]) (by simp) (RelCT.seq (R := Two fun q s => (SharedKSt q s ∧
    s.zf = some (!q.sch.gbad)) ∧ q.sch.close = false ∧ q.sch.comp = false)
      (two_post (gcd_ct fun _ _ h => h.1.1.1) fun q s h => ?_) ?_)
  · have hco := ne_false h.1.1.2 h.2
    exact WP.mono (gcd_stage h.1.1.1 h.1.2 hco) fun t ht => ⟨ht, h.1.2, hco⟩
  simp only [seqs]
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2, h₂.1.2]) (fin3_ct fun _ _ h => h.1.1.1) ?_
  refine (sharedTail_ct M hmc R).mono (fun _ _ h => two_bind (fun q _ _ h₁ h₂ =>
    ⟨q.tp, tail_pre h₁.1.1.1 h₁.1.2.1 h₁.1.2.2 (ne_false h₁.1.1.2 h₁.2),
      tail_pre h₂.1.1.1 h₂.1.2.1 h₂.1.2.2 (ne_false h₂.1.1.2 h₂.2)⟩) h) fun _ _ h => h

theorem sharedKMain_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) :
    RelCT isa (Two SharedK0) (kMainWith mm R.run) (fun _ _ => True) := by
  rw [kMainWith_eq]
  refine RelCT.seqs_app (by simp [loadC]) (by simp [closeCheck])
    (RelCT.seq (two_post (two_map SharedFPub.toFPub (fun _ _ h => h.1) loadC_ct) ?_) (sharedAfterLoad_ct M hmc R))
  rintro q s ⟨h, henv⟩
  exact WP.mono (WP.keep mmRegs (loadCStage_ok h) rfl) fun _ ⟨ht, hk⟩ => ⟨ht, henv.kept hk (by decide)⟩

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! # Constant time of the complete RSA candidate with the shared call -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

private structure SharedCPub extends CPub where
  z28 : slot f.w 28 ≤ f.Z

private abbrev SharedCPub.fp (p : SharedCPub) : SharedFPub := ⟨p.f, p.rsp, p.z28⟩

private structure SharedCRel (p : SharedCPub) (s : State) : Prop extends CRel p.toCPub s where
  env : SharedEnv p.f.B p.f.Z p.rsp s

/-- After `kEntry`'s first instruction. -/
private def SharedC1 (p : SharedCPub) (t : State) : Prop :=
  ∃ s, SharedCRel p s ∧ t.gpr .r11 = p.f.B ∧ t.gpr .rsp = p.rsp ∧
    WP isa (.block (kEntry.drop 1)) t (EntryPost s · (arg s 3))

/-- After `kEntry`. -/
private def SharedC2 (p : SharedCPub) (t : State) : Prop := ∃ s, SharedCRel p s ∧ EntryPost s t (arg s 3)

/-- After the zeros to `out` and the length check. -/
private def SharedC3 (p : SharedCPub) (t : State) : Prop := ∃ s t₁, SharedCRel p s ∧ EntryPost s t₁ (arg s 3) ∧ Front s t₁ t

private theorem SharedC3.cf {p : SharedCPub} {t : State} (h : SharedC3 p t) : t.cf = some (decide (p.f.rl < 8 * p.f.w)) := by
  obtain ⟨s, t₁, hs, -, hf⟩ := h
  rw [hf.cf, hs.rl, hs.w]

private theorem SharedC3.k0 {p : SharedCPub} {t : State} (h : SharedC3 p t)
    (hlt : 8 * p.f.w ≤ p.f.rl) : SharedK0 p.fp t := by
  obtain ⟨s, t₁, hs, he, hf⟩ := h
  exact ⟨(show C3 p.toCPub t from ⟨s, t₁, hs.toCRel, he, hf⟩).k0 (by omega_arith),
    hs.env.kept (he.keep.trans hf.keep) (by decide)⟩

private theorem sharedCode_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) : RelCT isa (Two SharedCRel) (VG.Impl.RsaKeyGen.X86_64.Candidate.codeWith mm R.run) fun _ _ => True := by
  unfold VG.Impl.RsaKeyGen.X86_64.Candidate.codeWith
  simp only [seqs]
  refine RelCT.seq (R := Two SharedC2) ?_ (RelCT.assoc (RelCT.seq (R := Two SharedC3) ?_ ?_))
  · -- The entry: the scratch space's base from the stack, then the header.
    rw [kEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := SharedC1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rsp, h₂.rsp]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := kctx_of hs.pre
    have hn := c.hs.nowrap
    have hZ := c.hZ
    have hk1 := c.k1
    have hhw : ∀ i < 32, InRegions s.wr (off (arg s 3) (8 * i)) 8 := fun i hi => c.hs.st (by omega_using [hZ, hk1, hi])
    have hh : WP isa (.block ([.mov .r11 (.mem { base := .rsp, disp := 32 })] ++ kEntry.drop 1)) s
        (EntryPost s · (arg s 3)) := by
      rw [← kEntry_split]; exact kEntry_ok rfl hhw c.ha c.hsep
    have e3 : s.gpr .rsp + BitVec.ofInt 64 32 = stackArgAddr s 3 := rfl
    have hB' : s.mem.readW (stackArgAddr s 3) 64 = stackArg s 3 := rfl
    refine WP.mono (WP.and' (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 3)
      (by xrun [State.ea, e3, c.ha 3 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans hs.B, (k.gpr (by decide)).trans hs.rsp, hw⟩
  · -- The zeros to `out` and the length check.
    refine kt_piece (fun p : SharedCPub => p.f.B) (fun p => p.f.wr) [kOut, kLen, kRandLen]
      (fun p => [(kOut, p.f.op), (kLen, BitVec.ofNat 64 (8 * p.f.w)), (kRandLen, BitVec.ofNat 64 p.f.rl)]) []
      (by decide) (fun _ => rfl) ?_ (pins_nil _) (by taint_decide) ?_
    · rintro p t ⟨s, hs, he⟩
      refine ⟨by rw [← hs.B, ← hs.wr]; exact kw_of hs.pre, by rw [he.rdi, hs.B], by rw [he.keep.2.2, hs.wr],
        fun e he' => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl | rfl
      · rw [← hs.B, he.out, hs.op]
      · rw [← hs.B, he.len, ← hs.w, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rw [← hs.B, he.rlen, ← hs.rl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rintro p t ⟨s, hs, he⟩
      exact WP.mono (front_ok (kctx_of hs.pre) he) fun t' hf => ⟨s, t, hs, he, hf⟩
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.cf, h₂.cf]) ?_ ?_
  · -- Too few octets.
    refine kt_ct (fun p : SharedCPub => p.f.B) (fun p => p.f.wr) [kUsedP] (fun p => [(kUsedP, p.f.up)]) [] (by decide)
      (fun _ => rfl) ?_ (pins_nil _) (by taint_decide)
    rintro p t ⟨⟨s, t₁, hs, he, hf⟩, -⟩
    have c := kctx_of hs.pre
    refine ⟨by rw [← hs.B, ← hs.wr]; exact kw_of hs.pre, by rw [hf.keep.gpr (by decide), he.rdi, hs.B],
      by rw [hf.keep.2.2, he.keep.2.2, hs.wr], fun e he' => ?_⟩
    simp only [List.mem_singleton] at he'
    subst he'
    show word t.mem p.f.B (8 * kUsedP) = p.f.up
    rw [← hs.B, hf.word c (i := kUsedP) (by decide), he.usedP, hs.up]
  · exact (sharedKMain_ct M hmc R).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
      ⟨p.fp, h₁.1.k0 (by have := h₁.2; simpa [eval, h₁.1.cf] using this),
        h₂.1.k0 (by have := h₂.2; simpa [eval, h₂.1.cf] using this)⟩) h) fun _ _ h => h

private def sharedCpubOf (s : State) (h : candPre s) : SharedCPub :=
  ⟨cpubOf s, by
    have c := kctx_of h
    have hz := c.hZ
    have hk := c.k8
    have h1 := c.k1
    change slot ((s.gpr .rsi).toNat / 8) 28 ≤ (arg s 4).toNat * 8
    simp only [slot, hdrBytes]
    omega_arith⟩

private theorem shared_crel_self {s : State} (h : sharedCandPre s) :
    SharedCRel (sharedCpubOf s h.1) s := ⟨crel_self h.1, h.2⟩

private theorem shared_crel_of {s t : State} (hs : sharedCandPre s) (ht : sharedCandPre t) (hp : candPub s t) :
    SharedCRel (sharedCpubOf s hs.1) t := by
  have hc := crel_of hs.1 ht.1 hp
  refine ⟨hc, ?_⟩
  change SharedEnv (cpubOf s).f.B (cpubOf s).f.Z (cpubOf s).rsp t
  rw [← hc.B, ← hc.Z, ← hc.rsp]
  exact ht.2

theorem sharedCode_constantTime (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) :
    ConstantTime isa sharedCandPre candPub (codeWith mm R.run) :=
  RelCT.constantTime ((sharedCode_ct M hmc R).mono (fun s _t ⟨hs, ht, hp⟩ =>
    ⟨sharedCpubOf s hs.1, shared_crel_self hs, shared_crel_of hs ht hp⟩) (fun _ _ h => h))

end VG.Proof.RsaKeyGen.X86_64
