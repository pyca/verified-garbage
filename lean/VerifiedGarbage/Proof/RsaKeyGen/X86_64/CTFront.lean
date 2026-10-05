import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# A candidate on x86-64: the stages before Montgomery setup

After `loadC`, every stage keeps `KSt`: `Good`, the arguments' header words,
the candidate in `aN` and the buffers, for public data `FPub` that includes
the schedule (`schedOf`) the leak fixes. Each stage is proven constant time
with a weak postcondition, then `two_post` recovers `KSt` (and the flag the
branch after it tests) from its correctness.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
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

/-! ## The schedule -/

theorem sched_close (L e : Nat) (p : Option Nat) (r : List Byte) :
    (schedOf L e p r).close =
      Spec.RsaKeyGen.tooClose (8 * L) p (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L))) := by
  unfold schedOf; dsimp only
  cases h : Spec.RsaKeyGen.tooClose (8 * L) p (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L)))
  · simp only [Bool.false_eq_true, ↓reduceIte]; split <;> (try split) <;> rfl
  · rfl

theorem sched_comp {L e : Nat} {p : Option Nat} {r : List Byte}
    (h : Spec.RsaKeyGen.tooClose (8 * L) p (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L))) = false) :
    (schedOf L e p r).comp =
      Spec.RsaKeyGen.obviouslyComposite (8 * L) (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L))) := by
  unfold schedOf; dsimp only; rw [h]; simp only [Bool.false_eq_true, ↓reduceIte]
  cases h' : Spec.RsaKeyGen.obviouslyComposite (8 * L) (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L)))
  · simp only [Bool.false_eq_true, ↓reduceIte]; split <;> rfl
  · rfl

theorem sched_gbad {L e : Nat} {p : Option Nat} {r : List Byte}
    (h : Spec.RsaKeyGen.tooClose (8 * L) p (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L))) = false)
    (h' : Spec.RsaKeyGen.obviouslyComposite (8 * L)
      (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L))) = false) :
    (schedOf L e p r).gbad =
      !(Nat.gcd (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L)) - 1) e == 1) := by
  unfold schedOf; dsimp only; rw [h, h']; simp only [Bool.false_eq_true, ↓reduceIte]
  cases h'' : !(Nat.gcd (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L)) - 1) e == 1)
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · rfl

theorem sched_mr {L e : Nat} {p : Option Nat} {r : List Byte}
    (h : Spec.RsaKeyGen.tooClose (8 * L) p (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L))) = false)
    (h' : Spec.RsaKeyGen.obviouslyComposite (8 * L)
      (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L))) = false)
    (h'' : (!(Nat.gcd (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L)) - 1) e == 1)) = false) :
    (schedOf L e p r).mr =
      shapeOf (Spec.RsaKeyGen.primalityTest (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L)))
        (r.drop L)) := by
  unfold schedOf; dsimp only; rw [h, h', h'']; rfl

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
  w4 : 4 ≤ q.w
  w64 : q.w ≤ 64
  rl : q.rl < 2 ^ 64
  rk : 8 * q.w ≤ q.rl
  el1 : 1 ≤ q.eB.length
  el8 : q.eB.length ≤ 8
  pl : q.pl = 0 ∨ q.pl = 8 * q.w

theorem FDims.td {q : FPub} (h : FDims q) : TDims q.tp :=
  ⟨by have := h.z; unfold slot aTab at *; dsimp only; omega, by have := h.z; unfold slot aTab aRm1 at *; dsimp only; omega,
    h.w4, h.w64⟩

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
    rw [hf.word_eq (fun r hr => Or.inl (by have := h208 r hr; omega)) (by omega)]; exact ha e he
  · rw [hf.wv_eq hN (by unfold slot aTab at *; omega)]; exact hc

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
  VG.Proof.RsaKeyGen.candidate_shape (by omega) _

theorem cand_gt {w : Nat} (hw : 4 ≤ w) (x : Nat) : 8161 < Spec.RsaKeyGen.candidate (64 * w) x := by
  obtain ⟨_, hlo, _⟩ := cand_shape hw x
  have : 2 ^ 13 ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- `closeCheck`, from `KSt`: ZF clear iff the candidate is too close. -/
theorem closeStage_ok {q : FPub} {s : State} (h : KSt q s) :
    WP isa (seqs closeCheck) s fun t => KSt q t ∧ t.zf = some (!q.sch.close) := by
  obtain ⟨mi, pB, r, hg, ha, hc, hp, -, -, hpl, -, hS⟩ := h.cand
  have hd := h.2.2.1
  have hz := hd.z
  have hw4 := hd.w4
  have hZ : slot q.w 8 ≤ q.Z := by unfold slot aTab at *; omega
  have hsch : q.sch.close = Spec.RsaKeyGen.tooClose (64 * q.w) (Spec.RsaKeyGen.otherPrime pB)
      (Spec.RsaKeyGen.candidate (64 * q.w) (Spec.Rsa.os2ip (r.take (8 * q.w)))) := by
    rw [← hS, sched_close, show 8 * (8 * q.w) = 64 * q.w by omega]
  have ha' := avsW_of ha
  refine WP.mono (closeCheck_ok hg hZ hw4 hd.w64 ha'.p ha'.len (by rw [hpl]; exact ha'.plen)
    (by rw [hpl]; exact hd.pl) hp) fun t ⟨hzf, hgt, hf, k⟩ => ⟨?_, ?_⟩
  · refine h.step ⟨mi, hgt⟩ hf (by simp only [closeRanges]; rng_le) (fun r hr => ?_) (by simp only [closeRanges]; rng_disj) k
    have : r.1 + r.2 ≤ slot q.w aTab + 2048 := by revert r hr; simp only [closeRanges]; rng_le
    omega
  · rw [hzf, hc, hsch]

/-- `trial`, from `KSt` and a candidate not too close: ZF clear iff it is
obviously composite. -/
theorem trialStage_ok {q : FPub} {s : State} (h : KSt q s) (hcl : q.sch.close = false) :
    WP isa (seqs trial) s fun t => KSt q t ∧ t.zf = some (!q.sch.comp) := by
  obtain ⟨mi, pB, r, hg, -, hc, -, -, -, -, -, hS⟩ := h.cand
  have hd := h.2.2.1
  have hz := hd.z
  have hw4 := hd.w4
  have hZ : slot q.w 8 ≤ q.Z := by unfold slot aTab at *; omega
  have hcl' := hcl
  rw [← hS, sched_close] at hcl'
  have hsch : q.sch.comp = Spec.RsaKeyGen.obviouslyComposite (64 * q.w)
      (Spec.RsaKeyGen.candidate (64 * q.w) (Spec.Rsa.os2ip (r.take (8 * q.w)))) := by
    rw [← hS, sched_comp hcl', show 8 * (8 * q.w) = 64 * q.w by omega]
  refine WP.mono (trial_ok hg hZ hz (by omega) hd.w64) fun t ⟨hzf, hgt, hf, k⟩ => ⟨?_, ?_⟩
  · refine h.step ⟨mi, hgt⟩ hf (by rng_le) (fun r hr => ?_) (by rng_disj) k
    have : r.1 + r.2 ≤ slot q.w aTab + 2048 := by revert r hr; rng_le
    omega
  · rw [hzf, hc, trialAny_eq (cand_gt hw4 _), hsch]

/-- `gcdCheck`, from `KSt` and a candidate neither too close nor obviously
composite: ZF set iff `gcd(c − 1, e) = 1`. -/
theorem gcdStage_ok {q : FPub} {s : State} (h : KSt q s) (hcl : q.sch.close = false) (hco : q.sch.comp = false) :
    WP isa (seqs gcdCheck) s fun t => KSt q t ∧ t.zf = some (!q.sch.gbad) := by
  obtain ⟨mi, pB, r, hg, ha, hc, -, he, -, -, -, hS⟩ := h.cand
  have hd := h.2.2.1
  have hz := hd.z
  have hw4 := hd.w4
  have hZ : slot q.w 8 ≤ q.Z := by unfold slot aTab at *; omega
  have hcl' := hcl
  rw [← hS, sched_close] at hcl'
  have hco' := hco
  rw [← hS, sched_comp hcl'] at hco'
  have hsch : q.sch.gbad = !(Nat.gcd (Spec.RsaKeyGen.candidate (64 * q.w) (Spec.Rsa.os2ip (r.take (8 * q.w))) - 1)
      (Spec.Rsa.os2ip q.eB) == 1) := by
    rw [← hS, sched_gbad hcl' hco', show 8 * (8 * q.w) = 64 * q.w by omega]
  obtain ⟨hodd, -, -⟩ := cand_shape hw4 (Spec.Rsa.os2ip (r.take (8 * q.w)))
  have h3 := cand_gt hw4 (Spec.Rsa.os2ip (r.take (8 * q.w)))
  have ha' := avsW_of ha
  have := hd.w64
  refine WP.mono (gcdCheck_ok hg hZ (by omega) (by omega) (by rw [hc]; exact hodd) (by rw [hc]; omega)
    ha'.e ha'.elen hd.el1 hd.el8 he) fun t ⟨hzf, hgt, hf, k⟩ => ⟨?_, ?_⟩
  · refine h.step ⟨mi, hgt⟩ hf (by rng_le) (fun r hr => ?_) (by rng_disj) k
    have : r.1 + r.2 ≤ slot q.w aTab + 2048 := by revert r hr; rng_le
    omega
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
    rw [VG.Proof.RsaKeyGen.primalityTest_cand (by omega) hsh, checksW_eq q.w (by have := hd.w64; omega) hw4]
  have ha' := avsW_of ha
  refine ⟨h.gw, hd.rl, mi, _, r, hg, hc, hsh, ha'.out, ha'.usedP, ha'.rand, ha'.len, by rw [hrl]; exact ha'.rlen,
    ha'.used, hr, hrl,
    by rw [hrl]; exact hd.rk, ?_⟩
  rw [hres]
  have := sched_mr hcl' hco' hgb'
  rw [hS, show 8 * (8 * q.w) = 64 * q.w by omega] at this
  exact this.symm

end VG.Proof.RsaKeyGen.X86_64
