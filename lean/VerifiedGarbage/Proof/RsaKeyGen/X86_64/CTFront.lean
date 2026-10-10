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

/-! ## The schedule -/

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
  ⟨by have := h.z; unfold slot aTab at *; dsimp only; omega_arith, by have := h.z; unfold slot aTab aRm1 at *; dsimp only; omega_arith,
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
  · refine h.step ⟨mi, hgt⟩ hf (by simp only [closeRanges]; rng_le) (fun r hr => ?_) (by simp only [closeRanges]; rng_disj) k
    have : r.1 + r.2 ≤ slot q.w aTab + 2048 := by revert r hr; simp only [closeRanges]; rng_le
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
  · refine h.step ⟨mi, hgt⟩ hf (by rng_le) (fun r hr => ?_) (by rng_disj) k
    have : r.1 + r.2 ≤ slot q.w aTab + 2048 := by revert r hr; rng_le
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
  · refine h.step ⟨mi, hgt⟩ hf (by rng_le) (fun r hr => ?_) (by rng_disj) k
    have : r.1 + r.2 ≤ slot q.w aTab + 2048 := by revert r hr; rng_le
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

/-- Everything after `loadC` leaks the same in runs that agree on the public
data and the schedule. -/
theorem afterLoad_ct (M : Mont) : RelCT isa (Two KSt) (seqs (closeCheck ++ ([.ite .ne (finUsed 2) (seqs (trial ++
    ([.ite .ne (finUsed 3) (seqs (gcdCheck ++
      ([.ite .ne (finUsed 3) (seqs (montSetup M.mm ++ millerRabin M.mm ++ [mrResult]))] : List (Prog isa))))] : List (Prog isa))))] : List (Prog isa)))) fun _ _ => True := by
  refine RelCT.seqs_app (by simp [closeCheck]) (by simp) (RelCT.seq (R := Two fun q s => KSt q s ∧
    s.zf = some (!q.sch.close)) (two_post closeCheck_ct fun _ _ h => closeStage_ok h) ?_)
  simp only [seqs]
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) (finUsed2_ct fun _ _ h => h.1.1) ?_
  refine RelCT.seqs_app (by simp [trial]) (by simp) (RelCT.seq (R := Two fun q s => (KSt q s ∧
    s.zf = some (!q.sch.comp)) ∧ q.sch.close = false) (two_post (trial_ct fun _ _ h => h.1.1) fun q s h => ?_) ?_)
  · have hcl := ne_false h.1.2 h.2
    exact WP.mono (trialStage_ok h.1.1 hcl) fun t ht => ⟨ht, hcl⟩
  simp only [seqs]
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2, h₂.1.2]) (finUsed3_ct fun _ _ h => h.1.1.1) ?_
  refine RelCT.seqs_app (by simp [gcdCheck, loadE]) (by simp) (RelCT.seq (R := Two fun q s => (KSt q s ∧
    s.zf = some (!q.sch.gbad)) ∧ q.sch.close = false ∧ q.sch.comp = false)
      (two_post (gcdCheck_ct fun _ _ h => h.1.1.1) fun q s h => ?_) ?_)
  · have hco := ne_false h.1.1.2 h.2
    exact WP.mono (gcdStage_ok h.1.1.1 h.1.2 hco) fun t ht => ⟨ht, h.1.2, hco⟩
  simp only [seqs]
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2, h₂.1.2]) (finUsed3_ct fun _ _ h => h.1.1.1) ?_
  refine (tail_ct M).mono (fun _ _ h => two_bind (fun q _ _ h₁ h₂ =>
    ⟨q.tp, tailPre h₁.1.1.1 h₁.1.2.1 h₁.1.2.2 (ne_false h₁.1.1.2 h₁.2),
      tailPre h₂.1.1.1 h₂.1.2.1 h₂.1.2.2 (ne_false h₂.1.1.2 h₂.2)⟩) h) fun _ _ h => h

/-! ## `loadC`, and `kMain` -/

/-- The arguments' header words. -/
def avs0 (q : FPub) : List (Nat × BitVec 64) :=
  [(kOut, q.op), (kLen, BitVec.ofNat 64 (8 * q.w)), (kUsedP, q.up), (kE, q.eP),
    (kElen, BitVec.ofNat 64 q.eB.length), (kP, q.pP), (kPlen, BitVec.ofNat 64 q.pl), (kRand, q.rP),
    (kRandLen, BitVec.ofNat 64 q.rl)]

def aS0 : List Nat := [kOut, kLen, kUsedP, kE, kElen, kP, kPlen, kRand, kRandLen]

/-- Before `loadC`: what `kMain_ok` needs, for the public data. -/
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
    simp only [loadCRanges]
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj
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

/-- `kMain` leaks the same in runs that agree on the public data. -/
theorem kMain_ct (M : Mont) : RelCT isa (Two K0) (kMain M.mm) fun _ _ => True := by
  rw [kMain_eq]
  exact RelCT.seqs_app (by simp [loadC]) (by simp [closeCheck])
    (RelCT.seq (two_post loadC_ct fun _ _ h => loadCStage_ok h) (afterLoad_ct M))

end VG.Proof.RsaKeyGen.X86_64
