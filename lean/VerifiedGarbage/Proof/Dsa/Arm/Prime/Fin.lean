module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr8
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint8
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr11
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Exp7
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont7
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Seqs
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint8
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Trial2
import VerifiedGarbage.Proof.MillerRabin.Arm.Pieces
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Vals

/-! # DSA's probable-prime test on ARMv7: the result

`finish r` writes the octets read in `r3` to `used` and returns `r`
(`finish_vp`). After Miller–Rabin (`mrResult_vp`) its status 0, 1 or 3 is
the test's 0, 1 or 2, with the octets read; a candidate that trial division
rejects returns 2 having read none. Both are the specification's: the status
`statD` and the octets read `usedD` of `probablePrime` (`res`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Proof.MillerRabin.Arm (RoundImpl)

/-- The test's status and the octets it read. -/
def statD (P : CP) (σ : State) : Nat := Proof.Dsa.ProbablePrime.status (res P σ)
def usedD (P : CP) (σ : State) : Nat :=
  match res P σ with
  | some (_, rest) => P.rl - rest.length
  | none => 0

/-- The end: the status `st` and `used`. -/
abbrev RF (P : CP) (E : State → Prop) (st : State → Nat) (used : State → Nat) (σ s : State) : Prop :=
  E σ ∧ Bk P σ s ∧ (s.gpr .r0).toNat = st σ ∧ Spec.Rsa.wordsAt s.mem (State.addr P.uP) 1 = [BitVec.ofNat 64 (used σ)]

theorem finish_eq (r : Nat) : finish r = ([.ldrSp .r2 foUsed] : List Instr) ++ finTail r := rfl

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

theorem In.uW {σ : State} (pre : In P σ) : P.rU ∈ σ.wr := by rw [pre.wr]; simp

/-- `used := r3`, and `r` returned. -/
theorem finish_vp {r : Nat} {u : State → Nat}
    (cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r2]) (.block (finTail r)) hc).isSome = true)
    (henc : encodable (BitVec.ofNat 32 r) = true) (hr : r < 2 ^ 32) :
    VP (fun σ s => (E σ ∧ Bk P σ s) ∧ s.gpr .r3 = BitVec.ofNat 32 (u σ) ∧ u σ < 2 ^ 32)
      (.block (finish r)) (RF P E (fun _ => r) u) := by
  rw [finish_eq]
  refine VP.block_append (G := fun σ s => ((E σ ∧ Bk P σ s) ∧
    s.gpr .r3 = BitVec.ofNat 32 (u σ) ∧ u σ < 2 ^ 32) ∧ s.gpr .r2 = P.uP) ?_ ?_
  · show VP _ (.block ([(Reg.r2, foUsed)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h⟩, p3, hu⟩ => ?_
    · rw [h₁.1.2.sp, h₁.1.2.pre.sp, h₂.1.2.sp, h₂.1.2.pre.sp]
    refine h.ldrSp (o := foUsed) (by decide) fun t u1 => WP.block_nil ⟨⟨⟨e, h.of_upd u1⟩,
      by rw [u1.other _ (by decide), p3], hu⟩, by rw [u1.gpr, h.pre.wU]⟩
  · refine VP.taint [.r2] cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨⟨e, h⟩, p3, hu⟩, p2⟩ => ?_
    · simp only [List.mem_singleton]; rintro r rfl; rw [h₁.2, h₂.2]
    have pre := h.pre
    have fU := pre.fU
    have wa : InRegions s.wr (State.addr P.uP) 4 :=
      ⟨_, by rw [h.wr]; exact pre.uW, by
        simpa using Offset.contains_base (State.addr P.uP) (d := 0) (n := 4) (k := 8) (by decide) (by decide)⟩
    have wb : InRegions s.wr (State.addr P.uP + BitVec.ofNat 64 4) 4 :=
      ⟨_, by rw [h.wr]; exact pre.uW, Offset.contains_base (State.addr P.uP) (d := 4) (n := 4) (k := 8) (by decide)
        (by decide)⟩
    refine wp_str (a := State.addr P.uP) (by decide) (by rw [p2, BitVec.add_zero]) wa fun s1 m1 => ?_
    refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
    refine wp_str (a := State.addr P.uP + BitVec.ofNat 64 4) (by decide)
      (by rw [u2.other _ (by decide), m1.gpr, p2]; exact addr_add (by omega)) (by rw [u2.wr, m1.wr]; exact wb)
      fun s3 m3 => ?_
    refine wp_mov (op2_imm henc) fun t u4 => WP.block_nil ?_
    have mt : t.mem = s.mem.writeW (State.addr P.uP) (0#32 ++ BitVec.ofNat 32 (u σ)) := by
      rw [u4.mem, m3.mem, u2.gpr, u2.mem, m1.mem, ← p3, VG.Proof.Rc2.Word32.write64_pair]
      rfl
    have fr : Frame [P.rU] s.mem t.mem := by
      rw [mt]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have rt : Rest [.r0, .r1] s t := (m1.rest _).trans ((u2.rest (by simp)).trans ((m3.rest _).trans (u4.rest (by simp))))
    refine ⟨e, h.of_frame (fr.mono fun r' hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
      rt.sp rt.rd rt.wr, ?_, ?_⟩
    · rw [u4.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
      rw [mt, Mem.readW_writeW_self64]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]
      simp
      omega

theorem slot_lt (m : Mem) (B : BitVec 32) (d : Nat) : slot m B d < 2 ^ 32 := by
  simp only [slot, w32]; exact BitVec.isLt _

/-- The status from Miller–Rabin's result. -/
def statS : Option (Bool × Spec.RsaKeyGen.Rand) → Nat
  | none => 0
  | some (true, _) => 1
  | some (false, _) => 3

theorem statQ_eq {σ : State} (pre : In P σ) : statQ P σ = statS (resQ P) := by
  unfold statQ; rw [resP_eq pre]
  rcases resQ P with _ | ⟨_ | _, _⟩ <;> rfl

theorem statS_vals (x : Option (Bool × Spec.RsaKeyGen.Rand)) : statS x = 0 ∨ statS x = 1 ∨ statS x = 3 := by
  rcases x with _ | ⟨_ | _, _⟩ <;> simp [statS]

/-- The comparison of `sStat` with `c`, keeping `X`. -/
theorem statCmp_vp {c : BitVec 32} {k : Nat} {X : State → State → Prop}
    (cert : Cert (.block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm c)]))
    (hc : encodable c = true) (hz : ∀ v ∈ [0, 1, 3], (BitVec.ofNat 32 v - c == 0) = decide (v = k))
    (hX : ∀ σ s t, X σ s → t.mem = s.mem → Rest [.r1] s t → X σ t) :
    VP (fun σ s => QS P E σ s ∧ X σ s) (.block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm c)])
      (fun σ s => (QS P E σ s ∧ X σ s) ∧ s.z = decide (statQ P σ = k)) :=
  VP.kv cert (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, x⟩ => by
    refine h.ldr hw (d := sStat) (by simp) (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
    refine wp_cmp (op2_imm hc) fun t f z => WP.block_nil ⟨⟨⟨e, h1.of_rest (f.rest []) f.mem,
      hw1.of (by rw [f.gpr]) (by rw [f.gpr]) (by rw [f.gpr]) f.wr⟩,
      hX σ s t x (by rw [f.mem, u1.mem]) ((u1.rest (by simp)).trans (f.rest [.r1]))⟩, ?_⟩
    rw [z, u1.gpr]
    simp only [upd_self]
    unfold statQ
    split
    · exact hz 0 (by simp)
    · exact hz 1 (by simp)
    · exact hz 3 (by simp)

theorem stat_of {σ s : State} {k : Nat} (pre : In P σ) (z : s.z = decide (statQ P σ = k))
    {b : Bool} (t : isa.eval .eq s = some b) : decide (statS (resQ P) = k) = b := by
  rw [isa_eq, z, statQ_eq pre] at t
  simpa using t

/-- The test's result is the public one. -/
theorem res_eq (hE : ∀ σ, E σ → In P σ ∧ EM P σ) {σ : State} (e : E σ) : res P σ = resQ P := by
  rw [(mr_facts (hE σ e).1 (hE σ e).2).1, resP_eq (hE σ e).1]

theorem usedQ_some {σ : State} (pre : In P σ) {b : Bool} {r : Spec.RsaKeyGen.Rand} (h : resQ P = some (b, r)) :
    usedQ P σ = P.rl - r.length := by
  unfold usedQ; rw [resP_eq pre, h]

/-- `r3 := [sUsed]` and the comparison of the status with 1. -/
theorem usedCmp_vp :
    VP (QS P E) (.block [.ldr .r3 .r8 sUsed, .ldr .r1 .r8 sStat, .cmp .r1 (.imm 1)])
      (fun σ s => (QS P E σ s ∧ s.gpr .r3 = BitVec.ofNat 32 (usedQ P σ)) ∧ s.z = decide (statQ P σ = 1)) := by
  show VP _ (.block (([.ldr .r3 .r8 sUsed] : List Instr) ++ [.ldr .r1 .r8 sStat, .cmp .r1 (.imm 1)])) _
  refine VP.block_append (VP.kv ldrUsed_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ =>
    h.ldr hw (d := sUsed) (by simp) (r := .r3) (by decide) fun t ht hwt u => WP.block_nil
      ⟨⟨e, ht, hwt⟩, by rw [u.gpr]; simp (config := {decide := true}) only [upd, ↓reduceIte]⟩)
    (statCmp_vp stat1_cmp_taint (by decide) (by decide) fun σ s t x _ r => by rw [r.gpr _ (by decide), x])

/-- The end from `QS`, with `r3 := u`. -/
theorem qsFinish_vp {r : Nat} {u : State → Nat} {X : State → State → Prop}
    (cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r2]) (.block (finTail r)) hc).isSome = true)
    (henc : encodable (BitVec.ofNat 32 r) = true) (hr : r < 2 ^ 32) (hu : ∀ σ, E σ → u σ < 2 ^ 32)
    (hst : ∀ σ, E σ → statD P σ = r) (hus : ∀ σ, E σ → usedD P σ = u σ) :
    VP (fun σ s => QS P E σ s ∧ s.gpr .r3 = BitVec.ofNat 32 (u σ) ∧ X σ s) (.block (finish r))
      (RF P E (statD P) (usedD P)) :=
  (finish_vp cert henc hr).mono (fun σ s ⟨⟨e, h, _⟩, p3, _⟩ => ⟨⟨e, h.bk⟩, p3, hu σ e⟩)
    fun σ s ⟨e, b, r0, w⟩ => ⟨e, b, by rw [r0, hst σ e], by rw [w, hus σ e]⟩

/-- Miller–Rabin's result. -/
theorem mrResult_vp (hE : ∀ σ, E σ → In P σ ∧ EM P σ) :
    VP (QS P E) Impl.Dsa.Arm.ProbablePrime.mrResult (RF P E (statD P) (usedD P)) := by
  have hs : ∀ σ, E σ → statD P σ = Proof.Dsa.ProbablePrime.status (resQ P) := fun σ e => by
    unfold statD; rw [res_eq hE e]
  have hu : ∀ σ, E σ → usedD P σ = match resQ P with | some (_, rest) => P.rl - rest.length | none => 0 :=
    fun σ e => by unfold usedD; rw [res_eq hE e]
  simp only [Impl.Dsa.Arm.ProbablePrime.mrResult]
  refine VP.seq (G := fun σ s => QS P E σ s ∧ s.z = decide (statQ P σ = 0))
    ((statCmp_vp (X := fun _ _ => True) (k := 0) stat0_cmp_taint (by decide) (by decide)
      fun _ _ _ _ _ _ => trivial).mono (fun σ s h => ⟨h, trivial⟩) fun _ _ h => ⟨h.1.1, h.2⟩) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · rw [isa_eq, isa_eq, h₁.2, h₂.2, statQ_eq (hE σ₁ h₁.1.1).1, statQ_eq (hE σ₂ h₂.1.1).1]
  · refine VP.ofImp (p := statS (resQ P) = 0) (fun σ s h => by
      have := stat_of (hE σ h.1.1.1).1 h.1.2 h.2; simpa using this) fun h0 => ?_
    have hn : resQ P = none := by
      revert h0; rcases resQ P with _ | ⟨_ | _, _⟩ <;> simp [statS]
    refine VP.block_append (G := fun σ s => QS P E σ s ∧ s.gpr .r3 = BitVec.ofNat 32 0 ∧ True)
      (VP.taint [] mov30_taint (fun _ _ _ _ _ _ r hr => absurd hr List.not_mem_nil)
        fun σ s ⟨⟨⟨e, h, hw⟩, _⟩, _⟩ => wp_mov (op2_imm (by decide)) fun t u => WP.block_nil
          ⟨⟨e, h.of_rest (u.rest (ws := [.r3]) (by simp)) u.mem, hw.of_upd u (by decide) (by decide) (by decide)⟩, u.gpr, trivial⟩)
      (qsFinish_vp (u := fun _ => 0) finTail0_taint (by decide) (by decide) (fun _ _ => by decide)
        (fun σ e => by rw [hs σ e, hn]; rfl) fun σ e => by rw [hu σ e, hn])
  · refine VP.ofImp (p := statS (resQ P) ≠ 0) (fun σ s h => by
      have := stat_of (hE σ h.1.1.1).1 h.1.2 h.2; simpa using this) fun hs0 => ?_
    obtain ⟨b, rest, hq⟩ : ∃ b rest, resQ P = some (b, rest) := by
      revert hs0; rcases resQ P with _ | ⟨b, rest⟩ <;> simp [statS]
    have hul : ∀ σ, E σ → usedQ P σ < 2 ^ 32 := fun σ e => by
      rw [usedQ_some (hE σ e).1 hq]; have := (hE σ e).1.rlt; omega
    have hus : ∀ σ, E σ → usedD P σ = usedQ P σ := fun σ e => by
      rw [hu σ e, hq, usedQ_some (hE σ e).1 hq]
    refine VP.seq (usedCmp_vp.mono (fun σ s h => h.1.1) fun _ _ h => h) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) ?_ ?_
    · rw [isa_eq, isa_eq, h₁.2, h₂.2, statQ_eq (hE σ₁ h₁.1.1.1).1, statQ_eq (hE σ₂ h₂.1.1.1).1]
    · refine VP.ofImp (p := b = true) (fun σ s h => by
        have := stat_of (hE σ h.1.1.1.1).1 h.1.2 h.2; rw [hq] at this
        revert this; cases b <;> simp [statS]) fun hb => ?_
      subst hb
      exact qsFinish_vp (X := fun _ _ => True) finTail1_taint (by decide) (by decide) hul
        (fun σ e => by rw [hs σ e, hq]; rfl) hus |>.mono (fun σ s h => ⟨h.1.1.1, h.1.1.2, trivial⟩) fun _ _ h => h
    · refine VP.ofImp (p := b = false) (fun σ s h => by
        have := stat_of (hE σ h.1.1.1.1).1 h.1.2 h.2; rw [hq] at this
        revert this; cases b <;> simp [statS]) fun hb => ?_
      subst hb
      exact qsFinish_vp (X := fun _ _ => True) finTail2_taint (by decide) (by decide) hul
        (fun σ e => by rw [hs σ e, hq]; rfl) hus |>.mono (fun σ s h => ⟨h.1.1.1, h.1.1.2, trivial⟩) fun _ _ h => h

/-- Once the candidate passed trial division. -/
theorem mrPart_vp (v : RoundImpl) (hE : ∀ σ, E σ → In P σ ∧ EM P σ) :
    VP (S2 P E) (Impl.Dsa.Arm.ProbablePrime.mrPart v.name v.code) (RF P E (statD P) (usedD P)) :=
  VP.seqs_app (a := [sub3 aCm1 aC aOne]) (List.cons_ne_nil _ _) (by simp) cm1_vp
    (VP.seqs_app (b := [montA, montB, Impl.Dsa.Arm.ProbablePrime.millerRabin v.name v.code,
        Impl.Dsa.Arm.ProbablePrime.mrResult]) (by simp [expSetup]) (List.cons_ne_nil _ _)
      (expSetup_vp fun σ e => (hE σ e).1)
      (montA_vp.seq (montB_vp.seq ((millerRabin_vp v hE).seq (mrResult_vp hE)))))

/-- Trial division rejected the candidate: 2, having read nothing. -/
theorem composite_vp (hE : ∀ σ, E σ → In P σ ∧ compv P σ = true) :
    VP (S2 P E) (.block (([.mov .r3 (.imm 0)] : List Instr) ++ Impl.Dsa.Arm.ProbablePrime.done 2)) (RF P E (statD P) (usedD P)) := by
  have hr : ∀ σ, E σ → res P σ = some (false, rB P σ) := fun σ e => by
    have pre := (hE σ e).1
    have sz := pre.sizes
    obtain ⟨hodd, hlo, -⟩ := cv_shape (σ := σ) pre
    have h3 : 3 < cv P σ := by
      have : 2 ^ 2 ≤ 2 ^ (P.bits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    unfold res
    rw [VG.Proof.Dsa.Generation.probablePrime_large h3 hodd, pre.bl]
    have hc := (hE σ e).2
    unfold compv at hc
    rw [hc]; rfl
  refine VP.block_append (G := fun σ s => (E σ ∧ Bk P σ s) ∧ s.gpr .r3 = BitVec.ofNat 32 0 ∧ 0 < 2 ^ 32)
    (VP.taint [] mov30_taint (fun _ _ _ _ _ _ r hr => absurd hr List.not_mem_nil)
      fun σ s ⟨e, h, _⟩ => wp_mov (op2_imm (by decide)) fun t u => WP.block_nil
        ⟨⟨e, h.bk.of_upd u⟩, u.gpr, by decide⟩)
    ((finish_vp (u := fun _ => 0) finTail2_taint (by decide) (by decide)).mono (fun _ _ h => h)
      fun σ s ⟨e, b, r0, w⟩ => ⟨e, b, by rw [r0]; unfold statD; rw [hr σ e]; rfl, by
        rw [w]; unfold usedD; rw [hr σ e]; simp only [rB_length, Nat.sub_self]⟩)

end

end VG.Proof.Dsa.Arm.Prime
