module

public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCT
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignFront
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignFront
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# DSA signing on RISC-V: constant time, the levels

`vg_dsa_sign` (`Sign.sign`) runs `Sign.entry`, then `checkKey` with
`Sign.body` or `Sign.zeroOut`, then `restore`. Its public data (`vdS`) is
the key's public octets (p||q||g||y), the nonce's and the digest's addresses
and lengths, and `out`, which the header keeps. The entry loads `scratch`'s
address from the stack, as verification's does (`sentry_rel`). Its levels
are validation's (`ValidateCT.lean`), each failing to `zeroOut`
(`szero_rel`, cut after its loads of the header), up to y's check, whose
passing side is `body`, its relation a hypothesis here.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv take_split)

/-! ## The failing side: `zeroOut` -/

/-- `zeroOut`'s loads of the header. -/
abbrev ZHs : List Instr := [.load .d .t4 .s6 Sign.hOut] ++ getQ .t5 ++ ([.add .t5 .t5 .t5, .li .s0 0] : List Instr)

abbrev FZs : List (Prog isa) := Code.flat Sign.zeroOut

theorem szhead_ok {v : VD} {s : State} (B : Base v s) (ho : v.out = some (oOf v)) :
    WP isa (.block ZHs) s (Fix [(.t4, oOf v), (.t5, BitVec.ofNat 64 (2 * v.L.ql))]) := by
  have hL := B.ok
  obtain ⟨hin24, hal24⟩ := ScrL.hdr B.scr hL (d := 24) (by decide) (by decide)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.t4] (Q := fun u => u.gpr .t4 = oOf v ∧ u.mem = s.mem)
    (by brun [Sign.hOut, B.regs.s6, hin24, hal24]; exact B.hout _ ho) (by decide) (by rfl))
    fun u ⟨⟨a4, mu⟩, ku⟩ => ?_
  have Bu := B.keepM ku mu
  refine WP.mono (getQ_ok Bu.scr hL Bu.regs .t5) fun w ⟨⟨b5, mw⟩, kw⟩ => ?_
  refine WP.mono (WP.keep [.t5, .s0] (Q := fun u => u.gpr .t5 = BitVec.ofNat 64 (2 * v.L.ql))
    (by
      brun [b5, exec_li_zero]
      simp only [BitVec.ofNat_add_ofNat]; congr 1; omega) (by decide) (by rfl)) fun t ⟨a5, kt⟩ => ?_
  exact ⟨(kt.gpr (r := .t4) (by decide)).trans ((kw.gpr (r := .t4) (by decide)).trans a4), a5, trivial⟩

/-- `zeroOut`, from a level whose states keep `out` in the header. -/
theorem szero_rel {Φ : VD → State → Prop} (hrun : ∀ v s, Φ v s → WP isa (Code.seqL FZs) s fun _ => True)
    (hB : ∀ v s, Φ v s → Base v s) (hO : ∀ v s, Φ v s → v.out = some (oOf v)) :
    RelCT isa (Two Φ) Sign.zeroOut fun _ _ => True :=
  chain_start (chain_cons hrun (m := 1) (by decide)
    (two_taint _ (pins_at_fix (rs := [.s6, .s11, .ra]) fixB (fun _ => rfl) fun _ _ h => ⟨[], _, .block rfl, (hB _ _ h).fixB⟩)
      (by taint_decide))
    (two_taint _ (pins_at_fix (rs := [.t4, .t5]) (fun v => [(.t4, oOf v),
        (.t5, BitVec.ofNat 64 (2 * v.L.ql))]) (fun _ => rfl) fun _ _ h =>
      WP.of_flat (c := .block ZHs) rfl (szhead_ok (hB _ _ h) (hO _ _ h))) (by taint_decide)))

/-! ## The entry -/

/-- A call's public data. -/
def vdS (s : State) : VD :=
  ⟨slayOf s, s.gpr .a2, s.gpr .a5, s.gpr .a7, (stackArg s 0).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .a2) (3 * (s.gpr .a4).toNat + (s.gpr .a6).toNat),
    3 * (s.gpr .a4).toNat + (s.gpr .a6).toNat, (s.gpr .a6).toNat, true, some (s.gpr .a0)⟩

/-- The contract's buffers are apart from `scratch`. -/
theorem ssrc {s : State} {A : Addr} {n k : Nat} (hm : (⟨A, n⟩ : Region) ∈ s.rd)
    (hd : (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩) (hn : n < 2 ^ 64) (hk : k ≤ n)
    {t : State} (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Src t (slayOf s) A k :=
  ⟨fun i hi => ⟨_, by rw [hr, hw]; exact List.mem_append_left _ hm,
    Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun i hi => Pub.ne_of_disjoint hd (by omega_arith) i (by omega_arith)⟩

/-- On entry. -/
def C0s (v : VD) (s : State) : Prop := sContract.pre s ∧ vdS s = v

theorem frontS : ∀ v s, C0s v s → WP isa (.block Sign.entry) s (P0 v) := by
  rintro _ s ⟨h, rfl⟩
  have hL := slayOf_ok h
  have hZ := hL.z256
  have hpre := h
  obtain ⟨hrd, -, -, -, -, -, -, dKS, dNS, dDS, -, -, -, -, -, -, -, -, hkl, -, -, -⟩ := h
  refine WP.mono (sfront_ok hpre) fun t ⟨F, k⟩ => ?_
  have hK : Src t (slayOf s) (s.gpr .a2) (3 * (s.gpr .a4).toNat + (s.gpr .a6).toNat) :=
    ssrc (by rw [hrd]; simp) dKS (s.gpr .a3).isLt (by omega) k.2.1 k.2.2
  exact ⟨⟨hL, F.regs, F.scr, hK, ssrc (by rw [hrd]; simp) dNS (s.gpr .a6).isLt (Nat.le_refl _) k.2.1 k.2.2,
    ssrc (by rw [hrd]; simp) dDS (stackArg s 0).isLt (Nat.min_le_left _ _) k.2.1 k.2.2,
    hK.bytes F.out (by simp only [slayOf] at hZ ⊢; omega),
    (by simp only [vdS, slayOf]; omega), (fun _ => F.dig), fun o ho => by cases ho; exact F.outw⟩, F.lens⟩

theorem outS : ∀ v s, C0s v s → v.out = some (oOf v) := by
  rintro _ s ⟨-, rfl⟩
  rfl

theorem kyC0s : ∀ v s, C0s v s → KY v := by
  rintro _ s ⟨-, rfl⟩
  exact Nat.le_refl _

/-- After loading `scratch`'s address. -/
def L1s (v : VD) (s : State) : Prop := s.gpr .t2 = v.L.S

theorem loadS_L1s {v : VD} {s : State} (h : C0s v s) :
    WP isa (.block [.addSp .t2 8, .load .d .t2 .t2 0]) s (L1s v) := by
  obtain ⟨hp, rfl⟩ := h
  obtain ⟨hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, sp16⟩ := hp
  have hld8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 :=
    ⟨sStackArgs s, List.mem_append_left _ (by rw [hrd]; simp), by
      simp only [Region.Contains, stackArgAddr, Nat.mul_zero, add_ofNat_zero]
      rw [show s.sp + BitVec.ofNat 64 8 - s.sp = BitVec.ofNat 64 8 by rw [BitVec.add_comm, BitVec.add_sub_cancel]]; decide⟩
  have hal8 : (s.sp + BitVec.ofNat 64 8).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hv8 : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = stackArg s 1 := rfl
  have first : WP isa (.block [.addSp .t2 8, .load .d .t2 .t2 0]) s fun s₁ => s₁ = s.write .t2 (stackArg s 1) := by
    brun [exec_addSp (show 8 < 2048 by decide), hld8, hal8, hv8, write_write]
  exact WP.mono first fun s₁ e => by rw [e]; exact gpr_write_self _ _ _

theorem pins_L1s : Pins L1s [.t2] := by
  intro v s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rw [h₁, h₂]

theorem sentry_rel : RelCT isa (Two C0s) (.block Sign.entry) fun _ _ => True := by
  unfold Sign.entry
  rw [List.append_assoc]
  refine RelCT.block_append (M := isa) (l₁ := ([.addSp .t2 8, .load .d .t2 .t2 0] : List Instr)) ?_
  exact RelCT.seq (two_post (two_taint [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
    fun _ _ h => loadS_L1s h) (two_taint _ pins_L1s (by taint_decide))

/-! ## The levels -/

abbrev RKs : Prog isa := andThen (.seq (.block ptrY) checkElem) Sign.body Sign.zeroOut
abbrev R3s : Prog isa := .seq setupP (andThen (.seq (.block ptrG) checkElem) RKs Sign.zeroOut)
abbrev R2s : Prog isa := andThen pModQ R3s Sign.zeroOut
abbrev R1s : Prog isa := andThen (.block (ptrQ ++ odd)) R2s Sign.zeroOut
abbrev R0s : Prog isa := odds R2s Sign.zeroOut
abbrev X2s : Prog isa :=
  .seq (.block [.addi .a3 .a1 0, .shift .sll .d .t3 .a1 32, .load .d .t4 .s6 hLens, .add .t4 .t4 .t3,
    .store .d .t4 .s6 hLens]) (andThen pairs R0s Sign.zeroOut)
abbrev X1s : Prog isa :=
  .seq (.block [.addi .a2 .a1 0]) (andThen (.seq (.block ptrQ) bytesBits) X2s Sign.zeroOut)

abbrev FTs : List (Prog isa) := Code.flat Sign.sign
abbrev FX1s : List (Prog isa) := Code.flat X1s
abbrev FX2s : List (Prog isa) := Code.flat X2s
abbrev FR0s : List (Prog isa) := Code.flat R0s
abbrev FR1s : List (Prog isa) := Code.flat R1s
abbrev FR2s : List (Prog isa) := Code.flat R2s
abbrev FR3s : List (Prog isa) := Code.flat R3s
abbrev FKs : List (Prog isa) := Code.flat RKs
abbrev FBs : List (Prog isa) := Code.flat Sign.body

abbrev ΦX1s (v : VD) (u : State) : Prop := At C0s FTs 5 v u ∧ u.gpr .a0 = 0
abbrev ΦX2s (v : VD) (u : State) : Prop := At ΦX1s FX1s 5 v u ∧ u.gpr .a0 = 0
abbrev ΦR0s (v : VD) (u : State) : Prop := At ΦX2s FX2s 12 v u ∧ u.gpr .a0 = 0
abbrev ΦR1s (v : VD) (u : State) : Prop := At ΦR0s FR0s 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR2s (v : VD) (u : State) : Prop := At ΦR1s FR1s 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR3s (v : VD) (u : State) : Prop := At ΦR2s FR2s 23 v u ∧ u.gpr .a0 = 0
abbrev ΦEgs (v : VD) (u : State) : Prop := At ΦR3s FR3s 45 v u ∧ u.gpr .a0 = 0
abbrev ΦKs (v : VD) (u : State) : Prop := At ΦR3s FR3s 46 v u ∧ u.gpr .a0 = 0
abbrev ΦEys (v : VD) (u : State) : Prop := At ΦKs FKs 28 v u ∧ u.gpr .a0 = 0
abbrev ΦBs (v : VD) (u : State) : Prop := At ΦKs FKs 29 v u ∧ u.gpr .a0 = 0

theorem hFTs : (FTs.drop 5).take 1 = [.ite (.zero .a0) X1s Sign.zeroOut] := rfl
theorem hFX1s : (FX1s.drop 5).take 1 = [.ite (.zero .a0) X2s Sign.zeroOut] := rfl
theorem hFX2s : (FX2s.drop 12).take 1 = [.ite (.zero .a0) R0s Sign.zeroOut] := rfl
theorem hFR0s : (FR0s.drop 1).take 1 = [.ite (.zero .a0) R1s Sign.zeroOut] := rfl
theorem hFR1s : (FR1s.drop 1).take 1 = [.ite (.zero .a0) R2s Sign.zeroOut] := rfl
theorem hFR2s : (FR2s.drop 23).take 1 = [.ite (.zero .a0) R3s Sign.zeroOut] := rfl
theorem hFR3gs : (FR3s.drop 45).take 1 = [.ite (.zero .a0) elemOrder (.block [])] := rfl
theorem hFR3s : (FR3s.drop 46).take 1 = [.ite (.zero .a0) RKs Sign.zeroOut] := rfl
theorem hFKys : (FKs.drop 28).take 1 = [.ite (.zero .a0) elemOrder (.block [])] := rfl
theorem hFKs : (FKs.drop 29).take 1 = [.ite (.zero .a0) Sign.body Sign.zeroOut] := rfl

theorem runTs : ∀ v s, C0s v s → WP isa (Code.seqL FTs) s fun _ => True := fun _ s h =>
  let ⟨tr, t, e, _⟩ := sign_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem runX1s : ∀ v s, ΦX1s v s → WP isa (Code.seqL FX1s) s fun _ => True := run_then runTs hFTs
theorem runX2s : ∀ v s, ΦX2s v s → WP isa (Code.seqL FX2s) s fun _ => True := run_then runX1s hFX1s
theorem runR0s : ∀ v s, ΦR0s v s → WP isa (Code.seqL FR0s) s fun _ => True := run_then runX2s hFX2s
theorem runR1s : ∀ v s, ΦR1s v s → WP isa (Code.seqL FR1s) s fun _ => True := run_then runR0s hFR0s
theorem runR2s : ∀ v s, ΦR2s v s → WP isa (Code.seqL FR2s) s fun _ => True := run_then runR1s hFR1s
theorem runR3s : ∀ v s, ΦR3s v s → WP isa (Code.seqL FR3s) s fun _ => True := run_then runR2s hFR2s
theorem runEgs : ∀ v s, ΦEgs v s → WP isa (Code.seqL FE) s fun _ => True := run_then runR3s hFR3gs
theorem runKs : ∀ v s, ΦKs v s → WP isa (Code.seqL FKs) s fun _ => True := run_then runR3s hFR3s
theorem runEys : ∀ v s, ΦEys v s → WP isa (Code.seqL FE) s fun _ => True := run_then runKs hFKys
theorem runBs : ∀ v s, ΦBs v s → WP isa (Code.seqL FBs) s fun _ => True := run_then runKs hFKs

theorem onX1s : ∀ v u, ΦX1s v u → SX1 v u := fun _ _ h => semX1 frontS ⟨atL rfl h.1, h.2⟩
theorem onX2s : ∀ v u, ΦX2s v u → SX2 v u := fun _ _ h => semX2 onX1s ⟨atL rfl h.1, h.2⟩
theorem onR0s : ∀ v u, ΦR0s v u → P1 v u := fun _ _ h => semR0 onX2s ⟨atL rfl h.1, h.2⟩
theorem onR1s : ∀ v u, ΦR1s v u → P1 v u ∧ v.p % 2 = 1 := fun _ _ h => semR1 onR0s ⟨atL rfl h.1, h.2⟩
theorem onR2s : ∀ v u, ΦR2s v u → SR2 v u := fun _ _ h => semR2 onR1s ⟨atL rfl h.1, h.2⟩
theorem onR3s : ∀ v u, ΦR3s v u → SR3 v u := fun _ _ h => semR3 onR2s ⟨atL rfl h.1, h.2⟩

theorem kyR3s : ∀ v u, ΦR3s v u → KY v := fun _ _ h =>
  at_pure (G := KY) (fun _ _ h => at_pure (G := KY) (fun _ _ h => at_pure (G := KY) (fun _ _ h =>
    at_pure (G := KY) (fun _ _ h => at_pure (G := KY) (fun _ _ h => at_pure (G := KY) kyC0s h.1) h.1) h.1) h.1)
      h.1) h.1

theorem onKs : ∀ v u, ΦKs v u → SK v u := fun _ _ h => semK onR3s kyR3s ⟨atL rfl h.1, h.2⟩

/-- `body`'s phase: the key passed the checks. -/
abbrev SS (v : VD) (u : State) : Prop := SK v u ∧ EOk v (2 * v.L.pl + v.L.ql)

theorem onBs : ∀ v u, ΦBs v u → SS v u := fun _ _ h =>
  let m := at_sem (Φ := ΦKs) (F := FK) (n := 29) (M := MK) (fun _ _ h => midK onKs h) (atL rfl h.1)
  ⟨m.1, m.2.mp h.2⟩

theorem oX1s : ∀ v u, ΦX1s v u → v.out = some (oOf v) := fun _ _ h => at_pure outS h.1
theorem oX2s : ∀ v u, ΦX2s v u → v.out = some (oOf v) := fun _ _ h => at_pure oX1s h.1
theorem oR0s : ∀ v u, ΦR0s v u → v.out = some (oOf v) := fun _ _ h => at_pure oX2s h.1
theorem oR1s : ∀ v u, ΦR1s v u → v.out = some (oOf v) := fun _ _ h => at_pure oR0s h.1
theorem oR2s : ∀ v u, ΦR2s v u → v.out = some (oOf v) := fun _ _ h => at_pure oR1s h.1
theorem oR3s : ∀ v u, ΦR3s v u → v.out = some (oOf v) := fun _ _ h => at_pure oR2s h.1
theorem oKs : ∀ v u, ΦKs v u → v.out = some (oOf v) := fun _ _ h => at_pure oR3s h.1

/-! ## The levels' relations -/

theorem s6_kepts : ∀ i ∈ instrs (seg FTs 1 6), dstOf i ≠ some .s6 := by
  have h : (instrs (seg FTs 1 6)).all (fun i => dstOf i != some .s6) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem pinsTs6 : Pins (At C0s FTs 6) [.s6] :=
  pins_fix (fun v => [(.s6, v.L.S)]) (fun _ => rfl) fun v u ⟨s₀, t, h₀, e⟩ => by
    rw [take_split FTs (n := 1) (m := 6) (by decide)] at e
    obtain ⟨_, _, u₁, -, e₁, e₂⟩ := exec_seqL_append.mp e
    have h₁ : u₁.gpr .s6 = v.L.S := (at_sem (Φ := C0s) (F := FTs) (n := 1) (M := P0)
      (fun _ _ h => WP.of_flat (c := .block Sign.entry) rfl (frontS _ _ h)) ⟨s₀, _, h₀, e₁⟩).1.regs.s6
    exact ⟨(Exec.gpr_callFree s6_kepts e₂ rfl).trans h₁, trivial⟩

section Levels

variable (hbody : RelCT isa (Two ΦBs) Sign.body fun _ _ => True)
include hbody

theorem Ks_rel : RelCT isa (Two ΦKs) RKs fun _ _ => True := by
  refine chain_start (chain_cons runKs (m := 1) (by decide)
    (two_taint _ (pinsL rfl (pinsK_0 onKs)) (by taint_decide)) ?_)
  refine chain_cons runKs (m := 28) (by decide) (two_taint _ (pinsL rfl (pinsK_1 onKs)) (by taint_decide)) ?_
  refine chain_cons runKs (m := 29) (by decide) (rel_ite_at hFKys (zeroL rfl (zeroEy onKs))
    (eo_rel runEys fun _ _ h => semEy onKs ⟨atL rfl h.1, h.2⟩) nil_rel) ?_
  exact chain_cons runKs (m := 30) (by decide) (rel_ite_at hFKs (zeroL rfl (zeroK onKs)) hbody
    (szero_rel (run_else runKs hFKs)
      (fun _ _ h => (at_sem (Φ := ΦKs) (F := FK) (n := 29) (M := MK) (fun _ _ h => midK onKs h)
        (atL rfl h.1)).1.1.base) fun _ _ h => at_pure oKs h.1)) nil_rel

theorem R3s_rel : RelCT isa (Two ΦR3s) R3s fun _ _ => True := by
  refine chain_start (chain_cons runR3s (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsR3_0 onR3s)) (by taint_decide)) ?_)
  refine chain_cons runR3s (m := 18) (by decide) (two_taint _ (pinsL rfl (pinsR3_2 onR3s)) (by taint_decide)) ?_
  refine chain_cons runR3s (m := 45) (by decide) (two_taint _ (pinsL rfl (pinsR3_18 onR3s)) (by taint_decide)) ?_
  refine chain_cons runR3s (m := 46) (by decide) (rel_ite_at hFR3gs (zeroL rfl (zeroEg onR3s))
    (eo_rel runEgs fun _ _ h => semEg onR3s ⟨atL rfl h.1, h.2⟩) nil_rel) ?_
  exact chain_cons runR3s (m := 47) (by decide) (rel_ite_at hFR3s (zeroL rfl (zeroR3 onR3s)) (Ks_rel hbody)
    (szero_rel (run_else runR3s hFR3s)
      (fun _ _ h => (at_sem (Φ := ΦR3s) (F := FR3) (n := 46) (M := MR3) (fun _ _ h => midR3 onR3s h)
        (atL rfl h.1)).1.base) fun _ _ h => at_pure oR3s h.1)) nil_rel

theorem R2s_rel : RelCT isa (Two ΦR2s) R2s fun _ _ => True := by
  refine chain_start (chain_cons runR2s (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsR2_0 onR2s)) (by taint_decide)) ?_)
  refine chain_cons runR2s (m := 10) (by decide) (two_taint _ (pinsL rfl (pinsR2_2 onR2s)) (by taint_decide)) ?_
  refine chain_cons runR2s (m := 23) (by decide) (two_taint _ (pinsL rfl (pinsR2_10 onR2s)) (by taint_decide)) ?_
  exact chain_cons runR2s (m := 24) (by decide) (rel_ite_at hFR2s (zeroL rfl (zeroR2 onR2s)) (R3s_rel hbody)
    (szero_rel (run_else runR2s hFR2s)
      (fun _ _ h => (at_sem (Φ := ΦR2s) (F := FR2) (n := 23) (M := MR2) (fun _ _ h => midR2 onR2s h)
        (atL rfl h.1)).1.1.1) fun _ _ h => at_pure oR2s h.1)) nil_rel

theorem R1s_rel : RelCT isa (Two ΦR1s) R1s fun _ _ => True :=
  chain_start (chain_cons runR1s (m := 1) (by decide) (relL rfl rfl (relR1 onR1s))
    (chain_cons runR1s (m := 2) (by decide) (rel_ite_at hFR1s (zeroL rfl (zeroR1 onR1s)) (R2s_rel hbody)
      (szero_rel (run_else runR1s hFR1s)
        (fun _ _ h => (at_sem (Φ := ΦR1s) (F := FR1) (n := 1) (M := MR1) (fun _ _ h => midR1 onR1s h)
          (atL rfl h.1)).1.1) fun _ _ h => at_pure oR1s h.1)) nil_rel))

theorem R0s_rel : RelCT isa (Two ΦR0s) R0s fun _ _ => True :=
  chain_start (chain_cons runR0s (m := 1) (by decide) (relL rfl rfl (relR0 onR0s))
    (chain_cons runR0s (m := 2) (by decide) (rel_ite_at hFR0s (zeroL rfl (zeroR0 onR0s)) (R1s_rel hbody)
      (szero_rel (run_else runR0s hFR0s)
        (fun _ _ h => (at_sem (Φ := ΦR0s) (F := FR0) (n := 1) (M := MR0) (fun _ _ h => midR0 onR0s h)
          (atL rfl h.1)).1.1) fun _ _ h => at_pure oR0s h.1)) nil_rel))

theorem X2s_rel : RelCT isa (Two ΦX2s) X2s fun _ _ => True :=
  chain_start (chain_cons runX2s (m := 12) (by decide)
    (two_taint _ (pinsL rfl (pinsX2_0 onX2s)) (by taint_decide))
    (chain_cons runX2s (m := 13) (by decide) (rel_ite_at hFX2s (zeroL rfl (zeroX2 onX2s)) (R0s_rel hbody)
      (szero_rel (run_else runX2s hFX2s)
        (fun _ _ h => (at_sem (Φ := ΦX2s) (F := FX2) (n := 12) (M := MX2) (fun _ _ h => midX2 onX2s h)
          (atL rfl h.1)).1) fun _ _ h => at_pure oX2s h.1)) nil_rel))

theorem X1s_rel : RelCT isa (Two ΦX1s) X1s fun _ _ => True := by
  refine chain_start (chain_cons runX1s (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsX1_0 onX1s)) (by taint_decide)) ?_)
  refine chain_cons runX1s (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsX1_2 onX1s)) (by taint_decide)) ?_
  refine chain_cons runX1s (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsX1_4 onX1s)) (by taint_decide)) ?_
  exact chain_cons runX1s (m := 6) (by decide) (rel_ite_at hFX1s (zeroL rfl (zeroX1 onX1s)) (X2s_rel hbody)
    (szero_rel (run_else runX1s hFX1s)
      (fun _ _ h => (at_sem (Φ := ΦX1s) (F := FX1) (n := 5) (M := MX1) (fun _ _ h => midX1 onX1s h)
        (atL rfl h.1)).1.1) fun _ _ h => at_pure oX1s h.1)) nil_rel

theorem sign_rel : RelCT isa (Two C0s) Sign.sign fun _ _ => True := by
  refine chain_start (chain_cons runTs (m := 1) (by decide) ?_ ?_)
  · refine RelCT.mono (P := Two C0s)
      (VG.Proof.Bignum.RISCV64.RelCT.seqL_single (sentry_rel.mono (fun _ _ h => h) fun _ _ _ => trivial))
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, at_zero_inv h₁, at_zero_inv h₂, hsp⟩) fun _ _ h => h
  refine chain_cons runTs (m := 2) (by decide) (two_taint _ (pinsL rfl (pinsT1 frontS)) (by taint_decide)) ?_
  refine chain_cons runTs (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsT2 frontS)) (by taint_decide)) ?_
  refine chain_cons runTs (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsT4 frontS)) (by taint_decide)) ?_
  refine chain_cons runTs (m := 6) (by decide) (rel_ite_at hFTs (zeroL rfl (zeroT frontS)) (X1s_rel hbody)
    (szero_rel (run_else runTs hFTs) (fun _ _ h => (at_sem (Φ := C0s) (F := TF Sign.entry) (n := 5) (M := MT)
        (fun _ _ h => midT frontS h) (atL rfl h.1)).1.1)
      fun _ _ h => at_pure outS h.1)) ?_
  exact two_taint _ pinsTs6 (by taint_decide)

end Levels

/-- Runs that agree on the contract's public data have the same public data `vdS`. -/
theorem vdS_eq {s t : State} (hs : sContract.pre s) (hp : sContract.pub s t) : vdS s = vdS t := by
  obtain ⟨-, e0, -, e2, e3, e4, e5, e6, e7, sa0, sa1, sa2, hl⟩ := hp
  have hk := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨e, -⟩ := List.append_inj' hl rfl
  simp only [Spec.Dsa.publicBytesLeak, bytesAt_take] at e
  have e := (List.map_inj_right fun _ _ h => BitVec.eq_of_toNat_eq h).mp e
  rw [← e2, ← e3, ← e4, ← e6, Nat.min_eq_right (by omega)] at e
  simp only [vdS, slayOf]
  rw [e, e0, e2, e4, e5, e6, e7, sa0, sa1, sa2]

end VG.Proof.Dsa.RISCV64.CT
