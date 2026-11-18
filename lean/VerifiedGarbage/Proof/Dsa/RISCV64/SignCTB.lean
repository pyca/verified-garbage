module

import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCT
import VerifiedGarbage.Proof.Dsa.RISCV64.Elem
import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Elem
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Dsa.RISCV64.SignCT`, which this module and modules that import it used -/

section

/-!
# DSA signing on RISC-V: constant time, the levels

`vg_dsa_sign` (`Sign.sign`) runs `Sign.entry`, then `Sign.checkSignKey` with
`Sign.body` or `Sign.zeroOut`, then `restore`. Its public data (`vdS`) is
the key's public octets (p||q||g||y), the nonce's and the digest's addresses
and lengths, and `out`, which the header keeps. The entry loads `scratch`'s
address from the stack, as verification's does (`sentry_rel`). Its levels
are validation's (`ValidateCT.lean`), each failing to `zeroOut`
(`szero_rel`, cut after its loads of the header), up to y's range (the
key's level has no `elemOrder`: `midKs`), whose passing side is `body`, its
relation a hypothesis here.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv take_split)
open VG.Proof.Bignum (slot)

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
      simp only [BitVec.ofNat_add_ofNat]; congr 1; omega_using []) (by decide) (by rfl)) fun t ⟨a5, kt⟩ => ?_
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
    ssrc (by rw [hrd]; simp) dKS (s.gpr .a3).isLt (by omega_using [hkl]) k.2.1 k.2.2
  exact ⟨⟨hL, F.regs, F.scr, hK, ssrc (by rw [hrd]; simp) dNS (s.gpr .a6).isLt (Nat.le_refl _) k.2.1 k.2.2,
    ssrc (by rw [hrd]; simp) dDS (stackArg s 0).isLt (Nat.min_le_left _ _) k.2.1 k.2.2,
    hK.bytes F.out (by simp only [slayOf] at hZ ⊢; omega_using [hZ]),
    (by simp only [vdS, slayOf]; omega_using []), (fun _ => F.dig), fun o ho => by cases ho; exact F.outw⟩, F.lens⟩

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
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [sp16]
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

abbrev RKs : Prog isa := andThen (.seq (.block ptrY) (.seq (loadArr 4) elemRange)) Sign.body Sign.zeroOut
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
abbrev ΦBs (v : VD) (u : State) : Prop := At ΦKs FKs 28 v u ∧ u.gpr .a0 = 0

theorem hFTs : (FTs.drop 5).take 1 = [.ite (.zero .a0) X1s Sign.zeroOut] := rfl
theorem hFX1s : (FX1s.drop 5).take 1 = [.ite (.zero .a0) X2s Sign.zeroOut] := rfl
theorem hFX2s : (FX2s.drop 12).take 1 = [.ite (.zero .a0) R0s Sign.zeroOut] := rfl
theorem hFR0s : (FR0s.drop 1).take 1 = [.ite (.zero .a0) R1s Sign.zeroOut] := rfl
theorem hFR1s : (FR1s.drop 1).take 1 = [.ite (.zero .a0) R2s Sign.zeroOut] := rfl
theorem hFR2s : (FR2s.drop 23).take 1 = [.ite (.zero .a0) R3s Sign.zeroOut] := rfl
theorem hFR3gs : (FR3s.drop 45).take 1 = [.ite (.zero .a0) elemOrder (.block [])] := rfl
theorem hFR3s : (FR3s.drop 46).take 1 = [.ite (.zero .a0) RKs Sign.zeroOut] := rfl
theorem hFKs : (FKs.drop 28).take 1 = [.ite (.zero .a0) Sign.body Sign.zeroOut] := rfl

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

/-- y's load and range, `CK` kept. -/
theorem yrange_CK {v : VD} {s : State} {o : Nat} (h : CK v s) (ho : o + v.L.pl ≤ v.kn)
    (h7 : s.gpr .s7 = off v.key o) (h8 : s.gpr .s8 = BitVec.ofNat 64 v.L.pl) :
    WP isa (.seq (loadArr 4) elemRange) s fun t => CK v t ∧ (t.gpr .a0 = 0 ↔ ERange v o) := by
  have hL := h.base.ok
  have hbuf := hL.buf_end
  have hqZ : v.L.qOff ≤ v.L.Z := by simp only [Lay.bOff] at hbuf; omega_using [hbuf]
  have e0 := Lay.slot_eq v.L.wp 0; have e1 := Lay.slot_eq v.L.wp 1; have e4 := Lay.slot_eq v.L.wp 4
  have hw := hL.wp_ge
  have hnw := hL.nowrap
  have en := h.inp.env
  have he := h.base.hk.sub ho
  refine WP.seq (WP.mono (loadArr_ok en (j := 4) (N := off v.key o) (by decide)
    (by rw [h7]; exact (BitVec.add_zero _).symm) h8 (by have := h.base.pl; omega_using [this]) (by have := hL.wp_eq; omega_using [this])
    he.rd (fun i hi x hx => he.sep i hi x (Nat.lt_of_lt_of_le hx hqZ))) fun s₁ ⟨⟨v4, top4, o1, a7⟩, k1⟩ => ?_)
  have e1' : Env s₁ v.L.S v.L.qOff v.L.wp :=
    ⟨en.hs.congr k1.2.2, a7, (k1.gpr (by decide)).trans en.s5, (k1.gpr (by decide)).trans en.t0, en.w2, en.w48,
      en.hZ⟩
  have A0 : wordsVal s₁.mem v.L.S (slot v.L.wp 0) v.L.wp = v.p := by
    rw [o1.wordsVal (by omega_using [e0, e4]) (by omega_arith)]; exact h.p0
  refine WP.mono (elemRange_ok e1' top4) fun t ⟨⟨r0, _, o2, e2⟩, k2⟩ => ?_
  rw [v4, A0, h.base.bytes ho] at r0
  have k12 := k1.trans k2
  exact ⟨h.elem k12 (by decide) (k12.gpr (by decide)) ⟨e2, (k12.gpr (by decide)).trans h.inp.s6⟩
    (p_elem2 o1 o2), r0⟩

/-- At the branch on y's range: `body`'s phase if it passes. -/
abbrev MKs (v : VD) (u : State) : Prop := SK v u ∧ (u.gpr .a0 = 0 ↔ ERange v (2 * v.L.pl + v.L.ql))

theorem midKs {v : VD} {s : State} (h : ΦKs v s) : WP isa (Code.seqL (FKs.take 28)) s (MKs v) := by
  obtain ⟨c, km, eg, ky⟩ := onKs _ _ h
  exact WP.of_flat (c := .seq (.block ptrY) (.seq (loadArr 4) elemRange)) rfl
    (WP.seq ((ptr_CK c (ptrY_ok c.base.scr c.base.ok c.base.regs)).mono fun _ ⟨⟨c', a7, a8⟩, _⟩ =>
      (yrange_CK c' (by omega) a7 a8).mono fun _ ⟨c'', a0⟩ => ⟨⟨c'', km, eg, ky⟩, a0⟩))

theorem zeroKs : ∀ v s₁ s₂, At ΦKs FKs 28 v s₁ → At ΦKs FKs 28 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => ERange v (2 * v.L.pl + v.L.ql)) fun _ _ h => (midKs h).mono fun _ h => h.2

/-- `body`'s phase: the domain passed the checks, and y its range. -/
abbrev SS (v : VD) (u : State) : Prop := SK v u ∧ ERange v (2 * v.L.pl + v.L.ql)

theorem onBs : ∀ v u, ΦBs v u → SS v u := fun _ _ h =>
  let m := at_sem (Φ := ΦKs) (F := FKs) (n := 28) (M := MKs) (fun _ _ h => midKs h) h.1
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
  exact chain_cons runKs (m := 29) (by decide) (rel_ite_at hFKs zeroKs hbody
    (szero_rel (run_else runKs hFKs)
      (fun _ _ h => (at_sem (Φ := ΦKs) (F := FKs) (n := 28) (M := MKs) (fun _ _ h => midKs h)
        h.1).1.1.base) fun _ _ h => at_pure oKs h.1)) nil_rel

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
  rw [← e2, ← e3, ← e4, ← e6, Nat.min_eq_right (by omega_using [hk])] at e
  simp only [vdS, slayOf]
  rw [e, e0, e2, e4, e5, e6, e7, sa0, sa1, sa2]

end VG.Proof.Dsa.RISCV64.CT

end

end

-- separate module: `body`'s cuts and their taint checks cost more than their imports, and `SignVerified`
-- states the result without them

/-!
# DSA signing on RISC-V: constant time, `body`

`sign_ct`: two runs of `vg_dsa_sign` from states that satisfy `sContract`
and agree on its public data leak the same trace. The levels are
`SignCT.lean`'s; `Sign.body` is `keyPair` then `Sign.tail`. Its list (`FBs`)
is cut after each block that loads the header's words: in `keyPair` (2, 12,
53), and after it (64); the tail's list (`FTl`, `tail_rel`), which
`vg_dsa_sign_prevalidated` shares after its own first step
(`PrevalidatedSignCT.lean`), in `gk` (2, 12, 53), `rRanges` (56, 67, 75),
`qMinus2` (118), `inverseK` (121, 131), `sValue` (172, 174, 188) and `output`
(259), from any level whose states are in the tail's phase (`TS`). Between
them the phases carry the key's and `out`'s regions (`OS`, the contract's,
kept by every run), the header's words and the arrays' facts the pieces
need.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv at_step)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-! ## The regions -/

/-- What signing's public data satisfies. -/
structure GS (v : VD) : Prop where
  sgl : v.sgl = v.L.ql
  kn : v.kn = 3 * v.L.pl + v.L.ql
  no : (oOf v).toNat + 2 * v.L.ql ≤ 2 ^ 64
  out : v.out = some (oOf v)
  full : v.full = true

/-- The key (x too) may be read, `out` written, both apart from `scratch`. -/
structure OS (v : VD) (u : State) : Prop where
  key : Src u v.L v.key (3 * v.L.pl + 2 * v.L.ql)
  wr : ∀ i < 2 * v.L.ql, InRegions u.wr (off (oOf v) i) 1
  src : Src u v.L (oOf v) (2 * v.L.ql)

theorem OS.keep {v : VD} {s t : State} (h : OS v s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : OS v t :=
  ⟨h.key.keep hrd hwr, by rw [hwr]; exact h.wr, h.src.keep hrd hwr⟩

theorem os_at {Φ : VD → State → Prop} {F : List (Prog isa)} {n : Nat} (h : ∀ v s, Φ v s → OS v s) {v : VD}
    {u : State} (hu : At Φ F n v u) : OS v u := by
  obtain ⟨s₀, t, h₀, e⟩ := hu
  obtain ⟨hr, hw, -⟩ := Exec.rdwr e
  exact (h v s₀ h₀).keep hr hw

theorem gC0s : ∀ v s, C0s v s → GS v := by
  rintro _ s ⟨h, rfl⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, nwO, -, -, -, -, -, hol, -, -, -, -⟩ := h
  have h1 : (s.gpr .a1).toNat = 2 * (slayOf s).ql := hol
  exact ⟨rfl, rfl, by show (s.gpr .a0).toNat + 2 * (slayOf s).ql ≤ _; rw [← h1]; exact nwO, rfl, rfl⟩

theorem osC0s : ∀ v s, C0s v s → OS v s := by
  rintro _ s ⟨h, rfl⟩
  obtain ⟨hrd, hwr, -, -, -, dOS, -, dKS, -, -, -, nwO, nwK, -, -, -, -, hol, hkl, -, -, -⟩ := h
  have h1 : (s.gpr .a1).toNat = 2 * (slayOf s).ql := hol
  have h3 : (s.gpr .a3).toNat = 3 * (slayOf s).pl + 2 * (slayOf s).ql := hkl
  refine ⟨ssrc (by rw [hrd]; simp) dKS (s.gpr .a3).isLt (by simp only [vdS]; omega_using [h3]) rfl rfl,
    fun i hi => ⟨_, by rw [hwr]; exact List.mem_cons_self .., Offset.contains_base _ (by
      simp only [vdS] at hi; omega_using [h1, hi]) (by simp only [vdS] at hi ⊢; omega_using [h1, hi])⟩,
    ⟨fun i hi => ⟨_, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self ..),
      Offset.contains_base _ (by simp only [vdS] at hi; omega_using [h1, hi]) (by simp only [vdS] at hi ⊢; omega_using [h1, hi])⟩,
    fun i hi => Pub.ne_of_disjoint dOS (by omega_using []) i (by simp only [vdS] at hi; omega_using [h1, hi])⟩⟩

theorem gBs : ∀ v u, ΦBs v u → GS v := fun _ _ h =>
  at_pure (G := GS) (fun _ _ h => at_pure (G := GS) (fun _ _ h => at_pure (G := GS) (fun _ _ h =>
    at_pure (G := GS) (fun _ _ h => at_pure (G := GS) (fun _ _ h => at_pure (G := GS) (fun _ _ h =>
      at_pure (G := GS) (fun _ _ h => at_pure (G := GS) gC0s h.1) h.1) h.1) h.1) h.1) h.1) h.1) h.1

theorem osBs : ∀ v u, ΦBs v u → OS v u := fun _ _ h =>
  os_at (fun _ _ h => os_at (fun _ _ h => os_at (fun _ _ h => os_at (fun _ _ h => os_at (fun _ _ h =>
    os_at (fun _ _ h => os_at (fun _ _ h => os_at osC0s h.1) h.1) h.1) h.1) h.1) h.1) h.1) h.1

/-- `body`'s phase, with the regions. -/
abbrev SBs (v : VD) (u : State) : Prop := SS v u ∧ GS v ∧ OS v u

theorem onSBs : ∀ v u, ΦBs v u → SBs v u := fun _ _ h => ⟨onBs _ _ h, gBs _ _ h, osBs _ _ h⟩

theorem SBs.vals {v : VD} {s : State} (h : SBs v s) :
    2 ≤ v.q ∧ v.q % 2 = 1 ∧ v.q < 2 ^ (8 * v.L.ql) ∧ v.qb ≤ v.L.ql ∧ 2 ≤ v.p ∧ v.p % 2 = 1 := by
  obtain ⟨⟨⟨c, ⟨hsz, hp, hq, _⟩, _⟩, _⟩, _⟩ := h
  obtain bd := VG.Proof.Dsa.supported_bounds hsz
  have hl := c.base.q_lt
  exact ⟨by omega_using [bd], hq, hl, q_bits (by omega_using [hq]) hl, by omega_using [bd], hp⟩

/-! ## The P space -/

/-- In the P space during `body`. -/
structure PK (v : VD) (t : State) : Prop where
  cb : CB v t
  lens : Lens v v.qb t
  q0 : arrQ t.mem v.L 0 = v.q
  os : OS v t

theorem PK.frame {v : VD} {s t : State} {rs : List Reg} (h : PK v s) (k : Keep rs s t)
    (ip : InP t v.L) (I : PInv t v.L) (K : BKept v.L s.mem t.mem) (hp0 : arrP t.mem v.L 0 = arrP s.mem v.L 0)
    (hp24 : arrP t.mem v.L 24 = arrP s.mem v.L 24) (hq0 : arrQ t.mem v.L 0 = arrQ s.mem v.L 0)
    (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : PK v t :=
  ⟨⟨h.cb.1.step (h.cb.1.regs.ofBKept k K hr) k.2.1 k.2.2 K.out (K.word (by decide) (by decide))
      (K.word (by decide) (by decide)), ip, I, hp0.trans h.cb.2.2.2.1, hp24.trans h.cb.2.2.2.2⟩,
    by rw [Lens, K.word (by decide) (by decide)]; exact h.lens, hq0.trans h.q0, h.os.keep k.2.1 k.2.2⟩

theorem PK.keepM {v : VD} {s t : State} {rs : List Reg} (h : PK v s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ inRegs ++ regsRegs ++ ([.t1] : List Reg), r ∉ rs := by decide) : PK v t :=
  h.frame k (h.cb.2.1.keep k fun r hm' => hr r (by simp [hm'])) (by
      show ((word t.mem v.L.S (slot v.L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
      rw [hm, k.gpr (fun hm' => hr .t1 (by simp) hm')]; exact h.cb.2.2.1)
    (by rw [hm]; exact BKept.refl _ _) (by rw [arrP, hm]) (by rw [arrP, hm]) (by rw [arrQ, hm])
    fun r hm' => hr r (by simp [hm'])

theorem sbs_PK {v : VD} {s : State} (h : SBs v s) : PK v s :=
  let c := h.1.1.1
  ⟨⟨c.base, c.inp, c.inv, c.p0, c.p24⟩, c.lens, c.q0, h.2.2⟩

theorem fix_PK {v : VD} {t : State} (h : PK v t) : Fix (fixB v ++ envP v) t := fix_CB h.cb

/-- `keyPair`'s first block: x's and g's pointers. -/
abbrev KP0 : List Instr := Sign.ptrX ++ ([.addi .s9 .s7 0] : List Instr) ++ ptrG

theorem stKP0 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : PK v s)
    (hc : ∀ t, PK v t → t.gpr .s7 = off v.key (v.L.pl + v.L.ql) → t.gpr .s8 = BitVec.ofNat 64 v.L.pl →
      t.gpr .s9 = off v.key (3 * v.L.pl + v.L.ql) → WP isa c t Q) :
    WP isa (.seq (.block KP0) c) s Q := by
  have B := h.cb.1
  have hL := B.ok
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (ptrX_ok B.scr hL B.regs) fun s₁ ⟨⟨a7, _, m1⟩, k1⟩ =>
    WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = off v.key (3 * v.L.pl + v.L.ql) ∧ u.mem = s₁.mem)
      (by brun [a7, BitVec.add_zero]) (by decide) (by rfl)) fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_)))
  obtain h2 := (h.keepM k1 m1).keepM k2 m2
  exact WP.mono (ptrG_ok h2.cb.1.scr hL h2.cb.1.regs) fun t ⟨⟨b7, b8, m3⟩, k3⟩ =>
    hc t (h2.keepM k3 m3) b7 b8 ((k3.gpr (by decide)).trans a9)

theorem pinsBs0 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 0) [.s6, .s11, .ra, .a7, .s5, .t0] :=
  pins_at_fix (fun v => fixB v ++ envP v) (fun _ => rfl) fun _ _ h =>
    ⟨[], _, .block rfl, fix_PK (sbs_PK (hsem _ _ h))⟩

theorem pinsBs2 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 2) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl),
      (.s9, off v.key (3 * v.L.pl + v.L.ql))]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq (.block KP0) (.block (getP .s8))) (by decide +kernel)
      (stKP0 (sbs_PK (hsem _ _ h)) fun _ c a7 _ a9 =>
        WP.mono (getP_ok c.cb.1.scr c.cb.1.ok c.cb.1.regs .s8) fun _ ⟨⟨a8, m⟩, k⟩ =>
          (fix_PK (c.keepM k m)).app
            ⟨(k.gpr (r := .s7) (by decide)).trans a7, a8, (k.gpr (r := .s9) (by decide)).trans a9, trivial⟩)

theorem pinsBs12 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 12) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s9, off v.key (3 * v.L.pl + v.L.ql)), (.s10, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq (.block KP0) (.seq (.block (getP .s8)) (.seq (loadArr 4) (.seq (copy 1 24)
      (.block (getQ .s10)))))) (by decide +kernel)
      (stKP0 (sbs_PK (hsem _ _ h)) fun _ c a7 _ a9 =>
        powP_pre c.cb (c.cb.1.hk.sub (by have := c.cb.1.kn; omega_using [this])) a7 a9)

/-- A power in the P space, from its pointers. -/
theorem powK {v : VD} {s : State} {N E : Addr} (h : PK v s) (hN : Src s v.L N v.L.pl) (h7 : s.gpr .s7 = N)
    (hE : Src s v.L E v.L.ql) (h9 : s.gpr .s9 = E) (hp : 2 ≤ v.p) (hpo : v.p % 2 = 1) :
    WP isa Verify.powP s fun t => PK v t := by
  obtain B := h.cb.1; have ip := h.cb.2.1; have I := h.cb.2.2.1; have p0 := h.cb.2.2.2.1
  have p24 := h.cb.2.2.2.2
  have hL := B.ok
  obtain e := Lay.slot_eq v.L.wp
  obtain e0 := e 0; have e1 := e 1; have e24 := e 24; have hw := hL.wp_ge
  refine WP.mono (powSrc_ok hL B.scr B.regs ip I hN h7 hE h9 p0 hp hpo p24) fun t ⟨⟨_, ip', I', o⟩, k⟩ =>
    h.frame k ip' I' (BKept.ofBody hL (p_arrays_body hL o)) (o.wordsVal (by omega_using [e0, e1]) (by omega_arith))
      (o.wordsVal (by omega_using [e1, e24]) (by omega_arith)) (keepQ_arr0 hL ((PLow.keepQ hL o)))

theorem pinsBs53 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SBs v u) :
    Pins (At Φ FBs 53) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (2 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl)])
    (fun _ => rfl) fun _ _ h => by
    obtain ⟨-, -, -, -, hp, hpo⟩ := (hsem _ _ h).vals
    exact WP.of_flat (c := .seq (.block KP0) (.seq Verify.powP (.block ptrY))) (by kernel_rfl)
      (stKP0 (sbs_PK (hsem _ _ h)) fun _ c a7 _ a9 => WP.seq (WP.mono (powK c
        (c.cb.1.hk.sub (by have := c.cb.1.kn; omega_using [this])) a7 (c.os.key.sub (by omega_using [])) a9 hp hpo) fun _ c' =>
        WP.mono (ptrY_ok c'.cb.1.scr c'.cb.1.ok c'.cb.1.regs) fun _ ⟨⟨b7, b8, m⟩, k⟩ =>
          (fix_PK (c'.keepM k m)).app ⟨b7, b8, trivial⟩))

/-- The mask of the key's checks is in the header's word `hMask`. -/
abbrev MWs (v : VD) (t : State) : Prop := ∃ b, word t.mem v.L.S hMask = mask b

/-- `keyPair`, then `c`. -/
theorem stKP {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : SBs v s)
    (hc : ∀ t, PK v t → MWs v t → WP isa c t Q) : WP isa (.seq Sign.keyPair c) s Q := by
  obtain ⟨-, -, -, -, hp, hpo⟩ := h.vals
  obtain P := sbs_PK h
  obtain B := P.cb.1; have ip := P.cb.2.1; have I := P.cb.2.2.1; have p0 := P.cb.2.2.2.1
  obtain p24 := P.cb.2.2.2.2; have os := P.os
  have hL := B.ok
  refine WP.seq (WP.mono (keyPair_ok hL B.scr B.regs ip I os.key p0 hp hpo p24)
    fun t ⟨⟨mx, ip', I', m, o, w⟩, k⟩ => hc t (P.frame k ip' I' ((BKept.ofBody hL (PLow.body hL o)).trans
      (BKept.ofMask hL w)) (by rw [mask_arrP hL w 0 (by decide), PLow.arr hL o (by decide) (.inl rfl)])
      (by rw [mask_arrP hL w 24 (by decide), PLow.arr hL o (by decide) (.inr (by decide))])
      (by rw [keepQ_arr0 hL (mask_keepQ hL w), keepQ_arr0 hL (PLow.keepQ hL o)])) ⟨_, mx⟩)

/-- The digest's scalar is below `2 q`. -/
theorem SBs.hz {v : VD} {s : State} (h : SBs v s) (m : Mem) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m v.dig (min v.d v.qb)) < 2 * v.q := by
  obtain ⟨⟨⟨_, ⟨hsz, _, _, _⟩, _⟩, _⟩, _⟩ := h
  obtain bd := VG.Proof.Dsa.supported_bounds hsz
  obtain hq8 : Spec.Dsa.bitLength v.q = 8 * (Spec.Dsa.bitLength v.q / 8) := by
    have : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength v.p) (Spec.Dsa.bitLength v.q) := hsz
    unfold Spec.Dsa.supportedSizes at this; omega_using [this]
  refine Nat.lt_of_lt_of_le (VG.Proof.Dsa.decodeBE_lt _) ?_
  rw [VG.Proof.Bignum.bytesAt_length]
  refine Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)) ?_
  have := pow_bitLength_le (q := v.q) (by omega_arith)
  rw [hq8, Nat.pow_mul] at this
  exact this

/-! ## The tail

From `gk` on (`Sign.tail`), after `keyPair` or any step that leaves a mask in
`hMask` and the P space as `keyPair` leaves it (`TS`). -/

/-- What the tail's cuts need of the public data. -/
structure TV (v : VD) : Prop where
  sz : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength v.p) (Spec.Dsa.bitLength v.q)
  vals : 2 ≤ v.q ∧ v.q % 2 = 1 ∧ v.q < 2 ^ (8 * v.L.ql) ∧ v.qb ≤ v.L.ql ∧ 2 ≤ v.p ∧ v.p % 2 = 1
  hz : ∀ m, Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m v.dig (min v.d v.qb)) < 2 * v.q

/-- The tail's phase. -/
abbrev TS (v : VD) (u : State) : Prop := (PK v u ∧ MWs v u) ∧ GS v ∧ TV v

theorem TS.vals {v : VD} {s : State} (h : TS v s) :
    2 ≤ v.q ∧ v.q % 2 = 1 ∧ v.q < 2 ^ (8 * v.L.ql) ∧ v.qb ≤ v.L.ql ∧ 2 ≤ v.p ∧ v.p % 2 = 1 := h.2.2.vals

theorem TS.hz {v : VD} {s : State} (h : TS v s) (m : Mem) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m v.dig (min v.d v.qb)) < 2 * v.q := h.2.2.hz m

theorem SBs.tv {v : VD} {s : State} (h : SBs v s) : TV v :=
  ⟨h.1.1.2.1.1, h.vals, h.hz⟩

/-- `keyPair` leaves the tail's phase. -/
theorem kp_TS {v : VD} {s : State} (h : SBs v s) : WP isa Sign.keyPair s (TS v) := by
  obtain ⟨-, -, -, -, hp, hpo⟩ := h.vals
  obtain P := sbs_PK h
  obtain B := P.cb.1; have ip := P.cb.2.1; have I := P.cb.2.2.1; have p0 := P.cb.2.2.2.1
  obtain p24 := P.cb.2.2.2.2; have os := P.os
  have hL := B.ok
  exact WP.mono (keyPair_ok hL B.scr B.regs ip I os.key p0 hp hpo p24)
    fun t ⟨⟨mx, ip', I', m, o, w⟩, k⟩ => ⟨⟨P.frame k ip' I' ((BKept.ofBody hL (PLow.body hL o)).trans
      (BKept.ofMask hL w)) (by rw [mask_arrP hL w 0 (by decide), PLow.arr hL o (by decide) (.inl rfl)])
      (by rw [mask_arrP hL w 24 (by decide), PLow.arr hL o (by decide) (.inr (by decide))])
      (by rw [keepQ_arr0 hL (mask_keepQ hL w), keepQ_arr0 hL (PLow.keepQ hL o)]), ⟨_, mx⟩⟩, h.2.1, h.tv⟩

abbrev FTl : List (Prog isa) := Code.flat Sign.tail

theorem pinsTl0 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 0) [.s6, .s11, .ra, .a7, .s5, .t0] :=
  pins_at_fix (fun v => fixB v ++ envP v) (fun _ => rfl) fun _ _ h =>
    ⟨[], _, .block rfl, fix_PK (hsem _ _ h).1.1⟩

/-- `gk`'s first block: the nonce's and g's pointers. -/
abbrev G0 : List Instr := [.addi .s9 .ra 0] ++ ptrG

theorem stG0 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : PK v s)
    (hc : ∀ t, PK v t → t.gpr .s7 = off v.key (v.L.pl + v.L.ql) → t.gpr .s8 = BitVec.ofNat 64 v.L.pl →
      t.gpr .s9 = v.sig → WP isa c t Q) :
    WP isa (.seq (.block G0) c) s Q := by
  have B := h.cb.1
  have hL := B.ok
  refine WP.seq (WP.block_append (WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = v.sig ∧ u.mem = s.mem)
    (by brun [B.regs.ra, BitVec.add_zero]) (by decide) (by rfl)) fun s₁ ⟨⟨a9, m1⟩, k1⟩ => ?_))
  obtain h1 := h.keepM k1 m1
  exact WP.mono (ptrG_ok h1.cb.1.scr hL h1.cb.1.regs) fun t ⟨⟨b7, b8, m2⟩, k2⟩ =>
    hc t (h1.keepM k2 m2) b7 b8 ((k2.gpr (by decide)).trans a9)

theorem pinsTl2 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 2) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl),
      (.s9, v.sig)]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq (.block G0) (.block (getP .s8))) (by decide +kernel)
      (stG0 (hsem _ _ h).1.1 fun _ c a7 _ a9 =>
        WP.mono (getP_ok c.cb.1.scr c.cb.1.ok c.cb.1.regs .s8) fun _ ⟨⟨a8, m⟩, k⟩ =>
          (fix_PK (c.keepM k m)).app
            ⟨(k.gpr (r := .s7) (by decide)).trans a7, a8, (k.gpr (r := .s9) (by decide)).trans a9, trivial⟩)

theorem pinsTl12 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 12) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s9, v.sig), (.s10, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun _ _ h =>
    WP.of_flat (c := .seq (.block G0) (.seq (.block (getP .s8)) (.seq (loadArr 4)
      (.seq (copy 1 24) (.block (getQ .s10)))))) (by decide +kernel)
      (stG0 (hsem _ _ h).1.1 fun _ c a7 _ a9 =>
        powP_pre c.cb (c.cb.1.hk.sub (by have := c.cb.1.kn; omega_using [this])) a7 a9)

theorem Base.ns {v : VD} {s : State} (h : Base v s) (hg : GS v) : Src s v.L v.sig v.L.ql := by
  rw [← hg.sgl]; exact h.hsg

theorem pinsTl53 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 53) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, v.L.Buf), (.s8, BitVec.ofNat 64 v.L.pl)]) (fun _ => rfl)
    fun _ _ h => by
    obtain ⟨-, -, -, -, hp, hpo⟩ := (hsem _ _ h).vals
    exact WP.of_flat (c := .seq (.block G0) (.seq Verify.powP
      (.block (bufBase .s7 .t2 ++ getP .s8)))) (by kernel_rfl)
      (stG0 (hsem _ _ h).1.1 fun _ c a7 _ a9 => WP.seq (WP.mono (powK c
        (c.cb.1.hk.sub (by have := c.cb.1.kn; omega_using [this])) a7 (c.cb.1.ns (hsem _ _ h).2.1) a9 hp hpo) fun _ c' =>
        WP.block_append (WP.mono (bufBase_ok c'.cb.1.scr c'.cb.1.ok c'.cb.1.regs (rd := .s7) (t := .t2)
          (by decide) (by decide) (by decide)) fun _ ⟨⟨f7, mu⟩, ku⟩ =>
          WP.mono (getP_ok (c'.keepM ku mu).cb.1.scr c'.cb.1.ok (c'.keepM ku mu).cb.1.regs .s8)
            fun _ ⟨⟨f8, m9⟩, k9⟩ => (fix_PK ((c'.keepM ku mu).keepM k9 m9)).app
              ⟨(k9.gpr (r := .s7) (by decide)).trans f7, f8, trivial⟩)))

/-- `gk`, then `c`. -/
theorem stGK {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : TS v s)
    (hc : ∀ t, Base v t → Lens v v.qb t → arrQ t.mem v.L 0 = v.q → OS v t → MWs v t → WP isa c t Q) :
    WP isa (.seq Sign.gk c) s Q := by
  obtain ⟨-, -, -, -, hp, hpo⟩ := h.vals
  obtain ⟨⟨P, ⟨b, mw⟩⟩, g, -⟩ := h
  obtain ⟨⟨B, ip, I, p0, p24⟩, l, q0, os⟩ := P
  have hL := B.ok
  refine WP.seq (WP.mono (gk_ok hL B.scr B.regs ip I (B.hk.take (by have := B.kn; omega_using [this])) (B.ns g) p0 hp hpo
    p24) fun u ⟨⟨_, _, _, m, o, b'⟩, k⟩ => ?_)
  obtain hb : Body v.L s.mem u.mem := (PLow.body hL o).trans (Body.ofBuf hL b' (by omega_using []))
  obtain K := BKept.ofBody hL hb
  exact hc u (B.step (B.regs.ofBKept k K) k.2.1 k.2.2 K.out (K.word (by decide) (by decide))
      (K.word (by decide) (by decide))) (by rw [Lens, K.word (by decide) (by decide)]; exact l)
    (by rw [keepQ_arr0 hL (bufKeepQ b' (by rcases hL.pl with e | e | e <;> rw [e] <;> decide)),
      keepQ_arr0 hL (PLow.keepQ hL o)]; exact q0) (os.keep k.2.1 k.2.2) ⟨b, by rw [hb.word (by decide)]; exact mw⟩

theorem pinsTl56 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 56) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s9, v.L.Buf), (.s10, BitVec.ofNat 64 v.L.pl)]) (fun _ => rfl)
    fun _ _ h => WP.of_flat (c := .seq Sign.gk (.block CMP)) (by kernel_rfl)
      (stGK (hsem _ _ h) fun _ B _ _ _ _ => (cmp_pre B).mono fun _ ⟨⟨B', iq, a9, a10, _⟩, _⟩ =>
        (B'.fixB.app (fix_envQ iq)).app ⟨a9, a10, trivial⟩)

/-! ## The Q space -/

/-- In the Q space during `body`, with q in its array 0. -/
structure QK (v : VD) (t : State) : Prop where
  base : Base v t
  lens : Lens v v.qb t
  qs : QS t v.L v.key v.sig
  q0 : arrQ t.mem v.L 0 = v.q
  os : OS v t
  mw : MWs v t

theorem QK.frame {v : VD} {s t : State} {rs : List Reg} (h : QK v s) (Q : QS t v.L v.key v.sig) (k : Keep rs s t)
    (K : BKept v.L s.mem t.mem) (hq0 : arrQ t.mem v.L 0 = arrQ s.mem v.L 0) (mw : MWs v t) : QK v t :=
  ⟨h.base.step Q.regs k.2.1 k.2.2 K.out (K.word (by decide) (by decide)) (K.word (by decide) (by decide)),
    by rw [Lens, K.word (by decide) (by decide)]; exact h.lens, Q, hq0.trans h.q0, h.os.keep k.2.1 k.2.2, mw⟩

theorem QK.withQ {v : VD} {s t : State} {rs : List Reg} (h : QK v s) (Q : QS t v.L v.key v.sig) (k : Keep rs s t)
    (qa : QArr v.L s.mem t.mem) : QK v t :=
  have hL := h.base.ok
  h.frame Q k (BKept.ofBody hL (qa.body hL)) (qa.arr0 hL)
    (let ⟨b, w⟩ := h.mw; ⟨b, by rw [(qa.body hL).word (by decide)]; exact w⟩)

theorem QK.qarr {v : VD} {s t : State} {rs : List Reg} (h : QK v s) (k : Keep rs s t) (qa : QArr v.L s.mem t.mem)
    (hr : ∀ r ∈ inRegs ++ regsRegs, r ∉ rs := by decide) : QK v t :=
  h.withQ (h.qs.step k (qa.body h.base.ok) hr) k qa

theorem QK.keepM {v : VD} {s t : State} {rs : List Reg} (h : QK v s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ inRegs ++ regsRegs, r ∉ rs := by decide) : QK v t :=
  h.qarr k (by rw [hm]; exact Outside.refl _ _ _ _) hr

theorem fix_QK {v : VD} {t : State} (h : QK v t) : Fix (fixB v ++ envQ v) t := h.base.fixB.app (fix_envQ h.qs.inq)

/-- Up to `rRanges`' first block, then `c`. -/
theorem stCMP {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : TS v s)
    (hc : ∀ t, QK v t → t.gpr .s9 = v.L.Buf → t.gpr .s10 = BitVec.ofNat 64 v.L.pl → WP isa c t Q) :
    WP isa (.seq Sign.gk (.seq (.block CMP) c)) s Q :=
  stGK h fun _ B l q0 os mw => WP.seq ((cmp_pre B).mono fun t ⟨⟨B', iq, a9, a10, m⟩, k⟩ =>
    hc t ⟨B', by rw [Lens, m]; exact l, ⟨iq, B'.scr, B'.regs⟩, by rw [arrQ, m]; exact q0, os.keep k.2.1 k.2.2,
      let ⟨b, w⟩ := mw; ⟨b, by rw [m]; exact w⟩⟩ a9 a10)

/-- `rRanges` up to the nonce's pointer, then `c`. -/
theorem stR6 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : TS v s)
    (hc : ∀ t, QK v t → WP isa c t Q) :
    WP isa (.seq Sign.gk (.seq (.block CMP) (.seq ModArith.reduce64 (.seq (copy 25 1)
      (.seq (zeroArr 7) c))))) s Q := by
  have hq := h.vals.1
  refine stCMP h fun s₂ K a9 a10 => ?_
  have hL := K.base.ok
  obtain hql : 20 ≤ v.L.ql ∧ v.L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  obtain hpl : 128 ≤ v.L.pl ∧ v.L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega_using [e]
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain e : ∀ j, slot v.L.wq j = 256 + j * (8 * (v.L.wq + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4; have e7 := e 7; have e8 := e 8; have e25 := e 25
  obtain e26 := e 26; have e28 := e 28
  have e2 := K.qs.inq.env
  refine WP.seq (WP.mono (ModArith.reduce64_ok (B := v.L.Q) (Z := 1600) (w := v.L.wq) (D := v.L.Buf) (L := v.L.pl)
    e2.hs (by omega_using [hwq]) (by omega_using [hwq]) (by omega_using [hwq, e4]) e2.a7 e2.s5 e2.t0
    (by show 0 < arrQ s₂.mem v.L 0; rw [K.q0]; omega_using [hq]) (by rw [a9]; exact (BitVec.add_zero _).symm) a10 (by omega_using [hpl])
    (by omega_using [hpl])
    (by have := bufRd hL K.base.scr (o := 0) (k := v.L.pl) (by omega_using [])
        simpa only [off, BitVec.add_zero] using this)
    (buf_apartQ v.L (n := v.L.pl) (by omega_using [hpl]))) fun s₃ ⟨⟨_, o3⟩, k3⟩ => ?_)
  obtain K3 := K.qarr k3 (QArr.of o3 (by omega_using []) (by omega_using [e1, e28]))
  refine WP.seq (WP.mono (copy_ok K3.qs.inq.env (o := 25) (a := 1) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨_, o4⟩, k4⟩ => ?_)
  obtain K4 := K3.qarr k4 (QArr.of o4 (by omega_using [e1, e25]) (by omega_using [e25, e28]))
  exact WP.seq (WP.mono (zeroArr_ok K4.qs.inq.env (j := 7) (by decide)) fun s₅ ⟨⟨_, o5⟩, k5⟩ =>
    hc s₅ (K4.qarr k5 (QArr.of o5 (by omega_using [e1, e7]) (by omega_using [e7, e28]))))

theorem pinsTl67 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 67) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.sig), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun _ _ h => WP.of_flat (c := .seq Sign.gk (.seq (.block CMP) (.seq ModArith.reduce64
      (.seq (copy 25 1) (.seq (zeroArr 7) (.block Verify.ptrR)))))) (by kernel_rfl)
      (stR6 (hsem _ _ h) fun _ K => WP.mono (ptrR_ok K.qs.scr K.base.ok K.qs.regs)
        fun _ ⟨⟨b7, b8, m⟩, k⟩ => (fix_QK (K.keepM k m)).app ⟨b7, b8, trivial⟩)

theorem pinsTl75 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 75) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.key (3 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h => WP.of_flat (c := .seq Sign.gk (.seq (.block CMP)
      (.seq ModArith.reduce64 (.seq (copy 25 1) (.seq (zeroArr 7) (.seq (.block Verify.ptrR) (.seq (loadArr 6)
        (.block Sign.ptrX)))))))) (by kernel_rfl)
      (stR6 (hsem _ _ h) fun _ K => by
        have hL := K.base.ok
        have hql : 20 ≤ _ ∧ _ ≤ 32 := K.base.ql
        have hwq := hL.wq_ge
        refine WP.seq (WP.mono (ptrR_ok K.qs.scr hL K.qs.regs) fun _ ⟨⟨b7, b8, m⟩, k⟩ => ?_)
        obtain K1 := K.keepM k m
        refine WP.seq (WP.mono (loadQ_ok (j := 6) K1.qs hL (by decide) (K1.base.ns (hsem _ _ h).2.1) b7 b8
          (by omega_using [hql]) (by omega_using [hwq])) fun _ ⟨⟨Q2, _, _, o2⟩, k2⟩ => ?_)
        obtain K2 := K1.withQ Q2 k2 (QArr.of o2 (by simp only [Lay.slot_eq]; omega_using []) (by simp only [Lay.slot_eq]; omega_using []))
        exact WP.mono (ptrX_ok K2.qs.scr hL K2.qs.regs) fun _ ⟨⟨c7, c8, m'⟩, k'⟩ =>
          (fix_QK (K2.keepM k' m')).app ⟨c7, c8, trivial⟩)

/-- `rRanges` after `gk`, then `c`. -/
theorem stRR {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : TS v s)
    (hc : ∀ t, QK v t → arrQ t.mem v.L 25 < v.q → WP isa c t Q) :
    WP isa (.seq Sign.gk (.seq Sign.rRanges c)) s Q := by
  have hq := h.vals.1
  refine stGK h fun t B l q0 os ⟨b, mw⟩ => ?_
  have hL := B.ok
  refine WP.seq (WP.mono (rRanges_ok hL B.scr B.regs os.key (B.ns h.2.1) (by rw [q0]; omega_using [hq]) mw)
    fun u ⟨⟨Q, r25, m, ⟨m₁, fa, fb⟩⟩, k⟩ => hc u ⟨B.step Q.regs k.2.1 k.2.2 ?_ ?_ ?_, ?_, Q, ?_, os.keep k.2.1 k.2.2,
      ⟨_, m⟩⟩ (by rw [r25, q0]; exact Nat.mod_lt _ (by omega_using [hq])))
  all_goals have K : BKept v.L t.mem u.mem := (BKept.ofBody hL (fa.body hL)).trans (BKept.ofMask hL fb)
  · exact K.out
  · exact K.word (by decide) (by decide)
  · exact K.word (by decide) (by decide)
  · rw [Lens, K.word (by decide) (by decide)]; exact l
  · exact (mask_keepQ' hL fa fb).trans q0

/-- `rrQ` after `rRanges`, then `c`. -/
theorem stRQ {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : TS v s)
    (hc : ∀ t, QK v t → QInv t v.L → arrQ t.mem v.L 24 = 2 ^ (128 * v.L.wq) % v.q → arrQ t.mem v.L 25 < v.q →
      WP isa c t Q) :
    WP isa (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ c))) s Q := by
  obtain ⟨hq, hqo, -⟩ := h.vals
  refine stRR h fun t K r25 => ?_
  have hL := K.base.ok
  exact WP.seq (WP.mono (rrQ25_ok hL K.qs (by rw [K.q0]; exact hq) (by rw [K.q0]; exact hqo))
    fun u ⟨⟨Q, I, h24, a25, qa⟩, k⟩ => hc u (K.frame Q k (BKept.ofBody hL (qa.body hL)) (qa.arr0 hL)
      (let ⟨b, w⟩ := K.mw; ⟨b, by rw [(qa.body hL).word (by decide)]; exact w⟩)) I (by rw [h24, K.q0])
      (by rw [a25 25 (by decide) (by decide)]; exact r25))

theorem pinsTl118 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 118) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.L.Buf), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun v _ h => WP.of_flat (c := .seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.minus2 (.block Verify.ptrBuf))))) (by kernel_rfl)
      (stRQ (hsem _ _ h) fun _ K _ _ _ => by
        have hL := K.base.ok
        refine WP.seq (WP.mono (minus2_ok K.qs.inq.env (show 2 ≤ arrQ _ v.L 0 by rw [K.q0]; exact (hsem _ _ h).vals.1))
          fun _ ⟨⟨_, o⟩, k⟩ => ?_)
        obtain K' := K.qarr k (QArr.of o (by simp only [Lay.slot_eq]; omega_using []) (by simp only [Lay.slot_eq]; omega_using []))
        exact WP.mono (ptrBuf_ok K'.qs.scr hL K'.qs.regs) fun _ ⟨⟨b7, b8, m⟩, k'⟩ =>
          (fix_QK (K'.keepM k' m)).app ⟨b7, b8, trivial⟩)

/-- `qMinus2` after `rrQ`, then `c`. -/
theorem stQM {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : TS v s)
    (hc : ∀ t, QK v t → QInv t v.L → arrQ t.mem v.L 24 = 2 ^ (128 * v.L.wq) % v.q → arrQ t.mem v.L 25 < v.q →
      WP isa c t Q) :
    WP isa (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ (.seq Verify.qMinus2 c)))) s Q := by
  obtain ⟨hq, -, hql, -⟩ := h.vals
  refine stRQ h fun t K I h24 r25 => ?_
  have hL := K.base.ok
  exact WP.seq (WP.mono (qMinus2_ok hL K.qs (by rw [K.q0]; exact hq) (by rw [K.q0]; exact hql))
    fun u ⟨⟨Q, _, kj, w0, qb⟩, k⟩ => hc u (K.frame Q k (BKept.ofBody hL (qb.body hL)) (qb.arr0 hL)
      (let ⟨b, w⟩ := K.mw; ⟨b, by rw [(qb.body hL).word (by decide)]; exact w⟩)) (I.keepW w0 (k.gpr (by decide)))
      (by rw [kj 24 (by decide) (by decide)]; exact h24) (by rw [kj 25 (by decide) (by decide)]; exact r25))

theorem pinsTl121 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 121) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.sig), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun _ _ h => WP.of_flat (c := .seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.qMinus2 (.block Verify.ptrR))))) (by kernel_rfl)
      (stQM (hsem _ _ h) fun _ K _ _ _ => WP.mono (ptrR_ok K.qs.scr K.base.ok K.qs.regs)
        fun _ ⟨⟨b7, b8, m⟩, k⟩ => (fix_QK (K.keepM k m)).app ⟨b7, b8, trivial⟩)

theorem pinsTl131 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 131) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.L.Buf), (.s8, BitVec.ofNat 64 v.L.ql), (.s9, off v.L.Buf 0),
      (.s10, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun v _ h => WP.of_flat (c := .seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.qMinus2 (.seq (.block Verify.ptrR) (.seq (loadArr 4) (.seq (copy 1 24)
        (.block (Verify.ptrBuf ++ [.addi .s9 .s7 0, .addi .s10 .s8 0]))))))))) (by kernel_rfl)
      (stQM (hsem _ _ h) fun _ K _ _ _ => by
        have hL := K.base.ok
        have hql : 20 ≤ _ ∧ _ ≤ 32 := K.base.ql
        have hwq := hL.wq_ge
        refine WP.seq (WP.mono (ptrR_ok K.qs.scr hL K.qs.regs) fun _ ⟨⟨b7, b8, m⟩, k⟩ => ?_)
        obtain K1 := K.keepM k m
        refine WP.seq (WP.mono (loadQ_ok (j := 4) K1.qs hL (by decide) (K1.base.ns (hsem _ _ h).2.1) b7 b8
          (by omega_using [hql]) (by omega_using [hwq])) fun _ ⟨⟨Q2, _, _, o2⟩, k2⟩ => ?_)
        obtain K2 := K1.withQ Q2 k2 (QArr.of o2 (by simp only [Lay.slot_eq]; omega_using []) (by simp only [Lay.slot_eq]; omega_using []))
        refine WP.seq (WP.mono (copy_ok K2.qs.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
          fun _ ⟨⟨_, o3⟩, k3⟩ => ?_)
        obtain K3 := K2.qarr k3 (QArr.of o3 (by simp only [Lay.slot_eq]; omega_using []) (by simp only [Lay.slot_eq]; omega_using []))
        refine WP.block_append (WP.mono (ptrBuf_ok K3.qs.scr hL K3.qs.regs) fun t ⟨⟨c7, c8, m4⟩, k4⟩ =>
          WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off v.L.Buf 0 ∧
            u.gpr .s10 = BitVec.ofNat 64 v.L.ql ∧ u.mem = t.mem) (by brun [c7, c8, BitVec.add_zero]) (by decide)
            (by rfl)) fun _ ⟨⟨c9, c10, m5⟩, k5⟩ => ?_)
        exact (fix_QK ((K3.keepM k4 m4).keepM k5 m5)).app ⟨(k5.gpr (r := .s7) (by decide)).trans c7,
          (k5.gpr (r := .s8) (by decide)).trans c8, c9, c10, trivial⟩)

/-- `inverseK` after `qMinus2`, then `c`. -/
theorem stINV {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : TS v s)
    (hc : ∀ t, QK v t → QInv t v.L → arrQ t.mem v.L 24 = 2 ^ (128 * v.L.wq) % v.q → arrQ t.mem v.L 4 < v.q →
      arrQ t.mem v.L 25 < v.q → WP isa c t Q) :
    WP isa (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ (.seq Verify.qMinus2
      (.seq Sign.inverseK c))))) s Q := by
  obtain ⟨hq, hqo, -⟩ := h.vals
  refine stQM h fun t K I h24 r25 => ?_
  have hL := K.base.ok
  exact WP.seq (WP.mono (inverseK_ok hL K.qs I (K.base.ns h.2.1) (by rw [K.q0]; exact hq) (by rw [K.q0]; exact hqo)
      (by rw [K.q0]; exact h24))
    fun u ⟨⟨Q, I', w4, k24, qa⟩, k⟩ => hc u (K.withQ Q k qa) I' (by rw [k24 24 (by decide) (by decide)]; exact h24)
      (by rw [w4, K.q0]; exact Nat.mod_lt _ (by omega_using [hq])) (by rw [k24 25 (by decide) (by decide)]; exact r25))

theorem pinsTl172 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 172) [.s6, .s11, .ra, .a7, .s5, .t0, .s8, .t3, .a0] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s8, BitVec.ofNat 64 v.qb), (.t3, BitVec.ofNat 64 v.d),
      (.a0, BitVec.ofNat 64 (if v.qb < v.d then 1 else 0))]) (fun _ => rfl) fun v _ h => by
    obtain hqb := (hsem _ _ h).vals.2.2.2.1
    refine WP.of_flat (c := .seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.qMinus2 (.seq Sign.inverseK (.block SLB)))))) (by kernel_rfl)
      (stINV (hsem _ _ h) fun _ K _ _ _ _ => ?_)
    have hL := K.base.ok
    obtain hp : v.L.pl < 2 ^ 16 := by have := K.base.pl; simp only [Nat.reducePow]; omega_using [this]
    obtain hq : v.L.ql < 2 ^ 16 := by have := K.base.ql; simp only [Nat.reducePow]; omega_using [this]
    obtain h3 : v.qb < 2 ^ 16 := by have := K.base.ql; simp only [Nat.reducePow]; omega_using [hqb, hq]
    obtain h4 : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega_using []
    refine WP.block_append (WP.block_append (WP.mono (getQb_ok K.base.scr hL K.base.regs.s6 .s8)
      fun u ⟨⟨a8, mu⟩, ku⟩ => WP.mono (getD_ok (K.base.scr.congr ku.2.2) hL
        (by rw [ku.gpr (by decide)]; exact K.base.regs.s6) .t3) fun w ⟨⟨b3, mw⟩, kw⟩ => ?_))
    have l := K.lens
    rw [Lens] at l
    rw [l, pack_qb hp hq h3 h4] at a8
    rw [mu, l, pack_d hp hq h3 h4] at b3
    obtain a8' : w.gpr .s8 = BitVec.ofNat 64 v.qb := (kw.gpr (by decide)).trans a8
    obtain hsub := sub_shr63 (a := v.qb) (b := v.d) (by simp only [Nat.reducePow] at *; omega_using [h3])
      (by simp only [Nat.reducePow] at *; omega_using [h4])
    refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = BitVec.ofNat 64 (if v.qb < v.d then 1 else 0) ∧
      t.mem = w.mem) (by brun [a8', b3, exec_shift_d (show 63 < 64 by decide), hsub]) (by decide) (by rfl))
      fun t ⟨⟨c0, mt⟩, kt⟩ => ?_
    obtain K' := ((K.keepM ku mu).keepM kw mw).keepM kt mt
    exact (fix_QK K').app ⟨(kt.gpr (r := .s8) (by decide)).trans a8', (kt.gpr (r := .t3) (by decide)).trans b3, c0,
      trivial⟩

theorem pinsTl174 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 174) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, v.dig), (.s8, BitVec.ofNat 64 (min v.d v.qb))])
    (fun _ => rfl) fun v _ h => by
    refine WP.of_flat (c := .seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.qMinus2 (.seq Sign.inverseK (.seq Verify.scalarLen (.block [.load .d .s7 .s6 hDigest]))))))) (by kernel_rfl)
      (stINV (hsem _ _ h) fun _ K _ _ _ _ => ?_)
    have hL := K.base.ok
    obtain h3 : v.qb < 2 ^ 16 := by
      have := K.base.ql; have := (hsem _ _ h).vals.2.2.2.1; simp only [Nat.reducePow]; omega_arith
    obtain h4 : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega_using []
    refine WP.seq (WP.mono (scalarLen_ok K.base.scr hL K.base.regs.s6 K.lens h3 h4) fun s₀ ⟨⟨a8, m0⟩, k0⟩ => ?_)
    obtain K0 := K.keepM k0 m0
    obtain ⟨hin, hal⟩ := ScrL.hdr K0.base.scr hL (d := 8) (by decide) (by decide)
    refine WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = v.dig ∧ u.mem = s₀.mem)
      (by brun [hDigest, K0.base.regs.s6, hin, hal]; exact K0.base.dig8 (hsem _ _ h).2.1.full) (by rfl) (by rfl))
      fun _ ⟨⟨a7, m1⟩, k1⟩ => ?_
    exact (fix_QK (K0.keepM k1 m1)).app ⟨a7, (k1.gpr (r := .s8) (by decide)).trans a8, trivial⟩

theorem pinsTl188 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 188) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.key (3 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.ql),
      (.s9, off v.key (3 * v.L.pl + v.L.ql)), (.s10, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl) fun v _ h => by
    refine WP.of_flat (c := .seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.qMinus2 (.seq Sign.inverseK (.seq Verify.scalar (.seq (zeroArr 7) (.seq (Sign.addMod 6 6 7)
        (.block (Sign.ptrX ++ [.addi .s9 .s7 0, .addi .s10 .s8 0])))))))))) (by kernel_rfl)
      (stINV (hsem _ _ h) fun _ K _ _ _ _ => ?_)
    have hL := K.base.ok
    have hwq := hL.wq_ge
    have hqs := hL.qslot
    obtain e : ∀ j, slot v.L.wq j = 256 + j * (8 * (v.L.wq + 2)) := fun _ => rfl
    obtain e0 := e 0; have e1 := e 1; have e6 := e 6; have e7 := e 7; have e8 := e 8; have e28 := e 28
    obtain hqb := (hsem _ _ h).vals.2.2.2.1
    obtain h4 : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega_using []
    refine WP.seq (WP.mono (scalar_ok hL K.qs (K.base.dig8 (hsem _ _ h).2.1.full) K.lens hqb h4
      (K.base.hdg.take (Nat.min_le_left _ _))) fun s₁ ⟨⟨Q1, v6, o1⟩, k1⟩ => ?_)
    obtain K1 := K.withQ Q1 k1 (QArr.of o1 (by omega_using [e1, e6]) (by omega_using [e6, e28]))
    refine WP.seq (WP.mono (zeroArr_ok K1.qs.inq.env (j := 7) (by decide)) fun s₂ ⟨⟨z7, o2⟩, k2⟩ => ?_)
    obtain K2 := K1.qarr k2 (QArr.of o2 (by omega_using [e1, e7]) (by omega_using [e7, e28]))
    obtain z2 : arrQ s₂.mem v.L 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt _ v.dig (min v.d v.qb)) :=
      (o2.wordsVal (by omega_using [e6, e7]) (by omega_using [hwq, e6])).trans v6
    refine WP.seq (WP.mono (addMod_ok K2.qs.inq.env (o := 6) (a := 6) (b := 7) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by show arrQ s₂.mem v.L 6 + arrQ s₂.mem v.L 7 < 2 * arrQ s₂.mem v.L 0
          rw [z2, show arrQ s₂.mem v.L 7 = 0 from z7, K2.q0, Nat.add_zero]; exact (hsem _ _ h).hz _))
      fun s₃ ⟨⟨_, fr3⟩, k3⟩ => ?_)
    obtain K3 := K2.qarr k3 (fr3.qarr (by decide) (by decide))
    refine WP.block_append (WP.mono (ptrX_ok K3.qs.scr hL K3.qs.regs) fun s₄ ⟨⟨b7, b8, m4⟩, k4⟩ =>
      WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off v.key (3 * v.L.pl + v.L.ql) ∧
        u.gpr .s10 = BitVec.ofNat 64 v.L.ql ∧ u.mem = s₄.mem) (by brun [b7, b8, BitVec.add_zero]) (by decide) (by rfl))
      fun _ ⟨⟨c9, c10, m5⟩, k5⟩ => ?_)
    exact (fix_QK ((K3.keepM k4 m4).keepM k5 m5)).app ⟨(k5.gpr (r := .s7) (by decide)).trans b7,
      (k5.gpr (r := .s8) (by decide)).trans b8, c9, c10, trivial⟩

/-- `sValue` after `inverseK`, then `c`. -/
theorem stSV {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : TS v s)
    (hc : ∀ t, QK v t → WP isa c t Q) :
    WP isa (.seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ (.seq Verify.qMinus2
      (.seq Sign.inverseK (.seq Sign.sValue c)))))) s Q := by
  obtain ⟨hq, hqo, -, hqb, -⟩ := h.vals
  obtain bd := VG.Proof.Dsa.supported_bounds h.2.2.sz
  refine stINV h fun t K I h24 h4 r25 => ?_
  have hL := K.base.ok
  obtain hd : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega_using []
  exact WP.seq (WP.mono (sValue_ok hL K.qs I (K.base.dig8 h.2.1.full) K.lens hqb hd
      (K.base.hdg.take (Nat.min_le_left _ _)) K.os.key (by rw [K.q0]; omega_using [hq, hqo]) (by rw [K.q0]; exact hqo)
      (by rw [K.q0]; exact h24) (by rw [K.q0]; exact h4) (by rw [K.q0]; exact r25) (by rw [K.q0]; exact h.hz _))
    fun u ⟨⟨Q, _, _, _, qa⟩, k⟩ => hc u (K.withQ Q k qa))

theorem pinsTl259 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → TS v u) :
    Pins (At Φ FTl 259) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, oOf v), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl)
    fun v _ h => by
    refine WP.of_flat (c := .seq Sign.gk (.seq Sign.rRanges (.seq Verify.rrQ
      (.seq Verify.qMinus2 (.seq Sign.inverseK (.seq Sign.sValue (.seq (zeroArr 7)
        (.seq (.block [.load .d .a4 .s6 hMask]) (.seq (Sign.nonZero 6) (.seq (.block [.addi .s4 .a4 0])
          (.seq (Sign.sel 1 25 7) (.seq (Sign.sel 2 6 7) (.block ([.load .d .s7 .s6 Sign.hOut] ++ getQ .s8))))))))))))))
      (by kernel_rfl) (stSV (hsem _ _ h) fun _ K => ?_)
    have hL := K.base.ok
    have hwq := hL.wq_ge
    have hqs := hL.qslot
    obtain e : ∀ j, slot v.L.wq j = 256 + j * (8 * (v.L.wq + 2)) := fun _ => rfl
    obtain e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e6 := e 6; have e7 := e 7
    obtain e8 := e 8; have e25 := e 25; have e26 := e 26; have e28 := e 28
    obtain ⟨b, hm⟩ := K.mw
    refine WP.seq (WP.mono (zeroArr_ok K.qs.inq.env (j := 7) (by decide)) fun s₁ ⟨⟨z7, o1⟩, k1⟩ => ?_)
    obtain qa1 : QArr v.L _ s₁.mem := QArr.of o1 (by omega_using [e1, e7]) (by omega_using [e7, e28])
    obtain K1 := K.qarr k1 qa1
    obtain ⟨hld, hal⟩ := ScrL.hdr K1.qs.scr hL (d := 0) (by decide) (by decide)
    obtain hw1 : word s₁.mem v.L.S hMask = mask b := by rw [(qa1.body hL).word (by decide)]; exact hm
    refine WP.seq (WP.mono (WP.keep [.a4] (Q := fun u => u.gpr .a4 = mask b ∧ u.mem = s₁.mem)
      (by brun [hMask, K1.qs.regs.s6, hld, hal]; exact hw1) (by decide) (by rfl)) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_)
    obtain K2 := K1.keepM k2 m2
    refine WP.seq (WP.mono (nonZero_ok K2.qs.inq.env (a := 6) (c := 0) (by decide) (by rw [m2]; exact z7) a4)
      fun s₃ ⟨⟨b4, m3⟩, k3⟩ => ?_)
    obtain K3 := K2.keepM k3 m3
    refine WP.seq (WP.mono (WP.keep [.s4] (Q := fun u => u.gpr .s4 = mask (b && decide (wordsVal s₂.mem v.L.Q
        (slot v.L.wq 6) v.L.wq ≠ 0)) ∧ u.mem = s₃.mem)
      (by brun [b4, BitVec.add_zero]) (by decide) (by rfl)) fun s₄ ⟨⟨a20, m4⟩, k4⟩ => ?_)
    obtain K4 := K3.keepM k4 m4
    refine WP.seq (WP.mono (sel_ok K4.qs.inq.env (o := 1) (a := 25) (t := 7) (by decide) (by decide)
      (by decide) (by decide) (by decide) a20) fun s₅ ⟨⟨_, o5⟩, k5⟩ => ?_)
    obtain K5 := K4.qarr k5 (QArr.of o5 (by omega_using []) (by omega_using [e1, e28]))
    refine WP.seq (WP.mono (sel_ok K5.qs.inq.env (o := 2) (a := 6) (t := 7) (by decide) (by decide)
      (by decide) (by decide) (by decide) ((k5.gpr (by decide)).trans a20)) fun s₆ ⟨⟨_, o6⟩, k6⟩ => ?_)
    obtain K6 := K5.qarr k6 (QArr.of o6 (by omega_using [e1, e2]) (by omega_using [e2, e28]))
    obtain ⟨hld', hal'⟩ := ScrL.hdr K6.qs.scr hL (d := 24) (by decide) (by decide)
    refine WP.block_append (WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = oOf v ∧ u.mem = s₆.mem)
      (by brun [Sign.hOut, K6.qs.regs.s6, hld', hal']; exact K6.base.hout _ (hsem _ _ h).2.1.out) (by decide) (by rfl))
      fun s₇ ⟨⟨a7, m7⟩, k7⟩ => WP.mono (getQ_ok (K6.qs.scr.congr k7.2.2) hL (K6.qs.regs.keepM k7 m7) .s8)
        fun _ ⟨⟨a8, m8⟩, k8⟩ => ?_)
    exact (fix_QK ((K6.keepM k7 m7).keepM k8 m8)).app ⟨(k8.gpr (r := .s7) (by decide)).trans a7, a8, trivial⟩

/-! ## The relations -/

/-- A level's run past a cut, from a run of the whole list. -/
theorem run_drop {Φ : VD → State → Prop} {F G : List (Prog isa)} {n : Nat}
    (hrun : ∀ v s, Φ v s → WP isa (Code.seqL F) s fun _ => True) (hd : F.drop n = G) :
    ∀ v s, At Φ F n v s → WP isa (Code.seqL G) s fun _ => True := by
  intro v s h
  obtain h' := at_step hrun (m := n + G.length) (Nat.le_add_right _ _) h
  obtain e : (F.drop n).take (n + G.length - n) = G := by
    rw [hd, Nat.add_sub_cancel_left, List.take_length]
  obtain ⟨t, u, ex, _⟩ := h'
  exact ⟨t, u, by rw [VG.Proof.Bignum.RISCV64.seg, e] at ex; exact ex, trivial⟩

theorem relCT_flat {P : State → State → Prop} {c : Prog isa} (h : RelCT isa P c fun _ _ => True) :
    RelCT isa P (Code.seqL c.flat) fun _ _ => True :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_flat.mpr e₁) (exec_flat.mpr e₂)

/-- The tail, from a level whose states are in its phase. -/
theorem tail_rel {Ψ : VD → State → Prop} (runT : ∀ v s, Ψ v s → WP isa (Code.seqL FTl) s fun _ => True)
    (hsem : ∀ v u, Ψ v u → TS v u) : RelCT isa (Two Ψ) Sign.tail fun _ _ => True := by
  refine chain_start (chain_cons runT (m := 2) (by decide) (two_taint _ (pinsTl0 hsem) (by taint_decide)) ?_)
  refine chain_cons runT (m := 12) (by decide) (two_taint _ (pinsTl2 hsem) (by taint_decide)) ?_
  refine chain_cons runT (m := 53) (by decide) (two_taint _ (pinsTl12 hsem) (by taint_decide)) ?_
  refine chain_cons runT (m := 56) (by decide) (two_taint _ (pinsTl53 hsem) (by taint_decide)) ?_
  refine chain_cons runT (m := 67) (by decide) (two_taint _ (pinsTl56 hsem) (by taint_decide)) ?_
  refine chain_cons runT (m := 75) (by decide) (two_taint _ (pinsTl67 hsem) (by taint_decide)) ?_
  refine chain_cons runT (m := 118) (by decide) (two_taint _ (pinsTl75 hsem) (by taint_decide)) ?_
  refine chain_cons runT (m := 121) (by decide) (two_taint _ (pinsTl118 hsem) (by taint_decide)) ?_
  refine chain_cons runT (m := 131) (by decide) (two_taint _ (pinsTl121 hsem) (by taint_decide)) ?_
  refine chain_cons runT (m := 172) (by decide) (two_taint _ (pinsTl131 hsem) (by taint_decide)) ?_
  refine chain_cons runT (m := 174) (by decide) (two_taint _ (pinsTl172 hsem) (by taint_decide)) ?_
  refine chain_cons runT (m := 188) (by decide) (two_taint _ (pinsTl174 hsem) (by taint_decide)) ?_
  refine chain_cons runT (m := 259) (by decide) (two_taint _ (pinsTl188 hsem) (by taint_decide)) ?_
  exact two_taint _ (pinsTl259 hsem) (by taint_decide)

theorem drop64 : FBs.drop 64 = FTl := by kernel_rfl

/-- `body`, from a level whose states are in its phase: `keyPair`'s cuts, then
the tail's. -/
theorem body_relS {Φ : VD → State → Prop} (runB : ∀ v s, Φ v s → WP isa (Code.seqL FBs) s fun _ => True)
    (hsem : ∀ v u, Φ v u → SBs v u) : RelCT isa (Two Φ) Sign.body fun _ _ => True := by
  refine chain_start (chain_cons runB (m := 2) (by decide) (two_taint _ (pinsBs0 hsem) (by taint_decide)) ?_)
  refine chain_cons runB (m := 12) (by decide) (two_taint _ (pinsBs2 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 53) (by decide) (two_taint _ (pinsBs12 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 64) (by decide) (two_taint _ (pinsBs53 hsem) (by taint_decide)) ?_
  rw [drop64]
  exact relCT_flat (tail_rel (run_drop runB drop64) fun _ _ h =>
    at_sem (Φ := Φ) (F := FBs) (n := 64) (M := TS)
      (fun _ _ h' => WP.of_flat (c := Sign.keyPair) (by decide +kernel) (kp_TS (hsem _ _ h'))) h)

theorem sign_ct : ConstantTime isa sContract.pre sContract.pub Sign.sign :=
  RelCT.constantTime ((sign_rel (body_relS runBs onSBs)).mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdS s, ⟨hs, rfl⟩, ⟨ht, (vdS_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.RISCV64.CT
