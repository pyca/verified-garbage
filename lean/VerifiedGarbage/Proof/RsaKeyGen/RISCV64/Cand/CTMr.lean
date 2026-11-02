module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.CTBase
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCallCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.CTBase
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCallCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Loop
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on RISC-V: the witnesses' loop in constant time

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/{CTLoop,CTDraw,CTMr}.lean`), over
RISC-V's blinded loop (`Proof/MillerRabin/RISCV64/Blinded/LoopCT.lean`).
`mr_ct`: two runs of `Witness.millerRabin` from calls with the same public
data (`KRel`), their working spaces prepared (`LCtx`), with the same stack
pointer, leak the same trace. Unlike the blinded loop, the two runs' candidates
and tapes differ: the working space's registers, the octets read and the tape's
length are the same (`pins_env`), and so is every branch:

* the octets left before each draw (`check_ok`) are a function of the
  witnesses so far;
* each witness's round passes in both runs or in neither (`pass_agree`), and
  the loop's iterations left are the same (`n0_eq`), both because the shape of
  the test's result is (`shape_eq`, from `shape_agree`);
* the round's call leaks only the working space (`roundCall_ctw`).

The taint analysis treats memory as secret, so the trace is cut after the
loads whose values the next pieces address with (the tape's address and the
octets read, `loadA`) and before the round's call, whose precondition is
correctness's (`lw_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum
open VG.Impl.MillerRabin.RISCV64.Search (ldh sth hStat hUsed loadDraw tapeShort)
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (Prep RcPost RcStk RC RCw RcW roundCall_ok roundCall_ctw)
open VG.Proof.Bignum (slot Frm word off)
open VG.Spec.RsaKeyGen (Rand)
open VG.Proof.RsaKeyGen (wit seg)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite)

/-! ## A run's loop -/

/-- The loop's public data: the call's (`pubOf`), and the loop's stack pointer. -/
abbrev KD : Type := CD × Addr

/-- The call from `s0` with the public data `a`, and its witnesses' loop from
`σ`: the working space prepared for the candidate, which is neither too close
to `p` nor shares a factor with `e`. -/
structure LCtx (a : CD) (s0 σ : State) : Prop where
  krel : KRel a s0
  t3 : T3 s0 (cw s0) (candOf s0) σ
  ncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false
  gcd : Nat.gcd (candOf s0 - 1) (Spec.Rsa.os2ip (eB s0)) = 1

/-- The loop's invariant (`LInv`) for the call from `s0`. -/
abbrev LI (s0 σ s : State) (k n : Nat) : Prop :=
  LInv σ s (stackArg s0 1) (s0.gpr .a7) (sL s0) (cw s0) (candOf s0) (rL s0)
    (VG.Proof.RsaKeyGen.checksW (cw s0)) (rB s0) k n

theorem rB_len (s0 : State) : (rB s0).length = rL s0 := bytesAt_len _ _ _

section
variable {a : CD} {s0 s0' σ σ' : State}

theorem LCtx.hB (C : LCtx a s0 σ) (C' : LCtx a s0' σ') : stackArg s0 1 = stackArg s0' 1 :=
  C.krel.arg C'.krel (i := 1) (by decide)

theorem LCtx.hL (C : LCtx a s0 σ) (C' : LCtx a s0' σ') : sL s0 = sL s0' := by
  show (stackArg s0 2).toNat = (stackArg s0' 2).toNat
  rw [C.krel.arg C'.krel (i := 2) (by decide)]

theorem LCtx.hw (C : LCtx a s0 σ) (C' : LCtx a s0' σ') : cw s0 = cw s0' := by
  simp only [cw, C.krel.oL_eq C'.krel]

theorem LCtx.hR (C : LCtx a s0 σ) (C' : LCtx a s0' σ') : s0.gpr .a7 = s0'.gpr .a7 :=
  C.krel.reg C'.krel (by decide)

theorem LCtx.hrl (C : LCtx a s0 σ) (C' : LCtx a s0' σ') : rL s0 = rL s0' := C.krel.rL_eq C'.krel

theorem candS_eq (hp : CIn s0) (hav : oL s0 ≤ rL s0) : candS s0 = candOf s0 := by
  obtain ⟨hw, -, -⟩ := cw_facts hp
  unfold candS candOf rB
  rw [take_bytesAt _ _ hav, hw, show 8 * (8 * cw s0) = 64 * cw s0 by omega]

theorem LCtx.hav (C : LCtx a s0 σ) : oL s0 ≤ rL s0 := by
  rw [C.t3.tc.hw]; exact C.t3.tc.h8

/-- The shape of the test's result is the same in both runs. -/
theorem shape_eq (C : LCtx a s0 σ) (C' : LCtx a s0' σ') :
    VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0))) =
      VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0') ((rB s0').drop (8 * cw s0'))) := by
  have hp := C.krel.1
  have hp' := C'.krel.1
  have hav := C.hav
  have hav' := C'.hav
  obtain ⟨hw, -, -⟩ := cw_facts hp
  obtain ⟨hw', -, -⟩ := cw_facts hp'
  have e := shape_agree C.krel C'.krel hav
    (by rw [candS_eq hp hav, show 8 * oL s0 = 64 * cw s0 by omega]; exact C.ncl)
    (by rw [candS_eq hp hav, show 8 * oL s0 = 64 * cw s0 by omega]; exact C.t3.noc)
    (by rw [candS_eq hp hav]; exact C.gcd)
  rwa [candS_eq hp hav, candS_eq hp' hav', hw, hw'] at e

end

section
variable {s0 σ : State} {w c : Nat}

/-- The test is the loop of `mrStep` with the checks for `w` words. -/
theorem T3.hpt (h : T3 s0 w c σ) :
    Spec.RsaKeyGen.primalityTest c ((rB s0).drop (8 * w)) =
      Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c (VG.Proof.RsaKeyGen.checksW w) (Spec.Rsa.splitTwos (c - 1)).1
        (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) ((rB s0).drop (8 * w)) := by
  have hpt := VG.Proof.RsaKeyGen.primalityTest_cand (by have := h.tc.hw4; omega) h.tc.shape ((rB s0).drop (8 * w))
  rwa [VG.Proof.RsaKeyGen.checksW_eq w (by have := h.tc.hw64; omega) h.tc.hw4] at hpt

/-- The tape at the loop's start. -/
theorem T3.tape (h : T3 s0 w c σ) : Spec.Rsa.bytesAt σ.mem (s0.gpr .a7) (rL s0) = rB s0 := by
  have hf := h.ctx.fr
  have hp := hf.pre
  have hrl : rL s0 < 2 ^ 64 := (stackArg s0 0).isLt
  exact bytes_keep hf.out hrl fun ρ hρ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · exact hp.oR.symm
    · exact hp.uR.symm
    · exact hp.rS
    · exact hp.Fr.symm

end

/-- The loop's iterations, `1` less, for the call from `s0`. -/
def n0 (s0 : State) : Nat :=
  iters0 (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (cw s0) (rB s0)

theorem n0_eq {a : CD} {s0 s0' σ σ' : State} (C : LCtx a s0 σ) (C' : LCtx a s0' σ') : n0 s0 = n0 s0' := by
  unfold n0 iters0
  rw [← C.t3.hpt, ← C'.t3.hpt, shape_eq C C', rB_len, rB_len, C.hrl C', C.hw C']

/-- The `k`-th witness passes in both runs or in neither. -/
theorem pass_agree {a : CD} {s0 s0' σ σ' s s' : State} {k n n' : Nat} (C : LCtx a s0 σ) (C' : LCtx a s0' σ')
    (h : LI s0 σ s k n) (h' : LI s0' σ' s' k n') (hav : 8 * cw s0 + 8 * cw s0 * k + 8 * cw s0 ≤ rL s0) :
    Proof.MillerRabin.Round.round (candOf s0) (wit (candOf s0) (8 * cw s0) (rB s0) (8 * cw s0 + 8 * cw s0 * k)).1 =
      Proof.MillerRabin.Round.round (candOf s0')
        (wit (candOf s0') (8 * cw s0') (rB s0') (8 * cw s0' + 8 * cw s0' * k)).1 := by
  have hw := C.hw C'
  have hl : (rB s0).length = (rB s0').length := by rw [rB_len, rB_len, C.hrl C']
  have hav' : 8 * cw s0' + 8 * cw s0' * k + 8 * cw s0' ≤ rL s0' := by rw [← hw, ← C.hrl C']; exact hav
  have hw4 := h.ctx.prep.env.hw
  have hw4' := h'.ctx.prep.env.hw
  have p₁ := VG.Proof.RsaKeyGen.mr_pass (a := (Spec.Rsa.splitTwos (candOf s0 - 1)).1)
    (m := (Spec.Rsa.splitTwos (candOf s0 - 1)).2) h.mr.go h.ctx.wb (by omega) (by rw [rB_len]; exact hav)
  have p₂ := VG.Proof.RsaKeyGen.mr_pass (a := (Spec.Rsa.splitTwos (candOf s0' - 1)).1)
    (m := (Spec.Rsa.splitTwos (candOf s0' - 1)).2) h'.mr.go h'.ctx.wb (by omega) (by rw [rB_len]; exact hav')
  rw [Prod.eta, ← h.mr.run, ← C.t3.hpt] at p₁
  rw [Prod.eta, ← h'.mr.run, ← C'.t3.hpt] at p₂
  change Spec.RsaKeyGen.mrIteration _ _ _ _ = Spec.RsaKeyGen.mrIteration _ _ _ _
  unfold wit
  rw [← p₁, ← p₂, shape_eq C C', hl, hw]

/-! ## What two runs share -/

theorem env_pins {s₁ s₂ : State} {B₁ B₂ : Addr} {Z₁ Z₂ w₁ w₂ : Nat} (e₁ : Env s₁ B₁ Z₁ w₁)
    (e₂ : Env s₂ B₂ Z₂ w₂) (hB : B₁ = B₂) (hw : w₁ = w₂) :
    ∀ r ∈ [Reg.a7, .s5, .t0, .s6], s₁.gpr r = s₂.gpr r := by
  subst hB hw
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e₁.a7, e₂.a7]
  · rw [e₁.s5, e₂.s5]
  · rw [e₁.t0, e₂.t0]
  · rw [e₁.s6, e₂.s6]

/-- A predicate that gives the working space of a call with the public data,
and the stack pointer, pins the working space's registers. -/
theorem pins_env {α : Type} {Φ : α → State → Prop} (f : α → KD)
    (h : ∀ x s, Φ x s → ∃ s0 Z, KRel (f x).1 s0 ∧ Env s (stackArg s0 1) Z (cw s0) ∧ s.sp = (f x).2) :
    Pins Φ [.a7, .s5, .t0, .s6] := by
  intro x s₁ s₂ h₁ h₂
  obtain ⟨s0, Z, k, e, sp⟩ := h x s₁ h₁
  obtain ⟨s0', Z', k', e', sp'⟩ := h x s₂ h₂
  exact ⟨sp.trans sp'.symm, env_pins e e' (k.arg k' (i := 1) (by decide)) (by simp only [cw, k.oL_eq k'])⟩

/-- The loop after `d.2` witnesses, with `n + 1` iterations left. -/
def KI (n : Nat) (d : KD × Nat) (s : State) : Prop :=
  ∃ s0 σ, LCtx d.1.1 s0 σ ∧ σ.sp = d.1.2 ∧ LI s0 σ s d.2 n

theorem KI.env {n : Nat} {d : KD × Nat} {s : State} (h : KI n d s) :
    ∃ s0 Z, KRel d.1.1 s0 ∧ Env s (stackArg s0 1) Z (cw s0) ∧ s.sp = d.1.2 := by
  obtain ⟨s0, σ, C, sp, hl⟩ := h
  exact ⟨s0, _, C.krel, hl.ctx.prep.env, hl.sp.trans sp⟩

/-- The working space's address in `s6`, and the stack pointer. -/
def R3 (d : KD × Nat) (s : State) : Prop := ∃ s0, KRel d.1.1 s0 ∧ s.gpr .s6 = stackArg s0 1 ∧ s.sp = d.1.2

theorem pins_R3 : Pins R3 [.s6] := by
  intro d s₁ s₂ ⟨s0, k, a6, asp⟩ ⟨s0', k', b6, bsp⟩
  refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  rw [a6, b6, k.arg k' (i := 1) (by decide)]

/-! ## A draw -/

/-- A draw's octets and its witness: the round's precondition. -/
theorem lw_ok {σ s : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl ch r k n) (hav : 8 * w + 8 * w * k + 8 * w ≤ rl) :
    WP isa (.seq loadDraw VG.Impl.RsaKeyGen.RISCV64.Witness.witness) s fun s2 =>
      RC ⟨B, L, w, c, (wit c (8 * w) r (8 * w + 8 * w * k)).1⟩ s2 ∧ s2.sp = s.sp := by
  have ctx := h.ctx
  have e := ctx.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have hnw := e.hs.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  refine WP.seq (WP.mono (WP.rdwr (load_ok ctx h.used hav)) fun s1 ⟨⟨⟨v1, _, f1, a71⟩, k1⟩, _, _, sp1⟩ => ?_)
  have f1' : Frm B (kgR w) s.mem s1.mem := VG.Proof.MillerRabin.RISCV64.Blinded.frm_widen f1 (by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨(8 * hUsed, 16), by simp [kgR], Nat.le_refl _, by omega_arith⟩
    · exact ⟨(slot w 3, 4 * (8 * (w + 2))), by simp [kgR], by rw [es, es]; omega_arith, by rw [es, es]; omega_arith⟩)
  have e1 : Env s1 B (8 * L) w := ⟨e.hs.congr k1.2.2, a71, (k1.gpr (by decide)).trans e.s5,
    (k1.gpr (by decide)).trans e.t0, (k1.gpr (by decide)).trans e.s6, e.hw, e.hw', e.hZ⟩
  have p1 : Prep s1 B L w c := Prep.ofKgR ctx.prep e1 (k1.gpr (by decide)) f1'
  have hx1 : A s1.mem B w 4 = Spec.Rsa.os2ip (seg r (8 * w + 8 * w * k) (8 * w)) := by
    rw [v1, ← h.tape, VG.Proof.RsaKeyGen.seg_bytesAt s.mem R hav]
  refine WP.mono (WP.rdwr (witness_ok (mctx_of e1 p1.t1 p1.n) e1.s6 ctx.prep.odd ctx.cb (bv_ofNat_toNat _).symm))
    fun s2 ⟨⟨⟨a42, _, f2⟩, k2⟩, _, _, sp2⟩ => ?_
  rw [hx1] at a42
  change A s2.mem B w 4 = (wit c (8 * w) r (8 * w + 8 * w * k)).1 at a42
  have e2 : Env s2 B (8 * L) w := e1.keep k2 (by decide)
  have f12 : Frm B (kgR w) s.mem s2.mem := f1'.trans (VG.Proof.MillerRabin.RISCV64.Blinded.frm_widen f2 (by
    intro q hq
    simp only [witRanges, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [kgR], Nat.le_refl _, Nat.le_refl _⟩
    all_goals exact ⟨(slot w 3, 4 * (8 * (w + 2))), by simp [kgR], by (try rw [es, es]); (try dsimp only); omega_arith,
      by (try rw [es, es]); (try dsimp only); omega_arith⟩))
  have t12 : s2.gpr .t1 = s.gpr .t1 := (k2.gpr (by decide)).trans (k1.gpr (by decide))
  have p2 : Prep s2 B L w c := Prep.ofKgR ctx.prep e2 t12 f12
  have sp12 : s2.sp = s.sp := sp2.trans sp1
  have hac : (wit c (8 * w) r (8 * w + 8 * w * k)).1 < c :=
    VG.Proof.MillerRabin.RISCV64.Blinded.witness_lt ctx.cb (by omega_arith)
  exact ⟨⟨p2, a42, hac, by rw [sp12]; exact ctx.sp16, by rw [sp12]; exact ctx.sp, by rw [sp12]; exact ctx.stk⟩,
    sp12⟩

/-- A draw's start: the loop, with a draw's octets left. -/
def DS (d : KD × Nat) (s : State) : Prop :=
  ∃ s0 σ n, LCtx d.1.1 s0 σ ∧ σ.sp = d.1.2 ∧ LI s0 σ s d.2 n ∧
    8 * cw s0 + 8 * cw s0 * d.2 + 8 * cw s0 ≤ rL s0

/-- After `loadA`: the tape's address at the octets read, a draw's octets and
array 4's base, and the working space's other registers. -/
def LA (d : KD × Nat) (s : State) : Prop :=
  ∃ s0, KRel d.1.1 s0 ∧ s.gpr .s7 = s0.gpr .a7 + BitVec.ofNat 64 (8 * cw s0 + 8 * cw s0 * d.2) ∧
    s.gpr .s8 = BitVec.ofNat 64 (8 * cw s0) ∧ s.gpr .a7 = off (stackArg s0 1) (slot (cw s0) 4) ∧
    s.gpr .t0 = BitVec.ofNat 64 (cw s0) ∧ s.gpr .s5 = BitVec.ofNat 64 (8 * (cw s0 + 2)) ∧
    s.gpr .s6 = stackArg s0 1 ∧ s.sp = d.1.2

theorem pins_LA : Pins LA [.a7, .t0, .s7, .s8, .s5, .s6] := by
  intro d s₁ s₂ ⟨s0, k, a17, a8, a7, a0, a5, a6, asp⟩ ⟨s0', k', b17, b8, b7, b0, b5, b6, bsp⟩
  have hB : stackArg s0 1 = stackArg s0' 1 := k.arg k' (i := 1) (by decide)
  have hw : cw s0 = cw s0' := by simp only [cw, k.oL_eq k']
  have hR : s0.gpr .a7 = s0'.gpr .a7 := k.reg k' (by decide)
  refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a7, b7, hB, hw]
  · rw [a0, b0, hw]
  · rw [a17, b17, hR, hw]
  · rw [a8, b8, hw]
  · rw [a5, b5, hw]
  · rw [a6, b6, hB]

/-- The working space's registers of a call with the public data. -/
def EP (d : KD × Nat) (s : State) : Prop :=
  ∃ s0 Z, KRel d.1.1 s0 ∧ Env s (stackArg s0 1) Z (cw s0) ∧ s.sp = d.1.2

theorem pins_EP : Pins EP [.a7, .s5, .t0, .s6] := pins_env (fun d => d.1) fun _ _ h => h

theorem DS.ki {d : KD × Nat} {s : State} (h : DS d s) : ∃ n, KI n d s := by
  obtain ⟨s0, σ, n, C, sp, hl, -⟩ := h
  exact ⟨n, s0, σ, C, sp, hl⟩

theorem load_ct : RelCT isa (Two DS) loadDraw fun _ _ => True := by
  have pS : Pins DS [.a7, .s5, .t0, .s6] := pins_env (fun d => d.1) fun d s h => by
    obtain ⟨n, hk⟩ := h.ki; exact hk.env
  unfold loadDraw
  refine RelCT.seq (two_post (Ψ := LA) (two_taint _ pS (by taint_decide)) fun d s h => ?_)
    (two_taint _ pins_LA (by taint_decide))
  obtain ⟨s0, σ, n, C, sp, hl, -⟩ := h
  have e := hl.ctx.prep.env
  exact WP.mono (WP.rdwr (loadA_ok hl.ctx hl.used)) fun t ⟨⟨⟨t7, t8, ta7, _⟩, kt⟩, _, _, tsp⟩ =>
    ⟨s0, C.krel, t7, t8, ta7, (kt.gpr (by decide)).trans e.t0, (kt.gpr (by decide)).trans e.s5,
      (kt.gpr (by decide)).trans e.s6, tsp.trans (hl.sp.trans sp)⟩

/-- Before the round's call: its precondition on the run's candidate and witness. -/
def D2 (d : KD × Nat) (s : State) : Prop :=
  ∃ s0 σ n u, LCtx d.1.1 s0 σ ∧ σ.sp = d.1.2 ∧ LI s0 σ u d.2 n ∧
    8 * cw s0 + 8 * cw s0 * d.2 + 8 * cw s0 ≤ rL s0 ∧
    RC ⟨stackArg s0 1, sL s0, cw s0, candOf s0,
      (wit (candOf s0) (8 * cw s0) (rB s0) (8 * cw s0 + 8 * cw s0 * d.2)).1⟩ s ∧ s.sp = u.sp

theorem lw_ct : RelCT isa (Two DS) (.seq loadDraw VG.Impl.RsaKeyGen.RISCV64.Witness.witness) fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := EP) load_ct fun d s h => ?_) (two_taint _ pins_EP (by taint_decide))
  obtain ⟨s0, σ, n, C, sp, hl, hav⟩ := h
  have e := hl.ctx.prep.env
  exact WP.mono (WP.rdwr (load_ok hl.ctx hl.used hav)) fun t ⟨⟨⟨_, _, _, ta7⟩, kt⟩, _, _, tsp⟩ =>
    ⟨s0, _, C.krel, ⟨e.hs.congr kt.2.2, ta7, (kt.gpr (by decide)).trans e.s5, (kt.gpr (by decide)).trans e.t0,
      (kt.gpr (by decide)).trans e.s6, e.hw, e.hw', e.hZ⟩, tsp.trans (hl.sp.trans sp)⟩

/-- After the round's call. -/
def RP (d : KD × Nat) (s : State) : Prop :=
  ∃ s0 σ n u s2, LCtx d.1.1 s0 σ ∧ σ.sp = d.1.2 ∧ LI s0 σ u d.2 n ∧
    8 * cw s0 + 8 * cw s0 * d.2 + 8 * cw s0 ≤ rL s0 ∧ s2.sp = u.sp ∧
    RcPost s2 (stackArg s0 1) (sL s0) (cw s0) (candOf s0)
      (wit (candOf s0) (8 * cw s0) (rB s0) (8 * cw s0 + 8 * cw s0 * d.2)).1 s

theorem RP.env {d : KD × Nat} {s : State} (h : RP d s) :
    ∃ s0 Z, KRel d.1.1 s0 ∧ Env s (stackArg s0 1) Z (cw s0) ∧ s.sp = d.1.2 := by
  obtain ⟨s0, σ, n, u, s2, C, sp, hl, -, sp2, hp⟩ := h
  exact ⟨s0, _, C.krel, hp.prep.env, hp.sp.trans (sp2.trans (hl.sp.trans sp))⟩

theorem roundCall_ct (R : RoundImpl) :
    RelCT isa (Two D2) (VG.Impl.MillerRabin.RISCV64.Search.roundCall R.name R.code) fun _ _ => True := by
  refine (roundCall_ctw R).mono (fun s₁ s₂ ⟨d, h₁, h₂⟩ => ?_) fun _ _ h => h
  obtain ⟨s0, σ, n, u, C, sp, hl, -, rc, hsp⟩ := h₁
  obtain ⟨s0', σ', n', u', C', sp', hl', -, rc', hsp'⟩ := h₂
  refine ⟨(⟨stackArg s0 1, sL s0, cw s0⟩ : RcW),
    ⟨candOf s0, (wit (candOf s0) (8 * cw s0) (rB s0) (8 * cw s0 + 8 * cw s0 * d.2)).1, rc⟩,
    ⟨candOf s0', (wit (candOf s0') (8 * cw s0') (rB s0') (8 * cw s0' + 8 * cw s0' * d.2)).1, ?_⟩, ?_⟩
  · show RC ⟨stackArg s0 1, sL s0, cw s0, candOf s0',
      (wit (candOf s0') (8 * cw s0') (rB s0') (8 * cw s0' + 8 * cw s0' * d.2)).1⟩ s₂
    rw [C.hB C', C.hL C', C.hw C']; exact rc'
  · rw [hsp, hsp', hl.sp, hl'.sp, sp, sp']

theorem round_ct (R : RoundImpl) :
    RelCT isa (Two D2) (VG.Impl.RsaKeyGen.RISCV64.Witness.round R.name R.code) fun _ _ => True := by
  have pP : Pins RP [.a7, .s5, .t0, .s6] := pins_env (fun d => d.1) fun _ _ h => h.env
  unfold VG.Impl.RsaKeyGen.RISCV64.Witness.round
  refine RelCT.seq (two_post (Ψ := RP) (roundCall_ct R) fun d s h => ?_) ?_
  · obtain ⟨s0, σ, n, u, C, sp, hl, hav, rc, hsp⟩ := h
    exact WP.mono (roundCall_ok R rc.1 rc.2.1 rc.2.2.1 rc.2.2.2.1 rc.2.2.2.2.1 rc.2.2.2.2.2) fun t ht =>
      ⟨s0, σ, n, u, s, C, sp, hl, hav, hsp, ht⟩
  refine two_ite (fun d s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · obtain ⟨s0, σ, n, u, s2, C, -, hl, hav, -, hp⟩ := h₁
    obtain ⟨s0', σ', n', u', s2', C', -, hl', -, -, hp'⟩ := h₂
    rw [Steps.eval_zero, Steps.eval_zero, hp.a0, hp'.a0, pass_agree C C' hl hl' hav]
  · exact two_taint _ (VG.Proof.MillerRabin.RISCV64.Blinded.Pins.of_imp pP fun _ _ h => h.1) (by taint_decide)
  · exact two_taint _ (VG.Proof.MillerRabin.RISCV64.Blinded.Pins.of_imp pP fun _ _ h => h.1) (by taint_decide)

theorem draw_ct (R : RoundImpl) :
    RelCT isa (Two DS) (VG.Impl.RsaKeyGen.RISCV64.Witness.draw R.name R.code) fun _ _ => True := by
  unfold VG.Impl.RsaKeyGen.RISCV64.Witness.draw
  refine RelCT.assoc (RelCT.seq (two_post (Ψ := D2) lw_ct fun d s h => ?_) (round_ct R))
  obtain ⟨s0, σ, n, C, sp, hl, hav⟩ := h
  exact WP.mono (lw_ok hl hav) fun t ⟨rc, tsp⟩ => ⟨s0, σ, n, s, C, sp, hl, hav, rc, tsp⟩

/-! ## An iteration -/

/-- After the check of the octets left. -/
def C1 (n : Nat) (d : KD × Nat) (s : State) : Prop :=
  ∃ s0 σ u, LCtx d.1.1 s0 σ ∧ σ.sp = d.1.2 ∧ LI s0 σ u d.2 n ∧
    ((s.gpr .t4 = BitVec.ofNat 64 (if rL s0 - (8 * cw s0 + 8 * cw s0 * d.2) < 8 * cw s0 then 1 else 0) ∧
      s.mem = u.mem ∧ s.sp = u.sp) ∧ s.rd = u.rd ∧ s.wr = u.wr) ∧ Keep [.t2, .t3, .t4] u s

theorem C1.ki {n : Nat} {d : KD × Nat} {s : State} (h : C1 n d s) : KI n d s := by
  obtain ⟨s0, σ, u, C, sp, hl, ⟨⟨-, hm, hsp⟩, -, -⟩, k⟩ := h
  exact ⟨s0, σ, C, sp, hl.ofMem hm k hsp⟩

theorem C1.ds {n : Nat} {d : KD × Nat} {s : State} (h : C1 n d s)
    (hz : isa.eval (.nonzero .t4) s = some false) : DS d s := by
  obtain ⟨s0, σ, u, C, sp, hl, ⟨⟨h4, hm, hsp⟩, -, -⟩, k⟩ := h
  refine ⟨s0, σ, n, C, sp, hl.ofMem hm k hsp, ?_⟩
  rw [Steps.eval_nonzero, h4] at hz
  have hu : 8 * cw s0 + 8 * cw s0 * d.2 ≤ (rB s0).length := hl.mr.used
  rw [rB_len] at hu
  by_contra hc
  have : rL s0 - (8 * cw s0 + 8 * cw s0 * d.2) < 8 * cw s0 := by omega
  simp only [this, ↓reduceIte] at hz
  exact absurd hz (by decide)

theorem body_ct (R : RoundImpl) (n : Nat) :
    RelCT isa (Two (KI n)) (.seq (.block tapeShort) (.seq (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat])
      (VG.Impl.RsaKeyGen.RISCV64.Witness.draw R.name R.code)) (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)])))
      fun _ _ => True := by
  have pI : Pins (KI n) [.a7, .s5, .t0, .s6] := pins_env (fun d => d.1) fun _ _ h => h.env
  have pC : Pins (C1 n) [.a7, .s5, .t0, .s6] := VG.Proof.MillerRabin.RISCV64.Blinded.Pins.of_imp pI fun _ _ h => h.ki
  refine RelCT.seq (two_post (Ψ := C1 n) (two_taint _ pI (by taint_decide)) fun d s h => ?_)
    (RelCT.seq (two_ite (fun d s₁ s₂ h₁ h₂ => ?_) ?_ ?_) (two_taint _ pins_R3 (by taint_decide)))
  · obtain ⟨s0, σ, C, sp, hl⟩ := id h
    exact WP.mono (check_ok hl) fun t ht => ⟨s0, σ, s, C, sp, hl, ht⟩
  · obtain ⟨s0, σ, u, C, -, -, ⟨⟨a4, -⟩, -⟩, -⟩ := h₁
    obtain ⟨s0', σ', u', C', -, -, ⟨⟨b4, -⟩, -⟩, -⟩ := h₂
    rw [Steps.eval_nonzero, Steps.eval_nonzero, a4, b4, C.hw C', C.hrl C']
  · refine two_post (Ψ := R3) (two_taint _ (VG.Proof.MillerRabin.RISCV64.Blinded.Pins.of_imp pC fun _ _ h => h.1)
      (by taint_decide)) fun d s ⟨h, _⟩ => ?_
    obtain ⟨s0, Z, k, e, sp⟩ := h.ki.env
    exact WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.setStat_ok (v := 0) e (by decide)) fun t ⟨⟨_, tsp⟩, kt⟩ =>
      ⟨s0, k, (kt.gpr (by decide)).trans e.s6, tsp.trans sp⟩
  · refine VG.Proof.MillerRabin.RISCV64.Blinded.two_map id (Ψ := DS) (fun d s ⟨h, hz⟩ => h.ds hz)
      (two_post (Ψ := R3) (draw_ct R) fun d s h => ?_)
    obtain ⟨s0, σ, m, C, sp, hl, hav⟩ := h
    exact WP.mono (draw_ok R hl hav) fun t ⟨lk, _⟩ => ⟨s0, C.krel, lk.prep.env.s6, lk.sp.trans sp⟩

/-! ## The loop -/

/-- After an iteration: the end, or the next iteration. -/
def BP (n : Nat) (d : KD × Nat) (s : State) : Prop :=
  ∃ s0 σ, LCtx d.1.1 s0 σ ∧ σ.sp = d.1.2 ∧
    ((isa.eval (.zero .t2) s = some false ∧ n = 0) ∨
      (isa.eval (.zero .t2) s = some true ∧ 0 < n ∧ LI s0 σ s (d.2 + 1) (n - 1)))

theorem loop_ct (R : RoundImpl) (n : Nat) :
    RelCT isa (Two (KI n)) (.loop (.seq (.block tapeShort) (.seq (.ite (.nonzero .t4)
      (.block [.li .t2 0, sth .t2 hStat]) (VG.Impl.RsaKeyGen.RISCV64.Witness.draw R.name R.code))
      (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)]))) (.zero .t2)) fun _ _ => True := by
  refine RelCT.loop (M := isa) (fun n => Two (KI n)) (fun n => ?_) n
  refine (two_post (Ψ := BP n) (body_ct R n) fun d s ⟨s0, σ, C, sp, hl⟩ =>
    WP.mono (body_ok R hl C.t3.hpt) fun t ht => ⟨s0, σ, C, sp, ?_⟩).mono (fun _ _ h => h) ?_
  · rcases ht with ⟨ev, hn, -⟩ | ⟨ev, hn, li⟩
    · exact .inl ⟨ev, hn⟩
    · exact .inr ⟨ev, hn, li⟩
  rintro s₁ s₂ ⟨d, ⟨s0, σ, C, sp, h₁⟩, ⟨s0', σ', C', sp', h₂⟩⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · obtain ⟨e₁, -⟩ := h₁.resolve_right fun ⟨_, h, _⟩ => by omega
    obtain ⟨e₂, -⟩ := h₂.resolve_right fun ⟨_, h, _⟩ => by omega
    refine ⟨by rw [e₁, e₂], fun _ => trivial, fun he => ?_⟩
    rw [e₁] at he; cases he
  · obtain ⟨e₁, -, l₁⟩ := h₁.resolve_left fun ⟨_, h⟩ => by omega
    obtain ⟨e₂, -, l₂⟩ := h₂.resolve_left fun ⟨_, h⟩ => by omega
    exact ⟨by rw [e₁, e₂], fun _ => trivial, fun _ => ⟨n - 1, by omega, (d.1, d.2 + 1),
      ⟨s0, σ, C, sp, l₁⟩, ⟨s0', σ', C', sp', l₂⟩⟩⟩

/-- The loop's start: the working space prepared, for the call from `s0` with
the public data `d.1`, at the stack pointer `d.2`. -/
def L3 (d : KD) (s : State) : Prop := ∃ s0, LCtx d.1 s0 s ∧ s.sp = d.2

/-- After the loop's counts are set up. -/
def L0 (d : KD) (s : State) : Prop := ∃ s0 σ, LCtx d.1 s0 σ ∧ σ.sp = d.2 ∧ LI s0 σ s 0 (n0 s0)

/-- The witnesses' loop: two runs from the same public data and stack pointer
leak the same. -/
theorem mr_ct (R : RoundImpl) :
    RelCT isa (Two L3) (VG.Impl.RsaKeyGen.RISCV64.Witness.millerRabin R.name R.code) fun _ _ => True := by
  have pL : Pins L3 [.a7, .s5, .t0, .s6] := pins_env id fun _ _ ⟨s0, C, sp⟩ =>
    ⟨s0, _, C.krel, C.t3.kc.prep.env, sp⟩
  unfold VG.Impl.RsaKeyGen.RISCV64.Witness.millerRabin
  refine RelCT.seq (two_post (Ψ := L0) (two_taint _ pL (by taint_decide)) fun d s ⟨s0, C, sp⟩ =>
    WP.mono (init_ok C.t3.kc C.t3.hu0 C.t3.tape C.t3.tc.h8) fun t ht => ⟨s0, s, C, sp, ht⟩) ?_
  exact (RelCT.exists_ fun n => loop_ct R n).mono
    (fun s₁ s₂ ⟨d, ⟨s0, σ, C, sp, h₁⟩, ⟨s0', σ', C', sp', h₂⟩⟩ =>
      ⟨n0 s0, (d, 0), ⟨s0, σ, C, sp, h₁⟩, ⟨s0', σ', C', sp', n0_eq C C' ▸ h₂⟩⟩) fun _ _ h => h

end VG.Proof.RsaKeyGen.RISCV64.Cand
