module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.RISCV64.ProbablePrime
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Prep
public import VerifiedGarbage.Proof.Bignum.Layout
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Setup
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.TrialOk
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Loop
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.MontPrep
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Impl.Dsa.RISCV64.ProbablePrime
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Prep
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Setup
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.TrialOk
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Loop
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.MontPrep
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
meta import VerifiedGarbage.Proof.Dsa.Generation.Primality
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Mont.OutsFrame
meta import VerifiedGarbage.Proof.Mont.RangeCover
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Witness
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Witness
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Load
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Load
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCallCT
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCallCT

/-! ### `MillerRabin.RISCV64.Blinded.LoopCT`, which only this module used -/

section

/-! ### `MillerRabin.RISCV64.Blinded.RoundCT`, which only this module used -/

section

/-!
# The blinded Miller–Rabin loop on RISC-V: constant time of a round

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/RoundCT.lean`):
`roundCall_ct`, two runs of `roundCall` with the same witness `a` (public, as
the tape is) leak the same trace, by `Search.roundCall_ct`. `round_ct`: the
round's outcome (`RcPost.a0`), which the branch tests, is a function of `c`
and `a`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64.Search VG.Impl.MillerRabin.RISCV64.Blinded
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (Prep RcPost RcStk roundCall_ok)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite)

/-- A round's start: the prepared candidate, the witness `a < c` in array 4,
and the round's stack. -/
def RS (a : BD × Nat) (s : State) : Prop :=
  Prep s a.1.B a.1.L a.1.w a.1.c ∧ A s.mem a.1.B a.1.w 4 = a.2 ∧ a.2 < a.1.c ∧ RcStk s a.1.B a.1.L ∧
    s.sp = a.1.sp

/-- `RS` as the call's precondition, `Search.RC`. -/
theorem roundCall_ct (Ri : RoundImpl) : RelCT isa (Two RS) (roundCall Ri.name Ri.code) fun _ _ => True :=
  (Search.roundCall_ct Ri).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨a.1.B, a.1.L, a.1.w, a.1.c, a.2⟩,
    ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1⟩, ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.1⟩,
    h₁.2.2.2.2.trans h₂.2.2.2.2.symm⟩) fun _ _ h => h

/-- After `roundCall`. -/
def RP (a : BD × Nat) (s : State) : Prop := ∃ s₀, RS a s₀ ∧ RcPost s₀ a.1.B a.1.L a.1.w a.1.c a.2 s

theorem round_ct (Ri : RoundImpl) :
    RelCT isa (Two RS) (Impl.MillerRabin.RISCV64.Blinded.round Ri.name Ri.code) fun _ _ => True := by
  have pP : Pins RP [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s ⟨s₀, h₀, hp⟩ =>
    ⟨hp.prep.env, hp.sp.trans h₀.2.2.2.2⟩
  unfold Impl.MillerRabin.RISCV64.Blinded.round
  refine RelCT.seq (two_post (Ψ := RP) (roundCall_ct Ri) fun a s h =>
    WP.mono (roundCall_ok Ri h.1 h.2.1 h.2.2.1 h.2.2.2.1.1 h.2.2.2.1.2.1 h.2.2.2.1.2.2) fun t ht => ⟨s, h, ht⟩) ?_
  refine two_ite (fun a s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ => by
    rw [Steps.eval_zero, Steps.eval_zero, h₁.a0, h₂.a0]) ?_ ?_
  · exact two_taint _ (Pins.of_imp pP fun _ _ h => h.1) (by taint_decide)
  · exact two_taint _ (Pins.of_imp pP fun _ _ h => h.1) (by taint_decide)

end VG.Proof.MillerRabin.RISCV64.Blinded

end

end

/-! ### `MillerRabin.RISCV64.Blinded.WitnessCT`, which only this module used -/

section

/-! ### `MillerRabin.RISCV64.Blinded.LoadCT`, which this module and modules that import it used -/

section

/-!
# The blinded Miller–Rabin loop on RISC-V: constant time of a draw's load

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/LoadCT.lean`): `load_ct`,
two runs of `load` from the same octets `used` of the tape leak the same
trace. The tape's address at `used` and the octets of a draw (`loadA_ok`),
loaded from the header, fix `loadN`'s addresses and count; the top word's
offset, loaded from the header, fixes the address of the mask's load and
store (`loadC1_ok`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64.Search VG.Impl.MillerRabin.RISCV64.Blinded
open VG.Proof.MillerRabin.RISCV64 (Env A)
open VG.Proof.Bignum (slot Frm wv word off ofs writeW_outside word_writeW_self)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite)

/-- A draw's start: the context, and `used` octets read with a draw left. -/
def LS (a : BD × Nat) (s : State) : Prop :=
  Ctx a.1 s ∧ word s.mem a.1.B (8 * hUsed) = BitVec.ofNat 64 a.2 ∧ a.2 + 8 * (a.1.t + 1) ≤ a.1.rl

/-- The first block of `load`. -/
abbrev loadA : List Instr :=
  [ldh .s7 hRand, ldh .t2 hUsed, .add .s7 .s7 .t2, ldh .s8 hK, .add .t2 .t2 .s8, sth .t2 hUsed] ++
    PublicChecked.base .a7 4

/-- After it. -/
def LA (a : BD × Nat) (s : State) : Prop :=
  ∃ s₀, LS a s₀ ∧ (s.gpr .s7 = a.1.R + BitVec.ofNat 64 a.2 ∧ s.gpr .s8 = BitVec.ofNat 64 (8 * (a.1.t + 1)) ∧
    s.gpr .a7 = off a.1.B (slot a.1.w 4) ∧
    s.mem = s₀.mem.writeW (off a.1.B (8 * hUsed)) (BitVec.ofNat 64 (a.2 + 8 * (a.1.t + 1)))) ∧
    Keep [.s7, .t2, .s8, .a7] s₀ s ∧ s.sp = s₀.sp

/-- After `loadN`. -/
def LN (a : BD × Nat) (s : State) : Prop :=
  ∃ u, LA a u ∧ VG.Proof.Mont.Outside a.1.B (slot a.1.w 4) (8 * a.1.w) u.mem s.mem ∧
    Keep [.a0, .s0, .t3, .t4, .t5] u s ∧ s.sp = u.sp

/-- After `a7` back: the working space's registers and the top word's offset. -/
def LB (a : BD × Nat) (s : State) : Prop :=
  Env s a.1.B (8 * a.1.L) a.1.w ∧ word s.mem a.1.B (8 * hTopOff) = BitVec.ofNat 64 (8 * a.1.t) ∧ s.sp = a.1.sp

/-- After `topAddr`: the top word's address in `t3`. -/
def LC1 (a : BD × Nat) (s : State) : Prop :=
  s.gpr .t3 = off a.1.B (slot a.1.w 4 + 8 * a.1.t) ∧ s.gpr .s6 = a.1.B ∧ s.sp = a.1.sp

/-- The rest of `load`'s last block: the mask. -/
abbrev loadC2 : List Instr := [ldh .t4 hTop, .load .d .t2 .t3 0, .logic .and .t2 .t2 .t4, .store .d .t2 .t3 0]

theorem topAddr_ok {v : State} {B : Addr} {L w t : Nat} (e : Env v B (8 * L) w)
    (hoff : word v.mem B (8 * hTopOff) = BitVec.ofNat 64 (8 * t)) :
    WP isa (.block topAddr) v fun x => x.gpr .t3 = off B (slot w 4 + 8 * t) ∧ x.gpr .s6 = B ∧ x.sp = v.sp := by
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  unfold topAddr
  rw [WP.block_append_iff]
  refine WP.mono (WP.rdwr (e.base (rd := .t3) (by decide) 4)) fun z ⟨⟨⟨z3, zm⟩, kz⟩, _, _, zsp⟩ => ?_
  have z6 : z.gpr .s6 = B := (kz.gpr (by decide)).trans e.s6
  have hz : Scr z B (8 * L) := e.hs.congr kz.2.2
  have r128 : z.mem.readW (B + 128#64) 64 = BitVec.ofNat 64 (8 * t) := by rw [zm]; exact hoff
  refine WP.mono (WP.rdwr (WP.keep [.t2, .t3] (Q := fun x => x.gpr .t3 = off B (slot w 4 + 8 * t) ∧ x.gpr .s6 = B)
    (by
      simp only [ldh, hTopOff]
      brun [z6, z3, r128, hz.ld (d := 128) (n := 8) (by omega), hz.al8 (d := 128) (by omega) (by decide)])
      (by rfl) (by rfl))) fun x ⟨⟨⟨x3, x6⟩, _⟩, _, _, xsp⟩ =>
    ⟨x3, x6, xsp.trans zsp⟩

theorem LA.regs {a : BD × Nat} {s : State} (h : LA a s) :
    s.gpr .a7 = off a.1.B (slot a.1.w 4) ∧ s.gpr .t0 = BitVec.ofNat 64 a.1.w ∧
      s.gpr .s7 = a.1.R + BitVec.ofNat 64 a.2 ∧ s.gpr .s8 = BitVec.ofNat 64 (8 * (a.1.t + 1)) ∧
      s.gpr .s5 = BitVec.ofNat 64 (8 * (a.1.w + 2)) ∧ s.gpr .s6 = a.1.B ∧ s.sp = a.1.sp := by
  obtain ⟨s₀, ⟨⟨c, -, sp⟩, -, -⟩, ⟨h7, h8, ha7, -⟩, k, hsp⟩ := h
  have e := c.prep.env
  exact ⟨ha7, (k.gpr (by decide)).trans e.t0, h7, h8, (k.gpr (by decide)).trans e.s5,
    (k.gpr (by decide)).trans e.s6, hsp.trans sp⟩

theorem LN.regs {a : BD × Nat} {s : State} (h : LN a s) :
    s.gpr .t0 = BitVec.ofNat 64 a.1.w ∧ s.gpr .s5 = BitVec.ofNat 64 (8 * (a.1.w + 2)) ∧
      s.gpr .s6 = a.1.B ∧ s.sp = a.1.sp := by
  obtain ⟨u, hu, -, k, hsp⟩ := h
  obtain ⟨-, h0, -, -, h5, h6, sp⟩ := hu.regs
  exact ⟨(k.gpr (by decide)).trans h0, (k.gpr (by decide)).trans h5, (k.gpr (by decide)).trans h6, hsp.trans sp⟩

theorem load_stA (a : BD × Nat) (s : State) (h : LS a s) : WP isa (.block loadA) s (LA a) :=
  WP.mono (WP.rdwr (loadA_ok h.1.1 h.2.1)) fun _ ⟨hu, _, _, sp⟩ => ⟨s, h, hu.1, hu.2, sp⟩

theorem load_stN (a : BD × Nat) (s : State) (h : LA a s) : WP isa Precompute.loadN s (LN a) := by
  obtain ⟨s₀, ⟨⟨ctx, -, sp⟩, hu, hav⟩, ⟨u7, u8, ua7, um⟩, ku, _⟩ := id h
  have e := ctx.prep.env
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (a.1.w + 2)) ≤ 8 * a.1.L := e.hZ
  have htw := ctx.tw
  have hw128 := e.hw'
  have hNr : ∀ i < 8 * (a.1.t + 1), InRegions (s.rd ++ s.wr) (off (a.1.R + BitVec.ofNat 64 a.2) i) 1 :=
    fun i hi => by
      rw [ku.2.1, ku.2.2, show off (a.1.R + BitVec.ofNat 64 a.2) i = a.1.R + BitVec.ofNat 64 a.2 + BitVec.ofNat 64 i
        from rfl, Offset.add_add]; exact ctx.rdR _ (by omega)
  have hNs : ∀ i < 8 * (a.1.t + 1), ∀ x, ofs a.1.B x < 8 * a.1.L → off (a.1.R + BitVec.ofNat 64 a.2) i ≠ x :=
    fun i hi x hx => by
      rw [show off (a.1.R + BitVec.ofNat 64 a.2) i = a.1.R + BitVec.ofNat 64 a.2 + BitVec.ofNat 64 i from rfl,
        Offset.add_add]; exact ctx.sepR _ (by omega) x hx
  exact WP.mono (WP.rdwr (loadN_ok (k := 8 * (a.1.t + 1)) (e.hs.congr ku.2.2) ua7
    (by rw [u7]; exact (BitVec.add_zero _).symm) u8 ((ku.gpr (by decide)).trans e.t0) (by omega)
    (by omega) (by omega) (by simp only [slot, hdrBytes]; omega) (by simp only [slot, hdrBytes]; omega)
    (by simp only [slot, hdrBytes]; omega) hNr hNs))
    fun v ⟨⟨_, vo, kv⟩, _, _, vsp⟩ => ⟨s, h, vo, kv, vsp⟩

theorem load_stB (a : BD × Nat) (s : State) (h : LN a s) :
    WP isa (.block [.addi .a7 .s6 hdrBytes]) s (LB a) := by
  obtain ⟨u, ⟨s₀, ⟨⟨ctx, -, sp⟩, -, -⟩, ⟨-, -, -, um⟩, ku, _⟩, vo, kv, _⟩ := id h
  obtain ⟨h0, h5, h6, hsp⟩ := h.regs
  have e := ctx.prep.env
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (a.1.w + 2)) ≤ 8 * a.1.L := e.hZ
  have r128 : word s.mem a.1.B (8 * hTopOff) = BitVec.ofNat 64 (8 * a.1.t) := by
    refine ((vo.word (d := 128) (by simp only [slot, hdrBytes]; omega) (by omega)).trans ?_).trans ctx.topOff
    rw [um]
    exact (writeW_outside _ _ _ (by simp only [hUsed]; omega)).word (by simp only [hUsed]; omega) (by omega)
  refine WP.mono (WP.rdwr (WP.keep [.a7] (Q := fun y => y.gpr .a7 = off a.1.B (slot a.1.w 0) ∧ y.mem = s.mem)
    (by brun [h6, hdrBytes]; simp only [slot, hdrBytes, Nat.zero_mul, Nat.add_zero]) (by rfl) (by rfl)))
    fun y ⟨⟨⟨y7, ym⟩, ky⟩, _, _, ysp⟩ => ⟨⟨e.hs.congr ((ky.2.2.trans kv.2.2).trans ku.2.2), y7,
      (ky.gpr (by decide)).trans h5, (ky.gpr (by decide)).trans h0, (ky.gpr (by decide)).trans h6, e.hw, e.hw', e.hZ⟩,
      by rw [ym]; exact r128, ysp.trans hsp⟩

theorem load_ct : RelCT isa (Two LS) load fun _ _ => True := by
  have pS : Pins LS [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s h => ⟨h.1.1.prep.env, h.1.2.2⟩
  have pA : Pins LA [.a7, .t0, .s7, .s8, .s5, .s6] := by
    intro a s₁ s₂ h₁ h₂
    obtain ⟨a7, a0, a17, a8, a5, a6, asp⟩ := h₁.regs
    obtain ⟨b7, b0, b17, b8, b5, b6, bsp⟩ := h₂.regs
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a7, b7]
    · rw [a0, b0]
    · rw [a17, b17]
    · rw [a8, b8]
    · rw [a5, b5]
    · rw [a6, b6]
  have pN : Pins LN [.t0, .s5, .s6] := by
    intro a s₁ s₂ h₁ h₂
    obtain ⟨a0, a5, a6, asp⟩ := h₁.regs
    obtain ⟨b0, b5, b6, bsp⟩ := h₂.regs
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a0, b0]
    · rw [a5, b5]
    · rw [a6, b6]
  have pB : Pins LB [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s h => ⟨h.1, h.2.2⟩
  have pC : Pins LC1 [.t3, .s6] := by
    intro a s₁ s₂ ⟨a3, a6, asp⟩ ⟨b3, b6, bsp⟩
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a3, b3]
    · rw [a6, b6]
  unfold load loadDraw
  refine RelCT.seq (RelCT.seq (two_post (two_taint _ pS (by taint_decide)) load_stA)
    (RelCT.seq (two_post (two_taint _ pA (by taint_decide)) load_stN)
      (two_post (two_taint _ pN (by taint_decide)) load_stB))) ?_
  exact RelCT.block_append (RelCT.seq (two_post (Ψ := LC1) (two_taint _ pB (by taint_decide)) fun a s h =>
      WP.mono (topAddr_ok h.1 h.2.1) fun x ⟨x3, x6, xsp⟩ => ⟨x3, x6, xsp.trans h.2.2⟩)
    (two_taint (c := .block loadC2) _ pC (by taint_decide)))

end VG.Proof.MillerRabin.RISCV64.Blinded

end

end

/-!
# The blinded Miller–Rabin loop on RISC-V: constant time of a draw's witness

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/WitnessCT.lean`):
`witness_ct`, two runs of `witness` from the same draw `X` (public, as the
tape is) leak the same trace: `atLeast2` and `ltN` branch on nothing, and
their flags, which the branches test, are functions of `X` and `c`
(`atLeast2_ok`, `ltN_ok`); in `force`, the top word's offset, loaded from the
header, fixes the address of the second load and store (`forceA_ok`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64.Search VG.Impl.MillerRabin.RISCV64.Blinded
open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Proof.MillerRabin.RISCV64 (Env A)
open VG.Proof.Bignum (slot Frm wv word off ofs writeW_outside word_writeW_self)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite)

/-- A witness's start: the context and the draw `X` cut to the bits of `c − 1`. -/
def WS (a : BD × Nat) (s : State) : Prop :=
  BCtx s a.1.B a.1.L a.1.w a.1.c a.1.R a.1.rl a.1.t a.1.b a.1.ch ∧ s.sp = a.1.sp ∧
    A s.mem a.1.B a.1.w 4 = a.2 % 2 ^ (64 * a.1.t + a.1.b)

/-- After `atLeast2`. -/
def W1 (a : BD × Nat) (s : State) : Prop :=
  ∃ s₀, WS a s₀ ∧ ((s.gpr .a3 = 0#64 ↔ A s₀.mem a.1.B a.1.w 4 < 2) ∧ s.mem = s₀.mem) ∧
    Keep a2Regs s₀ s ∧ s.sp = s₀.sp

/-- After `ltN`. -/
def W2 (a : BD × Nat) (s : State) : Prop :=
  ∃ s₁, W1 a s₁ ∧ (s.gpr .s4 = (if (A s₁.mem a.1.B a.1.w 4 ||| 1) < a.1.c then BitVec.allOnes 64 else 0) ∧
    Frm a.1.B [(slot a.1.w 3, 8 * (a.1.w + 2)), (slot a.1.w 6, 8 * (a.1.w + 2))] s₁.mem s.mem) ∧
    Keep ltNRegs s₁ s ∧ s.sp = s₁.sp

theorem W1.env {a : BD × Nat} {s : State} (h : W1 a s) : Env s a.1.B (8 * a.1.L) a.1.w ∧ s.sp = a.1.sp := by
  obtain ⟨s₀, ⟨c, sp, -⟩, -, k, hsp⟩ := h
  exact ⟨c.prep.env.keep k (by decide), hsp.trans sp⟩

/-- What `W2` gives: the working space's registers, the flags, and the
header words. -/
theorem W2.facts {a : BD × Nat} {s : State} (h : W2 a s) :
    Env s a.1.B (8 * a.1.L) a.1.w ∧ s.sp = a.1.sp ∧
      (s.gpr .a3 = 0#64 ↔ a.2 % 2 ^ (64 * a.1.t + a.1.b) < 2) ∧
      s.gpr .s4 = (if (a.2 % 2 ^ (64 * a.1.t + a.1.b) ||| 1) < a.1.c then BitVec.allOnes 64 else 0) ∧
      word s.mem a.1.B (8 * hTopOff) = BitVec.ofNat 64 (8 * a.1.t) ∧
      word s.mem a.1.B (8 * hTop) = BitVec.ofNat 64 (2 ^ a.1.b - 1) := by
  obtain ⟨s₁, h₁, ⟨h4, f2⟩, k2, sp2⟩ := h
  obtain ⟨s₀, ⟨c, sp, hx⟩, ⟨h3, m1⟩, k1, sp1⟩ := h₁
  have e := c.prep.env
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (a.1.w + 2)) ≤ 8 * a.1.L := e.hZ
  have es : ∀ j, slot a.1.w j = 256 + j * (8 * (a.1.w + 2)) := fun _ => rfl
  have kw : ∀ d, d + 8 ≤ slot a.1.w 3 → word s.mem a.1.B d = word s₀.mem a.1.B d := fun d hd => by
    rw [← m1]; exact f2.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [es] at hd ⊢ <;> omega) (by rw [es] at hd; omega)
  refine ⟨(e.keep k1 (by decide)).keep k2 (by decide), sp2.trans (sp1.trans sp), ?_, ?_,
    (kw _ (by simp only [hTopOff, es]; omega)).trans c.topOff, (kw _ (by simp only [hTop, es]; omega)).trans c.top⟩
  · rw [k2.gpr (by decide), h3, hx]
  · rw [h4, m1, hx]

/-- The first part of `force`: `x | 2` stored, and the top word's address in `t3`. -/
abbrev forceA : List Instr :=
  base .t3 4 ++ [.load .d .t2 .t3 0, .logicImm .or .t2 .t2 2, .store .d .t2 .t3 0] ++ topAddr

/-- The rest: the top bit cleared. -/
abbrev forceB : List Instr :=
  [ldh .t4 hTop, .shift .srl .d .t4 .t4 1, .load .d .t2 .t3 0, .logic .and .t2 .t2 .t4, .store .d .t2 .t3 0]

theorem force_eq : force = forceA ++ forceB := by
  simp only [force, forceA, forceB, List.append_assoc]

theorem forceA_ok {s : State} {B : Addr} {L w t : Nat} (e : Env s B (8 * L) w)
    (hoff : word s.mem B (8 * hTopOff) = BitVec.ofNat 64 (8 * t)) :
    WP isa (.block forceA) s fun x => x.gpr .t3 = off B (slot w 4 + 8 * t) ∧ x.gpr .s6 = B ∧ x.sp = s.sp := by
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.rdwr (e.base (rd := .t3) (by decide) 4)) fun y ⟨⟨⟨y3, ym⟩, ky⟩, _, _, ysp⟩ => ?_
  have ey : Env y B (8 * L) w := e.keep ky (by decide)
  have h4 : slot w 4 + 8 ≤ 2 ^ 64 := by rw [es]; omega
  have o1 := writeW_outside s.mem B (word s.mem B (slot w 4) ||| 2#64) h4
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun (z : State) =>
      z.mem = s.mem.writeW (off B (slot w 4)) (word s.mem B (slot w 4) ||| 2#64))
    (by brun [y3, ym, ey.hs.ld (d := slot w 4) (n := 8) (by rw [es]; omega),
          ey.hs.al8 (d := slot w 4) (by rw [es]; omega) (by rw [es]; omega),
          ey.hs.st (d := slot w 4) (n := 8) (by rw [es]; omega), BitVec.add_zero]) (by rfl) (by rfl)))
    fun z ⟨⟨zm, kz⟩, _, _, zsp⟩ => ?_
  have ez : Env z B (8 * L) w := ey.keep kz (by decide)
  have hoff' : word z.mem B (8 * hTopOff) = BitVec.ofNat 64 (8 * t) := by
    rw [zm, o1.word (by simp only [hTopOff]; rw [es]; omega) (by simp only [hTopOff]; omega)]; exact hoff
  exact WP.mono (topAddr_ok ez hoff') fun x ⟨x3, x6, xsp⟩ => ⟨x3, x6, xsp.trans (zsp.trans ysp)⟩

theorem beq_zero_of_iff {x : BitVec 64} {P : Prop} [Decidable P] (h : x = 0#64 ↔ P) : (x == 0) = decide P := by
  by_cases hp : P
  · rw [decide_eq_true hp]; exact beq_iff_eq.mpr (h.mpr hp)
  · rw [decide_eq_false hp]; exact beq_false_of_ne fun e => hp (h.mp e)

theorem witness_ct : RelCT isa (Two WS) witness fun _ _ => True := by
  have pS : Pins WS [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s h => ⟨h.1.prep.env, h.2.1⟩
  have p1 : Pins W1 [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s h => h.env
  have p2 : Pins W2 [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s h => ⟨h.facts.1, h.facts.2.1⟩
  -- `force`, from `W2`.
  have hforce : ∀ (Φ : BD × Nat → State → Prop), (∀ a s, Φ a s → W2 a s) →
      RelCT isa (Two Φ) (.block force) fun _ _ => True := fun Φ hΦ => by
    have pF : Pins Φ [.a7, .s5, .t0, .s6] := Pins.of_imp p2 hΦ
    let FA : BD × Nat → State → Prop := fun a s =>
      s.gpr .t3 = off a.1.B (slot a.1.w 4 + 8 * a.1.t) ∧ s.gpr .s6 = a.1.B ∧ s.sp = a.1.sp
    have pA : Pins FA [.t3, .s6] := by
      intro a s₁ s₂ ⟨a3, a6, asp⟩ ⟨b3, b6, bsp⟩
      refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a3, b3]
      · rw [a6, b6]
    rw [force_eq]
    refine RelCT.block_append (RelCT.seq (two_post (Ψ := FA) (two_taint _ pF (by taint_decide)) fun a s h => ?_)
      (two_taint (c := .block forceB) _ pA (by taint_decide)))
    obtain ⟨e, sp, -, -, hoff, -⟩ := (hΦ a s h).facts
    exact WP.mono (forceA_ok e hoff) fun x ⟨x3, x6, xsp⟩ => ⟨x3, x6, xsp.trans sp⟩
  unfold witness
  refine RelCT.seq (two_post (Ψ := W1) (two_taint _ pS (by taint_decide)) fun a s h =>
    WP.mono (WP.rdwr (atLeast2_ok h.1.prep.env)) fun t ⟨ht, _, _, tsp⟩ => ⟨s, h, ht.1, ht.2, tsp⟩) ?_
  refine RelCT.seq (two_post (Ψ := W2) (two_taint _ p1 (by taint_decide)) fun a s h => ?_) ?_
  · obtain ⟨s₀, ⟨c, -, -⟩, ⟨-, m1⟩, k1, _⟩ := id h
    exact WP.mono (WP.rdwr (ltN_ok (c := a.1.c) h.env.1 (by rw [m1]; exact c.prep.n)))
      fun t ⟨ht, _, _, tsp⟩ => ⟨s, h, ht.1, ht.2, tsp⟩
  refine two_ite (fun a s₁ s₂ h₁ h₂ => ?_) (hforce _ fun _ _ h => h.1) ?_
  · rw [Steps.eval_zero, Steps.eval_zero, beq_zero_of_iff h₁.facts.2.2.1, beq_zero_of_iff h₂.facts.2.2.1]
  refine two_ite (fun a s₁ s₂ h₁ h₂ => ?_) (hforce _ fun _ _ h => h.1.1) ?_
  · rw [Steps.eval_zero, Steps.eval_zero, h₁.1.facts.2.2.2.1, h₂.1.facts.2.2.2.1]
  exact two_taint _ (Pins.of_imp p2 fun _ _ h => h.1.1) (by taint_decide)

end VG.Proof.MillerRabin.RISCV64.Blinded

end

end

/-!
# The blinded Miller–Rabin loop on RISC-V: constant time

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/LoopCT.lean`): two runs of
the loop from the same public data (the working space, the candidate, the
tape and the search's parameters, and the stack pointer) leak the same trace.
`draw_ct`: a draw, by its load, witness and round (`load_ct`, `witness_ct`,
`round_ct`), from the public data each takes (the octets read, the draw, the
witness: functions of the tape). `body_ct`: an iteration, whose check of the
octets left (`check_ok`) is a function of the witnesses so far. `loop_ct`:
the loop, whose runs exit together, since an iteration exits exactly when it
is the last one (`body_ok`). `millerRabin_ct`: the whole loop, from no
octets read.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.MillerRabin.RISCV64.Search VG.Impl.MillerRabin.RISCV64.Blinded
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.Bignum (slot Frm word off wv writeW_outside word_writeW_self)
open VG.Spec.RsaKeyGen (Rand loop mrStep)
open VG.Proof.RsaKeyGen (mrSB wit seg)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite)

/-- The loop's state after `a.2` witnesses, with `n + 1` iterations left. -/
def BS (n : Nat) (a : BD × Nat) (s : State) : Prop :=
  ∃ σ, LInv σ s a.1.B a.1.R a.1.L a.1.w a.1.c a.1.rl a.1.t a.1.b a.1.ch a.1.r a.2 n ∧ σ.sp = a.1.sp

/-- A draw's start. -/
def DS (a : BD × Nat) (s : State) : Prop :=
  (∃ n, BS n a s) ∧ 8 * (a.1.t + 1) * a.2 + 8 * (a.1.t + 1) ≤ a.1.rl

/-- After the load. -/
def D1 (a : BD × Nat) (s : State) : Prop :=
  ∃ s₀, DS a s₀ ∧ LoadPost s₀ s a.1.B a.1.R a.1.w a.1.t a.1.b a.2 ∧ s.sp = s₀.sp

/-- After the witness. -/
def D2 (a : BD × Nat) (s : State) : Prop :=
  ∃ s₁, D1 a s₁ ∧ WitPost s₁ s a.1.B a.1.w a.1.c a.1.t a.1.r a.2 ∧ s.sp = s₁.sp

theorem draw_ct (Ri : RoundImpl) :
    RelCT isa (Two DS) (Impl.MillerRabin.RISCV64.Blinded.draw Ri.name Ri.code) fun _ _ => True := by
  unfold Impl.MillerRabin.RISCV64.Blinded.draw
  refine RelCT.seq (two_post (Ψ := D1) (two_map (fun a => (a.1, 8 * (a.1.t + 1) * a.2))
      (fun a s ⟨⟨n, σ, h, sp⟩, hav⟩ => ⟨⟨h.ctx, h.tape, h.sp.trans sp⟩, h.used, hav⟩) load_ct)
    fun a s hd => ?_) ?_
  · obtain ⟨⟨n, σ, h, sp⟩, hav⟩ := id hd
    exact WP.mono (WP.rdwr (load_ok h.ctx h.used hav)) fun t ⟨ht, _, _, tsp⟩ => ⟨s, hd, ht, tsp⟩
  refine RelCT.seq (two_post (Ψ := D2)
      (two_map (fun a => (a.1, Spec.Rsa.os2ip (seg a.1.r (0 + 8 * (a.1.t + 1) * a.2) (8 * (a.1.t + 1)))))
        (fun a s ⟨s₀, ⟨⟨n, σ, h, sp⟩, hav⟩, hl, hsp⟩ => by
          obtain ⟨-, ctx1, -, -, v1⟩ := after_load h hav hl hsp
          exact ⟨ctx1, hsp.trans (h.sp.trans sp), v1⟩) witness_ct)
      fun a s hd => ?_) ?_
  · obtain ⟨s₀, ⟨⟨n, σ, h, sp⟩, hav⟩, hl, hsp⟩ := id hd
    obtain ⟨e1, ctx1, -, hu1, v1⟩ := after_load h hav hl hsp
    have ctx := h.ctx
    exact WP.mono (WP.rdwr (witness_ok e1 ctx1.prep.n ctx1.prep.odd ctx.shape ctx1.top ctx1.topOff ctx.t0 ctx.tw
      ctx.b1 ctx.b64 v1 hu1)) fun t ⟨ht, _, _, tsp⟩ => ⟨s, hd, ht, tsp⟩
  exact two_map (fun a => (a.1, (wit a.1.c (8 * (a.1.t + 1)) a.1.r (0 + 8 * (a.1.t + 1) * a.2)).1))
    (fun a s ⟨s₁, ⟨s₀, ⟨⟨n, σ, h, sp⟩, hav⟩, hl, hsp1⟩, hw, hsp2⟩ => by
      obtain ⟨-, ctx2, -, ha, hac⟩ := after_witness h hav hl hsp1 hw hsp2
      exact ⟨ctx2.prep, ha, hac, ⟨ctx2.sp16, ctx2.sp, ctx2.stk⟩, hsp2.trans (hsp1.trans (h.sp.trans sp))⟩)
    (round_ct Ri)

/-- After the check. -/
def C1 (n : Nat) (a : BD × Nat) (s : State) : Prop :=
  ∃ s₀, BS n a s₀ ∧ ((s.gpr .t4 = BitVec.ofNat 64
      (if a.1.rl - 8 * (a.1.t + 1) * a.2 < 8 * (a.1.t + 1) then 1 else 0) ∧ s.mem = s₀.mem ∧ s.sp = s₀.sp) ∧
    s.rd = s₀.rd ∧ s.wr = s₀.wr) ∧ Keep [.t2, .t3, .t4] s₀ s

theorem C1.bs {n : Nat} {a : BD × Nat} {s : State} (h : C1 n a s) : BS n a s := by
  obtain ⟨s₀, ⟨σ, hl, sp⟩, ⟨⟨-, hm, hsp⟩, hrd, hwr⟩, k⟩ := h
  exact ⟨σ, hl.ofMem hm (hl.ctx.prep.env.keep k (by decide)) (k.gpr (by decide)) hsp hrd hwr, sp⟩

theorem BS.env {n : Nat} {a : BD × Nat} {s : State} (h : BS n a s) :
    Env s a.1.B (8 * a.1.L) a.1.w ∧ s.sp = a.1.sp := by
  obtain ⟨σ, hl, sp⟩ := h
  exact ⟨hl.ctx.prep.env, hl.sp.trans sp⟩

/-- The working space's address in `s6`, and the stack pointer. -/
def R3 (a : BD × Nat) (s : State) : Prop := s.gpr .s6 = a.1.B ∧ s.sp = a.1.sp

theorem pins_R3 : Pins R3 [.s6] := by
  intro a s₁ s₂ ⟨a6, asp⟩ ⟨b6, bsp⟩
  refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr; rw [a6, b6]

theorem body_ct (Ri : RoundImpl) (n : Nat) :
    RelCT isa (Two (BS n)) (.seq (.block tapeShort) (.seq (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat])
      (Impl.MillerRabin.RISCV64.Blinded.draw Ri.name Ri.code)) (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)])))
      fun _ _ => True := by
  have pB : Pins (BS n) [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s h => h.env
  have pC : Pins (C1 n) [.a7, .s5, .t0, .s6] := Pins.of_imp pB fun _ _ h => h.bs
  refine RelCT.seq (two_post (Ψ := C1 n) (two_taint _ pB (by taint_decide)) fun a s h => ?_)
    (RelCT.seq (two_ite (fun a s₁ s₂ ⟨_, _, ⟨⟨a4, _⟩, _⟩, _⟩ ⟨_, _, ⟨⟨b4, _⟩, _⟩, _⟩ => by
      rw [Steps.eval_nonzero, Steps.eval_nonzero, a4, b4]) ?_ ?_) (two_taint _ pins_R3 (by taint_decide)))
  · obtain ⟨σ, hl, sp⟩ := id h
    exact WP.mono (check_ok hl) fun t ht => ⟨s, h, ht⟩
  · refine two_post (Ψ := R3) (two_taint _ (Pins.of_imp pC fun _ _ h => h.1) (by taint_decide)) fun a s ⟨h, _⟩ => ?_
    obtain ⟨e, sp⟩ := h.bs.env
    exact WP.mono (setStat_ok (v := 0) e (by decide)) fun t ⟨⟨_, tsp⟩, kt⟩ =>
      ⟨(kt.gpr (by decide)).trans e.s6, tsp.trans sp⟩
  · refine two_map id (Ψ := DS) (fun a s ⟨h, hz⟩ => ⟨⟨n, h.bs⟩, ?_⟩) (two_post (Ψ := R3) (draw_ct Ri) fun a s h => ?_)
    · obtain ⟨⟨m, σ, hl, sp⟩, hav⟩ := h
      exact WP.mono (draw_ok Ri hl hav) fun t ⟨lk, _⟩ => ⟨lk.prep.env.s6, lk.sp.trans sp⟩
    · obtain ⟨s₀, ⟨σ, hl, -⟩, ⟨⟨h4, -⟩, -⟩, -⟩ := h
      rw [Steps.eval_nonzero, h4] at hz
      dsimp only [id]
      by_contra hc
      have : a.1.rl - 8 * (a.1.t + 1) * a.2 < 8 * (a.1.t + 1) := by omega
      simp only [this, ↓reduceIte] at hz
      exact absurd hz (by decide)

/-- After an iteration: the end, or the next state. -/
def BP (n : Nat) (a : BD × Nat) (s : State) : Prop :=
  ∃ σ, ((isa.eval (.zero .t2) s = some false ∧ n = 0 ∧
      MOut σ s a.1.B a.1.L a.1.w a.1.c a.1.rl a.1.ch a.1.r) ∨
    (isa.eval (.zero .t2) s = some true ∧ 0 < n ∧
      LInv σ s a.1.B a.1.R a.1.L a.1.w a.1.c a.1.rl a.1.t a.1.b a.1.ch a.1.r (a.2 + 1) (n - 1))) ∧ σ.sp = a.1.sp

theorem loop_ct (Ri : RoundImpl) (n : Nat) :
    RelCT isa (Two (BS n)) (.loop (.seq (.block tapeShort) (.seq (.ite (.nonzero .t4)
      (.block [.li .t2 0, sth .t2 hStat]) (Impl.MillerRabin.RISCV64.Blinded.draw Ri.name Ri.code))
      (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)]))) (.zero .t2)) fun _ _ => True := by
  refine RelCT.loop (M := isa) (fun n => Two (BS n)) (fun n => ?_) n
  refine (two_post (Ψ := BP n) (body_ct Ri n) fun a s ⟨σ, hl, sp⟩ =>
    WP.mono (body_ok Ri hl) fun t ht => ⟨σ, ht, sp⟩).mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨a, ⟨σ₁, h₁, sp₁⟩, ⟨σ₂, h₂, sp₂⟩⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · obtain ⟨e₁, -⟩ := h₁.resolve_right fun ⟨_, h, _⟩ => by omega
    obtain ⟨e₂, -⟩ := h₂.resolve_right fun ⟨_, h, _⟩ => by omega
    refine ⟨by rw [e₁, e₂], fun _ => trivial, fun he => ?_⟩
    rw [e₁] at he; cases he
  · obtain ⟨e₁, -, l₁⟩ := h₁.resolve_left fun ⟨_, h, _⟩ => by omega
    obtain ⟨e₂, -, l₂⟩ := h₂.resolve_left fun ⟨_, h, _⟩ => by omega
    exact ⟨by rw [e₁, e₂], fun _ => trivial, fun _ => ⟨n - 1, by omega, (a.1, a.2 + 1), ⟨σ₁, l₁, sp₁⟩, ⟨σ₂, l₂, sp₂⟩⟩⟩

/-- The loop's start: the context, no octets read, the tape. -/
def MS (a : BD) (s : State) : Prop :=
  BCtx s a.B a.L a.w a.c a.R a.rl a.t a.b a.ch ∧ word s.mem a.B (8 * hUsed) = BitVec.ofNat 64 0 ∧
    Spec.Rsa.bytesAt s.mem a.R a.rl = a.r ∧ s.sp = a.sp

theorem millerRabin_ct (Ri : RoundImpl) :
    RelCT isa (Two MS) (Impl.MillerRabin.RISCV64.Blinded.millerRabin Ri.name Ri.code) fun _ _ => True := by
  have pM : Pins MS [.a7, .s5, .t0, .s6] := pins_env id fun a s h => ⟨h.1.prep.env, h.2.2.2⟩
  unfold Impl.MillerRabin.RISCV64.Blinded.millerRabin
  refine RelCT.seq (two_post (Ψ := fun (a : BD) s => BS (iters0 a.c a.ch a.t a.r) (a, 0) s)
    (two_taint _ pM (by taint_decide)) fun a s h => WP.mono (init_ok h.1 h.2.1 h.2.2.1) fun t ht =>
      ⟨s, ht, h.2.2.2⟩) ?_
  exact (RelCT.exists_ fun n => loop_ct Ri n).mono
    (fun s₁ s₂ ⟨a, h₁, h₂⟩ => ⟨iters0 a.c a.ch a.t a.r, (a, 0), h₁, h₂⟩) fun _ _ h => h

end VG.Proof.MillerRabin.RISCV64.Blinded

end

end

/-! ### `Dsa.RISCV64.Prime.Correct`, which only this module used -/

section

/-!
# DSA's probable-prime test on RISC-V: correctness

As on PPC64LE (`Proof/Dsa/PPC64LE/Prime/*.lean`). `CIn bits s`: the
contract's precondition (with the table's region readable too), as the
proofs use it (`cin_of_pre`); `Shape`: what the code needs of each width
(`shape_of`). `entry_ok`: our caller's registers saved in `ws` from
`saveOff` (`Spill.save_ok`), the round's registers and the header's values
(`values_ok`), stored (`Spill.save_ok` again), and the arrays' addresses
(RSA's `Cand.hdrs_ok`): `EntryPost`, with the header `Hdr`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Prime
open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Dsa.RISCV64.ProbablePrime
open VG.Impl.MillerRabin.RISCV64.Search
open VG.Impl.MillerRabin.RISCV64.Blinded (hTopOff)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (hTrial)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.Bignum (word off slot Outside ofs Frm)
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (Prep)
open VG.Proof.MillerRabin.RISCV64.Blinded (BCtx MOut millerRabin_ok)
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.packed)

/-! ## The precondition -/

/-- The widths of DSA's primes. -/
abbrev Bits (bits : Nat) : Prop := bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072

/-- The arguments' regions, and the stack the test may use (the round's,
`below sp 96`, is part of it, `sub96`). -/
abbrev cW (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat * 8⟩
abbrev cR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev cU (s : State) : Region := ⟨s.gpr .a4, 8⟩
abbrev cS (s : State) : Region := ⟨s.sp - 512#64, 512⟩

theorem sub96 (s : State) : Region.Sub (below s.sp 96) (cS s) := below_sub (by decide) (by decide)

/-- The contract's precondition. -/
structure CIn (bits : Nat) (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  spLo : 512 ≤ s.sp.toNat
  rd : cR s ∈ s.rd
  wr : s.wr = [cW s, cU s]
  wR : (cW s).Disjoint (cR s)
  wU : (cW s).Disjoint (cU s)
  rU : (cR s).Disjoint (cU s)
  sW : (cS s).Disjoint (cW s)
  sR : (cS s).Disjoint (cR s)
  sU : (cS s).Disjoint (cU s)
  fw : (s.gpr .a0).toNat + (s.gpr .a1).toNat * 8 ≤ 2 ^ 64
  fr : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  fu : (s.gpr .a4).toNat + 8 ≤ 2 ^ 64
  size : keyOff + 8 * keyWords bits ≤ 8 * (s.gpr .a1).toNat
  odd : Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (s.gpr .a0) % 2 = 1
  bl : Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (s.gpr .a0)) = bits
  alW : (s.gpr .a0).toNat % 8 = 0
  alU : (s.gpr .a4).toNat % 8 = 0

theorem cin_of_pre (bits : Nat) (s : State) (h : (Proof.Dsa.ProbablePrime.contract (layout bits) abi 512).pre s) :
    CIn bits s := by
  sig_pre [Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs] at h
  obtain ⟨sp16, spLo, rd, wr, wR, wU, rU, sW, sR, sU, fw, fr, fu, size, odd, bl, alW, alU⟩ := h
  exact ⟨sp16, spLo, by rw [rd]; exact List.mem_singleton_self _, wr, wR, wU, rU, sW, sR, sU, fw, fr, fu, size,
    odd, bl, alW, alU⟩

/-- What the code needs of a width: the immediates fit, and the witness's
top word is word `t` with `b` bits. -/
structure Shape (bits : Nat) : Prop where
  w4 : 4 ≤ words bits
  w48 : words bits ≤ 48
  kw : keyWords bits < 2048
  hlen : len bits = bits / 8
  hlen8 : 8 * len bits = bits
  hlenw : len bits ≤ 8 * words bits
  hlen1 : 1 ≤ len bits
  t0 : 0 < (bits - 1) / 64
  tw : (bits - 1) / 64 < words bits
  b1 : 1 ≤ topBits bits
  b64 : topBits bits ≤ 64
  bt : bits = 64 * ((bits - 1) / 64) + topBits bits
  hdraw : draw bits = 8 * ((bits - 1) / 64 + 1)
  hoff : topOff bits = 8 * ((bits - 1) / 64)
  hchecks : checks bits = Spec.Dsa.primeChecks bits
  hcount : count bits = if words bits ≤ 16 then 512 else 1024
  stride : 8 * (words bits + 2) < 2048
  big : 13 ≤ bits - 1
  key : keyWords bits = 32 + 28 * (words bits + 2)
  maskb : 64 - topBits bits < 64
  cnt : count bits < 2048
  chk : checks bits < 2048
  drw : draw bits < 2048
  toff : topOff bits < 2048
  cnt1 : 1 ≤ count bits
  cnt2 : count bits ≤ 1024
  ch63 : checks bits < 2 ^ 63

theorem shape_of {bits : Nat} (hb : Bits bits) : Shape bits := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-! ## The entry -/

/-- The working space's base. -/
abbrev wsB (σ : State) : Addr := σ.gpr .a0 + BitVec.ofNat 64 keyOff

/-- The registers `values` writes. -/
def valRegs : List Reg := [.s6, .a7, .t0, .s5, .t1, .t2, .t3, .t4, .t5, .t6]

theorem mask_val {b : Nat} (hb1 : 1 ≤ b) (hb : b ≤ 64) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 1) >>> (64 - b) = BitVec.ofNat 64 (2 ^ b - 1) := by
  apply BitVec.eq_of_toNat_eq
  obtain h2 : 2 ^ b ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hb
  obtain h3 : (2 : Nat) ^ 64 = 2 ^ b * 2 ^ (64 - b) := by rw [← Nat.pow_add]; congr 1; omega
  obtain e1 : (BitVec.ofNat 64 0 - BitVec.ofNat 64 1).toNat = 2 ^ 64 - 1 := by decide
  rw [BitVec.toNat_ushiftRight, e1, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
  have hX1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hP1 : 1 ≤ 2 ^ (64 - b) := Nat.one_le_two_pow
  rw [h3]
  generalize 2 ^ b = X at *
  generalize 2 ^ (64 - b) = P at *
  obtain hXP : P ≤ X * P := Nat.le_mul_of_pos_left _ (by omega)
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, Nat.one_mul]; omega
  · rw [Nat.sub_add_cancel hX1]; omega

/-- The header's values in the registers, for the working space at `ws`. -/
structure HRegs (bits : Nat) (ws : Addr) (g : Reg → BitVec 64) : Prop where
  s6 : g .s6 = ws + BitVec.ofNat 64 keyOff
  a7 : g .a7 = off (ws + BitVec.ofNat 64 keyOff) (slot (words bits) 0)
  t0 : g .t0 = BitVec.ofNat 64 (words bits)
  s5 : g .s5 = BitVec.ofNat 64 (8 * (words bits + 2))
  t1 : g .t1 = BitVec.ofNat 64 (keyWords bits)
  t2 : g .t2 = BitVec.ofNat 64 0
  t3 : g .t3 = BitVec.ofNat 64 (checks bits)
  t4 : g .t4 = BitVec.ofNat 64 (count bits)
  t5 : g .t5 = BitVec.ofNat 64 (draw bits)
  t6 : g .t6 = BitVec.ofNat 64 (2 ^ topBits bits - 1)

/-- The header's values into registers. -/
theorem values_ok {bits : Nat} (hs : Shape bits) (s : State) :
    WP isa (.block (values bits)) s fun v => (HRegs bits (s.gpr .a0) v.gpr ∧ v.mem = s.mem) ∧ Keep valRegs s v := by
  have hkw := hs.kw
  have hst := hs.stride
  have hcnt := hs.cnt
  have hchk := hs.chk
  have hdrw := hs.drw
  obtain hw : words bits < 2048 := by have := hs.w48; omega
  have hmk := hs.maskb
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [values, keyOff, hdrBytes]
  brun [hkw, hst, hcnt, hchk, hdrw, hw, hmk, exec_shift_d, exec_li]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> gsimp
  · rfl
  · simp only [off, slot, hdrBytes, keyOff, Nat.zero_mul, Nat.add_zero, Offset.add_add]
  · exact mask_val hs.b1 hs.b64

/-- The working space is writable and does not wrap. -/
theorem scr_of {bits : Nat} {σ s : State} (h : CIn bits σ) (hwr : s.wr = σ.wr) :
    Scr s (wsB σ) (8 * keyWords bits) := by
  have hsz := h.size
  have hfw := h.fw
  refine ⟨⟨σ.gpr .a0, keyOff, (σ.gpr .a1).toNat * 8, by rw [hwr, h.wr]; exact List.mem_cons_self, rfl,
    by omega, by omega⟩, ?_, Spill.al8 h.alW (by decide)⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((σ.gpr .a0).toNat + keyOff % 2 ^ 64) (2 ^ 64)
  simp only [keyOff] at *
  omega

/-- The header's words. -/
structure Hdr (bits : Nat) (B R : Addr) (rl : BitVec 64) (m : Mem) : Prop where
  len : word m B 0 = BitVec.ofNat 64 (keyWords bits)
  w : word m B 48 = BitVec.ofNat 64 (words bits)
  arr : ∀ j < 8, word m B (8 * (8 + j)) = off B (slot (words bits) j)
  rand : word m B (8 * hRand) = R
  randLen : word m B (8 * hRandLen) = rl
  used : word m B (8 * hUsed) = BitVec.ofNat 64 0
  checks : word m B (8 * hChecks) = BitVec.ofNat 64 (checks bits)
  top : word m B (8 * hTop) = BitVec.ofNat 64 (2 ^ topBits bits - 1)
  k : word m B (8 * hK) = BitVec.ofNat 64 (draw bits)
  stride : word m B 224 = BitVec.ofNat 64 (8 * (words bits + 2))

/-- The header's word offsets. -/
def hdrWords : List Nat := [0, 48, 64, 72, 80, 88, 96, 104, 112, 120, 136, 144, 152, 168, 192, 216, 224]

theorem arr8 {j : Nat} (hj : j < 8) : 8 * (8 + j) ∈ hdrWords := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A change of memory that keeps the header's words keeps `Hdr`. -/
theorem Hdr.keep {bits : Nat} {B R : Addr} {rl : BitVec 64} {m m' : Mem} (h : Hdr bits B R rl m)
    (hw : ∀ d ∈ hdrWords, word m' B d = word m B d) : Hdr bits B R rl m' :=
  ⟨(hw _ (by decide)).trans h.len, (hw _ (by decide)).trans h.w,
    fun j hj => (hw _ (arr8 hj)).trans (h.arr j hj), (hw _ (by decide)).trans h.rand,
    (hw _ (by decide)).trans h.randLen, (hw _ (by decide)).trans h.used, (hw _ (by decide)).trans h.checks,
    (hw _ (by decide)).trans h.top, (hw _ (by decide)).trans h.k, (hw _ (by decide)).trans h.stride⟩

/-- After the entry. -/
structure EntryPost (bits : Nat) (σ s : State) : Prop where
  s6 : s.gpr .s6 = wsB σ
  a7 : s.gpr .a7 = off (wsB σ) (slot (words bits) 0)
  t0 : s.gpr .t0 = BitVec.ofNat 64 (words bits)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (words bits + 2))
  a0 : s.gpr .a0 = σ.gpr .a0
  svd : Spill.Saved (σ.gpr .a0) σ.gpr savedSlots s.mem
  hdr : Hdr bits (wsB σ) (σ.gpr .a2) (σ.gpr .a3) s.mem
  cnt : word s.mem (wsB σ) (8 * hTrial) = BitVec.ofNat 64 (count bits)
  frame : Frame [⟨σ.gpr .a0 + BitVec.ofNat 64 saveOff, 112⟩, ⟨wsB σ, 256⟩] σ.mem s.mem
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  syms : s.syms = σ.syms

theorem savedSlots_fits : Spill.Fits savedSlots := by decide
theorem hdrSlots_fits : Spill.Fits hdrSlots := by decide
theorem savedSlots_in : ∀ p ∈ savedSlots, saveOff ≤ p.2 ∧ p.2 + 8 ≤ saveOff + 112 := by decide
theorem hdrSlots_in : ∀ p ∈ hdrSlots, 0 ≤ p.2 ∧ p.2 + 8 ≤ 0 + 256 := by decide
theorem hdrSlots_out : ∀ p ∈ hdrSlots, p.2 + 8 ≤ 64 ∨ 64 + 8 * 8 ≤ p.2 := by decide

/-- A change of bytes `[d, d + n)` of a region of `Z ≥ d + n` bytes at `B`. -/
theorem frame_outside {B : Addr} {Z d n : Nat} {rs : List Region} {m m' : Mem}
    (ho : Outside B d n m m') (hd : d + n ≤ Z) : Frame (⟨B, Z⟩ :: rs) m m' := fun x hx => by
  have := hx _ List.mem_cons_self
  simp only [Region.Contains] at this
  exact ho x (.inr (by simp only [ofs]; omega))

/-- The state after `c` has the stack pointer and the addresses of statics
it had before. -/
theorem wp_sp_syms {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' => s'.sp = s.sp → s'.syms = s.syms → Q s') : WP isa c s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq (RISCV64.Exec.sp he) (RISCV64.Exec.syms he)⟩

/-- The entry: the registers saved, the round's registers and the header. -/
theorem entry_ok {bits : Nat} (hs : Shape bits) {σ : State} (h : CIn bits σ) :
    WP isa (.block (setup bits)) σ (EntryPost bits σ) := by
  have hsz := h.size
  have hfw := h.fw
  have hkey := hs.key
  have hw48 := hs.w48
  have hw4 := hs.w4
  obtain hwsW : cW σ ∈ σ.wr := by rw [h.wr]; exact List.mem_cons_self
  obtain inWs : ∀ d, d + 8 ≤ (σ.gpr .a1).toNat * 8 → InRegions σ.wr (σ.gpr .a0 + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨_, hwsW, by
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; omega⟩
  refine wp_sp_syms ?_
  rw [setup, List.append_assoc, List.append_assoc, show save = Spill.saveCode .a0 savedSlots from rfl,
    show hdrSlots.map (fun (r, d) => Instr.store .d r .s6 d) = Spill.saveCode .s6 hdrSlots from rfl]
  refine Spill.save_ok (b := .a0) (l := savedSlots) h.alW savedSlots_fits.1 (fun p hp =>
    inWs _ (by have := savedSlots_in p hp; simp only [saveOff, keyOff] at *; omega)) ?_
  generalize hM : Spill.saveMem σ.mem (σ.gpr .a0) σ.gpr savedSlots = M
  rw [WP.block_append_iff]
  refine WP.mono (values_ok hs _) fun v ⟨⟨hr, vm⟩, kv⟩ => ?_
  have v6 : v.gpr .s6 = wsB σ := hr.s6
  have vwr : v.wr = σ.wr := kv.2.2
  refine Spill.save_ok (b := .s6) (l := hdrSlots) (by rw [v6]; exact Spill.al8 h.alW (by decide))
    hdrSlots_fits.1 (fun p hp => by
      rw [vwr, v6, Offset.add_add]
      exact inWs _ (by have := hdrSlots_in p hp; simp only [keyOff] at *; omega)) ?_
  generalize hM2 : Spill.saveMem v.mem (v.gpr .s6) v.gpr hdrSlots = M2
  obtain sc : Scr { v with mem := M2 } (wsB σ) (8 * keyWords bits) := scr_of h vwr
  obtain hZ : 128 ≤ 8 * keyWords bits := by omega
  refine WP.mono (VG.Proof.RsaKeyGen.RISCV64.Cand.hdrs_ok sc v6 hr.a7 hr.s5 hZ 8 (Nat.le_refl _))
    fun t ⟨⟨tw, tout⟩, kt⟩ tsp tsy => ?_
  obtain tg : ∀ r, r ≠ .t2 → t.gpr r = v.gpr r := fun r hr => kt.gpr (by simp [hr])
  obtain nw : (wsB σ).toNat + 256 ≤ 2 ^ 64 := by have := sc.nowrap; omega
  -- The header.
  obtain sv : ∀ r d, (r, d) ∈ hdrSlots → word t.mem (wsB σ) d = v.gpr r := fun r d hm => by
    obtain ho := hdrSlots_out (r, d) hm
    obtain hi := hdrSlots_in (r, d) hm
    dsimp only at ho hi
    refine (tout.word ho (by omega)).trans ?_
    show M2.readW _ 64 = _
    rw [← hM2, ← v6]
    exact Spill.saveMem_saved hdrSlots_fits _ _ _ (r, d) hm
  obtain hd : Hdr bits (wsB σ) (σ.gpr .a2) (σ.gpr .a3) t.mem :=
    ⟨(sv .t1 _ (by decide)).trans hr.t1, (sv .t0 _ (by decide)).trans hr.t0, tw,
      (sv .a2 _ (by decide)).trans (kv.gpr (by decide)), (sv .a3 _ (by decide)).trans (kv.gpr (by decide)),
      (sv .t2 _ (by decide)).trans hr.t2, (sv .t3 _ (by decide)).trans hr.t3, (sv .t6 _ (by decide)).trans hr.t6,
      (sv .t5 _ (by decide)).trans hr.t5, (sv .s5 _ (by decide)).trans hr.s5⟩
  -- What changed.
  obtain f₁ : Frame [⟨σ.gpr .a0 + BitVec.ofNat 64 saveOff, 112⟩] σ.mem M := by
    rw [← hM]; exact Spill.saveMem_frame savedSlots_in (by decide) _ _ _
  obtain f₂ : Frame [⟨wsB σ, 256⟩] M M2 := by
    have vm' : v.mem = M := vm
    rw [← hM2, vm', v6]
    have := Spill.saveMem_frame (lo := 0) (n := 256) hdrSlots_in (by decide) M (wsB σ) v.gpr
    rwa [BitVec.add_zero] at this
  obtain f₃ : Frame [⟨wsB σ, 256⟩] M2 t.mem := frame_outside tout (by omega)
  obtain dSK : Region.Disjoint ⟨σ.gpr .a0 + BitVec.ofNat 64 saveOff, 112⟩ ⟨wsB σ, 256⟩ :=
    Offset.disjoint _ (.inl (by decide)) (by simp only [saveOff, keyOff] at *; omega)
      (by simp only [keyOff] at *; omega)
  refine ⟨(tg _ (by decide)).trans v6, (tg _ (by decide)).trans hr.a7, (tg _ (by decide)).trans hr.t0,
    (tg _ (by decide)).trans hr.s5, (tg _ (by decide)).trans (kv.gpr (by decide)), ?_, hd,
    (sv .t4 _ (by decide)).trans hr.t4, ?_, tsp, kt.2.1.trans kv.2.1, kt.2.2.trans vwr, tsy⟩
  · have s₀ : Spill.Saved (σ.gpr .a0) σ.gpr savedSlots M := by
      rw [← hM]; exact Spill.saveMem_saved savedSlots_fits _ _ _
    exact s₀.frame_in (lo := saveOff) (n := 112) savedSlots_in (f₂.trans f₃) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact dSK
  · exact (f₁.mono (by simp)).trans ((f₂.trans f₃).mono (by simp))

/-! ## The candidate -/

/-- The candidate, the tape and the test's result. -/
abbrev cand (bits : Nat) (σ : State) : Nat := Proof.Dsa.ProbablePrime.candidateAt (layout bits) σ.mem (σ.gpr .a0)
abbrev tape (σ : State) : Spec.RsaKeyGen.Rand := Spec.Rsa.bytesAt σ.mem (σ.gpr .a2) (σ.gpr .a3).toNat
abbrev res (bits : Nat) (σ : State) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (cand bits σ) (tape σ)

/-- After the entry, the Montgomery arithmetic's registers. -/
theorem env_of {bits : Nat} (hs : Shape bits) {σ s : State} (h : CIn bits σ) (ep : EntryPost bits σ s) :
    Env s (wsB σ) (8 * keyWords bits) (words bits) :=
  ⟨scr_of h ep.wr, ep.a7, ep.s5, ep.t0, ep.s6, hs.w4, by have := hs.w48; omega,
    by rw [hs.key]; simp only [slot, hdrBytes]; omega⟩

/-- A byte of the working space lies in `ws`. -/
theorem inW {bits : Nat} {σ : State} (h : CIn bits σ) {x : Addr}
    (hx : ofs (wsB σ) x < 8 * keyWords bits) : (cW σ).Contains x 1 := by
  have hsz := h.size
  have hfw := h.fw
  simp only [Region.Contains, ofs, wsB, keyOff] at hx hsz ⊢
  have : (x - σ.gpr .a0).toNat = (x - (σ.gpr .a0 + BitVec.ofNat 64 512)).toNat + 512 := by bv_omega
  omega

/-- The candidate's bytes lie below the working space. -/
theorem cand_sep {bits : Nat} {σ : State} (h : CIn bits σ) {i : Nat} (hi : i < 384) {x : Addr}
    (hx : ofs (wsB σ) x < 8 * keyWords bits) : off (σ.gpr .a0) i ≠ x := by
  rintro rfl
  have hsz := h.size
  have hfw := h.fw
  simp only [ofs, wsB, keyOff, off] at hx hsz
  have : (σ.gpr .a0 + BitVec.ofNat 64 i - (σ.gpr .a0 + BitVec.ofNat 64 512)).toNat = 2 ^ 64 - 512 + i := by
    bv_omega
  omega

/-- The candidate's bytes are unchanged by the entry. -/
theorem cand_keep {bits : Nat} {σ s : State} (ep : EntryPost bits σ s) {n : Nat} (hn : n ≤ 384) :
    Spec.Rsa.bytesAt s.mem (σ.gpr .a0) n = Spec.Rsa.bytesAt σ.mem (σ.gpr .a0) n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  refine ep.frame _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [Region.Contains, Offset.add_sub_add_left] <;> intro hc
  · exact Offset.not_lt_sub_ofNat (d := saveOff) (n := 112) (k := i) (Or.inl (by simp only [saveOff]; omega))
      (by omega) (by decide) (by decide) (by omega)
  · exact Offset.not_lt_sub_ofNat (d := keyOff) (n := 256) (k := i) (Or.inl (by simp only [keyOff]; omega))
      (by omega) (by decide) (by decide) (by omega)

/-- The candidate into array 0. -/
theorem loadC_ok {bits : Nat} (hs : Shape bits) {σ s : State} (h : CIn bits σ) (ep : EntryPost bits σ s) :
    WP isa (loadC bits) s fun t =>
      (A t.mem (wsB σ) (words bits) 0 = cand bits σ ∧
        Outside (wsB σ) (slot (words bits) 0) (8 * words bits) s.mem t.mem) ∧
      Keep [.s7, .s8, .a0, .s0, .t3, .t4, .t5] s t := by
  obtain e := env_of hs h ep
  have hlen := hs.hlenw
  have hlen1 := hs.hlen1
  have hw48 := hs.w48
  obtain hl384 : len bits ≤ 384 := by omega
  have hfw := h.fw
  have hsz := h.size
  obtain hl2 : len bits < 2048 := by omega
  unfold loadC
  refine WP.seq (WP.mono (WP.keep [.s7, .s8] (Q := fun (u : State) => u.gpr .s7 = off (σ.gpr .a0) 0 ∧
      u.gpr .s8 = BitVec.ofNat 64 (len bits) ∧ u.mem = s.mem) (by brun [ep.a0, hl2]) (by rfl) (by rfl))
    fun u ⟨⟨u7, u8, um⟩, ku⟩ => ?_)
  obtain eu : Env u (wsB σ) (8 * keyWords bits) (words bits) := e.keep ku (by decide)
  refine WP.mono (loadN_ok (k := len bits) eu.hs eu.a7 u7 u8 eu.t0 hlen1 hlen (by omega) (by simp only [slot, hdrBytes]; omega)
    (by simp only [slot, hdrBytes]; omega) (by have := eu.hZ; simp only [slot, hdrBytes] at *; omega)
    (fun i hi => ⟨_, by rw [ku.2.1, ku.2.2, ep.rd, ep.wr, h.wr]; exact List.mem_append_right _ List.mem_cons_self, by
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; have := hs.key; omega⟩)
    (fun i hi x hx => cand_sep h (by omega) hx)) fun t ⟨tv, to, kt⟩ => ?_
  refine ⟨⟨?_, by rw [← um]; exact to⟩, (ku.trans kt).mono (by decide)⟩
  show Mont.wordsVal t.mem (wsB σ) (slot (words bits) 0) (words bits) = _
  rw [tv, um, cand_keep ep hl384]
  simp only [cand, Proof.Dsa.ProbablePrime.candidateAt, layout, BitVec.add_zero, ← hs.hlen]
  rfl

/-! ## The table -/

/-- The trial table. -/
abbrev K : List (String × List (BitVec 64)) := VG.Impl.RsaKeyGen.TrialTable32.consts

/-- The table, as trial division reads it. -/
structure Tab (s : State) : Prop where
  fit : (s.syms TrialTable32.symbol).toNat + 8 * 1024 ≤ 2 ^ 64
  al : (s.syms TrialTable32.symbol).toNat % 8 = 0
  rd : (⟨s.syms TrialTable32.symbol, 8 * 1024⟩ : Region) ∈ s.rd
  held : ∀ i < 1024, s.mem.readW (s.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
    TrialTable32.packed.getD i 0
  wr : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms TrialTable32.symbol, 8 * 1024⟩ r

theorem tab_of {σ : State} (hk : ConstsOk K 512 σ) : Tab σ := by
  have hm : (TrialTable32.symbol, TrialTable32.packed) ∈ K := List.mem_cons_self
  have hl := VG.Proof.RsaKeyGen.TrialTable32.packed_length
  refine ⟨hl ▸ hk.fit hm, by have := hk.aligned hm; omega, hl ▸ hk.mem_rd hm,
    fun i hi => hk.readW hm (by rw [hl]; exact hi), hl ▸ hk.wr1⟩

/-- A change of memory apart from the table keeps it. -/
theorem Tab.frame {s t : State} (h : Tab s) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨s.syms TrialTable32.symbol, 8 * 1024⟩ r) (sy : t.syms = s.syms)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Tab t := by
  have hfit := h.fit
  refine ⟨sy ▸ h.fit, sy ▸ h.al, by rw [sy, hrd]; exact h.rd, fun i hi => ?_, by rw [sy, hwr]; exact h.wr⟩
  rw [sy, hf.readW (r := ⟨s.syms TrialTable32.symbol, 8 * 1024⟩) (Offset.contains_base _ (by omega) (by omega))
    hd (by decide)]
  exact h.held i hi

/-! ## The body -/

/-- What the body reads. -/
structure BIn (bits : Nat) (σ s : State) : Prop where
  hb : Bits bits
  cin : CIn bits σ
  env : Env s (wsB σ) (8 * keyWords bits) (words bits)
  hdr : Hdr bits (wsB σ) (σ.gpr .a2) (σ.gpr .a3) s.mem
  cnt : word s.mem (wsB σ) (8 * hTrial) = BitVec.ofNat 64 (count bits)
  cand : A s.mem (wsB σ) (words bits) 0 = cand bits σ
  tab : Tab s
  tape : Spec.Rsa.bytesAt s.mem (σ.gpr .a2) (σ.gpr .a3).toNat = tape σ
  syms : s.syms = σ.syms
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr

/-- After the body. -/
structure BOut (bits : Nat) (σ s t : State) : Prop where
  s6 : t.gpr .s6 = wsB σ
  stat : word t.mem (wsB σ) (8 * hStat) = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ))
  used : ∀ b rest, res bits σ = some (b, rest) →
    word t.mem (wsB σ) (8 * hUsed) = BitVec.ofNat 64 ((σ.gpr .a3).toNat - rest.length)
  frame : Frame [⟨wsB σ, 8 * keyWords bits⟩, below σ.sp 96] s.mem t.mem
  sp : t.sp = σ.sp
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr

/-- Trial division by the width's entries is RSA's. -/
theorem trial_spec {bits c : Nat} (hb : Bits bits) (large : 8161 < c) :
    VG.Proof.RsaKeyGen.trialPrefix c (count bits) = Spec.RsaKeyGen.obviouslyComposite bits c := by
  have := VG.Proof.RsaKeyGen.trialPrefix_spec (w := words bits) large
  rw [(shape_of hb).hcount, this]
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    simp [Spec.RsaKeyGen.obviouslyComposite, Spec.RsaKeyGen.trialPrimes, words]

/-- The candidate's facts the tests need. -/
theorem cand_facts {bits : Nat} {σ : State} (hb : Bits bits) (h : CIn bits σ) :
    8161 < cand bits σ ∧ 3 ≤ cand bits σ ∧ cand bits σ % 2 = 1 ∧
      Spec.RsaKeyGen.bitLength (cand bits σ - 1) = bits := by
  have hbl := h.bl
  have hodd := h.odd
  obtain hbig := (shape_of hb).big
  obtain ⟨hlo, -⟩ := (VG.Proof.Dsa.bitLength_iff_bounds (by omega)).mp hbl
  have : 2 ^ 13 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) hbig
  dsimp only [cand]
  exact ⟨by omega, by omega, hodd, VG.Proof.Dsa.Generation.predecessor_bits (by omega) hodd hbl⟩

/-- The header's word at `8 i` := `v` (`li` of `v` into `t2`, and `sth`). -/
theorem setHdr_ok {s : State} {B : Addr} {Z w v i : Nat} (e : Env s B Z w) (hv : v < 2048) (hi : i < 32) :
    WP isa (.block [.li .t2 v, sth .t2 i]) s fun x =>
      (x.mem = s.mem.writeW (off B (8 * i)) (BitVec.ofNat 64 v)) ∧ Keep [.t2] s x := by
  have hsc := e.hs
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [sth]
  brun [e.s6, hv, show 8 * i < 2048 by omega, hsc.st (d := 8 * i) (n := 8) (by omega),
    hsc.al8 (d := 8 * i) (by omega) (by omega)]

/-- A composite: `hStat := 2`. -/
theorem comp_ok {bits : Nat} {σ s : State} (h : BIn bits σ s)
    (hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = true) :
    WP isa (.block [.li .t2 2, sth .t2 hStat]) s (BOut bits σ s) := by
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (words bits + 2)) ≤ 8 * keyWords bits := e.hZ
  obtain ⟨hbig, -, hodd, -⟩ := cand_facts h.hb h.cin
  obtain hres : res bits σ = some (false, tape σ) := by
    rw [res, VG.Proof.Dsa.Generation.probablePrime_large (by omega) hodd, h.cin.bl, hc]; rfl
  refine wp_sp_syms (WP.mono (setHdr_ok (v := 2) (i := hStat) e (by decide) (by decide))
    fun x ⟨xm, kx⟩ xsp _ => ?_)
  obtain ho := VG.Proof.Bignum.writeW_outside s.mem (wsB σ) (d := 8 * hStat) (BitVec.ofNat 64 2)
    (by simp only [hStat]; omega)
  refine ⟨(kx.gpr (by decide)).trans e.s6, by rw [xm, VG.Proof.Bignum.word_writeW_self, hres]; rfl,
    fun b rest hr => ?_, by rw [xm]; exact frame_outside ho (by simp only [hStat]; omega), xsp.trans h.sp,
    kx.2.1.trans h.rd, kx.2.2.trans h.wr⟩
  rw [hres] at hr
  cases hr
  rw [xm, ho.word (by simp only [hStat, hUsed]; omega) (by simp only [hUsed]; omega), h.hdr.used]
  simp only [tape, Spec.Rsa.bytesAt, List.length_map, List.length_range, Nat.sub_self]

/-- The header's words lie apart from what `montPrep` writes. -/
theorem hdr_apart (w : Nat) :
    ∀ d ∈ 128 :: hdrWords, ∀ r ∈ VG.Proof.MillerRabin.RISCV64.Search.mpRanges w, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  intro d hd r hr
  obtain hd' : (d + 8 ≤ 56 ∨ 64 ≤ d) ∧ d + 8 ≤ 256 := by revert d; decide
  simp only [VG.Proof.MillerRabin.RISCV64.Search.mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes] <;> omega

/-- What `montPrep` writes lies within the working space. -/
theorem mp_within (w : Nat) :
    ∀ r ∈ VG.Proof.MillerRabin.RISCV64.Search.mpRanges w, r.1 + r.2 ≤ 256 + 28 * (8 * (w + 2)) := by
  intro r hr
  simp only [VG.Proof.MillerRabin.RISCV64.Search.mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes, VG.Impl.MillerRabin.RISCV64.aE] <;>
    omega

/-- A byte of the tape lies outside the working space. -/
theorem tape_out {bits : Nat} {σ : State} (h : CIn bits σ) {i : Nat} (hi : i < (σ.gpr .a3).toNat) :
    ¬ ofs (wsB σ) (σ.gpr .a2 + BitVec.ofNat 64 i) < 8 * keyWords bits := fun hx =>
  h.wR _ (inW h hx) (by
    simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := (σ.gpr .a3).isLt; omega)]; omega)

/-- After the offset of a witness's top word is stored, from the body's
state `s`. -/
structure MP (bits : Nat) (σ s x : State) : Prop where
  hb : Bits bits
  cin : CIn bits σ
  env : Env x (wsB σ) (8 * keyWords bits) (words bits)
  cand : A x.mem (wsB σ) (words bits) 0 = cand bits σ
  hdr : Hdr bits (wsB σ) (σ.gpr .a2) (σ.gpr .a3) x.mem
  top : word x.mem (wsB σ) (8 * hTopOff) = BitVec.ofNat 64 (topOff bits)
  tape : Spec.Rsa.bytesAt x.mem (σ.gpr .a2) (σ.gpr .a3).toNat = tape σ
  sp : x.sp = σ.sp
  rd : x.rd = σ.rd
  wr : x.wr = σ.wr
  frame : Frame [⟨wsB σ, 8 * keyWords bits⟩, below σ.sp 96] s.mem x.mem

/-- The offset of a witness's top word, in the word trial division read its
count from. -/
theorem topOff_ok {bits : Nat} {σ s : State} (h : BIn bits σ s) :
    WP isa (.block [.li .t2 (topOff bits), sth .t2 hTopOff]) s (MP bits σ s) := by
  have e := h.env
  obtain sh := shape_of h.hb
  have cin := h.cin
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (words bits + 2)) ≤ 8 * keyWords bits := e.hZ
  refine wp_sp_syms (WP.mono (setHdr_ok (v := topOff bits) (i := hTopOff) e sh.toff (by decide))
    fun x ⟨xm, kx⟩ xsp _ => ?_)
  obtain ho := VG.Proof.Mont.writeW_outside s.mem (wsB σ) (d := 8 * hTopOff) (BitVec.ofNat 64 (topOff bits))
    (by simp only [hTopOff]; omega)
  rw [← xm] at ho
  refine ⟨h.hb, cin, e.keep kx (by decide), ?_, h.hdr.keep fun d hd => ho.word (by
      have : d + 8 ≤ 128 ∨ 136 ≤ d := by revert d; decide
      simp only [hTopOff]; omega) (by have : d + 8 ≤ 256 := by revert d; decide
                                      omega),
    by rw [xm]; exact VG.Proof.Bignum.word_writeW_self _ _ _ _, ?_, xsp.trans h.sp, kx.2.1.trans h.rd,
    kx.2.2.trans h.wr, frame_outside ho (by simp only [hTopOff]; omega)⟩
  · rw [← h.cand]
    exact ho.wordsVal (.inr (by simp only [slot, hdrBytes, hTopOff]; omega))
      (by simp only [slot, hdrBytes]; omega)
  · rw [← h.tape]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    exact ho _ (.inr (by have := tape_out cin hi; simp only [hTopOff, ofs, VG.Proof.Mont.ofs] at this ⊢; omega))

/-- After `montPrep`: the blinded loop's context, no octets read, the tape,
and memory changed only in the working space. -/
theorem montPrep_ctx {bits : Nat} {σ s x : State} (h : MP bits σ s x) :
    WP isa montPrep x fun v =>
      BCtx v (wsB σ) (keyWords bits) (words bits) (cand bits σ) (σ.gpr .a2) (σ.gpr .a3).toNat
        ((bits - 1) / 64) (topBits bits) (checks bits) ∧
      word v.mem (wsB σ) (8 * hUsed) = BitVec.ofNat 64 0 ∧
      Spec.Rsa.bytesAt v.mem (σ.gpr .a2) (σ.gpr .a3).toNat = tape σ ∧ v.sp = σ.sp ∧ v.rd = σ.rd ∧
      v.wr = σ.wr ∧ Frame [⟨wsB σ, 8 * keyWords bits⟩, below σ.sp 96] s.mem v.mem := by
  obtain sh := shape_of h.hb
  have cin := h.cin
  have hZ : 256 + 28 * (8 * (words bits + 2)) ≤ 8 * keyWords bits := h.env.hZ
  obtain ⟨hbig, h3, hodd, hbl1⟩ := cand_facts h.hb cin
  have hch := sh.ch63
  refine wp_sp_syms (WP.mono (VG.Proof.MillerRabin.RISCV64.Search.montPrep_ok h.env h.cand hodd h3)
    fun v ⟨⟨ev, v0, vinv, vt1, v1, v9, v10, vE, vl, vO⟩, kv⟩ vsp _ => ?_)
  obtain vw : ∀ d ∈ 128 :: hdrWords, word v.mem (wsB σ) d = word x.mem (wsB σ) d := fun d hd =>
    VG.Proof.Mont.Outs.word vO (hdr_apart _ d hd) (by
      have : d + 8 ≤ 256 := by revert d; decide
      omega)
  obtain hd : Hdr bits (wsB σ) (σ.gpr .a2) (σ.gpr .a3) v.mem :=
    h.hdr.keep fun d hdm => vw d (List.mem_cons_of_mem _ hdm)
  obtain vt : word v.mem (wsB σ) (8 * hTopOff) = BitVec.ofNat 64 (topOff bits) :=
    (vw _ List.mem_cons_self).trans h.top
  obtain prep : Prep v (wsB σ) (keyWords bits) (words bits) (cand bits σ) :=
    ⟨ev, hd.len, hd.w, hd.stride, hd.arr, v0, h3, hodd, vinv, vt1, v1, v9, v10, vE, vl⟩
  obtain vsp' : v.sp = σ.sp := vsp.trans h.sp
  obtain vrd : v.rd = σ.rd := kv.2.1.trans h.rd
  obtain vwr : v.wr = σ.wr := kv.2.2.trans h.wr
  obtain bc : BCtx v (wsB σ) (keyWords bits) (words bits) (cand bits σ) (σ.gpr .a2) (σ.gpr .a3).toNat
      ((bits - 1) / 64) (topBits bits) (checks bits) := by
    refine ⟨prep, hd.rand, by rw [hd.randLen, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [hd.k, sh.hdraw],
      hd.top, by rw [vt, sh.hoff], hd.checks, sh.t0, sh.tw, sh.b1, sh.b64, by rw [hbl1]; exact sh.bt, hch,
      (σ.gpr .a3).isLt, fun i hi => ⟨_, List.mem_append_left _ (vrd ▸ cin.rd), ?_⟩,
      fun i hi y hy he => tape_out cin hi (he ▸ hy), by rw [vsp']; exact cin.sp16,
      by rw [vsp']; have := cin.spLo; omega,
      fun a ha hb => cin.sW a (sub96 σ a (by rw [vsp'] at ha; exact ha))
        (inW cin (by simp only [Region.Contains] at hb; exact hb)),
      fun i hi hc => cin.sR _ (sub96 σ _ (by rw [vsp'] at hc; exact hc)) ?_⟩ <;>
    · simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by have := (σ.gpr .a3).isLt; omega)]; omega
  obtain vtape : Spec.Rsa.bytesAt v.mem (σ.gpr .a2) (σ.gpr .a3).toNat = tape σ := by
    rw [← h.tape]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    refine vO _ fun r hr => .inr ?_
    obtain h1 := tape_out cin hi
    obtain h2 := mp_within _ r hr
    change r.1 + r.2 ≤ ofs (wsB σ) _
    omega
  exact ⟨bc, hd.used, vtape, vsp', vrd, vwr, h.frame.trans
    ((VG.Proof.Mont.Outs.frame vO fun r hr => Nat.le_trans (mp_within _ r hr) hZ).mono (by simp))⟩

/-- The test's result, past trial division. -/
theorem res_mr {bits : Nat} {σ : State} (hb : Bits bits) (cin : CIn bits σ)
    (hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = false) :
    res bits σ = Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep (cand bits σ) (checks bits)
      (Spec.Rsa.splitTwos (cand bits σ - 1)).1 (Spec.Rsa.splitTwos (cand bits σ - 1)).2) (1, 0) (tape σ) := by
  obtain ⟨hbig, -, hodd, -⟩ := cand_facts hb cin
  rw [res, VG.Proof.Dsa.Generation.probablePrime_large (by omega) hodd, cin.bl, hc, (shape_of hb).hchecks]; rfl

/-- No small prime divides: the offset of a witness's top word, `montPrep`
and the blinded Miller–Rabin loop. -/
theorem mr_ok (Ri : RoundImpl) {bits : Nat} {σ s : State} (h : BIn bits σ s)
    (hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = false) :
    WP isa (.seq (.block [.li .t2 (topOff bits), sth .t2 hTopOff])
      (.seq montPrep (VG.Impl.MillerRabin.RISCV64.Blinded.millerRabin Ri.name Ri.code))) s (BOut bits σ s) := by
  refine WP.seq (WP.mono (topOff_ok h) fun x hx => ?_)
  refine WP.seq (WP.mono (montPrep_ctx hx) fun v ⟨bc, hu, ht, vsp, vrd, vwr, fv⟩ => ?_)
  refine WP.mono (millerRabin_ok Ri bc hu ht) fun t mo => ?_
  obtain hres := res_mr h.hb h.cin hc
  obtain f₃ : Frame [⟨wsB σ, 8 * keyWords bits⟩, below σ.sp 96] v.mem t.mem := by
    rw [← vsp]; exact mo.1.frame
  exact ⟨mo.1.prep.env.s6, by rw [hres]; exact mo.2.1, fun b rest hr => mo.2.2 b rest (hres ▸ hr),
    fv.trans f₃, mo.1.sp.trans vsp, mo.1.rd.trans vrd, mo.1.wr.trans vwr⟩

/-- Trial division's start. -/
theorem BIn.div {bits : Nat} {σ s : State} (h : BIn bits σ s) :
    VG.Proof.RsaKeyGen.RISCV64.Cand.DivIn s (wsB σ) (8 * keyWords bits) (words bits) (count bits) :=
  ⟨h.env, h.cnt, (shape_of h.hb).cnt1, (shape_of h.hb).cnt2, h.tab.fit, h.tab.al, h.tab.rd, h.tab.held⟩

/-- Trial division keeps the body's context. -/
theorem bin_after_trial {bits : Nat} {σ s u : State} (h : BIn bits σ s) (um : u.mem = s.mem)
    (ug : ∀ r, r ∉ VG.Proof.RsaKeyGen.RISCV64.Cand.tdRegs → u.gpr r = s.gpr r) (urd : u.rd = s.rd)
    (uwr : u.wr = s.wr) (usp : u.sp = s.sp) (usy : u.syms = s.syms) : BIn bits σ u :=
  ⟨h.hb, h.cin, h.env.keep ⟨ug, urd, uwr⟩ (by decide), by rw [um]; exact h.hdr, by rw [um]; exact h.cnt,
    by rw [um]; exact h.cand,
    h.tab.frame (rs := []) (by rw [um]; exact Frame.refl _ _) (fun _ h => absurd h List.not_mem_nil) usy urd uwr,
    by rw [um]; exact h.tape, usy.trans h.syms, usp.trans h.sp, urd.trans h.rd, uwr.trans h.wr⟩

/-- The body. -/
theorem body_ok (Ri : RoundImpl) {bits : Nat} {σ s : State} (h : BIn bits σ s) :
    WP isa (body bits Ri.name Ri.code) s (BOut bits σ s) := by
  obtain ⟨hbig, -, -, -⟩ := cand_facts h.hb h.cin
  unfold body
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.RISCV64.Cand.TrialOk.trial_divOk.ok h.div)
    fun u ⟨u4, um, ug, urd, uwr, usp, usy⟩ => ?_)
  obtain hu : BIn bits σ u := bin_after_trial h um ug urd uwr usp usy
  rw [h.cand, trial_spec h.hb hbig] at u4
  obtain fr : ∀ t, BOut bits σ u t → BOut bits σ s t := fun t o =>
    ⟨o.s6, o.stat, o.used, by rw [← um]; exact o.frame, o.sp, o.rd, o.wr⟩
  refine WP.ite _ (Steps.eval_zero_ofNat u .a4 (by split <;> decide) u4) (fun hz => ?_) (fun hz => ?_)
  · have hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = false := by
      revert hz; cases Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) <;> simp
    exact WP.mono (mr_ok Ri hu hc) fr
  · have hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = true := by
      revert hz; cases Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) <;> simp
    exact WP.mono (comp_ok hu hc) fr

/-! ## The exit -/

theorem status_le (x : Option (Bool × Spec.RsaKeyGen.Rand)) : Proof.Dsa.ProbablePrime.status x ≤ 2 := by
  rcases x with _ | ⟨_ | _, _⟩ <;> simp [Proof.Dsa.ProbablePrime.status]

theorem status_eq_zero {x : Option (Bool × Spec.RsaKeyGen.Rand)} (h : Proof.Dsa.ProbablePrime.status x = 0) :
    x = none := by
  rcases x with _ | ⟨_ | _, _⟩ <;> first | rfl | cases h

theorem savedSlots_restorable : Spill.Restorable .t3 savedSlots := by decide
theorem savedSlots_regs : savedSlots.map Prod.fst =
    [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .ra, .a4] := by decide

/-- After the exit's first block: the calling convention's registers back,
the status in `a0`, `hUsed` in `t2` and `used` in `a4`. -/
def XMid (bits : Nat) (σ t f : State) : Prop :=
  abiPreserved σ f ∧ f.gpr .a0 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ)) ∧
    f.gpr .t2 = word t.mem (wsB σ) (8 * hUsed) ∧ f.gpr .a4 = σ.gpr .a4 ∧ f.mem = t.mem ∧ f.wr = t.wr

theorem exitA_ok {bits : Nat} {σ s t : State} (h : CIn bits σ) (o : BOut bits σ s t)
    (svd : Spill.Saved (σ.gpr .a0) σ.gpr savedSlots t.mem) :
    WP isa (.block ([ldh .a0 hStat, ldh .t2 hUsed, .addi .t3 .s6 (-(keyOff : Int))] ++ restore)) t
      (XMid bits σ t) := by
  obtain hsc : Scr t (wsB σ) (8 * keyWords bits) := scr_of h o.wr
  have hsz := h.size
  have hfw := h.fw
  obtain hst := status_le (res bits σ)
  obtain hkw : 32 ≤ keyWords bits := by unfold keyWords; omega
  obtain hwsW : cW σ ∈ t.wr := by rw [o.wr, h.wr]; exact List.mem_cons_self
  obtain inWs : ∀ d, d + 8 ≤ (σ.gpr .a1).toNat * 8 → InRegions (t.rd ++ t.wr) (σ.gpr .a0 + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hwsW, by
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; omega⟩
  rw [WP.block_append_iff]
  have s6 := o.s6
  refine wp_sp_syms (WP.mono (WP.keep [.a0, .t2, .t3] (Q := fun (u : State) =>
      u.gpr .a0 = word t.mem (wsB σ) (8 * hStat) ∧ u.gpr .t2 = word t.mem (wsB σ) (8 * hUsed) ∧
      u.gpr .t3 = σ.gpr .a0 ∧ u.mem = t.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u0, u2, u3, um⟩, ku⟩ usp _ => ?_)
  · have e3 : wsB σ - BitVec.ofNat 64 keyOff = σ.gpr .a0 := BitVec.add_sub_cancel _ _
    generalize wsB σ = B at hsc s6 e3 ⊢
    simp only [ldh, hStat, hUsed]
    brun [s6, show keyOff ≤ 2048 by decide, e3, hsc.ld (d := 160) (n := 8) (by omega),
      hsc.al8 (d := 160) (by omega) (by decide), hsc.ld (d := 152) (n := 8) (by omega),
      hsc.al8 (d := 152) (by omega) (by decide)]
  refine WP.mono (Spill.restore_wp (b := .t3) (B := σ.gpr .a0) h.alW u3 savedSlots_fits.1 savedSlots_restorable
    (fun p hp => by
      rw [ku.2.1, ku.2.2]
      exact inWs _ (by have := savedSlots_in p hp; simp only [saveOff, keyOff] at *; omega))
    (by rw [um]; exact svd)) fun f hf => ?_
  obtain hpres : ∀ r ∈ preserved, r ∈ savedSlots.map Prod.fst := by rw [savedSlots_regs]; decide
  obtain o0 : f.gpr .a0 = u.gpr .a0 := hf.other _ (by rw [savedSlots_regs]; decide)
  obtain o2 : f.gpr .t2 = u.gpr .t2 := hf.other _ (by rw [savedSlots_regs]; decide)
  refine ⟨⟨fun r hr => hf.gpr_of (.inl (hpres r hr)), hf.sp.trans (usp.trans o.sp),
      hf.gpr_of (.inl (by rw [savedSlots_regs]; decide))⟩, ?_, ?_,
    hf.gpr_of (.inl (by rw [savedSlots_regs]; decide)), hf.mem.trans um, hf.wr.trans ku.2.2⟩
  · rw [o0, u0]; exact o.stat
  · rw [o2, u2]

/-- What the exit leaves. -/
structure XOut (bits : Nat) (σ t f : State) : Prop where
  abi : abiPreserved σ f
  a0 : f.gpr .a0 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ))
  frame : Frame [cU σ] t.mem f.mem
  used : ∀ b rest, res bits σ = some (b, rest) →
    Spec.Rsa.wordsAt f.mem (σ.gpr .a4) 1 = [BitVec.ofNat 64 ((σ.gpr .a3).toNat - rest.length)]

theorem exit_ok {bits : Nat} {σ s t : State} (h : CIn bits σ) (o : BOut bits σ s t)
    (svd : Spill.Saved (σ.gpr .a0) σ.gpr savedSlots t.mem) :
    WP isa exit t (XOut bits σ t) := by
  obtain hst := status_le (res bits σ)
  unfold exit
  refine WP.seq (WP.mono (exitA_ok h o svd) fun f ⟨fa, f0, f2, f4, fm, fwr⟩ => ?_)
  refine WP.ite _ (Steps.eval_zero_ofNat f .a0 (by omega) f0) (fun hz => ?_) (fun hz => ?_)
  · have h0 : Proof.Dsa.ProbablePrime.status (res bits σ) = 0 := by simpa using hz
    exact WP.block_nil ⟨fa, f0, by rw [fm]; exact Frame.refl _ _, fun b rest hr => by
      rw [status_eq_zero h0] at hr; cases hr⟩
  · have hU : InRegions f.wr (f.gpr .a4 + BitVec.ofNat 64 0) 8 := ⟨cU σ, by rw [fwr, o.wr, h.wr]; simp, by
      rw [f4]; simp only [Region.Contains, BitVec.add_zero, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
    refine Steps.WP.cons (exec_store_d (by decide) (by rw [f4, BitVec.add_zero]; exact h.alU) hU)
      (WP.block_nil ⟨fa, f0, ?_, fun b rest hr => ?_⟩)
    · rw [f4, fm, BitVec.add_zero]
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
      rw [f4, Mem.readW_writeW_self64, f2, o.used b rest hr]

/-! ## The function -/

/-- A byte at offset `i` of `p` lies outside a region at offset `e`. -/
theorem not_in (p : Addr) {i e k : Nat} (h : i + 1 ≤ e ∨ e + k ≤ i) (hi : i + 1 ≤ 2 ^ 64) (he : e + k ≤ 2 ^ 64) :
    ¬ (⟨p + BitVec.ofNat 64 e, k⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint p h hi he _ (Region.contains_self _ _) hc

/-- A region at offset `d` of `ws` lies in `ws`. -/
theorem sub_ws {σ : State} {d n : Nat} (h : d + n ≤ (σ.gpr .a1).toNat * 8) :
    Region.Sub ⟨σ.gpr .a0 + BitVec.ofNat 64 d, n⟩ (cW σ) :=
  Offset.sub_base _ h

/-- What the function leaves. -/
structure COut (bits : Nat) (σ f : State) : Prop where
  abi : abiPreserved σ f
  a0 : f.gpr .a0 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ))
  keeps : Proof.Dsa.ModPow.Keeps (σ.gpr .a0) (σ.gpr .a1).toNat (layout bits).scratch σ.mem f.mem
  used : ∀ b rest, res bits σ = some (b, rest) →
    Spec.Rsa.wordsAt f.mem (σ.gpr .a4) 1 = [BitVec.ofNat 64 ((σ.gpr .a3).toNat - rest.length)]

/-- The bytes of `ws` the test keeps. -/
def Kept (bits : Nat) (σ : State) (m : Mem) : Prop :=
  ∀ i, i < 8 * (σ.gpr .a1).toNat → i < 384 ∨ 384 + (512 - 384 + 8 * keyWords bits) ≤ i →
    m (σ.gpr .a0 + BitVec.ofNat 64 i) = σ.mem (σ.gpr .a0 + BitVec.ofNat 64 i)

/-- After the entry and the candidate's load: the body's context, the saved
registers, and the bytes of `ws` kept. -/
theorem after_loadC {bits : Nat} (hb : Bits bits) {σ s₁ s₂ : State} (h : CIn bits σ) (hk : ConstsOk K 512 σ)
    (ep : EntryPost bits σ s₁)
    (hl : (A s₂.mem (wsB σ) (words bits) 0 = cand bits σ ∧
        Outside (wsB σ) (slot (words bits) 0) (8 * words bits) s₁.mem s₂.mem) ∧
      Keep [.s7, .s8, .a0, .s0, .t3, .t4, .t5] s₁ s₂) (sp₂ : s₂.sp = s₁.sp) (sy₂ : s₂.syms = s₁.syms) :
    BIn bits σ s₂ ∧ Spill.Saved (σ.gpr .a0) σ.gpr savedSlots s₂.mem ∧ Kept bits σ s₂.mem := by
  obtain ⟨⟨c₂, o₂⟩, k₂⟩ := hl
  obtain hs := shape_of hb
  have hsz := h.size
  have hfw := h.fw
  have hkey := hs.key
  have hw48 := hs.w48
  obtain hW : cW σ ∈ σ.wr := by rw [h.wr]; exact List.mem_cons_self
  obtain hslot : slot (words bits) 0 + 8 * words bits ≤ 8 * keyWords bits := by
    simp only [slot, VG.Impl.Bignum.hdrBytes]; omega
  obtain f₁ : Frame [cW σ] σ.mem s₁.mem := ep.frame.sub fun r hr => ⟨cW σ, List.mem_cons_self, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_ws (by simp only [saveOff, keyOff] at *; omega)⟩
  obtain f₂ : Frame [⟨wsB σ, 8 * keyWords bits⟩] s₁.mem s₂.mem := frame_outside o₂ hslot
  obtain f₂' : Frame [cW σ] s₁.mem s₂.mem := f₂.sub fun r hr => ⟨cW σ, List.mem_cons_self, by
    rw [List.mem_singleton] at hr; subst hr; exact sub_ws (by simp only [keyOff] at *; omega)⟩
  obtain fW := f₁.trans f₂'
  obtain bin : BIn bits σ s₂ := by
    refine ⟨hb, h, (env_of hs h ep).keep k₂ (by decide), ep.hdr.keep fun d hd => ?_, ?_, c₂,
      (tab_of hk).frame fW (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact (tab_of hk).wr _ hW)
        (sy₂.trans ep.syms) (k₂.2.1.trans ep.rd) (k₂.2.2.trans ep.wr), ?_, sy₂.trans ep.syms,
      sp₂.trans ep.sp, k₂.2.1.trans ep.rd, k₂.2.2.trans ep.wr⟩
    · have : d + 8 ≤ 256 := by revert d; decide
      exact o₂.word (.inl (by simp only [slot, VG.Impl.Bignum.hdrBytes]; omega)) (by
        have := (env_of hs h ep).hs.nowrap; omega)
    · rw [o₂.word (.inl (by simp only [slot, VG.Impl.Bignum.hdrBytes, hTrial]; omega)) (by
        have := (env_of hs h ep).hs.nowrap; simp only [hTrial]; omega)]
      exact ep.cnt
    · simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      exact fW.bytes (R := cR σ) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact h.wR.symm)
        (by have := (σ.gpr .a3).isLt; exact Nat.le_of_lt this) hi
  refine ⟨bin, ep.svd.frame_in (lo := saveOff) (n := 112) savedSlots_in f₂ fun r hr => ?_, fun i hi hout => ?_⟩
  · rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (show saveOff + 112 ≤ keyOff by decide)) (by simp only [saveOff] at *; omega)
      (by simp only [keyOff] at *; omega)
  simp only [keyOff] at hsz
  obtain e₁ : s₂.mem (σ.gpr .a0 + BitVec.ofNat 64 i) = s₁.mem (σ.gpr .a0 + BitVec.ofNat 64 i) :=
    f₂ _ fun r hr hc => by
      rw [List.mem_singleton] at hr; subst hr
      exact not_in _ (e := keyOff) (by simp only [keyOff]; omega) (by omega) (by simp only [keyOff]; omega) hc
  obtain e₀ : s₁.mem (σ.gpr .a0 + BitVec.ofNat 64 i) = σ.mem (σ.gpr .a0 + BitVec.ofNat 64 i) :=
    ep.frame _ fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact not_in _ (e := saveOff) (by simp only [saveOff]; omega) (by omega) (by simp only [saveOff]; omega) hc
      · exact not_in _ (e := keyOff) (by simp only [keyOff]; omega) (by omega) (by simp only [keyOff]; omega) hc
  rw [e₁, e₀]

/-- The saved registers survive the body. -/
theorem saved_body {bits : Nat} {σ s t : State} (h : CIn bits σ) (bo : BOut bits σ s t)
    (sv : Spill.Saved (σ.gpr .a0) σ.gpr savedSlots s.mem) :
    Spill.Saved (σ.gpr .a0) σ.gpr savedSlots t.mem := by
  have hsz := h.size
  have hfw := h.fw
  refine sv.frame_in (lo := saveOff) (n := 112) savedSlots_in bo.frame fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inl (show saveOff + 112 ≤ keyOff by decide)) (by simp only [saveOff] at *; omega)
      (by simp only [keyOff] at *; omega)
  · exact ((h.sW.sub_left (sub96 σ)).symm.sub_left (sub_ws (by simp only [saveOff, keyOff] at *; omega)))

/-- The body and the exit, from the body's context. -/
theorem tail_ok (Ri : RoundImpl) {bits : Nat} {σ s₂ : State} (h : CIn bits σ) (bin : BIn bits σ s₂)
    (sv₂ : Spill.Saved (σ.gpr .a0) σ.gpr savedSlots s₂.mem) (kept : Kept bits σ s₂.mem) :
    WP isa (.seq (body bits Ri.name Ri.code) exit) s₂ (COut bits σ) := by
  have hsz := h.size
  have hfw := h.fw
  refine WP.seq (WP.mono (body_ok Ri bin) fun t bo => ?_)
  refine WP.mono (exit_ok h bo (saved_body h bo sv₂)) fun f xo => ⟨xo.abi, xo.a0, fun i hi hout => ?_, xo.used⟩
  simp only [layout, List.mem_singleton, forall_eq, saveOff, keyOff] at hout hsz
  obtain inW : (cW σ).Contains (σ.gpr .a0 + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega) (by omega)
  obtain e₃ : f.mem (σ.gpr .a0 + BitVec.ofNat 64 i) = t.mem (σ.gpr .a0 + BitVec.ofNat 64 i) :=
    xo.frame _ fun r hr hc => by rw [List.mem_singleton] at hr; subst hr; exact h.wU _ inW hc
  obtain e₂ : t.mem (σ.gpr .a0 + BitVec.ofNat 64 i) = s₂.mem (σ.gpr .a0 + BitVec.ofNat 64 i) :=
    bo.frame _ fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact not_in _ (e := keyOff) (by simp only [keyOff]; omega) (by omega) (by simp only [keyOff]; omega) hc
      · exact h.sW _ (sub96 σ _ hc) inW
  rw [e₃, e₂, kept i hi (by omega)]

theorem code_ok (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) {σ : State} (h : CIn bits σ)
    (hk : ConstsOk K 512 σ) : WP isa (code bits Ri.name Ri.code) σ (COut bits σ) := by
  obtain hs := shape_of hb
  unfold code
  refine WP.seq (WP.mono (entry_ok hs h) fun s₁ ep => ?_)
  refine WP.seq (wp_sp_syms (WP.mono (loadC_ok hs h ep) fun s₂ hl sp₂ sy₂ => ?_))
  obtain ⟨bin, sv₂, kept⟩ := after_loadC hb h hk ep hl sp₂ sy₂
  exact tail_ok Ri h bin sv₂ kept

end VG.Proof.Dsa.RISCV64.Prime

end

end

-- separate module: its taint checks build in parallel with the correctness proofs, `Correct`

/-!
# DSA's probable-prime test on RISC-V: constant time

As on PPC64LE (`Proof/Dsa/PPC64LE/Prime/CT.lean`). `code_ct`: two runs
from states with the same public data `PD` (the arguments, the stack
pointer, the table's address, the candidate and the tape: the contract's
public data) leak the same trace. Each piece is the taint analysis's (the
entry, the candidate's load, the offset of the witness's top word,
`montPrep`, the blocks that store the status and the exit), or relates the
runs by correctness: trial division (RSA's `trial_divOk.ct`), the blinded
loop (`millerRabin_ct`), and the branches on trial division's result and on
the status, which are functions of the candidate and the tape.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Prime
open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Dsa.RISCV64.ProbablePrime
open VG.Impl.MillerRabin.RISCV64.Search (ldh sth hStat hUsed montPrep)
open VG.Impl.MillerRabin.RISCV64.Blinded (hTopOff)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (hTrial)
open VG.Impl.RsaKeyGen (TrialTable32.symbol)
open VG.Proof.Bignum (word off slot)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite)
open VG.Proof.MillerRabin.RISCV64.Blinded (BD MS BCtx millerRabin_ct Pins.of_imp two_map)

/-- The public data of a call. -/
structure PD where
  a0 : BitVec 64
  a1 : BitVec 64
  a2 : BitVec 64
  a3 : BitVec 64
  a4 : BitVec 64
  sp : Addr
  T : Addr
  c : Nat
  tape : Spec.RsaKeyGen.Rand

/-- A call's start, with public data `d`. -/
structure P0 (bits : Nat) (d : PD) (σ : State) : Prop where
  hb : Bits bits
  cin : CIn bits σ
  hk : ConstsOk K 512 σ
  a0 : σ.gpr .a0 = d.a0
  a1 : σ.gpr .a1 = d.a1
  a2 : σ.gpr .a2 = d.a2
  a3 : σ.gpr .a3 = d.a3
  a4 : σ.gpr .a4 = d.a4
  sp : σ.sp = d.sp
  T : σ.syms TrialTable32.symbol = d.T
  c : cand bits σ = d.c
  tape : tape σ = d.tape

/-- The working space's base, from the public data. -/
abbrev dB (d : PD) : Addr := d.a0 + BitVec.ofNat 64 keyOff

theorem P0.wsB {bits : Nat} {d : PD} {σ : State} (h : P0 bits d σ) : wsB σ = dB d := by
  show σ.gpr .a0 + BitVec.ofNat 64 keyOff = d.a0 + BitVec.ofNat 64 keyOff
  rw [h.a0]

theorem P0.res {bits : Nat} {d : PD} {σ : State} (h : P0 bits d σ) :
    res bits σ = Spec.Dsa.probablePrime d.c d.tape := by
  show Spec.Dsa.probablePrime (cand bits σ) (VG.Proof.Dsa.RISCV64.Prime.tape σ) = _
  rw [h.c, h.tape]

/-- After the entry. -/
def E1 (bits : Nat) (d : PD) (s : State) : Prop := ∃ σ, P0 bits d σ ∧ EntryPost bits σ s

/-- At the body. -/
def E2 (bits : Nat) (d : PD) (s : State) : Prop :=
  ∃ σ, P0 bits d σ ∧ BIn bits σ s ∧ Spill.Saved (σ.gpr .a0) σ.gpr savedSlots s.mem ∧ Kept bits σ s.mem

/-- After trial division. -/
def E2t (bits : Nat) (d : PD) (u : State) : Prop :=
  ∃ σ s, P0 bits d σ ∧ BIn bits σ s ∧
    u.gpr .a4 = BitVec.ofNat 64
      (if VG.Proof.RsaKeyGen.trialPrefix (A s.mem (wsB σ) (words bits) 0) (count bits) then 1 else 0) ∧
    u.mem = s.mem ∧ (∀ r, r ∉ VG.Proof.RsaKeyGen.RISCV64.Cand.tdRegs → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧
    u.wr = s.wr ∧ u.sp = s.sp ∧ u.syms = s.syms

/-- After the offset of the witness's top word. -/
def E2x (bits : Nat) (d : PD) (x : State) : Prop := ∃ σ s, P0 bits d σ ∧ MP bits σ s x

/-- After `montPrep`. -/
def E2m (bits : Nat) (d : PD) (v : State) : Prop :=
  ∃ σ, P0 bits d σ ∧
    BCtx v (wsB σ) (keyWords bits) (words bits) (cand bits σ) (σ.gpr .a2) (σ.gpr .a3).toNat
      ((bits - 1) / 64) (topBits bits) (checks bits) ∧
    word v.mem (wsB σ) (8 * hUsed) = BitVec.ofNat 64 0 ∧
    Spec.Rsa.bytesAt v.mem (σ.gpr .a2) (σ.gpr .a3).toNat = tape σ ∧ v.sp = σ.sp

/-- After the body. -/
def E3 (bits : Nat) (d : PD) (t : State) : Prop :=
  ∃ σ s, P0 bits d σ ∧ Spill.Saved (σ.gpr .a0) σ.gpr savedSlots s.mem ∧ BOut bits σ s t

/-- After the exit's first block. -/
def E4 (bits : Nat) (d : PD) (f : State) : Prop := ∃ σ t, P0 bits d σ ∧ XMid bits σ t f

/-- The registers of the Montgomery arithmetic, and the stack pointer, fixed
by the public data. -/
theorem pins_env' {α : Type} {Φ : α → State → Prop} (B : α → Addr) (L w : α → Nat) (sp : α → Addr)
    (h : ∀ a s, Φ a s → Env s (B a) (8 * L a) (w a) ∧ s.sp = sp a) :
    Pins Φ [.a7, .s5, .t0, .s6] := by
  intro a s₁ s₂ h₁ h₂
  obtain ⟨e₁, p₁⟩ := h a s₁ h₁
  obtain ⟨e₂, p₂⟩ := h a s₂ h₂
  refine ⟨p₁.trans p₂.symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e₁.a7, e₂.a7]
  · rw [e₁.s5, e₂.s5]
  · rw [e₁.t0, e₂.t0]
  · rw [e₁.s6, e₂.s6]

theorem E2t.bin {bits : Nat} {d : PD} {u : State} (h : E2t bits d u) : ∃ σ, P0 bits d σ ∧ BIn bits σ u := by
  obtain ⟨σ, s, p, b, -, um, ug, urd, uwr, usp, usy⟩ := h
  exact ⟨σ, p, bin_after_trial b um ug urd uwr usp usy⟩

/-- The offset of the witness's top word: no secret is involved. -/
theorem topOff_taint {bits : Nat} (hb : Bits bits) : ∃ hc, (VG.Taint.check taint (VG.RISCV64.Taint.ofRegs
    [.a7, .s5, .t0, .s6]) (.block [.li .t2 (topOff bits), sth .t2 hTopOff]) hc).isSome = true := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- The body. -/
theorem body_ct (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) :
    RelCT isa (Two (E2 bits)) (body bits Ri.name Ri.code) fun _ _ => True := by
  have pT : Pins (E2t bits) [.a7, .s5, .t0, .s6] :=
    pins_env' dB (fun _ => keyWords bits) (fun _ => words bits) PD.sp fun d u h => by
      obtain ⟨σ, p, b⟩ := h.bin
      rw [← p.wsB]; exact ⟨b.env, b.sp.trans p.sp⟩
  have pX : Pins (E2x bits) [.a7, .s5, .t0, .s6] :=
    pins_env' dB (fun _ => keyWords bits) (fun _ => words bits) PD.sp fun d x ⟨σ, s, p, hx⟩ => by
      rw [← p.wsB]; exact ⟨hx.env, hx.sp.trans p.sp⟩
  obtain ⟨_, hTop⟩ := topOff_taint hb
  unfold body
  refine RelCT.seq (two_post (Ψ := E2t bits)
    (VG.Proof.RsaKeyGen.RISCV64.Cand.TrialOk.trial_divOk.ct fun s₁ s₂ ⟨d, ⟨σ₁, p₁, b₁, _⟩, ⟨σ₂, p₂, b₂, _⟩⟩ => ?_)
    fun d s ⟨σ, p, b, _, _⟩ => WP.mono (VG.Proof.RsaKeyGen.RISCV64.Cand.TrialOk.trial_divOk.ok b.div)
      fun u hu => ⟨σ, s, p, b, hu⟩) ?_
  · have d₁ := b₁.div
    have d₂ := b₂.div
    rw [p₁.wsB] at d₁
    rw [p₂.wsB] at d₂
    refine ⟨dB d, _, _, _, d₁, d₂, b₁.sp.trans (p₁.sp.trans (b₂.sp.trans p₂.sp).symm),
      (congrFun b₁.syms _).trans (p₁.T.trans ((congrFun b₂.syms _).trans p₂.T).symm), fun i _ => ?_⟩
    rw [← p₁.wsB, b₁.cand, p₁.c, p₁.wsB, ← p₂.wsB, b₂.cand, p₂.c]
  refine two_ite (fun d u₁ u₂ ⟨σ₁, s₁, p₁, b₁, a4, _⟩ ⟨σ₂, s₂, p₂, b₂, b4, _⟩ => ?_) ?_
    (two_taint _ (Pins.of_imp pT fun _ _ h => h.1) (by taint_decide))
  · rw [Steps.eval_zero_ofNat u₁ .a4 (by split <;> decide) a4, Steps.eval_zero_ofNat u₂ .a4 (by split <;> decide) b4,
      b₁.cand, b₂.cand, p₁.c, p₂.c]
  refine RelCT.seq (two_post (Ψ := E2x bits) (two_taint _ (Pins.of_imp pT fun _ _ h => h.1) hTop)
    fun d u ⟨h, _⟩ => ?_) ?_
  · obtain ⟨σ, p, b⟩ := h.bin
    exact WP.mono (topOff_ok b) fun x hx => ⟨σ, u, p, hx⟩
  refine RelCT.seq (two_post (Ψ := E2m bits) (two_taint _ pX (by taint_decide))
    fun d x ⟨σ, s, p, hx⟩ => WP.mono (montPrep_ctx hx) fun v ⟨bc, hu, ht, vsp, _⟩ => ⟨σ, p, bc, hu, ht, vsp⟩) ?_
  refine two_map (fun d => (⟨dB d, d.a2, keyWords bits, words bits, d.c, d.a3.toNat, (bits - 1) / 64,
    topBits bits, checks bits, d.tape, d.sp⟩ : BD)) (fun d v ⟨σ, p, bc, hu, ht, vsp⟩ => ?_) (millerRabin_ct Ri)
  have hB := p.wsB
  rw [← hB, ← p.a2, ← p.a3, ← p.c, ← p.tape, ← p.sp]
  exact ⟨bc, hu, ht, vsp⟩

theorem code_ct (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) :
    RelCT isa (Two (P0 bits)) (code bits Ri.name Ri.code) fun _ _ => True := by
  obtain ⟨_, hE⟩ : ∃ hc, (VG.Taint.check taint (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
      (.block (setup bits)) hc).isSome = true := by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hL⟩ : ∃ hc, (VG.Taint.check taint (VG.RISCV64.Taint.ofRegs [.a0, .a7, .s5, .t0, .s6])
      (loadC bits) hc).isSome = true := by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have pP : Pins (P0 bits) [.a0, .a1, .a2, .a3, .a4] := by
    intro d σ₁ σ₂ p₁ p₂
    refine ⟨p₁.sp.trans p₂.sp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [p₁.a0, p₂.a0]
    · rw [p₁.a1, p₂.a1]
    · rw [p₁.a2, p₂.a2]
    · rw [p₁.a3, p₂.a3]
    · rw [p₁.a4, p₂.a4]
  have p1 : Pins (E1 bits) [.a0, .a7, .s5, .t0, .s6] := by
    have hr : ∀ d s, E1 bits d s → s.gpr .a0 = d.a0 ∧ s.gpr .a7 = off (dB d) (slot (words bits) 0) ∧
        s.gpr .s5 = BitVec.ofNat 64 (8 * (words bits + 2)) ∧ s.gpr .t0 = BitVec.ofNat 64 (words bits) ∧
        s.gpr .s6 = dB d ∧ s.sp = d.sp := fun d s ⟨σ, p, ep⟩ => by
      rw [← p.wsB]
      exact ⟨ep.a0.trans p.a0, ep.a7, ep.s5, ep.t0, ep.s6, ep.sp.trans p.sp⟩
    intro d s₁ s₂ h₁ h₂
    obtain ⟨a0, a7, a5, at0, a6, asp⟩ := hr d s₁ h₁
    obtain ⟨b0, b7, b5, bt0, b6, bsp⟩ := hr d s₂ h₂
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a0, b0]
    · rw [a7, b7]
    · rw [a5, b5]
    · rw [at0, bt0]
    · rw [a6, b6]
  have p3 : Pins (E3 bits) [.s6] := by
    rintro d t₁ t₂ ⟨σ₁, s₁, p₁, -, o₁⟩ ⟨σ₂, s₂, p₂, -, o₂⟩
    refine ⟨o₁.sp.trans (p₁.sp.trans (o₂.sp.trans p₂.sp).symm), fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [o₁.s6, o₂.s6, p₁.wsB, p₂.wsB]
  have p4 : Pins (E4 bits) [.a4] := by
    rintro d f₁ f₂ ⟨σ₁, t₁, p₁, x₁⟩ ⟨σ₂, t₂, p₂, x₂⟩
    refine ⟨x₁.1.2.1.trans (p₁.sp.trans (x₂.1.2.1.trans p₂.sp).symm), fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [x₁.2.2.2.1, x₂.2.2.2.1, p₁.a4, p₂.a4]
  unfold code
  refine RelCT.seq (two_post (Ψ := E1 bits) (two_taint _ pP hE) fun d σ p =>
    WP.mono (entry_ok (shape_of p.hb) p.cin) fun s ep => ⟨σ, p, ep⟩) ?_
  refine RelCT.seq (two_post (Ψ := E2 bits) (two_taint _ p1 hL) fun d s ⟨σ, p, ep⟩ =>
    wp_sp_syms (WP.mono (loadC_ok (shape_of p.hb) p.cin ep) fun s₂ hl sp₂ sy₂ =>
      ⟨σ, p, after_loadC p.hb p.cin p.hk ep hl sp₂ sy₂⟩)) ?_
  refine RelCT.seq (two_post (Ψ := E3 bits) (body_ct Ri hb) fun d s ⟨σ, p, bin, sv, _⟩ =>
    WP.mono (body_ok Ri bin) fun t bo => ⟨σ, s, p, sv, bo⟩) ?_
  unfold exit
  refine RelCT.seq (two_post (Ψ := E4 bits) (two_taint _ p3 (by taint_decide)) fun d t ⟨σ, s, p, sv, bo⟩ =>
    WP.mono (exitA_ok p.cin bo (saved_body p.cin bo sv)) fun f hf => ⟨σ, t, p, hf⟩) ?_
  refine two_ite (fun d f₁ f₂ ⟨σ₁, t₁, p₁, x₁⟩ ⟨σ₂, t₂, p₂, x₂⟩ => ?_) (RelCT.block_nil fun _ _ _ => trivial)
    (two_taint _ (Pins.of_imp p4 fun _ _ h => h.1) (by taint_decide))
  rw [Steps.eval_zero_ofNat f₁ .a0 (by have := status_le (res bits σ₁); omega) x₁.2.1,
    Steps.eval_zero_ofNat f₂ .a0 (by have := status_le (res bits σ₂); omega) x₂.2.1, p₁.res, p₂.res]

end VG.Proof.Dsa.RISCV64.Prime
