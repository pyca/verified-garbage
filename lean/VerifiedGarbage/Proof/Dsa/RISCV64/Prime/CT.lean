module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Prime.Correct
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.LoopCT
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Prime.Correct
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.LoopCT
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Omega

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
