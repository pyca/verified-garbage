module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Correct
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.CTTrial
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.LoopCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Correct
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.CTTrial
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.LoopCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Hdr
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Entry
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Hdr
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Load
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Entry
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Load

/-!
# DSA's probable-prime test on PPC64LE: constant time

`code_ct`: two runs from states with the same public data `PD` (the
arguments, the stack pointer, the table's address, the candidate and the
tape: the contract's public data) leak the same trace. Each piece is the
taint analysis's (the entry, the candidate's load, `prep`, the blocks
that store the status), or relates the runs by correctness: trial division
(`trial_ct`), the blinded loop (`millerRabin_ct`), and the branches on trial
division's result and on the status, which are functions of the candidate
and the tape.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.RsaKeyGen
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hStat hUsed)
open VG.Proof.Bignum (word off slot)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two Pins two_post two_taint two_ite)
open VG.Proof.MillerRabin.PPC64LE.Blinded (BD MS BCtx millerRabin_ct Pins.of_imp two_map)

/-- The public data of a call. -/
structure PD where
  r3 : BitVec 64
  r4 : BitVec 64
  r5 : BitVec 64
  r6 : BitVec 64
  r7 : BitVec 64
  sp : Addr
  T : Addr
  c : Nat
  tape : Spec.RsaKeyGen.Rand

/-- A call's start, with public data `d`. -/
def P0 (bits : Nat) (d : PD) (σ : State) : Prop :=
  Bits bits ∧ CIn bits σ ∧ ConstsOk K 176 σ ∧ σ.gpr .r3 = d.r3 ∧ σ.gpr .r4 = d.r4 ∧ σ.gpr .r5 = d.r5 ∧
    σ.gpr .r6 = d.r6 ∧ σ.gpr .r7 = d.r7 ∧ σ.sp = d.sp ∧ σ.syms TrialTable32.symbol = d.T ∧ cand bits σ = d.c ∧
    tape σ = d.tape

/-- After the entry. -/
def E1 (bits : Nat) (d : PD) (s : State) : Prop := ∃ σ, P0 bits d σ ∧ EntryPost bits σ s ∧ s.syms = σ.syms

/-- At the body. -/
def E2 (bits : Nat) (d : PD) (s : State) : Prop :=
  ∃ σ, P0 bits d σ ∧ BIn bits σ s ∧ Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots s.mem ∧
    Kept bits σ s.mem

/-- After trial division. -/
def E2t (bits : Nat) (d : PD) (u : State) : Prop :=
  ∃ σ s, P0 bits d σ ∧ BIn bits σ s ∧
    (u.gpr .r22 = BitVec.ofNat 64 (if VG.Proof.RsaKeyGen.trialPrefix (cand bits σ) (count bits) then 1 else 0) ∧
      u.mem = s.mem) ∧ (∀ r, r ∉ trialRegs → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      u.syms = s.syms

/-- After `prep`. -/
def E2m (bits : Nat) (d : PD) (v : State) : Prop :=
  ∃ σ, P0 bits d σ ∧
    BCtx v (wsB σ) (keyWords bits) (words bits) (cand bits σ) (σ.gpr .r5) (σ.gpr .r6).toNat
      ((bits - 1) / 64) (topBits bits) (checks bits) ∧
    word v.mem (wsB σ) (8 * hUsed) = BitVec.ofNat 64 0 ∧
    Spec.Rsa.bytesAt v.mem (σ.gpr .r5) (σ.gpr .r6).toNat = tape σ ∧ v.sp = σ.sp

/-- After the body. -/
def E3 (bits : Nat) (d : PD) (t : State) : Prop :=
  ∃ σ s, P0 bits d σ ∧ Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots s.mem ∧ BOut bits σ s t

/-- After the exit's first block. -/
def E4 (bits : Nat) (d : PD) (f : State) : Prop := ∃ σ t, P0 bits d σ ∧ XMid bits σ t f

/-- The working space's base, from the public data. -/
abbrev dB (d : PD) : Addr := d.r3 + BitVec.ofNat 64 keyOff

theorem P0.wsB {bits : Nat} {d : PD} {σ : State} (h : P0 bits d σ) : wsB σ = dB d := by
  show σ.gpr .r3 + BitVec.ofNat 64 keyOff = d.r3 + BitVec.ofNat 64 keyOff
  rw [h.2.2.2.1]

theorem E2.env {bits : Nat} {d : PD} {s : State} (h : E2 bits d s) :
    Env s (dB d) (8 * keyWords bits) (words bits) ∧ s.sp = d.sp := by
  obtain ⟨σ, p, b, -, -⟩ := h
  rw [← p.wsB]
  exact ⟨b.env, b.sp.trans p.2.2.2.2.2.2.2.2.1⟩

theorem E2t.bin {bits : Nat} {d : PD} {u : State} (h : E2t bits d u) : ∃ σ, P0 bits d σ ∧ BIn bits σ u := by
  obtain ⟨σ, s, p, b, ⟨-, um⟩, ug, urd, uwr, usp, usy⟩ := h
  exact ⟨σ, p, bin_after_trial b um ug urd uwr usp usy⟩

theorem pins_env' {α : Type} {Φ : α → State → Prop} (B : α → Addr) (L w : α → Nat) (sp : α → Addr)
    (h : ∀ a s, Φ a s → Env s (B a) (8 * L a) (w a) ∧ s.sp = sp a) :
    Pins Φ [.r10, .r11, .r29, .r31] := by
  intro a s₁ s₂ h₁ h₂
  obtain ⟨e₁, p₁⟩ := h a s₁ h₁
  obtain ⟨e₂, p₂⟩ := h a s₂ h₂
  refine ⟨p₁.trans p₂.symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e₁.h10, e₂.h10]
  · rw [e₁.h11, e₂.h11]
  · rw [e₁.h29, e₂.h29]
  · rw [e₁.h31, e₂.h31]

/-- The body. -/
theorem body_ct (Ri : RoundImpl) (bits : Nat) :
    RelCT isa (Two (E2 bits)) (body bits Ri.name Ri.code) fun _ _ => True := by
  have pE : Pins (E2 bits) [.r10, .r11, .r29, .r31] :=
    pins_env' dB (fun _ => keyWords bits) (fun _ => words bits) PD.sp fun _ _ h => h.env
  have pT : Pins (E2t bits) [.r10, .r11, .r29, .r31] :=
    pins_env' dB (fun _ => keyWords bits) (fun _ => words bits) PD.sp fun d u h => by
      obtain ⟨σ, p, b⟩ := h.bin
      rw [← p.wsB]; exact ⟨b.env, b.sp.trans p.2.2.2.2.2.2.2.2.1⟩
  unfold body
  refine RelCT.seq (two_post (Ψ := E2t bits) (two_map (fun d => (⟨dB d, d.T, keyWords bits, words bits, d.c,
      count bits, d.sp⟩ : TD)) (fun d s ⟨σ, p, b, _, _⟩ => ?_) trial_ct) fun d s ⟨σ, p, b, _, _⟩ => ?_) ?_
  · exact WP.mono (trial_ok b.env b.cand b.hdr.cnt (by rw [b.syms]) b.tab b.tabR) fun u hu => ⟨σ, s, p, b, hu⟩
  · have hn : 1 ≤ count bits ∧ count bits ≤ 1024 := by unfold count; split <;> decide
    rw [← p.wsB]
    refine ⟨b.env, b.cand.trans p.2.2.2.2.2.2.2.2.2.2.1, b.hdr.cnt, (congrFun b.syms _).trans p.2.2.2.2.2.2.2.2.2.1,
      by rw [← p.2.2.2.2.2.2.2.2.2.1]; exact b.tab, by rw [← p.2.2.2.2.2.2.2.2.2.1]; exact b.tabR,
      b.sp.trans p.2.2.2.2.2.2.2.2.1, hn.1, hn.2⟩
  refine two_ite (fun d u₁ u₂ ⟨σ₁, s₁, p₁, _, ⟨a22, _⟩, _⟩ ⟨σ₂, s₂, p₂, _, ⟨b22, _⟩, _⟩ => ?_) ?_ ?_
  · rw [VG.PPC64LE.eval_zero, VG.PPC64LE.eval_zero, a22, b22, p₁.2.2.2.2.2.2.2.2.2.2.1,
      p₂.2.2.2.2.2.2.2.2.2.2.1]
  · refine RelCT.seq (two_post (Ψ := E2m bits) (two_taint _ (Pins.of_imp pT fun _ _ h => h.1)
      (by unfold prep; split <;> taint_decide))
      fun d u ⟨h, _⟩ => ?_) ?_
    · obtain ⟨σ, p, b⟩ := h.bin
      exact WP.mono (montPrep_ctx b) fun v ⟨bc, hu, ht, vsp, _⟩ => ⟨σ, p, bc, hu, ht, vsp⟩
    refine two_map (fun d => (⟨dB d, d.r5, keyWords bits, words bits, d.c, d.r6.toNat, (bits - 1) / 64,
      topBits bits, checks bits, d.tape, d.sp⟩ : BD)) (fun d v ⟨σ, p, bc, hu, ht, vsp⟩ => ?_) (millerRabin_ct Ri)
    have hB := p.wsB
    obtain ⟨-, -, -, -, -, h5, h6, -, hsp, -, hc, htp⟩ := p
    rw [← hB, ← h5, ← h6, ← hc, ← htp, ← hsp]
    exact ⟨bc, hu, ht, vsp⟩
  · exact two_taint _ (Pins.of_imp pT fun _ _ h => h.1) (by taint_decide)

theorem P0.res {bits : Nat} {d : PD} {σ : State} (h : P0 bits d σ) : res bits σ = Spec.Dsa.probablePrime d.c d.tape := by
  show Spec.Dsa.probablePrime (cand bits σ) (tape σ) = _
  rw [h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2]

theorem code_ct (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) :
    RelCT isa (Two (P0 bits)) (code bits Ri.name Ri.code) fun _ _ => True := by
  obtain ⟨_, hE⟩ : ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
      (.block (save ++ setup bits)) hc).isSome = true := by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hL⟩ : ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs [.r3, .r10, .r11, .r29, .r31])
      (loadC bits) hc).isSome = true := by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have pP : Pins (P0 bits) [.r3, .r4, .r5, .r6, .r7] := by
    rintro d σ₁ σ₂ ⟨-, -, -, a3, a4, a5, a6, a7, asp, -⟩ ⟨-, -, -, b3, b4, b5, b6, b7, bsp, -⟩
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a3, b3]
    · rw [a4, b4]
    · rw [a5, b5]
    · rw [a6, b6]
    · rw [a7, b7]
  have p1 : Pins (E1 bits) [.r3, .r10, .r11, .r29, .r31] := by
    have hr : ∀ d s, E1 bits d s → s.gpr .r3 = d.r3 ∧ s.gpr .r10 = d.r3 + BitVec.ofNat 64 (keyOff + hdrBytes) ∧
        s.gpr .r11 = BitVec.ofNat 64 (2 * words bits) ∧ s.gpr .r29 = BitVec.ofNat 64 (8 * (words bits + 2)) ∧
        s.gpr .r31 = d.r3 + BitVec.ofNat 64 keyOff ∧ s.sp = d.sp := fun d s ⟨σ, p, ep, _⟩ => by
      have h3 := p.2.2.2.1
      exact ⟨(ep.other .r3 (by decide) (by decide)).trans h3, by rw [ep.regs.r10, h3], ep.regs.r11, ep.regs.r29,
        by rw [ep.regs.r31, h3], ep.sp.trans p.2.2.2.2.2.2.2.2.1⟩
    intro d s₁ s₂ h₁ h₂
    obtain ⟨a3, a10, a11, a29, a31, asp⟩ := hr d s₁ h₁
    obtain ⟨b3, b10, b11, b29, b31, bsp⟩ := hr d s₂ h₂
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a3, b3]
    · rw [a10, b10]
    · rw [a11, b11]
    · rw [a29, b29]
    · rw [a31, b31]
  have p3 : Pins (E3 bits) [.r31] := by
    rintro d t₁ t₂ ⟨σ₁, s₁, p₁, -, o₁⟩ ⟨σ₂, s₂, p₂, -, o₂⟩
    refine ⟨o₁.sp.trans (p₁.2.2.2.2.2.2.2.2.1.trans (o₂.sp.trans p₂.2.2.2.2.2.2.2.2.1).symm), fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [o₁.r31, o₂.r31, p₁.wsB, p₂.wsB]
  have p4 : Pins (E4 bits) [.r7] := by
    rintro d f₁ f₂ ⟨σ₁, t₁, p₁, x₁⟩ ⟨σ₂, t₂, p₂, x₂⟩
    refine ⟨x₁.1.2.1.trans (p₁.2.2.2.2.2.2.2.2.1.trans (x₂.1.2.1.trans p₂.2.2.2.2.2.2.2.2.1).symm), fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [x₁.2.2.2.1, x₂.2.2.2.1, p₁.2.2.2.2.2.2.2.1, p₂.2.2.2.2.2.2.2.1]
  unfold code
  refine RelCT.seq (two_post (Ψ := E1 bits) (two_taint _ pP hE) fun d σ p =>
    WP.mono_syms (entry_ok (shape_of p.1) p.2.1) fun s ep sy => ⟨σ, p, ep, sy⟩) ?_
  refine RelCT.seq (two_post (Ψ := E2 bits) (two_taint _ p1 hL) fun d s ⟨σ, p, ep, sy₁⟩ =>
    WP.mono_syms (loadC_ok (shape_of p.1) p.2.1 ep) fun s₂ hl sy₂ =>
      ⟨σ, p, after_loadC p.1 p.2.1 p.2.2.1 ep sy₁ hl sy₂⟩) ?_
  refine RelCT.seq (two_post (Ψ := E3 bits) (body_ct Ri bits) fun d s ⟨σ, p, bin, sv, _⟩ =>
    WP.mono (body_ok Ri bin) fun t bo => ⟨σ, s, p, sv, bo⟩) ?_
  unfold exit
  refine RelCT.seq (two_post (Ψ := E4 bits) (two_taint _ p3 (by taint_decide)) fun d t ⟨σ, s, p, sv, bo⟩ =>
    WP.mono (exitA_ok p.2.1 bo (saved_body p.2.1 bo sv)) fun f hf => ⟨σ, t, p, hf⟩) ?_
  refine two_ite (fun d f₁ f₂ ⟨σ₁, t₁, p₁, x₁⟩ ⟨σ₂, t₂, p₂, x₂⟩ => ?_) (RelCT.block_nil fun _ _ _ => trivial)
    (two_taint _ (Pins.of_imp p4 fun _ _ h => h.1) (by taint_decide))
  rw [VG.PPC64LE.eval_zero, VG.PPC64LE.eval_zero, x₁.2.1, x₂.2.1, p₁.res, p₂.res]

end VG.Proof.Dsa.PPC64LE.Prime
