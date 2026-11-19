module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Ctx
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCall
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCall
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `MillerRabin.RISCV64.Search.RoundCallCT`, which the modules that import this one used -/

section

/-!
# A prime search on RISC-V: the round's call in constant time

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Search/RoundCallCT.lean`):
`roundCall_ct`, two runs from the same prepared working space and witness
(`RC`) leak the same: the witness into Montgomery form and the arguments
from the working space's registers, the round as its contract makes it
(`RelCT.call`), and the registers back.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Search

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-- A round's call: the working space, the modulus and the witness. -/
structure RcD where
  B : Addr
  L : Nat
  w : Nat
  c : Nat
  a : Nat

/-- The stack below `sp` at a call: aligned, and the round's frame apart from
the working space. -/
def RcStk (s : State) (B : Addr) (L : Nat) : Prop :=
  s.sp.toNat % 16 = 0 ∧ 96 ≤ s.sp.toNat ∧ (below s.sp 96).Disjoint ⟨B, 8 * L⟩

/-- Before the call of a witness's round. -/
def RC (d : RcD) (s : State) : Prop :=
  Prep s d.B d.L d.w d.c ∧ A s.mem d.B d.w 4 = d.a ∧ d.a < d.c ∧ RcStk s d.B d.L

/-- With the arguments in `a0` and `a1`. -/
def RCm (d : RcD) (s : State) : Prop :=
  Prep s d.B d.L d.w d.c ∧ A s.mem d.B d.w 5 = d.a % d.c * 2 ^ (64 * d.w) % d.c ∧
    s.gpr .a0 = d.B ∧ s.gpr .a1 = BitVec.ofNat 64 d.L ∧ RcStk s d.B d.L

theorem pins_RC : Pins RC [.a7, .s5, .t0, .s6] := by
  rintro d s₁ s₂ ⟨h₁, -⟩ ⟨h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.env.a7, h₂.env.a7]
  · rw [h₁.env.s5, h₂.env.s5]
  · rw [h₁.env.t0, h₂.env.t0]
  · rw [h₁.env.s6, h₂.env.s6]

theorem rcPre_ok {d : RcD} {s : State} (h : RC d s) :
    WP isa (.seq (PublicChecked.montOp 5 4 1) (.block [.addi .a0 .s6 0, ldh .a1 hWsLen])) s (RCm d) := by
  obtain ⟨hp, ha, hac, hk⟩ := h
  refine WP.mono (WP.rdwr (rcHead_ok hp ha hac)) fun t ⟨m, _, _, sp⟩ => ?_
  exact ⟨m.prep, m.a5, m.a0, m.a1, by simp only [RcStk, sp]; exact hk⟩

theorem rcPre_ct : RelCT isa (Two RC)
    (.seq (PublicChecked.montOp 5 4 1) (.block [.addi .a0 .s6 0, ldh .a1 hWsLen])) (Two RCm) :=
  two_post (two_taint _ pins_RC (by taint_decide)) fun _ _ h => rcPre_ok h

theorem rcm_pre {d : RcD} {s : State} (h : RCm d s) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pre
      (s.callEntry.withRegions [] [⟨d.B, 8 * d.L⟩]) :=
  rc_pre h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2

theorem rc_pub {d : RcD} {s₁ s₂ : State} (h₁ : RCm d s₁) (h₂ : RCm d s₂) (hsp : s₁.sp = s₂.sp) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pub
      (s₁.callEntry.withRegions [] [⟨d.B, 8 * d.L⟩]) (s₂.callEntry.withRegions [] [⟨d.B, 8 * d.L⟩]) := by
  have e96 : (96 : Nat) = 95 + 1 := rfl
  rw [e96]
  sig_reduce [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, RISCV64.abi,
    RISCV64.argRegs]
  obtain ⟨p₁, -, a0₁, a1₁, -⟩ := h₁
  obtain ⟨p₂, -, a0₂, a1₂, -⟩ := h₂
  rw [a0₁, a1₁, a0₂, a1₂, p₁.width, p₂.width]
  exact ⟨⟨hsp, rfl⟩, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

/-- After the call: the working space's address. -/
def RCc (d : RcD) (s : State) : Prop := s.gpr .s6 = d.B

theorem rcCall_ct (R : RoundImpl) : RelCT isa (Two RCm) (.call R.name R.code) (Two RCc) := by
  refine two_post ?_ fun d s h => ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    obtain ⟨d, h₁, h₂, hsp⟩ := hp
    exact RelCT.call (P := fun a b => a = s₁ ∧ b = s₂) R.verified.1 R.verified.2.1 [] [⟨d.B, 8 * d.L⟩]
      (fun a b ⟨ha, hb⟩ => by
        subst ha hb
        exact ⟨rcm_pre h₁, rcm_pre h₂, rc_pub h₁ h₂ hsp, scr_covers' h₁.1.env.hs, fun _ _ => scr_covers h₁.1.env.hs,
          scr_covers' h₂.1.env.hs, fun _ _ => scr_covers h₂.1.env.hs⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  · have h6 := h.1.env.s6
    exact WP.callAny (k := Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96)
      R.verified.1 (rd := []) (wr := [⟨d.B, 8 * d.L⟩]) (rcm_pre h) (scr_covers' h.1.env.hs)
      (fun _ _ => scr_covers h.1.env.hs)
      (fun s' _ _ _ _ hcs _ => (hcs .s6 (by decide)).trans h6) (by have := R.stack; omega_arith)

theorem pins_RCc : Pins RCc [.s6] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁, h₂]

/-- The round's call leaks the same from the same working space and witness. -/
theorem roundCall_ct (R : RoundImpl) : RelCT isa (Two RC) (roundCall R.name R.code) fun _ _ => True := by
  unfold roundCall
  refine RelCT.assoc (RelCT.seq rcPre_ct (RelCT.seq (rcCall_ct R) ?_))
  exact two_taint _ pins_RCc (by taint_decide)

/-! ## Candidates and witnesses that differ

A search's candidates are secret: two runs call the round from the same
working space, of the same width, on different candidates and witnesses
(`RCw`). The round's public data is only the working space and its width
(`rc_pubw`), so the call leaks the same (`roundCall_ctw`). -/

/-- A round's call of `w` words in the working space `B` of `L` words. -/
structure RcW where
  B : Addr
  L : Nat
  w : Nat

/-- Before the call of a witness's round, on some candidate and witness. -/
def RCw (d : RcW) (s : State) : Prop := ∃ c a, RC ⟨d.B, d.L, d.w, c, a⟩ s

/-- With the arguments in `a0` and `a1`. -/
def RCmw (d : RcW) (s : State) : Prop := ∃ c a, RCm ⟨d.B, d.L, d.w, c, a⟩ s

theorem pins_RCw : Pins RCw [.a7, .s5, .t0, .s6] := by
  rintro d s₁ s₂ ⟨c₁, a₁, h₁⟩ ⟨c₂, a₂, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.1.env.a7, h₂.1.env.a7]
  · rw [h₁.1.env.s5, h₂.1.env.s5]
  · rw [h₁.1.env.t0, h₂.1.env.t0]
  · rw [h₁.1.env.s6, h₂.1.env.s6]

theorem rcPre_ctw : RelCT isa (Two RCw)
    (.seq (PublicChecked.montOp 5 4 1) (.block [.addi .a0 .s6 0, ldh .a1 hWsLen])) (Two RCmw) :=
  two_post (two_taint _ pins_RCw (by taint_decide)) fun _ _ ⟨c, a, h⟩ =>
    WP.mono (rcPre_ok h) fun _ ht => ⟨c, a, ht⟩

theorem rc_pubw {B : Addr} {L w c₁ c₂ a₁ a₂ : Nat} {s₁ s₂ : State} (h₁ : RCm ⟨B, L, w, c₁, a₁⟩ s₁)
    (h₂ : RCm ⟨B, L, w, c₂, a₂⟩ s₂) (hsp : s₁.sp = s₂.sp) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pub
      (s₁.callEntry.withRegions [] [⟨B, 8 * L⟩]) (s₂.callEntry.withRegions [] [⟨B, 8 * L⟩]) := by
  have e96 : (96 : Nat) = 95 + 1 := rfl
  rw [e96]
  sig_reduce [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, RISCV64.abi,
    RISCV64.argRegs]
  obtain ⟨p₁, -, a0₁, a1₁, -⟩ := h₁
  obtain ⟨p₂, -, a0₂, a1₂, -⟩ := h₂
  rw [a0₁, a1₁, a0₂, a1₂, p₁.width, p₂.width]
  exact ⟨⟨hsp, rfl⟩, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

/-- After the call: the working space's address. -/
def RCcw (d : RcW) (s : State) : Prop := s.gpr .s6 = d.B

theorem rcCall_ctw (R : RoundImpl) : RelCT isa (Two RCmw) (.call R.name R.code) (Two RCcw) := by
  refine two_post ?_ fun d s ⟨c, a, h⟩ => ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    obtain ⟨d, ⟨c₁, a₁, h₁⟩, ⟨c₂, a₂, h₂⟩, hsp⟩ := hp
    exact RelCT.call (P := fun a b => a = s₁ ∧ b = s₂) R.verified.1 R.verified.2.1 [] [⟨d.B, 8 * d.L⟩]
      (fun a b ⟨ha, hb⟩ => by
        subst ha hb
        exact ⟨rcm_pre h₁, rcm_pre h₂, rc_pubw h₁ h₂ hsp, scr_covers' h₁.1.env.hs, fun _ _ => scr_covers h₁.1.env.hs,
          scr_covers' h₂.1.env.hs, fun _ _ => scr_covers h₂.1.env.hs⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  · have h6 := h.1.env.s6
    exact WP.callAny (k := Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96)
      R.verified.1 (rd := []) (wr := [⟨d.B, 8 * d.L⟩]) (rcm_pre h) (scr_covers' h.1.env.hs)
      (fun _ _ => scr_covers h.1.env.hs)
      (fun s' _ _ _ _ hcs _ => (hcs .s6 (by decide)).trans h6) (by have := R.stack; omega_arith)

theorem pins_RCcw : Pins RCcw [.s6] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁, h₂]

/-- The round's call leaks the same from the same working space and width,
whatever the candidates and witnesses. -/
theorem roundCall_ctw (R : RoundImpl) : RelCT isa (Two RCw) (roundCall R.name R.code) fun _ _ => True := by
  unfold roundCall
  refine RelCT.assoc (RelCT.seq rcPre_ctw (RelCT.seq (rcCall_ctw R) ?_))
  exact two_taint _ pins_RCcw (by taint_decide)

end VG.Proof.MillerRabin.RISCV64.Search

end

end

/-!
# The blinded Miller–Rabin loop on RISC-V: constant time, the public data

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/CTBase.lean`): two runs of
the loop are related as RSA's signature verification relates them
(`Proof/RsaPkcs1Sig/RISCV64/Two.lean`): both satisfy the same predicate for
the same public data `BD` (the working space, the candidate, the tape and the
search's parameters, and the stack pointer), whatever else memory holds. The
candidate and the tape are public (DSA's primes are), so every branch and
address follows from them; the taint analysis checks the pieces whose
addresses and branches depend only on registers that the predicate fixes
(`two_taint`), and the predicate fixes the others from correctness.
`pins_env`: the working space's registers (`Env`) and the stack pointer.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64
open VG.Proof.MillerRabin.RISCV64 (Env)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite)

/-- The public data of the loop. -/
structure BD where
  B : Addr
  R : Addr
  L : Nat
  w : Nat
  c : Nat
  rl : Nat
  t : Nat
  b : Nat
  ch : Nat
  r : Spec.RsaKeyGen.Rand
  sp : Addr

/-- The loop's context for the public data `a`. -/
def Ctx (a : BD) (s : State) : Prop :=
  BCtx s a.B a.L a.w a.c a.R a.rl a.t a.b a.ch ∧ Spec.Rsa.bytesAt s.mem a.R a.rl = a.r ∧ s.sp = a.sp

/-- A predicate that gives the working space's registers and the stack
pointer fixes them. -/
theorem pins_env {α : Type} {Φ : α → State → Prop} (f : α → BD)
    (h : ∀ a s, Φ a s → Env s (f a).B (8 * (f a).L) (f a).w ∧ s.sp = (f a).sp) :
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

/-- Pins of fewer registers. -/
theorem Pins.sub {α : Type} {Φ : α → State → Prop} {rs rs' : List Reg} (h : Pins Φ rs)
    (hs : ∀ r ∈ rs', r ∈ rs) : Pins Φ rs' := fun a s₁ s₂ h₁ h₂ =>
  ⟨(h a s₁ s₂ h₁ h₂).1, fun r hr => (h a s₁ s₂ h₁ h₂).2 r (hs r hr)⟩

/-- Pins of more registers, each fixed by the predicate. -/
theorem Pins.cons {α : Type} {Φ : α → State → Prop} {rs : List Reg} (h : Pins Φ rs) (r : Reg)
    (hr : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → s₁.gpr r = s₂.gpr r) : Pins Φ (r :: rs) := fun a s₁ s₂ h₁ h₂ =>
  ⟨(h a s₁ s₂ h₁ h₂).1, fun r' hr' => by
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact hr a s₁ s₂ h₁ h₂
    · exact (h a s₁ s₂ h₁ h₂).2 r' hr'⟩

/-- A predicate implied by one with pins has them. -/
theorem Pins.of_imp {α : Type} {Φ Ψ : α → State → Prop} {rs : List Reg} (h : Pins Φ rs)
    (hi : ∀ a s, Ψ a s → Φ a s) : Pins Ψ rs := fun a s₁ s₂ h₁ h₂ => h a s₁ s₂ (hi a s₁ h₁) (hi a s₂ h₂)

/-- Two runs related through a map of their public data. -/
theorem two_map {α β : Type} {Φ : α → State → Prop} {Ψ : β → State → Prop} (f : α → β)
    (hf : ∀ a s, Φ a s → Ψ (f a) s) {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two Ψ) c Q) : RelCT isa (Two Φ) c Q :=
  h.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨f a, hf a _ h₁, hf a _ h₂⟩) fun _ _ h => h

end VG.Proof.MillerRabin.RISCV64.Blinded
