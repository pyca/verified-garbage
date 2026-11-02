module

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

end VG.Proof.MillerRabin.RISCV64.Search
