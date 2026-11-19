module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtQ
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Math
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Rsa.AArch64.Crt
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Impl.Rsa.AArch64.Crt
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual

/-! ### `Bignum.AArch64.CrtCTPSub`, which only this module used -/

section

/-!
# RSA with the CRT on AArch64: constant time, the steps of `p`'s phase

How a phase is composed: each piece's claim, for a predicate that carries
its hypotheses and what correctness gives after it (`ct_step`), and
`subModArr` (`subModArr_ct`), whose two loops run from bases loaded from the
header: the loads before the second loop are checked from `x0` and `x12`,
which the first loop keeps (`smMid_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## Composing pieces -/

/-- A piece whose claim holds for public data `g a`, then the rest, from
what correctness gives after the piece. -/
theorem ct_step {α β : Type} {Φ Ψ : α → State → Prop} {P : β → State → Prop} {c rest : Prog isa}
    (g : α → β) (hP : ∀ a s, Φ a s → P (g a) s) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a))
    (hc : RelCT isa (Two P) c fun _ _ => True) (hr : RelCT isa (Two Ψ) rest fun _ _ => True) :
    RelCT isa (Two Φ) (.seq c rest) fun _ _ => True :=
  RelCT.seq (two_post (two_map g hP hc) hw) hr

/-- A piece checked by the taint analysis from the registers `rs`, then the rest. -/
theorem ct_taint {α : Type} {Φ Ψ : α → State → Prop} {c rest : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) (hr : RelCT isa (Two Ψ) rest fun _ _ => True) :
    RelCT isa (Two Φ) (.seq c rest) fun _ _ => True :=
  RelCT.seq (two_piece rs hpin h hw) hr

/-- A list of pieces whose claim holds for public data `g a`, then the rest. -/
theorem ct_steps {α β : Type} {Φ Ψ : α → State → Prop} {P : β → State → Prop} {c rest : List (Prog isa)}
    (hc0 : c ≠ []) (hr0 : rest ≠ []) (g : α → β) (hP : ∀ a s, Φ a s → P (g a) s)
    (hw : ∀ a s, Φ a s → WP isa (seqs c) s (Ψ a))
    (hc : RelCT isa (Two P) (seqs c) fun _ _ => True) (hr : RelCT isa (Two Ψ) (seqs rest) fun _ _ => True) :
    RelCT isa (Two Φ) (seqs (c ++ rest)) fun _ _ => True :=
  RelCT.seqs_append hc0 hr0 (ct_step g hP hw hc hr)

/-- The last piece. -/
theorem ct_last {α β : Type} {Φ : α → State → Prop} {P : β → State → Prop} {c : Prog isa}
    (g : α → β) (hP : ∀ a s, Φ a s → P (g a) s) (hc : RelCT isa (Two P) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  two_map g hP hc

/-! ## `subModArr` -/

/-- `subModArr`'s blocks and loops. -/
def smBlk1 (a b : Nat) : List Instr :=
  [ldh .x16 (sArr a), ldh .x17 (sArr b), ldh .x13 (sArr Public.aAcc), ldh .x12 sW, movi .x7 0, mov .x14 .x12,
    .subs .x .x3 .x7 .x7]

def smLoop1 : Prog isa :=
  countLoop .x14 [ld .x3 .x16, ld .x4 .x17, .sbcs .x .x3 .x3 .x4, st .x3 .x13, next .x16, next .x17, next .x13]

def smBlk3 (o : Nat) : List Instr :=
  borrowMask ++ [ldh .x10 (sArr Public.aN), ldh .x8 (sArr Public.aAcc), ldh .x5 (sArr o), mov .x14 .x12,
    .adds .x .x3 .x7 .x7]

def smLoop2 : Prog isa :=
  countLoop .x14 [ld .x3 .x10, .logic .and .x .x3 .x3 .x15, ld .x4 .x8, .adcs .x .x3 .x3 .x4, st .x3 .x5,
    next .x10, next .x8, next .x5]

theorem subModArr_eq (o a b : Nat) :
    seqs (subModArr o a b) = .seq (.block (smBlk1 a b)) (.seq smLoop1 (.seq (.block (smBlk3 o)) smLoop2)) := rfl

/-- `subModArr`'s hypotheses for its timing: the workspace and its size. -/
def SmPre (L : Ws) (s : State) : Prop := GoodW L s ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31

/-- Before `subModArr aT aY aXc`'s first loop. -/
def Sm1 (L : Ws) (t : State) : Prop :=
  ∃ minv, Good t L.B L.Z L.w minv ∧ slot L.w 8 ≤ L.Z ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31 ∧
    t.gpr .x16 = off L.B (slot L.w Public.aY) ∧ t.gpr .x17 = off L.B (slot L.w aXc) ∧
    t.gpr .x13 = off L.B (slot L.w Public.aAcc) ∧ t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x7 = 0 ∧
    t.gpr .x14 = BitVec.ofNat 64 L.w ∧ t.c = true

/-- Before its second loop: its bases and count. -/
def Sm3 (L : Ws) (t : State) : Prop :=
  t.gpr .x0 = L.B ∧ t.gpr .x10 = off L.B (slot L.w Public.aN) ∧ t.gpr .x8 = off L.B (slot L.w Public.aAcc) ∧
    t.gpr .x5 = off L.B (slot L.w aT) ∧ t.gpr .x14 = BitVec.ofNat 64 L.w

theorem pins_smPre : Pins SmPre [.x0] := fun L s₁ s₂ h₁ h₂ => pins_goodW L s₁ s₂ h₁.1 h₂.1

theorem pins_sm1 : Pins Sm1 [.x0, .x12, .x13, .x14, .x16, .x17] := by
  intro L s₁ s₂ ⟨_, g₁, _, _, _, a₁, b₁, c₁, d₁, _, e₁, _⟩ ⟨_, g₂, _, _, _, a₂, b₂, c₂, d₂, _, e₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [g₁.x0, g₂.x0]
  · rw [d₁, d₂]
  · rw [c₁, c₂]
  · rw [e₁, e₂]
  · rw [a₁, a₂]
  · rw [b₁, b₂]

theorem pins_sm3 : Pins Sm3 [.x0, .x5, .x8, .x10, .x14] := by
  intro L s₁ s₂ ⟨a₁, b₁, c₁, d₁, e₁⟩ ⟨a₂, b₂, c₂, d₂, e₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [d₁, d₂]
  · rw [c₁, c₂]
  · rw [b₁, b₂]
  · rw [e₁, e₂]

/-- `subModArr aT aY aXc`'s first block. -/
theorem sm1_ok {L : Ws} {s : State} (h : SmPre L s) : WP isa (.block (smBlk1 Public.aY aXc)) s (Sm1 L) := by
  obtain ⟨⟨minv, hg, hZ⟩, hw, hw'⟩ := h
  have hl := GoodW.hl ⟨minv, hg, hZ⟩
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega_arith
  refine WP.mono (WP.keep [.x3, .x7, .x12, .x13, .x14, .x16, .x17] (Q := fun t =>
      t.gpr .x16 = off L.B (slot L.w Public.aY) ∧ t.gpr .x17 = off L.B (slot L.w aXc) ∧
      t.gpr .x13 = off L.B (slot L.w Public.aAcc) ∧ t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x7 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 L.w ∧ t.c = true ∧ t.mem = s.mem)
    (by brun [smBlk1, hg.x0, hdr_enc (sa _ (show Public.aY < 8 by decide)), hdr_enc (sa _ (show aXc < 8 by decide)),
      hdr_enc (sa _ (show Public.aAcc < 8 by decide)), hdr_enc (show sW < 32 by decide),
      hl _ (sa _ (show Public.aY < 8 by decide)), hl _ (sa _ (show aXc < 8 by decide)),
      hl _ (sa _ (show Public.aAcc < 8 by decide)), hl sW (by decide), hg.hdr.harr Public.aY (by decide),
      hg.hdr.harr aXc (by decide), hg.hdr.harr Public.aAcc (by decide), hg.hdr.hw])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h16, h17, h13, h12, h7, h14, hc, hm⟩, k⟩ => ?_
  exact ⟨minv, ⟨hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, by rw [hm]; exact hg.hdr⟩, hZ, hw, hw',
    h16, h17, h13, h12, h7, h14, hc⟩

/-- `subModArr aT aY aXc`'s first loop and the block after it, as
`subModArr_ok` runs them. -/
theorem smMid_ok {L : Ws} {t : State} (h : Sm1 L t) :
    WP isa (.seq smLoop1 (.block (smBlk3 aT))) t (Sm3 L) := by
  obtain ⟨minv, hg, hZ, hw, hw', h16, h17, h13, h12, h7, h14, hc₁⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot L.w j + 8 * (L.w + 2) ≤ L.Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega_arith
  have h0' : SubInv t L.B L.Z (slot L.w Public.aY) (slot L.w aXc) (slot L.w Public.aAcc) 0 t :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [h13]; rfl, Outside.refl _ _ _ _,
      by rw [hc₁]; rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := L.w) (by omega_arith) (by omega_arith)
    (SubInv t L.B L.Z (slot L.w Public.aY) (slot L.w aXc) (slot L.w Public.aAcc))
    (fun j hj u hI _ => subStep_ok (by have := sl _ (show Public.aY < 8 by decide); omega_arith)
      (by have := sl _ (show aXc < 8 by decide); omega_arith) (by have := sl _ (show Public.aAcc < 8 by decide); omega_arith)
      (by have := arr_sep (w := L.w) (show Public.aY ≠ Public.aAcc by decide); omega_arith)
      (by have := arr_sep (w := L.w) (show aXc ≠ Public.aAcc by decide); omega_arith) hj hI) h0' h14) fun s₂ hI => ?_)
  have s₂0 : s₂.gpr .x0 = L.B := (hI.keep.gpr .x0 (by decide)).trans hg.x0
  have s₂7 : s₂.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  have s₂12 : s₂.gpr .x12 = BitVec.ofNat 64 L.w := (hI.keep.gpr .x12 (by decide)).trans h12
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega_arith)
  have fh : ∀ i < 32, word s₂.mem L.B (8 * i) = word t.mem L.B (8 * i) := fun i hi =>
    hI.out.word (Or.inl (by have := hdr_lt_slot L.w Public.aAcc hi; omega_arith)) (by have := hdr_lt_slot L.w 8 hi; omega_arith)
  have aN : word s₂.mem L.B (8 * sArr Public.aN) = off L.B (slot L.w Public.aN) :=
    (fh _ (sa _ (show Public.aN < 8 by decide))).trans (hg.hdr.harr _ (show Public.aN < 8 by decide))
  have aA : word s₂.mem L.B (8 * sArr Public.aAcc) = off L.B (slot L.w Public.aAcc) :=
    (fh _ (sa _ (show Public.aAcc < 8 by decide))).trans (hg.hdr.harr _ (show Public.aAcc < 8 by decide))
  have aT' : word s₂.mem L.B (8 * sArr aT) = off L.B (slot L.w aT) :=
    (fh _ (sa _ (show aT < 8 by decide))).trans (hg.hdr.harr aT (by decide))
  have e1 := hdr_enc (sa _ (show Public.aN < 8 by decide))
  have e2 := hdr_enc (sa _ (show Public.aAcc < 8 by decide))
  have e3 := hdr_enc (sa _ (show aT < 8 by decide))
  have l1 := hl₂ _ (sa _ (show Public.aN < 8 by decide))
  have l2 := hl₂ _ (sa _ (show Public.aAcc < 8 by decide))
  have l3 := hl₂ _ (sa _ (show aT < 8 by decide))
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x8, .x10, .x14, .x15] (Q := Sm3 L) ?_
    (by decide) (by decide) (by decide +kernel)) fun _ h => h.1
  brun [Sm3, smBlk3, borrowMask, s₂0, s₂7, s₂12, csel_mask_not, e1, e2, e3, l1, l2, l3, aN, aA, aT']

/-- `subModArr aT aY aXc`, `p`'s difference, is constant time. -/
theorem subModArr_ct : RelCT isa (Two SmPre) (seqs (subModArr aT Public.aY aXc)) fun _ _ => True := by
  rw [subModArr_eq]
  refine RelCT.seq (two_piece (Ψ := Sm1) [.x0] pins_smPre (by taint_decide) fun _ _ h => sm1_ok h) ?_
  refine RelCT.assoc (RelCT.seq (two_piece (Ψ := Sm3) [.x0, .x12, .x13, .x14, .x16, .x17] pins_sm1
    (by taint_decide) fun _ _ h => smMid_ok h) ?_)
  exact two_taint [.x0, .x5, .x8, .x10, .x14] pins_sm3 (by taint_decide)

end VG.Proof.Bignum.AArch64

end

end

/-! ### `Bignum.AArch64.CrtCTPMq`, which only this module used -/

section

/-!
# RSA with the CRT on AArch64: constant time, `m_q G mod n`

`mqSteps` (`mqPart_ok`) is constant time (`mq_ct`) for a predicate (`Mq0`)
that carries, before each piece, its claim's hypotheses and what
correctness gives after it; `mq_chain` proves it from `mqPart_ok`'s
hypotheses, as `mqPart_ok` runs the pieces.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- The public data of `mqSteps`: the modulus' workspace and `q`'s. -/
structure MqPub where
  B : Addr
  Z : Nat
  w : Nat
  oq : Nat
  wq : Nat

/-- The modulus' workspace. -/
abbrev MqPub.ws (p : MqPub) : Ws := ⟨p.B, p.Z, p.w⟩

/-- `mqSteps`' block loading `q`'s `Y`: `q`'s base, then from it. -/
def mqBlk1 : List Instr := [ldh .x5 sWsQ]

def mqBlk2 : List Instr := [ldw .x16 .x5 (sArr Public.aY), ldw .x12 .x5 sW, ldh .x17 (sArr Public.aX)]

theorem mqSteps_eq (mul : Nat → Nat → Nat → Prog isa) :
    seqs (mqSteps mul) = .seq (zeroArr Public.aX) (.seq (.block (mqBlk1 ++ mqBlk2)) (.seq copyWords
      (.seq (mul Public.aX Public.aX Public.aR2) (mul Public.aX Public.aX Public.aY)))) := rfl

/-- Before `X := X R² R⁻¹`. -/
def Mq3 (M : Mont) (p : MqPub) (s : State) : Prop :=
  GoodW p.ws s ∧ WP isa (M.mm Public.aX Public.aX Public.aR2) s (GoodW p.ws)

/-- Before the copy of `m_q`. -/
def Mq2 (M : Mont) (p : MqPub) (s : State) : Prop :=
  s.gpr .x16 = off p.B (p.oq + slot p.wq Public.aY) ∧ s.gpr .x12 = BitVec.ofNat 64 p.wq ∧
    s.gpr .x17 = off p.B (slot p.w Public.aX) ∧ WP isa copyWords s (Mq3 M p)

/-- Before the loads from `q`'s workspace. -/
def Mq1b (M : Mont) (p : MqPub) (s : State) : Prop :=
  s.gpr .x5 = off p.B p.oq ∧ s.gpr .x0 = p.B ∧ WP isa (.block mqBlk2) s (Mq2 M p)

/-- Before the load of `q`'s base. -/
def Mq1 (M : Mont) (p : MqPub) (s : State) : Prop :=
  s.gpr .x0 = p.B ∧ WP isa (.block mqBlk1) s (Mq1b M p)

/-- Before `mqSteps`. -/
def Mq0 (M : Mont) (p : MqPub) (s : State) : Prop :=
  GoodW p.ws s ∧ WP isa (zeroArr Public.aX) s (Mq1 M p)

/-- `mqSteps` is constant time. -/
theorem mq_ct (M : Mont) : RelCT isa (Two (Mq0 M)) (seqs (mqSteps M.mm)) fun _ _ => True := by
  rw [mqSteps_eq]
  refine ct_step MqPub.ws (fun _ _ h => h.1) (fun _ _ h => h.2) (zeroArr_ct (by decide) (by taint_decide)) ?_
  obtain b1 : RelCT isa (Two (Mq1 M)) (.block mqBlk1) (Two (Mq1b M)) :=
    two_piece [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) fun _ _ h => h.2
  obtain b2 : RelCT isa (Two (Mq1b M)) (.block mqBlk2) (Two (Mq2 M)) :=
    two_piece [.x5, .x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]) (by taint_decide) fun _ _ h => h.2.2
  refine RelCT.seq (RelCT.block_append (RelCT.seq b1 b2)) ?_
  refine ct_taint [.x16, .x12, .x17] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]) (by taint_decide) (fun _ _ h => h.2.2.2) ?_
  exact ct_step MqPub.ws (fun _ _ h => h.1) (fun _ _ h => h.2) (M.ct (by unfold MmUse; decide))
    (ct_last MqPub.ws (fun _ _ h => h) (M.ct (by unfold MmUse; decide)))

/-- `mqPart_ok`'s hypotheses give `Mq0`. -/
theorem mq_chain (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mq : BitVec 64} {N oq wq : Nat}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hN : NVals s B w minv N)
    (hq : word s.mem B (8 * sWsQ) = off B oq) (hws : WsAt s.mem B oq wq mq) (hlo : slot w 8 ≤ oq)
    (hhi : oq + slot wq 8 + wsTab wq ≤ Z) (hwq : 1 ≤ wq) (hwq' : wq ≤ w) : Mq0 M ⟨B, Z, w, oq, wq⟩ s := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain lX := slot_le (w := w) (show Public.aX < 8 by decide)
  obtain hX0 := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
  obtain hY8 := slot_le (w := wq) (show Public.aY < 8 by decide)
  obtain hq8 : 8 * 32 ≤ slot wq 8 := by unfold slot hdrBytes; omega_arith
  obtain hqo : oq < 2 ^ 64 := by omega_arith
  obtain hqY := hdr_lt_slot wq 8 (show sArr Public.aY < 32 by decide)
  obtain hqW := hdr_lt_slot wq 8 (show sW < 32 by decide)
  -- `X := 0`.
  refine ⟨⟨minv, hg, show slot w 8 ≤ Z by omega_arith⟩, WP.mono (zeroArr_ok hg (by omega_arith) (by omega_arith)
    (show Public.aX < 8 by decide)) fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_⟩
  obtain hb₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w Public.aX hi; omega_arith)) (by omega_arith)
  obtain hq₁ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d := fun d hd hd' =>
    ho₁.word (Or.inr (by omega_arith)) hd'
  obtain hs₁ := hs.congr k₁.wr
  obtain hdi₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans hg.x0
  obtain hqy : word s₁.mem B (oq + 8 * sArr Public.aY) = off B (oq + slot wq Public.aY) := by
    rw [hq₁ _ (by omega_arith) (by omega_arith), ← word_off, hws.hdr.harr Public.aY (by decide), off_off]
  obtain hqw : word s₁.mem B (oq + 8 * sW) = BitVec.ofNat 64 wq := by
    rw [hq₁ _ (by omega_arith) (by omega_arith), ← word_off]; exact hws.hdr.hw
  obtain l1 := hs₁.ld (show 8 * sWsQ + 8 ≤ Z by have := hdr_lt_slot w 8 (show sWsQ < 32 by decide); omega_arith)
  refine ⟨hdi₁, WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = off B oq ∧ t.mem = s₁.mem)
    (by brun [mqBlk1, hdi₁, hdr_enc (show sWsQ < 32 by decide), l1, hb₁ sWsQ (by decide), hq])
    (by decide) (by decide) (by decide +kernel)) fun s₁' ⟨⟨h5, hm₁'⟩, k₁'⟩ =>
    ⟨h5, (k₁'.gpr .x0 (by decide)).trans hdi₁, ?_⟩⟩
  obtain hs₁' := hs₁.congr k₁'.wr
  obtain hdi₁' : s₁'.gpr .x0 = B := (k₁'.gpr .x0 (by decide)).trans hdi₁
  obtain hqy' : word s₁'.mem B (oq + 8 * sArr Public.aY) = off B (oq + slot wq Public.aY) := by rw [hm₁']; exact hqy
  obtain hqw' : word s₁'.mem B (oq + 8 * sW) = BitVec.ofNat 64 wq := by rw [hm₁']; exact hqw
  obtain hbx' : word s₁'.mem B (8 * sArr Public.aX) = off B (slot w Public.aX) := by
    rw [hm₁', hb₁ (sArr Public.aX) (by decide)]; exact hg.hdr.harr Public.aX (by decide)
  obtain l2 := hs₁'.ld (show oq + 8 * sArr Public.aY + 8 ≤ Z by omega_arith)
  obtain l3 := hs₁'.ld (show oq + 8 * sW + 8 ≤ Z by omega_arith)
  obtain l4 := hs₁'.ld (show 8 * sArr Public.aX + 8 ≤ Z by
    have := hdr_lt_slot w 8 (show sArr Public.aX < 32 by decide); omega_arith)
  obtain e1 := hdr_enc (sArr_lt (show Public.aY < 8 by decide))
  obtain e2 := hdr_enc (sArr_lt (show Public.aX < 8 by decide))
  refine WP.mono (WP.keep [.x12, .x16, .x17] (Q := fun t => t.gpr .x16 = off B (oq + slot wq Public.aY) ∧
      t.gpr .x12 = BitVec.ofNat 64 wq ∧ t.gpr .x17 = off B (slot w Public.aX) ∧ t.mem = s₁'.mem)
    (by brun [mqBlk2, ldw, hdi₁', h5, e1, hdr_enc (show sW < 32 by decide), e2, l2, hqy', l3, hqw', l4, hbx'])
    (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨hsi₂, h12₂, hbx₂, hm₂⟩, k₂⟩ =>
    ⟨hsi₂, h12₂, hbx₂, ?_⟩
  rw [hm₁'] at hm₂
  obtain k₂ := k₁'.trans k₂
  obtain hs₂ := hs₁.congr k₂.wr
  -- `X := m_q`.
  refine WP.mono (copyWords_ok (S := B) (eS := oq + slot wq Public.aY) (D := B) (eD := slot w Public.aX)
    (w := wq) hsi₂ hbx₂ h12₂ hwq (by omega_arith) (by omega_arith) (fun j hj => hs₂.ld (by omega_arith))
    (fun j hj => hs₂.st (by omega_arith)) (fun j hj b hb => Or.inr (by
      rw [ofs_off B (by omega_arith)]; omega_arith))) fun s₃ ⟨_, _, ho₃, _, _, k₃⟩ => ?_
  obtain hn₃ : ∀ j < 8, j ≠ Public.aX → wv s₃.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj hjx => by
    have := slot_sep (w := w) hjx
    have := slot_le (w := w) hj
    rw [ho₃.wv (by omega_arith) (by omega_arith), hm₂, ho₁.wv (by omega_arith) (by omega_arith)]
  obtain hg₃ : Good s₃ B Z w minv := ⟨hs.congr ((k₁.trans k₂).trans k₃).wr,
    ((k₂.trans k₃).gpr .x0 (by decide)).trans hdi₁, by
      have : ∀ i < 32, word s₃.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
        rw [ho₃.word (Or.inl (by have := hdr_lt_slot w Public.aX hi; omega_arith)) (by omega_arith), hm₂, hb₁ i hi]
      exact ⟨(this _ (by decide)).trans hg.hdr.hw, (this _ (by decide)).trans hg.hdr.hminv,
        fun j hj => (this _ (by unfold sArr; omega_arith)).trans (hg.hdr.harr j hj)⟩⟩
  obtain hw0 : word s₃.mem B (slot w Public.aN) = word s.mem B (slot w Public.aN) := by
    have := slot_sep (w := w) (show Public.aN ≠ Public.aX by decide)
    have := slot_le (w := w) (show Public.aN < 8 by decide)
    rw [ho₃.word (by omega_arith) (by omega_arith), hm₂, ho₁.word (by omega_arith) (by omega_arith)]
  -- `X := m_q R`.
  refine ⟨⟨minv, hg₃, show slot w 8 ≤ Z by omega_arith⟩, WP.mono (crtMmN_ok M hg₃ (by omega_arith) (by omega_arith) (by omega_arith)
    (o := Public.aX) (a := Public.aX) (b := Public.aR2) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ((hn₃ _ (by decide) (by decide)).trans hN.n) (by rw [hw0]; exact hN.inv)
    (by rw [hn₃ _ (by decide) (by decide)]; exact hN.r2lt)) fun s₄ h₄ => ⟨minv, h₄.1, show slot w 8 ≤ Z by omega_arith⟩⟩

end VG.Proof.Bignum.AArch64

end

end

/-! ### `Bignum.AArch64.CrtCTPH`, which only this module used -/

section

/-!
# RSA with the CRT on AArch64: constant time, `h = (m_p - m_q) qInv mod p`

`hSteps` (`hPart_ok`) is constant time (`h_ct`) for a predicate (`H0`) that
carries, before each piece, its claim's hypotheses and what correctness
gives after it; `h_chain` proves it from `hPart_ok`'s hypotheses, as
`hPart_ok` runs the pieces.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- The public data of `hSteps`: the modulus' workspace, `p`'s, and `qInv`'s
pointer and length. -/
structure HPub where
  B : Addr
  Z : Nat
  w : Nat
  o : Nat
  wx : Nat
  qp : Addr
  len : Nat

/-- `p`'s workspace. -/
abbrev HPub.pw (p : HPub) : Ws := ⟨off p.B p.o, slot p.wx 8, p.wx⟩

/-- `p`'s workspace, as `redc`'s and `loadArr`'s claims take it. -/
abbrev HPub.x (p : HPub) : XPub := ⟨p.B, p.Z, p.o, p.w, p.wx⟩

/-- `qInv`, as `loadArr`'s claim takes it. -/
abbrev HPub.q (p : HPub) : BPub := ⟨p.x, p.qp, p.len⟩

/-- Before the way back to the modulus' workspace. -/
def H6 (p : HPub) (s : State) : Prop := s.gpr .x0 = off p.B p.o

/-- Before `h := T qInv R⁻¹`. -/
def H5 (M : Mont) (p : HPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (M.mm Public.aY aT aChunk) s (H6 p)

/-- Before `qInv`'s mask. -/
def H4 (M : Mont) (p : HPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (seqs (maskArr aChunk)) s (H5 M p)

/-- Before `qInv`'s load. -/
def H3 (M : Mont) (p : HPub) (s : State) : Prop :=
  LPre aChunk sQinv sPlen p.q s ∧ WP isa (seqs (loadArr aChunk sQinv sPlen)) s (H4 M p)

/-- Before `T := m_p - m_q`. -/
def H2 (M : Mont) (p : HPub) (s : State) : Prop :=
  SmPre p.pw s ∧ WP isa (seqs (subModArr aT Public.aY aXc)) s (H3 M p)

/-- Before `m_q R_p` into `p`'s `X_c`. -/
def H1 (M : Mont) (p : HPub) (s : State) : Prop :=
  RPre Public.aX p.x s ∧ WP isa (seqs (redc M.mm Public.aX)) s (H2 M p)

/-- Before `hSteps`. -/
def H0 (M : Mont) (p : HPub) (s : State) : Prop :=
  s.gpr .x0 = p.B ∧ WP isa (.block [ldh .x0 sWsP]) s (H1 M p)

/-- `hSteps` after its `redc` is constant time. -/
theorem h2_ct (M : Mont) (hL : LoadCT aChunk sQinv sPlen) :
    RelCT isa (Two (H2 M)) (seqs (subModArr aT Public.aY aXc ++ (loadArr aChunk sQinv sPlen ++ (maskArr aChunk ++
      [M.mm Public.aY aT aChunk, .block [leave]])))) fun _ _ => True := by
  refine ct_steps (by simp [subModArr]) (by simp [loadArr]) HPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    subModArr_ct ?_
  refine ct_steps (by simp [loadArr]) (by simp [maskArr]) HPub.q (fun _ _ h => h.1) (fun _ _ h => h.2) hL ?_
  refine ct_steps (by simp [maskArr]) (by simp) HPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (maskArr_ct (by decide) (by taint_decide)) ?_
  exact ct_step HPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2) (M.ct (by unfold MmUse; decide))
    (two_taint [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [show s₁.gpr .x0 = _ from h₁, h₂]) (by taint_decide))

/-- `hSteps` is constant time. -/
theorem h_ct (M : Mont) (hR : RedcCT M Public.aX) (hL : LoadCT aChunk sQinv sPlen) :
    RelCT isa (Two (H0 M)) (seqs (hSteps M.mm)) fun _ _ => True := by
  simp only [hSteps, List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [redc]) (ct_taint [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) (fun _ _ h => h.2) ?_)
  exact ct_steps (by simp [redc]) (by simp [subModArr]) HPub.x (fun _ _ h => h.1) (fun _ _ h => h.2) hR
    (h2_ct M hL)

/-- `hTail_ok`'s hypotheses give `H2`. -/
theorem h2_chain (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mx : BitVec 64} {X o wx : Nat}
    {qp : Addr} {qib : List Byte} {c : Bool}
    (hc : SubCtx s B Z o w wx mx) (hT : o + slot wx 8 + wsTab wx ≤ Z) (hX : XVals s B o wx mx X) (hX1 : 1 < X)
    (hw28 : w < 2 ^ 28) (hwx2 : 2 ≤ wx)
    (hwx : wx ≤ w) (hyl : wv s.mem (off B o) (slot wx Public.aY) wx < X)
    (hlt : wv s.mem (off B o) (slot wx aXc) wx < X) (hmask : word s.mem (off B o) (8 * sMaskX) = mask c)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : word s.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length)
    (hqs : Src s B Z qp qib) (hq1 : 1 ≤ qib.length) (hq2 : qib.length < 2 ^ 31) (hqw : (qib.length + 7) / 8 ≤ wx)
    (hqi : c = true → Spec.Rsa.os2ip qib < X) : H2 M ⟨B, Z, w, o, wx, qp, qib.length⟩ s := by
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  have hlo := hc.lo
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  obtain ho64 : o < 2 ^ 64 := by omega_arith
  obtain hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  -- `T = (m_p - m_q) R_p mod p`.
  refine ⟨⟨⟨mx, hc.good, Nat.le_refl _⟩, hwx2, show wx < 2 ^ 31 by omega_arith⟩,
    WP.mono (subModArr_ok hc.good.scr hc.x0 hc.hdr (Nat.le_refl _) hwx2 (by omega_arith)
    (o := aT) (a := Public.aY) (b := aXc) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hX.n]; exact hyl) (by rw [hX.n]; exact hlt))
    fun s₃ ⟨_, ha₃, k₃⟩ => ?_⟩
  obtain ⟨hc₃, hX₃, fx₃⟩ := hc.of_arrays hX ha₃ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> decide) k₃.wr (k₃.gpr .x0 (by decide)) (by omega_arith)
  obtain hb₃ : ∀ d, d + 8 ≤ o → word s₃.mem B d = word s.mem B d := fun d hd => fx₃.x_below hd ho64
  obtain i03 : InScr B Z s.mem s₃.mem :=
    InScr.of_frm fx₃ fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega_arith
  obtain hM₃ : word s₃.mem (off B o) (8 * sMaskX) = mask c := by
    rw [ha₃.hslot (by decide)]; exact hmask
  -- `qInv`, masked.
  obtain a1 : word s₃.mem B (8 * sQinv) = qp := by rw [hb₃ _ (by unfold sQinv sFn; omega_arith)]; exact hqp
  obtain a2 : word s₃.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length := by
    rw [hb₃ _ (by unfold sPlen sFn; omega_arith)]; exact hql
  obtain a3 : Src s₃ B Z qp qib := hqs.congrK i03 k₃
  refine ⟨⟨mx, qib, hc₃, hwx2, hwx, show w < 2 ^ 30 by omega_arith, by decide, by decide, by decide, a1, a2, rfl, a3,
      hq1, hq2, hqw⟩,
    WP.mono (primeLoad_ok hc₃ hwx2 hwx (by omega_arith) (j := aChunk) (by decide) (sp := sQinv) (sl := sPlen)
      (by decide) (by decide) a1 a2 a3 hq1 hq2 hqw) fun s₄ ⟨hc₄, hq₄, ho₄, k₄⟩ => ?_⟩
  obtain hz₄ : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := by have := hc₄.good.scr.nowrap; omega_arith
  obtain hX₄ := hX₃.of_outside ho₄ (by decide) (by decide) (by decide) (Nat.le_refl _) hz₄
  obtain hM₄ : word s₄.mem (off B o) (8 * sMaskX) = mask c := by
    rw [ho₄.word (Or.inl (by have := hdr_lt_slot wx aChunk (show sMaskX < 32 by decide); omega_arith))
      (by unfold sMaskX sFn; omega_arith)]; exact hM₃
  refine ⟨⟨mx, hc₄.good, Nat.le_refl _⟩, WP.mono (maskArr_ok hc₄.good (Nat.le_refl _) (by omega_arith) (by omega_arith)
    (j := aChunk) (by decide) hM₄) fun s₅ ⟨_, hq₅, ho₅, _, k₅⟩ => ?_⟩
  obtain ho₅' : Outside (off B o) (slot wx aChunk) (8 * (wx + 2)) s₄.mem s₅.mem :=
    ho₅.mono (Nat.le_refl _) (by omega_arith)
  obtain hc₅ := hc₄.of_frm (rs := [(slot wx aChunk, 8 * (wx + 2))]) (Frm.of_outside ho₅' (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_le (w := wx) (show aChunk < 8 by decide)
    have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
    simp only; omega_arith) k₅.wr (k₅.gpr .x0 (by decide))
  obtain hX₅ := hX₄.of_outside ho₅' (by decide) (by decide) (by decide) (Nat.le_refl _) hz₄
  obtain hch : wv s₅.mem (off B o) (slot wx aChunk) wx < X := by
    rw [hq₅, hq₄]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte]; omega_arith
    · simp only [↓reduceIte]; exact hqi rfl
  -- `h = T qInv R_p⁻¹`.
  exact ⟨⟨mx, hc₅.good, Nat.le_refl _⟩, WP.mono (M.mm_ok (o := Public.aY) (a := aT) (b := aChunk) hc₅.good
    (Nat.le_refl _) hwx2 (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hX₅.inv (by rw [hX₅.n]; exact hch)) fun _ h₆ => h₆.1.x0⟩


/-- `hPart_ok`'s hypotheses give `H0`. -/
theorem h_chain (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {X o wx : Nat}
    {qp : Addr} {qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hslv : word s.mem B (8 * sWsP) = off B o) (hws : WsAt s.mem B o wx mx)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X)
    (hyl : wv s.mem (off B o) (slot wx Public.aY) wx < X)
    (hmask : word s.mem (off B o) (8 * sMaskX) = mask c)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : word s.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length)
    (hqs : Src s B Z qp qib) (hq1 : 1 ≤ qib.length) (hq2 : qib.length < 2 ^ 31) (hqw : (qib.length + 7) / 8 ≤ wx)
    (hqi : c = true → Spec.Rsa.os2ip qib < X) : H0 M ⟨B, Z, w, o, wx, qp, qib.length⟩ s := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  obtain ho64 : o < 2 ^ 64 := by omega_arith
  obtain hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  obtain l1 := hs.ld (show 8 * sWsP + 8 ≤ Z by have := hdr_lt_slot w 8 (show sWsP < 32 by decide); omega_arith)
  refine ⟨hg.x0, WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = off B o ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (show sWsP < 32 by decide), l1, hslv]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ?_⟩
  obtain hc₁ : SubCtx s₁ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k₁.wr) (by rw [hm₁]; exact hg.hdr) (by rw [hm₁]; exact hws) hdi₁ hlo (by have := tabBytes_le_wsTab wx; omega_arith)
  obtain hX₁ : XVals s₁ B o wx mx X := ⟨by rw [hm₁]; exact hX.n, by rw [hm₁]; exact hX.inv, by rw [hm₁]; exact hX.one⟩
  -- `m_q R_p` into `p`'s `X_c`.
  refine ⟨⟨mx, X, hc₁, hX₁, hwx2, hwx, show w < 2 ^ 30 by omega_arith, hX1, by decide⟩,
    WP.mono (redc_ok M hc₁ hX₁ hwx2 hwx (by omega_arith) hX1 (j := Public.aX) (by decide))
    fun s₂ ⟨hc₂, hX₂, hlt₂, _, f₂, k₂⟩ => ?_⟩
  obtain fx₂ : Frm B [xRange o wx] s₁.mem s₂.mem := f₂.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  obtain hY₂ : wv s₂.mem (off B o) (slot wx Public.aY) wx = wv s.mem (off B o) (slot wx Public.aY) wx := by
    obtain rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have := slot_le (w := wx) (show Public.aY < 8 by decide)
    have := hc₁.good.scr.nowrap
    rw [f₂.wv_eq (fun r hr => by have := rY r hr; omega_arith) (by omega_arith), hm₁]
  obtain hM₂ : word s₂.mem (off B o) (8 * sMaskX) = mask c := by
    rw [f₂.word_eq (fun r hr => by
      simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hdr_lt_slot wx Public.aAcc (show 31 < 32 by decide)
      have := hdr_lt_slot wx Public.aTmp (show 31 < 32 by decide)
      have := hdr_lt_slot wx aXc (show 31 < 32 by decide)
      have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
      have := hdr_lt_slot wx aT (show 31 < 32 by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sMaskX, sSrc, sRem, sFn] <;> omega_arith)
      (by unfold sMaskX sFn; omega_arith), hm₁]
    exact hmask
  obtain hb₂ : ∀ d, d + 8 ≤ o → word s₂.mem B d = word s.mem B d := fun d hd => by
    rw [fx₂.x_below hd ho64, hm₁]
  obtain i02 : InScr B Z s.mem s₂.mem := by
    have f := fx₂
    rw [hm₁] at f
    exact InScr.of_frm f fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega_arith
  exact h2_chain M hc₂ (by omega_arith) hX₂ hX1 hw28 hwx2 hwx (by rw [hY₂]; exact hyl) hlt₂ hM₂
    (by rw [hb₂ _ (by unfold sQinv sFn; omega_arith)]; exact hqp) (by rw [hb₂ _ (by unfold sPlen sFn; omega_arith)]; exact hql)
    (hqs.congrK i02 (k₁.trans k₂)) hq1 hq2 hqw hqi

end VG.Proof.Bignum.AArch64

end

end

/-!
# RSA with the CRT on AArch64: constant time, `p`'s phase

`pPhase` is constant time (`pPhase_ct`) given its pieces' claims: before
each piece, a predicate (`PO0` … `PO4`, then `hSteps`' `H0`) carries the
piece's hypotheses and what correctness gives after it; `o0_of` proves the
first from `PPre`, as `pPhase_ok` runs the pieces.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- The modulus' workspace. -/
abbrev PPhasePub.nw (p : PPhasePub) : Ws := ⟨p.ph.B, p.ph.Z, p.ph.w⟩

/-- The public data of the phase's first part. -/
abbrev PPhasePub.u (p : PPhasePub) : UPub := ⟨p.ph.B, p.ph.Z, p.ph.w, p.ph.minv, p.ph.N, p.ph.o, p.ph.wx⟩

/-- The public data of `m_q G mod n`. -/
abbrev PPhasePub.mq (p : PPhasePub) : MqPub := ⟨p.ph.B, p.ph.Z, p.ph.w, p.oq, p.wq⟩

/-- The public data of the exponentiation. -/
abbrev PPhasePub.pw (p : PPhasePub) : BPub := ⟨⟨p.ph.B, p.ph.Z, p.ph.o, p.ph.w, p.ph.wx⟩, p.ph.ep, p.ph.len⟩

/-- The public data of `h`. -/
abbrev PPhasePub.h (p : PPhasePub) : HPub := ⟨p.ph.B, p.ph.Z, p.ph.w, p.ph.o, p.ph.wx, p.qp, p.ph.len⟩

/-- Before the way back to the modulus' workspace. -/
def PO4 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  s.gpr .x0 = off p.ph.B p.ph.o ∧ WP isa (.block [leave]) s (H0 M p.h)

/-- Before the exponentiation. -/
def PO3 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  PwPre sWsP sDp sPlen p.pw s ∧ WP isa (seqs (powSteps M.mm sWsP sDp sPlen)) s (PO4 M p)

/-- Before `c G mod N`. -/
def PO2 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  GoodW p.nw s ∧ WP isa (M.mm Public.aY Public.aXm Public.aY) s (PO3 M p)

/-- Before `m_q G mod N`. -/
def PO1 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  Mq0 M p.mq s ∧ WP isa (seqs (mqSteps M.mm)) s (PO2 M p)

/-- Before `pPhase`. -/
def PO0 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  UPre sWsP p.u s ∧ WP isa (seqs (unitSteps M.mm sWsP)) s (PO1 M p)

/-- What `o3_of` gives, for any `PO3`: `o0_gen` takes it, so that the phase
with another exponentiation (5-bit windows) is proven once. -/
def O3Ok (P3 : PPhasePub → State → Prop) : Prop :=
  ∀ {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64}
    {N X C o wx oq wq : Nat} {ep qp : Addr} {eb qib : List Byte} {c : Bool}
    (_hg : Good s B Z w minv) (_hw28 : w < 2 ^ 28) (_hlo : slot w 8 ≤ o) (_hhi : o + slot wx 8 + wsTab wx ≤ Z)
    (_hwx2 : 2 ≤ wx) (_hwx : wx ≤ w) (_hslv : word s.mem B (8 * sWsP) = off B o) (_hws : WsAt s.mem B o wx mx)
    (_hX : XVals s B o wx mx X) (_hX1 : 1 < X) (_hXodd : X % 2 = 1)
    (_hcg : wv s.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N)
    (_hpl : wv s.mem (off B o) (slot wx Public.aY) wx < X)
    (_hpy : X ∣ N → wv s.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X)
    (_hep : word s.mem B (8 * sDp) = ep) (_hel : word s.mem B (8 * sPlen) = BitVec.ofNat 64 eb.length)
    (_hL1 : 1 ≤ eb.length) (_hL2 : eb.length ≤ 1024) (_he : Src s B Z ep eb)
    (_hmask : word s.mem (off B o) (8 * sMaskX) = mask c)
    (_hqp : word s.mem B (8 * sQinv) = qp) (_hql : qib.length = eb.length) (_hqs : Src s B Z qp qib)
    (_hqw : (qib.length + 7) / 8 ≤ wx) (_hqi : c = true → Spec.Rsa.os2ip qib < X),
    P3 ⟨⟨B, Z, w, minv, N, o, wx, ep, eb.length⟩, oq, wq, qp⟩ s

/-- From before the exponentiation: `PO3`, as `pPhase_ok` runs the rest. -/
theorem o3_of (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64}
    {N X C o wx oq wq : Nat} {ep qp : Addr} {eb qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hslv : word s.mem B (8 * sWsP) = off B o) (hws : WsAt s.mem B o wx mx)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hcg : wv s.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N)
    (hpl : wv s.mem (off B o) (slot wx Public.aY) wx < X)
    (hpy : X ∣ N → wv s.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X)
    (hep : word s.mem B (8 * sDp) = ep) (hel : word s.mem B (8 * sPlen) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb)
    (hmask : word s.mem (off B o) (8 * sMaskX) = mask c)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : qib.length = eb.length) (hqs : Src s B Z qp qib)
    (hqw : (qib.length + 7) / 8 ≤ wx) (hqi : c = true → Spec.Rsa.os2ip qib < X) :
    PO3 M ⟨⟨B, Z, w, minv, N, o, wx, ep, eb.length⟩, oq, wq, qp⟩ s := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  obtain ho64 : o < 2 ^ 64 := by omega_arith
  -- `c^dP R_p mod p`.
  refine ⟨⟨minv, mx, N, X, C, eb, hg, hw28, hlo, hhi, hwx2, hwx, by decide, hslv, hws, hX, hX1, hXodd, hcg, hpl,
      hpy, by decide, by decide, hep, hel, rfl, hL1, hL2, he⟩,
    WP.mono (powPhase_ok M hg hw28 hlo hhi hwx2 hwx (sl := sWsP) (by decide) hslv hws hX hX1 hXodd hcg hpl hpy
      (sd := sDp) (slen := sPlen) (by decide) (by decide) hep hel hL1 hL2 he)
      fun s₄ ⟨hc₄, hX₄, hlt₄, _, hM₄, fx₄, k₄⟩ => ?_⟩
  -- Back to the modulus'.
  refine ⟨hc₄.x0, WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = s₄.mem)
    (by brun [leave, hc₄.x0, hdr_enc (show sLink < 32 by decide), hc₄.ld' (show sLink < 32 by decide), hc₄.link'])
    (by decide) (by decide) (by decide +kernel)) fun s₅ ⟨⟨hdi₅, hm₅⟩, k₅⟩ => ?_⟩
  obtain fx₅ : Frm B [xRange o wx] s.mem s₅.mem := by rw [hm₅]; exact fx₄
  obtain k05 := k₄.trans k₅
  obtain hb₅ : ∀ d, d + 8 ≤ o → word s₅.mem B d = word s.mem B d := fun d hd => fx₅.x_below hd ho64
  obtain hg₅ : Good s₅ B Z w minv := ⟨hs.congr k05.wr, hdi₅, ⟨(hb₅ _ (by unfold sW; omega_arith)).trans hg.hdr.hw,
    (hb₅ _ (by unfold sMinv; omega_arith)).trans hg.hdr.hminv,
    fun j hj => (hb₅ _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega_arith); omega_arith)).trans
      (hg.hdr.harr j hj)⟩⟩
  obtain hX₅ : XVals s₅ B o wx mx X := ⟨by rw [hm₅]; exact hX₄.n, by rw [hm₅]; exact hX₄.inv, by rw [hm₅]; exact hX₄.one⟩
  obtain i05 : InScr B Z s.mem s₅.mem := InScr.of_frm fx₅ fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [xRange]; omega_arith
  -- `h`.
  obtain a1 : word s₅.mem B (8 * sWsP) = off B o := by rw [hb₅ _ (by unfold sWsP sFn; omega_arith)]; exact hslv
  obtain a2 : WsAt s₅.mem B o wx mx := by rw [hm₅]; exact hc₄.ws
  obtain a3 : wv s₅.mem (off B o) (slot wx Public.aY) wx < X := by rw [hm₅]; exact hlt₄
  obtain a5 : word s₅.mem (off B o) (8 * sMaskX) = mask c := by rw [hm₅, hM₄]; exact hmask
  obtain a6 : word s₅.mem B (8 * sQinv) = qp := by rw [hb₅ _ (by unfold sQinv sFn; omega_arith)]; exact hqp
  obtain a7 : word s₅.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length := by
    rw [hb₅ _ (by unfold sPlen sFn; omega_arith), hql]; exact hel
  have := h_chain M hg₅ hw28 hlo hhi hwx2 hwx a1 a2 hX₅ hX1 a3 a5 a6 a7 (hqs.congrK i05 k05) (by omega_arith)
    (by omega_arith) hqw hqi
  rw [hql] at this
  exact this

/-- `pPhase_ok`'s hypotheses give `PO0`. -/
theorem o0_gen (M : Mont) (P3 : PPhasePub → State → Prop) (ho3 : O3Ok P3) {p : PPhasePub} {s : State}
    (h : PPre p s) :
    UPre sWsP p.u s ∧ WP isa (seqs (unitSteps M.mm sWsP)) s fun s =>
      Mq0 M p.mq s ∧ WP isa (seqs (mqSteps M.mm)) s fun s =>
        GoodW p.nw s ∧ WP isa (M.mm Public.aY Public.aXm Public.aY) s (P3 p) := by
  obtain ⟨⟨B, Z, w, minv, N, o, wx, ep, len⟩, oq, wq, qp⟩ := p
  dsimp only [PPre] at h
  obtain ⟨mx, mq, X, C, eb, qib, c, h⟩ := h
  sig_split h
  rename_i hg hw hw28 hlo hhi hqhi hwx2 hwx hwq hwq' hslv hws hslq hwsq hN hodd hN1 hXm hX hX1 hXodd
    hmask hc hep hel _ob1 hL1 hL2 he hqp hql hqs hqw
  obtain rfl := _ob1
  have hqi := h
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  obtain hQ8 : 256 ≤ slot wq 8 := by unfold slot hdrBytes; omega_arith
  obtain hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  obtain hhi' : o + slot wx 8 + wsTab wx ≤ Z := by omega_arith
  obtain hsub : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r ∈ pRanges w ++ [xRange o wx]) → ∀ {m m' : Mem},
      Frm B rs m m' → Frm B (pRanges w ++ [xRange o wx]) m m' := fun h _ _ f => f.mono h
  obtain sgx : ∀ r ∈ gRanges w ++ [xRange o wx], r ∈ pRanges w ++ [xRange o wx] := fun r hr =>
    (List.mem_append.mp hr).elim (fun h => List.mem_append_left _ (List.mem_append_left _ h))
      (fun h => List.mem_append_right _ h)
  obtain sp : ∀ r ∈ pRanges w, r ∈ pRanges w ++ [xRange o wx] := fun r hr => List.mem_append_left _ hr
  obtain sg : ∀ r ∈ gRanges w, r ∈ pRanges w ++ [xRange o wx] := fun r hr =>
    List.mem_append_left _ (List.mem_append_left _ hr)
  obtain hqh : ∀ {m m' : Mem}, Frm B (pRanges w ++ [xRange o wx]) m m' → ∀ i < 32,
      word m' (off B oq) (8 * i) = word m (off B oq) (8 * i) := fun f i hi => by
    rw [word_off, word_off]; exact f.px_above hlo (by omega_arith) (by omega_arith)
  -- `R_p mod p`.
  refine ⟨⟨mx, X, hg, hw, hw28, hlo, hhi', hwx2, hwx, by decide, by decide, by decide, hslv, hws, hN, hodd, hN1,
      hX, hX1, hXodd⟩,
    WP.mono (unitPhase_ok M hg hw hw28 hlo hhi' hwx2 hwx (sl := sWsP) (by decide) (by decide) (by decide) hslv
      hws hN hodd hN1 hX hX1 hXodd) fun s₁ ⟨hg₁, hws₁, hX₁, hlt₁, hG₁, hpl₁, hpy₁, hM₁, f₁, k₁⟩ => ?_⟩
  obtain f₁' := hsub sgx f₁
  obtain hN₁ := hN.of_frm f₁ hlo hz (by omega_arith)
  obtain hslq₁ : word s₁.mem B (8 * sWsQ) = off B oq := by
    rw [f₁'.px_hdr hlo (by decide) (by decide) (by decide)]; exact hslq
  obtain hwsq₁ : WsAt s₁.mem B oq wq mq := hwsq.of_words fun i hi => hqh f₁' i (by omega_arith)
  -- `m_q G mod N`.
  refine ⟨mq_chain M hg₁ hw hw28 hN₁ hslq₁ hwsq₁ (show slot w 8 ≤ oq by omega_arith) hqhi hwq hwq',
    WP.mono (mqPart_ok M hg₁ hw hw28 hN₁ hodd hlt₁ hG₁ hslq₁ hwsq₁ (show slot w 8 ≤ oq by omega_arith) hqhi hwq hwq')
    fun s₂ ⟨hg₂, _, hmq₂, hY₂, f₂, k₂⟩ => ?_⟩
  obtain f₂' := hsub sp f₂
  obtain f₀₂ := f₁'.trans f₂'
  obtain hN₂ : NVals s₂ B w minv N := by
    exact ⟨by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.n,
      by rw [f₂'.px_word hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.inv,
      by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.r2,
      by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.r2lt,
      by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.one⟩
  -- `c G mod N`.
  refine ⟨⟨minv, hg₂, show slot w 8 ≤ Z by omega_arith⟩,
    WP.mono (mmY_ok M hg₂ (by omega_arith) (by omega_arith) (by omega_arith) (a := Public.aXm) (by decide) (by decide)
      (by decide) hN₂ (by rw [hY₂]; exact hlt₁)) fun s₃ ⟨hg₃, _, hm₃, f₃, k₃⟩ => ?_⟩
  obtain f₃' := hsub sg f₃
  obtain f₀₃ := f₀₂.trans f₃'
  obtain hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  obtain hXm₂ : wv s₂.mem B (slot w Public.aXm) w = wv s.mem B (slot w Public.aXm) w :=
    f₀₂.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain hcg : wv s₃.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₃, Nat.mul_mod, hXm₂, hXm, hY₂, hG₁, ← Nat.mul_mod]
    congr 1; ac_rfl
  obtain hpo : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ d,
      o ≤ d → d + 8 ≤ 2 ^ 64 → word m' B d = word m B d := fun f hrs d hd hd' =>
    f.word_eq (fun r hr => Or.inr (by have := pRanges_le w r (hrs r hr); omega_arith)) hd'
  obtain hpw : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ i < 32,
      word m' (off B o) (8 * i) = word m (off B o) (8 * i) := fun f hrs i hi => by
    rw [word_off, word_off]; exact hpo f hrs _ (by omega_arith) (by omega_arith)
  obtain sg' : ∀ r ∈ gRanges w, r ∈ pRanges w := fun r hr => List.mem_append_left _ hr
  obtain hpv : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ d k,
      d + 8 * k ≤ slot wx 8 → wv m' (off B o) d k = wv m (off B o) d k := fun f hrs d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpo f hrs _ (by omega_arith) (by omega_arith)
  obtain hY8 := slot_le (w := wx) (show Public.aY < 8 by decide)
  obtain hpY₃ : wv s₃.mem (off B o) (slot wx Public.aY) wx = wv s₁.mem (off B o) (slot wx Public.aY) wx := by
    rw [hpv f₃ sg' _ _ (by omega_arith), hpv f₂ (fun r h => h) _ _ (by omega_arith)]
  obtain hws₃ : WsAt s₃.mem B o wx mx := hws₁.of_words fun i hi => by
    rw [hpw f₃ sg' i (by omega_arith), hpw f₂ (fun r h => h) i (by omega_arith)]
  obtain hX₃ : XVals s₃ B o wx mx X :=
    (hX₁.of_below f₂ (fun r hr => Nat.le_trans (pRanges_le w r hr) hlo) (by omega_arith)).of_below f₃
      (fun r hr => Nat.le_trans (pRanges_le w r (sg' r hr)) hlo) (by omega_arith)
  obtain i03 : InScr B Z s.mem s₃.mem := InScr.of_frm f₀₃ fun r hr => by have := pxR_bound hlo r hr; omega_arith
  obtain k03 := (k₁.trans k₂).trans k₃
  obtain hM₃ : word s₃.mem (off B o) (8 * sMaskX) = mask c := by
    rw [hpw f₃ sg' _ (by decide), hpw f₂ (fun r h => h) _ (by decide), hM₁]; exact hmask
  exact ho3 hg₃ hw28 hlo hhi' hwx2 hwx (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hslv)
    hws₃ hX₃ hX1 hXodd hcg (by rw [hpY₃]; exact hpl₁) (fun hd => by rw [hpY₃]; exact hpy₁ hd)
    (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hep)
    (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hel) hL1 hL2 (he.congrK i03 k03) hM₃
    (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hqp) hql (hqs.congrK i03 k03) hqw hqi

theorem o0_of (M : Mont) {p : PPhasePub} {s : State} (h : PPre p s) : PO0 M p s :=
  o0_gen M (PO3 M) (@o3_of M) h

/-- `p`'s phase is constant time, given its pieces' claims. -/
theorem pPhase_ct (M : Mont) (hU : UnitCT M sWsP) (hP : PowCT M sWsP sDp sPlen) (hRX : RedcCT M Public.aX)
    (hL : LoadCT aChunk sQinv sPlen) : PPhaseCT M := by
  unfold PPhaseCT
  refine two_map id (fun _ _ h => o0_of M h) ?_
  rw [pPhase_eq]
  refine ct_steps (by simp [unitSteps]) (by simp [mqSteps]) PPhasePub.u (fun _ _ h => h.1) (fun _ _ h => h.2)
    hU ?_
  refine ct_steps (by simp [mqSteps]) (by simp) PPhasePub.mq (fun _ _ h => h.1) (fun _ _ h => h.2) (mq_ct M) ?_
  refine ct_steps (by simp) (by simp [powSteps]) PPhasePub.nw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (M.ct (by unfold MmUse; decide)) ?_
  refine ct_steps (by simp [powSteps]) (by simp) PPhasePub.pw (fun _ _ h => h.1) (fun _ _ h => h.2) hP ?_
  refine RelCT.seqs_append (by simp) (by simp [hSteps]) (ct_taint [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) (fun _ _ h => h.2) ?_)
  exact two_map PPhasePub.h (fun _ _ h => h) (h_ct M hRX hL)

end VG.Proof.Bignum.AArch64
