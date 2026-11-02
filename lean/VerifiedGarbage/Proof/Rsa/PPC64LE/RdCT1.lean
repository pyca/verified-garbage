module

import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCorrect
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdContract
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RdContract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCorrect
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCheck
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvEntry
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcFrame
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCheck
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvEntry
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.KcFrame
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvEntry
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCheck
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvLoads
public import Aesop.BuiltinRules
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvLoads

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: constant time of the entry and the check of `n`

As `RvCT1.lean` for `vg_rsa_recover_primes`, whose entry and check it shares,
with the public data of `rdP` (`rdPub`: the argument registers, the stack
arguments and the bytes of `n` and `e`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Recover (entry nCheck)

/-- The public data. -/
structure RdD where
  regs : List (BitVec 64)
  stk : List (BitVec 64)
  ne : List Nat

def rdPub (s : State) : RdD :=
  ⟨argRegs.map s.gpr, (List.range 4).map (PPC64LE.stackArg s), (nB s ++ eB s).map (·.toNat)⟩

/-- A state the contract allows, with the public data `d`. -/
def D0 (d : RdD) (s : State) : Prop := rdP.pre s ∧ rdPub s = d

theorem D0.reg {d : RdD} {s₁ s₂ : State} (h₁ : D0 d s₁) (h₂ : D0 d s₂) {r : Reg} (hr : r ∈ argRegs) :
    s₁.gpr r = s₂.gpr r :=
  List.map_inj_left.mp ((congrArg RdD.regs h₁.2).trans (congrArg RdD.regs h₂.2).symm) r hr

theorem D0.arg {d : RdD} {s₁ s₂ : State} (h₁ : D0 d s₁) (h₂ : D0 d s₂) {i : Nat} (hi : i < 4) :
    PPC64LE.stackArg s₁ i = PPC64LE.stackArg s₂ i :=
  List.map_inj_left.mp ((congrArg RdD.stk h₁.2).trans (congrArg RdD.stk h₂.2).symm) i (List.mem_range.mpr hi)

theorem D0.k {d : RdD} {s₁ s₂ : State} (h₁ : D0 d s₁) (h₂ : D0 d s₂) : kK s₁ = kK s₂ := by
  rw [kK, kK, h₁.reg h₂ (r := .r8) (by decide)]

theorem bytes_of_map {a b a' b' : List Byte} (h : (a ++ b).map (·.toNat) = (a' ++ b').map (·.toNat))
    (hl : a.length = a'.length) : a = a' ∧ b = b' :=
  List.append_inj ((List.map_inj_right fun _ _ e => BitVec.eq_of_toNat_eq e).mp h) hl

theorem D0.bytes {d : RdD} {s₁ s₂ : State} (h₁ : D0 d s₁) (h₂ : D0 d s₂) : nB s₁ = nB s₂ ∧ eB s₁ = eB s₂ :=
  bytes_of_map ((congrArg RdD.ne h₁.2).trans (congrArg RdD.ne h₂.2).symm)
    (by rw [VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.bytesAt_length, h₁.reg h₂ (r := .r8) (by decide)])

theorem D0.nV {d : RdD} {s₁ s₂ : State} (h₁ : D0 d s₁) (h₂ : D0 d s₂) : nV s₁ = nV s₂ :=
  congrArg Spec.Rsa.os2ip (h₁.bytes h₂).1

theorem D0.eV {d : RdD} {s₁ s₂ : State} (h₁ : D0 d s₁) (h₂ : D0 d s₂) : eV s₁ = eV s₂ :=
  congrArg Spec.Rsa.os2ip (h₁.bytes h₂).2

theorem D0.cB {d : RdD} {s₁ s₂ : State} (h₁ : D0 d s₁) (h₂ : D0 d s₂) : cB s₁ = cB s₂ := by
  show 8 * ((s₁.gpr .r10).toNat + (PPC64LE.stackArg s₁ 1).toNat) = 8 * ((s₂.gpr .r10).toNat + (PPC64LE.stackArg s₂ 1).toNat)
  rw [h₁.reg h₂ (r := .r10) (by decide), h₁.arg h₂ (i := 1) (by decide)]

/-! ## The entry -/

theorem rd_entry_split : entry = VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 2 ++ entry.drop 2 := rfl

/-- After the entry's first load. -/
def D1 (d : RdD) (t : State) : Prop :=
  ∃ s0, D0 d s0 ∧ Keep [.r11] s0 t ∧ t.gpr .r11 = PPC64LE.stackArg s0 2 ∧
    WP isa (.block (entry.drop 2)) t (REnt s0)

/-- After the entry. -/
def D2 (d : RdD) (t : State) : Prop := ∃ s0, D0 d s0 ∧ REnt s0 t

theorem pins_nil {α : Type} {Φ : α → State → Prop} : Pins Φ [] := by
  intro _ _ _ _ _ r hr; simp at hr

theorem pins_D1 : Pins D1 [.r3, .r5, .r7, .r8, .r9, .r10, .r11] := by
  rintro d s₁ s₂ ⟨a, ha, k₁, a11, -⟩ ⟨b, hb, k₂, b11, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (rw [a11, b11]; exact ha.arg hb (by decide))
    | (rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide)]; exact ha.reg hb (by decide))

theorem pins_D2 : Pins D2 [.r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31] := by
  rintro d s₁ s₂ ⟨a, ha, e₁⟩ ⟨b, hb, e₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e₁.args.r21, e₂.args.r21]; exact ha.reg hb (by decide)
  · rw [e₁.args.r22, e₂.args.r22]; exact ha.arg hb (by decide)
  · rw [e₁.args.r23, e₂.args.r23]; exact ha.reg hb (by decide)
  · rw [e₁.args.r24, e₂.args.r24]; exact ha.reg hb (by decide)
  · rw [e₁.args.r25, e₂.args.r25]; exact ha.reg hb (by decide)
  · rw [e₁.args.r26, e₂.args.r26]; exact ha.reg hb (by decide)
  · rw [e₁.args.r27, e₂.args.r27]; exact ha.reg hb (by decide)
  · rw [e₁.args.r28, e₂.args.r28]; exact ha.arg hb (by decide)
  · rw [e₁.r29, e₂.r29, ha.k hb]
  · rw [e₁.r30, e₂.r30, ha.k hb]
  · rw [e₁.base.r31, e₂.base.r31]; exact ha.arg hb (by decide)

theorem D1_of {d : RdD} {s : State} (hs : D0 d s) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 2)) s (D1 d) := by
  have hp := rv_kpre (rdP_pre hs.1)
  have hw := entry_ok (rdP_pre hs.1)
  rw [rd_entry_split, WP.block_append_iff] at hw
  have h11 : WP isa (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 2)) s fun t =>
      t.gpr .r11 = PPC64LE.stackArg s 2 ∧ Keep [.r11] s t := by
    refine WP.keep [.r11] ?_ (by decide)
    rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 2)]
    refine hp.stackArg_ok rfl rfl (r := .r11) (by decide) (by decide) (by decide) (WP.block_nil ?_)
    simp only [State.write, ↓reduceIte]
  exact WP.mono (WP.and hw h11) fun t ⟨w, e, k⟩ => ⟨s, hs, k, e, w⟩

theorem rd_entry_ct : RelCT isa (Two D0) (.block entry) (Two D2) := by
  rw [rd_entry_split]
  refine RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_nil (by taint_decide)) fun _ _ h => D1_of h)
    (two_post (two_taint _ pins_D1 (by taint_decide)) fun _ _ ⟨s0, hs, _, _, hw⟩ =>
      WP.mono hw fun _ h => ⟨s0, hs, h⟩))

/-! ## The check of `n` -/

/-- After `check1`. -/
def D3 (d : RdD) (u : State) : Prop :=
  ∃ s0 e, D0 d s0 ∧ REnt s0 e ∧ NC1 s0 u ∧ u.mem = e.mem ∧ Keep ncRegs e u

/-- After `check2`. -/
def D4 (d : RdD) (u : State) : Prop :=
  ∃ s0, D0 d s0 ∧ REnt s0 u ∧ (u.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (nV s0) (kK s0) = true)

theorem pins_D3 : Pins D3 [.r10, .r11] := by
  rintro d s₁ s₂ ⟨a, _, ha, _, ⟨-, -, a10, -, a11⟩, -⟩ ⟨b, _, hb, _, ⟨-, -, b10, -, b11⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a10, b10, ha.k hb]
  · rw [a11, b11, show nB0 a = nB0 b from (ha.bytes hb).1]

theorem D3_of {d : RdD} {s : State} (h : D2 d s) :
    WP isa (.seq (.block [.addi .r9 .r24 0, .addi .r10 .r25 0]) (.block VG.Impl.Rsa.PPC64LE.CrtValues.check1)) s
      (D3 d) := by
  obtain ⟨s0, hs, e⟩ := h
  exact WP.mono (nc1_ok e.base e.args) fun u ⟨h1, m, k⟩ => ⟨s0, s, hs, e, h1, m, k⟩

theorem D4_of {d : RdD} {s : State} (h : D3 d s) : WP isa VG.Impl.Rsa.PPC64LE.CrtValues.check2 s (D4 d) := by
  obtain ⟨s0, e, hs, he, h1, m1, k1⟩ := h
  refine WP.mono (nc2_ok h1) fun u ⟨⟨b2, a2, hv⟩, m2, k2⟩ => ⟨s0, hs, ?_, ?_⟩
  · exact ⟨b2, a2, (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans he.r29),
      (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans he.r30), m2.trans (m1.trans he.mem),
      ((he.keep.trans k1).trans k2).mono⟩
  · rw [show Spec.Rsa.os2ip (nB0 s0) = nV s0 from rfl] at hv; exact hv

theorem rd_check_ct : RelCT isa (Two D2) nCheck (Two D4) := by
  unfold nCheck VG.Impl.Rsa.PPC64LE.CrtValues.check
  refine RelCT.assoc (RelCT.seq (two_post (two_taint _ pins_D2 (by taint_decide)) fun _ _ h => D3_of h)
    (two_post (two_taint _ pins_D3 (by taint_decide)) fun _ _ h => D4_of h))

end VG.Proof.Rsa.PPC64LE.RecDet
