module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Correct
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Correct
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Body
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Stores

/-!
# `vg_rsa_keygen_key` on PPC64LE: constant time

As `vg_rsa_crt_values`'s (`Proof/Rsa/PPC64LE/CvCT.lean`): the taint analysis
treats memory as secret, so the working space's address (a stack argument)
is secret to it, although it is public. Two runs are related by `Two`
(`MontCT.lean`) at each step, both satisfying the same predicate for the
same public data (`pubOf`: the argument registers and the stack arguments):
after the entry's first load the working space's address, after the entry
the pointers and lengths it keeps in `r14`–`r24` and the base in `r31`.
The body has no branch but its loops, whose counts come from those
registers, and the taint analysis checks it from them.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG.Proof.Rsa.PPC64LE (InvLaw)
open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Key (code entry body)
open VG.Impl.Rsa.PPC64LE.CrtValues (restore)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

/-- The public data: the argument registers and the stack arguments. -/
structure KD where
  regs : List (BitVec 64)
  stk : List (BitVec 64)

def pubOf (s : State) : KD := ⟨argRegs.map s.gpr, (List.range 10).map (PPC64LE.stackArg s)⟩

/-- A state the contract allows, with the public data `d`. -/
def KRel (d : KD) (s : State) : Prop := keyP.pre s ∧ pubOf s = d

theorem KRel.reg {d : KD} {s₁ s₂ : State} (h₁ : KRel d s₁) (h₂ : KRel d s₂) {r : Reg}
    (hr : r ∈ argRegs) : s₁.gpr r = s₂.gpr r :=
  List.map_inj_left.mp ((congrArg KD.regs h₁.2).trans (congrArg KD.regs h₂.2).symm) r hr

theorem KRel.arg {d : KD} {s₁ s₂ : State} (h₁ : KRel d s₁) (h₂ : KRel d s₂) {i : Nat} (hi : i < 10) :
    PPC64LE.stackArg s₁ i = PPC64LE.stackArg s₂ i :=
  List.map_inj_left.mp ((congrArg KD.stk h₁.2).trans (congrArg KD.stk h₂.2).symm) i (List.mem_range.mpr hi)

/-! ## The entry -/

/-- What the entry establishes. -/
def EP (s0 s : State) : Prop := Base s0 s ∧ Args s0 s ∧ Keep entryRegs s0 s

/-- The entry after its first load, the working space's address. -/
def E1 (d : KD) (t : State) : Prop :=
  ∃ s0, KRel d s0 ∧ t.gpr .r11 = PPC64LE.stackArg s0 8 ∧
    WP isa (.block (entry.drop 2)) t (EP s0)

/-- After the entry. -/
def E2 (d : KD) (t : State) : Prop := ∃ s0, KRel d s0 ∧ EP s0 t

theorem entry_split : entry = VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 8 ++ entry.drop 2 := rfl

theorem pins_nil {α : Type} {Φ : α → State → Prop} : Pins Φ [] := by
  intro _ _ _ _ _ r hr; simp at hr

theorem pins_E1 : Pins E1 [.r11] := by
  rintro d s₁ s₂ ⟨a, ha, h₁, -⟩ ⟨b, hb, h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h₁, h₂, ha.arg hb (by decide)]

theorem E1_of {d : KD} {s : State} (hs : KRel d s) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 8)) s (E1 d) := by
  have hw := entry_ok hs.1
  rw [entry_split, WP.block_append_iff] at hw
  have h11 : WP isa (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 8)) s fun t =>
      t.gpr .r11 = PPC64LE.stackArg s 8 := by
    rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 8)]
    refine stackArg_ok hs.1 rfl rfl (r := .r11) (by decide) (by decide) (WP.block_nil ?_)
    simp only [State.write, ↓reduceIte]
  exact WP.mono (WP.and hw h11) fun t ⟨w, e⟩ => ⟨s, hs, e, w⟩

theorem entry_ct : RelCT isa (Two KRel) (.block entry) (Two E2) := by
  rw [entry_split]
  refine RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_nil (by taint_decide)) fun _ _ h => E1_of h)
    (two_post (two_taint _ pins_E1 (by taint_decide)) fun _ _ ⟨s0, hs, _, hw⟩ =>
      WP.mono hw fun _ h => ⟨s0, hs, h⟩))

/-! ## The body -/

/-- After the body. -/
def D (d : KD) (t : State) : Prop := ∃ s0 m, KRel d s0 ∧ Fr s0 m t

/-- The registers the body starts from. -/
abbrev brRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r31]

theorem pins_BA {Φ : KD → State → Prop} (hΦ : ∀ d s, Φ d s → ∃ s0, KRel d s0 ∧ Base s0 s ∧ Args s0 s) :
    Pins Φ brRegs := by
  intro d s₁ s₂ h₁ h₂ r hr
  obtain ⟨a, ha, b₁, a₁⟩ := hΦ _ _ h₁
  obtain ⟨b, hb, b₂, a₂⟩ := hΦ _ _ h₂
  simp only [brRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a₁.r14, a₂.r14, ha.reg hb (by decide)]
  · rw [a₁.r15, a₂.r15, ha.reg hb (by decide)]
  · rw [a₁.r16, a₂.r16, ha.reg hb (by decide)]
  · rw [a₁.r17, a₂.r17, ha.reg hb (by decide)]
  · rw [a₁.r18, a₂.r18, ha.arg hb (by decide)]
  · rw [a₁.r19, a₂.r19, ha.arg hb (by decide)]
  · rw [a₁.r20, a₂.r20, ha.arg hb (by decide)]
  · rw [a₁.r21, a₂.r21, ha.arg hb (by decide)]
  · rw [a₁.r22, a₂.r22, ha.reg hb (by decide)]
  · rw [a₁.r23, a₂.r23, ha.arg hb (by decide)]
  · rw [a₁.r24, a₂.r24, ha.reg hb (by decide)]
  · rw [b₁.r31, b₂.r31]; exact ha.arg hb (by decide)

theorem pins_E2 : Pins E2 brRegs := pins_BA fun _ _ ⟨s0, hs, b, a, _⟩ => ⟨s0, hs, b, a⟩

/-! The inverse reloads the registers of the arguments from memory, so the
body is checked in four parts, pinning them again after each phase that
calls it (`body_cut_ok`). -/

/-- The registers a later part starts from: the arguments, the base, `w` and the stride. -/
abbrev cutRegs : List Reg := brRegs ++ [.r29, .r30]

theorem pins_cut {Φ : KD → State → Prop}
    (hΦ : ∀ d s, Φ d s → ∃ s0, KRel d s0 ∧ Base s0 s ∧ Args s0 s ∧ WReg s0 s) : Pins Φ cutRegs := by
  intro d s₁ s₂ h₁ h₂ r hr
  rw [List.mem_append] at hr
  rcases hr with hr | hr
  · exact pins_BA (fun d s h => let ⟨s0, hs, b, a, _⟩ := hΦ d s h; ⟨s0, hs, b, a⟩) d s₁ s₂ h₁ h₂ r hr
  obtain ⟨a, ha, -, -, w₁⟩ := hΦ _ _ h₁
  obtain ⟨b, hb, -, -, w₂⟩ := hΦ _ _ h₂
  have ek : kW a = kW b := by simp only [kW, kL]; rw [ha.reg hb (by decide)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [w₁.1, w₂.1, ek]
  · rw [w₁.2, w₂.2, ek]

/-- From `qInv` on. -/
def Q4 (d : KD) (t : State) : Prop :=
  (∃ s0, KRel d s0 ∧ Base s0 t ∧ Args s0 t ∧ WReg s0 t) ∧ WP isa (seqs bodyT) t (D d)

/-- After `d`. -/
def Q3 (d : KD) (t : State) : Prop :=
  (∃ s0, KRel d s0 ∧ Base s0 t ∧ Args s0 t ∧ WReg s0 t) ∧
    WP isa (seqs [VG.Impl.RsaKeyGen.PPC64LE.Key.smallPart, VG.Impl.RsaKeyGen.PPC64LE.Key.qinvPart]) t (Q4 d)

/-- After `L`. -/
def Q2 (d : KD) (t : State) : Prop :=
  (∃ s0, KRel d s0 ∧ Base s0 t ∧ Args s0 t ∧ WReg s0 t) ∧ WP isa VG.Impl.RsaKeyGen.PPC64LE.Key.dPart t (Q3 d)

theorem body_Q2 [InvLaw] {d : KD} {s : State} (h : E2 d s) : WP isa (seqs bodyL) s (Q2 d) := by
  obtain ⟨s0, hs, b, a, -⟩ := h
  exact WP.mono (body_cut_ok b a) fun _ ⟨b5, a5, e5, w5⟩ => ⟨⟨s0, hs, b5, a5, e5⟩, WP.mono w5 fun _ ⟨b6, a6, e6, w6⟩ =>
    ⟨⟨s0, hs, b6, a6, e6⟩, WP.mono w6 fun _ ⟨b8, a8, e8, w8⟩ =>
      ⟨⟨s0, hs, b8, a8, e8⟩, WP.mono w8 fun _ ⟨⟨m, _, _, f, _⟩, _⟩ => ⟨s0, m, hs, f⟩⟩⟩⟩

theorem flat_body : body.flat = (seqs bodyL).flat ++ (Code.seq VG.Impl.RsaKeyGen.PPC64LE.Key.dPart
    (.seq (seqs [VG.Impl.RsaKeyGen.PPC64LE.Key.smallPart, VG.Impl.RsaKeyGen.PPC64LE.Key.qinvPart])
      (seqs bodyT))).flat := by
  simp only [body_eq, VG.Impl.RsaKeyGen.PPC64LE.Key.consts, seqs, Code.flat, List.append_assoc,
    List.cons_append, List.nil_append]

theorem body_ct [InvLaw] : RelCT isa (Two E2) body (Two D) :=
  VG.Proof.Rsa.PPC64LE.Keys.RelCT.cut flat_body (two_post (two_taint _ pins_E2 (by taint_decide)) fun _ _ h => body_Q2 h)
    (RelCT.seq (two_post (two_taint _ (pins_cut fun _ _ h => h.1) (by taint_decide)) fun _ _ h => h.2)
      (RelCT.seq (two_post (two_taint _ (pins_cut fun _ _ h => h.1) (by taint_decide)) fun _ _ h => h.2)
        (two_post (two_taint _ (pins_cut fun _ _ h => h.1) (by taint_decide)) fun _ _ h => h.2)))

theorem pins_D : Pins D [.r31] := by
  rintro d s₁ s₂ ⟨a, _, ha, f₁⟩ ⟨b, _, hb, f₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [f₁.r31, f₂.r31]; exact ha.arg hb (by decide)

theorem key_rel [InvLaw] : RelCT isa (Two KRel) code fun _ _ => True := by
  unfold code
  exact RelCT.seq entry_ct (RelCT.seq body_ct (two_taint _ pins_D (by taint_decide)))

theorem key_ct [InvLaw] : ConstantTime isa keyP.pre keyP.pub code :=
  RelCT.constantTime (key_rel.mono (fun s t ⟨hs, ht, hr, hsp, hst⟩ =>
    ⟨pubOf s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [pubOf, KD.mk.injEq]
      exact ⟨(List.map_inj_left.mpr hr).symm, hst.symm⟩⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.RsaKeyGen.PPC64LE.Key
