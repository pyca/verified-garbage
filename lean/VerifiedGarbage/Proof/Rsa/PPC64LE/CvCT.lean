module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCorrect
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCorrect
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCheck
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvFail
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCheck
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.CvFail
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts

/-!
# `vg_rsa_crt_values` on PPC64LE: constant time

The taint analysis treats memory as secret, so the working space's address
(a stack argument) and the bytes of `n` that `check` loads are secret to it,
although they are public. Two runs are related by `Two` (`MontCT.lean`) at
each step, both satisfying the same predicate for the same public data
(`pubOf`: the argument registers, the stack arguments and `n`'s bytes):
after the entry's first load the working space's address, after the entry
the pointers and lengths it keeps in `r14`–`r24`, after `check1` the first
byte of `n`, which `check2` branches on, and after `check2` whether `n` is
valid, which the branch tests (`RelCT.ite`). Everything else is checked by
the taint analysis from those registers.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.CrtValues (code entry check check1 check2 valid fail restore)

/-- The public data: the argument registers, the stack arguments and `n`'s bytes. -/
structure CvD where
  regs : List (BitVec 64)
  stk : List (BitVec 64)
  nb : List Byte

/-- `n`'s bytes. -/
abbrev nbOf (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (cvK s)

def pubOf (s : State) : CvD := ⟨argRegs.map s.gpr, (List.range 8).map (PPC64LE.stackArg s), nbOf s⟩

/-- A state the contract allows, with the public data `d`. -/
def CVRel (d : CvD) (s : State) : Prop := cvP.pre s ∧ pubOf s = d

theorem CVRel.reg {d : CvD} {s₁ s₂ : State} (h₁ : CVRel d s₁) (h₂ : CVRel d s₂) {r : Reg}
    (hr : r ∈ argRegs) : s₁.gpr r = s₂.gpr r :=
  List.map_inj_left.mp ((congrArg CvD.regs h₁.2).trans (congrArg CvD.regs h₂.2).symm) r hr

theorem CVRel.arg {d : CvD} {s₁ s₂ : State} (h₁ : CVRel d s₁) (h₂ : CVRel d s₂) {i : Nat} (hi : i < 8) :
    PPC64LE.stackArg s₁ i = PPC64LE.stackArg s₂ i :=
  List.map_inj_left.mp ((congrArg CvD.stk h₁.2).trans (congrArg CvD.stk h₂.2).symm) i (List.mem_range.mpr hi)

theorem CVRel.nb {d : CvD} {s : State} (h : CVRel d s) : nbOf s = d.nb := congrArg CvD.nb h.2

theorem CVRel.k {d : CvD} {s₁ s₂ : State} (h₁ : CVRel d s₁) (h₂ : CVRel d s₂) : cvK s₁ = cvK s₂ := by
  rw [cvK, cvK, h₁.reg h₂ (by decide)]

/-! ## The entry -/

/-- What the entry establishes. -/
def EP (s0 s : State) : Prop := Base s0 s ∧ Args s0 s ∧ Keep entryRegs s0 s

/-- The entry after its first load, the working space's address. -/
def E1 (d : CvD) (t : State) : Prop :=
  ∃ s0, CVRel d s0 ∧ t.gpr .r11 = PPC64LE.stackArg s0 6 ∧
    WP isa (.block (entry.drop 2)) t (EP s0)

/-- After the entry. -/
def E2 (d : CvD) (t : State) : Prop := ∃ s0, CVRel d s0 ∧ EP s0 t

theorem entry_split : entry = VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 6 ++ entry.drop 2 := rfl

theorem pins_nil {α : Type} {Φ : α → State → Prop} : Pins Φ [] := by
  intro _ _ _ _ _ r hr; simp at hr

theorem pins_E1 : Pins E1 [.r11] := by
  rintro d s₁ s₂ ⟨a, ha, h₁, -⟩ ⟨b, hb, h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h₁, h₂, ha.arg hb (by decide)]

theorem E1_of {d : CvD} {s : State} (hs : CVRel d s) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 6)) s (E1 d) := by
  have hw := entry_ok hs.1
  rw [entry_split, WP.block_append_iff] at hw
  have h11 : WP isa (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 6)) s fun t =>
      t.gpr .r11 = PPC64LE.stackArg s 6 := by
    rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 6)]
    refine stackArg_ok hs.1 rfl rfl (r := .r11) (by decide) (by decide) (WP.block_nil ?_)
    simp only [State.write, ↓reduceIte]
  exact WP.mono (WP.and hw h11) fun t ⟨w, e⟩ => ⟨s, hs, e, w⟩

theorem entry_ct : RelCT isa (Two CVRel) (.block entry) (Two E2) := by
  rw [entry_split]
  refine RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_nil (by taint_decide)) fun _ _ h => E1_of h)
    (two_post (two_taint _ pins_E1 (by taint_decide)) fun _ _ ⟨s0, hs, _, hw⟩ =>
      WP.mono hw fun _ h => ⟨s0, hs, h⟩))

/-! ## The check -/

/-- After `check1`. -/
def C1 (d : CvD) (t : State) : Prop :=
  ∃ s0 s, CVRel d s0 ∧ EP s0 s ∧
    (t.gpr .r0 = 0 ↔ ((nbOf s0).getD (cvK s0 - 1) 0).toNat % 2 = 1) ∧
    t.gpr .r11 = BitVec.ofNat 64 ((nbOf s0).getD 0 0).toNat ∧ t.mem = s.mem ∧ Keep [.r0, .r11, .r12] s t

/-- After `check2`. -/
def C2 (d : CvD) (t : State) : Prop :=
  ∃ s0, CVRel d s0 ∧ Base s0 t ∧ Args s0 t ∧
    (t.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (nIn s0) (cvK s0) = true)

theorem getD_of_lt {l : List Byte} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem len_nb (s : State) : (nbOf s).length = cvK s := by simp [Spec.Rsa.bytesAt]

/-- What `check1_ok` takes, after the entry. -/
theorem check_args {s0 s : State} (h : EP s0 s) :
    s.gpr .r9 = off (s0.gpr .r9) 0 ∧ s.gpr .r10 = BitVec.ofNat 64 (cvK s0) ∧
      (∀ i < cvK s0, InRegions (s.rd ++ s.wr) (off (s0.gpr .r9) i) 1) ∧
      ∀ i (hi : i < cvK s0), s.mem (off (s0.gpr .r9) i) = (nbOf s0)[i]'(by rw [len_nb]; exact hi) := by
  obtain ⟨b, -, k⟩ := h
  obtain ⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, dn, -, -, -, -, -, -, -, wn,
    -⟩ := id b.pre
  have wn' : (s0.gpr .r9).toNat + cvK s0 ≤ 2 ^ 64 := wn
  have hc : ∀ i < cvK s0, (⟨s0.gpr .r9, cvK s0⟩ : Region).Contains (off (s0.gpr .r9) i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  refine ⟨by rw [k.gpr _ (by decide)]; simp [off], by rw [k.gpr _ (by decide)]; exact ofNat_toNat64 _,
    fun i hi => ⟨_, List.mem_append_left _ (by rw [b.rd, hrd]; simp), hc i hi⟩,
    fun i hi => by rw [b.frame _ (past_of_disjoint dn (hc i hi))]; simp [Spec.Rsa.bytesAt, off]⟩

theorem pins_E2 : Pins E2 [.r9, .r10] := by
  rintro d s₁ s₂ ⟨a, ha, -, -, k₁⟩ ⟨b, hb, -, -, k₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide), ha.reg hb (by decide)]
  · rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide), ha.reg hb (by decide)]

theorem pins_C1 : Pins C1 [.r10, .r11] := by
  rintro d s₁ s₂ ⟨a, u₁, ha, ⟨-, -, k₁⟩, -, e₁, -, l₁⟩ ⟨b, u₂, hb, ⟨-, -, k₂⟩, -, e₂, -, l₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [l₁.gpr _ (by decide), l₂.gpr _ (by decide), k₁.gpr _ (by decide), k₂.gpr _ (by decide),
      ha.reg hb (by decide)]
  · rw [e₁, e₂, ha.nb, hb.nb]

theorem C1_of {d : CvD} {s : State} (h : E2 d s) : WP isa (.block check1) s (C1 d) := by
  obtain ⟨s0, hs, he⟩ := h
  obtain ⟨h9, h10, hrd, hb⟩ := check_args he
  obtain ⟨-, -, -, hk, -⟩ := pre_scr hs.1
  refine WP.mono (check1_ok h9 h10 hk (len_nb s0) hrd hb) fun t ⟨⟨i0, i11, im⟩, k⟩ =>
    ⟨s0, s, hs, he, by rw [i0, getD_of_lt (by rw [len_nb]; omega)], by rw [i11, getD_of_lt (by rw [len_nb]; omega)],
      im, k⟩

theorem C2_of {d : CvD} {s : State} (h : C1 d s) : WP isa check2 s (C2 d) := by
  obtain ⟨s0, u, hs, ⟨b, a, k⟩, i0, i11, im, ku⟩ := h
  obtain ⟨-, -, -, hk, hk'⟩ := pre_scr hs.1
  have h10 : s.gpr .r10 = BitVec.ofNat 64 (cvK s0) := by
    rw [ku.gpr _ (by decide), k.gpr _ (by decide)]; exact ofNat_toNat64 _
  refine WP.mono (check2_ok h10 hk hk' (len_nb s0) (by rw [i0, getD_of_lt (by rw [len_nb]; omega)])
    (by rw [i11, getD_of_lt (by rw [len_nb]; omega)])) fun t ⟨hv, tm, kt⟩ =>
    ⟨s0, hs, (b.of_regs ku im).of_regs kt tm, (a.of_keep ku).of_keep kt, hv⟩

theorem check_ct : RelCT isa (Two E2) check (Two C2) :=
  RelCT.seq (two_post (two_taint _ pins_E2 (by taint_decide)) fun _ _ h => C1_of h)
    (two_post (two_taint _ pins_C1 (by taint_decide)) fun _ _ h => C2_of h)

/-! ## The branches -/

/-- After either branch. -/
def D (d : CvD) (t : State) : Prop := ∃ s0 m, CVRel d s0 ∧ Fr s0 m t

/-- The registers both branches start from. -/
abbrev brRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r31]

theorem pins_br {Φ : CvD → State → Prop} (hΦ : ∀ d s, Φ d s → C2 d s) : Pins Φ brRegs := by
  intro d s₁ s₂ h₁ h₂ r hr
  obtain ⟨a, ha, b₁, a₁, -⟩ := hΦ _ _ h₁
  obtain ⟨b, hb, b₂, a₂, -⟩ := hΦ _ _ h₂
  simp only [brRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a₁.r14, a₂.r14, ha.reg hb (by decide)]
  · rw [a₁.r15, a₂.r15, ha.reg hb (by decide)]
  · rw [a₁.r16, a₂.r16, ha.reg hb (by decide)]
  · rw [a₁.r17, a₂.r17, ha.reg hb (by decide)]
  · rw [a₁.r18, a₂.r18, ha.reg hb (by decide)]
  · rw [a₁.r19, a₂.r19, ha.arg hb (by decide)]
  · rw [a₁.r20, a₂.r20, ha.arg hb (by decide)]
  · rw [a₁.r21, a₂.r21, ha.arg hb (by decide)]
  · rw [a₁.r22, a₂.r22, ha.arg hb (by decide)]
  · rw [a₁.r23, a₂.r23, ha.arg hb (by decide)]
  · rw [a₁.r24, a₂.r24, ha.arg hb (by decide)]
  · rw [b₁.r31, b₂.r31]; exact ha.arg hb (by decide)

theorem valid_D [InvLaw] {d : CvD} {s : State} (h : C2 d s ∧ s.gpr .r0 = 0) : WP isa valid s (D d) := by
  obtain ⟨⟨s0, hs, b, a, hv⟩, h0⟩ := h
  exact WP.mono (valid_ok b a (hv.mp h0)) fun _ ⟨⟨⟨m, f⟩, _⟩, _⟩ => ⟨s0, m, hs, f⟩

theorem fail_D {d : CvD} {s : State} (h : C2 d s ∧ s.gpr .r0 ≠ 0) : WP isa fail s (D d) := by
  obtain ⟨⟨s0, hs, b, a, -⟩, -⟩ := h
  exact WP.mono (fail_ok b a) fun _ ⟨f, _⟩ => ⟨s0, _, hs, f⟩

theorem valid_iff {d : CvD} {s₁ s₂ : State} (h₁ : C2 d s₁) (h₂ : C2 d s₂) :
    (s₁.gpr .r0 = 0 ↔ s₂.gpr .r0 = 0) := by
  obtain ⟨a, ha, -, -, i₁⟩ := h₁
  obtain ⟨b, hb, -, -, i₂⟩ := h₂
  rw [i₁, i₂, show nIn a = nIn b by simp only [nIn]; rw [show Spec.Rsa.bytesAt a.mem (a.gpr .r9) (cvK a) = nbOf a
    from rfl, ha.nb, show Spec.Rsa.bytesAt b.mem (b.gpr .r9) (cvK b) = nbOf b from rfl, hb.nb], ha.k hb]

theorem branch_ct [InvLaw] : RelCT isa (Two C2) (.ite (.zero .d .r0) valid fail) (Two D) := by
  refine RelCT.ite (fun s₁ s₂ ⟨d, h₁, h₂, _⟩ => ?_)
    (RelCT.mono (two_post (Φ := fun d s => C2 d s ∧ s.gpr .r0 = 0)
      (two_taint _ (pins_br fun _ _ h => h.1) (by taint_decide)) fun _ _ h => valid_D h)
      (fun s₁ s₂ ⟨⟨d, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
    (RelCT.mono (two_post (Φ := fun d s => C2 d s ∧ s.gpr .r0 ≠ 0)
      (two_taint _ (pins_br fun _ _ h => h.1) (by taint_decide)) fun _ _ h => fail_D h)
      (fun s₁ s₂ ⟨⟨d, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
  · rw [eval_zero, eval_zero]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact valid_iff h₁ h₂
  · rw [eval_zero] at hc
    have h0 : s₁.gpr .r0 = 0 := by simpa using hc
    exact ⟨d, ⟨h₁, h0⟩, ⟨h₂, (valid_iff h₁ h₂).mp h0⟩, hsp⟩
  · rw [eval_zero] at hc
    have h0 : s₁.gpr .r0 ≠ 0 := by simpa using hc
    exact ⟨d, ⟨h₁, h0⟩, ⟨h₂, fun e => h0 ((valid_iff h₁ h₂).mpr e)⟩, hsp⟩

theorem pins_D : Pins D [.r31] := by
  rintro d s₁ s₂ ⟨a, _, ha, f₁⟩ ⟨b, _, hb, f₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [f₁.r31, f₂.r31]; exact ha.arg hb (by decide)

theorem cv_rel [InvLaw] : RelCT isa (Two CVRel) code fun _ _ => True := by
  unfold code
  exact RelCT.seq entry_ct (RelCT.seq check_ct (RelCT.seq branch_ct (two_taint _ pins_D (by taint_decide))))

theorem cv_ct [InvLaw] : ConstantTime isa cvP.pre cvP.pub code :=
  RelCT.constantTime (cv_rel.mono (fun s t ⟨hs, ht, hr, hsp, hst, hb⟩ =>
    ⟨pubOf s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [pubOf, CvD.mk.injEq]
      exact ⟨(List.map_inj_left.mpr hr).symm, hst.symm, hb.symm⟩⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Rsa.PPC64LE.CrtValues
