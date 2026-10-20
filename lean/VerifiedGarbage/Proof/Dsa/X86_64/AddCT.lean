module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtArith
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.CrtMath

/-! # Constant time of DSA modular addition -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- `addMod`'s loads. -/
def addHead (a b : Nat) : List Instr :=
  [.mov .rbx (.mem (hdr (sArr a))), .mov .r9 (.mem (hdr (sArr b))), .mov .r10 (.mem (hdr (sArr Public.aN))),
    .mov .r8 (.mem (hdr (sArr Public.aAcc))), .mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr Public.aTmp))),
    .mov32 .rbp (.imm 0)]

/-- `addMod`'s sum. -/
def addLoop : Prog isa :=
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.mem (ix .r9 .r14)),
    .store (ix .r8 .r14) .rax, cfToRbp]

/-- `addMod`'s carry and the reload of its output's base. -/
def addCarry (o : Nat) : List Instr :=
  [.mov32 .rax (.imm 0), cfFromRbp, .alu .adc .rax (.imm 0), .store (ix .r8 .r12) .rax,
    .mov .rbx (.mem (hdr (sArr o)))]

theorem addCode_eq (o a b : Nat) :
    addMod o a b = .seq (.block (addHead a b)) (.seq addLoop (.seq (.block (addCarry o)) (.seq subMod selectAcc))) := rfl

/-- The workspace of `addMod`, for some `-m⁻¹`. -/
def AddPre (L : Ws) (s : State) : Prop := GoodW L s ∧ 1 ≤ L.w ∧ L.w < 2 ^ 31

/-- After `addMod`'s loads. -/
def AddHead (a b : Nat) (L : Ws) (t : State) : Prop :=
  t.gpr .rdi = L.B ∧ t.gpr .rbx = off L.B (slot L.w a) ∧ t.gpr .r9 = off L.B (slot L.w b) ∧
    t.gpr .r10 = off L.B (slot L.w Public.aN) ∧ t.gpr .r8 = off L.B (slot L.w Public.aAcc) ∧
    t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rsi = off L.B (slot L.w Public.aTmp) ∧ t.gpr .rbp = mask false ∧
    GoodW L t ∧ 1 ≤ L.w ∧ L.w < 2 ^ 31

/-- Before `addMod`'s subtraction and selection. -/
def AddMid (o : Nat) (L : Ws) (t : State) : Prop :=
  t.gpr .rbx = off L.B (slot L.w o) ∧ t.gpr .r10 = off L.B (slot L.w Public.aN) ∧
    t.gpr .r8 = off L.B (slot L.w Public.aAcc) ∧ t.gpr .r12 = BitVec.ofNat 64 L.w ∧
    t.gpr .rsi = off L.B (slot L.w Public.aTmp)

theorem addHead_ok {a b : Nat} (ha : a < 8) (hb : b < 8) {L : Ws} {s : State} (h : AddPre L s) : WP isa (.block (addHead a b)) s (AddHead a b L) := by
  obtain ⟨⟨minv, hg, hZ⟩, hw, hw'⟩ := h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  refine WP.mono (WP.keep [.rbx, .r9, .r10, .r8, .r12, .rsi, .rbp] (Q := fun t =>
      t.gpr .rbx = off L.B (slot L.w a) ∧ t.gpr .r9 = off L.B (slot L.w b) ∧
      t.gpr .r10 = off L.B (slot L.w Public.aN) ∧ t.gpr .r8 = off L.B (slot L.w Public.aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rsi = off L.B (slot L.w Public.aTmp) ∧ t.gpr .rbp = mask false ∧
      t.mem = s.mem)
    (by unfold addHead; xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr a) (by unfold sArr; omega), hl (sArr b) (by unfold sArr; omega),
      hl (sArr Public.aN) (by decide), hl (sArr Public.aAcc) (by decide), hl sW (by decide),
      hl (sArr Public.aTmp) (by decide), hg.hdr.harr a ha, hg.hdr.harr b hb,
      hg.hdr.harr Public.aN (by decide), hg.hdr.harr Public.aAcc (by decide), hg.hdr.harr Public.aTmp (by decide),
      hg.hdr.hw]) rfl)
    fun t ⟨⟨h1, h2, h3, h4, h5, h6, h7, hm⟩, k⟩ => ⟨(k.gpr (by decide)).trans hg.rdi, h1, h2, h3, h4, h5, h6, h7,
      ⟨minv, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hw, hw'⟩

theorem addCarry_ok {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (haAcc : a ≠ Public.aAcc) (hbAcc : b ≠ Public.aAcc) {L : Ws} {s₁ : State} (h : AddHead a b L s₁) : WP isa (.seq addLoop (.block (addCarry o))) s₁ (AddMid o L) := by
  obtain ⟨hdi, hbx, h9, h10, h8, h12, hsi, hbp, ⟨minv, hg, hZ⟩, hw, hw'⟩ := h
  have hs₁ := hg.scr
  have hn := hs₁.nowrap
  have sl : ∀ j < 8, slot L.w j + 8 * (L.w + 2) ≤ L.Z := fun j hj => (slot_le hj).trans hZ
  have sA := sl Public.aAcc (by decide)
  have sX := sl a ha
  have sT := sl b hb
  have p1 := slot_sep (w := L.w) haAcc
  have p2 := slot_sep (w := L.w) hbAcc
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      AddInv s₁ L.B L.Z (slot L.w Public.aAcc) (slot L.w a) (slot L.w b) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := L.w) (by omega) hw'
    (AddInv s₁ L.B L.Z (slot L.w Public.aAcc) (slot L.w a) (slot L.w b)) h0
    (fun j _ hj t hI => addStep_ok h8 hbx h9 h12 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hj hI)) fun s₂ hI => ?_)
  obtain ⟨c, hc, -⟩ := hI.val
  have s₂8 : s₂.gpr .r8 = off L.B (slot L.w Public.aAcc) := (hI.keep.gpr (by decide)).trans h8
  have s₂12 : s₂.gpr .r12 = BitVec.ofNat 64 L.w := (hI.keep.gpr (by decide)).trans h12
  have s₂di : s₂.gpr .rdi = L.B := (hI.keep.gpr (by decide)).trans hdi
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  have q1 := hdr_lt_slot L.w Public.aAcc (show sArr o < 32 by unfold sArr; omega)
  have q2 := hdr_lt_slot L.w 8 (show sArr o < 32 by unfold sArr; omega)
  have ho₂ : word s₂.mem L.B (8 * sArr o) = off L.B (slot L.w o) := by
    rw [hI.out.word (by omega) (by omega)]
    exact hg.hdr.harr o ho
  have hX : ∀ v : BitVec 64,
      (s₂.mem.writeW (off L.B (slot L.w Public.aAcc + 8 * L.w)) v).readW (off L.B (8 * sArr o)) 64 =
        off L.B (slot L.w o) := fun v =>
    ((writeW_outside s₂.mem L.B v (by omega)).word (Or.inl (by omega)) (by omega)).trans ho₂
  refine WP.mono (WP.keep [.rax, .rbp, .rbx] (Q := fun t => t.gpr .rbx = off L.B (slot L.w o))
    (by
      unfold addCarry cfFromRbp
      xrun [State.ea, ix, hdr, s₂di, hdrOff, addr0 s₂8 s₂12, hc, cf_mask,
        hI.scr.st (show slot L.w Public.aAcc + 8 * L.w + 8 ≤ L.Z by omega), sx0, hl₂ (sArr o) (by unfold sArr; omega),
        hX]) rfl) fun t ⟨hbx', k⟩ => ⟨hbx', ?_, ?_, ?_, ?_⟩
  · exact (k.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans h10)
  · exact (k.gpr (by decide)).trans s₂8
  · exact (k.gpr (by decide)).trans s₂12
  · exact (k.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans hsi)

theorem pins_addHead (a b : Nat) : Pins (AddHead a b) [.rdi, .rbx, .r9, .r10, .r8, .r12, .rsi] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁, -⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂, -⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]
  · rw [f₁, f₂]
  · rw [g₁, g₂]

theorem pins_addMid (o : Nat) : Pins (AddMid o) [.rbx, .r10, .r8, .r12, .rsi] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]

/-- Modular addition has a value-independent trace for either DSA schedule. -/
theorem addCode_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (haAcc : a ≠ Public.aAcc) (hbAcc : b ≠ Public.aAcc)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi]) (.block (addHead a b)) h₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .rbx, .r9, .r10, .r8, .r12, .rsi])
      (.seq addLoop (.block (addCarry o))) h₂).isSome = true)
    (ht₃ : (taint.check (Taint.ofRegs [.rbx, .r10, .r8, .r12, .rsi])
      (.seq subMod selectAcc) h₃).isSome = true) :
    RelCT isa (Two AddPre) (addMod o a b) fun _ _ => True := by
  rw [addCode_eq]
  exact RelCT.assoc (RelCT.assoc (RelCT.seq (two_post (Ψ := AddMid o)
    (RelCT.assoc' (RelCT.seq (two_piece (Ψ := AddHead a b) [.rdi]
      (pins_rdiB (fun L => L.B) fun _ _ ⟨⟨_, hg, _⟩, _⟩ => hg.rdi) ht₁
        fun _ _ h => addHead_ok ha hb h)
      (two_taint _ (pins_addHead a b) ht₂)))
    fun _ _ h => WP.seq (WP.seq (WP.mono (addHead_ok ha hb h)
      fun _ h₁ => WP.seq_iff.mp (addCarry_ok ho ha hb haAcc hbAcc h₁))))
    (two_taint _ (pins_addMid o) ht₃)))

end VG.Proof.Dsa.X86_64
