module

import VerifiedGarbage.Proof.Ffdh.X86_64.Checks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Checks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.CrtMath

/-! # FFDH on x86-64: comparisons in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (copyArr)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Only pointers and the number of words are public after the header loads. -/
def CmpRegs (a b : Nat) (L : Ws) (s : State) : Prop :=
  s.gpr .r12 = BitVec.ofNat 64 L.w ∧ s.gpr .rbx = off L.B (slot L.w a) ∧
    s.gpr .r10 = off L.B (slot L.w b)

private theorem pins_cmpRegs (a b : Nat) : Pins (CmpRegs a b) [.r12, .rbx, .r10] :=
  pins_of (fun L r => if r = .r12 then BitVec.ofNat 64 L.w else
    if r = .rbx then off L.B (slot L.w a) else off L.B (slot L.w b)) fun L s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2

private theorem ptrs_cmpRegs {a b : Nat} (ha : a < 8) (hb : b < 8) (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block (ptrs a b)) s (CmpRegs a b L) := by
  obtain ⟨_, hg, hZ⟩ := h
  exact WP.mono (ptrs_ok hg hZ ha hb) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

private theorem cmp_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {c : Prog isa}
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (ptrs a b)) hc₁).isSome = true)
    (hT' : (taint.check (Taint.ofRegs [.r12, .rbx, .r10]) c hc₂).isSome = true) :
    RelCT isa (Two GoodW) (.seq (.block (ptrs a b)) c) fun _ _ => True :=
  RelCT.seq (two_piece [.rdi] pins_goodW hT (ptrs_cmpRegs ha hb))
    (two_taint [.r12, .rbx, .r10] (pins_cmpRegs a b) hT')

/-- Secret operands change neither the addresses nor the loop count. -/
theorem ltArr_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (ptrs a b)) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (ltArr a b)) fun _ _ => True :=
  cmp_ct ha hb hT (by taint_decide)

theorem geArr_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (ptrs a b)) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (geArr a b)) fun _ _ => True :=
  cmp_ct ha hb hT (by taint_decide)

theorem eqArr_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (ptrs a b)) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (eqArr a b)) fun _ _ => True :=
  cmp_ct ha hb hT (by taint_decide)

theorem _root_.VG.Proof.Bignum.X86_64.GoodW.keep {L : Ws} {s t : State} (h : GoodW L s)
    (hm : t.mem = s.mem) (hdi : t.gpr .rdi = s.gpr .rdi) (hwr : t.wr = s.wr) : GoodW L t := by
  obtain ⟨mi, hg, hZ⟩ := h
  exact ⟨mi, ⟨hg.scr.congr hwr, hdi.trans hg.rdi, by rw [hm]; exact hg.hdr⟩, hZ⟩

/-- Layouts of at least one word and fewer than `2^31`. -/
def GoodW1 (L : Ws) (s : State) : Prop := GoodW L s ∧ 1 ≤ L.w ∧ L.w < 2 ^ 31

theorem two_goodW1 {s₁ s₂ : State} (h : Two GoodW1 s₁ s₂) : Two GoodW s₁ s₂ := two_mono (fun _ _ h => h.1) h

/-- The workspace, with `x16` the temporary array's base. -/
def TmpReg (L : Ws) (t : State) : Prop := GoodW L t ∧ t.gpr .rbx = off L.B (slot L.w aTmp)

theorem tmpPtr_ok (L : Ws) (s : State) (h : GoodW1 L s) :
    WP isa (.block [.mov .rbx (.mem (hdr (sArr aTmp)))]) s fun t => GoodW1 L t ∧ t.gpr .rbx = off L.B (slot L.w aTmp) := by
  obtain ⟨⟨mi, hg, hZ⟩, hw⟩ := h
  exact WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = off L.B (slot L.w aTmp) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (show 8 * sArr aTmp + 8 ≤ L.Z by have := hdr_lt_slot L.w 8 (show sArr aTmp < 32 by decide); omega),
      hg.hdr.harr aTmp (by decide)]) rfl)
    fun t ⟨⟨h16, hm⟩, k⟩ => ⟨⟨GoodW.keep ⟨mi, hg, hZ⟩ hm (k.gpr (by decide)) k.2.2, hw⟩, h16⟩

theorem or1_ok (L : Ws) (s : State) (h : GoodW1 L s ∧ s.gpr .rbx = off L.B (slot L.w aTmp)) :
    WP isa (.block [.mov .rax (.mem (at0 .rbx)), .alu .or .rax (.imm 1), .store (at0 .rbx) .rax]) s (GoodW1 L) := by
  obtain ⟨⟨⟨mi, hg, hZ⟩, hw⟩, h16⟩ := h
  have hn := hg.scr.nowrap
  have sT := Nat.le_trans (slot_le (w := L.w) (show aTmp < 8 by decide)) hZ
  have hT0 := hdr_lt_slot L.w aTmp (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = s.mem.writeW (off L.B (slot L.w aTmp))
      (word s.mem L.B (slot L.w aTmp) ||| 1))
    (by xrun [State.ea, at0, h16, show off L.B (slot L.w aTmp) + BitVec.ofInt 64 0 = off L.B (slot L.w aTmp) from by simp, hg.scr.ld (show slot L.w aTmp + 8 ≤ L.Z by omega), hg.scr.st (show slot L.w aTmp + 8 ≤ L.Z by omega)])
    rfl) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem L.B (d := slot L.w aTmp) (word s.mem L.B (slot L.w aTmp) ||| 1) (by omega)
  rw [← hm] at o
  exact ⟨⟨mi, hg.of_outside (by omega) o k.2.2 (k.gpr (by decide)), hZ⟩, hw⟩

theorem ltP_eq : seqs (([.block [.mov .rbx (.mem (hdr (sArr aTmp)))], .block [.mov .rax (.mem (at0 .rbx)), .alu .or .rax (.imm 1), .store (at0 .rbx) .rax]] : List (Prog isa)) ++ ltArr aTmp aN) = .seq (.block [.mov .rbx (.mem (hdr (sArr aTmp)))])
    (.seq (.block [.mov .rax (.mem (at0 .rbx)), .alu .or .rax (.imm 1), .store (at0 .rbx) .rax]) (seqs (ltArr aTmp aN))) := rfl

/-- `ltP a` (`a ≠ aTmp`). -/
theorem ltP_ct {a : Nat} (ha : a < 8) (haT : a ≠ aTmp) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr a))), .mov .rbx (.mem (hdr (sArr aTmp)))])
      hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.rdi]) (.block (ptrs aTmp aN)) hc₂).isSome = true) :
    RelCT isa (Two GoodW1) (seqs (ltP a)) fun _ _ => True := by
  unfold ltP
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [copyArr]) (by simp) ?_
  rw [ltP_eq]
  refine RelCT.seq (R := Two GoodW1) (two_post ((copyArr_ct (show aTmp < 8 by decide) ha hT₁).mono
      (fun _ _ h => two_goodW1 h) fun _ _ h => h) fun L s h => ?_)
    (RelCT.seq (two_piece [.rdi] (fun L s₁ s₂ h₁ h₂ => pins_goodW L s₁ s₂ h₁.1 h₂.1) (by taint_decide) tmpPtr_ok)
      (RelCT.seq (two_piece [.rbx] (pins_of (fun L _ => off L.B (slot L.w aTmp)) fun L s h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.2) (by taint_decide) or1_ok)
        ((ltArr_ct (show aTmp < 8 by decide) (show aN < 8 by decide) hT₂).mono (fun _ _ h => two_goodW1 h)
          fun _ _ h => h)))
  obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
  have hT0 := hdr_lt_slot L.w aTmp (show 31 < 32 by decide)
  exact WP.mono (copyArr_ok hg hZ hw hw' (show aTmp < 8 by decide) ha (Ne.symm haT)) fun t ⟨_, ho, k⟩ =>
    ⟨⟨mi, hg.of_outside (by omega) ho k.2.2 (k.gpr (by decide)), hZ⟩, hw, hw'⟩

/-- `GoodW1` after a change of memory at offsets `o ≥ 128`. -/
theorem GoodW1.of_outside {L : Ws} {s t : State} (h : GoodW1 L s) {o n : Nat} (ho : 8 * 16 ≤ o)
    (hout : Outside L.B o n s.mem t.mem) (hwr : t.wr = s.wr) (h0 : t.gpr .rdi = s.gpr .rdi) : GoodW1 L t :=
  let ⟨⟨mi, hg, hZ⟩, hw⟩ := h
  ⟨⟨mi, hg.of_outside ho hout hwr h0, hZ⟩, hw⟩

theorem GoodW1.keep {L : Ws} {s t : State} (h : GoodW1 L s) (hm : t.mem = s.mem) (h0 : t.gpr .rdi = s.gpr .rdi)
    (hwr : t.wr = s.wr) : GoodW1 L t := ⟨GoodW.keep h.1 hm h0 hwr, h.2⟩

theorem pins_goodW1 : Pins GoodW1 [.rdi] := fun L s₁ s₂ h₁ h₂ => pins_goodW L s₁ s₂ h₁.1 h₂.1

/-- A store of `x9` into the header slot `sl ≥ 16`. -/
theorem stF_ok {sl : Nat} (hsl : 16 ≤ sl) (hsl' : sl < 32) (L : Ws) (s : State) (h : GoodW1 L s) :
    WP isa (.block [.store (hdr sl) .rax]) s (GoodW1 L) := by
  obtain ⟨⟨mi, hg, hZ⟩, hw⟩ := h
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot L.w 0 hsl'
  have h8' := hdr_lt_slot L.w 8 hsl'
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = s.mem.writeW (off L.B (8 * sl)) (s.gpr .rax))
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.st (show 8 * sl + 8 ≤ L.Z by omega)]) rfl) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem L.B (d := 8 * sl) (s.gpr .rax) (by omega)
  rw [← hm] at o
  exact GoodW1.of_outside ⟨⟨mi, hg, hZ⟩, hw⟩ (by omega) o k.2.2 (k.gpr (by decide))

/-- `andF`. -/
theorem andF_ok (L : Ws) (s : State) (h : GoodW1 L s) : WP isa (.block andF) s (GoodW1 L) := by
  obtain ⟨⟨mi, hg, hZ⟩, hw⟩ := h
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot L.w 0 (show sF < 32 by decide)
  have h8' := hdr_lt_slot L.w 8 (show sF < 32 by decide)
  have eF : sF = 30 := rfl
  refine WP.mono (WP.keep [.rax] (Q := fun t' => ∃ v : BitVec 64, t'.mem = s.mem.writeW (off L.B (8 * sF)) v)
    (by unfold andF; xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (show 8 * sF + 8 ≤ L.Z by omega),
      hg.scr.st (show 8 * sF + 8 ≤ L.Z by omega)]; exact ⟨_, rfl⟩) rfl)
    fun t ⟨⟨v, hm⟩, k⟩ => ?_
  have o := writeW_outside s.mem L.B (d := 8 * sF) v (by omega)
  rw [← hm] at o
  exact GoodW1.of_outside ⟨⟨mi, hg, hZ⟩, hw⟩ (by omega) o k.2.2 (k.gpr (by decide))

/-- `range a` (`a ≠ aTmp`). -/
theorem range_ct {a : Nat} (ha : a < 8) (haT : a ≠ aTmp) {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.rdi]) (.block (ptrs aOne a)) hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr a))), .mov .rbx (.mem (hdr (sArr aTmp)))])
      hc₂).isSome = true)
    (hT₃ : (taint.check (Taint.ofRegs [.rdi]) (.block (ptrs aTmp aN)) hc₃).isSome = true) :
    RelCT isa (Two GoodW1) (seqs (range a)) fun _ _ => True := by
  rw [show range a = ltArr aOne a ++ (.block [.store (hdr sF) .rax] :: (ltP a ++ [.block andF])) by simp [range, gt1]]
  refine RelCT.seqs_append (by simp [ltArr, cmpArr]) (by simp) (RelCT.seq (R := Two GoodW1)
    (two_post ((ltArr_ct (show aOne < 8 by decide) ha hT₁).mono (fun _ _ h => two_goodW1 h) fun _ _ h => h)
      fun L s h => ?_) ?_)
  · obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
    exact WP.mono (ltArr_ok hg hZ hw hw' (show aOne < 8 by decide) ha) fun t ⟨_, hm, k⟩ =>
      GoodW1.keep ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ hm (k.gpr (by decide)) k.2.2
  refine seqs_cons_ct (by simp [ltP, copyArr]) (RelCT.seq (R := Two GoodW1)
    (two_piece [.rdi] pins_goodW1 (by taint_decide) (stF_ok (by decide) (by decide))) ?_)
  refine RelCT.seqs_append (by simp [ltP, copyArr]) (by simp) (RelCT.seq (R := Two GoodW1)
    (two_post (ltP_ct ha haT hT₂ hT₃) fun L s h => ?_) ?_)
  · obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
    have hT0 := hdr_lt_slot L.w aTmp (show 31 < 32 by decide)
    exact WP.mono (ltP_ok hg hZ hw hw' ha haT) fun t ⟨_, ho, k⟩ =>
      GoodW1.of_outside ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ (by omega) ho k.2.2 (k.gpr (by decide))
  exact two_taint [.rdi] pins_goodW1 (by taint_decide)

end VG.Proof.Ffdh.X86_64
