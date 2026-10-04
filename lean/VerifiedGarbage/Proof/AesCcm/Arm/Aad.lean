import VerifiedGarbage.Proof.AesCcm.Arm.Header
import VerifiedGarbage.Proof.AesGcm.Arm.Args
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-CCM on ARMv7: the associated data (`aad y`)

Untrusted: everything here is checked by Lean. The pieces read the stack
arguments, which the writes of the pieces miss, as on entry (`Stk`).
`aadHead y` chains the first block of the formatted associated data: the
encoding of its length followed by as many of its bytes as fit, padded
(`aadHead_ok`); `aad y` that block and the rest of the associated data,
padded, if there is any (`aad_ok`): the blocks `adataBlocks`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 copyLoop minLen)
open VG.Proof.AesGcm.Arm (LoopOut LoopPre copyLoop_ok bytesAt_frame toNat32 ofNat_sub32 z_cmp eval_eq' Keeps
  z_subFlags gpr_subFlags minLen_ok add32_ofNat_assoc ArgsKeep)
open VG.Proof.AesCcm (hdrLen headLen adataBlocks ctxCiph_frame bytesAt_prefix bytesAt_suffix
  bytesAt_writeBytes_at length_bytesAt)

/-- The stack arguments of `s` are those of the entry state `s₀`, apart from
`W` and the stack below `sp`. -/
structure Stk (w : BitVec 32) (s₀ s : State) : Prop where
  keep : ArgsKeep 6 s₀ s
  fit : s₀.sp.toNat + 4 * 6 ≤ 2 ^ 32
  rd : args s₀ 6 ∈ s₀.rd
  aw : (args s₀ 6).Disjoint ⟨State.addr w, 2560⟩

namespace Stk

variable {w : BitVec 32} {s₀ s : State} (h : Stk w s₀ s)
include h

/-- Argument `i`, at offset `4 i`. -/
theorem «at» (i : Nat) {off : Nat} (hi : i < 6) (hoff : 4 * i = off) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4 ∧
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32 = stackArg s₀ i :=
  h.keep.at h.fit h.rd i hi hoff

/-- Argument `i` is apart from `W`. -/
theorem slot_w (i : Nat) {off : Nat} (hi : i < 6) (hoff : 4 * i = off) {d n : Nat} (hd : d + n ≤ 2560) :
    (⟨State.addr (s.sp + BitVec.ofNat 32 off), 4⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, n⟩ := by
  subst hoff
  have := h.fit
  have e : State.addr (s.sp + BitVec.ofNat 32 (4 * i)) = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
    rw [h.keep.sp, Proof.AesGcm.Arm.argAddr_zero]; exact addr_add (by omega)
  rw [e]
  exact (h.aw.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.wSub hd)

theorem of_eq {s' : State} (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Stk w s₀ s' :=
  { h with keep := h.keep.of_eq hm hsp hrd hwr }

/-- After code that writes regions apart from the arguments. -/
theorem frame {s' : State} {rs : List Region} (hfr : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, (args s₀ 6).Disjoint r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Stk w s₀ s' :=
  { h with keep := h.keep.frame h.fit hfr hd hsp hrd hwr }

/-- The stack below `sp` is apart from the arguments. -/
theorem blw_args {sp : BitVec 32} (hsp : s₀.sp = sp) : (args s₀ 6).Disjoint (blw sp) := by
  have := h.fit
  subst hsp
  simp only [args, Proof.AesGcm.Arm.argAddr_zero]
  exact Offset.base_disjoint_below (State.addr s₀.sp) (n := 16) (k := 4 * 6) (by omega)

/-- After code that writes the MAC's regions. -/
theorem mac {sp : BitVec 32} (hsp₀ : s₀.sp = sp) {y : Nat} (hy : y + 16 ≤ 2560) {s' : State}
    (hfr : Frame (macR w sp y) s.mem s'.mem) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Stk w s₀ s' :=
  h.frame hfr (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.aw.sub_right (Lay.wSub hy)
    · exact h.aw.sub_right (Lay.wSub (by decide))
    · exact h.aw.sub_right (Lay.wSub (by decide))
    · exact h.blw_args hsp₀) hsp hrd hwr

end Stk

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem seq_assoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => WP.assoc h)

theorem seq_assoc4 {a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b (.seq c d))) e) s Q) : WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => seq_assoc3 h)

/-- What a piece of the MAC leaves: the environment, what it writes, the
MAC state `Y` at `W + y`, and the permissions. -/
structure MacStep (k w sp : BitVec 32) (R q1 : Nat) (s : State) (y : Nat) (Y : List Byte) (s' : State) :
    Prop where
  env : Env k w sp R q1 s'
  frame : Frame (macR w sp y) s.mem s'.mem
  out : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp)
include L

/-- The encoding of the length and the first bytes of the associated data,
padded, in `B`; `r4` and `r5` the rest. -/
theorem aadHeadPre_ok {s : State} (he : Env k w sp R q1 s) {A : BitVec 32} {a : Nat} (hA : Buf w sp s A a)
    (ha0 : 0 < a) (ha : a < 2 ^ 32) (h4 : s.gpr .r4 = A) (h5 : s.gpr .r5 = BitVec.ofNat 32 a) :
    WP isa (.seq header (.seq minLen (.seq (.block [.mov .r1 (.reg .r4), addI .r2 .r11 bO,
        .dp .add .r2 .r2 (.reg .r6), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)]) copyLoop))) s
      fun s₄ => Env k w sp R q1 s₄ ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
        Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem ∧
        s₄.gpr .r4 = A + BitVec.ofNat 32 (headLen a) ∧ s₄.gpr .r5 = BitVec.ofNat 32 (a - headLen a) ∧
        bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 32) 16 =
          Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (State.addr A) a).take (headLen a)) := by
  have hh := Proof.AesCcm.hdrLen_le a
  have hh26 : hdrLen a = 2 ∨ hdrLen a = 6 := by
    unfold hdrLen; by_cases h : a < 2 ^ 16 - 2 ^ 8 <;> simp [h, ha]
  have hh2 : 2 ≤ hdrLen a := by omega
  have hh6 : hdrLen a ≤ 6 := by omega
  refine WP.seq (WP.mono (header_ok L he ha0 ha h5) fun s₁ ⟨he₁, h6₁, g₁, ⟨rd₁, wr₁, sp₁⟩, f₁, hB₁⟩ => ?_)
  have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 a := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h5]
  have h4₁ : s₁.gpr .r4 = A := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h4]
  refine WP.seq (WP.mono (minLen_ok s₁ h6₁ h5₁ (by omega) ha) fun s₂ ⟨h3₂, g₂, k₂⟩ => ?_)
  have hn1 : min (16 - hdrLen a) a = headLen a := by unfold headLen; omega
  rw [hn1] at h3₂
  have hn1' : 1 ≤ headLen a ∧ headLen a ≤ a ∧ hdrLen a + headLen a ≤ 16 := by unfold headLen; omega
  have he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide)) k₂.sp k₂.rd k₂.wr
  have h11 := he₂.r11
  obtain ⟨s₃, run₃, a1, a2, a3, a4, a5, g₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r1 (.reg .r4), addI .r2 .r11 bO,
      .dp .add .r2 .r2 (.reg .r6), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)] s₂ = some s₃ ∧
      s₃.gpr .r1 = A ∧ s₃.gpr .r2 = w + BitVec.ofNat 32 (32 + hdrLen a) ∧
      s₃.gpr .r3 = BitVec.ofNat 32 (headLen a) ∧ s₃.gpr .r4 = A + BitVec.ofNat 32 (headLen a) ∧
      s₃.gpr .r5 = BitVec.ofNat 32 (a - headLen a) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → r ≠ .r5 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    have h4₂ : s₂.gpr .r4 = A := by rw [g₂ _ (by decide) (by decide), h4₁]
    have h5₂ : s₂.gpr .r5 = BitVec.ofNat 32 a := by rw [g₂ _ (by decide) (by decide), h5₁]
    have h6₂ : s₂.gpr .r6 = BitVec.ofNat 32 (hdrLen a) := by rw [g₂ _ (by decide) (by decide), h6₁]
    refine ⟨_, by simp only [bO]; arun [h11], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h4₂]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h11, h6₂, imm, add32_ofNat_assoc]
    · simp [gpr_setReg, h3₂]
    · simp [gpr_setReg, h4₂, h3₂]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h5₂, h3₂]
      exact ofNat_sub32 hn1'.2.1 ha
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide) (by decide))
    k₃.sp k₃.rd k₃.wr
  have hA₃ := (hA.take hn1'.2.1).of_eq (s' := s₃) (by rw [k₃.rd, k₂.rd, rd₁]) (by rw [k₃.wr, k₂.wr, wr₁])
  have eB := L.wA (d := 32 + hdrLen a) (by omega)
  have lp : LoopPre s₃ A (w + BitVec.ofNat 32 (32 + hdrLen a)) (headLen a) := by
    refine ⟨a1, a2, a3, hn1'.1, by omega, hA₃.fit, by rw [L.wN (by omega)]; have := L.ww; omega, hA₃.rd, ?_, ?_⟩
    · rw [eB]; exact he₃.perm.wC (by omega)
    · rw [eB]; exact hA₃.w.sub_right (Lay.wSub (by omega))
  refine WP.mono (copyLoop_ok s₃ lp) fun s₄ ⟨hm₄, lo⟩ => ?_
  have he₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) lo.sp lo.rd lo.wr
  rw [eB] at hm₄
  have fC : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains _ (d := 32 + hdrLen a) (n := headLen a) (e := 32) (k := 16) (by omega) (by omega)
        (by decide))
  have fB : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
    rw [← k₂.mem, ← k₃.mem] at f₁; exact f₁.trans fC
  have hAk : bytesAt s₃.mem (State.addr A) (headLen a) = (bytesAt s.mem (State.addr A) a).take (headLen a) := by
    rw [k₃.mem, k₂.mem, bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hA.w.sub_left (Region.sub_prefix hn1'.2.1)).sub_right (Lay.wSub (by decide))) (by omega),
      bytesAt_prefix _ _ hn1'.2.1]
  have hB₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 32) 16 =
      Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (State.addr A) a).take (headLen a)) := by
    have hl := Proof.AesCcm.length_encodeLen a
    have htl : ((bytesAt s.mem (State.addr A) a).take (headLen a)).length = headLen a := by
      rw [List.length_take, length_bytesAt]; omega
    rw [hm₄, show State.addr w + BitVec.ofNat 64 (32 + hdrLen a) =
        State.addr w + BitVec.ofNat 64 32 + BitVec.ofNat 64 (hdrLen a) by rw [Offset.add_add],
      bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega) (by decide), length_bytesAt, hAk, k₃.mem,
      k₂.mem, hB₁]
    rcases Proof.AesCcm.pad16_short (r := Spec.Ccm.encodeLen a ++ (bytesAt s.mem (State.addr A) a).take (headLen a))
      (by rw [List.length_append, hl, htl]; omega) with e | e
    · rw [e, List.length_append, hl, htl, List.take_left' hl, ← hl, List.drop_append, hl, List.append_assoc]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append, List.append_assoc,
        show 16 - hdrLen a - (hdrLen a + headLen a - hdrLen a) = 16 - (hdrLen a + headLen a) by omega]
    · exact absurd (congrArg List.length e) (by rw [List.length_append, hl]; simp; omega)
  exact ⟨he₄, by rw [lo.rd, k₃.rd, k₂.rd, rd₁], by rw [lo.wr, k₃.wr, k₂.wr, wr₁], fB,
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), a4],
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), a5], hB₄⟩

/-- The first block of the associated data. -/
theorem aadHead_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {A : BitVec 32} {a : Nat} (hA : Buf w sp s A a) (ha0 : 0 < a) (ha : a < 2 ^ 32)
    (h4 : s.gpr .r4 = A) (h5 : s.gpr .r5 = BitVec.ofNat 32 a) :
    WP isa (aadHead y) s (Absorbed k w sp R q1 s y (A + BitVec.ofNat 32 (headLen a)) (a - headLen a)
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        [Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (State.addr A) a).take (headLen a))])) := by
  refine seq_assoc4 (WP.seq (WP.mono (aadHeadPre_ok L he hA ha0 ha h4 h5)
    fun s₄ ⟨he₄, rd₄, wr₄, fB, h4₄, h5₄, hB₄⟩ => ?_))
  have hY₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 y) 16 =
      bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16 :=
    bytesAt_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (updBlock_ok L he₄ hR hy) fun s₅ ⟨he₅, rd₅, wr₅, g₅, f₅, o₅⟩ =>
    ⟨he₅, ?_, ?_, (fB.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_), ?_, by rw [rd₅, rd₄],
      by rw [wr₅, wr₄]⟩
  · rw [g₅ _ (by decide) (by decide), h4₄]
  · rw [g₅ _ (by decide) (by decide), h5₄]
  · simp only [List.mem_singleton] at hr; subst hr; exact sub_mac (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact sub_mac (by simp)
  · rw [o₅, hY₄, hB₄, ctxCiph_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide)) hRb]

omit L in
/-- `r4` and `r5` the associated data and its length, and `Z` for none. -/
theorem aadLd_ok {s₀ s : State} (hk : Stk w s₀ s) {A : BitVec 32} {al : Nat} (eA : stackArg s₀ 0 = A)
    (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (hal : al < 2 ^ 32) :
    ∃ s₁, runBlock isa [.ldrSp .r4 0, .ldrSp .r5 4, .cmp .r5 (imm 0)] s = some s₁ ∧ s₁.gpr .r4 = A ∧
      s₁.gpr .r5 = BitVec.ofNat 32 al ∧ s₁.z = decide (al = 0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  obtain ⟨i0, v0⟩ := hk.at 0 (by decide) (show 4 * 0 = 0 from rfl)
  obtain ⟨i1, v1⟩ := hk.at 1 (by decide) (show 4 * 1 = 4 from rfl)
  refine ⟨_, by arun [i0, v0, i1, v1], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v0, eA]
  · simp [gpr_setReg, v1, eal]
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, v1, eal, imm]
    rw [z_cmp hal (by decide)]
  · intro r a b; simp [gpr_setReg, a, b]
  · exact ⟨rfl, rfl, rfl, rfl⟩

omit L in
/-- `r4` and `r5` the data and its length. -/
theorem dataLd_ok {s₀ s : State} (hk : Stk w s₀ s) {D : BitVec 32} {n : Nat} (eD : stackArg s₀ 2 = D)
    (en : stackArg s₀ 3 = BitVec.ofNat 32 n) :
    ∃ s₁, runBlock isa [.ldrSp .r4 8, .ldrSp .r5 12] s = some s₁ ∧ s₁.gpr .r4 = D ∧
      s₁.gpr .r5 = BitVec.ofNat 32 n ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  obtain ⟨i2, v2⟩ := hk.at 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨i3, v3⟩ := hk.at 3 (by decide) (show 4 * 3 = 12 from rfl)
  refine ⟨_, by arun [i2, v2, i3, v3], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v2, eD]
  · simp [gpr_setReg, v3, en]
  · intro r a b; simp [gpr_setReg, a, b]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The associated data, formatted and chained. -/
theorem aad_ok {s₀ s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) (hk : Stk w s₀ s) {A : BitVec 32} {al : Nat} (eA : stackArg s₀ 0 = A)
    (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (hal : al < 2 ^ 32) (hA : Buf w sp s A al) :
    WP isa (aad y) s (MacStep k w sp R q1 s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        (adataBlocks (bytesAt s.mem (State.addr A) al)))) := by
  obtain ⟨s₁, run₁, h4₁, h5₁, hz, g₁, k₁⟩ := aadLd_ok hk eA eal hal
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hA₁ := hA.of_eq k₁.rd k₁.wr
  refine WP.ite (decide (al = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : al = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, by rw [k₁.mem]; exact Frame.refl _ _, ?_, k₁.rd, k₁.wr⟩
    simp only [k₁.mem, adataBlocks, length_bytesAt, h0, ↓reduceIte]; rfl
  · have h0 : al ≠ 0 := by simpa using hf
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    refine WP.seq (WP.mono (aadHead_ok L he₁ hR hy hA₁ (by omega) hal h4₁ h5₁) fun s₂ A₂ => ?_)
    have hn1 : headLen al ≤ al := by unfold headLen; omega
    have hT : al - headLen al ≠ 0 → Buf w sp s₂ (A + BitVec.ofNat 32 (headLen al)) (al - headLen al) :=
      fun e => (hA.sub (j := headLen al) (k := al - headLen al) (by omega) (by omega)).of_eq
        (by rw [A₂.rd, k₁.rd]) (by rw [A₂.wr, k₁.wr])
    refine WP.mono (absorbPad_ok L A₂.env hR hy hT (by omega) A₂.r4 A₂.r5) fun s₃ A₃ =>
      ⟨A₃.env, by rw [← k₁.mem]; exact A₂.frame.trans A₃.frame, ?_, by rw [A₃.rd, A₂.rd, k₁.rd],
        by rw [A₃.wr, A₂.wr, k₁.wr]⟩
    have eT : bytesAt s₂.mem (State.addr (A + BitVec.ofNat 32 (headLen al))) (al - headLen al) =
        (bytesAt s.mem (State.addr A) al).drop (headLen al) := by
      rcases Nat.eq_zero_or_pos (al - headLen al) with e | e
      · rw [e, List.drop_eq_nil_of_le (by rw [length_bytesAt]; omega)]; rfl
      · rw [hA.addr (j := headLen al) (by omega), bytesAt_suffix _ _ hn1, buf_kept hA₁ (by omega) A₂.frame,
          k₁.mem]
    rw [A₃.out, A₂.out, eT, ctxCiph_frame A₂.frame (k_macR L (by omega)) hRb, k₁.mem, ← Proof.Cmac.chain_append]
    simp only [adataBlocks, length_bytesAt, h0, ↓reduceIte]

end

end VG.Proof.AesCcm.Arm
