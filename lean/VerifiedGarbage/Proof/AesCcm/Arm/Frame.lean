module

public import VerifiedGarbage.Proof.AesCcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.AesCcm.Arm.Seal
import VerifiedGarbage.Proof.AesCcm.Bytes
import VerifiedGarbage.Proof.AesCcm.Arm.Aad
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Spec.Ccm.Contract
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.AesCcm.Arm.Seal
meta import VerifiedGarbage.Proof.AesCcm.Arm.Aad
public import VerifiedGarbage.Proof.AesGcm.Arm.CTBase
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.Arm.Entry
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTBase
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.Arm.Entry

/-! ### `AesCcm.Arm.CTFn`, which only this module used -/

section

/-! ### `AesCcm.Arm.CTCrypt`, which only this module used -/

section

/-! ### `AesCcm.Arm.CTMac`, which this module and modules that import it used -/

section

/-! ### `AesCcm.Arm.CTBase`, which only this module used -/

section

/-!
# AES-CCM on ARMv7: constant time, the invariants

Untrusted: everything here is checked by Lean. Two runs of `seal` or `open`
with the same public arguments (`onePub`) are related piece by piece by
invariants `CT I` (`Proof.AesGcm.Arm.CT`), whose parameters are the public
values: the pointers, the lengths, the rounds and `W` (`One`, the
arguments, as `Args`, with their values on the stack; `PubArgs`, which the
taint analysis of blocks reading them needs, `CT.args`). Each piece's
correctness lemma, in each run, gives the invariant of the next
(`One.next`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (CT ArgsKeep arg_frame)

/-- The stack arguments `a`, which the code may not write, as public. -/
structure PubArgs (sp : BitVec 32) (a : Nat → BitVec 32) (s : State) : Prop where
  hsp : s.sp = sp
  fit : sp.toNat + 4 * 7 ≤ 2 ^ 32
  wr : ∀ r ∈ s.wr, (args s 7).Disjoint r
  arg : ∀ i < 7, stackArg s i = a i

/-- A block the taint analysis checks from the registers `rs` and the stack
arguments, the same in both runs. -/
theorem CT.args {I : State → Prop} {c : Prog isa} {sp : BitVec 32} {a : Nat → BitVec 32} (rs : List Reg)
    (hI : ∀ s, I s → PubArgs sp a s) (hp : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint rs (4 * 7)) c h).isSome = true) : CT I c := by
  obtain ⟨_, hc⟩ := hc
  refine Proof.AesGcm.Arm.CT.argTaint rs (4 * 7) hp (fun s₁ s₂ h₁ h₂ => (hI _ h₁).hsp.trans (hI _ h₂).hsp.symm)
    (fun s h => ⟨by rw [(hI s h).hsp]; exact (hI s h).fit, fun r hr => ?_⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of ((hI _ h₁).hsp.trans (hI _ h₂).hsp.symm) (by rw [(hI _ h₁).hsp]; exact (hI _ h₁).fit)
      fun i hi => by rw [(hI _ h₁).arg i hi, (hI _ h₂).arg i hi]) hc
  have := (hI s h).wr r hr
  rwa [show Proof.AesCcm.Arm.args s 7 = ⟨State.addr s.sp, 4 * 7⟩ by
    simp only [Proof.AesCcm.Arm.args, Proof.AesGcm.Arm.argAddr_zero]] at this

/-- `a; (b; c)`, from `(a; b); c`. -/
theorem CT.assoc {I : State → Prop} {a b c : Prog isa} (h : CT I (.seq (.seq a b) c)) : CT I (.seq a (.seq b c)) :=
  RelCT.assoc h

/-- `a; (b; (c; (d; e)))`, from `(a; (b; (c; d))); e`. -/
theorem CT.assoc4 {I : State → Prop} {a b c d e : Prog isa} (h : CT I (.seq (.seq a (.seq b (.seq c d))) e)) :
    CT I (.seq a (.seq b (.seq c (.seq d e)))) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
    | seq d₁ f₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
    | seq d₂ f₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) f₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) f₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- The values of the stack arguments. -/
abbrev argVals (A D T w : BitVec 32) (al n tl : Nat) (i : Nat) : BitVec 32 :=
  [A, BitVec.ofNat 32 al, D, BitVec.ofNat 32 n, T, BitVec.ofNat 32 tl, w].getD i 0

/-- One run between the pieces, with its public values: the arguments, the
stack pointer and what the code may write. -/
structure One (k w sp N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  ar : Args s k w N A D R nl al n tl
  sp : s.sp = sp
  wr : ∀ r ∈ s.wr, (args s 7).Disjoint r
  eA : stackArg s 0 = A
  eal : stackArg s 1 = BitVec.ofNat 32 al
  eD : stackArg s 2 = D
  en : stackArg s 3 = BitVec.ofNat 32 n
  eT : stackArg s 4 = T
  etl : stackArg s 5 = BitVec.ofNat 32 tl
  eW : stackArg s 6 = w

namespace One

variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat} {s : State} (h : One k w sp N A D T R nl al n tl s)
include h

theorem pubArgs : PubArgs sp (argVals A D T w al n tl) s where
  hsp := h.sp
  fit := by rw [← h.sp]; exact h.ar.stk.fit
  wr := h.wr
  arg i hi := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega_using [hi]) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.eA
    · exact h.eal
    · exact h.eD
    · exact h.en
    · exact h.eT
    · exact h.etl
    · exact h.eW

/-- After code that writes regions apart from the stack arguments. -/
theorem next' {s' : State} {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, (args s 7).Disjoint r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : One k w sp N A D T R nl al n tl s' := by
  have Ar := h.ar
  have hk : Stk w s s' := Ar.stk.frame hf hd hsp hrd hwr
  have ea : args s' 7 = args s 7 := Proof.AesGcm.Arm.args_sp hsp 7
  have ka : ∀ i < 7, stackArg s' i = stackArg s i := hk.keep.arg
  have sb : blw s'.sp = blw s.sp := by rw [hsp]
  refine ⟨?_, by rw [hsp, h.sp], by rw [hwr, ea]; exact h.wr, by rw [ka 0 (by decide), h.eA],
    by rw [ka 1 (by decide), h.eal], by rw [ka 2 (by decide), h.eD], by rw [ka 3 (by decide), h.en],
    by rw [ka 4 (by decide), h.eT], by rw [ka 5 (by decide), h.etl], by rw [ka 6 (by decide), h.eW]⟩
  have L := Ar.lay
  exact {
    lay := ⟨L.kw, L.ww, by rw [hsp]; exact L.sp16, L.k_w, by rw [sb]; exact L.stk_k, by rw [sb]; exact L.stk_w⟩
    perm := Ar.perm.of_eq hrd hwr
    stk := ⟨ArgsKeep.refl 7 s', by rw [hsp]; exact Ar.stk.fit, by rw [ea, hrd]; exact Ar.stk.rd,
      by rw [ea]; exact Ar.stk.aw⟩
    rounds := Ar.rounds
    nonce := { Ar.nonce.of_eq hrd hwr with stk := by rw [sb]; exact Ar.nonce.stk }
    aad := { Ar.aad.of_eq hrd hwr with stk := by rw [sb]; exact Ar.aad.stk }
    data := ⟨{ Ar.data.buf.of_eq hrd hwr with stk := by rw [sb]; exact Ar.data.buf.stk }, by rw [hwr]; exact Ar.data.wr,
      Ar.data.k⟩
    nd := Ar.nd
    ad := Ar.ad
    da := by rw [ea]; exact Ar.da
    h7 := Ar.h7
    h13 := Ar.h13
    t4 := Ar.t4
    t16 := Ar.t16
    te := Ar.te
    hn := Ar.hn
    n32 := Ar.n32
    al32 := Ar.al32 }

/-- After code that writes regions within `mutR`. -/
theorem next {s' : State} {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ mutR w sp D n, Region.Sub r r') (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : One k w sp N A D T R nl al n tl s' := by
  rw [← h.sp] at hsub
  exact h.next' (hf.sub hsub) (args_mut h.ar) hsp hrd hwr

end One

end VG.Proof.AesCcm.Arm

end

end

/-!
# AES-CCM on ARMv7: the MAC is constant time

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` get the same arguments in both runs (`updBlock_ct`,
`Proof.AesCcm.Arm.upd_rel`); the branches are on the lengths, public; the
blocks between the calls the taint analysis checks.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 copyLoop minLen)
open VG.Proof.AesGcm.Arm (CT copyLoop_ok bytesAt_frame)
open VG.Proof.AesCcm (headLen)

/-- Before a piece chaining the `len` bytes at `P`. -/
def AbsI (k w sp : BitVec 32) (R q1 : Nat) (P : BitVec 32) (len : Nat) (s : State) : Prop :=
  Env k w sp R q1 s ∧ (len ≠ 0 → Buf w sp s P len) ∧ s.gpr .r4 = P ∧ s.gpr .r5 = BitVec.ofNat 32 len

theorem env_eq {k w sp : BitVec 32} {R q1 : Nat} {s₁ s₂ : State} (h₁ : Env k w sp R q1 s₁) (h₂ : Env k w sp R q1 s₂)
    {r : Reg} (hr : r = .r8 ∨ r = .r9 ∨ r = .r10 ∨ r = .r11) : s₁.gpr r = s₂.gpr r := by
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.r8, h₂.r8]
  · rw [h₁.r9, h₂.r9]
  · rw [h₁.r10, h₂.r10]
  · rw [h₁.r11, h₂.r11]

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- `updBlock y`. -/
theorem updBlock_ct {y : Nat} (hy : y = 0 ∨ y = 112) : CT (Env k w sp R q1) (updBlock y) := by
  refine CT.seq (J := fun s => UArgs s k (w + BitVec.ofNat 32 y) (w + BitVec.ofNat 32 32) (w + BitVec.ofNat 32 384)
    R 1 ∧ s.sp = sp) ?_ (fun s he => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11])
        (.block (updArgs y ++ [addI .r3 .r11 bO, .mov .r12 (imm 1)])) h).isSome = true := by
      rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => env_eq h₁ h₂ (by simpa using hr)) hc
  · obtain ⟨s₁, run₁, U, he₁, -, -⟩ := updBlockArgs_ok L he hR hy
    exact WP.of_runBlock ⟨s₁, run₁, U, he₁.sp⟩
  · exact upd_rel fun _ _ ⟨⟨U₁, e₁⟩, ⟨U₂, e₂⟩⟩ => ⟨U₁, U₂, e₁, e₂⟩

/-- The whole blocks of a string. -/
theorem absorbWhole_ct {y : Nat} (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (AbsI k w sp R q1 P len) (absorbWhole y) := by
  refine CT.seq (J := fun s => AbsI k w sp R q1 P len s ∧ s.gpr .r12 = BitVec.ofNat 32 (len / 16) ∧
    s.z = decide (len / 16 = 0)) ?_ (fun s ⟨he, hP, h4, h5⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5])
        (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2, h₂.2.2.2]) hc
  · obtain ⟨s₁, run₁, h12, hz, g₁, k₁⟩ := split16_ok hl h5
    refine WP.of_runBlock ⟨s₁, run₁, ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr,
      fun h => (hP h).of_eq k₁.rd k₁.wr, by rw [g₁ _ (by decide), h4], by rw [g₁ _ (by decide), h5]⟩, h12, hz⟩
  refine CT.ite (decide (len / 16 = 0)) (fun s h => h.2.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : len / 16 ≠ 0 := by simpa using hb
  refine CT.seq (J := fun s => UArgs s k (w + BitVec.ofNat 32 y) P (w + BitVec.ofNat 32 384) R (len / 16) ∧
    s.sp = sp) ?_ (fun s ⟨⟨he, hP, h4, _⟩, h12, _⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r8, .r9, .r10, .r11])
        (.block (updArgs y ++ [.mov .r3 (.reg .r4)])) h).isSome = true := by
      rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · rw [h₁.1.2.2.1, h₂.1.2.2.1]
    · exact env_eq h₁.1.1 h₂.1.1 hr
  · obtain ⟨s₂, run₂, U, he₂, -, -⟩ := absArgs_ok L he hR hy ((hP (by omega_using [h0])).take (Nat.mul_div_le len 16))
      (by omega_using [hl]) h4 h12
    exact WP.of_runBlock ⟨s₂, run₂, U, he₂.sp⟩
  · exact upd_rel fun _ _ ⟨⟨U₁, e₁⟩, ⟨U₂, e₂⟩⟩ => ⟨U₁, U₂, e₁, e₂⟩

/-- The last bytes of a string. -/
theorem absorbTail_ct {y : Nat} (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (AbsI k w sp R q1 P len) (absorbTail y) := by
  refine CT.seq (J := fun s => AbsI k w sp R q1 P len s ∧ s.gpr .r6 = BitVec.ofNat 32 (len % 16) ∧
    s.z = decide (len % 16 = 0)) ?_ (fun s ⟨he, hP, h4, h5⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5])
        (.block [.dp .and .r6 .r5 (imm 15), .cmp .r6 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2, h₂.2.2.2]) hc
  · obtain ⟨s₁, run₁, h6, hz, g₁, k₁⟩ := split15_ok hl h5
    refine WP.of_runBlock ⟨s₁, run₁, ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr,
      fun h => (hP h).of_eq k₁.rd k₁.wr, by rw [g₁ _ (by decide), h4], by rw [g₁ _ (by decide), h5]⟩, h6, hz⟩
  refine CT.ite (decide (len % 16 = 0)) (fun s h => h.2.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : len % 16 ≠ 0 := by simpa using hb
  refine CT.assoc (CT.seq (J := Env k w sp R q1) ?_ (fun _ ⟨⟨he, hP, h4, h5⟩, h6, _⟩ => ?_) (updBlock_ct L hR hy))
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r8, .r9, .r10, .r11])
        (.seq (.block (zero16 bO ++ [.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4), addI .r2 .r11 bO,
          .mov .r3 (.reg .r6)])) copyLoop) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | hr
    · rw [h₁.1.2.2.1, h₂.1.2.2.1]
    · rw [h₁.1.2.2.2, h₂.1.2.2.2]
    · rw [h₁.2.1, h₂.2.1]
    · exact env_eq h₁.1.1 h₂.1.1 hr
  · obtain ⟨s₃, run₃, -, lp, he₃, -, -, -, -⟩ := tailPre_ok L he hP hl h0 h4 h5 h6
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    exact WP.mono (copyLoop_ok s₃ lp) fun s₄ ⟨_, lo⟩ => he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) lo.sp lo.rd lo.wr

/-- A string padded. -/
theorem absorbPad_ct {y : Nat} (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (AbsI k w sp R q1 P len) (absorbPad y) :=
  CT.seq (absorbWhole_ct L hR hy hl) (fun _ ⟨he, hP, h4, h5⟩ =>
    WP.mono (absorbWhole_ok L he hR hy hP hl h4 h5) fun _ A => ⟨A.env, fun h => (hP h).of_eq A.rd A.wr, A.r4, A.r5⟩)
    (absorbTail_ct L hR hy hl)

/-- The first block of the associated data. -/
theorem aadHead_ct {y : Nat} (hy : y = 0 ∨ y = 112) {A : BitVec 32} {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 32) :
    CT (fun s => Env k w sp R q1 s ∧ Buf w sp s A a ∧ s.gpr .r4 = A ∧ s.gpr .r5 = BitVec.ofNat 32 a)
      (aadHead y) := by
  refine CT.assoc4 (CT.seq (J := Env k w sp R q1) ?_ (fun s ⟨he, hA, h4, h5⟩ =>
    WP.mono (aadHeadPre_ok L he hA ha0 ha h4 h5) fun _ h => h.1) (updBlock_ct L hR hy))
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r8, .r9, .r10, .r11])
      (.seq header (.seq minLen (.seq (.block [.mov .r1 (.reg .r4), addI .r2 .r11 bO, .dp .add .r2 .r2 (.reg .r6),
        .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)]) copyLoop))) h).isSome = true :=
    ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | hr
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]
  · exact env_eq h₁.1 h₂.1 hr

end

/-- Between the pieces of the MAC: one run, the environment with `q − 1` in
`r10`, and `Ctr₀` at `W + 48`. -/
def MacI (k w sp N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop :=
  One k w sp N A D T R nl al n tl s ∧ Env k w sp R (14 - nl) s ∧
    ∃ nonce : List Byte, nonce.length = nl ∧
      bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

section
variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat}

theorem c0_macR {y : Nat} (hy : y = 0 ∨ y = 112) (L : Lay k w sp) {m m' : Mem} (hf : Frame (macR w sp y) m m') :
    bytesAt m' (State.addr w + BitVec.ofNat 64 48) 16 = bytesAt m (State.addr w + BitVec.ofNat 64 48) 16 :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) (by decide)

/-- After a piece of the MAC. -/
theorem MacI.next {y : Nat} (hy : y = 0 ∨ y = 112) {s s' : State} (h : MacI k w sp N A D T R nl al n tl s)
    {Y : List Byte} (M : MacStep k w sp R (14 - nl) s y Y s') : MacI k w sp N A D T R nl al n tl s' := by
  obtain ⟨o, he, nonce, hl, hc⟩ := h
  have L : Lay k w sp := by have := o.ar.lay; rwa [o.sp] at this
  exact ⟨o.next M.frame (macR_mut hy) (by rw [M.env.sp, he.sp]) M.rd M.wr, M.env, nonce, hl,
    by rw [c0_macR hy L M.frame, hc]⟩

variable (L : Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hal : al < 2 ^ 32)
include L hR hal

/-- The associated data. -/
theorem aad_ct {y : Nat} (hy : y = 0 ∨ y = 112) : CT (MacI k w sp N A D T R nl al n tl) (aad y) := by
  refine CT.seq (J := fun s => MacI k w sp N A D T R nl al n tl s ∧ s.gpr .r4 = A ∧
    s.gpr .r5 = BitVec.ofNat 32 al ∧ s.z = decide (al = 0)) ?_ (fun s h => ?_) ?_
  · exact CT.args [] (fun s h => h.1.pubArgs) (fun _ _ _ _ _ h => by simp at h) ⟨_, by taint_decide⟩
  · obtain ⟨s₁, run₁, h4, h5, hz, g₁, k₁⟩ := aadLd_ok h.1.ar.stk h.1.eA h.1.eal hal
    have he₁ := h.2.1.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
    refine WP.of_runBlock ⟨s₁, run₁, ⟨h.1.next (rs := []) (by rw [k₁.mem]; exact Frame.refl _ _)
      (fun _ h => by simp at h) k₁.sp k₁.rd k₁.wr, he₁, ?_⟩, h4, h5, hz⟩
    obtain ⟨nonce, hl, hc⟩ := h.2.2
    exact ⟨nonce, hl, by rw [k₁.mem]; exact hc⟩
  refine CT.ite (decide (al = 0)) (fun s h => h.2.2.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : al ≠ 0 := by simpa using hb
  have hn1 : headLen al ≤ al := by unfold headLen; omega_using []
  have bufA : ∀ {s : State}, MacI k w sp N A D T R nl al n tl s → Buf w sp s A al := fun h => by
    have := h.1.ar.aad; rwa [h.1.sp] at this
  refine CT.seq (J := AbsI k w sp R (14 - nl) (A + BitVec.ofNat 32 (headLen al)) (al - headLen al))
    ((aadHead_ct L hR hy (by omega_using [h0]) hal).mono fun s ⟨h, h4, h5, _⟩ => ⟨h.2.1, bufA h, h4, h5⟩)
    (fun s ⟨h, h4, h5, _⟩ => WP.mono (aadHead_ok L h.2.1 hR hy (bufA h) (by omega_using [h0]) hal h4 h5) fun _ A₂ =>
      ⟨A₂.env, fun e => ((bufA h).sub (j := headLen al) (k := al - headLen al) (by omega_using [hn1]) (by omega_using [e])).of_eq
        A₂.rd A₂.wr, A₂.r4, A₂.r5⟩) (absorbPad_ct L hR hy (by omega_using [hal]))

/-- `B₀`. -/
theorem b0_ct {y : Nat} (hy : y = 0 ∨ y = 112) : CT (MacI k w sp N A D T R nl al n tl) (b0 y) := by
  refine CT.assoc (CT.seq (J := Env k w sp R (14 - nl)) ?_ (fun s ⟨o, he, nonce, hl, hc⟩ => ?_) (updBlock_ct L hR hy))
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint [.r8, .r9, .r10, .r11] (4 * 7))
        (.seq flagsCode (.block (b0Block y))) h).isSome = true := by
      rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.args _ (fun s h => h.1.pubArgs) (fun s₁ s₂ h₁ h₂ r hr => env_eq h₁.2.1 h₂.2.1 (by simpa using hr)) ⟨_, hc⟩
  · have Ar := o.ar
    exact WP.mono (b0Pre_ok L he Ar.stk o.etl o.eal o.en hl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te hal Ar.n32 Ar.hn hc hy)
      fun _ h => h.1

/-- The MAC. -/
theorem mac_ct {y : Nat} (hy : y = 0 ∨ y = 112) (hn : n < 2 ^ 32) : CT (MacI k w sp N A D T R nl al n tl) (mac y) := by
  refine CT.seq (J := MacI k w sp N A D T R nl al n tl) (b0_ct L hR hal hy) (fun s ⟨o, he, nonce, hl, hc⟩ => ?_) ?_
  · have Ar := o.ar
    exact WP.mono (b0_ok L he Ar.stk hR o.etl o.eal o.en hl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te hal Ar.n32 Ar.hn hc hy)
      fun _ M => MacI.next hy ⟨o, he, nonce, hl, hc⟩ M
  refine CT.seq (J := MacI k w sp N A D T R nl al n tl) (aad_ct L hR hal hy) (fun s h => ?_) ?_
  · obtain ⟨o, he, _⟩ := id h
    have bufA : Buf w sp s A al := by have := o.ar.aad; rwa [o.sp] at this
    exact WP.mono (aad_ok L he hR hy o.ar.stk o.eA o.eal hal bufA) fun _ M => MacI.next hy h M
  refine CT.seq (J := AbsI k w sp R (14 - nl) D n) ?_ (fun s ⟨o, he, _⟩ => ?_) (absorbPad_ct L hR hy hn)
  · exact CT.args [] (fun s h => h.1.pubArgs) (fun _ _ _ _ _ h => by simp at h) ⟨_, by taint_decide⟩
  · obtain ⟨s₁, run₁, h4, h5, g₁, k₁⟩ := dataLd_ok o.ar.stk o.eD o.en
    have bufD : Buf w sp s D n := by have := o.ar.data.buf; rwa [o.sp] at this
    exact WP.of_runBlock ⟨s₁, run₁, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr,
      fun _ => bufD.of_eq k₁.rd k₁.wr, h4, h5⟩

end

end VG.Proof.AesCcm.Arm

end

end

/-!
# AES-CCM on ARMv7: the tag and counter mode are constant time

Untrusted: everything here is checked by Lean. The calls of `vg_aes_ctr32`
get the same arguments in both runs (`Proof.AesGcm.Arm.CT.ctr`); the
branches are on the length of the data.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 xorLoop ctrFrame)
open VG.Proof.AesGcm.Arm (CT bytesAt_frame ctr_call CtrCall)

section
variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat}

/-- After code that writes `rs`, within what the pieces write and apart from `Ctr₀`. -/
theorem MacI.of {s s' : State} (h : MacI k w sp N A D T R nl al n tl s) (he : Env k w sp R (14 - nl) s')
    {rs : List Region} (hf : Frame rs s.mem s'.mem) (hsub : ∀ r ∈ rs, ∃ r' ∈ mutR w sp D n, Region.Sub r r')
    (hd : ∀ r ∈ rs, (⟨State.addr w + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : MacI k w sp N A D T R nl al n tl s' := by
  obtain ⟨o, he₀, nonce, hl, hc⟩ := h
  exact ⟨o.next hf hsub (by rw [he.sp, he₀.sp]) hrd hwr, he, nonce, hl, by rw [bytesAt_frame hf hd (by decide), hc]⟩

variable (L : Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- `tag y`. -/
theorem tag_ct {y : Nat} (hy : y = 0 ∨ y = 112) : CT (MacI k w sp N A D T R nl al n tl) (tag y) := by
  refine CT.seq (J := fun s => CtrCall s k (w + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 y)
    (w + BitVec.ofNat 32 384) R 1 ∧ s.sp = sp) ?_ (fun s ⟨o, he, nonce, hl, hc⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11])
        (.block ([.mov .r0 (imm 0)] ++ ctrAt ++ ctrArgs ++ [addI .r3 .r11 y, .mov .r12 (imm 1)])) h).isSome = true := by
      rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => env_eq h₁.2.1 h₂.2.1 (by simpa using hr)) hc
  · obtain ⟨s₃, run₃, C, he₃, -⟩ := tagArgs_ok L he hR (nonce := nonce) (by rw [hl]; exact o.ar.h7)
      (by rw [hl]; exact o.ar.h13) hc hy
    exact WP.of_runBlock ⟨s₃, run₃, C, he₃.sp⟩
  · exact CT.ctr fun _ _ ⟨C₁, e₁⟩ ⟨C₂, e₂⟩ => ⟨_, _, _, _, _, _, C₁, C₂, e₁.trans e₂.symm⟩

/-- Before counter mode. -/
def CrI (k w sp : BitVec 32) (R nl : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop :=
  Env k w sp R (14 - nl) s ∧ (∃ nonce : List Byte, nonce.length = nl ∧
    bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) ∧
  Dat k w sp s D n ∧ s.gpr .r4 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n

omit L hR in
theorem CrI.keep {s s' : State} (h : CrI k w sp R nl D n s) (hg : ∀ r, r ≠ .r12 → r ≠ .r6 → s'.gpr r = s.gpr r)
    (hk : Proof.AesGcm.Arm.Keeps s s') : CrI k w sp R nl D n s' := by
  obtain ⟨he, ⟨nonce, hl, hc⟩, hD, h4, h5⟩ := h
  exact ⟨he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hk.sp hk.rd hk.wr,
    ⟨nonce, hl, by rw [hk.mem]; exact hc⟩, hD.of_eq hk.rd hk.wr, by rw [hg _ (by decide) (by decide), h4],
    by rw [hg _ (by decide) (by decide), h5]⟩

/-- The whole blocks of the data. -/
theorem ctrWhole_ct (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn4 : n < 2 ^ 32) : CT (CrI k w sp R nl D n) ctrWhole := by
  refine CT.seq (J := fun s => CrI k w sp R nl D n s ∧ s.gpr .r12 = BitVec.ofNat 32 (n / 16) ∧
    s.z = decide (n / 16 = 0)) ?_ (fun s h => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5])
        (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.2, h₂.2.2.2.2]) hc
  · obtain ⟨s₁, run₁, h12, hz, g₁, k₁⟩ := split16_ok hn4 h.2.2.2.2
    exact WP.of_runBlock ⟨s₁, run₁, h.keep (fun r a _ => g₁ r a) k₁, h12, hz⟩
  refine CT.ite (decide (n / 16 = 0)) (fun s h => h.2.2) (fun _ => CT.skip) fun _ => ?_
  refine CT.seq (J := fun s => CtrCall s k (w + BitVec.ofNat 32 64) D (w + BitVec.ofNat 32 384) R (n / 16) ∧
    s.sp = sp) ?_ (fun s ⟨⟨he, ⟨nonce, hl, hc⟩, hD, h4, _⟩, h12, _⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r8, .r9, .r10, .r11])
        (.block ([.mov .r0 (imm 1)] ++ ctrAt ++ ctrArgs ++ [.mov .r3 (.reg .r4)])) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · rw [h₁.1.2.2.2.1, h₂.1.2.2.2.1]
    · exact env_eq h₁.1.1 h₂.1.1 hr
  · obtain ⟨s₄, run₄, C, he₄, -⟩ := ctrWholeArgs_ok L he hR (nonce := nonce) (by omega_using [h7, hl]) (by omega_using [h13, hl]) hc hD h4 h12
    exact WP.of_runBlock ⟨s₄, run₄, C, he₄.sp⟩
  · exact CT.ctr fun _ _ ⟨C₁, e₁⟩ ⟨C₂, e₂⟩ => ⟨_, _, _, _, _, _, C₁, C₂, e₁.trans e₂.symm⟩

/-- The last bytes of the data. -/
theorem ctrTail_ct (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn : n < 256 ^ (15 - nl)) (hn4 : n < 2 ^ 32) :
    CT (CrI k w sp R nl D n) ctrTail := by
  refine CT.seq (J := fun s => CrI k w sp R nl D n s ∧ s.gpr .r6 = BitVec.ofNat 32 (n % 16) ∧
    s.z = decide (n % 16 = 0)) ?_ (fun s h => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5])
        (.block [.dp .and .r6 .r5 (imm 15), .cmp .r6 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.2, h₂.2.2.2.2]) hc
  · obtain ⟨s₁, run₁, h6, hz, g₁, k₁⟩ := split15_ok hn4 h.2.2.2.2
    exact WP.of_runBlock ⟨s₁, run₁, h.keep (fun r _ b => g₁ r b) k₁, h6, hz⟩
  refine CT.ite (decide (n % 16 = 0)) (fun s h => h.2.2) (fun _ => CT.skip) fun _ => ?_
  let J₃ : State → Prop := fun s => Env k w sp R (14 - nl) s ∧ s.gpr .r4 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n ∧
    s.gpr .r6 = BitVec.ofNat 32 (n % 16)
  refine CT.seq (J := fun s => CtrCall s k (w + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 80)
      (w + BitVec.ofNat 32 384) R 1 ∧ J₃ s) ?_ (fun s ⟨⟨he, ⟨nonce, hl, hc⟩, _, h4, h5⟩, h6, _⟩ => ?_)
    (CT.seq (J := J₃) ?_ (fun s ⟨C, he, h4, h5, h6⟩ => WP.mono (ctr_call C) fun s' P =>
      ⟨he.of_saved P.saved P.sp P.rd P.wr, by rw [P.saved _ (by decide) (by decide), h4],
        by rw [P.saved _ (by decide) (by decide), h5], by rw [P.saved _ (by decide) (by decide), h6]⟩) ?_)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5, .r8, .r9, .r10, .r11])
        (.block (zero16 ksO ++ [.mov .r0 (.shifted .r5 .lsr 4), addI .r0 .r0 1] ++ ctrAt ++ ctrArgs ++
          [addI .r3 .r11 ksO, .mov .r12 (imm 1)])) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · rw [h₁.1.2.2.2.2, h₂.1.2.2.2.2]
    · exact env_eq h₁.1.1 h₂.1.1 hr
  · obtain ⟨s₅, run₅, C, he₅, g₅, -⟩ := ctrTailArgs_ok L he hR (nonce := nonce) (by omega_using [h7, hl]) (by omega_using [h13, hl]) hc
      (by rw [hl]; exact hn) hn4 h5
    exact WP.of_runBlock ⟨s₅, run₅, C, he₅, by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h4], by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h5],
      by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h6]⟩
  · exact CT.ctr fun _ _ ⟨C₁, e₁⟩ ⟨C₂, e₂⟩ => ⟨_, _, _, _, _, _, C₁, C₂, e₁.1.sp.trans e₂.1.sp.symm⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r8, .r9, .r10, .r11])
        (.seq (.block [addI .r1 .r11 ksO, .dp .sub .r2 .r5 (.reg .r6), .dp .add .r2 .r2 (.reg .r4),
          .mov .r3 (.reg .r6)]) xorLoop) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | hr
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · exact env_eq h₁.1 h₂.1 hr

end

end VG.Proof.AesCcm.Arm

end

end

/-!
# AES-CCM on ARMv7: `vg_aes_ccm_seal` and `vg_aes_ccm_open` are constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments (`onePub`) both satisfy the invariants of the same
public values (`entryI`), piece by piece. `open` compares the tags and masks
the data without a branch: whether the tag is right, in `r0` and `r7`, is
never branched on nor used as an address.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI recv cmp uO restore)
open VG.Proof.AesGcm.Arm (CT bytesAt_frame savedR)
open VG.Proof.AesCcm (length_bytesAt)

section
variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat} (L : Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- Counter mode. -/
theorem ctr_ct (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn : n < 256 ^ (15 - nl)) (hn4 : n < 2 ^ 32) :
    CT (MacI k w sp N A D T R nl al n tl) ctr := by
  refine CT.seq (J := CrI k w sp R nl D n) ?_ (fun s ⟨o, he, c0⟩ => ?_) ?_
  · exact CT.args [] (fun s h => h.1.pubArgs) (fun _ _ _ _ _ h => by simp at h) ⟨_, by taint_decide⟩
  · obtain ⟨s₁, run₁, h4, h5, g₁, k₁⟩ := dataLd_ok o.ar.stk o.eD o.en
    have hD : Dat k w sp s D n := by have := o.ar.data; rwa [o.sp] at this
    obtain ⟨nonce, hl, hc⟩ := c0
    exact WP.of_runBlock ⟨s₁, run₁, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr,
      ⟨nonce, hl, by rw [k₁.mem]; exact hc⟩, hD.of_eq k₁.rd k₁.wr, h4, h5⟩
  refine CT.seq (J := CrI k w sp R nl D n) (ctrWhole_ct L hR h7 h13 hn4) (fun s ⟨he, ⟨nonce, hl, hc⟩, hD, h4, h5⟩ => ?_)
    (ctrTail_ct L hR h7 h13 hn hn4)
  refine WP.mono (ctrWhole_ok L he hR (nonce := nonce) (by omega_using [h7, hl]) (by omega_using [h13, hl]) hc hD (by rw [hl]; exact hn) hn4 h4 h5)
    fun s' ⟨he', rd, wr, g, f, _⟩ => ⟨he', ⟨nonce, hl, ?_⟩, hD.of_eq rd wr, by rw [g _ (by decide) (by decide), h4],
      by rw [g _ (by decide) (by decide), h5]⟩
  rw [bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact ((hD.buf.w.sub_left (Region.sub_prefix (Nat.mul_div_le n 16))).sub_right
        (Lay.wSub (by decide))).symm) (by decide), hc]

end

/-- At the entry: one run, and the registers holding the key schedule, the
rounds and the nonce. -/
def EntI (k w sp N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop :=
  One k w sp N A D T R nl al n tl s ∧ s.gpr .r0 = k ∧ s.gpr .r1 = BitVec.ofNat 32 R ∧ s.gpr .r2 = N ∧
    s.gpr .r3 = BitVec.ofNat 32 nl

/-- After the entry. -/
def AftI (k w sp N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop :=
  One k w sp N A D T R nl al n tl s ∧ Env k w sp R (s.gpr .r10).toNat s ∧ s.gpr .r2 = N ∧
    s.gpr .r3 = BitVec.ofNat 32 nl

section
variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat} (L : Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)

/-- The entry. -/
theorem entry_ct : CT (EntI k w sp N A D T R nl al n tl) (.block entry) :=
  CT.args [.r0, .r1, .r2, .r3] (fun s h => h.1.pubArgs) (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2, h₂.2.2.2.2]) ⟨_, by taint_decide⟩

theorem entry_wpI {s : State} (h : EntI k w sp N A D T R nl al n tl s) :
    WP isa (.block entry) s (AftI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, h0, h1, h2, h3⟩ := h
  refine WP.mono (entry_wp o.ar h0 h1 o.eW) fun s₁ ⟨he₁, g₁, rd₁, wr₁, _, f₁⟩ => ?_
  have hsp : s₁.sp = s.sp := he₁.sp
  rw [o.sp] at he₁
  refine ⟨o.next' f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact o.ar.stk.aw.sub_right (Lay.wSub (by decide)))
    hsp rd₁ wr₁, he₁, by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h2],
    by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h3]⟩

/-- `Ctr₀`. -/
theorem ctrs_ct : CT (AftI k w sp N A D T R nl al n tl) ctrs :=
  CT.args [.r2, .r3, .r8, .r9, .r11] (fun s h => h.1.pubArgs) (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · rw [h₁.2.1.r8, h₂.2.1.r8]
    · rw [h₁.2.1.r9, h₂.2.1.r9]
    · rw [h₁.2.1.r11, h₂.2.1.r11]) ⟨_, by taint_decide⟩

include L in
theorem ctrs_wpI {s : State} (h : AftI k w sp N A D T R nl al n tl s) :
    WP isa ctrs s (MacI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, he, h2, h3⟩ := h
  have hN : Buf w sp s N nl := by have := o.ar.nonce; rwa [o.sp] at this
  refine WP.mono (ctrs_ok L he hN h2 h3 o.ar.h7 o.ar.h13) fun s₂ ⟨c₂, h10₂, f₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
  refine ⟨o.next f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact w_mut (.inl (by decide))) sp₂ rd₂ wr₂,
    ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he.r8],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he.r9], h10₂,
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he.r11],
      by rw [sp₂, he.sp], he.perm.of_eq rd₂ wr₂⟩, _, length_bytesAt _ _ _, c₂⟩

include L hR

theorem mac_wpI {y : Nat} (hy : y = 0 ∨ y = 112) {s : State} (h : MacI k w sp N A D T R nl al n tl s) :
    WP isa (mac y) s (MacI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, he, nonce, hl, hc⟩ := id h
  have Ar := o.ar
  have hA : Buf w sp s A al := by have := Ar.aad; rwa [o.sp] at this
  have hD : Buf w sp s D n := by have := Ar.data.buf; rwa [o.sp] at this
  exact WP.mono (mac_ok L he Ar.stk o.sp hR o.eA o.eal o.eD o.en o.etl hl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32
    Ar.n32 Ar.hn hc hy hA hD) fun _ M => MacI.next hy h M

theorem tag_wpI {y : Nat} (hy : y = 0 ∨ y = 112) {s : State} (h : MacI k w sp N A D T R nl al n tl s) :
    WP isa (tag y) s (MacI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, he, nonce, hl, hc⟩ := id h
  refine WP.mono (tag_ok L he hR (nonce := nonce) (by rw [hl]; exact o.ar.h7) (by rw [hl]; exact o.ar.h13) hc hy)
    fun s' ⟨he', rd, wr, _, f, _⟩ => h.of he' f (fun r hr => ?_) (fun r hr => ?_) rd wr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact w_mut (.inl (by decide))
    · exact w_mut (.inl (by omega_using [hy]))
    · exact w_mut (.inr ⟨by decide, by decide⟩)
    · exact blw_mut
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm

theorem ctr_wpI {s : State} (h : MacI k w sp N A D T R nl al n tl s) :
    WP isa ctr s (MacI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, he, nonce, hl, hc⟩ := id h
  have hD : Dat k w sp s D n := by have := o.ar.data; rwa [o.sp] at this
  refine WP.mono (ctr_ok L he o.ar.stk hR (nonce := nonce) (by rw [hl]; exact o.ar.h7) (by rw [hl]; exact o.ar.h13)
    hc o.eD o.en hD (by rw [hl]; exact o.ar.hn) o.ar.n32) fun s' ⟨he', rd, wr, _, f, _⟩ =>
      h.of he' f ctrR_mut (fun r hr => ?_) rd wr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm
  · exact (hD.buf.w.sub_right (Lay.wSub (by decide))).symm

/-- `vg_aes_ccm_seal`, from the entry invariant. -/
theorem seal_ctI (hal : al < 2 ^ 32) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn : n < 256 ^ (15 - nl)) (hn4 : n < 2 ^ 32) :
    CT (EntI k w sp N A D T R nl al n tl) «seal» := by
  refine CT.seq entry_ct (fun _ h => entry_wpI h) ?_
  refine CT.seq ctrs_ct (fun _ h => ctrs_wpI L h) ?_
  refine CT.seq (mac_ct L hR hal (.inl rfl) hn4) (fun _ h => mac_wpI L hR (.inl rfl) h) ?_
  refine CT.seq (tag_ct L hR (.inl rfl)) (fun _ h => tag_wpI L hR (.inl rfl) h) ?_
  refine CT.seq (ctr_ct L hR h7 h13 hn hn4) (fun _ h => ctr_wpI L hR h) ?_
  -- The copy of the tag to `tag`, a public stack argument, and the exit.
  exact CT.args [.r11] (fun s h => h.1.pubArgs) (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1.r11, h₂.2.1.r11]) ⟨_, by taint_decide⟩

/-- `vg_aes_ccm_open`, from the entry invariant. -/
theorem open_ctI (hal : al < 2 ^ 32) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn : n < 256 ^ (15 - nl)) (hn4 : n < 2 ^ 32) :
    CT (EntI k w sp N A D T R nl al n tl) «open» := by
  refine CT.seq entry_ct (fun _ h => entry_wpI h) ?_
  refine CT.seq ctrs_ct (fun _ h => ctrs_wpI L h) ?_
  refine CT.seq (ctr_ct L hR h7 h13 hn hn4) (fun _ h => ctr_wpI L hR h) ?_
  refine CT.seq (mac_ct L hR hal (.inr rfl) hn4) (fun _ h => mac_wpI L hR (.inr rfl) h) ?_
  refine CT.seq (tag_ct L hR (.inr rfl)) (fun _ h => tag_wpI L hR (.inr rfl) h) ?_
  exact CT.args [.r8, .r9, .r10, .r11] (fun s h => h.1.pubArgs)
    (fun s₁ s₂ h₁ h₂ r hr => env_eq h₁.2.1 h₂.2.1 (by simpa using hr)) ⟨_, by taint_decide⟩

end

end VG.Proof.AesCcm.Arm

end

end

/-! ### `AesCcm.Arm.Verified`, which only this module used -/

section

/-! ### `AesCcm.Arm.Open`, which only this module used -/

section

/-!
# AES-CCM on ARMv7: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is the entry, `Ctr₀`,
counter mode over the data (which decrypts it), the encrypted MAC of the
plaintext at `W + 112`, then the comparison of its first `t` bytes with the
received tag at `tag` (`recv`, `cmp`), the mask of the data and `restore`
(`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.Arm (imm recv cmp uO restore)
open VG.Proof.AesGcm.Arm (savedR SavedAt restore_ok covers_left bytesAt_frame Keeps)
open VG.Proof.AesCcm (ctxCiph_frame length_bytesAt xorFrom length_xorFrom crypt_eq take_xorFrom_zero mac_eq
  BlockCipher bytesAt_prefix bytesAt_writeBytes_base cryptTag_eq_iff)

/-- Whether the received tag `tag` is that of the decrypted `ct`. -/
abbrev tagOk (ciph : Spec.Ccm.Cipher) (tl : Nat) (nonce ct aad tag : List Byte) : Bool :=
  decide (Spec.Ccm.cryptTag ciph tl nonce tag = Spec.Ccm.mac ciph tl nonce aad (Spec.Ccm.crypt ciph nonce ct))

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' {s₀ : State} {k w N A D T : BitVec 32} {R nl al n tl : Nat} (Ar : Args s₀ k w N A D R nl al n tl)
    (Tb : TagB w s₀.sp D n T tl) (hTr : Covers [⟨State.addr T, tl⟩] (s₀.rd ++ s₀.wr)) (h0 : s₀.gpr .r0 = k) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 R) (h2 : s₀.gpr .r2 = N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 nl) (eA : stackArg s₀ 0 = A) (eal : stackArg s₀ 1 = BitVec.ofNat 32 al)
    (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n) (eT : stackArg s₀ 4 = T)
    (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) (eW : stackArg s₀ 6 = w) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧
      s'.gpr .r0 = (if tagOk (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
        (bytesAt s₀.mem (State.addr D) n) (bytesAt s₀.mem (State.addr A) al) (bytesAt s₀.mem (State.addr T) tl)
        then 1 else 0) ∧
      bytesAt s'.mem (State.addr D) n =
        (if tagOk (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
          (bytesAt s₀.mem (State.addr D) n) (bytesAt s₀.mem (State.addr A) al) (bytesAt s₀.mem (State.addr T) tl)
          then Spec.Ccm.crypt (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) (bytesAt s₀.mem (State.addr N) nl)
            (bytesAt s₀.mem (State.addr D) n)
          else zeros n) := by
  have L := Ar.lay
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain hsavedK : (⟨State.addr k, 240⟩ : Region).Disjoint (savedR w) := L.k_w' (by decide)
  have t16 := Ar.t16
  have t4 := Ar.t4
  refine WP.seq (WP.mono (entry_wp Ar h0 h1 eW) fun s₁ ⟨he₁, g₁, rd₁, wr₁, sv₁, f₁⟩ => ?_)
  obtain hent : ∀ {P : BitVec 32} {len : Nat}, Buf w s₀.sp s₀ P len →
      bytesAt s₁.mem (State.addr P) len = bytesAt s₀.mem (State.addr P) len := fun hP =>
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_arith)
  obtain hK₁ : Spec.Ccm.ctxCiph s₁.mem (State.addr k) R = Spec.Ccm.ctxCiph s₀.mem (State.addr k) R :=
    ctxCiph_frame f₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsavedK) hRb
  obtain hk₁ : Stk w s₀ s₁ := Ar.stk.frame f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Ar.stk.aw.sub_right (Lay.wSub (by decide)))
    he₁.sp rd₁ wr₁
  -- `Ctr₀`.
  obtain hN₁ := Ar.nonce.of_eq rd₁ wr₁
  refine WP.seq (WP.mono (ctrs_ok L he₁ hN₁ (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h2])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h3]) Ar.h7 Ar.h13)
    fun s₂ ⟨c₂, h10₂, f₂, g₂, rd₂, wr₂, sp₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  obtain he₂ : Env k w s₀.sp R (14 - nl) s₂ :=
    ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r8],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r9], h10₂,
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r11],
      by rw [sp₂, he₁.sp], he₁.perm.of_eq rd₂ wr₂⟩
  obtain f₂' : Frame (wR w s₀.sp) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact w_wR (.inl (by decide))
  obtain F₂ : Frame (mutR w s₀.sp D n) s₁.mem s₂.mem := f₂'.sub wR_mut
  obtain hk₂ := hk₁.frame F₂ (args_mut Ar) sp₂ rd₂ wr₂
  obtain rd₁₂ : s₂.rd = s₀.rd := rd₂.trans rd₁
  obtain wr₁₂ : s₂.wr = s₀.wr := wr₂.trans wr₁
  obtain hnl := length_bytesAt s₀.mem (State.addr N) nl
  obtain h7 : 7 ≤ (bytesAt s₀.mem (State.addr N) nl).length := by rw [hnl]; exact Ar.h7
  obtain h13 : (bytesAt s₀.mem (State.addr N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  -- Counter mode: the plaintext.
  refine WP.seq (WP.mono (ctr_ok L he₂ hk₂ Ar.rounds h7 h13 c₂ eD en (Ar.data.of_eq rd₁₂ wr₁₂)
    (by rw [hnl]; exact Ar.hn) Ar.n32) fun s₃ ⟨he₃, rd₃, wr₃, _, f₃, o₃⟩ => ?_)
  obtain F₃ : Frame (mutR w s₀.sp D n) s₁.mem s₃.mem := F₂.trans (f₃.sub ctrR_mut)
  obtain rd₁₃ : s₃.rd = s₀.rd := rd₃.trans rd₁₂
  obtain wr₁₃ : s₃.wr = s₀.wr := wr₃.trans wr₁₂
  obtain hk₃ := hk₁.frame F₃ (args_mut Ar) (by rw [he₃.sp, he₁.sp]) (by rw [rd₁₃, rd₁]) (by rw [wr₁₃, wr₁])
  obtain c₃ : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 48) 16 =
      Spec.Ccm.ctrBlock (bytesAt s₀.mem (State.addr N) nl) 0 := by
    rw [bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm
      · exact (Ar.data.buf.w.sub_right (Lay.wSub (by decide))).symm) (by decide), c₂]
  obtain a₃ : bytesAt s₃.mem (State.addr A) al = bytesAt s₀.mem (State.addr A) al := by
    rw [bytesAt_frame F₃ (aad_mut Ar) (by have := Ar.aad.lt; omega_arith), hent Ar.aad]
  -- The MAC of the plaintext, encrypted, at `W + 112`.
  refine WP.seq (WP.mono (mac_ok L he₃ hk₃ rfl Ar.rounds eA eal eD en etl hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.al32 Ar.n32 Ar.hn c₃ (y := uO) (.inr rfl) (Ar.aad.of_eq rd₁₃ wr₁₃) (Ar.data.buf.of_eq rd₁₃ wr₁₃))
    fun s₄ M => ?_)
  obtain c₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 48) 16 =
      Spec.Ccm.ctrBlock (bytesAt s₀.mem (State.addr N) nl) 0 := by
    rw [bytesAt_frame M.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), c₃]
  refine WP.seq (WP.mono (tag_ok L M.env Ar.rounds h7 h13 c₄ (y := uO) (.inr rfl))
    fun s₅ ⟨he₅, rd₅, wr₅, g₅, f₅, o₅⟩ => ?_)
  obtain f₅' : Frame (wR w s₀.sp) s₄.mem s₅.mem := f₅.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact w_wR (.inl (by decide))
    · exact w_wR (.inl (by decide))
    · exact w_wR (.inr ⟨by decide, by decide⟩)
    · exact ⟨_, by simp, fun _ h => h⟩
  obtain G₅ : Frame (wR w s₀.sp) s₃.mem s₅.mem := (M.frame.sub (macR_wR (.inr rfl))).trans f₅'
  obtain F₅ : Frame (mutR w s₀.sp D n) s₁.mem s₅.mem := F₃.trans (G₅.sub wR_mut)
  obtain rd₁₅ : s₅.rd = s₀.rd := by rw [rd₅, M.rd, rd₁₃]
  obtain wr₁₅ : s₅.wr = s₀.wr := by rw [wr₅, M.wr, wr₁₃]
  obtain hk₅ := hk₁.frame F₅ (args_mut Ar) (by rw [he₅.sp, he₁.sp]) (by rw [rd₁₅, rd₁]) (by rw [wr₁₅, wr₁])
  obtain hT₅ : bytesAt s₅.mem (State.addr T) tl = bytesAt s₀.mem (State.addr T) tl := by
    rw [bytesAt_frame F₅ (tag_mut Tb) (by omega_arith), bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Tb.w.sub_right (Lay.wSub (by decide))) (by omega_arith)]
  -- `t`, and the received tag padded at `W + 256`.
  obtain ⟨i5, v5⟩ := hk₅.at 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨s₆, run₆, h6₆, g₆, k₆⟩ : ∃ s₆, runBlock isa [.ldrSp .r6 20] s₅ = some s₆ ∧
      s₆.gpr .r6 = BitVec.ofNat 32 tl ∧ (∀ r, r ≠ .r6 → s₆.gpr r = s₅.gpr r) ∧ Keeps s₅ s₆ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5, etl]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  obtain he₆ := he₅.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide)) k₆.sp k₆.rd k₆.wr
  obtain ⟨i4, v4⟩ := (hk₅.of_eq k₆.mem k₆.sp k₆.rd k₆.wr).at 4 (by decide) (show 4 * 4 = 16 from rfl)
  rw [eT] at v4
  refine WP.seq (WP.mono (recv_ok L he₆ i4 v4
      (by rw [k₆.rd, k₆.wr, rd₁₅, wr₁₅]; exact hTr) Tb.wrap (Tb.w.sub_right (Lay.wSub (by decide))) h6₆
      (by omega_arith) t16) fun s₇ ⟨hR₇, fr₇, g₇, rd₇, wr₇, sp₇⟩ => ?_)
  obtain he₇ := he₆.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    sp₇ rd₇ wr₇
  obtain h6₇ : s₇.gpr .r6 = BitVec.ofNat 32 tl := by
    rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), h6₆]
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok L he₇ (o := uO) (.inr rfl) h6₇ (by omega_arith) t16)
    fun s₈ ⟨h0₈, fr₈, g₈, rd₈, wr₈, sp₈⟩ => ?_)
  obtain ⟨s₉, run₉, h7₉, g₉, k₉⟩ : ∃ s₉, runBlock isa [.mov .r7 (.reg .r0)] s₈ = some s₉ ∧
      s₉.gpr .r7 = s₈.gpr .r0 ∧ (∀ r, r ≠ .r7 → s₉.gpr r = s₈.gpr r) ∧ Keeps s₈ s₉ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  obtain he₉ := he₇.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₉ _ (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)])
    (k₉.sp.trans sp₈) (k₉.rd.trans rd₈) (k₉.wr.trans wr₈)
  obtain f₅₉ : Frame (wR w s₀.sp) s₅.mem s₉.mem := by
    rw [k₉.mem, ← k₆.mem] at *
    refine (fr₇.sub fun r hr => ?_).trans (fr₈.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact w_wR (.inr ⟨by decide, by decide⟩)
    · simp only [List.mem_singleton] at hr; subst hr; exact w_wR (.inr ⟨by decide, by decide⟩)
  obtain F₉ : Frame (mutR w s₀.sp D n) s₁.mem s₉.mem := F₅.trans (f₅₉.sub wR_mut)
  obtain rd₁₉ : s₉.rd = s₀.rd := by rw [k₉.rd, rd₈, rd₇, k₆.rd, rd₁₅]
  obtain wr₁₉ : s₉.wr = s₀.wr := by rw [k₉.wr, wr₈, wr₇, k₆.wr, wr₁₅]
  obtain hk₉ := hk₁.frame F₉ (args_mut Ar) (by rw [he₉.sp, he₁.sp]) (by rw [rd₁₉, rd₁]) (by rw [wr₁₉, wr₁])
  -- What the comparison compares.
  obtain hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (State.addr k) R) := fun _ x =>
    Proof.Cmac.aesWith_length _ _ x
  obtain cK : ∀ {m : Mem}, Frame (mutR w s₀.sp D n) s₁.mem m →
      Spec.Ccm.ctxCiph m (State.addr k) R = Spec.Ccm.ctxCiph s₀.mem (State.addr k) R := fun hf => by
    rw [ctxCiph_frame hf (k_mut Ar) hRb, hK₁]
  obtain d₂ : bytesAt s₂.mem (State.addr D) n = bytesAt s₀.mem (State.addr D) n := by
    rw [buf_wR Ar.data.buf f₂', hent Ar.data.buf]
  obtain p₃ : bytesAt s₃.mem (State.addr D) n = Spec.Ccm.crypt (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R)
      (bytesAt s₀.mem (State.addr N) nl) (bytesAt s₀.mem (State.addr D) n) := by
    rw [o₃, cK F₂, d₂, crypt_eq (hBC _)]
  obtain p₉ : bytesAt s₉.mem (State.addr D) n = bytesAt s₃.mem (State.addr D) n := by
    rw [buf_wR Ar.data.buf f₅₉, buf_wR Ar.data.buf G₅]
  obtain hl : (bytesAt s₀.mem (State.addr N) nl).length ≤ 15 := by rw [hnl]; have := Ar.h13; omega_arith
  have mo := M.out
  rw [cK F₃, a₃, p₃] at mo
  rw [cK (F₃.trans (M.frame.sub (macR_mut (.inr rfl)))), mo] at o₅
  obtain hY := congrArg List.length o₅
  rw [length_bytesAt, length_xorFrom] at hY
  obtain hV : bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 uO) tl =
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
          (bytesAt s₀.mem (State.addr A) al) (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R)
            (bytesAt s₀.mem (State.addr N) nl) (bytesAt s₀.mem (State.addr D) n))) := by
    rw [bytesAt_prefix _ _ t16, bytesAt_frame fr₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), k₆.mem, o₅, take_xorFrom_zero (hBC _) _ hY.symm t16, ← mac_eq _ _ hl]
  obtain hRv : bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 256) 16 =
      bytesAt s₀.mem (State.addr T) tl ++ Spec.Gcm.zeros (16 - tl) := by
    rw [hR₇, k₆.mem, hT₅]
  obtain hML : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
      (bytesAt s₀.mem (State.addr A) al) (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R)
        (bytesAt s₀.mem (State.addr N) nl) (bytesAt s₀.mem (State.addr D) n))).length = tl := by
    rw [mac_eq _ _ hl, List.length_take, ← mo, length_bytesAt]; omega_arith
  obtain key : decide (bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 uO) tl ++ Spec.Gcm.zeros (16 - tl) =
      bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 256) 16) =
      tagOk (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
        (bytesAt s₀.mem (State.addr D) n) (bytesAt s₀.mem (State.addr A) al) (bytesAt s₀.mem (State.addr T) tl) := by
    rw [hV, hRv, tagOk, decide_eq_decide, List.append_left_inj,
      cryptTag_eq_iff (hBC _) t16 _ (length_bytesAt _ _ _) hML, eq_comm]
  obtain h7' : s₉.gpr .r7 = if decide (bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 uO) tl ++
      Spec.Gcm.zeros (16 - tl) = bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 256) 16) then 1 else 0 := by
    rw [h7₉, h0₈]; simp only [decide_eq_true_eq]
  -- The mask.
  refine WP.seq (WP.mono (mask_ok he₉ hk₉ eD en (Ar.data.of_eq rd₁₉ wr₁₉) Ar.n32 h7')
    fun s₁₀ ⟨he₁₀, rd₁₀, wr₁₀, g₁₀, m₁₀⟩ => ?_)
  rw [key] at m₁₀
  obtain F₁₀ : Frame (mutR w s₀.sp D n) s₁.mem s₁₀.mem := F₉.trans (by
    rw [m₁₀]
    exact (writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  -- `ok` in `r0`, and `restore`.
  show WP isa (.block ([.mov .r0 (.reg .r7)] ++ restore)) s₁₀ _
  refine WP.block_append (WP.of_runBlock ⟨s₁₀.setReg .r0 (s₁₀.gpr .r7), by arun [], ?_⟩)
  refine WP.mono (restore_ok (by simp [gpr_setReg, he₁₀.r11]) L.ww
    (by simp only [rd_setReg, wr_setReg]; exact covers_left he₁₀.perm.w)
    (by simp only [mem_setReg]; exact sv₁.frame F₁₀ (saved_mut Ar)) (by simp only [sp_setReg]; exact he₁₀.sp))
    fun s' ⟨ab, hm, h0', _, _⟩ => ⟨ab, ?_, ?_⟩
  · rw [h0', gpr_setReg_self, g₁₀ _ (by decide) (by decide) (by decide) (by decide), h7']
    rw [key]
  · rw [hm, mem_setReg, m₁₀, bytesAt_writeBytes_base _ _ _ (by rw [length_mask]) (by have := Ar.data.buf.lt; omega_arith),
      length_mask, List.drop_eq_nil_of_le (by rw [length_bytesAt]), List.append_nil, p₉, p₃]

theorem openPost {s s' : State} {c : Prop} [Decidable c] {pt : List Byte}
    (hres : openRes s = if c then some pt else none) (h0 : s'.gpr .r0 = if decide c then 1 else 0)
    (hd : bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat =
      if decide c then pt else zeros (arg s 3).toNat) : openArm.post s s' := by
  by_cases hc : c
  · simp only [hc, decide_true, ite_true] at hres h0 hd
    simp only [openArm, hres]; exact ⟨h0, hd⟩
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false] at hres h0 hd
    simp only [openArm, hres]; exact ⟨h0, hd⟩

/-- `vg_aes_ccm_open`. -/
theorem open_wp {s : State} (h : openArm.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openArm.post s s' :=
  have A := args_of_open h
  WP.mono (open_wp' A.1.1 A.1.2 A.2 rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl
    (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl)
    fun _ ⟨ab, h0, hd⟩ => ⟨ab, openPost rfl h0 hd⟩

end VG.Proof.AesCcm.Arm

end

end


/-!
# AES-CCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, states satisfying the preconditions, and the shared contracts of
`Spec/Ccm/Contract.lean` with the working space as a last argument
(`Proof/AesCcm/Scratch.lean`), with 16 bytes of stack: each call pushes two
words, and `vg_cmac_aes_update` pushes two more for its own call of
`vg_aes_ctr32`. `Frame.lean` allocates the working space.
-/

@[expose] public section

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm

/-- The entry invariant of a run, from the arguments. -/
theorem entI_of {s : State} {T : BitVec 32} {tl : Nat}
    (Ar : Args s (s.gpr .r0) (arg s 6) (s.gpr .r2) (arg s 0) (arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat tl) (hT : arg s 4 = T) (htl : arg s 5 = BitVec.ofNat 32 tl)
    (hwr : ∀ r ∈ s.wr, (args s 7).Disjoint r) :
    EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) T (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat tl s :=
  ⟨⟨Ar, rfl, hwr, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, hT, htl, rfl⟩,
    rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm⟩

/-- The entry invariant of `seal`'s runs. -/
theorem entI_seal {s : State} (h : sealArm.pre s) :
    EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (arg s 4) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s := by
  obtain A := args_of_seal h
  refine entI_of A.1.1 rfl (ofNat_toNat32 _).symm fun r hr => ?_
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.1.1.da.symm
  · exact A.2.2.symm
  · exact A.1.1.stk.aw

/-- The entry invariant of `open`'s runs. -/
theorem entI_open {s : State} (h : openArm.pre s) :
    EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (arg s 4) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s := by
  obtain A := args_of_open h
  refine entI_of A.1.1 rfl (ofNat_toNat32 _).symm fun r hr => ?_
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact A.1.1.da.symm
  · exact A.1.1.stk.aw

/-- The second run, with the first's public arguments. -/
theorem entI_pub {pre : State → Prop}
    (hpre : ∀ {s}, pre s → EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (arg s 4)
      (s.gpr .r1).toNat (s.gpr .r3).toNat (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s)
    {s₁ s₂ : State} (h₂ : pre s₂) (hq : onePub s₁ s₂) :
    EntI (s₁.gpr .r0) (arg s₁ 6) s₁.sp (s₁.gpr .r2) (arg s₁ 0) (arg s₁ 2) (arg s₁ 4) (s₁.gpr .r1).toNat
      (s₁.gpr .r3).toNat (arg s₁ 1).toNat (arg s₁ 3).toNat (arg s₁ 5).toNat s₂ := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  obtain e := hpre h₂
  rwa [← q₀, ← q₁, ← q₂, ← q₃, ← q₄, ← qa 0 (by decide), ← qa 1 (by decide), ← qa 2 (by decide),
    ← qa 3 (by decide), ← qa 4 (by decide), ← qa 5 (by decide), ← qa 6 (by decide)] at e

theorem one_ct {pre : State → Prop}
    (hpre : ∀ {s}, pre s → EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (arg s 4)
      (s.gpr .r1).toNat (s.gpr .r3).toNat (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s)
    {c : Prog isa}
    (hc : ∀ {k w sp N A D T : BitVec 32} {R nl al n tl : Nat}, Lay k w sp → (R = 10 ∨ R = 12 ∨ R = 14) →
      al < 2 ^ 32 → 7 ≤ nl → nl ≤ 13 → n < 256 ^ (15 - nl) → n < 2 ^ 32 →
      Proof.AesGcm.Arm.CT (EntI k w sp N A D T R nl al n tl) c)
    {pub : State → State → Prop} (hp : ∀ s₁ s₂, pub s₁ s₂ → onePub s₁ s₂) :
    ConstantTime isa pre pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain Ar := (hpre h₁).1.ar
  exact (hc Ar.lay Ar.rounds Ar.al32 Ar.h7 Ar.h13 Ar.hn Ar.n32 _ _ _ _ _ _ ⟨hpre h₁, entI_pub hpre h₂ (hp _ _ hq)⟩
    e₁ e₂).1

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» :=
  one_ct entI_seal (fun L hR hal h7 h13 hn hn4 => seal_ctI L hR hal h7 h13 hn hn4) fun _ _ h => h

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» :=
  one_ct entI_open (fun L hR hal h7 h13 hn hn4 => open_ctI L hR hal h7 h13 hn hn4) fun _ _ h => h.1

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: a 7-byte nonce,
no associated data, no data, a 4-byte tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 7 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8014 then 4 else if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 28⟩], wr := [⟨0, 0⟩, ⟨0, 2560⟩] }

theorem seal_verified : Verified Arm.target «seal» (Proof.AesCcm.sealScratchContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => seal_wp hs) seal_ct (by
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
      sealArm, sealPre, oneLay, onePub, bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified : Verified Arm.target «open» (Proof.AesCcm.openScratchContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => open_wp hs) open_ct
    { pre := by
        sig_implies_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openLeak,
          openArm, openPre, oneLay, onePub, openLeak, bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Proof.AesCcm.openRoundsPost, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [openArm, openRes, ciph, Arm.State.addr] at h
        obtain e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openLeak,
          openArm, openPre, oneLay, onePub, openLeak, bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega_using [hi]) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
        · exact a3
        · exact a4
        · exact a5
        · exact a6
      sat := by
        sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openLeak,
          openArm, openPre, oneLay, onePub, openLeak, bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [openSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.AesCcm.Arm

end

end


/-!
# AES-CCM on ARMv7, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): their working space is their seventh stack
argument, after `aad`, `aad_len`, `data`, `len`, `tag` and `tag_len`, so the
frame of 2592 bytes holds a copy of those six words, the address of the
working space, the saved `lr` and the working space. The copies are read
only where the pre- and postconditions read the buffers, and `open`'s leak,
whether it succeeds, reads only its buffers (`Proof/AesCcm/Scratch.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesCcm.sealRoundsContract Arm.abi 2608).pre s := by
  implies_sat [Proof.AesCcm.sealRoundsContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «seal»)
      (Proof.AesCcm.sealRoundsContract Arm.abi 2608) :=
  Arm.Verified.stackScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre Arm.abi.ptrBits)
    (post := Proof.AesCcm.sealRoundsPost Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 6) seal_verified (by decide) (by decide) (by decide) (by decide)
    (sealPre_local _) (sealPost_local _) (sealPostOut_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesCcm.openRoundsContract Arm.abi 2608).pre s := by
  implies_sat [Proof.AesCcm.openRoundsContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Proof.AesCcm.openRoundsPost,
    Spec.Ccm.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «open»)
      (Proof.AesCcm.openRoundsContract Arm.abi 2608) :=
  Arm.Verified.stackScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre Arm.abi.ptrBits)
    (post := Proof.AesCcm.openRoundsPost Arm.abi.ptrBits) (wa := true) (stack := 16)
    (leak := some (Spec.Ccm.openLeak Arm.abi.ptrBits))
    (m := 6) open_verified (by decide) (by decide) (by decide) (by decide)
    (openPre_local _) (openPost_local _) (openPostOut_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesCcm.Arm
