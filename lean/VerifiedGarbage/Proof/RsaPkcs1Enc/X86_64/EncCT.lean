module
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCall

import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCall
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: constant time

Two runs from entry states that agree on the public data (`encK.pub`: the
pointers and lengths, `n` and `e`) leak the same trace. Each point of the
code is described, in each run, by what correctness says of it from that
run's entry state, which agrees with an anchor `a` on the public data
(`At`): the blocks and loops are checked by the taint analysis from the
registers this fixes (`PS`, the zero test and the mask are never among
them), the branch on the message's length agrees since the length is
public, and the call is constant time for its callee's contract, whose
public data it fixes too.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data.
The pieces of the code are proved for any relation `R` of an anchor to an
entry state that implies this one (`hR`), so that a variant of the function
with more public data (`PcCT`) uses them too. -/
def Sib (a s : State) : Prop := EPre s ∧ encK.pub a s

theorem pub_refl (s : State) : encK.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem Sib.arg {a s : State} (h : Sib a s) {i : Nat} (hi : i < 6) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.2.1) i (List.mem_range.mpr hi)).symm

theorem Sib.e {a s : State} (h : Sib a s) : eB s = eB a := h.2.2.2.2.symm

theorem Sib.fb {a s : State} (h : Sib a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

/-- A point of a run, described by `J` from the run's entry state, which `R`
relates to the anchor. -/
def At (R J : State → State → Prop) (a t : State) : Prop := ∃ s, R a s ∧ J s t

/-- A register `J` gives as a function of the public data. -/
theorem pin {R J : State → State → Prop} (hR : ∀ a s, R a s → Sib a s) {r : Reg} (f : State → BitVec 64)
    (hf : ∀ s t, J s t → t.gpr r = f s) (hs : ∀ a s, Sib a s → f s = f a) {a t₁ t₂ : State}
    (h₁ : At R J a t₁) (h₂ : At R J a t₂) : t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ (hR _ _ S₁), hs _ _ (hR _ _ S₂)]

/-- Registers `J` gives as functions of the public data, at once. -/
theorem pins {R J : State → State → Prop} (hR : ∀ a s, R a s → Sib a s) (rs : List (Reg × (State → BitVec 64)))
    (hf : ∀ p ∈ rs, ∀ s t, J s t → t.gpr p.1 = p.2 s) (hs : ∀ p ∈ rs, ∀ a s, Sib a s → p.2 s = p.2 a) :
    Pins (At R J) (rs.map (·.1)) := fun a t₁ t₂ h₁ h₂ r hr => by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact pin hR p.2 (hf p hp) (hs p hp) h₁ h₂

theorem arg_pin {i : Nat} (hi : i < 6) : ∀ a s, Sib a s → stackArg s i = stackArg a i := fun _ _ h => h.arg hi

theorem fb_pin : ∀ a s, Sib a s → fb s = fb a := fun _ _ h => h.fb

theorem const_pin (v : BitVec 64) : ∀ a s, Sib a s → (fun _ : State => v) s = (fun _ : State => v) a :=
  fun _ _ _ => rfl

theorem gpr_pin {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    ∀ a s, Sib a s → s.gpr r = a.gpr r := fun _ _ h => h.gpr hr

/-! ## The pieces before the call -/

section
variable {R : State → State → Prop} (hR : ∀ a s, R a s → Sib a s)
include hR

def J0 (s t : State) : Prop := t = allocState frameBytes s

theorem setup_two : RelCT isa (Two (At R J0)) (.block setup) (Two (At R AfterSetup)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pin hR fb (fun s t h => by rw [h]; rfl) fb_pin h₁ h₂) (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by subst ht; exact WP.mono (setup_step (hR _ _ S).1) fun _ h => ⟨s, S, h⟩

theorem ps_two : RelCT isa (Two (At R AfterSetup)) psLoop (Two (At R AfterPs)) :=
  two_piece [.rsp, .rsi, .rcx, .r10] (pins (J := AfterSetup) hR [(.rsp, fb), (.rsi, fun s => stackArg s 2),
      (.rcx, fun s => stackArg s 3), (.r10, fun _ => BitVec.ofNat 64 0)] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl) s t h
        · exact h.keep.gpr (by decide)
        · exact h.rsi
        · exact h.rcx
        · exact h.r10) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl)
        · exact fb_pin
        · exact arg_pin (by decide)
        · exact arg_pin (by decide)
        · exact const_pin _)) (by taint_decide)
    fun _ _ ⟨s, S, h⟩ => WP.mono (ps_step (hR _ _ S).1 h) fun _ h => ⟨s, S, h⟩

theorem sep_two : RelCT isa (Two (At R AfterPs)) (.block sep) (Two (At R Mid)) :=
  two_piece [.rsp, .rcx] (pins (J := AfterPs) hR [(.rsp, fb), (.rcx, fun s => stackArg s 3)] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) s t h
        · exact h.rsp
        · exact h.rcx) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl)
        · exact fb_pin
        · exact arg_pin (by decide))) (by taint_decide)
    fun _ _ ⟨s, S, h⟩ => WP.mono (sep_step (hR _ _ S).1 h) fun _ h => ⟨s, S, h⟩

theorem copy_two : RelCT isa (Two (At R Mid)) msgCopy (Two (At R PreCall)) := by
  refine two_ite (fun _ t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
    rw [eval_ne_mid h₁, eval_ne_mid h₂, (hR _ _ S₁).arg (by decide), (hR _ _ S₂).arg (by decide)]) ?_ ?_
  · refine two_piece [.rsp, .rdi, .rsi, .rcx, .r10] (fun a t₁ t₂ ⟨⟨s₁, S₁, h₁⟩, _⟩ ⟨⟨s₂, S₂, h₂⟩, _⟩ r hr => ?_)
      (by taint_decide) fun _ _ ⟨⟨s, S, h⟩, hc⟩ => WP.mono (msgLoop_step (hR _ _ S).1 h ?_) fun _ h => ⟨s, S, h⟩
    · have S₁ := hR _ _ S₁
      have S₂ := hR _ _ S₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.rsp, h₂.rsp, S₁.fb, S₂.fb]
      · rw [h₁.rdi, h₂.rdi, S₁.fb, S₂.fb, S₁.arg (by decide), S₂.arg (by decide)]
      · rw [h₁.rsi, h₂.rsi, S₁.arg (by decide), S₂.arg (by decide)]
      · rw [h₁.rcx, h₂.rcx, S₁.arg (by decide), S₂.arg (by decide)]
      · rw [h₁.r10, h₂.r10]
    · rw [eval_ne_mid h] at hc
      simp only [Option.some.injEq, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at hc
      exact Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq (by simp [h]))
  · refine two_piece [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
      fun _ _ ⟨⟨s, S, h⟩, hc⟩ => WP.block_nil ⟨s, S, empty_step (hR _ _ S).1 h ?_⟩
    rw [eval_ne_mid h] at hc
    simp only [Option.some.injEq, Bool.not_eq_eq_eq_not, Bool.not_false, beq_iff_eq] at hc
    rw [hc]; rfl

/-! ## The mask -/

def J7 (s t : State) : Prop :=
  t.gpr .rsp = fb s ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r10 = BitVec.ofNat 64 0

theorem maskArgs_two : RelCT isa (Two (At R AfterCall)) (.block maskArgs) (Two (At R J7)) :=
  two_piece [.rsp] (pins (J := AfterCall) hR [(.rsp, fb)] (by
        simp only [List.mem_singleton]; rintro p rfl s t h; exact h.rsp) (by
        simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun _ _ ⟨s, S, h⟩ => WP.mono (maskArgs_run (hR _ _ S).1 h)
      fun _ ⟨_, _, _, hdi, hcx, h10, k⟩ => ⟨s, S, (k.gpr (by decide)).trans h.rsp, hdi, hcx, h10⟩

theorem mask_ct : RelCT isa (Two (At R J7)) (.seq maskLoop (.block [.mov .rax (.reg .r11)])) fun _ _ => True :=
  two_taint [.rsp, .rdi, .rcx, .r10] (pins (J := J7) hR [(.rsp, fb), (.rdi, fun s => s.gpr .rdi),
      (.rcx, fun s => s.gpr .rcx), (.r10, fun _ => BitVec.ofNat 64 0)] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl) s t h
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl)
        · exact fb_pin
        · exact gpr_pin (by decide)
        · exact gpr_pin (by decide)
        · exact const_pin _)) (by taint_decide)

end

/-! ## The call -/

/-- The registers a callee sees, from the caller's. -/
theorem entry_regs (t : State) (rd wr : List Region) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions rd wr).gpr =
      [t.gpr .rdi, t.gpr .rsi, t.gpr .rdx, t.gpr .rcx, t.gpr .r8, t.gpr .r9, t.gpr .rsp - 8] := by
  simp only [List.map_cons, List.map_nil, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]

theorem regs_eq {s₁ s₂ : State}
    (h : [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map s₁.gpr = [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map s₂.gpr) :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r :=
  List.map_inj_left.mp h

/-- A caller's buffer, read by the callee: the same as at the entry. -/
theorem entryBytes {s t : State} (h : PreCall s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  rw [State.withRegions_mem]
  exact bytes_of_frame (frame_call (frame_of_outside h.out) (callEntry_frame h.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (ret_sub s)) hk ho hs hl

end VG.Proof.RsaPkcs1Enc.X86_64
