import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Framework.X86_64.Taint

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

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data. -/
def Sib (a s : State) : Prop := encK.pre s ∧ encK.pub a s

theorem pub_refl (s : State) : encK.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem Sib.arg {a s : State} (h : Sib a s) {i : Nat} (hi : i < 6) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.2.1) i (List.mem_range.mpr hi)).symm

theorem Sib.n {a s : State} (h : Sib a s) : nB s = nB a := h.2.2.2.1.symm

theorem Sib.e {a s : State} (h : Sib a s) : eB s = eB a := h.2.2.2.2.symm

theorem Sib.fb {a s : State} (h : Sib a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

/-- A point of a run, described by `J` from the run's entry state. -/
def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, Sib a s ∧ J s t

/-- A register `J` gives as a function of the public data. -/
theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : At J a t₁) (h₂ : At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

/-- Registers `J` gives as functions of the public data, at once. -/
theorem pins {J : State → State → Prop} (rs : List (Reg × (State → BitVec 64)))
    (hf : ∀ p ∈ rs, ∀ s t, J s t → t.gpr p.1 = p.2 s) (hs : ∀ p ∈ rs, ∀ a s, Sib a s → p.2 s = p.2 a) :
    Pins (At J) (rs.map (·.1)) := fun a t₁ t₂ h₁ h₂ r hr => by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact pin p.2 (hf p hp) (hs p hp) h₁ h₂

theorem arg_pin {i : Nat} (hi : i < 6) : ∀ a s, Sib a s → stackArg s i = stackArg a i := fun _ _ h => h.arg hi

theorem fb_pin : ∀ a s, Sib a s → fb s = fb a := fun _ _ h => h.fb

theorem const_pin (v : BitVec 64) : ∀ a s, Sib a s → (fun _ : State => v) s = (fun _ : State => v) a :=
  fun _ _ _ => rfl

theorem gpr_pin {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    ∀ a s, Sib a s → s.gpr r = a.gpr r := fun _ _ h => h.gpr hr

/-! ## The pieces before the call -/

def J0 (s t : State) : Prop := t = allocState frameBytes s

theorem setup_two : RelCT isa (Two (At J0)) (.block setup) (Two (At AfterSetup)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pin fb (fun s t h => by rw [h]; rfl) fb_pin h₁ h₂) (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by subst ht; exact WP.mono (setup_step (ePre_of S.1)) fun _ h => ⟨s, S, h⟩

theorem ps_two : RelCT isa (Two (At AfterSetup)) psLoop (Two (At AfterPs)) :=
  two_piece [.rsp, .rsi, .rcx, .r10] (pins (J := AfterSetup) [(.rsp, fb), (.rsi, fun s => stackArg s 2),
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
    fun _ _ ⟨s, S, h⟩ => WP.mono (ps_step (ePre_of S.1) h) fun _ h => ⟨s, S, h⟩

theorem sep_two : RelCT isa (Two (At AfterPs)) (.block sep) (Two (At Mid)) :=
  two_piece [.rsp, .rcx] (pins (J := AfterPs) [(.rsp, fb), (.rcx, fun s => stackArg s 3)] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) s t h
        · exact h.rsp
        · exact h.rcx) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl)
        · exact fb_pin
        · exact arg_pin (by decide))) (by taint_decide)
    fun _ _ ⟨s, S, h⟩ => WP.mono (sep_step (ePre_of S.1) h) fun _ h => ⟨s, S, h⟩

theorem copy_two : RelCT isa (Two (At Mid)) msgCopy (Two (At PreCall)) := by
  refine two_ite (fun _ t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
    rw [eval_ne_mid h₁, eval_ne_mid h₂, S₁.arg (by decide), S₂.arg (by decide)]) ?_ ?_
  · refine two_piece [.rsp, .rdi, .rsi, .rcx, .r10] (fun a t₁ t₂ ⟨⟨s₁, S₁, h₁⟩, _⟩ ⟨⟨s₂, S₂, h₂⟩, _⟩ r hr => ?_)
      (by taint_decide) fun _ _ ⟨⟨s, S, h⟩, hc⟩ => WP.mono (msgLoop_step (ePre_of S.1) h ?_) fun _ h => ⟨s, S, h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
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
      fun _ _ ⟨⟨s, S, h⟩, hc⟩ => WP.block_nil ⟨s, S, empty_step (ePre_of S.1) h ?_⟩
    rw [eval_ne_mid h] at hc
    simp only [Option.some.injEq, Bool.not_eq_eq_eq_not, Bool.not_false, beq_iff_eq] at hc
    rw [hc]; rfl

/-! ## The call -/

/-- Before the call, with its arguments in registers. -/
def J5 (s t : State) : Prop :=
  PreCall s t ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧
    t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

theorem callArgs_two : RelCT isa (Two (At PreCall)) (.block callArgs) (Two (At J5)) :=
  two_piece [.rsp] (pins (J := PreCall) [(.rsp, fb)] (by
        simp only [List.mem_singleton]; rintro p rfl s t h; exact h.rsp) (by
        simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun _ _ ⟨s, S, h⟩ => WP.mono (callArgs_run (ePre_of S.1) h)
      fun t' ⟨hm, hdi, hsi, hdx, hcx, h8, h9, k⟩ => ⟨s, S, ⟨(k.gpr (by decide)).trans h.rsp, k.2.1.trans h.rd,
        k.2.2.trans h.wr, hm ▸ h.out, hm ▸ h.slots, hm ▸ h.sZ, hm ▸ h.em⟩, hdi, hsi, hdx, hcx, h8, h9⟩

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

/-- What the callee's contract makes public, from the entry state. -/
theorem pub_view {a s t : State} (S : Sib a s) (h : J5 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (pubRd s) (pubWr s)).gpr =
      [a.gpr .rdi, a.gpr .rcx, a.gpr .rdx, a.gpr .rcx, a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 0 = off (fb a) oEM ∧
    stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 1 = a.gpr .rcx ∧
    stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 2 = stackArg a 4 ∧
    stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 3 = stackArg a 5 ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (pubRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .rcx).toNat = nB a ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (pubRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .r9).toNat = eB a := by
  obtain ⟨hpc, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hp := ePre_of S.1
  have rcx := S.gpr (r := .rcx) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, hpc.rsp, S.fb, rcx, S.gpr (r := .rdi) (by decide),
      S.gpr (r := .rdx) (by decide), S.gpr (r := .r8) (by decide), S.gpr (r := .r9) (by decide)]
  · rw [stackArg_entry hpc.rsp _ _ (by decide), ← S.fb]
    have := hpc.slots.a0; simp only [Bignum.X86_64.word, off_zero, Nat.mul_zero]; exact this
  · rw [stackArg_entry hpc.rsp _ _ (by decide), ← rcx]; exact hpc.slots.a1
  · rw [stackArg_entry hpc.rsp _ _ (by decide), ← S.arg (by decide)]; exact hpc.slots.a2
  · rw [stackArg_entry hpc.rsp _ _ (by decide), ← S.arg (by decide)]; exact hpc.slots.a3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [entryBytes hpc _ _ hp.dKn (by have := hp.dOn; rw [outR]; exact this) hp.dns.symm
      (by have := hp.wN; omega)]
    exact S.n
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [entryBytes hpc _ _ hp.dKe (by have := hp.dOe; rw [outR]; exact this) hp.des.symm
      (by have := hp.wE; omega)]
    exact S.e

theorem pub_ct (v : PubImpl) : RelCT isa (Two (At J5)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := pubChkK) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, n₁, e₁⟩ := pub_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, n₂, e₂⟩ := pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := pub_covers (ePre_of S₁.1) j₁.1
  obtain ⟨c₂, w₂⟩ := pub_covers (ePre_of S₂.1) j₂.1
  obtain ⟨h₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨h₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  exact ⟨pubRd s₁, pubWr s₁, pubRd s₂, pubWr s₂, pub_pre (ePre_of S₁.1) h₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁,
    pub_pre (ePre_of S₂.1) h₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂,
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩, c₁, w₁, c₂, w₂,
    by rw [h₁.rsp, h₂.rsp, S₁.fb, S₂.fb]⟩

theorem call_two (v : PubImpl) : RelCT isa (Two (At J5)) (.call v.name v.code) (Two (At PostCall)) :=
  two_post (pub_ct v) fun _ _ ⟨s, S, h, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (pub_call v (ePre_of S.1) h hdi hsi hdx hcx h8 h9) fun _ h => ⟨s, S, h.1⟩

/-! ## The mask -/

def J7 (s t : State) : Prop :=
  t.gpr .rsp = fb s ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r10 = BitVec.ofNat 64 0

theorem maskArgs_two : RelCT isa (Two (At PostCall)) (.block maskArgs) (Two (At J7)) :=
  two_piece [.rsp] (pins (J := PostCall) [(.rsp, fb)] (by
        simp only [List.mem_singleton]; rintro p rfl s t h; exact h.rsp) (by
        simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun _ _ ⟨s, S, h⟩ => WP.mono (maskArgs_run (ePre_of S.1) h)
      fun _ ⟨_, _, _, hdi, hcx, h10, k⟩ => ⟨s, S, (k.gpr (by decide)).trans h.rsp, hdi, hcx, h10⟩

theorem mask_ct : RelCT isa (Two (At J7)) (.seq maskLoop (.block [.mov .rax (.reg .r11)])) fun _ _ => True :=
  two_taint [.rsp, .rdi, .rcx, .r10] (pins (J := J7) [(.rsp, fb), (.rdi, fun s => s.gpr .rdi),
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

/-! ## The whole function -/

theorem body_ct (v : PubImpl) : RelCT isa (Two (At J0)) (body v.name v.code) fun _ _ => True := by
  rw [body_eq]
  exact RelCT.seq setup_two (RelCT.seq ps_two (RelCT.seq sep_two (RelCT.seq copy_two
    (RelCT.seq callArgs_two (RelCT.seq (call_two v) (RelCT.seq maskArgs_two mask_ct))))))

theorem enc_constantTime (v : PubImpl) : ConstantTime isa encK.pre encK.pub (code v.name v.code) :=
  RelCT.constantTime (relCT_alloc ((body_ct v).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, e₁⟩, ⟨s₂, ⟨h₂, hpub⟩, e₂⟩⟩)
    fun _ _ h => h))

/-! ## `Verified` -/

theorem enc_verified (v : PubImpl) :
    Verified target (code v.name v.code) (Spec.RsaPkcs1Enc.encryptContract abi encStack) :=
  Verified.of_correct (k := encK) (enc_correct v) (enc_constantTime v) encrypt_implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem enc_spSafe (v : PubImpl) : (code v.name v.code).all (fun i => !isa.writesSp i) = true := by
  simp only [code, body, Code.all, v.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Enc.X86_64
