import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two

/-!
# `vg_rsa_pkcs1_sign` on AArch64: constant time

The hash value and the private key are secret. The taint analysis checks
the code between the call and the branch on `encode`'s result, which
depends only on the hash value's length (`encodeId_isSome`); the call is
related by its callee's contract (`privCallCT`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Sign
open VG.Impl.RsaPkcs1Sig.AArch64 (encode)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_ite two_alloc encodeId EOut clob)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (eval_zero')
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The taint checks -/

section
variable {α : Type} {Φ : α → State → Prop}

theorem encArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block encArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem encode_taint (h : Pins Φ [.x8, .x9, .x10, .x11, .x12]) : RelCT isa (Two Φ) encode fun _ _ => True :=
  two_taint [.x8, .x9, .x10, .x11, .x12] h (by taint_decide)

theorem zeroSlots_taint (h : Pins Φ [.x17, .x19]) : RelCT isa (Two Φ) zeroSlots fun _ _ => True :=
  two_taint [.x17, .x19] h (by taint_decide)

theorem callArgs_taint (h : Pins Φ [.x16]) : RelCT isa (Two Φ) (.block callArgs) fun _ _ => True :=
  two_taint [.x16] h (by taint_decide)

theorem wipe_taint (h : Pins Φ [.x19]) : RelCT isa (Two Φ) wipe fun _ _ => True :=
  two_taint [.x19] h (by taint_decide)

theorem restore_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block restore) fun _ _ => True :=
  two_taint [] h (by taint_decide)

end

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, `hash`, and the bytes of `n` and `e`. -/
structure PubS (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x7], s.gpr r = a.gpr r
  h6 : (s.gpr .x6).setWidth 32 = (a.gpr .x6).setWidth 32
  args : ∀ i < 13, stackArg s i = stackArg a i
  bn : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat
  be : Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x4) (a.gpr .x5).toNat

theorem PubS.refl (s : State) : PubS s s :=
  ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

theorem leak_eq2 {a b a' b' : List Byte} (ha : a.length = a'.length)
    (h : (a ++ b).map (·.toNat) = (a' ++ b').map (·.toNat)) : a = a' ∧ b = b' :=
  List.append_inj ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h) ha

theorem pubS_of {S : Nat} {s₁ s₂ : State} (h : (Spec.RsaPkcs1Sig.signContract abi S).pub s₁ s₂) :
    PubS s₁ s₂ := by
  sig_pub [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_thirteen,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  obtain ⟨hn, he⟩ := leak_eq2 (by rw [bytesAt_length, bytesAt_length, h3]) hl
  refine ⟨hsp.symm, fun r hr => ?_, h6.symm, fun i hi => ?_, hn.symm, he.symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h7.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm,
      a10.symm, a11.symm, a12.symm]

/-! ## The points of the code -/

/-- An entry state with the anchor's public data. -/
def E (K : Nat) (a s : State) : Prop := PreS K s ∧ PubS a s

theorem E.fb {K : Nat} {a s : State} (h : E K a s) : fb s = fb a := by
  show s.sp - _ = a.sp - _; rw [h.2.sp]

theorem E.gpr {K : Nat} {a s : State} (h : E K a s) {r : Reg} (hr : r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x7]) :
    s.gpr r = a.gpr r := h.2.g r hr

/-- Whether an encoding succeeds depends only on the hash value's length. -/
theorem encodeId_isSome (x : BitVec 32) {H H' : List Byte} (hl : H.length = H'.length) (k : Nat) :
    (encodeId x H k).isSome = (encodeId x H' k).isSome := by
  unfold encodeId
  cases Spec.RsaPkcs1Sig.Hash.ofId x.toNat with
  | none => rfl
  | some h =>
    simp only [Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo, List.length_append, hl]
    split <;> rfl

theorem encOut_isSome {K : Nat} {a s : State} (h : E K a s) : (encOut s).isSome = (encOut a).isSome := by
  unfold encOut
  rw [h.2.h6, h.gpr (r := .x3) (by decide)]
  exact encodeId_isSome _ (by rw [bytesAt_length, bytesAt_length, h.2.args 0 (by decide)]) _

/-- `J a` at a point of the code, from an entry state with the anchor `a`'s
public data. -/
def At (K : Nat) (J : State → State → State → Prop) (a t : State) : Prop := ∃ s, E K a s ∧ J a s t

def JE (_ : State) : State → State → Prop := AtEnc
def JW (_ : State) (s w : State) : Prop := ∃ u, AtEnc s u ∧ Keep clob u w ∧ EOut u w (encOut s)
def JC (_ : State) (s t : State) : Prop := ∃ em, AtCall s em t
def JA (_ : State) (s t : State) : Prop := ∃ em, AfterCall s em t
def JM (_ : State) : State → State → Prop := Mid

theorem pins_and {α : Type} {Φ : α → State → Prop} {P : State → Prop} {rs : List Reg} (h : Pins Φ rs) :
    Pins (fun a s => Φ a s ∧ P s) rs := fun a s₁ s₂ h₁ h₂ => h a s₁ s₂ h₁.1 h₂.1

theorem pinsW {K : Nat} : Pins (At K JW) [.x17, .x19] := fun a w₁ w₂ ⟨s₁, h₁, u₁, j₁, k₁, _⟩
    ⟨s₂, h₂, u₂, j₂, k₂, _⟩ => by
  refine ⟨by rw [k₁.sp, k₂.sp, j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [k₁.get .x17, k₂.get .x17, j₁.x17, j₂.x17, h₁.gpr (by decide), h₂.gpr (by decide)]
  · rw [k₁.get .x19, k₂.get .x19, j₁.x19, j₂.x19, h₁.gpr (by decide), h₂.gpr (by decide)]

theorem pinsM {K : Nat} {J : State → State → State → Prop} (hJ : ∀ a s t, J a s t → Mid s t) :
    Pins (At K J) [.x19] := fun a t₁ t₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => by
  have m₁ := hJ _ _ _ j₁; have m₂ := hJ _ _ _ j₂
  refine ⟨by rw [m₁.sp, m₂.sp, h₁.fb, h₂.fb], fun r hr => ?_⟩
  rw [List.mem_singleton.mp hr, m₁.x19, m₂.x19, h₁.gpr (by decide), h₂.gpr (by decide)]

theorem pinsA {K : Nat} : Pins (At K JA) [.x19] := pinsM fun _ _ _ ⟨_, j⟩ => j.toMid
theorem pinsMid {K : Nat} : Pins (At K JM) [.x19] := pinsM fun _ _ _ j => j

/-! ## The call -/

theorem call_ct (c : PrivChecked) :
    RelCT isa (Two (At c.stack JC)) (.call c.name c.code) fun _ _ => True := by
  refine privCallCT c fun t₁ t₂ ⟨a, ⟨s₁, h₁, em₁, c₁⟩, ⟨s₂, h₂, em₂, c₂⟩⟩ => ?_
  refine ⟨privOk_of c h₁.1 c₁, privOk_of c h₂.1 c₂, ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, h₁.fb, h₂.fb]
  · have e : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x7], s₁.gpr r = s₂.gpr r :=
      fun r hr => (h₁.gpr hr).trans (h₂.gpr hr).symm
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0, e .x0 (by decide)]
    · rw [c₁.x1, c₂.x1, e .x1 (by decide)]
    · rw [c₁.x2, c₂.x2, e .x2 (by decide)]
    · rw [c₁.x3, c₂.x3, e .x3 (by decide)]
    · rw [c₁.x4, c₂.x4, e .x4 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x5 (by decide)]
    · rw [c₁.x6, c₂.x6, h₁.fb, h₂.fb]
    · rw [c₁.x7, c₂.x7, e .x3 (by decide)]
  · rw [c₁.args i hi, c₂.args i hi, h₁.2.args (i + 1) (by omega), h₂.2.args (i + 1) (by omega)]
  · rw [c₁.x2, c₁.x3, c₂.x2, c₂.x3, bytes_frame c₁.mem h₁.1.kn (by have := h₁.1.wn; omega),
      bytes_frame c₂.mem h₂.1.kn (by have := h₂.1.wn; omega), h₁.2.bn, h₂.2.bn]
  · rw [c₁.x4, c₁.x5, c₂.x4, c₂.x5, bytes_frame c₁.mem h₁.1.ke (by have := h₁.1.we; omega),
      bytes_frame c₂.mem h₂.1.ke (by have := h₂.1.we; omega), h₁.2.be, h₂.2.be]

/-! ## After the encoding -/

theorem afterEnc_ct (c : PrivChecked) :
    RelCT isa (Two (At c.stack JW)) (afterEnc c.name c.code) (Two (At c.stack JM)) := by
  unfold afterEnc
  have res : ∀ {a s w}, E c.stack a s → JW a s w →
      isa.eval (.zero .x .x0) w = some (encOut a).isNone := fun {a s w} h ⟨u, _, _, hout⟩ => by
    rw [eval_zero']
    have hs := encOut_isSome h
    cases he : encOut s with
    | none =>
      rw [he] at hout hs
      rw [hout.1]
      cases ha : encOut a with
      | none => rfl
      | some _ => rw [ha] at hs; cases hs
    | some em =>
      rw [he] at hout hs
      rw [hout.1]
      cases ha : encOut a with
      | none => rw [ha] at hs; cases hs
      | some _ => rfl
  refine two_ite (fun a w₁ w₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => by rw [res h₁ j₁, res h₂ j₂])
    (two_post (zeroSlots_taint (pins_and pinsW)) fun a w ⟨⟨s, h, u, hu, hK, hout⟩, hb⟩ => ?_) ?_
  · have hn : encOut s = none := by
      rw [res h ⟨u, hu, hK, hout⟩] at hb
      have := encOut_isSome h
      cases he : encOut s with
      | none => rfl
      | some _ => rw [he] at this; cases ha : encOut a <;> simp_all
    rw [hn] at hout
    exact WP.mono (zeroSlots_ok h.1 hu hK hout.2) fun w' hw' => ⟨s, h, hw'.1⟩
  refine RelCT.seq (two_post (Ψ := At c.stack JC)
    (callArgs_taint fun a w₁ w₂ ⟨⟨s₁, h₁, u₁, j₁, k₁, _⟩, _⟩ ⟨⟨s₂, h₂, u₂, j₂, k₂, _⟩, _⟩ =>
      ⟨by rw [k₁.sp, k₂.sp, j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun r hr => by
        rw [List.mem_singleton.mp hr, k₁.get .x16, k₂.get .x16, j₁.x16, j₂.x16, h₁.fb, h₂.fb]⟩)
    fun a w ⟨⟨s, h, u, hu, hK, hout⟩, hb⟩ => ?_) ?_
  · cases he : encOut s with
    | none =>
      rw [he] at hout
      rw [res h ⟨u, hu, hK, by rw [he]; exact hout⟩] at hb
      have := encOut_isSome h
      rw [he] at this
      cases ha : encOut a <;> simp_all
    | some em =>
      rw [he] at hout
      exact WP.mono (callArgs_ok h.1 hu hK hout.2 (encodeId_length he)) fun t ht => ⟨s, h, em, ht⟩
  refine RelCT.seq (two_post (Ψ := At c.stack JA) (call_ct c) fun a t ⟨s, h, em, ht⟩ =>
    WP.mono (call_ok c h.1 ht) fun t' ht' => ⟨s, h, em, ht'⟩) ?_
  exact two_post (wipe_taint pinsA) fun a t ⟨s, h, em, ht⟩ =>
    WP.mono (wipe_ok h.1 ht.toMid) fun w hw => ⟨s, h, hw.1⟩

theorem code_ct (c : PrivChecked) :
    RelCT isa (Two (E c.stack)) (code c.name c.code) fun _ _ => True := by
  unfold code
  refine two_alloc (R := fun _ _ => True) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := At c.stack JE)
    (encArgs_taint fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂]; simp only [allocated, h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩)
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    exact WP.mono (encArgs_ok h.1 (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated]))
      fun t ht => ⟨s, h, ht⟩
  refine RelCT.seq (two_post (Ψ := At c.stack JW)
    (encode_taint fun a u₁ u₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => ⟨by rw [j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun r hr => ?_⟩)
    fun a u ⟨s, h, hu⟩ => WP.mono (enc_ok h.1 hu) fun w ⟨hK, hout⟩ => ⟨s, h, u, hu, hK, hout⟩) ?_
  · change AtEnc s₁ u₁ at j₁
    change AtEnc s₂ u₂ at j₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [j₁.x8, j₂.x8, h₁.fb, h₂.fb]
    · rw [j₁.x9, j₂.x9, h₁.gpr (r := .x3) (by decide), h₂.gpr (r := .x3) (by decide)]
    · rw [j₁.x10, j₂.x10, h₁.2.h6, h₂.2.h6]
    · rw [j₁.x11, j₂.x11, h₁.gpr (r := .x7) (by decide), h₂.gpr (r := .x7) (by decide)]
    · rw [j₁.x12, j₂.x12, h₁.2.args 0 (by decide), h₂.2.args 0 (by decide)]
  refine RelCT.seq (afterEnc_ct c) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, h₁, m₁⟩ ⟨s₂, h₂, m₂⟩ =>
    ⟨by rw [m₁.sp, m₂.sp, h₁.fb, h₂.fb], fun _ h => absurd h List.not_mem_nil⟩

end VG.Proof.RsaPkcs1Sig.AArch64.Sgn
