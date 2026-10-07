import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCT

/-!
# `vg_rsa_pkcs1_recover` on AArch64: constant time

Everything the function reads is public, but the taint analysis cannot see
it of the bytes it loads: the branches on the call's result, on `encode`'s
and on `compare`'s are pinned by correctness (`two_ite`), and the code
between them is checked by the taint analysis (`two_taint`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Rec

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Recover
open VG.Impl.RsaPkcs1Sig.AArch64 (encode compare)
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 restore)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite two_alloc)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stackArgs_three fb eval_zero' leak_eq4)
open VG.Proof.MlKem.AArch64 (Only eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The taint checks -/

section
variable {α : Type} {Φ : α → State → Prop}

theorem lenCheck_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block lenCheck) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem zeroArgs_taint (h : Pins Φ [.x0, .x1]) : RelCT isa (Two Φ) zeroArgs fun _ _ => True :=
  two_taint [.x0, .x1] h (by taint_decide)

theorem pubArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem restore_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block restore) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem zeroKept_taint (h : Pins Φ [.x19, .x20]) : RelCT isa (Two Φ) zeroKept fun _ _ => True :=
  two_taint [.x19, .x20] h (by taint_decide)

theorem encArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block encArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem encode_taint (h : Pins Φ [.x8, .x9, .x10, .x11, .x12]) : RelCT isa (Two Φ) encode fun _ _ => True :=
  two_taint [.x8, .x9, .x10, .x11, .x12] h (by taint_decide)

theorem cmpArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block cmpArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem compare_taint (h : Pins Φ [.x13, .x14, .x15]) : RelCT isa (Two Φ) compare fun _ _ => True :=
  two_taint [.x13, .x14, .x15] h (by taint_decide)

theorem copyOut_taint (h : Pins Φ [.x19, .x20, .x21]) : RelCT isa (Two Φ) copyOut fun _ _ => True :=
  two_taint [.x19, .x20, .x21] h (by taint_decide)

end


/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, `hash`, and the bytes of `n`, `e` and the signature. -/
structure PubR (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x7], s.gpr r = a.gpr r
  h6 : (s.gpr .x6).setWidth 32 = (a.gpr .x6).setWidth 32
  args : ∀ i < 3, stackArg s i = stackArg a i
  bn : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat
  be : Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x4) (a.gpr .x5).toNat
  bg : Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .x7) (stackArg a 0).toNat

theorem PubR.refl (s : State) : PubR s s :=
  ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem leak_eq3 {a b c a' b' c' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (h : (a ++ b ++ c).map (·.toNat) = (a' ++ b' ++ c').map (·.toNat)) : a = a' ∧ b = b' ∧ c = c' := by
  have hi : a ++ b ++ c = a' ++ b' ++ c' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  obtain ⟨h₁, rfl⟩ := List.append_inj hi (by simp [ha, hb])
  obtain ⟨rfl, rfl⟩ := List.append_inj h₁ ha
  exact ⟨rfl, rfl, rfl⟩

theorem pubR_of {S : Nat} {s₁ s₂ : State} (h : (Spec.RsaPkcs1Sig.recoverContract abi S).pub s₁ s₂) :
    PubR s₁ s₂ := by
  sig_pub [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, stackArgs_three,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2⟩ := h
  obtain ⟨hn, he, hg⟩ := leak_eq3 (by rw [bytesAt_length, bytesAt_length, h3])
    (by rw [bytesAt_length, bytesAt_length, h5]) hl
  refine ⟨hsp.symm, fun r hr => ?_, h6.symm, fun i hi => ?_, hn.symm, he.symm, hg.symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h7.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm]

/-! ## The points of the code -/

/-- An entry state with the anchor's public data. -/
def E (K : Nat) (a s : State) : Prop := PreR K s ∧ PubR a s

theorem E.fb {K : Nat} {a s : State} (h : E K a s) : fb s = fb a := by
  show s.sp - _ = a.sp - _; rw [h.2.sp]

theorem E.gpr {K : Nat} {a s : State} (h : E K a s) {r : Reg} (hr : r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x7]) :
    s.gpr r = a.gpr r := h.2.g r hr

theorem E.valA {K : Nat} {a s : State} (h : E K a s) : valA s = valA a := by
  show Ver.fb s + _ = Ver.fb a + _; rw [h.fb, h.gpr (r := .x3) (by decide), h.gpr (r := .x1) (by decide)]

theorem pubOut_eq {K : Nat} {a s : State} (h : E K a s) (hsig : stackArg s 0 = s.gpr .x3) :
    pubOut s = pubOut a := by
  have hsa : stackArg a 0 = a.gpr .x3 := by rw [← h.2.args 0 (by decide), hsig, h.gpr (by decide)]
  have hg := h.2.bg
  rw [hsig, hsa] at hg
  unfold pubOut
  rw [h.2.bn, h.2.be, hg]

/-- The hash function and `EM₁`, of the anchor. -/
def hA (a : State) : Spec.RsaPkcs1Sig.Hash :=
  (Spec.RsaPkcs1Sig.Hash.ofId ((a.gpr .x6).setWidth 32).toNat).getD .md5

def emA (a : State) : List Byte := (pubOut a).getD []

theorem E.hh {K : Nat} {a s : State} (h : E K a s) :
    Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some (hA a) ∧ (s.gpr .x1).toNat = (hA a).len := by
  obtain ⟨h', e, l⟩ := h.1.hh
  have e' := e
  rw [h.2.h6] at e'
  unfold hA; rw [e']
  exact ⟨e, l⟩

theorem encRes_eq {K : Nat} {a s : State} (h : E K a s) :
    encRes s (hA a) (emA a) = encRes a (hA a) (emA a) := by
  unfold encRes; rw [h.gpr (r := .x3) (by decide)]

/-- `J a` at a point of the code, from an entry state with the anchor `a`'s
public data and a signature of `k` bytes. -/
def At (K : Nat) (J : State → State → State → Prop) (a t : State) : Prop :=
  ∃ s, E K a s ∧ stackArg s 0 = s.gpr .x3 ∧ J a s t

/-- The encoding of the anchor's hash value. -/
def emA' (a : State) : List Byte := (encRes a (hA a) (emA a)).getD []

/-- The points of the code after the call. -/
def JC (_ : State) : State → State → Prop := AtCall
def JA (_ : State) : State → State → Prop := AfterCall
def JE (a : State) (s u : State) : Prop := AtEnc s (emA a) u
def JF (a : State) (s w : State) : Prop := AfterEnc s (hA a) (emA a) w
def JG (a : State) (s v : State) : Prop := AtCmp s (hA a) (emA a) (emA' a) v
def JH (a : State) (s y : State) : Prop := AfterCmp s (hA a) (emA a) (emA' a) y
def JM (_ : State) : State → State → Prop := Mid

theorem pins_mid {K : Nat} {J : State → State → State → Prop} (hJ : ∀ a s t, J a s t → Mid s t) :
    Pins (At K J) [.x19, .x20, .x21] := fun a t₁ t₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ => by
  have m₁ := hJ _ _ _ j₁; have m₂ := hJ _ _ _ j₂
  refine ⟨by rw [m₁.sp, m₂.sp, h₁.fb, h₂.fb], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [m₁.x19, m₂.x19, h₁.gpr (by decide), h₂.gpr (by decide)]
  · rw [m₁.x20, m₂.x20, h₁.gpr (by decide), h₂.gpr (by decide)]
  · rw [m₁.x21, m₂.x21, h₁.gpr (by decide), h₂.gpr (by decide)]

theorem pins_sub {α : Type} {Φ : α → State → Prop} {rs rs' : List Reg} (h : Pins Φ rs)
    (hs : ∀ r ∈ rs', r ∈ rs := by decide) : Pins Φ rs' := fun a s₁ s₂ h₁ h₂ =>
  ⟨(h a s₁ s₂ h₁ h₂).1, fun r hr => (h a s₁ s₂ h₁ h₂).2 r (hs r hr)⟩

theorem pins_and {α : Type} {Φ : α → State → Prop} {P : State → Prop} {rs : List Reg} (h : Pins Φ rs) :
    Pins (fun a s => Φ a s ∧ P s) rs := fun a s₁ s₂ h₁ h₂ => h a s₁ s₂ h₁.1 h₂.1

theorem pinsA {K : Nat} : Pins (At K JA) [.x19, .x20, .x21] := pins_mid fun _ _ _ j => j.toMid
theorem pinsF {K : Nat} : Pins (At K JF) [.x19, .x20, .x21] := pins_mid fun _ _ _ j => j.mid
theorem pinsG {K : Nat} : Pins (At K JG) [.x19, .x20, .x21] := pins_mid fun _ _ _ j => j.mid
theorem pinsH {K : Nat} : Pins (At K JH) [.x19, .x20, .x21] := pins_mid fun _ _ _ j => j.mid
theorem pinsM {K : Nat} : Pins (At K JM) [.x19, .x20, .x21] := pins_mid fun _ _ _ j => j

/-! ## The call -/

theorem call_ct (c : PubChecked) :
    RelCT isa (Two (At c.stack JC)) (.call c.name c.code) fun _ _ => True := by
  refine pubCallCT c fun t₁ t₂ ⟨a, ⟨s₁, h₁, g₁, c₁⟩, ⟨s₂, h₂, g₂, c₂⟩⟩ => ?_
  change AtCall s₁ t₁ at c₁
  change AtCall s₂ t₂ at c₂
  refine ⟨pubOk_of c h₁.1 c₁ g₁, pubOk_of c h₂.1 c₂ g₂, ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, h₁.fb, h₂.fb]
  · have e : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x7], s₁.gpr r = s₂.gpr r :=
      fun r hr => (h₁.gpr hr).trans (h₂.gpr hr).symm
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0, h₁.fb, h₂.fb]
    · rw [c₁.x1, c₂.x1, e .x3 (by decide)]
    · rw [c₁.x2, c₂.x2, e .x2 (by decide)]
    · rw [c₁.x3, c₂.x3, e .x3 (by decide)]
    · rw [c₁.x4, c₂.x4, e .x4 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x5 (by decide)]
    · rw [c₁.x6, c₂.x6, e .x7 (by decide)]
    · rw [c₁.x7, c₂.x7, e .x3 (by decide)]
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [c₁.a0, c₂.a0, h₁.2.args 1 (by decide), h₂.2.args 1 (by decide)]
    · rw [c₁.a1, c₂.a1, h₁.2.args 2 (by decide), h₂.2.args 2 (by decide)]
  · rw [(call_bytes h₁.1 c₁ g₁).1, (call_bytes h₂.1 c₂ g₂).1, h₁.2.bn, h₂.2.bn]
  · rw [(call_bytes h₁.1 c₁ g₁).2.1, (call_bytes h₂.1 c₂ g₂).2.1, h₁.2.be, h₂.2.be]

/-! ## After the call -/

theorem release_ct {K : Nat} : RelCT isa (Two (At K JH)) release fun _ _ => True := by
  unfold release
  refine two_ite (fun a y₁ y₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ => ?_)
    (zeroKept_taint (pins_and (pins_sub pinsH))) (copyOut_taint (pins_and pinsH))
  rw [eval_nonzero, eval_nonzero]
  have e₁ := j₁.hiff; have e₂ := j₂.hiff
  by_cases he : emA a = emA' a
  · rw [e₁.mpr he, e₂.mpr he]
  · have n₁ : (y₁.gpr .x12 != 0) = true := bne_iff_ne.mpr fun h => he (e₁.mp h)
    have n₂ : (y₂.gpr .x12 != 0) = true := bne_iff_ne.mpr fun h => he (e₂.mp h)
    rw [n₁, n₂]

theorem tail_ct {K : Nat} : RelCT isa (Two (At K JF)) tail fun _ _ => True := by
  unfold tail
  have res : ∀ {a s w}, E K a s → AfterEnc s (hA a) (emA a) w →
      isa.eval (.zero .x .x0) w = some (encRes a (hA a) (emA a)).isNone := fun {a s w} h hw => by
    have hr := hw.res
    rw [encRes_eq h] at hr
    rw [eval_zero']
    cases he : encRes a (hA a) (emA a) with
    | none => rw [he] at hr; rw [hr]; rfl
    | some em' => rw [he] at hr; rw [hr.1]; rfl
  refine two_ite (fun a w₁ w₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ => by rw [res h₁ j₁, res h₂ j₂])
    (zeroKept_taint (pins_and (pins_sub pinsF))) ?_
  refine RelCT.seq (two_post (Ψ := At K JG) (cmpArgs_taint (pins_and (pins_sub pinsF)))
    fun a w ⟨⟨s, h, g, hw⟩, hb⟩ => ?_) ?_
  · have hr := hw.res
    rw [res h hw] at hb
    rw [encRes_eq h] at hr
    cases he : encRes a (hA a) (emA a) with
    | none => rw [he] at hb; cases hb
    | some em' =>
      rw [he] at hr
      obtain ⟨_, b1, b2, hv⟩ := hr
      have : emA' a = em' := by unfold emA'; rw [he]; rfl
      exact WP.mono (cmpArgs_ok hw.mid b1 b2 hv) fun v hv' => ⟨s, h, g, by unfold JG; rw [this]; exact hv'⟩
  refine RelCT.seq (two_post (Ψ := At K JH)
    (compare_taint fun a v₁ v₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ => ⟨by rw [j₁.mid.sp, j₂.mid.sp, h₁.fb, h₂.fb],
      fun r hr => ?_⟩)
    fun a v ⟨s, h, g, hv⟩ => WP.mono (cmp_ok h.1 hv) fun y hy => ⟨s, h, g, hy⟩) release_ct
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [j₁.x13, j₂.x13, h₁.gpr (r := .x3) (by decide), h₂.gpr (r := .x3) (by decide)]
  · rw [j₁.x14, j₂.x14, h₁.fb, h₂.fb]
  · rw [j₁.x15, j₂.x15, h₁.fb, h₂.fb]

theorem afterPub_ct {K : Nat} : RelCT isa (Two (At K JA)) afterPub fun _ _ => True := by
  unfold afterPub
  have res : ∀ {a s t}, E K a s → stackArg s 0 = s.gpr .x3 → AfterCall s t →
      isa.eval (.zero .w .x0) t = some (pubOut a).isNone := fun {a s t} h g ht => by
    have hr := ht.res
    rw [pubOut_eq h g] at hr
    simp only [eval, State.read]
    cases hpo : pubOut a with
    | none => rw [hpo] at hr; rw [hr.1]; rfl
    | some y => rw [hpo] at hr; rw [hr.1]; rfl
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, g₁, a₁⟩ ⟨s₂, h₂, g₂, a₂⟩ => by rw [res h₁ g₁ a₁, res h₂ g₂ a₂])
    (zeroKept_taint (pins_and (pins_sub pinsA))) ?_
  refine RelCT.seq (two_post (Ψ := At K JE) (encArgs_taint (pins_and (pins_sub pinsA)))
    fun a t ⟨⟨s, h, g, ht⟩, hb⟩ => ?_) ?_
  · change AfterCall s t at ht
    have hr := ht.res
    rw [res h g ht] at hb
    rw [pubOut_eq h g] at hr
    cases hpo : pubOut a with
    | none => rw [hpo] at hb; cases hb
    | some em =>
      rw [hpo] at hr
      have : emA a = em := by unfold emA; rw [hpo]; rfl
      exact WP.mono (atEnc_ok h.1 ht.toMid hr.2) fun u hu => ⟨s, h, g, by unfold JE; rw [this]; exact hu⟩
  refine RelCT.seq (two_post (Ψ := At K JF)
    (encode_taint fun a u₁ u₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ => ⟨by rw [j₁.mid.sp, j₂.mid.sp, h₁.fb, h₂.fb],
      fun r hr => ?_⟩)
    fun a u ⟨s, h, g, hu⟩ => WP.mono (enc_ok h.1 h.hh.1 h.hh.2 hu) fun w hw => ⟨s, h, g, hw⟩) tail_ct
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [j₁.x8, j₂.x8, h₁.fb, h₂.fb]
  · rw [j₁.x9, j₂.x9, h₁.gpr (r := .x3) (by decide), h₂.gpr (r := .x3) (by decide)]
  · rw [j₁.x10, j₂.x10, h₁.2.h6, h₂.2.h6]
  · rw [j₁.x11, j₂.x11, h₁.valA, h₂.valA]
  · rw [j₁.x12, j₂.x12, h₁.gpr (r := .x1) (by decide), h₂.gpr (r := .x1) (by decide)]

theorem code_ct (c : PubChecked) :
    RelCT isa (Two (E c.stack)) (code c.name c.code) fun _ _ => True := by
  unfold code
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E c.stack a s ∧ Only [.x8] s t ∧
      t.gpr .x8 = stackArg s 0 - s.gpr .x3)
    (lenCheck_taint fun _ _ _ h₁ h₂ => ⟨by rw [h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩)
    fun a s h => WP.mono (lenCheck_ok h.1) fun t ht => ⟨s, h, ht⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, _, e₁⟩ ⟨s₂, h₂, _, e₂⟩ => by
      rw [eval_len e₁, eval_len e₂, h₁.2.args 0 (by decide), h₂.2.args 0 (by decide),
        h₁.gpr (r := .x3) (by decide), h₂.gpr (r := .x3) (by decide)])
    (zeroArgs_taint fun _ _ _ ⟨⟨s₁, h₁, o₁, _⟩, _⟩ ⟨⟨s₂, h₂, o₂, _⟩, _⟩ =>
      ⟨by rw [o₁.sp, o₂.sp, h₁.2.sp, h₂.2.sp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [o₁.get .x0, o₂.get .x0, h₁.gpr (by decide), h₂.gpr (by decide)]
        · rw [o₁.get .x1, o₂.get .x1, h₁.gpr (by decide), h₂.gpr (by decide)]⟩) ?_
  refine two_alloc (R := fun _ _ => True) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := At c.stack JC)
    (pubArgs_taint fun _ _ _ ⟨u₁, ⟨⟨s₁, h₁, o₁, _⟩, _⟩, e₁⟩ ⟨u₂, ⟨⟨s₂, h₂, o₂, _⟩, _⟩, e₂⟩ =>
      ⟨by rw [e₁, e₂]; simp only [allocated, o₁.sp, o₂.sp, h₁.2.sp, h₂.2.sp],
        fun _ h => absurd h List.not_mem_nil⟩) fun a u ⟨t, ⟨⟨s, h, o, e⟩, hb⟩, hu⟩ => ?_) ?_
  · have hsig : stackArg s 0 = s.gpr .x3 := by
      rw [eval_len e] at hb; simpa using hb
    subst hu
    exact WP.mono (pubArgs_ok h.1 (by simp [allocated, o.sp]) (by simp [allocated, o.rd])
      (by simp [allocated, o.sp, o.wr]) (by simp [allocated, o.mem])
      (fun r hr => by simp only [allocated]; exact o.gpr r (by simpa using hr)) (fun r hr => o.vcs r hr))
      fun t ht => ⟨s, h, hsig, ht⟩
  refine RelCT.seq (two_post (Ψ := At c.stack JA) (call_ct c) fun a t ⟨s, h, g, ht⟩ =>
    WP.mono (call_ok c h.1 ht g) fun w hw => ⟨s, h, g, hw⟩) ?_
  refine RelCT.seq (two_post (Ψ := At c.stack JM) afterPub_ct
    fun a t ⟨s, h, g, ht⟩ => WP.mono (afterPub_ok h.1 h.hh.1 h.hh.2 ht) fun w hw => ⟨s, h, g, hw.1⟩) ?_
  exact restore_taint (pins_sub pinsM)

end VG.Proof.RsaPkcs1Sig.AArch64.Rec
