import VerifiedGarbage.Proof.AesXts.X86.Body

/-!
# XTS-AES on x86: constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`), as AES-CBC's are (`Proof/AesCbc/X86/CT.lean`): the taint
analysis covers the code around the call, from `esp`, the stack arguments
and `esi` (which the correctness proof pins to the public arguments,
`PInv`), and the call of the block function on all the blocks, in its frame,
is constant time by its own proof (AES-OCB's `blk_ct`).
-/

namespace VG.Proof.AesXts.X86

open VG VG.X86 VG.Impl.AesXts.X86
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86
open VG.Proof.MdStream.X86 (eval_ne)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Spec.Aes (bytesAt)

/-- A piece of code the taint analysis checks from the registers `rs`, `esp`
and the stack arguments, which agree in two runs, with what each run
reaches. -/
theorem taint_rel {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop} (rs : List Reg)
    (ht : ∃ h, (taint.check (argTaint rs (4 + 4 * 6)) c h).isSome = true)
    (ha : ∀ s₁ s₂, P s₁ s₂ → VG.X86.Taint.Agree (argTaint rs (4 + 4 * 6)) s₁ s₂)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ F₁ ∧ WP isa c s₂ F₂) :
    RelCT isa P c fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ := by
  obtain ⟨_, ht⟩ := ht
  exact ((RelCT.taint (A := taint) (P := P) _ ha ht).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

theorem saveT_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 6)) (.block saveT) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem passBody_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block passBody) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem callArgs_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 6)) (.block callArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem PInv.pt {s₀ : State} (hp : UPre s₀) {ys : List (List Byte)} {i : Nat} {s : State}
    (h : PInv s₀ ys i s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep h.big hi⟩

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (modeX86 (AesXts.xtsMode enc)).pub s₀ s₀')
include hq

theorem PInv.agree (hp : UPre s₀) (hp' : UPre s₀') {ys ys' : List (List Byte)} {i : Nat} {s₁ s₂ : State}
    (h₁ : PInv s₀ ys i s₁) (h₂ : PInv s₀' ys' i s₂) :
    VG.X86.Taint.Agree (argTaint [.esi] (4 + 4 * 6)) s₁ s₂ :=
  Pt.agree hq hp hp' (h₁.pt hp) (h₂.pt hp') fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.esi, h₂.esi, pub_D32 hq]

/-- A pass over the blocks, in two runs: the taint analysis checks each
iteration. -/
theorem pass_rel (hp : UPre s₀) (hp' : UPre s₀') (hN : 0 < N s₀) {ys ys' : List (List Byte)} :
    RelCT isa (fun a b => PInv s₀ ys 0 a ∧ PInv s₀' ys' 0 b) pass
      fun a b => PInv s₀ ys (N s₀) a ∧ PInv s₀' ys' (N s₀') b := by
  have hN' := pub_N hq
  let L (n : Nat) (s₁ s₂ : State) : Prop :=
    ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ PInv s₀ ys k s₁ ∧ PInv s₀' ys' k s₂
  refine (RelCT.loop (M := isa) L (fun n => ?_) (N s₀ - 0)).mono
    (fun _ _ h => ⟨0, rfl, hN, h.1, h.2⟩) fun _ _ h => h
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : L n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := taint_rel [.esi] passBody_taint
    (P := fun a b => N s₀ - k = N s₀ - k ∧ k < N s₀ ∧ PInv s₀ ys k a ∧ PInv s₀' ys' k b)
    (fun _ _ h => PInv.agree hq hp hp' h.2.2.1 h.2.2.2)
    (F₁ := fun (s : State) => PInv s₀ ys (k + 1) s ∧ s.zf = some (decide (k + 1 = N s₀)))
    (F₂ := fun (s : State) => PInv s₀' ys' (k + 1) s ∧ s.zf = some (decide (k + 1 = N s₀')))
    fun _ _ h => ⟨pstep_wp hp hk h.2.2.1, pstep_wp hp' (by rw [← hN']; exact hk) h.2.2.2⟩
  refine ct.mono (fun _ _ h => h) fun s₁ s₂ ⟨⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s₁ = _; rw [eval_ne, z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN']; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + 1 = N s₀ := by simpa using hf
    exact ⟨h0 ▸ l₁, by rw [← hN', ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : k + 1 ≠ N s₀ := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, by omega, l₁, l₂⟩

/-- All the blocks, in two runs. -/
theorem batch_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub b.code)
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    (hp : UPre s₀) (hp' : UPre s₀') (hN : 0 < N s₀) :
    RelCT isa (fun a b => LInv (AesXts.xtsMode enc) s₀ 0 a ∧ LInv (AesXts.xtsMode enc) s₀' 0 b) (batch b)
      fun a b => LInv (AesXts.xtsMode enc) s₀ (N s₀) a ∧ LInv (AesXts.xtsMode enc) s₀' (N s₀') b := by
  have hN' : 0 < N s₀' := by rw [← pub_N hq]; exact hN
  -- The tweak saved.
  have a := taint_rel [] saveT_taint (P := fun a b => LInv (AesXts.xtsMode enc) s₀ 0 a ∧
      LInv (AesXts.xtsMode enc) s₀' 0 b)
    (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr)
    (F₁ := PInv s₀ (blks s₀) 0) (F₂ := PInv s₀' (blks s₀') 0)
    fun _ _ h => ⟨saveT_wp hp (fun _ _ _ => rfl) (fun _ _ _ => rfl) h.1,
      saveT_wp hp' (fun _ _ _ => rfl) (fun _ _ _ => rfl) h.2⟩
  -- The first pass.
  have p₁ := pass_rel hq hp hp' hN (ys := blks s₀) (ys' := blks s₀')
  -- `T` restored, and the arguments of the call.
  have c := taint_rel [] callArgs_taint
    (P := fun a b => PInv s₀ (blks s₀) (N s₀) a ∧ PInv s₀' (blks s₀') (N s₀') b)
    (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr)
    (F₁ := fun (s' : State) => Proof.AesOcb.X86.BCall s' (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
      PInv s₀ (xored (iv0 s₀) (blks s₀) (N s₀)) 0 s')
    (F₂ := fun (s' : State) => Proof.AesOcb.X86.BCall s' (W s₀') (Dp s₀') (S s₀') (R s₀') (N s₀') ∧
      PInv s₀' (xored (iv0 s₀') (blks s₀') (N s₀')) 0 s')
    fun _ _ h => ⟨callArgs_wp hp h.1, callArgs_wp hp' h.2⟩
  -- The call.
  have k := (RelCT.mono (Proof.AesOcb.X86.blk_ct (fn := ⟨b.name, b.code⟩) ok ct
      (I := fun s => Proof.AesOcb.X86.BCall s (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧ s.gpr .esp = E s₀)
      fun _ h => h) (P' := fun a b =>
        (Proof.AesOcb.X86.BCall a (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
          PInv s₀ (xored (iv0 s₀) (blks s₀) (N s₀)) 0 a) ∧
        (Proof.AesOcb.X86.BCall b (W s₀') (Dp s₀') (S s₀') (R s₀') (N s₀') ∧
          PInv s₀' (xored (iv0 s₀') (blks s₀') (N s₀')) 0 b))
      (fun _ _ h => ⟨⟨h.1.1, h.1.2.esp⟩, by
        rw [pub_W hq, pub_Dp hq, pub_S hq, pub_R hq, pub_N hq, pub_E hq]; exact ⟨h.2.1, h.2.2.esp⟩⟩)
      fun _ _ _ => trivial).wp
    (F₁ := PInv s₀ ((xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀))) 0)
    (F₂ := PInv s₀' ((xored (iv0 s₀') (blks s₀') (N s₀')).map (ciphOf enc (R s₀') (wK s₀'))) 0)
    fun _ _ h => ⟨call_wp hp enc ok nosp stack hf h.1.1 h.1.2, call_wp hp' enc ok nosp stack hf h.2.1 h.2.2⟩
  -- The second pass.
  have p₂ := (pass_rel hq hp hp' hN).mono (fun _ _ h => h) fun _ _ h =>
    (⟨final_of enc h.1, final_of enc h.2⟩ : LInv (AesXts.xtsMode enc) s₀ (N s₀) _ ∧
      LInv (AesXts.xtsMode enc) s₀' (N s₀') _)
  exact a.seq (p₁.seq (c.seq ((k.mono (fun _ _ h => h) fun _ _ h => h.2).seq p₂)))

end

theorem crypt_ct (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub b.code)
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16)) :
    ConstantTime isa (modeX86 (AesXts.xtsMode enc)).pre (modeX86 (AesXts.xtsMode enc)).pub (crypt b) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (ends_rel h₁ h₂ hq (fun hp hp' hN => batch_rel hq ok ct nosp stack hf hp hp' hN)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.X86
