import VerifiedGarbage.Proof.AesXts.X86_64.Body
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# XTS-AES on x86-64: constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`), as AES-CBC's are (`Proof/AesCbc/X86_64/CT.lean`): the taint
analysis covers the code around the call, from the registers the correctness
proof pins to the public arguments (`PInv`), and the call of the block
function on all the blocks is constant time by its own proof (`blk_rel`).
-/

namespace VG.Proof.AesXts.X86_64

open VG VG.X86_64 VG.Impl.AesXts.X86_64
open VG.Impl.AesCbc.X86_64 (save setup restore)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Spec.Aes (bytesAt)

/-- A piece of code the taint analysis checks from the registers `rs`, which
agree in two runs, with what each run reaches. -/
theorem taint_rel {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop} (rs : List Reg)
    (ht : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true)
    (ha : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ F₁ ∧ WP isa c s₂ F₂) :
    RelCT isa P c fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ := by
  obtain ⟨_, ht⟩ := ht
  exact ((RelCT.taint (A := taint) (P := P) _ (fun s₁ s₂ h => Taint.agree_ofRegs (ha s₁ s₂ h)) ht).wp hw).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem saveT_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15])
    (.block saveT) h).isSome = true := ⟨_, by taint_decide⟩

theorem pass_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15]) pass h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem callArgs_taint : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r10, .r11, .r12, .r15])
    (.block callArgs) h).isSome = true := ⟨_, by taint_decide⟩

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (modeX86_64 (AesXts.xtsMode enc)).pub s₀ s₀')
include hq

theorem PInv.agree {ys ys' : List (List Byte)} {x10 x11 x10' x11' : BitVec 64} {i : Nat} {s₁ s₂ : State}
    (h₁ : PInv s₀ ys x10 x11 i s₁) (h₂ : PInv s₀' ys' x10' x11' i s₂) :
    ∀ r ∈ [Reg.r12, .r13, .r14, .r15], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.r12, h₂.r12, pub_Iv hq]
  · rw [h₁.r13, h₂.r13, pub_blk hq]
  · rw [h₁.r14, h₂.r14, pub_N hq]
  · rw [h₁.r15, h₂.r15, pub_S hq]

/-- All the blocks, in two runs. -/
theorem batch_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    (hp : UPre s₀) (hp' : UPre s₀') (hN : 0 < N s₀) :
    RelCT isa (fun a b => LInv (AesXts.xtsMode enc) s₀ 0 a ∧ LInv (AesXts.xtsMode enc) s₀' 0 b) (batch b)
      fun a b => LInv (AesXts.xtsMode enc) s₀ (N s₀) a ∧ LInv (AesXts.xtsMode enc) s₀' (N s₀') b := by
  have hN' : 0 < N s₀' := by rw [← pub_N hq]; exact hN
  -- The tweak saved.
  have a := taint_rel _ saveT_taint (P := fun a b => LInv (AesXts.xtsMode enc) s₀ 0 a ∧ LInv (AesXts.xtsMode enc) s₀' 0 b)
    (fun _ _ h r hr => LInv.agree hq h.1 h.2 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
    (F₁ := PInv s₀ (blks s₀) (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) 0)
    (F₂ := PInv s₀' (blks s₀') (blk s₀' 0) (BitVec.ofNat 64 (N s₀')) 0)
    fun _ _ h => ⟨saveT_wp hp (fun _ _ _ => rfl) (fun _ _ _ => rfl) h.1,
      saveT_wp hp' (fun _ _ _ => rfl) (fun _ _ _ => rfl) h.2⟩
  -- The first pass.
  have p₁ := taint_rel _ pass_taint (P := fun a b => PInv s₀ (blks s₀) (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) 0 a ∧
      PInv s₀' (blks s₀') (blk s₀' 0) (BitVec.ofNat 64 (N s₀')) 0 b) (fun _ _ h => PInv.agree hq h.1 h.2)
    (F₁ := PInv s₀ (blks s₀) (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) (N s₀))
    (F₂ := PInv s₀' (blks s₀') (blk s₀' 0) (BitVec.ofNat 64 (N s₀')) (N s₀'))
    fun _ _ h => ⟨pass_wp hp hN h.1, pass_wp hp' hN' h.2⟩
  -- The arguments of the call.
  have c := taint_rel _ callArgs_taint (P := fun a b =>
      PInv s₀ (blks s₀) (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) (N s₀) a ∧
      PInv s₀' (blks s₀') (blk s₀' 0) (BitVec.ofNat 64 (N s₀')) (N s₀') b)
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h.1.rbx, h.2.rbx, pub_W hq]
      · rw [h.1.rbp, h.2.rbp, pub_rsi hq]
      · rw [h.1.r10, h.2.r10, pub_blk hq]
      · rw [h.1.r11, h.2.r11, pub_N hq]
      · rw [h.1.r12, h.2.r12, pub_Iv hq]
      · rw [h.1.r15, h.2.r15, pub_S hq])
    (F₁ := fun (s' : State) => Proof.AesOcb.X86_64.BCall s' (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
      PInv s₀ (xored (iv0 s₀) (blks s₀) (N s₀)) (s'.gpr .r10) (s'.gpr .r11) 0 s')
    (F₂ := fun (s' : State) => Proof.AesOcb.X86_64.BCall s' (W s₀') (Dp s₀') (S s₀') (R s₀') (N s₀') ∧
      PInv s₀' (xored (iv0 s₀') (blks s₀') (N s₀')) (s'.gpr .r10) (s'.gpr .r11) 0 s')
    fun _ _ h => ⟨callArgs_wp hp h.1, callArgs_wp hp' h.2⟩
  -- The call.
  have k := (Proof.AesOcb.X86_64.blk_rel ok ct (name := b.name) (P := fun a b =>
      (Proof.AesOcb.X86_64.BCall a (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
        PInv s₀ (xored (iv0 s₀) (blks s₀) (N s₀)) (a.gpr .r10) (a.gpr .r11) 0 a) ∧
      (Proof.AesOcb.X86_64.BCall b (W s₀') (Dp s₀') (S s₀') (R s₀') (N s₀') ∧
        PInv s₀' (xored (iv0 s₀') (blks s₀') (N s₀')) (b.gpr .r10) (b.gpr .r11) 0 b)) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, h.1.1, by
        rw [pub_W hq, pub_Dp hq, pub_S hq, pub_R hq, pub_N hq]; exact h.2.1,
        by rw [h.1.2.rsp, h.2.2.rsp, pub_rsp hq]⟩).wp
    (F₁ := fun (s' : State) => PInv s₀ ((xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀)))
      (s'.gpr .r10) (s'.gpr .r11) 0 s')
    (F₂ := fun (s' : State) => PInv s₀' ((xored (iv0 s₀') (blks s₀') (N s₀')).map (ciphOf enc (R s₀') (wK s₀')))
      (s'.gpr .r10) (s'.gpr .r11) 0 s')
    fun _ _ h => ⟨call_wp hp enc ok nosp depth hf h.1.1 h.1.2, call_wp hp' enc ok nosp depth hf h.2.1 h.2.2⟩
  -- The second pass.
  have p₂ := taint_rel _ pass_taint (P := fun a b =>
      PInv s₀ ((xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀))) (a.gpr .r10) (a.gpr .r11) 0 a ∧
      PInv s₀' ((xored (iv0 s₀') (blks s₀') (N s₀')).map (ciphOf enc (R s₀') (wK s₀'))) (b.gpr .r10)
        (b.gpr .r11) 0 b) (fun _ _ h => PInv.agree hq h.1 h.2)
    (F₁ := LInv (AesXts.xtsMode enc) s₀ (N s₀)) (F₂ := LInv (AesXts.xtsMode enc) s₀' (N s₀'))
    fun _ _ h => ⟨WP.mono (pass_wp hp hN h.1) fun _ h => final_of enc h,
      WP.mono (pass_wp hp' hN' h.2) fun _ h => final_of enc h⟩
  exact a.seq (p₁.seq (c.seq ((k.mono (fun _ _ h => h) fun _ _ h => h.2).seq p₂)))

end

theorem crypt_ct (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16)) :
    ConstantTime isa (modeX86_64 (AesXts.xtsMode enc)).pre (modeX86_64 (AesXts.xtsMode enc)).pub (crypt b) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (ends_rel h₁ h₂ hq (fun hp hp' hN => batch_rel hq ok ct nosp depth hf hp hp' hN)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.X86_64
