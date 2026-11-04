module

public import VerifiedGarbage.Proof.MlDsa.X86.Message.Entry
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Pre
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: the layouts' shapes

Untrusted: everything here is checked by Lean. The contracts' public data,
spelled out (`SPub`, `VPub`), and the layouts of `sign_message`,
`verify_message` and `verify_message_cached` (`slay`, `vlay`) meet what the
proofs of the check, the entry and the hashes need (`sShape`, `vShape`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (E0 P0)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

/-- The public data of `signMessageContract p X86.abi 136`. -/
structure SPub (p : Params) (s s' : State) : Prop where
  esp : s.gpr .esp = s'.gpr .esp
  leak : signMessageLeak p (bytesAt s.mem ((arg s 0).setWidth 64) p.skLen)
      (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat) (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
      (bytesAt s.mem ((arg s 5).setWidth 64) 32) =
    signMessageLeak p (bytesAt s'.mem ((arg s' 0).setWidth 64) p.skLen)
      (bytesAt s'.mem ((arg s' 1).setWidth 64) (arg s' 2).toNat)
      (bytesAt s'.mem ((arg s' 3).setWidth 64) (arg s' 4).toNat) (bytesAt s'.mem ((arg s' 5).setWidth 64) 32)
  args : ∀ i < 8, arg s i = arg s' i

theorem spub_of {p : Params} {s s' : State} (h : (signMessageContract p X86.abi 136).pub s s') : SPub p s s' := by
  sig_pub [signMessageContract, signMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  refine ⟨e₁, e₂, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6
  | 7, _ => exact a7

/-- The public data of `verifyMessageContract p X86.abi 132` (`n = 7`) and
`verifyMessageCachedContract p X86.abi 132` (`n = 8`). -/
structure VPub (p : Params) (n : Nat) (s s' : State) : Prop where
  esp : s.gpr .esp = s'.gpr .esp
  leak : leakBytes (bytesAt s.mem ((arg s 0).setWidth 64) p.pkLen ++
      bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat ++
      bytesAt s.mem ((arg s 5).setWidth 64) p.sigLen) =
    leakBytes (bytesAt s'.mem ((arg s' 0).setWidth 64) p.pkLen ++
      bytesAt s'.mem ((arg s' 1).setWidth 64) (arg s' 2).toNat ++
      bytesAt s'.mem ((arg s' 3).setWidth 64) (arg s' 4).toNat ++ bytesAt s'.mem ((arg s' 5).setWidth 64) p.sigLen)
  args : ∀ i < n, arg s i = arg s' i

theorem vpub_of {p : Params} {s s' : State} (h : (verifyMessageContract p X86.abi 132).pub s s') : VPub p 7 s s' := by
  sig_pub [verifyMessageContract, verifyMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4, a5, a6⟩ := h
  refine ⟨e₁, e₂, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6

theorem cpub_of {p : Params} {s s' : State} (h : (verifyMessageCachedContract p X86.abi 132).pub s s') :
    VPub p 8 s s' := by
  sig_pub [verifyMessageCachedContract, verifyMessageCachedSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  refine ⟨e₁, e₂, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6
  | 7, _ => exact a7

/-- The leaf's frame, below the stack pointer on entry. -/
theorem frame_eq {s : State} (h : 16 ≤ (s.gpr .esp).toNat) :
    (⟨(E0 s).setWidth 64 - 16#64, 16⟩ : Region) = below (s.gpr .esp) 16 := by
  simp only [below]; rw [Taint.sub_setWidth h]

theorem sShape {p : Params} (hp : p ∈ params) : Shape (SPre p) (SPub p) (slay p) 7 p where
  sp _ _ := rfl
  rd _ _ := rfl
  wr _ _ := rfl
  argv s₀ _ i hi := by
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
  ctxLen _ _ := rfl
  scr _ _ := rfl
  siLt _ _ := by show 7 < 8; decide
  E _ _ := rfl
  ok _ h₀ h8 := slay_ok hp h₀ h8
  e16 s₀ h₀ := ⟨by show 16 ≤ (s₀.gpr .esp).toNat; have := h₀.sp; omega,
    by show (s₀.gpr .esp).toNat + 4 ≤ _; have := h₀.spA; omega⟩
  fit _ h₀ := by show _ + 4 + 4 * 8 ≤ _; have := h₀.spA; omega
  fd s₀ h₀ := by
    rw [frame_eq (by have := h₀.sp; omega)]
    exact (stk_eq h₀.sp ▸ h₀.kArgs).sub_left (below_sub (by omega) h₀.sp)
  ain _ h₀ := List.mem_append_right _ (by
    rw [h₀.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  n5 _ _ := by show 5 ≤ 8; decide
  pubE _ _ _ _ hq := hq.esp
  pubA _ _ _ _ hq := ⟨hq.args 4 (by decide), hq.args 7 (by decide)⟩
  pubL _ _ _ _ hq := ⟨hq.esp, by simp only [slay, hq.args 0 (by decide), hq.args 1 (by decide),
      hq.args 2 (by decide), hq.args 3 (by decide), hq.args 4 (by decide), hq.args 5 (by decide),
      hq.args 6 (by decide), hq.args 7 (by decide)], by simp only [Lay.X32, slay, hq.args 7 (by decide)], rfl,
    hq.args 0 (by decide), hq.args 1 (by decide), hq.args 2 (by decide), hq.args 3 (by decide),
    hq.args 4 (by decide)⟩

theorem vlay_argv {p : Params} {n : Nat} (hn : n = 7 ∨ n = 8) (s : State) :
    ∀ i < n, (vlay p n s).argv.getD i 0 = arg s i := by
  rcases hn with rfl | rfl <;> intro i hi
  · match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
  · match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl

theorem vShape {p : Params} (hp : p ∈ params) {n : Nat} {T : State → List Region} :
    Shape (VPre p n T) (VPub p n) (vlay p n) 6 p where
  sp _ _ := rfl
  rd _ _ := rfl
  wr _ _ := rfl
  argv s₀ h₀ := vlay_argv h₀.hn s₀
  ctxLen _ _ := rfl
  scr _ _ := rfl
  siLt _ h₀ := by show 6 < n; have := h₀.hn; omega
  E _ _ := rfl
  ok _ h₀ h8 := vlay_ok hp h₀ h8
  e16 s₀ h₀ := ⟨by show 16 ≤ (s₀.gpr .esp).toNat; have := h₀.sp; omega,
    by show (s₀.gpr .esp).toNat + 4 ≤ _; have := h₀.spA; omega⟩
  fit _ h₀ := by show _ + 4 + 4 * n ≤ _; have := h₀.spA; omega
  fd s₀ h₀ := by
    rw [frame_eq (by have := h₀.sp; omega)]
    exact (stk_eq h₀.sp ▸ h₀.kArgs).sub_left (below_sub (by omega) h₀.sp)
  ain _ h₀ := List.mem_append_right _ (by
    rw [h₀.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  n5 _ h₀ := by show 5 ≤ n; have := h₀.hn; omega
  pubE _ _ _ _ hq := hq.esp
  pubA _ _ h₀ _ hq := ⟨hq.args 4 (by have := h₀.hn; omega), hq.args 6 (by have := h₀.hn; omega)⟩
  pubL s₀ s₀' h₀ _ hq := by
    have hn := h₀.hn
    have e : ((List.range (n - 7)).map fun i => arg s₀ (7 + i)) = (List.range (n - 7)).map fun i => arg s₀' (7 + i) :=
      List.map_congr_left fun i hi => hq.args _ (by rw [List.mem_range] at hi; omega)
    exact ⟨hq.esp, by simp only [vlay, hq.args 0 (by omega), hq.args 1 (by omega),
      hq.args 2 (by omega), hq.args 3 (by omega), hq.args 4 (by omega), hq.args 5 (by omega),
      hq.args 6 (by omega), e], by simp only [Lay.X32, vlay, hq.args 6 (by omega)], rfl,
    hq.args 0 (by omega), hq.args 1 (by omega), hq.args 2 (by omega), hq.args 3 (by omega),
    hq.args 4 (by omega)⟩

/-- A shape, for a stronger precondition. -/
theorem Shape.pre_mono {Pre Pre' : State → Prop} {Pub : State → State → Prop} {lay : State → Lay} {si : Nat}
    {p : Params} (hS : Shape Pre Pub lay si p) (h : ∀ s, Pre' s → Pre s) : Shape Pre' Pub lay si p where
  sp s₀ h₀ := hS.sp s₀ (h _ h₀)
  rd s₀ h₀ := hS.rd s₀ (h _ h₀)
  wr s₀ h₀ := hS.wr s₀ (h _ h₀)
  argv s₀ h₀ := hS.argv s₀ (h _ h₀)
  ctxLen s₀ h₀ := hS.ctxLen s₀ (h _ h₀)
  scr s₀ h₀ := hS.scr s₀ (h _ h₀)
  siLt s₀ h₀ := hS.siLt s₀ (h _ h₀)
  E s₀ h₀ := hS.E s₀ (h _ h₀)
  ok s₀ h₀ := hS.ok s₀ (h _ h₀)
  e16 s₀ h₀ := hS.e16 s₀ (h _ h₀)
  fit s₀ h₀ := hS.fit s₀ (h _ h₀)
  fd s₀ h₀ := hS.fd s₀ (h _ h₀)
  ain s₀ h₀ := hS.ain s₀ (h _ h₀)
  n5 s₀ h₀ := hS.n5 s₀ (h _ h₀)
  pubE s₀ s₀' h₀ h₀' := hS.pubE s₀ s₀' (h _ h₀) (h _ h₀')
  pubA s₀ s₀' h₀ h₀' := hS.pubA s₀ s₀' (h _ h₀) (h _ h₀')
  pubL s₀ s₀' h₀ h₀' := hS.pubL s₀ s₀' (h _ h₀) (h _ h₀')

end VG.Proof.MlDsa.X86.Message
