module
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Final

public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Pre
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Words

/-!
# ML-DSA signing on x86 (32-bit): `vg_mldsa{44,65,87}_sign`

The body in the leaf's frame (`piece`), and `Verified` against `signContract`
(`verified`), for any implementations of the primitives that `PrimsOk` says
are verified, and any of the three parameter sets.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece P0 LeafPost satState)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-- A piece whose precondition on the initial state is part of `Pre`. -/
theorem pre_pure {Pre : State → Prop} {Pub : State → State → Prop} {A B : State → State → Prop} {c : Prog isa}
    (φ : State → Prop) (h : Piece Pre Pub (fun s₀ s => A s₀ s ∧ φ s₀) B c) :
    Piece (fun s => Pre s ∧ φ s) Pub A B c where
  wp s₀ s h₀ ha := h.wp s₀ s h₀.1 ⟨ha, h₀.2⟩
  ct s₀ s₀' h₀ h₀' hq := (h.ct s₀ s₀' h₀.1 h₀'.1 hq).mono (fun _ _ ⟨a, a'⟩ => ⟨⟨a, h₀.2⟩, ⟨a', h₀'.2⟩⟩)
    fun _ _ h => h

/-- The runs' precondition: the layout, and `KEYS`. -/
abbrev KPre (p : Params) (s₀ : State) : Prop := TPre (Y p) s₀ ∧ KeysPre p s₀

/-- `vg_mldsa*_sign_core`, a leaf around `body`. -/
theorem piece (F : PrimsOk P) (ps : PS p) (hsp : NoSp (body P p)) :
    Piece (KPre p) (SPub p) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Done p s₀) s₀ s') (sign P p) := by
  have hb := pre_pure (KeysPre p) (body_piece F ps)
  exact Piece.leaf (W (Y p)) hsp (fun _ hp => ⟨hp.1.E0_big, by have := hp.1.sp'; omega⟩) (fun _ hp => hp.1.hW)
    (fun _ _ _ _ hq => hq.1.1) (hb.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h.2⟩)

/-- `KEYS` as the contract says it. -/
theorem keysW_eq (ps : PS p) {s₀ : State} (hp : TPre (Y p) s₀) :
    keysW s₀ = keysWord s₀.mem ((arg s₀ 4).setWidth 64) := by
  unfold keysW keysWord
  rw [Buf.addr_eq hp (sc_ok' ps (by decide) (by decide))]

theorem slot_addr (ps : PS p) {s₀ : State} (hp : TPre (Y p) s₀) {j : Nat} (hj : j < nS p) :
    Buf.addr s₀ (pS j) = (arg s₀ 4).setWidth 64 + BitVec.ofNat 64 (oP j) :=
  Buf.addr_eq hp (slot_ok' ps hj)

/-- The contract's precondition on `KEYS`, as the proof's. -/
theorem keysPre_of (ps : PS p) {s₀ : State} (hp : TPre (Y p) s₀)
    (h : keysWord s₀.mem ((arg s₀ 4).setWidth 64) = 0 ∨
      KeysIn p s₀.mem ((arg s₀ 4).setWidth 64) (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen)) :
    KeysPre p s₀ := by
  have hk := ps.hk
  have hl := ps.hl
  rcases h with h | h
  · exact .inl (by rw [keysW_eq ps hp]; exact h)
  have sk : skOf p s₀ = bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen := by
    simp only [skOf, bSk, addr0]
  refine .inr ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have e := h j (by omega)
    rw [PreparedKey.secret_s1 p _ hj, ← sk] at e
    rw [slot_addr ps hp (by simp only [nS, s1B]; omega)]
    exact e
  · have e := h (p.ℓ + j) (by omega)
    rw [PreparedKey.secret_s2 p _ hj, ← sk,
      show 5 + 2 * p.k + 2 * p.ℓ + (p.ℓ + j) = s2B p + j by simp only [s2B]; omega] at e
    rw [slot_addr ps hp (by simp only [nS, s2B]; omega)]
    exact e
  · have e := h (p.ℓ + p.k + j) (by omega)
    rw [PreparedKey.secret_t0 p _ hj, ← sk,
      show 5 + 2 * p.k + 2 * p.ℓ + (p.ℓ + p.k + j) = t0B p + j by simp only [t0B]; omega] at e
    rw [slot_addr ps hp (by simp only [nS, t0B]; omega)]
    exact e

theorem core_pub_of (ps : PS p) {s₀ s₀' : State} (hp : TPre (Y p) s₀) (hp' : TPre (Y p) s₀')
    (h : (signCoreContract p X86.abi 96).pub s₀ s₀') : SPub p s₀ s₀' := by
  sig_pub [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4⟩ := h
  simp only [List.cons.injEq] at e₂
  refine ⟨⟨e₁, fun i hi => ?_, ?_⟩, ?_⟩
  · rw [Y_n] at hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    exacts [a0, a1, a2, a3, a4]
  · have e := e₂.1
    simp only [keysOf, keysW_eq ps hp, keysW_eq ps hp']
    by_cases h₁ : keysWord s₀.mem ((arg s₀ 4).setWidth 64) = 0 <;>
      by_cases h₂ : keysWord s₀'.mem ((arg s₀' 4).setWidth 64) = 0 <;>
      simp only [h₁, h₂, ↓reduceIte] at e ⊢ <;> cases e
  · simp only [skOf, muOf, rndOf, bSk, bMu, bRnd, addr0]
    exact e₂.2

/-- Memory with the arguments `0`, `0x2000`, `0x3000`, `0x8000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x20 else if a = 0x500d then 0x30 else if a = 0x5011 then 0x80 else if a = 0x5016 then 1 else 0

theorem sat (h3 : Ok3 p) : ∃ s, (signCoreContract p X86.abi 96).pre s := by
  rcases h3 with rfl | rfl | rfl
  · refine ⟨satState satMem [⟨0, 2560⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 2420⟩, ⟨0x10000, 77824⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | exact Or.inl (by decide +kernel)
        | decide +kernel
  · refine ⟨satState satMem [⟨0, 4032⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 3309⟩, ⟨0x10000, 103424⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | exact Or.inl (by decide +kernel)
        | decide +kernel
  · refine ⟨satState satMem [⟨0, 4896⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 4627⟩, ⟨0x10000, 144384⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | exact Or.inl (by decide +kernel)
        | decide +kernel

/-- `vg_mldsa{44,65,87}_sign_core`, with the primitives `P`, is verified against `signCoreContract`. -/
theorem verified (F : PrimsOk P) (h3 : Ok3 p) (hsp : NoSp (body P p)) :
    Verified X86.target (sign P p) (signCoreContract p X86.abi 96) := by
  have ps := PS.of h3
  refine Piece.verified (((piece F ps hsp).pre_mono
    (fun _ h => ⟨(core_pre_of h).1, keysPre_of ps (core_pre_of h).1 (core_pre_of h).2⟩)
    fun _ _ h h' hq => core_pub_of ps (core_pre_of h).1 (core_pre_of h').1 hq).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) (sat h3)
  obtain ⟨habi, -, -, s, hd, hm, hax⟩ := hq
  refine ⟨habi, ?_⟩
  sig_post [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  rw [sw32, hax, hm]
  unfold Done at hd
  simp only [skOf, muOf, rndOf, bSk, bMu, bRnd, bSig, addr0] at hd
  exact hd

end VG.Proof.MlDsa.X86.Sign
