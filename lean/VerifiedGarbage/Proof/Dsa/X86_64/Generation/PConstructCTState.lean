module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructPlan
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PShape
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashShape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArgumentBlocksCT
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArguments
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStores
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStores
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadCT
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArgumentBlocksCT
meta import VerifiedGarbage.Proof.RsaKeyGen.Table
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArguments

/-! ### `Dsa.X86_64.Generation.CandidateWorkspaceCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.CandidateFrameCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.CandidateArithmeticCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.CandidateLoadState`, which this module and modules that import it used -/

section

/-! # Public values and workspace preservation through the two candidate loads -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

structure CandidatePublic where
  B : Addr
  Z : Nat
  w : Nat
  xp : Addr
  qp : Addr
  xb : List Byte
  qb : List Byte

def CandidatePublic.xLoad (p : CandidatePublic) : LoadPublic := ⟨p.B, p.Z, p.w, p.xp, p.xb⟩
def CandidatePublic.qLoad (p : CandidatePublic) : LoadPublic := ⟨p.B, p.Z, p.w, p.qp, p.qb⟩
def CandidatePublic.reduction (p : CandidatePublic) : ReductionPublic :=
  ⟨p.B, p.Z, p.w, Spec.Rsa.os2ip p.xb, Spec.Rsa.os2ip p.qb⟩

structure CandidateInput (p : CandidatePublic) (s : State) : Prop where
  x : LoadState 16 17 p.xLoad s
  q : LoadState 18 19 p.qLoad s
  qPositive : 0 < Spec.Rsa.os2ip p.qb
  qFits : 2 * Spec.Rsa.os2ip p.qb < 2 ^ (64 * p.w)

structure CandidateFirst (p : CandidatePublic) (s : State) : Prop where
  q : LoadState 18 19 p.qLoad s
  x : wv s.mem p.B (slot p.w 0) p.w = Spec.Rsa.os2ip p.xb
  qPositive : 0 < Spec.Rsa.os2ip p.qb
  qFits : 2 * Spec.Rsa.os2ip p.qb < 2 ^ (64 * p.w)

structure CandidateLoaded (p : CandidatePublic) (s : State) : Prop where
  ws : Ws s p.B p.Z p.w
  x : wv s.mem p.B (slot p.w 0) p.w = Spec.Rsa.os2ip p.xb
  q : wv s.mem p.B (slot p.w 2) p.w = Spec.Rsa.os2ip p.qb
  qPositive : 0 < Spec.Rsa.os2ip p.qb
  qFits : 2 * Spec.Rsa.os2ip p.qb < 2 ^ (64 * p.w)

theorem candidateFirst_state {p : CandidatePublic} {s : State} (h : CandidateInput p s) :
    WP isa (seqs (loadA 0 16 17)) s (CandidateFirst p) := by
  refine WP.mono (loadCandidateArray_ok h.x.ws (by decide : 0 < 16) (by decide : 16 < 32)
    (by decide : 17 < 32) h.x.pointer h.x.length h.x.source h.x.positive h.x.fits)
    fun t ⟨ht, hx, f, hk⟩ => ?_
  have hdr (d : Nat) (hd : d + 8 ≤ 256) : word t.mem p.B d = word s.mem p.B d := by
    apply f.word_eq
    · simp only [List.mem_singleton]; rintro r rfl
      left; simp only [slot, hdrBytes]; omega_using [hd]
    · have := h.x.ws.h256; have := h.x.ws.scr.nowrap; omega_using [hd]
  refine ⟨⟨ht, (hdr 144 (by decide)).trans h.q.pointer, (hdr 152 (by decide)).trans h.q.length,
    h.q.source.congrK ?_ hk, h.q.positive, h.q.fits⟩, hx, h.qPositive, h.qFits⟩
  intro a ha
  apply f a
  simp only [List.mem_singleton]; rintro r rfl
  right
  exact Nat.le_trans (h.x.ws.sl (by decide : 0 < 16)) ha

theorem candidateSecond_state {p : CandidatePublic} {s : State} (h : CandidateFirst p s) :
    WP isa (seqs (loadA 2 18 19)) s (CandidateLoaded p) := by
  have hw : Ws s p.B p.Z p.w := h.q.ws
  refine WP.mono (loadCandidateArray_ok h.q.ws (by decide : 2 < 16) (by decide : 18 < 32)
    (by decide : 19 < 32) h.q.pointer h.q.length h.q.source h.q.positive h.q.fits)
    fun t ⟨ht, hq, f, _⟩ => ?_
  change Frm p.B [ar p.w 2] s.mem t.mem at f
  refine ⟨ht, ?_, hq, h.qPositive, h.qFits⟩
  rw [f.wv_eq (by
    simp only [List.mem_singleton]; rintro r rfl
    left; simp only [slot, hdrBytes]; omega_using [])
    (by have := hw.sl (by decide : 0 < 16); have := hw.scr.nowrap; omega_arith)]
  exact h.x

theorem candidateDouble_state {p : CandidatePublic} {s : State} (h : CandidateLoaded p s) :
    WP isa (Impl.Dsa.X86_64.Generation.doubleArray 2) s (ReductionStart p.reduction) := by
  refine WP.mono (doubleArray_ok h.ws (by decide : 2 < 16) (by rw [h.q]; exact h.qFits))
    fun t ⟨hq, ho, hk⟩ => ?_
  have f : Frm p.B [ar p.w 2] s.mem t.mem :=
    Frm.of_outside (ho.mono (n' := 8 * (p.w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp [ar])
  have ht := h.ws.congr f (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) hk (by decide)
  refine ⟨ht, ?_, ?_, h.qPositive⟩
  · change wv t.mem p.B (slot p.w 0) p.w = Spec.Rsa.os2ip p.xb
    rw [f.wv_eq (by
      simp only [List.mem_singleton]; rintro r rfl
      left; simp only [slot, hdrBytes]; omega_using [])
      (by have := h.ws.sl (by decide : 0 < 16); have := h.ws.scr.nowrap; omega_arith)]
    exact h.x
  · change wv t.mem p.B (slot p.w 2) p.w = 2 * Spec.Rsa.os2ip p.qb
    rw [hq, h.q]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.ReductionExponentCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.CandidateReductionCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.ReductionCT`, which this module and modules that import it used -/

section

/-! # Public-width arithmetic pieces used in p-candidate reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation

variable {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
  (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a))

include hws

theorem doubleArray_ct (dst : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.seq (.block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base dst .rbx)) (wordLoop 0 shlBody)) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (doubleArray dst) s (Ψ a)) :
    RelCT isa (Two Φ) (doubleArray dst) (Two Ψ) := by
  unfold doubleArray at *
  simp only [List.append_assoc] at hw ⊢
  exact ws_ct B Z w hws ht hw

theorem subtractRemainder_ct (dst x rem : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.seq (.block (([.mov32 .rbp (.imm 0)] : List Instr) ++ (base x .r8 ++ (base rem .r10 ++ base dst .rsi))))
        (wordLoop 0 subBody)) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (subtractRemainder dst x rem) s (Ψ a)) :
    RelCT isa (Two Φ) (subtractRemainder dst x rem) (Two Ψ) := by
  unfold subtractRemainder at *
  simp only [List.append_assoc] at hw ⊢
  exact ws_ct B Z w hws ht hw

theorem incrementEven_ct (dst : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.block (base dst .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .add .rax (.imm 1),
        .store (at0 .rbx) .rax] : List Instr))) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.block (incrementEven dst)) s (Ψ a)) :
    RelCT isa (Two Φ) (.block (incrementEven dst)) (Two Ψ) := by
  unfold incrementEven at *
  simp only [List.append_assoc] at hw ⊢
  exact ws_block_ct B Z w hws ht hw

theorem candidateDivmod_ct
    (hw : ∀ a s, Φ a s → WP isa (divmod 0 1 2 3) s (Ψ a)) :
    RelCT isa (Two Φ) (divmod 0 1 2 3) (Two Ψ) := by
  have e : divmod 0 1 2 3 = .seq (.block (ws ++ (base 1 .r8 ++ ([.mov .r11 (.reg .r12)] ++
      (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)])))))
      (.seq zeroAccLoop (.loop (divStep 0 1 2 3) .ne)) := by
    simp only [divmod, divInit, seqs, List.append_assoc]
  rw [e] at hw ⊢
  exact ws_ct B Z w hws (by taint_decide) hw

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Constant time of p reduction from X and 2q -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Bignum.X86_64

theorem reductionCopy_ct : RelCT isa (Two ReductionStart) (copyA 4 0) (Two ReductionCopied) := by
  have e : copyA 4 0 = .seq (.block (ws ++ (base 0 .rsi ++ base 4 .rbx)))
      VG.Impl.Rsa.X86_64.copyWords := by simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct ReductionPublic.B ReductionPublic.Z ReductionPublic.w (fun _ _ h => h.1)
    (by taint_decide) (fun _ _ h => by rw [← e]; exact reductionCopy_state h)

theorem reductionDivide_ct :
    RelCT isa (Two ReductionCopied) (divmod 0 1 2 3) (Two ReductionDivided) :=
  candidateDivmod_ct ReductionPublic.B ReductionPublic.Z ReductionPublic.w
    (fun _ _ h => h.1.1) (fun _ _ h => reductionDivide_state h)

theorem reductionSubtract_ct : RelCT isa (Two ReductionDivided)
    (Impl.Dsa.X86_64.Generation.subtractRemainder 5 4 1) (Two ReductionSubtracted) :=
  subtractRemainder_ct ReductionPublic.B ReductionPublic.Z ReductionPublic.w
    (fun _ _ h => h.1) 5 4 1 (by taint_decide) (fun _ _ h => reductionSubtract_state h)

theorem reductionIncrement_ct : RelCT isa (Two ReductionSubtracted)
    (.block (Impl.Dsa.X86_64.Generation.incrementEven 5)) (fun _ _ => True) := by
  have ct := incrementEven_ct (Φ := ReductionSubtracted) (Ψ := fun _ _ => True)
    ReductionPublic.B ReductionPublic.Z ReductionPublic.w (fun _ _ h => h.1) 5 (by taint_decide)
    (fun _ _ h => WP.mono (incrementEven_ok h.1 (by decide : 5 < 16) h.2) (fun _ _ => True.intro))
  exact ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro)

theorem reduceCandidate_ct : RelCT isa (Two ReductionStart)
    Impl.Dsa.X86_64.Generation.reduceCandidate (fun _ _ => True) :=
  RelCT.seq reductionCopy_ct (RelCT.seq reductionDivide_ct (RelCT.seq reductionSubtract_ct reductionIncrement_ct))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Constant time of the saved generator-exponent calculation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64

def DoubleReady (a : Nat) (p : ReductionPublic) (s : State) : Prop :=
  Ws s p.B p.Z p.w ∧ 2 * wv s.mem p.B (slot p.w a) p.w < 2 ^ (64 * p.w)

theorem doubleZero_ct : RelCT isa (Two (DoubleReady 0))
    (Impl.Dsa.X86_64.Generation.doubleArray 0) (fun _ _ => True) := by
  have ct := doubleArray_ct (Φ := DoubleReady 0) (Ψ := fun _ _ => True)
    ReductionPublic.B ReductionPublic.Z ReductionPublic.w (fun _ _ h => h.1) 0 (by taint_decide)
    (fun _ _ h => WP.mono (doubleArray_ok h.1 (by decide : 0 < 16) h.2) (fun _ _ => True.intro))
  exact ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro)

theorem reduceExponent_ct : RelCT isa (Two ReductionStart)
    (.seq Impl.Dsa.X86_64.Generation.reduceCandidate (Impl.Dsa.X86_64.Generation.doubleArray 0))
    (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := DoubleReady 0) reduceCandidate_ct ?_) doubleZero_ct
  intro p s h
  have hxlt : p.x < 2 ^ (64 * p.w) := h.2.1 ▸ wv_lt s.mem p.B (slot p.w 0) p.w
  have bound : 2 * (p.x / (2 * p.q)) ≤ p.x := by
    calc
      2 * (p.x / (2 * p.q)) ≤ p.q * (2 * (p.x / (2 * p.q))) :=
        Nat.le_mul_of_pos_left _ h.2.2.2
      _ = 2 * p.q * (p.x / (2 * p.q)) := by ac_rfl
      _ ≤ p.x := Nat.mul_div_le _ _
  exact WP.mono (reduceCandidate_ok h.1 h.2.1 h.2.2.1 h.2.2.2)
    fun t ⟨ht, _, hq, _, _⟩ => ⟨ht, by rw [hq]; omega_using [hxlt, bound]⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Constant time of complete candidate and generator-exponent arithmetic -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

theorem candidateFirst_ct : RelCT isa (Two CandidateInput)
    (seqs (loadA 0 16 17)) (Two CandidateFirst) :=
  two_post (two_map CandidatePublic.xLoad (fun _ _ h => h.x)
    (loadCandidate_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => candidateFirst_state h)

theorem candidateSecond_ct : RelCT isa (Two CandidateFirst)
    (seqs (loadA 2 18 19)) (Two CandidateLoaded) :=
  two_post (two_map CandidatePublic.qLoad (fun _ _ h => h.q)
    (loadCandidate_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => candidateSecond_state h)

theorem candidateDouble_ct : RelCT isa (Two CandidateLoaded)
    (Impl.Dsa.X86_64.Generation.doubleArray 2)
    (Two fun (p : CandidatePublic) s => ReductionStart p.reduction s) :=
  doubleArray_ct CandidatePublic.B CandidatePublic.Z CandidatePublic.w
    (fun _ _ h => h.ws) 2 (by taint_decide) (fun _ _ h => candidateDouble_state h)

theorem candidateArithmetic_ct : RelCT isa (Two CandidateInput)
    Impl.Dsa.X86_64.Generation.candidateArithmetic (fun _ _ => True) :=
  RelCT.seq candidateFirst_ct (RelCT.seq candidateSecond_ct (RelCT.seq candidateDouble_ct
    (two_map CandidatePublic.reduction (fun _ _ h => h) reduceExponent_ct)))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.CandidateStoresCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.StoreCT`, which only this module used -/

section

/-! # Constant time of full-width candidate and exponent stores -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

structure StorePublic where
  B : Addr
  Z : Nat
  w : Nat
  out : Addr

structure StoreState (ptr : Nat) (p : StorePublic) (s : State) : Prop where
  ws : Ws s p.B p.Z p.w
  pointer : word s.mem p.B (8 * ptr) = p.out
  length : word s.mem p.B 136 = BitVec.ofNat 64 (8 * p.w)
  mask : word s.mem p.B (8 * Public.sMask) = mask true
  write : ∀ i < 8 * p.w, InRegions s.wr (off p.out i) 1
  outside : ∀ i < 8 * p.w, p.Z ≤ ofs p.B (off p.out i)

def storePublicRegs (a : Nat) (p : StorePublic) : Reg → BitVec 64
  | .rdi => p.B
  | .rbx => off p.B (slot p.w a)
  | .rsi => p.out
  | .rcx => BitVec.ofNat 64 (8 * p.w)
  | _ => 0

theorem storeCandidate_ct {a ptr : Nat} (ha : a < 16) (hp : ptr < 32)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base a .rbx ++
      ([.mov .rsi (.mem (hdr ptr)), .mov .rcx (.mem (hdr 17)),
        .mov .r15 (.mem (hdr Public.sMask))] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (StoreState ptr)) (seqs (storeA a ptr 17 Public.sMask)) (fun _ _ => True) := by
  have ct := pin_ct (c₂ := storeBE) (Φ := StoreState ptr) (Ψ := fun _ _ => True)
    [.rdi] [.rdi, .rbx, .rsi, .rcx] (storePublicRegs a) (by
      intro p s t hs ht r hr
      simp only [List.mem_singleton] at hr
      subst r; exact hs.ws.rdi.trans ht.ws.rdi.symm) ht
    (fun p s h => WP.mono (storeBlk_ok h.ws hp (by decide : 17 < 32) h.pointer h.length)
      fun t ⟨hbx, hsi, hcx, hdi⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide)
    (fun _ _ h => WP.mono (storeCandidateArray_ok h.ws ha hp h.pointer h.length h.mask h.write h.outside)
      (fun _ _ => True.intro))
  exact ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Save p and its exponent with public addressing -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

structure CandidateOutputs where
  B : Addr
  Z : Nat
  w : Nat
  p : Addr
  exponent : Addr

def CandidateOutputs.pStore (p : CandidateOutputs) : StorePublic := ⟨p.B, p.Z, p.w, p.p⟩
def CandidateOutputs.eStore (p : CandidateOutputs) : StorePublic := ⟨p.B, p.Z, p.w, p.exponent⟩
def CandidateStoreState (p : CandidateOutputs) (s : State) : Prop :=
  StoreState 20 p.pStore s ∧ StoreState 21 p.eStore s

theorem candidateStoreFirst_state {p : CandidateOutputs} {s : State} (h : CandidateStoreState p s) :
    WP isa (seqs (storeA 5 20 17 Public.sMask)) s (StoreState 21 p.eStore) := by
  refine WP.mono (storeCandidateArray_ok h.1.ws (by decide : 5 < 16) (by decide : 20 < 32)
    h.1.pointer h.1.length h.1.mask h.1.write h.1.outside) fun t ⟨_, _, ht, f, hk⟩ => ?_
  change Frm p.B [(p.Z, 2 ^ 64)] s.mem t.mem at f
  have hw : Ws s p.B p.Z p.w := h.1.ws
  have header (d : Nat) (hd : d + 8 ≤ 256) : word t.mem p.B d = word s.mem p.B d := by
    apply f.word_eq
    · simp only [List.mem_singleton]; rintro r rfl
      exact Or.inl (Nat.le_trans hd hw.h256)
    · have := hw.h256; have := hw.scr.nowrap; omega_using [hd]
  exact ⟨ht, (header 168 (by decide)).trans h.2.pointer,
    (header 136 (by decide)).trans h.2.length,
    (header (8 * Public.sMask) (by decide)).trans h.2.mask,
    (fun i hi => by rw [hk.2.2]; exact h.2.write i hi), h.2.outside⟩

theorem candidateStores_ct : RelCT isa (Two CandidateStoreState)
    Impl.Dsa.X86_64.Generation.candidateStores (fun _ _ => True) := by
  refine RelCT.seq (two_post
    (two_map CandidateOutputs.pStore (fun _ _ h => h.1)
      (storeCandidate_ct (by decide : 5 < 16) (by decide : 20 < 32) (by taint_decide)))
    (fun _ _ h => candidateStoreFirst_state h)) ?_
  exact two_map CandidateOutputs.eStore (fun _ _ h => h)
    (storeCandidate_ct (by decide : 0 < 16) (by decide : 21 < 32) (by taint_decide))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Candidate arithmetic accepts the persistent frame's actual words -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/CandidateBuildCT.lean`, which only this module imported.
section

/-! # The complete byte-to-byte p-candidate builder has a public trace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64

structure CandidateBuildPublic where
  input : CandidatePublic
  p : Addr
  exponent : Addr

def CandidateBuildPublic.outputs (p : CandidateBuildPublic) : CandidateOutputs :=
  ⟨p.input.B, p.input.Z, p.input.w, p.p, p.exponent⟩

def CandidateBuildState (p : CandidateBuildPublic) (s : State) : Prop :=
  CandidateInput p.input s ∧ CandidateStoreState p.outputs s

theorem candidateArithmetic_storeState {p : CandidateBuildPublic} {s : State} (h : CandidateBuildState p s) :
    WP isa Impl.Dsa.X86_64.Generation.candidateArithmetic s (CandidateStoreState p.outputs) := by
  have hw : Ws s p.input.B p.input.Z p.input.w := h.1.x.ws
  refine WP.mono (candidateArithmetic_ok hw h.1.x.pointer h.1.x.length h.1.q.pointer h.1.q.length
    h.1.x.source h.1.q.source h.1.x.positive h.1.x.fits h.1.q.positive h.1.q.fits
    h.1.qPositive h.1.qFits) fun t ⟨ht, _, _, f, hk⟩ => ?_
  have header (d : Nat) (hd : d + 8 ≤ 256) : word t.mem p.input.B d = word s.mem p.input.B d := by
    apply f.word_eq
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;>
        left <;> simp only [slot, hdrBytes] <;> omega_using [hd]
    · have := hw.h256; have := hw.scr.nowrap; omega_using [hd]
  exact ⟨⟨ht, (header 160 (by decide)).trans h.2.1.pointer,
    (header 136 (by decide)).trans h.2.1.length,
    (header (8 * Public.sMask) (by decide)).trans h.2.1.mask,
    (fun i hi => by rw [hk.2.2]; exact h.2.1.write i hi), h.2.1.outside⟩,
    ⟨ht, (header 168 (by decide)).trans h.2.2.pointer,
    (header 136 (by decide)).trans h.2.2.length,
    (header (8 * Public.sMask) (by decide)).trans h.2.2.mask,
    (fun i hi => by rw [hk.2.2]; exact h.2.2.write i hi), h.2.2.outside⟩⟩

theorem candidateBuild_ct : RelCT isa (Two CandidateBuildState)
    Impl.Dsa.X86_64.Generation.candidateBuild (fun _ _ => True) :=
  RelCT.seq (two_post (two_map CandidateBuildPublic.input (fun _ _ h => h.1) candidateArithmetic_ct)
    (fun _ _ h => candidateArithmetic_storeState h))
    (two_map CandidateBuildPublic.outputs (fun _ _ h => h) candidateStores_ct)

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.Dsa.Generation.Layout

structure CandidateFramePublic where
  B : Addr
  F : Addr
  arena : Addr
  Z : Nat
  w : Nat
  xb : List Byte
  qb : List Byte
  xLength : xb.length = 8 * w
  qLength : qb.length ≤ 8 * w
  qNonempty : 1 ≤ qb.length
  qPositive : 0 < Spec.Rsa.os2ip qb
  qFits : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w)
  separate : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8
  pOutside : ∀ i < 8 * w, Z ≤ ofs B (off (off arena p) i)
  eOutside : ∀ i < 8 * w, Z ≤ ofs B (off (off arena exponent) i)

def CandidateFramePublic.build (c : CandidateFramePublic) : CandidateBuildPublic :=
  ⟨⟨c.B, c.Z, c.w, off c.arena shaped, off c.arena q, c.xb, c.qb⟩,
    off c.arena p, off c.arena exponent⟩

def CandidateFramePublic.pointers (c : CandidateFramePublic) : ArgumentPointers := ⟨c.B, c.F⟩

structure CandidateFrameInputs (c : CandidateFramePublic) (s : State) : Prop where
  stack : s.gpr .rsp = c.F
  read : ∀ k < 37, InRegions (s.rd ++ s.wr) (off c.F (8 * k)) 8
  arena : word s.mem c.F 40 = c.arena
  x : Src s c.B c.Z (off c.arena shaped) c.xb
  q : Src s c.B c.Z (off c.arena q) c.qb
  pWrite : ∀ i < 8 * c.w, InRegions s.wr (off (off c.arena p) i) 1
  eWrite : ∀ i < 8 * c.w, InRegions s.wr (off (off c.arena exponent) i) 1

def CandidateFrameBefore (pLen qLen : Nat) (c : CandidateFramePublic) (s : State) : Prop :=
  CandidateFrameInputs c s ∧ Ws s c.B c.Z c.w ∧ c.xb.length = pLen ∧ c.qb.length = qLen

theorem candidateFrame_ready {pLen qLen : Nat} {c : CandidateFramePublic} {s : State}
    (h : CandidateFrameBefore pLen qLen c s) :
    WP isa (.block (headerArguments (candidateArguments pLen qLen))) s (CandidateBuildState c.build) := by
  have hp : pLen < 2 ^ 31 := by omega_using [h.2.1.w2, c.xLength, h.2.2.1]
  have hq : qLen < 2 ^ 31 := by omega_using [hp, c.qLength, c.xLength, h.2.2.1, h.2.2.2]
  have hw := candidateArguments_ok h.2.1 hp hq h.1.stack h.1.read
    (W := fun k => word s.mem c.F (8 * k)) (fun _ _ => rfl) c.separate
  refine WP.mono hw fun t ⟨ht, hxp, hxl, hqp, hql, hpp, hep, hm, hf, hk⟩ => ?_
  have frame : Frm c.B [(128, 128)] s.mem t.mem := Frm.of_outside hf (by simp)
  have bound : ∀ r ∈ [(128, 128)], r.1 + r.2 ≤ c.Z := by
    simp only [List.mem_singleton, forall_eq]; exact h.2.1.h256
  have sx := h.1.x.congrK (InScr.of_frm frame bound) hk
  have sq := h.1.q.congrK (InScr.of_frm frame bound) hk
  have px : word t.mem c.B 128 = off c.arena shaped := by simpa only [h.1.arena] using hxp
  have pq : word t.mem c.B 144 = off c.arena q := by simpa only [h.1.arena] using hqp
  have pp : word t.mem c.B 160 = off c.arena p := by simpa only [h.1.arena] using hpp
  have pe : word t.mem c.B 168 = off c.arena exponent := by simpa only [h.1.arena] using hep
  have xl : word t.mem c.B 136 = BitVec.ofNat 64 c.xb.length := by rw [h.2.2.1]; exact hxl
  have ql : word t.mem c.B 152 = BitVec.ofNat 64 c.qb.length := by rw [h.2.2.2]; exact hql
  have outlen : word t.mem c.B 136 = BitVec.ofNat 64 (8 * c.w) := by rw [← c.xLength]; exact xl
  refine ⟨⟨⟨ht, px, xl, sx, ?_, Nat.le_of_eq c.xLength⟩,
    ⟨ht, pq, ql, sq, c.qNonempty, c.qLength⟩, c.qPositive, c.qFits⟩,
    ⟨ht, pp, outlen, hm, ?_, c.pOutside⟩, ⟨ht, pe, outlen, hm, ?_, c.eOutside⟩⟩
  · change 1 ≤ c.xb.length
    omega_using [c.xLength, h.2.1.w1]
  · intro i hi; rw [hk.2.2]; exact h.1.pWrite i hi
  · intro i hi; rw [hk.2.2]; exact h.1.eWrite i hi

theorem candidateFromFrame_ct (pLen qLen : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .rsp])
      (.block (headerArguments (candidateArguments pLen qLen))) hc).isSome = true) :
    RelCT isa (Two (CandidateFrameBefore pLen qLen)) (candidateFromFrame pLen qLen) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_map CandidateFramePublic.pointers
    (fun _ _ h => ⟨h.2.1.rdi, h.1.stack⟩) (candidateArguments_ct pLen qLen ht))
    (fun _ _ h => candidateFrame_ready h)) ?_
  exact two_map CandidateFramePublic.build (fun _ _ h => h) candidateBuild_ct

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Initialize candidate-reduction scratch while retaining source bytes and frame arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.Dsa.Generation.Layout

structure CandidateWorkspacePublic where
  frame : CandidateFramePublic
  base : frame.B = off frame.arena arithmetic
  room : slot frame.w 16 ≤ frame.Z
  lower : 2 ≤ frame.w
  upper : frame.w < 2 ^ 24
  outside : ∀ k < 37, ∀ i < 8, frame.Z ≤ ofs frame.B (off (off frame.F (8 * k)) i)

def CandidateWorkspaceBefore (w pLen qLen : Nat) (c : CandidateWorkspacePublic) (s : State) : Prop :=
  CandidateFrameInputs c.frame s ∧ Scr s c.frame.B c.frame.Z ∧
    c.frame.w = w ∧ c.frame.xb.length = pLen ∧ c.frame.qb.length = qLen

def CandidateWorkspaceBase (w pLen qLen : Nat) (c : CandidateWorkspacePublic) (s : State) : Prop :=
  CandidateWorkspaceBefore w pLen qLen c s ∧ s.gpr .rdi = c.frame.B

theorem candidateWorkspace_base {w pLen qLen : Nat} {c : CandidateWorkspacePublic} {s : State}
    (h : CandidateWorkspaceBefore w pLen qLen c s) :
    WP isa (.block workspaceBase) s (CandidateWorkspaceBase w pLen qLen c) := by
  have ld := h.1.read 5 (by decide)
  have hv : s.mem.readW (off c.frame.F 40) 64 = c.frame.arena := h.1.arena
  have step : WP isa (.block workspaceBase) s fun t => t.gpr .rdi = c.frame.B ∧ t.mem = s.mem := by
    xrun [workspaceBase, VG.Proof.RsaOaep.X86_64.ea_sp, h.1.stack, ld, hv,
      sx_ofNat (by decide : arithmetic < 2 ^ 31)]
    exact c.base.symm
  refine WP.mono (WP.keep [.rdi] step rfl) fun t ⟨⟨hb, hm⟩, hk⟩ => ?_
  refine ⟨⟨?_, h.2.1.congr hk.2.2, h.2.2⟩, hb⟩
  exact ⟨(hk.gpr (by decide)).trans h.1.stack,
    (fun k hk' => by rw [hk.2.1, hk.2.2]; exact h.1.read k hk'),
    hm ▸ h.1.arena, h.1.x.congrK (fun _ _ => by rw [hm]) hk,
    h.1.q.congrK (fun _ _ => by rw [hm]) hk,
    (fun i hi => by rw [hk.2.2]; exact h.1.pWrite i hi),
    (fun i hi => by rw [hk.2.2]; exact h.1.eWrite i hi)⟩

theorem candidateWorkspace_ready {w pLen qLen : Nat} {c : CandidateWorkspacePublic} {s : State}
    (h : CandidateWorkspaceBase w pLen qLen c s) :
    WP isa (workspace w) s (CandidateFrameBefore pLen qLen c.frame) := by
  have step := workspace_ok h.1.2.1 h.2 c.room c.lower c.upper
  rw [h.1.2.2.1] at step
  refine WP.mono step fun t ⟨ht, _, ff, hk⟩ => ?_
  have hz : 256 ≤ c.frame.Z := Nat.le_trans (Nat.le_add_right 256 _) c.room
  have bound : ∀ r ∈ [(48, 80), (224, 8)], r.1 + r.2 ≤ c.frame.Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega_using [hz]
  have ht' : Ws t c.frame.B c.frame.Z c.frame.w := by rw [h.1.2.2.1]; exact ht
  refine ⟨?_, ht', h.1.2.2.2⟩
  refine ⟨(hk.gpr (by decide)).trans h.1.1.stack, ?_, ?_,
    h.1.1.x.congrK (InScr.of_frm ff bound) hk, h.1.1.q.congrK (InScr.of_frm ff bound) hk, ?_, ?_⟩
  · intro k hk'; rw [hk.2.1, hk.2.2]; exact h.1.1.read k hk'
  · exact (frame_word_of_workspace ff bound (c.outside 5 (by decide))).trans h.1.1.arena
  · intro i hi; rw [hk.2.2]; exact h.1.1.pWrite i hi
  · intro i hi; rw [hk.2.2]; exact h.1.1.eWrite i hi

theorem reduceFromFrame_ct (w pLen qLen : Nat) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi]) (workspace w) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .rsp])
      (.block (headerArguments (candidateArguments pLen qLen))) hc₂).isSome = true) :
    RelCT isa (Two (CandidateWorkspaceBefore w pLen qLen))
      (seqs [.block workspaceBase, workspace w, candidateFromFrame pLen qLen]) (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_post (two_taint [.rsp] ?_ (by taint_decide))
    (fun _ _ h => candidateWorkspace_base h))
    (RelCT.seq (two_post (two_taint [.rdi] ?_ ht₁)
      (fun _ _ h => candidateWorkspace_ready h)) ?_)
  · intro c s t hs ht r hr
    simp only [List.mem_singleton] at hr; subst r
    exact hs.1.stack.trans ht.1.stack.symm
  · intro c s t hs ht r hr
    simp only [List.mem_singleton] at hr; subst r
    exact hs.2.trans ht.2.symm
  · exact two_map CandidateWorkspacePublic.frame (fun _ _ h => h) (candidateFromFrame_ct pLen qLen ht₂)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.PShapeValue`, which this module and modules that import it used -/

section

/-! # The shaped hash bytes are determined by the public seed and offset -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

def HashPlan.shapedValue (p : HashPlan) (H : Spec.Mgf1.Hash) (plen : Nat) : Nat :=
  Spec.Ffdh.candidateOf (8 * plen)
    (VG.Proof.Dsa.Generation.contributions (8 * p.len)
      (fun j => Spec.Dsa.decodeBE (p.digest H j)) (p.count + 1))

theorem hash_shaped_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : State}
    (hs : HashState p H (p.count + 1) s) {plen : Nat}
    (hl : 2 ≤ plen) (hroom : plen ≤ (p.count + 1) * p.len) :
    Spec.Ffdh.candidateOf (8 * plen) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem
      (off p.output ((p.count + 1) * p.len - plen)) plen)) = p.shapedValue H plen := by
  have hsuf := VG.Proof.Dsa.Generation.bytesAt_suffix_value s.mem p.output ((p.count + 1) * p.len - plen) plen
  rw [Nat.sub_add_cancel hroom, hash_complete_value hs, pow256_eq] at hsuf
  change Spec.Ffdh.candidateOf (8 * plen) (Spec.Dsa.decodeBE _) = _
  rw [← hsuf, VG.Proof.Dsa.Generation.candidateOf_mod_width (by omega_using [hl]) (Nat.le_refl _)]
  rfl

theorem pShape_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : State}
    (hs : HashState p H (p.count + 1) s) {plen : Nat} {op : Addr}
    (hl : 2 ≤ plen) (hlmax : plen ≤ 1024) (hroom : plen ≤ (p.count + 1) * p.len)
    (hop : p.W 0 = op) (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j) :
    WP isa (Impl.Dsa.X86_64.Generation.pShape p.len p.count plen) s fun t =>
      Spec.Rsa.bytesAt t.mem op plen = Spec.Dsa.encodeBE plen (p.shapedValue H plen) := by
  obtain ⟨V, R⟩ := hs.rep
  unfold Impl.Dsa.X86_64.Generation.pShape
  refine WP.seq (WP.mono (pShapeArgs_ok hs.layout R hop p.output_slot p.size.2.2 hlmax)
    fun u ⟨hdi, hsi, hcx, hdx, hm, hk⟩ => ?_)
  let rp := off p.output ((p.count + 1) * p.len - plen)
  let bs := Spec.Rsa.bytesAt s.mem rp plen
  have hbl : bs.length = plen := by simp [bs, Spec.Rsa.bytesAt]
  have hrd : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
    intro i hi
    rw [hbl] at hi
    obtain ⟨r, hr, hc⟩ := hs.outputWrite ((p.count + 1) * p.len - plen + i) (by omega_using [hroom, hi])
    refine ⟨r, ?_, ?_⟩
    · rw [hk.2.1, hk.2.2]; exact List.mem_append_right _ hr
    · simpa only [rp, off_off] using hc
  have hb : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
    intro i hi
    rw [hm]
    simp only [bs, Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD]
    simp [show i < plen by omega_using [hbl, hi]]
  refine WP.mono (VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ok
    (by omega_using [hl] : 9 ≤ 8 * plen) (by omega_using [hlmax]) (by rw [hbl]; omega_using [])
    hsi hdi (by rw [hbl]; exact hcx) hdx hrd
    (fun i hi => by rw [hk.2.2]; exact hout i (hbl ▸ hi)) hb
    (fun i hi j hj => hsep i (hbl ▸ hi) j (hbl ▸ hj)))
    fun t ⟨_, hx, _, _⟩ => ?_
  rw [hbl] at hx
  have value : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem op plen) = p.shapedValue H plen := by
    change Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) = _
    rw [hx]
    exact hash_shaped_value hs hl hroom
  have encoded := VG.Proof.Dsa.encodeBE_decodeBE (Spec.Rsa.bytesAt t.mem op plen)
  rw [bytesAt_length, value] at encoded
  exact encoded.symm

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Public data connecting p hashing to native reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def PConstructPlan.withWords (p : PConstructPlan) (W : Nat → BitVec 64)
    (hw : ∀ i < 6, W i = p.hash.W i) : PConstructPlan :=
  { p with
    hash := p.hash.withWords W (fun i hi => hw i (by omega_using [hi]))
    base := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.base
    shapedSlot := by simpa only [HashPlan.withWords, hw 0 (by decide), hw 5 (by decide)] using p.shapedSlot
    shapedOutside := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.shapedOutside
    shapedHash := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.shapedHash
    shapedInput := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.shapedInput
    qHash := by simpa only [HashPlan.withWords, HashPlan.changed, hw 5 (by decide)] using p.qHash
    pOutside := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.pOutside
    exponentOutside := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.exponentOutside
    pExponent := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.pExponent
    frameArithmetic := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.frameArithmetic
    hashArithmetic := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.hashArithmetic }

structure PConstructPublic where
  plan : PConstructPlan
  ws : List Region

def PConstructBefore (n : Nat) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (p : PConstructPublic) (s : State) : Prop :=
  (∃ W, ∃ hw : ∀ i < 6, W i = p.plan.hash.W i,
    PConstructState (p.plan.withWords W hw) H s ∧ FrV n p.plan.hash.F p.ws s) ∧
    p.plan.len = pLen ∧ p.plan.hash.len = qLen

def PConstructPublic.hash (p : PConstructPublic) : PHashPublic := ⟨p.plan.hash, p.ws⟩

theorem pConstruct_hash {n pLen qLen : Nat} {H : Spec.Mgf1.Hash} {p : PConstructPublic} {s : State}
    (h : PConstructBefore n H pLen qLen p s) :
    ContributionBefore n H 0 qLen ((8 * pLen - 1) / (8 * qLen)) p.hash s := by
  obtain ⟨⟨W, hw, hs, hf⟩, hp, hq⟩ := h
  exact ⟨⟨W, (fun i hi => hw i (by omega_using [hi])), hs.hash, hf⟩, hq,
    p.plan.hashCount.trans (by rw [hp, hq])⟩

def PConstructPublic.workspace (p : PConstructPublic) (H : Spec.Mgf1.Hash) : CandidateWorkspacePublic where
  frame := {
    B := p.plan.B
    F := p.plan.hash.F
    arena := p.plan.hash.W 5
    Z := p.plan.Z
    w := p.plan.len / 8
    xb := Spec.Dsa.encodeBE p.plan.len (p.plan.hash.shapedValue H p.plan.len)
    qb := p.plan.qb
    xLength := by rw [VG.Proof.Dsa.encodeBE_length]; rcases p.plan.width with h | h | h <;> omega_using [h]
    qLength := by
      rw [p.plan.qLength]
      rcases p.plan.width with h | h | h <;> rcases p.plan.hash.width with q | q <;> omega_using [h, q]
    qNonempty := by rw [p.plan.qLength]; rcases p.plan.hash.width with h | h <;> omega_using [h]
    qPositive := p.plan.qPositive
    qFits := p.plan.qFits
    separate := p.plan.frameHeaders
    pOutside := by
      have he : 8 * (p.plan.len / 8) = p.plan.len := by rcases p.plan.width with h | h | h <;> omega_using [h]
      simpa only [he] using p.plan.pOutside
    eOutside := by
      have he : 8 * (p.plan.len / 8) = p.plan.len := by rcases p.plan.width with h | h | h <;> omega_using [h]
      simpa only [he] using p.plan.exponentOutside }
  base := p.plan.base.symm
  room := p.plan.workspaceRoom
  lower := by rcases p.plan.width with h | h | h <;> dsimp only <;> omega_using [h]
  upper := by rcases p.plan.width with h | h | h <;> dsimp only <;> omega_using [h]
  outside := p.plan.frameOutside

end VG.Proof.Dsa.X86_64.Generation
