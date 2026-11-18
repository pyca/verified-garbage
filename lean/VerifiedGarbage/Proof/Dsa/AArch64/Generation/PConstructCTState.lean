module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PShape
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashPlan
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShapeArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashShape
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShape
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Contract
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
public import Aesop.BuiltinRules
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Reduce
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Rsa.AArch64.Div
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NarrowDivision
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Rsa.AArch64.Div
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NarrowDivision
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateStores
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateStores
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArguments

/-! ### `Dsa.AArch64.Generation.CandidateWorkspaceCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.CandidateFrameCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.CandidateBuildCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.CandidateStoresCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.StoreCT`, which only this module used -/

section

/-! Full-width candidate and exponent stores have public addressing. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys

structure StorePublic where
  B : Addr
  Z : Nat
  w : Nat
  out : Addr

structure StoreState (ptr : Nat) (p : StorePublic) (s : State) : Prop where
  ws : VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w
  pointer : word s.mem p.B (8 * ptr) = p.out
  length : word s.mem p.B 136 = BitVec.ofNat 64 (8 * p.w)
  mask : word s.mem p.B (8 * sMask) = mask true
  write : ∀ i < 8 * p.w, InRegions s.wr (off p.out i) 1
  outside : ∀ i < 8 * p.w, p.Z ≤ ofs p.B (off p.out i)

theorem storeCandidate_ct {a ptr : Nat} (ha : a < 16) (hp : ptr < 32)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base a .x8 ++
      [ldh .x1 ptr, ldh .x9 17, .add .x .x1 .x1 .x9, ldh .x15 sMask])) hc).isSome = true) :
    RelCT isa (Two (StoreState ptr)) (seqs (storeA a ptr 17 sMask)) (fun _ _ => True) := by
  have ct := pin_ct (c₂ := storeBE) (Φ := StoreState ptr) (Ψ := fun _ _ => True)
    [.x0] [.x0, .x8, .x1, .x9] (fun p => soVal p.B (off p.B (slot p.w a)) p.out (8 * p.w))
    (fun _ _ _ hs ht r hr => by obtain rfl := List.mem_singleton.mp hr; exact hs.ws.x0.trans ht.ws.x0.symm)
    ht (fun p s h => storeBlk_ok h.ws hp (by decide : 17 < 32) h.pointer h.length) (by taint_decide)
    (fun _ _ h => WP.mono (storeCandidateArray_ok h.ws ha hp h.pointer h.length h.mask h.write h.outside)
      (fun _ _ => True.intro))
  exact ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Save p and its exponent with public addressing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys

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
    WP isa (seqs (storeA 5 20 17 VG.Impl.Bignum.Public.sMask)) s (StoreState 21 p.eStore) := by
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
    (header (8 * VG.Impl.Bignum.Public.sMask) (by decide)).trans h.2.mask,
    (fun i hi => by rw [hk.wr]; exact h.2.write i hi), h.2.outside⟩

theorem candidateStores_ct : RelCT isa (Two CandidateStoreState)
    Impl.Dsa.AArch64.Generation.candidateStores (fun _ _ => True) := by
  refine RelCT.seq (two_post
    (two_map CandidateOutputs.pStore (fun _ _ h => h.1)
      (storeCandidate_ct (by decide : 5 < 16) (by decide : 20 < 32) (by taint_decide)))
    (fun _ _ h => candidateStoreFirst_state h)) ?_
  exact two_map CandidateOutputs.eStore (fun _ _ h => h)
    (storeCandidate_ct (by decide : 0 < 16) (by decide : 21 < 32) (by taint_decide))

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.CandidateArithmeticCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.ArithmeticCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.ArithmeticFrame`, which only this module used -/

section

/-! Arithmetic instructions preserve the workspace even when a result overflows. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64 VG.Proof.MlKem.AArch64

theorem doubleArray_ws {s : State} {B : Addr} {Z w dst : Nat}
    (h : VG.Proof.Rsa.AArch64.Ws s B Z w) (hd : dst < 16) :
    WP isa (Impl.Dsa.AArch64.Generation.doubleArray dst) s fun t => VG.Proof.Rsa.AArch64.Ws t B Z w := by
  have sd := h.sl hd
  unfold Impl.Dsa.AArch64.Generation.doubleArray
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, hm₁, _⟩, k₁⟩ => ?_))
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x7, .x14, .x3]
    (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = false ∧ t.mem = s₁.mem)
    (by brun [h12]) rfl rfl rfl) fun s₂ ⟨⟨h14, hc, hm₂⟩, k₂⟩ => ?_)
  refine WP.mono (base_ok dst .x16 (((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0)
    ((k₂.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h16, hm₃, hc₃⟩, k₃⟩ => ?_
  have k := (k₁.trans k₂).trans k₃
  refine WP.mono (shl_ok (h.scr.congr k.wr) h16
    ((k₃.gpr .x14 (by decide)).trans h14) (by have := h.w1; omega_using [this])
    (by have := h.w2; omega_using [this]) (by omega_using [sd])) fun t ⟨_, _, ho, kt⟩ => ?_
  rw [hm₃, hm₂, hm₁] at ho
  exact h.congr' (Frm.of_outside ho (List.mem_singleton_self _))
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact KMut.ofSlot _ _ _)
    (k.trans kt) (by decide)

theorem copyArray_ws {s : State} {B : Addr} {Z w o a : Nat} (h : VG.Proof.Rsa.AArch64.Ws s B Z w)
    (ho : o < 16) (ha : a < 16) (hoa : o ≠ a) :
    WP isa (copyA o a) s fun t => VG.Proof.Rsa.AArch64.Ws t B Z w := by
  refine WP.mono (copyA_ok h ho ha hoa) fun t ⟨_, out, _, _, hk⟩ => ?_
  exact h.congr' (Frm.of_outside out (List.mem_singleton_self _))
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact KMut.ofSlot _ _ _) hk (by decide)

theorem divideArray_ws {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.AArch64.Ws s B Z w)
    (hwide : Impl.Dsa.AArch64.Generation.reduceWords ≤ w) :
    WP isa (Impl.Dsa.AArch64.Generation.divNarrow Impl.Dsa.AArch64.Generation.reduceWords 0 1 2 3) s
      fun t => VG.Proof.Rsa.AArch64.Ws t B Z w := by
  refine WP.mono (divNarrow_ok h hwide (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨_, hf, hk, _⟩ => ?_
  exact h.congr' hf (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact KMut.ofSlot _ _ _) hk (by decide)

theorem subtractArray_ws {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.AArch64.Ws s B Z w) :
    WP isa (seqs (subA 5 4 1)) s fun t => VG.Proof.Rsa.AArch64.Ws t B Z w := by
  refine WP.mono (subA_ok h (by decide) (by decide) (by decide) (Or.inr (by decide)) (by decide))
    fun t ⟨_, out, _, _, _, hk⟩ => ?_
  exact h.congr' (Frm.of_outside out (List.mem_singleton_self _))
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact KMut.ofSlot _ _ _) hk (by decide)

theorem incrementEven_ws {s : State} {B : Addr} {Z w dst : Nat}
    (h : VG.Proof.Rsa.AArch64.Ws s B Z w) (hd : dst < 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.incrementEven dst)) s fun t => VG.Proof.Rsa.AArch64.Ws t B Z w := by
  have hn := h.scr.nowrap
  have sd := h.sl hd
  have hw : 1 ≤ w := by have := h.w1; omega_using [this]
  unfold Impl.Dsa.AArch64.Generation.incrementEven
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨_, h11, hm₁, _⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok dst .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11)
    fun s₂ ⟨⟨h16, hm₂, _⟩, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).wr
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem =
    s.mem.writeW (off B (slot w dst)) (word s.mem B (slot w dst) + 1))
    (by brun [h16, hs₂.ld (d := slot w dst) (by omega_using [sd]), hs₂.st (d := slot w dst) (by omega_using [sd]), hm₂, hm₁]; rfl)
    rfl rfl rfl) fun t ⟨hm, k₃⟩ => ?_
  have ho : Outside B (slot w dst) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega_using [hn, sd])
  exact h.congr' (Frm.of_outside ho (List.mem_singleton_self _))
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact KMut.ofSlot _ _ _)
    ((k₁.trans k₂).trans k₃) (by decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! Candidate reduction arithmetic leaks only its workspace and word count. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Impl.Dsa.AArch64.Generation

/-- The working space and its word count, at least the narrow division's. -/
structure ArithmeticPublic where
  B : Addr
  Z : Nat
  w : Nat
  wide : reduceWords ≤ w

def ArithmeticGood (p : ArithmeticPublic) (s : State) : Prop := VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w

theorem doubleArray_ct {dst : Nat} (hd : dst = 0 ∨ dst = 2) :
    RelCT isa (Two ArithmeticGood) (doubleArray dst) (Two ArithmeticGood) := by
  rcases hd with rfl | rfl
  all_goals
    unfold doubleArray
    simp only [List.append_assoc]
    exact ws_ct (fun p : ArithmeticPublic => p.B) (fun p : ArithmeticPublic => p.Z) (fun p : ArithmeticPublic => p.w) (fun _ _ h => h)
      (by taint_decide) (fun _ _ h => doubleArray_ws h (by decide))

theorem copyReduction_ct : RelCT isa (Two ArithmeticGood) (copyA 4 0) (Two ArithmeticGood) := by
  change RelCT isa (Two ArithmeticGood) (.seq (.block (ws ++ (base 0 .x16 ++ base 4 .x17))) copyWords) _
  exact ws_ct (fun p : ArithmeticPublic => p.B) (fun p : ArithmeticPublic => p.Z) (fun p : ArithmeticPublic => p.w) (fun _ _ h => h)
    (by taint_decide) (fun _ _ h => copyArray_ws h (by decide) (by decide) (by decide))

theorem zeroReduction_ct : RelCT isa (Two ArithmeticGood) (zeroA 1) (fun _ _ => True) := by
  change RelCT isa (Two ArithmeticGood) (.seq (.block (ws ++ (base 1 .x8 ++ [movi .x7 0]))) zeroAcc) _
  exact ws_ct0 (fun p : ArithmeticPublic => p.B) (fun p : ArithmeticPublic => p.Z) (fun p : ArithmeticPublic => p.w) (fun _ _ h => h) (by taint_decide)

theorem divideReduction_ct :
    RelCT isa (Two ArithmeticGood) (divNarrow reduceWords 0 1 2 3) (Two ArithmeticGood) := by
  unfold divNarrow
  refine pin_seq [.x0, .x12, .x11] (fun p : ArithmeticPublic => wsVal p.B p.w)
    zeroReduction_ct ?_ (by taint_decide) ?_
  · intro p s h
    exact WP.mono (zeroA_ok h (by decide : 1 < 16)) fun _ ⟨_, _, h12, h11, _, hk⟩ =>
      wsVal_of ((hk.gpr .x0 (by decide)).trans h.x0) h12 h11
  · intro p s h
    exact divideArray_ws h p.wide

theorem subtractReduction_ct : RelCT isa (Two ArithmeticGood) (seqs (subA 5 4 1)) (Two ArithmeticGood) := by
  rw [subA_eq']
  exact ws_ct (fun p : ArithmeticPublic => p.B) (fun p : ArithmeticPublic => p.Z) (fun p : ArithmeticPublic => p.w) (fun _ _ h => h)
    (by taint_decide) (fun _ _ h => subtractArray_ws h)

theorem incrementReduction_ct : RelCT isa (Two ArithmeticGood) (.block (incrementEven 5)) (Two ArithmeticGood) := by
  unfold incrementEven
  simp only [List.append_assoc]
  exact ws_block_ct (fun p : ArithmeticPublic => p.B) (fun p : ArithmeticPublic => p.Z) (fun p : ArithmeticPublic => p.w) (fun _ _ h => h)
    (by taint_decide) (fun _ _ h => incrementEven_ws h (by decide))

theorem reduceCandidate_ct : RelCT isa (Two ArithmeticGood) reduceCandidate (Two ArithmeticGood) :=
  RelCT.seq copyReduction_ct (RelCT.seq divideReduction_ct (RelCT.seq subtractReduction_ct incrementReduction_ct))

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! Complete candidate and generator-exponent arithmetic has a public trace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys

structure CandidatePublic where
  B : Addr
  Z : Nat
  w : Nat
  xp : Addr
  qp : Addr
  xb : List Byte
  qb : List Byte
  wide : Impl.Dsa.AArch64.Generation.reduceWords ≤ w
  narrow : qb.length ≤ 32

def CandidatePublic.xLoad (p : CandidatePublic) : LoadPublic := ⟨p.B, p.Z, p.w, p.xp, p.xb⟩
def CandidatePublic.qLoad (p : CandidatePublic) : LoadPublic := ⟨p.B, p.Z, p.w, p.qp, p.qb⟩
def CandidatePublic.workspace (p : CandidatePublic) : ArithmeticPublic := ⟨p.B, p.Z, p.w, p.wide⟩

def CandidateInput (p : CandidatePublic) (s : State) : Prop :=
  LoadState 16 17 p.xLoad s ∧ LoadState 18 19 p.qLoad s

def CandidateFirst (p : CandidatePublic) (s : State) : Prop := LoadState 18 19 p.qLoad s

theorem candidateFirst_state {p : CandidatePublic} {s : State} (h : CandidateInput p s) :
    WP isa (seqs (loadA 0 16 17)) s (CandidateFirst p) := by
  refine WP.mono (loadCandidateArray_ok h.1.ws (by decide) (by decide) (by decide)
    h.1.pointer h.1.length h.1.source h.1.positive h.1.fits) fun t ⟨ht, _, hf, hk⟩ => ?_
  have hdr (d : Nat) (hd : d + 8 ≤ 256) : word t.mem p.B d = word s.mem p.B d := by
    apply hf.word_eq
    · simp only [List.mem_singleton]; rintro r rfl
      left; simp only [slot, VG.Impl.Bignum.hdrBytes]; omega_using [hd]
    · have := h.1.ws.h256; have := h.1.ws.scr.nowrap; omega_using [hd]
  refine ⟨ht, (hdr 144 (by decide)).trans h.2.pointer, (hdr 152 (by decide)).trans h.2.length,
    h.2.source.congrK ?_ hk, h.2.positive, h.2.fits⟩
  intro a ha
  apply hf a
  simp only [List.mem_singleton]; rintro r rfl
  right
  exact Nat.le_trans (h.1.ws.sl (by decide : 0 < 16)) ha

theorem candidateSecond_state {p : CandidatePublic} {s : State} (h : CandidateFirst p s) :
    WP isa (seqs (loadA 2 18 19)) s (ArithmeticGood p.workspace) :=
  WP.mono (loadCandidateArray_ok h.ws (by decide) (by decide) (by decide)
    h.pointer h.length h.source h.positive h.fits) (fun _ ⟨ht, _, _, _⟩ => ht)

theorem candidateArithmetic_ct : RelCT isa (Two CandidateInput)
    Impl.Dsa.AArch64.Generation.candidateArithmetic (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.candidateArithmetic
  refine RelCT.seq (two_post
    (two_map CandidatePublic.xLoad (fun _ _ h => h.1)
      (loadCandidate_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => candidateFirst_state h)) ?_
  refine RelCT.seq (two_post
    (two_map CandidatePublic.qLoad (fun _ _ h => h)
      (loadCandidate_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => candidateSecond_state h)) ?_
  exact two_map CandidatePublic.workspace (fun _ _ h => h)
    ((RelCT.seq (doubleArray_ct (Or.inr rfl)) (RelCT.seq reduceCandidate_ct (doubleArray_ct (Or.inl rfl)))).mono
      (fun _ _ h => h) (fun _ _ _ => True.intro))

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The complete byte-to-byte p-candidate builder has a public trace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64

structure CandidateBuildPublic where
  input : CandidatePublic
  p : Addr
  exponent : Addr

def CandidateBuildPublic.outputs (p : CandidateBuildPublic) : CandidateOutputs :=
  ⟨p.input.B, p.input.Z, p.input.w, p.p, p.exponent⟩

def CandidateBuildState (p : CandidateBuildPublic) (s : State) : Prop :=
  CandidateInput p.input s ∧ CandidateStoreState p.outputs s ∧
    0 < Spec.Rsa.os2ip p.input.qb ∧ 2 * Spec.Rsa.os2ip p.input.qb < 2 ^ (64 * p.input.w)

theorem candidateArithmetic_storeState {p : CandidateBuildPublic} {s : State} (h : CandidateBuildState p s) :
    WP isa Impl.Dsa.AArch64.Generation.candidateArithmetic s (CandidateStoreState p.outputs) := by
  have hw : Ws s p.input.B p.input.Z p.input.w := h.1.1.ws
  refine WP.mono (candidateArithmetic_ok hw h.1.1.pointer h.1.1.length h.1.2.pointer h.1.2.length
    h.1.1.source h.1.2.source h.1.1.positive h.1.1.fits h.1.2.positive h.1.2.fits
    h.2.2.1 h.2.2.2 p.input.wide p.input.narrow) fun t ⟨ht, _, _, f, hk⟩ => ?_
  have header (d : Nat) (hd : d + 8 ≤ 256) : word t.mem p.input.B d = word s.mem p.input.B d := by
    apply f.word_eq
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;>
        left <;> simp only [slot, VG.Impl.Bignum.hdrBytes] <;> omega_using [hd]
    · have := hw.h256; have := hw.scr.nowrap; omega_using [hd]
  exact ⟨⟨ht, (header 160 (by decide)).trans h.2.1.1.pointer,
    (header 136 (by decide)).trans h.2.1.1.length,
    (header (8 * VG.Impl.Bignum.Public.sMask) (by decide)).trans h.2.1.1.mask,
    (fun i hi => by rw [hk.wr]; exact h.2.1.1.write i hi), h.2.1.1.outside⟩,
    ⟨ht, (header 168 (by decide)).trans h.2.1.2.pointer,
    (header 136 (by decide)).trans h.2.1.2.length,
    (header (8 * VG.Impl.Bignum.Public.sMask) (by decide)).trans h.2.1.2.mask,
    (fun i hi => by rw [hk.wr]; exact h.2.1.2.write i hi), h.2.1.2.outside⟩⟩

theorem candidateBuild_ct : RelCT isa (Two CandidateBuildState)
    Impl.Dsa.AArch64.Generation.candidateBuild (fun _ _ => True) :=
  RelCT.seq (two_post (two_map CandidateBuildPublic.input (fun _ _ h => h.1) candidateArithmetic_ct)
    (fun _ _ h => candidateArithmetic_storeState h))
    (two_map CandidateBuildPublic.outputs (fun _ _ h => h) candidateStores_ct)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Candidate arithmetic accepts the persistent frame's actual words -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Impl.Dsa.Generation.Layout

structure CandidateFramePublic where
  B : Addr
  F : Addr
  arena : Addr
  Z : Nat
  w : Nat
  width : w ≤ 48
  xb : List Byte
  qb : List Byte
  xLength : xb.length = 8 * w
  qLength : qb.length ≤ 8 * w
  qNonempty : 1 ≤ qb.length
  qPositive : 0 < Spec.Rsa.os2ip qb
  qFits : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w)
  wide : reduceWords ≤ w
  narrow : qb.length ≤ 32
  separate : ∀ k < 34, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8
  pOutside : ∀ i < 8 * w, Z ≤ ofs B (off (off arena p) i)
  eOutside : ∀ i < 8 * w, Z ≤ ofs B (off (off arena exponent) i)

def CandidateFramePublic.build (c : CandidateFramePublic) : CandidateBuildPublic :=
  ⟨⟨c.B, c.Z, c.w, off c.arena shaped, off c.arena q, c.xb, c.qb, c.wide, c.narrow⟩,
    off c.arena p, off c.arena exponent⟩

structure CandidateFrameInputs (c : CandidateFramePublic) (s : State) : Prop where
  stack : s.sp = c.F
  read : ∀ k < 34, InRegions (s.rd ++ s.wr) (off c.F (8 * k)) 8
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
  have hp : pLen < 2 ^ 16 := by omega_using [c.width, c.xLength, h.2.2.1]
  have hq : qLen < 2 ^ 16 := by omega_using [hp, c.qLength, c.xLength, h.2.2.1, h.2.2.2]
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
    ⟨ht, pq, ql, sq, c.qNonempty, c.qLength⟩⟩,
    ⟨⟨ht, pp, outlen, hm, ?_, c.pOutside⟩, ⟨ht, pe, outlen, hm, ?_, c.eOutside⟩⟩, c.qPositive, c.qFits⟩
  · change 1 ≤ c.xb.length
    omega_using [c.xLength, h.2.1.w1]
  · intro i hi; rw [hk.wr]; exact h.1.pWrite i hi
  · intro i hi; rw [hk.wr]; exact h.1.eWrite i hi

theorem candidateFromFrame_ct (pLen qLen : Nat) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (candidateArguments pLen qLen))) hc).isSome = true) :
    RelCT isa (Two (CandidateFrameBefore pLen qLen)) (candidateFromFrame pLen qLen) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_taint [.x0] ?_ ht)
    (fun _ _ h => candidateFrame_ready h)) ?_
  · intro c s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.2.1.x0.trans ht.2.1.x0.symm
  · exact two_map CandidateFramePublic.build (fun _ _ h => h) candidateBuild_ct

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Initialize candidate-reduction scratch while retaining source bytes and frame arguments -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Impl.Dsa.Generation.Layout

structure CandidateWorkspacePublic where
  frame : CandidateFramePublic
  base : frame.B = off frame.arena arithmetic
  room : slot frame.w 16 ≤ frame.Z
  lower : 2 ≤ frame.w
  upper : frame.w ≤ 48
  outside : ∀ k < 34, ∀ i < 8, frame.Z ≤ ofs frame.B (off (off frame.F (8 * k)) i)

def CandidateWorkspaceBefore (w pLen qLen : Nat) (c : CandidateWorkspacePublic) (s : State) : Prop :=
  CandidateFrameInputs c.frame s ∧ Scr s c.frame.B c.frame.Z ∧
    c.frame.w = w ∧ c.frame.xb.length = pLen ∧ c.frame.qb.length = qLen

def CandidateWorkspaceBase (w pLen qLen : Nat) (c : CandidateWorkspacePublic) (s : State) : Prop :=
  CandidateWorkspaceBefore w pLen qLen c s ∧ s.gpr .x0 = c.frame.B

theorem candidateWorkspace_base {w pLen qLen : Nat} {c : CandidateWorkspacePublic} {s : State}
    (h : CandidateWorkspaceBefore w pLen qLen c s) :
    WP isa (.block workspaceBase) s (CandidateWorkspaceBase w pLen qLen c) := by
  have ld := h.1.read 5 (by decide)
  have hv : s.mem.readW (off c.frame.F 40) 64 = c.frame.arena := h.1.arena
  have step : WP isa (.block workspaceBase) s fun t => t.gpr .x0 = c.frame.B ∧ t.mem = s.mem := by
    brun [workspaceBase, exec_ldrSp (off := 40) (by decide), h.1.stack, ld, hv]
    change c.frame.arena + (BitVec.ofNat 16 arithmetic).setWidth 64 = _
    rw [show (BitVec.ofNat 16 arithmetic).setWidth 64 = BitVec.ofNat 64 arithmetic by decide]
    exact c.base.symm
  refine WP.mono (WP.keep [.x0, .x3] step rfl rfl rfl) fun t ⟨⟨hb, hm⟩, hk⟩ => ?_
  refine ⟨⟨?_, h.2.1.congr hk.wr, h.2.2⟩, hb⟩
  exact ⟨hk.sp.trans h.1.stack,
    (fun k hk' => by rw [hk.rd, hk.wr]; exact h.1.read k hk'),
    hm ▸ h.1.arena, h.1.x.congrK (fun _ _ => by rw [hm]) hk,
    h.1.q.congrK (fun _ _ => by rw [hm]) hk,
    (fun i hi => by rw [hk.wr]; exact h.1.pWrite i hi),
    (fun i hi => by rw [hk.wr]; exact h.1.eWrite i hi)⟩

theorem candidateWorkspace_ready {w pLen qLen : Nat} {c : CandidateWorkspacePublic} {s : State}
    (h : CandidateWorkspaceBase w pLen qLen c s) :
    WP isa (workspace w) s (CandidateFrameBefore pLen qLen c.frame) := by
  have step := workspace_ok h.1.2.1 h.2 c.room c.lower c.upper
  rw [h.1.2.2.1] at step
  refine WP.mono step fun t ⟨ht, _, ff, hk⟩ => ?_
  have hz : 256 ≤ c.frame.Z := Nat.le_trans (Nat.le_add_right 256 _) c.room
  have bound : ∀ r ∈ workspaceRanges, r.1 + r.2 ≤ c.frame.Z := by
    simp only [workspaceRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only <;> omega_using [hz]
  have ht' : Ws t c.frame.B c.frame.Z c.frame.w := by rw [h.1.2.2.1]; exact ht
  refine ⟨?_, ht', h.1.2.2.2⟩
  refine ⟨hk.sp.trans h.1.1.stack, ?_, ?_,
    h.1.1.x.congrK (InScr.of_frm ff bound) hk, h.1.1.q.congrK (InScr.of_frm ff bound) hk, ?_, ?_⟩
  · intro k hk'; rw [hk.rd, hk.wr]; exact h.1.1.read k hk'
  · exact (frame_word_of_workspace ff bound (c.outside 5 (by decide))).trans h.1.1.arena
  · intro i hi; rw [hk.wr]; exact h.1.1.pWrite i hi
  · intro i hi; rw [hk.wr]; exact h.1.1.eWrite i hi

theorem reduceFromFrame_ct (w pLen qLen : Nat) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (workspace w) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (candidateArguments pLen qLen))) hc₂).isSome = true) :
    RelCT isa (Two (CandidateWorkspaceBefore w pLen qLen))
      (seqs [.block workspaceBase, workspace w, candidateFromFrame pLen qLen]) (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => candidateWorkspace_base h))
    (RelCT.seq (two_post (two_taint [.x0] ?_ ht₁)
      (fun _ _ h => candidateWorkspace_ready h)) ?_)
  · intro c s t hs ht r hr
    simp only [List.mem_singleton] at hr; subst r
    exact hs.2.trans ht.2.symm
  · exact two_map CandidateWorkspacePublic.frame (fun _ _ h => h) (candidateFromFrame_ct pLen qLen ht₂)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.PShapeValue`, which this module and modules that import it used -/

section

/-! # The shaped hash bytes are determined by the public seed and offset -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

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
  rw [Nat.sub_add_cancel hroom, hash_complete_value hs, VG.Proof.Bignum.pow256_eq] at hsuf
  change Spec.Ffdh.candidateOf (8 * plen) (Spec.Dsa.decodeBE _) = _
  rw [← hsuf, VG.Proof.Dsa.Generation.candidateOf_mod_width (by omega_using [hl]) (Nat.le_refl _)]
  rfl

theorem pShape_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : State}
    (hs : HashState p H (p.count + 1) s) {plen : Nat} {op : Addr}
    (hl : 2 ≤ plen) (hlmax : plen ≤ 1024) (hroom : plen ≤ (p.count + 1) * p.len)
    (hop : p.W 0 = op) (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j) :
    WP isa (Impl.Dsa.AArch64.Generation.pShape p.len p.count plen) s fun t =>
      Spec.Rsa.bytesAt t.mem op plen = Spec.Dsa.encodeBE plen (p.shapedValue H plen) := by
  obtain ⟨V, R⟩ := hs.rep
  unfold Impl.Dsa.AArch64.Generation.pShape
  refine WP.seq (WP.mono (pShapeArgs_ok hs.layout R hop p.output_slot (by have hc := p.count_le; rcases p.width with h | h <;> rw [h] <;> omega_using [hc]) hlmax)
    fun u ⟨hdi, hsi, hcx, hm, hk⟩ => ?_)
  let rp := off p.output ((p.count + 1) * p.len - plen)
  let bs := Spec.Rsa.bytesAt s.mem rp plen
  have hbl : bs.length = plen := by simp [bs, Spec.Rsa.bytesAt]
  have hrd : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
    intro i hi
    rw [hbl] at hi
    obtain ⟨r, hr, hc⟩ := hs.outputWrite ((p.count + 1) * p.len - plen + i) (by omega_using [hroom, hi])
    refine ⟨r, ?_, ?_⟩
    · rw [hk.rd, hk.wr]; exact List.mem_append_right _ hr
    · simpa only [rp, off_off] using hc
  have hb : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
    intro i hi
    rw [hm]
    simp only [bs, Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD]
    simp [show i < plen by omega_using [hbl, hi]]
  refine WP.mono (qShape_ok (by rw [hbl]; exact hl) (by rw [hbl]; omega_using [hlmax])
    hsi hdi (by rw [hbl]; exact hcx) hrd
    (fun i hi => by rw [hk.wr]; exact hout i (hbl ▸ hi)) hb
    (fun i hi j hj => hsep i (hbl ▸ hi) j (hbl ▸ hj)))
    fun t ⟨houtbytes, _, _⟩ => ?_
  have hx : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) =
      Spec.Ffdh.candidateOf (8 * plen) (Spec.Rsa.os2ip bs) := by
    rw [← hbl, houtbytes]
    exact VG.Proof.Ffdh.ParameterCandidate.shapedOctets_value
      (by intro he; have := congrArg List.length he; simp only [List.length_nil, hbl] at this; omega_using [hl, this])
      (by decide : 7 < 8) (by rw [hbl]; omega_using [hl])
  have value : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem op plen) = p.shapedValue H plen := by
    change Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) = _
    rw [hx]
    exact hash_shaped_value hs hl hroom
  have encoded := VG.Proof.Dsa.encodeBE_decodeBE (Spec.Rsa.bytesAt t.mem op plen)
  rw [VG.Proof.Bignum.bytesAt_length, value] at encoded
  exact encoded.symm

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Public data connecting p hashing to native reduction -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

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

def PConstructBefore (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (p : PConstructPublic) (s : State) : Prop :=
  (∃ W, ∃ hw : ∀ i < 6, W i = p.plan.hash.W i,
    PConstructState (p.plan.withWords W hw) H s) ∧
    p.plan.len = pLen ∧ p.plan.hash.len = qLen

def PConstructPublic.hash (p : PConstructPublic) : PHashPublic := ⟨p.plan.hash⟩

theorem pConstruct_hash {pLen qLen : Nat} {H : Spec.Mgf1.Hash} {p : PConstructPublic} {s : State}
    (h : PConstructBefore H pLen qLen p s) :
    ContributionBefore H 0 qLen ((8 * pLen - 1) / (8 * qLen)) p.hash s := by
  obtain ⟨⟨W, hw, hs⟩, hp, hq⟩ := h
  exact ⟨⟨W, (fun i hi => hw i (by omega_using [hi])), hs.hash⟩, hq,
    p.plan.hashCount.trans (by rw [hp, hq])⟩

def PConstructPublic.workspace (p : PConstructPublic) (H : Spec.Mgf1.Hash) : CandidateWorkspacePublic where
  frame := {
    B := p.plan.B
    F := p.plan.hash.F
    arena := p.plan.hash.W 5
    Z := p.plan.Z
    w := p.plan.len / 8
    width := by rcases p.plan.width with h | h | h <;> omega_using [h]
    xb := Spec.Dsa.encodeBE p.plan.len (p.plan.hash.shapedValue H p.plan.len)
    qb := p.plan.qb
    xLength := by rw [VG.Proof.Dsa.encodeBE_length]; rcases p.plan.width with h | h | h <;> omega_using [h]
    qLength := by
      rw [p.plan.qLength]
      rcases p.plan.width with h | h | h <;> rcases p.plan.hash.width with q | q <;> omega_using [h, q]
    qNonempty := by rw [p.plan.qLength]; rcases p.plan.hash.width with h | h <;> omega_using [h]
    qPositive := p.plan.qPositive
    qFits := p.plan.qFits
    wide := by
      rcases p.plan.width with h | h | h <;> rw [h] <;> decide
    narrow := by rw [p.plan.qLength]; rcases p.plan.hash.width with h | h <;> omega_using [h]
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

end VG.Proof.Dsa.AArch64.Generation
