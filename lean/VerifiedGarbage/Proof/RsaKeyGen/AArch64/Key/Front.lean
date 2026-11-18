module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.State
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdE
import VerifiedGarbage.Proof.Rsa.AArch64.CkPieces
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTBase
public import VerifiedGarbage.Proof.Rsa.AArch64.Div
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.Div
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.Inv
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import Mathlib.Data.Nat.Basic
import Mathlib.Order.RelClasses

/-! ### `RsaKeyGen.AArch64.Key.CTUnits`, which the modules that import this one used -/

section

/-!
# An RSA key from its primes on AArch64: constant time, the key routines

Each of `zeroA`, `copyA`, `constA`, `ltA`, `geA`, `eqMask`, `neMask`,
`selC`, `setOneA`, `oddMaskOf`, `evenMaskOf`, `divmod` and `inverse` leaks
the same from two runs in `KG F` (`…_ct0`, with no postcondition), and
leaves `KG F` for facts `F` its changes keep (`Stab`, `…_ct`); `selC`,
`setOneA` and `inverse` need the facts their correctness needs. The taint
checks are the callers' (`by taint_decide` on the concrete code).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## Clearing and copying -/

/-- The registers `zeroA` changes. -/
abbrev zRegs : List Reg := [.x11, .x12, .x8, .x7, .x14, .x16]

theorem zeroA_eq (j : Nat) : zeroA j = .seq (.block (ws ++ (base j .x8 ++ ([movi .x7 0] : List Instr)))) zeroAcc := by
  simp only [zeroA, List.append_assoc]

theorem zeroA_ct0 {F : KIn → State → Prop} {j : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) hc).isSome = true) :
    RelCT isa (Two (KG F)) (zeroA j) fun _ _ => True := by
  rw [zeroA_eq]; exact kg_ws0 ht

theorem zeroA_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hF : Stab F [.arr j] zRegs)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) hc).isSome = true) :
    RelCT isa (Two (KG F)) (zeroA j) (Two (KG F)) :=
  kg_ct (zeroA_ct0 ht) fun I _ s h _ hf => WP.mono (zeroA_k h hj) fun t ⟨ht, f, _, _, k⟩ =>
    ⟨ht, hF I s t h.hZ hf f k⟩

/-- `zeroA`, and the array zero after it. -/
theorem zeroAZ_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hF : Stab F [.arr j] zRegs)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) hc).isSome = true) :
    RelCT isa (Two (KG F)) (zeroA j) (Two (KG fun I t => F I t ∧ Zero j I t)) :=
  kg_ct (zeroA_ct0 ht) fun I _ s h _ hf => WP.mono (zeroA_k h hj) fun t ⟨ht, f, z, _, k⟩ =>
    ⟨ht, hF I s t h.hZ hf f k, z⟩

/-- The registers `copyA` changes. -/
abbrev cpRegs : List Reg := [.x11, .x12, .x3, .x14, .x16, .x17]

theorem copyA_eq (o a : Nat) : copyA o a = .seq (.block (ws ++ (base a .x16 ++ base o .x17))) copyWords := by
  simp only [copyA, List.append_assoc]

theorem copyA_ct0 {F : KIn → State → Prop} {o a : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base a .x16 ++ base o .x17)) copyWords)
      hc).isSome = true) :
    RelCT isa (Two (KG F)) (copyA o a) fun _ _ => True := by
  rw [copyA_eq]; exact kg_ws0 ht

theorem copyA_ct {F : KIn → State → Prop} {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a)
    (hF : Stab F [.arr o] cpRegs) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base a .x16 ++ base o .x17)) copyWords)
      hc).isSome = true) :
    RelCT isa (Two (KG F)) (copyA o a) (Two (KG F)) :=
  kg_ct (copyA_ct0 ht) fun I _ s h _ hf => WP.mono (copyA_k h ho ha hoa) fun t ⟨ht, f, _, _, k⟩ =>
    ⟨ht, hF I s t h.hZ hf f k⟩

/-- `[o] := [a]`, with word `W` of `[o]` zero. -/
theorem zc_ct {F : KIn → State → Prop} {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a)
    (hF : Stab F [.arr o] allR) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base o .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base a .x16 ++ base o .x17)) copyWords)
      hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (.seq (zeroA o) (copyA o a)) (Two (KG fun I t => F I t ∧ TopZ o I t)) :=
  RelCT.seq (kg_ct (G := fun I t => F I t ∧ TopZ o I t) (zeroA_ct0 ht₁) fun I _ s h _ hf =>
      WP.mono (zeroA_k h ho) fun _ ⟨ht, f, z, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f (k.mono (by decide)), (wv_zero2 z).2⟩)
    (kg_ct (copyA_ct0 ht₂) fun I _ s h _ ⟨hf, t0⟩ => WP.mono (copyA_k h ho ha hoa) fun _ ⟨ht, f, _, tt, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f (k.mono (by decide)), tt.trans t0⟩)

/-! ## Constants -/

/-- The registers `constA` changes. -/
abbrev cRegs : List Reg := [.x11, .x12, .x8, .x7, .x14, .x16, .x3]

theorem constA_eq (x : Nat) : seqs (constA x) = .seq (zeroA aC)
    (.block (ws ++ (base aC .x16 ++ ([movi .x3 x, st .x3 .x16] : List Instr)))) := by
  simp only [constA, seqs, List.append_assoc]

theorem constA_ct0 {F : KIn → State → Prop} (x : Nat) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base aC .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11])
      (.block (base aC .x16 ++ ([movi .x3 x, st .x3 .x16] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (constA x)) fun _ _ => True := by
  rw [constA_eq]
  exact kg_then (G := NF) (zeroA_ct0 ht₁) (fun I _ s h _ _ => WP.mono (zeroA_k h (j := aC) (by decide))
    fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) (kg_wsb0 ht₂)

theorem constA_ct {F : KIn → State → Prop} (x : Nat) (hx : x < 2 ^ 16) (hF : Stab F [.arr aC] cRegs)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base aC .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11])
      (.block (base aC .x16 ++ ([movi .x3 x, st .x3 .x16] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (constA x)) (Two (KG F)) :=
  kg_ct (constA_ct0 x ht₁ ht₂) fun I _ s h _ hf => WP.mono (constA_k h hx) fun t ⟨ht, f, _, k⟩ =>
    ⟨ht, hF I s t h.hZ hf f k⟩

/-! ## Comparisons and masks -/

/-- The registers `ltA` and `geA` change. -/
abbrev ltRegs : List Reg := [.x3, .x4, .x7, .x11, .x12, .x14, .x15, .x16, .x17]

theorem ltA_eq (a b : Nat) : seqs (ltA a b) = .seq (.block (ws ++ (([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] :
    List Instr) ++ (base a .x16 ++ base b .x17)))) (.seq cmpLoop (.block borrowMask)) := by
  simp only [ltA, cmpA, seqs, List.append_assoc, List.cons_append, List.nil_append]

theorem geA_eq (a b : Nat) : seqs (geA a b) = .seq (.block (ws ++ (([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] :
    List Instr) ++ (base a .x16 ++ base b .x17)))) (.seq cmpLoop (.block carryMask)) := by
  simp only [geA, cmpA, seqs, List.append_assoc, List.cons_append, List.nil_append]

theorem ltA_ct {F G : KIn → State → Prop} {a b : Nat} (ha : a < 16) (hb : b < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → t.mem = s.mem → Keep ltRegs s t →
      t.gpr .x15 = mask (decide (av I s.mem a < av I s.mem b)) → G I t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7] : List Instr) ++ (base a .x16 ++ base b .x17))) (.seq cmpLoop (.block borrowMask)))
      hc).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (ltA a b)) (Two (KG G)) := by
  rw [ltA_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← ltA_eq]
    exact WP.mono (ltA_k h ha hb) fun t ⟨ht, hm, h15, _, k⟩ => ⟨ht, hFG I s t h.hZ hf hm k h15⟩

theorem geA_ct {F G : KIn → State → Prop} {a b : Nat} (ha : a < 16) (hb : b < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → t.mem = s.mem → Keep ltRegs s t →
      t.gpr .x15 = mask (decide (av I s.mem b ≤ av I s.mem a)) → G I t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7] : List Instr) ++ (base a .x16 ++ base b .x17))) (.seq cmpLoop (.block carryMask)))
      hc).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (geA a b)) (Two (KG G)) := by
  rw [geA_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← geA_eq]
    exact WP.mono (geA_k h ha hb) fun t ⟨ht, hm, h15, _, k⟩ => ⟨ht, hFG I s t h.hZ hf hm k h15⟩

/-- The registers `eqMask` and `neMask` change. -/
abbrev eqRegs : List Reg := [.x3, .x4, .x7, .x9, .x11, .x12, .x14, .x15, .x16, .x17]

theorem eqMask_eq (a b : Nat) : seqs (eqMask a b) = .seq (.block (ws ++ ([movi .x9 0, mov .x14 .x12] : List Instr)))
    (.seq (.block (base a .x16 ++ base b .x17)) (.seq (countLoop .x14 xorBody) (.block zeroMask))) := by
  simp only [eqMask, eqA, seqs, List.cons_append, List.nil_append]

theorem neMask_eq (a b : Nat) : seqs (neMask a b) = .seq (.block (ws ++ ([movi .x9 0, mov .x14 .x12] : List Instr)))
    (.seq (.block (base a .x16 ++ base b .x17)) (.seq (countLoop .x14 xorBody) (.block nonzeroMask))) := by
  simp only [neMask, eqA, seqs, List.cons_append, List.nil_append]

theorem eqMask_ct {F G : KIn → State → Prop} {a b : Nat} (ha : a < 16) (hb : b < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → t.mem = s.mem → Keep eqRegs s t →
      t.gpr .x15 = mask (decide (av I s.mem a = av I s.mem b)) → G I t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x9 0, mov .x14 .x12] : List Instr))
      (.seq (.block (base a .x16 ++ base b .x17)) (.seq (countLoop .x14 xorBody) (.block zeroMask)))) hc).isSome =
      true) :
    RelCT isa (Two (KG F)) (seqs (eqMask a b)) (Two (KG G)) := by
  rw [eqMask_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← eqMask_eq]
    exact WP.mono (eqMask_k h ha hb) fun t ⟨ht, hm, h15, _, k⟩ => ⟨ht, hFG I s t h.hZ hf hm k h15⟩

theorem neMask_ct {F G : KIn → State → Prop} {a b : Nat} (ha : a < 16) (hb : b < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → t.mem = s.mem → Keep eqRegs s t →
      t.gpr .x15 = mask (!decide (av I s.mem a = av I s.mem b)) → G I t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x9 0, mov .x14 .x12] : List Instr))
      (.seq (.block (base a .x16 ++ base b .x17)) (.seq (countLoop .x14 xorBody) (.block nonzeroMask)))) hc).isSome =
      true) :
    RelCT isa (Two (KG F)) (seqs (neMask a b)) (Two (KG G)) := by
  rw [neMask_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← neMask_eq]
    exact WP.mono (neMask_k h ha hb) fun t ⟨ht, hm, h15, _, k⟩ => ⟨ht, hFG I s t h.hZ hf hm k h15⟩

/-! ## Selection and setting -/

/-- The registers `selC` changes. -/
abbrev selRegs : List Reg := [.x3, .x4, .x11, .x12, .x14, .x16, .x17]

theorem selC_eq (j : Nat) : seqs (selC j) = .seq (.block (ws ++ (([mov .x14 .x12] : List Instr) ++
    (base aC .x16 ++ base j .x17)))) VG.Impl.Rsa.AArch64.Crt.selLoop := by
  simp only [selC, seqs, List.append_assoc]

theorem selC_ct0 {F : KIn → State → Prop} {j : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([mov .x14 .x12] : List Instr) ++
      (base aC .x16 ++ base j .x17))) VG.Impl.Rsa.AArch64.Crt.selLoop) hc).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (selC j)) fun _ _ => True := by
  rw [selC_eq]; exact kg_ws0 ht

/-- `selC j` under a mask in `x15`. -/
theorem selC_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjC : j ≠ aC) (hF : Stab F [.arr j] selRegs)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([mov .x14 .x12] : List Instr) ++
      (base aC .x16 ++ base j .x17))) VG.Impl.Rsa.AArch64.Crt.selLoop) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ X15M I t)) (seqs (selC j)) (Two (KG F)) :=
  kg_ct (selC_ct0 ht) fun I _ s h _ ⟨hf, _, h15⟩ => WP.mono (selC_k h hj hjC h15) fun t ⟨ht, f, _, _, k⟩ =>
    ⟨ht, hF I s t h.hZ hf f k⟩

/-- The registers `setOneA` changes. -/
abbrev soRegs : List Reg := [.x11, .x12, .x16, .x3]

theorem setOneA_eq (j : Nat) : setOneA j = ws ++ (base j .x16 ++ ([movi .x3 1, st .x3 .x16] : List Instr)) := by
  simp only [setOneA, List.append_assoc]

theorem setOne_ct {F G : KIn → State → Prop} {j : Nat} (hj : j < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → 1 ≤ I.W → F I s → KF I.B I.W [.arr j] s.mem t.mem → Keep soRegs s t →
      av I t.mem j = 1 → G I t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block (base j .x16 ++ ([movi .x3 1, st .x3 .x16] :
      List Instr))) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ Zero j I t)) (.block (setOneA j)) (Two (KG G)) := by
  rw [setOneA_eq]
  exact kg_wsb ht fun I _ s h _ ⟨hf, hz⟩ => by
    rw [← setOneA_eq]
    have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_arith
    exact WP.mono (setOne_k h hj hz) fun t ⟨ht, f, v, k⟩ =>
      ⟨ht, hFG I s t h.hZ hw1 hf f k (av_of_full v (Nat.one_lt_two_pow (by omega_arith)))⟩

/-! ## Division and inverses -/

/-- The registers `divmod` and `inverse` change. -/
abbrev dvRegs : List Reg := .x11 :: .x12 :: stepRegs

theorem divmod_eq (iQ iR iD iT : Nat) : divmod iQ iR iD iT = .seq (zeroA iR) (.seq (.block [.lsl .x .x6 .x12 6])
    (.loop (VG.Impl.Rsa.AArch64.Keys.divStep iQ iR iD iT) (.nonzero .x .x6))) := rfl

theorem divmod_ct {F : KIn → State → Prop} {iQ iR iD iT : Nat} (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16)
    (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT) (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT)
    (hF : Stab F [.arr iQ, .arr iR, .arr iT] dvRegs) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base iR .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [.lsl .x .x6 .x12 6])
      (.loop (VG.Impl.Rsa.AArch64.Keys.divStep iQ iR iD iT) (.nonzero .x .x6))) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (divmod iQ iR iD iT) (Two (KG F)) := by
  rw [divmod_eq]
  refine kg_ct (kpin_seq0 [.x0, .x12, .x11] (fun p : KP => wsVal p.q.B p.q.W) (zeroA_ct0 ht₁)
    (fun _ _ h => WP.mono (zeroA_ok h.ws hR) fun _ ⟨_, _, h12, h11, _, k⟩ =>
      wsVal_of ((k.gpr .x0 (by decide)).trans h.ws.x0) h12 h11) ht₂) fun I _ s h _ hf => ?_
  rw [← divmod_eq]
  refine WP.mono (divmod_ok h.ws hQ hR hD hT dQR dQD dQT dRD dRT dDT) fun t ⟨_, hf', k, _⟩ => ?_
  have f : KF I.B I.W [.arr iQ, .arr iR, .arr iT] s.mem t.mem := hf'
  exact ⟨h.step f (all_mut_arrs (js := [iQ, iR, iT]) (by simp [hQ, hR, hT])) k, hF I s t h.hZ hf f k⟩

/-- `inverse`'s start, for `u`, `v`, `x₁`, `x₂` and the modulus `m`. -/
abbrev InvS (iU iV iX₁ iX₂ iM : Nat) : KIn → State → Prop := fun I t =>
  atop I t.mem iU = 0 ∧ av I t.mem iV = av I t.mem iM ∧ av I t.mem iX₁ = 1 ∧ av I t.mem iX₂ = 0

theorem inverse_eq (iU iV iX₁ iX₂ iM iT : Nat) : inverse iU iV iX₁ iX₂ iM iT =
    .seq (.block (ws ++ ([.lsr .x .x3 .x12 21] : List Instr)))
      (.ite (.zero .x .x3) (VG.Impl.Rsa.AArch64.Keys.inverseB iU iV iX₁ iX₂ iM iT)
        (VG.Impl.Rsa.AArch64.Keys.inverseBits iU iV iX₁ iX₂ iM iT)) := rfl

theorem inverse_ct0 {F : KIn → State → Prop} {iU iV iX₁ iX₂ iM iT : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([.lsr .x .x3 .x12 21] : List Instr))
      (.ite (.zero .x .x3) (VG.Impl.Rsa.AArch64.Keys.inverseB iU iV iX₁ iX₂ iM iT) (VG.Impl.Rsa.AArch64.Keys.inverseBits iU iV iX₁ iX₂ iM iT))) hc).isSome = true) :
    RelCT isa (Two (KG F)) (inverse iU iV iX₁ iX₂ iM iT) fun _ _ => True := by
  rw [inverse_eq]; exact kg_ws0 ht

theorem inverse_ct [VG.Proof.Rsa.AArch64.InvLaw] {F : KIn → State → Prop} {iU iV iX₁ iX₂ iM iT : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT)
    (hF : Stab F [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT] dvRegs)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([.lsr .x .x3 .x12 21] : List Instr))
      (.ite (.zero .x .x3) (VG.Impl.Rsa.AArch64.Keys.inverseB iU iV iX₁ iX₂ iM iT) (VG.Impl.Rsa.AArch64.Keys.inverseBits iU iV iX₁ iX₂ iM iT))) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ InvS iU iV iX₁ iX₂ iM I t)) (inverse iU iV iX₁ iX₂ iM iT)
      (Two (KG F)) :=
  kg_ct (inverse_ct0 ht) fun I _ s h _ ⟨hf, hU0, hVM, hX1, hX2⟩ => by
    refine WP.mono (InvLaw.inverse_ok h.ws hU hV hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M
      dX₂T dMT hU0 hVM hX1 hX2) fun t ⟨_, hf', k, _⟩ => ?_
    have hn := h.ws.scr.nowrap
    have f : KF I.B I.W [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT] s.mem t.mem :=
      KF.of_frm hf' fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact ⟨.arr iU, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
        · exact ⟨.arr iV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
        · exact ⟨.arr iX₁, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
        · exact ⟨.arr iX₂, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
        · exact ⟨.arr iT, by simp, by simp [Rc.range], by simp [Rc.range]⟩
    exact ⟨h.step f (all_mut_arrs (js := [iU, iV, iX₁, iX₂, iT]) (by simp [hU, hV, hX₁, hX₂, hT])) k,
      hF I s t h.hZ hf f k⟩

/-- Array `j` fits in the primes' `w = W / 2` words. -/
abbrev Fits (j : Nat) : KIn → State → Prop := fun I t => av I t.mem j < 2 ^ (64 * (I.pl / 8))

theorem inverseHalf_eq (iU iV iX₁ iX₂ iM iT : Nat) : inverseAt halfW iU iV iX₁ iX₂ iM iT =
    .seq (.block (ws ++ halfW)) (seqs ([VG.Impl.Rsa.AArch64.Keys.inverseB iU iV iX₁ iX₂ iM iT] ++ tailZ iV ++
      tailZ iX₂)) := rfl

/-- `inverseAt halfW`, from `[v] = [m]` and `[u]`, `[m]` of the primes'
width, for facts `F` that its changes keep. -/
theorem inverseHalf_ct [VG.Proof.Rsa.AArch64.InvLaw] {F : KIn → State → Prop} {iU iV iX₁ iX₂ iM iT : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT)
    (hF : Stab F [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT] dvRegs)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block halfW)
      (seqs ([VG.Impl.Rsa.AArch64.Keys.inverseB iU iV iX₁ iX₂ iM iT] ++ tailZ iV ++ tailZ iX₂))) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ AvEq iV iM I t ∧ Fits iU I t ∧ Fits iM I t))
      (inverseAt halfW iU iV iX₁ iX₂ iM iT) (Two (KG F)) :=
  kg_ct (by rw [inverseHalf_eq]; exact kg_ws0 ht) fun I _ s h L ⟨hf, hVM, bU, bM⟩ =>
    WP.mono (inverseHalf_k h L hU hV hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT
      bU bM hVM) fun t ⟨ht, f, k, _⟩ => ⟨ht, hF I s t h.hZ hf f k⟩

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-!
# An RSA key from its primes on AArch64: the primes

The loads of `p`, `q` and `e` (`loads_k`), `p` and `q` ordered (`order_k`),
and `p − 1` and `q − 1` (`decTo_k`); together, from `KS` to `KPrimes`
(`front_k`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## The loads -/

/-- `p`, `q` (`pl` octets each) into `aPa` and `aQa`, and `e` into `kEv`. -/
theorem loads_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (L : KLens I) :
    WP isa (seqs (loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++
      ([.block [sth .x3 kEv]] : List (Prog isa)))))) s
      fun t => KS I s₀ t ∧ KF I.B I.W [.arr aPa, .arr aQa, .hdr kEv] s.mem t.mem ∧
        av I t.mem aPa = I.P₀ ∧ av I t.mem aQa = I.Q₀ ∧ word t.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
  have hZ := h.hZ
  have hW := L.W
  have hpl1 := L.pl1
  have hpl8 := L.pl8
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h.ws (j := aPa) (by decide)
    (by decide) (by decide) h.args.pp h.args.pl h.p L.pbl (by omega_arith) (by omega_arith)) fun s₁ ⟨v₁, o₁, _, _, k₁⟩ => ?_)
  have f₁ := KF.arr1 (B := I.B) (W := I.W) (j := aPa) o₁ (Nat.le_refl _) (Nat.le_refl _)
  have h₁ := h.step f₁ (all_mut_arr (by decide)) k₁
  refine wp_seqs_append (by simp [loadA]) (by simp [loadE]) (WP.mono (loadA_ok h₁.ws (j := aQa) (by decide)
    (by decide) (by decide) h₁.args.qp h₁.args.pl h₁.q L.qbl (by omega_arith) (by omega_arith)) fun s₂ ⟨v₂, o₂, _, _, k₂⟩ => ?_)
  have f₂ := KF.arr1 (B := I.B) (W := I.W) (j := aQa) o₂ (Nat.le_refl _) (Nat.le_refl _)
  have h₂ := h₁.step f₂ (all_mut_arr (by decide)) k₂
  refine wp_seqs_append (by simp [loadE]) (by simp) (WP.mono (loadE_ok h₂.ws h₂.args.e
    (by rw [h₂.args.el, L.ebl]) (by rw [L.ebl]; exact L.el1) (by rw [L.ebl]; exact L.el8) h₂.e)
    fun s₃ ⟨hx3, m₃, k₃⟩ => ?_)
  have h₃ := h₂.regs m₃ k₃
  simp only [seqs]
  have hst := h₃.ws.scr.st (d := 8 * kEv) (by have := h₃.ws.h256; unfold kEv sFn; omega_arith)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₃.mem.writeW (off I.B (8 * kEv))
    (BitVec.ofNat 64 I.E)) (by
      have hx3' : s₃.gpr .x3 = BitVec.ofNat 64 I.E := by
        show _ = BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb); rw [← hx3, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      brun [h₃.ws.x0, hdr_enc (show kEv < 32 by decide), hst, hx3']) rfl rfl rfl) fun t ⟨hm, k₄⟩ => ?_
  obtain ⟨ht, f₄, hw⟩ := h₃.hdrW (i := kEv) (by unfold kEv sFn; omega_arith) hm k₄
  refine ⟨ht, ((f₁.trans f₂).trans (by rw [← m₃]; exact f₄)).mono (by decide), ?_, ?_, hw⟩
  · rw [f₄.av (by decide) (j := aPa) (by decide) (by decide) hZ, m₃,
      f₂.av (by decide) (j := aPa) (by decide) (by decide) hZ]; exact v₁
  · rw [f₄.av (by decide) (j := aQa) (by decide) (by decide) hZ, m₃]; exact v₂

/-! ## The order -/

/-- `order`: `p` and `q` swapped if `p < q`. -/
theorem order_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (seqs order) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aPa, .arr aQa] s.mem t.mem ∧
      av I t.mem aPa = (if av I s.mem aPa < av I s.mem aQa then av I s.mem aQa else av I s.mem aPa) ∧
      av I t.mem aQa = (if av I s.mem aPa < av I s.mem aQa then av I s.mem aPa else av I s.mem aQa) := by
  have hn := h.ws.scr.nowrap
  have sP := h.ws.sl (j := aPa) (by decide)
  have sQ := h.ws.sl (j := aQa) (by decide)
  have sp := slot_sep (w := I.W) (j := aPa) (k := aQa) (by decide)
  unfold order
  refine wp_seqs_append (by simp [ltA, cmpA]) (by simp) (WP.mono (ltA_k h (a := aPa) (b := aQa) (by decide)
    (by decide)) fun s₁ ⟨h₁, m₁, h15, _, k₁⟩ => ?_)
  simp only [seqs]
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (wsMov_ok h₁.ws) fun s₂ ⟨⟨h12, h11, h14, m₂, _⟩, k₂⟩ =>
    WP.mono (base2_ok aPa aQa .x16 .x17 ((k₂.gpr .x0 (by decide)).trans h₁.ws.x0) h11)
      fun s₃ ⟨⟨h16, h17, m₃, _⟩, k₃⟩ => ?_))
  have k23 := k₂.trans k₃
  refine WP.mono (cswap_ok (h₁.ws.scr.congr k23.wr) h16 h17 ((k23.gpr .x15 (by decide)).trans h15)
    ((k₃.gpr .x14 (by decide)).trans h14) (by have := h.ws.w1; omega_arith) (by have := h.ws.w2; omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith)) fun t ⟨hX, hY, hf, k₄⟩ => ?_
  have hm : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  rw [hm] at hX hY hf
  have f : KF I.B I.W [.arr aPa, .arr aQa] s.mem t.mem :=
    KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨.arr aPa, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
      · exact ⟨.arr aQa, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
  refine ⟨h.step f (all_mut_arrs (js := [aPa, aQa]) (by decide)) ((k₁.trans k23).trans k₄), f, ?_, ?_⟩
  · dsimp only [av]; rw [hX]; split <;> simp_all <;> (simp only [av] at *; omega_arith)
  · dsimp only [av]; rw [hY]; split <;> simp_all <;> (simp only [av] at *; omega_arith)

/-! ## Minus one -/

theorem dec_arith {x y L : Nat} {b : Bool} (hx : x < L)
    (hv : x + (if (!decide (y = 0)) = true then 1 else 0) = y + L * b.toNat) : x = y - 1 := by
  by_cases hz : y = 0
  · simp only [hz, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, Nat.add_zero, Nat.zero_add] at hv
    cases b <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero] at hv <;> omega_arith
  · simp only [hz, decide_false, Bool.not_false, ite_true] at hv
    cases b <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero] at hv <;> omega_arith

/-- `decTo`'s last part: `[o] := [o] − ([aC] & x15)` over `W` words. -/
theorem subC_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {o : Nat} (ho : o < 16) (hoC : o ≠ aC) {c : Bool}
    (h15 : s.gpr .x15 = mask c) :
    WP isa (seqs [.block (ws ++ ([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr) ++ base o .x16 ++ base aC .x17 ++
        base o .x8), countLoop .x14 subMBody]) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧
      (∃ b : Bool, av I t.mem o + (if c then av I s.mem aC else 0) = av I s.mem o + 2 ^ (64 * I.W) * b.toNat) ∧
      atop I t.mem o = atop I s.mem o := by
  have hn := h.ws.scr.nowrap
  have so := h.ws.sl ho
  have sC := h.ws.sl (j := aC) (by decide)
  have pC := slot_sep (w := I.W) hoC
  simp only [seqs]
  rw [show ws ++ ([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr) ++ base o .x16 ++ base aC .x17 ++ base o .x8 =
    (ws ++ ([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr)) ++ (base o .x16 ++ base aC .x17 ++ base o .x8) by
      simp only [List.append_assoc]]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (ltHead_ok h.ws) fun s₁ ⟨⟨_, h11, _, h14, hc, m₁⟩, k₁⟩ =>
    WP.mono (base3_ok o aC o .x16 .x17 .x8 ((k₁.gpr .x0 (by decide)).trans h.ws.x0) h11)
      fun s₂ ⟨⟨h16, h17, h8, m₂, c₂⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  refine WP.mono (subM_ok (N := I.W) (h.ws.scr.congr k12.wr) h16 h17 h8 ((k₂.gpr .x14 (by decide)).trans h14)
    ((k12.gpr .x15 (by decide)).trans h15) (c₂.trans hc) (by have := h.ws.w1; omega_arith) (by have := h.ws.w2; omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (.inl rfl) (by omega_arith)) fun t ⟨hv, o', k₃⟩ => ?_
  rw [m₂, m₁] at hv o'
  have f := KF.arr1 (B := I.B) (W := I.W) (j := o) o' (Nat.le_refl _) (by omega_arith)
  exact ⟨h.step f (all_mut_arr ho) (k12.trans k₃), f, ⟨_, hv⟩, o'.word (Or.inr (Nat.le_refl _)) (by omega_arith)⟩

/-- `decTo o j`: `[o] := [j] − 1` (0 for 0), with word `W` zero. -/
theorem decTo_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {o j : Nat} (ho : o < 16) (hj : j < 16)
    (hoj : o ≠ j) (hoC : o ≠ aC) (hjC : j ≠ aC) :
    WP isa (seqs (decTo o j)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr o, .arr aC] s.mem t.mem ∧
      av I t.mem o = av I s.mem j - 1 ∧ atop I t.mem o = 0 := by
  have hZ := h.hZ
  have hok : [Rc.arr aC].all Rc.ok = true := by decide
  have e : decTo o j = [zeroA o, copyA o j] ++ (constA 0 ++ (neMask j aC ++ (constA 1 ++
      [.block (ws ++ ([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr) ++ base o .x16 ++ base aC .x17 ++
        base o .x8), countLoop .x14 subMBody]))) := by
    simp only [decTo, List.append_assoc]
  rw [e]
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h ho hj hoj) fun s₁ ⟨h₁, f₁, v₁, t₁⟩ => ?_)
  refine wp_seqs_append (by simp [constA]) (by simp [neMask, eqA]) (WP.mono (constA_k h₁ (x := 0) (by decide))
    fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  have cz : av I s₂.mem aC = 0 := av_of_full c₂ (Nat.two_pow_pos _)
  refine wp_seqs_append (by simp [neMask, eqA]) (by simp [constA]) (WP.mono (neMask_k h₂ (a := j) (b := aC) hj
    (by decide)) fun s₃ ⟨h₃, m₃, h15, _, k₃⟩ => ?_)
  have vj : av I s₂.mem j = av I s.mem j := by
    rw [f₂.av hok hj (by simp [hjC]) hZ]
    exact f₁.av (by simp [Rc.ok, ho]) hj (by simp [hoj.symm]) hZ
  rw [cz, vj] at h15
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h₃ (x := 1) (by decide))
    fun s₄ ⟨h₄, f₄, c₄, k₄⟩ => ?_)
  have c1 : av I s₄.mem aC = 1 := av_of_full c₄ (Nat.one_lt_two_pow (by have := h.ws.w1; omega_arith))
  refine WP.mono (subC_k h₄ (o := o) ho hoC (c := !decide (av I s.mem j = 0))
    (by rw [k₄.gpr .x15 (by decide), h15])) fun t ⟨ht, f₅, hb, t₅⟩ => ?_
  obtain ⟨b, hv⟩ := hb
  have vo : av I s₄.mem o = av I s.mem j := by
    rw [f₄.av hok ho (by simp [hoC]) hZ, m₃, f₂.av hok ho (by simp [hoC]) hZ]; exact v₁
  have tO : atop I s₄.mem o = 0 := by
    rw [f₄.at hok ho (by simp [hoC]) hZ, m₃, f₂.at hok ho (by simp [hoC]) hZ]; exact t₁
  refine ⟨ht, (((f₁.trans f₂).trans (by rw [← m₃]; exact f₄)).trans f₅).mono (by simp), ?_, by rw [t₅]; exact tO⟩
  rw [c1, vo] at hv
  exact dec_arith (wv_lt t.mem I.B (slot I.W o) I.W) hv

/-! ## From the loads to `p − 1` and `q − 1` -/

theorem lt_of_os2ip_len {bs : List Byte} {n : Nat} (h : bs.length = n) : Spec.Rsa.os2ip bs < 2 ^ (8 * n) := by
  have := VG.Proof.Bignum.os2ip_lt bs
  rw [h, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  exact this

/-- The parts the front changes. -/
abbrev csF : List Rc := [.arr aPa, .arr aQa, .hdr kEv, .arr aPm, .arr aQm, .arr aC]

/-- From the loads to `p − 1` and `q − 1`. -/
theorem front_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (L : KLens I) :
    WP isa (seqs (loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++
      (([.block [sth .x3 kEv]] : List (Prog isa)) ++ (order ++ (decTo aPm aPa ++ decTo aQm aQa))))))) s
      fun t => KPrimes I s₀ t ∧ KF I.B I.W csF s.mem t.mem ∧ atop I t.mem aPm = 0 ∧ atop I t.mem aQm = 0 := by
  have hZ := h.hZ
  -- The loads.
  rw [show loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++
      (([.block [sth .x3 kEv]] : List (Prog isa)) ++ (order ++ (decTo aPm aPa ++ decTo aQm aQa))))) =
      (loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [sth .x3 kEv]] : List (Prog isa))))) ++
        (order ++ (decTo aPm aPa ++ decTo aQm aQa)) by simp only [List.append_assoc]]
  refine wp_seqs_append (by simp [loadA]) (by simp [order, ltA, cmpA]) (WP.mono (loads_k h L)
    fun s₁ ⟨h₁, f₁, vP₁, vQ₁, ev₁⟩ => ?_)
  -- The order.
  refine wp_seqs_append (by simp [order, ltA, cmpA]) (by simp [decTo]) (WP.mono (order_k h₁)
    fun s₂ ⟨h₂, f₂, vP₂, vQ₂⟩ => ?_)
  rw [vP₁, vQ₁] at vP₂ vQ₂
  -- `p − 1`, `q − 1`.
  refine wp_seqs_append (by simp [decTo]) (by simp [decTo]) (WP.mono (decTo_k h₂ (o := aPm) (j := aPa) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, vPm₃, tPm₃⟩ => ?_)
  refine WP.mono (decTo_k h₃ (o := aQm) (j := aQa) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨ht, f₄, vQm₄, tQm₄⟩ => ?_
  have hok3 : [Rc.arr aPm, Rc.arr aC].all Rc.ok = true := by decide
  have hok4 : [Rc.arr aQm, Rc.arr aC].all Rc.ok = true := by decide
  refine ⟨⟨ht, ?_, ?_, ?_, ?_, ?_⟩, (((f₁.trans f₂).trans f₃).trans f₄).mono (by decide), ?_, tQm₄⟩
  · rw [f₄.av hok4 (by decide) (by decide) hZ, f₃.av hok3 (by decide) (by decide) hZ, vP₂]
  · rw [f₄.av hok4 (by decide) (by decide) hZ, f₃.av hok3 (by decide) (by decide) hZ, vQ₂]
  · rw [f₄.av hok4 (by decide) (by decide) hZ, vPm₃, vP₂]
  · rw [vQm₄, f₃.av hok3 (by decide) (by decide) hZ, vQ₂]
  · rw [f₄.word hok4 (by decide) (by decide), f₃.word hok3 (by decide) (by decide),
      f₂.word (by decide) (by decide) (by decide), ev₁]
  · rw [f₄.at hok4 (by decide) (by decide) hZ, tPm₃]

/-! ## Bounds on the inputs -/

theorem KLens.P_lt {I : KIn} (L : KLens I) : I.P < 2 ^ (64 * (I.pl / 8)) := by
  have hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega_arith
  have hP₀ : I.P₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.pbl
  have hQ₀ : I.Q₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.qbl
  simp only [KIn.P] at hP₀ hQ₀ ⊢; split <;> omega_arith

theorem KLens.Q_lt {I : KIn} (L : KLens I) : I.Q < 2 ^ (64 * (I.pl / 8)) := by
  have hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega_arith
  have hP₀ : I.P₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.pbl
  have hQ₀ : I.Q₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.qbl
  simp only [KIn.Q] at hP₀ hQ₀ ⊢; split <;> omega_arith

theorem KLens.E_lt {I : KIn} (L : KLens I) : I.E < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (lt_of_os2ip_len L.ebl) (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega_arith))

theorem KLens.L_lt {I : KIn} (L : KLens I) : I.L < 2 ^ (64 * I.W) := by
  have hW := L.W
  have hPw := L.P_lt
  have hQw := L.Q_lt
  have h1 : I.L ≤ (I.P - 1) * (I.Q - 1) ∨ I.L = 0 := by
    rcases Nat.eq_zero_or_pos ((I.P - 1) * (I.Q - 1)) with h0 | h0
    · right; simp only [KIn.L]
      rcases Nat.mul_eq_zero.mp h0 with h' | h' <;> simp [h']
    · left; exact Nat.le_of_dvd h0 (Nat.lcm_dvd_mul _ _)
  have h2 : (I.P - 1) * (I.Q - 1) < 2 ^ (64 * I.W) := by
    rw [hW, show 64 * (2 * (I.pl / 8)) = 64 * (I.pl / 8) + 64 * (I.pl / 8) by omega_arith, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le (by omega_arith) (by omega_arith) (Nat.two_pow_pos _)
  rcases h1 with h1 | h1
  · omega_arith
  · rw [h1]; exact Nat.two_pow_pos _

end VG.Proof.RsaKeyGen.AArch64.Key
