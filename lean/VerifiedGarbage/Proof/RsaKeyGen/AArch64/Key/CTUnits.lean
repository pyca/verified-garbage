import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTBase

/-!
# An RSA key from its primes on AArch64: constant time, the key routines

Each of `zeroA`, `copyA`, `constA`, `ltA`, `geA`, `eqMask`, `neMask`,
`selC`, `setOneA`, `oddMaskOf`, `evenMaskOf`, `divmod` and `inverse` leaks
the same from two runs in `KG F` (`…_ct0`, with no postcondition), and
leaves `KG F` for facts `F` its changes keep (`Stab`, `…_ct`); `selC`,
`setOneA` and `inverse` need the facts their correctness needs. The taint
checks are the callers' (`by taint_decide` on the concrete code).
-/

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

/-- The registers `oddMaskOf` changes. -/
abbrev omRegs : List Reg := [.x3, .x4, .x7, .x11, .x12, .x15, .x16]

/-- The registers `evenMaskOf` changes. -/
abbrev emRegs : List Reg := [.x3, .x4, .x11, .x12, .x15, .x16]

theorem oddMaskOf_eq (j : Nat) : oddMaskOf j = ws ++ (base j .x16 ++ ([movi .x7 0, ld .x3 .x16] ++ oddMask)) := by
  simp only [oddMaskOf, List.append_assoc]

theorem evenMaskOf_eq (j : Nat) : evenMaskOf j = ws ++ (base j .x16 ++ ([ld .x3 .x16, movi .x4 1,
    .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] : List Instr)) := by
  simp only [evenMaskOf, List.append_assoc]

theorem oddMaskOf_ct {F G : KIn → State → Prop} {j : Nat} (hj : j < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → t.mem = s.mem → Keep omRegs s t →
      t.gpr .x15 = mask (decide (av I s.mem j % 2 = 1)) → G I t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block (base j .x16 ++ ([movi .x7 0, ld .x3 .x16] ++ oddMask)))
      hc).isSome = true) :
    RelCT isa (Two (KG F)) (.block (oddMaskOf j)) (Two (KG G)) := by
  rw [oddMaskOf_eq]
  exact kg_wsb ht fun I _ s h _ hf => by
    rw [← oddMaskOf_eq]
    exact WP.mono (oddMaskOf_k h hj) fun t ⟨ht, hm, h15, _, _, _, k⟩ => ⟨ht, hFG I s t h.hZ hf hm k h15⟩

theorem evenMaskOf_ct {F G : KIn → State → Prop} {j : Nat} (hj : j < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → t.mem = s.mem → Keep emRegs s t →
      t.gpr .x15 = mask (decide (av I s.mem j % 2 = 0)) → G I t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block (base j .x16 ++ ([ld .x3 .x16, movi .x4 1,
      .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (KG F)) (.block (evenMaskOf j)) (Two (KG G)) := by
  rw [evenMaskOf_eq]
  exact kg_wsb ht fun I _ s h _ hf => by
    rw [← evenMaskOf_eq]
    exact WP.mono (evenMaskOf_k h hj) fun t ⟨ht, hm, h15, _, _, k⟩ => ⟨ht, hFG I s t h.hZ hf hm k h15⟩

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
    have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
    exact WP.mono (setOne_k h hj hz) fun t ⟨ht, f, v, k⟩ =>
      ⟨ht, hFG I s t h.hZ hw1 hf f k (av_of_full v (Nat.one_lt_two_pow (by omega)))⟩

/-- `zeroA j` then `setOneA j`. -/
theorem one_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hF : Stab F [.arr j] allR)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block (base j .x16 ++ ([movi .x3 1, st .x3 .x16] :
      List Instr))) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (.seq (zeroA j) (.block (setOneA j))) (Two (KG fun I t => F I t ∧ AvIs j 1 I t)) :=
  RelCT.seq (zeroAZ_ct hj (hF.sub) ht₁)
    (setOne_ct hj (fun I s t hZ _ hf f k v => ⟨hF I s t hZ hf (f.mono (by simp)) (k.mono (by decide)), v⟩) ht₂)

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
    .seq (.block (ws ++ ([.lsl .x .x6 .x12 7] : List Instr)))
      (.loop (VG.Impl.Rsa.AArch64.Keys.invStep iU iV iX₁ iX₂ iM iT) (.nonzero .x .x6)) := rfl

theorem inverse_ct0 {F : KIn → State → Prop} {iU iV iX₁ iX₂ iM iT : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([.lsl .x .x6 .x12 7] : List Instr))
      (.loop (VG.Impl.Rsa.AArch64.Keys.invStep iU iV iX₁ iX₂ iM iT) (.nonzero .x .x6))) hc).isSome = true) :
    RelCT isa (Two (KG F)) (inverse iU iV iX₁ iX₂ iM iT) fun _ _ => True := by
  rw [inverse_eq]; exact kg_ws0 ht

theorem inverse_ct {F : KIn → State → Prop} {iU iV iX₁ iX₂ iM iT : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT)
    (hF : Stab F [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT] dvRegs)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([.lsl .x .x6 .x12 7] : List Instr))
      (.loop (VG.Impl.Rsa.AArch64.Keys.invStep iU iV iX₁ iX₂ iM iT) (.nonzero .x .x6))) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ InvS iU iV iX₁ iX₂ iM I t)) (inverse iU iV iX₁ iX₂ iM iT)
      (Two (KG F)) :=
  kg_ct (inverse_ct0 ht) fun I _ s h _ ⟨hf, hU0, hVM, hX1, hX2⟩ => by
    refine WP.mono (inverse_ok h.ws hU hV hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M
      dX₂T dMT hU0 hVM hX1 hX2) fun t ⟨_, hf', k, _⟩ => ?_
    have hn := h.ws.scr.nowrap
    have f : KF I.B I.W [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT] s.mem t.mem :=
      KF.of_frm hf' fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact ⟨.arr iU, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
        · exact ⟨.arr iV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
        · exact ⟨.arr iX₁, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
        · exact ⟨.arr iX₂, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
        · exact ⟨.arr iT, by simp, by simp [Rc.range], by simp [Rc.range]⟩
    exact ⟨h.step f (all_mut_arrs (js := [iU, iV, iX₁, iX₂, iT]) (by simp [hU, hV, hX₁, hX₂, hT])) k,
      hF I s t h.hZ hf f k⟩

end VG.Proof.RsaKeyGen.AArch64.Key
