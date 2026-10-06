import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.CTBase

/-!
# An RSA key from its primes on x86-64: constant time, the key routines

Each of `constA`, `ltA`, `eqMask`, `selC`, `subC`, `setOneA`, `divmod` and
`inverse` leaks the same from two runs in `KG F` and leaves `KG F`, for
facts `F` its changes keep (`Stab`); `selC`, `subC`, `setOneA` and
`inverse` need the facts their correctness needs.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- `constA`'s store of `x`. -/
theorem constBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (x : BitVec 32) :
    WP isa (.block (ws ++ (base aC .rbx ++ ([.mov32 .rax (.imm x), .store (at0 .rbx) .rax] : List Instr)))) s
      fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem ∧ Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.ws.scr.nowrap
  have sC := h.ws.sl (j := aC) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aC (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.ws.rdi) h9)
    fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
  have hs₃ := h.ws.scr.congr (k₂.trans k₃).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off I.B (slot I.W aC)) (x.setWidth 64)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₃.st (d := slot I.W aC) (by omega), m₃, m₂]) rfl) fun t ⟨hm, k₄⟩ => ?_
  have o₄ := writeW_outside s.mem I.B (x.setWidth 64) (d := slot I.W aC) (by omega)
  rw [← hm] at o₄
  have f₄ := KF.arr1 (j := aC) o₄ (Nat.le_refl _) (by omega)
  have kk := (k₂.trans k₃).trans k₄
  exact ⟨h.step f₄ (all_mut_arr (by decide)) kk (by decide), f₄, kk.mono (by simp)⟩

theorem constA_ct {F : KIn → State → Prop} (x : BitVec 32) (hF : Stab F [.arr aC] [.r12, .r9, .r8, .rax, .r14, .rbx])
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base aC .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.block (base aC .rbx ++ ([.mov32 .rax (.imm x), .store (at0 .rbx) .rax] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (constA x)) (Two (KG F)) := by
  have e : seqs (constA x) = .seq (zeroA aC)
      (.block (ws ++ (base aC .rbx ++ ([.mov32 .rax (.imm x), .store (at0 .rbx) .rax] : List Instr)))) := by
    simp only [constA, seqs, List.append_assoc]
  rw [e]
  exact RelCT.seq (zeroA_ct (by decide) (hF.mono (by simp) (by simp)) ht₁)
    (kg_wsb ht₂ fun I _ s h _ hf => WP.mono (constBlk_k h x) fun _ ⟨ht, f, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f (k.mono (by simp))⟩)

theorem ltA_eq (a b : Nat) : seqs (ltA a b) = .seq (.block (ws ++ (base a .rbx ++ (base b .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr)))))
    (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp]) := by
  simp only [ltA, seqs, List.append_assoc]

theorem ltA_ct {F G : KIn → State → Prop} {a b : Nat} (ha : a < 16) (hb : b < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → t.mem = s.mem → Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t →
      t.gpr .rbp = mask (decide (av I s.mem a < av I s.mem b)) → G I t)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr))))
      (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp]))
      hc).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (ltA a b)) (Two (KG G)) := by
  rw [ltA_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← ltA_eq]
    exact WP.mono (ltA_k h ha hb) fun _ ⟨ht, hm, hbp, _, _, _, k⟩ => ⟨ht, hFG I s _ h.hZ hf hm k hbp⟩

theorem eqMask_eq (a b : Nat) : seqs (eqMask a b) = .seq (.block (ws ++ (base a .rbx ++ (base b .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr))))) (.seq (wordLoop 0 xorBody) (.block isZero)) := by
  simp only [eqMask, eqA, seqs, List.append_assoc, List.cons_append, List.nil_append]

theorem eqMask_ct {F G : KIn → State → Prop} {a b : Nat} (ha : a < 16) (hb : b < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → t.mem = s.mem → Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t →
      t.gpr .rbp = mask (decide (av I s.mem a = av I s.mem b)) → G I t)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr)))) (.seq (wordLoop 0 xorBody) (.block isZero))) hc).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (eqMask a b)) (Two (KG G)) := by
  rw [eqMask_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← eqMask_eq]
    exact WP.mono (eqMask_k h ha hb) fun _ ⟨ht, hm, hbp, k⟩ => ⟨ht, hFG I s _ h.hZ hf hm k hbp⟩

/-- A mask in `rbp`. -/
abbrev RbpM : KIn → State → Prop := fun _ t => ∃ c, t.gpr .rbp = mask c

/-- A mask in `r15`. -/
abbrev R15M : KIn → State → Prop := fun _ t => ∃ c, t.gpr .r15 = mask c

theorem selC_eq (j : Nat) : seqs (selC j) = .seq (.block (ws ++ (base j .r8 ++ base aC .rsi))) (wordLoop 0 selBody) := by
  simp only [selC, seqs, List.append_assoc]

theorem selC_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjC : j ≠ aC)
    (hF : Stab F [.arr j] [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14]) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8 ++ base aC .rsi))
      (wordLoop 0 selBody)) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ RbpM I t)) (seqs (selC j)) (Two (KG F)) := by
  rw [selC_eq]
  exact kg_ws ht fun I _ s h _ ⟨hf, c, hbp⟩ => by
    rw [← selC_eq]
    exact WP.mono (selC_k h hj hjC hbp) fun _ ⟨ht, f, _, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

theorem subC_eq (o a : Nat) : seqs (subC o a) = .seq (.block (ws ++ (base a .r8 ++ (base aC .r10 ++ (base o .rsi ++
    ([.mov32 .rbp (.imm 0)] : List Instr)))))) (wordLoop 0 subMBody) := by
  simp only [subC, seqs, List.append_assoc]

theorem subC_ct {F : KIn → State → Prop} {o a : Nat} (ho : o < 16) (ha : a < 16) (hoC : o ≠ aC) (haC : a ≠ aC)
    (hoa : o = a ∨ o ≠ a) (hF : Stab F [.arr o] [.r12, .r9, .r8, .r10, .rsi, .rbp, .rax, .rdx, .r14])
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .r8 ++ (base aC .r10 ++
      (base o .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr))))) (wordLoop 0 subMBody)) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ R15M I t)) (seqs (subC o a)) (Two (KG F)) := by
  rw [subC_eq]
  exact kg_ws ht fun I _ s h _ ⟨hf, c, h15⟩ => by
    rw [← subC_eq]
    exact WP.mono (subC_k h ho ha hoC haC hoa h15) fun _ ⟨ht, f, _, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

/-- Array `j` zero. -/
abbrev Zero (j : Nat) : KIn → State → Prop := fun I t => wv t.mem I.B (slot I.W j) (I.W + 2) = 0

theorem setOneA_eq (j : Nat) : setOneA j = ws ++ (base j .rbx ++
    ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr)) := by
  simp only [setOneA, List.append_assoc]

theorem setOne_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hF : Stab F [.arr j] [.r12, .r9, .rbx, .rax])
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++
      ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ Zero j I t)) (.block (setOneA j)) (Two (KG F)) := by
  rw [setOneA_eq]
  exact kg_wsb ht fun I _ s h _ ⟨hf, hz⟩ => by
    rw [← setOneA_eq]
    exact WP.mono (setOne_k h hj hz) fun _ ⟨ht, f, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

/-- `zeroA j` then `setOneA j`. -/
theorem one_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hF : Stab F [.arr j] [.r12, .r9, .r8, .rbx, .rax, .r14])
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++
      ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (.seq (zeroA j) (.block (setOneA j))) (Two (KG F)) :=
  RelCT.seq (kg_ws ht₁ fun I _ s h _ hf => WP.mono (zeroA_k h hj) fun _ ⟨ht, f, hz, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f (k.mono (by simp)), hz⟩)
    (setOne_ct hj (hF.mono (by simp) (by simp)) ht₂)

/-- The registers `divmod` and `inverse` may change. -/
abbrev dvRegs : List Reg := List.filter (· != .rdi) (.r9 :: .r11 :: stepRegs)

theorem divmod_eq (iQ iR iD iT : Nat) : divmod iQ iR iD iT = .seq (.block (ws ++ (base iR .r8 ++
    (([.mov .r11 (.reg .r12)] : List Instr) ++ (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++
    ([.mov32 .r13 (.imm 0)] : List Instr))))))
    (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep iQ iR iD iT) .ne)) := by
  simp only [divmod, divInit, seqs, List.append_assoc]

theorem divmod_ct {F : KIn → State → Prop} {iQ iR iD iT : Nat} (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16)
    (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT) (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT)
    (hF : Stab F [.arr iQ, .arr iR, .arr iT] dvRegs) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base iR .r8 ++
      (([.mov .r11 (.reg .r12)] : List Instr) ++ (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++
      ([.mov32 .r13 (.imm 0)] : List Instr)))))
      (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep iQ iR iD iT) .ne))) hc).isSome = true) :
    RelCT isa (Two (KG F)) (divmod iQ iR iD iT) (Two (KG F)) := by
  rw [divmod_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← divmod_eq]
    refine WP.mono (divmod_ok h.ws.scr h.ws.rdi h.ws.hw h.ws.hS (by have := h.ws.w1; omega) h.ws.w2 h.ws.hZ hQ hR hD
      hT dQR dQD dQT dRD dRT dDT) fun t ⟨hdi, hf', k, _⟩ => ?_
    have f : KF I.B I.W [.arr iQ, .arr iR, .arr iT] s.mem t.mem := hf'
    have k' : Keep dvRegs s t :=
      ⟨fun r hr => if e : r = .rdi then by rw [e, hdi, h.ws.rdi] else k.1 r fun hm => hr (List.mem_filter.mpr
        ⟨hm, by simp [e]⟩), k.2⟩
    exact ⟨h.step f (all_mut_arrs (js := [iQ, iR, iT]) (by simp [hQ, hR, hT])) k' (by decide), hF I s t h.hZ hf f k'⟩

/-- `inverse`'s start, for `u`, `v`, `x₁`, `x₂` and the modulus `m`. -/
abbrev InvS (iU iV iX₁ iX₂ iM : Nat) : KIn → State → Prop := fun I t =>
  atop I t.mem iU = 0 ∧ av I t.mem iV = av I t.mem iM ∧ av I t.mem iX₁ = 1 ∧ av I t.mem iX₂ = 0

theorem inverse_eq (iU iV iX₁ iX₂ iM iT : Nat) : inverse iU iV iX₁ iX₂ iM iT =
    .seq (.block (ws ++ (([.mov .r11 (.reg .r12)] : List Instr) ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr)))))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep iU iV iX₁ iX₂ iM iT) .ne) := by
  simp only [inverse, invInit, List.append_assoc]

theorem inverse_ct {F : KIn → State → Prop} {iU iV iX₁ iX₂ iM iT : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT)
    (hF : Stab F [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT, .hdr sMo] dvRegs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.mov .r11 (.reg .r12)] : List Instr) ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr))))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep iU iV iX₁ iX₂ iM iT) .ne)) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ InvS iU iV iX₁ iX₂ iM I t)) (inverse iU iV iX₁ iX₂ iM iT)
      (Two (KG F)) := by
  rw [inverse_eq]
  exact kg_ws ht fun I _ s h _ ⟨hf, hU0, hVM, hX1, hX2⟩ => by
    rw [← inverse_eq]
    refine WP.mono (inverse_ok h.ws.scr h.ws.rdi h.ws.hw h.ws.hS (by have := h.ws.w1; omega) h.ws.w2 h.ws.hZ hU hV
      hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT hU0 hVM hX1 hX2)
      fun t ⟨hdi, hf', k, _⟩ => ?_
    have f : KF I.B I.W [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT, .hdr sMo] s.mem t.mem :=
      KF.of_frm hf' fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨.arr iU, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
        · exact ⟨.arr iV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
        · exact ⟨.arr iX₁, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
        · exact ⟨.arr iX₂, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
        · exact ⟨.arr iT, by simp, by simp [Rc.range], by simp [Rc.range]⟩
        · exact ⟨.hdr sMo, by simp, by simp [Rc.range], by simp [Rc.range]⟩
    have k' : Keep dvRegs s t :=
      ⟨fun r hr => if e : r = .rdi then by rw [e, hdi, h.ws.rdi] else k.1 r fun hm => hr (List.mem_filter.mpr
        ⟨hm, by simp [e]⟩), k.2⟩
    refine ⟨h.step f ?_ k' (by decide), hF I s t h.hZ hf f k'⟩
    simp only [List.all_cons, List.all_nil, Rc.mut, sMo, sFn, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

end VG.Proof.RsaKeyGen.X86_64.Key
