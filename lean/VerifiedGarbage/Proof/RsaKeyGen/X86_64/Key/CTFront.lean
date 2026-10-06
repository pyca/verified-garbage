import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.CTUnits
import VerifiedGarbage.Proof.Rsa.X86_64.CvCT

/-!
# An RSA key from its primes on x86-64: constant time, the loads, the order and `p − 1`, `q − 1`

The loads take the pointer and the length from the header, which correctness
pins to the public data (`loadA_ct`, `loadE_ct`); the rest are pieces of
the key routines.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE kE kElen)

/-- `loadA`'s block and `loadBE`, from `KS`. -/
theorem loadTail_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j sPtr sLen len : Nat} {ptr : Addr}
    {bs : List Byte} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem I.B (8 * sPtr) = ptr)
    (hl : word s.mem I.B (8 * sLen) = BitVec.ofNat 64 len) (hsrc : Src s I.B I.Z ptr bs) (hbl : bs.length = len)
    (hl1 : 1 ≤ len) (hlw : len ≤ 8 * I.W) :
    WP isa (.seq (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen))] :
      List Instr))) loadBE) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧ Keep allR s t := by
  have hw := h.ws
  have hn := hw.scr.nowrap
  have sj := hw.sl hj
  have hw2 := hw.w2
  refine WP.seq (WP.mono (loadBlk_ok hw hP hL hp hl) fun t ⟨hbx, hsi, hcx, _, hm, k⟩ => ?_)
  have ht := h.same hm k (by decide)
  have hsrc' := hsrc.congrK (fun x _ => by rw [hm]) k
  refine WP.mono (loadBE_ok (w := (len + 7) / 8) ht.ws.scr hsi hcx hbx hbl hl1 (by omega) rfl (by omega)
    (fun i hi => hsrc'.rd i (by omega)) (fun i hi => hsrc'.val i (by omega))
    (fun i hi => Or.inr (by have := hsrc'.out i (by omega); omega))) fun t' ⟨_, o, k'⟩ => ?_
  rw [hm] at o
  have f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega)
  exact ⟨h.step f (all_mut_arr hj) (k.trans k') (by decide), f, (k.trans k').mono (by decide)⟩

theorem loadA_eq (j sPtr sLen : Nat) : seqs (loadA j sPtr sLen) = .seq (zeroA j)
    (.seq (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen))] : List Instr)))
      loadBE) := by
  simp only [loadA, seqs]

/-- `loadA j sPtr sLen` for the number whose pointer and length (functions of
the public inputs) are in the header slots `sPtr` and `sLen`. -/
theorem loadA_ct {F : KIn → State → Prop} {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (ptr : KQ → Addr) (len : KQ → Nat)
    (hA : ∀ I m₀ s, KS I m₀ s → KLens I → word s.mem I.B (8 * sPtr) = ptr I.pub ∧
      word s.mem I.B (8 * sLen) = BitVec.ofNat 64 (len I.pub) ∧
      (∃ bs, Src s I.B I.Z (ptr I.pub) bs ∧ bs.length = len I.pub) ∧ 1 ≤ len I.pub ∧ len I.pub ≤ 8 * I.W)
    (hF : Stab F [.arr j] allR) {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) hc₂).isSome = true)
    (ht₃ : (taint.check (Taint.ofRegs [.rdi, .rbx, .rsi, .rcx]) loadBE hc₃).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (loadA j sPtr sLen)) (Two (KG F)) := by
  rw [loadA_eq]
  refine RelCT.seq (zeroA_ct hj (hF.mono (fun _ h => h) (by decide)) ht₁) ?_
  refine pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx]
    (fun p : KP => ioVal p.q.B (off p.q.B (slot (2 * p.q.pl / 8) j)) (ptr p.q) (len p.q)) (pins_kg F) ht₂ ?_ ht₃ ?_
  · rintro ⟨q, st⟩ s ⟨I, m₀, rfl, rfl, hk, L, O, -⟩
    obtain ⟨hp, hl, -⟩ := hA I m₀ s hk L
    exact WP.mono (loadBlk_ok hk.ws hP hL hp hl) fun t ⟨hbx, hsi, hcx, hdi, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdi
      · exact hbx
      · exact hsi
      · exact hcx
  · rintro ⟨q, st⟩ s ⟨I, m₀, rfl, rfl, hk, L, O, hf⟩
    obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, hl1, hlw⟩ := hA I m₀ s hk L
    exact WP.mono (loadTail_k hk hj hP hL hp hl hsrc hbl hl1 hlw) fun t ⟨ht, f, k⟩ =>
      ⟨I, m₀, rfl, rfl, ht, L, O, hF I s t hk.hZ hf f k⟩

theorem loadAP_ct : RelCT isa (Two (KG NF)) (seqs (loadA aPa kPp kPl)) (Two (KG NF)) :=
  loadA_ct (by decide) (by decide) (by decide) KQ.pP KQ.pl
    (fun I _ _ h L => ⟨h.args.pp, h.args.pl, ⟨_, h.p, L.pbl⟩, show 1 ≤ I.pl by have := L.pl1; omega,
      show I.pl ≤ 8 * I.W by rw [L.W]; have := L.pl8; omega⟩)
    (stab_nf _ _) (by taint_decide) (by taint_decide) (by taint_decide)

theorem loadAQ_ct : RelCT isa (Two (KG NF)) (seqs (loadA aQa kQp kPl)) (Two (KG NF)) :=
  loadA_ct (by decide) (by decide) (by decide) KQ.pQ KQ.pl
    (fun I _ _ h L => ⟨h.args.qp, h.args.pl, ⟨_, h.q, L.qbl⟩, show 1 ≤ I.pl by have := L.pl1; omega,
      show I.pl ≤ 8 * I.W by rw [L.W]; have := L.pl8; omega⟩)
    (stab_nf _ _) (by taint_decide) (by taint_decide) (by taint_decide)

/-- `e`'s pointer and length. -/
def eVal (pE : Addr) (el : Nat) : Reg → BitVec 64
  | .rsi => pE
  | .rcx => BitVec.ofNat 64 el
  | _ => 0

theorem loadE_eq : seqs (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa))) =
    .seq (.block [.mov .rsi (.mem (hdr kE)), .mov .rcx (.mem (hdr kElen)), .mov32 .rbx (.imm 0)])
      (.seq (.loop (.block [.shift .ror .rbx 56, .movzx8 .rax (at0 .rsi), .alu .add .rbx (.reg .rax),
        .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne) (.block [.store (hdr kEv) .rbx])) := rfl

/-- `e`'s load and its store into `kEv`. -/
theorem loadE_ct : RelCT isa (Two (KG NF)) (seqs (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa)))) (Two (KG EvOK)) := by
  rw [loadE_eq]
  refine pin_ct [.rdi] [.rdi, .rsi, .rcx]
    (fun p : KP => fun r => if r = .rdi then p.q.B else eVal p.q.pE p.q.el r) (pins_kg NF) (by taint_decide) ?_
    (by taint_decide) ?_
  · rintro ⟨q, st⟩ s ⟨I, m₀, rfl, rfl, hk, L, O, -⟩
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi =>
      hk.ws.scr.ld (by have := hk.ws.h256; omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = I.pE ∧
        t.gpr .rcx = BitVec.ofNat 64 I.el) (by
      xrun [State.ea, hdr, hk.ws.rdi, hdrOff, hl kE (by decide), hl kElen (by decide), hk.args.e, hk.args.el]) rfl)
      fun t ⟨⟨hsi, hcx⟩, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (k.gpr (by decide)).trans hk.ws.rdi
    · exact hsi
    · exact hcx
  · rintro ⟨q, st⟩ s ⟨I, m₀, rfl, rfl, hk, L, O, -⟩
    obtain ⟨hg, hZ8⟩ := hk.ws.good
    have e₁ := loadE_ok hg hZ8 hk.args.e (by rw [hk.args.el, L.ebl]) (by rw [L.ebl]; exact L.el1)
      (by rw [L.ebl]; exact L.el8) hk.e
    rw [show seqs loadE = .seq (.block [.mov .rsi (.mem (hdr kE)), .mov .rcx (.mem (hdr kElen)),
      .mov32 .rbx (.imm 0)]) (.loop (.block [.shift .ror .rbx 56, .movzx8 .rax (at0 .rsi), .alu .add .rbx (.reg .rax),
        .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne) from rfl] at e₁
    refine WP.assoc (WP.seq (WP.mono e₁ fun s₃ ⟨hbx, m₃, k₃⟩ => ?_))
    have h₃ := hk.same m₃ k₃ (by decide)
    have hst := h₃.ws.scr.st (d := 8 * kEv) (by have := h₃.ws.h256; unfold kEv sFn; omega)
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₃.mem.writeW (off I.B (8 * kEv))
      (BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb))) (by
        have hbx' : s₃.gpr .rbx = BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb) := by
          rw [← hbx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        xrun [State.ea, hdr, h₃.ws.rdi, hdrOff, hst, hbx']) rfl) fun t ⟨hm, k₄⟩ => ?_
    obtain ⟨ht, -, hw⟩ := h₃.hdrW (i := kEv) (by unfold kEv sFn; omega) hm k₄ (by decide)
    exact ⟨I, m₀, rfl, rfl, ht, L, O, hw⟩

theorem order_eq : seqs order = .seq (.block (ws ++ (base aPa .rbx ++ (base aQa .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr)))))
    (.seq (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp])
      (.seq (.block [.mov .r15 (.reg .rbp)]) (wordLoop 0 cswapBody))) := by
  simp only [order, ltA, seqs, List.append_assoc, List.cons_append, List.nil_append]

theorem order_ct : RelCT isa (Two (KG EvOK)) (seqs order) (Two (KG EvOK)) := by
  rw [order_eq]
  exact kg_ws (by taint_decide) fun I _ s h _ hf => by
    rw [← order_eq]
    exact WP.mono (order_k h) fun _ ⟨ht, f, _, _⟩ => ⟨ht, (f.word (by decide) (by decide) (by decide)).trans hf⟩

/-- `rbp`'s mask, negated, into `r15`. -/
theorem negR15_ok {s : State} {c : Bool} (h : s.gpr .rbp = mask c) :
    WP isa (.block [.mov .r15 (.reg .rbp), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]) s fun t =>
      t.mem = s.mem ∧ Keep [.r15] s t ∧ t.gpr .r15 = mask (!c) := by
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask (!c) ∧ t.mem = s.mem)
    (by xrun [h, sxM1, maskNot]) rfl) fun t ⟨⟨h15, hm⟩, k⟩ => ⟨hm, k, h15⟩

theorem decTo_eq (o j : Nat) : decTo o j = [zeroA o, copyA o j] ++ (constA 0 ++ (eqMask j aC ++
    (([.block [.mov .r15 (.reg .rbp), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa)) ++ (constA 1 ++ subC o o)))) := by
  simp only [decTo, subC, List.append_assoc]

/-- `decTo o j`, for facts that its changes keep. -/
theorem decTo_ct {F : KIn → State → Prop} {o j : Nat} (ho : o < 16) (hj : j < 16) (hoj : o ≠ j) (hoC : o ≠ aC)
    (hF : Stab F [.arr o, .arr aC] allR)
    {h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base o .r8)) zeroAccLoop) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rsi ++ base o .rbx))
      Impl.Rsa.X86_64.copyWords) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base aC .r8)) zeroAccLoop) h₃).isSome = true)
    (t₄ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.block (base aC .rbx ++ ([.mov32 .rax (.imm 0), .store (at0 .rbx) .rax] : List Instr))) h₄).isSome = true)
    (t₅ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rbx ++ (base aC .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr)))) (.seq (wordLoop 0 xorBody) (.block isZero))) h₅).isSome = true)
    (t₆ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r15 (.reg .rbp),
      .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]) h₆).isSome = true)
    (t₇ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.block (base aC .rbx ++ ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr))) h₇).isSome = true)
    (t₈ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base o .r8 ++ (base aC .r10 ++
      (base o .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr))))) (wordLoop 0 subMBody)) h₈).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (decTo o j)) (Two (KG F)) := by
  rw [decTo_eq]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA o, copyA o j]) _ from
    RelCT.seq (zeroA_ct ho (hF.mono (by simp) (by decide)) t₁) (copyA_ct ho hj hoj (hF.mono (by simp) (by decide)) t₂)) ?_
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 0 (hF.mono (by simp) (by decide)) t₃ t₄) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := fun I t => F I t ∧ RbpM I t) hj
    (by decide) (fun I s t hZ hf hm k hbp => ⟨hF I s t hZ hf (by rw [hm]; exact KF.refl _ _ _ |>.mono (by simp))
      (k.mono (by decide)), _, hbp⟩) t₅) ?_
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [.block [.mov .r15 (.reg .rbp),
      .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]]) _ from
    kg_regs (G := fun I t => F I t ∧ R15M I t) (by decide) t₆ fun I s hZ ⟨hf, c, hbp⟩ => WP.mono (negR15_ok hbp) fun t ⟨hm, k, h15⟩ =>
      ⟨hm, k, hF I s t hZ hf (by rw [hm]; exact KF.refl _ _ _ |>.mono (by simp)) (k.mono (by decide)), _, h15⟩) ?_
  refine rs_app (by simp [constA]) (by simp [subC]) (constA_ct 1
    (stab_and (hF.mono (by simp) (by decide)) (stab_r15 (by decide))) t₃ t₇) ?_
  exact subC_ct ho ho hoC hoC (.inl rfl) (hF.mono (by simp) (by decide)) t₈

theorem decP_ct : RelCT isa (Two (KG EvOK)) (seqs (decTo aPm aPa)) (Two (KG EvOK)) :=
  decTo_ct (by decide) (by decide) (by decide) (by decide) (stab_ev _ (by decide) (by decide))
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)

theorem decQ_ct : RelCT isa (Two (KG EvOK)) (seqs (decTo aQm aQa)) (Two (KG EvOK)) :=
  decTo_ct (by decide) (by decide) (by decide) (by decide) (stab_ev _ (by decide) (by decide))
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)

end VG.Proof.RsaKeyGen.X86_64.Key
