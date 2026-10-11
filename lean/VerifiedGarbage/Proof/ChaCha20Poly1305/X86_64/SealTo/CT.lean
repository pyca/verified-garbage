import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.SealTo.Correct

/-!
# ChaCha20-Poly1305 encryption with part of the data read from elsewhere, x86-64: constant time

`sealTo` leaks the same in two runs whose entry states agree on what
`seal`'s do and on `src` and `src_len` (`PubTo`): as `seal_rel`, but for
`oop`, whose branches and loop are on `src_len`, which the code loads from
the stack, where the taint analysis does not track it. So `oop` is analysed
in pieces (`oop_rel`): each piece by the taint analysis from the registers
public at its start, which agree in both runs by what correctness proves of
each run (`RelCT.wp`), and each branch's condition agrees in both runs the
same way.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `sealTo`'s public data: `seal`'s, `src` and `src_len`. -/
def PubTo (s₁ s₂ : State) : Prop :=
  pubX86_64 s₁ s₂ ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3

/-- Only the registers `rs` public, nothing known of the regions. -/
def τR (rs : List Reg) : X86_64.Taint.T := { regs := .ofList rs, flags := false }

theorem agreeR {rs : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    X86_64.Taint.Agree (τR rs) s₁ s₂ :=
  ⟨⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩, fun h => absurd rfl h,
    ⟨fun h => absurd rfl h, fun _ h => by simp [τR] at h⟩, ⟨fun h => absurd rfl h, fun _ h => by simp [τR] at h⟩,
    fun _ h => by simp [τR] at h, fun _ h => by simp [τR] at h, X86_64.Taint.noLo, X86_64.Taint.noXr⟩

/-- What `oop` needs of each run (`oop_ok`'s hypotheses). -/
structure OopPre (s₀ s : State) : Prop where
  big : 960 < L s₀
  args : XArgsM s₀ (mm s₀) s
  rd : s.rd = s₀.rd
  r15 : s.gpr .r15 = cx s₀
  s2 : s.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2
  s3 : s.mem.readW (stackArgAddr s₀ 3) 64 = stackArg s₀ 3
  st : stateAt s.mem (off (cx s₀) 64) =
    (Spec.ChaCha20.initState (K s₀) 0 (N s₀)).set 12 (BitVec.ofNat 32 (mm s₀ / 64 + 1))

section
variable {s₀ s₀' : State} (hT : ToPre s₀) (hT' : ToPre s₀') (hq : PubTo s₀ s₀')

include hq in
theorem PubTo.mmPP : L s₀ = L s₀' ∧ SL s₀ = SL s₀' ∧ mm s₀ = mm s₀' ∧ PP s₀ = PP s₀' := by
  obtain ⟨⟨-, -, -, -, -, p6, -, -, -⟩, -, p3⟩ := hq
  have e1 : L s₀ = L s₀' := by simp only [L, p6]
  have e2 : SL s₀ = SL s₀' := by simp only [SL, p3]
  refine ⟨e1, e2, by simp only [mm, e1], ?_⟩
  simp only [PP, mm, e1, e2]

end

/-! ## The pieces of `oop`, in each run -/

/-- After the first block. -/
structure P1 (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = BitVec.ofNat 64 (mm s₀)
  rax : s.gpr .rax = BitVec.ofNat 64 (SL s₀)
  cf : s.cf = some (decide (SL s₀ < mm s₀))
  r15 : s.gpr .r15 = cx s₀
  r14 : s.gpr .r14 = dp s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  s2 : s.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2
  big : 960 < L s₀

theorem p1_ok {s₀ : State} (hT : ToPre s₀) {s : State} (h : OopPre s₀ s) :
    WP isa (.block [.mov .rbx (.reg .r13), .alu .sub .rbx (.reg .rdx), .mov .rax (.mem (at_ .rsp 32)),
      .alu .cmp .rax (.reg .rbx)]) s (P1 s₀) :=
  WP.mono (oop1_ok hT h.args h.rd h.s3) fun _ ⟨rbx, rax, g, rd, wr, m, cf⟩ =>
    ⟨rbx, rax, cf, by rw [g _ (by decide) (by decide)]; exact h.r15,
      by rw [g _ (by decide) (by decide)]; exact h.args.r14, by rw [g _ (by decide) (by decide)]; exact h.args.rsp,
      by rw [rd]; exact h.rd, by rw [wr]; exact h.args.wr, by rw [m]; exact h.s2, h.big⟩

/-- After the second block, with `src_len ≥ m`. -/
structure P2 (s₀ s : State) : Prop where
  rax : s.gpr .rax = BitVec.ofNat 64 (PP s₀)
  zf : s.zf = some (decide (PP s₀ = 0))
  rbx : s.gpr .rbx = BitVec.ofNat 64 (mm s₀)
  r15 : s.gpr .r15 = cx s₀
  r14 : s.gpr .r14 = dp s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  s2 : s.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2

theorem p2_ok {s₀ : State} {s : State} (h : P1 s₀ s) (hc : ¬ SL s₀ < mm s₀) :
    WP isa (.block [.alu .sub .rax (.reg .rbx), .shift .shr .rax 10, .shift .shl .rax 10,
      .alu .test .rax (.reg .rax)]) s (P2 s₀) :=
  WP.mono (oop2_ok (a := SL s₀) (by omega) (stackArg s₀ 3).isLt h.rax h.rbx) fun _ ⟨rax, g, rd, wr, m, zf⟩ => by
    rw [PP_eq h.big (by omega)] at rax zf
    exact ⟨rax, zf, by rw [g _ (by decide)]; exact h.rbx, by rw [g _ (by decide)]; exact h.r15,
      by rw [g _ (by decide)]; exact h.r14, by rw [g _ (by decide)]; exact h.rsp, by rw [rd]; exact h.rd,
      by rw [wr]; exact h.wr, by rw [m]; exact h.s2⟩

/-- After the loop's arguments. -/
structure P3 (s₀ s : State) : Prop where
  rdi : s.gpr .rdi = off (cx s₀) 608
  rsi : s.gpr .rsi = sp s₀ + BitVec.ofNat 64 (mm s₀)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (PP s₀)
  rcx : s.gpr .rcx = dp s₀ + BitVec.ofNat 64 (mm s₀)
  r9 : s.gpr .r9 = off (cx s₀) 128
  rbx : s.gpr .rbx = BitVec.ofNat 64 (mm s₀ + PP s₀)
  r15 : s.gpr .r15 = cx s₀
  r14 : s.gpr .r14 = dp s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem p3_ok {s₀ : State} (hT : ToPre s₀) {s : State} (h : P2 s₀ s) :
    WP isa (.block (([.vmovdqu32Load .xmm0 (at_ .r15 64), .vmovdqu32Store (at_ .r15 608) .xmm0] : List Instr) ++
      (([.mov .rsi (.mem (at_ .rsp 24)), .alu .add .rsi (.reg .rbx), .mov .rcx (.reg .r14),
        .alu .add .rcx (.reg .rbx), .mov .rdx (.reg .rax)] : List Instr) ++ ptr .rdi .r15 608 ++
        ptr .r9 .r15 128 ++ ([.alu .add .rbx (.reg .rax)] : List Instr)))) s (P3 s₀) := by
  have hp := hT.hp
  have i₂ : InRegions (s.rd ++ s.wr) (stackArgAddr s₀ 2) 8 :=
    ⟨arg2R s₀, by rw [h.rd]; simp [hT.g2], by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  have i₆₄ : InRegions (s.rd ++ s.wr) (off (cx s₀) 64) 64 := by
    rw [h.rd, h.wr]; exact hp.in_ctx' (by lit_omega)
  have o₆₀₈ : InRegions s.wr (off (cx s₀) 608) 64 := by rw [h.wr]; exact hp.in_ctx (by lit_omega)
  have F : ∀ (m : BitVec 512), Frame [sub s₀ 608 64] s.mem (s.mem.writeW (off (cx s₀) 608) m) := fun m =>
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  refine WP.block_append (WP.mono (zcopy_ok h.r15 i₆₄ o₆₀₈) fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ =>
    WP.mono (oopG_ok (s₀ := s₀) (m := mm s₀) (P := PP s₀) (by rw [g₄]; exact h.r15) (by rw [g₄]; exact h.r14)
      (by rw [g₄]; exact h.rbx) (by rw [g₄]; exact h.rax) (by rw [g₄]; exact h.rsp)
      (by
        rw [m₄, (F _).readW (r := arg2R s₀) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
          (by simpa using hT.g_c.sub_right (sub_ctx s₀ (k := 608) (n := 64) (by lit_omega))) (by decide), h.s2])
      (by rw [rd₄, wr₄]; exact i₂)) fun _ ⟨rsi, rcx, rdx, rdi, r9, rbx, g, _, _, _⟩ => ?_)
  have k : ∀ q : Reg, q ≠ .rsi → q ≠ .rcx → q ≠ .rdx → q ≠ .rdi → q ≠ .r9 → q ≠ .rbx → _ := fun q a b c d e f =>
    (g q a b c d e f).trans (congrFun g₄ q)
  exact ⟨rdi, rsi, rdx, rcx, r9, rbx,
    (k .r15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r15,
    (k .r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r14,
    (k .rsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.rsp⟩

/-! ## The taint checks of the pieces -/

theorem oop1_taint : ∃ h, (taintS.check (τR [.rsp, .r13, .rdx]) (.block [.mov .rbx (.reg .r13),
    .alu .sub .rbx (.reg .rdx), .mov .rax (.mem (at_ .rsp 32)), .alu .cmp .rax (.reg .rbx)]) h).isSome = true := by
  taint_decide_sum []

theorem oop2_taint : ∃ h, (taintS.check (τR []) (.block [.alu .sub .rax (.reg .rbx), .shift .shr .rax 10,
    .shift .shl .rax 10, .alu .test .rax (.reg .rax)]) h).isSome = true := by
  taint_decide_sum []

theorem skip_taint : ∃ h, (taintS.check (τR []) (.block []) h).isSome = true := by
  taint_decide_sum []

theorem oop3_taint : ∃ h, (taintS.check (τR [.r15, .rsp])
    (.block (([.vmovdqu32Load .xmm0 (at_ .r15 64), .vmovdqu32Store (at_ .r15 608) .xmm0] : List Instr) ++
      (([.mov .rsi (.mem (at_ .rsp 24)), .alu .add .rsi (.reg .rbx), .mov .rcx (.reg .r14),
        .alu .add .rcx (.reg .rbx), .mov .rdx (.reg .rax)] : List Instr) ++ ptr .rdi .r15 608 ++
        ptr .r9 .r15 128 ++ ([.alu .add .rbx (.reg .rax)] : List Instr)))) h).isSome = true := by
  taint_decide_sum []

theorem oop4_taint : ∃ h, (taintS.check (τR [.rdi, .rsi, .rdx, .rcx, .r9, .rsp, .rbx, .r14, .r15])
    (.seq xorToLoop (.block restArgs)) h).isSome = true := by
  taint_decide_sum []

/-! ## `oop` in two runs -/

section
variable {s₀ s₀' : State} (hT : ToPre s₀) (hT' : ToPre s₀') (hq : PubTo s₀ s₀')
include hT hT' hq

theorem oop_rel :
    RelCT isa (fun s₁ s₂ => OopPre s₀ s₁ ∧ OopPre s₀' s₂) oop
      fun s₁ s₂ => XArgsM s₀ (mm s₀ + PP s₀) s₁ ∧ XArgsM s₀' (mm s₀' + PP s₀') s₂ := by
  obtain ⟨eL, eSL, emm, ePP⟩ := hq.mmPP
  obtain ⟨⟨-, -, -, -, p5, p6, p7, -, p9⟩, a2, -⟩ := hq
  obtain ⟨_, t1⟩ := oop1_taint
  obtain ⟨_, t2⟩ := oop2_taint
  obtain ⟨_, t0⟩ := skip_taint
  obtain ⟨_, t3⟩ := oop3_taint
  obtain ⟨_, t4⟩ := oop4_taint
  have skip : ∀ {P : State → State → Prop}, RelCT isa P (.block []) fun _ _ => True := fun {P} =>
    RelCT.taint (A := taintS) (P := P) (τR []) (fun _ _ _ => agreeR (by simp)) t0
  have r1 := (RelCT.taint (A := taintS) (P := fun s₁ s₂ => OopPre s₀ s₁ ∧ OopPre s₀' s₂) (τR [.rsp, .r13, .rdx])
    (fun s₁ s₂ h => agreeR (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [h.1.args.rsp, h.2.args.rsp, p7], by rw [h.1.args.r13, h.2.args.r13, p6],
        by rw [h.1.args.rdx, h.2.args.rdx, eL, emm]⟩)) t1).wp
    (F₁ := P1 s₀) (F₂ := P1 s₀') fun s₁ s₂ h => ⟨p1_ok hT h.1, p1_ok hT' h.2⟩
  have hc1 : ∀ s₁ s₂, (True ∧ P1 s₀ s₁ ∧ P1 s₀' s₂) → isa.eval .b s₁ = isa.eval .b s₂ := fun s₁ s₂ h => by
    simp [eval, h.2.1.cf, h.2.2.cf, eSL, emm]
  have r2 := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (True ∧ P1 s₀ s₁ ∧ P1 s₀' s₂) ∧ isa.eval .b s₁ = some false) (τR [])
    (fun _ _ _ => agreeR (by simp)) t2).wp (F₁ := P2 s₀) (F₂ := P2 s₀') fun s₁ s₂ h => by
      have e₁ := h.2
      have e₂ := (hc1 _ _ h.1).symm.trans h.2
      simp only [eval, h.1.2.1.cf, h.1.2.2.cf, Option.some.injEq, decide_eq_false_iff_not] at e₁ e₂
      exact ⟨p2_ok h.1.2.1 e₁, p2_ok h.1.2.2 e₂⟩
  have hc2 : ∀ s₁ s₂, (True ∧ P2 s₀ s₁ ∧ P2 s₀' s₂) → isa.eval .e s₁ = isa.eval .e s₂ := fun s₁ s₂ h => by
    simp [eval, h.2.1.zf, h.2.2.zf, ePP]
  have r3 := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (True ∧ P2 s₀ s₁ ∧ P2 s₀' s₂) ∧ isa.eval .e s₁ = some false) (τR [.r15, .rsp])
    (fun s₁ s₂ h => agreeR (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [h.1.2.1.r15, h.1.2.2.r15, cx, cx, p9], by rw [h.1.2.1.rsp, h.1.2.2.rsp, p7]⟩)) t3).wp
    (F₁ := P3 s₀) (F₂ := P3 s₀') fun s₁ s₂ h => ⟨p3_ok hT h.1.2.1, p3_ok hT' h.1.2.2⟩
  have r4 := RelCT.taint (A := taintS) (P := fun s₁ s₂ => True ∧ P3 s₀ s₁ ∧ P3 s₀' s₂)
    (τR [.rdi, .rsi, .rdx, .rcx, .r9, .rsp, .rbx, .r14, .r15])
    (fun s₁ s₂ h => agreeR (by
      have e := h.2.1; have e' := h.2.2
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [e.rdi, e'.rdi, cx, cx, p9], by rw [e.rsi, e'.rsi, sp, sp, a2, emm],
        by rw [e.rdx, e'.rdx, ePP], by rw [e.rcx, e'.rcx, dp, dp, p5, emm], by rw [e.r9, e'.r9, cx, cx, p9],
        by rw [e.rsp, e'.rsp, p7], by rw [e.rbx, e'.rbx, emm, ePP], by rw [e.r14, e'.r14, dp, dp, p5],
        by rw [e.r15, e'.r15, cx, cx, p9]⟩)) t4
  have inner : RelCT isa (fun s₁ s₂ => (True ∧ P1 s₀ s₁ ∧ P1 s₀' s₂) ∧ isa.eval .b s₁ = some false)
      (.seq (.block [.alu .sub .rax (.reg .rbx), .shift .shr .rax 10, .shift .shl .rax 10,
          .alu .test .rax (.reg .rax)])
        (.ite .e (.block [])
          (.seq (.block (([.vmovdqu32Load .xmm0 (at_ .r15 64), .vmovdqu32Store (at_ .r15 608) .xmm0] : List Instr) ++
            (([.mov .rsi (.mem (at_ .rsp 24)), .alu .add .rsi (.reg .rbx), .mov .rcx (.reg .r14),
              .alu .add .rcx (.reg .rbx), .mov .rdx (.reg .rax)] : List Instr) ++ ptr .rdi .r15 608 ++
              ptr .r9 .r15 128 ++ ([.alu .add .rbx (.reg .rax)] : List Instr))))
            (.seq xorToLoop (.block restArgs))))) fun _ _ => True :=
    r2.seq (RelCT.ite hc2 skip (r3.seq r4))
  rw [oop_eq]
  exact (r1.seq (RelCT.ite hc1 skip inner)).wp
    (F₁ := XArgsM s₀ (mm s₀ + PP s₀)) (F₂ := XArgsM s₀' (mm s₀' + PP s₀')) (fun s₁ s₂ h =>
      ⟨WP.mono (oop_ok hT h.1.big h.1.args h.1.rd h.1.r15 h.1.s2 h.1.s3 h.1.st) fun _ o => o.args,
       WP.mono (oop_ok hT' h.2.big h.2.args h.2.rd h.2.r15 h.2.s2 h.2.s3 h.2.st) fun _ o => o.args⟩)
    |>.mono (fun _ _ h => h) fun _ _ h => h.2

end

end VG.Proof.ChaCha20Poly1305.X86_64
