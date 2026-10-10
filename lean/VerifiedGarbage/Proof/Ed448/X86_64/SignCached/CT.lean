import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.HashCT
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Correct
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.CT

/-!
# Ed448 signing with a cached public key on x86-64: constant time

Two runs from states that satisfy the contract and agree on its public data,
the pointers and the lengths, leak the same, whatever the private key, the
public key, the context and the message: the moves, the frame, the pruning
and the clearing address only the stack; the hashes leak only the layout
(`seedHash_tr`, `nonceHash_tr`, `chalHash_tr`); and the calls of
`vg_ed448_scalar_reduce`, `vg_ed448_scalar_base` and
`vg_ed448_scalar_mul_add` leak only their pointers (`red_tr`, `base_tr`,
`mulAdd_tr`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk Arg callA hdr fH fScr)
open VG.Proof.Ed448.X86_64.Verify (Moved SpOnly spOnly_nomem block_rsp_tr ghost_step Ghost argsIn3 argsIn5 gpr_ce
  rsp_ce hdr_spOnly)
open VG.Proof.MlKem.X86_64 (Keep)

section
variable {I : Lay → Mem → Mem → Prop}

/-! ## The calls -/

theorem red_tr {Φ : Lay → Mem → State → Prop} {d : Nat} (h₂ : d + 57 ≤ 448) (h₃ : d < 2 ^ 31) :
    RelCT isa (Two I Φ) (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce [.sp d, .sp fH, .slot fScr])
      fun _ _ => True := by
  have regs : ∀ (L : Lay) g mx m₀ (t t1 : State), Ctx L g mx m₀ t → Moved [.sp d, .sp fH, .slot fScr] t t1 →
      t1.gpr .rdi = L.SP + BitVec.ofNat 64 d ∧ t1.gpr .rsi = L.H ∧ t1.gpr .rdx = L.scr ∧ t1.gpr .rsp = L.SP :=
    fun L g mx m₀ t t1 hc hm => by
      obtain ⟨e1, e2, e3⟩ := argsIn3 hm.1.1
      rw [hc.sp] at e1 e2
      rw [hc.slot, hc.pScr] at e3
      exact ⟨e1, e2, e3, (hm.2.gpr (by decide)).trans hc.rsp⟩
  refine call_tr (by simp [Arg.ok, fScr, fH]; omega) Proof.Ed448.X86_64.scalarReduce_ok
    Proof.Ed448.X86_64.scalarReduce_ct
    (fun L => [⟨L.H, 114⟩]) (fun L => [⟨L.SP + BitVec.ofNat 64 d, 57⟩, L.SCR])
    (fun L g mx m₀ t t1 hL hc _ hm => ?_)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 _ _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · obtain ⟨g1, g2, g3, g4⟩ := regs L g mx m₀ t t1 hc hm
    simp only [Proof.Ed448.X86_64.scalarReduceLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), rsp_ce, g1, g2, g3, g4,
      Verify.sp_sub8, State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, fr_x hL (d := 16) (by omega), ret_fr h₂, ret_x hL, fr_x hL h₂, hL.nScr⟩
  · obtain ⟨x1, x2, x3, x4⟩ := regs L g₁ mx₁ m₁ a a1 c₁ f₁
    obtain ⟨y1, y2, y3, y4⟩ := regs L g₂ mx₂ m₂ b b1 c₂ f₂
    simp only [Proof.Ed448.X86_64.scalarReduceLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), rsp_ce,
      x1, x2, x3, x4, y1, y2, y3, y4, and_self]
  · refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact in_fr (d := 16) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨L.FR, by simp, Verify.within_off _ h₂⟩, ⟨L.SCR, by simp [hL.wr], Verify.within_self _⟩]

theorem base_tr (hb : BaseOk) (hct : BaseCT) {Φ : Lay → Mem → State → Prop} :
    RelCT isa (Two I Φ) (callA "vg_ed448_scalar_base" Impl.Ed448.X86_64.scalarBase [.slot fOut, .sp fR, .slot fScr])
      fun _ _ => True := by
  have regs : ∀ (L : Lay) g mx m₀ (t t1 : State), Ctx L g mx m₀ t → Moved [.slot fOut, .sp fR, .slot fScr] t t1 →
      t1.gpr .rdi = L.out ∧ t1.gpr .rsi = L.R ∧ t1.gpr .rdx = L.scr ∧ t1.gpr .rsp = L.SP :=
    fun L g mx m₀ t t1 hc hm => by
      obtain ⟨e1, e2, e3⟩ := argsIn3 hm.1.1
      rw [hc.slot, hc.pOut] at e1
      rw [hc.sp] at e2
      rw [hc.slot, hc.pScr] at e3
      exact ⟨e1, e2, e3, (hm.2.gpr (by decide)).trans hc.rsp⟩
  refine call_tr (by decide) hb hct (fun L => [⟨L.R, 57⟩]) (fun L => [⟨L.out, 57⟩, L.SCR])
    (fun L g mx m₀ t t1 hL hc _ hm => ?_)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 _ _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · obtain ⟨g1, g2, g3, g4⟩ := regs L g mx m₀ t t1 hc hm
    exact base_cpre hL ((gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp)).trans g1)
      ((gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp)).trans g2) ((gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp)).trans g3)
      (by rw [rsp_ce, g4, Verify.sp_sub8]) rfl rfl
  · obtain ⟨x1, x2, x3, x4⟩ := regs L g₁ mx₁ m₁ a a1 c₁ f₁
    obtain ⟨y1, y2, y3, y4⟩ := regs L g₂ mx₂ m₂ b b1 c₂ f₂
    simp only [Contract.clear, Proof.Ed448.X86_64.scalarBaseLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), rsp_ce,
      x1, x2, x3, x4, y1, y2, y3, y4, and_self]
  · refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact in_fr (d := 384) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨L.OUT, by simp [hL.wr], Verify.within_base _ (by omega)⟩,
        ⟨L.SCR, by simp [hL.wr], Verify.within_self _⟩]

theorem mulAdd_tr {Φ : Lay → Mem → State → Prop} :
    RelCT isa (Two I Φ) (callA "vg_ed448_scalar_mul_add" Impl.Ed448.X86_64.scalarMulAdd
      [.slotOff fOut 57, .sp fR, .sp fK, .sp fS, .slot fScr]) fun _ _ => True := by
  have regs : ∀ (L : Lay) g mx m₀ (t t1 : State), Ctx L g mx m₀ t →
      Moved [.slotOff fOut 57, .sp fR, .sp fK, .sp fS, .slot fScr] t t1 →
      t1.gpr .rdi = L.out + BitVec.ofNat 64 57 ∧ t1.gpr .rsi = L.R ∧ t1.gpr .rdx = L.K ∧ t1.gpr .rcx = L.S ∧
        t1.gpr .r8 = L.scr ∧ t1.gpr .rsp = L.SP :=
    fun L g mx m₀ t t1 hc hm => by
      obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hm.1.1
      simp only [Arg.val, hc.rsp, hc.pOut, hc.pScr] at e1 e5
      rw [hc.sp] at e2 e3 e4
      exact ⟨e1, e2, e3, e4, e5, (hm.2.gpr (by decide)).trans hc.rsp⟩
  refine call_tr (by decide) Proof.Ed448.X86_64.scalarMulAdd_ok Proof.Ed448.X86_64.scalarMulAdd_ct
    (fun L => [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩]) (fun L => [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR])
    (fun L g mx m₀ t t1 hL hc _ hm => ?_)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 _ _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · obtain ⟨g1, g2, g3, g4, g5, g6⟩ := regs L g mx m₀ t t1 hc hm
    simp only [Proof.Ed448.X86_64.scalarMulAddLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), rsp_ce,
      g1, g2, g3, g4, g5, g6, Verify.sp_sub8, State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, fr_x hL (d := 384) (by omega), fr_x hL (d := 256) (by omega),
      fr_x hL (d := 320) (by omega), ret_r hL (hL.kOut.sub_right o2_sub), ret_x hL,
      (hL.xOut.sub_right o2_sub).symm, hL.nScr⟩
  · obtain ⟨x1, x2, x3, x4, x5, x6⟩ := regs L g₁ mx₁ m₁ a a1 c₁ f₁
    obtain ⟨y1, y2, y3, y4, y5, y6⟩ := regs L g₂ mx₂ m₂ b b1 c₂ f₂
    simp only [Proof.Ed448.X86_64.scalarMulAddLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), rsp_ce,
      x1, x2, x3, x4, x5, x6, y1, y2, y3, y4, y5, y6, and_self]
  · refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [in_fr (d := 384) (by omega), in_fr (d := 256) (by omega), in_fr (d := 320) (by omega)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨L.OUT, by simp [hL.wr], Verify.within_off _ (by omega)⟩,
        ⟨L.SCR, by simp [hL.wr], Verify.within_self _⟩]

/-! ## The blocks -/

theorem stk_spOnly {d : Nat} (r : Reg) : SpOnly (.store (stk d) r) :=
  ⟨fun s₁ s₂ h => by simp [addrs, State.ea, stk, h], rfl⟩

theorem prune_spOnly : ∀ i ∈ prune, SpOnly i := by
  intro i hi
  simp only [prune, loads, mods, stores, sRegs, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first
    | exact stk_spOnly _
    | exact spOnly_nomem (fun _ => rfl) rfl
    | exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩

theorem wipe_spOnly : ∀ i ∈ wipe, SpOnly i := by
  intro i hi
  simp only [wipe, List.mem_cons, List.mem_map, List.mem_range] at hi
  rcases hi with rfl | ⟨k, -, rfl⟩
  · exact spOnly_nomem (fun _ => rfl) rfl
  · exact stk_spOnly _

/-! ## The frame's body -/

abbrev T (I : Lay → Mem → Mem → Prop) : State → State → Prop := Two I fun _ _ _ => True

theorem blk_two {is : List Instr} (h : ∀ i ∈ is, SpOnly i)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → WP isa (.block is) t (Ctx L g mx m₀)) :
    RelCT isa (T I) (.block is) (T I) :=
  two_wp (block_rsp_tr h fun _ _ h => h.rsp) fun L g mx m₀ t hL hc _ =>
    WP.mono (hw L g mx m₀ t hL hc) fun _ h => ⟨h, trivial⟩

theorem two_true {c : Prog isa} (hct : RelCT isa (T I) c fun _ _ => True)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → WP isa c t (Ctx L g mx m₀)) :
    RelCT isa (T I) c (T I) :=
  two_wp hct fun L g mx m₀ t hL hc _ => WP.mono (hw L g mx m₀ t hL hc) fun _ h => ⟨h, trivial⟩

/-- The frame's body, after the header. -/
theorem rest_tr (hb : BaseOk) (hct : BaseCT) :
    RelCT isa (T I) (.seq seedHash <| .seq (.block prune) <| .seq nonceHash <|
      .seq (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce [.sp fR, .sp fH, .slot fScr]) <|
      .seq (callA "vg_ed448_scalar_base" Impl.Ed448.X86_64.scalarBase [.slot fOut, .sp fR, .slot fScr]) <|
      .seq chalHash <|
      .seq (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce [.sp fK, .sp fH, .slot fScr]) <|
      .seq (callA "vg_ed448_scalar_mul_add" Impl.Ed448.X86_64.scalarMulAdd
        [.slotOff fOut 57, .sp fR, .sp fK, .sp fS, .slot fScr]) (.block wipe)) fun _ _ => True := by
  have a := two_true (I := I) seedHash_tr fun _ _ _ _ _ hL hc => WP.mono (seedHash_ok hL hc) fun _ h => h.1
  have b := blk_two (I := I) prune_spOnly fun _ _ _ _ _ hL hc => WP.mono (prune_ok hL hc) fun _ h => h.1
  have c := two_true (I := I) nonceHash_tr fun _ _ _ _ _ hL hc => WP.mono (nonceHash_ok hL hc) fun _ h => h.1
  have d := two_true (I := I) (red_tr (d := 384) (by omega) (by omega))
    fun _ _ _ _ _ hL hc => WP.mono (red_ok hL hc (d := 384) (by omega) (by omega) (by omega)) fun _ h => h.1
  have e := two_true (I := I) (base_tr hb hct) fun _ _ _ _ _ hL hc => WP.mono (base_ok hb hL hc) fun _ h => h.1
  have f := two_true (I := I) chalHash_tr fun _ _ _ _ _ hL hc => WP.mono (chalHash_ok hL hc) fun _ h => h.1
  have g := two_true (I := I) (red_tr (d := 256) (by omega) (by omega))
    fun _ _ _ _ _ hL hc => WP.mono (red_ok hL hc (d := 256) (by omega) (by omega) (by omega)) fun _ h => h.1
  have h := two_true (I := I) mulAdd_tr fun _ _ _ _ _ hL hc => WP.mono (mulAdd_ok hL hc) fun _ h => h.1
  exact a.seq (b.seq (c.seq (d.seq (e.seq (f.seq (g.seq (h.seq (block_rsp_tr wipe_spOnly fun _ _ h => h.rsp))))))))

end

/-! ## The function -/

/-- The public data of the contract, spelled out. -/
structure SPub (s₁ s₂ : State) : Prop where
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  rdi : s₁.gpr .rdi = s₂.gpr .rdi
  rsi : s₁.gpr .rsi = s₂.gpr .rsi
  rdx : s₁.gpr .rdx = s₂.gpr .rdx
  rcx : s₁.gpr .rcx = s₂.gpr .rcx
  r8 : s₁.gpr .r8 = s₂.gpr .r8
  r9 : s₁.gpr .r9 = s₂.gpr .r9
  a0 : stackArg s₁ 0 = stackArg s₂ 0
  a1 : stackArg s₁ 1 = stackArg s₂ 1

theorem sPub_of {s₁ s₂ : State} (h : (Spec.Ed448.signCachedContract X86_64.abi 464).pub s₁ s₂) : SPub s₁ s₂ := by
  sig_pub [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, X86_64.abi,
    X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem slay_eq {s₁ s₂ : State} (h₁ : SPre s₁) (h₂ : SPre s₂) (h : SPub s₁ s₂) : slay s₁ = slay s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [sSeed, sPk, sCtx, sMsg, sArgs, stackArgAddr, h.rsi, h.rdx, h.rcx, h.r8, h.r9,
      h.a0, h.rsp]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [sOut, sScr, h.rdi, h.a1]
  simp only [slay, h.rsp, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.a0, h.a1, e1, e2]

/-- The entry states of two runs: the precondition and the public data. -/
abbrev SP2 (x y : State) : Prop :=
  (Spec.Ed448.signCachedContract X86_64.abi 464).pre x ∧ (Spec.Ed448.signCachedContract X86_64.abi 464).pre y ∧
    (Spec.Ed448.signCachedContract X86_64.abi 464).pub x y

/-- After the moves before the push. -/
abbrev SMov (x x2 : State) : Prop :=
  (x2.gpr .r10 = stackArg x 0 ∧ x2.gpr .r11 = stackArg x 1 ∧ x2.mem = x.mem ∧ x2.mxcsr = x.mxcsr) ∧
    Keep [.r10, .r11, .rax] x x2

theorem signCached_ct (hb : BaseOk) (hct : BaseCT) :
    ConstantTime isa (Spec.Ed448.signCachedContract X86_64.abi 464).pre
      (Spec.Ed448.signCachedContract X86_64.abi 464).pub signCached := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (Spec.Ed448.signCachedContract X86_64.abi 464).pre s₁ ∧
      (Spec.Ed448.signCachedContract X86_64.abi 464).pre s₂ ∧
      (Spec.Ed448.signCachedContract X86_64.abi 464).pub s₁ s₂) = Ghost SP2 (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold signCached
  have hmov := ghost_step (P := SP2) (A := fun x a => a = x) (B := SMov)
    (c := .block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)])
    (block_rsp_tr (fun i hi => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
        · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
        · exact spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨x, y, hxy, e₁, e₂⟩ => by subst e₁ e₂; exact (sPub_of hxy.2.2).rsp)
    fun x y a b hxy e₁ e₂ => by
      subst e₁ e₂
      exact ⟨signMov_ok (sPre_of hxy.1), signMov_ok (sPre_of hxy.2.1)⟩
  refine RelCT.seq hmov ?_
  refine RelCT.frame (R := fun _ _ => True) (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2.gpr (by decide), f₂.2.gpr (by decide)]; exact (sPub_of hxy.2.2).rsp) ?_
  -- The frame's body, from the push.
  let A : State → State → Prop := fun x a => ∃ s₁, SMov x s₁ ∧ a = pushed regs s₁
  let B : State → State → Prop := fun x t => Ctx (slay x) x.gpr x.mxcsr x.mem t
  have hh := ghost_step (P := SP2) (A := A) (B := B) (c := .block hdr)
    (block_rsp_tr hdr_spOnly
      fun a b ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩ => by
        subst e₁ e₂
        rw [pushed_rsp, pushed_rsp, f₁.2.gpr (by decide), f₂.2.gpr (by decide), (sPub_of hxy.2.2).rsp])
    fun x y a b hxy fa fb => by
      have en : ∀ {x a : State}, (Spec.Ed448.signCachedContract X86_64.abi 464).pre x → A x a →
          WP isa (.block hdr) a (B x) := fun hx ⟨s₁, f, e⟩ => by
        subst e
        have h := sPre_of hx
        have hL := slay_ok h
        have hc := entry_ctx hL (by rw [f.2.gpr (by decide), slay_B]) f.2.2.1 f.2.2.2 f.1.2.1
          (f.2.gpr (by decide)) f.1.1 (f.2.gpr (by decide)) (f.2.gpr (by decide)) (f.2.gpr (by decide))
          (f.2.gpr (by decide)) (f.2.gpr (by decide))
        exact WP.mono (hdr_ok hL hc) fun t ⟨hc', _⟩ =>
          hc'.congr (fun r hr _ => f.2.gpr (cs_tmp r hr)) f.1.2.2.2 f.1.2.2.1
      exact ⟨en hxy.1 fa, en hxy.2.1 fb⟩
  refine RelCT.seq (RelCT.mono hh (fun a b ⟨s₁, s₂, ⟨x, y, hxy, f₁, f₂⟩, e₁, e₂⟩ =>
    ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩) fun a b ⟨x, y, hxy, ca, cb⟩ => ?_)
    (rest_tr (I := fun _ _ _ => True) hb hct)
  have hx := sPre_of hxy.1
  have e := slay_eq hx (sPre_of hxy.2.1) (sPub_of hxy.2.2)
  exact ⟨slay x, x.gpr, y.gpr, x.mxcsr, y.mxcsr, x.mem, y.mem, slay_ok hx, trivial, ca, e ▸ cb, trivial, trivial⟩

end VG.Proof.Ed448.X86_64.SignCached
