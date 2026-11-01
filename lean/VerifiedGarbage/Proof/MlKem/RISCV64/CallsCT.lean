module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Calls
import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Calls
meta import VerifiedGarbage.Proof.MlKem.RISCV64.KemLay
meta import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Impl.MlKem.RISCV64.Top

/-!
# ML-KEM on RISC-V: calling the primitives in constant time

As on PPC64LE (`Proof/MlKem/PPC64LE/CallsCT.lean`). The taint analysis proves
the primitives constant time from any state whose stack pointer and argument
registers are public (`addT`, …), so two runs that call one with the same
arguments leak the same trace (`RelCT.callT`), whatever else holds of them.
`vg_mlkem_sample_ntt` leaks its seed, so two runs that call it must also have
the same seed (`sample_ct`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A call of code that is constant time from any state with public `pub`. -/
theorem RelCT.callT {n : String} {c : Prog isa} {pub : State → State → Prop}
    (hct : ConstantTime isa (fun _ => True) pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → pub s₁.callEntry s₂.callEntry) :
    RelCT isa P (.call n c) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      have ht := hct _ _ _ _ _ _ trivial trivial (hP _ _ hp) b₁ b₂
      exact ⟨by simp only [ht], trivial⟩

/-- Taint analysis of any code (not only a block). -/
theorem taint_prog {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨hsp a b hab, fun r hr => hP a b hab r (Taint.mem_ofRegs.mp hr)⟩) h

/-- `c` is constant time from any two states that agree on the stack pointer
and the registers `rs`, by the taint analysis. -/
def RegsCT (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc : VG.Taint.Hint VG.RISCV64.taint.T, (VG.RISCV64.taint.check (Taint.ofRegs rs) c hc).isSome = true

theorem RegsCT.relct {rs : List Reg} {c : Prog isa} (h : RegsCT rs c) {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r) :
    RelCT isa P c fun _ _ => True :=
  h.elim fun _ h => taint_prog rs hsp hP h

/-- A contract with no precondition, whose public data is the stack pointer
and the registers `rs`. -/
def kT (rs : List Reg) : Contract isa := mkK (fun _ => True) (fun _ _ => True) (regsEq rs)

theorem addT : ConstantTime isa (fun _ => True) (regsEq [.a0, .a1]) Impl.MlKem.RISCV64.add :=
  Add.ctRegs (k := kT [.a0, .a1]) [.a0, .a1] (fun _ _ h => h.2) (fun _ _ h => h.1) (by taint_decide)

theorem subT : ConstantTime isa (fun _ => True) (regsEq [.a0, .a1]) Impl.MlKem.RISCV64.sub :=
  Add.ctRegs (k := kT [.a0, .a1]) [.a0, .a1] (fun _ _ h => h.2) (fun _ _ h => h.1) (by taint_decide)

theorem mulT : ConstantTime isa (fun _ => True) (regsEq [.a0, .a1, .a2, .a3]) Impl.MlKem.RISCV64.multiplyNTTs :=
  Add.ctRegs (k := kT [.a0, .a1, .a2, .a3]) [.a0, .a1, .a2, .a3] (fun _ _ h => h.2) (fun _ _ h => h.1)
    (by taint_decide)

theorem nttT : ConstantTime isa (fun _ => True) (regsEq [.a0, .a1]) Impl.MlKem.RISCV64.ntt :=
  Add.ctRegs (k := kT [.a0, .a1]) [.a0, .a1] (fun _ _ h => h.2) (fun _ _ h => h.1) (by taint_decide)

theorem nttInvT : ConstantTime isa (fun _ => True) (regsEq [.a0, .a1]) Impl.MlKem.RISCV64.nttInv :=
  Add.ctRegs (k := kT [.a0, .a1]) [.a0, .a1] (fun _ _ h => h.2) (fun _ _ h => h.1) (by taint_decide)

theorem cbd2T : ConstantTime isa (fun _ => True) (regsEq [.a0, .a1]) Impl.MlKem.RISCV64.cbd2 :=
  Add.ctRegs (k := kT [.a0, .a1]) [.a0, .a1] (fun _ _ h => h.2) (fun _ _ h => h.1) (by taint_decide)

theorem encode12T : ConstantTime isa (fun _ => True) (regsEq [.a0, .a1]) Impl.MlKem.RISCV64.encode12 :=
  Add.ctRegs (k := kT [.a0, .a1]) [.a0, .a1] (fun _ _ h => h.2) (fun _ _ h => h.1) (by taint_decide)

theorem decode12T : ConstantTime isa (fun _ => True) (regsEq [.a0, .a1]) Impl.MlKem.RISCV64.decode12 :=
  Add.ctRegs (k := kT [.a0, .a1]) [.a0, .a1] (fun _ _ h => h.2) (fun _ _ h => h.1) (by taint_decide)

theorem compressT :
    ConstantTime isa (fun _ => True) (regsEq [.a0, .a1, .a2, .a3]) Impl.MlKem.RISCV64.compressEncode := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    (RelCT.seq (CompressEncode.zext_rel.mono (fun s₁ s₂ ⟨_, _, hsp, hr⟩ => ?_) fun _ _ h => h)
      (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
        (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) (by taint_decide)))
  refine ⟨hsp, fun r hm => hr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rcases hm with rfl | rfl | rfl <;> simp),
    by rw [hr .a1 (by simp)]⟩

theorem decompressT :
    ConstantTime isa (fun _ => True) (regsEq [.a0, .a1, .a2, .a3]) Impl.MlKem.RISCV64.decodeDecompress := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    (RelCT.seq (DecodeDecompress.zext_rel.mono (fun s₁ s₂ ⟨_, _, hsp, hr⟩ => ?_) fun _ _ h => h)
      (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
        (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) (by taint_decide)))
  refine ⟨hsp, fun r hm => hr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rcases hm with rfl | rfl | rfl <;> simp),
    by rw [hr .a2 (by simp)]⟩

/-- Two runs that call a primitive with the same stack pointer and registers `rs`. -/
theorem callEq {rs : List Reg} (hl : ∀ r ∈ rs, r ∉ linkRegs) {a b : State} (hsp : a.sp = b.sp)
    (h : ∀ r ∈ rs, a.gpr r = b.gpr r) : regsEq rs a.callEntry b.callEntry :=
  ⟨by rw [State.callEntry_sp, State.callEntry_sp, hsp], fun r hr => by
    rw [State.callEntry_gpr _ (hl r hr), State.callEntry_gpr _ (hl r hr), h r hr]⟩

theorem regs2 {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧ a.gpr .a0 = b.gpr .a0 ∧ a.gpr .a1 = b.gpr .a1) :
    ∀ a b, P a b → regsEq [.a0, .a1] a.callEntry b.callEntry := fun a b h =>
  callEq (by decide) (hP a b h).1 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hP a b h).2.1
    · exact (hP a b h).2.2

theorem regs4 {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧ a.gpr .a0 = b.gpr .a0 ∧ a.gpr .a1 = b.gpr .a1 ∧ a.gpr .a2 = b.gpr .a2 ∧
      a.gpr .a3 = b.gpr .a3) :
    ∀ a b, P a b → regsEq [.a0, .a1, .a2, .a3] a.callEntry b.callEntry := fun a b h =>
  callEq (by decide) (hP a b h).1 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hP a b h).2.1
    · exact (hP a b h).2.2.1
    · exact (hP a b h).2.2.2.1
    · exact (hP a b h).2.2.2.2

/-! ## `vg_mlkem_sample_ntt` -/

theorem kSample_ct : ConstantTime isa kSample.pre kSample.pub Impl.MlKem.RISCV64.sampleNTT :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨⟨hsp, hr⟩, hb⟩ e₁ e₂ =>
    (Sample.all_ct ⟨h₁, h₂, hsp, hr .a0 (by simp), hr .a1 (by simp), hr .a2 (by simp), hb⟩
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1

theorem Ctx.sp_eq {L : Lay} {a b : State} (ha : Ctx L a) (hb : Ctx L b) : a.sp = b.sp := by
  have e := ha.sp.symm.trans hb.sp
  have := BitVec.sub_add_cancel a.sp (BitVec.ofNat 64 1168)
  rw [e, BitVec.sub_add_cancel] at this
  exact this.symm

/-- What `vg_mlkem_sample_ntt` needs, as `sampleL` builds it. -/
theorem sample_view {L : Lay} {s : State} (hc : Ctx L s) {i o j o' k o'' : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = L.A j o') (g5 : s.gpr .a2 = L.A k o'')
    (s_ij : sepB L.sizes (i, o, 34) (j, o', 1024) = true) (s_ik : sepB L.sizes (i, o, 34) (k, o'', 2048) = true)
    (s_jk : sepB L.sizes (j, o', 1024) (k, o'', 2048) = true) (s_i1 : sepB L.sizes (i, o, 34) (1, 0, 1168) = true)
    (s_j1 : sepB L.sizes (j, o', 1024) (1, 0, 1168) = true) (s_k1 : sepB L.sizes (k, o'', 2048) (1, 0, 1168) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) (wk : L.buf k ∈ s.wr) (aj : L.Al j o')
    (ak : L.Al k o'') :
    Sample.Pre (view s [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]) ∧
      Covers ([⟨L.A i o, 34⟩] ++ [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]) (s.rd ++ s.wr) ∧
      Covers [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩] s.wr ∧
      Sample.B (view s [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]) = bytesAt s.mem (L.A i o) 34 := by
  have hL := hc.ok
  let V := view s [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]
  have eS : Sample.SEED V = L.A i o := by simp only [V, Sample.SEED, view_r3, g3]
  have eA : Sample.A V = L.A j o' := by simp only [V, Sample.A, view_r4, g4]
  have eC : Sample.S V = L.A k o'' := by simp only [V, Sample.S, view_r5, g5]
  have eb : Sample.STK V = L.R 1 0 1168 := hc.bel
  have cw : Covers [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩] s.wr :=
    covers_cons' (Lay.covers wj (sepB_bounds s_jk).2) (covers_cons' (Lay.covers wk (sepB_bounds (sepB_symm s_ik)).2)
      covers_nil')
  have hpre : Sample.Pre V := by
    refine ⟨hc.al, hc.sp1168, by simp only [V, eS, State.withRegions_rd], by simp only [V, eA, eC, State.withRegions_wr],
      by rw [eS, eA]; exact Lay.disj hL s_ij, by rw [eS, eC]; exact Lay.disj hL s_ik,
      by rw [eA, eC]; exact Lay.disj hL s_jk, by rw [eb, eS]; exact Lay.disj hL (sepB_symm s_i1),
      by rw [eb, eA]; exact Lay.disj hL (sepB_symm s_j1), by rw [eb, eC]; exact Lay.disj hL (sepB_symm s_k1),
      by rw [eS]; exact Lay.fitB hL (sepB_bounds s_ij) (by decide),
      by rw [eA]; exact Lay.fitB hL (sepB_bounds s_jk) (by decide),
      by rw [eC]; exact Lay.fitB hL (sepB_bounds (sepB_symm s_ik)) (by decide), by rw [eA]; exact aj.four,
      by rw [eC]; exact ak⟩
  refine ⟨hpre, covers_append (Lay.covers wi (sepB_bounds s_ij).2) (covers_wr cw), cw, ?_⟩
  show bytesAt s.mem (Sample.SEED V) 34 = _
  rw [eS]

/-- Two runs that call `vg_mlkem_sample_ntt` on the same pointers and seed. -/
theorem sample_ct {L : Lay} {i o j o' k o'' : Nat} {P : State → State → Prop}
    (hP : ∀ a b, P a b → Ctx L a ∧ Ctx L b ∧
      a.gpr .a0 = L.A i o ∧ a.gpr .a1 = L.A j o' ∧ a.gpr .a2 = L.A k o'' ∧
      b.gpr .a0 = L.A i o ∧ b.gpr .a1 = L.A j o' ∧ b.gpr .a2 = L.A k o'' ∧
      bytesAt a.mem (L.A i o) 34 = bytesAt b.mem (L.A i o) 34 ∧
      L.buf i ∈ a.rd ++ a.wr ∧ L.buf j ∈ a.wr ∧ L.buf k ∈ a.wr ∧
      L.buf i ∈ b.rd ++ b.wr ∧ L.buf j ∈ b.wr ∧ L.buf k ∈ b.wr)
    (s_ij : sepB L.sizes (i, o, 34) (j, o', 1024) = true) (s_ik : sepB L.sizes (i, o, 34) (k, o'', 2048) = true)
    (s_jk : sepB L.sizes (j, o', 1024) (k, o'', 2048) = true) (s_i1 : sepB L.sizes (i, o, 34) (1, 0, 1168) = true)
    (s_j1 : sepB L.sizes (j, o', 1024) (1, 0, 1168) = true) (s_k1 : sepB L.sizes (k, o'', 2048) (1, 0, 1168) = true)
    (aj : L.Al j o') (ak : L.Al k o'') :
    RelCT isa P callSample fun _ _ => True :=
  RelCT.call kSample_ok kSample_ct [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩] fun a b hab => by
    obtain ⟨ca, cb, a3, a4, a5, b3, b4, b5, eb, wia, wja, wka, wib, wjb, wkb⟩ := hP a b hab
    obtain ⟨pa, c1a, c2a, ba⟩ := sample_view ca a3 a4 a5 s_ij s_ik s_jk s_i1 s_j1 s_k1 wia wja wka aj ak
    obtain ⟨pb, c1b, c2b, bb⟩ := sample_view cb b3 b4 b5 s_ij s_ik s_jk s_i1 s_j1 s_k1 wib wjb wkb aj ak
    refine ⟨pa, pb, ⟨⟨by simp only [State.withRegions_sp, State.callEntry_sp]; exact Ctx.sp_eq ca cb,
      fun r hr => ?_⟩, by rw [ba, bb, eb]⟩, c1a, c2a, c1b, c2b⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [view_r3, view_r3, a3, b3]
    · rw [view_r4, view_r4, a4, b4]
    · rw [view_r5, view_r5, a5, b5]

/-! ## Loops counted by a register -/

theorem isa_eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero r) s = some (s.gpr r != 0) := rfl

/-- A loop whose body runs `N` times, related in two runs by invariants at
the same iteration. -/
theorem relct_loop_nz {body : Prog isa} {r : Reg} {I₁ I₂ : Nat → State → Prop} {N : Nat} (hN : 0 < N)
    (hstep : ∀ i < N, RelCT isa (fun a b => I₁ i a ∧ I₂ i b) body fun a b =>
      (I₁ (i + 1) a ∧ (a.gpr r != 0) = decide (i + 1 ≠ N)) ∧ (I₂ (i + 1) b ∧ (b.gpr r != 0) = decide (i + 1 ≠ N))) :
    RelCT isa (fun a b => I₁ 0 a ∧ I₂ 0 b) (.loop body (.nonzero r)) fun a b => I₁ N a ∧ I₂ N b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := body) (c := .nonzero r)
    (Q := fun a b => I₁ N a ∧ I₂ N b)
    (fun n a b => ∃ t, t < N ∧ n = N - t ∧ I₁ t a ∧ I₂ t b) (fun n => ?_) N) ?_ (fun _ _ h => h)
  · refine RelCT.mono (P := fun a b => ∃ t, t < N ∧ n = N - t ∧ I₁ t a ∧ I₂ t b)
      (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
    by_cases ht : t < N
    · by_cases hn : n = N - t
      · refine RelCT.mono (P := fun a b => I₁ t a ∧ I₂ t b) (hstep t ht) (fun _ _ hab => hab.2.2)
          fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
        · rw [isa_eval_nonzero, isa_eval_nonzero, z₁, z₂]
        · have : t + 1 = N := by
            rw [isa_eval_nonzero, z₁, Option.some.injEq] at e; simpa using e
          rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
        · have : t + 1 ≠ N := by
            rw [isa_eval_nonzero, z₁, Option.some.injEq] at e; simpa using e
          exact ⟨N - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
      · exact RelCT.of_false fun _ _ hab => hn hab.2.1
    · exact RelCT.of_false fun _ _ hab => ht hab.1
  · exact fun a b hab => ⟨0, hN, rfl, hab⟩

/-! ## What each parameter set checks by evaluation -/

/-- What each parameter set proves of its code by evaluation: the contracts of
its primitives that compress to `d_u` and `d_v` bits (and decompress from
them), as calls on regions of a layout (as `compressL` and `decompressL`),
and their constant time. -/
structure _root_.VG.Impl.MlKem.RISCV64.KemLay.CallsOk (K : KemLay) : Prop where
  cu : ∀ {L : Lay} {s : State}, L.Ok → ∀ {i o j o' d : Nat}, s.gpr .a0 = L.A i o →
    s.gpr .a1 = BitVec.ofNat 64 d → s.gpr .a2 = L.A j o' → s.gpr .a3 = BitVec.ofNat 64 (32 * d) →
    d = K.du ∨ d = K.dv → sepB L.sizes (i, o, 1024) (j, o', 32 * d) = true → L.buf i ∈ s.rd ++ s.wr →
    L.buf j ∈ s.wr → ∀ {f : Poly}, PolyIs s.mem (L.A i o) f → L.Al i o → ∀ {Q : State → Prop},
    (∀ s', Kept (L.RL [(j, o', 32 * d)]) s s' → bytesAt s'.mem (L.A j o') (32 * d) = compressEncode d f → Q s') →
    WP isa K.callCU s Q
  du : ∀ {L : Lay} {s : State}, L.Ok → ∀ {i o j o' d : Nat}, s.gpr .a0 = L.A i o →
    s.gpr .a1 = BitVec.ofNat 64 (32 * d) → s.gpr .a2 = BitVec.ofNat 64 d → s.gpr .a3 = L.A j o' →
    d = K.du ∨ d = K.dv → sepB L.sizes (i, o, 32 * d) (j, o', 1024) = true → L.buf i ∈ s.rd ++ s.wr →
    L.buf j ∈ s.wr → L.Al j o' → ∀ {Q : State → Prop},
    (∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (decodeDecompress d (bytesAt s.mem (L.A i o) (32 * d))) → Q s') →
    WP isa K.callDU s Q
  cuT : ConstantTime isa (fun _ => True) (regsEq [.a0, .a1, .a2, .a3]) K.compress
  duT : ConstantTime isa (fun _ => True) (regsEq [.a0, .a1, .a2, .a3]) K.decompress
  seedT : ∀ t, RegsCT [.s11]
    (.block (seedBytes t ++ .addi .a0 .s11 oSeed :: polyAddr .a1 K.jAhat ++ polyAddr .a2 K.jSample))
  zeroT : RegsCT [.s11] (zeroPoly K.jAcc)
  kgSetupT : RegsCT [.a0, .a1, .a2, .a3] (.block K.kgSetup)
  rhoT : RegsCT [.s9, .s11] (copy .s11 oSeed .s9 (384 * K.k) 32)
  ekT : RegsCT [.s8, .s9] (copy .s9 0 .s8 (384 * K.k) K.ekLen)
  zT : RegsCT [.s8, .s10] (copy .s10 32 .s8 (768 * K.k + 64) 32)
  encSeedT : RegsCT [.s10, .s11] (copy .s10 (384 * K.k) .s11 oSeed 32)
  ctT : RegsCT [.s8, .s11] (copy .s8 0 .s11 oCin K.ctLen)
  cmpT : RegsCT [.s7, .s8] K.compare

theorem kl768_calls : kl768.CallsOk :=
  ⟨fun hL _ _ _ _ _ g3 g4 g5 g6 hd => compressL hL g3 g4 g5 g6 (by rcases hd with rfl | rfl <;> decide),
    fun hL _ _ _ _ _ g3 g4 g5 g6 hd => decompressL hL g3 g4 g5 g6 (by rcases hd with rfl | rfl <;> decide),
    compressT, decompressT, fun t => by cases t <;> exact ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.MlKem.RISCV64
