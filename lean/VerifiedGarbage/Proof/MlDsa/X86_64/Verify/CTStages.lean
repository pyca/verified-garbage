module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.StageC
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
public import VerifiedGarbage.Proof.MlKem.X86_64.Rel
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Flag
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Top
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlKem.X86_64.Rel
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Flag
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Top
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlDsa.X86_64.Verify.CTBase`, which this module and modules that import it used -/

section

/-!
# ML-DSA verification on x86-64: constant time, the pieces without calls

Two runs from inputs with the same public data (`RV`) keep the same pointers
(`T.lrel`). A block that accesses no memory, followed by code that the taint
analysis checks from the registers it sets (`blockLoop_tr`), leaks the same in
both: the copy (`copy_tr`), the mask of a sampler's output (`mask_tr`) and the
comparison (`cmpAnd_tr`). The rest is checked by the taint analysis.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (at_)
open VG.Spec.MlDsa

/-- Two runs from states satisfying `VPre p` with the same public data, each
satisfying `I` from its own initial state. -/
abbrev RV (p : Params) (I : State → State → Prop) : State → State → Prop := Rel2 (VPre p) (verifyK p).pub I

theorem T.sameB {p : Params} {σ₁ σ₂ x y : State} (pub : (verifyK p).pub σ₁ σ₂) (h₁ : T p σ₁ x) (h₂ : T p σ₂ y) :
    SameB x y := by
  refine ⟨fun r hr => ?_, by rw [h₁.rsp, h₂.rsp, pub.2.2.2.2.1]⟩
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, pub.2.2.2.1]
  · rw [h₁.rbp, h₂.rbp, pub.1]
  · rw [h₁.r12, h₂.r12, pub.2.1]
  · rw [h₁.r13, h₂.r13, pub.2.2.1]

theorem RV.lrel {p : Params} (hp : p ∈ params) {I : State → State → Prop} (hI : ∀ σ s, I σ s → T p σ s)
    {x y : State} (h : RV p I x y) : LRel (vR p) (vW p) x y := by
  obtain ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩ := h
  exact ⟨(hI _ _ i₁).lay hp v₁, (hI _ _ i₂).lay hp v₂, T.sameB pub (hI _ _ i₁) (hI _ _ i₂)⟩

/-! ## A block without memory accesses, then code the taint analysis checks -/

theorem blockLoop_tr {B : List Instr} {L : Prog isa} {P : State → State → Prop}
    (hB : ∀ i ∈ B, ∀ s, isa.addrs i s = []) {F : State → State → Prop}
    (hw : ∀ x y, P x y → WP isa (.block B) x (F x) ∧ WP isa (.block B) y (F y)) (rs : List Reg)
    (hQ : ∀ x y x' y', P x y → F x x' → F y y' → ∀ r ∈ rs, x'.gpr r = y'.gpr r)
    {hc : VG.Taint.Hint X86_64.Taint.T} (h : (taint.check (X86_64.Taint.ofRegs rs) L hc).isSome = true) :
    RelCT isa P (.seq (.block B) L) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (block_nomem_tr hB) hw hQ) (taintRel rs (fun _ _ h => h) h)

theorem SameB.arg {x y : State} (h : SameB x y) {p : Ptr} (hp : p.1 ∈ bases) : (Arg.ptr p).val x = (Arg.ptr p).val y :=
  h.pa hp

theorem copy_tr {dst src : Ptr} {n : Nat} (hok : ∀ a ∈ copyArgs dst src n, a.2.Ok ∧ a.1 ∈ argRegs)
    (hd : dst.1 ∈ bases) (hs : src.1 ∈ bases) {P : State → State → Prop} (hP : ∀ x y, P x y → SameB x y) :
    RelCT isa P (copy dst src n) fun _ _ => True := by
  have nd : ((copyArgs dst src n).map (·.1)).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  unfold copy
  refine blockLoop_tr (glue_nomem _) (fun x y _ => ⟨glue_ok' hok nd x, glue_ok' hok nd y⟩) [.rdi, .rsi, .rcx]
    (fun x y x' y' hp hx hy r hr => ?_) (by taint_decide)
  have e := hP x y hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [hx.1.1 _ (List.mem_cons_self ..), hy.1.1 _ (List.mem_cons_self ..)]; exact e.arg hd
  · rw [hx.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      hy.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))]; exact e.arg hs
  · rw [hx.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
      hy.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))]; rfl

theorem maskPre_wp {a : Ptr} (hok : (Arg.ptr a).Ok) {N : Nat} (hN : N < 2 ^ 31) (s : State) :
    WP isa (.block (glue [(.rdi, .ptr a), (.rcx, .imm (N / 4))] ++ ([.mov32 .rdx (.imm 0), .alu32 .sub .rdx (.reg .rax),
      .xop (.movq .xmm0 .rdx), .xop (.pshufd .xmm0 .xmm0 0)] : List Instr))) s
      fun s' => s'.gpr .rdi = (Arg.ptr a).val s ∧ s'.gpr .rcx = BitVec.ofNat 64 (N / 4) := by
  have hok' : ∀ x ∈ ([(.rdi, .ptr a), (.rcx, .imm (N / 4))] : List (Reg × Arg)), x.2.Ok ∧ x.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨hok, by decide⟩, ⟨show N / 4 < 2 ^ 31 by omega_using [hN], by decide⟩⟩
  rw [WP.block_append_iff]
  refine WP.mono (glue_ok' hok' (by simp only [List.map_cons, List.map_nil]; decide) s) fun s1 h1 => ?_
  refine WP.mono (maskPre_ok s1) fun s2 ⟨_, k2⟩ => ⟨?_, ?_⟩
  · rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_self ..)
  · rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem mask_tr {a : Ptr} (hok : (Arg.ptr a).Ok) (hb : a.1 ∈ bases) {N : Nat} (hN : N < 2 ^ 31)
    {P : State → State → Prop} (hP : ∀ x y, P x y → SameB x y) : RelCT isa P (mask a N) fun _ _ => True := by
  unfold mask
  refine blockLoop_tr (fun i hi s => ?_) (fun x y _ => ⟨maskPre_wp hok hN x, maskPre_wp hok hN y⟩)
    [.rdi, .rcx]
    (fun x y x' y' hp hx hy r hr => ?_) (by taint_decide)
  · rcases List.mem_append.mp hi with h | h
    · exact glue_nomem _ i h s
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.1, hy.1]; exact (hP x y hp).arg hb
    · rw [hx.2, hy.2]

theorem cmpPre_wp {a b : Ptr} {n : Nat} (hok : ∀ x ∈ ([(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] : List (Reg × Arg)),
      x.2.Ok ∧ x.1 ∈ argRegs) (s : State) :
    WP isa (.block (glue [(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] ++ ([.mov32 .rdx (.imm 0)] : List Instr))) s
      fun s' => s'.gpr .rsi = (Arg.ptr a).val s ∧ s'.gpr .rdi = (Arg.ptr b).val s ∧
        s'.gpr .rcx = (Arg.imm n).val s := by
  rw [WP.block_append_iff]
  refine WP.mono (glue_ok' hok (by simp only [List.map_cons, List.map_nil]; decide) s) fun s1 h1 => ?_
  refine WP.mono (WP.keep [.rdx] (Q := fun s₂ => s₂.mem = s1.mem ∧ s₂.gpr .rdx = 0) (by xrun) (Proof.MlKem.X86_64.writesOnly_of (by decide))) fun s2 ⟨_, k2⟩ => ⟨?_, ?_, ?_⟩
  · rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_self ..)
  · rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · rw [k2.gpr (by decide)]
    exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem cmpAnd_tr {a b : Ptr} {n : Nat}
    (hok : ∀ x ∈ ([(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] : List (Reg × Arg)), x.2.Ok ∧ x.1 ∈ argRegs)
    (ha : a.1 ∈ bases) (hb : b.1 ∈ bases) {P : State → State → Prop} (hP : ∀ x y, P x y → SameB x y) :
    RelCT isa P (cmpAnd a b n) fun _ _ => True := by
  unfold cmpAnd
  refine blockLoop_tr (fun i hi s => ?_) (fun x y _ => ⟨cmpPre_wp hok x, cmpPre_wp hok y⟩) [.rsi, .rdi, .rcx]
    (fun x y x' y' hp hx hy r hr => ?_) (by taint_decide)
  · rcases List.mem_append.mp hi with h | h
    · exact glue_nomem _ i h s
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hx.1, hy.1]; exact (hP x y hp).arg ha
    · rw [hx.2.1, hy.2.1]; exact (hP x y hp).arg hb
    · rw [hx.2.2, hy.2.2]; rfl

/-! ## Blocks the taint analysis checks -/

theorem and15_tr {P : State → State → Prop} : RelCT isa P (.block and15) fun _ _ => True :=
  block_nomem_tr fun i hi s => by simp only [and15, List.mem_singleton] at hi; subst hi; rfl

theorem pro_tr {p : Params} : RelCT isa (RV p fun σ s => s = σ) (.block proF) fun _ _ => True :=
  taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    subst h₁ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [pub.2.2.2.1, pub.1, pub.2.1, pub.2.2.1]) (by taint_decide)

theorem epi_tr {p : Params} : RelCT isa (RV p (T p)) (.block epi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.rbx, h₂.rbx, pub.2.2.2.1]) (by taint_decide)

end VG.Proof.MlDsa.X86_64.Verify

end

end

/-!
# ML-DSA verification on x86-64: constant time, the hint and `z`

Two runs with the same public data (`RV`) run the same code: each piece's
invariant holds of each run from its own inputs (`relInv`), which gives what
each call's trace needs (the pointers, reduced inputs, and the public bytes it
reads); the branches test results that are functions of the signature alone
(the hint is well formed, `z` is small: `ifOk_rel`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt)

theorem layOk : ∀ p ∈ params, LayOk (vB p) := by unfold LayOk; decide

/-- Two runs after a piece `F` from states satisfying `I` keep the layout. -/
theorem RV.lrelStep {p : Params} (hp : p ∈ params) {I : State → State → Prop} (hI : ∀ σ s, I σ s → T p σ s)
    {F : State → State → Prop} (hF : ∀ s₀ s, F s₀ s → ∃ W, PostB s₀ s W) {x y : State}
    (h : RV p (fun σ s => ∃ s₀, I σ s₀ ∧ F s₀ s) x y) : LRel (vR p) (vW p) x y := by
  obtain ⟨σ₁, σ₂, v₁, v₂, pub, ⟨x₀, i₁, f₁⟩, ⟨y₀, i₂, f₂⟩⟩ := h
  obtain ⟨_, hx⟩ := hF _ _ f₁
  obtain ⟨_, hy⟩ := hF _ _ f₂
  exact (RV.lrel hp hI ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩).post hx hy

/-- A piece that keeps the layout leaves two runs with the same pointers. -/
theorem RelCT.sameB {P : State → State → Prop} {c : Prog isa} (ht : RelCT isa P c fun _ _ => True)
    (hw : ∀ x y, P x y → WP isa c x (fun x' => ∃ W, PostB x x' W) ∧ WP isa c y (fun y' => ∃ W, PostB y y' W))
    (hs : ∀ x y, P x y → SameB x y) : RelCT isa P c fun x y => SameB x y :=
  RelCT.postDep ht hw fun x y _ _ hp ⟨_, hx⟩ ⟨_, hy⟩ => (hs x y hp).post hx hy

theorem and15_post (x : State) : WP isa (.block and15) x fun x' => ∃ W, PostB x x' W :=
  WP.mono (and15_ok x) fun x' ⟨⟨_, hm⟩, k⟩ =>
    ⟨_, (postB_of_keep k (by decide) (by rw [hm]; exact Frame.refl _ _) : PPostB x x' [])⟩

theorem sampledTail_tr {a : Ptr} (hok : (Arg.ptr a).Ok) (hb : a.1 ∈ bases) :
    RelCT isa (fun x y => SameB x y) (.seq (.block and15) (mask a)) fun _ _ => True :=
  RelCT.seq (RelCT.sameB and15_tr (fun x y _ => ⟨and15_post x, and15_post y⟩) fun _ _ h => h)
    (mask_tr hok hb (N := 256) (by decide) fun _ _ h => h)

theorem sampledTail4_tr {a : Ptr} (hok : (Arg.ptr a).Ok) (hb : a.1 ∈ bases) :
    RelCT isa (fun x y => SameB x y) (.seq (.block and15) (mask a 1024)) fun _ _ => True :=
  RelCT.seq (RelCT.sameB and15_tr (fun x y _ => ⟨and15_post x, and15_post y⟩) fun _ _ h => h)
    (mask_tr hok hb (N := 1024) (by decide) fun _ _ h => h)

theorem flag_ne {P : Prop} [Decidable P] (h : (flag P).setWidth 32 ≠ 0) : P := by
  by_contra hn
  exact h (by unfold flag; rw [ifn hn]; rfl)

/-! ## Branches -/

theorem ifOk_rel {p : Params} (hp : p ∈ params) {I It : State → State → Prop} {c : Prog isa}
    (hT : ∀ σ s, I σ s → T p σ s)
    (he : ∀ x y, RV p I x y → (x.gpr .r15).setWidth 32 = (y.gpr .r15).setWidth 32)
    (hk : ∀ σ s₀ s, VPre p σ → I σ s₀ → PPostB s₀ s [] → s.gpr .r15 = s₀.gpr .r15 →
      (s₀.gpr .r15).setWidth 32 ≠ 0 → It σ s)
    (ht : RelCT isa (RV p It) c (RV p (T p))) : RelCT isa (RV p I) (ifOk c) (RV p (T p)) := by
  refine ifOk_tr he (RelCT.mono ht (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩, hPx, hPy, ex, ey, hne⟩ =>
    ⟨σ₁, σ₂, v₁, v₂, pub, hk σ₁ x₀ x v₁ i₁ hPx ex hne, hk σ₂ y₀ y v₂ i₂ hPy ey
      (by rw [← he x₀ y₀ ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩]; exact hne)⟩) fun _ _ h => h) ?_
  rintro x y ⟨x₀, y₀, ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩, hPx, hPy, _, _, _⟩
  exact ⟨σ₁, σ₂, v₁, v₂, pub, (hT _ _ i₁).step hp v₁ hPx (tChk_nil p hp), (hT _ _ i₂).step hp v₂ hPy (tChk_nil p hp)⟩

/-! ## The hint -/

theorem S1.r15 {p : Params} {σ s : State} (h : S1 p σ s) :
    s.gpr .r15 = flag ((vHint p (vSig p σ)).isSome = true) := by
  unfold S1 at h
  obtain ⟨_, hm⟩ := h
  split at hm
  · rename_i _ hh; rw [hm.1, hh]; exact flag_congr (by simp)
  · rename_i hh; rw [hm, hh]; exact flag_congr (by simp)

theorem hint_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    RelCT isa (RV p fun σ s => T p σ s ∧ s.gpr .r15 = flag True) (hint P p) (RV p (S1 p)) := by
  have hc := hintChk_all p hp
  simp only [hintChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1, _⟩, c3⟩, c4⟩ := hc
  refine relInv (fun σ s hv hs => hint_ok C hp hv hs.1) ?_
  unfold hint
  refine RelCT.seq (hintUnpackAt_tr C.hintUnpack (layOk p hp) c3 c1 fun x y h => ?_)
    (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)
  have L := RV.lrel hp (fun _ _ h => h.1) h
  obtain ⟨σ₁, σ₂, _, _, pub, i₁, i₂⟩ := h
  exact ⟨L.1, L.2.1, L.2.2, by rw [i₁.1.sigSlice c4, i₂.1.sigSlice c4, pub.2.2.2.2.2.2.2.1]⟩

/-! ## `z` -/

/-- After `z[0], …, z[i - 1]`, with a well-formed hint. -/
def Iz (p : Params) (i : Nat) (σ s : State) : Prop := ∃ h, vHint p (vSig p σ) = some h ∧ S2 p h i σ s

theorem Iz.t {p : Params} {i : Nat} {σ s : State} (h : Iz p i σ s) : T p σ s :=
  let ⟨_, _, hs⟩ := h; hs.t

theorem zOne_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {i : Nat} (hi : i < p.ℓ) :
    RelCT isa (RV p (Iz p i)) (zOne P p i) (RV p (Iz p (i + 1))) := by
  have hc := zChk_all p hp i hi
  simp only [zChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, _⟩, _⟩, _⟩, _⟩, c8⟩, c9⟩ := hc
  refine relInv (fun σ s hv ⟨h, hh, hs⟩ => WP.mono (zOne_ok C hp hv hi hs) fun _ h' => ⟨h, hh, h'⟩) ?_
  unfold zOne
  refine RelCT.seq (relInv (I' := fun σ s => ∃ s₀, Iz p i σ s₀ ∧
      (PPostB s₀ s [(pZ i, 1024)] ∧ ∃ f, PolyIs s.mem (pa s₀ (pZ i)) f))
    (fun σ s hv hs => WP.mono (bitUnpackAt_ok C.bitUnpack (hs.t.lay hp hv) c2 c3 c1) fun _ ⟨hP, _, hq⟩ =>
      ⟨s, hs, hP, _, hq⟩)
    (bitUnpackAt_tr C.bitUnpack (layOk p hp) c2 c3 c1 fun x y h => RV.lrel hp (fun _ _ h => h.t) h)) ?_
  refine RelCT.seq (normLtAt_tr C.normLt (layOk p hp) c9 c8 fun x y h => ?_) and15_tr
  have L := RV.lrelStep hp (fun _ _ h => Iz.t h) (fun _ _ f => ⟨_, f.1⟩) h
  obtain ⟨_, _, _, _, _, ⟨x₀, _, fx, _, hx⟩, ⟨y₀, _, fy, _, hy⟩⟩ := h
  exact ⟨L.1, L.2.1, by rw [pa_rbx fx]; exact hx.1, by rw [pa_rbx fy]; exact hy.1, L.2.2⟩

theorem zs_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    RelCT isa (RV p (Iz p 0)) (seqR (zOne P p) 0 p.ℓ) (RV p (Iz p p.ℓ)) := by
  have := seqR_tr (R := fun i => RV p (Iz p i)) p.ℓ 0 fun i _ hi => zOne_tr C hp (by omega_using [hi])
  rwa [Nat.zero_add] at this

end VG.Proof.MlDsa.X86_64.Verify
