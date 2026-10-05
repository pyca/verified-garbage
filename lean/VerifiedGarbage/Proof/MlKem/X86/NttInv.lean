import VerifiedGarbage.Proof.MlKem.X86.Mul
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.NttSetup`. -/
section

/-!
# ML-KEM on x86 (32-bit): the start of `vg_mlkem_ntt` and `vg_mlkem_inv_ntt`

Both load `scratch` into `eax` (`ld_piece`), store the zeta table there, point
`ebp` at zeta `z`, and store `f + 1024` in the argument slot of `scratch`
(`setup_piece`), leaving `MemOK` with the input polynomial.
-/

namespace VG.Proof.MlKem.X86.NttLoop

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

theorem Pre.of {s₀ : State} {stk : Nat} {t : Poly → Poly}
    (h : (inPlaceContract X86.abi t stk).pre s₀) (hs : stk = 16) : VG.Proof.MlKem.X86.NttLoop.Pre s₀ := by
  subst hs
  sig_pre [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- After `ldScratch`. -/
structure S1 (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  eax : s.gpr .eax = VG.Proof.MlKem.X86.NttLoop.sP s₀

theorem ld_piece : Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlKem.X86.NttLoop.S1 (.block ldScratch) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₁ := P0_argAddr s₀ 1
    have i₁ := P0_argIn (s₀ := s₀) (n := 2) (i := 1) (by omega) fit (by simp [hp.wr])
    have v₁ := P0_arg hp.sp (n := 2) (i := 1) (by omega) fit (by
      simpa [← hp.stk_eq] using hp.stk_a)
    simp only [Nat.mul_one, Nat.reduceAdd] at a₁
    apply WP.of_runBlock
    simp only [ldScratch, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea,
      State.load32, State.setReg, Option.map_some, a₁, i₁, v₁, ite_true, Option.some.injEq,
      exists_eq_left']
    exact ⟨by simp, rfl, rfl, rfl, by simp⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', VG.Proof.MlKem.X86.NttLoop.pub_esp hq]

theorem arg01_sep {s₀ : State} (hp : VG.Proof.MlKem.X86.NttLoop.Pre s₀) : Mem.Sep (argAddr s₀ 0) 4 (argAddr s₀ 1) 4 := by
  have := hp.sp'
  intro x h₁ h₂
  simp only [argAddr, E0] at this h₁ h₂
  bv_omega

theorem setup_piece (z : Nat) {hh : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .eax]) (.block (nttSetup z)) hh).isSome = true) :
    Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub VG.Proof.MlKem.X86.NttLoop.S1 (fun s₀ s => LB s₀ (polyAt s₀.mem (VG.Proof.MlKem.X86.NttLoop.fA s₀)) z s) (.block (nttSetup z)) := by
  refine Piece.taint [.esp, .eax] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) ht
  · have fs := hp.s_fit
    have fit := hp.sp'
    rw [nttSetup]
    refine table_spec zetaTable (b := .eax) (by decide) (p := VG.Proof.MlKem.X86.NttLoop.sA s₀) _ s _
      (fun k hk => by
        show (s.gpr .eax + BitVec.ofNat 32 (4 * k)).setWidth 64 = _
        rw [h.eax, ea_off (by omega)])
      (fun k hk => hp.in_s h.wr (by omega)) fun s₁ o₁ f₁ c₁ => ?_
    have esp₁ : s₁.gpr .esp = (P0 s₀).gpr .esp := by rw [o₁.gpr .esp (by decide), h.esp]
    have eax₁ : s₁.gpr .eax = VG.Proof.MlKem.X86.NttLoop.sP s₀ := by rw [o₁.gpr .eax (by decide), h.eax]
    have wr₁ : s₁.wr = (P0 s₀).wr := o₁.wr.trans h.wr
    have rd₁ : s₁.rd = (P0 s₀).rd := o₁.rd.trans h.rd
    have a20 : (s₁.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 0 := by
      rw [esp₁]; exact P0_argAddr s₀ 0
    have a24 : (s₁.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by
      rw [esp₁]; exact P0_argAddr s₀ 1
    have in0 : InRegions (s₁.rd ++ s₁.wr) (argAddr s₀ 0) 4 := hp.in_a wr₁ (by decide)
    have in1 : InRegions s₁.wr (argAddr s₀ 1) 4 :=
      ⟨VG.Proof.MlKem.X86.NttLoop.aR s₀, by rw [wr₁, P0_wr, hp.wr]; simp, hp.arg_in (by decide)⟩
    have hsa : ∀ r ∈ [polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀)], (⟨argAddr s₀ 0, 4⟩ : Region).Disjoint r := by
      simp only [List.mem_singleton, forall_eq]
      exact (hp.s_a.symm.sub_left fun x hx => by
        have := hp.arg_in (i := 0) (by decide)
        simp only [Region.Contains] at hx this ⊢; omega)
    have v0 : s₁.mem.readW (argAddr s₀ 0) 32 = VG.Proof.MlKem.X86.NttLoop.fP s₀ := by
      rw [f₁.readW (Region.contains_self _ _) hsa (by decide), h.mem]
      exact P0_arg hp.sp (n := 2) (i := 0) (by omega) fit (by simpa [← hp.stk_eq] using hp.stk_a)
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.ea, at_, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a20, a24, in0, in1, v0, Option.some.injEq,
      exists_eq_left']
    have hs1 : Frame [polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀)] (P0 s₀).mem s₁.mem := h.mem ▸ f₁
    refine ⟨by simp [esp₁], rd₁, wr₁, by simp [eax₁], ?_, ?_, ?_, ?_, ?_⟩
    · exact (hs1.mono fun r hr => by simp at hr ⊢; exact .inr (.inl hr)).writeW (by simp) _
        (hp.arg_in (by decide))
    · intro k hk
      rw [coeffAt_writeW_sep _ _ _ (hp.s_a.sep (coeff_contains _ (by rw [n_eq]; omega)) (hp.arg_in (by decide))),
        c₁ k hk]
      rfl
    · rw [Mem.readW_writeW_sep (VG.Proof.MlKem.X86.NttLoop.arg01_sep hp) (by decide), v0]
    · exact Mem.readW_writeW_self32 _ _ _
    · have fr : Frame [frameR s₀, polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀), VG.Proof.MlKem.X86.NttLoop.aR s₀] s₀.mem
          (s₁.mem.writeW (argAddr s₀ 1) (VG.Proof.MlKem.X86.NttLoop.fP s₀ + 1024)) :=
        ((hp.P0_keep.mono (by simp)).trans (hs1.mono (by simp))).writeW (by simp) _ (hp.arg_in (by decide))
      refine polyIs_congr (fun k hk => bytes_frame fr (fun r hr => ?_) (by decide) k hk) ⟨hp.f_red, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [← hp.stk_eq]; exact hp.stk_f.symm
      · exact hp.f_s
      · exact hp.f_a
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.esp, h'.esp, VG.Proof.MlKem.X86.NttLoop.pub_esp hq]
    · rw [h.eax, h'.eax, VG.Proof.MlKem.X86.NttLoop.sP, VG.Proof.MlKem.X86.NttLoop.sP, hq.2.2]

end VG.Proof.MlKem.X86.NttLoop

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Ntt`. -/
section

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_ntt`

The seven layers of Algorithm 9 (`ntt_eq_layers`), each a `layer_piece`
(`NttLoop.lean`) of the butterfly `bflyBody` (`bfly_spec`), with the zetas
from `zetas[1]` up.
-/

namespace VG.Proof.MlKem.X86.NttFwd

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.NttLoop
open VG.Spec.MlKem

/-- The butterfly of Algorithm 9. -/
def bf : Bfly := ⟨bflyBody, bfly, bfly_spec⟩

/-- The zeta of block `c` of the layer with `len`. -/
def kf (len c : Nat) : Nat := 128 / len + c

theorem lay (len B : Nat) (hB : len * B = 128) (hBp : 0 < B) (hk : 128 / len + B ≤ 128) (P : State → Poly)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp 20))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr []) (.block (blockInit len)) h₂).isSome = true)
    {h₃ : Taint.Hint VG.X86.Taint.T}
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block bflyBody) h₃).isSome = true)
    {h₄ : Taint.Hint VG.X86.Taint.T}
    (t₄ : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd zUp)) h₄).isSome = true) :
    Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => LB s₀ (P s₀) (VG.Proof.MlKem.X86.NttFwd.kf len 0) s)
      (fun s₀ s => LB s₀ (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (P s₀) len B) (VG.Proof.MlKem.X86.NttFwd.kf len B) s) (layerCode bflyBody zUp len) :=
  layer_piece VG.Proof.MlKem.X86.NttFwd.bf VG.Proof.MlKem.X86.NttFwd.kf P true len B hB hBp (fun c _ => by simp [VG.Proof.MlKem.X86.NttFwd.kf]; omega) (fun c hc => by simp only [VG.Proof.MlKem.X86.NttFwd.kf]; omega)
    (fun h => absurd h (by decide)) t₁ t₂ t₃ t₄

/-- The input polynomial. -/
abbrev F (s₀ : State) : Poly := polyAt s₀.mem (VG.Proof.MlKem.X86.NttLoop.fA s₀)

theorem nil_piece {A : State → State → Prop} : Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub A A (.block []) :=
  Piece.taint [] (fun _ _ _ h => WP.block_nil_iff.mpr h) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)

theorem nttLayer_eq (f : Poly) (len : Nat) : nttLayer f len = layerN bfly VG.Proof.MlKem.X86.NttFwd.kf f len (128 / len) := rfl

theorem fold_eq (f : Poly) : nttLens.foldl nttLayer f =
    layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf
      (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf f 128 1) 64 2) 32 4) 16 8) 8 16) 4 32) 2 64 := by
  simp only [nttLens, List.foldl_cons, List.foldl_nil, VG.Proof.MlKem.X86.NttFwd.nttLayer_eq, Nat.reduceDiv]

theorem layers_piece : Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => LB s₀ (VG.Proof.MlKem.X86.NttFwd.F s₀) 1 s)
    (fun s₀ s => LB s₀ (nttLens.foldl nttLayer (VG.Proof.MlKem.X86.NttFwd.F s₀)) 128 s)
    (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2]) := by
  refine Piece.seq (VG.Proof.MlKem.X86.NttFwd.lay 128 1 (by decide) (by decide) (by decide) VG.Proof.MlKem.X86.NttFwd.F (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.NttFwd.lay 64 2 (by decide) (by decide) (by decide) (fun s₀ => layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (VG.Proof.MlKem.X86.NttFwd.F s₀) 128 1)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.NttFwd.lay 32 4 (by decide) (by decide) (by decide)
    (fun s₀ => layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (VG.Proof.MlKem.X86.NttFwd.F s₀) 128 1) 64 2)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.NttFwd.lay 16 8 (by decide) (by decide) (by decide)
    (fun s₀ => layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (VG.Proof.MlKem.X86.NttFwd.F s₀) 128 1) 64 2) 32 4)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.NttFwd.lay 8 16 (by decide) (by decide) (by decide)
    (fun s₀ => layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (VG.Proof.MlKem.X86.NttFwd.F s₀) 128 1) 64 2) 32 4) 16 8)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.NttFwd.lay 4 32 (by decide) (by decide) (by decide)
    (fun s₀ => layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (VG.Proof.MlKem.X86.NttFwd.F s₀) 128 1)
      64 2) 32 4) 16 8) 8 16)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.NttFwd.lay 2 64 (by decide) (by decide) (by decide)
    (fun s₀ => layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf
      (layerN bfly VG.Proof.MlKem.X86.NttFwd.kf (VG.Proof.MlKem.X86.NttFwd.F s₀) 128 1) 64 2) 32 4) 16 8) 8 16) 4 32)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact nil_piece.mono (fun _ _ _ h => h) fun s₀ _ _ h => by rw [VG.Proof.MlKem.X86.NttFwd.fold_eq]; exact h

theorem body_piece : Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => s = P0 s₀)
    (fun s₀ s => LB s₀ (nttLens.foldl nttLayer (VG.Proof.MlKem.X86.NttFwd.F s₀)) 128 s)
    (.seq (.block ldScratch) (.seq (.block (nttSetup 1)) (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2]))) :=
  Piece.seq VG.Proof.MlKem.X86.NttLoop.ld_piece (Piece.seq (VG.Proof.MlKem.X86.NttLoop.setup_piece 1 (by taint_decide)) VG.Proof.MlKem.X86.NttFwd.layers_piece)

/-- The regions the body writes. -/
abbrev W (s₀ : State) : List Region := [polyRegion (VG.Proof.MlKem.X86.NttLoop.fA s₀), polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀), VG.Proof.MlKem.X86.NttLoop.aR s₀]

theorem hW {s₀ : State} (hp : VG.Proof.MlKem.X86.NttLoop.Pre s₀) : ∀ r ∈ VG.Proof.MlKem.X86.NttFwd.W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by rw [← hp.stk_eq]; exact hp.stk_f, hp.ret_f⟩
  · exact ⟨by rw [← hp.stk_eq]; exact hp.stk_s, hp.ret_s⟩
  · exact ⟨by rw [← hp.stk_eq]; exact hp.stk_a, hp.ret_a⟩

theorem piece : Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => LB s₀ (nttLens.foldl nttLayer (VG.Proof.MlKem.X86.NttFwd.F s₀)) 128 s) s₀ s') Impl.MlKem.X86.ntt :=
  Piece.leaf VG.Proof.MlKem.X86.NttFwd.W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp => VG.Proof.MlKem.X86.NttFwd.hW hp) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.mem.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- Memory with the arguments `0` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 4 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.ntt (nttContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of (t := VG.Spec.MlKem.ntt) h rfl) fun s s' _ _ h => by
      sig_pub [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm, ntt_eq_layers]
    exact hinv.mem.poly
  · let st := satState VG.Proof.MlKem.X86.NttFwd.satMem [] [⟨0, 1024⟩, ⟨0x400, 1024⟩, ⟨0x5004, 8⟩]
    refine ⟨st, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg st 0) = BitVec.ofNat 64 0 by decide]
           refine reduced_below (fun a ha => ?_) 0 (by decide)
           simp only [VG.Proof.MlKem.X86.NttFwd.satMem]
           rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])
        | decide +kernel

end VG.Proof.MlKem.X86.NttFwd

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.NttInv`. -/
section

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_inv_ntt`

The seven layers of Algorithm 10 (`nttInv_eq_layers`), each a `layer_piece`
(`NttLoop.lean`) of the inverse butterfly `ibflyBody` (`ibfly_spec`), with the
zetas from `zetas[127]` down; then every coefficient times 3303 (`scaleBody`).
-/

namespace VG.Proof.MlKem.X86.NttInvP

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.NttLoop
open VG.Proof.MlKem.X86.NttFwd (F nil_piece W hW)
open VG.Spec.MlKem

/-- The butterfly of Algorithm 10. -/
def bf : Bfly := ⟨ibflyBody, bflyInv, ibfly_spec⟩

/-- The zeta of block `c` of the layer with `len`. -/
def kf (len c : Nat) : Nat := 256 / len - 1 - c

theorem lay (len B : Nat) (hB : len * B = 128) (hBp : 0 < B) (hk : 256 / len - 1 < 128)
    (hk1 : B + 1 ≤ 256 / len) (P : State → Poly)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp 20))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr []) (.block (blockInit len)) h₂).isSome = true)
    {h₃ : Taint.Hint VG.X86.Taint.T}
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block ibflyBody) h₃).isSome = true)
    {h₄ : Taint.Hint VG.X86.Taint.T}
    (t₄ : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd zDown)) h₄).isSome = true) :
    Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => LB s₀ (P s₀) (VG.Proof.MlKem.X86.NttInvP.kf len 0) s)
      (fun s₀ s => LB s₀ (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (P s₀) len B) (VG.Proof.MlKem.X86.NttInvP.kf len B) s) (layerCode ibflyBody zDown len) :=
  layer_piece VG.Proof.MlKem.X86.NttInvP.bf VG.Proof.MlKem.X86.NttInvP.kf P false len B hB hBp (fun c _ => by simp only [VG.Proof.MlKem.X86.NttInvP.kf, Bool.false_eq_true, ite_false]; omega)
    (fun c hc => by simp only [VG.Proof.MlKem.X86.NttInvP.kf]; omega) (fun _ c hc => by simp only [VG.Proof.MlKem.X86.NttInvP.kf]; omega) t₁ t₂ t₃ t₄

theorem nttInvLayer_eq (f : Poly) (len : Nat) :
    nttInvLayer f len = layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf f len (128 / len) := rfl

theorem fold_eq (f : Poly) : nttInvLens.foldl nttInvLayer f =
    layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf
      (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf f 2 64) 4 32) 8 16) 16 8) 32 4) 64 2) 128 1 := by
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil, VG.Proof.MlKem.X86.NttInvP.nttInvLayer_eq, Nat.reduceDiv]

theorem layers_piece : Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => LB s₀ (VG.Proof.MlKem.X86.NttFwd.F s₀) 127 s)
    (fun s₀ s => LB s₀ (nttInvLens.foldl nttInvLayer (VG.Proof.MlKem.X86.NttFwd.F s₀)) 0 s)
    (layers (layerCode ibflyBody zDown) [2, 4, 8, 16, 32, 64, 128]) := by
  refine Piece.seq (VG.Proof.MlKem.X86.NttInvP.lay 2 64 (by decide) (by decide) (by decide) (by decide) VG.Proof.MlKem.X86.NttFwd.F (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.NttInvP.lay 4 32 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (VG.Proof.MlKem.X86.NttFwd.F s₀) 2 64)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.NttInvP.lay 8 16 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (VG.Proof.MlKem.X86.NttFwd.F s₀) 2 64) 4 32)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.NttInvP.lay 16 8 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (VG.Proof.MlKem.X86.NttFwd.F s₀) 2 64) 4 32) 8 16)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.NttInvP.lay 32 4 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (VG.Proof.MlKem.X86.NttFwd.F s₀) 2 64)
      4 32) 8 16) 16 8)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.NttInvP.lay 64 2 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf
      (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (VG.Proof.MlKem.X86.NttFwd.F s₀) 2 64) 4 32) 8 16) 16 8) 32 4)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.NttInvP.lay 128 1 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf
      (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (layerN bflyInv VG.Proof.MlKem.X86.NttInvP.kf (VG.Proof.MlKem.X86.NttFwd.F s₀) 2 64) 4 32) 8 16) 16 8) 32 4) 64 2)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact nil_piece.mono (fun _ _ _ h => h) fun s₀ _ _ h => by rw [VG.Proof.MlKem.X86.NttInvP.fold_eq]; exact h

/-! ## The multiplication by 3303 -/

/-- `G` with its first `t` coefficients times 3303. -/
def scaled (G : Poly) (t : Nat) : Poly := Vector.ofFn fun i => if i.val < t then G[i.val]! * 3303 else G[i.val]!

theorem scaled_get (G : Poly) (t : Nat) {i : Nat} (hi : i < n) :
    (VG.Proof.MlKem.X86.NttInvP.scaled G t)[i]! = if i < t then G[i]! * 3303 else G[i]! := by
  rw [getElem!_eq _ hi, VG.Proof.MlKem.X86.NttInvP.scaled, Vector.getElem_ofFn]

theorem scaled_zero (G : Poly) : VG.Proof.MlKem.X86.NttInvP.scaled G 0 = G :=
  ext_getElem! fun i hi => by rw [VG.Proof.MlKem.X86.NttInvP.scaled_get _ _ hi, ite_eq_right (Nat.not_lt_zero i)]

theorem scaled_succ (G : Poly) (t : Nat) :
    VG.Proof.MlKem.X86.NttInvP.scaled G (t + 1) = (VG.Proof.MlKem.X86.NttInvP.scaled G t).set! t (G[t]! * 3303) :=
  ext_getElem! fun i hi => by
    rw [VG.Proof.MlKem.X86.NttInvP.scaled_get _ _ hi]
    by_cases e : t = i
    · subst e; rw [getElem!_set!_self _ hi, ite_eq_left (by omega)]
    · rw [getElem!_set!_ne _ hi e, VG.Proof.MlKem.X86.NttInvP.scaled_get _ _ hi]
      by_cases h : i < t
      · rw [ite_eq_left (by omega), ite_eq_left h]
      · rw [ite_eq_right (by omega), ite_eq_right h]

theorem scaled_all (G : Poly) : VG.Proof.MlKem.X86.NttInvP.scaled G 256 = G.map (· * 3303) :=
  ext_getElem! fun i hi => by rw [VG.Proof.MlKem.X86.NttInvP.scaled_get _ _ hi, ite_eq_left (by rw [n_eq] at hi; exact hi), map_mul_get _ hi]

/-- After `t` coefficients. -/
structure SI (s₀ : State) (G : Poly) (t : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = VG.Proof.MlKem.X86.NttLoop.fP s₀ + BitVec.ofNat 32 (4 * t)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - t)
  frame : Frame [polyRegion (VG.Proof.MlKem.X86.NttLoop.fA s₀), polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀), VG.Proof.MlKem.X86.NttLoop.aR s₀] (P0 s₀).mem s.mem
  poly : PolyIs s.mem (VG.Proof.MlKem.X86.NttLoop.fA s₀) (VG.Proof.MlKem.X86.NttInvP.scaled G t)

theorem scale_step {s₀ : State} (hp : VG.Proof.MlKem.X86.NttLoop.Pre s₀) {G : Poly} {t : Nat} (ht : t < 256) {s : State}
    (h : VG.Proof.MlKem.X86.NttInvP.SI s₀ G t s) :
    WP isa (.block scaleBody) s fun s' => VG.Proof.MlKem.X86.NttInvP.SI s₀ G (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < 256)) := by
  have ff := hp.f_fit
  have ht' : t < n := by rw [n_eq]; exact ht
  have ea : (s.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (VG.Proof.MlKem.X86.NttLoop.fA s₀) t := by
    rw [h.esi, ea_add (by omega), Nat.add_zero]
  have inF := hp.in_f h.wr ht
  have ha := polyIs_coeffAt h.poly ht'
  rw [coeffAt_eq] at ha
  have la := val_lt (VG.Proof.MlKem.X86.NttInvP.scaled G t)[t]!
  generalize ea' : (VG.Proof.MlKem.X86.NttInvP.scaled G t)[t]!.val = a at ha la
  have ha' : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 (by omega)
  rw [scaleBody]
  refine wp_movm (by rw [State.ea, at_, ea]; exact inRd inF) (wp_cons rfl (wp_mul (wp_movr
    (red_spec (r := .ebx) (by decide) (by decide) _ _ _ (x := a * 3303) ?_ ?_ fun s₂ o₂ v₂ => ?_))))
  · simp only [State.setReg, execMul_eax, ite_true, ite_false, State.ea, at_, ea, ha, reduceCtorEq]
    simp only [ha', show (3303 : BitVec 32).toNat = 3303 from rfl]
    exact toNat_ofNat32 (by omega)
  · simp only [State.setReg, execMul_eax, ite_true, ite_false, State.ea, at_, ea, ha, reduceCtorEq]
    simp only [ha', show (3303 : BitVec 32).toNat = 3303 from rfl]
    exact toNat_ofNat32 (by omega)
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3])]
    simp only [State.setReg, h3, ite_false]
    rw [execMul_other _ _ h1 h2]
    simp only [h1, h2, ite_false]
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have ecx₂ := g₂ .ecx (by decide) (by decide) (by decide)
  have esp₂ := g₂ .esp (by decide) (by decide) (by decide)
  have m₂ : s₂.mem = s.mem := o₂.mem
  have wr₂ : s₂.wr = s.wr := o₂.wr
  have bx₂ : s₂.gpr .ebx = BitVec.ofNat 32 (a * 3303 % q) := eq_ofNat_of_toNat v₂
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    esi₂, ecx₂, m₂, wr₂, bx₂, ea, inF, Option.some.injEq, exists_eq_left']
  have hv : BitVec.ofNat 32 (a * 3303 % q) = BitVec.ofNat 32 ((G[t]! * 3303).val) := by
    rw [← ea', VG.Proof.MlKem.X86.NttInvP.scaled_get _ _ ht', ite_eq_right (Nat.lt_irrefl t), val_mul]
    rfl
  refine ⟨⟨by simp [esp₂, h.esp], o₂.rd.trans h.rd, h.wr, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, ite_false, ite_true, h.esi]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx]
    exact cnt_next ht
  · exact h.frame.writeW (by simp) _ (coeff_contains _ ht')
  · rw [hv, VG.Proof.MlKem.X86.NttInvP.scaled_succ]
    exact polyIs_writeW h.poly ht' _
  · simp only [eval, h.ecx]
    exact cnt_ne ht (by omega)

/-- The polynomial after the layers. -/
abbrev G (s₀ : State) : Poly := nttInvLens.foldl nttInvLayer (VG.Proof.MlKem.X86.NttFwd.F s₀)

/-- `esi` at `f`, the layers done. -/
structure SA (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = VG.Proof.MlKem.X86.NttLoop.fP s₀
  frame : Frame [polyRegion (VG.Proof.MlKem.X86.NttLoop.fA s₀), polyRegion (VG.Proof.MlKem.X86.NttLoop.sA s₀), VG.Proof.MlKem.X86.NttLoop.aR s₀] (P0 s₀).mem s.mem
  poly : PolyIs s.mem (VG.Proof.MlKem.X86.NttLoop.fA s₀) (VG.Proof.MlKem.X86.NttInvP.G s₀)

theorem esi_piece : Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => LB s₀ (VG.Proof.MlKem.X86.NttInvP.G s₀) 0 s) VG.Proof.MlKem.X86.NttInvP.SA (.block [.mov .esi (.mem (at_ .esp 20))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have hsl : (s.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 0 := by
      rw [h.esp]; exact P0_argAddr s₀ 0
    have ins : InRegions (s.rd ++ s.wr) (argAddr s₀ 0) 4 := hp.in_a h.wr (by decide)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
      State.ea, at_, State.load32, hsl, ins, h.mem.arg0, ite_true, Option.some.injEq, exists_eq_left']
    exact ⟨by simp [h.esp], h.rd, h.wr, by simp, h.mem.frame, h.mem.poly⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, VG.Proof.MlKem.X86.NttLoop.pub_esp hq]

theorem ecx_piece : Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub VG.Proof.MlKem.X86.NttInvP.SA (fun s₀ s => VG.Proof.MlKem.X86.NttInvP.SI s₀ (VG.Proof.MlKem.X86.NttInvP.G s₀) 0 s) (.block [.mov .ecx (.imm 256)]) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
    Option.some.injEq, exists_eq_left']
  exact ⟨by simp [h.esp], h.rd, h.wr, by simp [h.esi], by simp, h.frame, by rw [VG.Proof.MlKem.X86.NttInvP.scaled_zero]; exact h.poly⟩

theorem scale_piece : Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => VG.Proof.MlKem.X86.NttInvP.SI s₀ (VG.Proof.MlKem.X86.NttInvP.G s₀) 0 s) (fun s₀ s => VG.Proof.MlKem.X86.NttInvP.SI s₀ (VG.Proof.MlKem.X86.NttInvP.G s₀) 256 s)
    (.loop (.block scaleBody) .ne) :=
  Piece.countLoop (by decide) (fun t s₀ s => VG.Proof.MlKem.X86.NttInvP.SI s₀ (VG.Proof.MlKem.X86.NttInvP.G s₀) t s) [.esp, .esi, .ecx]
    (fun t ht s₀ s hp h => VG.Proof.MlKem.X86.NttInvP.scale_step hp ht h)
    (fun t _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.esp, h'.esp, VG.Proof.MlKem.X86.NttLoop.pub_esp hq]
      · rw [h.esi, h'.esi, VG.Proof.MlKem.X86.NttLoop.fP, VG.Proof.MlKem.X86.NttLoop.fP, hq.2.1]
      · rw [h.ecx, h'.ecx]) (by taint_decide)

theorem body_piece : Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => s = P0 s₀) (fun s₀ s => VG.Proof.MlKem.X86.NttInvP.SI s₀ (VG.Proof.MlKem.X86.NttInvP.G s₀) 256 s)
    (.seq (.block ldScratch) (.seq (.block (nttSetup 127))
      (.seq (layers (layerCode ibflyBody zDown) [2, 4, 8, 16, 32, 64, 128])
        (.seq (.block [.mov .esi (.mem (at_ .esp 20))])
          (.seq (.block [.mov .ecx (.imm 256)]) (.loop (.block scaleBody) .ne)))))) :=
  Piece.seq VG.Proof.MlKem.X86.NttLoop.ld_piece (Piece.seq (VG.Proof.MlKem.X86.NttLoop.setup_piece 127 (by taint_decide)) (Piece.seq VG.Proof.MlKem.X86.NttInvP.layers_piece
    (Piece.seq VG.Proof.MlKem.X86.NttInvP.esi_piece (Piece.seq VG.Proof.MlKem.X86.NttInvP.ecx_piece VG.Proof.MlKem.X86.NttInvP.scale_piece))))

theorem piece : Piece VG.Proof.MlKem.X86.NttLoop.Pre VG.Proof.MlKem.X86.NttLoop.Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => VG.Proof.MlKem.X86.NttInvP.SI s₀ (VG.Proof.MlKem.X86.NttInvP.G s₀) 256 s) s₀ s') Impl.MlKem.X86.nttInv :=
  Piece.leaf VG.Proof.MlKem.X86.NttFwd.W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp => VG.Proof.MlKem.X86.NttFwd.hW hp) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem verified : Verified X86.target Impl.MlKem.X86.nttInv (nttInvContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of (t := VG.Spec.MlKem.nttInv) h rfl)
      fun s s' _ _ h => by
        sig_pub [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes] at h
        exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    rw [hm, nttInv_eq_layers, ← VG.Proof.MlKem.X86.NttInvP.scaled_all]
    exact hinv.poly
  · let st := satState NttFwd.satMem [] [⟨0, 1024⟩, ⟨0x400, 1024⟩, ⟨0x5004, 8⟩]
    refine ⟨st, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg st 0) = BitVec.ofNat 64 0 by decide]
           refine reduced_below (fun a ha => ?_) 0 (by decide)
           simp only [NttFwd.satMem]
           rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])
        | decide +kernel

end VG.Proof.MlKem.X86.NttInvP

end
