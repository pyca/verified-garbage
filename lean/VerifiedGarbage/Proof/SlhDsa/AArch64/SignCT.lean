module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignBody
public import VerifiedGarbage.Proof.SlhDsa.AArch64.KeyGenCT
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.SignBody
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.KeyGenCT
public meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint

/-!
# SLH-DSA (SHAKE) on AArch64, `sign`: constant time

The blocks by the taint analysis, from the registers that hold the same
public values in both runs (`ct_*`); the hashes by `hashM_ct`, the calls of
`forsSign` and `xmssTree` by their contracts (`RelCT.call`), whose public
data are pointers; each from the states the correctness proofs describe
(`KeyGen.relSeq`). Then `sign_verified`, against `signContract`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Sign

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.KeyGen (Shake6 taintR relSeq)

section
variable {P : State → State → Prop}

theorem ct_pro {p : Params} (hp : Shake6 p)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], x.gpr r = y.gpr r) :
    RelCT isa P (.block (proCode p)) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_fblock {p : Params} (hp : Shake6 p)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19, .x25], x.gpr r = y.gpr r) :
    RelCT isa P (.block (fblock p)) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_init {p : Params} (hp : Shake6 p)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x25], x.gpr r = y.gpr r) :
    RelCT isa P (.block (([.movz .x .x21 0 0] : List Instr) ++ Impl.SlhDsa.AArch64.lea .x20 .x25 (p.n + p.forsSigLen)))
      fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_lblock {p : Params} (hp : Shake6 p)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19, .x20, .x21], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.Shake.treeLanes p .x21 .x22 ++
      ([Impl.SlhDsa.AArch64.Thash4.mov .x0 .x19, Impl.SlhDsa.AArch64.Thash4.mov .x1 .x23,
        Impl.SlhDsa.AArch64.Thash4.mov .x2 .x20] : List Instr))) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_next {p : Params} (hp : Shake6 p)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x20, .x21], x.gpr r = y.gpr r) :
    RelCT isa P (.block (([.addImm .x .x20 .x20 p.xmssSigLen] : List Instr) ++ Impl.SlhDsa.AArch64.movV .x11 (2 ^ p.hp - 1) ++
      ([.logic .and .x .x23 .x22 .x11, .lsr .x .x22 .x22 p.hp, .addImm .x .x21 .x21 1, .subImm .x .x9 .x21 p.d] :
        List Instr))) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_epi (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.restoreRegsAt Layout.oTop Impl.SlhDsa.AArch64.Shake.topSaved ++
      ([.movz .x .x0 1 0] : List Instr))) fun _ _ => True :=
  taintR _ hr (by taint_decide)

theorem ct_lsr (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x4], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.lsr .x .x9 .x4 8]) fun _ _ => True :=
  taintR _ hr (by taint_decide)

theorem ct_ret2 (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r) :
    RelCT isa P (.block [.movz .x .x0 2 0]) fun _ _ => True :=
  taintR _ hr (by taint_decide)

end

/-! ## The layers -/

open VG.Proof.SlhDsa.X86_64.SignTop (hsFold)
open VG.Proof.MlKem.AArch64 (Only)
open VG.Impl.SlhDsa.AArch64.Shake (Arg)

/-- What two runs share: the pointers and lengths, and `sp`. -/
structure PubE (σ₁ σ₂ : State) : Prop where
  regs : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r
  sp : σ₁.sp = σ₂.sp

/-- Before a layer's call. -/
structure LB (p : Params) (σ : State) (j : Nat) (u : State) : Prop where
  ctx : Ctx p σ u
  env : ∃ pk a16, Env p u.mem (σ.gpr .x7) pk a16
  x0 : u.gpr .x0 = σ.gpr .x7
  x1 : (u.gpr .x1).toNat < 2 ^ 32
  x2 : u.gpr .x2 = σ.gpr .x6 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)
  x20 : u.gpr .x20 = σ.gpr .x6 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)
  x21 : u.gpr .x21 = BitVec.ofNat 64 j

theorem lb_wp {p : Params} (hP : LP p) {σ t : State} (hK : SG p σ) {pre M₀ : List Byte} {T₀ I₀ j : Nat}
    (hI : I₀ < 2 ^ p.hp) (hj : j < p.d) (hL : LI p σ pre M₀ T₀ I₀ j t) :
    WP isa (.block (Impl.SlhDsa.AArch64.Shake.treeLanes p .x21 .x22 ++
      ([Impl.SlhDsa.AArch64.Thash4.mov .x0 .x19, Impl.SlhDsa.AArch64.Thash4.mov .x1 .x23,
        Impl.SlhDsa.AArch64.Thash4.mov .x2 .x20] : List Instr))) t (LB p σ j) := by
  have hd := hP.d22
  have hpow : 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hP.hp9
  have hI' := X86_64.SignTop.hsFold_leaf p (M := M₀) (skSeed := chunk (skB p σ) p.n 0)
    (pkSeed := chunk (skB p σ) p.n 2) (idxTree := T₀) hI j
  obtain ⟨a, he⟩ := hL.env
  exact lblock_ok hP.sz hK hL.ctx he (by rw [hL.x21, BitVec.toNat_ofNat]; omega)
    fun u hcu heu hgu h0 h1 h2 _ => ⟨hcu, ⟨_, _, heu⟩, h0, by rw [h1, hL.x23, BitVec.toNat_ofNat]; omega,
      by rw [h2, hL.x20], by rw [hgu .x20 (by decide), hL.x20], by rw [hgu .x21 (by decide), hL.x21]⟩

/-- After a layer's call. -/
structure LC (p : Params) (σ : State) (j : Nat) (u : State) : Prop where
  sp : u.sp = σ.sp
  x20 : u.gpr .x20 = σ.gpr .x6 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)
  x21 : u.gpr .x21 = BitVec.ofNat 64 j

theorem layer_ct {p : Params} (hS : Shake6 p) (hP : LP p) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true)
    {σ₁ σ₂ : State} (hK₁ : SG p σ₁) (hK₂ : SG p σ₂) (hE : PubE σ₁ σ₂)
    {pre₁ M₁ pre₂ M₂ : List Byte} {T₁ I₁ T₂ I₂ j : Nat} (hI₁ : I₁ < 2 ^ p.hp) (hI₂ : I₂ < 2 ^ p.hp)
    (hj : j < p.d) :
    RelCT isa (fun a b => LI p σ₁ pre₁ M₁ T₁ I₁ j a ∧ LI p σ₂ pre₂ M₂ T₂ I₂ j b)
      (Impl.SlhDsa.AArch64.Shake.layerBody p f) fun _ _ => True := by
  have hsl := hP.sigLt
  have hoff : p.n + p.forsSigLen + j * p.xmssSigLen + p.xmssSigLen ≤ p.sigLen := by
    rw [hP.sigLen]; have := Nat.mul_le_mul_right p.xmssSigLen (show j + 1 ≤ p.d by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have e6 : σ₁.gpr .x6 = σ₂.gpr .x6 := hE.regs .x6 (by decide)
  have e7 : σ₁.gpr .x7 = σ₂.gpr .x7 := hE.regs .x7 (by decide)
  unfold Impl.SlhDsa.AArch64.Shake.layerBody
  refine relSeq (ct_lblock hS fun x y ⟨hx', hy'⟩ => ⟨by rw [hx'.ctx.sp, hy'.ctx.sp, hE.sp], fun r hr => ?_⟩)
    (fun a ha => lb_wp hP hK₁ hI₁ hj ha) (fun b hb => lb_wp hP hK₂ hI₂ hj hb) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hx'.ctx.x19, hy'.ctx.x19, e7]
    · rw [hx'.x20, hy'.x20, e6]
    · rw [hx'.x21, hy'.x21]
  have cwp : ∀ {σ : State}, SG p σ → ∀ u, LB p σ j u →
      WP isa (.call f.xmssName (Impl.SlhDsa.AArch64.Shake.xmssCode p f)) u (LC p σ j) := fun hK u hu => by
    obtain ⟨pk, a, he⟩ := hu.env
    exact xmssCall_ok hP.sz hsl hx hxn hK hu.ctx hu.x0 hu.x1 hu.x2 hoff hP.xpos he
      fun s' hcs hpres _ _ _ _ => ⟨hcs.sp, by rw [hpres .x20 (by decide) (by decide), hu.x20],
        by rw [hpres .x21 (by decide) (by decide), hu.x21]⟩
  refine relSeq (RelCT.call hx.1 hx.2.1 [] [⟨σ₁.gpr .x7, scratchLen⟩,
      ⟨σ₁.gpr .x6 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen), p.xmssSigLen⟩] fun a b ⟨ha, hb⟩ => ?_)
    (cwp hK₁) (cwp hK₂) (ct_next hS fun x y ⟨hx', hy'⟩ => ⟨by rw [hx'.sp, hy'.sp, hE.sp], fun r hr => ?_⟩)
  · obtain ⟨pk₁, a₁, he₁⟩ := ha.env
    obtain ⟨pk₂, a₂, he₂⟩ := hb.env
    obtain ⟨q₁, c₁, w₁⟩ := xmss_pre hsl hK₁ ha.ctx ha.x0 ha.x1 ha.x2 hoff hP.xpos he₁
    obtain ⟨q₂, c₂, w₂⟩ := xmss_pre hsl hK₂ hb.ctx hb.x0 hb.x1 hb.x2 hoff hP.xpos he₂
    rw [← e6, ← e7] at q₂ c₂ w₂
    refine ⟨q₁, q₂, ?_, c₁, w₁, c₂, w₂⟩
    simp only [xmssContract, State.withRegions_gpr]
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
      State.callEntry_gpr _ (by decide), ha.x0, hb.x0, ha.x2, hb.x2, e6, e7]
    exact ⟨rfl, rfl, by simp only [State.withRegions, State.callEntry]; rw [ha.ctx.sp, hb.ctx.sp, hE.sp]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx'.x20, hy'.x20, e6]
    · rw [hx'.x21, hy'.x21]

theorem loop_ct {p : Params} (hS : Shake6 p) (hP : LP p) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true) (hd1 : 1 ≤ p.d)
    {σ₁ σ₂ : State} (hK₁ : SG p σ₁) (hK₂ : SG p σ₂) (hE : PubE σ₁ σ₂)
    {pre₁ M₁ pre₂ M₂ : List Byte} {T₁ I₁ T₂ I₂ : Nat} (hT₁ : T₁ < 2 ^ 64) (hT₂ : T₂ < 2 ^ 64)
    (hI₁ : I₁ < 2 ^ p.hp) (hI₂ : I₂ < 2 ^ p.hp) :
    RelCT isa (fun a b => LI p σ₁ pre₁ M₁ T₁ I₁ 0 a ∧ LI p σ₂ pre₂ M₂ T₂ I₂ 0 b)
      (.loop (Impl.SlhDsa.AArch64.Shake.layerBody p f) (.nonzero .x .x9)) fun _ _ => True := by
  have hd := hP.d22
  refine RelCT.mono (RelCT.loop (I := fun n a b => ∃ j, j < p.d ∧ n = p.d - j ∧
      LI p σ₁ pre₁ M₁ T₁ I₁ j a ∧ LI p σ₂ pre₂ M₂ T₂ I₂ j b) (fun n => RelCT.exists_ fun j => ?_) p.d)
    (fun a b ⟨h₁, h₂⟩ => ⟨0, by omega, by omega, h₁, h₂⟩) fun _ _ h => h
  by_cases hjn : j < p.d ∧ n = p.d - j
  · obtain ⟨hj, hn⟩ := hjn
    refine RelCT.mono (RelCT.wp (layer_ct hS hP hx hxn hK₁ hK₂ hE hI₁ hI₂ hj) (F₁ := fun (w : State) =>
        LI p σ₁ pre₁ M₁ T₁ I₁ (j + 1) w ∧ w.gpr .x9 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 p.d)
      (F₂ := fun (w : State) => LI p σ₂ pre₂ M₂ T₂ I₂ (j + 1) w ∧ w.gpr .x9 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 p.d)
      fun a b ⟨ha, hb⟩ => ⟨layer_ok hP hx hxn hK₁ hT₁ hI₁ hj ha, layer_ok hP hx hxn hK₂ hT₂ hI₂ hj hb⟩)
      (fun a b h => ⟨h.2.2.1, h.2.2.2⟩) fun a b ⟨_, ⟨ha, h9a⟩, ⟨hb, h9b⟩⟩ => ?_
    rw [MlKem.AArch64.eval_nonzero, MlKem.AArch64.eval_nonzero, h9a, h9b]
    refine ⟨rfl, fun _ => trivial, fun h => ⟨p.d - (j + 1), ?_, j + 1, ?_, rfl, ha, hb⟩⟩ <;>
    · by_cases e : j + 1 = p.d
      · rw [e, BitVec.sub_self] at h; simp at h
      · omega
  · exact RelCT.of_false fun a b ⟨h, h', _⟩ => hjn ⟨h, h'⟩

/-! ## The body -/

theorem notx9 : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], r ∉ [Reg.x9] := by decide

theorem body_ct {p : Params} (hS : Shake6 p) (hp : VG.Proof.SlhDsa.X86_64.VerifyTop.VPar p) (hP : LP p)
    {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (v : Proof.Sha3.AArch64.Permutation) (hv : f.keccak = v.callee)
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true)
    (hf : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.forsCode p f) (forsContract p))
    (hfn : (Impl.SlhDsa.AArch64.Shake.forsCode p f).noFrames = true)
    {σ₁ σ₂ : State} (hK₁ : SG p σ₁) (hK₂ : SG p σ₂) (hE : PubE σ₁ σ₂)
    (h4₁ : (σ₁.gpr .x4).toNat < 256) (h4₂ : (σ₂.gpr .x4).toNat < 256) :
    RelCT isa (fun a b => Only [.x9] σ₁ a ∧ Only [.x9] σ₂ b) (Impl.SlhDsa.AArch64.Shake.signBody p f)
      fun _ _ => True := by
  have hz := hP.sz
  have hn := hz.n32
  have hsl := hP.sigLt
  have hfsl : p.n + p.forsSigLen ≤ p.sigLen := by rw [hP.sigLen]; omega
  have e : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r := hE.regs
  have e6 := e .x6 (by decide)
  have e7 := e .x7 (by decide)
  rw [signBody_eq]
  -- the first block
  refine relSeq (ct_pro hS fun x y ⟨hx', hy'⟩ => ⟨by rw [hx'.sp, hy'.sp, hE.sp], fun r hr => by
      rw [hx'.get r (notx9 r hr), hy'.get r (notx9 r hr), e r hr]⟩)
    (fun a ha => pro_ok hz hK₁ h4₁ ha) (fun b hb => pro_ok hz hK₂ h4₂ hb) ?_
  -- `R`
  have hpub : ∀ {a b : State}, Ctx p σ₁ a → HRegs σ₁ a → Ctx p σ₂ b → HRegs σ₂ b → ∀ (xs : List Arg) (dst : Arg),
      (∀ x ∈ xs, argVal a x = argVal b x) → argVal a dst = argVal b dst → HashPub a b xs dst :=
    fun ca ra cb rb xs dst hx hd => ⟨by rw [ca.sp, cb.sp, hE.sp], by rw [ra.x20, rb.x20, e .x1 (by decide)],
      by rw [ra.x21, rb.x21, e .x2 (by decide)], by rw [ra.x22, rb.x22, e .x3 (by decide)],
      by rw [ra.x23, rb.x23, e .x4 (by decide)], hx, hd⟩
  have hscr : ∀ {a b : State}, Ctx p σ₁ a → Ctx p σ₂ b → ∀ o, argVal a (.scr o) = argVal b (.scr o) :=
    fun ca cb o => by simp only [argVal, ca.x19, cb.x19, e7]
  refine relSeq (hashM_ct p hn v hv (S := σ₁.gpr .x7) fun a b ⟨⟨ca, ra⟩, ⟨cb, rb⟩⟩ =>
      ⟨hashInR hz hK₁ ca ra, by rw [e7]; exact hashInR hz hK₂ cb rb, hpub ca ra cb rb _ _ (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact hscr ca cb _
        · show a.gpr .x24 = b.gpr .x24; rw [ra.x24, rb.x24, e .x5 (by decide)])
        (by show a.gpr .x25 = b.gpr .x25; rw [ra.x25, rb.x25, e6])⟩)
    (fun a ⟨ca, ra⟩ => hashR_ok hz v hv hK₁ ca ra) (fun b ⟨cb, rb⟩ => hashR_ok hz v hv hK₂ cb rb) ?_
  -- the digest
  refine relSeq (hashM_ct p hn v hv (S := σ₁.gpr .x7) fun a b ⟨⟨ca, ra, _⟩, ⟨cb, rb, _⟩⟩ =>
      ⟨hashInD hz hp.m64 hK₁ ca ra, by rw [e7]; exact hashInD hz hp.m64 hK₂ cb rb, hpub ca ra cb rb _ _ (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · show a.gpr .x25 = b.gpr .x25; rw [ra.x25, rb.x25, e6]
        · exact hscr ca cb _
        · exact hscr ca cb _) (hscr ca cb _)⟩)
    (fun a ⟨ca, ra, Ra⟩ => hashD_ok hz hp.m64 v hv hK₁ ca ra Ra)
    (fun b ⟨cb, rb, Rb⟩ => hashD_ok hz hp.m64 v hv hK₂ cb rb Rb) ?_
  -- the indices and the lanes
  refine relSeq (ct_fblock hS fun x y ⟨⟨cx, rx, _⟩, ⟨cy, ry, _⟩⟩ => ⟨by rw [cx.sp, cy.sp, hE.sp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [cx.x19, cy.x19, e7]
      · rw [rx.x25, ry.x25, e6]⟩)
    (fun a ⟨ca, ra, Ra, Da⟩ => fblock_ok hp hK₁ ca ra Ra Da) (fun b ⟨cb, rb, Rb, Db⟩ => fblock_ok hp hK₂ cb rb Rb Db) ?_
  -- FORS
  have hI₁ := Iv_lt hp σ₁
  have hI₂ := Iv_lt hp σ₂
  have hpow : 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hP.hp9
  refine relSeq (RelCT.call hf.1 hf.2.1 [] [⟨σ₁.gpr .x7, scratchLen⟩,
      ⟨σ₁.gpr .x6 + BitVec.ofNat 64 p.n, p.forsSigLen⟩] fun a b ⟨ha, hb⟩ => ?_)
    (fun a ha => fors_ok hp hP hf hfn hK₁ ha) (fun b hb => fors_ok hp hP hf hfn hK₂ hb) ?_
  · obtain ⟨q₁, c₁, w₁⟩ := fors_pre hsl hK₁ ha.ctx ha.x0 (by rw [ha.x2, BitVec.toNat_ofNat]; omega) ha.x1
      (by omega) hp.fpos ha.env
    obtain ⟨q₂, c₂, w₂⟩ := fors_pre hsl hK₂ hb.ctx hb.x0 (by rw [hb.x2, BitVec.toNat_ofNat]; omega) hb.x1
      (by omega) hp.fpos hb.env
    rw [← e6, ← e7] at q₂ c₂ w₂
    refine ⟨q₁, q₂, ?_, c₁, w₁, c₂, w₂⟩
    simp only [forsContract, State.withRegions_gpr]
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
      State.callEntry_gpr _ (by decide), ha.x0, hb.x0, ha.x1, hb.x1, e6, e7]
    exact ⟨rfl, rfl, by simp only [State.withRegions, State.callEntry]; rw [ha.ctx.sp, hb.ctx.sp, hE.sp]⟩
  -- the layers
  refine relSeq (ct_init hS fun x y ⟨hx', hy'⟩ => ⟨by rw [hx'.ctx.sp, hy'.ctx.sp, hE.sp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hx'.x25, hy'.x25, e6]⟩)
    (fun a ha => init_wp hP hK₁ ha) (fun b hb => init_wp hP hK₂ hb) ?_
  refine relSeq (loop_ct hS hP hx hxn hp.d1 hK₁ hK₂ hE (Tv_lt hp σ₁) (Tv_lt hp σ₂) hI₁ hI₂)
    (fun a ha => loop_ok hP hx hxn hp.d1 hK₁ (Tv_lt hp σ₁) hI₁ ha)
    (fun b hb => loop_ok hP hx hxn hp.d1 hK₂ (Tv_lt hp σ₂) hI₂ hb) ?_
  exact ct_epi fun x y ⟨hx', hy'⟩ => ⟨by rw [hx'.ctx.sp, hy'.ctx.sp, hE.sp], fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [hx'.ctx.x19, hy'.ctx.x19, e7]⟩

/-! ## The function -/

theorem lsr_wp (σ : State) : WP isa (.block [.lsr .x .x9 .x4 8]) σ fun s =>
    Only [.x9] σ s ∧ s.gpr .x9 = σ.gpr .x4 >>> 8 :=
  MlKem.AArch64.wp_lsr (by decide) fun s o e => MlKem.AArch64.wp_nil ⟨o, e⟩

/-- `sign` is constant time: its timing depends only on the pointers and the lengths. -/
theorem sign_ct {p : Params} (hS : Shake6 p) (hp : VG.Proof.SlhDsa.X86_64.VerifyTop.VPar p) (hP : LP p)
    {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (v : Proof.Sha3.AArch64.Permutation) (hv : f.keccak = v.callee)
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true)
    (hf : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.forsCode p f) (forsContract p))
    (hfn : (Impl.SlhDsa.AArch64.Shake.forsCode p f).noFrames = true) :
    ConstantTime isa (sgK p).pre (sgK p).pub (Impl.SlhDsa.AArch64.Shake.sign p f) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, psp⟩ := hpub
  have hK₁ : SG p s₁ := h₁
  have hK₂ : SG p s₂ := h₂
  have hE : PubE s₁ s₂ := ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption, psp⟩
  have hct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (Impl.SlhDsa.AArch64.Shake.sign p f) fun _ _ => True := by
    unfold Impl.SlhDsa.AArch64.Shake.sign
    refine relSeq (ct_lsr fun x y ⟨hx', hy'⟩ => ⟨by rw [hx', hy', psp], fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hx', hy', p4]⟩)
      (fun a ha => by rw [ha]; exact lsr_wp s₁) (fun b hb => by rw [hb]; exact lsr_wp s₂) ?_
    refine RelCT.ite (fun a b ⟨⟨_, ha⟩, ⟨_, hb⟩⟩ => by rw [MlKem.AArch64.eval_nonzero, MlKem.AArch64.eval_nonzero, ha, hb, p4])
      (ct_ret2 fun x y ⟨⟨⟨ox, _⟩, ⟨oy, _⟩⟩, _⟩ => ⟨by rw [ox.sp, oy.sp, psp], fun _ h => absurd h List.not_mem_nil⟩) ?_
    have h4 : ∀ {σ a : State}, a.gpr .x9 = σ.gpr .x4 >>> 8 → isa.eval (.nonzero .x .x9) a = some false →
        (σ.gpr .x4).toNat < 256 := fun {σ a} ha hc => by
      rw [MlKem.AArch64.eval_nonzero, ha, Option.some.injEq, lsr8_eq, decide_eq_false_iff_not] at hc; omega
    by_cases hl : (s₁.gpr .x4).toNat < 256
    · exact RelCT.mono (body_ct hS hp hP v hv hx hxn hf hfn hK₁ hK₂ hE hl (by rw [← p4]; exact hl))
        (fun a b ⟨⟨⟨oa, _⟩, ⟨ob, _⟩⟩, _⟩ => ⟨oa, ob⟩) fun _ _ h => h
    · exact RelCT.of_false fun a b ⟨⟨⟨_, ha⟩, _⟩, hc⟩ => hl (h4 ha hc)
  exact (hct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

def sgSat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x6 => 0x100000 | .x7 => 0x100000000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, p.n⟩]
  wr := [⟨0x100000, p.sigLen⟩, ⟨0x100000000, scratchWords * 8⟩]

theorem sg_implies {p : Params} (hz : Sz p) (hsl : p.sigLen < 2 ^ 31) :
    (sgK p).Implies (Spec.SlhDsa.signContract p AArch64.abi 16) := by
  have hn := hz.n32
  refine ⟨fun s h => ?_, fun s s' _ h => ?_, fun s₁ s₂ _ _ h => ?_, ⟨sgSat p, ?_⟩⟩
  · sig_pre [Spec.SlhDsa.signContract, Spec.SlhDsa.signSig, AArch64.abi, VG.AArch64.argRegs] at h
    sig_split h
    rename_i a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, h⟩
  · sig_post [Spec.SlhDsa.signContract, Spec.SlhDsa.signSig, AArch64.abi, VG.AArch64.argRegs]
    exact h
  · sig_pub [Spec.SlhDsa.signContract, Spec.SlhDsa.signSig, AArch64.abi, VG.AArch64.argRegs] at h
    obtain ⟨hsp, -, h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, hsp⟩
  · have hsk : p.skLen ≤ 128 := by simp only [Params.skLen]; omega
    sig_pre [Spec.SlhDsa.signContract, Spec.SlhDsa.signSig, AArch64.abi, VG.AArch64.argRegs, sgSat]
    sig_and_intros
    all_goals first
      | rfl
      | omega
      | (simp only [BitVec.reduceToNat]; omega)
      | (simp only [scratchWords, BitVec.reduceToNat]; omega)
      | (apply Offset.disjoint_of_le <;> dsimp only <;> simp only [BitVec.reduceToNat, BitVec.reduceSub] <;> omega)
      | (apply Region.Disjoint.symm; apply Offset.disjoint_of_le <;> dsimp only <;> simp only [BitVec.reduceToNat, BitVec.reduceSub] <;> omega)
      | (apply Offset.disjoint_of_le <;> dsimp only <;> simp only [scratchWords, BitVec.reduceToNat] <;> omega)
      | (apply Region.Disjoint.symm; apply Offset.disjoint_of_le <;> dsimp only <;>
          simp only [scratchWords, BitVec.reduceToNat, BitVec.reduceSub] <;> omega)
      | (apply Offset.disjoint_of_le <;> dsimp only <;>
          simp only [scratchWords, BitVec.reduceToNat, BitVec.reduceSub] <;> omega)

/-- `vg_slhdsa_shake_*_sign` for a SHAKE parameter set `p`, over any
`forsSign` and `xmssTree` verified against their contracts, meets
`signContract` in constant time. -/
theorem sign_verified {p : Params} (hS : Shake6 p) (hp : VG.Proof.SlhDsa.X86_64.VerifyTop.VPar p) (hP : LP p)
    {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (v : Proof.Sha3.AArch64.Permutation) (hv : f.keccak = v.callee)
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true)
    (hf : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.forsCode p f) (forsContract p))
    (hfn : (Impl.SlhDsa.AArch64.Shake.forsCode p f).noFrames = true) :
    Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.sign p f) (Spec.SlhDsa.signContract p AArch64.abi 16) :=
  Verified.of_correct (fun _ h => by
      obtain ⟨t, s', e, hq⟩ := sign_wp (fun σ s hK h4 hs => body_ok hp hP v hv hx hxn hf hfn hK h4 hs) h
      exact ⟨t, s', e, hq.1, hq.2⟩)
    (sign_ct hS hp hP v hv hx hxn hf hfn) (sg_implies hP.sz hp.sigLt)

end VG.Proof.SlhDsa.AArch64.Sign
