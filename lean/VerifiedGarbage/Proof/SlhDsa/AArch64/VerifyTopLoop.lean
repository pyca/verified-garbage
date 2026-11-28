module

-- separate module: the hypertree's layers, rebuilt only when xmssPk's contract or the lanes' blocks change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyTopFors
public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyXmssCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `verify`: the hypertree's layers

Before layer `j` (`LI`): the layer's XMSS signature's place in `x20`, `j`
in `x21`, its tree and leaf index in `x22` and `x23`, and the root below at
`oMsg`, as `htFold` gives them (`htV`). The block after FORS gives `LI` of
layer 0 (`init_wp`); a layer, its lanes' addresses and the call of
`xmssPk`, the next (`layer_ok`), and the loop all `d` (`loop_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.VerifyTop

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout movV lea)
open VG.Proof.SlhDsa (layerTree treeAdrs)
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar htFold htStep htFold_succ)
open VG.Proof.SlhDsa.AArch64.Sign (env_adrs)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_addImm wp_movz)

/-- Before layer `j`, from the entry state `σ`. -/
structure LI (p : Params) (σ : State) (j : Nat) (t : State) : Prop where
  ctx : Ctx p σ t
  x20 : t.gpr .x20 = σ.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)
  x21 : t.gpr .x21 = BitVec.ofNat 64 j
  x22 : t.gpr .x22 = BitVec.ofNat 64 (htV p σ j).2.1
  x23 : t.gpr .x23 = BitVec.ofNat 64 (htV p σ j).2.2
  msg : bytesAt t.mem (at' (σ.gpr .x7) Layout.oMsg) p.n = (htV p σ j).1
  env : ∃ a16, Env p t.mem (σ.gpr .x7) (PKs p σ) a16

theorem xsl_lt {p : Params} (hp : VPar p) : p.xmssSigLen < 4096 := by
  have h1 := hp.len
  have h2 := hp.hp9
  have h3 := (Sz.of_vpar hp).n32
  simp only [Params.xmssSigLen]
  rw [h1]
  calc (2 * p.n + 3 + p.hp) * p.n ≤ (2 * 32 + 3 + 9) * 32 := Nat.mul_le_mul (by omega) h3
    _ < 4096 := by decide

theorem htV_tree {p : Params} (σ : State) : ∀ j, (htV p σ j).2.1 ≤ Tv p σ
  | 0 => Nat.le_refl _
  | j + 1 => by
    simp only [htV] at *
    rw [htFold_succ]
    exact Nat.le_trans (Nat.shiftRight_le _ _) (htV_tree σ j)

theorem htV_leaf {p : Params} (hp : VPar p) (σ : State) : ∀ j, (htV p σ j).2.2 < 2 ^ p.hp
  | 0 => Iv_lt hp σ
  | j + 1 => by
    simp only [htV]
    rw [htFold_succ]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The block after FORS. -/
theorem init_wp {p : Params} (hp : VPar p) {σ t : State} (hK : VG p σ) (ht : FP p σ t) :
    WP isa (.block (([.movz .x .x21 0 0] : List Instr) ++ lea .x20 .x24 (p.n + p.forsSigLen))) t (LI p σ 0) := by
  have hsl := hp.fsl
  rw [← List.append_nil (([.movz .x .x21 0 0] : List Instr) ++ lea .x20 .x24 (p.n + p.forsSigLen)),
    List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movz fun t₁ o₁ e₁ => lea_ok (.inr (by decide)) (by omega) fun t₂ o₂ e₂ => wp_nil ?_
  have o := (o₁.trans o₂).mono (show ∀ r ∈ [Reg.x21, .x20], r ∈ [Reg.x21, .x20] from fun _ h => h)
  exact ⟨ht.ctx.of_keep (Sz.of_vpar hp).n32 hK o (by decide) (by decide) (by decide),
    by rw [e₂, o₁.get .x24, ht.ctx.x24, Nat.zero_mul, Nat.add_zero], by rw [o₂.get .x21, e₁]; rfl,
    by rw [o.get .x22, ht.x22]; rfl, by rw [o.get .x23, ht.x23]; rfl,
    by rw [o.mem, ht.msg]; rfl, by obtain ⟨a, he⟩ := ht.env; exact ⟨a, by rw [o.mem]; exact he⟩⟩

/-- The block before a layer's call: the lanes' addresses and the call's arguments. -/
theorem lblock_ok {p : Params} (hz : Sz p) {σ t : State} (hK : VG p σ) (hc : Ctx p σ t) {pk a : List Byte}
    (he : Env p t.mem (σ.gpr .x7) pk a) (hL : (t.gpr .x21).toNat < 2 ^ 32) {Q : State → Prop}
    (k : ∀ u, Ctx p σ u → Env p u.mem (σ.gpr .x7) pk (layerTree (t.gpr .x21).toNat (t.gpr .x22).toNat) →
      (∀ r, r ∉ [.x12, .x13, .x14, .x0, .x1, .x2] → u.gpr r = t.gpr r) → u.gpr .x0 = σ.gpr .x7 →
      u.gpr .x1 = t.gpr .x23 → u.gpr .x2 = t.gpr .x20 →
      Frame (adrsRegions p.n (σ.gpr .x7)) t.mem u.mem → Q u) :
    WP isa (.block (Impl.SlhDsa.AArch64.Shake.treeLanes p .x21 .x22 ++
      ([Impl.SlhDsa.AArch64.Thash4.mov .x0 .x19, Impl.SlhDsa.AArch64.Thash4.mov .x1 .x23,
        Impl.SlhDsa.AArch64.Thash4.mov .x2 .x20] : List Instr))) t Q := by
  have hw : (⟨σ.gpr .x7, scratchLen⟩ : Region) ∈ t.wr := by rw [hc.wr, hK.wr]; simp
  refine treeLanes_ok (p := p) hz.nv (by decide) hc.x19 hw hL fun u₁ k₁ f₁ a₁ => ?_
  refine wp_addImm (by decide) fun u₂ o₂ e₂ => wp_addImm (by decide) fun u₃ o₃ e₃ =>
    wp_addImm (by decide) fun u₄ o₄ e₄ => wp_nil ?_
  have k₄ : Keep [.x12, .x13, .x14, .x0, .x1, .x2] t u₄ := (k₁.trans (o₂.trans (o₃.trans o₄)).keep).mono (by decide)
  have hm : u₄.mem = u₁.mem := by rw [o₄.mem, o₃.mem, o₂.mem]
  refine k u₄ ?_ ?_ (fun r hr => k₄.get r (by simpa using hr)) ?_ ?_ ?_ (by rw [hm]; exact f₁)
  · exact hc.of_frame hz.n32 hK k₄.rd k₄.wr k₄.sp (k₄.get .x19) (k₄.get .x24)
      (fun r hr => k₄.get r (by revert r; decide)) k₄.vcs (by rw [hm]; exact f₁) (adrs_free hz.n32 σ)
  · rw [hm]; exact env_adrs hz.n32 he.seedA he.seedB f₁ a₁
  · rw [o₄.get .x0, o₃.get .x0, e₂, BitVec.add_zero, k₁.get .x19, hc.x19]
  · rw [o₄.get .x1, e₃, BitVec.add_zero, o₂.get .x23, k₁.get .x23]
  · rw [e₄, BitVec.add_zero, o₃.get .x20, o₂.get .x20, k₁.get .x20]

/-- One layer. -/
theorem layer_ok {p : Params} (hp : VPar p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (g : Impl.SlhDsa.AArch64.Verify.VFns) {σ t : State} (hK : VG p σ) (hsl : (σ.gpr .x6).toNat = p.sigLen)
    {j : Nat} (hj : j < p.d) (hL : LI p σ j t) :
    WP isa (Impl.SlhDsa.AArch64.Verify.layerBody p f g) t fun w =>
      LI p σ (j + 1) w ∧ w.gpr .x9 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 p.d := by
  have hz := Sz.of_vpar hp
  have hn := hz.n32
  have hd := hp.d22
  have hsl31 := hp.sigLt
  have hxs := hp.xsl
  obtain ⟨a, he⟩ := hL.env
  have hT' : (htV p σ j).2.1 < 2 ^ 64 := Nat.lt_of_le_of_lt (htV_tree σ j) (Tv_lt hp σ)
  have hI' := htV_leaf hp σ j
  have hpow : 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hp.hp9
  have hoff : p.n + p.forsSigLen + j * p.xmssSigLen + p.xmssSigLen ≤ p.sigLen := by
    rw [hp.sigLen]; have := Nat.mul_le_mul_right p.xmssSigLen (show j + 1 ≤ p.d by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  unfold Impl.SlhDsa.AArch64.Verify.layerBody
  refine WP.seq (lblock_ok hz hK hL.ctx he (by rw [hL.x21, BitVec.toNat_ofNat]; omega)
    fun u hcu heu hgu h0 h1 h2 hfu => ?_)
  rw [hL.x21, hL.x22, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt hT'] at heu
  have hu1 : (u.gpr .x1).toNat = (htV p σ j).2.2 := by
    rw [h1, hL.x23, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hu2 : u.gpr .x2 = σ.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen) := by rw [h2, hL.x20]
  obtain ⟨hcv, hcw, hfo, hdo⟩ := part_ok hK hcu hsl hoff hp.xpos
  have hg : ∀ r, r ∉ linkRegs → (u.callEntry.withRegions
      [⟨σ.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen), p.xmssSigLen⟩]
      [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩]).gpr r = u.gpr r :=
    fun r h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  refine WP.seq (XmssPk.xmssPkcall_ok hz hh T ht g.xmssPkName ⟨⟨by rw [State.withRegions_rd, hg _ (by decide), hu2],
      by rw [State.withRegions_wr, hg _ (by decide), h0], by rw [hg _ (by decide), h0]; exact hK.f_scr,
      by rw [hg _ (by decide), h0]; have := hK.f_scr; simp only [scratchLen] at this; simp; omega,
      by rw [hg _ (by decide), h0]; exact empty_disj _ _,
      fun r hr => by
        rw [hg _ (by decide), hu2] at hr; simp only [List.mem_singleton] at hr; subst hr; exact hfo,
      fun r hr => by
        rw [hg _ (by decide), hu2] at hr; simp only [List.mem_singleton] at hr; subst hr
        rw [hg _ (by decide), h0]; exact hdo⟩,
    ⟨_, _, by rw [hg _ (by decide), h0]; exact heu⟩,
    by rw [hg _ (by decide), hu1]; exact hI'⟩ hcv hcw
    fun s' hrd hwr hsp hfr hpres hv hpost => ?_)
  dsimp only [xmssPkContract] at hpost
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.x0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.x1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.x2 ∉ linkRegs by decide), h0, hu1, hu2] at hpost
  obtain ⟨he', hroot, hF⟩ := hpost _ _ heu
  have hcs : Ctx p σ s' := hcu.of_frame hn hK hrd hwr hsp (hpres _ (by decide) (by decide))
    (hpres _ (by decide) (by decide)) (fun r hr => hpres r (by revert r; decide) (by revert r; decide)) hv hF
    (changes_free hz)
  have gs : ∀ r ∈ [Reg.x20, .x21, .x22, .x23], s'.gpr r = t.gpr r := fun r hr => by
    rw [hpres r (by revert r; decide) (by revert r; decide), hgu r (by revert r; decide)]
  rw [← List.append_nil (([.addImm .x .x20 .x20 p.xmssSigLen] : List Instr) ++ movV .x11 (2 ^ p.hp - 1) ++
    ([.logic .and .x .x23 .x22 .x11, .lsr .x .x22 .x22 p.hp, .addImm .x .x21 .x21 1, .subImm .x .x9 .x21 p.d] :
      List Instr))]
  refine Sign.next_ok (is := []) (xsl_lt hp) hp.hp9 (by omega) fun w o e20 e23 e22 e21 e9 =>
    wp_nil ⟨⟨hcs.of_keep hn hK o (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [e20, gs .x20 (by decide), hL.x20, addr_add, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  · rw [e21, gs .x21 (by decide), hL.x21, BitVec.ofNat_add]
  · rw [e22, gs .x22 (by decide), hL.x22]
    simp only [htV] at hT' ⊢
    rw [htFold_succ]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, htStep, Nat.mod_eq_of_lt hT',
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hT')]
  · simp only [htV] at hT' ⊢
    rw [htFold_succ]
    apply BitVec.eq_of_toNat_eq
    have hmod := Nat.mod_lt (htFold p (pkF p σ) (sigH p σ) (PKs p σ) (Tv p σ) (Iv p σ) j).2.1 (Nat.two_pow_pos p.hp)
    rw [e23, gs .x22 (by decide), hL.x22, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT']
    simp only [htStep]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · have hmu : bytesAt u.mem (at' (σ.gpr .x7) Layout.oMsg) p.n = (htV p σ j).1 := by
      rw [bytesAt_frame hfu (fun r hr => ?_) (by omega)]
      · exact hL.msg
      exact (lane_disj hn (.inr hr) (by simp only [Layout.oMsg, Layout.oA]; omega))
    have hsig : bytesAt u.mem (σ.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)) p.xmssSigLen =
        chunk (sigH p σ) p.xmssSigLen j := by
      rw [hcu.bytes_out (by omega) hdo
        (hK.stk_sig.sub_right (Offset.sub_base _ (by rw [hsl]; exact hoff))).symm, sigH,
        KeyGen.chunk_bytesAt _ _ hj, addr_add, Nat.mul_comm p.xmssSigLen j]
    rw [o.mem, hroot, hmu, hsig]
    simp only [htV]
    rw [htFold_succ]
    rfl
  · exact ⟨_, by rw [o.mem]; exact he'⟩
  · rw [e9, gs .x21 (by decide), hL.x21, BitVec.ofNat_add]

/-- The layers. -/
theorem loop_ok {p : Params} (hp : VPar p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (g : Impl.SlhDsa.AArch64.Verify.VFns) {σ t : State} (hK : VG p σ) (hsl : (σ.gpr .x6).toNat = p.sigLen)
    (hL : LI p σ 0 t) :
    WP isa (.loop (Impl.SlhDsa.AArch64.Verify.layerBody p f g) (.nonzero .x .x9)) t (LI p σ p.d) := by
  have hd := hp.d22
  have hd1 := hp.d1
  refine WP.loop (M := isa) (Inv := fun (n : Nat) (u : State) => ∃ j, j < p.d ∧ n = p.d - j ∧ LI p σ j u)
    (fun n s hs => ?_) p.d t (show ∃ j, j < p.d ∧ p.d = p.d - j ∧ LI p σ j t from ⟨0, by omega, by omega, hL⟩)
  obtain ⟨j, hj, hn, hs⟩ := hs
  refine WP.mono (layer_ok hp hh T ht g hK hsl hj hs) fun s' ⟨hs', h9⟩ => ?_
  rw [MlKem.AArch64.eval_nonzero, h9]
  by_cases e : j + 1 = p.d
  · left
    rw [e, BitVec.sub_self]
    exact ⟨rfl, e ▸ hs'⟩
  · right
    refine ⟨by rw [Option.some.injEq]; exact bne_iff_ne.mpr (Sign.sub_ne_zero (show j + 1 < p.d by omega) (by omega)),
      p.d - (j + 1), by omega, j + 1, by omega, rfl, hs'⟩

end VG.Proof.SlhDsa.AArch64.VerifyTop
