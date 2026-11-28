module

-- separate module: the hypertree's layers, rebuilt only when xmssTree's contract or the lanes' blocks change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignCalls
public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignPro
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopLanes
public import VerifiedGarbage.Proof.SlhDsa.SignTopSpec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `sign`: the hypertree's layers

The block after FORS (`init_ok`): the first layer and the first XMSS
signature's place; and the block after each layer's XMSS signature, the
next signature's place, the next layer's indices and the layer counter
(`next_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Sign

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout movV lea)
open VG.Proof.SlhDsa (layerTree treeAdrs)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_addImm wp_subImm wp_movz wp_and wp_lsr)

section
variable {is : List Instr} {u : State} {Q : State → Prop}

theorem and_mask (x : BitVec 64) {k : Nat} (hk : k ≤ 9) :
    (x &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk; omega)]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- The block after FORS. -/
theorem init_ok {p : Params} (hfl : p.n + p.forsSigLen < 2 ^ 64)
    (k : ∀ t, Only [.x21, .x20] u t → t.gpr .x21 = 0 → t.gpr .x20 = u.gpr .x25 + BitVec.ofNat 64 (p.n + p.forsSigLen) →
      WP isa (.block is) t Q) :
    WP isa (.block ((([.movz .x .x21 0 0] : List Instr) ++ lea .x20 .x25 (p.n + p.forsSigLen)) ++ is)) u Q := by
  rw [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movz fun t₁ o₁ e₁ => lea_ok (.inr (by decide)) hfl fun t₂ o₂ e₂ =>
    k t₂ ((o₁.trans o₂).mono (by decide)) (by rw [o₂.get .x21, e₁]; rfl) (by rw [e₂, o₁.get .x25])

/-- The block after a layer's XMSS signature. -/
theorem next_ok {p : Params} (hxs : p.xmssSigLen < 4096) (hp9 : p.hp ≤ 9) (hd : p.d < 4096)
    (k : ∀ t, Only [.x20, .x11, .x23, .x22, .x21, .x9] u t → t.gpr .x20 = u.gpr .x20 + BitVec.ofNat 64 p.xmssSigLen →
      (t.gpr .x23).toNat = (u.gpr .x22).toNat % 2 ^ p.hp → t.gpr .x22 = u.gpr .x22 >>> p.hp →
      t.gpr .x21 = u.gpr .x21 + BitVec.ofNat 64 1 → t.gpr .x9 = u.gpr .x21 + BitVec.ofNat 64 1 - BitVec.ofNat 64 p.d →
      WP isa (.block is) t Q) :
    WP isa (.block ((([.addImm .x .x20 .x20 p.xmssSigLen] : List Instr) ++ movV .x11 (2 ^ p.hp - 1) ++
      ([.logic .and .x .x23 .x22 .x11, .lsr .x .x22 .x22 p.hp, .addImm .x .x21 .x21 1, .subImm .x .x9 .x21 p.d] :
        List Instr)) ++ is))
      u Q := by
  have hm : 2 ^ p.hp - 1 < 2 ^ 64 := by have := Nat.pow_le_pow_right (show 0 < 2 by decide) hp9; omega
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_addImm hxs fun t₁ o₁ e₁ => movV_ok hm fun t₂ o₂ e₂ => wp_and fun t₃ o₃ e₃ =>
    wp_lsr (by omega) fun t₄ o₄ e₄ => wp_addImm (by decide) fun t₅ o₅ e₅ => wp_subImm hd fun t₆ o₆ e₆ =>
    k t₆ ((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).mono (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [o₆.get .x20, o₅.get .x20, o₄.get .x20, o₃.get .x20, o₂.get .x20, e₁]
  · rw [o₆.get .x23, o₅.get .x23, o₄.get .x23, e₃, o₂.get .x22, o₁.get .x22, e₂, and_mask _ hp9]
  · rw [o₆.get .x22, o₅.get .x22, e₄, o₃.get .x22, o₂.get .x22, o₁.get .x22]
  · rw [o₆.get .x21, e₅, o₄.get .x21, o₃.get .x21, o₂.get .x21, o₁.get .x21]
  · rw [e₆, e₅, o₄.get .x21, o₃.get .x21, o₂.get .x21, o₁.get .x21]

end

/-! ## The lanes' addresses -/

/-- `Env` with the lanes' addresses rewritten. -/
theorem env_adrs {p : Params} (hn : p.n ≤ 32) {m m' : Mem} {S : Addr} {pk a' : List Byte}
    (hsA : ∀ k < 4, bytesAt m (at' S (Layout.laneA k)) p.n = pk) (hsB : ∀ k < 4, bytesAt m (at' S (Layout.laneB k)) p.n = pk)
    (hf : Frame (adrsRegions p.n S) m m')
    (ha : ∀ j < 4, ∀ b < 2, bytesAt m' (at' S (laneAdrs p.n j b)) 16 = a') : Env p m' S pk a' := by
  have hsd : ∀ {k b : Nat}, k < 4 → b < 2 → ∀ r ∈ adrsRegions p.n S,
      Region.Disjoint ⟨at' S (if b = 0 then Layout.laneA k else Layout.laneB k), p.n⟩ r := fun {k b} hk hb r hr => by
    simp only [adrsRegions, List.mem_flatMap, List.mem_range, List.mem_map] at hr
    obtain ⟨k', hk', b', hb', rfl⟩ := hr
    have h1 := laneAdrs_lt (n := p.n) hn hk' hb'
    have h2 := laneAdrs_lt (n := p.n) hn hk hb
    refine Offset.disjoint S ?_ (by split <;> simp only [laneA_eq, laneB_eq] <;> omega) (by omega)
    simp only [laneAdrs] at h1 h2 ⊢
    split <;> split <;> simp only [laneA_eq, laneB_eq] at * <;> omega
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have := hsd (b := 0) hk (by decide); simp only [ite_true] at this
    rw [bytesAt_frame hf this (by omega)]; exact hsA k hk
  · have := hsd (b := 1) hk (by decide); simp only [show (1 : Nat) ≠ 0 by decide, ite_false] at this
    rw [bytesAt_frame hf this (by omega)]; exact hsB k hk
  · simpa [laneAdrs] using ha k hk 0 (by decide)
  · simpa [laneAdrs] using ha k hk 1 (by decide)

/-! ## The layers -/

open VG.Proof.SlhDsa.X86_64.SignTop (hsFold hsSig hsFold_succ hsFold_leaf)

theorem hsFold_tree {p : Params} {M skSeed pkSeed : List Byte} {T I : Nat} :
    ∀ j, (hsFold p M skSeed pkSeed T I j).2.1 ≤ T
  | 0 => Nat.le_refl _
  | j + 1 => by
    rw [hsFold_succ]
    exact Nat.le_trans (Nat.shiftRight_le _ _) (hsFold_tree j)

/-- Before layer `j`, from the entry state `σ`, with FORS's public key `M₀`, the
indices `T₀` and `I₀`, and the signature so far `pre` (`R` and FORS's). -/
structure LI (p : Params) (σ : State) (pre M₀ : List Byte) (T₀ I₀ j : Nat) (t : State) : Prop where
  ctx : Ctx p σ t
  x20 : t.gpr .x20 = σ.gpr .x6 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)
  x21 : t.gpr .x21 = BitVec.ofNat 64 j
  x22 : t.gpr .x22 = BitVec.ofNat 64 (hsFold p M₀ (chunk (skB p σ) p.n 0) (chunk (skB p σ) p.n 2) T₀ I₀ j).2.1
  x23 : t.gpr .x23 = BitVec.ofNat 64 (hsFold p M₀ (chunk (skB p σ) p.n 0) (chunk (skB p σ) p.n 2) T₀ I₀ j).2.2
  msg : bytesAt t.mem (at' (σ.gpr .x7) Layout.oMsg) p.n =
    (hsFold p M₀ (chunk (skB p σ) p.n 0) (chunk (skB p σ) p.n 2) T₀ I₀ j).1
  sig : bytesAt t.mem (σ.gpr .x6) (p.n + p.forsSigLen + j * p.xmssSigLen) =
    pre ++ (List.range j).flatMap (hsSig p M₀ (chunk (skB p σ) p.n 0) (chunk (skB p σ) p.n 2) T₀ I₀)
  env : ∃ a16, Env p t.mem (σ.gpr .x7) (chunk (skB p σ) p.n 2) a16

theorem adrs_free {p : Params} (hn : p.n ≤ 32) (σ : State) : ∀ r ∈ adrsRegions p.n (σ.gpr .x7), Free p σ r := by
  intro r hr
  simp only [adrsRegions, List.mem_flatMap, List.mem_range, List.mem_map] at hr
  obtain ⟨k, hk, b, hb, rfl⟩ := hr
  have := laneAdrs_lt (n := p.n) hn hk hb
  exact .inl ⟨Offset.sub_base _ (by simp only [scratchLen]; omega),
    Offset.disjoint _ (by simp only [Layout.oTop]; omega) (by omega) (by simp only [Layout.oTop]; omega)⟩

/-- The block before a layer's call: the lanes' addresses and the call's arguments. -/
theorem lblock_ok {p : Params} (hz : Sz p) {σ t : State} (hK : SG p σ) (hc : Ctx p σ t) {pk a : List Byte}
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
  · exact hc.of_frame hz.n32 hK k₄.rd k₄.wr k₄.sp (k₄.get .x19) (fun r hr => k₄.get r (by revert r; decide)) k₄.vcs
      (by rw [hm]; exact f₁) (adrs_free hz.n32 σ)
  · rw [hm]; exact env_adrs hz.n32 he.seedA he.seedB f₁ a₁
  · rw [o₄.get .x0, o₃.get .x0, e₂, BitVec.add_zero, k₁.get .x19, hc.x19]
  · rw [o₄.get .x1, e₃, BitVec.add_zero, o₂.get .x23, k₁.get .x23]
  · rw [e₄, BitVec.add_zero, o₃.get .x20, o₂.get .x20, k₁.get .x20]

/-- What the layers need of the parameter set. -/
structure LP (p : Params) : Prop where
  sz : Sz p
  hp9 : p.hp ≤ 9
  d22 : p.d ≤ 22
  xsl : p.xmssSigLen < 4096
  xpos : 0 < p.xmssSigLen
  sigLen : p.sigLen = p.n + p.forsSigLen + p.d * p.xmssSigLen
  sigLt : p.sigLen < 2 ^ 63

theorem bytesAt_add'' (m : Mem) (a : Addr) (x y : Nat) :
    bytesAt m a (x + y) = bytesAt m a x ++ bytesAt m (a + BitVec.ofNat 64 x) y := KeyGen.bytesAt_add' m a x y

/-- One layer. -/
theorem layer_ok {p : Params} (hP : LP p) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true)
    {σ t : State} (hK : SG p σ) {pre M₀ : List Byte} {T₀ I₀ j : Nat} (hT : T₀ < 2 ^ 64) (hI : I₀ < 2 ^ p.hp)
    (hj : j < p.d) (hL : LI p σ pre M₀ T₀ I₀ j t) :
    WP isa (Impl.SlhDsa.AArch64.Shake.layerBody p f) t fun w =>
      LI p σ pre M₀ T₀ I₀ (j + 1) w ∧ w.gpr .x9 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 p.d := by
  have hz := hP.sz
  have hn := hz.n32
  have hd := hP.d22
  have hsl := hP.sigLt
  obtain ⟨a, he⟩ := hL.env
  have hT' : (hsFold p M₀ (chunk (skB p σ) p.n 0) (chunk (skB p σ) p.n 2) T₀ I₀ j).2.1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (hsFold_tree j) hT
  have hI' := hsFold_leaf p (M := M₀) (skSeed := chunk (skB p σ) p.n 0) (pkSeed := chunk (skB p σ) p.n 2)
    (idxTree := T₀) hI j
  have hpow : 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hP.hp9
  have hoff : p.n + p.forsSigLen + j * p.xmssSigLen + p.xmssSigLen ≤ p.sigLen := by
    rw [hP.sigLen]; have := Nat.mul_le_mul_right p.xmssSigLen (show j + 1 ≤ p.d by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  unfold Impl.SlhDsa.AArch64.Shake.layerBody
  refine WP.seq (lblock_ok hz hK hL.ctx he (by rw [hL.x21, BitVec.toNat_ofNat]; omega)
    fun u hcu heu hgu h0 h1 h2 hfu => ?_)
  rw [hL.x21, hL.x22, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt hT'] at heu
  have hu1 : (u.gpr .x1).toNat < 2 ^ p.hp := by rw [h1, hL.x23, BitVec.toNat_ofNat]; omega
  refine WP.seq (xmssCall_ok hz (by have := hP.sigLt; omega) hx hxn hK hcu h0 (by omega)
    (off := p.n + p.forsSigLen + j * p.xmssSigLen) (by rw [h2, hL.x20]) hoff hP.xpos heu
    fun s' hcs hpres he' hroot hsig hF => ?_)
  have g : ∀ r ∈ [Reg.x20, .x21, .x22, .x23], s'.gpr r = t.gpr r := fun r hr => by
    rw [hpres r (by revert r; decide) (by revert r; decide), hgu r (by revert r; decide)]
  rw [← List.append_nil (([.addImm .x .x20 .x20 p.xmssSigLen] : List Instr) ++ movV .x11 (2 ^ p.hp - 1) ++
    ([.logic .and .x .x23 .x22 .x11, .lsr .x .x22 .x22 p.hp, .addImm .x .x21 .x21 1, .subImm .x .x9 .x21 p.d] :
      List Instr))]
  refine next_ok (is := []) hP.xsl hP.hp9 (by omega) fun w o e20 e23 e22 e21 e9 => wp_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hcs.of_frame hn hK o.rd o.wr o.sp (o.get .x19) (fun r hr => o.get r (by revert r; decide)) o.vcs
      (rs := []) (fun x _ => by rw [o.mem]) (fun _ h => absurd h List.not_mem_nil)
  · rw [e20, g .x20 (by decide), hL.x20, addr_add, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  · rw [e21, g .x21 (by decide), hL.x21, BitVec.ofNat_add]
  · rw [e22, g .x22 (by decide), hL.x22, hsFold_succ]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, X86_64.SignTop.hsStep, Nat.mod_eq_of_lt hT',
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hT')]
  · rw [hsFold_succ]
    apply BitVec.eq_of_toNat_eq
    have hmod := Nat.mod_lt (hsFold p M₀ (chunk (skB p σ) p.n 0) (chunk (skB p σ) p.n 2) T₀ I₀ j).2.1 (Nat.two_pow_pos p.hp)
    rw [e23, g .x22 (by decide), hL.x22, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT']
    simp only [X86_64.SignTop.hsStep]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · rw [o.mem, hroot, hsFold_succ, key_chunk p σ (by decide)]
    rfl
  · have hsg1 : bytesAt s'.mem (σ.gpr .x6) (p.n + p.forsSigLen + j * p.xmssSigLen) =
        pre ++ (List.range j).flatMap (hsSig p M₀ (chunk (skB p σ) p.n 0) (chunk (skB p σ) p.n 2) T₀ I₀) := by
      rw [bytesAt_frame hF (fun r hr => ?_) (by omega)]
      · rw [bytesAt_frame hfu (fun r hr => ?_) (by omega)]
        · exact hL.sig
        simp only [adrsRegions, List.mem_flatMap, List.mem_range, List.mem_map] at hr
        obtain ⟨k, hk, b, hb, rfl⟩ := hr
        have := laneAdrs_lt (n := p.n) hn hk hb
        exact (hK.sig_scr.sub_left (Region.sub_prefix (base := σ.gpr .x6)
          (len := p.n + p.forsSigLen + j * p.xmssSigLen) (len' := p.sigLen) (by omega))).sub_right
          (Offset.sub_base _ (by simp only [scratchLen]; omega))
      rcases List.mem_append.mp hr with hr | hr
      · exact (hK.sig_scr.sub_left (Region.sub_prefix (base := σ.gpr .x6)
          (len := p.n + p.forsSigLen + j * p.xmssSigLen) (len' := p.sigLen) (by omega))).sub_right
          (changes_in hz r hr).1
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega)
    have hsg2 : bytesAt s'.mem (σ.gpr .x6 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)) p.xmssSigLen =
        hsSig p M₀ (chunk (skB p σ) p.n 0) (chunk (skB p σ) p.n 2) T₀ I₀ j := by
      have hmu : bytesAt u.mem (at' (σ.gpr .x7) Layout.oMsg) p.n =
          (hsFold p M₀ (chunk (skB p σ) p.n 0) (chunk (skB p σ) p.n 2) T₀ I₀ j).1 := by
        rw [bytesAt_frame hfu (fun r hr => ?_) (by omega)]
        · exact hL.msg
        simp only [adrsRegions, List.mem_flatMap, List.mem_range, List.mem_map] at hr
        obtain ⟨k, hk, b, hb, rfl⟩ := hr
        have := laneAdrs_lt (n := p.n) hn hk hb
        exact Offset.disjoint _ (by simp only [Layout.oMsg]; omega) (by simp only [Layout.oMsg]; omega) (by omega)
      rw [hsig hu1, h1, hL.x23, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), key_chunk p σ (by decide), hmu]
      rfl
    rw [o.mem, Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, bytesAt_add'', hsg1, hsg2, List.range_succ,
      List.flatMap_append, List.flatMap_singleton, List.append_assoc]
  · exact ⟨_, by rw [o.mem]; exact he'⟩
  · rw [e9, g .x21 (by decide), hL.x21, BitVec.ofNat_add]

theorem sub_ne_zero {a b : Nat} (ha : a < b) (hb : b < 2 ^ 64) : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ 0 := by
  intro h
  have h' : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
    have := congrArg (· + BitVec.ofNat 64 b) h
    simpa [BitVec.sub_add_cancel] using this
  have := congrArg BitVec.toNat h'
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt hb] at this
  omega

/-- The layers. -/
theorem loop_ok {p : Params} (hP : LP p) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true) (hd1 : 1 ≤ p.d)
    {σ t : State} (hK : SG p σ) {pre M₀ : List Byte} {T₀ I₀ : Nat} (hT : T₀ < 2 ^ 64) (hI : I₀ < 2 ^ p.hp)
    (hL : LI p σ pre M₀ T₀ I₀ 0 t) :
    WP isa (.loop (Impl.SlhDsa.AArch64.Shake.layerBody p f) (.nonzero .x .x9)) t (LI p σ pre M₀ T₀ I₀ p.d) := by
  have hd := hP.d22
  refine WP.loop (M := isa) (Inv := fun (n : Nat) (u : State) => ∃ j, j < p.d ∧ n = p.d - j ∧ LI p σ pre M₀ T₀ I₀ j u)
    (fun n s hs => ?_)
    p.d t (show ∃ j, j < p.d ∧ p.d = p.d - j ∧ LI p σ pre M₀ T₀ I₀ j t from ⟨0, by omega, by omega, hL⟩)
  obtain ⟨j, hj, hn, hs⟩ := hs
  refine WP.mono (layer_ok hP hx hxn hK hT hI hj hs) fun s' ⟨hs', h9⟩ => ?_
  rw [MlKem.AArch64.eval_nonzero, h9]
  by_cases e : j + 1 = p.d
  · left
    rw [e, BitVec.sub_self]
    exact ⟨rfl, e ▸ hs'⟩
  · right
    refine ⟨by rw [Option.some.injEq]; exact bne_iff_ne.mpr (sub_ne_zero (show j + 1 < p.d by omega) (by omega)), p.d - (j + 1), by omega, j + 1, by omega,
      rfl, hs'⟩

/-- The epilogue: the caller's registers back, and 1. -/
theorem epi_ok {p : Params} {σ t : State} (hK : SG p σ) (hc : Ctx p σ t) :
    WP isa (.block (Impl.SlhDsa.AArch64.restoreRegsAt Layout.oTop Impl.SlhDsa.AArch64.Shake.topSaved ++
      ([.movz .x .x0 1 0] : List Instr))) t fun w =>
      abiPreserved σ w ∧ (w.gpr .x0).setWidth 32 = 1 ∧ w.mem = t.mem := by
  have hw : (⟨σ.gpr .x7, scratchLen⟩ : Region) ∈ t.wr := by rw [hc.wr, hK.wr]; simp
  refine restoreRegsAt_ok KeyGen.topSaved_nodup ⟨by decide, by decide⟩
    (by rw [hc.x19]; exact KeyGen.in_scr (List.mem_append_right _ hw) (by decide)) fun u o v => ?_
  refine wp_movz fun w o' e' => wp_nil ⟨⟨fun r hr => ?_, by rw [o'.sp, o.sp, hc.sp],
    fun r hr => by rw [o'.vcs r hr, o.vcs r hr, hc.vcs r hr]⟩, by rw [e']; rfl, by rw [o'.mem, o.mem]⟩
  rw [o'.get r (by revert r; decide)]
  by_cases h : r ∈ Impl.SlhDsa.AArch64.Shake.topSaved
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    rw [v i hi, hc.x19, hc.saved i (by simp only [Impl.SlhDsa.AArch64.Shake.topSaved, List.length] at hi; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  · have hu : r ∈ untouched := by revert r h; decide
    rw [o.get r (by revert r hu; decide), hc.cs r hu]

end VG.Proof.SlhDsa.AArch64.Sign
