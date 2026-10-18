module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Interleaved counter mode and GHASH on AArch64: GHASH's instructions

Untrusted: everything here is checked by Lean. `ghPart_ok`: `ghPart`
(`Impl.Gcm.AArch64.Stitch`) leaves in `Y` (`v16`) the `gh8V` of `Y`, the eight
blocks at `x9` as loaded, and the powers and keys of the table at `x19`
(`Ops.lean`), writing only `v16` and `v18`–`v29`: a pair of blocks and its products
(`pair_ok`), added (`addFirst_ok`, `addNext_ok`), and the reduction
(`reduce_ok`), each as bits.
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64
open VG.Proof.Gcm.AArch64.Pmull (Prod reduce ext8 VOnly v_setV gpr_setV mem_setV rd_setV wr_setV sp_setV
  exec_pmull0 exec_pmull1 exec_eor exec_ext8 eor_ok loadRev_ok vdword_xor vdword_append_0 vdword_append_1)
open VG.Impl.Gcm.AArch64.Stitch

/-- The registers `ghPart` writes. -/
abbrev ghV : List VReg :=
  [.v16, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29]

/-- The product registers. -/
def prodS (s : State) : Prod := ⟨s.v LO, s.v MID, s.v HI⟩

theorem exec_eor3 (d n m a : VReg) (s : State) :
    exec (.vop (.eor3 d n m a)) s = some (s.setV d (s.v n ^^^ s.v m ^^^ s.v a)) := rfl

theorem exec_trn (op : VPermOp) (d n m : VReg) (s : State) :
    exec (.vop (.perm op .d2 d n m)) s = some (s.setV d (op.eval .d2 (s.v n) (s.v m))) := rfl

theorem trn_sum (a b : BitVec 128) :
    VPermOp.eval .trn1 .d2 a b ^^^ VPermOp.eval .trn2 .d2 a b =
      ofVDwords (vdword a 0 ^^^ vdword a 1) (vdword b 0 ^^^ vdword b 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, ofVDwords, vdword, BitVec.getLsbD_xor,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64 <;> simp [h, hi, List.getD] <;> omega

/-! ## A pair of blocks -/

theorem vdword_ofVDwords0 (a b : BitVec 64) : vdword (ofVDwords a b) 0 = a := vdword_append_0 _ _
theorem vdword_ofVDwords1 (a b : BitVec 64) : vdword (ofVDwords a b) 1 = b := vdword_append_1 _ _

/-- Block `j` of the eight at `x9`, as loaded. -/
def blkV (s : State) (j : Nat) : BitVec 128 :=
  VRevOp.eval .rev64b (s.mem.read (s.gpr .x9 + BitVec.ofNat 64 (16 * j)) 16)

/-- The table's value at `x19 + o`. -/
def tblV (s : State) (o : Nat) : BitVec 128 := s.mem.read (s.gpr .x19 + BitVec.ofNat 64 o) 16

/-- The rest of a pair: the keys loaded, the sums of the blocks' halves
packed, and the six products. -/
theorem pairTail_ok (p k l : Nat) (s : State) (hk : sOff k % 16 = 0 ∧ sOff k < 4096 * 16)
    (hl : sOff l % 16 = 0 ∧ sOff l < 4096 * 16) (hp : kOff p % 16 = 0 ∧ kOff p < 4096 * 16)
    (hink : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (sOff k)) 16)
    (hinl : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (sOff l)) 16)
    (hinp : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (kOff p)) 16) :
    WP isa (.block [.ldrq S₁ .x19 (sOff k), .ldrq S₂ .x19 (sOff l), .ldrq KP .x19 (kOff p),
      .vop (.perm .trn1 .d2 T A₁ A₂), .vop (.perm .trn2 .d2 U A₁ A₂), .vop (.logic .eor T T U),
      .vop (.pmull false X₁ A₁ S₁), .vop (.pmull true A₁ A₁ S₁),
      .vop (.pmull false X₂ A₂ S₂), .vop (.pmull true A₂ A₂ S₂),
      .vop (.pmull false U T KP), .vop (.pmull true T T KP)]) s fun s' =>
      s'.v X₁ = polyMul (vdword (s.v A₁) 0) (vdword (tblV s (sOff k)) 0) ∧
      s'.v A₁ = polyMul (vdword (s.v A₁) 1) (vdword (tblV s (sOff k)) 1) ∧
      s'.v X₂ = polyMul (vdword (s.v A₂) 0) (vdword (tblV s (sOff l)) 0) ∧
      s'.v A₂ = polyMul (vdword (s.v A₂) 1) (vdword (tblV s (sOff l)) 1) ∧
      s'.v U = polyMul (vdword (s.v A₁) 0 ^^^ vdword (s.v A₁) 1) (vdword (tblV s (kOff p)) 0) ∧
      s'.v T = polyMul (vdword (s.v A₂) 0 ^^^ vdword (s.v A₂) 1) (vdword (tblV s (kOff p)) 1) ∧
      VOnly [S₁, S₂, KP, T, U, X₁, A₁, X₂, A₂] s s' := by
  rw [WP.block_cons_iff]
  refine ⟨_, Pmull.exec_ldrq hk.1 hk.2 hink, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Pmull.exec_ldrq hl.1 hl.2 (by simpa only [gpr_setV, rd_setV, wr_setV] using hinl), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Pmull.exec_ldrq hp.1 hp.2 (by simpa only [gpr_setV, rd_setV, wr_setV] using hinp), ?_⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_trn, exec_eor, exec_pmull0, exec_pmull1,
    Option.some.injEq, exists_eq_left', v_setV, gpr_setV, mem_setV, ite_true, ite_false, reduceCtorEq, tblV,
    trn_sum, vdword_ofVDwords0, vdword_ofVDwords1]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, ⟨fun r hr => ?_, by simp only [gpr_setV],
    by simp only [mem_setV], by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-- `Y` added to `A₂` if `y`. -/
theorem addY_ok (y : Bool) (s : State) :
    WP isa (.block (if y then [.vop (.logic .eor A₂ A₂ Y)] else [])) s fun s' =>
      s'.v A₂ = s.v A₂ ^^^ (if y then s.v Y else 0) ∧ VOnly [A₂] s s' := by
  cases y
  · exact WP.block_nil ⟨by simp, VOnly.refl _ _⟩
  · exact WP.mono (eor_ok A₂ A₂ Y s) fun s' ⟨h, o⟩ => ⟨by rw [h]; rfl, o⟩

/-- The table's offsets. -/
theorem sOff_ok (k : Nat) (hk : k ≤ 8) : sOff k % 16 = 0 ∧ sOff k < 4096 * 16 := by
  unfold sOff tbl; omega
theorem kOff_ok (p : Nat) (hp : p < 4) : kOff p % 16 = 0 ∧ kOff p < 4096 * 16 := by
  unfold kOff tbl; omega

/-- What `ghPart` reads. -/
structure GhIn (s : State) : Prop where
  blk : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (16 * j)) 16
  sw : ∀ k, 1 ≤ k → k ≤ 8 → InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (sOff k)) 16
  key : ∀ p < 4, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (kOff p)) 16

theorem GhIn.of {s s' : State} (h : GhIn s) (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    GhIn s' :=
  ⟨fun j hj => by rw [hg, hrd, hwr]; exact h.blk j hj, fun k a b => by rw [hg, hrd, hwr]; exact h.sw k a b,
    fun p hp => by rw [hg, hrd, hwr]; exact h.key p hp⟩

theorem ld_eq (a : VReg) (j : Nat) : ld a j = Impl.Gcm.AArch64.Pmull.loadRev a .x9 (16 * j) := rfl

/-- Pair `p` of blocks `a` and `b`, by the powers `k` and `l`. -/
theorem pair_ok (p a k b l : Nat) (y : Bool) (s : State) (hin : GhIn s) (hp : p < 4) (ha : a < 8)
    (hb : b < 8) (hk : 1 ≤ k ∧ k ≤ 8) (hl : 1 ≤ l ∧ l ≤ 8) :
    WP isa (.block (pair p a k b l y)) s fun s' =>
      s'.v X₁ = polyMul (vdword (blkV s a) 0) (vdword (tblV s (sOff k)) 0) ∧
      s'.v A₁ = polyMul (vdword (blkV s a) 1) (vdword (tblV s (sOff k)) 1) ∧
      s'.v X₂ = polyMul (vdword (blkV s b ^^^ (if y then s.v Y else 0)) 0) (vdword (tblV s (sOff l)) 0) ∧
      s'.v A₂ = polyMul (vdword (blkV s b ^^^ (if y then s.v Y else 0)) 1) (vdword (tblV s (sOff l)) 1) ∧
      s'.v U = polyMul (vdword (blkV s a) 0 ^^^ vdword (blkV s a) 1) (vdword (tblV s (kOff p)) 0) ∧
      s'.v T = polyMul (vdword (blkV s b ^^^ (if y then s.v Y else 0)) 0 ^^^
        vdword (blkV s b ^^^ (if y then s.v Y else 0)) 1) (vdword (tblV s (kOff p)) 1) ∧
      VOnly [A₁, A₂, S₁, S₂, KP, T, U, X₁, X₂] s s' := by
  unfold pair
  simp only [List.append_assoc]
  rw [ld_eq, ld_eq, WP.block_append_iff]
  refine WP.mono (loadRev_ok A₁ .x9 (16 * a) s (Nat.mul_mod_right 16 _) (by omega) (hin.blk a ha))
    fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadRev_ok A₂ .x9 (16 * b) s₁ (Nat.mul_mod_right 16 _) (by omega)
    (by rw [o₁.rd, o₁.wr, o₁.gpr]; exact hin.blk b hb)) fun s₂ ⟨l₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addY_ok y s₂) fun s₃ ⟨e₃, o₃⟩ => ?_
  have o₁₃ := o₁.trans (o₂.trans o₃)
  have hin₃ := hin.of o₁₃.gpr o₁₃.rd o₁₃.wr
  refine WP.mono (pairTail_ok p k l s₃ (sOff_ok k hk.2) (sOff_ok l hl.2) (kOff_ok p hp)
    (hin₃.sw k hk.1 hk.2) (hin₃.sw l hl.1 hl.2) (hin₃.key p hp))
    fun s' ⟨h1, h2, h3, h4, h5, h6, o⟩ => ?_
  have hA₁ : s₃.v A₁ = blkV s a := by
    rw [o₃.v A₁ (by decide), o₂.v A₁ (by decide), l₁]; rfl
  have hA₂ : s₃.v A₂ = blkV s b ^^^ (if y then s.v Y else 0) := by
    rw [e₃, l₂, o₁.mem, o₁.gpr, o₂.v Y (by decide), o₁.v Y (by decide)]; rfl
  have ht : ∀ o, tblV s₃ o = tblV s o := fun o => by simp only [tblV, o₁₃.mem, o₁₃.gpr]
  rw [hA₁] at h1 h2 h5
  rw [hA₂] at h3 h4 h6
  simp only [ht] at h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6, (o₁₃.trans o).weaken⟩

/-- A pair's products, the first: their sums. -/
theorem addFirst_ok (s : State) :
    WP isa (.block addFirst) s fun s' =>
      prodS s' = ⟨s.v A₁ ^^^ s.v A₂, s.v U ^^^ s.v T, s.v X₁ ^^^ s.v X₂⟩ ∧ VOnly [HI, LO, MID] s s' := by
  apply WP.of_runBlock
  simp only [addFirst, runBlock_cons, runStep_some, runBlock_nil, exec_eor, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [prodS, v_setV, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

/-- A pair's products added. -/
theorem addNext_ok (s : State) :
    WP isa (.block addNext) s fun s' =>
      prodS s' = ⟨s.v LO ^^^ s.v A₁ ^^^ s.v A₂, s.v MID ^^^ s.v U ^^^ s.v T, s.v HI ^^^ s.v X₁ ^^^ s.v X₂⟩ ∧
        VOnly [HI, LO, MID] s s' := by
  apply WP.of_runBlock
  simp only [addNext, runBlock_cons, runStep_some, runBlock_nil, exec_eor3, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [prodS, v_setV, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The reduction of `fix` of the product, into `Y`. -/
theorem reduce_ok (s : State) (hc : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly) :
    WP isa (.block Impl.Gcm.AArch64.Stitch.reduce) s fun s' =>
      s'.v Y = Pmull.reduce (fix (prodS s)) ∧ VOnly [T, U, MID, HI, Y] s s' := by
  have hc0 : vdword (ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly) 0 =
    Impl.Gcm.AArch64.Pmull.poly := vdword_append_0 _ _
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Stitch.reduce, runBlock_cons, runStep_some, runBlock_nil, exec_pmull0, exec_ext8,
    exec_eor3, Option.some.injEq, exists_eq_left', v_setV, ite_true, ite_false, reduceCtorEq, hc]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [hc0, Pmull.reduce, fix, prodS]
    have e : s.v MID ^^^ (ext8 (s.v LO) (s.v LO) ^^^ s.v LO ^^^ s.v HI) ^^^
        polyMul (vdword (s.v LO) 0) Impl.Gcm.AArch64.Pmull.poly =
        s.v MID ^^^ s.v HI ^^^ s.v LO ^^^ ext8 (s.v LO) (s.v LO) ^^^
          polyMul (vdword (s.v LO) 0) Impl.Gcm.AArch64.Pmull.poly := by
      ac_rfl
    rw [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-! ## The part -/

/-- The products of pair `p`, added to `pv`. -/
def pairP (s : State) (pv : Prod) (p : Nat) : Prod :=
  kpair pv (blkV s (pa p)) (tblV s (sOff (pk p))) (blkV s (pb p) ^^^ (if p = 3 then s.v Y else 0))
    (tblV s (sOff (pl p))) (tblV s (kOff p))

/-- The registers a pair and its sums write. -/
abbrev pairV : List VReg := [.v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29]

theorem pairAdd_ok (p : Nat) (hp : p < 4) (first : Bool) (s₀ s : State) (hin : GhIn s₀)
    (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hy : s.v Y = s₀.v Y) :
    WP isa (.block (pair p (pa p) (pk p) (pb p) (pl p) (decide (p = 3)) ++ (if first then addFirst else addNext)))
      s fun s' => prodS s' = pairP s₀ (if first then ⟨0, 0, 0⟩ else prodS s) p ∧ VOnly pairV s s' := by
  have hin' := hin.of hg hrd hwr
  rw [WP.block_append_iff]
  have hpa : pa p < 8 := by unfold pa; split <;> omega
  have hpb : pb p < 8 := by unfold pb; split <;> omega
  have hpk : 1 ≤ pk p ∧ pk p ≤ 8 := by unfold pk; split <;> omega
  have hpl : 1 ≤ pl p ∧ pl p ≤ 8 := by unfold pl; split <;> omega
  refine WP.mono (pair_ok p (pa p) (pk p) (pb p) (pl p) (decide (p = 3)) s hin' hp hpa hpb hpk hpl)
    fun s₁ ⟨h1, h2, h3, h4, h5, h6, o₁⟩ => ?_
  have eb : ∀ j, blkV s j = blkV s₀ j := fun j => by simp only [blkV, hm, hg]
  have et : ∀ o, tblV s o = tblV s₀ o := fun o => by simp only [tblV, hm, hg]
  cases first
  · refine WP.mono (addNext_ok s₁) fun s' ⟨e, o⟩ => ⟨?_, (o₁.trans o).weaken⟩
    rw [e, h1, h2, h3, h4, h5, h6, o₁.v LO (by decide), o₁.v MID (by decide), o₁.v HI (by decide)]
    simp only [pairP, kpair, kadd, prodS, decide_eq_true_eq, hy, eb, et, Bool.false_eq_true, ite_false]
  · refine WP.mono (addFirst_ok s₁) fun s' ⟨e, o⟩ => ⟨?_, (o₁.trans o).weaken⟩
    rw [e, h1, h2, h3, h4, h5, h6]
    simp only [pairP, kpair, kadd, BitVec.ofNat_eq_ofNat, BitVec.zero_xor, ite_true, decide_eq_true_eq, hy, eb, et]

theorem ghPart_eq : ghPart =
    (pair 0 (pa 0) (pk 0) (pb 0) (pl 0) (decide (0 = 3)) ++ (if true then addFirst else addNext)) ++
    ((pair 1 (pa 1) (pk 1) (pb 1) (pl 1) (decide (1 = 3)) ++ (if false then addFirst else addNext)) ++
    ((pair 2 (pa 2) (pk 2) (pb 2) (pl 2) (decide (2 = 3)) ++ (if false then addFirst else addNext)) ++
    ((pair 3 (pa 3) (pk 3) (pb 3) (pl 3) (decide (3 = 3)) ++ (if false then addFirst else addNext)) ++
    Impl.Gcm.AArch64.Stitch.reduce))) := by
  simp only [ghPart, List.append_assoc]; rfl

theorem ghPart_ok (s : State) (hin : GhIn s)
    (hc : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly) :
    WP isa (.block ghPart) s fun s' =>
      s'.v Y = gh8V (s.v Y) (blkV s) (fun k => tblV s (sOff k)) (fun p => tblV s (kOff p)) ∧
        VOnly ghV s s' := by
  rw [ghPart_eq, WP.block_append_iff]
  refine WP.mono (pairAdd_ok 0 (by decide) true s s hin rfl rfl rfl rfl rfl) fun s₁ ⟨p₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairAdd_ok 1 (by decide) false s s₁ hin o₁.gpr o₁.mem o₁.rd o₁.wr (o₁.v Y (by decide)))
    fun s₂ ⟨p₂, o₂⟩ => ?_
  have O₂ := (o₁.trans o₂).weaken (rs' := pairV)
  rw [WP.block_append_iff]
  refine WP.mono (pairAdd_ok 2 (by decide) false s s₂ hin O₂.gpr O₂.mem O₂.rd O₂.wr (O₂.v Y (by decide)))
    fun s₃ ⟨p₃, o₃⟩ => ?_
  have O₃ := (O₂.trans o₃).weaken (rs' := pairV)
  rw [WP.block_append_iff]
  refine WP.mono (pairAdd_ok 3 (by decide) false s s₃ hin O₃.gpr O₃.mem O₃.rd O₃.wr (O₃.v Y (by decide)))
    fun s₄ ⟨p₄, o₄⟩ => ?_
  have O₄ := (O₃.trans o₄).weaken (rs' := pairV)
  refine WP.mono (reduce_ok s₄ (by rw [O₄.v C (by decide), hc])) fun s' ⟨e, o⟩ => ⟨?_, (O₄.trans o).weaken⟩
  rw [e, p₄, p₃, p₂, p₁]
  simp only [ite_true, Bool.false_eq_true, ite_false, gh8V, pairP]

end VG.Proof.Gcm.AArch64.Stitch
