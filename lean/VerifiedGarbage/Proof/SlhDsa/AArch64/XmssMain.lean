module

-- separate module: the correctness of `xmssTree`, rebuilt without its constant-time proof's taint checks

public import VerifiedGarbage.Proof.SlhDsa.AArch64.XmssLeaves
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopShared
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `xmssTree`, the whole function

After the leaves (`XmssLeaves.lean`): the authentication path zeroed and
`levels`'s parameters set (`hblock_ok`), the call of `levels` on the
`2^h′` leaves (`heights_ok`), the root copied to `oMsg` and the
callee-saved registers restored (`xmss_wp`), and so `xmssContract`'s
postcondition (`xmss_correct`), as on x86-64.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Xmss

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase (in_scr in_scr' disj_scr scr0 at_add env_frame regions_scr regions_out
  laneA_eq laneB_eq env_a16 env_unique bytesAt_frame bytesAt_eq readW_frame)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)
open VG.Proof.SlhDsa.X86_64.XmssTree (leaf upNodes_xmss pick_xmss xorB_zero)

variable {p : Params}

/-! ## The heights block -/

/-- The heights block, as `heights` has it. -/
abbrev hbList (n len hp : Nat) : List Instr :=
  ([.addImm .x .x10 .x21 (len * n)] : List Instr) ++ Impl.SlhDsa.AArch64.zeroWords .x10 0 (hp * n / 8) ++
    Impl.SlhDsa.AArch64.Tree.setParams (.imm 0) (.imm 0) (.imm 2) (.imm 0) ++
    ([.addImm .x .x0 .x19 0] : List Instr) ++ Impl.SlhDsa.AArch64.lea .x1 .x19 Layout.oN ++
    Impl.SlhDsa.AArch64.movV .x2 (2 ^ hp) ++
    ([.movz .x .x3 0 0, .addImm .x .x4 .x10 0, .addImm .x .x5 .x20 0] : List Instr)

abbrev hbCode (p : Params) : List Instr := hbList p.n p.len p.hp

/-- The registers the heights block writes. -/
abbrev hbRegs : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x14]

/-- After the heights block, before the call of `levels`. -/
structure HB (p : Params) (u v : State) (S AU : Addr) : Prop where
  x0 : v.gpr .x0 = S
  x1 : v.gpr .x1 = at' S Layout.oN
  x2 : v.gpr .x2 = BitVec.ofNat 64 (2 ^ p.hp)
  x3 : v.gpr .x3 = 0
  x4 : v.gpr .x4 = AU
  x5 : v.gpr .x5 = u.gpr .x20
  keep : Keep hbRegs u v
  zero : bytesAt v.mem AU (p.hp * p.n) = List.replicate (p.hp * p.n) 0
  vars : ∀ i < 4, varAt v.mem S 3 i = if i = 2 then 2 else 0
  frame : Frame [⟨AU, p.hp * p.n⟩, ⟨at' S (Layout.oVar 3 0), 32⟩] u.mem v.mem

theorem var_eq (i : Nat) : Layout.oVar 3 i = 1496 + 8 * i := rfl

theorem readW_write_other (m : Mem) {a b : Addr} (v : BitVec 64) (h : Mem.Sep a 8 b 8) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep h (by decide)

/-- The heights block: the authentication path zeroed, `levels`'s parameters
and arguments. -/
theorem hblock_ok (hz : Sz p) (hhp9 : p.hp ≤ 9) {u : State} {S sig : Addr}
    (h19 : u.gpr .x19 = S) (h21 : u.gpr .x21 = sig) (hwS : (⟨S, 65536⟩ : Region) ∈ u.wr)
    (hws : (⟨sig, p.xmssSigLen⟩ : Region) ∈ u.wr) (hf : sig.toNat + p.xmssSigLen ≤ 2 ^ 64)
    (hAd : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, Layout.oSigTmp⟩) {Q : State → Prop}
    (k : ∀ v, HB p u v S (sig + BitVec.ofNat 64 (p.len * p.n)) → Q v) :
    WP isa (.block (hbCode p)) u Q := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hln : p.len * p.n ≤ 2144 := by rw [hz.len]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  have h512 : 2 ^ p.hp ≤ 512 :=
    calc 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp9
      _ = 512 := rfl
  have hpn : p.hp * p.n ≤ 288 := Nat.mul_le_mul hhp9 hn32
  have hw8 : 8 * (p.hp * p.n / 8) = p.hp * p.n := by
    have : p.hp * p.n % 8 = 0 := by rw [Nat.mul_mod, hn8, Nat.mul_zero]
    omega
  obtain ⟨AU, hAU⟩ : ∃ AU, AU = sig + BitVec.ofNat 64 (p.len * p.n) := ⟨_, rfl⟩
  rw [← hAU] at k
  have hSL := xmssSigLen_eq (p := p)
  rw [hbCode, hbList]
  generalize hMV : Impl.SlhDsa.AArch64.movV .x2 (2 ^ p.hp) = MV
  generalize hLE : Impl.SlhDsa.AArch64.lea .x1 .x19 Layout.oN = LE
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine MlKem.AArch64.wp_addImm (by omega) fun t₁ o₁ e₁ => ?_
  have h10 : t₁.gpr .x10 = AU := by rw [e₁, h21, hAU]
  refine zeroWords_ok (t := .x10) (by decide) (by omega) (by
      rw [o₁.wr, h10]
      refine ⟨_, hws, ?_⟩
      rw [hAU, addr_add]
      exact Offset.contains_base sig (by rw [hw8, hSL]; omega) (by omega)) fun t₂ k₂ f₂ z₂ => ?_
  rw [h10, hw8, BitVec.add_zero] at f₂ z₂
  have h19₂ : t₂.gpr .x19 = S := by rw [k₂.get .x19, o₁.get .x19, h19]
  have hwS₂ : (⟨S, 65536⟩ : Region) ∈ t₂.wr := by rw [k₂.wr, o₁.wr]; exact hwS
  -- `setParams`
  simp only [Impl.SlhDsa.AArch64.Tree.setParams, Impl.SlhDsa.AArch64.Tree.Src.mov, Impl.SlhDsa.AArch64.Tree.var,
    List.append_assoc, List.cons_append, List.nil_append]
  refine movV_ok (by decide) fun t₃ o₃ e₃ => MlKem.AArch64.wp_strx (a := at' S (Layout.oVar 3 0)) (by decide)
    (by rw [o₃.get .x19, h19₂]) (by rw [o₃.wr]; exact in_scr hwS₂ (by rw [var_eq]; omega)) fun t₄ m₄ => ?_
  refine movV_ok (by decide) fun t₅ o₅ e₅ => MlKem.AArch64.wp_strx (a := at' S (Layout.oVar 3 1)) (by decide)
    (by rw [o₅.get .x19, m₄.gpr, o₃.get .x19, h19₂])
    (by rw [o₅.wr, m₄.wr, o₃.wr]; exact in_scr hwS₂ (by rw [var_eq]; omega)) fun t₆ m₆ => ?_
  refine movV_ok (by decide) fun t₇ o₇ e₇ => MlKem.AArch64.wp_strx (a := at' S (Layout.oVar 3 2)) (by decide)
    (by rw [o₇.get .x19, m₆.gpr, o₅.get .x19, m₄.gpr, o₃.get .x19, h19₂])
    (by rw [o₇.wr, m₆.wr, o₅.wr, m₄.wr, o₃.wr]; exact in_scr hwS₂ (by rw [var_eq]; omega)) fun t₈ m₈ => ?_
  refine movV_ok (by decide) fun t₉ o₉ e₉ => MlKem.AArch64.wp_strx (a := at' S (Layout.oVar 3 3)) (by decide)
    (by rw [o₉.get .x19, m₈.gpr, o₇.get .x19, m₆.gpr, o₅.get .x19, m₄.gpr, o₃.get .x19, h19₂])
    (by rw [o₉.wr, m₈.wr, o₇.wr, m₆.wr, o₅.wr, m₄.wr, o₃.wr]; exact in_scr hwS₂ (by rw [var_eq]; omega))
    fun t₁₀ m₁₀ => ?_
  have K₁₀ : Keep [.x9] t₂ t₁₀ := (((((((o₃.keep.trans m₄.keep).trans o₅.keep).trans m₆.keep).trans o₇.keep).trans
    m₈.keep).trans o₉.keep).trans m₁₀.keep).mono (by simp)
  have hm₁₀ : t₁₀.mem = (((t₂.mem.writeW (at' S (Layout.oVar 3 0)) (BitVec.ofNat 64 0)).writeW
      (at' S (Layout.oVar 3 1)) (BitVec.ofNat 64 0)).writeW (at' S (Layout.oVar 3 2)) (BitVec.ofNat 64 2)).writeW
      (at' S (Layout.oVar 3 3)) (BitVec.ofNat 64 0) := by
    rw [m₁₀.mem, e₉, o₉.mem, m₈.mem, e₇, o₇.mem, m₆.mem, e₅, o₅.mem, m₄.mem, e₃, o₃.mem]
  have hc : ∀ i < 4, (⟨at' S (Layout.oVar 3 0), 32⟩ : Region).Contains (at' S (Layout.oVar 3 i)) (64 / 8) :=
    fun i hi => Offset.contains S (by rw [var_eq, var_eq]; omega) (by rw [var_eq, var_eq]; omega) (by rw [var_eq]; omega)
  have hfw : Frame [⟨at' S (Layout.oVar 3 0), 32⟩] t₂.mem t₁₀.mem := by
    rw [hm₁₀]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hc 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (hc 1 (by decide))).writeW (List.mem_singleton_self _) _
      (hc 2 (by decide))).writeW (List.mem_singleton_self _) _ (hc 3 (by decide))
  -- the arguments
  refine MlKem.AArch64.wp_addImm (by decide) fun t₁₁ o₁₁ e₁₁ => ?_
  subst hLE hMV
  refine lea_ok (off := Layout.oN) (.inr (show Reg.x1 ≠ Reg.x19 by decide)) (by decide) fun t₁₂ o₁₂ e₁₂ => ?_
  refine movV_ok (by omega) fun t₁₃ o₁₃ e₁₃ => ?_
  refine MlKem.AArch64.wp_movz fun t₁₄ o₁₄ e₁₄ => MlKem.AArch64.wp_addImm (by decide) fun t₁₅ o₁₅ e₁₅ =>
    MlKem.AArch64.wp_addImm (by decide) fun t₁₆ o₁₆ e₁₆ => MlKem.AArch64.wp_nil (k t₁₆ ?_)
  have O : Only [.x0, .x1, .x2, .x3, .x4, .x5] t₁₀ t₁₆ :=
    (((((o₁₁.trans o₁₂).trans o₁₃).trans o₁₄).trans o₁₅).trans o₁₆).mono (by simp)
  have g10 : t₁₀.gpr .x10 = AU := by rw [K₁₀.get .x10, k₂.get .x10, h10]
  have g19 : t₁₀.gpr .x19 = S := by rw [K₁₀.get .x19, h19₂]
  have hsep : ∀ i j, i < 4 → j < 4 → i ≠ j → Mem.Sep (at' S (Layout.oVar 3 i)) 8 (at' S (Layout.oVar 3 j)) 8 :=
    fun i j hi hj hij => Offset.sep S (by rw [var_eq, var_eq]; omega) (by rw [var_eq]; omega) (by rw [var_eq]; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_⟩
  · rw [o₁₆.get .x0, o₁₅.get .x0, o₁₄.get .x0, o₁₃.get .x0, o₁₂.get .x0, e₁₁, g19, BitVec.add_zero]
  · rw [o₁₆.get .x1, o₁₅.get .x1, o₁₄.get .x1, o₁₃.get .x1, e₁₂, o₁₁.get .x19, g19]
  · rw [o₁₆.get .x2, o₁₅.get .x2, o₁₄.get .x2, e₁₃]
  · rw [o₁₆.get .x3, o₁₅.get .x3, e₁₄]; rfl
  · rw [o₁₆.get .x4, e₁₅, o₁₄.get .x10, o₁₃.get .x10, o₁₂.get .x10, o₁₁.get .x10, g10, BitVec.add_zero]
  · rw [e₁₆, o₁₅.get .x20, o₁₄.get .x20, o₁₃.get .x20, o₁₂.get .x20, o₁₁.get .x20, K₁₀.get .x20, k₂.get .x20,
      o₁.get .x20, BitVec.add_zero]
  · exact ((o₁.keep.trans k₂).trans (K₁₀.trans O.keep)).mono (by simp)
  · rw [O.mem, bytesAt_frame hfw (fun r hr => ?_) (by omega), z₂]
    simp only [List.mem_singleton] at hr; subst hr
    rw [hAU]
    exact (hAd.sub_left (Offset.sub_base sig (by rw [hSL]))).sub_right
      (Offset.sub_base S (by rw [var_eq, show Layout.oSigTmp = 30144 from rfl]; omega))
  · simp only [varAt]
    rw [O.mem, hm₁₀]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [readW_write_other _ _ (hsep 0 3 (by decide) (by decide) (by decide)),
        readW_write_other _ _ (hsep 0 2 (by decide) (by decide) (by decide)),
        readW_write_other _ _ (hsep 0 1 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]; rfl
    · rw [readW_write_other _ _ (hsep 1 3 (by decide) (by decide) (by decide)),
        readW_write_other _ _ (hsep 1 2 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]; rfl
    · rw [readW_write_other _ _ (hsep 2 3 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]; rfl
    · rw [Mem.readW_writeW_self64]; rfl
  · rw [O.mem]
    have f₁ : Frame [⟨AU, p.hp * p.n⟩, ⟨at' S (Layout.oVar 3 0), 32⟩] u.mem t₂.mem := by
      rw [← o₁.mem]; exact f₂.mono fun r hr => by simp at hr ⊢; simp [hr]
    exact f₁.trans (hfw.mono fun r hr => by simp at hr ⊢; simp [hr])

theorem bytesAt_app (m : Mem) (a : Addr) (x y : Nat) :
    bytesAt m a (x + y) = bytesAt m a x ++ bytesAt m (a + BitVec.ofNat 64 x) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc, BitVec.ofNat_add]

/-- `levels`'s precondition at a call from `v`: the `2^h′` leaves at `oN`,
the authentication path at `AU`. -/
theorem levels_pre (hz : Sz p) (hhp : 1 ≤ p.hp) (hhp9 : p.hp ≤ 9) {σ u v : State} {S sig AU : Addr}
    (hR : Regions σ S [] ⟨sig, p.xmssSigLen⟩) (hAU : AU = sig + BitVec.ofNat 64 (p.len * p.n))
    (hv : HB p u v S AU) (h5 : (v.gpr .x5).toNat < 2 ^ 32) (hwr : v.wr = σ.wr) {pk a : List Byte}
    (he : Env p v.mem S pk a) :
    (levelsContract p).pre (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]) ∧
      Covers ([] ++ [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]) (v.rd ++ v.wr) ∧
      Covers [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩] v.wr := by
  have hn32 := hz.n32
  have h512 : 2 ^ p.hp ≤ 512 :=
    calc 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp9
      _ = 512 := rfl
  have hSL := xmssSigLen_eq (p := p)
  have h2h : (BitVec.ofNat 64 (2 ^ p.hp)).toNat = 2 ^ p.hp := by rw [BitVec.toNat_ofNat]; omega
  have hlog : heightsOf (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]) = p.hp := by
    simp only [heightsOf]; rw [callEntry_gpr' _ _ _ (by decide), hv.x2, h2h, Nat.log2_two_pow]
  have hsub : Region.Sub ⟨AU, p.hp * p.n⟩ ⟨sig, p.xmssSigLen⟩ := by
    rw [hAU]; exact Offset.sub_base sig (by rw [hSL])
  have hvm : ∀ i < 4, varAt (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]).mem S 3 i =
      varAt v.mem S 3 i := fun i _ => rfl
  refine ⟨⟨?_, ⟨pk, a, ?_⟩, by rw [callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide), hv.x0, hv.x1],
    by rw [hlog]; exact hhp, by rw [hlog, callEntry_gpr' _ _ _ (by decide), hv.x3]; simp; omega,
    by rw [hlog, callEntry_gpr' _ _ _ (by decide), hv.x2, h2h],
    by rw [callEntry_gpr' _ _ _ (by decide), hv.x2, h2h, show Layout.nodeSlots = 520 from rfl]
       have := Nat.mul_le_mul (show 2 ^ p.hp + 8 ≤ 520 by omega) hn32; omega,
    by rw [callEntry_gpr' _ _ _ (by decide)]; exact h5, ?_, ?_, ?_, ?_⟩,
    covers_call hR hwr (d := p.len * p.n) hAU (by rw [hSL])⟩
  · rw [callEntry_gpr' _ _ _ (by decide), callEntry_gpr' _ _ _ (by decide), hv.x0, hv.x4, hlog]
    exact regions_call hR hsub (by
      have := hR.out_fit
      have h16 : 1 ≤ p.hp * p.n := Nat.mul_pos hhp (by have := hz.n16; omega)
      simp only at this ⊢
      rw [hAU, BitVec.toNat_add, BitVec.toNat_ofNat]; rw [hSL] at this
      have : sig.toNat + p.len * p.n < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt (by omega : p.len * p.n < 2 ^ 64), Nat.mod_eq_of_lt this]; omega)
  · rw [callEntry_gpr' _ _ _ (by decide), hv.x0, State.withRegions_mem, State.callEntry_mem]; exact he
  all_goals rw [callEntry_gpr' _ _ _ (by decide), hv.x0, hvm _ (by decide), hv.vars _ (by decide)]; decide

/-- After the heights. -/
structure HPost (p : Params) (σ : State) (S sig : Addr) (pk a sk M : List Byte) (w : State) : Prop where
  x19 : w.gpr .x19 = S
  kept : ∀ r ∈ kept, w.gpr r = σ.gpr r
  sp : w.sp = σ.sp
  rd : w.rd = σ.rd
  wr : w.wr = σ.wr
  vcs : ∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64
  env : Env p w.mem S pk a
  saved : Spill.Saved S σ.gpr slots1 w.mem
  root : bytesAt w.mem (at' S Layout.oN) p.n = xmssNode p sk 0 p.hp pk (treeAdrs a)
  xsig : (σ.gpr .x1).toNat < 2 ^ p.hp →
    bytesAt w.mem sig p.xmssSigLen = xmssSign p M sk (σ.gpr .x1).toNat pk (treeAdrs a)
  frame : Frame (changes p S ++ [⟨sig, p.xmssSigLen⟩]) σ.mem w.mem

/-- The code of the heights. -/
abbrev heightsCode (p : Params) (T : Thash4Impl p.n) (t4name ln : String) : Prog isa :=
  Impl.SlhDsa.AArch64.Xmss.heights ⟨p.n, p.len⟩ p.hp t4name ln T.code

/-- The heights: the call of `levels` on the leaves. -/
theorem heights_ok (hz : Sz p) (T : Thash4Impl p.n) (t4name ln : String) (hC : Callees p T t4name)
    (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9) {σ : State} {S sig : Addr} {pk a sk M : List Byte}
    (hR : Regions σ S [] ⟨sig, p.xmssSigLen⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32)
    {u : State} (hI : LInv p σ S sig pk a sk M (2 ^ (p.hp - 2)) u) :
    WP isa (heightsCode p T t4name ln) u (HPost p σ S sig pk a sk M) := by
  have hn32 := hz.n32
  have hln : p.len * p.n ≤ 2144 := by rw [hz.len]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  have h512 : 2 ^ p.hp ≤ 512 :=
    calc 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp9
      _ = 512 := rfl
  have h4 := pow_hp hhp
  have ha : a.length = 16 := env_a16 hI.env
  have eN : Layout.oN = 12480 := rfl
  have eT : Layout.oSigTmp = 30144 := rfl
  have hwS := regions_scr hR
  have hws := regions_out hR
  have hsigd : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, Layout.oSigTmp⟩ := hR.out_scr
  have hSL := xmssSigLen_eq (p := p)
  have hcap : (2 ^ p.hp + 8) * p.n ≤ 16640 := by have := Nat.mul_le_mul (show 2 ^ p.hp + 8 ≤ 520 by omega) hn32; omega
  have hpn : p.hp * p.n ≤ 288 := Nat.mul_le_mul hhp9 hn32
  obtain ⟨AU, hAU⟩ : ∃ AU, AU = sig + BitVec.ofNat 64 (p.len * p.n) := ⟨_, rfl⟩
  unfold heightsCode Impl.SlhDsa.AArch64.Xmss.heights
  refine WP.seq (hblock_ok hz hhp9 hI.x19 hI.x21 (by rw [hI.wr]; exact hwS) (by rw [hI.wr]; exact hws) hR.out_fit
    hsigd fun v hv => ?_)
  rw [← hAU] at hv
  have hvfr : ∀ {o l : Nat}, o + l ≤ Layout.oVar 3 0 ∨ Layout.oVar 3 0 + 32 ≤ o → o + l ≤ Layout.oSigTmp →
      ∀ r ∈ [(⟨AU, p.hp * p.n⟩ : Region), ⟨at' S (Layout.oVar 3 0), 32⟩], Region.Disjoint ⟨at' S o, l⟩ r := by
    intro o l h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hAU]
      exact ((hsigd.sub_left (Offset.sub_base sig (by rw [hSL]))).sub_right (Offset.sub_base S h₂)).symm
    · exact disj_scr S h₁ (by rw [eT] at h₂; omega) (by rw [var_eq]; omega)
  have hvenv : Env p v.mem S pk a := env_frame hn32 hI.env hv.frame fun h₁ h₂ =>
    hvfr (by rw [var_eq]; simp only [Layout.oA] at h₁; omega) (by rw [eT]; simp only [Layout.oN] at h₂; omega)
  have h5 : v.gpr .x5 = σ.gpr .x1 := by rw [hv.x5, hI.x20]
  obtain ⟨hpre, hc, hw⟩ := levels_pre hz (by omega) hhp9 hR hAU hv (by rw [h5]; exact hidx)
    (by rw [hv.keep.wr, hI.wr]) hvenv
  refine WP.callV hC.levels.1 hpre hc hw (fun s' h₁ h₂ h₃ _ h₅ _ h₇ hpost => ?_) hC.levelsNF
  -- what the call did
  have E0 : (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]).gpr .x0 = S := by
    rw [callEntry_gpr' _ _ _ (by decide), hv.x0]
  have E1 : (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]).gpr .x1 = at' S Layout.oN := by
    rw [callEntry_gpr' _ _ _ (by decide), hv.x1]
  have h2h : (BitVec.ofNat 64 (2 ^ p.hp)).toNat = 2 ^ p.hp := by rw [BitVec.toNat_ofNat]; omega
  have E2 : ((v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]).gpr .x2).toNat = 2 ^ p.hp := by
    rw [callEntry_gpr' _ _ _ (by decide), hv.x2, h2h]
  have E3 : ((v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]).gpr .x3).toNat = 0 := by
    rw [callEntry_gpr' _ _ _ (by decide), hv.x3]; rfl
  have E4 : (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]).gpr .x4 = AU := by
    rw [callEntry_gpr' _ _ _ (by decide), hv.x4]
  have E5 : ((v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]).gpr .x5).toNat = (σ.gpr .x1).toNat := by
    rw [callEntry_gpr' _ _ _ (by decide), h5]
  have hlog : heightsOf (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]) = p.hp := by
    simp only [heightsOf]; rw [E2, Nat.log2_two_pow]
  have hV0 : (varAt v.mem S 3 0).toNat = 0 := by rw [hv.vars 0 (by decide)]; rfl
  have hV1 : (varAt v.mem S 3 1).toNat = 0 := by rw [hv.vars 1 (by decide)]; rfl
  have hV2 : (varAt v.mem S 3 2).toNat = TREE := by rw [hv.vars 2 (by decide)]; rfl
  have hV3 : (varAt v.mem S 3 3).toNat = 0 := by rw [hv.vars 3 (by decide)]; rfl
  simp only [levelsContract, E0, E1, E2, E3, E4, E5, hlog, State.withRegions_mem, State.callEntry_mem,
    hV0, hV1, hV2, hV3] at hpost
  obtain ⟨env₂, root₂, auth₂, fr₂⟩ := hpost pk a hvenv
  -- the regions, and what each frame keeps
  have hAUs : Region.Sub ⟨AU, p.hp * p.n⟩ ⟨sig, p.xmssSigLen⟩ := by rw [hAU]; exact Offset.sub_base sig (by rw [hSL])
  have hW0 : Region.Sub ⟨sig, p.len * p.n⟩ ⟨sig, p.xmssSigLen⟩ := Region.sub_prefix (by omega)
  have hWA : Region.Disjoint ⟨sig, p.len * p.n⟩ ⟨AU, p.hp * p.n⟩ := by
    have h := Offset.disjoint sig (d := 0) (n := p.len * p.n) (e := p.len * p.n) (k := p.hp * p.n) (.inl (by omega))
      (by have := hR.out_fit; simp only at this; omega) (by have := hR.out_fit; simp only at this; omega)
    rwa [← scr0 sig, ← hAU] at h
  have FU : Frame (Impl.SlhDsa.AArch64.Layout.oN |> fun _ => levelsChanges p S (at' S Layout.oN) (2 ^ p.hp) ++
      [⟨AU, p.hp * p.n⟩, ⟨at' S (Layout.oVar 3 0), 32⟩]) u.mem s'.mem := by
    refine (hv.frame.sub fun r hr => ?_).trans (fr₂.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  simp only at FU
  -- the parts of `scratch` the heights keep
  have hkeep : ∀ {o l : Nat}, 1008 ≤ o → o + l ≤ Layout.oVar 3 0 - 88 →
      ∀ r ∈ levelsChanges p S (at' S Layout.oN) (2 ^ p.hp) ++ [⟨AU, p.hp * p.n⟩, ⟨at' S (Layout.oVar 3 0), 32⟩],
        Region.Disjoint ⟨at' S o, l⟩ r := by
    intro o l h₁ h₂ r hr
    rw [var_eq] at h₂
    simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with (⟨k, hk, rfl⟩ | (rfl | rfl | rfl)) | (rfl | rfl)
    · exact disj_scr S (by rw [laneA_eq]; omega) (by omega) (by rw [laneA_eq]; omega)
    · have h : Region.Disjoint ⟨at' S o, l⟩ ⟨at' S 0, workUsed⟩ :=
        disj_scr S (by simp only [workUsed]; omega) (by omega) (by simp only [workUsed]; omega)
      rwa [show at' S 0 = S from (scr0 S).symm] at h
    · exact disj_scr S (by simp only [Layout.oFrame, Layout.oVars, Layout.frameLen]; omega) (by omega)
        (by simp only [Layout.oFrame, Layout.oVars, Layout.frameLen]; omega)
    · exact disj_scr S (by rw [eN]; omega) (by omega) (by rw [eN]; omega)
    · rw [hAU]
      exact ((hsigd.sub_left (Offset.sub_base sig (by rw [hSL]))).sub_right (Offset.sub_base S (by rw [eT]; omega))).symm
    · exact disj_scr S (by rw [var_eq]; omega) (by omega) (by rw [var_eq]; omega)
  -- the WOTS⁺ signature, outside what the heights change
  have hsigK : bytesAt s'.mem sig (p.len * p.n) = bytesAt u.mem sig (p.len * p.n) := by
    refine bytesAt_frame FU (fun r hr => ?_) (by omega)
    simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    have hlow : ∀ {o l : Nat}, o + l ≤ Layout.oSigTmp → Region.Disjoint ⟨sig, p.len * p.n⟩ ⟨at' S o, l⟩ :=
      fun h => (hsigd.sub_left hW0).sub_right (Offset.sub_base S h)
    rcases hr with (⟨k, hk, rfl⟩ | (rfl | rfl | rfl)) | (rfl | rfl)
    · exact hlow (by rw [laneA_eq, eT]; omega)
    · have h := hlow (o := 0) (l := workUsed) (by rw [eT]; simp only [workUsed]; omega)
      rwa [show at' S 0 = S from (scr0 S).symm] at h
    · exact hlow (by rw [eT]; simp only [Layout.oFrame, Layout.oVars, Layout.frameLen]; omega)
    · exact hlow (by rw [eT, eN]; omega)
    · exact hWA
    · exact hlow (by rw [eT, var_eq]; omega)
  -- the leaves, as `levels` read them
  have hL : nodesAt p v.mem (at' S Layout.oN) (2 ^ p.hp) =
      (List.range (2 ^ p.hp)).map fun j => xmssNode p sk j 0 pk (treeAdrs a) := by
    simp only [nodesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    have hin : (i + 1) * p.n ≤ 16384 := by have := Nat.mul_le_mul (show i + 1 ≤ 512 by omega) hn32; omega
    rw [at_add, bytesAt_frame hv.frame (hvfr (by rw [var_eq, eN]; omega)
      (by rw [eT, eN]; rw [Nat.add_mul, Nat.one_mul] at hin; omega)) (by omega)]
    exact hI.nodes i (by omega)
  have hup : ∀ r ≤ p.hp, upNodes p pk a TREE 0 0 0 (nodesAt p v.mem (at' S Layout.oN) (2 ^ p.hp)) r =
      (List.range (2 ^ (p.hp - r))).map fun j => xmssNode p sk j (0 + r) pk (treeAdrs a) := fun r hr => by
    rw [hL, show (List.range (2 ^ p.hp)).map (fun j => xmssNode p sk j 0 pk (treeAdrs a)) =
      (List.range (2 ^ (p.hp - r + r))).map (fun j => xmssNode p sk j 0 pk (treeAdrs a)) by
        rw [Nat.sub_add_cancel hr], upNodes_xmss ha sk pk r 0 (p.hp - r)]
  have hcs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = u.gpr r := fun r hr h30 => by
    rw [h₅ r hr h30, hv.keep.gpr r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)]
  have hsub : ∀ r ∈ levelsChanges p S (at' S Layout.oN) (2 ^ p.hp) ++ [⟨AU, p.hp * p.n⟩, ⟨at' S (Layout.oVar 3 0), 32⟩],
      ∃ R ∈ changes p S ++ [⟨sig, p.xmssSigLen⟩], Region.Sub r R := by
    intro r hr
    simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with (⟨k, hk, rfl⟩ | (rfl | rfl | rfl)) | (rfl | rfl)
    · refine ⟨⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩, ?_, Region.sub_prefix (by
        simp only [Layout.strideA]; omega)⟩
      simp only [changes, laneTails, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
      exact .inl (.inl (.inr ⟨k, hk, .inl rfl⟩))
    · exact ⟨_, by simp [changes], fun _ h => h⟩
    · exact ⟨⟨at' S Layout.oVars, 4 * Layout.frameLen⟩, by simp [changes],
        Offset.sub S (by simp [Layout.oFrame]) (by simp [Layout.oFrame, Layout.oVars, Layout.frameLen])⟩
    · exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp [changes], Region.sub_prefix (by
        rw [show Layout.nodeSlots = 520 from rfl]; omega)⟩
    · exact ⟨⟨sig, p.xmssSigLen⟩, by simp, hAUs⟩
    · exact ⟨⟨at' S Layout.oVars, 4 * Layout.frameLen⟩, by simp [changes],
        Offset.sub S (by rw [var_eq]; simp [Layout.oVars]) (by rw [var_eq]; simp [Layout.oVars, Layout.frameLen])⟩
  have hkt : ∀ r ∈ kept, s'.gpr r = σ.gpr r := fun r hr => by
    have hp : r ∈ preserved := by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [preserved]
    have h30 : r ≠ .x30 := by intro e; subst e; simp [kept] at hr
    rw [hcs r hp h30, hI.kept r hr]
  refine ⟨by rw [hcs _ (by simp [preserved]) (by decide), hI.x19], hkt,
    by rw [h₃, hv.keep.sp, hI.sp], by rw [h₁, hv.keep.rd, hI.rd], by rw [h₂, hv.keep.wr, hI.wr],
    fun r hr => by rw [h₇ r hr, hv.keep.vcs r hr, hI.vcs r hr], env₂,
    saved_keep hI.saved FU fun r hr => hkeep (by omega) (by rw [var_eq]; omega) r hr, ?_, fun hidx' => ?_,
    hI.frame.trans (FU.sub hsub)⟩
  · rw [root₂, hup p.hp (Nat.le_refl _), Nat.sub_self, Nat.pow_zero, List.range_one, List.map_cons, List.map_nil,
      List.getD_cons_zero, Nat.zero_add]
  · rw [hSL, bytesAt_app, ← hAU, bytesAt_flat s'.mem AU p.n p.hp, xmssSign_eq, hsigK, hI.wsig (by omega)]
    refine congrArg _ (Proof.SlhDsa.flatMap_range_congr fun r hr => ?_)
    have hz0 : bytesAt v.mem (AU + BitVec.ofNat 64 (r * p.n)) p.n = List.replicate p.n 0 := by
      refine bytesAt_eq (by simp) fun i hi => ?_
      have hrn : r * p.n + i < p.hp * p.n := by
        have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.hp by omega); rw [Nat.add_mul, Nat.one_mul] at this; omega
      have := congrArg (·.getD (r * p.n + i) 0) hv.zero
      rw [TreeBase.getD_bytesAt _ _ hrn] at this
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, this]
      simp [hi, hrn]
    rw [auth₂ r hr, hz0, hup r (by omega), pick_xmss hr hidx', xorB_zero (xmssNode_length hn32 _ _ _ _ _),
      Nat.zero_add]

/-! ## The whole function -/

/-- `xmssTree`'s code. -/
abbrev xmssCode (p : Params) (T : Thash4Impl p.n) (t4name wn ln : String) : Prog isa :=
  Impl.SlhDsa.AArch64.Xmss.xmssTree ⟨p.n, p.len⟩ p.hp t4name wn ln T.code

theorem restore1_eq : Impl.SlhDsa.AArch64.restoreRegs 1 Impl.SlhDsa.AArch64.Xmss.saved =
    Impl.SlhDsa.AArch64.restoreRegsAt 1152 [.x19, .x20, .x21, .x22, .x30] := rfl

/-- `xmssTree`, from its precondition: its postcondition and the calling convention. -/
theorem xmss_wp (hz : Sz p) (T : Thash4Impl p.n) (t4name wn ln : String) (hC : Callees p T t4name)
    (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9) {s : State} (hpre : (xmssContract p).pre s) :
    WP isa (xmssCode p T t4name wn ln) s fun s' => abiPreserved s s' ∧ (xmssContract p).post s s' := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have eN : Layout.oN = 12480 := rfl
  have eM : Layout.oMsg = 1984 := rfl
  have eT : Layout.oSigTmp = 30144 := rfl
  obtain ⟨hR, ⟨pk, a, hE⟩, hidx⟩ := hpre
  generalize hS : s.gpr .x0 = S at hR hE
  have hwS := regions_scr hR
  have hsk : SkAt p s.mem S (bytesAt s.mem (at' S Layout.oSkSeed) p.n) := rfl
  unfold xmssCode Impl.SlhDsa.AArch64.Xmss.xmssTree
  refine WP.seq (WP.mono (entry_ok hz hS hR hE hsk) fun u hu => ?_)
  refine WP.seq (WP.mono (leaves_ok hz T t4name wn hC hhp hhp9 hR hidx hu) fun u' hu' => ?_)
  refine WP.seq (WP.mono (heights_ok hz T t4name ln hC hhp hhp9 hR hidx hu') fun w hw => ?_)
  have hw8 : 8 * (p.n / 8) = p.n := by omega
  have hwS' : (⟨S, 65536⟩ : Region) ∈ w.wr := by rw [hw.wr]; exact hwS
  rw [restore1_eq, ← List.append_nil (Impl.SlhDsa.AArch64.restoreRegsAt _ _)]
  refine copyWords_ok (t := .x19) (sr := .x19) (d₂ := Layout.oMsg) (d₁ := Layout.oN) (w := p.n / 8)
    ⟨by decide, by decide, by rw [eN]; omega, by rw [eM]; omega, by rw [hw.x19, hw8]; exact in_scr' hwS' (by omega),
      by rw [hw.x19, hw8]; exact in_scr hwS' (by omega),
      by rw [hw.x19, hw8]; exact disj_scr S (by omega) (by omega) (by omega)⟩
    fun w₁ k₁ f₁ c₁ => ?_
  rw [hw.x19, hw8] at f₁ c₁
  have h19₁ : w₁.gpr .x19 = S := by rw [k₁.get .x19, hw.x19]
  refine restoreRegsAt_ok (by decide) (by decide)
    (by rw [h19₁, k₁.rd, k₁.wr]; exact in_scr' hwS' (by simp only [List.length_cons, List.length_nil]; omega)) fun t' o' g' => MlKem.AArch64.wp_nil ?_
  -- the saved registers
  have hsv : Spill.Saved S s.gpr slots1 w₁.mem := saved_keep hw.saved f₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact disj_scr S (by omega) (by omega) (by omega)
  have hg : ∀ (i : Nat) (h : i < 5), t'.gpr ([Reg.x19, .x20, .x21, .x22, .x30][i]) =
      s.gpr ([Reg.x19, .x20, .x21, .x22, .x30][i]) := fun i h => by
    rw [g' i h, h19₁]
    have := hsv ([Reg.x19, .x20, .x21, .x22, .x30][i], 1152 + 8 * i) (by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [slots1])
    exact this
  have hF : Frame (changes p S ++ [⟨s.gpr .x2, p.xmssSigLen⟩]) s.mem t'.mem := by
    rw [o'.mem]
    exact hw.frame.trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨at' S Layout.oMsg, 64⟩, by simp [changes], Region.sub_prefix (by omega)⟩)
  refine ⟨⟨fun r hr => ?_, by rw [o'.sp, k₁.sp, hw.sp], fun r hr => by rw [o'.vcs r hr, k₁.vcs r hr, hw.vcs r hr]⟩,
    fun pk' a' sk' hE' hsk' => ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg 0 (by decide)
    · exact hg 1 (by decide)
    · exact hg 2 (by decide)
    · exact hg 3 (by decide)
    all_goals first
      | exact hg 4 (by decide)
      | (rw [o'.gpr _ (by decide), k₁.get _ (by decide)]; exact hw.kept _ (by decide))
  -- the postcondition
  simp only [hS] at hE' hsk' ⊢
  obtain ⟨rfl, rfl⟩ := env_unique hE hE'
  have e₃ : sk' = bytesAt s.mem (at' S Layout.oSkSeed) p.n := hsk'.symm
  subst e₃
  refine ⟨?_, ?_, fun hi => ?_, hF⟩
  · rw [o'.mem]
    exact env_frame hn32 hw.env f₁ fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by simp only [Layout.oA] at h₁; omega) (by simp only [Layout.oN] at h₂; omega) (by omega)
  · rw [o'.mem, c₁, hw.root]
  · rw [o'.mem, bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.out_scr.sub_right (Offset.sub_base S (by omega))) (by have := hR.out_fit; simp only at this; omega)]
    exact hw.xsig hi

/-- The first part of `Verified`. -/
theorem xmss_correct (hz : Sz p) (T : Thash4Impl p.n) (t4name wn ln : String) (hC : Callees p T t4name)
    (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9) :
    ∀ s, (xmssContract p).pre s → ∃ t s',
      Exec isa (xmssCode p T t4name wn ln) s t s' ∧ abiPreserved s s' ∧ (xmssContract p).post s s' :=
  fun s h => by
    obtain ⟨t, s', e, abi, post⟩ := xmss_wp hz T t4name wn ln hC hhp hhp9 h
    exact ⟨t, s', e, abi, post⟩

end VG.Proof.SlhDsa.AArch64.Xmss
