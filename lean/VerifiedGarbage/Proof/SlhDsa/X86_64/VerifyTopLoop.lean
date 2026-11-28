module

-- separate module: the layers' loop, one stage of the chain of verify's proof

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopBody
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopPro
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkDigits
import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsLeaf
import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGen

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: the hypertree's layers

Untrusted: everything here is checked by Lean. Before layer `j` (`LI`): its
tree and leaf index in variables 0 and 1, `j` in variable 2, its XMSS
signature's address in variable 3, and the root below at `oMsg`, as
`htFold` gives them; a layer (`layer_ok`) gives the next, and the loop all
`d` (`loop_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave treeLanes stk)
open VG.Impl.SlhDsa.X86_64.Verify (vvar fVSig forsPk xmssPk layerBody)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_store ea_at)

/-- The XMSS signatures of the hypertree. -/
abbrev sigHt (p : Params) (L : VL) (m₀ : Mem) : List Byte :=
  bytesAt m₀ (L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen)) (p.d * p.xmssSigLen)

/-- Before layer `j`, from FORS's public key `F` and the indices `T`, `Lf`. -/
structure LI (p : Params) (L : VL) (g : Reg → BitVec 64) (m₀ : Mem) (F : List Byte) (T Lf j : Nat) (t : State) :
    Prop where
  ctx : Ctx L g m₀ t
  v0 : t.mem.readW (L.var 0) 64 = BitVec.ofNat 64 (htFold p F (sigHt p L m₀) (bytesAt m₀ L.pk L.n) T Lf j).2.1
  v1 : t.mem.readW (L.var 1) 64 = BitVec.ofNat 64 (htFold p F (sigHt p L m₀) (bytesAt m₀ L.pk L.n) T Lf j).2.2
  v2 : t.mem.readW (L.var 2) 64 = BitVec.ofNat 64 j
  v3 : t.mem.readW (L.var 3) 64 = L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)
  msg : bytesAt t.mem (at' L.S Layout.oMsg) p.n = (htFold p F (sigHt p L m₀) (bytesAt m₀ L.pk L.n) T Lf j).1

theorem htFold_tree (p : Params) (M sigHt pkSeed : List Byte) (T Lf : Nat) :
    ∀ j, (htFold p M sigHt pkSeed T Lf j).2.1 ≤ T
  | 0 => by simp [htFold_zero]
  | j + 1 => by
    rw [htFold_succ]
    simp only [htStep, Nat.shiftRight_eq_div_pow]
    exact Nat.le_trans (Nat.div_le_self _ _) (htFold_tree p M sigHt pkSeed T Lf j)

theorem htFold_leaf (p : Params) (M sigHt pkSeed : List Byte) (T Lf : Nat) (h : Lf < 2 ^ p.hp) :
    ∀ j, (htFold p M sigHt pkSeed T Lf j).2.2 < 2 ^ p.hp
  | 0 => by simp [htFold_zero, h]
  | j + 1 => by
    rw [htFold_succ]
    exact Nat.mod_lt _ (Nat.pow_pos (by decide))

theorem var_sep (L : VL) {i j : Nat} (h : i ≠ j) (hi : i < 4) (hj : j < 4) :
    Mem.Sep (L.var i) (64 / 8) (L.var j) (64 / 8) :=
  Offset.sep L.S (by omega) (by rw [show oKgSave = 34080 from rfl]; omega) (by rw [show oKgSave = 34080 from rfl]; omega)

theorem ofNat_of_toNat {x : BitVec 64} {v : Nat} (h : x.toNat = v) : x = BitVec.ofNat 64 v := by
  subst h; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem toNat_ofNat64 {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

variable {L : VL} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The block after `xmssPk`: the next layer's indices, and the comparison. -/
theorem next_ok {p : Params} (hp : VPar p) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {tr j : Nat}
    (htr : tr < 2 ^ 64) (hj : j < p.d) {a3 : Addr}
    (h0 : t.mem.readW (L.var 0) 64 = BitVec.ofNat 64 tr) (h2 : t.mem.readW (L.var 2) 64 = BitVec.ofNat 64 j)
    (h3 : t.mem.readW (L.var 3) 64 = a3) :
    WP isa (.block [.mov .rax (.mem (vvar 3)), .alu .add .rax (.imm (BitVec.ofNat 32 p.xmssSigLen)), .store (vvar 3) .rax,
        .mov .rax (.mem (vvar 0)), .mov .rcx (.reg .rax), .alu .and .rcx (.imm (BitVec.ofNat 32 (2 ^ p.hp - 1))),
        .store (vvar 1) .rcx, .shift .shr .rax p.hp, .store (vvar 0) .rax,
        .mov .rax (.mem (vvar 2)), .alu .add .rax (.imm 1), .store (vvar 2) .rax,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 p.d))]) t fun s' => Ctx L g m₀ s' ∧
      isa.eval .ne s' = some (decide (j + 1 ≠ p.d)) ∧
      s'.mem.readW (L.var 0) 64 = BitVec.ofNat 64 (tr >>> p.hp) ∧
      s'.mem.readW (L.var 1) 64 = BitVec.ofNat 64 (tr % 2 ^ p.hp) ∧
      s'.mem.readW (L.var 2) 64 = BitVec.ofNat 64 (j + 1) ∧
      s'.mem.readW (L.var 3) 64 = a3 + BitVec.ofNat 64 p.xmssSigLen ∧
      bytesAt s'.mem (at' L.S Layout.oMsg) p.n = bytesAt t.mem (at' L.S Layout.oMsg) p.n := by
  have hhp := hp.hp9
  have hd := hp.d22
  have hxs := hp.xsl
  have hm : 2 ^ p.hp - 1 < 2 ^ 31 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hhp; omega
  have hb : t.gpr .rbx = L.S := hc.rbx
  refine wp_movm (by rw [ea_vvar, hb]) (inVar hc (by omega)) fun t₁ u₁ => wp_addi fun t₂ u₂ => ?_
  have hb₂ : t₂.gpr .rbx = L.S := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb]
  refine wp_store (a := L.var 3) (by rw [ea_vvar, hb₂]) (by rw [u₂.wr, u₁.wr]; exact var_in hc (by omega))
    fun t₃ g₃ m₃ r₃ w₃ => ?_
  refine wp_movm (a := L.var 0) (by rw [ea_vvar, g₃, hb₂])
    (by rw [r₃, w₃, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact inVar hc (by omega)) fun t₄ u₄ => wp_mov fun t₅ u₅ => ?_
  refine VG.Proof.SlhDsa.X86_64.wp_andi fun t₆ u₆ => ?_
  have hb₆ : t₆.gpr .rbx = L.S := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃, hb₂]
  have hw₆ : t₆.wr = t.wr := by rw [u₆.wr, u₅.wr, u₄.wr, w₃, u₂.wr, u₁.wr]
  have hr₆ : t₆.rd = t.rd := by rw [u₆.rd, u₅.rd, u₄.rd, r₃, u₂.rd, u₁.rd]
  refine wp_store (a := L.var 1) (by rw [ea_vvar, hb₆]) (by rw [hw₆]; exact var_in hc (by omega))
    fun t₇ g₇ m₇ r₇ w₇ => ?_
  refine Levels.wp_shr (n := p.hp) hp.hp1 (by omega) fun t₈ u₈ => ?_
  have hb₈ : t₈.gpr .rbx = L.S := by rw [u₈.other _ (by decide), g₇, hb₆]
  refine wp_store (a := L.var 0) (by rw [ea_vvar, hb₈]) (by rw [u₈.wr, w₇, hw₆]; exact var_in hc (by omega))
    fun t₉ g₉ m₉ r₉ w₉ => ?_
  refine wp_movm (a := L.var 2) (by rw [ea_vvar, g₉, hb₈])
    (by rw [r₉, w₉, u₈.rd, u₈.wr, r₇, w₇, hr₆, hw₆]; exact inVar hc (by omega)) fun t₁₀ u₁₀ => wp_addi fun t₁₁ u₁₁ => ?_
  have hb₁₁ : t₁₁.gpr .rbx = L.S := by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), g₉, hb₈]
  refine wp_store (a := L.var 2) (by rw [ea_vvar, hb₁₁])
    (by rw [u₁₁.wr, u₁₀.wr, w₉, u₈.wr, w₇, hw₆]; exact var_in hc (by omega)) fun t₁₂ g₁₂ m₁₂ r₁₂ w₁₂ => ?_
  refine Fors.wp_cmpiC fun t₁₃ g₁₃ m₁₃ r₁₃ w₁₃ z₁₃ _ => WP.block_nil ?_
  -- the values read
  have e0 : t₄.gpr .rax = BitVec.ofNat 64 tr := by
    rw [u₄.gpr, m₃, Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide), u₂.mem, u₁.mem, h0]
  have e2 : t₁₀.gpr .rax = BitVec.ofNat 64 j := by
    rw [u₁₀.gpr, m₉, Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide), u₈.mem, m₇,
      Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide), u₆.mem, u₅.mem, u₄.mem, m₃,
      Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide), u₂.mem, u₁.mem, h2]
  have hj64 : j + 1 < 2 ^ 64 := by omega
  have v2 : t₁₁.gpr .rax = BitVec.ofNat 64 (j + 1) := by
    rw [u₁₁.gpr, e2, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
  -- the memory
  have hm₁₃ : t₁₃.mem = ((((t.mem.writeW (L.var 3) (t₂.gpr .rax)).writeW (L.var 1) (t₆.gpr .rcx)).writeW (L.var 0)
      (t₈.gpr .rax)).writeW (L.var 2) (t₁₁.gpr .rax)) := by
    rw [m₁₃, m₁₂, u₁₁.mem, u₁₀.mem, m₉, u₈.mem, m₇, u₆.mem, u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]
  have hvc : ∀ i < 4, Region.Contains ⟨at' L.S (oKgSave + 48), 32⟩ (L.var i) 8 := fun i hi => by
    show Region.Contains ⟨L.S + BitVec.ofNat 64 (oKgSave + 48), 32⟩ (L.S + BitVec.ofNat 64 (oKgSave + 48 + 8 * i)) 8
    rw [show oKgSave = 34080 from rfl]; exact Offset.contains L.S (by omega) (by omega) (by omega)
  have hf : Frame [⟨at' L.S (oKgSave + 48), 32⟩] t.mem t₁₃.mem := by
    rw [hm₁₃]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hvc 3 (by omega))).writeW (List.mem_singleton_self _)
      _ (hvc 1 (by omega))).writeW (List.mem_singleton_self _) _ (hvc 0 (by omega))).writeW
      (List.mem_singleton_self _) _ (hvc 2 (by omega))
  have hg : ∀ r, r ≠ .rax → r ≠ .rcx → t₁₃.gpr r = t.gpr r := fun r h1 h2 => by
    rw [g₁₃, g₁₂, u₁₁.other _ h1, u₁₀.other _ h1, g₉, u₈.other _ h1, g₇, u₆.other _ h2, u₅.other _ h2, u₄.other _ h1,
      g₃, u₂.other _ h1, u₁.other _ h1]
  have hcs : ∀ r ∈ calleeSaved, r ≠ .rax ∧ r ≠ .rcx := fun r hr => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  refine ⟨hc.of_frame hL (by rw [r₁₃, r₁₂, u₁₁.rd, u₁₀.rd, r₉, u₈.rd, r₇, hr₆])
      (by rw [w₁₃, w₁₂, u₁₁.wr, u₁₀.wr, w₉, u₈.wr, w₇, hw₆]) (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide))
      (fun r hr _ _ => hg r (hcs r hr).1 (hcs r hr).2) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact free_vars hL), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ForsCT.eval_ne', z₁₃, g₁₂, v2]
    simp only [Option.map_some, Option.some.injEq]
    rw [Levels.sx_ofNat (by omega)]
    by_cases e : j + 1 = p.d
    · rw [e]; simp
    · have : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 p.d ≠ 0 := by
        intro h
        have h' : BitVec.ofNat 64 (j + 1) = BitVec.ofNat 64 p.d := by
          have := BitVec.sub_add_cancel (BitVec.ofNat 64 (j + 1)) (BitVec.ofNat 64 p.d)
          rw [h] at this; simpa using this.symm
        have := congrArg BitVec.toNat h'
        rw [toNat_ofNat64 hj64, toNat_ofNat64 (by omega)] at this
        exact e this
      simp [e]
      exact this
  · rw [hm₁₃, Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64,
      u₈.gpr, g₇, u₆.other _ (by decide), u₅.other _ (by decide), e0]
    refine ofNat_of_toNat ?_
    rw [BitVec.toNat_ushiftRight, toNat_ofNat64 htr]
  · rw [hm₁₃, Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64, u₆.gpr,
      u₅.gpr, e0, Levels.sx_ofNat hm]
    refine ofNat_of_toNat ?_
    rw [BitVec.toNat_and, toNat_ofNat64 htr, toNat_ofNat64 (Nat.lt_trans hm (by decide)), Nat.and_two_pow_sub_one_eq_mod]
  · rw [hm₁₃, Mem.readW_writeW_self64, v2]
  · rw [hm₁₃, Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64, u₂.gpr,
      u₁.gpr, h3, Levels.sx_ofNat (n := p.xmssSigLen) hxs]
  · refine bytesAt_frame hf (fun r hr => ?_) (by have := hp.n; omega)
    simp only [List.mem_singleton] at hr; subst hr
    have := hp.n
    exact Levels.disj_scr L.S (by simp only [show Layout.oMsg = 30496 from rfl, show oKgSave = 34080 from rfl]; omega)
      (by simp only [show Layout.oMsg = 30496 from rfl]; omega) (by rw [show oKgSave = 34080 from rfl]; omega)

/-- At the call of `xmssPk` of layer `j`, from the state `t₀` before it. -/
structure LB1Post (p : Params) (L : VL) (g : Reg → BitVec 64) (m₀ : Mem) (F : List Byte) (T Lf j : Nat)
    (t₀ t : State) : Prop where
  ctx : Ctx L g m₀ t
  adr : Adr L t.mem (Proof.SlhDsa.layerTree j (htFold p F (sigHt p L m₀) (bytesAt m₀ L.pk L.n) T Lf j).2.1)
  rdi : t.gpr .rdi = L.S
  rsi : t.gpr .rsi = BitVec.ofNat 64 (htFold p F (sigHt p L m₀) (bytesAt m₀ L.pk L.n) T Lf j).2.2
  rdx : t.gpr .rdx = L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)
  vars : ∀ i < 4, t.mem.readW (L.var i) 64 = t₀.mem.readW (L.var i) 64
  msg : bytesAt t.mem (at' L.S Layout.oMsg) p.n = bytesAt t₀.mem (at' L.S Layout.oMsg) p.n

/-- Layer `j`'s first block: its addresses and `xmssPk`'s arguments. -/
theorem lb1_ok {p : Params} (hp : VPar p) (hL : L.Ok) (hn : L.n = p.n) {F : List Byte} {T Lf j : Nat}
    (hT : T < 2 ^ 64) (hj : j < p.d) {t : State} (hI : LI p L g m₀ F T Lf j t) :
    WP isa (.block (([.mov .r10 (.mem (vvar 2)), .mov .r9 (.mem (vvar 0))] : List Instr) ++ treeLanes p .r10 .r9 ++
        ([.mov .rdi (.reg .rbx), .mov .rsi (.mem (vvar 1)), .mov .rdx (.mem (vvar 3))] : List Instr))) t
      (LB1Post p L g m₀ F T Lf j t) := by
  have hd := hp.d22
  have hhp := hp.hp9
  have hc := hI.ctx
  have htr : (htFold p F (sigHt p L m₀) (bytesAt m₀ L.pk L.n) T Lf j).2.1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (htFold_tree p _ _ _ T Lf j) hT
  simp only [List.append_assoc, List.cons_append]
  refine wp_movm (a := L.var 2) (by rw [ea_vvar, hc.rbx]) (inVar hc (by omega)) fun t₁ u₁ =>
    wp_movm (a := L.var 0) (by rw [ea_vvar, u₁.other _ (by decide), hc.rbx])
      (by rw [u₁.rd, u₁.wr]; exact inVar hc (by omega)) fun t₂ u₂ => ?_
  have hc₂ : Ctx L g m₀ t₂ := (hc.regs u₁.rd u₁.wr u₁.mem fun r hr => u₁.other r (by
    intro e; subst e; revert hr; decide)).regs u₂.rd u₂.wr u₂.mem fun r hr => u₂.other r (by
    intro e; subst e; revert hr; decide)
  refine WP.block_append (M := isa) (l₁ := treeLanes p .r10 .r9) ?_
  refine lanes_ok hL hn (j := j) (T := (htFold p F (sigHt p L m₀) (bytesAt m₀ L.pk L.n) T Lf j).2.1) (by omega) htr hc₂
    (by rw [u₂.other _ (by decide), u₁.gpr, hI.v2, toNat_ofNat64 (by omega)]) (by rw [u₂.gpr, u₁.mem, hI.v0])
    fun u hcu hgu had hfu => ?_
  have hvu : ∀ i < 4, u.mem.readW (L.var i) 64 = t.mem.readW (L.var i) 64 := fun i hi => by
    rw [Thash4Avx.readW_frame hfu (vars_lanes hi), u₂.mem, u₁.mem]
  have hmu : bytesAt u.mem (at' L.S Layout.oMsg) p.n = bytesAt t.mem (at' L.S Layout.oMsg) p.n := by
    rw [bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := hp.n
      exact Levels.disj_scr L.S (by simp only [show Layout.oMsg = 30496 from rfl, Layout.oA]; omega)
        (by simp only [show Layout.oMsg = 30496 from rfl]; omega) (by simp only [Layout.oA]; omega)) (by have := hp.n; omega),
      u₂.mem, u₁.mem]
  refine wp_mov fun t₄ u₄ => wp_movm (a := L.var 1) (by rw [ea_vvar, u₄.other _ (by decide), hcu.rbx])
    (by rw [u₄.rd, u₄.wr]; exact inVar hcu (by omega)) fun t₅ u₅ =>
    wp_movm (a := L.var 3) (by rw [ea_vvar, u₅.other _ (by decide), u₄.other _ (by decide), hcu.rbx])
      (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact inVar hcu (by omega)) fun t₆ u₆ => WP.block_nil ?_
  have hm₆ : t₆.mem = u.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have hc₆ : Ctx L g m₀ t₆ := hcu.regs (by rw [u₆.rd, u₅.rd, u₄.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr]) hm₆
    fun r hr => by
      have h1 : r ≠ .rdx := by intro e; subst e; revert hr; decide
      have h2 : r ≠ .rsi := by intro e; subst e; revert hr; decide
      have h3 : r ≠ .rdi := by intro e; subst e; revert hr; decide
      rw [u₆.other _ h1, u₅.other _ h2, u₄.other _ h3]
  have e1 : t₆.gpr .rdi = L.S := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hcu.rbx]
  have e2 : t₆.gpr .rsi = BitVec.ofNat 64 (htFold p F (sigHt p L m₀) (bytesAt m₀ L.pk L.n) T Lf j).2.2 := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, hvu 1 (by omega), hI.v1]
  have e3 : t₆.gpr .rdx = L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen) := by
    rw [u₆.gpr, u₅.mem, u₄.mem, hvu 3 (by omega), hI.v3]
  refine ⟨hc₆, by rw [hm₆]; exact had, e1, e2, e3, fun i hi => by rw [hm₆, hvu i hi], by rw [hm₆, hmu]⟩

/-- Layer `j`. -/
theorem layer_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T4 : Thash4Impl p.n) (ht : f.t4 = T4.code)
    (hp : VPar p) (hst : T4.stack + 16 ≤ L.st) (hL : L.Ok) (hn : L.n = p.n) (hsl : L.sigL = p.sigLen)
    (gv : Impl.SlhDsa.X86_64.Verify.VFns) {F : List Byte} {T Lf j : Nat} (hT : T < 2 ^ 64) (hLf : Lf < 2 ^ p.hp)
    (hj : j < p.d) {t : State} (hI : LI p L g m₀ F T Lf j t) :
    WP isa (layerBody p f gv) t fun s' => isa.eval .ne s' = some (decide (j + 1 ≠ p.d)) ∧
      LI p L g m₀ F T Lf (j + 1) s' := by
  have hd := hp.d22
  have htr : (htFold p F (sigHt p L m₀) (bytesAt m₀ L.pk L.n) T Lf j).2.1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (htFold_tree p _ _ _ T Lf j) hT
  have hlf := htFold_leaf p F (sigHt p L m₀) (bytesAt m₀ L.pk L.n) T Lf hLf j
  unfold layerBody
  refine WP.seq (WP.mono (lb1_ok hp hL hn hT hj hI) fun t₆ hb => ?_)
  have hsl' : p.n + p.forsSigLen + j * p.xmssSigLen + p.xmssSigLen ≤ L.sigL := by
    rw [hsl, hp.sigLen]
    have := Nat.mul_le_mul_right p.xmssSigLen (show j + 1 ≤ p.d by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  refine WP.seq ?_
  refine WP.mono (xmssCall_ok T4 ht hp hst hL hn hsl' hb.ctx
    (a16 := Proof.SlhDsa.layerTree j (htFold p F (sigHt p L m₀) (bytesAt m₀ L.pk L.n) T Lf j).2.1) hb.adr hlf hb.rdi hb.rsi hb.rdx gv.xmssPkName)
    fun t₇ ⟨hc₇, hv₇, hmsg₇⟩ => ?_
  refine WP.mono (next_ok hp hL hc₇ htr hj (by rw [hv₇ 0 (by omega), hb.vars 0 (by omega), hI.v0])
    (by rw [hv₇ 2 (by omega), hb.vars 2 (by omega), hI.v2]) rfl) fun s' ⟨hc', hne, w0, w1, w2, w3, wm⟩ => ⟨hne, ?_⟩
  refine ⟨hc', ?_, ?_, w2, ?_, ?_⟩
  · rw [w0, htFold_succ]; rfl
  · rw [w1, htFold_succ]; rfl
  · rw [w3, hv₇ 3 (by omega), hb.vars 3 (by omega), hI.v3, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  · rw [wm, hmsg₇, htFold_succ]
    simp only [htStep]
    rw [hb.msg, hI.msg, sigHt, KeyGen.chunk_bytesAt _ _ hj, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      Nat.mul_comm p.xmssSigLen j]

/-- The `d` layers. -/
theorem loop_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T4 : Thash4Impl p.n) (ht : f.t4 = T4.code)
    (hp : VPar p) (hst : T4.stack + 16 ≤ L.st) (hL : L.Ok) (hn : L.n = p.n) (hsl : L.sigL = p.sigLen)
    (gv : Impl.SlhDsa.X86_64.Verify.VFns) {F : List Byte} {T Lf : Nat} (hT : T < 2 ^ 64) (hLf : Lf < 2 ^ p.hp)
    {t : State} (hI : LI p L g m₀ F T Lf 0 t) :
    WP isa (.loop (layerBody p f gv) .ne) t (LI p L g m₀ F T Lf p.d) := by
  have hd := hp.d1
  refine WP.loop (M := isa) (fun n s => n ≤ p.d ∧ 0 < n ∧ LI p L g m₀ F T Lf (p.d - n) s) (fun n s ⟨h1, h2, hI'⟩ => ?_) p.d t
    ⟨Nat.le_refl _, hd, by rw [Nat.sub_self]; exact hI⟩
  refine WP.mono (layer_ok T4 ht hp hst hL hn hsl gv hT hLf (j := p.d - n) (by omega) hI') fun s' ⟨hne, hI''⟩ => ?_
  by_cases e : p.d - n + 1 = p.d
  · left
    refine ⟨by rw [hne]; simp [e], ?_⟩
    rw [e] at hI''; exact hI''
  · right
    refine ⟨by rw [hne]; simp [e], n - 1, by omega, by omega, by omega, ?_⟩
    rw [show p.d - (n - 1) = p.d - n + 1 by omega]; exact hI''

/-- Before the loop: layer 0's leaf at `idx_leaf`, its signature after FORS's. -/
theorem start_ok {p : Params} (hp : VPar p) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {F : List Byte} {T Lf : Nat}
    (h0 : t.mem.readW (L.var 0) 64 = BitVec.ofNat 64 T) (h1 : t.mem.readW (L.var 1) 64 = BitVec.ofNat 64 Lf)
    (hm : bytesAt t.mem (at' L.S Layout.oMsg) p.n = F) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (vvar 2) .rax, .mov .rax (.mem (stk fVSig)),
        .alu .add .rax (.imm (BitVec.ofNat 32 (p.n + p.forsSigLen))), .store (vvar 3) .rax]) t
      (LI p L g m₀ F T Lf 0) := by
  have hfs := hp.fsl
  refine wp_mov32i fun t₁ u₁ => wp_store (a := L.var 2) (by rw [ea_vvar, u₁.other _ (by decide), hc.rbx])
    (by rw [u₁.wr]; exact var_in hc (by omega)) fun t₂ g₂ m₂ r₂ w₂ => ?_
  refine wp_movm (a := L.SP + BitVec.ofNat 64 16) (by rw [show stk fVSig = stk 16 from rfl, ea_stk, g₂,
    u₁.other _ (by decide), hc.rsp]) (by rw [r₂, w₂, u₁.rd, u₁.wr]; exact hc.inFr (by omega)) fun t₃ u₃ =>
    wp_addi fun t₄ u₄ => ?_
  refine wp_store (a := L.var 3) (by rw [ea_vvar, u₄.other _ (by decide), u₃.other _ (by decide), g₂,
    u₁.other _ (by decide), hc.rbx]) (by rw [u₄.wr, u₃.wr, w₂, u₁.wr]; exact var_in hc (by omega))
    fun t₅ g₅ m₅ r₅ w₅ => WP.block_nil ?_
  have hvc : ∀ i < 4, Region.Contains ⟨at' L.S (oKgSave + 48), 32⟩ (L.var i) 8 := fun i hi => by
    show Region.Contains ⟨L.S + BitVec.ofNat 64 (oKgSave + 48), 32⟩ (L.S + BitVec.ofNat 64 (oKgSave + 48 + 8 * i)) 8
    rw [show oKgSave = 34080 from rfl]; exact Offset.contains L.S (by omega) (by omega) (by omega)
  have hm₅ : t₅.mem = (t.mem.writeW (L.var 2) (t₁.gpr .rax)).writeW (L.var 3) (t₄.gpr .rax) := by
    rw [m₅, u₄.mem, u₃.mem, m₂, u₁.mem]
  have hf : Frame [⟨at' L.S (oKgSave + 48), 32⟩] t.mem t₅.mem := by
    rw [hm₅]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hvc 2 (by omega))).writeW
      (List.mem_singleton_self _) _ (hvc 3 (by omega))
  have hg : ∀ r, r ≠ .rax → t₅.gpr r = t.gpr r := fun r h => by
    rw [g₅, u₄.other _ h, u₃.other _ h, g₂, u₁.other _ h]
  have hc₅ : Ctx L g m₀ t₅ := hc.of_frame hL (by rw [r₅, u₄.rd, u₃.rd, r₂, u₁.rd]) (by rw [w₅, u₄.wr, u₃.wr, w₂, u₁.wr])
    (hg _ (by decide)) (hg _ (by decide)) (fun r hr _ _ => hg r (by intro e; subst e; revert hr; decide)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact free_vars hL)
  refine ⟨hc₅, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm₅, Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide), h0]; rfl
  · rw [hm₅, Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide), h1]; rfl
  · rw [hm₅, Mem.readW_writeW_sep (var_sep L (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64, u₁.gpr]; rfl
  · rw [hm₅, Mem.readW_writeW_self64, u₄.gpr, u₃.gpr, m₂, Thash4Avx.readW_frame (frame_writeW _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.fr_scr (d := 16) (n := 8) (by omega)).sub_right (fun a h => hL.scr_sub
          (o := oKgSave + 48) (l := 32) (by rw [show oKgSave = 34080 from rfl]; omega) a (var_sub hL (i := 2) (by omega) a h))),
      u₁.mem, hc.pSig, Levels.sx_ofNat (by omega)]
    simp
  · rw [bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := hp.n
      exact Levels.disj_scr L.S (by simp only [show Layout.oMsg = 30496 from rfl, show oKgSave = 34080 from rfl]; omega)
        (by simp only [show Layout.oMsg = 30496 from rfl]; omega) (by rw [show oKgSave = 34080 from rfl]; omega))
      (by have := hp.n; omega), hm]
    rfl

end VG.Proof.SlhDsa.X86_64.VerifyTop
