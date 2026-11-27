module

import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlKem.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.MlKem.Arm.Reduce
meta import VerifiedGarbage.Proof.Framework.Range

/-! ### `MlKem.Arm.Ntt`, which this module and modules that import it used -/

section

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_ntt`

The registers saved and the table of the zetas stored (`setup_ok`); then the
layers, each `layF` of `wBlockN` on words (`Reduce.lean`,
`Proof/MlKem/Blocks.lean`), and the registers restored (`restore_ok`).

Each butterfly's code is symbolically executed once, for any state, length
and offset (`bfly_run`, `bflyC_run`), and stores its `op` of the two words
(`bfly_core`, `bflyC_core`): what `CoreOk` states of a butterfly's code. The
rest is for any such code: butterflies in a row (`grp_ok`), the loop over
groups of four (`grpLoop_ok`), a block of either kind (`blkS_ok`, `blkL_ok`,
which prove `BlockOk`), and a layer of any program that is such a block
(`lay_ok`), with the zetas of the table at `zB` (`Tab`). `LI` is what holds
between layers. The first six layers leave words less than `13 q` congruent
to the specification's (`layersF_rel`), and the last, of `opFC`, its
coefficients (`layerFC_val`, `ntt_split`). `NTT⁻¹` (`NttInv.lean`) uses all
but the butterflies.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.Ntt

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem

/-! ## Registers kept -/

/-- `s'` has the registers `rs`, and the regions and stack pointer, of `s`. -/
structure Keep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r ∈ rs, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem keep_iff {rs : List Reg} {s s' : State} :
    Keep rs s s' ↔ (∀ r ∈ rs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨fun h => ⟨h.gpr, h.rd, h.wr, h.sp⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- The lemmas that prove `Keep` after a symbolic execution (`run_block`). -/
macro "keep_regs" : tactic => `(tactic| plain_simp_names (
                   set_option linter.unusedSimpArgs false in
                   simp only [keep_iff, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
                     implies_true, and_self, and_true, true_and, reduceCtorEq, ↓reduceIte]))

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keep.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs s₂ s₃) :
    Keep rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s') (hs : ∀ r ∈ rs', r ∈ rs) :
    Keep rs' s s' :=
  ⟨fun r hr => h.gpr r (hs r hr), h.rd, h.wr, h.sp⟩

/-! ## Butterflies -/

/-- `-q` and `q` in `r8` and `r12`, the zeta `z` and its quotient in `r7` and
`r9`, and `c` in `r10`. -/
def ZetaIn (c : BitVec 32) (z : Zq) (s : State) : Prop :=
  s.gpr .r8 = Nq ∧ s.gpr .r12 = 3329 ∧ s.gpr .r7 = BitVec.ofNat 32 z.val ∧
    s.gpr .r9 = BitVec.ofNat 32 (zetaQuot z.val) ∧ s.gpr .r10 = c

/-- The registers the loop over a block's groups keeps. -/
abbrev bflyKeep : List Reg := [.r1, .r2, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- The registers a butterfly keeps. -/
abbrev coreKeep : List Reg := [.r0, .r1, .r2, .r3, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

theorem ZetaIn.keep {c : BitVec 32} {z : Zq} {s s' : State} (hk : Keep bflyKeep s s') (h : ZetaIn c z s) :
    ZetaIn c z s' :=
  ⟨(hk.gpr .r8 (by decide)).trans h.1, (hk.gpr .r12 (by decide)).trans h.2.1,
    (hk.gpr .r7 (by decide)).trans h.2.2.1, (hk.gpr .r9 (by decide)).trans h.2.2.2.1,
    (hk.gpr .r10 (by decide)).trans h.2.2.2.2⟩

/-- The code `code len o` stores what the butterfly `op` gives of the words
`j + o` and `j + o + len` of the polynomial at `p`, with `r0` pointing at
coefficient `j` and the registers as `C` says for the zeta. -/
def CoreOk (code : Nat → Nat → List Instr) (op : Word → Word → Zq → Word × Word) (C : Zq → State → Prop) : Prop :=
  ∀ (p : BitVec 32) (len j o : Nat), 0 < len → len ≤ 128 → o < 4 → j + o + len < 256 → p.toNat + 1024 ≤ 2 ^ 32 →
    ∀ (z : Zq) (G : WPoly) (s : State), s.gpr .r0 = p + BitVec.ofNat 32 (4 * j) → C z s →
      LP s.mem (State.addr p) G → polyRegion (State.addr p) ∈ s.wr →
      WP isa (.block (code len o)) s fun s' =>
        LP s'.mem (State.addr p) (wbfly op G (j + o) len z) ∧ Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        Keep coreKeep s s'

/-! ## Loads, stores and values -/

/-- A pointer to coefficient `j`, plus the offset of coefficient `j + k`. -/
theorem addr_at {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {j k : Nat} (h : j + k < 256) :
    State.addr (p + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 (4 * k)) = coeffAddr (State.addr p) (j + k) :=
  addr_coeff hp (Nat.mul_add 4 j k).symm h

theorem wr_at {p : BitVec 32} {s : State} (hw : polyRegion (State.addr p) ∈ s.wr) {j : Nat} (h : j < 256) :
    InRegions s.wr (coeffAddr (State.addr p) j) 4 :=
  inRegions_of hw (coeff_contains _ (by rw [n_eq]; exact h))

theorem rd_at {p : BitVec 32} {s : State} (hw : polyRegion (State.addr p) ∈ s.wr) {j : Nat} (h : j < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (State.addr p) j) 4 :=
  inRegions_of (List.mem_append_right _ hw) (coeff_contains _ (by rw [n_eq]; exact h))

theorem q_shl1 : (3329 : BitVec 32) <<< 1 = 6658 := by decide

/-! ## The butterflies of `NTT`, symbolically -/

section
variable {s : State} {x z zp : BitVec 32} {len o : Nat} (ho : 4 * (o + len) < 4096) (h0 : s.gpr .r0 = x)
  (h7 : s.gpr .r7 = z) (h8 : s.gpr .r8 = Nq) (h9 : s.gpr .r9 = zp) (h12 : s.gpr .r12 = 3329)
  (iA : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * o))) 4)
  (iB : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 4)
  (oA : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * o))) 4)
  (oB : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 4)
include ho h0 h7 h8 h9 h12 iA iB oA oB

theorem bfly_run :
    WP isa (.block (Impl.MlKem.Arm.bfly len o)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * (o + len))))
          (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 + 6658 -
            bmz (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) z zp)).writeW
        (State.addr (x + BitVec.ofNat 32 (4 * o)))
          (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 +
            bmz (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) z zp) ∧
      Keep coreKeep s s' := by
  have ho' : 4 * o < 4096 := by omega_using [ho]
  run_block [Impl.MlKem.Arm.bfly, mulz, bmz, h0, h7, h8, h9, h12, iA, iB, oA, oB, ho, ho', q_shl1]
  keep_regs

theorem bflyC_run (h10 : s.gpr .r10 = 40318) :
    WP isa (.block (bflyC len o)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * (o + len))))
          (bcan (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 + 6658 -
            bmz (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) z zp))).writeW
        (State.addr (x + BitVec.ofNat 32 (4 * o)))
          (bcan (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 +
            bmz (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) z zp)) ∧
      Keep coreKeep s s' := by
  have ho' : 4 * o < 4096 := by omega_using [ho]
  run_block [bflyC, canon, mulz, bmz, bcan, h0, h7, h8, h9, h10, h12, iA, iB, oA, oB, ho, ho', q_shl1]
  keep_regs

end

theorem bfly_core (c : BitVec 32) : CoreOk Impl.MlKem.Arm.bfly opF (ZetaIn c) := by
  intro p len j o hl hl' ho hj hp z G s h0 ⟨z8, z12, z7, z9, _⟩ hG hw
  have eA := addr_at hp (j := j) (k := o) (by omega_using [hj])
  have eB := addr_at hp (j := j) (k := o + len) (by omega_using [hj])
  have hjo : j + o < 256 := by omega_using [hj]
  have hjn : j + o < n := by rw [n_eq]; exact hjo
  have hjl : j + o + len < n := by rw [n_eq]; exact hj
  rw [← Nat.add_assoc] at eB
  refine WP.mono (bfly_run (len := len) (o := o) (by omega_using [hl', ho]) h0 z7 z8 z9 z12
    (by rw [eA]; exact rd_at hw hjo) (by rw [eB]; exact rd_at hw hj)
    (by rw [eA]; exact wr_at hw hjo) (by rw [eB]; exact wr_at hw hj)) fun s' ⟨hm, hk⟩ => ⟨?_, ?_, hk⟩
  · rw [hm, eA, eB, lp_word hG hjn, lp_word hG hjl]
    exact lp_bfly hG opF hl hjl z (toW_val _).symm (toW_val _).symm
  · rw [hm, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjl)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjn)

theorem bflyC_core : CoreOk bflyC opFC (ZetaIn 40318) := by
  intro p len j o hl hl' ho hj hp z G s h0 ⟨z8, z12, z7, z9, z10⟩ hG hw
  have eA := addr_at hp (j := j) (k := o) (by omega_using [hj])
  have eB := addr_at hp (j := j) (k := o + len) (by omega_using [hj])
  have hjo : j + o < 256 := by omega_using [hj]
  have hjn : j + o < n := by rw [n_eq]; exact hjo
  have hjl : j + o + len < n := by rw [n_eq]; exact hj
  rw [← Nat.add_assoc] at eB
  refine WP.mono (bflyC_run (len := len) (o := o) (by omega_using [hl', ho]) h0 z7 z8 z9 z12
    (by rw [eA]; exact rd_at hw hjo) (by rw [eB]; exact rd_at hw hj)
    (by rw [eA]; exact wr_at hw hjo) (by rw [eB]; exact wr_at hw hj) z10) fun s' ⟨hm, hk⟩ => ⟨?_, ?_, hk⟩
  · rw [hm, eA, eB, lp_word hG hjn, lp_word hG hjl]
    exact lp_bfly hG opFC hl hjl z (toW_val _).symm (toW_val _).symm
  · rw [hm, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjl)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjn)

/-! ## Butterflies in a row -/

theorem ptr_step (p : BitVec 32) (a : Nat) (c : BitVec 32) (b : Nat) (hc : c = BitVec.ofNat 32 (4 * b)) :
    p + BitVec.ofNat 32 (4 * a) + c = p + BitVec.ofNat 32 (4 * (a + b)) := by
  rw [hc, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem grpEnd_ok (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm 16), .subs .r3 .r3 (.imm 1)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 + 16 ∧ s'.gpr .r3 = s.gpr .r3 - 1 ∧ s'.z = (s.gpr .r3 - 1 == 0) ∧
        s'.mem = s.mem ∧ Keep bflyKeep s s' := by
  run_block []
  keep_regs

section
variable {code : Nat → Nat → List Instr} {op : Word → Word → Zq → Word × Word} {C : Zq → State → Prop}
  (hb : CoreOk code op C) (hC : ∀ z s s', Keep bflyKeep s s' → C z s → C z s')
include hb hC

/-- `u` butterflies in a row from coefficient `j`, where `r0` points. -/
theorem grp_ok {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {len j u : Nat} (hlen : 0 < len)
    (hl : len ≤ 128) (hu : u ≤ 4) (hj : j + u + len ≤ 256) (k : Nat) (G : WPoly) (s : State)
    (h0 : s.gpr .r0 = p + BitVec.ofNat 32 (4 * j)) (hz : C (zeta k) s) (hG : LP s.mem (State.addr p) G)
    (hw : polyRegion (State.addr p) ∈ s.wr) :
    WP isa (.block (grp (code len) u)) s fun s' =>
      LP s'.mem (State.addr p) (wBlockN op G len k j u) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ Keep coreKeep s s' := by
  refine wp_range_flatMap (M := isa) (fun t s' => LP s'.mem (State.addr p) (wBlockN op G len k j t) ∧
      Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ Keep coreKeep s s')
    (fun t s' ht ⟨hP, hf, hk'⟩ => ?_) u (Nat.le_refl _) s ⟨hG, Frame.refl _ _, Keep.refl _ _⟩
  refine WP.mono (hb p len j t hlen hl (by omega_using [ht, hu]) (by omega_using [ht, hj]) hp (zeta k) _ s'
    ((hk'.gpr .r0 (by decide)).trans h0) (hC _ s s' (hk'.mono (by decide)) hz) hP (by rw [hk'.wr]; exact hw))
    fun s'' ⟨hP', hf', hk''⟩ => ⟨?_, hf.trans hf', hk'.trans hk''⟩
  rw [wBlockN, foldl_range'_succ, ← wBlockN]; exact hP'

/-- The loop over `N` groups of four butterflies, from coefficient `start`. -/
theorem grpLoop_ok {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {len start N : Nat} (hlen : 0 < len)
    (hl : len ≤ 128) (hN : 0 < N) (hN' : N ≤ 32) (hs : start + 4 * N + len ≤ 256) (k : Nat) (G : WPoly) (s : State)
    (h0 : s.gpr .r0 = p + BitVec.ofNat 32 (4 * start)) (hz : C (zeta k) s) (hG : LP s.mem (State.addr p) G)
    (hw : polyRegion (State.addr p) ∈ s.wr) (h3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (N - 0))) :
    WP isa (grpLoop (code len)) s fun s' =>
      LP s'.mem (State.addr p) (wBlockN op G len k start (4 * N)) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + 4 * N)) ∧ Keep bflyKeep s s' := by
  refine wp_loop_ne (fun t s' => LP s'.mem (State.addr p) (wBlockN op G len k start (4 * t)) ∧
      Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + 4 * t)) ∧
      s'.gpr .r3 = BitVec.ofNat 32 (1 * (N - t)) ∧ Keep bflyKeep s s') hN
    (fun t ht s' ⟨hP, hf, h0', h3', hk⟩ => ?_) (fun _ ⟨hP, hf, h0', _, hk⟩ => ⟨hP, hf, h0', hk⟩)
    ⟨hG, Frame.refl _ _, by rw [h0, Nat.mul_zero, Nat.add_zero], h3, Keep.refl _ _⟩
  rw [WP.block_append_iff]
  refine WP.mono (grp_ok hb hC hp hlen hl (Nat.le_refl 4) (by omega_using [hs, ht]) k _ s' h0' (hC _ s s' hk hz) hP
    (by rw [hk.wr]; exact hw)) fun s₁ ⟨hP₁, hf₁, k₁⟩ => ?_
  refine WP.mono (grpEnd_ok s₁) fun s'' ⟨h0'', h3'', hz'', m'', k₂⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [m'', Nat.mul_succ, (wBlk_ok op).add]; exact hP₁
  · rw [m'']; exact hf.trans hf₁
  · rw [h0'', k₁.gpr .r0 (by decide), h0', ptr_step p _ 16 4 rfl,
      show start + 4 * t + 4 = start + 4 * (t + 1) by omega_using []]
  · rw [h3'', k₁.gpr .r3 (by decide), h3']; exact count_sub (k := 1) ht
  · exact hk.trans ((k₁.mono (by decide)).trans k₂)
  · rw [hz'', k₁.gpr .r3 (by decide), h3']; exact count_z (k := 1) ht (by decide) (by omega_using [hN'])

end

/-! ## A block -/

/-- The table of the zetas, each with its quotient, at `P`. -/
def Tab (m : Mem) (P : Addr) : Prop := ∀ j < 128, m.readW (P + BitVec.ofNat 64 (4 * j)) 32 =
  BitVec.ofNat 32 (zetaQuot (zetaTable.getD j 0) + 65536 * zetaTable.getD j 0)

/-- Writes elsewhere keep the table. -/
theorem Tab.frame {m m' : Mem} {P : Addr} (h : Tab m P) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (polyRegion P).Disjoint r) : Tab m' P := fun j hj => by
  rw [hf.readW (r := polyRegion P) (contains_off (by omega_using [hj]) (by omega_using [hj])) hd (by decide)]
  exact h j hj

/-- The zeta of index `k` of the table, unpacked. -/
theorem zeta_unpack {k : Nat} (hk : k < 128) :
    BitVec.ofNat 32 (zetaQuot (zetaTable.getD k 0) + 65536 * zetaTable.getD k 0) >>> 16 =
        BitVec.ofNat 32 (zeta k).val ∧
      BitVec.ofNat 32 (zetaQuot (zetaTable.getD k 0) + 65536 * zetaTable.getD k 0) -
          (BitVec.ofNat 32 (zetaQuot (zetaTable.getD k 0) + 65536 * zetaTable.getD k 0) >>> 16) <<< 16 =
        BitVec.ofNat 32 (zetaQuot (zeta k).val) := by
  rw [zetaTable_eq, zetas_getD hk]
  have hz := val_lt (zeta k)
  exact unpack (by omega_using [hz]) (zetaQuot_lt (zeta k).isLt)

/-- The pointer to the next zeta. -/
def nextZ (op : DpOp) (x : BitVec 32) : BitVec 32 := if op = .add then x + 4 else x - 4

theorem zetaPre_ok (op : DpOp) (hop : op = .add ∨ op = .sub) (s : State) {x : BitVec 32} (h1 : s.gpr .r1 = x)
    (hi : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block (zetaPre op)) s fun s' =>
      s'.gpr .r7 = s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 >>> 16 ∧
      s'.gpr .r9 = s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 -
        (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 >>> 16) <<< 16 ∧
      s'.gpr .r1 = (if op = .add then x + 4 else x - 4) ∧ s'.mem = s.mem ∧
      Keep [.r0, .r2, .r3, .r8, .r10, .r11, .r12, .lr] s s' := by
  rcases hop with rfl | rfl <;>
  · run_block [zetaPre, zetaLoad, h1, hi]
    keep_regs

theorem blkEnd_ok (c : Nat) (he : encodable (BitVec.ofNat 32 c) = true) (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 c)), .subs .r2 .r2 (.imm 1)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 c ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧
        s'.z = (s.gpr .r2 - 1 == 0) ∧ s'.mem = s.mem ∧
        Keep [.r1, .r7, .r8, .r9, .r10, .r11, .r12, .lr] s s' := by
  run_block [he]
  keep_regs

theorem movR3_ok (c : Nat) (he : encodable (BitVec.ofNat 32 c) = true) (s : State) :
    WP isa (.block [.mov .r3 (.imm (BitVec.ofNat 32 c))]) s fun s' =>
      s'.gpr .r3 = BitVec.ofNat 32 c ∧ s'.mem = s.mem ∧
        Keep [.r0, .r1, .r2, .r7, .r8, .r9, .r10, .r11, .r12, .lr] s s' := by
  run_block [he]
  keep_regs

/-- The registers a block and a layer keep. -/
abbrev blkKeep : List Reg := [.r8, .r10, .r11, .r12, .lr]

/-- The program `blk` is a block of the layer with `len` of the polynomial
at `p`: with `r0` at coefficient `start` and `r1` at entry `k` of the table
at `zB`, it runs the `len` butterflies `op` with `zeta k`, and leaves `r0`
at the next block, `r1` at the next entry and the count of blocks in `r2`
one less. -/
def BlockOk (blk : Prog isa) (op : Word → Word → Zq → Word × Word) (dop : DpOp) (c : BitVec 32) (len : Nat)
    (p zB : BitVec 32) : Prop :=
  ∀ (start k : Nat), start + 2 * len ≤ 256 → k < 128 → ∀ (G : WPoly) (s : State),
    s.gpr .r0 = p + BitVec.ofNat 32 (4 * start) → s.gpr .r1 = zB + BitVec.ofNat 32 (4 * k) → s.gpr .r8 = Nq →
    s.gpr .r12 = 3329 → s.gpr .r10 = c → LP s.mem (State.addr p) G → polyRegion (State.addr p) ∈ s.wr →
    polyRegion (State.addr zB) ∈ s.rd ++ s.wr → Tab s.mem (State.addr zB) →
    WP isa blk s fun s' =>
      LP s'.mem (State.addr p) (wBlockN op G len k start len) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + 2 * len)) ∧ s'.gpr .r1 = nextZ dop (s.gpr .r1) ∧
        s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧ Keep blkKeep s s'

/-- The zeta of a block, as `zetaPre` reads it. -/
theorem zeta_read {zB : BitVec 32} (hzf : zB.toNat + 1024 ≤ 2 ^ 32) {k : Nat} (hk : k < 128) {s : State}
    (hzw : polyRegion (State.addr zB) ∈ s.rd ++ s.wr) (ht : Tab s.mem (State.addr zB)) :
    InRegions (s.rd ++ s.wr) (State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 4 ∧
      s.mem.readW (State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 32 >>> 16 =
        BitVec.ofNat 32 (zeta k).val ∧
      s.mem.readW (State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 32 -
          (s.mem.readW (State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 32 >>> 16) <<< 16 =
        BitVec.ofNat 32 (zetaQuot (zeta k).val) := by
  have eS := addr_ptr zB (4 * k) 0 (by omega_using [hzf, hk])
  rw [eS, Nat.add_zero, ht k hk]
  exact ⟨inRegions_of hzw (contains_off (by omega_using [hk]) (by omega_using [hk])), zeta_unpack hk⟩

section
variable {code : Nat → Nat → List Instr} {op : Word → Word → Zq → Word × Word} {c : BitVec 32}
  (hb : CoreOk code op (ZetaIn c)) {p zB : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32)
  (hzf : zB.toNat + 1024 ≤ 2 ^ 32) {len : Nat} (hlen : 0 < len) (dop : DpOp) (hop : dop = .add ∨ dop = .sub)
include hb hp hzf hlen hop

/-- A block of at most four butterflies, in a row. -/
theorem blkS_ok (hl : len ≤ 4) : BlockOk (nttBlkS (code len) len dop) op dop c len p zB := by
  intro start k hs hk G s h0 h1 h8 h12 h10 hG hw hzw ht
  obtain ⟨hzi, hz7, hz9⟩ := zeta_read hzf hk hzw ht
  have he : encodable (BitVec.ofNat 32 (8 * len)) = true := by
    have : ∀ l < 5, encodable (BitVec.ofNat 32 (8 * l)) = true := by decide
    exact this len (by omega_using [hl])
  rw [nttBlkS, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zetaPre_ok dop hop s h1 hzi) fun s₁ ⟨e7, e9, e1, m₁, k₁⟩ => ?_
  rw [hz7] at e7
  rw [hz9] at e9
  refine WP.mono (grp_ok hb (fun _ _ _ hk h => h.keep hk) hp hlen (by omega_using [hl]) hl (by omega_using [hs])
    k G s₁ ((k₁.gpr .r0 (by decide)).trans h0)
    ⟨(k₁.gpr .r8 (by decide)).trans h8, (k₁.gpr .r12 (by decide)).trans h12, e7, e9,
      (k₁.gpr .r10 (by decide)).trans h10⟩ (by rw [m₁]; exact hG)
    (by rw [k₁.wr]; exact hw)) fun s₂ ⟨hP, hf, k₂⟩ => ?_
  refine WP.mono (blkEnd_ok (8 * len) he s₂) fun s' ⟨h0', h2', hz', m', k₃⟩ => ⟨by rw [m']; exact hP,
    by rw [m', ← m₁]; exact hf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0', k₂.gpr .r0 (by decide), k₁.gpr .r0 (by decide), h0, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega_using []
  · rw [k₃.gpr .r1 (by decide), k₂.gpr .r1 (by decide), e1, h1]; rfl
  · rw [h2', k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · rw [hz', k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · exact ((k₁.mono (rs' := blkKeep) (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))

/-- A longer block, four butterflies at a time. -/
theorem blkL_ok (hl : len ≤ 128) (hl4 : 4 * (len / 4) = len) :
    BlockOk (nttBlkL (code len) len dop) op dop c len p zB := by
  intro start k hs hk G s h0 h1 h8 h12 h10 hG hw hzw ht
  obtain ⟨hzi, hz7, hz9⟩ := zeta_read hzf hk hzw ht
  have he : encodable (BitVec.ofNat 32 (4 * len)) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 (4 * l)) = true := by decide
    exact this len (by omega_using [hl])
  have he3 : encodable (BitVec.ofNat 32 (len / 4)) = true := by
    have : ∀ l < 33, encodable (BitVec.ofNat 32 l) = true := by decide
    exact this (len / 4) (by omega_using [hl])
  rw [nttBlkL]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (zetaPre_ok dop hop s h1 hzi) fun s₁ ⟨e7, e9, e1, m₁, k₁⟩ => ?_
  rw [hz7] at e7
  rw [hz9] at e9
  refine WP.mono (movR3_ok (len / 4) he3 s₁) fun s₂ ⟨e3, m₂, k₂⟩ => ?_
  refine WP.seq (WP.mono (grpLoop_ok hb (fun _ _ _ hk h => h.keep hk) hp hlen hl (N := len / 4) (start := start)
    (by omega_using [hl4, hlen]) (by omega_using [hl]) (by omega_using [hl4, hs]) k G s₂
    ((k₂.gpr .r0 (by decide)).trans ((k₁.gpr .r0 (by decide)).trans h0))
    ⟨(k₂.gpr .r8 (by decide)).trans ((k₁.gpr .r8 (by decide)).trans h8),
      (k₂.gpr .r12 (by decide)).trans ((k₁.gpr .r12 (by decide)).trans h12),
      (k₂.gpr .r7 (by decide)).trans e7, (k₂.gpr .r9 (by decide)).trans e9,
      (k₂.gpr .r10 (by decide)).trans ((k₁.gpr .r10 (by decide)).trans h10)⟩
    (by rw [m₂, m₁]; exact hG) (by rw [k₂.wr, k₁.wr]; exact hw) (by rw [e3, Nat.sub_zero, Nat.one_mul]))
    fun s₃ ⟨hP, hf, h0₃, k₃⟩ => ?_)
  rw [hl4] at hP h0₃
  refine WP.mono (blkEnd_ok (4 * len) he s₃) fun s' ⟨h0', h2', hz', m', k₄⟩ => ⟨by rw [m']; exact hP,
    by rw [m', ← m₁, ← m₂]; exact hf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0', h0₃, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega_using []
  · rw [k₄.gpr .r1 (by decide), k₃.gpr .r1 (by decide), k₂.gpr .r1 (by decide), e1, h1]; rfl
  · rw [h2', k₃.gpr .r2 (by decide), k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · rw [hz', k₃.gpr .r2 (by decide), k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · exact (((k₁.mono (rs' := blkKeep) (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))

end

/-! ## A layer -/

theorem layPre_ok (c : Nat) (hc : c ≤ 128) (s : State) :
    WP isa (.block [.mov .r2 (.imm (BitVec.ofNat 32 c))]) s fun s' =>
      s'.gpr .r2 = BitVec.ofNat 32 c ∧ s'.mem = s.mem ∧ Keep [.r0, .r1, .r8, .r10, .r11, .r12, .lr] s s' := by
  have he : encodable (BitVec.ofNat 32 c) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 l) = true := by decide
    exact this c (by omega_using [hc])
  run_block [he]
  keep_regs

theorem layPost_ok (s : State) :
    WP isa (.block [.dp .sub .r0 .r0 (.imm 1024)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 - 1024 ∧ s'.mem = s.mem ∧ Keep [.r1, .r8, .r10, .r11, .r12, .lr] s s' := by
  run_block []
  keep_regs

/-- The facts about the lengths of the layers. -/
theorem lens_facts : ∀ len ∈ [2, 4, 8, 16, 32, 64, 128], 0 < len ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧
    0 < 128 / len ∧ 128 / len ≤ 128 := by
  decide

/-- A layer, from `r0` = `f` and the zeta of its first block at `r1`. -/
theorem lay_ok {blk : Prog isa} {op : Word → Word → Zq → Word × Word} {dop : DpOp} {c : BitVec 32} {len : Nat}
    {p zB : BitVec 32} (hblk : BlockOk blk op dop c len p zB) (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128])
    (zi : Nat → Nat) (hzi : ∀ b < 128 / len, zi b < 128)
    (hstep : ∀ b < 128 / len, nextZ dop (zB + BitVec.ofNat 32 (4 * zi b)) = zB + BitVec.ofNat 32 (4 * zi (b + 1)))
    (F : WPoly) (s : State) (h0 : s.gpr .r0 = p) (h1 : s.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi 0))
    (h8 : s.gpr .r8 = Nq) (h12 : s.gpr .r12 = 3329) (h10 : s.gpr .r10 = c) (hF : LP s.mem (State.addr p) F)
    (hw : polyRegion (State.addr p) ∈ s.wr) (hzw : polyRegion (State.addr zB) ∈ s.rd ++ s.wr)
    (hd : (polyRegion (State.addr zB)).Disjoint (polyRegion (State.addr p))) (ht : Tab s.mem (State.addr zB)) :
    WP isa (nttLay blk len) s fun s' =>
      LP s'.mem (State.addr p) (layF (wBlockN op) F len zi (128 / len)) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p ∧
        s'.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi (128 / len)) ∧ Keep blkKeep s s' := by
  obtain ⟨hl0, hl1, hl2, hl3, hl4⟩ := lens_facts len hlen
  have hdd : ∀ r ∈ [polyRegion (State.addr p)], (polyRegion (State.addr zB)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hd
  refine WP.seq (WP.mono (layPre_ok (128 / len) hl4 s) fun s₁ ⟨e2, m₁, k₁⟩ => WP.seq ?_)
  refine WP.mono (Q := fun (s₂ : State) => LP s₂.mem (State.addr p) (layF (wBlockN op) F len zi (128 / len)) ∧
      Frame [polyRegion (State.addr p)] s.mem s₂.mem ∧ s₂.gpr .r0 = p + BitVec.ofNat 32 (4 * 256) ∧
      s₂.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi (128 / len)) ∧ Keep blkKeep s s₂) ?_
    fun s₂ ⟨hP, hf, h0₂, h1₂, k₂⟩ => ?_
  · refine wp_loop_ne (fun b s' => LP s'.mem (State.addr p) (layF (wBlockN op) F len zi b) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (2 * len * b)) ∧
        s'.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi b) ∧ s'.gpr .r2 = BitVec.ofNat 32 (1 * (128 / len - b)) ∧
        Keep blkKeep s s') hl3 (fun b hb s' ⟨hP, hf, h0', h1', h2', hk⟩ => ?_)
      (fun s' ⟨hP, hf, h0', h1', _, hk⟩ => ⟨hP, hf, by rw [h0', hl2], h1', hk⟩)
      ⟨by rw [m₁]; exact hF, by rw [m₁]; exact Frame.refl _ _, by rw [k₁.gpr .r0 (by decide), h0]; simp,
        by rw [k₁.gpr .r1 (by decide), h1], by rw [e2]; simp, k₁.mono (by decide)⟩
    have hcm : 2 * len * b + 2 * len ≤ 256 := by
      have : 2 * len * (b + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega_using [hb])
      rw [Nat.mul_succ] at this; omega_using [hl2, this]
    refine WP.mono (hblk _ _ hcm (hzi b hb) _ s' h0' h1'
      ((hk.gpr .r8 (by decide)).trans h8) ((hk.gpr .r12 (by decide)).trans h12)
      ((hk.gpr .r10 (by decide)).trans h10) hP (by rw [hk.wr]; exact hw)
      (by rw [hk.rd, hk.wr]; exact hzw)
      (ht.frame hf hdd)) fun s'' ⟨hP', hf', h0'', h1'', h2'', hz'', hk'⟩ => ⟨⟨?_, hf.trans hf', ?_, ?_, ?_,
        hk.trans hk'⟩, ?_⟩
    · rw [layF, foldl_range_succ, ← layF]; exact hP'
    · rw [h0'', Nat.mul_succ]
    · rw [h1'', h1', hstep b hb]
    · rw [h2'', h2']; exact count_sub (k := 1) hb
    · rw [hz'', h2']; exact count_z (k := 1) hb (by decide) (by omega_using [hl4])
  · refine WP.mono (layPost_ok s₂) fun s' ⟨h0', m', k₃⟩ => ⟨by rw [m']; exact hP, by rw [m']; exact hf, ?_,
      by rw [k₃.gpr .r1 (by decide), h1₂], k₂.trans (k₃.mono (by decide))⟩
    rw [h0', h0₂]
    exact BitVec.add_sub_cancel _ _

/-! ## Between layers -/

section
variable (s₀ : State)

abbrev pf : BitVec 32 := s₀.gpr .r0
abbrev ps : BitVec 32 := s₀.gpr .r1
abbrev F : Addr := State.addr (pf s₀)
abbrev S : Addr := State.addr (ps s₀)
abbrev P : Poly := polyAt s₀.mem (F s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (F s₀), polyRegion (S s₀)]
  disj : (polyRegion (F s₀)).Disjoint (polyRegion (S s₀))
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitS : (ps s₀).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s₀.mem (F s₀)

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  sav : Saved m₁ (S s₀ + BitVec.ofNat 64 512) s₀.gpr
  tab : ∀ j < 128, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 =
    BitVec.ofNat 32 (zetaQuot (zetaTable.getD j 0) + 65536 * zetaTable.getD j 0)
  poly : PolyIs m₁ (F s₀) (P s₀)

/-- Between layers: the words `G` at `f`, entry `k` of the table at `r1`,
`-q` in `r8`, `q` in `r12` and `c` in `r10`, with the memory `m₁` after the
setup changed only at `f`. -/
structure LI (s₀ : State) (m₁ : Mem) (c : BitVec 32) (G : WPoly) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pf s₀
  r1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 (4 * k)
  r8 : s.gpr .r8 = Nq
  r12 : s.gpr .r12 = 3329
  r10 : s.gpr .r10 = c
  poly : LP s.mem (F s₀) G
  frame : Frame [polyRegion (F s₀)] m₁ s.mem
  keep : Keep [.lr] s₀ s

theorem LI.step {s₀ : State} {m₁ : Mem} {c : BitVec 32} {G G' : WPoly} {k k' : Nat} {s s' : State}
    (hI : LI s₀ m₁ c G k s) (hP : LP s'.mem (F s₀) G') (hf : Frame [polyRegion (F s₀)] s.mem s'.mem)
    (h0 : s'.gpr .r0 = pf s₀) (h1 : s'.gpr .r1 = ps s₀ + BitVec.ofNat 32 (4 * k')) (hk : Keep blkKeep s s') :
    LI s₀ m₁ c G' k' s' :=
  ⟨h0, h1, (hk.gpr .r8 (by decide)).trans hI.r8, (hk.gpr .r12 (by decide)).trans hI.r12,
    (hk.gpr .r10 (by decide)).trans hI.r10, hP, hI.frame.trans hf, hI.keep.trans (hk.mono (by decide))⟩

/-- A layer whose blocks are `blk`, between layers. -/
theorem layI_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {c : BitVec 32} {blk : Prog isa}
    {op : Word → Word → Zq → Word × Word} {dop : DpOp} {len : Nat}
    (hblk : BlockOk blk op dop c len (pf s₀) (ps s₀)) (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128])
    (zi : Nat → Nat) (hzi : ∀ b < 128 / len, zi b < 128)
    (hstep : ∀ b < 128 / len, nextZ dop (ps s₀ + BitVec.ofNat 32 (4 * zi b)) =
      ps s₀ + BitVec.ofNat 32 (4 * zi (b + 1))) {G : WPoly} {s : State} (hI : LI s₀ m₁ c G (zi 0) s) :
    WP isa (nttLay blk len) s fun s' =>
      LI s₀ m₁ c (layF (wBlockN op) G len zi (128 / len)) (zi (128 / len)) s' := by
  have hd : ∀ r ∈ [polyRegion (F s₀)], (polyRegion (S s₀)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm
  refine WP.mono (lay_ok hblk hlen zi hzi hstep G s hI.r0 hI.r1 hI.r8 hI.r12 hI.r10 hI.poly
    (by rw [hI.keep.wr, hp.wr]; simp) (by rw [hI.keep.rd, hI.keep.wr, hp.rd, hp.wr]; simp) hp.disj.symm
    (Tab.frame hm.tab hI.frame hd)) fun s' ⟨hP, hf, h0, h1, hk⟩ => hI.step hP hf h0 h1 hk

/-! ## The layers of `NTT` -/

/-- The chain of zeta indices of the layers `ls` of `NTT`, from `k`. -/
def Chain : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 128 / len ∧ Chain (256 / len) ls

/-- The zeta index after the layers `ls`, from `k`. -/
def chainEnd : Nat → List Nat → Nat
  | k, [] => k
  | _, len :: ls => chainEnd (256 / len) ls

theorem lens_fwd : ∀ len ∈ [2, 4, 8, 16, 32, 64, 128], 128 / len + 128 / len = 256 / len ∧ 256 / len ≤ 128 := by
  decide

/-- A layer of `NTT` whose blocks are `blk`, with the butterfly `op`. -/
theorem layF_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {c : BitVec 32} {blk : Prog isa}
    {op : Word → Word → Zq → Word × Word} {len : Nat} (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128])
    (hblk : BlockOk blk op .add c len (pf s₀) (ps s₀)) {G : WPoly} {s : State}
    (hI : LI s₀ m₁ c G (128 / len) s) :
    WP isa (nttLay blk len) s fun s' =>
      LI s₀ m₁ c (layF (wBlockN op) G len (fun b => 128 / len + b) (128 / len)) (256 / len) s' := by
  obtain ⟨h1, h2⟩ := lens_fwd len hlen
  refine WP.mono (layI_ok hp hm hblk hlen (fun b => 128 / len + b) (fun b hb => by omega_using [h1, h2, hb])
    (fun b _ => by
      simp only [nextZ, ite_true, BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
        ← BitVec.ofNat_add]
      congr 2) hI) fun s' hI' => ?_
  rw [h1] at hI'
  exact hI'

theorem lays_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {c : BitVec 32} (blk : Nat → Prog isa) :
    ∀ (ls : List Nat) (G : WPoly) (k : Nat) (s : State),
      (∀ len ∈ ls, len ∈ [2, 4, 8, 16, 32, 64, 128] ∧ BlockOk (blk len) opF .add c len (pf s₀) (ps s₀)) →
      Chain k ls → LI s₀ m₁ c G k s →
      WP isa (lays blk ls) s fun s' => LI s₀ m₁ c (ls.foldl layerF G) (chainEnd k ls) s'
  | [], _, _, _, _, _, hI => WP.block_nil hI
  | len :: ls, G, k, s, hls, ⟨hk, hc⟩, hI => by
    obtain ⟨hlen, hblk⟩ := hls len (List.mem_cons_self ..)
    exact WP.seq (WP.mono (layF_ok hp hm hlen hblk (hk ▸ hI)) fun s' hI' =>
      lays_ok hp hm blk ls _ (256 / len) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc hI')

/-- `NTT`, as the code's runs of layers. -/
theorem ntt_split (f : Poly) :
    Spec.MlKem.ntt f = nttLayer ([4].foldl nttLayer ([128, 64, 32, 16, 8].foldl nttLayer f)) 2 := by
  rw [ntt_eq_layers]
  simp only [nttLens, List.foldl_cons, List.foldl_nil]

/-! ## Setup and the end -/

/-- The registers saved and the table stored. -/
theorem setup_base {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r1 512 ++ tableZ zetaTable .r1)) s₀ fun s =>
      Setup s₀ s.mem ∧ (∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  have fS := hp.fitS
  have wS : ∀ {o n : Nat}, o + n ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) n := fun h => by
    rw [hp.wr]; exact inRegions_of (by simp) (contains_off h (by omega_arith))
  rw [WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r1 (off := 512) (by decide) (fit_le (by decide) fS) fun i hi => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact wS (by omega_arith)) fun s₁ h₁ => ?_
  have g1 : (s₁.gpr .r1) = ps s₀ := by rw [h₁.gpr]
  refine WP.mono (tableZ_ok zetaTable (by decide) (b := .r1) (by decide) (by rw [g1]; exact fit_le (by decide) fS)
    fun k hk => by rw [g1, h₁.wr]; exact wS (by omega_arith)) fun s₂ h₂ => ?_
  have hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · rw [List.mem_singleton] at hr; subst hr
      exact region_sub_off (by decide)
    · rw [List.mem_singleton] at hr; subst hr
      rw [g1, ← add_ofNat_zero (State.addr (ps s₀))]
      exact region_sub_off (by decide)
  have hm : Setup s₀ s₂.mem := by
    refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
    · rw [h₂.frame.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact h₁.saved i hi
      · rw [List.mem_singleton] at hr; subst hr
        rw [g1, add_ofNat_add, ← add_ofNat_zero (State.addr (ps s₀))]
        exact region_disj_off (by omega_arith) (by omega_arith) (by omega_arith) hS
    · have := h₂.tab j hj; rwa [g1] at this
    · exact polyIs_frame fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
        ⟨hp.red, rfl⟩
  exact ⟨hm, fun r hr => (h₂.gpr r hr).trans (by rw [h₁.gpr]), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r1 512 ++ tableZ zetaTable .r1 ++ constsN ++
      ([.dp .add .r1 .r1 (.imm 4), .movw .r10 40318] : List Instr)))
      s₀ fun s => Setup s₀ s.mem ∧ LI s₀ s.mem 40318 (lift (P s₀)) 1 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  have e0 := e .r0 (by decide)
  have e1 := e .r1 (by decide)
  have elr := e .lr (by decide)
  run_block [constsN, e0, e1, elr, rd, wr, sp, constsN_val, hm, true_and]
  exact ⟨by simp [e0], by simp, by simp, by simp, by simp, lp_lift hm.poly, Frame.refl _ _,
    ⟨fun r hr => by rw [List.mem_singleton] at hr; subst hr; simp [elr], rfl, rfl, rfl⟩⟩

/-- The registers restored, from a state that kept the working space. -/
theorem restore_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {s : State}
    (h1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 512) (hlr : s.gpr .lr = s₀.gpr .lr) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) (hf : Frame [polyRegion (F s₀)] m₁ s.mem) {f : Poly}
    (hP : PolyIs s.mem (F s₀) f) :
    WP isa (.block (restoreRegs .r1 0)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ PolyIs s'.mem (F s₀) f := by
  have fS := hp.fitS
  have hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have e1 : State.addr (s.gpr .r1) + BitVec.ofNat 64 0 = S s₀ + BitVec.ofNat 64 512 := by
    rw [h1, addr_add (by omega_arith), add_ofNat_zero]
  refine WP.mono (restoreRegs_ok .r1 (by decide) (off := 0) (by decide) (by rw [h1]; bv_omega)
    (g := s₀.gpr) (by
      rw [e1]
      intro i hi
      rw [hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact hm.sav i hi
      · rw [List.mem_singleton] at hr; subst hr
        refine hp.disj.symm.sub_left ?_
        rw [add_ofNat_add]
        exact region_sub_off (by omega_arith))
    fun i hi => by
      rw [e1, hrd, hwr, hp.wr, add_ofNat_add]
      exact inRegions_of (R := polyRegion (S s₀)) (by simp) (contains_off (by omega_arith) (by omega_arith)))
    fun s' h' => ⟨preserved_of_restore h' hlr, h'.sp.trans hsp, ?_⟩
  rw [h'.mem]
  exact hP

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ntt s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (F s₀) (Spec.MlKem.ntt (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, hI⟩ => ?_)
  refine WP.seq (WP.mono (lays_ok hp hm (fun len => nttBlkL (Impl.MlKem.Arm.bfly len) len .add)
    [128, 64, 32, 16, 8] _ 1 s₁ (fun len hl => ?_) (by simp only [Chain]; decide) hI) fun s₂ hI₂ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, blkL_ok (bfly_core _) hp.fitF hp.fitS (by decide) .add (.inl rfl) (by decide) (by decide)⟩
  refine WP.seq (WP.mono (lays_ok hp hm (fun len => nttBlkS (Impl.MlKem.Arm.bfly len) len .add)
    [4] _ 32 s₂ (fun len hl => ?_) (by simp only [Chain]; decide) hI₂) fun s₃ hI₃ => ?_)
  · rw [List.mem_singleton] at hl; subst hl
    exact ⟨by decide, blkS_ok (bfly_core _) hp.fitF hp.fitS (by decide) .add (.inl rfl) (by decide)⟩
  refine WP.seq (WP.mono (layF_ok hp hm (len := 2) (by decide)
    (blkS_ok bflyC_core hp.fitF hp.fitS (by decide) .add (.inl rfl) (by decide)) hI₃) fun s₄ hI₄ => ?_)
  refine restore_ok hp hm hI₄.r1 (hI₄.keep.gpr .lr (by decide)) hI₄.keep.rd hI₄.keep.wr hI₄.keep.sp hI₄.frame ?_
  have h11 : Rel 11 _ _ := layersF_rel [128, 64, 32, 16, 8] 1 _ _ (by decide) (by decide) (lift_rel (P s₀))
  have hr : Rel 13 _ _ := layersF_rel [4] 11 _ _ (by decide) (by decide) h11
  rw [ntt_split]
  refine polyIs_of_toNat fun j hj => ?_
  rw [hI₄.poly j hj]
  exact layerFC_val hr (by decide) (by rw [n_eq] at hj; exact hj)

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

end VG.Proof.MlKem.Arm.Ntt

end

end

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_inv_ntt`

As `vg_mlkem_ntt` (`Ntt.lean`), with the zetas from the last and the inverse
butterflies, which store the words `opI` gives (`ibfly_run`, `ibfly_core`):
the first six layers keep words less than `2q` congruent to those of
`NTT⁻¹` (`layersI_rel`). The last layer's one block is the loop over groups
of four of `ibflyS` (`grpLoop_ok` with `ibflyS_core`), with 3303 and the
layer's zeta times it in registers (`scalePre_ok`): it leaves the last
layer's coefficients times 3303 (`lastInv_val`), which `nttInv_split` says
is `NTT⁻¹`.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.NttInv

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Proof.MlKem.Arm.Ntt

/-! ## The inverse butterflies -/

section
variable {s : State} {x z zp : BitVec 32} {len o : Nat} (ho : 4 * (o + len) < 4096) (h0 : s.gpr .r0 = x)
  (h7 : s.gpr .r7 = z) (h8 : s.gpr .r8 = Nq) (h9 : s.gpr .r9 = zp) (h12 : s.gpr .r12 = 3329)
  (iA : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * o))) 4)
  (iB : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 4)
  (oA : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * o))) 4)
  (oB : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 4)
include ho h0 h7 h8 h9 h12 iA iB oA oB

theorem ibfly_run :
    WP isa (.block (ibfly len o)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * o)))
          (bpr (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 +
            s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32))).writeW
        (State.addr (x + BitVec.ofNat 32 (4 * (o + len))))
          (bmz (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32 + 6658 -
            s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32) z zp) ∧
      Keep coreKeep s s' := by
  have ho' : 4 * o < 4096 := by omega_using [ho]
  run_block [ibfly, mulz, bmz, bpr, h0, h7, h8, h9, h12, iA, iB, oA, oB, ho, ho', q_shl1]
  keep_regs

theorem ibflyS_run {f fp : BitVec 32} (h10 : s.gpr .r10 = f) (h11 : s.gpr .r11 = fp) :
    WP isa (.block (ibflyS len o)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * o)))
          (cs (bmz (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 +
            s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) f fp))).writeW
        (State.addr (x + BitVec.ofNat 32 (4 * (o + len))))
          (cs (bmz (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32 + 6658 -
            s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32) z zp)) ∧
      Keep coreKeep s s' := by
  have ho' : 4 * o < 4096 := by omega_using [ho]
  run_block [ibflyS, mulz, csub, bmz, cs, h0, h7, h8, h9, h10, h11, h12, iA, iB, oA, oB, ho, ho', q_shl1]
  keep_regs

end

theorem ibfly_core (c : BitVec 32) : CoreOk ibfly opI (ZetaIn c) := by
  intro p len j o hl hl' ho hj hp z G s h0 ⟨z8, z12, z7, z9, _⟩ hG hw
  have eA := addr_at hp (j := j) (k := o) (by omega_using [hj])
  have eB := addr_at hp (j := j) (k := o + len) (by omega_using [hj])
  have hjo : j + o < 256 := by omega_using [hj]
  have hjn : j + o < n := by rw [n_eq]; exact hjo
  have hjl : j + o + len < n := by rw [n_eq]; exact hj
  rw [← Nat.add_assoc] at eB
  refine WP.mono (ibfly_run (len := len) (o := o) (by omega_using [hl', ho]) h0 z7 z8 z9 z12
    (by rw [eA]; exact rd_at hw hjo) (by rw [eB]; exact rd_at hw hj)
    (by rw [eA]; exact wr_at hw hjo) (by rw [eB]; exact wr_at hw hj)) fun s' ⟨hm, hk⟩ => ⟨?_, ?_, hk⟩
  · rw [hm, eA, eB, lp_word hG hjn, lp_word hG hjl]
    exact lp_bflyInv hG opI hl hjl z (toW_val _).symm (toW_val _).symm
  · rw [hm, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjn)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjl)

/-- The registers of the last layer: `ZetaIn` of the zeta times 3303, with
3303 in `r10`, and its quotient in `r11`. -/
def ScaleIn (z : Zq) (s : State) : Prop :=
  ZetaIn (BitVec.ofNat 32 cInv.val) (z * cInv) s ∧ s.gpr .r11 = BitVec.ofNat 32 (zetaQuot cInv.val)

theorem ScaleIn.keep {z : Zq} {s s' : State} (hk : Keep bflyKeep s s') (h : ScaleIn z s) : ScaleIn z s' :=
  ⟨h.1.keep hk, (hk.gpr .r11 (by decide)).trans h.2⟩

theorem ibflyS_core : CoreOk ibflyS opIS ScaleIn := by
  intro p len j o hl hl' ho hj hp z G s h0 ⟨⟨z8, z12, z7, z9, z10⟩, z11⟩ hG hw
  have eA := addr_at hp (j := j) (k := o) (by omega_using [hj])
  have eB := addr_at hp (j := j) (k := o + len) (by omega_using [hj])
  have hjo : j + o < 256 := by omega_using [hj]
  have hjn : j + o < n := by rw [n_eq]; exact hjo
  have hjl : j + o + len < n := by rw [n_eq]; exact hj
  rw [← Nat.add_assoc] at eB
  refine WP.mono (ibflyS_run (len := len) (o := o) (by omega_using [hl', ho]) h0 z7 z8 z9 z12
    (by rw [eA]; exact rd_at hw hjo) (by rw [eB]; exact rd_at hw hj)
    (by rw [eA]; exact wr_at hw hjo) (by rw [eB]; exact wr_at hw hj) z10 z11) fun s' ⟨hm, hk⟩ => ⟨?_, ?_, hk⟩
  · rw [hm, eA, eB, lp_word hG hjn, lp_word hG hjl]
    exact lp_bflyInv hG opIS hl hjl z (toW_val _).symm (toW_val _).symm
  · rw [hm, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjn)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjl)

/-! ## The layers -/

/-- The chain of zeta indices of the layers `ls` of `NTT⁻¹`, from `k`. -/
def ChainInv : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 256 / len - 1 ∧ ChainInv (128 / len - 1) ls

/-- The zeta index after the layers `ls`, from `k`. -/
def chainEndInv : Nat → List Nat → Nat
  | k, [] => k
  | _, len :: ls => chainEndInv (128 / len - 1) ls

theorem lens_inv : ∀ len ∈ [2, 4, 8, 16, 32, 64, 128], 128 / len ≤ 256 / len - 1 ∧ 256 / len ≤ 128 ∧
    256 / len - 1 - 128 / len = 128 / len - 1 := by decide

/-- A layer of `NTT⁻¹` whose blocks are `blk`. -/
theorem layInv_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {c : BitVec 32} {blk : Prog isa}
    {len : Nat} (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128])
    (hblk : BlockOk blk opI .sub c len (pf s₀) (ps s₀)) {G : WPoly} {s : State}
    (hI : LI s₀ m₁ c G (256 / len - 1) s) :
    WP isa (nttLay blk len) s fun s' => LI s₀ m₁ c (layerI G len) (128 / len - 1) s' := by
  obtain ⟨h1, h2, h3⟩ := lens_inv len hlen
  refine WP.mono (layI_ok hp hm hblk hlen (fun b => 256 / len - 1 - b) (fun b hb => by omega_using [h2])
    (fun b hb => by
      simp only [nextZ, reduceCtorEq, ite_false]
      rw [show 4 * (256 / len - 1 - b) = 4 * (256 / len - 1 - (b + 1)) + 4 by omega_using [h1, hb],
        BitVec.ofNat_add, ← BitVec.add_assoc]
      exact BitVec.add_sub_cancel _ _) hI) fun s' hI' => ?_
  rw [h3] at hI'
  exact hI'

theorem lays_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {c : BitVec 32} (blk : Nat → Prog isa) :
    ∀ (ls : List Nat) (G : WPoly) (k : Nat) (s : State),
      (∀ len ∈ ls, len ∈ [2, 4, 8, 16, 32, 64, 128] ∧ BlockOk (blk len) opI .sub c len (pf s₀) (ps s₀)) →
      ChainInv k ls → LI s₀ m₁ c G k s →
      WP isa (lays blk ls) s fun s' => LI s₀ m₁ c (ls.foldl layerI G) (chainEndInv k ls) s'
  | [], _, _, _, _, _, hI => WP.block_nil hI
  | len :: ls, G, k, s, hls, ⟨hk, hc⟩, hI => by
    obtain ⟨hlen, hblk⟩ := hls len (List.mem_cons_self ..)
    exact WP.seq (WP.mono (layInv_ok hp hm hlen hblk (hk ▸ hI)) fun s' hI' =>
      lays_ok hp hm blk ls _ (128 / len - 1) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc hI')

/-- `NTT⁻¹`, as the code's runs of layers and its last layer. -/
theorem nttInv_split (f : Poly) : Spec.MlKem.nttInv f =
    (nttInvLayer ([8, 16, 32, 64].foldl nttInvLayer ([2, 4].foldl nttInvLayer f)) 128).map (· * 3303) := by
  rw [nttInv_eq_layers]
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil]

/-! ## The last layer -/

theorem scaleZeta_eq : scaleZeta = (zeta 1 * cInv).val := by
  have h : zetaTable.getD 1 0 = (zeta 1).val := by rw [zetaTable_eq]; exact zetas_getD (by decide)
  rw [Fin.val_mul, ← h]
  rfl

theorem scaleZeta_word : (BitVec.ofNat 16 scaleZeta).setWidth 32 = BitVec.ofNat 32 (zeta 1 * cInv).val := by
  rw [movw_val (by rw [scaleZeta_eq]; exact Nat.lt_trans (val_lt _) (by decide)), scaleZeta_eq]

theorem scaleQuot_word :
    (BitVec.ofNat 16 (zetaQuot scaleZeta)).setWidth 32 = BitVec.ofNat 32 (zetaQuot (zeta 1 * cInv).val) := by
  rw [movw_val (by rw [scaleZeta_eq]; exact zetaQuot_lt (zeta 1 * cInv).isLt), scaleZeta_eq]

/-- The constants of the last layer, and the count of its groups. -/
theorem scalePre_ok {s : State} (h8 : s.gpr .r8 = Nq) (h12 : s.gpr .r12 = 3329) :
    WP isa (.block scalePre) s fun s' =>
      ScaleIn (zeta 1) s' ∧ s'.gpr .r3 = BitVec.ofNat 32 (1 * (32 - 0)) ∧ s'.mem = s.mem ∧
        Keep [.r0, .r1, .lr] s s' := by
  run_block [scalePre, ScaleIn, ZetaIn, h8, h12, scaleZeta_word, scaleQuot_word]
  keep_regs

/-! ## Setup and the end -/

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r1 512 ++ tableZ zetaTable .r1 ++ constsN ++
      ([.dp .add .r1 .r1 (.imm 508)] : List Instr)))
      s₀ fun s => Setup s₀ s.mem ∧ LI s₀ s.mem (s₀.gpr .r10) (lift (P s₀)) 127 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  have e0 := e .r0 (by decide)
  have e1 := e .r1 (by decide)
  have e10 := e .r10 (by decide)
  have elr := e .lr (by decide)
  run_block [constsN, e0, e1, e10, elr, rd, wr, sp, constsN_val, hm, true_and]
  exact ⟨by simp [e0], by simp, by simp, by simp, by simp [e10], lp_lift hm.poly, Frame.refl _ _,
    ⟨fun r hr => by rw [List.mem_singleton] at hr; subst hr; simp [elr], rfl, rfl, rfl⟩⟩

/-- The registers restored, from a state that kept the working space. -/
theorem restore_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {s : State}
    (h1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 4) (hlr : s.gpr .lr = s₀.gpr .lr)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) (hf : Frame [polyRegion (F s₀)] m₁ s.mem)
    {f : Poly} (hP : PolyIs s.mem (F s₀) f) :
    WP isa (.block (restoreRegs .r1 508)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ PolyIs s'.mem (F s₀) f := by
  have fS := hp.fitS
  have hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have e1 : State.addr (s.gpr .r1) + BitVec.ofNat 64 508 = S s₀ + BitVec.ofNat 64 512 := by
    rw [h1, addr_add (by omega_arith), add_ofNat_add]
  refine WP.mono (restoreRegs_ok .r1 (by decide) (off := 508) (by decide) (by rw [h1]; bv_omega)
    (g := s₀.gpr) (by
      rw [e1]
      intro i hi
      rw [hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact hm.sav i hi
      · rw [List.mem_singleton] at hr; subst hr
        refine hp.disj.symm.sub_left ?_
        rw [add_ofNat_add]
        exact region_sub_off (by omega_arith))
    fun i hi => by
      rw [e1, hrd, hwr, hp.wr, add_ofNat_add]
      exact inRegions_of (R := polyRegion (S s₀)) (by simp) (contains_off (by omega_arith) (by omega_arith)))
    fun s' h' => ⟨preserved_of_restore h' hlr, h'.sp.trans hsp, ?_⟩
  rw [h'.mem]
  exact hP

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa nttInv s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (F s₀) (Spec.MlKem.nttInv (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, hI⟩ => ?_)
  refine WP.seq (WP.mono (lays_ok hp hm (fun len => nttBlkS (ibfly len) len .sub)
    [2, 4] _ 127 s₁ (fun len hl => ?_) (by simp only [ChainInv]; decide) hI) fun s₂ hI₂ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;>
      exact ⟨by decide, blkS_ok (ibfly_core _) hp.fitF hp.fitS (by decide) .sub (.inr rfl) (by decide)⟩
  refine WP.seq (WP.mono (lays_ok hp hm (fun len => nttBlkL (ibfly len) len .sub)
    [8, 16, 32, 64] _ 31 s₂ (fun len hl => ?_) (by simp only [ChainInv]; decide) hI₂) fun s₃ hI₃ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, blkL_ok (ibfly_core _) hp.fitF hp.fitS (by decide) .sub (.inr rfl) (by decide)
        (by decide)⟩
  refine WP.seq (WP.mono (scalePre_ok hI₃.r8 hI₃.r12) fun s₄ ⟨hz, e3, m₄, k₄⟩ => ?_)
  have hG := hI₃.poly
  rw [← m₄] at hG
  refine WP.seq (WP.mono (grpLoop_ok ibflyS_core (fun _ _ _ hk h => h.keep hk) hp.fitF (len := 128) (start := 0)
    (N := 32) (by decide) (by decide) (by decide) (by decide) (by decide) 1 _ s₄
    (by rw [k₄.gpr .r0 (by decide), hI₃.r0]; simp) hz hG
    (by rw [k₄.wr, hI₃.keep.wr, hp.wr]; simp) e3) fun s₅ ⟨hP, hf, _, k₅⟩ => ?_)
  refine restore_ok hp hm ((k₅.gpr .r1 (by decide)).trans ((k₄.gpr .r1 (by decide)).trans hI₃.r1))
    ((k₅.gpr .lr (by decide)).trans ((k₄.gpr .lr (by decide)).trans (hI₃.keep.gpr .lr (by decide))))
    (k₅.rd.trans (k₄.rd.trans hI₃.keep.rd)) (k₅.wr.trans (k₄.wr.trans hI₃.keep.wr))
    (k₅.sp.trans (k₄.sp.trans hI₃.keep.sp)) (hI₃.frame.trans (m₄ ▸ hf)) ?_
  have h2 : Rel 2 _ _ := layersI_rel [2, 4] _ _ (by decide) ((lift_rel (P s₀)).mono (by decide))
  have hr : Rel 2 _ _ := layersI_rel [8, 16, 32, 64] _ _ (by decide) h2
  rw [nttInv_split]
  refine polyIs_of_toNat fun j hj => ?_
  rw [hP j hj]
  exact lastInv_val hr (by rw [n_eq] at hj; exact hj)

end VG.Proof.MlKem.Arm.NttInv
