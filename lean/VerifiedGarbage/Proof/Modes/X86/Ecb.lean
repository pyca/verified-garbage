module
-- separate module: ECB for any core, which each cipher's ECB imports

public import VerifiedGarbage.Proof.Modes.X86.Wide
public import VerifiedGarbage.Impl.Modes.X86.Ecb
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms

/-!
# ECB on x86 (32-bit), for any core

`ecbLevels_wp`: `Core.ecbLevels` (`Impl/Modes/X86/Ecb.lean`), for a core `c`
with `CoreSpec c` and group sizes that fit it (`LevelsFit`), with its
arguments on the stack (`f(key, data, n, scratch)`, the key `c.ka`
arguments), replaces each of the `n` blocks at `data` with the core's cipher
of it (SP 800-38A §6.1, for the cipher or its inverse), and keeps the
callee-saved registers and the return address. Each cipher's contract
follows from it.

* The mode: `ecbMode`'s operations compute `ecbF`, the cipher of the block,
  which keeps the chaining value it has no use for (`ecbMode_computes`), and
  `ecbWide`'s compute it on each block of a group (`ecbWide_computes`), so
  the loops of `Wide.lean` take all the steps (`levels_ok`, `narrow_ok`).
* The function (`ecbWith_wp`) is `seqWith_wp` without an initialization
  vector: the chaining value of the invariant (`Inv`) is whatever its slots
  hold after the setup (`EcbSetUp`), which no step changes.
-/

@[expose] public section

namespace VG.Proof.Modes.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Modes VG.Impl.Modes.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Cbc (Cipher)

/-! ## The mode -/

/-- ECB's step: the block's cipher; the chaining value, which ECB has no use
for, is kept. -/
def ecbF (ciph : Cipher) : StepFn := fun c x => (ciph x, c)

theorem ecbF_run (ciph : Cipher) : ∀ (c : List Byte) (xs : List (List Byte)),
    run (ecbF ciph) c xs = (xs.map ciph, c)
  | _, [] => rfl
  | c, x :: xs => by simp only [run, ecbF, ecbF_run ciph c xs, List.map_cons]

theorem ecbF_blockwise {L : Nat} {ciph : Cipher} (hc : ∀ b, (ciph b).length = L) :
    Blockwise (ecbF ciph) L L := fun _ _ h1 _ => ⟨hc _, h1⟩

/-- Close a goal of nested `if`s on arithmetic conditions. -/
local macro "arith_ifs" : tactic =>
  `(tactic| ((repeat' split) <;> first | rfl | (exfalso; omega) | (congr 1; omega)))

section
variable (bw : Nat)

/-- The pres of `G` blocks: the data's first `G` blocks in the buffer. -/
theorem ecbWide_pre (a : Areas) : ∀ G l i, applyOps (ecbWide bw G).pre a l i =
    if l = .buf ∧ i < 4 * bw * G then a .dat i else a l i
  | 0, l, i => by
    simp only [ecbWide, widen_pre_zero, applyOps_nil, Nat.mul_zero, Nat.not_lt_zero, and_false, ite_false]
  | G + 1, l, i => by
    have ih : applyOps (Mode.widen G (4 * bw) (ecbMode bw)).pre a =
        fun l i => if l = .buf ∧ i < 4 * bw * G then a .dat i else a l i :=
      funext fun l => funext fun i => ecbWide_pre a G l i
    simp only [ecbWide]
    rw [widen_pre_succ, applyOps_append, ih]
    simp only [ecbMode, copyBlk_shift, shOff, copyAt_apply (show Loc.buf ≠ .dat by decide)]
    rw [Nat.mul_succ]
    generalize 4 * bw * G = m
    cases l <;> simp only [reduceCtorEq, false_and, ite_false, true_and] <;> arith_ifs

/-- The posts of `G` blocks: the buffer's first `G` blocks in the data. -/
theorem ecbWide_post (b : Areas) : ∀ G l i, applyOps (ecbWide bw G).post b l i =
    if l = .dat ∧ i < 4 * bw * G then b .buf i else b l i
  | 0, l, i => by
    simp only [ecbWide, widen_post_zero, applyOps_nil, Nat.mul_zero, Nat.not_lt_zero, and_false, ite_false]
  | G + 1, l, i => by
    have ih : applyOps (Mode.widen G (4 * bw) (ecbMode bw)).post b =
        fun l i => if l = .dat ∧ i < 4 * bw * G then b .buf i else b l i :=
      funext fun l => funext fun i => ecbWide_post b G l i
    simp only [ecbWide]
    rw [widen_post_succ, applyOps_append, ih]
    simp only [ecbMode, copyBlk_shift, shOff, copyAt_apply (show Loc.dat ≠ .buf by decide)]
    rw [Nat.mul_succ]
    generalize 4 * bw * G = m
    cases l <;> simp only [reduceCtorEq, false_and, ite_false, true_and] <;> arith_ifs

end

section
variable {bw : Nat} {len : Loc → Nat}

theorem ecbWide_inBounds (G : Nat) (hd : 4 * bw * G ≤ len .dat) (hb : 4 * bw * G ≤ len .buf) :
    (∀ o ∈ (ecbWide bw G).pre, o.InBounds len) ∧ (∀ o ∈ (ecbWide bw G).post, o.InBounds len) := by
  refine ⟨flatMap_inBounds fun j hj => ?_, flatMap_inBounds fun j hj => ?_⟩
  · simp only [ecbMode, copyBlk_shift, shOff]
    have := blk_le (L := 4 * bw) hj
    exact copyAt_inBounds (by omega_using [hb, this]) (by omega_using [hd, this])
  · simp only [ecbMode, copyBlk_shift, shOff]
    have := blk_le (L := 4 * bw) hj
    exact copyAt_inBounds (by omega_using [hd, this]) (by omega_using [hb, this])

end

section
variable {bw : Nat} {ciph : Cipher} (hc : ∀ b, (ciph b).length = 4 * bw)
include hc

/-- ECB, one block a step. -/
theorem ecbMode_computes : Computes (ecbMode bw) (4 * bw) ciph (ecbF ciph) := by
  intro a
  have hb : rd (applyOps (copyBlk bw .buf .dat) a) .buf (4 * bw) = rd a .dat (4 * bw) :=
    rd_eq (rd_length _ _ _) fun i hi => by
      rw [copyBlk_apply (show Loc.buf ≠ .dat by decide), ite_eq_left ⟨rfl, hi⟩, getD_rd hi]
  simp only [stepA, ecbMode, ecbF]
  refine ⟨rd_eq (hc _) fun i hi => ?_, rd_eq (rd_length _ _ _) fun i hi => ?_⟩
  · rw [copyBlk_apply (show Loc.dat ≠ .buf by decide), ite_eq_left ⟨rfl, hi⟩]
    simp only [cryptBuf, ite_true, hb]
  · rw [copyBlk_apply (show Loc.dat ≠ .buf by decide), ite_eq_right (fun h => by cases h.1)]
    simp only [cryptBuf, reduceCtorEq, ite_false]
    rw [copyBlk_apply (show Loc.buf ≠ .dat by decide), ite_eq_right (fun h => by cases h.1), getD_rd hi]

/-- ECB, `G` blocks a step: the cipher of each block of the group. -/
theorem ecbWide_computes (G : Nat) :
    ComputesB (ecbWide bw G) (4 * bw) (4 * bw * G) (blocksCipher (4 * bw) G ciph)
      (group (4 * bw) G (ecbF ciph)) := by
  intro a
  have hst : (ecbWide bw G).step = G * (4 * bw) := rfl
  have hLG : G * (4 * bw) = 4 * bw * G := Nat.mul_comm _ _
  rw [hst, hLG]
  have hb : rd (applyOps (ecbWide bw G).pre a) .buf (4 * bw * G) = rd a .dat (4 * bw * G) :=
    rd_eq (rd_length _ _ _) fun i hi => by rw [ecbWide_pre, ite_eq_left ⟨rfl, hi⟩, getD_rd hi]
  have hl : (blocksCipher (4 * bw) G ciph (rd a .dat (4 * bw * G))).length = 4 * bw * G := by
    rw [blocksCipher, length_flatten_of (L := 4 * bw) (fun y hy => by
      simp only [List.mem_map] at hy; obtain ⟨z, -, rfl⟩ := hy; exact hc z), List.length_map, split_length]
    exact hLG
  simp only [group, ecbF_run, stepA]
  refine ⟨rd_eq hl fun i hi => ?_, rd_eq (rd_length _ _ _) fun i hi => ?_⟩
  · rw [ecbWide_post, ite_eq_left ⟨rfl, hi⟩]
    simp only [cryptBuf, ite_true, hb]
    rfl
  · rw [ecbWide_post, ite_eq_right (fun h => by cases h.1)]
    simp only [cryptBuf, reduceCtorEq, ite_false]
    rw [ecbWide_pre, ite_eq_right (fun h => by cases h.1), getD_rd hi]

end

/-! ## The arguments -/

variable {c : Core}

section
variable (s₀ : State)

/-- The data pointer, the number of blocks and the scratch buffer: the
arguments after the key's. -/
abbrev eDp (c : Core) : BitVec 32 := arg s₀ c.ka
abbrev eN (c : Core) : Nat := (arg s₀ (c.ka + 1)).toNat
abbrev eS (c : Core) : BitVec 32 := arg s₀ (c.ka + 2)

abbrev eArgsR (c : Core) : Region := ⟨argAddr s₀ 0, 4 * (c.ka + 3)⟩
abbrev eScrR (c : Core) : Region := ⟨(eS s₀ c).setWidth 64, 4 * c.total⟩

/-- The data, on entry. -/
abbrev eData (c : Core) : Region := dataRegion (eDp s₀ c) (4 * c.bw) (eN s₀ c)

end

/-- What the function needs on entry: the arguments readable, the data and
the scratch buffer writable, none wrapping around, and apart from each
other, the arguments, the return address and the core's stack. -/
structure EcbPre (c : Core) (s₀ : State) : Prop where
  args : eArgsR s₀ c ∈ s₀.rd ++ s₀.wr
  espFit : (s₀.gpr .esp).toNat + 4 * (c.ka + 4) ≤ 2 ^ 32
  scr : ScrIn s₀ (eS s₀ c) c.total
  dataW : eData s₀ c ∈ s₀.wr
  dataFit : (eDp s₀ c).toNat + 4 * c.bw * eN s₀ c ≤ 2 ^ 32
  dataScr : Region.Disjoint (eData s₀ c) (eScrR s₀ c)
  argsScr : Region.Disjoint (eArgsR s₀ c) (eScrR s₀ c)
  retScr : Region.Disjoint (retR s₀) (eScrR s₀ c)
  retData : Region.Disjoint (retR s₀) (eData s₀ c)
  stkData : Region.Disjoint (stkRegion (E s₀) c.stack) (eData s₀ c)
  stkMode : Region.Disjoint (stkRegion (E s₀) c.stack) ⟨slotA (eS s₀ c) c.slots, 40⟩
  stkArgs : Region.Disjoint (stkRegion (E s₀) c.stack) (eArgsR s₀ c)
  stkRet : Region.Disjoint (stkRegion (E s₀) c.stack) (retR s₀)
  stack : c.stack ≤ (s₀.gpr .esp).toNat
  layout : Layout c

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.dSlot, Core.nSlot, Core.savedSlot]); omega_arith))

theorem ecbArg_contains (s₀ : State) (hfit : (s₀.gpr .esp).toNat + 4 * (c.ka + 4) ≤ 2 ^ 32) {i : Nat}
    (hi : i < c.ka + 3) : (eArgsR s₀ c).Contains (argAddr s₀ i) 4 := by
  rw [argAddr_eq s₀ (n := c.ka + 3) hfit hi]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- `mov r, [esp + 4 + 4 i]`: argument `i`, while the arguments are unchanged. -/
theorem ecb_wp_arg {s₀ s : State} (hp : EcbPre c s₀) (hesp : s.gpr .esp = s₀.gpr .esp)
    (hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr) (hm : ∀ i < c.ka + 3, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) {d : Reg}
    {i : Nat} (hi : i < c.ka + 3) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (argOp i)) :: is)) s Q := by
  obtain e : addr (s.gpr .esp) (4 + 4 * i) = argAddr s₀ i := by rw [hesp]; rfl
  refine wp_ldm (B := s.gpr .esp) rfl (by rw [e, hrw]; exact ⟨_, hp.args, ecbArg_contains s₀ hp.espFit hi⟩)
    fun s' u => ?_
  rw [e, hm i hi] at u
  exact k s' u

/-! ## The entry -/

/-- After the entry: the scratch buffer at `sb`, the callee-saved registers
in their slots. -/
structure EcbEntered (c : Core) (s₀ s : State) : Prop where
  b : s.gpr sb = eS s₀ c
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ i < 4, s.mem.readW (slotA (eS s₀ c) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx)
  frame : Frame [modeR c (eS s₀ c)] s₀.mem s.mem

theorem ecbEntry_wp {s₀ : State} (hp : EcbPre c s₀) : WP isa (.block c.ecbEntry) s₀ (EcbEntered c s₀) := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  obtain slotW : ∀ k, k < c.total → InRegions s₀.wr (addr (eS s₀ c) (4 * k)) 4 := fun k hk =>
    ⟨_, hp.scr.wr, by rw [addr_eq (by omega_arith)]; exact slot_contains hfit (by omega_arith)⟩
  obtain inMode : ∀ i < 4, (modeR c (eS s₀ c)).Contains (slotA (eS s₀ c) (c.savedSlot i)) (32 / 8) := fun i hi =>
    VG.Offset.contains _ (by slot_omega) (by slot_omega) (by omega_arith)
  obtain sep : ∀ i < 4, ∀ j < 4, i ≠ j →
      Region.Disjoint ⟨slotA (eS s₀ c) (c.savedSlot i), 4⟩ ⟨slotA (eS s₀ c) (c.savedSlot j), 4⟩ :=
    fun i hi j hj hij => VG.Offset.disjoint _ (by slot_omega) (by slot_omega) (by slot_omega)
  obtain aS : ∀ i < 4, addr (eS s₀ c) (4 * c.savedSlot i) = slotA (eS s₀ c) (c.savedSlot i) := fun i hi =>
    addr_slotA hfit (by slot_omega)
  simp only [Core.ecbEntry, range4_map, List.cons_append, List.nil_append, at_]
  refine ecb_wp_arg hp rfl rfl (fun _ _ => rfl) (by omega_arith) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .eax = eS s₀ c := u₁.gpr
  refine wp_stm b₁ (by rw [u₁.wr]; exact slotW _ (by slot_omega)) fun s₂ u₂ => ?_
  refine wp_stm (B := eS s₀ c) (by rw [u₂.gpr]; exact b₁) (by rw [u₂.wr, u₁.wr]; exact slotW _ (by slot_omega))
    fun s₃ u₃ => ?_
  refine wp_stm (B := eS s₀ c) (by rw [u₃.gpr, u₂.gpr]; exact b₁)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact slotW _ (by slot_omega)) fun s₄ u₄ => ?_
  refine wp_stm (B := eS s₀ c) (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact b₁)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact slotW _ (by slot_omega)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => WP.block_nil ?_
  obtain g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  obtain vals : ∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  obtain m₅ : s₅.mem = (((s₀.mem.writeW (slotA (eS s₀ c) (c.savedSlot 0)) (s₀.gpr .ebx)).writeW
      (slotA (eS s₀ c) (c.savedSlot 1)) (s₀.gpr .esi)).writeW (slotA (eS s₀ c) (c.savedSlot 2))
      (s₀.gpr .edi)).writeW (slotA (eS s₀ c) (c.savedSlot 3)) (s₀.gpr .ebp) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, aS 0 (by decide), aS 1 (by decide),
      aS 2 (by decide), aS 3 (by decide)]
    simp only [Core.savedRegs, List.getD_cons_zero, List.getD_cons_succ]
    rw [vals _ (by decide), vals _ (by decide), vals _ (by decide), vals _ (by decide)]
  obtain f₅ : Frame [modeR c (eS s₀ c)] s₀.mem s₅.mem := by
    rw [m₅]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (inMode 0 (by decide))).writeW List.mem_cons_self _
      (inMode 1 (by decide))).writeW List.mem_cons_self _ (inMode 2 (by decide))).writeW List.mem_cons_self _
      (inMode 3 (by decide))
  refine ⟨by rw [u₆.gpr, g₅]; exact b₁, by rw [u₆.other _ (by decide), g₅, vals _ (by decide)],
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    fun i hi => ?_, by rw [u₆.mem]; exact f₅⟩
  rw [u₆.mem, m₅]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
  · rw [readW_write_sep (sep 0 (by decide) 3 (by decide) (by decide)),
      readW_write_sep (sep 0 (by decide) 2 (by decide) (by decide)),
      readW_write_sep (sep 0 (by decide) 1 (by decide) (by decide)), Mem.readW_writeW_self32]; rfl
  · rw [readW_write_sep (sep 1 (by decide) 3 (by decide) (by decide)),
      readW_write_sep (sep 1 (by decide) 2 (by decide) (by decide)), Mem.readW_writeW_self32]; rfl
  · rw [readW_write_sep (sep 2 (by decide) 3 (by decide) (by decide)), Mem.readW_writeW_self32]; rfl
  · rw [Mem.readW_writeW_self32]; rfl

/-! ## The exit -/

theorem ecbRestore_wp {s₀ t : State} (hp : EcbPre c s₀) (hb : t.gpr sb = eS s₀ c)
    (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr)
    (hsv : ∀ i < 4, t.mem.readW (slotA (eS s₀ c) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx))
    {Q : State → Prop}
    (k : ∀ t', (∀ r ∈ calleeSaved, r ≠ .esp → t'.gpr r = s₀.gpr r) → t'.gpr .esp = t.gpr .esp → t'.mem = t.mem →
      Q t') :
    WP isa (.block c.restore) t Q := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  obtain slotR : ∀ i < 4, InRegions (t.rd ++ t.wr) (addr (eS s₀ c) (4 * c.savedSlot i)) 4 := fun i hi =>
    ⟨_, by rw [hrw]; exact List.mem_append_right _ hp.scr.wr, by
      rw [addr_eq (by slot_omega)]; exact slot_contains hfit (by slot_omega)⟩
  obtain aS : ∀ i < 4, addr (eS s₀ c) (4 * c.savedSlot i) = slotA (eS s₀ c) (c.savedSlot i) := fun i hi =>
    addr_slotA hfit (by slot_omega)
  simp only [Core.restore, slotAt, at_]
  refine wp_ldm hb (slotR 0 (by decide)) fun t₁ u₁ => ?_
  refine wp_ldm (B := eS s₀ c) (by rw [u₁.other _ (by decide)]; exact hb)
    (by rw [u₁.rd, u₁.wr]; exact slotR 1 (by decide)) fun t₂ u₂ => ?_
  refine wp_ldm (B := eS s₀ c) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact slotR 3 (by decide)) fun t₃ u₃ => ?_
  refine wp_ldm (B := eS s₀ c)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact slotR 2 (by decide)) fun t₄ u₄ => WP.block_nil ?_
  obtain mm : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine k t₄ (fun r hr hne => ?_) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide)]) (by rw [u₄.mem, mm])
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, aS 0 (by decide),
      hsv 0 (by decide)]; rfl
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, aS 1 (by decide), hsv 1 (by decide)]; rfl
  · rw [show sb = .edi from rfl] at u₄
    rw [u₄.gpr, mm, aS 2 (by decide), hsv 2 (by decide)]; rfl
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, aS 3 (by decide), hsv 3 (by decide)]; rfl
  · exact absurd rfl hne

/-! ## The setup -/

/-- The inputs: the data's blocks, on entry. -/
abbrev eXs0 (c : Core) (s₀ : State) : List (List Byte) :=
  chunksAt (4 * c.bw) s₀.mem ((eDp s₀ c).setWidth 64) (eN s₀ c)

/-- What the mode's slots of a chaining value hold in `s`. -/
abbrev eChn (c : Core) (s₀ s : State) : List Byte := bytesAt s.mem (slotA (eS s₀ c) c.chnSlot) (4 * c.bw)

/-- After the setup, at the loops. -/
structure EcbSetUp (cs : CoreSpec c) (F : StepFn) (k : cs.Key) (s₀ s : State) : Prop where
  fixed : Fixed c s (eS s₀ c) (eDp s₀ c) (eN s₀ c) (4 * c.bw)
  inv : Inv cs s (eS s₀ c) (eDp s₀ c) (eN s₀ c) (4 * c.bw) k F (eChn c s₀ s) (eXs0 c s₀) 0 s
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ i < 4, s.mem.readW (slotA (eS s₀ c) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx)
  frame : Frame [modeR c (eS s₀ c), coreRegion c (eS s₀ c), stkRegion (E s₀) c.stack] s₀.mem s.mem

theorem ecbSetup_wp (cs : CoreSpec c) {F : StepFn} {s₀ : State} {k : cs.Key} (hp : EcbPre c s₀)
    (hk : cs.KeyArgs s₀ [eScrR s₀ c] k) :
    WP isa (.seq (.block c.ecbEntry) (.seq c.prepare (.block c.ecbArgs))) s₀ (EcbSetUp cs F k s₀) := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  obtain hbw : 0 < c.bw ∧ c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_arith
  obtain modeScr : Region.Sub (modeR c (eS s₀ c)) (eScrR s₀ c) := VG.Offset.sub_base _ (by omega_arith)
  obtain coreScr : Region.Sub (coreRegion c (eS s₀ c)) (eScrR s₀ c) := Region.sub_prefix (by omega_arith)
  refine WP.seq (WP.mono_syms (ecbEntry_wp hp) fun s₁ h₁ sy₁ => ?_)
  obtain hS₁ : ScrIn s₁ (eS s₀ c) c.total := ⟨by rw [h₁.wr]; exact hp.scr.wr, hfit⟩
  refine WP.seq (WP.mono (cs.prepare_wp h₁.b hS₁ List.mem_cons_self
    (cs.keyArgs_congr hk h₁.esp h₁.rd h₁.wr sy₁ (h₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, modeScr⟩))
    (by rw [h₁.esp]; exact hp.stack)) fun s₂ ⟨ready₂, b₂, esp₂, f₂, rd₂, wr₂⟩ => ?_)
  refine WP.syms_intro ?_
  rw [h₁.esp] at f₂
  obtain esp₂' : s₂.gpr .esp = s₀.gpr .esp := by rw [esp₂, h₁.esp]
  obtain f₀₂ : Frame [modeR c (eS s₀ c), coreRegion c (eS s₀ c), stkRegion (E s₀) c.stack] s₀.mem s₂.mem :=
    (h₁.frame.mono (by simp)).trans (f₂.mono (by simp))
  obtain argsOut : ∀ r ∈ [modeR c (eS s₀ c), coreRegion c (eS s₀ c), stkRegion (E s₀) c.stack],
      Region.Disjoint (eArgsR s₀ c) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.argsScr.sub_right modeScr
    · exact hp.argsScr.sub_right coreScr
    · exact hp.stkArgs.symm
  obtain argsK : ∀ {m : Mem},
      Frame [modeR c (eS s₀ c), coreRegion c (eS s₀ c), stkRegion (E s₀) c.stack] s₀.mem m →
      ∀ i < c.ka + 3, m.readW (argAddr s₀ i) 32 = arg s₀ i := fun h i hi =>
    h.readW (ecbArg_contains s₀ hp.espFit hi) argsOut (by decide)
  obtain hd : c.dSlot < c.total := by slot_omega
  obtain hn : c.nSlot < c.total := by slot_omega
  obtain dIn : (modeR c (eS s₀ c)).Contains (slotA (eS s₀ c) c.dSlot) (32 / 8) :=
    VG.Offset.contains _ (by slot_omega) (by slot_omega) (by omega_arith)
  obtain nIn : (modeR c (eS s₀ c)).Contains (slotA (eS s₀ c) c.nSlot) (32 / 8) :=
    VG.Offset.contains _ (by slot_omega) (by slot_omega) (by omega_arith)
  obtain rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [rd₂, wr₂, h₁.rd, h₁.wr]
  obtain hS₂ : ScrIn s₂ (eS s₀ c) c.total := ⟨by rw [wr₂]; exact hS₁.wr, hfit⟩
  simp only [Core.ecbArgs, slotAt, at_]
  refine ecb_wp_arg hp esp₂' rw₂ (argsK f₀₂) (by omega_arith) fun s₃ u₃ => ?_
  refine wp_stm (B := eS s₀ c) (by rw [u₃.other _ (by decide)]; exact b₂)
    (by rw [u₃.wr]; exact slot_inW hS₂ hd) fun s₄ u₄ => ?_
  obtain m₄ : s₄.mem = s₂.mem.writeW (slotA (eS s₀ c) c.dSlot) (arg s₀ c.ka) := by
    rw [u₄.mem, u₃.mem, u₃.gpr, addr_slotA hfit hd]
  obtain f₀₄ : Frame [modeR c (eS s₀ c), coreRegion c (eS s₀ c), stkRegion (E s₀) c.stack] s₀.mem s₄.mem := by
    rw [m₄]; exact f₀₂.writeW List.mem_cons_self _ dIn
  refine ecb_wp_arg hp (by rw [u₄.gpr, u₃.other _ (by decide), esp₂'])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]) (argsK f₀₄) (by omega_arith) fun s₅ u₅ => ?_
  refine wp_stm (B := eS s₀ c) (by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]; exact b₂)
    (by rw [u₅.wr, u₄.wr, u₃.wr]; exact slot_inW hS₂ hn) fun s₆ u₆ => WP.block_nil fun sy₆ => ?_
  obtain m₆ : s₆.mem = (s₂.mem.writeW (slotA (eS s₀ c) c.dSlot) (arg s₀ c.ka)).writeW
      (slotA (eS s₀ c) c.nSlot) (arg s₀ (c.ka + 1)) := by
    rw [u₆.mem, u₅.mem, u₅.gpr, addr_slotA hfit hn, m₄]
  obtain g₆ : ∀ r, r ≠ .eax → s₆.gpr r = s₂.gpr r := fun r h => by
    rw [u₆.gpr, u₅.other r h, u₄.gpr, u₃.other r h]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, h₁.rd]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, h₁.wr]
  obtain esp₆ : s₆.gpr .esp = s₀.gpr .esp := by rw [g₆ _ (by decide), esp₂']
  obtain b₆ : s₆.gpr sb = eS s₀ c := by rw [g₆ _ (by decide)]; exact b₂
  obtain fdn : Frame (dnSlots c (eS s₀ c)) s₂.mem s₆.mem := by
    rw [m₆]
    obtain h1 : (⟨slotA (eS s₀ c) c.dSlot, 4⟩ : Region).Contains (slotA (eS s₀ c) c.dSlot) (32 / 8) :=
      Region.contains_self _ _
    obtain h2 : (⟨slotA (eS s₀ c) c.nSlot, 4⟩ : Region).Contains (slotA (eS s₀ c) c.nSlot) (32 / 8) :=
      Region.contains_self _ _
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ h1).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ h2
  obtain f₀₆ : Frame [modeR c (eS s₀ c), coreRegion c (eS s₀ c), stkRegion (E s₀) c.stack] s₀.mem s₆.mem := by
    rw [m₆, ← m₄]; exact f₀₄.writeW List.mem_cons_self _ nIn
  obtain hF : Fixed c s₆ (eS s₀ c) (eDp s₀ c) (eN s₀ c) (4 * c.bw) :=
    ⟨⟨by rw [wr₆]; exact hp.scr.wr, hfit⟩, ⟨_, 0, _, by rw [wr₆]; exact hp.dataW, (BitVec.add_zero _).symm,
      by omega_arith, by have := hp.dataFit; omega_arith⟩, hp.dataFit, hp.dataScr,
      by rw [esp₆]; exact hp.stkData, by rw [esp₆]; exact hp.stkMode, by rw [esp₆]; exact hp.stack,
      ⟨by omega_arith, Nat.le_refl _⟩, hL⟩
  obtain dn : Region.Disjoint ⟨slotA (eS s₀ c) c.dSlot, 4⟩ ⟨slotA (eS s₀ c) c.nSlot, 4⟩ :=
    VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
  obtain dnOut : ∀ r ∈ dnSlots c (eS s₀ c), Region.Disjoint (coreRegion c (eS s₀ c)) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.base_disjoint _ (by slot_omega) (by slot_omega)
    · exact VG.Offset.base_disjoint _ (by slot_omega) (by slot_omega)
  -- A slot of the mode outside the slots of the data pointer and the count.
  obtain keepSlot : ∀ {R : Region}, Region.Sub R (modeR c (eS s₀ c)) → (∀ r ∈ dnSlots c (eS s₀ c), R.Disjoint r) →
      R.len ≤ 2 ^ 64 → ∀ {i}, i < R.len → s₆.mem (R.base + BitVec.ofNat 64 i) = s₁.mem (R.base + BitVec.ofNat 64 i) :=
    fun hsub hd hl _ hi => by
      rw [fdn.bytes hd hl hi]
      refine f₂.bytes (fun r hr => ?_) hl hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (VG.Offset.disjoint_base _ (by slot_omega) (by omega_arith)).sub_left hsub
      · exact (hp.stkMode.symm.sub_left hsub)
  refine ⟨hF, ⟨b₆, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, Frame.refl _ _⟩, esp₆, rd₆, wr₆, fun i hi => ?_, f₀₆⟩
  · rw [m₆, readW_write_sep dn, Mem.readW_writeW_self32, Nat.mul_zero]
    exact (BitVec.add_zero _).symm
  · rw [m₆, Mem.readW_writeW_self32, Nat.sub_zero]
    simp only [eN, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact cs.ready_frame ready₂ (by rw [esp₆, esp₂']) (by rw [rd₆, rd₂, h₁.rd]) (by rw [wr₆, wr₂, h₁.wr]) sy₆ fdn
      (fun r hr => ⟨_, by rw [wr₂, h₁.wr]; exact hp.scr.wr, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Offset.sub_base _ (by slot_omega)
        · exact VG.Offset.sub_base _ (by slot_omega)⟩)
      (fun r hr => .inl (dnOut r hr))
  · rw [chunksAt_frame f₀₆ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.dataScr.sub_right modeScr
      · exact hp.dataScr.sub_right coreScr
      · exact hp.stkData.symm) (by have := hp.dataFit; omega_arith)]
    simp only [List.take_zero, run, List.nil_append, List.drop_zero]
  · simp only [List.take_zero, run]
  · rw [← h₁.saved i hi]
    exact Mem.readW_congr fun u hu => keepSlot (R := ⟨slotA (eS s₀ c) (c.savedSlot i), 4⟩)
      (VG.Offset.sub _ (by slot_omega) (by slot_omega)) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
        · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))
      (by show 4 ≤ 2 ^ 64; omega_arith) (by simpa using hu)

/-! ## The function -/

/-- What the code `loops` must do, from the state after the setup, with the
first block to take and whatever chaining value the mode's slots hold: all
the steps. -/
def EcbLoopsOk (cs : CoreSpec c) (F : StepFn) (s₀ : State) (k : cs.Key) (loops : Prog isa) : Prop :=
  ∀ s c0, Fixed c s (eS s₀ c) (eDp s₀ c) (eN s₀ c) (4 * c.bw) →
    Inv cs s (eS s₀ c) (eDp s₀ c) (eN s₀ c) (4 * c.bw) k F c0 (eXs0 c s₀) 0 s →
    WP isa loops s (Inv cs s (eS s₀ c) (eDp s₀ c) (eN s₀ c) (4 * c.bw) k F c0 (eXs0 c s₀) (eN s₀ c))

/-- The function, for any loops that take all the steps of a step function
`F`. -/
theorem ecbWith_wp (cs : CoreSpec c) {F : StepFn} {s₀ : State} {k : cs.Key} {loops : Prog isa}
    (hp : EcbPre c s₀) (hloops : EcbLoopsOk cs F s₀ k loops) (hk : cs.KeyArgs s₀ [eScrR s₀ c] k) :
    WP isa (c.ecbWith loops) s₀ fun s' => abiPreserved s₀ s' ∧ ∃ c0,
      chunksAt (4 * c.bw) s'.mem ((eDp s₀ c).setWidth 64) (eN s₀ c) = (run F c0 (eXs0 c s₀)).1 := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_arith
  obtain modeScr : Region.Sub (modeR c (eS s₀ c)) (eScrR s₀ c) := VG.Offset.sub_base _ (by omega_arith)
  obtain coreScr : Region.Sub (coreRegion c (eS s₀ c)) (eScrR s₀ c) := Region.sub_prefix (by omega_arith)
  obtain dnScr : Region.Sub (dnRegion c (eS s₀ c)) (eScrR s₀ c) := VG.Offset.sub_base _ (by slot_omega)
  obtain hlen : (eXs0 c s₀).length = eN s₀ c := chunksAt_length _ _ _ _
  obtain hsu := ecbSetup_wp cs (F := F) hp hk
  rw [WP.seq_iff] at hsu
  unfold Core.ecbWith
  refine WP.seq (WP.mono hsu fun s₁ h₁ => ?_)
  rw [WP.seq_iff] at h₁
  refine WP.seq (WP.mono h₁ fun s₂ h₂ => WP.seq (WP.mono h₂ fun s₃ h₃ => ?_))
  refine WP.seq (WP.mono (hloops s₃ _ h₃.fixed h₃.inv) fun s₄ h₄ => ?_)
  -- What the run so far changed.
  obtain big₀ : ∀ {R : Region}, (∀ r ∈ [modeR c (eS s₀ c), coreRegion c (eS s₀ c), stkRegion (E s₀) c.stack] ++
      big c (eS s₀ c) (eDp s₀ c) (eN s₀ c) (4 * c.bw) (E s₀), R.Disjoint r) → R.len ≤ 2 ^ 64 → ∀ {i}, i < R.len →
      s₄.mem (R.base + BitVec.ofNat 64 i) = s₀.mem (R.base + BitVec.ofNat 64 i) := fun hd hl _ hi => by
    have f := h₄.frame
    rw [h₃.esp] at f
    rw [f.bytes (fun r hr => hd r (List.mem_append_right _ hr)) hl hi]
    exact h₃.frame.bytes (fun r hr => hd r (List.mem_append_left _ hr)) hl hi
  obtain bigScr : ∀ {R : Region}, R.Disjoint (eScrR s₀ c) → R.Disjoint (stkRegion (E s₀) c.stack) →
      R.Disjoint (eData s₀ c) →
      ∀ r ∈ [modeR c (eS s₀ c), coreRegion c (eS s₀ c), stkRegion (E s₀) c.stack] ++
        big c (eS s₀ c) (eDp s₀ c) (eN s₀ c) (4 * c.bw) (E s₀), R.Disjoint r := fun h1 h2 h3 r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1.sub_right modeScr
    · exact h1.sub_right coreScr
    · exact h2
    · exact h1.sub_right coreScr
    · exact h1.sub_right dnScr
    · exact h3
    · exact h2
  have b₄ : s₄.gpr sb = eS s₀ c := h₄.b
  obtain esp₄ : s₄.gpr .esp = s₀.gpr .esp := by rw [h₄.esp, h₃.esp]
  obtain rw₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [h₄.rd, h₄.wr, h₃.rd, h₃.wr]
  obtain sv₄ : ∀ i < 4, s₄.mem.readW (slotA (eS s₀ c) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx) :=
    fun i hi => by
      rw [← h₃.saved i hi]
      refine h₄.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact VG.Offset.disjoint_base _ (by slot_omega) (by slot_omega)
      · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
      · exact (hp.dataScr.sub_right (VG.Offset.sub_base _ (by slot_omega))).symm
      · rw [h₃.esp]; exact (hp.stkMode.sub_right (VG.Offset.sub _ (by slot_omega) (by slot_omega))).symm
  obtain ret₄ : s₄.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 :=
    Mem.readW_congr fun u hu => big₀ (R := retR s₀) (bigScr hp.retScr hp.stkRet.symm hp.retData)
      (by show 4 ≤ 2 ^ 64; omega_arith) (by simpa using hu)
  obtain data₄ : chunksAt (4 * c.bw) s₄.mem ((eDp s₀ c).setWidth 64) (eN s₀ c) =
      (run F (eChn c s₀ s₃) (eXs0 c s₀)).1 := by
    rw [h₄.data, List.take_of_length_le (by omega_arith), List.drop_of_length_le (by omega_arith), List.append_nil]
  refine ecbRestore_wp hp b₄ rw₄ sv₄ fun t g e m => ⟨⟨fun r hr => ?_, by rw [m, ret₄]⟩, _, by rw [m, data₄]⟩
  by_cases h : r = .esp
  · subst h; rw [e, esp₄]
  · exact g r hr h

section
variable (cs : CoreSpec c) {s₀ : State} {k : cs.Key}

/-- A level of ECB, `g` blocks a step. -/
theorem ecbWide_ok {g : Nat} (hg : 0 < g) (hG : g ≤ c.G) :
    WideOk cs (ecbMode c.bw) (ecbF (cs.cipher k)) k (ecbWide c.bw g) g := by
  obtain ⟨hw1, hw2⟩ := ecbWide_inBounds (bw := c.bw) (len := lensB c (g * (4 * c.bw)) (4 * c.bw * g))
    g (lensB_wide _ _ (by decide)) (lensB_wide _ _ (by decide))
  exact ⟨hg, hG, rfl, hw1, hw2, ⟨_, ecbWide_computes (cs.cipher_len k) _, bufCipher_blocks hG⟩⟩

/-- ECB, by groups of `g` blocks for each `g` of `gs` in turn, then one
block at a time: each block's cipher in its place. -/
theorem ecbLevels_wp {gs : List Nat} (hfit : LevelsFit c gs) (hp : EcbPre c s₀)
    (hk : cs.KeyArgs s₀ [eScrR s₀ c] k) :
    WP isa (c.ecbLevels gs) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem ((eDp s₀ c).setWidth 64) (eN s₀ c) = (eXs0 c s₀).map (cs.cipher k) := by
  have b := blk_bounds (c := c) (st := (ecbMode c.bw).step) rfl
  refine WP.mono (ecbWith_wp cs (F := ecbF (cs.cipher k)) hp (fun _ _ hF hI =>
    levels_ok cs (fun g hg => ecbWide_ok cs (hfit g hg).1 (hfit g hg).2) (ecbF_blockwise (cs.cipher_len k))
      (narrow_ok cs (copyBlk_inBounds (b _) (b _)) (copyBlk_inBounds (b _) (b _))
        (ecbMode_computes (cs.cipher_len k))) hF.scr hF.layout (BitVec.isLt _) (fun _ => hF) hI) hk)
    fun s' ⟨h1, c0, h2⟩ => ⟨h1, ?_⟩
  rw [h2, ecbF_run]

end

end VG.Proof.Modes.X86
