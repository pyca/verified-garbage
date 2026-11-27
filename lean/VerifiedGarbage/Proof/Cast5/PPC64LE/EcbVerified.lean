module

public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.Block
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Cast5.Memory
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-! ### `Cast5.PPC64LE.Ecb`, which this module and modules that import it used -/

section

/-!
# CAST5 on PPC64LE: ECB

`ecb_wp`: every block becomes its encryption or decryption, one at a time
(`loop_run`); `LR` and our caller's `r14`–`r30` are saved in the working
space and restored. The loop writes only the blocks.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE

/-! ## Frames of the layouts -/

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨Q, 8⟩ r) : Spec.Cast5.blockAt m' Q = Spec.Cast5.blockAt m Q := by
  apply Vector.ext
  intro j hj
  rw [Proof.Cast5.blockAt_get _ _ hj, Proof.Cast5.blockAt_get _ _ hj]
  exact hf.bytes (R := ⟨Q, 8⟩) hd (by show (8 : Nat) ≤ 2 ^ 64; decide) hj

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨K, 128⟩ r) : Spec.Cast5.scheduleAt m' K = Spec.Cast5.scheduleAt m K := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Cast5.scheduleAt, Vector.getElem_ofFn]
  rw [hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 3 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 2 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 1 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i < 128 by omega_arith)]

/-- Memory holding a table, later: its words are kept by writes apart from it. -/
theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} {W : List (BitVec 64)} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 8 * W.length⟩ r) (hl : 8 * W.length < 2 ^ 64) (h : Held m T W) :
    Held m' T W := fun i hi => by
  rw [hf.readW (Offset.contains_base _ (by omega_arith) (by omega_arith)) hd (by decide)]
  exact h i hi

theorem s1234_len : 8 * Impl.Cast5.s1234.length = 4096 := by rw [Impl.Cast5.s1234, table_length]

theorem ofNat_bne_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0) = !decide (a = 0) := by
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this; exact this)
    simp only [bne, decide_eq_false h, Bool.not_false, Bool.not_eq_true']
    exact beq_eq_false_iff_ne.mpr this

/-! ## The loop -/

/-- The block `b` of the data at `D`. -/
abbrev wAt (D : Addr) (b : Nat) : Addr := D + BitVec.ofNat 64 (8 * b)

/-- The registers the loop writes. -/
def loopWrites : List Reg := roundRegs ++ [dat, cnt]

/-- The loop's fixed facts, about the state `s₀` before it: the schedule at
`S`, the `n` blocks at `D`, the table at `T`, readable and apart from the
blocks, and zero and 255 in their registers. -/
structure LoopEnv (S D T : Addr) (n N : Nat) (s₀ : State) : Prop where
  r3 : s₀.gpr sch = S
  r4 : s₀.gpr rnd = BitVec.ofNat 64 n
  nv : n = 12 ∨ n = 16
  r0 : s₀.gpr .r0 = 0
  c255 : s₀.gpr c255 = 255#64
  tbl : s₀.gpr tbl = T
  key : (⟨S, 128⟩ : Region) ∈ s₀.rd ++ s₀.wr
  kfit : S.toNat + 128 ≤ 2 ^ 64
  data : (⟨D, 8 * N⟩ : Region) ∈ s₀.wr
  keyData : (⟨S, 128⟩ : Region).Disjoint ⟨D, 8 * N⟩
  fit : D.toNat + 8 * N ≤ 2 ^ 64
  trd : (⟨T, 4096⟩ : Region) ∈ s₀.rd ++ s₀.wr
  held : Held s₀.mem T Impl.Cast5.s1234
  tblData : (⟨T, 4096⟩ : Region).Disjoint ⟨D, 8 * N⟩

/-- After `k` blocks. -/
structure EInv (S D : Addr) (n N : Nat) (up : Bool) (s₀ : State) (k : Nat) (u : State) : Prop where
  le : k ≤ N
  ptr : u.gpr dat = wAt D k
  cnt : u.gpr cnt = BitVec.ofNat 64 (N - k)
  keep : Keep loopWrites s₀ u
  done : ∀ b < k, Spec.Cast5.blockAt u.mem (wAt D b) =
    cipher up (Spec.Cast5.scheduleAt s₀.mem S) n (Spec.Cast5.blockAt s₀.mem (wAt D b))
  rest : ∀ b, k ≤ b → b < N → Spec.Cast5.blockAt u.mem (wAt D b) = Spec.Cast5.blockAt s₀.mem (wAt D b)
  frame : Frame [⟨D, 8 * N⟩] s₀.mem u.mem

theorem ecb_step {S D T : Addr} {n N : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D T n N s₀) {k : Nat}
    (hk : k < N) {u : State} (I : EInv S D n N up s₀ k u) :
    WP isa (.seq (crypt up dat) (.block [.addi dat dat 8, .subi cnt cnt 1])) u
      (fun u' => EInv S D n N up s₀ (k + 1) u' ∧ u'.gpr cnt = BitVec.ofNat 64 (N - (k + 1))) := by
  have fit := L.fit
  have g (q : Reg) (hq : q ∉ loopWrites := by decide) : u.gpr q = s₀.gpr q := I.keep.gpr hq
  have dTD : ∀ r ∈ [(⟨D, 8 * N⟩ : Region)], Region.Disjoint ⟨T, 8 * Impl.Cast5.s1234.length⟩ r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; rw [s1234_len]; exact L.tblData
  have hK : Spec.Cast5.scheduleAt u.mem S = Spec.Cast5.scheduleAt s₀.mem S :=
    scheduleAt_frame I.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.keyData
  have bp : BPre u dat (wAt D k) S n :=
    { ptr := I.ptr
      prOk := ⟨by decide, by decide⟩
      sched := by rw [g sch]; exact L.r3
      rounds := by rw [g rnd]; exact L.r4
      nv := L.nv
      zero := by rw [g _]; exact L.r0
      c255 := by rw [g _]; exact L.c255
      trd := by rw [g tbl, L.tbl, I.keep.2.1, I.keep.2.2]; exact L.trd
      held := by
        rw [g tbl, L.tbl]
        exact held_frame I.frame dTD (by rw [s1234_len]; decide) L.held
      inP := ⟨_, by rw [I.keep.2.2]; exact L.data, fun off hw => by
        rw [Offset.add_add]; exact Offset.contains_base D (by omega_arith) (by omega_arith)⟩
      inK := by rw [I.keep.2.1, I.keep.2.2]; exact L.key
      kfit := L.kfit }
  refine WP.seq (WP.mono (crypt_ok bp up) fun u₁ B => ?_)
  refine wp_addi (by decide) (by decide) fun u₂ h₂ => wp_subi (by decide) (by decide) fun u₃ h₃ => wp_nil ?_
  have m₃ : u₃.mem = u₁.mem := by rw [h₃.mem, h₂.mem]
  have c₃ : u₃.gpr cnt = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [h₃.gpr, h₂.other _ (by decide), B.keep.gpr (by decide), I.cnt]
    apply BitVec.eq_of_toNat_eq; simp; omega_arith
  have other : ∀ b, b < N → b ≠ k →
      Spec.Cast5.blockAt u₃.mem (wAt D b) = Spec.Cast5.blockAt u.mem (wAt D b) := fun b hb hne => by
    rw [m₃, blockAt_frame B.frame fun r hr => ?_]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨⟨by omega_arith, ?_, c₃, ?_, fun b hb => ?_, fun b h1 h2 => ?_, ?_⟩, c₃⟩
  · rw [h₃.other _ (by decide), h₂.gpr, B.keep.gpr (by decide), I.ptr, Offset.add_add]
    congr 2
  · exact (((I.keep.trans B.keep).trans h₂.keep).trans h₃.keep).mono (by decide)
  · by_cases hbk : b = k
    · subst hbk
      rw [m₃, B.blk, hK, I.rest b (by omega_arith) hk]
    · rw [other b (by omega_arith) hbk]; exact I.done b (by omega_arith)
  · rw [other b h2 (by omega_arith)]; exact I.rest b (by omega_arith) h2
  · rw [m₃]
    refine I.frame.trans (B.frame.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Offset.sub_base D (by omega_arith)⟩

theorem loop_run {S D T : Addr} {n N : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D T n N s₀) (hn : 0 < N)
    {u : State} (I : EInv S D n N up s₀ 0 u) :
    WP isa (.loop (.seq (crypt up dat) (.block [.addi dat dat 8, .subi cnt cnt 1])) (.nonzero .d cnt)) u
      (EInv S D n N up s₀ N) := by
  refine WP.loop (M := isa) (Q := EInv S D n N up s₀ N)
    (fun m v => ∃ k, k < N ∧ m = N - k ∧ EInv S D n N up s₀ k v) ?_ N u ⟨0, hn, rfl, I⟩
  intro m v ⟨k, hk, hm, J⟩
  refine WP.mono (ecb_step L hk J) fun v' ⟨J', hz⟩ => ?_
  have hn64 : N < 2 ^ 64 := by have := L.fit; omega_arith
  rw [eval_nonzero, hz, ofNat_bne_zero (by omega_arith)]
  by_cases e : k + 1 = N
  · left
    exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp; omega_arith, N - (k + 1), by omega_arith, k + 1, by omega_arith, rfl, J'⟩

/-! ## Saving and restoring -/

/-- `LR` (through `r0`) and the callee-saved registers, as the prologue
saves them. -/
def allSlots : List (Reg × Nat) := (.r0, lrOff) :: savedSlots

theorem prologue_eq (b : Reg) (sym : String) :
    prologue b sym = .mflr .r0 :: (Spill.saveCode b allSlots ++
      ([.adrSym tbl sym, .li c255 255, .li zero 0] : List Instr)) := rfl

theorem epilogue_eq (b : Reg) :
    epilogue b = Spill.restoreCode b (savedSlots ++ [(.r0, lrOff)]) ++ ([.mtlr .r0] : List Instr) := rfl

theorem allSlots_fits : Spill.Fits allSlots := by decide
theorem allSlots_ok : ∀ p ∈ allSlots, p.2 % 8 = 0 ∧ p.2 < 32768 := allSlots_fits.1
theorem allSlots_lt : ∀ p ∈ allSlots, 64 ≤ p.2 ∧ p.2 + 8 ≤ 64 + 144 := by decide
theorem restoreSlots_ok : ∀ p ∈ savedSlots ++ [(.r0, lrOff)], p.2 % 8 = 0 ∧ p.2 < 32768 := by decide
theorem restoreSlots_lt : ∀ p ∈ savedSlots ++ [(.r0, lrOff)], 64 ≤ p.2 ∧ p.2 + 8 ≤ 64 + 144 := by decide

/-- The prologue: the slots hold `LR` and the callee-saved registers; the
table's address, 255 and zero in their registers. -/
theorem prologue_ok (s : State) (b : Reg) (hb : b ≠ .r0) (sym : String) {B : Addr} (hB : s.gpr b = B)
    (hw : ∀ p ∈ allSlots, InRegions s.wr (B + BitVec.ofNat 64 p.2) 8) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Spill.Saved B (s.write .r0 s.lr).gpr allSlots u.mem →
      Frame [⟨B + BitVec.ofNat 64 64, 144⟩] s.mem u.mem →
      Keep [.r0, tbl, c255] s u → u.gpr tbl = s.syms sym → u.gpr c255 = 255#64 → u.gpr .r0 = 0 →
      u.syms = s.syms → WP isa (.block is) u Q) :
    WP isa (.block (prologue b sym ++ is)) s Q := by
  rw [prologue_eq, List.cons_append, List.append_assoc]
  refine WP.cons exec_mflr ?_
  have hb₁ : (s.write .r0 s.lr).gpr b = B := by rw [RegUpd.gpr_write_of_ne s s.lr hb, hB]
  refine Spill.save_ok (s := s.write .r0 s.lr) (by exact hb) allSlots_ok
    (fun p hp => by rw [hb₁]; exact hw p hp) ?_
  rw [hb₁]
  generalize hM : Spill.saveMem (s.write .r0 s.lr).mem B (s.write .r0 s.lr).gpr allSlots = M
  rw [List.cons_append]
  refine WP.cons (exec_adrSym (by decide)) ?_
  refine WP.cons (exec_li (by decide)) (WP.cons (exec_li (by decide)) ?_)
  have sv : Spill.Saved B (s.write .r0 s.lr).gpr allSlots M := by
    rw [← hM]; exact Spill.saveMem_saved allSlots_fits _ _ _
  have fr : Frame [⟨B + BitVec.ofNat 64 64, 144⟩] s.mem M := by
    rw [← hM]; exact Spill.saveMem_frame allSlots_lt (by decide) _ _ _
  refine k _ sv fr ⟨fun r hr => ?_, rfl, rfl⟩ (by simp [State.write]) (by simp [State.write])
    (by simp [State.write]) rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [State.write, hr.1, hr.2.1, hr.2.2]

/-! ## The function -/

/-- What ECB may assume: the schedule and the table readable, the `n`
blocks and the working space writable, all apart, none wrapping around, and
12 or 16 rounds. -/
structure EcbPre (s : State) : Prop where
  key : (⟨s.gpr .r3, 128⟩ : Region) ∈ s.rd ++ s.wr
  kfit : (s.gpr .r3).toNat + 128 ≤ 2 ^ 64
  data : (⟨s.gpr .r5, 8 * (s.gpr .r6).toNat⟩ : Region) ∈ s.wr
  fit : (s.gpr .r5).toNat + 8 * (s.gpr .r6).toNat ≤ 2 ^ 64
  scr : (⟨s.gpr .r7, 256⟩ : Region) ∈ s.wr
  sfit : (s.gpr .r7).toNat + 256 ≤ 2 ^ 64
  keyData : (⟨s.gpr .r3, 128⟩ : Region).Disjoint ⟨s.gpr .r5, 8 * (s.gpr .r6).toNat⟩
  keyScr : (⟨s.gpr .r3, 128⟩ : Region).Disjoint ⟨s.gpr .r7, 256⟩
  dataScr : (⟨s.gpr .r5, 8 * (s.gpr .r6).toNat⟩ : Region).Disjoint ⟨s.gpr .r7, 256⟩
  nv : (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 16
  trd : (⟨s.syms Impl.Cast5.s1234Sym, 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (s.syms Impl.Cast5.s1234Sym) Impl.Cast5.s1234
  tblData : (⟨s.syms Impl.Cast5.s1234Sym, 4096⟩ : Region).Disjoint ⟨s.gpr .r5, 8 * (s.gpr .r6).toNat⟩
  tblScr : (⟨s.syms Impl.Cast5.s1234Sym, 4096⟩ : Region).Disjoint ⟨s.gpr .r7, 256⟩

/-- What ECB guarantees. -/
structure EcbPost (up : Bool) (s s' : State) : Prop where
  done : ∀ b < (s.gpr .r6).toNat, Spec.Cast5.blockAt s'.mem (wAt (s.gpr .r5) b) =
    cipher up (Spec.Cast5.scheduleAt s.mem (s.gpr .r3)) (s.gpr .r4).toNat
      (Spec.Cast5.blockAt s.mem (wAt (s.gpr .r5) b))
  frame : Frame [⟨s.gpr .r5, 8 * (s.gpr .r6).toNat⟩, ⟨s.gpr .r7, 256⟩] s.mem s'.mem
  saved : ∀ r ∈ saved, s'.gpr r = s.gpr r
  lr : s'.lr = s.lr

theorem slot_sub (B : Addr) {d : Nat} (hd : 64 ≤ d ∧ d + 8 ≤ 64 + 144) :
    Region.Sub ⟨B + BitVec.ofNat 64 d, 8⟩ ⟨B, 256⟩ := Offset.sub_base _ (by omega_arith)

theorem ecb_wp (up : Bool) {s : State} (h : EcbPre s) :
    WP isa (Impl.Cast5.PPC64LE.ecb up) s (EcbPost up s) := by
  have fit := h.fit
  have sfit := h.sfit
  have hw : ∀ p ∈ allSlots, InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 p.2) 8 := fun p hp =>
    ⟨_, h.scr, Offset.contains_base _ (by have := allSlots_lt p hp; omega_arith) (by have := allSlots_lt p hp; omega_arith)⟩
  have sub144 : Region.Sub ⟨s.gpr .r7 + BitVec.ofNat 64 64, 144⟩ ⟨s.gpr .r7, 256⟩ := Offset.sub_base _ (by decide)
  unfold Impl.Cast5.PPC64LE.ecb
  apply WP.seq
  rw [← List.append_nil (prologue wkE _)]
  refine prologue_ok s wkE (by decide) _ rfl hw fun s₀ sv₀ fr₀ k₀ t₀ c₀ z₀ sy₀ => wp_nil ?_
  have g₀ (q : Reg) (hq : q ∉ [Reg.r0, tbl, c255] := by decide) : s₀.gpr q = s.gpr q := k₀.gpr hq
  have dS : ∀ r ∈ [(⟨s.gpr .r7 + BitVec.ofNat 64 64, 144⟩ : Region)], Region.Disjoint ⟨s.gpr .r3, 128⟩ r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.keyScr.sub_right sub144
  have dB (b : Nat) (hb : b < (s.gpr .r6).toNat) :
      ∀ r ∈ [(⟨s.gpr .r7 + BitVec.ofNat 64 64, 144⟩ : Region)], Region.Disjoint ⟨wAt (s.gpr .r5) b, 8⟩ r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (h.dataScr.sub_left (Offset.sub_base _ (by omega_arith))).sub_right sub144
  have hn := h.nv
  have L : LoopEnv (s.gpr .r3) (s.gpr .r5) (s.syms Impl.Cast5.s1234Sym) (s.gpr .r4).toNat (s.gpr .r6).toNat s₀ :=
    { r3 := g₀ _
      r4 := by rw [g₀ rnd]; simp
      nv := h.nv
      r0 := z₀
      c255 := c₀
      tbl := t₀
      key := by rw [k₀.2.1, k₀.2.2]; exact h.key
      kfit := h.kfit
      data := by rw [k₀.2.2]; exact h.data
      keyData := h.keyData
      fit := fit
      trd := by rw [k₀.2.1, k₀.2.2]; exact h.trd
      held := held_frame fr₀ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [s1234_len]; exact h.tblScr.sub_right sub144)
        (by rw [s1234_len]; decide) h.held
      tblData := h.tblData }
  have I0 : EInv (s.gpr .r3) (s.gpr .r5) (s.gpr .r4).toNat (s.gpr .r6).toNat up s₀ 0 s₀ :=
    ⟨by omega_arith, by rw [g₀ dat]; simp [wAt], by rw [g₀ cnt]; simp, Keep.refl _ _, fun b hb => absurd hb (by omega_arith),
      fun _ _ _ => rfl, Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (Q := EInv (s.gpr .r3) (s.gpr .r5) (s.gpr .r4).toNat (s.gpr .r6).toNat up s₀
    (s.gpr .r6).toNat) ?_ fun u U => ?_
  · refine WP.ite (s.gpr .r6 == 0) (by rw [eval_zero, g₀ cnt]) (fun hz => ?_) (fun hz => ?_)
    · have hn : (s.gpr .r6).toNat = 0 := by simp only [beq_iff_eq] at hz; simp [hz]
      exact WP.block_nil (hn ▸ I0)
    · have hn : 0 < (s.gpr .r6).toNat := by
        have : s.gpr .r6 ≠ 0 := by simpa using hz
        have : (s.gpr .r6).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
        omega_arith
      exact loop_run L hn I0
  · rw [epilogue_eq]
    have r7 : u.gpr wkE = s.gpr .r7 := by rw [U.keep.gpr (by decide), g₀ wkE]
    have hsv : Spill.Saved (s.gpr .r7) (s.write .r0 s.lr).gpr (savedSlots ++ [(.r0, lrOff)]) u.mem :=
      (sv₀.sub (by decide)).frame
        U.frame fun p hp r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (h.dataScr.symm.sub_left (slot_sub _ (restoreSlots_lt p hp)))
    refine Spill.restore_ok (by decide) r7 restoreSlots_ok (by decide) (fun p hp => ?_) hsv fun s' R => ?_
    · rw [U.keep.2.1, U.keep.2.2, k₀.2.1, k₀.2.2]
      exact ⟨_, List.mem_append_right _ h.scr, Offset.contains_base _
        (by have := restoreSlots_lt p hp; omega_arith) (by have := restoreSlots_lt p hp; omega_arith)⟩
    refine WP.cons exec_mtlr (wp_nil ⟨fun b hb => ?_, ?_, fun r hr => ?_, ?_⟩)
    · show Spec.Cast5.blockAt s'.mem _ = _
      rw [R.mem, U.done b hb, scheduleAt_frame fr₀ dS, blockAt_frame fr₀ (dB b hb)]
    · show Frame _ s.mem s'.mem
      rw [R.mem]
      refine (fr₀.sub fun r hr => ?_).trans (U.frame.mono fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub144⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
    · show s'.gpr r = s.gpr r
      have hm : (r, savedOff + 8 * saved.idxOf r) ∈ savedSlots ++ [(.r0, lrOff)] := by
        simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
      have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hr (by decide)
      rw [R.gpr _ hm, RegUpd.gpr_write_of_ne s s.lr h0]
    · show s'.gpr .r0 = s.lr
      rw [R.gpr (.r0, lrOff) (by decide)]
      exact RegUpd.gpr_write_self s _ _

end VG.Proof.Cast5.PPC64LE

end

end

/-!
# CAST5 ECB on PPC64LE: verified

Constant time by the taint analysis: `r3`–`r7` and the table's address are
public (`taintSym`). The proof's contract (`ecbPC`) is `ecbP` for the state
without the table's region, with what the contract says of the table
(`ConstsOk`).
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)

def dir (up : Bool) : Spec.Cast5.Direction := if up then .encrypt else .decrypt

/-- The ECB functions' contract on PPC64LE, as their proof states it. -/
def ecbP (up : Bool) : Contract isa where
  pre s :=
    let sch : Region := ⟨s.gpr .r3, 128⟩
    let dat : Region := ⟨s.gpr .r5, 8 * (s.gpr .r6).toNat⟩
    let scr : Region := ⟨s.gpr .r7, 256⟩
    s.rd = [sch] ∧ s.wr = [dat, scr] ∧ sch.Disjoint dat ∧ sch.Disjoint scr ∧ dat.Disjoint scr ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 * (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + 256 ≤ 2 ^ 64 ∧ ((s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 16)
  post s s' :=
    Spec.Cast5.blocksAt s'.mem (s.gpr .r5) (s.gpr .r6).toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt s.mem (s.gpr .r3)) (s.gpr .r4).toNat (dir up)
        (Spec.Cast5.blocksAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

/-- The ECB functions' contract with the table, as the proof states it. -/
def ecbPC (up : Bool) : Contract isa where
  pre s := (ecbP up).pre (stripConsts ecbConsts s) ∧ ConstsOk ecbConsts 0 s
  post := (ecbP up).post
  pub s₁ s₂ := (ecbP up).pub s₁ s₂ ∧ s₁.syms s1234Sym = s₂.syms s1234Sym

section
variable {name : String} {ws : List (BitVec 64)} {st : Nat} {s : State}

/-- What the contract says of a function's one table: its words. -/
theorem ConstsOk.held1 (h : ConstsOk [(name, ws)] st s) : Held s.mem (s.syms name) ws :=
  h.2.1 _ List.mem_cons_self

/-- The code may read it. -/
theorem ConstsOk.rd1 (h : ConstsOk [(name, ws)] st s) : (⟨s.syms name, 8 * ws.length⟩ : Region) ∈ s.rd :=
  h.mem_rd List.mem_cons_self

/-- No writable region overlaps it. -/
theorem ConstsOk.wr1 (h : ConstsOk [(name, ws)] st s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms name, 8 * ws.length⟩ r :=
  (h.2.2.1 _ List.mem_cons_self).2.1

end

theorem stripConsts_rd_mem {K : List (String × List (BitVec 64))} {s : State} {r : Region}
    (h : r ∈ (stripConsts K s).rd) : r ∈ s.rd := List.mem_of_mem_take h

theorem ecb_blocks (K : Spec.Cast5.Schedule) (n : Nat) (up : Bool) (m m' : Mem) (D : Addr) (N : Nat)
    (h : ∀ b < N, Spec.Cast5.blockAt m' (wAt D b) = cipher up K n (Spec.Cast5.blockAt m (wAt D b))) :
    Spec.Cast5.blocksAt m' D N = Spec.Cast5.ecb K n (dir up) (Spec.Cast5.blocksAt m D N) := by
  simp only [Spec.Cast5.blocksAt, Spec.Cast5.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

/-- The registers ECB writes. -/
def ecbRegs : List Reg := [.r0, .r4, .r5, .r6, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19,
  .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30]

theorem ecb_ok (up : Bool) (hw : writesOnly ecbRegs (ecb up) = true) (hn : (ecb up).noCalls = true)
    (s : State) (hs : (ecbPC up).pre s) :
    ∃ t s', Exec isa (ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbPC up).post s s' := by
  obtain ⟨⟨hrd, hwr, dKD, dKS, dDS, hkf, hdf, hcf, hn'⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr dKD dKS dDS hkf hdf hcf hn'
  have trd : (⟨s.syms s1234Sym, 4096⟩ : Region) ∈ s.rd := s1234_len ▸ ConstsOk.rd1 hk
  have twr : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r := s1234_len ▸ ConstsOk.wr1 hk
  have pre : EcbPre s :=
    { key := List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
      kfit := hkf
      data := by rw [hwr]; simp
      fit := hdf
      scr := by rw [hwr]; simp
      sfit := hcf
      keyData := dKD
      keyScr := dKS
      dataScr := dDS
      nv := hn'
      trd := List.mem_append_left _ trd
      held := ConstsOk.held1 hk
      tblData := twr _ (by rw [hwr]; simp)
      tblScr := twr _ (by rw [hwr]; simp) }
  obtain ⟨t, s', he, hp, hk'⟩ := WP.keep ecbRegs (ecb_wp up pre) hw hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hp.lr⟩,
    ecb_blocks _ _ _ _ _ _ _ hp.done⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    first
    | exact hp.saved _ (by decide)
    | exact hk'.gpr (by decide)

theorem ecb_agree (up : Bool) : ∀ s₁ s₂, (ecbPC up).pre s₁ → (ecbPC up).pre s₂ → (ecbPC up).pub s₁ s₂ →
    (taintSym [s1234Sym]).Agree (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  intro s₁ s₂ _ _ ⟨h, hsy⟩
  refine ⟨⟨h.2.2.2.2.2, fun r hr => ?_⟩, fun n hn => by
    simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

theorem ecbEncrypt_ct : ConstantTime isa (ecbPC true).pre (ecbPC true).pub ecbEncrypt :=
  VG.Taint.constantTime (A := vectorTaintSym [s1234Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (ecb_agree true) (by taint_decide)

theorem ecbDecrypt_ct : ConstantTime isa (ecbPC false).pre (ecbPC false).pub ecbDecrypt :=
  VG.Taint.constantTime (A := vectorTaintSym [s1234Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (ecb_agree false) (by taint_decide)

/-- A state satisfying the precondition without the table: no blocks. -/
def ecbSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 12 | .r5 => 0x2000 | .r7 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 256⟩]

theorem ecbP_implies (up : Bool) : (ecbP up).Implies (Proof.Cast5.ecbRoundsContract abi (dir up)) := by
  cases up <;>
  sig_implies [Proof.Cast5.ecbRoundsContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, Proof.Cast5.ecbRoundsPost, abi, argRegs,
    ecbP, dir] [ecbSat] using ecbSat

theorem ecbConsts_eq : ecbConsts = [(s1234Sym, s1234)] := rfl

/-- The memory of the witness with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def ecbSatMem : Mem := fun a =>
  if (a - 0x100000).toNat < 4096 then constMem 0x100000 s1234 a else 0

theorem ecbSatMem_held : ∀ i < s1234.length,
    ecbSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0 := by
  intro i hi
  have hl : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]
  rw [hl] at hi
  have hm : ecbSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 s1234).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat = 8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hj])]
    unfold ecbSatMem
    rw [e, ite_eq_left (show 8 * i + j < 4096 by omega_using [hi, hj])]
  exact hm.trans (constMem_held 0x100000 s1234 (by rw [hl]; decide) i (by rw [hl]; exact hi))

/-- A state satisfying the precondition with the table. -/
def ecbSatC : State :=
  { ecbSat with mem := ecbSatMem, rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩], syms := fun _ => 0x100000 }

theorem ecb_sat (up : Bool) : (Proof.Cast5.ecbRoundsContract (abi.withConsts ecbConsts) (dir up)).pre ecbSatC := by
  have hl : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]
  have held := ecbSatMem_held
  rw [ecbConsts_eq]
  generalize s1234 = W at hl held ⊢
  generalize e : ecbSatC = s
  sig_pre [Proof.Cast5.ecbRoundsContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, abi, argRegs, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x2000, 0⟩, ⟨0x3000, 256⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem ecbPC_implies (up : Bool) :
    (ecbPC up).Implies (Proof.Cast5.ecbRoundsContract (abi.withConsts ecbConsts) (dir up)) :=
  { pre := fun _ hs => ⟨(ecbP_implies up).pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr ((ecbP_implies up).post (stripConsts ecbConsts s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨(ecbP_implies up).pub (stripConsts ecbConsts s₁) (stripConsts ecbConsts s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨ecbSatC, ecb_sat up⟩ }

theorem ecbEncrypt_verified :
    Verified target ecbEncrypt (Proof.Cast5.ecbEncryptRoundsContract (abi.withConsts ecbConsts)) :=
  Verified.of_correct (ecb_ok true (by lit_decide) (by lit_decide)) ecbEncrypt_ct (ecbPC_implies true)

theorem ecbDecrypt_verified :
    Verified target ecbDecrypt (Proof.Cast5.ecbDecryptRoundsContract (abi.withConsts ecbConsts)) :=
  Verified.of_correct (ecb_ok false (by lit_decide) (by lit_decide)) ecbDecrypt_ct (ecbPC_implies false)

end VG.Proof.Cast5.PPC64LE
