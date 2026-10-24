module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

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
  rw [hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 3 < 128 by omega),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 2 < 128 by omega),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 1 < 128 by omega),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i < 128 by omega)]

/-- Memory holding a table, later: its words are kept by writes apart from it. -/
theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} {W : List (BitVec 64)} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 8 * W.length⟩ r) (hl : 8 * W.length < 2 ^ 64) (h : Held m T W) :
    Held m' T W := fun i hi => by
  rw [hf.readW (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
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
        rw [Offset.add_add]; exact Offset.contains_base D (by omega) (by omega)⟩
      inK := by rw [I.keep.2.1, I.keep.2.2]; exact L.key
      kfit := L.kfit }
  refine WP.seq (WP.mono (crypt_ok bp up) fun u₁ B => ?_)
  refine wp_addi (by decide) (by decide) fun u₂ h₂ => wp_subi (by decide) (by decide) fun u₃ h₃ => wp_nil ?_
  have m₃ : u₃.mem = u₁.mem := by rw [h₃.mem, h₂.mem]
  have c₃ : u₃.gpr cnt = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [h₃.gpr, h₂.other _ (by decide), B.keep.gpr (by decide), I.cnt]
    apply BitVec.eq_of_toNat_eq; simp; omega
  have other : ∀ b, b < N → b ≠ k →
      Spec.Cast5.blockAt u₃.mem (wAt D b) = Spec.Cast5.blockAt u.mem (wAt D b) := fun b hb hne => by
    rw [m₃, blockAt_frame B.frame fun r hr => ?_]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega) (by omega) (by omega)
  refine ⟨⟨by omega, ?_, c₃, ?_, fun b hb => ?_, fun b h1 h2 => ?_, ?_⟩, c₃⟩
  · rw [h₃.other _ (by decide), h₂.gpr, B.keep.gpr (by decide), I.ptr, Offset.add_add]
    congr 2
  · exact (((I.keep.trans B.keep).trans h₂.keep).trans h₃.keep).mono (by decide)
  · by_cases hbk : b = k
    · subst hbk
      rw [m₃, B.blk, hK, I.rest b (by omega) hk]
    · rw [other b (by omega) hbk]; exact I.done b (by omega)
  · rw [other b h2 (by omega)]; exact I.rest b (by omega) h2
  · rw [m₃]
    refine I.frame.trans (B.frame.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Offset.sub_base D (by omega)⟩

theorem loop_run {S D T : Addr} {n N : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D T n N s₀) (hn : 0 < N)
    {u : State} (I : EInv S D n N up s₀ 0 u) :
    WP isa (.loop (.seq (crypt up dat) (.block [.addi dat dat 8, .subi cnt cnt 1])) (.nonzero .d cnt)) u
      (EInv S D n N up s₀ N) := by
  refine WP.loop (M := isa) (Q := EInv S D n N up s₀ N)
    (fun m v => ∃ k, k < N ∧ m = N - k ∧ EInv S D n N up s₀ k v) ?_ N u ⟨0, hn, rfl, I⟩
  intro m v ⟨k, hk, hm, J⟩
  refine WP.mono (ecb_step L hk J) fun v' ⟨J', hz⟩ => ?_
  have hn64 : N < 2 ^ 64 := by have := L.fit; omega
  rw [eval_nonzero, hz, ofNat_bne_zero (by omega)]
  by_cases e : k + 1 = N
  · left
    exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp; omega, N - (k + 1), by omega, k + 1, by omega, rfl, J'⟩

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
    Region.Sub ⟨B + BitVec.ofNat 64 d, 8⟩ ⟨B, 256⟩ := Offset.sub_base _ (by omega)

theorem ecb_wp (up : Bool) {s : State} (h : EcbPre s) :
    WP isa (Impl.Cast5.PPC64LE.ecb up) s (EcbPost up s) := by
  have fit := h.fit
  have sfit := h.sfit
  have hw : ∀ p ∈ allSlots, InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 p.2) 8 := fun p hp =>
    ⟨_, h.scr, Offset.contains_base _ (by have := allSlots_lt p hp; omega) (by have := allSlots_lt p hp; omega)⟩
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
    exact (h.dataScr.sub_left (Offset.sub_base _ (by omega))).sub_right sub144
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
    ⟨by omega, by rw [g₀ dat]; simp [wAt], by rw [g₀ cnt]; simp, Keep.refl _ _, fun b hb => absurd hb (by omega),
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
        omega
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
        (by have := restoreSlots_lt p hp; omega) (by have := restoreSlots_lt p hp; omega)⟩
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
