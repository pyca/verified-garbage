import VerifiedGarbage.Proof.Cast5.X86_64.Block
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# CAST5 on x86-64: ECB

`ecb blk` saves the callee-saved registers in the working space, runs the
block function `blk` once for each block, and restores them (`ecb_ok`).
-/

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5.X86_64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym ecbConsts keyConsts)
open VG.Proof.MlKem.X86_64 (Keep sx_ofNat WP.keep writesOnly wp_countdown)

/-- The facts of the ECB functions' precondition on this target (the shared
contract's, `Spec.Cast5.ecbContract`, with the table `VG_CAST5_S1234`). -/
structure EPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, 128⟩, ⟨s.syms s1234Sym, 4096⟩]
  wr : s.wr = [⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩, ⟨s.gpr .r8, 256⟩]
  held : ∀ i < 512, s.mem.readW (s.syms s1234Sym + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 64
  dTD : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩
  dTS : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .r8, 256⟩
  dKD : Region.Disjoint ⟨s.gpr .rdi, 128⟩ ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩
  dKS : Region.Disjoint ⟨s.gpr .rdi, 128⟩ ⟨s.gpr .r8, 256⟩
  dDS : Region.Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩ ⟨s.gpr .r8, 256⟩
  dspD : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩
  dspS : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r8, 256⟩
  fK : (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64
  fD : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat * 8 ≤ 2 ^ 64
  fS : (s.gpr .r8).toNat + 256 ≤ 2 ^ 64
  rounds : (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 16

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr)
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : Spec.Cast5.blockAt m' p = Spec.Cast5.blockAt m p := by
  apply Vector.ext
  intro i hi
  rw [blockAt_get _ _ hi, blockAt_get _ _ hi]
  exact hf.bytes hd (by change 8 ≤ 2 ^ 64; decide) hi

/-- The saved registers, and where. -/
theorem saved_eq : saved = [(.rbx, 16), (.rbp, 24), (.r12, 32), (.r13, 40), (.r14, 48), (.r15, 56)] := rfl

theorem slot_sep (m : Mem) (S : Addr) {a b : Nat} (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 2 ^ 64)
    (hb : b + 8 ≤ 2 ^ 64) (v : BitVec 64) :
    (m.writeW (S + BitVec.ofNat 64 b) v).readW (S + BitVec.ofNat 64 a) 64 = m.readW (S + BitVec.ofNat 64 a) 64 :=
  Mem.readW_writeW_sep (Offset.sep S h ha hb) (by decide)

/-- The callee-saved registers saved in the working space at `r8`, which is
otherwise unchanged; ZF set if there are no blocks. -/
theorem save_ok (s : State) (hw : InRegions s.wr (s.gpr .r8) 256) :
    WP isa (.block (save ++ ([.alu .test .rcx (.reg .rcx)] : List Instr))) s fun u =>
      u.gpr = s.gpr ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms ∧
      Frame [⟨s.gpr .r8, 256⟩] s.mem u.mem ∧
      (∀ r d, (r, d) ∈ saved → u.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 = s.gpr r) ∧
      u.zf = some (s.gpr .rcx == 0) := by
  have hs (d : Nat) (hd : d + 8 ≤ 256) : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 d) 8 :=
    CallLay.inRegions_sub hw hd (by decide)
  have h16 := hs 16 (by decide)
  have h24 := hs 24 (by decide)
  have h32 := hs 32 (by decide)
  have h40 := hs 40 (by decide)
  have h48 := hs 48 (by decide)
  have h56 := hs 56 (by decide)
  rw [saved_eq] at *
  unfold save
  rw [saved_eq]
  xrun [VG.Proof.Cast5.X86_64.ea_at, h16, h24, h32, h40, h48, h56, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, BitVec.and_self]
  have hc (d : Nat) (hd : d + 8 ≤ 256) : Region.Contains ⟨s.gpr .r8, 256⟩ (s.gpr .r8 + BitVec.ofNat 64 d) (64 / 8) :=
    Offset.contains_base _ (by omega) (by omega)
  refine ⟨rfl, ?_, fun r d h => ?_⟩
  · refine (((((((Frame.refl _ _).writeW List.mem_cons_self _ (hc 16 (by decide))).writeW List.mem_cons_self _
      (hc 24 (by decide))).writeW List.mem_cons_self _ (hc 32 (by decide))).writeW List.mem_cons_self _
      (hc 40 (by decide))).writeW List.mem_cons_self _ (hc 48 (by decide))).writeW List.mem_cons_self _
      (hc 56 (by decide)))
  · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp (disch := decide) only [slot_sep, Mem.readW_writeW_self64]

/-- The callee-saved registers loaded back from the working space. -/
theorem restore_ok (u : State) {val : Reg → BitVec 64}
    (hin : InRegions (u.rd ++ u.wr) (u.gpr .r8) 256)
    (hslot : ∀ r d, (r, d) ∈ saved → u.mem.readW (u.gpr .r8 + BitVec.ofNat 64 d) 64 = val r) :
    WP isa (.block restore) u fun v =>
      (∀ r d, (r, d) ∈ saved → v.gpr r = val r) ∧ v.mem = u.mem ∧
      (∀ q, q ≠ .rbx → q ≠ .rbp → q ≠ .r12 → q ≠ .r13 → q ≠ .r14 → q ≠ .r15 → v.gpr q = u.gpr q) := by
  have hs (d : Nat) (hd : d + 8 ≤ 256) : InRegions (u.rd ++ u.wr) (u.gpr .r8 + BitVec.ofNat 64 d) 8 :=
    CallLay.inRegions_sub hin hd (by decide)
  rw [saved_eq] at hslot
  have v16 := hslot .rbx 16 (by simp)
  have v24 := hslot .rbp 24 (by simp)
  have v32 := hslot .r12 32 (by simp)
  have v40 := hslot .r13 40 (by simp)
  have v48 := hslot .r14 48 (by simp)
  have v56 := hslot .r15 56 (by simp)
  unfold restore
  rw [saved_eq]
  xrun [VG.Proof.Cast5.X86_64.ea_at, hs 16 (by decide), hs 24 (by decide), hs 32 (by decide),
    hs 40 (by decide), hs 48 (by decide), hs 56 (by decide), v16, v24, v32, v40, v48, v56,
    List.map_cons, List.map_nil]
  refine ⟨fun r d h => ?_, fun q h1 h2 h3 h4 h5 h6 => ?_⟩
  · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · simp only [h1, h2, h3, h4, h5, h6, ite_false]

/-- The state of the ECB loop with `b` blocks done, from `s`, each block `x`
replaced with `f x`. -/
structure LInv (s : State) (f : Spec.Cast5.Block → Spec.Cast5.Block) (b : Nat) (u : State) : Prop where
  rdi : u.gpr .rdi = s.gpr .rdi
  rsi : u.gpr .rsi = s.gpr .rsi
  r8 : u.gpr .r8 = s.gpr .r8
  rsp : u.gpr .rsp = s.gpr .rsp
  rdx : u.gpr .rdx = s.gpr .rdx + BitVec.ofNat 64 (8 * b)
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  syms : u.syms = s.syms
  frame : Frame [⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩, ⟨s.gpr .r8, 256⟩] s.mem u.mem
  slots : ∀ r d, (r, d) ∈ saved → u.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 = s.gpr r
  data : ∀ j < (s.gpr .rcx).toNat,
    Spec.Cast5.blockAt u.mem (s.gpr .rdx + BitVec.ofNat 64 (8 * j)) =
      if j < b then f (Spec.Cast5.blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (8 * j)))
      else Spec.Cast5.blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (8 * j))

/-- Both writable regions are disjoint from a region disjoint from each. -/
theorem wr_disj {s : State} {R : Region} (h1 : R.Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩)
    (h2 : R.Disjoint ⟨s.gpr .r8, 256⟩) :
    ∀ r ∈ [(⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩ : Region), ⟨s.gpr .r8, 256⟩], R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h1
  · exact h2

/-- A block's precondition, inside the loop. -/
theorem LInv.bpre {s u : State} (h : EPre s) {f : Spec.Cast5.Block → Spec.Cast5.Block} {b : Nat}
    (hu : LInv s f b u) (hb : b < (s.gpr .rcx).toNat) :
    BPre u (Spec.Cast5.scheduleAt s.mem (s.gpr .rdi)) (s.gpr .rsi).toNat := by
  have hdK := wr_disj h.dKD h.dKS
  have hdT := wr_disj h.dTD h.dTS
  have sub16 : Region.Sub ⟨s.gpr .r8, 16⟩ ⟨s.gpr .r8, 256⟩ := Region.sub_prefix (by decide)
  refine ⟨⟨?_, fun j hj => ?_, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩, h.rounds, ?_, ?_⟩
  · rw [hu.rd, hu.wr, hu.rdi, h.rd]
    exact ⟨_, List.mem_append_left _ List.mem_cons_self, Region.contains_self _ _⟩
  · rw [hu.rdi, scheduleAt_getD _ _ hj, hu.frame.readW (r := ⟨s.gpr .rdi, 128⟩)
      (Offset.contains_base _ (by omega) (by omega)) hdK (by decide)]
  · rw [hu.wr, hu.r8, h.wr]
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by unfold Region.Contains; simp⟩
  · unfold Readable; rw [hu.rd, hu.wr, hu.syms, h.rd]
    exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), Region.contains_self _ _⟩
  · rw [s1234_length] at hi
    rw [hu.syms, hu.frame.readW (r := ⟨s.syms s1234Sym, 4096⟩)
      (Offset.contains_base _ (by omega) (by omega)) hdT (by decide)]
    exact h.held i hi
  · rw [hu.rdi, hu.r8]; exact h.dKS.sub_right sub16
  · rw [hu.syms, hu.r8]; exact h.dTS.sub_right sub16
  · rw [hu.rdi]; exact h.fK
  · rw [hu.syms]; exact h.fitT
  · rw [hu.rsi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hu.wr, hu.rdx, h.wr]
    exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by have := h.fD; omega)⟩

/-- The loop's step: a block function run on block `b`. -/
theorem LInv.step {s u v : State} (h : EPre s) {f : Spec.Cast5.Block → Spec.Cast5.Block} {b : Nat}
    (hu : LInv s f b u) (hb : b < (s.gpr .rcx).toNat)
    (hv : BPost u (f (Spec.Cast5.blockAt u.mem (u.gpr .rdx))) v) : LInv s f (b + 1) v := by
  obtain ⟨vout, vf, vdx, _, _, vrd, vwr, vsy, vg⟩ := hv
  have g (q : Reg) (hq : q ∉ roundRegs) (h13 : q ≠ .r13) (hdx : q ≠ .rdx) (hcx : q ≠ .rcx) :
      v.gpr q = u.gpr q := vg q hq h13 hdx hcx
  have hN := h.fD
  -- The regions the block function writes, within those of the function.
  have sD : Region.Sub ⟨u.gpr .rdx, 8⟩ ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩ := by
    rw [hu.rdx]; exact Offset.sub_base _ (by omega)
  have sS : Region.Sub ⟨u.gpr .r8, 16⟩ ⟨s.gpr .r8, 256⟩ := by rw [hu.r8]; exact Region.sub_prefix (by decide)
  -- What lies outside both.
  have outside {R : Region} (hD : R.Disjoint ⟨u.gpr .rdx, 8⟩) (hS : R.Disjoint ⟨u.gpr .r8, 16⟩) :
      ∀ r ∈ [(⟨u.gpr .rdx, 8⟩ : Region), ⟨u.gpr .r8, 16⟩], R.Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hD
    · exact hS
  refine ⟨(g .rdi (by decide) (by decide) (by decide) (by decide)).trans hu.rdi,
    (g .rsi (by decide) (by decide) (by decide) (by decide)).trans hu.rsi,
    (g .r8 (by decide) (by decide) (by decide) (by decide)).trans hu.r8,
    (g .rsp (by decide) (by decide) (by decide) (by decide)).trans hu.rsp, ?_, vrd.trans hu.rd,
    vwr.trans hu.wr, vsy.trans hu.syms, ?_, fun r d hrd => ?_, fun j hj => ?_⟩
  · rw [vdx, hu.rdx, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, add_ofNat_add]; congr 2
  · refine hu.frame.trans (vf.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, sD⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sS⟩
  · have hd : 16 ≤ d ∧ d ≤ 56 := by
      simp only [saved_eq, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hrd
      omega
    have sSlot : Region.Sub ⟨s.gpr .r8 + BitVec.ofNat 64 d, 8⟩ ⟨s.gpr .r8, 256⟩ := Offset.sub_base _ (by omega)
    rw [vf.readW (r := ⟨s.gpr .r8 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (outside
      ((h.dDS.symm.sub_left sSlot).sub_right sD)
      (by rw [hu.r8]; exact Offset.disjoint_base _ (by omega) (by omega))) (by decide)]
    exact hu.slots r d hrd
  · by_cases hjb : j = b
    · subst hjb
      have hd := hu.data j hj
      rw [ite_eq_right (Nat.lt_irrefl _)] at hd
      rw [ite_eq_left (Nat.lt_succ_self _), ← hd, ← hu.rdx, vout]
    · have hsub : Region.Sub ⟨s.gpr .rdx + BitVec.ofNat 64 (8 * j), 8⟩ ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩ :=
        Offset.sub_base _ (by omega)
      rw [blockAt_frame vf _ (outside (by rw [hu.rdx]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        ((h.dDS.sub_left hsub).sub_right sS)), hu.data j hj]
      by_cases hjl : j < b
      · rw [ite_eq_left hjl, ite_eq_left (by omega)]
      · rw [ite_eq_right hjl, ite_eq_right (by omega)]

theorem toNat_eq_zero_of_beq {x : BitVec 64} (h : (x == 0) = true) : x.toNat = 0 := by
  rw [beq_iff_eq] at h; rw [h]; rfl

/-- `ecb blk`, for a block function `blk` that replaces the block `x` at `rdx`
with `f k n x`. -/
theorem ecb_ok {blk : Prog isa} {f : Spec.Cast5.Schedule → Nat → Spec.Cast5.Block → Spec.Cast5.Block}
    (hblk : ∀ u k n, BPre u k n → WP isa blk u (BPost u (f k n (Spec.Cast5.blockAt u.mem (u.gpr .rdx)))))
    (s : State) (h : EPre s) :
    WP isa (ecb blk) s fun t =>
      Spec.Cast5.blocksAt t.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
        (Spec.Cast5.blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).map
          (f (Spec.Cast5.scheduleAt s.mem (s.gpr .rdi)) (s.gpr .rsi).toNat) ∧
      gprPreserved s t := by
  let F := f (Spec.Cast5.scheduleAt s.mem (s.gpr .rdi)) (s.gpr .rsi).toNat
  have hw : InRegions s.wr (s.gpr .r8) 256 := by
    rw [h.wr]; exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
  have sS : ∀ j < (s.gpr .rcx).toNat,
      Region.Sub ⟨s.gpr .rdx + BitVec.ofNat 64 (8 * j), 8⟩ ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩ :=
    fun j hj => Offset.sub_base _ (by omega)
  unfold ecb
  refine WP.seq (WP.mono (save_ok s hw) fun u ⟨ug, urd, uwr, usy, uf, uslot, uz⟩ => ?_)
  have h0 : LInv s F 0 u := by
    refine ⟨by rw [ug], by rw [ug], by rw [ug], by rw [ug], by rw [ug, Nat.mul_zero, BitVec.add_zero], urd,
      uwr, usy, uf.mono fun r hr => ?_, uslot, fun j hj => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; exact .inr hr
    · rw [ite_eq_right (Nat.not_lt_zero _)]
      refine blockAt_frame uf _ fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact h.dDS.sub_left (sS j hj)
  -- The blocks.
  have loop : WP isa (.ite .e (.block []) (.loop blk .ne)) u (LInv s F (s.gpr .rcx).toNat) := by
    refine WP.ite (s.gpr .rcx == 0) uz (fun hz => ?_) (fun hz => ?_)
    · rw [toNat_eq_zero_of_beq hz]
      exact WP.block_nil h0
    · have hpos : 0 < (s.gpr .rcx).toNat := by
        apply Nat.pos_of_ne_zero
        intro e
        have : s.gpr .rcx = 0 := BitVec.eq_of_toNat_eq e
        rw [this] at hz
        exact absurd hz (by decide)
      refine wp_countdown (cnt := .rcx) (N := (s.gpr .rcx).toNat) (s.gpr .rcx).isLt hpos (LInv s F)
        (fun i hi v hv _ => WP.mono (hblk v _ _ (hv.bpre h hi)) fun w hw' => ?_) (fun _ h => h) h0
        (by rw [ug, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      exact ⟨hv.step h hi hw', hw'.2.2.2.1, hw'.2.2.2.2.1⟩
  refine WP.seq (WP.mono loop fun v hv => ?_)
  have hin : InRegions (v.rd ++ v.wr) (v.gpr .r8) 256 := by
    rw [hv.rd, hv.wr, hv.r8]; obtain ⟨g, hg, hc⟩ := hw; exact ⟨g, List.mem_append_right _ hg, hc⟩
  refine WP.mono (restore_ok v (val := s.gpr) hin (by rw [hv.r8]; exact hv.slots)) fun t ⟨tg, tm, to⟩ => ?_
  refine ⟨?_, ⟨fun r hr => ?_, ?_⟩⟩
  · simp only [Spec.Cast5.blocksAt, List.map_map, tm]
    refine List.map_congr_left fun j hj => ?_
    rw [Function.comp_apply, hv.data j (List.mem_range.mp hj), ite_eq_left (List.mem_range.mp hj)]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tg _ 16 (by decide)
    · exact tg _ 24 (by decide)
    · rw [to .rsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hv.rsp]
    · exact tg _ 32 (by decide)
    · exact tg _ 40 (by decide)
    · exact tg _ 48 (by decide)
    · exact tg _ 56 (by decide)
  · rw [tm, hv.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (wr_disj h.dspD h.dspS) (by decide)]

end VG.Proof.Cast5.X86_64
