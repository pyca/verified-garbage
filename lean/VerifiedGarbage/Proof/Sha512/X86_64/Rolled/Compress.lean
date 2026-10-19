module

public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Rounds
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# SHA-512 on x86-64, rolled: the compression function

`correct` proves `Impl.Sha512.X86_64.Rolled.compress` correct from
`Avx2.Pre`, the precondition of `Proof.Sha512.compressWideX86_64` (1328 bytes
of scratch space). The proof follows the unrolled one
(`Proof/Sha512/X86_64/Compress.lean`), whose lemmas for the schedule, the
loading and the updating of the hash value it uses: the first sixteen rounds
run unrolled (`first_ok`), the others sixteen per iteration of a loop
(`iter_ok`), through the index `rdx = 128 j`.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Rolled

open VG VG.X86_64 VG.Impl.Sha512.X86_64 VG.Impl.Sha512.X86_64.Rolled
open VG.Spec.Sha512 (HashValue Word Block K W stateAt blockAt compressBlocks compress)
open VG.Proof.Sha512.X86_64 (Vars pubRegs st bp nb scr stR blR retR H₀ blkAddr blk blk_word
  compressBlocks_succ contains_offset contains_offset' ofInt_natCast stateAt_get stateAt_eq
  writeState stateAt_writeState frame_writeState slotAddr winRegion win_contains slot_sep
  schedule_ok load_ok_of update_ok_of work_ne var_mem pubRegs_ne ea_at Saved saved_bound saveMem)

/-- The scratch space of the shared contract. -/
abbrev scrW (s₀ : State) : Region := ⟨scr s₀, 1328⟩

/-! ## Regions -/

namespace Pre
variable {s₀ : State} (h : Avx2.Pre s₀)
include h

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 8 :=
  ⟨scrW s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 8 :=
  ⟨scrW s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 8 := by
  have := h.nb_lt
  rw [ofInt_natCast, show blkAddr s₀ i + BitVec.ofNat 64 (8 * t) =
    bp s₀ + BitVec.ofNat 64 (128 * i + 8 * t) from Offset.add_ofNat_add_ofNat _ _ _]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 8 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## Keeping `rsi` and `rdx` in the scratch space -/

/-- Where `enter` keeps `rsi` and `rdx`. -/
abbrev spA (scr : Addr) : Addr := Spill.slot scr 176
abbrev spB (scr : Addr) : Addr := Spill.slot scr 184

/-- The slots that keep `rsi` and `rdx`. -/
abbrev spR (p : Addr) : Region := ⟨spA p, 16⟩

theorem sp_sub (p : Addr) : Region.Sub (spR p) ⟨p, 1328⟩ := Offset.sub_base _ (by omega)

theorem win_sp (p : Addr) : Region.Disjoint (winRegion p) (spR p) :=
  Offset.base_disjoint _ (by omega) (by omega)

theorem win_sub (p : Addr) : Region.Sub (winRegion p) ⟨p, 1328⟩ := Region.sub_prefix (by omega)

theorem enter_ok (s : State) (hA : InRegions s.wr (spA (s.gpr .rcx)) 8)
    (hB : InRegions s.wr (spB (s.gpr .rcx)) 8) :
    WP isa (.block enter) s fun s' =>
      s'.gpr .rsi = s.syms kSym ∧ s'.gpr .rdx = s.gpr .rsi ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW (spA (s.gpr .rcx)) (s.gpr .rsi)).writeW (spB (s.gpr .rcx)) (s.gpr .rdx) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [enter, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, State.store64,
    Spill.ea_slot, hA, hB, ite_true, State.setReg, Option.map_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨by simp, by simp, fun r h1 h2 => by simp [h1, h2], by simp, trivial, trivial⟩

theorem leave_ok (s : State) (hA : InRegions (s.rd ++ s.wr) (spA (s.gpr .rcx)) 8)
    (hB : InRegions (s.rd ++ s.wr) (spB (s.gpr .rcx)) 8) :
    WP isa (.block leave) s fun s' =>
      s'.gpr .rsi = s.mem.readW (spA (s.gpr .rcx)) 64 ∧ s'.gpr .rdx = s.mem.readW (spB (s.gpr .rcx)) 64 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [leave, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, State.load64,
    Spill.ea_slot, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    reduceCtorEq, ↓reduceIte, hA, hB, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 => by simp [h1, h2], trivial, trivial, trivial⟩

theorem spill_read (p : Addr) (m : Mem) (a b : BitVec 64) :
    ((m.writeW (spA p) a).writeW (spB p) b).readW (spA p) 64 = a ∧
      ((m.writeW (spA p) a).writeW (spB p) b).readW (spB p) 64 = b :=
  ⟨(Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)).trans
    (Mem.readW_writeW_self m _ 8 a (by decide)), Mem.readW_writeW_self _ _ 8 b (by decide)⟩

theorem spA_in (p : Addr) : (spR p).Contains (spA p) 8 :=
  Offset.contains (e := 176) (d := 176) (n := 8) (k := 16) p (by omega) (by omega) (by omega)

theorem spB_in (p : Addr) : (spR p).Contains (spB p) 8 :=
  Offset.contains (e := 176) (d := 184) (n := 8) (k := 16) p (by omega) (by omega) (by omega)

theorem spill_frame (p : Addr) (m : Mem) (a b : BitVec 64) :
    Frame [spR p] m ((m.writeW (spA p) a).writeW (spB p) b) := by
  refine ((Frame.refl _ m).writeW (List.mem_singleton_self _) a ?_).writeW (List.mem_singleton_self _) b ?_
  · exact spA_in p
  · exact spB_in p

theorem spill_keep {p : Addr} {m m' : Mem} (hf : Frame [winRegion p] m m') :
    m'.readW (spA p) 64 = m.readW (spA p) 64 ∧ m'.readW (spB p) 64 = m.readW (spB p) 64 :=
  ⟨hf.readW (spA_in _) (by simpa using (win_sp _).symm) (by decide),
    hf.readW (spB_in _) (by simpa using (win_sp _).symm) (by decide)⟩

theorem sp_in {s₀ : State} (hp : Avx2.Pre s₀) {s : State} (hrcx : s.gpr .rcx = scr s₀)
    (hwr : s.wr = s₀.wr) :
    InRegions s.wr (spA (s.gpr .rcx)) 8 ∧ InRegions s.wr (spB (s.gpr .rcx)) 8 := by
  rw [hrcx, hwr]
  exact ⟨⟨scrW s₀, by simp [hp.wr], Offset.contains_base (d := 176) (n := 8) (k := 1328) _ (by omega) (by omega)⟩,
    ⟨scrW s₀, by simp [hp.wr], Offset.contains_base (d := 184) (n := 8) (k := 1328) _ (by omega) (by omega)⟩⟩

theorem sp_in' {s₀ : State} (hp : Avx2.Pre s₀) {s : State} (hrcx : s.gpr .rcx = scr s₀)
    (hwr : s.wr = s₀.wr) :
    InRegions (s.rd ++ s.wr) (spA (s.gpr .rcx)) 8 ∧ InRegions (s.rd ++ s.wr) (spB (s.gpr .rcx)) 8 := by
  obtain ⟨⟨r, hr, hc⟩, ⟨r', hr', hc'⟩⟩ := sp_in hp hrcx hwr
  exact ⟨⟨r, List.mem_append_right _ hr, hc⟩, ⟨r', List.mem_append_right _ hr', hc'⟩⟩

/-! ## The loop's index -/

theorem e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide

theorem toLoop_ok (s : State) :
    WP isa (.block toLoop) s fun s' =>
      s'.gpr .rdx = idx 1 ∧ (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [toLoop, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, State.setReg,
    Option.map_some, Option.some.injEq, exists_eq_left', e128, ↓reduceIte]
  exact ⟨rfl, fun r h => by simp [h], trivial, trivial, trivial⟩

theorem step_ok (s : State) :
    WP isa (.block step) s fun s' =>
      eval .ne s' = some (!(s.gpr .rdx + 128 - BitVec.signExtend 64 (640 : BitVec 32) == 0)) ∧
      s'.gpr .rdx = s.gpr .rdx + 128 ∧ (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [step, ↓reduceIte, Nat.reducePow, and_self, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, State.setReg, arithFlags, State.setFlags, e128,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial, fun r h => by simp [h], trivial⟩

/-- The loop stops after iteration 4: `128 (j + 1) = 640`. -/
theorem step_idx {j : Nat} (hj : j < 5) :
    (idx j + 128 - BitVec.signExtend 64 (640 : BitVec 32) == 0) = (j + 1 == 5) := by
  revert j; decide

theorem idx_succ (j : Nat) : idx j + 128 = idx (j + 1) := by
  simp only [idx]
  rw [show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, ← BitVec.ofNat_add]
  congr 1

/-! ## The first sixteen rounds -/

/-- `schedule t` (`t < 16`), reading the block through `rdx`. -/
theorem schedule0_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hrdx : s.gpr .rdx = bp) (hrcx : s.gpr .rcx = scr)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 8)
    (hbin : InRegions (s.rd ++ s.wr) (bp + BitVec.ofInt 64 ↑(8 * t)) 8)
    (hblk : bswap64 (s.mem.readW (bp + BitVec.ofInt 64 ↑(8 * t)) 64) = W M t) :
    WP isa (.block (schedule0 t)) s fun s' =>
      s'.gpr T0 = W M t ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ T0 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hout ⊢
  apply WP.of_runBlock
  simp only [schedule0, slot, at_, T0]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, State.ea,
    State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, hrdx, hrcx, hbin, hout, hblk,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r h0 => ?_⟩
  simp [h0]

/-- The registers the rounds keep. -/
theorem pub_of {s s' : State} (h : ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) :
    ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := fun r hr =>
  have := pubRegs_ne hr; h r this.1 this.2.1 this.2.2

theorem vars_of {t : Nat} {s s' : State} {v : HashValue} (hv : Vars t s v)
    (h : ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) : Vars t s' v := by
  have e : ∀ k, s'.gpr (var t k) = s.gpr (var t k) := fun k =>
    have := work_ne (var_mem t k); h _ this.1 this.2.1 this.2.2
  simp only [Vars, e] at hv ⊢
  exact hv

/-- What the rounds keep of the state `sE` they start from, and the window
of the schedule after round `n`. -/
structure Win (M : Block) (scr : Addr) (sE : State) (n : Nat) (s : State) : Prop where
  rd : s.rd = sE.rd
  wr : s.wr = sE.wr
  syms : s.syms = sE.syms
  frame : Frame [winRegion scr] sE.mem s.mem
  win : ∀ j < n, n ≤ j + 16 → s.mem.readW (slotAddr scr j) 64 = W M j

/-- After round `t`'s schedule step and round, the window holds `W M t`. -/
theorem Win.step {M : Block} {scr : Addr} {sE s s' : State} {t : Nat} (h : Win M scr sE t s)
    (hm : s'.mem = s.mem.writeW (slotAddr scr t) (W M t)) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) : Win M scr sE (t + 1) s' := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsy.trans h.syms, ?_, fun j hj hj' => ?_⟩
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
  · rw [hm]
    by_cases hjt : j = t
    · subst hjt; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (slot_sep scr (by omega)) (by decide)]
      exact h.win j (by omega) (by omega)

/-- The first `n ≤ 16` rounds, from `sE`, after `enter`: the block at `rdx`, the table at `rsi`. -/
theorem first_ok (H : HashValue) (M : Block) (bp scr : Addr) (sE : State)
    (hrdx : sE.gpr .rdx = bp) (hrcx : sE.gpr .rcx = scr) (hrsi : sE.gpr .rsi = sE.syms kSym)
    (hout : ∀ j, InRegions sE.wr (slotAddr scr j) 8)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sE.rd ++ sE.wr) (bp + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 8)
    (hblk : ∀ m, Frame [winRegion scr] sE.mem m →
      ∀ t : Nat, t < 16 → bswap64 (m.readW (bp + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M t)
    (h0 : Vars 0 sE H) :
    ∀ n ≤ 16, WP isa (first n) sE fun s =>
      Vars n s (VG.Spec.Sha512.rounds H M n) ∧ (∀ r ∈ pubRegs, s.gpr r = sE.gpr r) ∧
      Win M scr sE n s := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨by rw [rounds_zero]; exact h0, fun _ _ => rfl,
      ⟨rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s ⟨hv, hpub, hW⟩ => ?_)
    rw [WP.block_append_iff]
    have hs_rdx : s.gpr .rdx = bp := (hpub .rdx (by decide)).trans hrdx
    have hs_rcx : s.gpr .rcx = scr := (hpub .rcx (by decide)).trans hrcx
    refine VG.X86_64.WP.mono_syms (schedule0_ok n s M bp scr hs_rdx hs_rcx
      (by rw [hW.wr]; exact hout) (by rw [hW.rd, hW.wr]; exact hbin n (by omega))
      (hblk _ hW.frame n (by omega))) fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ hsy₁ => ?_
    have hr₁' : ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → s₁.gpr r = s.gpr r := fun r h _ _ => hr₁ r h
    have hv₁ := vars_of hv hr₁'
    have hb : s₁.gpr .rsi = s₁.syms kSym := by
      rw [hr₁' .rsi (by decide) (by decide) (by decide), hpub .rsi (by decide), hrsi, hsy₁, hW.syms]
    refine VG.X86_64.WP.mono_syms (round_ok n (kSlot0 n) s₁ _ (K n) _ hv₁
      (exec_kSlot0 s₁ _ (by omega) hb) hT0) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ hsy₂ => ?_
    refine ⟨by rw [rounds_succ, round_eq]; exact hv₂, fun r hr => ?_,
      hW.step (hm₂.trans hm₁) (hrd₂.trans hrd₁) (hwr₂.trans hwr₁) (hsy₂.trans hsy₁)⟩
    rw [hr₂ r hr, pub_of hr₁' r hr, hpub r hr]

/-! ## The iterations -/

theorem slot_mod {a b : Nat} (h : a % 16 = b % 16) : slot a = slot b := by
  simp only [slot, h]

/-- The schedule step of round `16 + t'` is that of round `16 j + t'`. -/
theorem schedule_shift {j t' : Nat} (hj : 1 ≤ j) :
    schedule (16 + t') = schedule (16 * j + t') := by
  simp only [Impl.Sha512.X86_64.schedule, show ¬(16 + t' < 16) by omega, show ¬(16 * j + t' < 16) by omega,
    ite_false, slot_mod (show (16 + t' + 14) % 16 = (16 * j + t' + 14) % 16 by omega),
    slot_mod (show (16 + t' + 9) % 16 = (16 * j + t' + 9) % 16 by omega),
    slot_mod (show (16 + t' + 1) % 16 = (16 * j + t' + 1) % 16 by omega),
    slot_mod (show (16 + t') % 16 = (16 * j + t') % 16 by omega)]

theorem vars16 {s : State} {v : HashValue} : Vars 16 s v ↔ Vars 0 s v := by
  simp only [Vars, var]

/-- The first `n ≤ 16` rounds of iteration `j` (`1 ≤ j < 5`), from its start `sI`. -/
theorem iter_ok (H : HashValue) (M : Block) (scr : Addr) (sE sI : State) {j : Nat} (hj : 1 ≤ j) (hj' : j < 5)
    (hrcx : sE.gpr .rcx = scr) (hrsi : sE.gpr .rsi = sE.syms kSym)
    (hout : ∀ i, InRegions sE.wr (slotAddr scr i) 8)
    (hin : ∀ i, InRegions (sE.rd ++ sE.wr) (slotAddr scr i) 8)
    (h0 : Vars 0 sI (VG.Spec.Sha512.rounds H M (16 * j)))
    (hpub0 : ∀ r ∈ pubRegs, r ≠ .rdx → sI.gpr r = sE.gpr r) (hrdx0 : sI.gpr .rdx = idx j)
    (hW0 : Win M scr sE (16 * j) sI) :
    ∀ n ≤ 16, WP isa (iter n) sI fun s =>
      Vars n s (VG.Spec.Sha512.rounds H M (16 * j + n)) ∧
      (∀ r ∈ pubRegs, r ≠ .rdx → s.gpr r = sE.gpr r) ∧ s.gpr .rdx = idx j ∧
      Win M scr sE (16 * j + n) s := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil (M := isa) ⟨h0, hpub0, hrdx0, hW0⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s ⟨hv, hpub, hrdx, hW⟩ => ?_)
    rw [WP.block_append_iff, schedule_shift hj]
    have hs_rcx : s.gpr .rcx = scr := (hpub .rcx (by decide) (by decide)).trans hrcx
    refine VG.X86_64.WP.mono_syms (schedule_ok (16 * j + n) s M (s.gpr .rsi) scr rfl hs_rcx
      (by rw [hW.rd, hW.wr]; exact hin) (by rw [hW.wr]; exact hout)
      (fun h => absurd h (by omega)) (fun h => absurd h (by omega)) (fun _ => hW.win))
      fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ hsy₁ => ?_
    have hv₁ : Vars n s₁ (VG.Spec.Sha512.rounds H M (16 * j + n)) := vars_of hv hr₁
    have hrdx₁ : s₁.gpr .rdx = idx j := (hr₁ .rdx (by decide) (by decide) (by decide)).trans hrdx
    have hb : s₁.gpr .rsi = s₁.syms kSym := by
      rw [hr₁ .rsi (by decide) (by decide) (by decide), hpub .rsi (by decide) (by decide), hrsi, hsy₁,
        hW.syms]
    refine VG.X86_64.WP.mono_syms (round_ok n (kSlot n) s₁ _ (K (16 * j + n)) _ hv₁
      (exec_kSlot s₁ _ n hrdx₁ hb (by omega)) hT0) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ hsy₂ => ?_
    refine ⟨by rw [show 16 * j + (n + 1) = 16 * j + n + 1 by omega, rounds_succ, round_eq]; exact hv₂,
      fun r hr hr' => ?_, by rw [hr₂ .rdx (by decide)]; exact hrdx₁, ?_⟩
    · rw [hr₂ r hr, pub_of hr₁ r hr, hpub r hr hr']
    · rw [show 16 * j + (n + 1) = 16 * j + n + 1 by omega]
      exact hW.step (hm₂.trans hm₁) (hrd₂.trans hrd₁) (hwr₂.trans hwr₁) (hsy₂.trans hsy₁)

/-- `Win` through code that changes only `rdx` and the flags. -/
theorem Win.of_eq {M : Block} {scr : Addr} {sE s s' : State} {n : Nat} (h : Win M scr sE n s)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsy : s'.syms = s.syms) :
    Win M scr sE n s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsy.trans h.syms, hm ▸ h.frame, fun j hj hj' => hm ▸ h.win j hj hj'⟩

/-- Rounds 16–79: the loop's four iterations. -/
theorem loop_ok (H : HashValue) (M : Block) (scr : Addr) (sE sL : State)
    (hrcx : sE.gpr .rcx = scr) (hrsi : sE.gpr .rsi = sE.syms kSym)
    (hout : ∀ i, InRegions sE.wr (slotAddr scr i) 8)
    (hin : ∀ i, InRegions (sE.rd ++ sE.wr) (slotAddr scr i) 8)
    (h0 : Vars 0 sL (VG.Spec.Sha512.rounds H M 16))
    (hpub0 : ∀ r ∈ pubRegs, r ≠ .rdx → sL.gpr r = sE.gpr r) (hrdx0 : sL.gpr .rdx = idx 1)
    (hW0 : Win M scr sE 16 sL) :
    WP isa (.loop (.seq (iter 16) (.block step)) .ne) sL fun s =>
      Vars 0 s (VG.Spec.Sha512.rounds H M 80) ∧ (∀ r ∈ pubRegs, r ≠ .rdx → s.gpr r = sE.gpr r) ∧
      Win M scr sE 80 s := by
  let Inv : Nat → State → Prop := fun m s => ∃ j, m = 5 - j ∧ 1 ≤ j ∧ j < 5 ∧
    Vars 0 s (VG.Spec.Sha512.rounds H M (16 * j)) ∧ (∀ r ∈ pubRegs, r ≠ .rdx → s.gpr r = sE.gpr r) ∧
    s.gpr .rdx = idx j ∧ Win M scr sE (16 * j) s
  have hstep : ∀ m s, Inv m s → WP isa (.seq (iter 16) (.block step)) s (fun s' =>
      (eval .ne s' = some false ∧ Vars 0 s' (VG.Spec.Sha512.rounds H M 80) ∧
        (∀ r ∈ pubRegs, r ≠ .rdx → s'.gpr r = sE.gpr r) ∧ Win M scr sE 80 s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨j, rfl, hj, hj', hv, hpub, hrdx, hW⟩
    refine WP.seq (WP.mono (iter_ok H M scr sE s hj hj' hrcx hrsi hout hin hv hpub hrdx hW 16 (Nat.le_refl _))
      fun s₁ ⟨hv₁, hpub₁, hrdx₁, hW₁⟩ => ?_)
    refine VG.X86_64.WP.mono_syms (step_ok s₁) fun s₂ ⟨he, hrdx₂, hg, hm, hrd, hwr⟩ hsy => ?_
    have hv₂ : Vars 0 s₂ (VG.Spec.Sha512.rounds H M (16 * (j + 1))) := by
      rw [show 16 * (j + 1) = 16 * j + 16 by omega]
      have := vars16.mp hv₁
      simp only [Vars] at this ⊢
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := this
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hg _ (by decide)]; assumption
    have hpub₂ : ∀ r ∈ pubRegs, r ≠ .rdx → s₂.gpr r = sE.gpr r := fun r hr hr' =>
      (hg r hr').trans (hpub₁ r hr hr')
    have hW₂ : Win M scr sE (16 * (j + 1)) s₂ := by
      rw [show 16 * (j + 1) = 16 * j + 16 by omega]; exact hW₁.of_eq hm hrd hwr hsy
    rw [hrdx₁, step_idx hj'] at he
    by_cases hlast : j + 1 = 5
    · left
      have hb : (j + 1 == 5) = true := beq_iff_eq.mpr hlast
      refine ⟨by rw [he, hb]; rfl, ?_, hpub₂, ?_⟩
      · rw [show 80 = 16 * (j + 1) by omega]; exact hv₂
      · rw [show 80 = 16 * (j + 1) by omega]; exact hW₂
    · right
      have hb : (j + 1 == 5) = false := beq_eq_false_iff_ne.mpr hlast
      refine ⟨by rw [he, hb]; rfl, 5 - (j + 1), by omega, j + 1, rfl, by omega, by omega, hv₂, hpub₂,
        by rw [hrdx₂, hrdx₁, idx_succ], hW₂⟩
  exact WP.loop (M := isa) Inv hstep 4 sL ⟨1, rfl, Nat.le_refl _, by decide, h0, hpub0, hrdx0, hW0⟩

/-! ## One block -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rcx : s.gpr .rcx = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrW s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i
  saved : Saved s₀ s.mem
  syms : s.syms = s₀.syms

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

theorem saved_frame {s₀ : State} (hp : Avx2.Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [winRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m' ∨ Frame [spR (scr s₀)] m m') :
    Saved s₀ m' := by
  rcases hf with hf | hf | hf <;> refine Spill.Saved.frame h hf fun p hp' r hr => ?_ <;>
    rw [List.mem_singleton.mp hr] <;> have := saved_bound p hp'
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by omega))
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- The hash value, through a frame of the window or of the spill slots. -/
theorem state_frame {s₀ : State} (hp : Avx2.Pre s₀) {m m' : Mem}
    (hf : Frame [winRegion (scr s₀)] m m' ∨ Frame [spR (scr s₀)] m m') :
    stateAt m' (st s₀) = stateAt m (st s₀) := by
  apply stateAt_eq
  intro k hk
  rcases hf with hf | hf
  · rw [hf.readW (contains_offset' (off := 8 * k) (len := 64) (by omega) (by omega))
      (by simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)) (by decide), ← stateAt_get _ _ hk]
  · rw [hf.readW (contains_offset' (off := 8 * k) (len := 64) (by omega) (by omega))
      (by simpa using Region.Disjoint.sub_right hp.st_scr (sp_sub _)) (by decide), ← stateAt_get _ _ hk]

theorem sub_scrW (s₀ : State) {r : Region} (h : Region.Sub r ⟨scr s₀, 1328⟩) :
    ∀ r' ∈ [r], ∃ r'' ∈ [stR s₀, scrW s₀], Region.Sub r' r'' :=
  fun r' hr => ⟨scrW s₀, by simp, by simp at hr; subst hr; exact h⟩

theorem body_ok {s₀ : State} (hp : Avx2.Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa Rolled.body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have hscr : (⟨scr s₀, 1328⟩ : Region) ∈ s₀.wr := by simp [hp.wr]
  -- load and enter
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine VG.X86_64.WP.mono_syms (load_ok_of hL.rdi (by rw [hL.rd, hL.wr]; exact fun k hk => hp.in_state hk))
    fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ hsy₁ => ?_
  have hrcx₁ : s₁.gpr .rcx = scr s₀ := (hpub₁ .rcx (by decide)).trans hL.rcx
  have hwr₁' : s₁.wr = s₀.wr := hwr₁.trans hL.wr
  have hrd₁' : s₁.rd = s₀.rd := hrd₁.trans hL.rd
  obtain ⟨spa, spb⟩ := sp_in hp hrcx₁ hwr₁'
  refine VG.X86_64.WP.mono_syms (enter_ok s₁ spa spb)
    fun sE ⟨hrsiE, hrdxE, hgE, hmE, hrdE, hwrE⟩ hsyE => ?_
  have hrcxE : sE.gpr .rcx = scr s₀ := by rw [hgE _ (by decide) (by decide)]; exact hrcx₁
  have hrdxE' : sE.gpr .rdx = blkAddr s₀ i := by rw [hrdxE, hpub₁ .rsi (by decide), hL.rsi]
  have hrsiE' : sE.gpr .rsi = sE.syms kSym := by rw [hrsiE, hsyE]
  have hspE : Frame [spR (scr s₀)] s₁.mem sE.mem := by rw [hmE, hrcx₁]; exact spill_frame _ _ _ _
  have hvE : Vars 0 sE (stateAt s.mem (st s₀)) := by
    have e : ∀ k, sE.gpr (var 0 k) = s₁.gpr (var 0 k) := fun k =>
      hgE _ (fun h => (by decide : ∀ r ∈ work, r ≠ .rsi) _ (var_mem 0 k) h)
        (fun h => (by decide : ∀ r ∈ work, r ≠ .rdx) _ (var_mem 0 k) h)
    simp only [Vars, e] at hv₁ ⊢
    exact hv₁
  have hblkR : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] sE.mem m → ∀ t : Nat, t < 16 →
      bswap64 (m.readW (blkAddr s₀ i + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (Pre.blk_contains hp hi ht) hblkR (by decide),
      hspE.readW (Pre.blk_contains hp hi ht) (by simpa using Region.Disjoint.sub_right hp.blk_scr (sp_sub _))
        (by decide), hm₁,
      hL.frame.readW (Pre.blk_contains hp hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  -- the first sixteen rounds
  refine WP.seq (WP.mono (first_ok _ (blk s₀ i) _ (scr s₀) sE hrdxE' hrcxE hrsiE'
    (by rw [hwrE, hwr₁']; exact Pre.out_slot hp)
    (fun t ht => by rw [hrdE, hwrE, hrd₁', hwr₁']; exact Pre.in_blk hp hi ht) hblk hvE 16 (Nat.le_refl _))
    fun sF ⟨hvF, hpubF, hWF⟩ => ?_)
  -- the loop
  refine WP.seq (VG.X86_64.WP.mono_syms (Q := fun sL => Vars 0 sL
      (VG.Spec.Sha512.rounds (stateAt s.mem (st s₀)) (blk s₀ i) 16) ∧
      (∀ r ∈ pubRegs, r ≠ .rdx → sL.gpr r = sE.gpr r) ∧ sL.gpr .rdx = idx 1 ∧
      Win (blk s₀ i) (scr s₀) sE 16 sL) ?_ fun sL ⟨hvL, hpubL, hrdxL, hWL⟩ _ => ?_)
  · refine VG.X86_64.WP.mono_syms (toLoop_ok sF) fun sL ⟨hrdxL, hgL, hmL, hrdL, hwrL⟩ hsyL => ?_
    refine ⟨?_, fun r hr hr' => (hgL r hr').trans (hpubF r hr), hrdxL, hWF.of_eq hmL hrdL hwrL hsyL⟩
    have := vars16.mp hvF
    simp only [Vars] at this ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [hgL _ (by decide)]; assumption
  refine WP.seq (WP.mono (loop_ok _ (blk s₀ i) (scr s₀) sE sL hrcxE hrsiE'
    (by rw [hwrE, hwr₁']; exact Pre.out_slot hp)
    (by rw [hrdE, hwrE, hrd₁', hwr₁']; exact Pre.in_slot hp) hvL hpubL hrdxL hWL)
    fun s₃ ⟨hv₃, hpub₃, hW₃⟩ => ?_)
  -- leave, update and advance
  rw [List.append_assoc, WP.block_append_iff]
  have hrcx₃ : s₃.gpr .rcx = scr s₀ := (hpub₃ .rcx (by decide) (by decide)).trans hrcxE
  have hwr₃ : s₃.wr = s₀.wr := by rw [hW₃.wr, hwrE, hwr₁']
  have hrd₃ : s₃.rd = s₀.rd := by rw [hW₃.rd, hrdE, hrd₁']
  obtain ⟨spa', spb'⟩ := sp_in' hp hrcx₃ hwr₃
  refine VG.X86_64.WP.mono_syms (leave_ok s₃ spa' spb')
    fun s₄ ⟨hrsi₄, hrdx₄, hg₄, hm₄, hrd₄, hwr₄⟩ hsy₄ => ?_
  have sk := spill_keep (p := scr s₀) hW₃.frame
  have sr := spill_read (scr s₀) s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx)
  rw [← hrcx₁, ← hmE] at sr
  rw [hrcx₃, sk.1, ← hrcx₁, sr.1, hpub₁ .rsi (by decide)] at hrsi₄
  rw [hrcx₃, sk.2, ← hrcx₁, sr.2, hpub₁ .rdx (by decide)] at hrdx₄
  have hrdi₄ : s₄.gpr .rdi = st s₀ := by
    rw [hg₄ _ (by decide) (by decide), hpub₃ .rdi (by decide) (by decide), hgE _ (by decide) (by decide),
      hpub₁ .rdi (by decide), hL.rdi]
  have hst₄ : stateAt s₄.mem (st s₀) = stateAt s.mem (st s₀) := by
    rw [hm₄, state_frame hp (.inl hW₃.frame), state_frame hp (.inr hspE), hm₁]
  have hv₄ : Vars 0 s₄ (VG.Spec.Sha512.rounds (stateAt s.mem (st s₀)) (blk s₀ i) 80) := by
    simp only [Vars] at hv₃ ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv₃
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [hg₄ _ (by decide) (by decide)]; assumption
  refine VG.X86_64.WP.mono_syms (update_ok_of _ (stateAt s.mem (st s₀)) hv₄ hrdi₄
    (by rw [hrd₄, hwr₄, hrd₃, hwr₃]; exact fun k hk => hp.in_state hk)
    (by rw [hwr₄, hwr₃]; exact fun k hk => hp.out_state hk)
    fun k hk => by rw [← hst₄, stateAt_get _ _ hk]) fun s₅ h₅ hsy₅ => ?_
  obtain ⟨hm₅, hrsi₅, hrdx₅, hzf₅, hrdi₅, hrcx₅, hrsp₅, hrd₅, hwr₅⟩ := h₅
  have hrdx : s₄.gpr .rdx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hrdx₄, hL.rdx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrW s₀] s₀.mem s₅.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hspE.sub (sub_scrW s₀ (sp_sub _))) ?_
    refine Frame.trans (hW₃.frame.sub (sub_scrW s₀ (win_sub _))) ?_
    rw [hm₅, hm₄]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hrsp₄ : s₄.gpr .rsp = s₀.gpr .rsp := by
    rw [hg₄ _ (by decide) (by decide), hpub₃ .rsp (by decide) (by decide), hgE _ (by decide) (by decide),
      hpub₁ .rsp (by decide), hL.rsp]
  have hcommon : Common s₀ (i + 1) s₅ := by
    refine ⟨by rw [hrdi₅, hrdi₄], by rw [hrcx₅, hg₄ _ (by decide) (by decide)]; exact hrcx₃,
      by rw [hrsp₅, hrsp₄], by rw [hrd₅, hrd₄, hrd₃], by rw [hwr₅, hwr₄, hwr₃], hframe, ?_, ?_, ?_⟩
    · rw [hm₅, stateAt_writeState, compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₅]
      refine saved_frame hp ?_ (.inr (.inl (frame_writeState (Frame.refl _ _) _)))
      rw [hm₄]
      refine saved_frame hp ?_ (.inl hW₃.frame)
      refine saved_frame hp ?_ (.inr (.inr hspE))
      rw [hm₁]; exact hL.saved
    · rw [hsy₅, hsy₄, hW₃.syms, hsyE, hsy₁]; exact hL.syms
  have hev : eval .ne s₅ = some (!(s₄.gpr .rdx - 1 == 0)) := by
    simp [eval, hzf₅]
  rw [hrdx] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon with rsi := ?_, rdx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      simpa using h0
    · rw [hrsi₅, hrsi₄, hL.rsi]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (128 : BitVec _) = BitVec.ofNat _ 128 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hrdx₅, hrdx]

/-! ## Prologue and epilogue -/

theorem save_ok {s₀ : State} (hp : Avx2.Pre s₀) :
    WP isa (.block (save ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) := by
  rw [WP.block_append_iff]
  refine WP.mono (Spill.save_ok .rcx saved s₀ fun p hp' => ?_) fun s₁ ⟨hg, hrd, hwr, hm⟩ => ?_
  · have := saved_bound p hp'
    exact ⟨scrW s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
      State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨hg, hrd, hwr, hm, by rw [hg]⟩

theorem saveMem_frame {s₀ : State} : Frame [scrW s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := saved_bound p hp; omega) (by decide)

theorem common_zero {s₀ : State} (hp : Avx2.Pre s₀) {s₁ : State} (hg : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) (hsy : s₁.syms = s₀.syms) :
    Common s₀ 0 s₁ := by
  refine ⟨by rw [hg], by rw [hg], by rw [hg], hrd, hwr, ?_, ?_,
    by rw [hm]; exact Spill.saveMem_saved _ _ _ _ (by decide), hsy⟩
  · rw [hm]; exact saveMem_frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq
    intro k hk
    rw [saveMem_frame.readW (contains_offset' (off := 8 * k) (len := 64) (by omega) (by omega))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get _ _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : Avx2.Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha512.compressWideX86_64.post s₀ s' := by
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
  refine WP.mono (Spill.restore_ok .rcx saved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [hc.rcx]; exact hc.saved)) fun s' ⟨h₁, h₂, hm, _⟩ => ?_
  · have := saved_bound p hp'
    rw [hc.rcx, hc.rd, hc.wr]
    exact ⟨scrW s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  · exact ⟨⟨Spill.calleeSaved_ok h₁ h₂ (by decide) hc.rsp, by rw [hm]; exact hret⟩,
      by show stateAt _ _ = _; rw [hm]; exact hc.state⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Avx2.Pre s₀) :
    WP isa Rolled.compress s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha512.compressWideX86_64.post s₀ s' := by
  refine WP.seq (VG.X86_64.WP.mono_syms (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hzf⟩ hsy => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  have hc₀ := common_zero hp hg hrd hwr hm hsy
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa Rolled.body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        rsi := by rw [hg]; simp [blkAddr]
        rdx := by rw [hg]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

end VG.Proof.Sha512.X86_64.Rolled
