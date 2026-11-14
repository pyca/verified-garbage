module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecFrame
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: up to the private-key operation

From the state after the frame's push: our return address and the arguments
in their slots (`Slots`), the private-key operation's twelve stack arguments
copied from ours, and its arguments in registers (`setup_ok`, into
`AtPriv`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.PPC64LE.RegUpd (gpr_write_self gpr_write_of_ne mem_write)

variable {pc : Bool}

theorem exec_addSp0 {s : State} {d : Reg} : exec (.addSp d 0) s = some (s.write d s.sp) := by
  simp [exec]

/-- What the slots hold from the entry state `s`. -/
def slotVal (s : State) (r : Reg) : BitVec 64 := if r = .r0 then s.lr else s.gpr r

/-- The slots: our return address and the arguments. -/
structure Slots (s : State) (m : Mem) : Prop where
  sv : Spill.Saved (fb s) (slotVal s) savedSlots m
  dl : m.readW (fb s + BitVec.ofNat 64 oDl) 64 = stackArg s 0
  inp : m.readW (fb s + BitVec.ofNat 64 oIn) 64 = stackArg s 1
  scr : m.readW (fb s + BitVec.ofNat 64 oScr) 64 = stackArg s 13

/-- The slots' region. -/
abbrev slotR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oOut, frameBytes - oOut⟩

theorem savedSlots_offs : ∀ p ∈ savedSlots, oOut ≤ p.2 ∧ p.2 + 8 ≤ oOut + (frameBytes - oOut) := by decide

theorem Slots.frame {s : State} {m m' : Mem} (S : Slots s m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (slotR s) r) : Slots s m' := by
  have one : ∀ {d : Nat}, oOut ≤ d → d + 8 ≤ frameBytes → m'.readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left
      (Offset.sub _ h₁ (by unfold oOut frameBytes at *; omega_using [h₂]))) (by decide)
  refine ⟨S.sv.frame hf fun p hp r hr => (hd r hr).sub_left (Offset.sub _ (savedSlots_offs p hp).1
    (savedSlots_offs p hp).2), ?_, ?_, ?_⟩
  · rw [one (by decide) (by decide)]; exact S.dl
  · rw [one (by decide) (by decide)]; exact S.inp
  · rw [one (by decide) (by decide)]; exact S.scr

/-- In the frame, from the entry state `s`: the callee-saved registers as on
entry, the slots, memory changed only in the stack the function uses. -/
structure Fr (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = fr s :: s.wr
  hi : ∀ r ∈ preserved, t.gpr r = s.gpr r
  mem : Frame [kR s] s.mem t.mem
  sl : Slots s t.mem

/-- At the call of `vg_rsa_private_checked`. -/
structure AtPriv (pc : Bool) (s t : State) : Prop extends Fr s t where
  r3 : t.gpr .r3 = s.gpr .r3
  r4 : t.gpr .r4 = s.gpr .r7
  r5 : t.gpr .r5 = s.gpr .r6
  r6 : t.gpr .r6 = s.gpr .r7
  r7 : t.gpr .r7 = s.gpr .r8
  r8 : t.gpr .r8 = s.gpr .r9
  r9 : t.gpr .r9 = stackArg s 1
  r10 : t.gpr .r10 = s.gpr .r7
  psa : ∀ i < nCallArgs pc, t.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (3 + i)

/-- The frame's push stores the back chain at its base. -/
theorem fb_contains (s : State) : (kR s).Contains (fb s) 8 := by
  have := frame_contains s (d := 0) (n := 8) (by decide)
  rwa [BitVec.add_zero] at this

/-- Our stack argument `j` is in the arguments' region, apart from the stack. -/
theorem arg_readG {s : State} (h : DPre pc s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat}
    (hj : j < if pc then 17 else 15) : m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  exact hm.readW (in_aR (pc := pc) hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ka.symm) (by decide)

theorem arg_inG {s t : State} (h : DPre pc s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < if pc then 17 else 15) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 (arg j)) 8 := by
  rw [← stackArgAddr_fb, hrd, h.hrd]
  exact ⟨aR pc s, List.mem_append_left _ (by simp [rdL]), in_aR hj⟩

theorem arg_read {s : State} (h : DPre pc s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat} (hj : j < 15) :
    m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j :=
  arg_readG h hm (lt_args hj)

theorem arg_in {s t : State} (h : DPre pc s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 15) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 (arg j)) 8 :=
  arg_inG h hrd (lt_args hj)

/-- The Parameter Save Area of the call: its twelve, or with `pc` fourteen,
stack arguments. -/
abbrev psaR (pc : Bool) (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, if pc then 112 else 96⟩

theorem psa_le : (if pc then 112 else 96) ≤ 112 := by cases pc <;> decide

theorem psa_sub (s : State) : Region.Sub (psaR pc s) (kR s) := frame_sub s (by cases pc <;> decide)

theorem nCall_lt {n : Nat} (hn : n < nCallArgs pc) : n < 14 ∧ 3 + n < if pc then 17 else 15 := by
  cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] at hn ⊢ <;> omega_using [hn]

theorem fR_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (kR s) := by
  have := frame_sub s (d := 0) (n := frameBytes) (by omega_using [])
  rwa [BitVec.add_zero] at this

/-- The saves, from the state after the frame's push: `r12` holds the frame's
base, the slots of `savedSlots` hold our return address and the arguments,
and memory is changed only in the frame. -/
theorem saves_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, v.sp = fb s → v.rd = s.rd → v.wr = fr s :: s.wr → v.gpr .r12 = fb s →
      (∀ r, r ≠ .r12 → r ≠ .r0 → v.gpr r = s.gpr r) → Frame [kR s] s.mem v.mem →
      Spill.Saved (fb s) (slotVal s) savedSlots v.mem → WP isa (.block rest) v Q) :
    WP isa (.block (saves ++ rest)) (allocated frameBytes s) Q := by
  rw [show saves = [fp, .mflr .r0] ++ Spill.saveCode .r12 savedSlots from rfl, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_addSp0, WP.block_cons_iff.mpr ⟨_, exec_mflr, ?_⟩⟩
  generalize hu : ((allocated frameBytes s).write .r12 (allocated frameBytes s).sp).write .r0
    ((allocated frameBytes s).write .r12 (allocated frameBytes s).sp).lr = u
  have u12 : u.gpr .r12 = fb s := by
    rw [← hu, gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide), gpr_write_self]; rfl
  have uwr : u.wr = fr s :: s.wr := by rw [← hu]; rfl
  have ug : ∀ p ∈ savedSlots, u.gpr p.1 = slotVal s p.1 := by
    intro p hp
    simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [← hu, State.write, slotVal, allocated]
  refine Spill.save_ok (b := .r12) (l := savedSlots) (by decide) (by decide) (fun p hp => ?_) ?_
  · have := savedSlots_offs p hp
    rw [uwr, u12]; exact in_fr s _ (by unfold oOut at this; omega_using [this]) (by unfold oOut frameBytes at *; omega_using [this])
  refine k _ (by rw [← hu]; rfl) (by rw [← hu]; rfl) uwr u12 (fun r h12 h0 => ?_) ?_ ?_
  · show u.gpr r = s.gpr r
    rw [← hu, gpr_write_of_ne _ _ h0, gpr_write_of_ne _ _ h12]; rfl
  · show Frame [kR s] s.mem (Spill.saveMem u.mem (u.gpr .r12) u.gpr savedSlots)
    have hum : u.mem = s.mem.write (fb s) 8 s.sp := by rw [← hu]; rfl
    have f1 : Frame [kR s] s.mem u.mem := by
      rw [hum]; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (fb_contains s)
    rw [u12]
    exact f1.trans ((Spill.saveMem_frame_base (n := frameBytes) (fun p hp => by
      have := savedSlots_offs p hp; unfold oOut frameBytes at *; omega_using [this]) (by decide) _ _ _).sub
      fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, fR_sub s⟩)
  · show Spill.Saved (fb s) (slotVal s) savedSlots (Spill.saveMem u.mem (u.gpr .r12) u.gpr savedSlots)
    rw [u12]
    exact fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans (ug p hp)

/-- After copying the first `n` stack arguments, from `w`. -/
structure CI (pc : Bool) (s w : State) (n : Nat) (t : State) : Prop where
  keep : Keep [.r0] w t
  mem : Frame [psaR pc s] w.mem t.mem
  psa : ∀ i < n, t.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (3 + i)

theorem copy_step {s w : State} (h : DPre pc s) (hw12 : w.gpr .r12 = fb s) (hrd : w.rd = s.rd)
    (hwr : w.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem w.mem) {n : Nat} (hn : n < nCallArgs pc) {t : State}
    (hc : CI pc s w n t) : WP isa (.block (copyArg n)) t (CI pc s w (n + 1)) := by
  obtain ⟨hn14, hn'⟩ := nCall_lt hn
  have t12 : t.gpr .r12 = fb s := (hc.keep.gpr _ (by decide)).trans hw12
  have hmt : Frame [kR s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub s⟩)
  have hin : InRegions (t.rd ++ t.wr) (t.gpr .r12 + BitVec.ofNat 64 (arg (3 + n))) 8 := by
    rw [t12]; exact arg_inG h (hc.keep.rd.trans hrd) hn'
  have hv : t.mem.readW (t.gpr .r12 + BitVec.ofNat 64 (arg (3 + n))) 64 = stackArg s (3 + n) := by
    rw [t12]; exact arg_readG h hmt hn'
  have ho : InRegions t.wr (t.gpr .r12 + BitVec.ofNat 64 (96 + 8 * n)) 8 := by
    rw [t12, hc.keep.wr, hwr]; exact in_fr s _ (by omega_using []) (by unfold frameBytes; omega_using [hn14])
  have harg : arg (3 + n) < 2 ^ 15 ∧ arg (3 + n) % 4 = 0 := by unfold arg frameBytes; omega_using [hn14]
  apply WP.of_runBlock
  simp only [copyArg, mvArg, runBlock_cons, runStep_some, exec_load_d (show Reg.r12 ≠ .r0 by decide) harg hin]
  rw [exec_store_d (show Reg.r12 ≠ .r0 by decide) ⟨by omega_using [hn14], by omega_using []⟩
    (by rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide)]; exact ho)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide), gpr_write_self, mem_write, hv, t12]
  refine ⟨⟨fun r hr => ?_, hc.keep.rd, hc.keep.wr, hc.keep.sp, hc.keep.lr⟩, ?_, fun i hi => ?_⟩
  · show (t.write .r0 _).gpr r = w.gpr r
    rw [gpr_write_of_ne _ _ (by simpa using hr)]; exact hc.keep.gpr r hr
  · have := psa_le (pc := pc)
    exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using [])
      (by cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] at hn ⊢ <;> omega_arith) (by omega_using [this]))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hi])) (by omega_arith) (by omega_using [hn14])) (by decide)]
      exact hc.psa i hi
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {s w : State} (h : DPre pc s) (hw12 : w.gpr .r12 = fb s) (hrd : w.rd = s.rd)
    (hwr : w.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem w.mem) :
    WP isa (.block ((List.range (nCallArgs pc)).flatMap copyArg)) w (CI pc s w (nCallArgs pc)) :=
  wp_range_flatMap (M := isa) (CI pc s w) (fun _ _ hn hc => copy_step h hw12 hrd hwr hm hn hc) (nCallArgs pc)
    (Nat.le_refl _) w
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- A word of the frame's slots or Parameter Save Area is writable and in
the stack the function uses. -/
theorem slot_in (s : State) {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ frameBytes) :
    InRegions (fr s :: s.wr) (fb s + BitVec.ofNat 64 d) 8 := in_fr s _ h₁ h₂

theorem slotMoves_ok {s v : State} (h : DPre pc s) (h12 : v.gpr .r12 = fb s) (hrd : v.rd = s.rd)
    (hwr : v.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem v.mem) :
    WP isa (.block slotMoves) v fun w =>
      (w.mem = ((v.mem.writeW (fb s + BitVec.ofNat 64 oDl) (stackArg s 0)).writeW (fb s + BitVec.ofNat 64 oIn)
        (stackArg s 1)).writeW (fb s + BitVec.ofNat 64 oScr) (stackArg s 13)) ∧ Keep [.r0] v w := by
  have fw : ∀ {m : Mem} {d : Nat}, Frame [kR s] s.mem m → d + 8 ≤ frameBytes → ∀ x : BitVec 64,
      Frame [kR s] s.mem (m.writeW (fb s + BitVec.ofNat 64 d) x) :=
    fun hm hd x => hm.writeW (List.mem_singleton_self _) _ (frame_contains s hd)
  have a0 := arg_read h hm (j := 0) (by decide)
  have a1 := arg_read h (fw hm (d := oDl) (by decide) (stackArg s 0)) (j := 1) (by decide)
  have a13 := arg_read h (fw (fw hm (d := oDl) (by decide) (stackArg s 0)) (d := oIn) (by decide)
    (stackArg s 1)) (j := 13) (by decide)
  have i0 := arg_in h hrd (j := 0) (by decide)
  have i1 := arg_in h hrd (j := 1) (by decide)
  have i13 := arg_in h hrd (j := 13) (by decide)
  have o1 : InRegions v.wr (fb s + BitVec.ofNat 64 oDl) 8 := by rw [hwr]; exact slot_in s (by decide) (by decide)
  have o2 : InRegions v.wr (fb s + BitVec.ofNat 64 oIn) 8 := by rw [hwr]; exact slot_in s (by decide) (by decide)
  have o3 : InRegions v.wr (fb s + BitVec.ofNat 64 oScr) 8 := by rw [hwr]; exact slot_in s (by decide) (by decide)
  have c0 : arg 0 < 2 ^ 15 ∧ arg 0 % 4 = 0 := by decide
  have c1 : arg 1 < 2 ^ 15 ∧ arg 1 % 4 = 0 := by decide
  have c13 : arg 13 < 2 ^ 15 ∧ arg 13 % 4 = 0 := by decide
  have d1 : oDl < 2 ^ 15 := by decide
  have d2 : oDl % 4 = 0 := by decide
  have d3 : oIn < 2 ^ 15 := by decide
  have d4 : oIn % 4 = 0 := by decide
  have d5 : oScr < 2 ^ 15 := by decide
  have d6 : oScr % 4 = 0 := by decide
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold slotMoves mvArg
  prun [h12, c0, c1, c13, d1, d2, d3, d4, d5, d6, i0, i1, i13, o1, o2, o3, a0, a1, a13]

theorem setup_ok {s : State} (h : DPre pc s) :
    WP isa (.block (setup pc)) (allocated frameBytes s) (AtPriv pc s) := by
  rw [show setup pc = saves ++ (slotMoves ++ ((List.range (nCallArgs pc)).flatMap copyArg ++ privRegs)) by
    simp only [setup, List.append_assoc]]
  refine saves_ok fun v vsp vrd vwr v12 hg vm vsv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (slotMoves_ok h v12 vrd vwr vm) fun w ⟨wm, kw⟩ => ?_
  have w12 : w.gpr .r12 = fb s := (kw.gpr _ (by decide)).trans v12
  -- the slots after the moves
  have sep : ∀ {d e : Nat}, d + 8 ≤ e ∨ e + 8 ≤ d → e + 8 ≤ frameBytes → d + 8 ≤ frameBytes →
      Mem.Sep (fb s + BitVec.ofNat 64 d) 8 (fb s + BitVec.ofNat 64 e) 8 := fun h₁ h₂ h₃ =>
    Offset.sep _ h₁ (by unfold frameBytes at *; omega_using [h₃]) (by unfold frameBytes at *; omega_using [h₂])
  have fm : Frame [kR s] s.mem w.mem := by
    rw [wm]
    exact ((vm.writeW (List.mem_singleton_self _) _ (frame_contains s (by decide))).writeW
      (List.mem_singleton_self _) _ (frame_contains s (by decide))).writeW (List.mem_singleton_self _) _
      (frame_contains s (by decide))
  have sl : Slots s w.mem := by
    have f3 : Frame [⟨fb s + BitVec.ofNat 64 oDl, 24⟩] v.mem w.mem := by
      rw [wm]
      exact ((Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
        (Offset.contains _ (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by decide) (by decide) (by decide))
    refine ⟨vsv.frame f3 fun p hp r hr => ?_, ?_, ?_, ?_⟩
    · rw [List.mem_singleton.mp hr]
      have : p ∈ savedSlots := hp
      simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · rw [wm, Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
    · rw [wm, Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
    · rw [wm, Mem.readW_writeW_self64]
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok h w12 (kw.rd.trans vrd) (kw.wr.trans vwr) fm) fun t hc => ?_
  have t12 : t.gpr .r12 = fb s := (hc.keep.gpr _ (by decide)).trans w12
  have pl := psa_le (pc := pc)
  have tm : Frame [kR s] s.mem t.mem := fm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub s⟩)
  have tsl : Slots s t.mem := sl.frame hc.mem fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by unfold oOut; omega_using [pl])) (by unfold oOut frameBytes; omega_using []) (by omega_using [pl])
  have kt : ∀ r, r ≠ .r12 → r ≠ .r0 → t.gpr r = s.gpr r := fun r h1 h2 =>
    (hc.keep.gpr r (by simpa using h2)).trans ((kw.gpr r (by simpa using h2)).trans (hg r h1 h2))
  have i1 : t.mem.readW (fb s + BitVec.ofNat 64 oIn) 64 = stackArg s 1 := tsl.inp
  have hIn : InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 oIn) 8 := by
    rw [hc.keep.rd, hc.keep.wr, kw.rd, kw.wr, vwr]; exact in_fr' s _ _ (by decide) (by decide)
  have c1 : oIn < 2 ^ 15 := by decide
  have c2 : oIn % 4 = 0 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r4, .r5, .r6, .r7, .r8, .r9, .r10] (Q := fun u =>
    u.gpr .r4 = s.gpr .r7 ∧ u.gpr .r5 = s.gpr .r6 ∧ u.gpr .r6 = s.gpr .r7 ∧ u.gpr .r7 = s.gpr .r8 ∧
      u.gpr .r8 = s.gpr .r9 ∧ u.gpr .r9 = stackArg s 1 ∧ u.gpr .r10 = s.gpr .r7 ∧ u.mem = t.mem) ?_ rfl)
    fun u ⟨⟨u4, u5, u6, u7, u8, u9, u10, um⟩, ku⟩ => ?_
  · unfold privRegs
    prun [t12, c1, c2, hIn, i1, kt .r6 (by decide) (by decide), kt .r7 (by decide) (by decide),
      kt .r8 (by decide) (by decide), kt .r9 (by decide) (by decide), BitVec.or_self, Impl.AesGcm.PPC64LE.mov]
  have kall : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r0] → u.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ku.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      kt r hr.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2]
  refine ⟨⟨ku.sp.trans (hc.keep.sp.trans (kw.sp.trans vsp)), ku.rd.trans (hc.keep.rd.trans (kw.rd.trans vrd)),
    ku.wr.trans (hc.keep.wr.trans (kw.wr.trans vwr)), fun r hr => kall r (by revert r; decide), um ▸ tm,
    um ▸ tsl⟩, kall _ (by decide), u4, u5, u6, u7, u8, u9, u10, fun i hi => by rw [um]; exact hc.psa i hi⟩
