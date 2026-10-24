module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# `vg_rsa_private_checked` on PPC64LE: up to the call of `vg_rsa_private_crt`

From the state after the frame's push: the saves, the values kept in
`r24`–`r29`, the call's arguments, and its ten stack arguments copied from
ours (`setup_ok`, into `AtCrt`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.PPC64LE.RegUpd (gpr_write_self gpr_write_of_ne mem_write)

theorem exec_addSp0 {s : State} {d : Reg} : exec (.addSp d 0) s = some (s.write d s.sp) := by
  simp [exec]

/-- In the frame, from the entry state `s`: our caller's registers and
return address in their slots, the other callee-saved registers as on entry,
memory changed only in the stack the function uses. -/
structure Fr (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = fr s :: s.wr
  lr : t.lr = s.lr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  mem : Frame [kR s] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  ls : t.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

/-- At the call of `vg_rsa_private_crt`. -/
structure AtCrt (s t : State) : Prop extends Fr s t where
  r3 : t.gpr .r3 = fb s + BitVec.ofNat 64 oM
  r4 : t.gpr .r4 = s.gpr .r6
  r5 : t.gpr .r5 = s.gpr .r5
  r6 : t.gpr .r6 = s.gpr .r6
  r7 : t.gpr .r7 = s.gpr .r9
  r8 : t.gpr .r8 = s.gpr .r6
  r9 : t.gpr .r9 = stackArg s 0
  r10 : t.gpr .r10 = stackArg s 1
  r12 : t.gpr .r12 = fb s
  r24 : t.gpr .r24 = s.gpr .r3
  r25 : t.gpr .r25 = s.gpr .r5
  r26 : t.gpr .r26 = s.gpr .r6
  r27 : t.gpr .r27 = s.gpr .r7
  r28 : t.gpr .r28 = s.gpr .r8
  r29 : t.gpr .r29 = s.gpr .r9
  psa : ∀ i < 10, t.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (2 + i)

/-- The frame's push stores the back chain at its base. -/
theorem fb_contains (s : State) : (kR s).Contains (fb s) 8 := by
  have := frame_contains s (d := 0) (n := 8) (by decide)
  rwa [BitVec.add_zero] at this

/-- The saves, from the state after the frame's push: `r12` holds the frame's
base, `r24`–`r29` and the return address are in their slots, and memory is
changed only in the frame. -/
theorem save_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, Fr s v → v.gpr .r12 = fb s → (∀ r, r ≠ .r12 → r ≠ .r0 → v.gpr r = s.gpr r) →
      WP isa (.block rest) v Q) :
    WP isa (.block (([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
      ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) ++ rest)) (allocated frameBytes s) Q := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_addSp0, ?_⟩
  generalize hu : (allocated frameBytes s).write .r12 (allocated frameBytes s).sp = u
  have u12 : u.gpr .r12 = fb s := by rw [← hu, gpr_write_self]; rfl
  have uwr : u.wr = fr s :: s.wr := by rw [← hu]; rfl
  refine Spill.save_ok (b := .r12) (l := saved) (by decide) saved_ho (fun p hp => ?_) ?_
  · have := saved_offs p hp
    rw [uwr, u12]; exact in_fr s _ (by unfold oSave at this; omega) (by unfold oSave frameBytes at *; omega)
  generalize hu₂ : ({ u with mem := Spill.saveMem u.mem (u.gpr .r12) u.gpr saved } : State) = u₂
  have g₂ : u₂.gpr = u.gpr := by rw [← hu₂]
  have m₂ : u₂.mem = Spill.saveMem u.mem (fb s) u.gpr saved := by rw [← hu₂, u12]
  have hin : InRegions u₂.wr (u₂.gpr .r12 + BitVec.ofNat 64 oLr) 8 := by
    have : u₂.wr = fr s :: s.wr := by rw [← hu₂]; exact uwr
    rw [this, g₂, u12]; exact in_fr s _ (by decide) (by decide)
  refine WP.block_cons_iff.mpr ⟨_, exec_mflr, WP.block_cons_iff.mpr ⟨_, exec_store_d (t := .r0) (n := .r12)
    (off := oLr) (by decide) ⟨by decide, by decide⟩
    (by rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide)]; exact hin), ?_⟩⟩
  have hum : u.mem = s.mem.write (fb s) 8 s.sp := by rw [← hu]; rfl
  have fr₂ : Frame [kR s] s.mem u₂.mem := by
    rw [m₂]
    have f1 : Frame [kR s] s.mem u.mem := by
      rw [hum]; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (fb_contains s)
    exact f1.trans (Spill.saveMem_frame_base (fun p hp => by
      have := saved_offs p hp; unfold oSave frameBytes at *; omega) (by decide) _ _ _)
  have sv₂ : Spill.Saved (fb s) s.gpr saved u₂.mem := by
    rw [m₂]
    refine fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans ?_
    have h12 : p.1 ≠ .r12 := by revert p; decide
    rw [← hu, gpr_write_of_ne _ _ h12]; rfl
  have hd : ∀ p ∈ saved, ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 oLr, 8⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 p.2, 8⟩ r := fun p hp r hr => by
    have := saved_offs p hp
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by unfold oSave oLr at *; omega)) (by unfold oSave at *; omega) (by decide)
  have e12 : (u₂.write .r0 u₂.lr).gpr .r12 = fb s := by rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide), g₂, u12]
  rw [e12]
  refine k _ ⟨?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩ ?_ fun r h12 h0 => ?_
  · show u₂.sp = fb s; rw [← hu₂, ← hu]; rfl
  · show u₂.rd = s.rd; rw [← hu₂, ← hu]; rfl
  · show u₂.wr = fr s :: s.wr; rw [← hu₂]; exact uwr
  · show u₂.lr = s.lr; rw [← hu₂, ← hu]; rfl
  · show (u₂.write .r0 u₂.lr).gpr r = s.gpr r
    have h0 : r ≠ .r0 := by revert r; decide
    have h12 : r ≠ .r12 := by revert r; decide
    rw [gpr_write_of_ne _ _ h0, g₂, ← hu, gpr_write_of_ne _ _ h12]; rfl
  · show Frame [kR s] s.mem ((u₂.write .r0 u₂.lr).mem.writeW (fb s + BitVec.ofNat 64 oLr) _)
    rw [mem_write]
    exact fr₂.writeW (List.mem_singleton_self _) _ (frame_contains s (by decide))
  · show Spill.Saved (fb s) s.gpr saved ((u₂.write .r0 u₂.lr).mem.writeW (fb s + BitVec.ofNat 64 oLr) _)
    rw [mem_write]
    exact sv₂.frame (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)) hd
  · show ((u₂.write .r0 u₂.lr).mem.writeW (fb s + BitVec.ofNat 64 oLr) _).readW _ 64 = s.lr
    rw [Mem.readW_writeW_self64, gpr_write_self]; show u₂.lr = s.lr; rw [← hu₂, ← hu]; rfl
  · show (u₂.write .r0 u₂.lr).gpr .r12 = fb s; exact e12
  · show (u₂.write .r0 u₂.lr).gpr r = s.gpr r
    rw [gpr_write_of_ne _ _ h0, g₂, ← hu, gpr_write_of_ne _ _ h12]; rfl

/-- Our stack argument `j` is in the arguments' region, apart from the frame. -/
theorem arg_read {s : State} (h : PreP s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat} (hj : j < 12) :
    m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  exact hm.readW (in_aR hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ka.symm) (by decide)

theorem arg_in {s t : State} (h : PreP s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 12) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 (arg j)) 8 := by
  rw [← stackArgAddr_fb, hrd, h.hrd]
  exact ⟨_, List.mem_append_left _ (by simp), in_aR hj⟩

/-- The values kept in `r24`–`r29` and `vg_rsa_private_crt`'s arguments in
registers. -/
theorem head_ok {s v : State} (h : PreP s) (F : Fr s v) (h12 : v.gpr .r12 = fb s)
    (hg : ∀ r, r ≠ .r12 → r ≠ .r0 → v.gpr r = s.gpr r) :
    WP isa (.block ([.logic .or .r24 .r3 .r3, .logic .or .r25 .r5 .r5, .logic .or .r26 .r6 .r6,
      .logic .or .r27 .r7 .r7, .logic .or .r28 .r8 .r8, .logic .or .r29 .r9 .r9] ++
      ([.addi .r3 .r12 oM, .logic .or .r4 .r26 .r26, .logic .or .r7 .r29 .r29, .logic .or .r8 .r26 .r26,
        .load .d .r9 .r12 (arg 0), .load .d .r10 .r12 (arg 1)] : List Instr))) v fun w =>
      (w.gpr .r3 = fb s + BitVec.ofNat 64 oM ∧ w.gpr .r4 = s.gpr .r6 ∧ w.gpr .r7 = s.gpr .r9 ∧
        w.gpr .r8 = s.gpr .r6 ∧ w.gpr .r9 = stackArg s 0 ∧ w.gpr .r10 = stackArg s 1 ∧
        w.gpr .r24 = s.gpr .r3 ∧ w.gpr .r25 = s.gpr .r5 ∧ w.gpr .r26 = s.gpr .r6 ∧ w.gpr .r27 = s.gpr .r7 ∧
        w.gpr .r28 = s.gpr .r8 ∧ w.gpr .r29 = s.gpr .r9 ∧ w.mem = v.mem) ∧
      Keep [.r24, .r25, .r26, .r27, .r28, .r29, .r3, .r4, .r7, .r8, .r9, .r10] v w := by
  have a0 := arg_read h F.mem (j := 0) (by decide)
  have a1 := arg_read h F.mem (j := 1) (by decide)
  have i0 := arg_in h F.rd (j := 0) (by decide)
  have i1 := arg_in h F.rd (j := 1) (by decide)
  have c0 : arg 0 < 2 ^ 15 := by decide
  have c1 : arg 1 < 2 ^ 15 := by decide
  have d0 : arg 0 % 4 = 0 := by decide
  have d1 : arg 1 % 4 = 0 := by decide
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  prun [c0, c1, d0, d1, i0, i1, a0, a1, h12, hg .r3 (by decide) (by decide), hg .r5 (by decide) (by decide),
    hg .r6 (by decide) (by decide), hg .r7 (by decide) (by decide), hg .r8 (by decide) (by decide),
    hg .r9 (by decide) (by decide), BitVec.or_self,
    exec_addi (show Reg.r12 ≠ .r0 by decide) (show oM < 2 ^ 15 by decide)]

/-- The Parameter Save Area of the calls. -/
abbrev psaR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 80⟩

/-- After copying the first `n` stack arguments, from `w`. -/
structure CI (s w : State) (n : Nat) (t : State) : Prop where
  keep : Keep [.r0] w t
  mem : Frame [psaR s] w.mem t.mem
  psa : ∀ i < n, t.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (2 + i)

theorem copy_step {s w : State} (h : PreP s) (hw12 : w.gpr .r12 = fb s) (hrd : w.rd = s.rd)
    (hwr : w.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem w.mem) {n : Nat} (hn : n < 10) {t : State}
    (hc : CI s w n t) : WP isa (.block (argCopy n)) t (CI s w (n + 1)) := by
  have t12 : t.gpr .r12 = fb s := (hc.keep.gpr _ (by decide)).trans hw12
  have psa_sub : Region.Sub (psaR s) (kR s) := frame_sub s (by decide)
  have hmt : Frame [kR s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub⟩)
  have hin : InRegions (t.rd ++ t.wr) (t.gpr .r12 + BitVec.ofNat 64 (arg (2 + n))) 8 := by
    rw [t12]; exact arg_in h (hc.keep.rd.trans hrd) (by omega)
  have hv : t.mem.readW (t.gpr .r12 + BitVec.ofNat 64 (arg (2 + n))) 64 = stackArg s (2 + n) := by
    rw [t12]; exact arg_read h hmt (by omega)
  have ho : InRegions t.wr (t.gpr .r12 + BitVec.ofNat 64 (96 + 8 * n)) 8 := by
    rw [t12, hc.keep.wr, hwr]; exact in_fr s _ (by omega) (by unfold frameBytes; omega)
  have harg : arg (2 + n) < 2 ^ 15 ∧ arg (2 + n) % 4 = 0 := by unfold arg frameBytes; omega
  apply WP.of_runBlock
  simp only [argCopy, runBlock_cons, runStep_some, exec_load_d (show Reg.r12 ≠ .r0 by decide) harg hin]
  rw [exec_store_d (show Reg.r12 ≠ .r0 by decide) ⟨by omega, by omega⟩
    (by rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide)]; exact ho)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide), gpr_write_self, mem_write, hv, t12]
  refine ⟨⟨fun r hr => ?_, hc.keep.rd, hc.keep.wr, hc.keep.sp, hc.keep.lr⟩, ?_, fun i hi => ?_⟩
  · show (t.write .r0 _).gpr r = w.gpr r
    rw [gpr_write_of_ne _ _ (by simpa using hr)]; exact hc.keep.gpr r hr
  · exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by decide))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact hc.psa i hi
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {s w : State} (h : PreP s) (hw12 : w.gpr .r12 = fb s) (hrd : w.rd = s.rd)
    (hwr : w.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem w.mem) :
    WP isa (.block ((List.range 10).flatMap argCopy)) w (CI s w 10) :=
  wp_range_flatMap (M := isa) (CI s w) (fun _ _ hn hc => copy_step h hw12 hrd hwr hm hn hc) 10 (Nat.le_refl _) w
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem setup_ok {s : State} (h : PreP s) :
    WP isa (.block (save ++ crtArgs)) (allocated frameBytes s) (AtCrt s) := by
  have e : save ++ crtArgs = ([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
      ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) ++
      ((([.logic .or .r24 .r3 .r3, .logic .or .r25 .r5 .r5, .logic .or .r26 .r6 .r6, .logic .or .r27 .r7 .r7,
        .logic .or .r28 .r8 .r8, .logic .or .r29 .r9 .r9] : List Instr) ++
      ([.addi .r3 .r12 oM, .logic .or .r4 .r26 .r26, .logic .or .r7 .r29 .r29, .logic .or .r8 .r26 .r26,
        .load .d .r9 .r12 (arg 0), .load .d .r10 .r12 (arg 1)] : List Instr)) ++
      (List.range 10).flatMap argCopy) := by
    rw [save_eq, crtArgs]; simp only [List.append_assoc]; rfl
  rw [e]
  refine save_ok fun v F h12 hg => ?_
  rw [WP.block_append_iff]
  refine WP.mono (head_ok h F h12 hg) fun w ⟨⟨w3, w4, w7, w8, w9, w10, w24, w25, w26, w27, w28, w29, wm⟩, kw⟩ => ?_
  have w12 : w.gpr .r12 = fb s := (kw.gpr _ (by decide)).trans h12
  refine WP.mono (copies_ok h w12 (kw.rd.trans F.rd) (kw.wr.trans F.wr) (by rw [wm]; exact F.mem))
    fun t hc => ?_
  have k := hc.keep
  have psa_sub : Region.Sub (psaR s) (kR s) := frame_sub s (by decide)
  have hd : ∀ {d n : Nat}, 96 + 80 ≤ d → d + n ≤ frameBytes →
      ∀ r ∈ [psaR s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r :=
    fun hdn hdn' r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr hdn) (by unfold frameBytes at hdn'; omega) (by decide)
  refine ⟨⟨k.sp.trans (kw.sp.trans F.sp), k.rd.trans (kw.rd.trans F.rd), k.wr.trans (kw.wr.trans F.wr),
    k.lr.trans (kw.lr.trans F.lr), fun r hr => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hc.psa⟩
  · rw [k.gpr _ (by revert r; decide), kw.gpr _ (by revert r; decide)]; exact F.hi r hr
  · have hm : Frame [kR s] w.mem t.mem := hc.mem.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub⟩
    rw [wm] at hm
    exact F.mem.trans hm
  · have hm : Frame [psaR s] v.mem t.mem := by rw [← wm]; exact hc.mem
    exact F.sv.frame hm fun p hp => by
      have := saved_offs p hp; exact hd (by unfold oSave at this; omega) (by unfold oSave frameBytes at *; omega)
  · rw [hc.mem.readW (Region.contains_self _ _) (hd (by decide) (by decide)) (by decide), wm]; exact F.ls
  · rw [k.gpr _ (by decide)]; exact w3
  · rw [k.gpr _ (by decide)]; exact w4
  · rw [k.gpr _ (by decide), kw.gpr _ (by decide)]; exact hg _ (by decide) (by decide)
  · rw [k.gpr _ (by decide), kw.gpr _ (by decide)]; exact hg _ (by decide) (by decide)
  · rw [k.gpr _ (by decide)]; exact w7
  · rw [k.gpr _ (by decide)]; exact w8
  · rw [k.gpr _ (by decide)]; exact w9
  · rw [k.gpr _ (by decide)]; exact w10
  · exact (k.gpr _ (by decide)).trans w12
  · rw [k.gpr _ (by decide)]; exact w24
  · rw [k.gpr _ (by decide)]; exact w25
  · rw [k.gpr _ (by decide)]; exact w26
  · rw [k.gpr _ (by decide)]; exact w27
  · rw [k.gpr _ (by decide)]; exact w28
  · rw [k.gpr _ (by decide)]; exact w29

end VG.Proof.Rsa.PPC64LE.Priv
