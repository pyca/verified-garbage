module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: up to `encode`

From the state after the frame's push: the saves, the values kept in
`r26`–`r30` and `encode`'s arguments (`setup_ok`, into `AtEnc`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign
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

/-- At `encode`. -/
structure AtEnc (s t : State) : Prop extends Fr s t where
  r4 : t.gpr .r4 = fb s + BitVec.ofNat 64 oEM
  r5 : t.gpr .r5 = s.gpr .r6
  r6 : t.gpr .r6 = ((s.gpr .r9).setWidth 32).setWidth 64
  r7 : t.gpr .r7 = s.gpr .r10
  r8 : t.gpr .r8 = stackArg s 0
  r12 : t.gpr .r12 = fb s
  r26 : t.gpr .r26 = s.gpr .r3
  r27 : t.gpr .r27 = s.gpr .r5
  r28 : t.gpr .r28 = s.gpr .r6
  r29 : t.gpr .r29 = s.gpr .r7
  r30 : t.gpr .r30 = s.gpr .r8

/-- The frame's push stores the back chain at its base. -/
theorem fb_contains (s : State) : (kR s).Contains (fb s) 8 := by
  have := frame_contains s (d := 0) (n := 8) (by decide)
  rwa [BitVec.add_zero] at this

theorem fR_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (kR s) := by
  have := frame_sub s (d := 0) (n := frameBytes) (by omega)
  rwa [BitVec.add_zero] at this

/-- The saves, from the state after the frame's push. -/
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
    exact f1.trans ((Spill.saveMem_frame_base (n := frameBytes) (fun p hp => by
      have := saved_offs p hp; unfold oSave frameBytes at *; omega) (by decide) _ _ _).sub
      fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, fR_sub s⟩)
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

/-- Our stack argument `j` is in the arguments' region, apart from the stack. -/
theorem arg_read {s : State} (h : SPre s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat} (hj : j < 13) :
    m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  exact hm.readW (in_aR hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ka.symm) (by decide)

theorem arg_in {s t : State} (h : SPre s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 13) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 (arg j)) 8 := by
  rw [← stackArgAddr_fb, hrd, h.hrd]
  exact ⟨_, List.mem_append_left _ (by simp), in_aR hj⟩

theorem setup_ok {s : State} (h : SPre s) :
    WP isa (.block (save ++ encArgs)) (allocated frameBytes s) (AtEnc s) := by
  have e : save ++ encArgs = ([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
      ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) ++
      (([.logic .or .r26 .r3 .r3, .logic .or .r27 .r5 .r5, .logic .or .r28 .r6 .r6, .logic .or .r29 .r7 .r7,
        .logic .or .r30 .r8 .r8] : List Instr) ++ encArgs) := by
    rw [save_eq]; simp only [List.append_assoc]
  rw [e]
  refine save_ok fun v F h12 hg => ?_
  have a0 := arg_read h F.mem (j := 0) (by decide)
  have i0 := arg_in h F.rd (j := 0) (by decide)
  have c0 : arg 0 < 2 ^ 15 := by decide
  have d0 : arg 0 % 4 = 0 := by decide
  have c1 : oEM < 2 ^ 15 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r26, .r27, .r28, .r29, .r30, .r4, .r5, .r6, .r7, .r8]
    (Q := fun w => w.gpr .r4 = fb s + BitVec.ofNat 64 oEM ∧ w.gpr .r5 = s.gpr .r6 ∧ w.gpr .r6 = ((s.gpr .r9).setWidth 32).setWidth 64 ∧
      w.gpr .r7 = s.gpr .r10 ∧ w.gpr .r8 = stackArg s 0 ∧ w.gpr .r26 = s.gpr .r3 ∧ w.gpr .r27 = s.gpr .r5 ∧
      w.gpr .r28 = s.gpr .r6 ∧ w.gpr .r29 = s.gpr .r7 ∧ w.gpr .r30 = s.gpr .r8 ∧ w.mem = v.mem) ?_ rfl)
    fun w ⟨⟨w4, w5, w6, w7, w8, w26, w27, w28, w29, w30, wm⟩, kw⟩ => ?_
  · unfold encArgs
    prun [c0, d0, c1, i0, a0, h12, hg .r3 (by decide) (by decide), hg .r5 (by decide) (by decide),
      hg .r6 (by decide) (by decide), hg .r7 (by decide) (by decide), hg .r8 (by decide) (by decide),
      hg .r9 (by decide) (by decide), hg .r10 (by decide) (by decide), BitVec.or_self,
      exec_addi (show Reg.r12 ≠ .r0 by decide) c1, Impl.AesGcm.PPC64LE.mov,
      exec_lsr_w (show 0 < 32 by decide), BitVec.ushiftRight_zero]
  · refine ⟨⟨kw.sp.trans F.sp, kw.rd.trans F.rd, kw.wr.trans F.wr, kw.lr.trans F.lr,
      fun r hr => (kw.gpr _ (by revert r; decide)).trans (F.hi r hr), wm ▸ F.mem, wm ▸ F.sv, wm ▸ F.ls⟩,
      w4, w5, w6, w7, w8, (kw.gpr _ (by decide)).trans h12, w26, w27, w28, w29, w30⟩

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign
