import VerifiedGarbage.Proof.RsaPss.X86_64.SignFrame
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# RSASSA-PSS signing on x86-64: the prologue

From the entry state, after the frame's push, `signPrologue` saves `rbx`,
`rbp` and `r12` and the arguments to their slots, and `n0` reads the
modulus' first byte (`signPro_ok`): the working space and the frame as
`Rep` says, with nothing else written.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable {G : Spec.Mgf1.Hash}

theorem fb_toNat {s : State} (hp : SPre G s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold signStack Proof.Rsa.X86_64.stackBytes at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

theorem SPre.geo {s : State} (hp : SPre G s) : Geo (fb s) (stackArg s 13) := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsl := hp.hsl
  have hk := hp.k1
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 13, oRsa⟩ ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ :=
    Region.sub_prefix (by unfold oRsa; omega)
  refine ⟨by omega, by unfold oRsa; omega, ((hp.dKs.sub_left (frame_sub s)).sub_right sS),
    ((hp.dKs.sub_left (ret_sub s)).sub_right sS)⟩

/-- The address of stack argument `j`, from the frame. -/
theorem argAddr (s : State) (j : Nat) : off (fb s) (frameBytes + 8 + 8 * j) = stackArgAddr s j := by
  simp only [off, fb, stackArgAddr]
  rw [show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

theorem allocState_gpr' (bytes : Nat) (s : State) (r : Reg) :
    (allocState bytes s).gpr r = if r = .rsp then s.gpr .rsp - BitVec.ofNat 64 bytes else s.gpr r := rfl

/-- The frame's region. -/
abbrev frR (s : State) : Region := ⟨fb s, frameBytes⟩

/-- Stack argument `j`, read from memory changed only in the frame. -/
theorem arg_read {s : State} (hp : SPre G s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 15) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 120⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (frame_sub s)).symm

/-- One stack argument copied to a slot. -/
theorem copy1_ok {s : State} (hp : SPre G s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 15) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov .rax (.mem (arg j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by omega)
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    refine ⟨⟨stackArgAddr s 0, 120⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), ?_⟩
    rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))⟩
  xrun [arg, ea_sp, hsp, hin, arg_read hp hf hj, hsc.st (d := d) hd]

theorem frame_w {s : State} (hp : SPre G s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := fb_toNat hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- The slots `signPrologue` stores to, and what. -/
def proW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (fun k => word s.mem (fb s) (8 * k))
    41 (s.gpr .rbx)) 42 (s.gpr .rbp)) 43 (s.gpr .r12)) 16 (s.gpr .rdi)) 18 (s.gpr .rdx)) 17 (s.gpr .rcx))
    19 (s.gpr .r8)) 20 (s.gpr .r9)) 37 (stackArg s 10)) 39 (stackArg s 11)) 40 (stackArg s 12)) 21 (stackArg s 13))
    22 (stackArg s 14)

theorem signPrologue_eq : signPrologue =
    ([.store (sp sRbx) .rbx, .store (sp sRbp) .rbp, .store (sp sR12) .r12, .store (sp sOut) .rdi,
      .store (sp sN) .rdx, .store (sp sK) .rcx, .store (sp sE) .r8, .store (sp sEl) .r9] : List Instr) ++
    ([.mov .rax (.mem (arg 10)), .store (sp sDig) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 11)), .store (sp sSalt) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 12)), .store (sp sSaltLen) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 13)), .store (sp sScr) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 14)), .store (sp sScrLen) .rax] : List Instr) := rfl

/-- The prologue: the slots as `proW` says, the working space untouched. -/
theorem signPro_ok {s : State} (hp : SPre G s) :
    WP isa (.block signPrologue) (allocState frameBytes s) fun t => Keep [.rax] (allocState frameBytes s) t ∧
      Lay t (fb s) (stackArg s 13) ∧ Rep t.mem (fb s) (stackArg s 13) (fun o => s.mem (off (stackArg s 13) o)) (proW s) ∧
      Frame [frR s] s.mem t.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  have G' := hp.geo
  set A := allocState frameBytes s with hA
  have hsp : A.gpr .rsp = fb s := rfl
  have hfr : frR s ∈ A.wr := List.mem_cons_self ..
  have hsc : Scr A (fb s) frameBytes := Scr.of_mem hfr (by omega)
  have R0 : Rep s.mem (fb s) (stackArg s 13) (fun o => s.mem (off (stackArg s 13) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [signPrologue_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  have R1 := ((((((((R0.wf G' (k := 41) (by decide) (s.gpr .rbx)).wf G' (k := 42) (by decide) (s.gpr .rbp)).wf G'
    (k := 43) (by decide) (s.gpr .r12)).wf G' (k := 16) (by decide) (s.gpr .rdi)).wf G' (k := 18) (by decide)
    (s.gpr .rdx)).wf G' (k := 17) (by decide) (s.gpr .rcx)).wf G' (k := 19) (by decide) (s.gpr .r8)).wf G'
    (k := 20) (by decide) (s.gpr .r9))
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = (((((((s.mem.writeW (off (fb s) (8 * 41)) (s.gpr .rbx)).writeW
      (off (fb s) (8 * 42)) (s.gpr .rbp)).writeW (off (fb s) (8 * 43)) (s.gpr .r12)).writeW (off (fb s) (8 * 16))
      (s.gpr .rdi)).writeW (off (fb s) (8 * 18)) (s.gpr .rdx)).writeW (off (fb s) (8 * 17)) (s.gpr .rcx)).writeW
      (off (fb s) (8 * 19)) (s.gpr .r8)).writeW (off (fb s) (8 * 20)) (s.gpr .r9)) ?_ rfl) fun t1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, hsp, hsc.st (d := sRbx) (by decide), hsc.st (d := sRbp) (by decide), hsc.st (d := sR12) (by decide),
      hsc.st (d := sOut) (by decide), hsc.st (d := sN) (by decide), hsc.st (d := sK) (by decide),
      hsc.st (d := sE) (by decide), hsc.st (d := sEl) (by decide), allocState_gpr']
    rfl
  have f1 : Frame [frR s] s.mem t1.mem := by
    rw [hm1]
    exact frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp
      (Frame.refl _ _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  refine WP.mono (copy1_ok hp sp1 (k1.2.2 ▸ hfr) k1.2.1 f1 (j := 10) (d := sDig) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  refine WP.mono (copy1_ok hp ((k2.gpr (by decide)).trans sp1) (k2.2.2 ▸ k1.2.2 ▸ hfr) (k2.2.1.trans k1.2.1) f2
    (j := 11) (d := sSalt) (by decide) (by decide)) fun t3 ⟨k3, hm3, f3⟩ => ?_
  have k23 := k2.trans k3
  refine WP.mono (copy1_ok hp ((k23.gpr (by decide)).trans sp1) (k23.2.2 ▸ k1.2.2 ▸ hfr) (k23.2.1.trans k1.2.1) f3
    (j := 12) (d := sSaltLen) (by decide) (by decide)) fun t4 ⟨k4, hm4, f4⟩ => ?_
  have k24 := k23.trans k4
  refine WP.mono (copy1_ok hp ((k24.gpr (by decide)).trans sp1) (k24.2.2 ▸ k1.2.2 ▸ hfr) (k24.2.1.trans k1.2.1) f4
    (j := 13) (d := sScr) (by decide) (by decide)) fun t5 ⟨k5, hm5, f5⟩ => ?_
  have k25 := k24.trans k5
  refine WP.mono (copy1_ok hp ((k25.gpr (by decide)).trans sp1) (k25.2.2 ▸ k1.2.2 ▸ hfr) (k25.2.1.trans k1.2.1) f5
    (j := 14) (d := sScrLen) (by decide) (by decide)) fun t6 ⟨k6, hm6, f6⟩ => ?_
  have k16 : Keep [.rax] A t6 := (k1.trans (k25.trans k6)).mono (by decide)
  have R6 : Rep t6.mem (fb s) (stackArg s 13) (fun o => s.mem (off (stackArg s 13) o)) (proW s) := by
    rw [hm6, hm5, hm4, hm3, hm2, hm1]
    exact ((((R1.wf G' (k := 37) (by decide) (stackArg s 10)).wf G' (k := 39) (by decide) (stackArg s 11)).wf G'
      (k := 40) (by decide) (stackArg s 12)).wf G' (k := 21) (by decide) (stackArg s 13)).wf G' (k := 22) (by decide)
      (stackArg s 14)
  have h392 : frameBytes = 392 := rfl
  have hss : signStack = 3656 := rfl
  have := hp.sp1
  refine ⟨k16, ⟨(k16.gpr (by decide)).trans hsp, k16.2.2 ▸ hfr, by omega, by omega, ?_, ?_, G'.dFS, G'.dRS⟩, R6, f6⟩
  · have hsl := hp.hsl
    have hk := hp.k1
    refine ⟨⟨stackArg s 13, 0, (stackArg s 14).toNat * 8, by rw [k16.2.2, hA]; simp [allocState, hp.hwr], (BitVec.add_zero _).symm,
      by unfold oRsa; omega, hp.wS.trans' (by omega)⟩, G'.Sw⟩
  · rw [show sScr = 8 * 21 from rfl]
    exact (R6.fr 21 (by decide)).trans (by simp [proW, upd])

end VG.Proof.RsaPss.X86_64
