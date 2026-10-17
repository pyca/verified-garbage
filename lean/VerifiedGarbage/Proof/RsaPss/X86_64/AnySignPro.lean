module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySignFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# RSASSA-PSS signing on x86-64: the prologue

From the entry state, after the frame's push, `signPrologue` saves `rbx`,
`rbp` and `r12` and the arguments to their slots, and `n0` reads the
modulus' first byte (`signPro_okA`): the working space and the frame as
`Rep` says, with nothing else written.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaPss.X86_64.AnyHash (sHd sHsel sMsel)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable {G : Spec.Mgf1.Hash}

theorem fb_toNatA {s : State} (hp : SPreA G s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold signStack Proof.Rsa.X86_64.stackBytes at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

theorem SPreA.geo {s : State} (hp : SPreA G s) : Geo (fb s) (stackArg s 14) := by
  have hF := fb_toNatA hp
  have := hp.sp2
  have hsl := hp.hsl
  have hk := hp.k1
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 14, oRsa⟩ ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ :=
    Region.sub_prefix (by unfold oRsa; omega)
  refine ⟨by omega, by unfold oRsa; omega, ((hp.dKs.sub_left (frame_sub s)).sub_right sS),
    ((hp.dKs.sub_left (ret_sub s)).sub_right sS)⟩

/-- Stack argument `j`, read from memory changed only in the frame. -/
theorem arg_readA {s : State} (hp : SPreA G s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 18) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 144⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (frame_sub s)).symm

/-- One stack argument copied to a slot. -/
theorem copy1_okA {s : State} (hp : SPreA G s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 18) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov .rax (.mem (arg j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNatA hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by omega)
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    refine ⟨⟨stackArgAddr s 0, 144⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), ?_⟩
    rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))⟩
  xrun [arg, ea_sp, hsp, hin, arg_readA hp hf hj, hsc.st (d := d) hd]

/-- The low 32 bits of a stack argument, zero-extended, copied to a slot. -/
theorem copy32_okA {s : State} (hp : SPreA G s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 18) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov32 .rax (.mem (arg j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (((stackArg s j).setWidth 32).setWidth 64) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNatA hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by omega)
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 4 := by
    refine ⟨⟨stackArgAddr s 0, 144⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), ?_⟩
    rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  have hv : u.mem.readW (off (fb s) (frameBytes + 8 + 8 * j)) 32 = (stackArg s j).setWidth 32 := by
    rw [readW32_low, arg_readA hp hf hj]
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d)
      (((stackArg s j).setWidth 32).setWidth 64)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))⟩
  xrun [arg, ea_sp, hsp, hin, hv, hsc.st (d := d) hd]

theorem frame_wA {s : State} (hp : SPreA G s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := fb_toNatA hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- The slots `signPrologue` stores to, and what. -/
def proWA (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd
    (fun k => word s.mem (fb s) (8 * k))
    41 (s.gpr .rbx)) 42 (s.gpr .rbp)) 43 (s.gpr .r12)) 16 (s.gpr .rdi)) 18 (s.gpr .rdx)) 17 (s.gpr .rcx))
    19 (s.gpr .r8)) 20 (s.gpr .r9)) 37 (stackArg s 10)) 15 (stackArg s 11)) 39 (stackArg s 12)) 40 (stackArg s 13))
    21 (stackArg s 14)) 22 (stackArg s 15)) 47 (((stackArg s 16).setWidth 32).setWidth 64))
    48 (((stackArg s 17).setWidth 32).setWidth 64)

theorem signPrologue_eqA : AnyHash.signPrologue =
    ([.store (sp sRbx) .rbx, .store (sp sRbp) .rbp, .store (sp sR12) .r12, .store (sp sOut) .rdi,
      .store (sp sN) .rdx, .store (sp sK) .rcx, .store (sp sE) .r8, .store (sp sEl) .r9] : List Instr) ++
    ([.mov .rax (.mem (arg 10)), .store (sp sDig) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 11)), .store (sp sHd) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 12)), .store (sp sSalt) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 13)), .store (sp sSaltLen) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 14)), .store (sp sScr) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 15)), .store (sp sScrLen) .rax] : List Instr) ++
    ([.mov32 .rax (.mem (arg 16)), .store (sp sHsel) .rax] : List Instr) ++
    ([.mov32 .rax (.mem (arg 17)), .store (sp sMsel) .rax] : List Instr) := rfl

/-- The prologue: the slots as `proWA` says, the working space untouched. -/
theorem signPro_okA {s : State} (hp : SPreA G s) :
    WP isa (.block AnyHash.signPrologue) (allocState frameBytes s) fun t => Keep [.rax] (allocState frameBytes s) t ∧
      Lay t (fb s) (stackArg s 14) ∧ Rep t.mem (fb s) (stackArg s 14) (fun o => s.mem (off (stackArg s 14) o)) (proWA s) ∧
      Frame [frR s] s.mem t.mem := by
  have hF := fb_toNatA hp
  have := hp.sp2
  have G' := hp.geo
  set A := allocState frameBytes s with hA
  have hsp : A.gpr .rsp = fb s := rfl
  have hfr : frR s ∈ A.wr := List.mem_cons_self ..
  have hsc : Scr A (fb s) frameBytes := Scr.of_mem hfr (by omega)
  have R0 : Rep s.mem (fb s) (stackArg s 14) (fun o => s.mem (off (stackArg s 14) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [signPrologue_eqA, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
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
    exact frame_wA hp (frame_wA hp (frame_wA hp (frame_wA hp (frame_wA hp (frame_wA hp (frame_wA hp (frame_wA hp
      (Frame.refl _ _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  refine WP.mono (copy1_okA hp sp1 (k1.2.2 ▸ hfr) k1.2.1 f1 (j := 10) (d := sDig) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  refine WP.mono (copy1_okA hp ((k2.gpr (by decide)).trans sp1) (k2.2.2 ▸ k1.2.2 ▸ hfr) (k2.2.1.trans k1.2.1) f2
    (j := 11) (d := sHd) (by decide) (by decide)) fun t3 ⟨k3, hm3, f3⟩ => ?_
  have k23 := k2.trans k3
  refine WP.mono (copy1_okA hp ((k23.gpr (by decide)).trans sp1) (k23.2.2 ▸ k1.2.2 ▸ hfr) (k23.2.1.trans k1.2.1) f3
    (j := 12) (d := sSalt) (by decide) (by decide)) fun t4 ⟨k4, hm4, f4⟩ => ?_
  have k24 := k23.trans k4
  refine WP.mono (copy1_okA hp ((k24.gpr (by decide)).trans sp1) (k24.2.2 ▸ k1.2.2 ▸ hfr) (k24.2.1.trans k1.2.1) f4
    (j := 13) (d := sSaltLen) (by decide) (by decide)) fun t5 ⟨k5, hm5, f5⟩ => ?_
  have k25 := k24.trans k5
  refine WP.mono (copy1_okA hp ((k25.gpr (by decide)).trans sp1) (k25.2.2 ▸ k1.2.2 ▸ hfr) (k25.2.1.trans k1.2.1) f5
    (j := 14) (d := sScr) (by decide) (by decide)) fun t6 ⟨k6, hm6, f6⟩ => ?_
  have k26 := k25.trans k6
  refine WP.mono (copy1_okA hp ((k26.gpr (by decide)).trans sp1) (k26.2.2 ▸ k1.2.2 ▸ hfr) (k26.2.1.trans k1.2.1) f6
    (j := 15) (d := sScrLen) (by decide) (by decide)) fun t7 ⟨k7, hm7, f7⟩ => ?_
  have k27 := k26.trans k7
  refine WP.mono (copy32_okA hp ((k27.gpr (by decide)).trans sp1) (k27.2.2 ▸ k1.2.2 ▸ hfr) (k27.2.1.trans k1.2.1) f7
    (j := 16) (d := sHsel) (by decide) (by decide)) fun t8 ⟨k8, hm8, f8⟩ => ?_
  have k28 := k27.trans k8
  refine WP.mono (copy32_okA hp ((k28.gpr (by decide)).trans sp1) (k28.2.2 ▸ k1.2.2 ▸ hfr) (k28.2.1.trans k1.2.1) f8
    (j := 17) (d := sMsel) (by decide) (by decide)) fun t9 ⟨k9, hm9, f9⟩ => ?_
  have k16 : Keep [.rax] A t9 := (k1.trans (k28.trans k9)).mono (by decide)
  have R9 : Rep t9.mem (fb s) (stackArg s 14) (fun o => s.mem (off (stackArg s 14) o)) (proWA s) := by
    rw [hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]
    exact (((((((R1.wf G' (k := 37) (by decide) (stackArg s 10)).wf G' (k := 15) (by decide) (stackArg s 11)).wf G'
      (k := 39) (by decide) (stackArg s 12)).wf G' (k := 40) (by decide) (stackArg s 13)).wf G' (k := 21) (by decide)
      (stackArg s 14)).wf G' (k := 22) (by decide) (stackArg s 15)).wf G' (k := 47) (by decide)
      (((stackArg s 16).setWidth 32).setWidth 64)).wf G' (k := 48) (by decide) (((stackArg s 17).setWidth 32).setWidth 64)
  have h392 : frameBytes = 392 := rfl
  have hss : signStack = 3656 := rfl
  have := hp.sp1
  refine ⟨k16, ⟨(k16.gpr (by decide)).trans hsp, k16.2.2 ▸ hfr, by omega, by omega, ?_, ?_, G'.dFS, G'.dRS⟩, R9, f9⟩
  · have hsl := hp.hsl
    have hk := hp.k1
    refine ⟨⟨stackArg s 14, 0, (stackArg s 15).toNat * 8, by rw [k16.2.2, hA]; simp [allocState, hp.hwr], (BitVec.add_zero _).symm,
      by unfold oRsa; omega, hp.wS.trans' (by omega)⟩, G'.Sw⟩
  · rw [show sScr = 8 * 21 from rfl]
    exact (R9.fr 21 (by decide)).trans (by simp [proWA, upd])

end VG.Proof.RsaPss.X86_64.Any
