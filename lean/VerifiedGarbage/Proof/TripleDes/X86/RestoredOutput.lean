import VerifiedGarbage.Proof.TripleDes.X86.Save
import VerifiedGarbage.Proof.TripleDes.X86.WordStore
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.X86.RoundStep

/-! ## `FinalPermutation` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

theorem fp_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 32 32 .eax .ebx .edi .esi .ecx) s = some s' ∧
      s'.gpr .eax = (Spec.TripleDes.permute Spec.TripleDes.fp
        (packedInput 64 32 (s.gpr .edi) (s.gpr .esi))).setWidth 32 ∧
      s'.gpr .ebx = ((Spec.TripleDes.permute Spec.TripleDes.fp
        (packedInput 64 32 (s.gpr .edi) (s.gpr .esi))) >>> 32).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.fp (by decide) 32 32
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .edi .esi .eax .ebx (instrs finalPermutation.lit) finalPermutation_check (by decide +kernel) s
  have hcode : permuteCode Spec.TripleDes.fp 64 32 32 .eax .ebx .edi .esi .ecx = instrs finalPermutation.lit :=
    congrArg instrs finalPermutation.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩

end VG.Proof.TripleDes.X86

end

/-! ## `FinalSave` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86

def finalMem (s : State) : Mem :=
  (s.mem.writeW (wordAddr (s.gpr .ebp) 6) (s.gpr .eax)).writeW
    (wordAddr (s.gpr .ebp) 7) (s.gpr .ebx)

theorem finalStores_ok (s : State) (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa [.store (memOp .ebp 24) .eax, .store (memOp .ebp 28) .ebx] s = some s' ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = finalMem s := by
  have h6 := hok.slotIn 6 (by decide)
  have h7 := hok.slotIn 7 (by decide)
  simp only [wordAddr, addr, sboxCfg] at h6 h7
  refine ⟨{s with mem := finalMem s}, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.ea,
      memOp, h6, h7, ite_true]
    rfl, rfl, rfl, rfl, rfl⟩

structure FinalSavePost (x : BitVec 64) (s s' : State) : Prop where
  lo : s'.mem.readW (wordAddr (s.gpr .ebp) 6) 32 = x.setWidth 32
  hi : s'.mem.readW (wordAddr (s.gpr .ebp) 7) 32 = (x >>> 32).setWidth 32
  bp : s'.gpr .ebp = s.gpr .ebp
  sp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [workRegion s] s.mem s'.mem

theorem finalSave_ok (s : State) (hok : Ok sboxCfg s) :
    WP isa (.block finalSave) s (FinalSavePost
      (Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .esi ++ s.gpr .edi)) s) := by
  rw [finalSave, WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, sp₁, mem₁, regs₁⟩ := fp_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have bp₁ := regs₁ .ebp (by decide +kernel)
  obtain ⟨s₂, run₂, gpr₂, rd₂, wr₂, mem₂⟩ := finalStores_ok s₁ (hok.congr bp₁ bp₁ rd₁ wr₁)
  have hsep : Mem.Sep (wordAddr (s.gpr .ebp) 6) 4 (wordAddr (s.gpr .ebp) 7) 4 := by
    rw [wordAddr, wordAddr, addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega),
      addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega)]
    exact Offset.sep _ (by decide) (by decide) (by decide)
  have hm : s₂.mem = (s.mem.writeW (wordAddr (s.gpr .ebp) 6) (s₁.gpr .eax)).writeW
      (wordAddr (s.gpr .ebp) 7) (s₁.gpr .ebx) := by rw [mem₂, finalMem, bp₁, mem₁]
  refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, ?_, by rw [gpr₂]; exact bp₁,
    by rw [gpr₂]; exact sp₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  · rw [hm, Mem.readW_writeW_sep hsep (by decide), Mem.readW_writeW_self32, lo₁]
    rfl
  · rw [hm, Mem.readW_writeW_self32, hi₁]
    rfl
  · have h6 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 6) 4 := by
      rw [wordAddr, addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega)]
      exact Offset.contains _ (by decide) (by decide) (by decide)
    have h7 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 7) 4 := by
      rw [wordAddr, addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega)]
      exact Offset.contains _ (by decide) (by decide) (by decide)
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ h6).writeW
      (List.mem_singleton_self _) _ h7

end VG.Proof.TripleDes.X86

end

/-! ## `RestoredOutput` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

def finalWord (s : State) : BitVec 64 :=
  s.mem.readW (addr (s.gpr .eax) 28) 32 ++ s.mem.readW (addr (s.gpr .eax) 24) 32

theorem restoredOutput_ok (s : State) (fit : (dataArg s).toNat + 8 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hr : ∀ k ∈ [24, 28], InRegions (s.rd ++ s.wr) (addr (s.gpr .eax) k) 4)
    (hw : ∀ i < 2, InRegions s.wr (wordAddr (dataArg s) i) 4) :
    ∃ s', runBlock isa restoredOutput s = some s' ∧
      s'.mem = s.mem.writeW (addr32 (dataArg s)) (byteRev64 (finalWord s)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) := by
  have hw0 := hw 0 (by decide)
  have hw1 := hw 1 (by decide)
  have h24 := hr 24 (by decide)
  have h28 := hr 28 (by decide)
  simp only [wordAddr, addr, dataArg] at harg hw0 hw1
  simp only [addr] at h24 h28
  refine ⟨_, by
    simp only [restoredOutput, rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, State.ea, memOp, harg, hw0, hw1, h24, h28, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only [mem_setReg, gpr_setReg, reduceCtorEq, ite_true, ite_false]
    have ha0 : (dataArg s + BitVec.ofNat 32 0).setWidth 64 = addr32 (dataArg s) := by simp [addr32]
    have ha1 : (dataArg s + BitVec.ofNat 32 4).setWidth 64 = addr32 (dataArg s) + 4 := addr_eq (by omega)
    change (s.mem.writeW ((dataArg s + BitVec.ofNat 32 0).setWidth 64)
      (bswap (s.mem.readW (addr (s.gpr .eax) 28) 32))).writeW
      ((dataArg s + BitVec.ofNat 32 4).setWidth 64)
      (bswap (s.mem.readW (addr (s.gpr .eax) 24) 32)) = _
    rw [ha0, ha1, writeW_pair, bswapPair]
    rfl
  · rfl
  · rfl
  · intro r ha hc hd
    simp only [gpr_setReg, ha, hc, hd, ite_false]

end VG.Proof.TripleDes.X86

end
