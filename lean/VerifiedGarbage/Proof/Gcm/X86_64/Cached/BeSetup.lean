module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.CtrsBe
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The setup of the counters added to as bytes

`beSetup_ok`: `StitchZH.beSetup off` stores the constants `beFour` and
`sixteen` at `r11 + 896` and `r11 + 912`, and leaves in `r10` the 32-bit
block index read from `rsp + off`, less one, in its top byte.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZH (beSetup)
open VG.Proof.Gcm.X86_64 (beFour)
open VG.Proof.Gcm.X86_64.StitchZ (sixteen)

theorem pslldq_beFour : XShiftOp.pslldq.eval ((0 : BitVec 64) ++ (0x0400000000000000 : BitVec 64)) 8 = beFour := by
  decide

theorem sixteen_eq : (0 : BitVec 64) ++ (16 : BitVec 64) = sixteen := by decide

/-- The constants of `StitchZH.beSetup`. -/
theorem beConsts_ok (s : State)
    (h896 : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 896) 16)
    (h912 : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 912) 16) :
    WP isa (.block ((beSetup 0).take 7)) s fun t =>
      t.mem = (s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 896) beFour).writeW
        (s.gpr .r11 + BitVec.ofNat 64 912) sixteen ∧
      (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧ (∀ x, x ≠ .xmm13 → ∀ l < 4, t.zlane x l = s.zlane x l) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have ea : ∀ (t : State) (b : Reg) (d : Nat), t.ea (at_ b d) = t.gpr b + BitVec.ofNat 64 d := fun t b d => by
    rw [VG.Proof.Gcm.X86_64.Pclmul.ea_at, BitVec.ofInt_natCast]
  apply WP.of_runBlock
  simp only [beSetup, List.take, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, isa, ea,
    State.store128_eq, State.lane, RegUpd.xmm_setV, ↓reduceIte, State.setMem_wr, State.setMem_gpr, State.setMem_mem, RegUpd.gpr_setV, RegUpd.wr_setV, RegUpd.mem_setV,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, reduceCtorEq,
    h896, h912, Option.some.injEq, exists_eq_left', pslldq_beFour, sixteen_eq]
  refine ⟨?_, fun r hr => ?_, fun x hx l hl => ?_, ?_, ?_⟩ <;> try trivial
  · simp only [hr, ↓reduceIte]
  · simp [State.zlane, State.lane, State.setMem, State.setV, State.setReg, hx]

/-- `StitchZH.beSetup off`. -/
theorem beSetup_ok (off : Nat) (s : State) {i : BitVec 32}
    (h896 : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 896) 16)
    (h912 : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 912) 16)
    (hI : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 off) 4)
    (hi : ((s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 896) beFour).writeW (s.gpr .r11 + BitVec.ofNat 64 912)
      sixteen).readW (s.gpr .rsp + BitVec.ofNat 64 off) 32 = i) :
    WP isa (.block (beSetup off)) s fun t =>
      t.gpr .r10 = ((i - 1) <<< 24).setWidth 64 ∧
      t.mem = (s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 896) beFour).writeW
        (s.gpr .r11 + BitVec.ofNat 64 912) sixteen ∧
      (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧ (∀ x, x ≠ .xmm13 → ∀ l < 4, t.zlane x l = s.zlane x l) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  rw [show beSetup off = (beSetup 0).take 7 ++ [.mov32 .r10 (.mem (at_ .rsp off)), .alu32 .sub .r10 (.imm 1),
    .shift32 .shl .r10 24] from rfl, WP.block_append_iff]
  refine WP.mono (beConsts_ok s h896 h912) fun t ⟨m, g, z, rd, wr⟩ => ?_
  have ea : t.ea (at_ .rsp off) = s.gpr .rsp + BitVec.ofNat 64 off := by
    rw [VG.Proof.Gcm.X86_64.Pclmul.ea_at, BitVec.ofInt_natCast, g _ (by decide)]
  have hI' : InRegions (t.rd ++ t.wr) (s.gpr .rsp + BitVec.ofNat 64 off) 4 := by rw [rd, wr]; exact hI
  have h24 : 1 ≤ 24 ∧ 24 ≤ 31 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, readSrc32, State.load32, ea, hI', ↓reduceIte,
    Option.map_some, execAlu32, Option.bind_some, execShift32, State.setReg32, RegUpd.gpr_setReg_self, m, hi,
    h24, and_self, RegUpd.setWidth_setWidth_32, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r hr => ?_, fun x hx l hl => ?_, ?_, ?_⟩ <;> try trivial
  · simp only [RegUpd.gpr_setReg, hr, ↓reduceIte, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags]
    exact g r hr
  · exact z x hx l hl

open VG.Spec.Gcm (Block) in
open VG.Proof.Gcm.X86_64.Stitch (SPre cb pp pR dR in_sub) in
open VG.Proof.Gcm.X86_64.StitchZ (Ready AInv R10 IdxOk idxR BeConsts) in
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame) in
/-- From the loops' state without the index (`Ready`) to the one with it
(`Ready … true`): `beSetup` stores the constants and loads the index, the
low word of the counter block, from `rsp + off`. -/
theorem ready_be {s₀ : State} (hp : SPre s₀) {off : Nat} (hx : IdxOk off [dR s₀, pR s₀] s₀)
    {P : Nat → Nat → Block} {s : State} (hR : Ready s₀ P s) :
    WP isa (.block (beSetup off)) s fun t => Ready s₀ P t true ∧ HKeep s t := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  have hr11 : s.gpr .r11 = pp s₀ := hR.gpr .r11 (by decide) (by decide) (by decide)
  have hsp : s.gpr .rsp = s₀.gpr .rsp := hR.gpr .rsp (by decide) (by decide) (by decide)
  obtain ⟨hi, hI, hd⟩ := hx
  have c896 : (pR s₀).Contains (pp s₀ + BitVec.ofNat 64 896) (128 / 8) := Offset.contains_base _ (by omega) (by omega)
  have c912 : (pR s₀).Contains (pp s₀ + BitVec.ofNat 64 912) (128 / 8) := Offset.contains_base _ (by omega) (by omega)
  have fr : Frame [pR s₀] s.mem
      ((s.mem.writeW (pp s₀ + BitVec.ofNat 64 896) beFour).writeW (pp s₀ + BitVec.ofNat 64 912) sixteen) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c896).writeW (List.mem_singleton_self _) _ c912
  have hi₁ : ((s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 896) beFour).writeW (s.gpr .r11 + BitVec.ofNat 64 912)
      sixteen).readW (s.gpr .rsp + BitVec.ofNat 64 off) 32 = (cb s₀).extractLsb' 0 32 := by
    rw [hr11, hsp, fr.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd _ (by simp)) (show 32 / 8 < 2 ^ 64 by decide),
      hR.a.frame.readW (Region.contains_self _ _) hd (show 32 / 8 < 2 ^ 64 by decide)]
    exact hi
  refine WP.mono (WP.hkeep (is := beSetup off) rfl (beSetup_ok off s
    (by rw [hr11, hR.a.wr]; exact in_sub hp.p_in (by omega)) (by rw [hr11, hR.a.wr]; exact in_sub hp.p_in (by omega))
    (by rw [hsp, hR.a.rd, hR.a.wr]; exact hI) hi₁)) fun t ⟨⟨g10, m, g, z, rd, wr⟩, hh⟩ => ⟨?_, hh⟩
  rw [hr11] at m
  have ft : Frame [pR s₀] s.mem t.mem := by rw [m]; exact fr
  have hA : AInv s₀ 0 t true :=
    ⟨hR.a.le, fun l hl => by rw [z _ (by decide) l hl]; exact hR.a.ctr l hl,
      fun l hl => by rw [z _ (by decide) l hl]; exact hR.a.msk l hl,
      fun l hl => by rw [z _ (by decide) l hl]; exact hR.a.inc l hl,
      by rw [g _ (by decide)]; exact hR.a.rdi, by rw [g _ (by decide)]; exact hR.a.rsi,
      ⟨by rw [g10]; simp only [idxR, BitVec.ofNat_eq_ofNat, BitVec.add_zero],
        by rw [m]; exact ⟨by
          rw [Mem.readW_writeW_sep (Offset.sep _ (Or.inl (by omega)) (by omega) (by omega)) (by decide)]
          exact Mem.readW_writeW_self _ _ 16 _ (by decide), Mem.readW_writeW_self _ _ 16 _ (by decide)⟩⟩,
      hR.a.frame.trans (ft.sub fun r hr => ⟨pR s₀, by simp, fun a ha => by
        simp only [List.mem_singleton] at hr; subst hr; exact ha⟩),
      fun k hk => by
        rw [blockAt_frame ft fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.d_p.sub_left (Offset.sub_base _ (by omega))]
        exact hR.a.blocks k hk,
      by rw [rd]; exact hR.a.rd, by rw [wr]; exact hR.a.wr⟩
  have keepLow : ∀ o, o + 16 ≤ 896 →
      t.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 = s.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 := fun o ho => by
    rw [m, Mem.readW_writeW_sep (Offset.sep _ (Or.inl (by omega)) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (Or.inl (by omega)) (by omega) (by omega)) (by decide)]
  exact ⟨hA, by rw [g _ (by decide)]; exact hR.rdx, by rw [g _ (by decide)]; exact hR.rax,
    fun r h1 h2 h3 => by rw [g r h3]; exact hR.gpr r h1 h2 h3,
    fun k hk l hl => by rw [keepLow _ (by omega)]; exact hR.pw k hk l hl,
    fun l hl => by rw [z _ (by decide) l hl]; exact hR.m1 l hl,
    by rw [z _ (by decide) 0 (by decide)]; exact hR.y,
    fun l h1 h4 => by rw [z _ (by decide) l h4]; exact hR.y1 l h1 h4⟩

end VG.Proof.Gcm.X86_64.StitchZH
