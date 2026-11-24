module

public import VerifiedGarbage.Proof.Aes.X86.VariantProof
public import VerifiedGarbage.Proof.Aes.X86.Vperm
import VerifiedGarbage.Proof.Aes.X86.Vperm.Lit
import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.AesNi.Arith
import VerifiedGarbage.Proof.Aes.X86.AesNi.Counters
import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Aes.X86.VariantProof
meta import VerifiedGarbage.Proof.Aes.X86.Vperm
meta import VerifiedGarbage.Proof.Aes.X86.Vperm.Lit
meta import VerifiedGarbage.Proof.Aes.X86.Ctr32
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Arith
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Counters
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Spec

/-!
# `AesCtr32` on x86 (32-bit): vector permutations (SSSE3)

`vg_aes_ctr32_to_ssse3` (`Impl/Aes/X86/Vperm.lean`), a block at a time: the
final counter is written first; after `c` blocks the first `c` of the result
are the data's XORed with the keystream (`CInv`). It uses the first 496 bytes
of its scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Variants.AesCtr32.X86.Ssse3

open VG VG.X86
open VG.Impl.Aes.X86.Vperm
open VG.Impl.Aes.X86.AesNi (at_ argOp)
open VG.Proof.Aes.X86 (GPre CPre ctrPost argRg retR schP nRounds ctrP datP nBlk scrP schR ctrR scrR srcR dstP dstR reg32
  addr_zero addr_add addr_add64 in_rd in_rd_left in_reg part_sub_reg reg_contains part_contains part_sub part_disj icb_lo ctr_after
  ctrToτN ctr_agreeN ctrTo_agreeN)
open VG.Proof.Aes.X86.Vperm
open VG.Proof.Aes.X86.AesNi (sch cb ciph bAddr blk tAddr pfx counterLane counterLane_state cache_prefix memory_prefix
  ctrState_rev aesWith_eq blockAt_frame blockAt_writeW_xor)
open VG.Proof.Aes.Vector (st)
open VG.Spec.Gcm (blockAt inc32)

variable {B : Nat} {s₀ : State}

theorem args_of (hp : GPre true s₀ B) : Args 5 B (scrP s₀) s₀ where
  fit := hp.fB
  scr := hp.wB
  argIn := in_rd_left (hp.rA 5 (.inl (by decide)))
  arg := rfl

theorem sched_of (hp : GPre true s₀ B) : Sched B (scrP s₀) (schP s₀) (nRounds s₀) (sch s₀) s₀ where
  fit := hp.fS
  sch := List.mem_append_left _ hp.rS
  sep := hp.dSB
  argIn := fun i hi => in_rd_left (hp.rA i (.inl (by omega_using [hi])))
  argSep := fun i hi => hp.aB.sub_left (hp.argSub (.inl (by omega_using [hi])))
  arg0 := rfl
  arg1 := by
    show arg s₀ 1 = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rounds := hp.rounds
  key := fun j hj => by
    have hR : nRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_using [h]
    rw [addr_eq (by have := hp.fS; omega_using [hj, hR, this])]
    exact VG.Proof.Aes.Vector.keyIs_readW _ _ (by omega_using [hj])

/-- The AES state of a register is the same on both sides. -/
theorem st_eq (v : BitVec 128) : VG.Proof.Aes.X86.AesNi.st v = st v := rfl

/-- After `c` blocks. -/
structure CInv (B : Nat) (sk : Nat → BitVec 128) (s₀ : State) (c : Nat) (s : State) : Prop where
  core : CoreIn enc Enc.all B (scrP s₀) (nRounds s₀) sk s
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Spill.Saved s.mem (addr (scrP s₀)) s₀.gpr enc.savedRegs
  frame : Frame [ctrR s₀, dstR true s₀, scrR s₀ B] s₀.mem s.mem
  pre : s.mem.readW (addr (scrP s₀) Ctr.prefixOff) 128 = (0 : BitVec 32) ++ pfx s₀
  ctr : blockAt s.mem ((ctrP s₀).setWidth 64) = Nat.repeat inc32 (nBlk s₀) (cb s₀)
  edx : s.gpr .edx = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 c
  esi : s.gpr .esi = datP s₀ + BitVec.ofNat 32 (16 * c)
  eax : s.gpr .eax = dstP true s₀ + BitVec.ofNat 32 (16 * c)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (nBlk s₀ - c)
  le : c ≤ nBlk s₀
  blocks : ∀ k < nBlk s₀, blockAt s.mem (tAddr s₀ true k) =
    if k < c then blk s₀ k ^^^ ciph s₀ (Nat.repeat inc32 k (cb s₀)) else blockAt s₀.mem (tAddr s₀ true k)

/-- An argument, after writes to the buffers. -/
theorem arg_ok (hp : GPre true s₀ B) {s : State} (hesp : s.gpr .esp = s₀.gpr .esp) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hf : Frame [ctrR s₀, dstR true s₀, scrR s₀ B] s₀.mem s.mem) {i : Nat} (hi : i < 7) :
    s.gpr .esp = s₀.gpr .esp ∧ InRegions (s.rd ++ s.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 ∧
      s.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i := by
  have hi' : i < 6 ∨ (true = true ∧ i = 6) := by
    by_cases h : i < 6
    · exact .inl h
    · exact .inr ⟨rfl, by omega_using [hi, h]⟩
  refine ⟨hesp, by rw [hrd, hwr]; exact in_rd_left (hp.rA i hi'), hf.readW (hp.argC hi') (fun r hr => ?_) (by decide)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.aC
  · exact hp.aD
  · exact hp.aB

/-- The counter block's arguments. -/
theorem ctrArgs_ok (hp : GPre true s₀ B) (hB : 496 ≤ B) {sk : Nat → BitVec 128} {s : State}
    (h : TabSt enc Enc.all (scrP s₀) s₀ Enc.all.length s) (hc : CoreIn enc Enc.all B (scrP s₀) (nRounds s₀) sk s) :
    WP isa (.block Ctr.args) s fun s' => CInv B sk s₀ 0 s' ∧ s'.zf = some (decide (nBlk s₀ = 0)) := by
  have fC := hp.fC
  have fB := hp.fB
  have hN : enc.saved + 16 ≤ B := by omega_using [hB, show enc.saved = 464 from rfl]
  have hf₀ : Frame [scrR s₀ B] s₀.mem s.mem := h.sub hN
  have hf : Frame [ctrR s₀, dstR true s₀, scrR s₀ B] s₀.mem s.mem := hf₀.mono fun r hr =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  obtain ⟨e2, i2, a2⟩ := arg_ok hp h.esp h.rd h.wr hf (i := 2) (by decide)
  rw [show Ctr.args = ([.mov .ecx (.mem (argOp 2))] : List Instr) ++ (([.movdquLoad .xmm0 (at_ .ecx 0),
    .xop (.shift .pslldq .xmm0 4), .xop (.shift .psrldq .xmm0 4)] : List Instr) ++
    (.movdquStore (at_ .edi Ctr.prefixOff) .xmm0 :: ([.mov .edx (.mem (at_ .ecx 12)), .bswap .edx, .mov .eax (.reg .edx),
      .alu .add .eax (.mem (argOp 4)), .bswap .eax, .store (at_ .ecx 12) .eax, .mov .esi (.mem (argOp 3)),
      .mov .eax (.mem (argOp 6)), .mov .ebp (.mem (argOp 4)), .alu .test .ebp (.reg .ebp)] : List Instr))) from rfl,
    WP.block_append_iff]
  refine WP.mono (wp_g (Q := fun s' => Wp.Upd s s' .ecx (ctrP s₀)) rfl
    (Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * 2) e2 i2 fun s₁ u₁ => WP.block_nil (by rw [a2] at u₁; exact u₁)))
    fun s₁ ⟨u₁, x₁⟩ => ?_
  have hca : addr (ctrP s₀) 0 = (ctrP s₀).setWidth 64 := addr_zero _
  have hce : s₁.ea (at_ .ecx 0) = (ctrP s₀).setWidth 64 := by rw [at_, ea_mk, u₁.gpr, hca]
  have hwC : ctrR s₀ ∈ s.wr := by rw [h.wr]; exact hp.wC
  have hcIn : InRegions (s₁.rd ++ s₁.wr) ((ctrP s₀).setWidth 64) 16 :=
    ⟨ctrR s₀, List.mem_append_right _ (by rw [u₁.wr]; exact hwC), Region.contains_self _ _⟩
  have hcr : s₁.mem.readW ((ctrP s₀).setWidth 64) 128 = s₀.mem.readW ((ctrP s₀).setWidth 64) 128 := by
    rw [u₁.mem]
    refine hf₀.readW (r := ctrR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.dCB
  refine wp_x rfl (fun m hm => ?_) ?_
  · simp only [List.filterMap_cons, xmemOp, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    rw [hce]; exact hcIn
  generalize hff : xvals (fun m => s₁.mem.readW (s₁.ea m) 128) s₁.xmm ([.movdquLoad .xmm0 (at_ .ecx 0),
    .xop (.shift .pslldq .xmm0 4), .xop (.shift .psrldq .xmm0 4)] : List Instr) = f
  have hf0 : f .xmm0 = (0 : BitVec 32) ++ pfx s₀ := by
    rw [← hff]
    simp only [xvals, xval, put_apply, ite_true]
    rw [hce, hcr, cache_prefix]
  have hf6 : f .xmm6 = s.xmm .xmm6 := by rw [← hff, xvals_keep _ _ _ _ (by decide), x₁]
  have hf7 : f .xmm7 = s.xmm .xmm7 := by rw [← hff, xvals_keep _ _ _ _ (by decide), x₁]
  have he2 : (setX s₁ f).ea ⟨.edi, Ctr.prefixOff⟩ = addr (scrP s₀) 480 := by
    rw [ea_mk, show (setX s₁ f).gpr .edi = scrP s₀ from (u₁.other _ (by decide)).trans h.edi]; rfl
  have hpIn : InRegions s₁.wr (addr (scrP s₀) 480) 16 :=
    in_reg (by rw [u₁.wr, h.wr]; exact hp.wB) fB (by omega_using [hB]) (by decide)
  refine WP.block_cons_iff.mpr ⟨{ setX s₁ f with mem := s₁.mem.writeW (addr (scrP s₀) 480) ((0 : BitVec 32) ++ pfx s₀) }, ?_, ?_⟩
  · show (setX s₁ f).store128 ((setX s₁ f).ea ⟨.edi, Ctr.prefixOff⟩) (f .xmm0) = _
    rw [he2, hf0]
    exact ite_eq_left hpIn
  generalize hs₂ : ({ setX s₁ f with mem := s₁.mem.writeW (addr (scrP s₀) 480) ((0 : BitVec 32) ++ pfx s₀) } : State) = s₂
  have hm₂ : s₂.mem = s.mem.writeW (addr (scrP s₀) 480) ((0 : BitVec 32) ++ pfx s₀) := by rw [← hs₂, ← u₁.mem]
  have hg₂ : s₂.gpr = s₁.gpr := by rw [← hs₂]; rfl
  have hrd₂ : s₂.rd = s.rd := by rw [← hs₂, ← u₁.rd]; rfl
  have hwr₂ : s₂.wr = s.wr := by rw [← hs₂, ← u₁.wr]; rfl
  have hx₂ : s₂.xmm = f := by rw [← hs₂]; rfl
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [hg₂, u₁.other _ (by decide), h.esp]
  have edi₂ : s₂.gpr .edi = scrP s₀ := by rw [hg₂, u₁.other _ (by decide), h.edi]
  have ecx₂ : s₂.gpr .ecx = ctrP s₀ := by rw [hg₂, u₁.gpr]
  -- The prefix.
  have hP : Frame [⟨addr (scrP s₀) 480, 16⟩] s.mem s₂.mem := by
    rw [hm₂]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have hPB : Region.Sub ⟨addr (scrP s₀) 480, 16⟩ (scrR s₀ B) := part_sub_reg fB (by omega_using [hB])
  have hf₂ : Frame [scrR s₀ B] s₀.mem s₂.mem := hf₀.trans (hP.sub fun r hr => ⟨scrR s₀ B, List.mem_cons_self, by
    simp only [List.mem_singleton] at hr; subst hr; exact hPB⟩)
  have hf₂' : Frame [ctrR s₀, dstR true s₀, scrR s₀ B] s₀.mem s₂.mem := hf₂.mono fun r hr =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  have hctr12 : s₂.mem.readW (addr (ctrP s₀) 12) 32 = s₀.mem.readW (addr (ctrP s₀) 12) 32 := by
    refine hf₂.readW (r := ctrR s₀) (reg_contains fC (by decide) (by decide)) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.dCB
  have hlo : bswap (s₀.mem.readW (addr (ctrP s₀) 12) 32) = (cb s₀).extractLsb' 0 32 := icb_lo _ fC
  -- The final counter, and the rest of the arguments.
  have hc12 : InRegions (s₂.rd ++ s₂.wr) (addr (ctrP s₀) 12) 4 :=
    ⟨ctrR s₀, List.mem_append_right _ (by rw [hwr₂]; exact hwC), reg_contains fC (by decide) (by decide)⟩
  refine WP.mono (wp_g (Q := fun s' => s'.mem = s₂.mem.writeW (addr (ctrP s₀) 12)
      (bswap ((cb s₀).extractLsb' 0 32 + arg s₀ 4)) ∧ s'.rd = s₂.rd ∧ s'.wr = s₂.wr ∧ s'.gpr .edi = s₂.gpr .edi ∧
      s'.gpr .esp = s₂.gpr .esp ∧ s'.gpr .edx = (cb s₀).extractLsb' 0 32 ∧ s'.gpr .esi = datP s₀ ∧
      s'.gpr .eax = arg s₀ 6 ∧ s'.gpr .ebp = arg s₀ 4 ∧ s'.zf = some (arg s₀ 4 &&& arg s₀ 4 == 0)) rfl ?_) fun s' hh => ?_
  · refine Wp.wp_ldm (B := ctrP s₀) (o := 12) ecx₂ hc12 fun t₁ v₁ => Wp.wp_bswap fun t₂ v₂ => Wp.wp_mov fun t₃ v₃ => ?_
    have esp₃ : t₃.gpr .esp = s₀.gpr .esp := by
      rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), esp₂]
    have m₃ : t₃.mem = s₂.mem := by rw [v₃.mem, v₂.mem, v₁.mem]
    have rd₃ : t₃.rd = s₀.rd := by rw [v₃.rd, v₂.rd, v₁.rd, hrd₂, h.rd]
    have wr₃ : t₃.wr = s₀.wr := by rw [v₃.wr, v₂.wr, v₁.wr, hwr₂, h.wr]
    obtain ⟨-, j4, b4⟩ := arg_ok hp esp₃ rd₃ wr₃ (by rw [m₃]; exact hf₂') (i := 4) (by decide)
    refine Wp.wp_addm (B := s₀.gpr .esp) (o := 4 + 4 * 4) esp₃ j4 fun t₄ v₄ => Wp.wp_bswap fun t₅ v₅ => ?_
    have edx₅ : t₅.gpr .edx = (cb s₀).extractLsb' 0 32 := by
      rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.gpr, hctr12, hlo]
    have eax₅ : t₅.gpr .eax = bswap ((cb s₀).extractLsb' 0 32 + arg s₀ 4) := by
      rw [v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, v₁.gpr, hctr12, hlo, b4]
    have ecx₅ : t₅.gpr .ecx = ctrP s₀ := by
      rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
        v₁.other _ (by decide), ecx₂]
    have m₅ : t₅.mem = s₂.mem := by rw [v₅.mem, v₄.mem, m₃]
    have rd₅ : t₅.rd = s₀.rd := by rw [v₅.rd, v₄.rd, rd₃]
    have wr₅ : t₅.wr = s₀.wr := by rw [v₅.wr, v₄.wr, wr₃]
    refine Wp.wp_stm (B := ctrP s₀) (o := 12) ecx₅
      (by rw [wr₅]; exact ⟨ctrR s₀, hp.wC, reg_contains fC (by decide) (by decide)⟩) fun t₆ v₆ => ?_
    have m₆ : t₆.mem = s₂.mem.writeW (addr (ctrP s₀) 12) (bswap ((cb s₀).extractLsb' 0 32 + arg s₀ 4)) := by
      rw [v₆.mem, m₅, eax₅]
    have hf₆ : Frame [ctrR s₀, dstR true s₀, scrR s₀ B] s₀.mem t₆.mem := by
      rw [m₆]
      exact hf₂'.writeW List.mem_cons_self _ (reg_contains fC (by decide) (by decide))
    have esp₆ : t₆.gpr .esp = s₀.gpr .esp := by rw [v₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), esp₃]
    have rd₆ : t₆.rd = s₀.rd := v₆.rd.trans rd₅
    have wr₆ : t₆.wr = s₀.wr := v₆.wr.trans wr₅
    obtain ⟨-, j3, b3⟩ := arg_ok hp esp₆ rd₆ wr₆ hf₆ (i := 3) (by decide)
    obtain ⟨-, j6, b6⟩ := arg_ok hp esp₆ rd₆ wr₆ hf₆ (i := 6) (by decide)
    obtain ⟨-, j4', b4'⟩ := arg_ok hp esp₆ rd₆ wr₆ hf₆ (i := 4) (by decide)
    refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * 3) esp₆ j3 fun t₇ v₇ => ?_
    refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * 6) ((v₇.other _ (by decide)).trans esp₆)
      (by rw [v₇.rd, v₇.wr]; exact j6) fun t₈ v₈ => ?_
    refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * 4)
      ((v₈.other _ (by decide)).trans ((v₇.other _ (by decide)).trans esp₆))
      (by rw [v₈.rd, v₈.wr, v₇.rd, v₇.wr]; exact j4') fun t₉ v₉ => ?_
    refine Wp.wp_test fun u w z => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [w.mem, v₉.mem, v₈.mem, v₇.mem, m₆]
    · rw [w.rd, v₉.rd, v₈.rd, v₇.rd, rd₆, hrd₂, h.rd]
    · rw [w.wr, v₉.wr, v₈.wr, v₇.wr, wr₆, hwr₂, h.wr]
    · rw [w.gpr, v₉.other _ (by decide), v₈.other _ (by decide), v₇.other _ (by decide), v₆.gpr, v₅.other _ (by decide),
        v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)]
    · rw [w.gpr, v₉.other _ (by decide), v₈.other _ (by decide), v₇.other _ (by decide), esp₆, esp₂]
    · rw [w.gpr, v₉.other _ (by decide), v₈.other _ (by decide), v₇.other _ (by decide), v₆.gpr, edx₅]
    · rw [w.gpr, v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, b3]
    · rw [w.gpr, v₉.other _ (by decide), v₈.gpr, v₇.mem, b6]
    · rw [w.gpr, v₉.gpr, v₈.mem, v₇.mem, b4']
    · rw [z, v₉.gpr, v₈.mem, v₇.mem, b4']
  · obtain ⟨⟨m, rd, wr, e, p, dx, si, ax, bp, z⟩, x⟩ := hh
    have hl := (Enc.setupOk (b := true)).len
    have hC : Frame [ctrR s₀] s₂.mem s'.mem := by
      rw [m]
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (reg_contains fC (by decide) (by decide))
    have hCP : Frame [ctrR s₀, ⟨addr (scrP s₀) 480, 16⟩] s.mem s'.mem :=
      (hP.mono fun r hr => List.mem_cons_of_mem _ hr).trans (hC.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
    have hall : Frame [ctrR s₀, scrR s₀ B] s₀.mem s'.mem :=
      (hf₂.mono fun r hr => List.mem_cons_of_mem _ hr).trans (hC.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
    have hdB : ∀ o n, o + n ≤ 480 → ∀ r ∈ [ctrR s₀, (⟨addr (scrP s₀) 480, 16⟩ : Region)],
        Region.Disjoint ⟨addr (scrP s₀) o, n⟩ r := fun o n hon r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.dCB.sub_right (part_sub_reg fB (by omega_using [hon, hB]))).symm
      · exact part_disj fB (by omega_using [hon, hB]) (by omega_using [hB]) (.inl hon)
    have hn : nBlk s₀ < 2 ^ 32 := (arg s₀ 4).isLt
    refine ⟨⟨hc.of_frame (rs := [ctrR s₀, ⟨addr (scrP s₀) 480, 16⟩]) ?_ ?_ (rd.trans hrd₂) (wr.trans hwr₂)
      (by rw [x, hx₂, hf6]) (by rw [x, hx₂, hf7]) hCP hl (fun o ho r hr => hdB o 16 (by omega_using [ho, show enc.slots = 224 from rfl]) r hr)
      (fun r hr => ?_), p.trans esp₂, by rw [rd, hrd₂, h.rd], by rw [wr, hwr₂, h.wr],
      h.saved.of_frame hCP (R := ⟨addr (scrP s₀) 464, 16⟩) (fun q hq => ?_) (hdB 464 16 (by decide)),
      hall.mono fun r hr => ?_, ?_, ?_, by rw [dx]; exact (BitVec.add_zero _).symm,
      by rw [si]; exact (BitVec.add_zero _).symm, by rw [ax]; exact (BitVec.add_zero _).symm, ?_, Nat.zero_le _,
      fun k hk => ?_⟩, ?_⟩
    · rw [e, edi₂, h.edi]
    · rw [p, esp₂, h.esp]
    · rw [h.esp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hA := hp.argSub (i := 1) (.inl (by decide))
      rcases hr with rfl | rfl
      · exact hp.aC.sub_left hA
      · exact (hp.aB.sub_left hA).sub_right hPB
    · rcases savedRegs_mem hq with rfl | rfl | rfl | rfl <;>
        exact part_contains fB (by omega_using [hB]) (by decide) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · show s'.mem.readW (addr (scrP s₀) 480) 128 = _
      refine (hC.readW (r := ⟨addr (scrP s₀) 480, 16⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)).trans ?_
      · simp only [List.mem_singleton] at hr; subst hr
        exact (hp.dCB.sub_right hPB).symm
      · rw [hm₂, Mem.readW_writeW_self _ _ 16 _ (by decide)]
    · refine ctr_after fC (N := arg s₀ 4) (by rw [nBlk, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (fun k hk => ?_) ?_
      · rw [m]
        have h1 : (s₂.mem.writeW (addr (ctrP s₀) 12) (bswap ((cb s₀).extractLsb' 0 32 + arg s₀ 4))) (addr (ctrP s₀) k) =
            s₂.mem (addr (ctrP s₀) k) := by
          change (s₂.mem.write (addr (ctrP s₀) 12) 4 _) _ = _
          rw [Mem.write_apply]
          rw [addr_eq (by omega_using [hk, fC]), addr_eq (by omega_using [fC])]
          exact (Offset.sep_base ((ctrP s₀).setWidth 64) (n := 12) (e := 12) (k := 4)
            (by decide) (by decide)) _ (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hk])]; exact hk)
        rw [h1, addr_eq (by omega_using [hk, fC])]
        exact hf₂.bytes (R := ctrR s₀) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.dCB) (by change 16 ≤ 2 ^ 64; decide)
          (by change k < 16; omega_using [hk])
      · rw [m, Mem.readW_writeW_self32, hlo]
    · rw [bp, Nat.sub_zero, nBlk, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [ite_eq_right (Nat.not_lt_zero k)]
      refine blockAt_frame hall fun r hr => ?_
      have hs : Region.Sub ⟨tAddr s₀ true k, 16⟩ (dstR true s₀) := Offset.sub_base _ (by omega_using [hk])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dCD.symm.sub_left hs
      · exact hp.dDB.sub_left hs
    · rw [z, BitVec.and_self]
      refine congrArg some ?_
      rw [show arg s₀ 4 = BitVec.ofNat 32 (nBlk s₀) by rw [nBlk, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        Wp.ofNat_beq_zero hn]

/-- `movd r, d`. -/
theorem wp_movd {rest : List Instr} {r : XReg} {d : Reg} {s : State} {Q : State → Prop}
    (q : WP isa (.block rest) (setX s (put s.xmm r ((0 : BitVec 96) ++ s.gpr d))) Q) :
    WP isa (.block (.xop (.movd r d) :: rest)) s Q :=
  WP.block_cons_iff.mpr ⟨_, rfl, q⟩

/-- The source blocks not yet read are as they were. -/
theorem CInv.src (hp : GPre true s₀ B) {sk : Nat → BitVec 128} {c : Nat} {s : State} (h : CInv B sk s₀ c s) {k : Nat}
    (hk : k < nBlk s₀) (hc : c ≤ k) : blockAt s.mem (bAddr s₀ k) = blk s₀ k := by
  rcases hp.sd with he | hdis
  · have e : bAddr s₀ k = tAddr s₀ true k := by simp only [bAddr, tAddr, he]
    have hb := h.blocks k hk
    rw [ite_eq_right (show ¬ k < c by omega_using [hc])] at hb
    rw [e, hb, ← e]
  · exact blockAt_frame h.frame fun r hr => by
      have hs : Region.Sub ⟨bAddr s₀ k, 16⟩ (srcR s₀) := Offset.sub_base _ (by omega_using [hk])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.dCS.sub_right hs).symm
      · exact hdis.sub_left hs
      · exact hp.dSrcB.sub_left hs

/-- The keystream block. -/
theorem counter_ok (hp : GPre true s₀ B) (hB : 496 ≤ B) {sk : Nat → BitVec 128} {c : Nat} {s : State}
    (h : CInv B sk s₀ c s) :
    WP isa (.block Ctr.counter) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.gpr .edx = s.gpr .edx + 1 ∧
      s'.xmm .xmm6 = s.xmm .xmm6 ∧ s'.xmm .xmm7 = s.xmm .xmm7 ∧
      st (s'.xmm .xmm0) = VG.Proof.Aes.ctrState (cb s₀) c := by
  rw [show Ctr.counter = ([.mov .ecx (.reg .edx), .bswap .ecx] : List Instr) ++ (.xop (.movd .xmm0 .ecx) ::
    (([.xop (.shift .pslldq .xmm0 12), .movdquLoad .xmm1 (at_ .edi Ctr.prefixOff),
      .xop (.bin .por .xmm0 .xmm1)] : List Instr) ++ [.alu .add .edx (.imm 1)])) from rfl, WP.block_append_iff]
  refine WP.mono (wp_g (Q := fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
    (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.gpr .ecx = bswap (s.gpr .edx)) rfl
    (Wp.wp_mov fun t₁ u₁ => Wp.wp_bswap fun t₂ u₂ => WP.block_nil ⟨by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr], fun r hr => by rw [u₂.other r hr, u₁.other r hr], by rw [u₂.gpr, u₁.gpr]⟩))
    fun s₁ ⟨⟨m, rd, wr, g, cx⟩, x⟩ => ?_
  refine wp_movd ?_
  have he : (setX s₁ (put s₁.xmm .xmm0 ((0 : BitVec 96) ++ s₁.gpr .ecx))).ea (at_ .edi Ctr.prefixOff) =
      addr (scrP s₀) 480 := by
    rw [at_, ea_mk]
    show addr (s₁.gpr .edi) Ctr.prefixOff = _
    rw [g _ (by decide), h.core.edi]; rfl
  have hin : InRegions (s₁.rd ++ s₁.wr) (addr (scrP s₀) 480) 16 :=
    in_rd (in_reg (by rw [wr, h.wr]; exact hp.wB) hp.fB (by omega_using [hB]) (by decide))
  refine wp_x rfl (fun mo hm => ?_) ?_
  · simp only [List.filterMap_cons, xmemOp, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    rw [he]; exact hin
  generalize hff : xvals (fun mo => (setX s₁ (put s₁.xmm .xmm0 ((0 : BitVec 96) ++ s₁.gpr .ecx))).mem.readW
    ((setX s₁ (put s₁.xmm .xmm0 ((0 : BitVec 96) ++ s₁.gpr .ecx))).ea mo) 128)
    (setX s₁ (put s₁.xmm .xmm0 ((0 : BitVec 96) ++ s₁.gpr .ecx))).xmm
    ([.xop (.shift .pslldq .xmm0 12), .movdquLoad .xmm1 (at_ .edi Ctr.prefixOff),
      .xop (.bin .por .xmm0 .xmm1)] : List Instr) = f
  have hpre : s₁.mem.readW (addr (scrP s₀) 480) 128 = (0 : BitVec 32) ++ pfx s₀ := by rw [m]; exact h.pre
  have hf0 : f .xmm0 = counterLane (s.gpr .edx) ((0 : BitVec 32) ++ pfx s₀) := by
    rw [← hff]
    simp only [xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, setX_xmm]
    rw [he, show (setX s₁ (put s₁.xmm .xmm0 ((0 : BitVec 96) ++ s₁.gpr .ecx))).mem = s₁.mem from rfl, hpre, cx]
    rfl
  have hf6 : f .xmm6 = s.xmm .xmm6 := by rw [← hff, xvals_keep _ _ _ _ (by decide), setX_xmm, put_ne _ _ (by decide), x]
  have hf7 : f .xmm7 = s.xmm .xmm7 := by rw [← hff, xvals_keep _ _ _ _ (by decide), setX_xmm, put_ne _ _ (by decide), x]
  refine WP.mono (wp_g rfl (Wp.wp_addi fun t u => WP.block_nil u)) fun t ⟨u, y⟩ => ?_
  refine ⟨u.mem.trans m, u.rd.trans rd, u.wr.trans wr, fun r h1 h2 => (u.other r h2).trans (g r h1), ?_, ?_, ?_, ?_⟩
  · rw [u.gpr]
    exact congrArg (· + 1) (g _ (by decide))
  · rw [y]; exact hf6
  · rw [y]; exact hf7
  · rw [y]
    show st (f .xmm0) = _
    rw [hf0, h.edx]
    exact counterLane_state (cb s₀) (pfx s₀) c fun k hk => memory_prefix _ _ hk

/-- One block. -/
theorem body_ok (hp : GPre true s₀ B) (hB : 496 ≤ B) {sk : Nat → BitVec 128}
    (hcore : ∀ {s : State}, CoreIn enc Enc.all B (scrP s₀) (nRounds s₀) sk s →
      WP isa enc.core s fun s' => Kept s s' ∧
        st (s'.xmm .xmm0) = Spec.Aes.cipher (nRounds s₀) (sch s₀) (st (s.xmm .xmm0)))
    {c : Nat} (hc : c < nBlk s₀) {s : State} (h : CInv B sk s₀ c s) :
    WP isa Ctr.body s fun s' => CInv B sk s₀ (c + 1) s' ∧ s'.zf = some (decide (nBlk s₀ = c + 1)) := by
  have fS := hp.fSrc
  have fD := hp.fD
  have fB := hp.fB
  have hl := (Enc.setupOk (b := true)).len
  refine WP.seq (WP.mono (counter_ok hp hB h) fun s₁ ⟨m₁, rd₁, wr₁, g₁, dx₁, x6₁, x7₁, st₁⟩ => ?_)
  have hc₁ : CoreIn enc Enc.all B (scrP s₀) (nRounds s₀) sk s₁ :=
    h.core.of_frame (rs := []) (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide)) rd₁ wr₁ x6₁ x7₁
      (by rw [m₁]; exact Frame.refl _ _) hl (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)
  refine WP.seq (WP.mono (hcore hc₁) fun s₂ ⟨k, x₂⟩ => ?_)
  have g₂ : ∀ r, r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [k.gpr r h1 h2, g₁ r h2 h3]
  have dx₂ : s₂.gpr .edx = s.gpr .edx + 1 := by rw [k.gpr _ (by decide) (by decide), dx₁]
  have m₂ : s₂.mem = s.mem := k.mem.trans m₁
  have rd₂ : s₂.rd = s₀.rd := k.rd.trans (rd₁.trans h.rd)
  have wr₂ : s₂.wr = s₀.wr := k.wr.trans (wr₁.trans h.wr)
  -- The keystream block.
  have hks : XBinOp.eval .pshufb (s₂.xmm .xmm0) VG.Proof.Gcm.X86.revMask =
      ciph s₀ (Nat.repeat inc32 c (cb s₀)) := by
    refine (aesWith_eq _ _ _ _ ?_).symm
    rw [st_eq, st_eq, x₂, st₁, ctrState_rev]
    rfl
  have es : addr (s₂.gpr .esi) 0 = bAddr s₀ c := by
    rw [g₂ _ (by decide) (by decide) (by decide), h.esi, addr_add, Nat.add_zero, addr_eq (by omega_using [fS, hc])]
  have ed : addr (s₂.gpr .eax) 0 = tAddr s₀ true c := by
    rw [g₂ _ (by decide) (by decide) (by decide), h.eax, addr_add, Nat.add_zero, addr_eq (by omega_using [fD, hc])]
  rw [show Ctr.xor = ([.movdquLoad .xmm1 (at_ .esi 0), px .xmm0 .xmm1] : List Instr) ++
    (.movdquStore (at_ .eax 0) .xmm0 :: ([.alu .add .esi (.imm 16), .alu .add .eax (.imm 16),
      .alu .sub .ebp (.imm 1)] : List Instr)) from rfl]
  have hsub : Region.Sub ⟨tAddr s₀ true c, 16⟩ (dstR true s₀) := Offset.sub_base _ (by omega_using [hc])
  refine wp_x rfl (fun mo hm => ?_) ?_
  · simp only [List.filterMap_cons, xmemOp, px, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    rw [at_, ea_mk, es, rd₂, wr₂]
    exact ⟨srcR s₀, hp.rSrc, Offset.contains_base _ (by omega_using [hc]) (by omega_using [fS, hc])⟩
  generalize hff : xvals (fun mo => s₂.mem.readW (s₂.ea mo) 128) s₂.xmm
    ([.movdquLoad .xmm1 (at_ .esi 0), px .xmm0 .xmm1] : List Instr) = f
  have hf0 : f .xmm0 = XBinOp.eval .pxor (s₂.xmm .xmm0) (s.mem.readW (bAddr s₀ c) 128) := by
    rw [← hff]
    simp only [px, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false]
    rw [at_, ea_mk, es, m₂]
  have hf6 : f .xmm6 = s.xmm .xmm6 := by rw [← hff, xvals_keep _ _ _ _ (by decide), k.x6, x6₁]
  have hf7 : f .xmm7 = s.xmm .xmm7 := by rw [← hff, xvals_keep _ _ _ _ (by decide), k.x7, x7₁]
  have hout : InRegions s₂.wr (tAddr s₀ true c) 16 := by
    rw [wr₂]
    exact ⟨dstR true s₀, hp.wD, Offset.contains_base _ (by omega_using [hc]) (by omega_using [fD, hc])⟩
  refine WP.block_cons_iff.mpr ⟨{ setX s₂ f with mem := s₂.mem.writeW (tAddr s₀ true c) (f .xmm0) }, ?_, ?_⟩
  · show (setX s₂ f).store128 ((setX s₂ f).ea ⟨.eax, 0⟩) (f .xmm0) = _
    rw [show (setX s₂ f).ea ⟨.eax, 0⟩ = addr (s₂.gpr .eax) 0 from rfl, ed]
    exact ite_eq_left hout
  generalize hs₃ : ({ setX s₂ f with mem := s₂.mem.writeW (tAddr s₀ true c) (f .xmm0) } : State) = s₃
  have hm₃ : s₃.mem = s.mem.writeW (tAddr s₀ true c)
      (XBinOp.eval .pxor (s₂.xmm .xmm0) (s.mem.readW (bAddr s₀ c) 128)) := by rw [← hs₃, ← hf0, ← m₂]
  have hg₃ : s₃.gpr = s₂.gpr := by rw [← hs₃]; rfl
  have hrd₃ : s₃.rd = s₀.rd := by rw [← hs₃, ← rd₂]; rfl
  have hwr₃ : s₃.wr = s₀.wr := by rw [← hs₃, ← wr₂]; rfl
  have hx₃ : s₃.xmm = f := by rw [← hs₃]; rfl
  refine WP.mono (wp_g (Q := fun s' => s'.mem = s₃.mem ∧ s'.rd = s₃.rd ∧ s'.wr = s₃.wr ∧
    (∀ r, r ≠ .esi → r ≠ .eax → r ≠ .ebp → s'.gpr r = s₃.gpr r) ∧ s'.gpr .esi = s₃.gpr .esi + 16 ∧
    s'.gpr .eax = s₃.gpr .eax + 16 ∧ s'.gpr .ebp = s₃.gpr .ebp - 1 ∧ s'.zf = some (s₃.gpr .ebp - 1 == 0)) rfl ?_)
    fun s' hh => ?_
  · refine Wp.wp_addi fun t₁ u₁ => Wp.wp_addi fun t₂ u₂ => Wp.wp_subi fun t₃ u₃ _ z =>
      WP.block_nil ⟨?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₃.mem, u₂.mem, u₁.mem]
    · rw [u₃.rd, u₂.rd, u₁.rd]
    · rw [u₃.wr, u₂.wr, u₁.wr]
    · rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
    · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [z, u₂.other _ (by decide), u₁.other _ (by decide)]
  · obtain ⟨⟨m, rd, wr, g, si, ax, bp, z⟩, x⟩ := hh
    have hf' : Frame [⟨tAddr s₀ true c, 16⟩] s.mem s'.mem := by
      rw [m, hm₃]
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
    have gi : ∀ r, r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
      rw [hg₃, g₂ r h1 h2 h3]
    have ebp' : s.gpr .ebp - 1 = BitVec.ofNat 32 (nBlk s₀ - (c + 1)) := by
      rw [h.ebp, Wp.ofNat_pred (by omega_using [hc])]; congr 1
    have hdB : ∀ o n, o + n ≤ 496 → ∀ r ∈ [(⟨tAddr s₀ true c, 16⟩ : Region)],
        Region.Disjoint ⟨addr (scrP s₀) o, n⟩ r := fun o n hon r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.dDB.sub_left hsub).sub_right (part_sub_reg fB (by omega_using [hon, hB]))).symm
    refine ⟨⟨h.core.of_frame (rs := [⟨tAddr s₀ true c, 16⟩]) ?_ ?_ (by rw [rd, hrd₃, h.rd]) (by rw [wr, hwr₃, h.wr])
      (by rw [x, hx₃, hf6]) (by rw [x, hx₃, hf7]) hf' hl
      (fun o ho => hdB o 16 (by omega_using [ho, show enc.slots = 224 from rfl])) (fun r hr => ?_),
      ?_, rd.trans hrd₃, wr.trans hwr₃,
      h.saved.of_frame hf' (R := ⟨addr (scrP s₀) 464, 16⟩) (fun q hq => ?_) (hdB 464 16 (by decide)),
      h.frame.trans (hf'.sub fun r hr => ⟨dstR true s₀, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩),
      (hf'.readW (Region.contains_self _ _) (hdB 480 16 (by decide)) (by decide)).trans h.pre,
      (blockAt_frame hf' fun r hr => ?_).trans h.ctr, ?_, ?_, ?_, ?_, hc, fun j hj => ?_⟩, ?_⟩
    · rw [g _ (by decide) (by decide) (by decide), gi _ (by decide) (by decide) (by decide)]
    · rw [g _ (by decide) (by decide) (by decide), gi _ (by decide) (by decide) (by decide)]
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.esp]
      exact (hp.aD.sub_left (hp.argSub (i := 1) (.inl (by decide)))).sub_right hsub
    · rw [g _ (by decide) (by decide) (by decide), gi _ (by decide) (by decide) (by decide), h.esp]
    · rcases savedRegs_mem hq with rfl | rfl | rfl | rfl <;>
        exact part_contains fB (by omega_using [hB]) (by decide) (by decide) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.dCD.sub_right hsub
    · rw [g _ (by decide) (by decide) (by decide), hg₃, dx₂, h.edx, BitVec.add_assoc]
      exact congrArg _ (BitVec.ofNat_add _ _).symm
    · rw [si, gi _ (by decide) (by decide) (by decide), h.esi, BitVec.add_assoc]
      exact congrArg _ ((BitVec.ofNat_add _ _).symm.trans (congrArg _ (by omega_using [])))
    · rw [ax, gi _ (by decide) (by decide) (by decide), h.eax, BitVec.add_assoc]
      exact congrArg _ ((BitVec.ofNat_add _ _).symm.trans (congrArg _ (by omega_using [])))
    · rw [bp, gi _ (by decide) (by decide) (by decide), ebp']
    · by_cases ej : j = c
      · subst ej
        rw [ite_eq_left (Nat.lt_succ_self j), m, hm₃, blockAt_writeW_xor, h.src hp hj (Nat.le_refl j), hks]
      · rw [blockAt_frame hf' fun r hr => ?_, h.blocks j hj]
        · by_cases hjc : j < c
          · rw [ite_eq_left hjc, ite_eq_left (by omega_using [hjc])]
          · rw [ite_eq_right hjc, ite_eq_right (by omega_using [hjc, ej])]
        · simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_using [ej]) (by omega_using [fD, hj]) (by omega_using [fD, hc])
    · rw [z, gi _ (by decide) (by decide) (by decide), ebp', Wp.ofNat_beq_zero (by omega_using [fD])]
      exact congrArg some (decide_eq_decide.mpr (by omega_using [hc]))

theorem correct (hp : GPre true s₀ B) (hB : 496 ≤ B) :
    WP isa ctr32To s₀ fun s' => abiPreserved s₀ s' ∧ ctrPost true s₀ s' := by
  have hN : enc.saved + 16 ≤ B := by omega_using [hB, show enc.saved = 464 from rfl]
  obtain ⟨sk, hprep, hcore⟩ := Enc.cryptOk.prep hp.fB hN hp.wB (sched_of hp)
  refine WP.seq (WP.mono (setup_ok Enc.setupOk (args_of hp) hN) fun s₁ ⟨h₁, h6, h7⟩ => ?_)
  refine WP.seq (WP.mono (hprep h₁ h6 h7) fun s₂ ⟨h₂, c₂⟩ => ?_)
  refine WP.seq (WP.mono (ctrArgs_ok hp hB h₂ c₂) fun s₃ ⟨h₃, z₃⟩ => ?_)
  refine WP.seq (WP.mono (Q := CInv B sk s₀ (nBlk s₀)) ?_ fun s₄ h₄ => ?_)
  · refine WP.ite (decide (nBlk s₀ = 0)) (by simp [eval, z₃]) (fun e => ?_) (fun e => ?_)
    · rw [of_decide_eq_true e]; exact WP.block_nil h₃
    · have e0 : nBlk s₀ ≠ 0 := of_decide_eq_false e
      refine WP.loop (M := isa) (fun n s' => ∃ c, n = nBlk s₀ - c ∧ c < nBlk s₀ ∧ CInv B sk s₀ c s')
        (fun n s' ⟨c, hn, hc, i⟩ => ?_) (nBlk s₀) s₃ ⟨0, rfl, by omega_using [e0], h₃⟩
      refine WP.mono (body_ok hp hB hcore hc i) fun s'' ⟨i', z⟩ => ?_
      by_cases e : nBlk s₀ = c + 1
      · exact .inl ⟨by simp [eval, z, e], by rw [e]; exact i'⟩
      · exact .inr ⟨by simp [eval, z, e], nBlk s₀ - (c + 1), by omega_using [hn, hc], c + 1, rfl,
          by omega_using [hc, e], i'⟩
  · refine WP.mono (restore_ok h₄.core.edi h₄.esp hp.fB hN (by rw [h₄.wr]; exact hp.wB) rfl h₄.saved)
      fun s' ⟨m, g⟩ => ⟨⟨g, ?_⟩, ?_, by rw [m]; exact h₄.ctr⟩
    · rw [m]
      refine h₄.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.rC
      · exact hp.rD
      · exact hp.rB
    · rw [m]
      apply List.ext_getElem
      · simp [Spec.Gcm.blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream]
      · intro k h₁ h₂
        have hk : k < nBlk s₀ := by simpa [Spec.Gcm.blocksAt] using h₁
        have hb := h₄.blocks k hk
        rw [ite_eq_left hk] at hb
        simp only [Spec.Gcm.blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream, List.getElem_map,
          List.getElem_range, List.getElem_zipWith, List.length_map, List.length_range]
        exact hb

/-- With a scratch buffer of `B` bytes, in place. -/
theorem ctr32N_correct (hB : 496 ≤ B) (s : State) (hs : (Proof.Aes.ctr32X86N B).pre s) :
    ∃ t s', Exec isa ctr32To s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.ctr32X86N B).post s s' :=
  have hp := CPre.ofN hs
  (correct (hp.gpre (by omega_using [hB])) hB).imp fun _ ⟨s', he, h, h₂, h₃⟩ =>
    ⟨s', he, h, by simpa only [ctrPost, dstP, ↓reduceIte, hp.same] using h₂, h₃⟩

/-- Out of place. -/
theorem ctr32ToN_correct (hB : 496 ≤ B) (s : State) (hs : (Proof.Aes.ctr32ToX86N B).pre s) :
    ∃ t s', Exec isa ctr32To s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.ctr32ToX86N B).post s s' :=
  (correct (GPre.ofToN hs (by omega_using [hB])) hB).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem ctr32_ct : ConstantTime isa (Proof.Aes.ctr32X86N 496).pre (Proof.Aes.ctr32X86N 496).pub ctr32To :=
  VG.Taint.constantTime (A := sseTaint) (ctrToτN 496) (fun _ _ h₁ h₂ hp => ctr_agreeN h₁ h₂ hp) (by taint_decide)

theorem ctr32To_ct : ConstantTime isa (Proof.Aes.ctr32ToX86N 496).pre (Proof.Aes.ctr32ToX86N 496).pub ctr32To :=
  VG.Taint.constantTime (A := sseTaint) (ctrToτN 496) (fun _ _ h₁ h₂ hp => ctrTo_agreeN h₁ h₂ hp) (by taint_decide)

theorem ctr32_ct' : ConstantTime isa Proof.Aes.ctr32X86.pre Proof.Aes.ctr32X86.pub ctr32To :=
  VG.Taint.constantTime (A := sseTaint) (ctrToτN 2048) (fun _ _ h₁ h₂ hp => ctr_agreeN h₁ h₂ hp) (by taint_decide)

theorem ctr32To_ct' : ConstantTime isa Proof.Aes.ctr32ToX86.pre Proof.Aes.ctr32ToX86.pub ctr32To :=
  VG.Taint.constantTime (A := sseTaint) (ctrToτN 2048) (fun _ _ h₁ h₂ hp => ctrTo_agreeN h₁ h₂ hp) (by taint_decide)

/-- The implementation. -/
def variant : Proof.Aes.X86.Ctr32Impl where
  callee := ⟨"vg_aes_ctr32_to_ssse3", ctr32To⟩
  depth := by lit_decide
  stack := by lit_decide
  ok := ctr32N_correct (by decide)
  ct := ctr32_ct'
  nosp := NoSp.of_all (by lit_decide)
  spSafe := Code.all_of_spTest (by lit_decide)
  scrub := by lit_decide
  suffix := "_ssse3"
  features := ["ssse3"]
  okTo := ctr32ToN_correct (by decide)
  ctTo := ctr32To_ct'
  scr := 496
  small := ⟨ctr32N_correct (Nat.le_refl _), ctr32_ct, ctr32ToN_correct (Nat.le_refl _), ctr32To_ct⟩
  expand := Proof.Aes.X86.Ctr32Impl.scalar.expand
  expandDepth := Proof.Aes.X86.Ctr32Impl.scalar.expandDepth
  expandStack := Proof.Aes.X86.Ctr32Impl.scalar.expandStack
  expandOk := Proof.Aes.X86.Ctr32Impl.scalar.expandOk
  expandCt := Proof.Aes.X86.Ctr32Impl.scalar.expandCt
  expandNosp := Proof.Aes.X86.Ctr32Impl.scalar.expandNosp
  expandSpSafe := Proof.Aes.X86.Ctr32Impl.scalar.expandSpSafe
  expandScrub := Proof.Aes.X86.Ctr32Impl.scalar.expandScrub

end VG.Proof.Variants.AesCtr32.X86.Ssse3
