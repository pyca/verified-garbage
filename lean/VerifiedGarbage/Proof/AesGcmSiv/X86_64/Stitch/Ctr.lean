module
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Aes

import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Enc
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM-SIV's sealing loops: counter mode on the groups

`ctr_ok`: `Impl.AesGcmSiv.X86_64Stitch.ctr` enciphers the `r9` blocks at
`r12` (a multiple of 16, at least 16) in counter mode from the counter block
at `rdx`, which it advances: the batches of `dec`, with nothing between their
rounds (`batch_ok`), sixteen blocks a body. It needs what the interleaved
loop needs (`SPre`) and leaves what it leaves but `Y` (`CPost`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.AesGcmSiv.X86_64Stitch (setupK cbody ctr batch storeCtr)
open VG.Proof.Gcm.X86_64.Pclmul (const_ok toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Proof.Gcm.X86_64.Vpclmul (getLsbD_one8)
open VG.Proof.Gcm.X86_64.Stitch (in_rdwr)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Spec.Aes (bytesAt)

/-- What counter mode on the groups leaves: the data enciphered, the counter
block advanced, nothing else written but the working space. -/
structure CPost (s₀ s : State) : Prop where
  data : ∀ k < nb s₀, bytesAt s.mem (bAddr s₀ k) 16 = ctb s₀ k
  ctr : bytesAt s.mem (cp s₀) 16 = Spec.GcmSiv.counterBlock (icb s₀) (nb s₀)
  frame : Frame [cR s₀, dR s₀, pR s₀] s₀.mem s.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `vinserti128 r, r, r, 1`: the low lane in both. -/
theorem insSelf_ok (r : XReg) (s : State) :
    WP isa (.block [.vop (.vinserti128 r r r 1)]) s fun s' =>
      (∀ l < 2, s'.lane r l = s.lane r 0) ∧ YFrame [r] s s' := by
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ⟨fun l hl => ?_, rfl, rfl, rfl, rfl, fun r' hr l hl => ?_⟩⟩
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [VOp.exec, State.setV, State.lane]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [hr, VOp.exec, State.setV, State.lane]

/-- `setupK` after the mask. -/
abbrev setupKT : List Instr :=
  [.movImm64 .r10 1, .vop (.vmovq .xmm15 .r10),
   .vmovdquLoad .l128 .xmm14 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rdx 0),
   .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm15), .vop (.vinserti128 .xmm14 .xmm14 .xmm13 1),
   .movImm64 .r10 2, .vop (.vmovq .xmm15 .r10), .vop (.vinserti128 .xmm15 .xmm15 .xmm15 1),
   .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi),
   .mov .rax (.reg .rdx), .mov .rdx (.reg .r12)]

theorem setupKT_ok (s : State) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block setupKT) s fun s' =>
      s'.lane .xmm14 0 = s.mem.readW (s.gpr .rdx) 128 ∧
      s'.lane .xmm14 1 = XBinOp.eval .paddd (s.mem.readW (s.gpr .rdx) 128) ((0 : BitVec 64) ++ BitVec.ofNat 64 1) ∧
      (∀ l < 2, s'.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two) ∧
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rax = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r12 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hc' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hc
  apply WP.of_runBlock
  simp only [setupKT, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hc', VBinOp.sse, getLsbD_one8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun l hl => ?_, ?_, trivial, trivial, fun r h1 h2 h3 => ?_,
    fun r h13 h14 h15 l hl => ?_, trivial, trivial, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; rfl
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · bv_omega
  · simp [h1, h2, h3]
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h13, h14, h15]

/-- `add rdx, 256; sub r9, 16`. -/
theorem nextC_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
        s'.zf = some ((s.gpr .r9 - 16) == 0) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.lane r l = s.lane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- The counter loop's state: `e` groups enciphered. -/
structure CInv (s₀ : State) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  rdx : s.gpr .rdx = dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * e)
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r

theorem setupK_ok {s₀ : State} (hp : SPre s₀) : WP isa (.block setupK) s₀ (CInv s₀ 0) := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  rw [show setupK = Impl.Gcm.X86_64.Pclmul.const .xmm0 revMask ++
    ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1)] : List Instr) ++ setupKT from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (insSelf_ok .xmm0 s₁) fun s₂ ⟨v₂, f₂⟩ => ?_
  have g₂ : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [f₂.gpr, o₁.gpr r hr]
  have m₂ : s₂.mem = s₀.mem := by rw [f₂.mem, o₁.mem]
  refine WP.mono (setupKT_ok s₂ (by rw [f₂.wr, o₁.wr, g₂ _ (by decide)]; exact hp.c_in))
    fun s₃ ⟨c140, c141, c15, r10, rax, rdx, gk, lk, m₃, rd₃, wr₃⟩ => ?_
  have hd : s₂.mem.readW (s₂.gpr .rdx) 128 = d₀ s₀ := by rw [g₂ _ (by decide), m₂]
  refine ⟨⟨Nat.zero_le _, fun l hl => ?_, fun l hl => ?_, c15, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_⟩,
    by rw [rdx, g₂ _ (by decide), Nat.mul_zero, BitVec.add_zero],
    by rw [gk _ (by decide) (by decide) (by decide), g₂ _ (by decide), Nat.mul_zero, Nat.sub_zero]; simp,
    by rw [rax, g₂ _ (by decide)], fun r h1 h2 _ h4 => by rw [gk r h1 h2 h4, g₂ r h1]⟩
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [c140, hd, Nat.mul_zero, ctrX₀]
    · rw [c141, hd]
      conv => lhs; rw [← ctrX₀ s₀, ctrX, paddd_one, ← BitVec.ofNat_add]
  · rw [lk _ (by decide) (by decide) (by decide) l hl, v₂ l hl]; show s₁.xmm .xmm0 = _; rw [c₁]
  · rw [gk _ (by decide) (by decide) (by decide), g₂ _ (by decide)]
  · rw [gk _ (by decide) (by decide) (by decide), g₂ _ (by decide)]
  · rw [r10, g₂ _ (by decide), g₂ _ (by decide)]
  · rw [m₃, m₂]; exact Frame.refl _ _
  · rw [m₃, m₂]; simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false]
  · rw [rd₃, f₂.rd, o₁.rd]
  · rw [wr₃, f₂.wr, o₁.wr]

theorem cbody_ok {s₀ : State} (hp : SPre s₀) {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State}
    (hI : CInv s₀ e s) :
    WP isa cbody s fun s' => CInv s₀ (e + 1) s' ∧ s'.zf = some (decide (nb s₀ - 16 * (e + 1) = 0)) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hw := hp.wrap_d
  have hrdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * e := by
    rw [hI.rdx, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 256 * e) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ YFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩
  refine WP.seq (WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * e) (j := 0) (by omega) hI.a
    (by rw [hrdx]; omega) trivial) fun s₁ ⟨hA₁, _, hg₁, _, _⟩ => ?_)
  refine WP.seq (WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * e + 8) (j := 4) (by omega) hA₁
    (by rw [hg₁, hrdx]; omega) trivial) fun s₂ ⟨hA₂, _, hg₂, _, _⟩ => ?_)
  refine WP.mono (nextC_ok s₂) fun s' ⟨frdx, fr9, fzf, fg, fl, fm, frd, fwr⟩ => ?_
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, hg₁]
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1)) := by
    rw [hg₂, hg₁, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
  refine ⟨⟨?_, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4⟩, ?_⟩
  · rw [show 16 * (e + 1) = 16 * e + 8 + 8 by omega]
    exact ⟨hA₂.le, fun l hl => by rw [fl]; exact hA₂.ctr l hl, fun l hl => by rw [fl]; exact hA₂.msk l hl,
      fun l hl => by rw [fl]; exact hA₂.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  · rw [frdx, hg₂, hg₁, hI.rdx, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, add_ofNat_assoc]
    congr 2
  · rw [fzf, hr9]
    simp only [Option.some.injEq]
    by_cases h : nb s₀ - 16 * (e + 1) = 0
    · simp [h]
    · simp only [h, decide_false]
      exact beq_false_of_ne fun h' => h (by
        have := congrArg BitVec.toNat h'
        rwa [toNat_ofNat_lt (by omega)] at this)

/-- The counter block stored, and the upper lanes cleared. -/
theorem ctrFin_ok {s₀ : State} (hp : SPre s₀) {e : Nat} (he : nb s₀ = 16 * e) {s : State} (hI : CInv s₀ e s) :
    WP isa (.block (storeCtr ++ ([.vop .vzeroupper] : List Instr))) s (CPost s₀) := by
  have hw := hp.wrap_d
  rw [WP.block_append_iff]
  refine WP.mono (storeCtr_ok s (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hI.rax] at m₁
  have fC : Frame [cR s₀] s.mem s₁.mem := by rw [m₁]; exact frame_write16 _ _ _
  have cD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  refine ⟨fun k hk => ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, by show s₁.rd = _; rw [rd₁, hI.a.rd],
    by show s₁.wr = _; rw [wr₁, hI.a.wr]⟩
  · show bytesAt s₁.mem _ 16 = _
    rw [Proof.AesGcm.X86_64.bytesAt_frame fC (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cD k hk) (by decide),
      hI.a.blocks k hk]
    simp only [show k < 16 * e by omega, ite_true]
  · show bytesAt s₁.mem (cp s₀) 16 = _
    rw [m₁, bytesAt_writeW128, hI.a.ctr 0 (by decide), Nat.add_zero, he, le16_ctrX (rest₀ s₀)]
  · show Frame _ s₀.mem s₁.mem
    rw [m₁]
    exact (hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)
  · show s₁.gpr r = _
    rw [g₁]; exact hI.gpr r h1 h2 h3 h4

/-- Counter mode on the groups. -/
theorem ctr_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) : WP isa ctr s₀ (CPost s₀) := by
  have h16 := hp.nb16
  refine WP.seq (WP.mono (setupK_ok hp) fun s₁ hI₁ => WP.seq ?_)
  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ CInv s₀ e s
  have hstep : ∀ m s, I m s → WP isa cbody s (fun s' =>
      (eval .ne s' = some false ∧ ∃ e, nb s₀ = 16 * e ∧ CInv s₀ e s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI⟩
    refine WP.mono (cbody_ok hp he hI) fun s' ⟨hI', hzf⟩ => ?_
    by_cases h0 : nb s₀ - 16 * (e + 1) = 0
    · exact .inl ⟨by simp only [eval, hzf, h0, decide_true, Option.map_some, Bool.not_true],
        e + 1, by omega, hI'⟩
    · exact .inr ⟨by simp only [eval, hzf, h0, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 1), by omega, e + 1, rfl, by omega, hI'⟩
  exact WP.mono (WP.loop (M := isa) I hstep (nb s₀ - 16 * 0) s₁ ⟨0, rfl, by omega, hI₁⟩)
    fun s ⟨e, he, hI⟩ => ctrFin_ok hp he hI

end VG.Proof.AesGcmSiv.X86_64.Stitch
