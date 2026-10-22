module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Pipeline
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract

/-! ## Ready -/

@[expose] public section

section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

/-- The state after setup and before the first AES or hash batch. -/
structure Ready (s₀ : State) (P : Nat → Block) (s : State) : Prop where
  env : Env s₀ P s
  templates : Templates s₀ 0 0 s.mem
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + 8
  cursor : s.gpr .rdx = dp s₀
  remaining : s.gpr .r9 = s₀.gpr .r9
  hash : s.lane .xmm2 0 = y₀ s₀
  frame : Frame [pR s₀] s₀.mem s.mem
  /-- The byte-reversal mask, and the counter block as loaded, from which
  `regCounters` builds the first batch's counters. -/
  mask : s.lane .xmm0 0 = revMask
  base : XBinOp.eval .pshufb (s.lane .xmm7 0) revMask = cb s₀

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Cursor -/
section

/-! # Public cursor updates and loop conditions -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64

theorem next8_ok (s : State) (n : BitVec 32) :
    WP isa (.block [.alu .add .rdx (.imm 128), .alu .sub .r9 (.imm 8), .alu .cmp .r9 (.imm n)]) s
      fun t => t.gpr .rdx = s.gpr .rdx + 128 ∧ t.gpr .r9 = s.gpr .r9 - 8 ∧
        t.cf = some (decide ((s.gpr .r9 - 8).toNat < (n.signExtend 64).toNat)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → t.gpr r = s.gpr r) ∧ (∀ r l, t.lane r l = s.lane r l) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

theorem cmp8_ok (s : State) (n : BitVec 32) :
    WP isa (.block [.alu .cmp .r9 (.imm n)]) s fun t =>
      t.cf = some (decide ((s.gpr .r9).toNat < (n.signExtend 64).toNat)) ∧ YFrame [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, isa, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Dispatch -/
section

/-! # Selecting a fixed schedule from the public round count -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch

open VG.X86_64.RegUpd
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at)

/-- `t` is `s` but for `rax` and the flags. -/
structure RaxStep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  lane : ∀ r, ∀ l < 2, t.lane r l = s.lane r l

theorem key_zf (p : Addr) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((p + BitVec.ofNat 64 a) - (p + BitVec.ofNat 64 b) == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have e2 := congrArg (· + (p + BitVec.ofNat 64 b)) e
    simp only [BitVec.sub_add_cancel] at e2
    have e3 : BitVec.ofNat 64 a = BitVec.ofNat 64 b := (BitVec.add_right_inj p).mp (by simpa using e2)
    have := congrArg BitVec.toNat e3
    simp only [BitVec.toNat_ofNat, Nat.reducePow] at this ha hb
    omega

/-- The first test of the key size: `r10` against `rdi + 160`. -/
private theorem keyCmp10_ok (s : State) {n : Nat} (hn : n < 2 ^ 32)
    (h10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * n)) :
    WP isa (.block [.mov .rax (.reg .rdi), .alu .add .rax (.imm 160), .alu .cmp .r10 (.reg .rax)]) s
      fun t => t.zf = some (decide (n = 10)) ∧ t.gpr .rax = s.gpr .rdi + BitVec.ofNat 64 160 ∧
        RaxStep s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  have e : BitVec.signExtend 64 (160 : BitVec 32) = BitVec.ofNat 64 160 := by decide
  refine ⟨?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, fun _ _ _ => rfl⟩⟩
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, reduceCtorEq, ite_false, h10, e]
    rw [key_zf _ (by simp only [Nat.reducePow]; omega) (by decide)]
    simp only [Option.some.injEq]
    exact decide_eq_decide.mpr (by omega)
  · simp [gpr_setReg]
  · simp [gpr_setReg, hr]

/-- The second: `r10` against `rdi + 192`. -/
private theorem keyCmp12_ok (t : State) {p : Addr} {n : Nat} (hn : n < 2 ^ 32)
    (h10 : t.gpr .r10 = p + BitVec.ofNat 64 (16 * n)) (hax : t.gpr .rax = p + BitVec.ofNat 64 160) :
    WP isa (.block [.alu .add .rax (.imm 32), .alu .cmp .r10 (.reg .rax)]) t
      fun u => u.zf = some (decide (n = 12)) ∧ RaxStep t u := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e : BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 32 := by decide
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, fun _ _ _ => rfl⟩⟩
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, reduceCtorEq, ite_false, h10,
      hax, e, Offset.add_add]
    rw [key_zf _ (by simp only [Nat.reducePow]; omega) (by decide)]
    simp only [Option.some.injEq]
    exact decide_eq_decide.mpr (by omega)
  · simp [gpr_setReg, hr]

/-- The setup, then the loop for the key size, read back from where the
setup saved it. -/
theorem dispatch_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {su : List Instr} {a b c : Prog isa}
    {R Q : State → Prop} (hsu : WP isa (.block su) s₀ R)
    (hR : ∀ s, R s → s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr s₀))
    (ha : ∀ s t, R s → RaxStep s t → nr s₀ = 10 → WP isa a t Q)
    (hb : ∀ s t, R s → RaxStep s t → nr s₀ = 12 → WP isa b t Q)
    (hc : ∀ s t, R s → RaxStep s t → nr s₀ = 14 → WP isa c t Q) :
    WP isa (Impl.Gcm.X86_64.StitchAvx8.dispatch su a b c) s₀ Q := by
  have hn : nr s₀ < 2 ^ 32 := by rcases hp.rounds with h | h | h <;> omega
  unfold Impl.Gcm.X86_64.StitchAvx8.dispatch
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono hsu fun s hs => ?_
  refine WP.mono (keyCmp10_ok s hn (hR s hs)) fun t ⟨hz, hax, ht⟩ => ?_
  refine WP.ite (decide (nr s₀ = 10)) (by simp only [eval, hz]) (fun he => ha s t hs ht (by simpa using he))
    (fun he => ?_)
  have h10 : nr s₀ ≠ 10 := by simpa using he
  have hr10 : t.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr s₀) := by
    rw [ht.gpr _ (by decide)]; exact hR s hs
  refine WP.seq (WP.mono (keyCmp12_ok t hn hr10 hax) fun u ⟨hz', hu⟩ => ?_)
  have ht' : RaxStep s u := ⟨fun r hr => by rw [hu.gpr r hr, ht.gpr r hr], by rw [hu.mem, ht.mem],
    by rw [hu.rd, ht.rd], by rw [hu.wr, ht.wr], fun r l hl => by rw [hu.lane r l hl, ht.lane r l hl]⟩
  refine WP.ite (decide (nr s₀ = 12)) (by simp only [eval, hz'])
    (fun he => hb s u hs ht' (by simpa using he)) (fun he => ?_)
  have h12 : nr s₀ ≠ 12 := by simpa using he
  exact hc s u hs ht' (by rcases hp.rounds with he | he | he <;> omega)

/-- What the setup leaves holds after reading the key size back. -/
theorem Ready.rax {s₀ s t : State} {P : Nat → VG.Spec.Gcm.Block} (h : Ready s₀ P s) (ht : RaxStep s t) :
    Ready s₀ P t := by
  have he := h.env
  have hm := ht.mem
  refine ⟨⟨by rw [ht.gpr _ (by decide)]; exact he.rdi, by rw [ht.gpr _ (by decide)]; exact he.rsi,
    by rw [ht.gpr _ (by decide)]; exact he.rcx, by rw [ht.gpr _ (by decide)]; exact he.r11,
    by rw [ht.gpr _ (by decide)]; exact he.r10,
    fun r h1 h2 h3 h4 h5 h6 => by rw [ht.gpr r h1]; exact he.other r h1 h2 h3 h4 h5 h6,
    by rw [hm]; exact he.frame, by rw [hm]; exact he.powers, by rw [hm]; exact he.mask,
    by rw [hm]; exact he.poly, by rw [hm]; exact he.rounds, by rw [hm]; exact he.data,
    by rw [hm]; exact he.saved, by rw [ht.rd]; exact he.rd, by rw [ht.wr]; exact he.wr⟩,
    by rw [hm]; exact h.templates, by rw [ht.gpr _ (by decide)]; exact h.counter,
    by rw [ht.gpr _ (by decide)]; exact h.cursor, by rw [ht.gpr _ (by decide)]; exact h.remaining,
    by rw [ht.lane _ _ (by decide)]; exact h.hash, by rw [hm]; exact h.frame,
    by rw [ht.lane _ _ (by decide)]; exact h.mask, by rw [ht.lane _ _ (by decide)]; exact h.base⟩

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Finish -/
section

/-! # Writing the final counter and hash and restoring the entry registers -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (finish)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32)

structure FinishPost (s₀ start : State) (n : Nat) (y : Block) (s : State) : Prop where
  counter : blockAt s.mem (cp s₀) = Nat.repeat inc32 n (cb s₀)
  hash : blockAt s.mem (yp s₀) = y
  frame : Frame [cR s₀, yR s₀] start.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finish_ok {s₀ s : State} {lo : Nat} {P : Nat → Block} (hp : SPre s₀ lo) (hE : Env s₀ P s)
    (n : Nat) (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (n + 8)) :
    WP isa (.block finish) s (FinishPost s₀ s n (s.lane .xmm2 0)) := by
  have hcode : finish = finishHead ++
      ([.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
        .vmovdquStore .l128 (at_ .rcx 0) .xmm2] : List Instr) ++
      [.vop .vzeroupper] ++ restoreEntry := rfl
  rw [hcode, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (finishHead_ok s (by
    rw [hE.wr, hE.rsi]; exact in_sub hp.c_in (off := 12) (by decide)) (by
    rw [hE.rd, hE.wr, hE.r11]; exact in_rdwr (in_sub hp.p_in (off := 768) (by decide))) (by
    rw [hE.r11, hE.rsi]
    exact (hp.p_c.sub_left (Offset.sub_base (pp s₀) (d := 768) (n := 16) (k := 1024) (by decide))).sub_right
      (Offset.sub_base (cp s₀) (d := 12) (n := 4) (k := 16) (by decide)) |>.sep
      (Region.contains_self _ _) (Region.contains_self _ _)))
    fun t ⟨htM, ht0, htG, htX, htR, htW⟩ => ?_
  have hnum : (s.gpr .r8).setWidth 32 - 8 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 n := by
    rw [hv, BitVec.ofNat_add]
    change ((cb s₀).extractLsb' 0 32 + (BitVec.ofNat 32 n + 8)) - 8 = _
    rw [← BitVec.add_assoc, BitVec.add_sub_cancel]
  rw [hE.rsi, hnum] at htM
  have fct : Frame [cR s₀] s.mem t.mem := by
    rw [htM]
    exact (Frame.refl _ _).writeW List.mem_cons_self _
      (Offset.contains_base (cp s₀) (d := 12) (n := 4) (k := 16) (by decide) (by decide))
  have hcb : blockAt s.mem (cp s₀) = cb s₀ := blockAt_frame hE.frame (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.d_c.symm
    · exact hp.p_c.symm)
  have ct : blockAt t.mem (cp s₀) = Nat.repeat inc32 n (cb s₀) := by
    rw [htM]
    have hc := refreshCounter_ok s.mem (cp s₀) (cb s₀) 0 n hcb
    simpa only [Nat.zero_add] using hc
  rw [WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx t (by
    rw [ht0, hE.r11]; exact hE.mask) (by
    rw [htW, hE.wr, htG _ (by decide) (by decide), hE.rcx]; exact hp.y_in))
    fun u ⟨huM, huG, huR, huW, _⟩ => ?_
  rw [htG _ (by decide) (by decide), hE.rcx, htX _ (by decide) 0 (by decide)] at huM
  have fyu : Frame [yR s₀] t.mem u.mem := by
    rw [huM]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have fu : Frame [cR s₀, yR s₀] s.mem u.mem :=
    (fct.mono (by simp)).trans (fyu.mono (by simp))
  have py : ∀ r ∈ [cR s₀, yR s₀], (pR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.p_c
    · exact hp.p_y
  have saved : ∀ d, d + 8 ≤ 1024 → u.mem.readW (pp s₀ + BitVec.ofNat 64 d) 64 =
      s.mem.readW (pp s₀ + BitVec.ofNat 64 d) 64 := fun d hd =>
    fu.readW (r := pR s₀) (Offset.contains_base _ hd (by omega)) py (by decide)
  have ur11 : u.gpr .r11 = pp s₀ := by rw [huG, htG _ (by decide) (by decide), hE.r11]
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨VOp.exec .vzeroupper u, rfl, ?_⟩
  rw [WP.block_nil_iff]
  refine WP.mono (restoreEntry_ok (VOp.exec .vzeroupper u)
    (by change InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 808) 8
        rw [huR, huW, htR, htW, hE.rd, hE.wr, ur11]
        exact in_rdwr (in_sub hp.p_in (off := 808) (by decide)))
    (by change InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 800) 8
        rw [huR, huW, htR, htW, hE.rd, hE.wr, ur11]
        exact in_rdwr (in_sub hp.p_in (off := 800) (by decide))))
    fun v ⟨hv8, hvi, hvG, hvM, hvR, hvW⟩ => ?_
  change v.gpr .r8 = u.mem.readW (u.gpr .r11 + BitVec.ofNat 64 808) 64 at hv8
  change v.gpr .rsi = u.mem.readW (u.gpr .r11 + BitVec.ofNat 64 800) 64 at hvi
  change v.mem = u.mem at hvM
  refine ⟨?_, ?_, hvM ▸ fu, ?_, ?_, ?_⟩
  · rw [hvM]
    exact (blockAt_frame fyu (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.c_y)).trans ct
  · rw [hvM, huM, VG.Proof.Gcm.X86_64.blockAt_store]
  · intro r hax hdx h9 h10
    by_cases h8 : r = .r8
    · subst r
      rw [hv8, ur11, saved 808 (by decide)]; exact hE.data
    by_cases hi : r = .rsi
    · subst r
      rw [hvi, ur11, saved 800 (by decide)]; exact hE.rounds
    · rw [hvG r h8 hi]
      change u.gpr r = s₀.gpr r
      rw [huG, htG r hax h8]
      exact hE.other r hax hdx h8 h9 h10 hi
  · exact hvR.trans (huR.trans (htR.trans hE.rd))
  · exact hvW.trans (huW.trans (htW.trans hE.wr))

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## SetupPrefix -/
section

/-! # Establishing the batch environment from the saved entry state -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (setupC)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt)

theorem setupPrefix_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) (s : State) (P : Nat → Block)
    (hg : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r)
    (hm : Frame [pR s₀] s₀.mem s.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (h0 : s.lane .xmm0 0 = revMask) (h1 : s.lane .xmm1 0 = poly)
    (hP : ∀ k < 8, s.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128 = P k)
    (hsv : s.mem.readW (pp s₀ + 816) 64 = s₀.mem.readW (pp s₀ + 816) 64) :
    WP isa (.block (setupC ++ metaCode ++ counterHead)) s fun t =>
      Env s₀ P t ∧ Frame [pR s₀] s₀.mem t.mem ∧
      t.gpr .rdx = dp s₀ ∧ t.gpr .r9 = s₀.gpr .r9 ∧
      (t.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 ∧
      XBinOp.eval .pshufb (t.lane .xmm7 0) revMask = cb s₀ ∧ t.lane .xmm2 0 = y₀ s₀ ∧
      t.lane .xmm0 0 = revMask := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setupC_ok s h0 (by rw [hwr, hg _ (by decide)]; exact hp.y_in))
    fun u ⟨hyu, hu10, hax, hdx, hgu, hxu, hmu, hrdu, hwru⟩ => ?_
  have gu : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → u.gpr r = s₀.gpr r :=
    fun r hax hdx h10 => (hgu r hax hdx h10).trans (hg r hax)
  have gu11 : u.gpr .r11 = pp s₀ := gu _ (by decide) (by decide) (by decide)
  have gu10 : u.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀) := by
    rw [hu10, hg _ (by decide), hg _ (by decide)]
  have guax : u.gpr .rax = cp s₀ := hax.trans (hg _ (by decide))
  have gudx : u.gpr .rdx = dp s₀ := hdx.trans (hg _ (by decide))
  have hmu0 : Frame [pR s₀] s₀.mem u.mem := hmu ▸ hm
  rw [WP.block_append_iff]
  refine WP.mono (meta_ok u
    (by rw [hwru, hwr, gu11]; exact in_sub hp.p_in (off := 768) (by decide))
    (by rw [hwru, hwr, gu11]; exact in_sub hp.p_in (off := 784) (by decide))
    (by rw [hwru, hwr, gu11]; exact in_sub hp.p_in (off := 808) (by decide))
    (by rw [hwru, hwr, gu11]; exact in_sub hp.p_in (off := 800) (by decide)))
    fun v ⟨hmv, hgv, hxv, hrdv, hwrv⟩ => ?_
  have fm : Frame [metaR u] u.mem v.mem := hmv ▸ meta_frame u
  have fmv : Frame [pR s₀] s₀.mem v.mem := hmu0.trans (fm.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨pR s₀, List.mem_singleton_self _, by
      simpa only [metaR, gu11] using (Offset.sub_base (pp s₀) (d := 768) (n := 48) (k := 1024) (by decide))⟩)
  have gvax : v.gpr .rax = cp s₀ := by rw [hgv]; exact guax
  have vcb : blockAt v.mem (cp s₀) = cb s₀ := blockAt_frame fmv (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.p_c.symm)
  refine WP.mono (counterHead_ok v (by
    rw [hrdv, hwrv, hrdu, hwru, hrd, hwr, gvax, BitVec.add_zero]
    exact in_rdwr hp.c_in) (by
    rw [hrdv, hwrv, hrdu, hwru, hrd, hwr, gvax]
    exact in_rdwr (in_sub hp.c_in (off := 12) (by decide))))
    fun t ⟨hti, ht8, ht7, hgt, hxt, hmt, hrdt, hwrt⟩ => ?_
  have gt : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → r ≠ .rsi → r ≠ .r8 →
      t.gpr r = s₀.gpr r := by
    intro r hax hdx h10 hsi h8
    rw [hgt r hsi h8, hgv]; exact gu r hax hdx h10
  have ft : Frame [pR s₀] s₀.mem t.mem := hmt ▸ fmv
  have ep : Env s₀ P t := by
    constructor
    · exact gt _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [hti, gvax]
    · exact gt _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact gt _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [hgt _ (by decide) (by decide), hgv]; exact gu10
    · intro r hax hdx h8 h9 h10 hsi; exact gt r hax hdx h10 hsi h8
    · exact ft.mono (by simp)
    · intro k hk
      rw [hmt]
      have he : v.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128 =
          u.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128 :=
        fm.readW (r := ⟨pp s₀ + BitVec.ofNat 64 (128 + 16 * k), 16⟩)
          (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
          (by intro r hr; simp only [List.mem_singleton] at hr; subst r
              rw [metaR, gu11]
              exact Offset.disjoint (pp s₀) (by omega) (by omega) (by decide)) (by decide)
      rw [he, hmu]; exact hP k hk
    · rw [hmt, hmv, ← gu11]
      exact (meta_mask u).trans ((hxu _ (by decide) 0 (by decide)).trans h0)
    · rw [hmt, hmv, ← gu11]
      exact (meta_poly u).trans ((hxu _ (by decide) 0 (by decide)).trans h1)
    · rw [hmt, hmv, ← gu11]
      exact (meta_rounds u).trans (gu _ (by decide) (by decide) (by decide))
    · rw [hmt, hmv, ← gu11]
      exact (meta_data u).trans gudx
    · rw [hmt, hmv, ← gu11]
      exact (meta_saved u).trans (by rw [hmu, gu11]; exact hsv)
    · exact hrdt.trans (hrdv.trans (hrdu.trans hrd))
    · exact hwrt.trans (hwrv.trans (hwru.trans hwr))
  refine ⟨ep, ft, ?_, gt _ (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_⟩
  · rw [hgt _ (by decide) (by decide), hgv]; exact gudx
  · rw [ht8, gvax, VG.Proof.Aes.X86_64.icb_lo, vcb]
  · rw [ht7, gvax, BitVec.add_zero, ← blockAt_eq]; exact vcb
  · rw [hxt _ (by decide), hxv, hyu, hg _ (by decide)]
    exact blockAt_frame hm (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.p_y.symm)
  · rw [hxt _ (by decide), hxv]; exact (hxu _ (by decide) 0 (by decide)).trans h0

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Seeds -/
section

/-! # Seeding the first eight counter templates -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt inc32)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (prepCounter)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)

def Seeded (s₀ : State) (n : Nat) (m : Mem) : Prop :=
  ∀ i < 8, blockAt m (templateAddr s₀ i) = Nat.repeat inc32 (if i < n then i else 0) (cb s₀)

theorem Seeded.done {s₀ : State} {m : Mem} (h : Seeded s₀ 8 m) : Templates s₀ 0 0 m := by
  intro i hi
  simpa only [hi, ite_true, Nat.zero_add, Nat.not_lt_zero, ite_false, Nat.add_zero] using h i hi

theorem copyTemplate_ok {s₀ s : State} {P : Nat → Block} {lo : Nat} (hp : SPre s₀ lo)
    (hE : Env s₀ P s) (i : Nat) (hi : i < 8)
    (hC : XBinOp.eval .pshufb (s.lane .xmm7 0) revMask = cb s₀) :
    WP isa (.block [.vmovdquStore .l128 (at_ .r11 (640 + 16 * i)) .xmm7]) s fun t =>
      Env s₀ P t ∧ blockAt t.mem (templateAddr s₀ i) = cb s₀ ∧ BufferFrame s t ∧
      Frame [⟨templateAddr s₀ i, 16⟩] s.mem t.mem := by
  have hw : InRegions s.wr (s.ea (at_ .r11 (640 + 16 * i))) 16 := by
    rw [VG.Proof.Aes.X86_64.AesNi.ea_at, BitVec.ofInt_natCast, hE.wr, hE.r11]
    exact in_sub hp.p_in (by omega)
  have hw' : InRegions s.wr (pp s₀ + BitVec.ofNat 64 (640 + 16 * i)) 16 := by
    simpa only [VG.Proof.Aes.X86_64.AesNi.ea_at, BitVec.ofInt_natCast, hE.r11] using hw
  rw [WP.block_cons_iff]
  refine ⟨s.setMem (s.mem.writeW (templateAddr s₀ i) (s.lane .xmm7 0)), ?_, ?_⟩
  · simp only [exec, isa, State.store128_eq,
      VG.Proof.Aes.X86_64.AesNi.ea_at, BitVec.ofInt_natCast, hE.r11, hw', ite_true]
    rfl
  have hf : BufferFrame s (s.setMem (s.mem.writeW (templateAddr s₀ i) (s.lane .xmm7 0))) :=
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have hm : Frame [⟨templateAddr s₀ i, 16⟩] s.mem
      (s.mem.writeW (templateAddr s₀ i) (s.lane .xmm7 0)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  refine WP.block_nil ⟨hE.buffer hf (hm.sub fun r hr => ?_), ?_, hf, hm⟩
  · simp only [List.mem_singleton] at hr
    subst r
    exact ⟨workR s₀, List.mem_singleton_self _,
      Offset.sub (pp s₀) (d := 640 + 16 * i) (e := 512) (n := 16) (k := 256) (by omega) (by omega)⟩
  · rw [State.setMem_mem, blockAt_eq, Mem.readW_writeW_self s.mem _ 16 _ (by decide)]
    exact hC

theorem copyTemplates_ok {s₀ : State} {P : Nat → Block} {lo : Nat} (hp : SPre s₀ lo)
    (s : State) (hE : Env s₀ P s)
    (hC : XBinOp.eval .pshufb (s.lane .xmm7 0) revMask = cb s₀)
    (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).map fun i =>
      .vmovdquStore .l128 (at_ .r11 (640 + 16 * i)) .xmm7)) s fun t =>
      Env s₀ P t ∧ (∀ i < n, blockAt t.mem (templateAddr s₀ i) = cb s₀) ∧
      BufferFrame s t ∧ Frame [counterR s₀] s.mem t.mem := by
  induction n with
  | zero => exact WP.block_nil ⟨hE, fun _ h => (Nat.not_lt_zero _ h).elim, .refl _, .refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hEt, hTt, hf, hm⟩ => ?_
    simp only [List.map_cons, List.map_nil]
    refine WP.mono (copyTemplate_ok hp hEt n (by omega) (by rw [hf.lane]; exact hC))
      fun u ⟨hEu, hTu, hf', hm'⟩ => ?_
    refine ⟨hEu, fun i hi => ?_, hf.trans hf', hm.trans (hm'.sub fun r hr => ?_)⟩
    · by_cases he : i = n
      · subst i; exact hTu
      · exact (VG.Proof.Aes.X86_64.AesNi.blockAt_frame hm' (by
          intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact Offset.disjoint (pp s₀) (d := 640 + 16 * i) (e := 640 + 16 * n)
            (n := 16) (k := 16) (by omega) (by omega) (by omega))).trans (hTt i (by omega))
    · simp only [List.mem_singleton] at hr; subst r
      exact ⟨counterR s₀, List.mem_singleton_self _,
        Offset.sub (pp s₀) (d := 640 + 16 * n) (e := 640) (n := 16) (k := 128) (by omega) (by omega)⟩

theorem seedTemplate_ok {s₀ s : State} {P : Nat → Block} {lo : Nat} (hp : SPre s₀ lo)
    (hE : Env s₀ P s) (n : Nat) (hn : n < 8) (hT : Seeded s₀ n s.mem)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32) :
    WP isa (.block (prepCounter n)) s fun t =>
      Env s₀ P t ∧ Seeded s₀ (n + 1) t.mem ∧ BufferFrame s t ∧
      Frame [⟨pp s₀ + BitVec.ofNat 64 (652 + 16 * n), 4⟩] s.mem t.mem := by
  refine WP.mono (prepCounter_ok s n (by
    rw [hE.wr, hE.r11]; exact in_sub hp.p_in (by omega))) fun t ⟨hm, hf⟩ => ?_
  rw [hE.r11, hv] at hm
  have hF : Frame [⟨pp s₀ + BitVec.ofNat 64 (652 + 16 * n), 4⟩] s.mem t.mem := by
    rw [hm]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  refine ⟨hE.buffer hf (hF.sub fun r hr => ?_), ?_, hf, hF⟩
  · simp only [List.mem_singleton] at hr; subst r
    exact ⟨workR s₀, List.mem_singleton_self _,
      Offset.sub (pp s₀) (d := 652 + 16 * n) (e := 512) (n := 4) (k := 256) (by omega) (by omega)⟩
  · intro i hi
    by_cases he : i = n
    · subst i
      have htn : blockAt s.mem (templateAddr s₀ n) = Nat.repeat inc32 0 (cb s₀) := by
        simpa only [Nat.lt_irrefl, ite_false] using hT n hn
      rw [hm, ← templateWord]
      simpa only [Nat.zero_add, Nat.lt_add_one, Nat.le_refl, ite_true] using
        refreshCounter_ok s.mem (templateAddr s₀ n) (cb s₀) 0 n htn
    · have hk : (if i < n + 1 then i else 0) = (if i < n then i else 0) := by
        split_ifs <;> omega
      rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hF (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact Offset.disjoint (pp s₀) (by omega) (by omega) (by omega)), hk]
      exact hT i hi

theorem seedTemplates_ok {s₀ : State} {P : Nat → Block} {lo : Nat} (hp : SPre s₀ lo)
    (s : State) (hE : Env s₀ P s) (hT : Seeded s₀ 0 s.mem)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32) (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).flatMap prepCounter)) s fun t =>
      Env s₀ P t ∧ Seeded s₀ n t.mem ∧ BufferFrame s t ∧ Frame [counterR s₀] s.mem t.mem := by
  induction n with
  | zero => exact WP.block_nil ⟨hE, hT, .refl _, .refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hEt, hTt, hf, hm⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (seedTemplate_ok hp hEt n (by omega) hTt (by
      rw [hf.gpr .r8 (by decide)]; exact hv)) fun u ⟨hEu, hTu, hf', hm'⟩ => ?_
    refine ⟨hEu, hTu, hf.trans hf', hm.trans (hm'.sub fun r hr => ?_)⟩
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨counterR s₀, List.mem_singleton_self _,
      Offset.sub (pp s₀) (d := 652 + 16 * n) (e := 640) (n := 4) (k := 128) (by omega) (by omega)⟩

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## SetupTail -/
section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (prepCounter)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block)

def counterTail : List Instr :=
  (List.range 8).map (fun i => .vmovdquStore .l128 (at_ .r11 (640 + 16 * i)) .xmm7) ++
  (List.range 8).flatMap prepCounter ++ [.alu32 .add .r8 (.imm 8)]

theorem counterTail_ok {s₀ s : State} {P : Nat → Block} {lo : Nat} (hp : SPre s₀ lo)
    (hE : Env s₀ P s) (hC : XBinOp.eval .pshufb (s.lane .xmm7 0) revMask = cb s₀)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32) :
    WP isa (.block counterTail) s fun t => Env s₀ P t ∧ Templates s₀ 0 0 t.mem ∧
      (t.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + 8 ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → t.gpr r = s.gpr r) ∧
      (∀ r l, t.lane r l = s.lane r l) ∧ Frame [counterR s₀] s.mem t.mem := by
  rw [counterTail, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyTemplates_ok hp s hE hC 8 (by decide)) fun u ⟨hu, hc, hf, hm⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (seedTemplates_ok hp u hu (by
    intro i hi; simpa only [Nat.not_lt_zero, ite_false, Nat.repeat] using hc i hi)
    (by rw [hf.gpr .r8 (by decide)]; exact hv) 8 (by decide)) fun v ⟨hvE, hvT, hvF, hvM⟩ => ?_
  refine WP.mono (bump_ok v) fun t ⟨ht8, htG, htM, htX, htR, htW⟩ => ?_
  refine ⟨hvE.move (fun r _ _ h8 _ => htG r h8) htM htR htW,
    htM ▸ hvT.done, ?_, ?_, ?_, htM ▸ hm.trans hvM⟩
  · rw [ht8, hvF.gpr .r8 (by decide), hf.gpr .r8 (by decide), hv]
  · intro r hax h8; rw [htG r h8, hvF.gpr r hax, hf.gpr r hax]
  · intro r l; rw [htX, hvF.lane, hf.lane]

end VG.Proof.Gcm.X86_64.StitchAvx8

end
