module

public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.FRow
public import VerifiedGarbage.Proof.X25519.X86_64.Env
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.X25519.Invert
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.FRow
meta import VerifiedGarbage.Proof.X25519.X86_64.Env
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.X25519.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Loop
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
import VerifiedGarbage.Proof.X25519.X86_64.Ops
import VerifiedGarbage.Proof.X25519.X86_64.Freeze
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Loop
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
meta import VerifiedGarbage.Proof.X25519.X86_64.Ops
meta import VerifiedGarbage.Proof.X25519.X86_64.Freeze

/-! ### `X25519.X86_64.Divstep.Main`, which only this module used -/

section

/-! ### `X25519.X86_64.Divstep.Batch`, which only this module used -/

section

/-!
# X25519 on x86-64, inversion by divsteps: a batch

A batch (`dbatch`) takes the state of the working area (`DMem`) to the next
`dbatchV` and counts down the batches (`dbatch_ok`), changing only the area
`[512, 768)`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- The working area holds the state `t`. -/
structure DMem (m : Mem) (base : Addr) (t : DSt) : Prop where
  D : word m base dsD = t.D
  f : fe m base dsF = t.f
  g : fe m base dsG = t.g
  a : fe m base dsA = t.a
  b : fe m base dsB = t.b

/-- `r8–r11 = [o]`. -/
theorem loads4_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 32 ≤ 4096) :
    WP isa (.block (loads o .r8 .r9 .r10 .r11)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = fe s.mem base o ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  drun [loads, State.load64, ea_sc, hs.rdi, inR hs (show o + 8 ≤ 4096 by omega_using [ho]),
    inR hs (show o + 8 + 8 ≤ 4096 by omega_using [ho]), inR hs (show o + 16 + 8 ≤ 4096 by omega_using [ho]),
    inR hs (show o + 24 + 8 ≤ 4096 by omega_using [ho]), RegUpd.gpr_setReg_self]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4⟩ := hr
  simp only [RegUpd.gpr_setReg, h1, h2, h3, h4, ↓reduceIte]

/-- `[dst] = [src]`. -/
theorem copy4_ok {s : State} {base : Addr} (hs : Scr s base) {dst src : Nat} (hd : dst + 32 ≤ 4096)
    (hsrc : src + 32 ≤ 4096) :
    WP isa (.block (copy4 dst src)) s fun t =>
      fe t.mem base dst = fe s.mem base src ∧ Outside base dst 32 s.mem t.mem ∧
      (∀ r, r ∉ [.r8, .r9, .r10, .r11] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  rw [copy4, WP.block_append_iff]
  refine WP.mono (loads4_ok hs hsrc) fun s₁ ⟨e1, k1⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps k1 (by decide)) (by unfold Slot; omega_using [hd])) fun t ⟨mt, gt, rt, wt⟩ =>
    ⟨?_, ?_, fun r hr => (gt r).trans (k1.1 r hr), rt.trans k1.2.2.1, wt.trans k1.2.2.2⟩
  · rw [mt, fe_st4 _ _ (by omega_using [hd]), e1]
  · rw [mt, k1.2.1]; exact st4_outside _ _ (by omega_using [hd]) _ _ _ _

/-- The count of batches less one. -/
theorem batchEnd_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j ≤ 10) (hc : s.gpr .rbp = BitVec.ofNat 64 (256 * j)) :
    WP isa (.block batchEnd) s fun t =>
      t.gpr .rbp = BitVec.ofNat 64 (256 * (j - 1)) ∧ t.zf = some (decide (j - 1 = 0)) ∧ Keeps [.rbp] s t := by
  obtain e : BitVec.ofNat 64 (256 * j) - BitVec.signExtend 64 (256 : BitVec 32) = BitVec.ofNat 64 (256 * (j - 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (BitVec.signExtend 64 (256 : BitVec 32)).toNat = 256 by decide]
    omega_using [hj]
  apply WP.of_runBlock
  simp only [batchEnd, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.zf_setReg, RegUpd.zf_arithFlags, RegUpd.gpr_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left', hc, e]
  refine ⟨trivial, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [ofNat_eq_zero (show 256 * (j - 1) < 2 ^ 64 by omega_using [hj'])]
    simp only [decide_eq_decide]
    omega_using []
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem dbatch_eq : dbatch = .seq dsteps (.block (fRow dsU dsV dsNF ++ (fRow dsQ dsR dsG ++ (copy4 dsF dsNF ++
    (aRow dsU dsV dsNA ++ (aRow dsQ dsR dsB ++ (copy4 dsA dsNA ++ batchEnd))))))) := by
  simp only [dbatch, List.append_assoc]

theorem pkW_eq {m : Mem} {base : Addr} {t : DSt} (h : DMem m base t) :
    pkW m base = pkBatchV t.D (BitVec.ofNat 64 t.f) (BitVec.ofNat 64 t.g) := by
  rw [pkW, ← ofNat_fe m base dsF, ← ofNat_fe m base dsG, h.D, h.f, h.g]

/-- Writes within the working area. -/
theorem Outside.wide {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : 512 ≤ o)
    (h2 : o + n ≤ 768) : Outside base 512 256 m m' := fun x hx => h x (by omega_using [h1, h2, hx])

/-- A batch. -/
theorem dbatch_ok {s : State} {base : Addr} (hs : Scr s base) {t₀ : DSt} (hm : DMem s.mem base t₀) {j : Nat}
    (hj : 1 ≤ j) (hj10 : j ≤ 10) (hc : s.gpr .rbp = BitVec.ofNat 64 (256 * j)) :
    WP isa dbatch s fun u =>
      DMem u.mem base (dbatchV t₀) ∧ u.gpr .rbp = BitVec.ofNat 64 (256 * (j - 1)) ∧
      u.zf = some (decide (j - 1 = 0)) ∧ Outside base 512 256 s.mem u.mem ∧
      (∀ r, r ∉ dsClob → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have hn := hs.nowrap
  rw [dbatch_eq]
  refine WP.seq (WP.mono (dsteps_ok hs) fun s₁ ⟨eD, eU, eV, eQ, eR, O1, b1, g1, r1, w1⟩ => ?_)
  obtain hs₁ : Scr s₁ base := ⟨(g1 _ (by decide)).trans hs.rdi, w1 ▸ hs.wr, hs.nowrap⟩
  rw [pkW_eq hm] at eD eU eV eQ eR
  rw [WP.block_append_iff]
  refine WP.mono (fRow_ok hs₁ (by decide) (by decide) (by decide)) fun s₂ ⟨f2, O2, g2, r2, w2⟩ => ?_
  obtain hs₂ : Scr s₂ base := ⟨(g2 _ (by decide)).trans hs₁.rdi, w2 ▸ hs₁.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (fRow_ok hs₂ (by decide) (by decide) (by decide)) fun s₃ ⟨f3, O3, g3, r3, w3⟩ => ?_
  obtain hs₃ : Scr s₃ base := ⟨(g3 _ (by decide)).trans hs₂.rdi, w3 ▸ hs₂.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (copy4_ok hs₃ (by decide) (by decide)) fun s₄ ⟨f4, O4, g4, r4, w4⟩ => ?_
  obtain hs₄ : Scr s₄ base := ⟨(g4 _ (by decide)).trans hs₃.rdi, w4 ▸ hs₃.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (aRow_ok hs₄ (by decide) (by decide) (by decide)) fun s₅ ⟨f5, O5, g5, r5, w5⟩ => ?_
  obtain hs₅ : Scr s₅ base := ⟨(g5 _ (by decide)).trans hs₄.rdi, w5 ▸ hs₄.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (aRow_ok hs₅ (by decide) (by decide) (by decide)) fun s₆ ⟨f6, O6, g6, r6, w6⟩ => ?_
  obtain hs₆ : Scr s₆ base := ⟨(g6 _ (by decide)).trans hs₅.rdi, w6 ▸ hs₅.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (copy4_ok hs₆ (by decide) (by decide)) fun s₇ ⟨f7, O7, g7, r7, w7⟩ => ?_
  obtain hs₇ : Scr s₇ base := ⟨(g7 _ (by decide)).trans hs₆.rdi, w7 ▸ hs₆.wr, hs.nowrap⟩
  obtain nb : Reg.rbp ∉ rowClob := by decide
  obtain c7 : s₇.gpr .rbp = BitVec.ofNat 64 (256 * j) := by
    rw [g7 _ (by decide), g6 _ nb, g5 _ nb, g4 _ (by decide), g3 _ nb, g2 _ nb, b1, hc]
  refine WP.mono (batchEnd_ok s₇ hj hj10 c7) fun u ⟨cu, zu, ku⟩ =>
    ⟨⟨?_, ?_, ?_, ?_, ?_⟩, cu, zu, ?_, fun r hr => ?_, ?_, ?_⟩
  all_goals try rw [ku.2.1]
  · rw [O7.word (by decide) (by decide), O6.word (by decide) (by decide),
      O5.word (by decide) (by decide), O4.word (by decide) (by decide), O3.word (by decide) (by decide),
      O2.word (by decide) (by decide), eD]
    rfl
  · rw [O7.fe (by decide) (by decide), O6.fe (by decide) (by decide), O5.fe (by decide) (by decide), f4, O3.fe (by decide) (by decide), f2, eU, eV, O1.fe (by decide) (by decide), O1.fe (by decide) (by decide), hm.f, hm.g]
    rfl
  · rw [O7.fe (by decide) (by decide), O6.fe (by decide) (by decide), O5.fe (by decide) (by decide), O4.fe (by decide) (by decide), f3, O2.word (by decide) (by decide), O2.word (by decide) (by decide), eQ, eR, O2.fe (by decide) (by decide), O2.fe (by decide) (by decide),
      O1.fe (by decide) (by decide), O1.fe (by decide) (by decide), hm.f, hm.g]
    rfl
  · rw [f7, O6.fe (by decide) (by decide), f5, O4.word (by decide) (by decide), O4.word (by decide) (by decide), O3.word (by decide) (by decide), O3.word (by decide) (by decide), O2.word (by decide) (by decide), O2.word (by decide) (by decide), eU, eV, O4.fe (by decide) (by decide), O4.fe (by decide) (by decide),
      O3.fe (by decide) (by decide), O3.fe (by decide) (by decide), O2.fe (by decide) (by decide), O2.fe (by decide) (by decide), O1.fe (by decide) (by decide), O1.fe (by decide) (by decide), hm.a, hm.b]
    rfl
  · rw [O7.fe (by decide) (by decide), f6, O5.word (by decide) (by decide), O5.word (by decide) (by decide), O4.word (by decide) (by decide), O4.word (by decide) (by decide), O3.word (by decide) (by decide), O3.word (by decide) (by decide), O2.word (by decide) (by decide), O2.word (by decide) (by decide), eQ, eR,
      O5.fe (by decide) (by decide), O5.fe (by decide) (by decide), O4.fe (by decide) (by decide), O4.fe (by decide) (by decide), O3.fe (by decide) (by decide), O3.fe (by decide) (by decide), O2.fe (by decide) (by decide), O2.fe (by decide) (by decide), O1.fe (by decide) (by decide), O1.fe (by decide) (by decide), hm.a, hm.b]
    rfl
  · exact (O1.wide (by decide) (by decide)).trans <| (O2.wide (by decide) (by decide)).trans <| (O3.wide (by decide) (by decide)).trans <|
      (O4.wide (by decide) (by decide)).trans <| (O5.wide (by decide) (by decide)).trans <| (O6.wide (by decide) (by decide)).trans (O7.wide (by decide) (by decide))
  · have h' : r ≠ .rbp := by intro h; subst h; exact hr (by decide)
    obtain hr' : r ∉ rowClob := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    obtain h8 : r ∉ [Reg.r8, .r9, .r10, .r11] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> decide)
    rw [ku.1 r (by simp only [List.mem_singleton]; exact h'), g7 r h8, g6 r hr', g5 r hr', g4 r h8, g3 r hr',
      g2 r hr', g1 r hr]
  · rw [ku.2.2.1, r7, r6, r5, r4, r3, r2, r1]
  · rw [ku.2.2.2, w7, w6, w5, w4, w3, w2, w1]

end VG.Proof.X25519.X86_64

end

end


/-!
# X25519 on x86-64, inversion by divsteps: the whole inversion

`invertDS F` leaves in slot 17 (`T1`) `byAlg` of slot 4 (`Z2`), changing
only the working area `[512, 768)` and the registers `clob` and `rbx`
(`invertDS_ok`): the start holds `drun x 0` for the fully reduced `x`
(`dinit_ok`), each batch takes it to the next (`dbatch_ok`), and the end
multiplies `a` by the constant `kSel f` (`dsel_ok`). With `DivstepInv`, that
is `[Z2]^(p-2)` (`invertDS_pow`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The words of `p` stored at `F`, and `a`, `b`, `d` and the count. -/
abbrev dinitB : List Instr :=
  ((List.range 4).flatMap fun i =>
    [.movImm64 .rax (BitVec.ofNat 64 (pNat >>> (64 * i))), .store (sc (dsF + 8 * i)) .rax]) ++
  [.mov32 .rax (.imm 0)] ++ stores dsA .rax .rax .rax .rax ++ stores dsB .rax .rax .rax .rax ++
  [.mov32 .rax (.imm 1), .store (sc dsB) .rax, .store (sc dsD) .rax, .mov32 .rbp (.imm 2560)]

theorem dinit_eq : dinit = freeze Z2 ++ (store4 dsG ++ dinitB) := by
  simp only [dinit, dinitB, List.append_assoc]

/-- A word written in the working area. -/
theorem Outside.writeW_in {base : Addr} {m₀ m : Mem} (h : Outside base 512 256 m₀ m) {d : Nat} {v : BitVec 64}
    (hd : 512 ≤ d) (hd' : d + 8 ≤ 768) : Outside base 512 256 m₀ (m.writeW (off base d) v) :=
  fun x hx => (writeW_outside m base v (by omega_arith) x (by omega_arith)).trans (h x hx)

theorem z2560 : (2560 : BitVec 32).setWidth 64 = BitVec.ofNat 64 (256 * 10) := by decide

/-- `f = p`, `a = 0`, `b = 1`, `d = 1`, the count `10`. -/
theorem dinitB_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block dinitB) s fun t =>
      fe t.mem base dsF = Spec.X25519.P ∧ fe t.mem base dsA = 0 ∧ fe t.mem base dsB = 1 ∧
      word t.mem base dsD = 1 ∧ t.gpr .rbp = BitVec.ofNat 64 (256 * 10) ∧
      fe t.mem base dsG = fe s.mem base dsG ∧ Outside base 512 256 s.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbp → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  simp only [dinitB, stores, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, dsF, dsG, dsA, dsB, dsD, Nat.reduceMul, Nat.reduceAdd]
  drun [State.store64, ea_sc, hs.rdi, inW hs (show 576 + 8 ≤ 4096 by decide),
    inW hs (show 584 + 8 ≤ 4096 by decide), inW hs (show 592 + 8 ≤ 4096 by decide),
    inW hs (show 600 + 8 ≤ 4096 by decide), inW hs (show 544 + 8 ≤ 4096 by decide),
    inW hs (show 552 + 8 ≤ 4096 by decide), inW hs (show 560 + 8 ≤ 4096 by decide),
    inW hs (show 568 + 8 ≤ 4096 by decide), inW hs (show 512 + 8 ≤ 4096 by decide),
    inW hs (show 520 + 8 ≤ 4096 by decide), inW hs (show 528 + 8 ≤ 4096 by decide),
    inW hs (show 536 + 8 ≤ 4096 by decide), inW hs (show 704 + 8 ≤ 4096 by decide), z1, zs0, z2560,
    RegUpd.gpr_setReg_self]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr hr' => ?_⟩
  all_goals try simp (disch := omega_arith) only [X86_64.fe, val4, dword_writeW_ne, dword_writeW_self]
  · simp only [pNat]; decide
  · rfl
  · rfl
  · repeat refine Outside.writeW_in ?_ (by omega_arith) (by omega_arith)
    exact Outside.refl _ _ _ _
  · simp only [hr, hr', ↓reduceIte]

/-- The start: the state `drun x 0` for the fully reduced `x`, and the count. -/
theorem dinit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block dinit) s fun t =>
      DMem t.mem base (drun (fe s.mem base Z2 % Spec.X25519.P) 0) ∧ t.gpr .rbp = BitVec.ofNat 64 (256 * 10) ∧
      Outside base 512 256 s.mem t.mem ∧ (∀ r, r ∉ dsClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  rw [dinit_eq, WP.block_append_iff]
  refine WP.mono (freeze_ok hs (by unfold Slot; decide)) fun s₁ ⟨e1, k1⟩ => ?_
  obtain hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok hs₁ (by unfold Slot; decide)) fun s₂ ⟨m2, g2, r2, w2⟩ => ?_
  obtain hs₂ : Scr s₂ base := ⟨(g2 _).trans hs₁.rdi, w2 ▸ hs₁.wr, hs.nowrap⟩
  refine WP.mono (dinitB_ok hs₂) fun t ⟨fF, fA, fB, wD, wC, fG, O, gt, rt, wt⟩ =>
    ⟨⟨wD, fF, ?_, fA, fB⟩, wC, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [fG, m2, fe_st4 _ _ (by decide), e1]; rfl
  · have O2 : Outside base 512 256 s.mem s₂.mem := by
      rw [m2, k1.2.1]
      exact Outside.wide (st4_outside _ _ (by decide) _ _ _ _) (by decide) (by decide)
    exact O2.trans O
  · have h' : r ≠ .rax := by intro h; subst h; exact hr (by decide)
    obtain h'' : r ≠ .rbp := by intro h; subst h; exact hr (by decide)
    rw [gt r h' h'', g2, k1.1 r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))]
  · rw [rt, r2, k1.2.2.1]
  · rw [wt, w2, k1.2.2.2]

/-- The batches: from `drun x 0` and the count `10`, `drun x 10`. -/
theorem dloops_ok {s : State} {base : Addr} (hs : Scr s base) {x : Nat} (hm : DMem s.mem base (drun x 0))
    (hc : s.gpr .rbp = BitVec.ofNat 64 (256 * 10)) :
    WP isa (.loop dbatch .ne) s fun t =>
      DMem t.mem base (drun x 10) ∧ Outside base 512 256 s.mem t.mem ∧
      (∀ r, r ∉ dsClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine cntLoop_ok (n := 10)
    (Inv := fun j t => DMem t.mem base (drun x (10 - j)) ∧ t.gpr .rbp = BitVec.ofNat 64 (256 * j) ∧
      Outside base 512 256 s.mem t.mem ∧ (∀ r, r ∉ dsClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr)
    (fun j t hj1 hjN ⟨mt, ct, Ot, gt, rt, wt⟩ => ?_) (fun t ⟨mt, _, Ot, gt, rt, wt⟩ => ⟨mt, Ot, gt, rt, wt⟩)
    (by decide) ⟨hm, hc, Outside.refl _ _ _ _, fun _ _ => rfl, rfl, rfl⟩
  obtain ht : Scr t base := ⟨(gt _ (by decide)).trans hs.rdi, wt ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (dbatch_ok ht mt hj1 hjN ct) fun u ⟨mu, cu, zu, Ou, gu, ru, wu⟩ =>
    ⟨⟨?_, cu, Ot.trans Ou, fun r hr => (gu r hr).trans (gt r hr), ru.trans rt, wu.trans wt⟩, zu⟩
  rw [show 10 - (j - 1) = (10 - j) + 1 by omega_arith]
  exact mu

theorem sel_mask (a b m : BitVec 64) (hm : m = 0 ∨ m = BitVec.allOnes 64) :
    a ^^^ ((b ^^^ a) &&& m) = if m = 0 then a else b := by
  rcases hm with rfl | rfl
  · simp
  · have : BitVec.allOnes 64 ≠ 0 := by decide
    simp only [BitVec.and_allOnes, this, ↓reduceIte]
    rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem top_mask (w : BitVec 64) : (0 : BitVec 64) - (w >>> 63) = if 2 ^ 63 ≤ w.toNat then BitVec.allOnes 64 else 0 := by
  rw [maskW_eq]; unfold maskW
  by_cases h : 2 ^ 63 ≤ w.toNat
  · simp only [(msb_iff w).2 h, h, ↓reduceIte]
  · have h' : ¬ w.msb = true := fun h' => h ((msb_iff w).1 h')
    simp only [h', h, Bool.false_eq_true, ↓reduceIte]

/-- `[dsK] = kSel f`. -/
theorem dsel_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block dsel) s fun t =>
      fe t.mem base dsK = kSel (fe s.mem base dsF) ∧ Outside base dsK 32 s.mem t.mem ∧
      (∀ r, r ∉ [.rax, .rcx, .rdx] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  simp only [dsel, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, dsF, dsK, Nat.reduceMul, Nat.reduceAdd]
  drun [State.load64, State.store64, ea_sc, hs.rdi, inR hs (show 600 + 8 ≤ 4096 by decide),
    inW hs (show 640 + 8 ≤ 4096 by decide), inW hs (show 648 + 8 ≤ 4096 by decide),
    inW hs (show 656 + 8 ≤ 4096 by decide), inW hs (show 664 + 8 ≤ 4096 by decide), zs0,
    RegUpd.gpr_setReg_self, top_mask]
  obtain hm : ∀ w : BitVec 64, (if 2 ^ 63 ≤ w.toNat then BitVec.allOnes 64 else 0) = 0 ∨
      (if 2 ^ 63 ≤ w.toNat then BitVec.allOnes 64 else 0) = BitVec.allOnes 64 := fun w => by
    split <;> simp
  simp only [sel_mask _ _ _ (hm _)]
  refine ⟨?_, ?_, fun r hr => ?_⟩
  · simp (disch := omega_arith) only [X86_64.fe, val4, dword_writeW_ne, dword_writeW_self]
    obtain h3 := (word s.mem base 600).isLt
    obtain e : (fe s.mem base 576 < 2 ^ 255) = ¬ 2 ^ 63 ≤ (word s.mem base 600).toNat := by
      simp only [X86_64.fe, val4, Nat.reduceAdd]
      have := (word s.mem base 576).isLt; have := (word s.mem base 584).isLt; have := (word s.mem base 592).isLt
      apply propext; omega_arith
    unfold kSel
    rw [show (576 : Nat) = dsF from rfl] at e
    simp only [dsF] at e ⊢
    by_cases h : 2 ^ 63 ≤ (word s.mem base 600).toNat
    · have hn : ¬ (fe s.mem base 576 < 2 ^ 255) := by rw [e]; exact fun h' => h' h
      have : BitVec.allOnes 64 ≠ 0 := by decide
      simp only [h, hn, ↓reduceIte, this]
      decide
    · have hn : fe s.mem base 576 < 2 ^ 255 := by rw [e]; exact h
      simp only [h, hn, ↓reduceIte]
      decide
  · intro x hx
    rw [writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2, ↓reduceIte]

variable {fld : Field} (hf : FieldOk fld)

include hf in
/-- The inversion by divsteps: slot 17 becomes `byAlg` of slot 4, and only the
working area `[512, 768)` and the registers `clob` and `rbx` change. -/
theorem invertDS_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (invertDS fld) s fun t =>
      (∀ r, r ∉ clob → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 512 256 s.mem t.mem ∧ E t.mem base 17 = byAlg (E s.mem base 4) := by
  have hn := hs.nowrap
  obtain hc : ∀ r, r ∉ clob → r ≠ .rbx → r ∉ dsClob := fun r h1 h2 h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact h2 rfl | exact h1 (by decide)
  refine WP.seq (WP.mono (dinit_ok hs) fun s₁ ⟨m1, c1, O1, g1, r1, w1⟩ => ?_)
  obtain hs₁ : Scr s₁ base := ⟨(g1 _ (by decide)).trans hs.rdi, w1 ▸ hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (dloops_ok hs₁ m1 c1) fun s₂ ⟨m2, O2, g2, r2, w2⟩ => ?_)
  obtain hs₂ : Scr s₂ base := ⟨(g2 _ (by decide)).trans hs₁.rdi, w2 ▸ hs₁.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (dsel_ok hs₂) fun s₃ ⟨k3, O3, g3, r3, w3⟩ => ?_
  obtain hs₃ : Scr s₃ base := ⟨(g3 _ (by decide)).trans hs₂.rdi, w3 ▸ hs₂.wr, hs.nowrap⟩
  refine WP.mono (hf.mul hs₃ (by unfold Slot; decide) (by unfold Slot; decide) (by unfold Slot; decide))
    fun t ⟨op, ft⟩ => ⟨fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [op.gpr r h1, g3 r (fun h => h1 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> decide)), g2 r (hc r h1 h2), g1 r (hc r h1 h2)]
  · rw [op.rd, r3, r2, r1]
  · rw [op.wr, w3, w2, w1]
  · exact ((O1.trans O2).trans (Outside.wide O3 (by decide) (by decide))).trans
      (Outside.wide op.mem (by decide) (by decide))
  · show F t.mem base T1 = _
    rw [ft, show (T1 : Nat) = dsA from rfl]
    show toFe (fe s₃.mem base dsA) * toFe (fe s₃.mem base dsK) = _
    rw [O3.fe (d := dsA) (by decide) (by decide), k3, m2.a, m2.f]
    unfold byAlg
    obtain hx : (E s.mem base 4).val = fe s.mem base Z2 % Spec.X25519.P := by
      simp only [E, F, toFe, Fin.val_ofNat]; rfl
    rw [hx]

include hf in
/-- With the theory of divsteps, the inversion is `[Z2]^(p-2)`. -/
theorem invertDS_pow [DivstepInv] {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (invertDS fld) s fun t =>
      (∀ r, r ∉ clob → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 512 256 s.mem t.mem ∧
      E t.mem base 17 = Spec.X25519.pow (E s.mem base 4) (Spec.X25519.P - 2) :=
  WP.mono (invertDS_ok hf hs) fun _ ⟨g, r, w, o, e⟩ => ⟨g, r, w, o, e.trans (DivstepInv.eq _)⟩

end VG.Proof.X25519.X86_64

end

end

/-! ### `X25519.Field64Contract`, which only this module used -/

section

/-!
# Curve25519's field elements in radix `2^64`, in the working space

Not trusted: how the proofs of the inversion in radix `2^64`
(`vg_gf25519_r64_invert`, `z^(p-2)` in `GF(p)`, `p = 2^255 - 19`, each element
four 64-bit words) state where its operands are.

An element is 32 bytes, a little-endian number below `2^256` (`valAt`), not
necessarily below `p`: any 32 bytes are an element. The elements live in a
working space `ws` of 4096 bytes (`[u64; 512]`, X25519's working space and
the start of Ed25519's), at fixed offsets, those where that code keeps them.
The inversion reads `z` at byte 128 (`zAt`) and writes `z^(p-2)` at byte 544
(`invAt`); bytes 512 to 767 (`invOwnAt` to `invOwnEnd`) are its own working
space and its result. Every other byte of `ws` keeps its value (`InvKeeps`).
-/

@[expose] public section

namespace VG.Proof.X25519.Field64

open VG.Spec VG.Spec.X25519

/-- The bytes of the working space. -/
def wsBytes : Nat := 4096

/-- The bytes of an element. -/
def elemBytes : Nat := 32

/-- The value of the element at byte offset `o` of the working space `ws`:
its 32 bytes, little-endian. -/
def valAt (m : Mem) (ws : Addr) (o : BitVec 32) : Nat :=
  (m.read (ws + BitVec.ofNat 64 o.toNat) elemBytes).toNat

/-! ## Inversion -/

/-- Where `vg_gf25519_r64_invert` reads `z`. -/
def zAt : BitVec 32 := 128

/-- Where it writes `z^(p-2)`. -/
def invAt : BitVec 32 := 544

/-- Where its own working space, and its result, start. -/
def invOwnAt : Nat := 512

/-- Where they end. -/
def invOwnEnd : Nat := 768

/-- Every byte of `ws` but those of the inversion's own working space and
result (bytes 512 to 767) keeps its value. -/
def InvKeeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < invOwnAt ∨ invOwnEnd ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

end VG.Proof.X25519.Field64

end

end


/-!
# X25519 on x86-64: `vg_gf25519_r64_invert`'s power

`invertFn` keeps the callee-saved registers the divsteps write in
`xmm0`–`xmm5` (`invSaves_ok`, `invRestores_ok`), and leaves in slot 17
(byte 544) slot 4's (byte 128) power `p - 2` (`invertFn_pow`, from
`invertDS_pow`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519
open VG.Proof.X25519.Field64 (valAt zAt invAt InvKeeps)

theorem setXmm_gpr' (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).gpr = s.gpr := rfl
theorem setXmm_mem' (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mem = s.mem := rfl
theorem setXmm_rd' (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).rd = s.rd := rfl
theorem setXmm_wr' (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).wr = s.wr := rfl
theorem setXmm_xmm' (s : State) (r r' : XReg) (v : BitVec 128) :
    (s.setXmm r v).xmm r' = if r' = r then v else s.xmm r' := rfl

/-- `invSaves`: the callee-saved registers in `xmm0`–`xmm5`. -/
theorem invSaves_ok (s : State) :
    WP isa (.block invSaves) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .rbx ∧ s'.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .rbp ∧
      s'.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r12 ∧ s'.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .r13 ∧
      s'.xmm .xmm4 = (0 : BitVec 64) ++ s.gpr .r14 ∧ s'.xmm .xmm5 = (0 : BitVec 64) ++ s.gpr .r15 := by
  apply WP.of_runBlock
  simp only [invSaves, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    Option.some.injEq, exists_eq_left', setXmm_gpr', setXmm_mem', setXmm_rd', setXmm_wr', setXmm_xmm',
    reduceCtorEq, ↓reduceIte]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- `invRestores`: the callee-saved registers out of `xmm0`–`xmm5`, nothing else changed but
them. -/
theorem invRestores_ok (s : State) :
    WP isa (.block invRestores) s fun s' =>
      s'.gpr .rbx = (s.xmm .xmm0).extractLsb' 0 64 ∧ s'.gpr .rbp = (s.xmm .xmm1).extractLsb' 0 64 ∧
      s'.gpr .r12 = (s.xmm .xmm2).extractLsb' 0 64 ∧ s'.gpr .r13 = (s.xmm .xmm3).extractLsb' 0 64 ∧
      s'.gpr .r14 = (s.xmm .xmm4).extractLsb' 0 64 ∧ s'.gpr .r15 = (s.xmm .xmm5).extractLsb' 0 64 ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [invRestores, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left', RegUpd.xmm_setReg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r a b c d e f => ?_, rfl, rfl, rfl⟩
  all_goals try (simp only [RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; done)
  simp only [RegUpd.gpr_setReg_of_ne _ _ a, RegUpd.gpr_setReg_of_ne _ _ b, RegUpd.gpr_setReg_of_ne _ _ c,
    RegUpd.gpr_setReg_of_ne _ _ d, RegUpd.gpr_setReg_of_ne _ _ e, RegUpd.gpr_setReg_of_ne _ _ f]

/-- `invertFn` as the inline inversion `invertDS` is to its caller: slot 17
becomes slot 4's power `p - 2`, and only the working area `[512, 768)` and the
registers `clob` and `rbx` change (it keeps more). -/
theorem invertFn_pow [DivstepInv] {s : State} {base : Addr} (hs : Scr s base) :
    WP isa invertFn s fun t =>
      (∀ r, r ∉ clob → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 512 256 s.mem t.mem ∧
      E t.mem base 17 = Spec.X25519.pow (E s.mem base 4) (Spec.X25519.P - 2) := by
  refine WP.seq (WP.mono (invSaves_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  have hs₁ : Scr s₁ base := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (invertDS_pow baseline_ok hs₁) fun s₂ ⟨g₂, rd₂, wr₂, o₂, e₂⟩ => ?_)
  refine WP.mono (invRestores_ok s₂) fun s₃ ⟨_, _, _, _, _, _, k₃, m₃, rd₃, wr₃⟩ => ?_
  refine ⟨fun r hc hb => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], ?_, ?_⟩
  · have hne : ∀ q ∈ [Reg.rbp, .r12, .r13, .r14, .r15], r ≠ q := fun q hq h => hc (by
      subst h; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide)
    rw [k₃ r hb (hne _ (by simp)) (hne _ (by simp)) (hne _ (by simp)) (hne _ (by simp))
      (hne _ (by simp)), g₂ r hc hb, g₁]
  · rw [m₃]; rw [← m₁]; exact o₂
  · rw [m₃, e₂, m₁]

end VG.Proof.X25519.X86_64
