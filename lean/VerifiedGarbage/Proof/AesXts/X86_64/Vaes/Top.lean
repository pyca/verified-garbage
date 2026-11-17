module

public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesXts.X86_64.Steps
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Loop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesXts.X86_64Vaes
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! ### `AesXts.X86_64.Vaes.Body`, which this module and modules that import it used -/

section

/-!
# One-pass XTS-AES on x86-64: the loops

`constK_ok`: `0x87` into both lanes of `ymm11`. `groups_wp`: from `GInv 0 0`,
if eight blocks are left, the tweaks loaded into `ymm4`–`ymm7` (`TwR 0`),
the eight-block loop, and the tweaks stored back reach `GInv c c` with fewer
than eight blocks left.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0)
open VG.Impl.AesXts.X86_64Vaes (constK group ldT stT tws bufOff)
open VG.Proof.AesXts (b16)
open VG.Proof.Aes.X86_64.AesNi (inRegions_wr ofInt_natCast)

theorem constK_ok (s : State) : WP isa (.block constK) s fun s' =>
    (∀ l < 2, qword (s'.lane .xmm11 l) 0 = 0x87) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [constK, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun r h => by simp [State.setReg, State.setV, h], by simp [State.setReg, State.setV],
    by simp [State.setReg, State.setV], by simp [State.setReg, State.setV]⟩
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> simp [State.lane, State.setV, State.setReg, qword] <;> rfl

/-- `GInv` is kept by any change of registers it does not name. -/
theorem GInv.congr {enc : Bool} {KP : State → Prop} {s₀ : State} (hst : Stable KP s₀) {b c : Nat} {s s' : State}
    (h : GInv enc KP s₀ b c s) (hg : ∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : GInv enc KP s₀ b c s' where
  kp := hst s s' h.kp (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide))
    (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide)) hrd hwr
    (by rw [hm]; exact Frame.refl _ _)
  le := h.le
  r8 := by rw [hg _ (by decide) (by decide), h.r8]
  r9 := by rw [hg _ (by decide) (by decide), h.r9]
  r11 := by rw [hg _ (by decide) (by decide), h.r11]
  r10 := by rw [hg _ (by decide) (by decide), h.r10]
  keep := fun r h1 h2 h3 h4 h5 h6 h7 => by rw [hg r h1 h2, h.keep r h1 h2 h3 h4 h5 h6 h7]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := by rw [hm]; exact h.frame
  data := by rw [hm]; exact h.data
  buf := by rw [hm]; exact h.buf
  rdx := by rw [hg _ (by decide) (by decide), h.rdx]

/-- `cmp r9, 8`. -/
theorem cmp8_ok {enc : Bool} {KP : State → Prop} {s₀ : State} (hst : Stable KP s₀) {c : Nat} {s : State}
    (h : GInv enc KP s₀ c c s) :
    WP isa (.block [.alu .cmp .r9 (.imm 8)]) s fun s' =>
      GInv enc KP s₀ c c s' ∧ s'.cf = some (decide (N s₀ - c < 8)) := by
  have e16 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hr9 := h.r9
  have hn : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, e16, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨h.congr hst (fun _ _ _ => rfl) rfl rfl rfl, ?_⟩
  simp only [arithFlags, State.setFlags, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - c < 2 ^ 64 by omega_arith),
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- The tweak registers from the buffer: `TwR 0`. -/
theorem ldT_twr {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) (hst : Stable KP s₀) {b : Nat}
    {s : State} (h : GInv enc KP s₀ b b s) (hK : ∀ l < 2, qword (s.lane .xmm11 l) 0 = 0x87) :
    WP isa (.block (ldT tws 0)) s fun s' => GInv enc KP s₀ b b s' ∧ TwR s₀ b s' := by
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  refine WP.mono (ldT_ok tws 0 s (by decide) fun k hk => inRegions_wr ⟨scrR s₀, by rw [hW]; simp, by
      rw [h.r8, ofInt_natCast]
      rw [show tws.length = 4 from rfl] at hk
      exact Offset.contains_base _ (by simp only [bufOff]; omega_arith) (by simp only [bufOff]; omega_arith)⟩)
    fun s' ⟨e, g, m, rd, wr, x⟩ => ?_
  refine ⟨h.congr hst (fun r _ _ => by rw [g]) m rd wr, ⟨fun k hk l hl => ?_, fun l hl => by
    rw [x _ (by decide) l hl]; exact hK l hl⟩⟩
  have hk4 : k < 4 := hk
  rw [e k hk l hl, h.r8, show bufOff + 32 * (0 + k) + 16 * l = bufOff + 16 * (2 * k + l) by omega_arith,
    ← bytesAt_b16, h.buf _ (by omega_arith)]

/-- The tweak registers back to the buffer: `GInv c c`. -/
theorem stT_ginv {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) (hst : Stable KP s₀) {b c : Nat}
    {s : State} (h : GInv enc KP s₀ b c s) (ht : TwR s₀ c s) :
    WP isa (.block (stT tws 0)) s (GInv enc KP s₀ c c) := by
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  refine WP.mono (stT_ok tws 0 s (fun k hk => ⟨scrR s₀, by rw [hW]; simp, by
      rw [h.r8, ofInt_natCast]
      rw [show tws.length = 4 from rfl] at hk
      exact Offset.contains_base _ (by simp only [bufOff]; omega_arith) (by simp only [bufOff]; omega_arith)⟩) (by rw [h.r8]; simp only [bufOff]; have : tws.length = 4 := rfl; omega_arith))
    fun s' ⟨e, f, g, rd, wr, _⟩ => ?_
  rw [h.r8, Nat.mul_zero, Nat.add_zero, show 32 * tws.length = 128 from rfl] at f
  rw [h.r8] at e
  have fb : Frame [bufR s₀] s.mem s'.mem := f.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, Region.sub_prefix (by decide)⟩
  have fs : Frame [scrR s₀] s.mem s'.mem := fb.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, buf_scr⟩
  have hbd : ∀ k < N s₀, ∀ r ∈ [bufR s₀], Region.Disjoint ⟨blk s₀ k, 16⟩ r := fun k hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right buf_scr
  exact ⟨hst s s' h.kp (by rw [g]) (by rw [g]) (by rw [g]) (by rw [g]) rd wr (fb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, fun _ h => h⟩),
    h.le, by rw [g, h.r8], by rw [g, h.r9], by rw [g, h.r11], by rw [g, h.r10],
    fun r h1 h2 h3 h4 h5 h6 h7 => by rw [g, h.keep r h1 h2 h3 h4 h5 h6 h7], by rw [rd, h.rd], by rw [wr, h.wr],
    h.frame.trans (fs.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩),
    fun k hk => by rw [AesCbc.X86_64.bytesAt_frame fb (hbd k hk) (by decide), h.data k hk],
    fun j hj => by
      have hk : j / 2 < tws.length := by have : tws.length = 4 := rfl; omega_arith
      rw [bytesAt_b16, slot, show bufOff + 16 * j = bufOff + 32 * (0 + j / 2) + 16 * (j % 2) by omega_arith,
        e _ hk _ (Nat.mod_lt _ (by decide)), ht.tw _ hk _ (Nat.mod_lt _ (by decide))]
      congr 1; omega_arith,
    by rw [g, h.rdx]⟩

/-- The eight-block loop, from block `b`, if eight blocks are left. -/
theorem groups_wp {enc : Bool} {KP : State → Prop} {f8 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk8 enc f8 KP s₀) {b : Nat} {s : State} (h : GInv enc KP s₀ b b s)
    (hcf : s.cf = some (decide (N s₀ - b < 8))) :
    WP isa (.ite .b (.block []) (.seq (.block (constK ++ ldT tws 0))
      (.seq (.loop (group f8) .ae) (.block (stT tws 0 ++ ([.vop .vzeroupper] : List Instr)))))) s
      fun s' => ∃ c, N s₀ - c < 8 ∧ GInv enc KP s₀ c c s' := by
  refine WP.ite (decide (N s₀ - b < 8)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨b, by simpa using hb, h⟩
  · simp at hb
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (constK_ok s) fun s₁ ⟨k₁, g₁, m₁, rd₁, wr₁⟩ => ?_
    have h₁ : GInv enc KP s₀ b b s₁ := h.congr hst (fun r h1 _ => g₁ r h1) m₁ rd₁ wr₁
    refine WP.mono (ldT_twr hp hst h₁ k₁) fun s₂ ⟨h₂, t₂⟩ => ?_
    let I : Nat → State → Prop := fun m t => ∃ c, m = N s₀ - c ∧ c + 8 ≤ N s₀ ∧ GInv enc KP s₀ b c t ∧ TwR s₀ c t
    have hstep : ∀ m t, I m t → WP isa (group f8) t (fun t' =>
        (eval .ae t' = some false ∧ ∃ c, N s₀ - c < 8 ∧ GInv enc KP s₀ b c t' ∧ TwR s₀ c t') ∨
        (eval .ae t' = some true ∧ ∃ m' < m, I m' t')) := by
      rintro m t ⟨c, rfl, hc, hI, hT⟩
      refine WP.mono (group_wp hp hst hf hc hI hT) fun t' ⟨⟨hI', hT'⟩, hcf'⟩ => ?_
      by_cases hlt : N s₀ - (c + 8) < 8
      · exact .inl ⟨by simp [eval, hcf', hlt], c + 8, hlt, hI', hT'⟩
      · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 8), by omega_arith, c + 8, rfl, by omega_arith, hI', hT'⟩
    refine WP.seq (WP.mono (WP.loop (M := isa) I hstep (N s₀ - b) s₂ ⟨b, rfl, by omega_arith, h₂, t₂⟩)
      fun s₃ ⟨c, hc, h₃, t₃⟩ => ?_)
    rw [WP.block_append_iff]
    refine WP.mono (stT_ginv hp hst h₃ t₃) fun s₄ h₄ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
    exact ⟨c, hc, h₄.congr hst (fun _ _ _ => rfl) rfl rfl rfl⟩

end VG.Proof.AesXts.X86_64.Vaes

end

end

/-! ### `AesXts.X86_64.Vaes.Tail`, which this module and modules that import it used -/

section

/-! ### `AesXts.X86_64.Vaes.TailOps`, which this module and modules that import it used -/

section

/-!
# One-pass XTS-AES on x86-64: the tweaks XORed in, one block per register

The blocks left after the eight-block loop go through 128-bit registers:
`tPreList_ok` loads block register `k` from `r11 + 16 k` and XORs in the
tweak at `rax + 16 k`; `tPostList_ok` XORs it in again and stores it.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at inRegions_wr ofInt_natCast)
open VG.Impl.AesXts.X86_64Vaes (tPre tPost)

theorem nodup9 {b : XReg} {bs : List XReg} (h : (XReg.xmm9 :: b :: bs).Nodup) :
    b ≠ .xmm9 ∧ b ∉ bs ∧ (XReg.xmm9 :: bs).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, not_or] at h ⊢
  exact ⟨Ne.symm h.1.1, h.2.1, h.1.2, h.2.2⟩

theorem tPre1_ok (b : XReg) (d : Nat) (s : State) (h9 : b ≠ .xmm9)
    (hd : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 16)
    (he : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad b (at_ .r11 d), .movdquLoad .xmm9 (at_ .rax d), .xop (.bin .pxor b .xmm9)]) s
      fun s' =>
      s'.xmm b = s.mem.readW (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 128 ^^^
        s.mem.readW (s.gpr .rax + BitVec.ofInt 64 (d : Int)) 128 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ [.xmm9, b] → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm,
    State.load128, ea_at, hd, he, Option.map_some, Option.some.injEq, exists_eq_left', h9]
  refine ⟨by simp [XBinOp.eval], trivial, trivial, trivial, trivial, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

theorem tPost1_ok (b : XReg) (d : Nat) (s : State) (h9 : b ≠ .xmm9)
    (hd : InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 16)
    (he : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad .xmm9 (at_ .rax d), .xop (.bin .pxor b .xmm9), .movdquStore (at_ .r11 d) b]) s
      fun s' =>
      s'.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofInt 64 (d : Int))
        (s.xmm b ^^^ s.mem.readW (s.gpr .rax + BitVec.ofInt 64 (d : Int)) 128) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ [.xmm9, b] → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm,
    State.load128, State.store128_eq, ea_at, hd, he, Option.map_some, Option.some.injEq, exists_eq_left', h9]
  refine ⟨by simp [State.setMem, XBinOp.eval], rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

theorem tPreList_ok (regs : List XReg) (j : Nat) (s : State) (hnd : (.xmm9 :: regs).Nodup)
    (hd : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (he : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16) :
    WP isa (.block (tPre regs j)) s fun s' =>
      (∀ k (h : k < regs.length), s'.xmm regs[k] =
        s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (16 * (j + k))) 128 ^^^
          s.mem.readW (s.gpr .rax + BitVec.ofNat 64 (16 * (j + k))) 128) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ .xmm9 :: regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    obtain ⟨h9, hbs, hnd'⟩ := nodup9 hnd
    simp only [List.length_cons] at hd he
    rw [tPre, WP.block_append_iff]
    have hd0 := hd 0 (by omega_arith)
    have he0 := he 0 (by omega_arith)
    rw [Nat.add_zero] at hd0 he0
    refine WP.mono (tPre1_ok b (16 * j) s h9 hd0 he0) fun s₁ ⟨v₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih (j + 1) s₁ hnd'
        (fun k hk => by rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega_arith]; exact hd (k + 1) (by omega_arith))
        (fun k hk => by rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega_arith]; exact he (k + 1) (by omega_arith)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [g₁, m₁] at hb
    refine ⟨fun k hk => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b (by simp [h9, hbs]), v₁, ofInt_natCast]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk), show j + 1 + k = j + (k + 1) by omega_arith]
    · simp only [List.mem_cons, not_or] at hr
      rw [hx r (by simp [hr.1, hr.2.2]), o₁ r (by simp [hr.1, hr.2.1])]

theorem tPostList_ok (regs : List XReg) (j : Nat) (s : State) (hnd : (.xmm9 :: regs).Nodup)
    (hd : ∀ k < regs.length, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (he : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (hw : (s.gpr .r11).toNat + 16 * (j + regs.length) ≤ 2 ^ 64)
    (hsep : ∀ k < regs.length,
      Region.Disjoint ⟨s.gpr .rax + BitVec.ofNat 64 (16 * (j + k)), 16⟩
        ⟨s.gpr .r11 + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩) :
    WP isa (.block (tPost regs j)) s fun s' =>
      (∀ k (h : k < regs.length), s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (16 * (j + k))) 128 =
          s.xmm regs[k] ^^^ s.mem.readW (s.gpr .rax + BitVec.ofNat 64 (16 * (j + k))) 128) ∧
      Frame [⟨s.gpr .r11 + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ .xmm9 :: regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    obtain ⟨h9, hbs, hnd'⟩ := nodup9 hnd
    simp only [List.length_cons] at hd he hw hsep
    rw [tPost, WP.block_append_iff]
    have hd0 := hd 0 (by omega_arith)
    have he0 := he 0 (by omega_arith)
    rw [Nat.add_zero] at hd0 he0
    refine WP.mono (tPost1_ok b (16 * j) s h9 hd0 he0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have h11 : s₁.gpr .r11 = s.gpr .r11 := by rw [g₁]
    have hax : s₁.gpr .rax = s.gpr .rax := by rw [g₁]
    rw [ofInt_natCast] at m₁
    have hblk : Frame [⟨s.gpr .r11 + BitVec.ofNat 64 (16 * j), 16⟩] s.mem s₁.mem := by
      rw [m₁]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
        simp only [Region.Contains, BitVec.sub_self]; simp)
    have hslot : ∀ k < bs.length,
        s₁.mem.readW (s.gpr .rax + BitVec.ofNat 64 (16 * (j + 1 + k))) 128 =
          s.mem.readW (s.gpr .rax + BitVec.ofNat 64 (16 * (j + 1 + k))) 128 := by
      intro k hk
      refine hblk.readW (r := ⟨_, 16⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      have := hsep (k + 1) (by omega_arith)
      rw [show j + (k + 1) = j + 1 + k by omega_arith] at this
      exact this.sub_right (Region.sub_prefix (by omega_arith))
    refine WP.mono (ih (j + 1) s₁ hnd' (fun k hk => by
        rw [wr₁, h11, show j + 1 + k = j + (k + 1) by omega_arith]; exact hd (k + 1) (by omega_arith))
      (fun k hk => by
        rw [rd₁, wr₁, hax, show j + 1 + k = j + (k + 1) by omega_arith]; exact he (k + 1) (by omega_arith))
      (by rw [h11]; omega_arith)
      (fun k hk => by
        rw [hax, h11]
        have := hsep (k + 1) (by omega_arith)
        rw [show j + (k + 1) = j + 1 + k by omega_arith] at this
        refine this.sub_right ?_
        intro a ha
        simp only [Region.Contains] at ha ⊢
        rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega_arith)] at ha ⊢
        have := (a - s.gpr .r11).isLt
        omega_arith)) fun s' ⟨hb, hf, g, rd, wr, xs⟩ => ?_
    rw [h11, hax] at hb
    rw [h11] at hf
    have hdj : ∀ r ∈ [(⟨s.gpr .r11 + BitVec.ofNat 64 (16 * (j + 1)), 16 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .r11 + BitVec.ofNat 64 (16 * j), 16⟩ r := by
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega_arith)] at h₁ h₂
      have := (a - s.gpr .r11).isLt
      omega_arith
    refine ⟨fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hf.readW (Region.contains_self _ _) hdj (by decide), m₁, Mem.readW_writeW_self s.mem _ 16 _ (by decide)]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hne : bs[k] ≠ b := fun h => hbs (h ▸ List.getElem_mem hk')
        have hne9 : bs[k] ≠ .xmm9 := fun h => (List.nodup_cons.mp hnd').1 (h ▸ List.getElem_mem hk')
        rw [show j + (k + 1) = j + 1 + k by omega_arith, hb k hk', x₁ _ (by simp [hne, hne9]), hslot k hk']
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .r11 + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega_arith)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega_arith)] at ha ⊢
      have := (a - s.gpr .r11).isLt
      omega_arith
    · simp only [List.mem_cons, not_or] at hr
      rw [xs r (by simp [hr.1, hr.2.2]), x₁ r (by simp [hr.1, hr.2.1])]

end VG.Proof.AesXts.X86_64.Vaes

end

end

/-!
# One-pass XTS-AES on x86-64: the blocks left

After the eight-block loop, fewer than eight blocks are left, with their
tweaks at `scratch + 256` on (`GInv b c` with `b = c`). `TInv b c` adds that
`rax` points at the tweak of block `c`. `tbody_ok`: block `c` through the
AES-NI round code `f` on `xmm0`, its tweak XORed in before and after;
`tail_wp` runs it for each block left.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0)
open VG.Impl.AesXts.X86_64Vaes (bufOff tPre tPost)
open VG.Proof.AesXts (b16)
open VG.Proof.Aes.X86_64.AesNi (st inRegions_wr ofInt_natCast XFrame)

/-- `f` computes the cipher (or its inverse) on `xmm0`. -/
def Blk1 (enc : Bool) (f : List XReg → Prog isa) (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s, KP s → WP isa (f [.xmm0]) s fun s' =>
    st (s'.xmm .xmm0) = stF enc (R s₀) (wK s₀) (st (s.xmm .xmm0)) ∧ XFrame [.xmm8, .xmm0] s s'

/-- In the tail: `rax` points at the tweak of block `c`. -/
structure TInv (enc : Bool) (KP : State → Prop) (s₀ : State) (b c : Nat) (s : State) : Prop where
  g : GInv enc KP s₀ b c s
  bc : b ≤ c
  lt : N s₀ < b + 8
  rax : s.gpr .rax = slot s₀ (c - b)

/-- `n` blocks from block `c` lie in the data. -/
theorem group_data_n {s₀ : State} {c n : Nat} (hc : c + n ≤ N s₀) : Region.Sub ⟨blk s₀ c, 16 * n⟩ (dataR s₀) := by
  rw [blk]; exact Offset.sub_base _ (by omega_arith)

/-- Block `c` through `f` on `xmm0`, and the pointers advanced. -/
theorem tbody_ok {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk1 enc f KP s₀) (rs : List XReg) (n : Nat)
    (hrs : rs = [.xmm0] ∧ n = 1)
    {b c : Nat} (hc : c + n ≤ N s₀) {s : State} (h : TInv enc KP s₀ b c s) :
    WP isa (.seq (.block (tPre rs 0)) (.seq (f rs) (.block (tPost rs 0 ++
        ([.alu .add .r11 (.imm (BitVec.ofNat 32 (16 * n))), .alu .add .rax (.imm (BitVec.ofNat 32 (16 * n))),
          .alu .sub .r9 (.imm (BitVec.ofNat 32 n))] : List Instr))))) s fun s' =>
      TInv enc KP s₀ b (c + n) s' ∧ s'.zf = some (decide (N s₀ - (c + n) = 0)) := by
  obtain ⟨hrs1, hn1⟩ := hrs
  obtain hlen : rs.length = n := by rw [hrs1, hn1]; rfl
  obtain hnd : (XReg.xmm9 :: rs).Nodup := by rw [hrs1]; decide
  have hg := h.g
  have hw := hp.data_wrap
  have hsw := hp.scr_wrap
  have hlt := h.lt
  have hbc := h.bc
  obtain hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [hg.wr, hp.wr]
  obtain inD : ∀ k < rs.length, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int)) 16 := by
    intro k hk
    refine ⟨dataR s₀, by rw [hW]; simp, ?_⟩
    rw [hg.r11, ofInt_natCast, blk, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain inT : ∀ k < rs.length, InRegions s.wr (s.gpr .rax + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int)) 16 := by
    intro k hk
    refine ⟨scrR s₀, by rw [hW]; simp, ?_⟩
    rw [h.rax, ofInt_natCast, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by simp only [bufOff]; omega_arith) (by simp only [bufOff]; omega_arith)
  -- The tweaks XORed in.
  refine WP.seq (WP.mono (tPreList_ok rs 0 s hnd (fun k hk => inRegions_wr (inD k hk))
    (fun k hk => inRegions_wr (inT k hk))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  obtain kp₁ : KP s₁ := hst s s₁ hg.kp (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) rd₁ wr₁
    (by rw [m₁]; exact Frame.refl _ _)
  -- The rounds.
  obtain hf' : WP isa (f rs) s₁ fun s' =>
      st (s'.xmm .xmm0) = stF enc (R s₀) (wK s₀) (st (s₁.xmm .xmm0)) ∧ XFrame [.xmm8, .xmm0] s₁ s' := by
    rw [hrs1]; exact hf s₁ kp₁
  refine WP.seq (WP.mono hf' fun s₂ ⟨e₂', f₂⟩ => ?_)
  obtain e₂ : ∀ b ∈ rs, st (s₂.xmm b) = stF enc (R s₀) (wK s₀) (st (s₁.xmm b)) := fun b hb => by
    rw [hrs1] at hb; simp only [List.mem_singleton] at hb; subst hb; exact e₂'
  obtain g₂ : s₂.gpr = s.gpr := f₂.gpr.trans g₁
  obtain m₂ : s₂.mem = s.mem := f₂.mem.trans m₁
  obtain wr₂ : s₂.wr = s.wr := f₂.wr.trans wr₁
  obtain rd₂ : s₂.rd = s.rd := f₂.rd.trans rd₁
  obtain kp₂ : KP s₂ := hst s₁ s₂ kp₁ (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr])
    f₂.rd f₂.wr (by rw [f₂.mem]; exact Frame.refl _ _)
  -- The tweaks XORed in again, and the blocks stored.
  rw [WP.block_append_iff]
  obtain hr11N : (s.gpr .r11).toNat = (Dp s₀).toNat + 16 * c := by rw [hg.r11]; exact hp.blk_toNat (by omega_arith)
  refine WP.mono (tPostList_ok rs 0 s₂ hnd (fun k hk => by rw [wr₂, g₂]; exact inD k hk)
    (fun k hk => by rw [rd₂, wr₂, g₂]; exact inRegions_wr (inT k hk)) (by rw [g₂, hr11N]; omega_arith)
    (fun k hk => by
      rw [g₂, h.rax, hg.r11, Nat.mul_zero, BitVec.add_zero, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ((hp.data_scr.sub_left (group_data_n (s₀ := s₀) (c := c) (n := rs.length) (by omega_arith))).sub_right
        (UPre.scr_sub (by simp only [bufOff]; omega_arith))).symm))
    fun s₃ ⟨e₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  rw [g₂, hg.r11, Nat.mul_zero, BitVec.add_zero, m₂, hlen] at f₃
  rw [g₂, m₂] at e₃
  obtain g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  obtain kp₃ : KP s₃ := hst s₂ s₃ kp₂ (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) rd₃ wr₃ (by
    rw [m₂]; exact f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  obtain hdata : ∀ k < N s₀, bytesAt s₃.mem (blk s₀ k) 16 = if k < c + n then outBlk enc s₀ k
      else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    by_cases hin : c ≤ k ∧ k < c + n
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega_arith⟩
      obtain hi : i < rs.length := by omega_arith
      obtain ab : blk s₀ (c + i) = s.gpr .r11 + BitVec.ofNat 64 (16 * (0 + i)) := by
        rw [hg.r11, blk, blk, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
      obtain sl : slot s₀ (c - b + i) = s.gpr .rax + BitVec.ofNat 64 (16 * (0 + i)) := by
        rw [h.rax, slot, slot, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
      rw [bytesAt_b16, ab, e₃ _ hi, ← sl, ← ab]
      obtain e1 := e₁ _ hi
      rw [← ab, ← sl] at e1
      obtain hc' : st (s₂.xmm rs[i]) = stF enc (R s₀) (wK s₀)
          (st (s.mem.readW (blk s₀ (c + i)) 128 ^^^ s.mem.readW (slot s₀ (c - b + i)) 128)) := by
        rw [e₂ _ (List.getElem_mem hi), e1]
      rw [xts_word enc (R s₀) (wK s₀) _ _ _ hc', ← bytesAt_b16, ← bytesAt_b16, hg.buf _ (by omega_arith),
        hg.data _ hk, show b + (c - b + i) = c + i by omega_arith]
      simp only [show ¬ c + i < c by omega_arith, ite_false, show c + i < c + n by omega_arith, ite_true]
    · rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [blk, blk]
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), hg.data k hk]
      by_cases hlt' : k < c
      · simp only [hlt', ite_true, show k < c + n by omega_arith]
      · simp only [hlt', ite_false, show ¬ k < c + n by omega_arith]
  obtain hbuf : ∀ j < 8, bytesAt s₃.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (b + j) := fun j hj => by
    rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.data_scr.sub_left (group_data_n hc)).sub_right (slot_scr (j := j) (by omega_arith))).symm) (by decide), hg.buf j hj]
  obtain fr : Frame [dataR s₀, scrR s₀] s₀.mem s₃.mem :=
    hg.frame.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  obtain hrd : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hg.rd]
  obtain hwr : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hg.wr]
  -- `add r11, 16 n`, `add rax, 16 n` and `sub r9, n`.
  obtain e16 : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * n)) = BitVec.ofNat 64 (16 * n) := by rw [hn1]; decide
  obtain e1 : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by rw [hn1]; decide
  obtain hr11 : s₃.gpr .r11 = blk s₀ c := by rw [g₃', hg.r11]
  obtain hrax : s₃.gpr .rax = slot s₀ (c - b) := by rw [g₃', h.rax]
  obtain hr9 : s₃.gpr .r9 = BitVec.ofNat 64 (N s₀ - c) := by rw [g₃', hg.r9]
  obtain hsub : BitVec.ofNat 64 (N s₀ - c) - BitVec.ofNat 64 n = BitVec.ofNat 64 (N s₀ - (c + n)) := by
    rw [Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
  obtain hadd : blk s₀ c + BitVec.ofNat 64 (16 * n) = blk s₀ (c + n) := by
    rw [blk, blk, BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * c + 16 * n = 16 * (c + n) by omega_arith]
  obtain hadd' : slot s₀ (c - b) + BitVec.ofNat 64 (16 * n) = slot s₀ (c + n - b) := by
    rw [slot, slot, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e16, e1, hr11, hrax, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨hst s₃ _ kp₃ (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), hc,
      by simp [g₃', hg.r8], by simp; exact hsub, by simp; exact hadd, by simp [g₃', hg.r10],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h1, h5, h7, g₃', hg.keep r h1 h2 h3 h4 h5 h6 h7],
      hrd, hwr, fr, hdata, hbuf, by simp [g₃', hg.rdx]⟩, by omega_arith, hlt, by simp; exact hadd'⟩, ?_⟩
  simp only [hsub]
  exact Aes.X86_64.AesNi.Ecb.beq_ofNat_zero' (by have := (s₀.gpr .r8).isLt; omega_arith)

open VG.Impl.AesXts.X86_64Vaes (tail tail1)

/-- The blocks left, one at a time. -/
theorem tail_wp {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk1 enc f KP s₀) {c : Nat} (hlt : N s₀ < c + 8) {s : State}
    (h : GInv enc KP s₀ c c s) :
    WP isa (tail f) s (TInv enc KP s₀ c (N s₀)) := by
  have hle := h.le
  obtain hn := (s₀.gpr .r8).isLt
  -- `mov rax, r8`, `add rax, 256` and `test r9, r9`.
  obtain e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have hr8 := h.r8
  have hr9 := h.r9
  obtain st₁ : WP isa (.block [.mov .rax (.reg .r8), .alu .add .rax (.imm 256), .alu .test .r9 (.reg .r9)]) s
      fun s₁ => TInv enc KP s₀ c c s₁ ∧ s₁.zf = some (decide (N s₀ - c = 0)) := by
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      arithFlags, State.setFlags, State.setReg, e256, hr8, hr9, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨hst s _ h.kp (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), h.le,
      by simp [hr8], by simp [hr9], by simp [h.r11], by simp [h.r10],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h1, h.keep r h1 h2 h3 h4 h5 h6 h7],
      h.rd, h.wr, h.frame, h.data, h.buf, by simp [h.rdx]⟩, Nat.le_refl _, hlt, ?_⟩, ?_⟩
    · simp only [ite_true, Nat.sub_self, slot, Nat.mul_zero, Nat.add_zero, bufOff]; rfl
    · simp only [BitVec.and_self]
      rw [Aes.X86_64.AesNi.Ecb.beq_ofNat_zero' (k := N s₀ - c) (by omega_arith)]
  refine WP.seq (WP.mono st₁ fun s₃ ⟨h₃, zf₃⟩ => ?_)
  -- One block at a time.
  refine WP.ite (decide (N s₀ - c = 0)) (by simp [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · simp at hz
    exact WP.block_nil (by rw [show N s₀ = c by omega_arith]; exact h₃)
  · simp at hz
    let I : Nat → State → Prop := fun m t => ∃ d, m = N s₀ - d ∧ d < N s₀ ∧ TInv enc KP s₀ c d t
    obtain hstep : ∀ m t, I m t → WP isa (tail1 f) t (fun t' =>
        (eval .ne t' = some false ∧ TInv enc KP s₀ c (N s₀) t') ∨
        (eval .ne t' = some true ∧ ∃ m' < m, I m' t')) := by
      rintro m t ⟨d, rfl, hd, hI⟩
      refine WP.mono (tbody_ok hp hst hf [.xmm0] 1 ⟨rfl, rfl⟩ (by omega_arith) hI) fun t' ⟨hI', zf'⟩ => ?_
      by_cases hz' : N s₀ - (d + 1) = 0
      · exact .inl ⟨by simp [eval, zf', hz'], by rw [show N s₀ = d + 1 by omega_arith]; exact hI'⟩
      · exact .inr ⟨by simp [eval, zf', hz'], N s₀ - (d + 1), by omega_arith, d + 1, rfl, by omega_arith, hI'⟩
    exact WP.loop (M := isa) I hstep (N s₀ - c) s₃ ⟨c, rfl, by omega_arith, h₃⟩

end VG.Proof.AesXts.X86_64.Vaes

end

end

/-! ### `AesXts.X86_64.Vaes.Setup`, which this module and modules that import it used -/

section

/-!
# One-pass XTS-AES on x86-64: the arguments and the first eight tweaks

`enter` moves the arguments and loads the tweak into `rax` and `rcx`; `gen`
stores the tweaks of blocks `0 … 7` at `scratch + 256`, multiplying by `α`
in registers between them (`genStep_ok`, `gen_ok`), and puts the last round
key's address in `r10` (`gen_all_ok`). `SInv`: the state during, and
`SInvK` after, from which `GInv 0 0` follows for anything the rounds need
that it keeps.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0)
open VG.Impl.AesXts.X86_64Vaes (bufOff enter mulAr genStep gen)
open VG.X86_64.RegUpd
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at ofInt_natCast)

/-- During `gen`, after `n` tweaks. -/
structure SInv (s₀ : State) (n : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = S s₀
  r9 : s.gpr .r9 = BitVec.ofNat 64 (N s₀)
  r11 : s.gpr .r11 = Dp s₀
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scrR s₀] s₀.mem s.mem
  buf : ∀ j < n, bytesAt s.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) j
  rdx : s.gpr .rdx = Iv s₀
  tw : tw (s.gpr .rax) (s.gpr .rcx) = Spec.Xts.next (iv0 s₀) n

/-- After `gen`: the tweaks, and the last round key's address in `r10`. -/
def SInvK (s₀ s : State) : Prop := SInv s₀ 8 s ∧ s.gpr .r10 = W s₀ + BitVec.ofNat 64 (16 * R s₀)

theorem mulAr_ok (s : State) :
    ∃ s', runBlock isa mulAr s = some s' ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.gpr .rax = (s.gpr .rax <<< 1) ^^^ (if (s.gpr .rcx).msb then (0x87 : BitVec 64) else 0) ∧
      s'.gpr .rcx = (s.gpr .rcx <<< 1) ||| (if (s.gpr .rax).msb then (1 : BitVec 64) else 0) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, mulAr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, cf_setReg, cf_arithFlags]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ => ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, h₁, h₂, h₃]
  · simp only [gpr_setReg, ↓reduceIte, carry_self, add_self, mask_87]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, carry_self, carry_self_c, add_self,
      shl_add_bit]

theorem genStep_ok {s₀ : State} (hp : UPre s₀) {n : Nat} (hn : n < 8) {s : State} (h : SInv s₀ n s) :
    WP isa (.block (genStep n)) s (SInv s₀ (n + 1)) := by
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have a0 : s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 16 * n : Nat) : Int) = slot s₀ n := by
    rw [h.r8, ofInt_natCast]
  have a8 : s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 16 * n + 8 : Nat) : Int) = slot s₀ n + BitVec.ofNat 64 8 := by
    rw [h.r8, ofInt_natCast, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
  have in0 : InRegions s.wr (slot s₀ n) 8 := ⟨scrR s₀, by rw [hW]; simp,
    Offset.contains_base _ (by simp only [bufOff]; omega_using [hn]) (by simp only [bufOff]; omega_using [hn])⟩
  have in8 : InRegions s.wr (slot s₀ n + BitVec.ofNat 64 8) 8 := ⟨scrR s₀, by rw [hW]; simp, by
    rw [slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by simp only [bufOff]; omega_using [hn]) (by simp only [bufOff]; omega_using [hn])⟩
  rw [genStep, WP.block_append_iff]
  have st₁ : WP isa (.block [.store (at_ .r8 (bufOff + 16 * n)) .rax, .store (at_ .r8 (bufOff + 16 * n + 8)) .rcx]) s
      fun s₁ => s₁.mem = (s.mem.writeW (slot s₀ n) (s.gpr .rax)).writeW (slot s₀ n + BitVec.ofNat 64 8) (s.gpr .rcx) ∧
        s₁.gpr = s.gpr ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_at, a0, a8, in0, in8, ↓reduceIte,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial⟩
  refine WP.mono st₁ fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => ?_
  obtain ⟨s₂, run₂, g₂, rax₂, rcx₂, m₂, rd₂, wr₂⟩ := mulAr_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have fS : Frame [⟨slot s₀ n, 16⟩] s.mem s₂.mem := by rw [m₂, m₁]; exact AesCbc.frame_store2 _ _ _
  have hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [g₂ r h1 h2 h3, g₁]
  refine ⟨by rw [hg _ (by decide) (by decide) (by decide), h.r8], by rw [hg _ (by decide) (by decide) (by decide), h.r9],
    by rw [hg _ (by decide) (by decide) (by decide), h.r11],
    fun r h1 h2 h3 h4 h5 h6 h7 => by rw [hg r h1 h2 h6, h.keep r h1 h2 h3 h4 h5 h6 h7],
    by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr],
    h.frame.trans (fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, slot_scr (j := n) (by omega_using [hn])⟩), fun j hj => ?_,
    by rw [hg _ (by decide) (by decide) (by decide), h.rdx], ?_⟩
  · by_cases hjn : j = n
    · subst hjn
      rw [m₂, m₁, Proof.Cmac.bytesAt_store2, ← h.tw]
    · rw [AesCbc.X86_64.bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_using [hjn]) (by simp only [bufOff]; omega_using [hn, hj]) (by simp only [bufOff]; omega_using [hn]))
        (by decide), h.buf j (by omega_using [hj, hjn])]
  · rw [rax₂, rcx₂, mulAlpha_le8, g₁, h.tw]; rfl

theorem gen_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : SInv s₀ 0 s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap genStep)) s (SInv s₀ n)
  | 0, _ => WP.block_nil h
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (gen_ok hp h n (by omega_using [hn])) fun s₁ h₁ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact genStep_ok hp (by omega_using [hn]) h₁

/-- The last round key's address, `rdi + 16 · rounds`, into `r10`. -/
theorem lastKey_ok {s₀ : State} {s : State} (h : SInv s₀ 8 s) :
    WP isa (.block ([.mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
      .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)] : List Instr)) s
      (SInvK s₀) := by
  have hrsi := h.keep .rsi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrdi := h.keep .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    arithFlags, State.setFlags, State.setReg, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.r8], by simp [h.r9], by simp [h.r11], fun r h1 h2 h3 h4 h5 h6 h7 => by
    simp [h6, h.keep r h1 h2 h3 h4 h5 h6 h7], h.rd, h.wr, h.frame, h.buf, by simp [h.rdx], by simpa using h.tw⟩, ?_⟩
  simp only [↓reduceIte, hrsi, hrdi, W, R]
  bv_omega

theorem gen_all_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : SInv s₀ 0 s) :
    WP isa (.block gen) s (SInvK s₀) := by
  rw [gen, WP.block_append_iff]
  exact WP.mono (gen_ok hp h 8 (Nat.le_refl _)) fun s₁ h₁ => lastKey_ok h₁

/-- The arguments moved. -/
theorem enter_ok {s₀ : State} (hp : UPre s₀) : WP isa (.block enter) s₀ (SInv s₀ 0) := by
  have hIv8 : InRegions (s₀.rd ++ s₀.wr) (Iv s₀ + BitVec.ofNat 64 8) 8 := ⟨ivR s₀, by rw [hp.wr]; simp, AesCbc.X86_64.cIv8⟩
  have z0 : BitVec.ofInt 64 ((0 : Nat) : Int) = 0 := rfl
  have z8 : BitVec.ofInt 64 ((8 : Nat) : Int) = BitVec.ofNat 64 8 := rfl
  have hIv : InRegions (s₀.rd ++ s₀.wr) (Iv s₀) 8 := ⟨ivR s₀, by rw [hp.wr]; simp, AesCbc.X86_64.cIv0⟩
  have hIv0 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdx + 0) 8 := by simpa using hIv
  apply WP.of_runBlock
  simp only [enter, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.setReg, State.load64, ea_at, z0, z8, hIv0, hIv8,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by simp, by simp, by simp, fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h1, h2, h4, h5, h7],
    rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _), by simp, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte]
  rw [show s₀.gpr .rdx + 0 = Iv s₀ by simp, tw_readW]
  rfl

end VG.Proof.AesXts.X86_64.Vaes

end

end

/-!
# One-pass XTS-AES on x86-64: the whole function

`crypt_wp`: `crypt pre L f` meets the contract of `vg_aes_xts_encrypt` (or
`vg_aes_xts_decrypt`), given that `pre` sets up what the rounds need (`KP`)
without disturbing the tweaks, that the loop `L` takes groups of eight blocks
(`LoopOk`; `loop8_ok` for `loop8`), and that `f` computes the cipher (or its
inverse) on `xmm0`.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0 modeX86_64)
open VG.Impl.AesXts.X86_64Vaes (bufOff finish)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at ofInt_natCast)

theorem getElem_tweaks (t : List Byte) {n k : Nat} (hk : k < n) :
    (Spec.Xts.tweaks t n)[k]'(by rw [AesXts.length_tweaks]; exact hk) = Spec.Xts.next t k := by
  induction n generalizing t k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [Spec.Xts.tweaks, List.getElem_cons_succ]; rw [ih _ (by omega_using [hk]), AesXts.next_succ']

/-- After the setup, with what the rounds need. -/
theorem SInvK.ginv {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) {s : State} (hk : SInvK s₀ s)
    (hkp : KP s) : GInv enc KP s₀ 0 0 s :=
  have h := hk.1
  { kp := hkp
    le := Nat.zero_le _
    r8 := h.r8
    r9 := by rw [h.r9, Nat.sub_zero]
    r11 := by rw [h.r11, blk, Nat.mul_zero]; exact (BitVec.add_zero _).symm
    r10 := hk.2
    keep := h.keep
    rd := h.rd
    wr := h.wr
    frame := h.frame.mono fun r hr => by simp at hr; simp [hr]
    data := fun k hk => by
      simp only [Nat.not_lt_zero, ite_false]
      exact AesCbc.X86_64.bytesAt_frame h.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.data_scr.sub_left (UPre.data_sub hk)) (by decide)
    buf := fun j hj => by rw [h.buf j hj, Nat.zero_add]
    rdx := h.rdx }

/-- The contract, from `GInv … N` and the tweak after the last block stored. -/
theorem post_of {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) {b : Nat} {s : State}
    (h : GInv enc KP s₀ b (N s₀) s) (s' : State) (hf : Frame [ivR s₀] s.mem s'.mem)
    (hiv : bytesAt s'.mem (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) (N s₀))
    (hgs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s₀ s' := by
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · rw [hgs r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [hf.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.ret_iv) (by decide),
      h.frame.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.ret_data
        · exact hp.ret_scr) (by decide)]
  · show Spec.Cbc.blocksAt s'.mem (Dp s₀) (N s₀) = Spec.Xts.crypt (ciphOf enc (R s₀) (wK s₀)) (iv0 s₀)
      (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀))
    apply List.ext_getElem (by rw [AesXts.length_crypt, AesCbc.length_blocksAt, AesCbc.length_blocksAt])
    intro k h₁ h₂
    have hk : k < N s₀ := by rwa [AesCbc.length_blocksAt] at h₁
    rw [AesCbc.getElem_blocksAt _ _ hk]
    simp only [Spec.Xts.crypt, List.getElem_zipWith]
    rw [getElem_tweaks _ (by rwa [AesCbc.length_blocksAt]), AesCbc.getElem_blocksAt _ _ hk,
      AesCbc.X86_64.bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.iv_data.sub_right (UPre.data_sub hk)).symm)
        (by decide), h.data k hk]
    simp only [hk, ite_true]
  · show bytesAt s'.mem (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀)).length
    rw [AesCbc.length_blocksAt, hiv]

/-- The tweak after the last block copied to the tweak pointer. -/
theorem finish_wp {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) {b : Nat} {s : State}
    (h : TInv enc KP s₀ b (N s₀) s) :
    WP isa (.block finish) s fun s' => gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s₀ s' := by
  have hg := h.g
  have hsw := hp.scr_wrap
  have hlt := h.lt
  have hbc := h.bc
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [hg.wr, hp.wr]
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [hg.rd, hW, hp.rd]; rfl
  have z0 : BitVec.ofInt 64 ((0 : Nat) : Int) = 0#64 := rfl
  have z8 : BitVec.ofInt 64 ((8 : Nat) : Int) = BitVec.ofNat 64 8 := rfl
  let T := slot s₀ (N s₀ - b)
  have inT0 : InRegions (s.rd ++ s.wr) (s.gpr .rax + 0#64) 8 := ⟨scrR s₀, by rw [hR]; simp, by
    rw [h.rax]; simpa using Offset.contains_base (S s₀) (d := bufOff + 16 * (N s₀ - b)) (n := 8) (k := 2176)
      (by simp only [bufOff]; omega_using [hlt]) (by simp only [bufOff]; omega_using [hlt])⟩
  have inI0 : InRegions s.wr (Iv s₀ + 0#64) 8 := ⟨ivR s₀, by rw [hW]; simp, by simpa using AesCbc.X86_64.cIv0⟩
  have inI8 : InRegions s.wr (Iv s₀ + BitVec.ofNat 64 8) 8 := ⟨ivR s₀, by rw [hW]; simp, AesCbc.X86_64.cIv8⟩
  have inT8 : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 8) 8 := ⟨scrR s₀, by rw [hR]; simp, by
    rw [h.rax, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by simp only [bufOff]; omega_using [hlt]) (by simp only [bufOff]; omega_using [hlt])⟩
  have hrdx := hg.rdx
  apply WP.of_runBlock
  simp only [finish, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.setReg, State.load64, State.store64, ea_at, z0, z8, hrdx, inT0, inT8, inI0, inI8,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [BitVec.add_zero]
  have hT8 : Region.Disjoint ⟨T + BitVec.ofNat 64 8, 8⟩ ⟨Iv s₀, 8⟩ := by
    have hiv : Region.Disjoint (scrR s₀) ⟨Iv s₀, 8⟩ :=
      hp.iv_scr.symm.sub_right (Region.sub_prefix (len := 8) (len' := 16) (by decide))
    refine hiv.sub_left ?_
    show Region.Sub ⟨slot s₀ (N s₀ - b) + BitVec.ofNat 64 8, 8⟩ (scrR s₀)
    rw [slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.sub_base _ (by simp only [bufOff]; omega_using [hlt])
  have f1 : Frame [⟨Iv s₀, 8⟩] s.mem (s.mem.writeW (Iv s₀) (s.mem.readW T 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [h.rax]
  refine post_of hp hg _ (AesCbc.frame_store2 _ _ _) ?_ fun r hr => ?_
  · rw [Proof.Cmac.bytesAt_store2, f1.readW (r := ⟨T + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hT8) (by decide)]
    rw [← tw, tw_readW, hg.buf _ (by omega_using [hlt]), show b + (N s₀ - b) = N s₀ by omega_using [hbc]]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

open VG.Impl.AesXts.X86_64Vaes (crypt enter gen loop8)

/-- `L` takes groups of eight blocks while eight are left: from `GInv 0 0`,
with `cmp r9, 8` done, to `GInv c c` with fewer than eight left. -/
def LoopOk (enc : Bool) (L : Prog isa) (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s, GInv enc KP s₀ 0 0 s → s.cf = some (decide (N s₀ < 8)) →
    WP isa L s fun s' => ∃ c, N s₀ - c < 8 ∧ GInv enc KP s₀ c c s'

theorem loop8_ok {enc : Bool} {KP : State → Prop} {f8 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf8 : Blk8 enc f8 KP s₀) : LoopOk enc (loop8 f8) KP s₀ :=
  fun _ h hcf => groups_wp hp hst hf8 h (by rw [hcf, Nat.sub_zero])

/-- The function's body, with at least one block. -/
theorem body_wp {enc : Bool} {KP : State → Prop} {pre L : Prog isa} {f : List XReg → Prog isa} {s₀ : State}
    (hp : UPre s₀) (hst : Stable KP s₀) (hL : LoopOk enc L KP s₀) (hf : Blk1 enc f KP s₀)
    (hpre : ∀ s, SInvK s₀ s → WP isa pre s fun s' => SInvK s₀ s' ∧ KP s') :
    WP isa (.seq (.block (enter ++ gen)) (.seq pre (.seq (.block [.alu .cmp .r9 (.imm 8)])
      (.seq L (.seq (Impl.AesXts.X86_64Vaes.tail f) (.block finish)))))) s₀
      fun s' => gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s₀ s' := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (enter_ok hp) fun s₁ h₁ => WP.mono (gen_all_ok hp h₁) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (hpre s₂ h₂) fun s₃ ⟨h₃, kp₃⟩ => ?_)
  have g₃ := SInvK.ginv (enc := enc) hp h₃ kp₃
  refine WP.seq (WP.mono (cmp8_ok hst g₃) fun s₄ ⟨g₄, cf₄⟩ => ?_)
  refine WP.seq (WP.mono (hL s₄ g₄ (by simpa using cf₄)) fun s₅ ⟨c, hc, g₅⟩ => ?_)
  exact WP.seq (WP.mono (tail_wp hp hst hf (by omega_using [hc]) g₅) fun s₆ h₆ => finish_wp hp h₆)

/-- The whole function. -/
theorem crypt_wp {enc : Bool} {KP : State → State → Prop} {pre L : Prog isa} {f : List XReg → Prog isa} {s₀ : State}
    (h0 : (modeX86_64 (AesXts.xtsMode enc)).pre s₀)
    (hst : ∀ s₁ : State, UPre s₁ → Stable (KP s₁) s₁)
    (hL : ∀ s₁ : State, UPre s₁ → LoopOk enc L (KP s₁) s₁)
    (hf : ∀ s₁ : State, UPre s₁ → Blk1 enc f (KP s₁) s₁)
    (hpre : ∀ s₁ : State, UPre s₁ → ∀ s, SInvK s₁ s → WP isa pre s fun s' => SInvK s₁ s' ∧ KP s₁ s') :
    WP isa (crypt pre L f) s₀ fun s' => gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s₀ s' := by
  have hn : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  have st : WP isa (.block [.alu .test .r8 (.reg .r8)]) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.zf = some (decide (N s₀ = 0)) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp only [arithFlags, State.setFlags, BitVec.and_self]
    have e : s₀.gpr .r8 = BitVec.ofNat 64 (N s₀) := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [e, Aes.X86_64.AesNi.Ecb.beq_ofNat_zero' hn]
  refine WP.seq (WP.mono st fun s₁ ⟨g, m, rd, wr, zf⟩ => ?_)
  refine WP.ite (decide (N s₀ = 0)) (by simp [eval, zf]) (fun hz => ?_) (fun hz => ?_)
  · simp at hz
    refine WP.block_nil ⟨⟨fun r _ => by rw [g], by rw [m]⟩, ?_, ?_⟩
    · show Spec.Cbc.blocksAt s₁.mem (Dp s₀) (N s₀) = Spec.Xts.crypt _ _ (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀))
      rw [hz]; rfl
    · show bytesAt s₁.mem (Iv s₀) 16 = Spec.Xts.next _ (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀)).length
      rw [AesCbc.length_blocksAt, hz, m]; rfl
  · have h1 : (modeX86_64 (AesXts.xtsMode enc)).pre s₁ := by
      simp only [modeX86_64, g, rd, wr]; simpa only [modeX86_64] using h0
    have hp₁ := UPre.of h1
    refine WP.mono (body_wp hp₁ (hst s₁ hp₁) (hL s₁ hp₁) (hf s₁ hp₁) (hpre s₁ hp₁)) fun s' ⟨gp, po⟩ => ?_
    refine ⟨⟨fun r hr => by rw [gp.1 r hr, g], by rw [← m, ← g]; exact gp.2⟩, ?_⟩
    simp only [modeX86_64, g, m] at po ⊢
    exact po

end VG.Proof.AesXts.X86_64.Vaes
