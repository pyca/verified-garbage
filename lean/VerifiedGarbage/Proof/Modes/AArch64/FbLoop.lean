module

public import VerifiedGarbage.Proof.Modes.Fb
public import VerifiedGarbage.Impl.Modes.AArch64.Fb
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Proof.Modes.AArch64.Group
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# OFB and CFB on AArch64, for any core: the data loop

As on x86-64 (`Proof/Modes/X86_64/FbLoop.lean`). `fbOp_wp`: the mode's step
after `crypt` (`fbOp`) XORs the buffer's first block into the data's block
and makes the buffer the next input block (`fbByte`), each a `copyN_wp` or
`xorN_wp`. `fbBlock_wp`: one iteration enciphers the input block `Iⱼ` in
the buffer (`BlockSpec.crypt_wp`), makes block `j` of the data its output
(`fbOut`) and the buffer `Iⱼ₊₁` (`fbIn`). Blocks are `8 bw` bytes.

The IV's address is kept in a register `iv` the core does not write
(`KeepsReg`), which `keepsReg_of_regSafe` checks of the core's code.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Modes (FbMode)
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)

/-! ## Code that keeps a register -/

/-- Every execution of `p` keeps the register `r`: the modes' requirement of
a core's `prepare` and `crypt` for the register holding the IV's address. -/
def KeepsReg (r : Reg) (p : Prog isa) : Prop := ∀ s t s', Exec isa p s t s' → s'.gpr r = s.gpr r

/-- Whether no instruction of `c` writes `r` (`keepsReg`), with no calls or
frames. -/
def regSafe (r : Reg) : Prog isa → Bool
  | .block is => is.all (keepsReg r)
  | .seq a b => regSafe r a && regSafe r b
  | .ite _ a b => regSafe r a && regSafe r b
  | .loop b _ => regSafe r b
  | _ => false

theorem keepsReg_of_regSafe {r : Reg} {c : Prog isa} (hc : regSafe r c = true) : KeepsReg r c := by
  intro s t s' h
  revert hc
  induction h with
  | icall | icallNext => intro hc; simp only [regSafe, Bool.false_eq_true] at hc
  | block e => exact fun hc => keepsReg_ok hc e
  | seq _ _ ih₁ ih₂ =>
    intro hc
    simp only [regSafe, Bool.and_eq_true] at hc
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  | iteT _ _ ih => intro hc; simp only [regSafe, Bool.and_eq_true] at hc; exact ih hc.1
  | iteF _ _ ih => intro hc; simp only [regSafe, Bool.and_eq_true] at hc; exact ih hc.2
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => intro hc; exact (ih₂ hc).trans (ih₁ hc)
  | call => intro hc; simp only [regSafe, Bool.false_eq_true] at hc
  | frame => intro hc; simp only [regSafe, Bool.false_eq_true] at hc

theorem KeepsReg.seq {r : Reg} {a b : Prog isa} (ha : KeepsReg r a) (hb : KeepsReg r b) :
    KeepsReg r (.seq a b) := by
  intro s t s' h
  cases h with
  | seq h₁ h₂ => exact (hb _ _ _ h₂).trans (ha _ _ _ h₁)

theorem KeepsReg.ite {r : Reg} {c : isa.Cond} {a b : Prog isa} (ha : KeepsReg r a) (hb : KeepsReg r b) :
    KeepsReg r (.ite c a b) := by
  intro s t s' h
  cases h with
  | iteT _ h => exact ha _ _ _ h
  | iteF _ h => exact hb _ _ _ h

theorem KeepsReg.loop {r : Reg} {b : Prog isa} {c : isa.Cond} (hb : KeepsReg r b) : KeepsReg r (.loop b c) := by
  intro s t s' h
  generalize hc : (Code.loop b c : Prog isa) = p at h
  induction h with
  | loopExit h₁ _ => cases hc; exact hb _ _ _ h₁
  | loopNext h₁ _ _ _ ih => cases hc; exact (ih rfl).trans (hb _ _ _ h₁)
  | _ => cases hc

theorem WP.keepReg {r : Reg} {p : Prog isa} (h : KeepsReg r p) {s : State} {Q : State → Prop} (w : WP isa p s Q) :
    WP isa p s fun t => Q t ∧ t.gpr r = s.gpr r :=
  let ⟨t, s', e, q⟩ := w
  ⟨t, s', e, q, h _ _ _ e⟩

variable {c : Core}

/-- The step after `crypt`, on the data's block at `A` (in `dataReg`) and the
buffer's first block at `T`. -/
theorem fbOp_wp (mo : FbMode) (hbI : 8 * c.buf + 8 * c.bw ≤ 32768) (hb8 : 8 * c.bw ≤ 32768) {s : State} {A T : Addr}
    (hA : s.gpr c.dataReg = A) (hT : s.gpr sb + BitVec.ofNat 64 (8 * c.buf) = T) (d6 : c.dataReg ≠ .x6)
    (d7 : c.dataReg ≠ .x7)
    (wA : ∀ w < c.bw, InRegions s.wr (A + BitVec.ofNat 64 (8 * w)) 8)
    (wT : ∀ w < c.bw, InRegions s.wr (T + BitVec.ofNat 64 (8 * w)) 8)
    (sep : Region.Disjoint ⟨A, 8 * c.bw⟩ ⟨T, 8 * c.bw⟩) (fit : 8 * c.bw ≤ 2 ^ 64) :
    WP isa (.block (c.fbOp mo)) s fun s' => (∀ x, x ≠ .x6 → x ≠ .x7 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ u < 8 * c.bw, s'.mem (A + BitVec.ofNat 64 u) =
        s.mem (A + BitVec.ofNat 64 u) ^^^ s.mem (T + BitVec.ofNat 64 u)) ∧
      (∀ u < 8 * c.bw, s'.mem (T + BitVec.ofNat 64 u) =
        fbByte mo (s.mem (T + BitVec.ofNat 64 u)) (s.mem (A + BitVec.ofNat 64 u))) ∧
      Frame [⟨A, 8 * c.bw⟩, ⟨T, 8 * c.bw⟩] s.mem s'.mem := by
  have p0 : ∀ X : Addr, X + BitVec.ofNat 64 0 = X := fun X => by simp
  have hx : NPre c.bw s .x6 .x7 c.dataReg sb 0 (8 * c.buf) A T :=
    ⟨by rw [hA, p0], hT, Ne.symm d6, by decide, Ne.symm d7, by decide, by decide, by omega_using [], by omega_using [hb8], by omega_using [hbI],
      wA, fun w hw => inRd (wT w hw), sep, fit⟩
  have fA : ∀ {m : Mem} {f : Nat → Byte}, Frame [⟨A, 8 * c.bw⟩, ⟨T, 8 * c.bw⟩] m (over m A (8 * c.bw) f) :=
    (over_frame _ _ _ _).sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
  have fT : ∀ {m : Mem} {f : Nat → Byte}, Frame [⟨A, 8 * c.bw⟩, ⟨T, 8 * c.bw⟩] m (over m T (8 * c.bw) f) :=
    (over_frame _ _ _ _).sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
  cases mo
  · refine WP.mono (xorN_wp hx (by decide)) fun s₁ h₁ => ⟨h₁.regs, h₁.rd, h₁.wr, fun u hu => ?_, fun u hu => ?_, ?_⟩
    · rw [h₁.mem, over_at hu fit]
    · rw [h₁.mem, over_sep sep hu fit]; rfl
    · rw [h₁.mem]; exact fA
  · refine WP.block_append (WP.mono (xorN_wp hx (by decide)) fun s₁ h₁ => ?_)
    have hy : NPre c.bw s₁ .x6 .x6 sb c.dataReg (8 * c.buf) 0 T A :=
      ⟨by rw [h₁.regs _ (by decide) (by decide)]; exact hT, by rw [h₁.regs _ d6 d7, hA, p0], by decide, Ne.symm d6,
        by decide, Ne.symm d6, by omega_using [], by decide, by omega_using [hbI], by omega_using [hb8],
        fun w hw => by rw [h₁.wr]; exact wT w hw, fun w hw => by rw [h₁.rd, h₁.wr]; exact inRd (wA w hw),
        sep.symm, fit⟩
    refine WP.mono (copyN_wp hy) fun s₂ h₂ => ⟨fun x hx hx' => by rw [h₂.regs x hx hx, h₁.regs x hx hx'],
      by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr], fun u hu => ?_, fun u hu => ?_, ?_⟩
    · rw [h₂.mem, over_sep sep.symm hu fit, h₁.mem, over_at hu fit]
    · rw [h₂.mem, over_at hu fit, h₁.mem, over_at hu fit]; rfl
    · rw [h₂.mem, h₁.mem]; exact fA.trans fT
  · refine WP.block_append (WP.mono (xorN_wp hx (by decide)) fun s₁ h₁ => ?_)
    have hy : NPre c.bw s₁ .x6 .x7 sb c.dataReg (8 * c.buf) 0 T A :=
      ⟨by rw [h₁.regs _ (by decide) (by decide)]; exact hT, by rw [h₁.regs _ d6 d7, hA, p0], by decide, Ne.symm d6,
        by decide, Ne.symm d7, by omega_using [], by decide, by omega_using [hbI], by omega_using [hb8],
        fun w hw => by rw [h₁.wr]; exact wT w hw, fun w hw => by rw [h₁.rd, h₁.wr]; exact inRd (wA w hw),
        sep.symm, fit⟩
    refine WP.mono (xorN_wp hy (by decide)) fun s₂ h₂ => ⟨fun x hx hx' => by rw [h₂.regs x hx hx', h₁.regs x hx hx'],
      by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr], fun u hu => ?_, fun u hu => ?_, ?_⟩
    · rw [h₂.mem, over_sep sep.symm hu fit, h₁.mem, over_at hu fit]
    · rw [h₂.mem, over_at hu fit, h₁.mem, over_at hu fit, over_sep sep hu fit]
      exact xor_xor_cancel _ _
    · rw [h₂.mem, h₁.mem]; exact fA.trans fT

/-- The data loop, before block `j`; `m₀` is the memory on entry, `iv` the
IV. -/
structure FInv (cs : BlockSpec c) (mo : FbMode) (ivR : Reg) (s₀ : State) (m₀ : Mem) (B D : Addr) (n : Nat)
    (k : cs.Key) (iv : List Byte) (j : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  ready : cs.Ready s B k
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * j)
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - j)
  lt : j < n
  buf : ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (fbIn mo (8 * c.bw) (cs.cipher k) m₀ D iv j).getD u 0
  data : ∀ q < n, ∀ r < 8 * c.bw, s.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
    if q < j then (fbOut mo (8 * c.bw) (cs.cipher k) m₀ D iv q).getD r 0
    else m₀ (D + BitVec.ofNat 64 (8 * c.bw * q + r))
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ivK : s.gpr ivR = s₀.gpr ivR

/-- The data loop, done. -/
structure FDone (cs : BlockSpec c) (mo : FbMode) (ivR : Reg) (s₀ : State) (m₀ : Mem) (B D : Addr) (n : Nat)
    (k : cs.Key) (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  buf : ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (fbIn mo (8 * c.bw) (cs.cipher k) m₀ D iv n).getD u 0
  data : DInv (8 * c.bw) m₀ s.mem D n n (fbOut mo (8 * c.bw) (cs.cipher k) m₀ D iv)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ivK : s.gpr ivR = s₀.gpr ivR

theorem fbBlock_wp (cs : BlockSpec c) (mo : FbMode) {ivR : Reg} (hivR : ivR ∉ modeRegs c) {s₀ : State} {m₀ : Mem}
    {B D : Addr} {n : Nat} {k : cs.Key} {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw))
    (hsc : KeepsReg ivR c.crypt) {j : Nat} {s : State} (hi : FInv cs mo ivR s₀ m₀ B D n k iv j s) :
    WP isa (c.fbBlock mo) s fun s' =>
      (isa.eval (.nonzero .x c.leftReg) s' = some false ∧ FDone cs mo ivR s₀ m₀ B D n k iv s') ∨
      (isa.eval (.nonzero .x c.leftReg) s' = some true ∧ FInv cs mo ivR s₀ m₀ B D n k iv (j + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbI := hL.bufImm
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hj := hi.lt
  have hL0 : 0 < 8 * c.bw := by omega_using [hbw0]
  have hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hLn : 8 * c.bw * n = 8 * (c.bw * n) := Nat.mul_assoc _ _ _
  have h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega_using [hL0])
  have hjl := idx_lt (L := 8 * c.bw) hj
  have hj1 : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d6, d7, -⟩ := not_own down
  obtain ⟨l6, l7, -⟩ := not_own lown
  obtain ⟨iown, idr, ilr⟩ := of_not_modeRegs hivR
  obtain ⟨i6, i7, -⟩ := not_own iown
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega_using [hfitD]
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 (8 * c.bw * j)
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have hwS : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subT : Region.Sub ⟨T, 8 * c.bw⟩ ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega_using [hroom, hbuf, hGb])
  have subTbuf : Region.Sub ⟨T, 8 * c.bw⟩ (blkRegion c B) := Region.sub_prefix hLG
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.total⟩ := Region.sub_prefix (by omega_using [hroom])
  have subA : Region.Sub ⟨A, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ := VG.Offset.sub_base D hjl
  have dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.total⟩ → Region.Disjoint ⟨D, 8 * c.bw * n⟩ r :=
    fun h => hp.sep.sub_right h
  have dAT : Region.Disjoint ⟨A, 8 * c.bw⟩ ⟨T, 8 * c.bw⟩ := (dDS subT).sub_left subA
  have hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  have hbj : ∀ w < c.bw, c.bw * j + w < c.bw * n := fun w hw' => by have := idx_lt (L := c.bw) hj; omega_using [hw', this]
  have inT : ∀ w < c.bw, InRegions s.wr (T + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by omega_using [hroom, hbuf, hGb, hw']) (by omega_using [hbI, hbw2, hw'])⟩
  have inA : ∀ w < c.bw, InRegions s.wr (A + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwD, by rw [addr_add, hw]; exact VG.Offset.contains_base D (by have := hbj w hw'; omega_using [hLn, this]) (by have := hbj w hw'; omega_using [hLn, hn64, this])⟩
  have hqr : ∀ {q r}, q < n → r < 8 * c.bw → 8 * c.bw * q + r < 8 * c.bw * n := fun hq hr => by
    have := idx_lt (L := 8 * c.bw) hq; omega_using [hr, this]
  -- Enciphered.
  unfold Core.fbBlock
  refine WP.seq (WP.mono (WP.keepReg hsc (cs.crypt_wp hi.base ⟨hwS, hfit⟩ hi.ready))
    fun s₂ ⟨⟨base₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩, i₂⟩ => ?_)
  have eT : blkAddr c B 0 = T := by simp only [blkAddr, T, Nat.mul_zero, Nat.add_zero]
  have hin : bytesAt s.mem T (8 * c.bw) = fbIn mo (8 * c.bw) ciph m₀ D iv j := by
    apply List.ext_getElem (by
      simp only [bytesAt, List.length_map, List.length_range]; rw [fbIn_length (cs.cipher_len k) m₀ D hiv])
    intro u h1 _
    have hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [hi.buf u hu, List.getElem_eq_getD 0]
  have E₂ : ∀ u < 8 * c.bw, s₂.mem (T + BitVec.ofNat 64 u) = (ciph (fbIn mo (8 * c.bw) ciph m₀ D iv j)).getD u 0 :=
    fun u hu => by rw [← bytesAt_getD s₂.mem T hu, ← eT, ks₂ 0 hG0, eT, hin]
  have D₂ : ∀ q < n, ∀ r < 8 * c.bw, s₂.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      s.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) := fun q hq r hr =>
    f₂.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact dDS subCore) hn64 (hqr hq hr)
  -- The step after `crypt`.
  have data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, hi.dataR]
  refine WP.block_append (WP.mono_syms (fbOp_wp mo (by omega_using [hbI, hbw2]) (by omega_using [hbw2]) data₂ (by rw [base₂]) d6 d7
    (fun w hw' => by rw [wr₂]; exact inA w hw') (fun w hw' => by rw [wr₂]; exact inT w hw') dAT (by omega_using [hjl, hn64]))
    fun s₃a ⟨g₃a, rd₃a, wr₃a, mA₃, mT₃, f₃a⟩ sy₃a => ?_)
  obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b⟩ := addImm_ok s₃a c.dataReg c.dataReg (v := 8 * c.bw) (by omega_using [hbw2])
  obtain ⟨s₃, e₃, l₃, o₃, m₃, rd₃, wr₃⟩ := subImm_ok s₃b c.leftReg c.leftReg (v := 1) (by decide)
  refine WP.of_runBlock ⟨s₃, by
    rw [Core.fbNext, show ([.addImm .x c.dataReg c.dataReg (8 * c.bw), .subImm .x c.leftReg c.leftReg 1] :
      List Instr) = [.addImm .x c.dataReg c.dataReg (8 * c.bw)] ++ [.subImm .x c.leftReg c.leftReg 1] from rfl,
      runBlock_app, e₃b, Option.bind_some, e₃], ?_⟩
  have keep₃ : ∀ x, x ≠ .x6 → x ≠ .x7 → x ≠ c.dataReg → x ≠ c.leftReg → s₃.gpr x = s₂.gpr x :=
    fun x h1 h2 h3 h4 => by rw [o₃ x h4, o₃b x h3, g₃a x h1 h2]
  have left₂ : s₃b.gpr c.leftReg = BitVec.ofNat 64 (n - j) := by
    rw [o₃b _ (Ne.symm hdl), g₃a _ l6 l7, lr₂, hi.leftR]
  have left₃ : s₃.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [l₃, left₂, VG.Offset.ofNat_sub_ofNat (by omega_using [hj]), show n - j - 1 = n - (j + 1) by omega_using []]
  have hz₃ : isa.eval (.nonzero .x c.leftReg) s₃ = some !(decide (j + 1 = n)) := by
    rw [eval_nonzero, left₃, ofNat_beq_zero (by omega_using [h8n, hn64]), decide_eq_decide.mpr (show n - (j + 1) = 0 ↔ j + 1 = n by omega_using [hj])]
  have hAL : A + BitVec.ofNat 64 (8 * c.bw) = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by rw [addr_add, hj1]
  have data₃ : s₃.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by
    rw [o₃ _ hdl, a₃b, g₃a _ d6 d7, data₂, hAL]
  have mem₃ : s₃.mem = s₃a.mem := by rw [m₃, m₃b]
  have base₃ : s₃.gpr sb = B := by
    rw [keep₃ _ (by decide) (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂]
  have ivK₃ : s₃.gpr ivR = s₀.gpr ivR := by rw [keep₃ _ i6 i7 idr ilr, i₂, hi.ivK]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₃b, rd₃a, rd₂, hi.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₃b, wr₃a, wr₂, hi.wr]
  have f₃ : Frame [⟨A, 8 * c.bw⟩, ⟨T, 8 * c.bw⟩] s₂.mem s₃.mem := by rw [mem₃]; exact f₃a
  -- The slots.
  have slotOut : ∀ i < 10, ∀ {R : Region}, (Region.Sub R ⟨D, 8 * c.bw * n⟩ ∨ R = ⟨T, 8 * c.bw⟩ ∨
      R = coreRegion c B) → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi10 R hR => by
    rcases hR with h | rfl | rfl
    · exact ((dDS (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.total by
        omega_using [hroom, hi10]))).sub_left h).symm
    · exact VG.Offset.disjoint B (.inr (by omega_using [hbuf, hGb])) (by omega_using [hroom, hfit, hi10]) (by omega_using [hbI, hbw2])
    · exact VG.Offset.disjoint_base B (by omega_using []) (by omega_using [hroom, hfit, hi10])
  have saved₃ : ∀ i < 10, s₃.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi10 => by
    rw [← hi.saved i hi10]
    refine (f₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slotOut i hi10 (.inl subA)
      · exact slotOut i hi10 (.inr (.inl rfl))) (by decide)).trans ?_
    exact f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi10 (.inr (.inr rfl))) (by decide)
  have fr₃ : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₃.mem :=
    hi.frame.trans ((f₂.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩).trans
      (f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subA⟩
        · exact ⟨_, List.mem_cons_self, subT⟩))
  have ready₃ : cs.Ready s₃ B k := cs.ready_frame ready₂ f₃ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ((dDS subCore).sub_left subA).symm
    · exact .inr subTbuf)
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by rw [wr₂]; exact hwD, subA⟩
      · exact ⟨_, by rw [wr₂]; exact hwS, subT⟩,
      by rw [rd₃, rd₃b, rd₃a], by rw [wr₃, wr₃b, wr₃a],
      by rw [runBlock_syms e₃, runBlock_syms e₃b, sy₃a]⟩ fun r hr => by
    obtain ⟨h1, h2, h3⟩ := of_not_modeRegs hr
    exact keep₃ r (not_own h1).1 (not_own h1).2.1 h2 h3
  -- The buffer and the data.
  have mA : ∀ u < 8 * c.bw, s.mem (A + BitVec.ofNat 64 u) = m₀ (A + BitVec.ofNat 64 u) := fun u hu => by
    rw [addr_add, hi.data j hj u hu, ite_eq_right (Nat.lt_irrefl _)]
  have D₂' : ∀ u < 8 * c.bw, s₂.mem (A + BitVec.ofNat 64 u) = s.mem (A + BitVec.ofNat 64 u) := fun u hu => by
    rw [addr_add]; exact D₂ j hj u hu
  have buf₃ : ∀ u < 8 * c.bw, s₃.mem (T + BitVec.ofNat 64 u) =
      (fbIn mo (8 * c.bw) ciph m₀ D iv (j + 1)).getD u 0 := fun u hu => by
    rw [mem₃, mT₃ u hu, E₂ u hu, fbIn_succ_getD mo (cs.cipher_len k) m₀ D iv j hu, ← addr_add,
      ← mA u hu, D₂' u hu]
  have data₃' : ∀ q < n, ∀ r < 8 * c.bw, s₃.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      if q < j + 1 then (fbOut mo (8 * c.bw) ciph m₀ D iv q).getD r 0
      else m₀ (D + BitVec.ofNat 64 (8 * c.bw * q + r)) := fun q hq r hr => by
    by_cases hqj : q = j
    · rw [ite_eq_left (by omega_using [hqj]), hqj, fbOut_getD mo (cs.cipher_len k) m₀ D iv j hr, mem₃, ← addr_add, mA₃ r hr,
        E₂ r hr, D₂' r hr, mA r hr]
    · have out : ∀ R ∈ [(⟨A, 8 * c.bw⟩ : Region), ⟨T, 8 * c.bw⟩],
          ¬ R.Contains (D + BitVec.ofNat 64 (8 * c.bw * q + r)) 1 := fun R hR => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
        rcases hR with rfl | rfl
        · have := hqr hq hr
          refine not_contains_off D ?_ (by omega_using [hn64, this]) hL0 (by omega_using [hjl, hn64])
          rcases Nat.lt_or_gt_of_ne hqj with h | h
          · have := idx_lt (L := 8 * c.bw) h; omega_arith
          · have := idx_lt (L := 8 * c.bw) h; omega_arith
        · exact fun hc => dDS subT _ (VG.Offset.contains_base D (by have := hqr hq hr; omega_using [this]) (by have := hqr hq hr; omega_using [hn64, this])) hc
      rw [mem₃, f₃a _ out, D₂ q hq r hr, hi.data q hq r hr]
      by_cases h3 : q < j
      · rw [ite_eq_left h3, ite_eq_left (by omega_using [h3])]
      · rw [ite_eq_right h3, ite_eq_right (by omega_using [hqj, h3])]
  by_cases hdone : j + 1 = n
  · exact .inl ⟨by rw [hz₃, decide_eq_true hdone]; rfl, base₃, saved₃, by rw [← hdone]; exact buf₃,
      dinv_of_blocks hL0 fun q hq r hr => by rw [data₃' q hq r hr, hdone], fr₃, rd₃', wr₃', ivK₃⟩
  · exact .inr ⟨by rw [hz₃, decide_eq_false hdone]; rfl, base₃, ready₃, saved₃, data₃, left₃, by omega_using [hj, hdone], buf₃,
      data₃', fr₃, rd₃', wr₃', ivK₃⟩

/-- The data loop. -/
theorem fbLoop_wp (cs : BlockSpec c) (mo : FbMode) {ivR : Reg} (hivR : ivR ∉ modeRegs c) {s₀ : State} {m₀ : Mem}
    {B D : Addr} {n : Nat} {k : cs.Key} {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw))
    (hsc : KeepsReg ivR c.crypt) {s : State} (hi : FInv cs mo ivR s₀ m₀ B D n k iv 0 s) :
    WP isa (.loop (c.fbBlock mo) (.nonzero .x c.leftReg)) s (FDone cs mo ivR s₀ m₀ B D n k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ FInv cs mo ivR s₀ m₀ B D n k iv j s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (fbBlock_wp cs mo hivR hiv hp hsc hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - (j + 1), by have := d.lt; have := hj.lt; omega_arith, j + 1, rfl, d⟩

end VG.Proof.Modes.AArch64
