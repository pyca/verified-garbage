module

public import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
public import VerifiedGarbage.Impl.Modes.X86_64.FbFinal
public import VerifiedGarbage.Proof.Modes.X86_64.FbFinalTail
public import VerifiedGarbage.Proof.Modes.FbFinal
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit

/-!
# OFB and CFB of a message's last piece on x86-64, for any core: the loop

`fbSeg_wp`: one segment of `fbFinal`'s loop enciphers its input block `Iⱼ`
in the buffer (`BlockSpec.crypt_wp`), giving `Oⱼ`; if a whole block of the
`len` bytes is left, it makes the block `fbOut` and the buffer `Iⱼ₊₁`
(`fbIn`), as `fb`'s (`fbBlock_wp`); if `r < L` bytes are left, it XORs the
first `r` bytes of `Oⱼ` into them (`xorLoop_wp`), which are then those of
`fbOut j`, and leaves `Oⱼ` in the buffer. Blocks are `L = 8 bw` bytes.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Modes (FbMode)
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- What the loop works on: the scratch buffer at `B`, the `len` bytes at
`D`. -/
structure FPre (c : Core) (s₀ : State) (B D : Addr) (len : Nat) : Prop where
  scr : ScrIn s₀ B c.ctrSlots
  dat : (⟨D, len⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, len⟩ ⟨B, 8 * c.ctrSlots⟩
  fitD : D.toNat + len ≤ 2 ^ 64
  small : len < 2 ^ 64
  stk : StkOk c s₀

/-- The loop, before segment `j`; `m₀` is the memory on entry, `iv` the IV. -/
structure FInvF (cs : BlockSpec c) (mo : FbMode) (s₀ : State) (m₀ : Mem) (B D : Addr) (len : Nat) (k : cs.Key)
    (iv : List Byte) (j : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  ready : cs.Ready s B k
  saved : ∀ i < 7, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * j)
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * j)
  lt : 8 * c.bw * j < len
  buf : ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (fbIn mo (8 * c.bw) (cs.cipher k) m₀ D iv j).getD u 0
  data : ∀ i < len, s.mem (D + BitVec.ofNat 64 i) =
    if i < 8 * c.bw * j then (fbOut mo (8 * c.bw) (cs.cipher k) m₀ D iv (i / (8 * c.bw))).getD (i % (8 * c.bw)) 0
    else m₀ (D + BitVec.ofNat 64 i)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, len⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : s.xmm Core.ivX = s₀.xmm Core.ivX

/-- The loop, done. -/
structure FDoneF (cs : BlockSpec c) (mo : FbMode) (s₀ : State) (m₀ : Mem) (B D : Addr) (len : Nat) (k : cs.Key)
    (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 7, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  buf : ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (fbNextF mo (8 * c.bw) (cs.cipher k) m₀ D iv len).getD u 0
  data : ∀ i < len, s.mem (D + BitVec.ofNat 64 i) =
    (fbOut mo (8 * c.bw) (cs.cipher k) m₀ D iv (i / (8 * c.bw))).getD (i % (8 * c.bw)) 0
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, len⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : s.xmm Core.ivX = s₀.xmm Core.ivX

/-- A region at an offset of `p` that does not wrap around. -/
theorem fit_off (p : Addr) {d n : Nat} (h : p.toNat + d + n ≤ 2 ^ 64) (hn : 0 < n) :
    (p + BitVec.ofNat 64 d).toNat + n ≤ 2 ^ 64 := by
  have hp := p.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem xorByte_scal (Rd Rl : Reg) : (xorByte Rd Rl).all scalarI = true := rfl

/-- The partial segment's code is scalar. -/
theorem fbTail_scal (c : Core) :
    scalCode (.seq (.block c.fbTailStart) (.loop (.block (xorByte c.dataReg c.leftReg)) .ne)) = true := rfl

theorem fbSeg_wp (cs : BlockSpec c) (mo : FbMode) {s₀ : State} {m₀ : Mem} {B D : Addr} {len : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : FPre c s₀ B D len) (hsc : KeepsIv c.crypt)
    (hz : (s₀.xmm Core.ivX).extractLsb' 64 64 = 0) {j : Nat} {s : State}
    (hi : FInvF cs mo s₀ m₀ B D len k iv j s) :
    WP isa (c.fbSeg mo) s fun s' => (s'.zf = some true ∧ FDoneF cs mo s₀ m₀ B D len k iv s') ∨
      (s'.zf = some false ∧ FInvF cs mo s₀ m₀ B D len k iv (j + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hj := hi.lt
  have hL0 : 0 < 8 * c.bw := by omega_arith
  have hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hj1 : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, -, dc, -, d10, dsb, dsp, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, -, lc, -, l10, lsb, lsp, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  have hlen64 : len ≤ 2 ^ 64 := by omega_arith
  have hsmall := hp.small
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 (8 * c.bw * j)
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have hwS : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, len⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subT : Region.Sub ⟨T, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  have subTbuf : Region.Sub ⟨T, 8 * c.bw⟩ (blkRegion c B) := Region.sub_prefix hLG
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    Region.sub_prefix (by simp only [Core.ctrSlots]; omega_arith)
  have dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.ctrSlots⟩ → Region.Disjoint ⟨D, len⟩ r :=
    fun h => hp.sep.sub_right h
  have hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  have inT : ∀ w < c.bw, InRegions s.wr (T + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by simp only [Core.ctrSlots]; omega_arith) (by omega_arith)⟩
  -- Enciphered.
  unfold Core.fbSeg
  refine WP.seq (WP.mono (WP.keepIv hsc (by rw [hi.xmm]; exact hz) (cs.crypt_wp hi.base ⟨hwS, hfit⟩ hi.ready))
    fun s₂ ⟨⟨base₂, rsp₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩, x₂⟩ => ?_)
  rw [hi.rsp] at f₂
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
  have D₂ : ∀ i < len, s₂.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hi' =>
    f₂.bytes (R := ⟨D, len⟩) (hp.stk.coreFrame_disj (dDS subCore) ⟨_, hp.dat, fun _ h => h⟩) hlen64 hi'
  have mA : ∀ u, 8 * c.bw * j + u < len → s.mem (A + BitVec.ofNat 64 u) = m₀ (A + BitVec.ofNat 64 u) := fun u hu => by
    rw [addr_add, hi.data _ hu, ite_eq_right (by omega_arith)]
  have D₂' : ∀ u, 8 * c.bw * j + u < len → s₂.mem (A + BitVec.ofNat 64 u) = s.mem (A + BitVec.ofNat 64 u) :=
    fun u hu => by rw [addr_add]; exact D₂ _ hu
  -- Whether a whole block is left.
  have hleft : s₂.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * j) := by rw [lr₂, hi.leftR]
  obtain ⟨s₃, e₃, cf₃, g₃, m₃, rd₃, wr₃⟩ := cmpImm_ok s₂ c.leftReg (BitVec.ofNat 32 (8 * c.bw)) (K := 8 * c.bw) hleft
    (by omega_arith) (by rw [signExtend_small (by omega_arith)]; simp only [BitVec.toNat_ofNat]; omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have x₃ : s₃.xmm Core.ivX = s₀.xmm Core.ivX := by rw [runBlock_vec rfl e₃, x₂, hi.xmm]
  have sy₃ : s₃.syms = s₂.syms := runBlock_syms e₃
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hi.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hi.wr]
  have data₃ : s₃.gpr c.dataReg = A := by rw [g₃, dr₂, hi.dataR]
  have base₃ : s₃.gpr sb = B := by rw [g₃, base₂]
  -- The slots: none of the core's, nor in the data or the buffer's first block.
  have slotOut : ∀ i < 7, ∀ {R : Region}, (Region.Sub R ⟨D, len⟩ ∨ R = ⟨T, 8 * c.bw⟩ ∨
      R = coreRegion c B) → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi7 R hR => by
    rcases hR with h | rfl | rfl
    · exact ((dDS (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
        simp only [Core.ctrSlots]; omega_arith))).sub_left h).symm
    · exact VG.Offset.disjoint B (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)
  have saved₂ : ∀ i < 7, s₂.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64 :=
    fun i hi7 => by
      rw [← hi.saved i hi7]
      exact f₂.readW (Region.contains_self _ _) (hp.stk.coreFrame_disj (slotOut i hi7 (.inr (.inr rfl)))
        ⟨_, hp.scr.wr, VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
          simp only [Core.ctrSlots]; omega_arith)⟩) (by decide)
  have fr₂ : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, len⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s₂.mem :=
    hi.frame.trans (f₂.sub (coreFrame_sub ⟨_, List.mem_cons_self, subCore⟩))
  refine WP.ite (decide (len - 8 * c.bw * j < 8 * c.bw)) (by simp [X86_64.eval, cf₃]) (fun hb => ?_) (fun hb => ?_)
  · -- A partial segment: `r` bytes.
    have hb' : len - 8 * c.bw * j < 8 * c.bw := by simpa using hb
    let r := len - 8 * c.bw * j
    have hr0 : 0 < r := by omega_arith
    have hdiv : len / (8 * c.bw) = j := by
      rw [show len = 8 * c.bw * j + r by omega_arith]; exact idx_div hb'
    have hmod : len % (8 * c.bw) = r := by
      rw [show len = 8 * c.bw * j + r by omega_arith]; exact idx_mod hb'
    obtain ⟨s₄a, e₄a, a₄a, o₄a, m₄a, rd₄a, wr₄a⟩ := movR_ok s₃ .rax sb
    obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₄a .rax (BitVec.ofNat 32 (8 * c.buf))
    have run₄ : runBlock isa c.fbTailStart s₃ = some s₄ := by
      rw [Core.fbTailStart, show ([.mov .rax (.reg sb), .alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf)))] :
        List Instr) = [movR .rax sb] ++ [.alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf)))] from rfl,
        runBlock_app, e₄a, Option.bind_some, e₄]
    have rax₄ : s₄.gpr .rax = T := by rw [a₄, a₄a, base₃, signExtend_small (by omega_arith)]
    have g₄ : ∀ x, x ≠ .rax → s₄.gpr x = s₃.gpr x := fun x h => by rw [o₄ x h, o₄a x h]
    have mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₄a, m₃]
    have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₄a, rd₃']
    have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₄a, wr₃']
    have subTr : Region.Sub ⟨T, r⟩ ⟨T, 8 * c.bw⟩ := Region.sub_prefix (by omega_arith)
    have subAr : Region.Sub ⟨A, r⟩ ⟨D, len⟩ := VG.Offset.sub_base D (by omega_arith)
    have hxp : XPre s₄ T A r c.dataReg c.leftReg :=
      { pos := hr0
        small := by omega_arith
        fitK := fit_off B (by simp only [Core.ctrSlots] at hfit; omega_arith) hr0
        fitR := fit_off D (by omega_arith) hr0
        disj := ((dDS subT).sub_left subAr).sub_right subTr |>.symm
        rdK := fun q hq => by
          rw [rd₄', wr₄']
          exact inRd ⟨_, hp.scr.wr, by
            rw [addr_add]; exact VG.Offset.contains_base B (by simp only [Core.ctrSlots]; omega_arith) (by omega_arith)⟩
        wrR := fun q hq => by
          rw [wr₄']
          exact ⟨_, hp.dat, by rw [addr_add]; exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)⟩
        dl := hdl
        dRax := ⟨da, la⟩
        dR10 := ⟨d10, l10⟩
        dRcx := ⟨dc, lc⟩ }
    have hx0 : XInv s₄ T A r c.dataReg c.leftReg 0 s₄ :=
      { rax := by rw [rax₄]; simp
        dat := by rw [g₄ _ da, data₃]; simp
        left := by rw [g₄ _ la, g₃, hleft, Nat.sub_zero]
        lt := hr0
        data := fun q hq => by rw [ite_eq_right (Nat.not_lt_zero _)]
        frame := Frame.refl _ _
        rd := rfl
        wr := rfl
        gpr := fun _ _ _ _ _ _ => rfl }
    refine WP.mono (WP.vecKeep (fbTail_scal c) (WP.seq (WP.of_runBlock ⟨s₄, run₄, xorLoop_wp hxp hx0⟩)))
      fun s₅ ⟨d₅, x₅, _⟩ => .inl ⟨d₅.zf, ?_⟩
    have f₅ : Frame [⟨A, r⟩] s₂.mem s₅.mem := by rw [← mem₄]; exact d₅.frame
    have g₅ : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rcx → x ≠ c.dataReg → x ≠ c.leftReg → s₅.gpr x = s₂.gpr x :=
      fun x h1 h2 h3 h4 h5 => by rw [d₅.gpr x h1 h2 h3 h4 h5, g₄ x h1, g₃]
    have kT : ∀ u < 8 * c.bw, s₅.mem (T + BitVec.ofNat 64 u) = s₂.mem (T + BitVec.ofNat 64 u) := fun u hu =>
      f₅.bytes (R := ⟨T, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact ((dDS subT).sub_left subAr).symm) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
    refine ⟨by rw [g₅ _ (by decide) (by decide) (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂],
      by rw [g₅ _ (by decide) (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp), rsp₂, hi.rsp],
      fun i hi7 => ?_, fun u hu => ?_, fun i hi' => ?_, ?_, by rw [d₅.rd, rd₄'], by rw [d₅.wr, wr₄'],
      by rw [x₅]; exact x₃⟩
    · rw [← saved₂ i hi7]
      exact f₅.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact slotOut i hi7 (.inl subAr)) (by decide)
    · rw [kT u hu, E₂ u hu, fbNextF, ite_eq_right (by rw [hmod]; omega_arith), hdiv]
    · by_cases hlt : i < 8 * c.bw * j
      · have out : ∀ R ∈ [(⟨A, r⟩ : Region)], ¬ R.Contains (D + BitVec.ofNat 64 i) 1 := fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR
          exact not_contains_off D (.inl hlt) (by omega_arith) hr0 (by omega_arith)
        rw [f₅ _ out, D₂ i hi', hi.data i hi', ite_eq_left hlt]
      · obtain ⟨q, rfl⟩ : ∃ q, i = 8 * c.bw * j + q := ⟨i - 8 * c.bw * j, by omega_arith⟩
        have hq : q < r := by omega_arith
        have e := d₅.data q hq
        rw [mem₄] at e
        rw [← addr_add, e, idx_div (by omega_arith), idx_mod (by omega_arith), D₂' q (by omega_arith),
          mA q (by omega_arith), fbOut_getD mo (cs.cipher_len k) m₀ D iv j (by omega_arith), E₂ q (by omega_arith),
          addr_add]
    · exact fr₂.trans (f₅.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subAr⟩)
  · -- A whole block.
    have hb' : 8 * c.bw ≤ len - 8 * c.bw * j := by simpa using hb
    have hjl : 8 * c.bw * j + 8 * c.bw ≤ len := by omega_arith
    have hjl' : 8 * (c.bw * j) + 8 * c.bw ≤ len := by rw [← Nat.mul_assoc]; exact hjl
    have subA : Region.Sub ⟨A, 8 * c.bw⟩ ⟨D, len⟩ := VG.Offset.sub_base D hjl
    have dAT : Region.Disjoint ⟨A, 8 * c.bw⟩ ⟨T, 8 * c.bw⟩ := (dDS subT).sub_left subA
    have inA : ∀ w < c.bw, InRegions s.wr (A + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
      ⟨_, hwD, by rw [addr_add, hw]; exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)⟩
    refine WP.block_append (WP.mono_syms (WP.vecKeep (fbOp_scal c mo) (fbOp_wp mo data₃ (by rw [base₃]) da
      (fun w hw' => by rw [wr₃, wr₂]; exact inA w hw') (fun w hw' => by rw [wr₃, wr₂]; exact inT w hw') dAT
      (by omega_arith))) fun s₃a ⟨⟨g₃a, rd₃a, wr₃a, mA₃, mT₃, f₃a⟩, x₃a, _⟩ sy₃a => ?_)
    obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b⟩ := addImm_ok s₃a c.dataReg (BitVec.ofNat 32 (8 * c.bw))
    obtain ⟨s₄, e₄, l₄, z₄, o₄, m₄, rd₄, wr₄⟩ := subImm_ok s₃b c.leftReg (BitVec.ofNat 32 (8 * c.bw))
    refine WP.of_runBlock ⟨s₄, by
      rw [Core.fbNextBytes, show ([.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw))),
        .alu .sub c.leftReg (.imm (BitVec.ofNat 32 (8 * c.bw)))] : List Instr) =
        [.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw)))] ++
          [.alu .sub c.leftReg (.imm (BitVec.ofNat 32 (8 * c.bw)))] from rfl,
        runBlock_app, e₃b, Option.bind_some, e₄], ?_⟩
    have keep₄ : ∀ x, x ≠ .rax → x ≠ c.dataReg → x ≠ c.leftReg → s₄.gpr x = s₂.gpr x := fun x h1 h2 h3 => by
      rw [o₄ x h3, o₃b x h2, g₃a x h1, g₃]
    have left₃ : s₃b.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * j) := by
      rw [o₃b _ (Ne.symm hdl), g₃a _ la, g₃, hleft]
    have hsx : (BitVec.ofNat 32 (8 * c.bw)).signExtend 64 = BitVec.ofNat 64 (8 * c.bw) := signExtend_small (by omega_arith)
    have left₄ : s₄.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * (j + 1)) := by
      rw [l₄, left₃, hsx, VG.Offset.ofNat_sub_ofNat hb', hj1, Nat.sub_sub]
    have hz₄ : s₄.zf = some (decide (8 * c.bw * (j + 1) = len)) := by
      rw [z₄, left₃, hsx, VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
      simp only [Option.some.injEq, decide_eq_decide]; omega_arith
    have hAL : A + BitVec.ofNat 64 (8 * c.bw) = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by rw [addr_add, hj1]
    have data₄ : s₄.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by
      rw [o₄ _ hdl, a₃b, g₃a _ da, data₃, hsx, hAL]
    have mem₄ : s₄.mem = s₃a.mem := by rw [m₄, m₃b]
    have xmm₄ : s₄.xmm Core.ivX = s₀.xmm Core.ivX := by
      rw [runBlock_vec rfl e₄, runBlock_vec rfl e₃b, x₃a, x₃]
    have base₄ : s₄.gpr sb = B := by rw [keep₄ _ (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂]
    have rsp₄ : s₄.gpr .rsp = s₀.gpr .rsp := by
      rw [keep₄ _ (by decide) (Ne.symm dsp) (Ne.symm lsp), rsp₂, hi.rsp]
    have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃b, rd₃a, rd₃']
    have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃b, wr₃a, wr₃']
    have f₃ : Frame [⟨A, 8 * c.bw⟩, ⟨T, 8 * c.bw⟩] s₂.mem s₄.mem := by rw [mem₄, ← m₃]; exact f₃a
    have saved₄ : ∀ i < 7, s₄.mem.readW (wordAddr B (c.slots + i)) 64 =
        s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi7 => by
      rw [← saved₂ i hi7]
      exact f₃.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact slotOut i hi7 (.inl subA)
        · exact slotOut i hi7 (.inr (.inl rfl))) (by decide)
    have fr₄ : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, len⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s₄.mem :=
      fr₂.trans (f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subA⟩
        · exact ⟨_, List.mem_cons_self, subT⟩)
    have ready₄ : cs.Ready s₄ B k := cs.ready_frame ready₂ f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ((dDS subCore).sub_left subA).symm
      · exact .inr subTbuf)
      ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, by rw [wr₂]; exact hwD, subA⟩
        · exact ⟨_, by rw [wr₂]; exact hwS, subT⟩,
        by rw [rd₄, rd₃b, rd₃a, rd₃], by rw [wr₄, wr₃b, wr₃a, wr₃],
        by rw [runBlock_syms e₄, runBlock_syms e₃b, sy₃a, sy₃]⟩
      fun r hr => by
      obtain ⟨h1, -, -, -, -, h6, h7⟩ := of_not_modeRegs hr; exact keep₄ r h1 h6 h7
    have buf₄ : ∀ u < 8 * c.bw, s₄.mem (T + BitVec.ofNat 64 u) =
        (fbIn mo (8 * c.bw) ciph m₀ D iv (j + 1)).getD u 0 := fun u hu => by
      rw [mem₄, mT₃ u hu, m₃, E₂ u hu, D₂' u (by omega_arith), mA u (by omega_arith),
        fbIn_succ_getD mo (cs.cipher_len k) m₀ D iv j hu, addr_add]
    have data₄' : ∀ i < len, s₄.mem (D + BitVec.ofNat 64 i) =
        if i < 8 * c.bw * (j + 1) then (fbOut mo (8 * c.bw) ciph m₀ D iv (i / (8 * c.bw))).getD (i % (8 * c.bw)) 0
        else m₀ (D + BitVec.ofNat 64 i) := fun i hi' => by
      by_cases hin : 8 * c.bw * j ≤ i ∧ i < 8 * c.bw * (j + 1)
      · obtain ⟨q, rfl⟩ : ∃ q, i = 8 * c.bw * j + q := ⟨i - 8 * c.bw * j, by omega_arith⟩
        have hq : q < 8 * c.bw := by omega_arith
        rw [ite_eq_left hin.2, idx_div hq, idx_mod hq, fbOut_getD mo (cs.cipher_len k) m₀ D iv j hq, mem₄, ← addr_add,
          mA₃ q hq, m₃, E₂ q hq, D₂' q (by omega_arith), mA q (by omega_arith)]
      · have out : ∀ R ∈ [(⟨A, 8 * c.bw⟩ : Region), ⟨T, 8 * c.bw⟩],
            ¬ R.Contains (D + BitVec.ofNat 64 i) 1 := fun R hR => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
          rcases hR with rfl | rfl
          · exact not_contains_off D (by omega_arith) (by omega_arith) hL0 (by omega_arith)
          · exact fun hc => dDS subT _ (VG.Offset.contains_base D (by omega_arith) (by omega_arith)) hc
        rw [mem₄, f₃a _ out, m₃, D₂ i hi', hi.data i hi']
        by_cases h3 : i < 8 * c.bw * j
        · rw [ite_eq_left h3, ite_eq_left (by omega_arith)]
        · rw [ite_eq_right h3, ite_eq_right (by omega_arith)]
    by_cases hdone : 8 * c.bw * (j + 1) = len
    · refine .inl ⟨by rw [hz₄, decide_eq_true hdone], base₄, rsp₄, saved₄, fun u hu => ?_,
        fun i hi' => by rw [data₄' i hi', ite_eq_left (by omega_arith)], fr₄, rd₄', wr₄', xmm₄⟩
      have hmod : len % (8 * c.bw) = 0 := by rw [← hdone]; exact Nat.mul_mod_right _ _
      have hdiv : len / (8 * c.bw) = j + 1 := by rw [← hdone]; exact Nat.mul_div_cancel_left _ hL0
      rw [buf₄ u hu, fbNextF, ite_eq_left hmod, hdiv]
    · exact .inr ⟨by rw [hz₄, decide_eq_false hdone], base₄, rsp₄, ready₄, saved₄, data₄, left₄, by omega_arith,
        buf₄, data₄', fr₄, rd₄', wr₄', xmm₄⟩

/-- The loop. -/
theorem fbFinalLoop_wp (cs : BlockSpec c) (mo : FbMode) {s₀ : State} {m₀ : Mem} {B D : Addr} {len : Nat}
    {k : cs.Key} {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : FPre c s₀ B D len) (hsc : KeepsIv c.crypt)
    (hz : (s₀.xmm Core.ivX).extractLsb' 64 64 = 0) {s : State} (hi : FInvF cs mo s₀ m₀ B D len k iv 0 s) :
    WP isa (.loop (c.fbSeg mo) .ne) s (FDoneF cs mo s₀ m₀ B D len k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = len - 8 * c.bw * j ∧ FInvF cs mo s₀ m₀ B D len k iv j s)
    (fun m s hs => ?_) len s ⟨0, by simp, hi⟩
  obtain ⟨j, rfl, hj⟩ := hs
  have hbw0 := cs.layout.bw_pos
  refine WP.mono (fbSeg_wp cs mo hiv hp hsc hz hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], len - 8 * c.bw * (j + 1), by
      have := d.lt; have := hj.lt; rw [Nat.mul_succ]; omega, j + 1, rfl, d⟩

end VG.Proof.Modes.X86_64
