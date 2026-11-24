module

public import VerifiedGarbage.Proof.Aes.X86.Sse.Blocks
public import VerifiedGarbage.Proof.Aes.X86.Sse.Loops
public import VerifiedGarbage.Proof.Aes.X86.Sse.Rounds
public import VerifiedGarbage.Proof.Aes.X86.Ctr32
public import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.Exec
meta import VerifiedGarbage.Impl.Aes.X86.Sse
meta import VerifiedGarbage.Proof.Aes.X86.Ctr32CT
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-!
# AES counter mode, in SSE2 registers, on x86 (32-bit)

A pass of `vg_aes_ctr32_to` writes the next eight counter blocks to the
slots (`ctrBlocks_ok`), encrypts them (`encrypt8_ok`) and XORs as many of
them as there are blocks left into the data (`xorOut_ok`). `DataInv` says
which bytes of the destination are done.
-/

@[expose] public section

namespace VG.Proof.Aes.X86.Sse

open VG VG.X86 VG.Impl.Aes.X86.Sse VG.Proof.Aes
open VG.Impl.Aes.X86 (sb at_ argOp movI addI subI addR subR dbl movR)
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_addm wp_add wp_sub wp_subi wp_ldm wp_stm wp_cmpi wp_test
  wp_bswap toNat_ofNat_lt ofNat_pred ofNat_beq_zero)

/-! ## The counter block, as the scratch buffer has it -/

/-- The words of the counter block in the scratch buffer at `B`, and the counter. -/
abbrev cw (m : Mem) (B : BitVec 32) (v : Nat) : BitVec 32 := m.readW (addr B (cwOff v)) 32
abbrev cnum (m : Mem) (B : BitVec 32) : BitVec 32 := m.readW (addr B cNum) 32

/-! ## The counter blocks of a pass -/

section
variable {is : List Instr} {s : State} {P : State → Prop}

theorem wp_shq {op : XShiftOp} {d n : Nat}
    (k : ∀ s', XUpd s s' (X d) (op.eval (s.xmm (X d)) (BitVec.ofNat 8 n)) → WP isa (.block is) s' P) :
    WP isa (.block (shq op d n :: is)) s P :=
  Wp.cons rfl (k _ (XUpd.setXmm _ _ _))

theorem wp_movd {d : XReg} {r : Reg} (k : ∀ s', XUpd s s' d ((0 : BitVec 96) ++ s.gpr r) → WP isa (.block is) s' P) :
    WP isa (.block (.xop (.movd d r) :: is)) s P :=
  Wp.cons rfl (k _ (XUpd.setXmm _ _ _))

theorem wp_por {d r : XReg} (k : ∀ s', XUpd s s' d (s.xmm d ||| s.xmm r) → WP isa (.block is) s' P) :
    WP isa (.block (.xop (.bin .por d r) :: is)) s P :=
  Wp.cons rfl (k _ (XUpd.setXmm _ _ _))

/-- `wp_mov`, and the SSE registers are kept. -/
theorem wp_mov' {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → s'.xmm = s.xmm → WP isa (.block is) s' P) :
    WP isa (.block (movR d r :: is)) s P :=
  Wp.cons rfl (k _ (Upd.setReg _ _ _) rfl)

theorem wp_addi' {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.xmm = s.xmm → WP isa (.block is) s' P) :
    WP isa (.block (addI d v :: is)) s P :=
  Wp.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_bswap' {d : Reg} (k : ∀ s', Upd s s' d (bswap (s.gpr d)) → s'.xmm = s.xmm → WP isa (.block is) s' P) :
    WP isa (.block (.bswap d :: is)) s P :=
  Wp.cons rfl (k _ (Upd.setReg _ _ _) rfl)

theorem wp_ldm' {d b : Reg} {A : BitVec 32} {o : Nat} (hb : s.gpr b = A) (hin : InRegions (s.rd ++ s.wr) (addr A o) 4)
    (k : ∀ s', Upd s s' d (s.mem.readW (addr A o) 32) → s'.xmm = s.xmm → WP isa (.block is) s' P) :
    WP isa (.block (.mov d (.mem ⟨b, o⟩) :: is)) s P :=
  Wp.cons (s' := s.setReg d (s.mem.readW (addr A o) 32)) (by simp [reduceExec, Wp.readSrc_mem hb hin])
    (k _ (Upd.setReg _ _ _) rfl)

theorem wp_stx' {d : XReg} {b : Reg} {A : BitVec 32} {o : Nat} (hb : s.gpr b = A) (hin : InRegions s.wr (addr A o) 16)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr A o) (s.xmm d)) → s'.xmm = s.xmm → WP isa (.block is) s' P) :
    WP isa (.block (.movdquStore ⟨b, o⟩ d :: is)) s P := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW (addr A o) (s.xmm d) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl)
  simp only [reduceExec, State.store128, ea_mk, hb, hin, ite_true]

end

/-- The bytes of a counter block: twelve of the words' and the counter's. -/
def ctrByte (m : Mem) (B : BitVec 32) (i : Nat) : Byte :=
  if i % 16 < 12 then m (addr B 288 + BitVec.ofNat 64 (i % 16))
  else (bswap (cnum m B + BitVec.ofNat 32 (i / 16))).extractLsb' (8 * (i % 16 - 12)) 8

theorem low12 (L : BitVec 128) (x : BitVec 32) {i : Nat} (hi : i < 16) :
    (XBinOp.eval .por (XShiftOp.eval .pslldq ((0 : BitVec 96) ++ x) (BitVec.ofNat 8 12))
      (XShiftOp.eval .psrldq (XShiftOp.eval .pslldq L (BitVec.ofNat 8 4)) (BitVec.ofNat 8 4))).extractLsb' (8 * i) 8 =
      if i < 12 then L.extractLsb' (8 * i) 8 else x.extractLsb' (8 * (i - 12)) 8 := by
  show ((((0 : BitVec 96) ++ x) <<< 96) ||| ((L <<< 32) >>> 32)).extractLsb' (8 * i) 8 = _
  refine byte_ext fun j hj => ?_
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  by_cases h : i < 12
  · rw [ite_eq_left h, BitVec.getLsbD_extractLsb']
    simp [hj, show 8 * i + j < 96 by omega_using [h, hj], show 32 + (8 * i + j) < 128 by omega_using [h, hj]]
  · rw [ite_eq_right h, BitVec.getLsbD_extractLsb']
    simp [hj, show ¬ 8 * i + j < 96 by omega_using [h], show ¬ 32 + (8 * i + j) < 128 by omega_using [h],
      show 8 * i + j < 128 by omega_using [hi, hj],
      show 8 * i + j - 96 = 8 * (i - 12) + j by omega_using [h], show 8 * (i - 12) + j < 32 by omega_using [hi, hj]]

/-- With `j` of the counter blocks written. -/
structure WInv (s₀ : State) (B : BitVec 32) (j : Nat) (s : State) : Prop where
  x1 : s.xmm .xmm1 = XShiftOp.eval .psrldq (XShiftOp.eval .pslldq (s₀.mem.readW (addr B 288) 128) (BitVec.ofNat 8 4))
    (BitVec.ofNat 8 4)
  esi : s.gpr .esi = cnum s₀.mem B
  other : ∀ r, r ≠ .eax → r ≠ .esi → s.gpr r = s₀.gpr r
  mem : s.mem = patch s₀.mem (B.setWidth 64) (16 * j) (ctrByte s₀.mem B)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ctrBlock_ok {s₀ : State} {B : BitVec 32} (hb : s₀.gpr .edi = B) (hfit : B.toNat + 2048 ≤ 2 ^ 32)
    (hw : reg32 B 2048 ∈ s₀.wr) {j : Nat} (hj : j < 8) {s : State} (hi : WInv s₀ B j s) {rest : List Instr}
    {P : State → Prop} (h : ∀ s', WInv s₀ B (j + 1) s' → WP isa (.block rest) s' P) :
    WP isa (.block (ctrBlock j ++ rest)) s P := by
  refine wp_mov' fun s₁ u₁ x₁ => wp_addi' fun s₂ u₂ x₂ => wp_bswap' fun s₃ u₃ x₃ => wp_movd fun s₄ u₄ => wp_shq fun s₅ u₅ =>
    wp_por fun s₆ u₆ => ?_
  have g : ∀ r, r ≠ .eax → s₆.gpr r = s.gpr r := fun r hr => by
    rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.other r hr, u₂.other r hr, u₁.other r hr]
  have hmem : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hwr : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hrd : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hedi : s₆.gpr .edi = B := by rw [g _ (by decide), hi.other _ (by decide) (by decide), hb]
  refine wp_stx' (A := B) (o := 16 * j) hedi (by rw [hwr, hi.wr]; exact in_reg hw hfit (by omega_using [hj]) (by decide))
    fun s₇ u₇ x₇ => ?_
  refine h s₇ ⟨?_, ?_, fun r h1 h2 => by rw [u₇.gpr, g r h1, hi.other r h1 h2], ?_, by rw [u₇.rd, hrd, hi.rd],
    by rw [u₇.wr, hwr, hi.wr]⟩
  · rw [x₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), x₃, x₂, x₁, hi.x1]
  · rw [u₇.gpr, g _ (by decide), hi.esi]
  · have hx : s₆.xmm .xmm0 = XBinOp.eval .por
        (XShiftOp.eval .pslldq ((0 : BitVec 96) ++ bswap (cnum s₀.mem B + BitVec.ofNat 32 j)) (BitVec.ofNat 8 12))
        (XShiftOp.eval .psrldq (XShiftOp.eval .pslldq (s₀.mem.readW (addr B 288) 128) (BitVec.ofNat 8 4))
          (BitVec.ofNat 8 4)) := by
      have e0 : s₅.xmm .xmm0 = XShiftOp.eval .pslldq
          ((0 : BitVec 96) ++ bswap (cnum s₀.mem B + BitVec.ofNat 32 j)) (BitVec.ofNat 8 12) := by
        rw [show s₅.xmm .xmm0 = _ from u₅.xmm, show s₄.xmm (X 0) = _ from u₄.xmm, u₃.gpr, u₂.gpr, u₁.gpr, hi.esi]
      have e1 : s₅.xmm .xmm1 = s.xmm .xmm1 := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), x₃, x₂, x₁]
      rw [show s₆.xmm .xmm0 = s₅.xmm .xmm0 ||| s₅.xmm .xmm1 from u₆.xmm, e0, e1, hi.x1]; rfl
    rw [u₇.mem, hmem, hi.mem, show s₆.xmm (X 0) = _ from hx, addr_eq (by omega_using [hfit, hj])]
    refine patch_write (by omega_using [hj]) fun i hi16 => ?_
    rw [low12 _ _ hi16, ctrByte, show (16 * j + i) % 16 = i by omega_using [hi16],
      show (16 * j + i) / 16 = j by omega_using [hi16], byte_of_readW _ _ hi16]

theorem ctrBlocks_run {s₀ : State} {B : BitVec 32} (hb : s₀.gpr .edi = B) (hfit : B.toNat + 2048 ≤ 2 ^ 32)
    (hw : reg32 B 2048 ∈ s₀.wr) {rest : List Instr} {P : State → Prop}
    (h : ∀ s', WInv s₀ B 8 s' → WP isa (.block rest) s' P) :
    ∀ r j, j + r = 8 → ∀ s, WInv s₀ B j s → WP isa (.block ((List.range' j r).flatMap ctrBlock ++ rest)) s P := by
  intro r
  induction r with
  | zero => intro j hj s hi; subst hj; exact h s hi
  | succ r ih =>
    intro j hj s hi
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    exact ctrBlock_ok hb hfit hw (by omega_using [hj]) hi fun s' hi' => ih (j + 1) (by omega_using [hj]) s' hi'

/-- The counter blocks `c … c + 7`, and the next counter. -/
theorem ctrBlocks_ok {s₀ : State} {B : BitVec 32} (hb : s₀.gpr .edi = B) (hfit : B.toNat + 2048 ≤ 2 ^ 32)
    (hw : reg32 B 2048 ∈ s₀.wr) {P : State → Prop}
    (h : ∀ s', (∀ i < 128, s'.mem (B.setWidth 64 + BitVec.ofNat 64 i) = ctrByte s₀.mem B i) →
      cnum s'.mem B = cnum s₀.mem B + 8 → Frame [⟨B.setWidth 64, 128⟩, ⟨addr B cNum, 4⟩] s₀.mem s'.mem →
      (∀ r, r ≠ .eax → r ≠ .esi → s'.gpr r = s₀.gpr r) → s'.rd = s₀.rd → s'.wr = s₀.wr → P s') :
    WP isa (.block ctrBlocks) s₀ P := by
  have hrd : ∀ o n, 0 < n → o + n ≤ 2048 → InRegions (s₀.rd ++ s₀.wr) (addr B o) n := fun o n h0 ho =>
    ⟨_, List.mem_append_right _ hw, reg_contains hfit ho h0⟩
  rw [show ctrBlocks = ldm 1 .edi 288 :: shq .pslldq 1 4 :: shq .psrldq 1 4 :: Instr.mov .esi (.mem (at_ .edi cNum)) ::
    ((List.range' 0 8).flatMap ctrBlock ++ [addI .esi 8, .store (at_ .edi cNum) .esi]) from rfl]
  refine wp_ldx hb (hrd 288 16 (by decide) (by decide)) fun s₁ u₁ => wp_shq fun s₂ u₂ => wp_shq fun s₃ u₃ =>
    wp_ldm' (A := B) (o := cNum) (by rw [u₃.gpr, u₂.gpr, u₁.gpr, hb])
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hrd _ 4 (by decide) (by decide)) fun s₄ u₄ x₄ => ?_
  have hi : WInv s₀ B 0 s₄ :=
    ⟨by rw [x₄, show s₃.xmm .xmm1 = _ from u₃.xmm, show s₂.xmm (X 1) = _ from u₂.xmm, show s₁.xmm (X 1) = _ from u₁.xmm],
      by rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem], fun r _ h2 => by rw [u₄.other r h2, u₃.gpr, u₂.gpr, u₁.gpr],
      by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, Nat.mul_zero, patch_zero], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  refine ctrBlocks_run hb hfit hw (fun s₅ h₅ => ?_) 8 0 rfl s₄ hi
  refine wp_addi fun s₆ u₆ => wp_stm (B := B) (o := cNum)
    (by rw [u₆.other _ (by decide), h₅.other _ (by decide) (by decide), hb])
    (by rw [u₆.wr, h₅.wr]; exact in_reg hw hfit (by decide) (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have hm : s₇.mem = (patch s₀.mem (B.setWidth 64) 128 (ctrByte s₀.mem B)).writeW (addr B cNum) (cnum s₀.mem B + 8) := by
    rw [u₇.mem, u₆.gpr, u₆.mem, h₅.mem, h₅.esi]
  refine h s₇ (fun i hi => ?_) (by rw [hm]; exact Mem.readW_writeW_self32 _ _ _) ?_ (fun r h1 h2 => ?_)
    (by rw [u₇.rd, u₆.rd, h₅.rd]) (by rw [u₇.wr, u₆.wr, h₅.wr])
  · rw [hm]
    refine ((Frame.refl [⟨addr B cNum, 4⟩] _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _) _
      fun r hr hc => ?_).trans (patch_at hi (by decide))
    simp only [List.mem_singleton] at hr; subst hr
    rw [← addr_eq (by omega_using [hfit, hi])] at hc
    exact part_disj hfit (a := i) (n := 1) (by omega_using [hi]) (by decide) (.inl (by simp only [cNum]; omega_using [hi]))
      _ (Region.contains_self _ _) hc
  · rw [hm]
    exact ((patch_frame _ _ _ _).mono (by simp)).writeW (by simp) _ (Region.contains_self _ _)
  · rw [u₇.gpr, u₆.other r h2, h₅.other r h1 h2]

/-- The counter blocks, as states. -/
theorem ctrByte_state {m : Mem} {B : BitVec 32} {icb : Spec.Gcm.Block} {k : Nat}
    (hw : ∀ i < 12, m (addr B 288 + BitVec.ofNat 64 i) = (Spec.Gcm.toBytes icb).getD i 0)
    (hc : cnum m B = icb.extractLsb' 0 32 + BitVec.ofNat 32 k) {i : Nat} :
    ctrByte m B i = (ctrState icb (k + i / 16)).getD (i % 16) 0 := by
  have hi := Nat.mod_lt i (show 16 > 0 by decide)
  simp only [ctrState, getD_eq _ hi, Vector.getElem_ofFn]
  rw [ctrBlock_byte _ _ hi, ctrByte]
  by_cases h : i % 16 < 12
  · rw [ite_eq_left h, ite_eq_left h, hw _ h]
  · rw [ite_eq_right h, ite_eq_right h, hc, BitVec.add_assoc, ← BitVec.ofNat_add]
    refine byte_ext fun j hj => ?_
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, Bool.true_and,
      bswap_bit _ (by omega_using [hi]) hj]
    congr 1; omega_using [h, hi]

/-! ## The data -/

/-- The data after `d` bytes: the keystream `ks` XORed into the first `d` of
the `16 n` bytes at `S`, written to `D` (the same bytes in place), the other
bytes at `D` as they were, and the bytes at `S` not yet read as they were. -/
def DataInv (m₀ m : Mem) (S D : Addr) (n d : Nat) (ks : Nat → Byte) : Prop :=
  (∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < d then m₀ (S + BitVec.ofNat 64 i) ^^^ ks i else m₀ (D + BitVec.ofNat 64 i)) ∧
  ∀ i < 16 * n, d ≤ i → m (S + BitVec.ofNat 64 i) = m₀ (S + BitVec.ofNat 64 i)

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat = if j ≤ i then i - j else 2 ^ 64 + i - j := by
  split <;> bv_omega

/-- `c` more bytes. -/
theorem dataInv_patch {m₀ m : Mem} {S D : Addr} {n d c : Nat} {ks v : Nat → Byte} (hn : 16 * n < 2 ^ 64)
    (hd : d + c ≤ 16 * n) (hsd : SrcDst S D n) (h : DataInv m₀ m S D n d ks)
    (hv : ∀ i < c, v i = m (S + BitVec.ofNat 64 (d + i)) ^^^ ks (d + i)) :
    DataInv m₀ (patch m (D + BitVec.ofNat 64 d) c v) S D n (d + c) ks := by
  refine ⟨fun i hi => ?_, fun i hi hdi => ?_⟩
  · rw [patch, off_toNat D (by omega_using [hi, hn]) (by omega_using [hd, hn])]
    by_cases h1 : d ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - d < c
      · rw [ite_eq_left h2, hv _ h2, show d + (i - d) = i by omega_using [h1], h.2 i hi h1,
          ite_eq_left (show i < d + c by omega_using [h2, h1])]
      · rw [ite_eq_right h2, h.1 i hi, ite_eq_right (show ¬ i < d by omega_using [h1]),
          ite_eq_right (show ¬ i < d + c by omega_using [h2, h1])]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - d < c by omega_using [hd, hn]), h.1 i hi,
        ite_eq_left (show i < d by omega_using [h1]), ite_eq_left (show i < d + c by omega_using [h1])]
  · rw [← h.2 i hi (by omega_using [hdi])]
    refine patch_frame m _ c v _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains] at hc
    rcases hsd with rfl | hdis
    · rw [off_toNat S (by omega_using [hi, hn]) (by omega_using [hd, hn]), ite_eq_left (by omega_using [hdi])] at hc
      omega_using [hc, hdi]
    · refine hdis (S + BitVec.ofNat 64 i) ?_ ?_
      · simp only [Region.Contains]
        rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hn])]
        omega_using [hi]
      · simp only [Region.Contains]
        have : (BitVec.ofNat 64 d).toNat = d := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hd, hn])]
        bv_omega

/-- `DataInv` after a write apart from the source and the destination. -/
theorem dataInv_frame {m₀ m m' : Mem} {S D : Addr} {n d : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r)
    (hs : ∀ r ∈ rs, Region.Disjoint ⟨S, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : DataInv m₀ m S D n d ks) : DataInv m₀ m' S D n d ks :=
  ⟨fun i hi => by
    rw [← h.1 i hi]
    exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega_arith) hi,
   fun i hi hdi => by
    rw [← h.2 i hi hdi]
    exact hf.bytes (R := ⟨S, 16 * n⟩) hs (by simp only; omega_arith) hi⟩

/-- The keystream, byte by byte: byte `i` is byte `i mod 16` of the
encrypted counter block `i / 16`. -/
def keyStream (R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) (i : Nat) : Byte :=
  (Spec.Aes.cipher R w (ctrState icb (i / 16))).getD (i % 16) 0

theorem ctr32_of_dataInv {m₀ m : Mem} {S D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (h : DataInv m₀ m S D n (16 * n) (keyStream R w icb)) :
    Spec.Gcm.blocksAt m D n =
      Spec.Gcm.ctr32 (Spec.Gcm.aesWith R w) icb (Spec.Gcm.blocksAt m₀ S n) := by
  unfold Spec.Gcm.ctr32 Spec.Gcm.keystream Spec.Gcm.blocksAt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.length_map,
    List.length_range]
  simp only [List.length_map, List.length_range] at h1
  refine block_ext fun k hk => ?_
  rw [toBytes_xor _ _ hk, toBytes_blockAt _ _ hk, toBytes_blockAt _ _ hk, BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, h.1 _ (by omega_arith), ite_eq_left (by omega_arith)]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [toBytes_ofBytes (by simp) hk, keyStream, show (16 * i + k) / 16 = i by omega_arith,
    show (16 * i + k) % 16 = k by omega_arith, getD_eq _ hk, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]
  rfl

/-! ## A pass -/

/-- Where the source is, with the destination at `D`. -/
structure Src (rd wr : List Region) (B Sp D : BitVec 32) (n : Nat) : Prop where
  src : reg32 Sp (16 * n) ∈ rd ++ wr
  fit : Sp.toNat + 16 * n ≤ 2 ^ 32
  sep : (reg32 Sp (16 * n)).Disjoint (reg32 B 2048)
  sd : SrcDst (Sp.setWidth 64) (D.setWidth 64) n

section
variable {rd wr : List Region} {B S E Sp D : BitVec 32} {R n : Nat} {w : List Byte} {m₀ : Mem} {g : Reg → BitVec 32}
  {icb : Spec.Gcm.Block}

/-- The counter block's words, and the counter, before block `k`. -/
structure CtrAt (m : Mem) (B : BitVec 32) (icb : Spec.Gcm.Block) (k : Nat) : Prop where
  words : ∀ i < 12, m (addr B 288 + BitVec.ofNat 64 i) = (Spec.Gcm.toBytes icb).getD i 0
  num : cnum m B = icb.extractLsb' 0 32 + BitVec.ofNat 32 k

/-- Before a pass, `k` blocks done. -/
structure CInv (rd wr : List Region) (B S E Sp D : BitVec 32) (R n : Nat) (w : List Byte) (icb : Spec.Gcm.Block)
    (m₀ : Mem) (g : Reg → BitVec 32) (k : Nat) (s : State) : Prop where
  hk : k ≤ n
  good : Good rd wr B S E R w s
  keys : KeysAt s.mem B w (R - 1)
  kept : Kept B D n m₀ g s.mem
  edx : s.gpr .edx = Sp + BitVec.ofNat 32 (16 * k)
  ebx : s.gpr .ebx = D + BitVec.ofNat 32 (16 * k)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (n - k)
  ctr : k < n → CtrAt s.mem B icb k
  data : DataInv m₀ s.mem (Sp.setWidth 64) (D.setWidth 64) n (16 * k) (keyStream R w icb)

/-- The counter's words are in `[288, 304)`. -/
theorem CtrAt.frame (hfit : B.toNat + 2048 ≤ 2 ^ 32) {m m' : Mem} {k : Nat} (h : CtrAt m B icb k) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨addr B 288, 16⟩ r) : CtrAt m' B icb k where
  words := fun i hi => by
    rw [← h.words i hi]
    exact hf.bytes (R := ⟨addr B 288, 16⟩) hd (by show 16 ≤ 2 ^ 64; decide) (by show i < 16; omega_using [hi])
  num := by
    rw [← h.num]
    exact hf.readW (part_contains hfit (by decide) (by decide) (by decide) (by decide)) hd (by decide)

theorem xorOut_ok (he : Env rd wr B S E R) (hd : Data wr B S E D n) (hs : Src rd wr B Sp D n) {k : Nat} {s : State}
    (hg : Good rd wr B S E R w s) (hkeys : KeysAt s.mem B w (R - 1)) (hkept : Kept B D n m₀ g s.mem)
    (hdx : s.gpr .edx = Sp + BitVec.ofNat 32 (16 * k)) (hbx : s.gpr .ebx = D + BitVec.ofNat 32 (16 * k))
    (hbp : s.gpr .ebp = BitVec.ofNat 32 (n - k)) (hctr : CtrAt s.mem B icb (k + 8))
    (hdata : DataInv m₀ s.mem (Sp.setWidth 64) (D.setWidth 64) n (16 * k) (keyStream R w icb)) (hk : k < n)
    (hv : ∀ i < 128, s.mem (B.setWidth 64 + BitVec.ofNat 64 i) = keyStream R w icb (16 * k + i)) :
    WP isa xorOut s fun s' => CInv rd wr B S E Sp D R n w icb m₀ g (k + min 8 (n - k)) s' ∧
      s'.zf = some (decide (k + min 8 (n - k) = n)) := by
  have fD := hd.fit
  have fS := hs.fit
  have fB := he.fitB
  have hR := he.hR
  obtain ⟨m, hm⟩ : ∃ m, m = min 8 (n - k) := ⟨_, rfl⟩
  rw [← hm]
  have hm0 : 0 < m := by omega_using [hm, hk]
  have hm8 : m ≤ 8 := by omega_using [hm]
  have hkm : k + m ≤ n := by omega_using [hm, hk]
  obtain ⟨pfit, paddr, psub⟩ := part_blocks fD hkm hm0
  obtain ⟨sfit, saddr, ssub⟩ := part_blocks fS hkm hm0
  refine WP.seq (wp_mov fun s₁ u₁ => WP.block_nil ?_)
  have hbp₁ : s₁.gpr .ebp = BitVec.ofNat 32 (n - k) := by rw [u₁.other _ (by decide), hbp]
  refine WP.seq (takeCount_ok (by omega_using [fD]) hbp₁ fun s₂ u₂ => ?_)
  rw [← hm] at u₂
  refine WP.seq (wp_sub fun s₃ u₃ _ => WP.block_nil ?_)
  have hcx : s₃.gpr .ecx = BitVec.ofNat 32 m := by rw [u₃.other _ (by decide), u₂.gpr]
  have hbp₃ : s₃.gpr .ebp = BitVec.ofNat 32 (n - (k + m)) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), hbp₁, Wp.sub_ofNat (by omega_using [hkm]),
      show n - k - m = n - (k + m) by omega_using []]
  have g₃ : ∀ r, r ≠ .ecx → r ≠ .esi → r ≠ .ebp → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h1, u₁.other r h2]
  have hsi : s₃.gpr .esi = B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hg.edi]
  have hdx₃ := (g₃ .edx (by decide) (by decide) (by decide)).trans hdx
  have hbx₃ := (g₃ .ebx (by decide) (by decide) (by decide)).trans hbx
  have hmem₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = rd := by rw [u₃.rd, u₂.rd, u₁.rd, hg.rd]
  have wr₃ : s₃.wr = wr := by rw [u₃.wr, u₂.wr, u₁.wr, hg.wr]
  have bsub : Region.Sub ⟨B.setWidth 64, 16 * m⟩ (reg32 B 2048) := Region.sub_prefix (by omega_using [hm8])
  refine WP.seq (WP.mono (xor_loop (by omega_using [hm8]) hm0 hcx (by rw [hsi]; omega_using [fB, hm8])
    (by rw [hdx₃]; exact sfit) (by rw [hbx₃]; exact pfit)
    (by rw [hsi, rd₃, wr₃]; have := blocksIn_of (a := 0) (m := m) (List.mem_append_right rd he.scr) fB (by omega_using [hm8])
        simpa using this)
    (by rw [hdx₃, rd₃, wr₃]; exact blocksIn_of hs.src fS (by omega_using [hkm]))
    (by rw [hbx₃, wr₃]; exact blocksIn_of hd.dat fD (by omega_using [hkm]))
    (by rw [hsi, hbx₃]; exact ((hd.sep.sub_left psub).sub_right bsub).symm)
    (by rw [hdx₃, hbx₃]
        rcases hs.sd with e | e
        · exact .inl (by rw [show Sp = D from BitVec.eq_of_toNat_eq (by
            have := congrArg BitVec.toNat e; rwa [toNat_setWidth32, toNat_setWidth32] at this)])
        · exact .inr ((e.sub_left ssub).sub_right psub))) fun s₄ h₄ => ?_)
  refine wp_test fun s₅ u₅ hz => WP.block_nil ?_
  have hmem₅ : s₅.mem = patch s.mem (D.setWidth 64 + BitVec.ofNat 64 (16 * k)) (16 * m)
      (fun i => s.mem (B.setWidth 64 + BitVec.ofNat 64 i) ^^^
        s.mem (Sp.setWidth 64 + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 i)) := by
    rw [u₅.mem, h₄.mem, hbx₃, hdx₃, hsi, paddr, saddr, hmem₃]
  have hf : Frame [⟨(D + BitVec.ofNat 32 (16 * k)).setWidth 64, 16 * m⟩] s.mem s₅.mem := by
    rw [hmem₅, paddr]; exact patch_frame _ _ _ _
  have hsub : ∀ r ∈ [(⟨(D + BitVec.ofNat 32 (16 * k)).setWidth 64, 16 * m⟩ : Region)],
      Region.Sub r (reg32 D (16 * n)) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact psub
  have g₅ : ∀ r, r ≠ .ecx → r ≠ .esi → r ≠ .ebp → r ≠ .edx → r ≠ .ebx → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [u₅.gpr, h₄.other r h1 (by simp [h2, h4, h5]), g₃ r h1 h2 h3]
  have hbp₅ : s₅.gpr .ebp = BitVec.ofNat 32 (n - (k + m)) := by
    rw [u₅.gpr, h₄.other _ (by decide) (by decide), hbp₃]
  refine ⟨⟨hkm, hg.data hd he (by rw [u₅.rd, h₄.rd, rd₃, hg.rd]) (by rw [u₅.wr, h₄.wr, wr₃, hg.wr])
    (g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)) hf hsub,
    KeysAt.data hd fB (by omega_using [hR]) hkeys hf hsub, hkept.data fB hd.sep hf hsub, ?_, ?_, hbp₅, fun hlt => ?_, ?_⟩, ?_⟩
  · rw [u₅.gpr, h₄.ptr _ (by simp), hdx₃, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]
  · rw [u₅.gpr, h₄.ptr _ (by simp), hbx₃, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]
  · rw [show m = 8 by omega_using [hm, hlt]]
    exact hctr.frame fB hf fun r hr => ((hd.sep.sub_right (part_sub_reg fB (by decide))).symm).sub_right (hsub r hr)
  · rw [hmem₅, Nat.mul_add]
    refine dataInv_patch (by omega_using [fD]) (by omega_using [hkm]) hs.sd hdata fun i hi => ?_
    rw [hv i (by omega_using [hi, hm8]), BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.xor_comm]
  · rw [hz, h₄.other _ (by decide) (by decide), hbp₃, BitVec.and_self, ofNat_beq_zero (by omega_using [fD])]
    exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_using [h, hkm], fun h => by omega_using [h]⟩)

/-- The regions `ctrBlocks` writes. -/
theorem ctrRegs_sub (hfit : B.toNat + 2048 ≤ 2 ^ 32) :
    ∀ r ∈ [(⟨B.setWidth 64, 128⟩ : Region), ⟨addr B cNum, 4⟩], Region.Sub r (reg32 B 2048) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Region.sub_prefix (by decide)
  · exact part_sub_reg hfit (by decide)

/-- The regions `ctrBlocks` writes are apart from what is at `[o, o + l)`. -/
theorem ctrRegs_disj (hfit : B.toNat + 2048 ≤ 2 ^ 32) {o l : Nat} (ho : 128 ≤ o) (hol : o + l ≤ 2048)
    (hc : o + l ≤ 300 ∨ 304 ≤ o) :
    ∀ r ∈ [(⟨B.setWidth 64, 128⟩ : Region), ⟨addr B cNum, 4⟩], Region.Disjoint ⟨addr B o, l⟩ r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [← addr_zero]; exact part_disj hfit hol (by decide) (.inr (by omega_using [ho]))
  · exact part_disj hfit hol (by decide) (by simp only [cNum]; omega_using [hc])

theorem group_ok (he : Env rd wr B S E R) (hd : Data wr B S E D n) (hs : Src rd wr B Sp D n) {k : Nat} {s : State}
    (hi : CInv rd wr B S E Sp D R n w icb m₀ g k s) (hk : k < n) :
    WP isa group s fun s' => CInv rd wr B S E Sp D R n w icb m₀ g (k + min 8 (n - k)) s' ∧
      s'.zf = some (decide (k + min 8 (n - k) = n)) := by
  have fD := hd.fit
  have fB := he.fitB
  have hR := he.hR
  have hc := hi.ctr hk
  refine WP.seq (ctrBlocks_ok hi.good.edi fB (by rw [hi.good.wr]; exact he.scr) fun s₁ hb hn hf hg hrd hwr => ?_)
  have hsub := ctrRegs_sub fB
  have good₁ := hi.good.step he hrd hwr (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide)) hf hsub
  have keys₁ := hi.keys.frame (by omega_using [hR]) fB hf
    (ctrRegs_disj fB (by decide) (by decide) (.inr (by decide)))
  have kept₁ := hi.kept.scratch fB hf hsub (ctrRegs_disj fB (by decide) (by decide) (.inl (by decide)))
  have data₁ := dataInv_frame hf (fun r hr => hd.sep.sub_right (hsub r hr)) (fun r hr => hs.sep.sub_right (hsub r hr))
    (by omega_using [fD]) hi.data
  have ctr₁ : CtrAt s₁.mem B icb (k + 8) :=
    ⟨fun i hi12 => by
      rw [← hc.words i hi12]
      exact hf.bytes (R := ⟨addr B 288, 12⟩) (ctrRegs_disj fB (by decide) (by decide) (.inl (by decide)))
        (by show 12 ≤ 2 ^ 64; decide) hi12,
     by rw [hn, hc.num, BitVec.add_assoc, BitVec.ofNat_add]; rfl⟩
  have hrel : InRel (Q s₁) (fun b => ctrState icb (k + b)) := inRel_of_bytes good₁.edi fB fun i hi128 => by
    rw [hb i hi128, ctrByte_state hc.words hc.num]
  refine WP.seq (WP.mono (encrypt8_ok he good₁ keys₁ hrel) fun s₂ ⟨r₂, hout⟩ => ?_)
  have keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → s₂.gpr r = s.gpr r := fun r h1 h2 h3 =>
    (r₂.keep r h1 h2 h3).trans (hg r h1 h3)
  refine xorOut_ok he hd hs r₂.good r₂.keys (kept₁.slots fB r₂.frame)
    ((keep _ (by decide) (by decide) (by decide)).trans hi.edx) ((keep _ (by decide) (by decide) (by decide)).trans hi.ebx)
    ((keep _ (by decide) (by decide) (by decide)).trans hi.ebp)
    (ctr₁.frame fB r₂.frame fun r hr => ?_)
    (dataInv_frame r₂.frame (fun r hr => hd.sep.sub_right (slots_sub r hr)) (fun r hr => hs.sep.sub_right (slots_sub r hr))
      (by omega_using [fD]) data₁) hk fun i hi128 => ?_
  · simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint _ ⟨B.setWidth 64, 272⟩
    rw [← addr_zero]
    exact part_disj fB (by decide) (by decide) (.inr (by decide))
  · rw [bytes_of_inRel r₂.good.edi fB hout i hi128, keyStream, show (16 * k + i) / 16 = k + i / 16 by omega_using [],
      show (16 * k + i) % 16 = i % 16 by omega_using []]

theorem groups_ok (he : Env rd wr B S E R) (hd : Data wr B S E D n) (hs : Src rd wr B Sp D n) {s : State}
    (hi : CInv rd wr B S E Sp D R n w icb m₀ g 0 s) (hn : 0 < n) :
    WP isa (.loop group .ne) s (CInv rd wr B S E Sp D R n w icb m₀ g n) := by
  refine WP.loop (M := isa) (fun j s => ∃ k, j = n - k ∧ k < n ∧ CInv rd wr B S E Sp D R n w icb m₀ g k s)
    (fun j s ⟨k, hj, hk, hi⟩ => WP.mono (group_ok he hd hs hi hk) fun s' ⟨h, hz⟩ => ?_) n s ⟨0, rfl, hn, hi⟩
  by_cases hlast : k + min 8 (n - k) = n
  · rw [hlast] at h
    exact .inl ⟨by simp [X86.eval, hz, hlast], h⟩
  · exact .inr ⟨by simp [X86.eval, hz, hlast], n - (k + min 8 (n - k)), by omega_using [hj, hk], _, rfl,
      by omega_using [hlast, hk], h⟩

end

/-! ## The prologue -/

/-- After `ctrSetup`. -/
structure SetUp (B C N : BitVec 32) (s s' : State) : Prop where
  other : ∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨addr B 288, 16⟩, ⟨addr C 12, 4⟩] s.mem s'.mem
  words : ∀ i < 12, s'.mem (addr B 288 + BitVec.ofNat 64 i) = s.mem (addr C i)
  num : cnum s'.mem B = bswap (s.mem.readW (addr C 12) 32)
  ctr : s'.mem.readW (addr C 12) 32 = bswap (bswap (s.mem.readW (addr C 12) 32) + N)

theorem ctrSetup_ok {s : State} {B C E N : BitVec 32} (hb : s.gpr .edi = B) (he : s.gpr .esp = E)
    (hfit : B.toNat + 2048 ≤ 2 ^ 32) (hw : reg32 B 2048 ∈ s.wr) (hC : C.toNat + 16 ≤ 2 ^ 32) (hwC : reg32 C 16 ∈ s.wr)
    (hsep : (reg32 C 16).Disjoint (reg32 B 2048)) (in2 : InRegions (s.rd ++ s.wr) (addr E 12) 4)
    (in4 : InRegions (s.rd ++ s.wr) (addr E 20) 4) (h2 : s.mem.readW (addr E 12) 32 = C)
    (h4 : s.mem.readW (addr E 20) 32 = N) (hsep4 : Region.Disjoint ⟨addr E 20, 4⟩ (reg32 B 2048)) :
    WP isa (.block ctrSetup) s (SetUp B C N s) := by
  have inB : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 := fun t ht o ho => by
    rw [ht]; exact in_reg hw hfit ho (by decide)
  have inC : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → ∀ o, o + 4 ≤ 16 → InRegions (t.rd ++ t.wr) (addr C o) 4 :=
    fun t h1 h2 o ho => by rw [h1, h2]; exact in_rd (in_reg hwC hC ho (by decide))
  -- What is written of the scratch buffer, and what is read of the counter block meanwhile.
  have cB : ∀ o, 288 ≤ o → o + 4 ≤ 304 → (⟨addr B 288, 16⟩ : Region).Contains (addr B o) (32 / 8) := fun o h1 h2 =>
    part_contains hfit (by decide) h1 h2 (by decide)
  have bsub : ∀ r ∈ [(⟨addr B 288, 16⟩ : Region)], Region.Sub r (reg32 B 2048) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg hfit (by decide)
  have rdC : ∀ {m : Mem}, Frame [⟨addr B 288, 16⟩] s.mem m → ∀ o, o + 4 ≤ 16 →
      m.readW (addr C o) 32 = s.mem.readW (addr C o) 32 := fun hf o ho =>
    hf.readW (reg_contains hC ho (by decide)) (fun r hr => hsep.sub_right (bsub r hr)) (by decide)
  refine wp_ldm (B := E) (o := 12) he in2 fun s₁ u₁ => ?_
  have c₁ : s₁.gpr .ecx = C := u₁.gpr.trans h2
  refine wp_ldm (B := C) (o := 0) c₁ (inC _ u₁.rd u₁.wr 0 (by decide)) fun s₂ u₂ => ?_
  refine wp_stm (B := B) (o := 288) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb])
    (inB _ (by rw [u₂.wr, u₁.wr]) _ (by decide)) fun s₃ u₃ => ?_
  have f₃ : Frame [⟨addr B 288, 16⟩] s.mem s₃.mem := by
    rw [u₃.mem, u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cB _ (by decide) (by decide))
  have g₃ : ∀ r, r ≠ .eax → r ≠ .ecx → s₃.gpr r = s.gpr r := fun r h1 h2 => by rw [u₃.gpr, u₂.other r h1, u₁.other r h2]
  have c₃ : s₃.gpr .ecx = C := by rw [u₃.gpr, u₂.other _ (by decide), c₁]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  refine wp_ldm (B := C) (o := 4) c₃ (inC _ rd₃ wr₃ 4 (by decide)) fun s₄ u₄ => ?_
  refine wp_stm (B := B) (o := 292) (by rw [u₄.other _ (by decide), g₃ _ (by decide) (by decide), hb])
    (inB _ (by rw [u₄.wr, wr₃]) _ (by decide)) fun s₅ u₅ => ?_
  have f₅ : Frame [⟨addr B 288, 16⟩] s.mem s₅.mem := by
    rw [u₅.mem, u₄.mem]; exact f₃.writeW (List.mem_singleton_self _) _ (cB _ (by decide) (by decide))
  have g₅ : ∀ r, r ≠ .eax → r ≠ .ecx → s₅.gpr r = s.gpr r := fun r h1 h2 => by rw [u₅.gpr, u₄.other r h1, g₃ r h1 h2]
  have c₅ : s₅.gpr .ecx = C := by rw [u₅.gpr, u₄.other _ (by decide), c₃]
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, rd₃]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, wr₃]
  refine wp_ldm (B := C) (o := 8) c₅ (inC _ rd₅ wr₅ 8 (by decide)) fun s₆ u₆ => ?_
  refine wp_stm (B := B) (o := 296) (by rw [u₆.other _ (by decide), g₅ _ (by decide) (by decide), hb])
    (inB _ (by rw [u₆.wr, wr₅]) _ (by decide)) fun s₇ u₇ => ?_
  have f₇ : Frame [⟨addr B 288, 16⟩] s.mem s₇.mem := by
    rw [u₇.mem, u₆.mem]; exact f₅.writeW (List.mem_singleton_self _) _ (cB _ (by decide) (by decide))
  have g₇ : ∀ r, r ≠ .eax → r ≠ .ecx → s₇.gpr r = s.gpr r := fun r h1 h2 => by rw [u₇.gpr, u₆.other r h1, g₅ r h1 h2]
  have c₇ : s₇.gpr .ecx = C := by rw [u₇.gpr, u₆.other _ (by decide), c₅]
  have rd₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, rd₅]
  have wr₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, wr₅]
  refine wp_ldm (B := C) (o := 12) c₇ (inC _ rd₇ wr₇ 12 (by decide)) fun s₈ u₈ => wp_bswap fun s₉ u₉ => ?_
  refine wp_stm (B := B) (o := 300)
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), g₇ _ (by decide) (by decide), hb])
    (inB _ (by rw [u₉.wr, u₈.wr, wr₇]) _ (by decide)) fun s₁₀ u₁₀ => ?_
  have v₉ : s₉.gpr .eax = bswap (s.mem.readW (addr C 12) 32) := by rw [u₉.gpr, u₈.gpr, rdC f₇ 12 (by decide)]
  have m₁₀ : s₁₀.mem = (((s.mem.writeW (addr B 288) (s.mem.readW (addr C 0) 32)).writeW (addr B 292)
      (s.mem.readW (addr C 4) 32)).writeW (addr B 296) (s.mem.readW (addr C 8) 32)).writeW (addr B 300)
      (bswap (s.mem.readW (addr C 12) 32)) := by
    rw [u₁₀.mem, v₉, u₉.mem, u₈.mem, u₇.mem, u₆.gpr, rdC f₅ 8 (by decide), u₆.mem, u₅.mem, u₄.gpr, rdC f₃ 4 (by decide),
      u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem]
  have f₁₀ : Frame [⟨addr B 288, 16⟩] s.mem s₁₀.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem]; exact f₇.writeW (List.mem_singleton_self _) _ (cB _ (by decide) (by decide))
  have g₁₀ : ∀ r, r ≠ .eax → r ≠ .ecx → s₁₀.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₁₀.gpr, u₉.other r h1, u₈.other r h1, g₇ r h1 h2]
  have c₁₀ : s₁₀.gpr .ecx = C := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), c₇]
  have rd₁₀ : s₁₀.rd = s.rd := by rw [u₁₀.rd, u₉.rd, u₈.rd, rd₇]
  have wr₁₀ : s₁₀.wr = s.wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, wr₇]
  refine wp_addm (B := E) (o := 20) (by rw [g₁₀ _ (by decide) (by decide), he]) (by rw [rd₁₀, wr₁₀]; exact in4)
    fun s₁₁ u₁₁ => wp_bswap fun s₁₂ u₁₂ => ?_
  refine wp_stm (B := C) (o := 12) (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), c₁₀])
    (by rw [u₁₂.wr, u₁₁.wr, wr₁₀]; exact in_reg hwC hC (by decide) (by decide)) fun s₁₃ u₁₃ => WP.block_nil ?_
  have v₁₂ : s₁₂.gpr .eax = bswap (bswap (s.mem.readW (addr C 12) 32) + N) := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, v₉,
      f₁₀.readW (Region.contains_self _ _) (fun r hr => hsep4.sub_right (bsub r hr)) (by decide), h4]
  have m₁₃ : s₁₃.mem = s₁₀.mem.writeW (addr C 12) (bswap (bswap (s.mem.readW (addr C 12) 32) + N)) := by
    rw [u₁₃.mem, v₁₂, u₁₂.mem, u₁₁.mem]
  -- The write of the counter block is apart from the scratch buffer.
  have fC : Frame [reg32 C 16] s₁₀.mem s₁₃.mem := by
    rw [m₁₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (reg_contains hC (by decide) (by decide))
  have rdB : ∀ o, o + 4 ≤ 2048 → s₁₃.mem.readW (addr B o) 32 = s₁₀.mem.readW (addr B o) 32 := fun o ho =>
    fC.readW (reg_contains hfit ho (by decide)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hsep.symm) (by decide)
  have hcw : ∀ v < 3, s₁₃.mem.readW (addr B (288 + 4 * v)) 32 = s.mem.readW (addr C (4 * v)) 32 := fun v hv => by
    rw [rdB _ (by omega_using [hv]), m₁₀]
    rcases (by omega_using [hv] : v = 0 ∨ v = 1 ∨ v = 2) with rfl | rfl | rfl <;>
      simp (disch := decide) only [rd_wr_ne hfit, Nat.reduceMul, Nat.reduceAdd, Mem.readW_writeW_self32]
  refine ⟨fun r h1 h2 => by rw [u₁₃.gpr, u₁₂.other r h1, u₁₁.other r h1, g₁₀ r h1 h2],
    by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀], by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀], ?_, fun i hi => ?_, ?_, ?_⟩
  · rw [m₁₃]
    exact (f₁₀.mono (by simp)).writeW (by simp) _ (Region.contains_self _ _)
  · have h := hcw (i / 4) (by omega_using [hi])
    have e1 := Mem.extractLsb'_read s₁₃.mem (addr B (288 + 4 * (i / 4))) (n := 4) (Nat.mod_lt i (by decide))
    have e2 := Mem.extractLsb'_read s.mem (addr C (4 * (i / 4))) (n := 4) (Nat.mod_lt i (by decide))
    rw [addr_add64 (by omega_using [hfit, hi])] at e1
    rw [addr_add64 (by omega_using [hC, hi]), Nat.div_add_mod] at e2
    rw [addr_add64 (by omega_using [hfit, hi]), ← e2, show 288 + i = 288 + 4 * (i / 4) + i % 4 by omega_using [], ← e1]
    exact congrArg (BitVec.extractLsb' (8 * (i % 4)) 8) h
  · rw [cnum, rdB _ (by decide), m₁₀]; exact Mem.readW_writeW_self32 _ _ _
  · rw [m₁₃]; exact Mem.readW_writeW_self32 _ _ _

/-! ## The whole function -/

theorem blocksAt_frame {rs : List Region} {m m' : Mem} {A : Addr} {n : Nat} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨A, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64) :
    Spec.Gcm.blocksAt m' A n = Spec.Gcm.blocksAt m A n := by
  unfold Spec.Gcm.blocksAt
  refine List.map_congr_left fun j hj => Proof.Gcm.blockAt_congr fun k hk => ?_
  have hj := List.mem_range.mp hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hf.bytes (R := ⟨A, 16 * n⟩) hd (by show 16 * n ≤ 2 ^ 64; omega_using [hn]) (by show _ < 16 * n; omega_using [hj, hk])

/-- The precondition, with the arguments by name. -/
structure CtrEnv (s₀ : State) (B C S Sp D E : BitVec 32) (R n : Nat) (w : List Byte) : Prop where
  env : Env s₀.rd s₀.wr B S E R
  data : Data s₀.wr B S E D n
  src : Src s₀.rd s₀.wr B Sp D n
  fC : C.toNat + 16 ≤ 2 ^ 32
  wC : reg32 C 16 ∈ s₀.wr
  argC : ∀ i < 7, (argRg true s₀).Contains (addr E (4 + 4 * i)) 4
  argSub : ∀ i < 7, Region.Sub ⟨addr E (4 + 4 * i), 4⟩ (argRg true s₀)
  argIn : ∀ i < 7, InRegions (s₀.rd ++ s₀.wr) (addr E (4 + 4 * i)) 4
  aB : (argRg true s₀).Disjoint (reg32 B 2048)
  aC : (argRg true s₀).Disjoint (reg32 C 16)
  dCB : (reg32 C 16).Disjoint (reg32 B 2048)
  dCD : (reg32 C 16).Disjoint (reg32 D (16 * n))
  dCS : (reg32 C 16).Disjoint (reg32 Sp (16 * n))
  dSC : (reg32 S 240).Disjoint (reg32 C 16)
  rB : (retR s₀).Disjoint (reg32 B 2048)
  rC : (retR s₀).Disjoint (reg32 C 16)
  rD : (retR s₀).Disjoint (reg32 D (16 * n))
  esp : s₀.gpr .esp = E
  arg : ∀ i < 7, s₀.mem.readW (addr E (4 + 4 * i)) 32 = X86.arg s₀ i
  a0 : X86.arg s₀ 0 = S
  a1 : X86.arg s₀ 1 = BitVec.ofNat 32 R
  a2 : X86.arg s₀ 2 = C
  a3 : X86.arg s₀ 3 = Sp
  a4 : X86.arg s₀ 4 = BitVec.ofNat 32 n
  a5 : X86.arg s₀ 5 = B
  a6 : X86.arg s₀ 6 = D
  w : ∀ i < 16 * (R + 1), s₀.mem (addr S i) = w.getD i 0

theorem CtrEnv.of {s₀ : State} (hp : GPre true s₀) :
    CtrEnv s₀ (scrP s₀) (ctrP s₀) (schP s₀) (datP s₀) (X86.arg s₀ 6) (s₀.gpr .esp) (nRounds s₀) (nBlk s₀)
      (Spec.Aes.bytesAt s₀.mem ((schP s₀).setWidth 64) (16 * (nRounds s₀ + 1))) := by
  have lt6 : ∀ i < 7, i < 6 ∨ (true = true ∧ i = 6) := fun i hi => by
    rcases Nat.lt_or_ge i 6 with h | h
    · exact .inl h
    · exact .inr ⟨rfl, by omega_using [hi, h]⟩
  have argSub : ∀ i < 7, Region.Sub ⟨addr (s₀.gpr .esp) (4 + 4 * i), 4⟩ (argRg true s₀) := fun i hi =>
    hp.argSub (lt6 i hi)
  have argIn : ∀ i < 7, InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 := fun i hi => by
    obtain ⟨r, hr, hc⟩ := hp.rA i (lt6 i hi)
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  have hd := hp.wD; have hfd := hp.fD; have hdB := hp.dDB; have hdS := hp.dSD; have haD := hp.aD; have hsd := hp.sd
  have hdC := hp.dCD; have hrD := hp.rD
  simp only [dstR, dstP, ↓reduceIte] at hd hfd hdB hdS haD hsd hdC hrD
  exact
  { env :=
    { scr := hp.wB
      fitB := hp.fB
      sch := List.mem_append_left _ hp.rS
      fitS := hp.fS
      sepS := hp.dSB
      rounds := hp.rounds
      argIn := fun i hi => argIn i (by omega_using [hi])
      argSep := fun i hi => hp.aB.sub_left (argSub i (by omega_using [hi])) }
    data := ⟨hd, hfd, hdB, hdS, fun i hi => haD.sub_left (argSub i (by omega_using [hi]))⟩
    src := ⟨hp.rSrc, hp.fSrc, hp.dSrcB, hsd⟩
    fC := hp.fC
    wC := hp.wC
    argC := fun i hi => hp.argC (lt6 i hi)
    argSub := argSub
    argIn := argIn
    aB := hp.aB, aC := hp.aC, dCB := hp.dCB, dCD := hdC, dCS := hp.dCS, dSC := hp.dSC, rB := hp.rB, rC := hp.rC, rD := hrD,
    esp := rfl, arg := fun _ _ => rfl, a0 := rfl,
    a1 := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    a2 := rfl, a3 := rfl
    a4 := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    a5 := rfl, a6 := rfl
    w := fun i hi => by
      have hR := hp.rounds
      have hS := hp.fS
      rw [addr_eq (by omega_using [hS, hi, hR])]
      simp only [Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hi, Option.map_some, Option.getD_some] }

/-- After the prologue. -/
structure CtrStart (s₀ : State) (B C S E : BitVec 32) (R n : Nat) (w : List Byte) (s : State) : Prop where
  good : Good s₀.rd s₀.wr B S E R w s
  frame : Frame [⟨addr B 272, 32⟩, reg32 C 16] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr B) s₀.gpr savedRegs
  ctr : CtrAt s.mem B (Spec.Gcm.blockAt s₀.mem (C.setWidth 64)) 0
  next : Spec.Gcm.blockAt s.mem (C.setWidth 64) =
    Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt s₀.mem (C.setWidth 64))

section
variable {s₀ : State} {B C S Sp D E : BitVec 32} {R n : Nat} {w : List Byte}

theorem CtrEnv.dis (h : CtrEnv s₀ B C S Sp D E R n w) {r : Region} (h1 : r.Disjoint (reg32 B 2048))
    (h2 : r.Disjoint (reg32 C 16)) : ∀ r' ∈ [(⟨addr B 272, 32⟩ : Region), reg32 C 16], r.Disjoint r' := by
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · exact h1.sub_right (part_sub_reg h.env.fitB (by decide))
  · exact h2

theorem ctrStart_ok (h : CtrEnv s₀ B C S Sp D E R n w) :
    WP isa (.block (saveRegs 5 ++ ctrSetup)) s₀ (CtrStart s₀ B C S E R n w) := by
  have fB := h.env.fitB
  have fC := h.fC
  have hR := h.env.hR
  rw [WP.block_append_iff]
  refine WP.mono (saveRegs_ok (by rw [h.esp]; exact (h.arg 5 (by decide)).trans h.a5)
    (by rw [h.esp]; exact h.argIn 5 (by decide)) fB h.env.scr) fun s₁ h₁ => ?_
  have sub₁ : ∀ r ∈ [(⟨addr B 272, 16⟩ : Region)], Region.Sub r (reg32 B 2048) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by decide)
  have esp₁ : s₁.gpr .esp = E := (h₁.other _ (by decide) (by decide)).trans h.esp
  have arg₁ : ∀ i < 7, s₁.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi =>
    (h₁.frame.readW (h.argC i hi) (fun r hr => h.aB.sub_right (sub₁ r hr)) (by decide)).trans (h.arg i hi)
  have e₁ : ∀ k < 16, s₁.mem (addr C k) = s₀.mem (addr C k) := fun k hk =>
    frame_one h₁.frame (reg_contains fC (by omega_using [hk]) (by decide)) fun r hr => h.dCB.sub_right (sub₁ r hr)
  have b₁ : Spec.Gcm.blockAt s₁.mem (C.setWidth 64) = Spec.Gcm.blockAt s₀.mem (C.setWidth 64) :=
    Proof.Gcm.blockAt_congr fun k hk => by rw [← addr_eq (by omega_using [fC, hk]), e₁ k hk]
  refine WP.mono (ctrSetup_ok (N := BitVec.ofNat 32 n) h₁.edi esp₁ fB (by rw [h₁.wr]; exact h.env.scr) fC
    (by rw [h₁.wr]; exact h.wC) h.dCB (by rw [h₁.rd, h₁.wr]; exact h.argIn 2 (by decide))
    (by rw [h₁.rd, h₁.wr]; exact h.argIn 4 (by decide)) ((arg₁ 2 (by decide)).trans h.a2)
    ((arg₁ 4 (by decide)).trans h.a4) (h.aB.sub_left (h.argSub 4 (by decide)))) fun s₂ h₂ => ?_
  have F₂ : Frame [⟨addr B 272, 32⟩, reg32 C 16] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨addr B 272, 32⟩, by simp, part_sub fB (by decide) (by decide) (by decide)⟩
      · exact ⟨reg32 C 16, by simp, part_sub_reg fC (by decide)⟩
  have arg₂ : ∀ i < 7, s₂.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi =>
    (F₂.readW (h.argC i hi) (h.dis h.aB h.aC) (by decide)).trans (h.arg i hi)
  refine ⟨⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, (h₂.other _ (by decide) (by decide)).trans h₁.edi,
    (h₂.other _ (by decide) (by decide)).trans esp₁, (arg₂ 0 (by decide)).trans h.a0, (arg₂ 1 (by decide)).trans h.a1,
    fun i hi => ?_⟩, F₂, h₁.saved.of_frame h₂.frame (saved_in fB) fun r hr => ?_, ⟨fun i hi => ?_, ?_⟩, ?_⟩
  · rw [← h.w i hi]
    have hS := h.env.fitS
    exact frame_one F₂ (reg_contains hS (by omega_using [hi, hR]) (by decide)) (h.dis h.env.sepS h.dSC)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact part_disj fB (by decide) (by decide) (.inl (by decide))
    · exact (h.dCB.symm.sub_left (part_sub_reg fB (by decide))).sub_right (part_sub_reg fC (by decide))
  · rw [h₂.words i hi, toBytes_blockAt _ _ (by omega_using [hi]), ← addr_eq (by omega_using [fC, hi]),
      e₁ i (by omega_using [hi])]
  · rw [h₂.num, icb_lo _ fC, b₁, BitVec.add_zero]
  · rw [← b₁]
    refine ctr_after fC rfl (fun k hk => ?_) h₂.ctr
    refine frame_one (r := ⟨addr C k, 1⟩) h₂.frame (Region.contains_self _ _) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (h.dCB.sub_left (part_sub_reg fC (by omega_using [hk]))).sub_right (part_sub_reg fB (by decide))
    · exact part_disj fC (N := 16) (by omega_using [hk]) (by decide) (.inl (by omega_using [hk]))

/-- The round keys, and the pointers. -/
theorem ctrPtrs_ok (h : CtrEnv s₀ B C S Sp D E R n w) {s : State} (hs : CtrStart s₀ B C S E R n w s) :
    WP isa keys s fun s₁ => WP isa (.block ctrPtrs) s₁ fun s' =>
      CInv s₀.rd s₀.wr B S E Sp D R n w (Spec.Gcm.blockAt s₀.mem (C.setWidth 64)) s.mem s₀.gpr 0 s' ∧
        s'.zf = some (decide (n = 0)) := by
  have fB := h.env.fitB
  have fD := h.data.fit
  have fSp := h.src.fit
  refine WP.mono (keys_ok h.env hs.good) fun s₃ ⟨good₃, f₃, keys₃⟩ => ?_
  have sub₃ : ∀ r ∈ [(⟨addr B keysOff, 1664⟩ : Region)], Region.Sub r (reg32 B 2048) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by decide)
  have kdisj : ∀ {o l : Nat}, o + l ≤ 384 → ∀ r ∈ [(⟨addr B keysOff, 1664⟩ : Region)], Region.Disjoint ⟨addr B o, l⟩ r :=
    fun h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj fB (by omega_using [h]) (by decide) (.inl (by simp only [keysOff]; exact h))
  have kept₃ : Kept B D n s.mem s₀.gpr s₃.mem := Kept.scratch fB ⟨hs.saved, Frame.refl _ _⟩ f₃ sub₃ (kdisj (by decide))
  have arg₃ : ∀ i < 7, s₃.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi =>
    (f₃.readW (h.argC i hi) (fun r hr => h.aB.sub_right (sub₃ r hr)) (by decide)).trans
      ((hs.frame.readW (h.argC i hi) (h.dis h.aB h.aC) (by decide)).trans (h.arg i hi))
  have data₃ : DataInv s.mem s₃.mem (Sp.setWidth 64) (D.setWidth 64) n (16 * 0)
      (keyStream R w (Spec.Gcm.blockAt s₀.mem (C.setWidth 64))) := by
    have fr : ∀ {A : BitVec 32}, A.toNat + 16 * n ≤ 2 ^ 32 → (reg32 A (16 * n)).Disjoint (reg32 B 2048) → ∀ i < 16 * n,
        s₃.mem (A.setWidth 64 + BitVec.ofNat 64 i) = s.mem (A.setWidth 64 + BitVec.ofNat 64 i) := fun hA h i hi =>
      f₃.bytes (R := reg32 _ (16 * n)) (fun r hr => h.sub_right (sub₃ r hr)) (by show 16 * n ≤ 2 ^ 64; omega_using [hA]) hi
    exact ⟨fun i hi => by rw [ite_eq_right (by omega_using []), fr fD h.data.sep i hi], fun i hi _ => fr fSp h.src.sep i hi⟩
  have in₃ : ∀ (t : State), t.rd = s₃.rd → t.wr = s₃.wr → ∀ i < 7, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t h1 h2 i hi => by rw [h1, h2, good₃.rd, good₃.wr]; exact h.argIn i hi
  refine wp_ldm (B := E) (o := 16) good₃.esp (in₃ _ rfl rfl 3 (by decide)) fun s₄ u₄ =>
    wp_ldm (B := E) (o := 28) ((u₄.other _ (by decide)).trans good₃.esp) (in₃ _ u₄.rd u₄.wr 6 (by decide)) fun s₅ u₅ =>
    wp_ldm (B := E) (o := 20) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), good₃.esp])
      (in₃ _ (by rw [u₅.rd, u₄.rd]) (by rw [u₅.wr, u₄.wr]) 4 (by decide)) fun s₆ u₆ => wp_test fun s₇ u₇ hz =>
      WP.block_nil ?_
  have hbp : s₇.gpr .ebp = BitVec.ofNat 32 n := by
    rw [u₇.gpr, u₆.gpr, u₅.mem, u₄.mem, arg₃ 4 (by decide), h.a4]
  have m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  refine ⟨
    { hk := Nat.zero_le _
      good := (good₃.upd h.env u₄ (by decide) (by decide) |>.upd h.env u₅ (by decide) (by decide)
        |>.upd h.env u₆ (by decide) (by decide)).step h.env (rs := []) u₇.rd u₇.wr
        (by rw [u₇.gpr]) (by rw [u₇.gpr]) (by rw [u₇.mem]; exact Frame.refl _ _) (by simp)
      keys := by rw [m₇]; exact keys₃
      kept := by rw [m₇]; exact kept₃
      edx := by
        rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, arg₃ 3 (by decide), h.a3]; simp
      ebx := by rw [u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.mem, arg₃ 6 (by decide), h.a6]; simp
      ebp := hbp
      ctr := fun _ => by rw [m₇]; exact hs.ctr.frame fB f₃ (kdisj (by decide))
      data := by rw [m₇]; exact data₃ }, ?_⟩
  rw [hz, ← u₇.gpr, hbp, BitVec.and_self, ofNat_beq_zero (by omega_using [fD])]

/-- The passes, and the epilogue. -/
theorem ctrEnd_ok (h : CtrEnv s₀ B C S Sp D E R n w) {s₂ s : State} (h₂ : CtrStart s₀ B C S E R n w s₂)
    (hi : CInv s₀.rd s₀.wr B S E Sp D R n w (Spec.Gcm.blockAt s₀.mem (C.setWidth 64)) s₂.mem s₀.gpr 0 s)
    (hz : s.zf = some (decide (n = 0))) :
    WP isa (.seq (.ite .e (.block []) (.loop group .ne)) (.block restoreRegs)) s fun s' => abiPreserved s₀ s' ∧
      Spec.Gcm.blocksAt s'.mem (D.setWidth 64) n =
        Spec.Gcm.ctr32 (Spec.Gcm.aesWith R w) (Spec.Gcm.blockAt s₀.mem (C.setWidth 64))
          (Spec.Gcm.blocksAt s₀.mem (Sp.setWidth 64) n) ∧
      Spec.Gcm.blockAt s'.mem (C.setWidth 64) =
        Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt s₀.mem (C.setWidth 64)) := by
  have fB := h.env.fitB
  have fSp := h.src.fit
  refine WP.seq (WP.mono
    (Q := CInv s₀.rd s₀.wr B S E Sp D R n w (Spec.Gcm.blockAt s₀.mem (C.setWidth 64)) s₂.mem s₀.gpr n)
    (WP.ite (decide (n = 0)) (by simp only [X86.eval, hz]) (fun hb => WP.block_nil ?_) fun hb => ?_) fun s₈ h₈ => ?_)
  · have hn0 : n = 0 := by simpa using hb
    subst hn0
    exact hi
  · exact groups_ok h.env h.data h.src hi (Nat.pos_of_ne_zero (by simpa using hb))
  refine WP.mono (restoreRegs_ok h₈.good.edi fB (by rw [h₈.good.wr]; exact h.env.scr) h₈.kept.saved)
    fun s₉ r₉ => ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact r₉.abi (by decide) (by decide) (h₈.good.esp.trans h.esp.symm)
  · rw [r₉.mem, h₈.kept.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact h₂.frame.readW (r := retR s₀) (Region.contains_self _ _) (h.dis h.rB h.rC) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.rB
      · exact h.rD
  · rw [r₉.mem, ctr32_of_dataInv h₈.data,
      blocksAt_frame h₂.frame (h.dis h.src.sep h.dCS.symm) (by omega_using [fSp])]
  · rw [← h₂.next]
    refine Proof.Gcm.blockAt_congr fun k hk => ?_
    rw [r₉.mem]
    exact h₈.kept.frame.bytes (R := reg32 C 16) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.dCB
      · exact h.dCD) (by show 16 ≤ 2 ^ 64; decide) hk

end

theorem correct_ctr {s₀ : State} (hp : GPre true s₀) :
    WP isa ctr32To s₀ fun s' => abiPreserved s₀ s' ∧ ctrPost true s₀ s' := by
  have h := CtrEnv.of hp
  refine WP.seq (WP.mono (ctrStart_ok h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ctrPtrs_ok h h₁) fun s₂ h₂ => ?_)
  exact WP.seq (WP.mono h₂ fun s₃ ⟨hi, hz⟩ => ctrEnd_ok h h₁ hi hz)

/-- `vg_aes_ctr32_to` in place. -/
theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32X86.pre s) :
    ∃ t s', Exec isa ctr32To s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32X86.post s s' :=
  have hp := CPre.of hs
  (correct_ctr hp.gpre).imp fun _ ⟨s', he, h, h₂, h₃⟩ => ⟨s', he, h, by simpa only [dstP, ↓reduceIte, hp.same] using h₂, h₃⟩

theorem ctr32To_correct (s : State) (hs : Proof.Aes.ctr32ToX86.pre s) :
    ∃ t s', Exec isa ctr32To s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32ToX86.post s s' :=
  (correct_ctr (GPre.ofTo hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32X86.pre Proof.Aes.ctr32X86.pub ctr32To :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) ctrToτ₀ (fun _ _ h₁ h₂ hp => ctr_agree₀ h₁ h₂ hp) (by taint_decide)

theorem ctr32To_ct : ConstantTime isa Proof.Aes.ctr32ToX86.pre Proof.Aes.ctr32ToX86.pub ctr32To :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) ctrToτ₀ (fun _ _ h₁ h₂ hp => ctrTo_agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.Aes.X86.Sse
