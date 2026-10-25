module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-!
# A row of a square, with the carry handed from the row before

`AdxRect8.rowS`: `AdxRect8.row`'s column blocks but the last in a loop that
stops one block early (`nextColumnS`, or no loop for a row of one block),
then the carry the row before left in `sFn 15` (`handOffset`) added to the
pending carry (`addHand`), then the last block, whose input starts at that
carry's word: the row's contribution and the handed carry, at its word
(`rowS_ok`). The row does not write `sFn 15`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8 (cols cols_keep)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset handOffset)

theorem nextColumnS_ok {s : State} {B : Addr} {Z w j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hj : j+16 < 2^64) (hw : w < 2^64)
    (hidx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j) :
    WP isa (.block AdxRect8.nextColumnS) s fun t =>
      t.mem = s.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (j+8)) ∧
      t.zf = some (decide (j+16=w)) ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  have hiZ : 8*sFn 13+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 13 < 32 by decide); omega_arith
  have hwZ : 8*sW+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_arith
  unfold AdxRect8.nextColumnS
  rw [show ([.mov .rax (.mem (hdr (sFn 13))), .alu .add .rax (.imm 8),
      .store (hdr (sFn 13)) .rax, .alu .add .rax (.imm 8), .alu .cmp .rax (.mem (hdr sW))] : List Instr) =
      [.mov .rax (.mem (hdr (sFn 13))), .alu .add .rax (.imm 8), .store (hdr (sFn 13)) .rax] ++
      [.alu .add .rax (.imm 8), .alu .cmp .rax (.mem (hdr sW))] from rfl, WP.block_append_iff]
  have first : WP isa (.block [.mov .rax (.mem (hdr (sFn 13))), .alu .add .rax (.imm 8),
      .store (hdr (sFn 13)) .rax]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (j+8) ∧
      t.mem = s.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (j+8)) ∧ Keep [.rax] s t := by
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (j+8) ∧
      t.mem = s.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (j+8))) ?_ rfl)
      fun t ⟨⟨a,b⟩,k⟩ => ⟨a,b,k⟩
    xrun [State.ea,hdr,hd,hdrOff,hs.ld hiZ,hs.st hiZ,hidx,
      show (8 : BitVec 32).signExtend 64 = 8 from rfl,BitVec.ofNat_add]
    exact ⟨rfl,rfl⟩
  refine WP.mono first fun a ⟨ra,ma,ka⟩ => ?_
  have sa := hs.congr ka.2.2
  have wa : word a.mem B (8*sW) = BitVec.ofNat 64 w := by
    rw [ma,(writeW_outside s.mem B (BitVec.ofNat 64 (j+8)) (by omega_arith : 8*sFn 13+8 ≤ 2^64)).word
      (by decide : 8*sW+8 ≤ 8*sFn 13 ∨ 8*sFn 13+8 ≤ 8*sW) (by omega_arith),hh.hw]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = a.mem ∧ t.zf = some (decide (j+16=w))) ?_ rfl)
    fun t ⟨⟨mt,zt⟩,kt⟩ => ⟨mt.trans ma,zt,(ka.trans kt).mono (by simp)⟩
  xrun [State.ea,hdr,(ka.gpr (by decide)).trans hd,hdrOff,sa.ld hwZ,wa,ra,
    show (8 : BitVec 32).signExtend 64 = 8 from rfl,
    show BitVec.ofNat 64 (j+8) + 8 = BitVec.ofNat 64 (j+16) by
      rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,← BitVec.ofNat_add],
    ofNat_sub_beq hj hw]

theorem oneTest_ok {s : State} {B : Addr} {Z w j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hj : j+8 < 2^64) (hw : w < 2^64)
    (hidx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j) :
    WP isa (.block AdxRect8.oneTest) s fun t =>
      t.mem = s.mem ∧ t.zf = some (decide (j+8=w)) ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  have hiZ : 8*sFn 13+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 13 < 32 by decide); omega_arith
  have hwZ : 8*sW+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_arith
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧ t.zf = some (decide (j+8=w))) ?_ rfl)
    fun t ⟨⟨mt,zt⟩,kt⟩ => ⟨mt,zt,kt⟩
  unfold AdxRect8.oneTest
  xrun [State.ea,hdr,hd,hdrOff,hs.ld hiZ,hs.ld hwZ,hidx,hh.hw,
    show (8 : BitVec 32).signExtend 64 = 8 from rfl,
    show BitVec.ofNat 64 j + 8 = BitVec.ofNat 64 (j+8) by
      rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,← BitVec.ofNat_add],
    ofNat_sub_beq hj hw]

theorem addHand_ok {s : State} {B : Addr} {Z w : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hZ : slot w 8 ≤ Z) :
    WP isa (.block AdxRect8.addHand) s fun t =>
      t.mem = s.mem.writeW (off B carryOffset) (word s.mem B handOffset + word s.mem B carryOffset) ∧
      Keep [.rax] s t := by
  have hn := hs.nowrap
  have h15 : 8*sFn 15+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 15 < 32 by decide); omega_arith
  have h14 : 8*sFn 14+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 14 < 32 by decide); omega_arith
  refine WP.keep [.rax] (Q := fun t => t.mem =
    s.mem.writeW (off B carryOffset) (word s.mem B handOffset + word s.mem B carryOffset)) ?_ rfl
  unfold AdxRect8.addHand
  xrun [State.ea,hdr,hd,hdrOff,hs.ld h15,hs.ld h14,hs.st h14,carryOffset,handOffset]

/-- What a block that keeps the memory and the registers but `rax` keeps of
the stream's invariant. -/
theorem StreamInv.of_keep {s₀ s t : State} {B : Addr} {Z w a b i j₀ k x cb : Nat} {mi : BitVec 64}
    (h : StreamInv s₀ B Z w a b i j₀ k mi x cb s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    StreamInv s₀ B Z w a b i j₀ k mi x cb t := by
  have cl : cols t = cols s := cols_keep hk (by decide)
  refine ⟨h.scr.congr hk.2.2,hm ▸ h.hdr,(hk.gpr (by decide)).trans h.rdi,hm ▸ h.indexI,hm ▸ h.indexJ,
    hm ▸ h.carry,(h.keep.trans hk).mono (by decide),hm ▸ h.frame,(hk.gpr (by decide)).trans h.pa,
    (hk.gpr (by decide)).trans h.pb,(hk.gpr (by decide)).trans h.po,?_⟩
  have v := h.val
  unfold streamVal at v ⊢
  rw [hm,cl]
  exact v

/-- The handed carry into the pending carry before block `k`, whose input
starts at its word. -/
theorem addHand_inv {s₀ s : State} {B : Addr} {Z w a b i j₀ k σ x cb : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hk8 : i+j₀+8*(k+1) ≤ 2*w) (hcb : cb ≤ 2)
    (h : StreamInv s₀ B Z w a b i j₀ k mi x cb s) (hσ : (word s.mem B handOffset).toNat = σ) (hσ2 : σ ≤ 2) :
    WP isa (.block AdxRect8.addHand) s
      (StreamInv s₀ B Z w a b i j₀ k mi (x + (2 : Nat)^(64*(i+j₀+8*(k+1))) * σ) 4) := by
  have nowrap := h.scr.nowrap
  have rt := slot_le (w := w) (show aTmp < 8 by decide)
  have rawZ : rawBase w+8*(2*w) ≤ Z := by unfold rawBase slot aAcc aTmp at *; omega_arith
  refine WP.mono (addHand_ok h.scr h.rdi hZ) fun t ⟨mt,kt⟩ => ?_
  have hc := h.carry
  have oC : Outside B carryOffset 8 s.mem t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by unfold carryOffset sFn; omega_arith)
  have ct : (word t.mem B carryOffset).toNat = σ + (word s.mem B carryOffset).toNat := by
    rw [mt,word_writeW_self,BitVec.toNat_add,hσ,Nat.mod_eq_of_lt (by omega_arith)]
  have cl : cols t = cols s := cols_keep kt (by decide)
  have fr : Frm B (rowRanges w) s.mem t.mem := Frm.of_outside oC (by simp [rowRanges])
  have hrow : carryOffset+8 ≤ rawBase w := by unfold rawBase carryOffset sFn slot hdrBytes aAcc; omega_arith
  have same : streamVal t B w (i+j₀+8*k) = streamVal s B w (i+j₀+8*k) := by
    unfold streamVal
    rw [cl,oC.wv (Or.inr (by omega_arith)) (by omega_arith),oC.wv (Or.inr (by omega_arith)) (by omega_arith)]
  refine ⟨h.scr.congr kt.2.2,?_,(kt.gpr (by decide)).trans h.rdi,?_,?_,by rw [ct]; omega_arith,
    (h.keep.trans kt).mono (by decide),h.frame.trans fr,(kt.gpr (by decide)).trans h.pa,
    (kt.gpr (by decide)).trans h.pb,(kt.gpr (by decide)).trans h.po,?_⟩
  · exact frame_hdr h.hdr (by unfold rawBase slot; omega_arith) fr
  · rw [oC.word (by unfold carryOffset sFn; omega_arith) (by unfold sFn; omega_arith)]; exact h.indexI
  · rw [oC.word (by unfold carryOffset sFn; omega_arith) (by unfold sFn; omega_arith)]; exact h.indexJ
  · have v := h.val
    rw [same,ct,Nat.mul_add]
    generalize (2 : Nat)^(64*(i+j₀+8*(k+1))) = P at v ⊢
    omega_arith

/-- A square's row: `AdxRect8.row`'s contribution, plus the carry `σ` handed
in `sFn 15`, at word `i + w` of the raw product. -/
theorem rowS_ok {s : State} {B : Addr} {Z w a b i j₀ n σ : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca cb : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hi : i+8 ≤ w)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hwN : w = j₀+8*n) (hn : 0 < n)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hjdx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j₀)
    (hc : (word s.mem B carryOffset).toNat = 0)
    (hσ : (word s.mem B handOffset).toNat = σ) (hσ2 : σ ≤ 2) :
    WP isa (AdxRect8.rowS ca cb) s (RowInv s B Z w a b i j₀ n mi ((2 : Nat)^(64*(i+w)) * σ) 2) := by
  have nowrap := hs.nowrap
  have hR : handOffset+8 ≤ rawBase w := by unfold rawBase handOffset sFn slot hdrBytes aAcc; omega_arith
  have hH : ∀ {m : Mem}, Frm B (rowRanges w) s.mem m → word m B handOffset = word s.mem B handOffset := by
    intro m f
    refine f.word_eq ?_ (by unfold handOffset sFn; omega_arith)
    intro r hr
    simp only [rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl hR
    · exact Or.inr (by unfold carryOffset handOffset sFn; omega_arith)
    · exact Or.inr (by unfold handOffset sFn; omega_arith)
  unfold AdxRect8.rowS
  refine WP.seq (WP.mono (setup_ok hs hd hh hZ hv pa pb hidx hjdx) fun u ⟨ua,ub,uo,um,ku⟩ => ?_)
  refine WP.seq (WP.mono (rowLoad_ok (s₀ := s) (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd) (um ▸ hh) hZ hi
    (by omega_arith) (um ▸ hidx) (um ▸ hjdx) (um ▸ hc) ua ub uo um (ku.mono (by decide))) fun v hv0 => ?_)
  -- the blocks but the last
  have front : WP isa (.seq (.block AdxRect8.oneTest) (.ite .e (.block []) (.loop AdxRect8.rowStepS .ne))) v
      (StreamInv s B Z w a b i j₀ (n-1) mi 0 2) := by
    refine WP.seq (WP.mono (oneTest_ok (j := j₀) hv0.scr hv0.rdi hv0.hdr hZ (by omega_arith) (by omega_arith)
      (by simpa only [Nat.mul_zero,Nat.add_zero] using hv0.indexJ)) fun y ⟨my,zy,ky⟩ => ?_)
    have hy := hv0.of_keep my ky
    by_cases h1 : n = 1
    · refine WP.ite true (by simp [eval,zy,show j₀+8=w by omega_arith]) (fun _ => WP.block_nil ?_) (by intro h; cases h)
      rw [h1]; exact hy
    · refine WP.ite false (by simp [eval,zy,show ¬ j₀+8=w by omega_arith]) (by intro h; cases h) (fun _ => ?_)
      exact wp_upto (a := 0) (N := n-1) (by omega_arith) (StreamInv s B Z w a b i j₀ · mi 0 2)
        (fun k _ hk t h => by
          unfold AdxRect8.rowStepS
          refine WP.mono (streamStep_gen hZ hw hi ha hb ha1 ha2 hb1 hb2 hwN (by omega_arith)
            (fun u hs hd hh hj => nextColumnS_ok hs hd hh hZ (by omega_arith) (by omega_arith) hj) h)
            fun t ⟨zt,ht⟩ => ⟨?_,ht⟩
          rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega_arith)))
        (fun _ h => h) hy
  refine WP.seq (WP.mono front fun y hy => ?_)
  have σy : (word y.mem B handOffset).toNat = σ := by rw [hH hy.frame]; exact hσ
  refine WP.seq (WP.mono (addHand_inv hZ (by omega_arith) (Nat.le_refl _) hy σy hσ2) fun z hz => ?_)
  rw [Nat.zero_add] at hz
  refine WP.seq (WP.mono (streamStep_inv hZ hw hi ha hb ha1 ha2 hb1 hb2 hwN (by omega_arith) hz) fun t ⟨_,ht⟩ => ?_)
  rw [show n-1+1 = n by omega_arith,show i+j₀+8*n = i+w by omega_arith] at ht
  exact rowEnd_ok hZ hi hwN ht

end VG.Proof.Bignum.X86_64.AdxRect8
