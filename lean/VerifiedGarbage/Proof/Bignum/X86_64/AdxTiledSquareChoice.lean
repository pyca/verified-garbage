module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCross
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
public import VerifiedGarbage.Proof.Bignum.Triangular
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.OpAt
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTri8
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddClose
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-! ### `Bignum.X86_64.AdxTiledSquareRow`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxRect8RowS`, which this module and modules that import it used -/

section

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

end

end

/-! ## AdxTiledSquareInit -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

theorem rowInit_ok {s : State} {B : Addr} {Z w i : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hZ : slot w 8≤Z)
    (hidx : word s.mem B (8*sFn 12)=BitVec.ofNat 64 i) :
    WP isa (.block AdxTiledSquare.rowInit) s fun t =>
      word t.mem B carryOffset=0 ∧ word t.mem B (8*sFn 13)=BitVec.ofNat 64 (i+8) ∧
      Outside B (8*sFn 13) 16 s.mem t.mem ∧ Keep [.rax] s t := by
  have nowrap := hs.nowrap
  obtain bound : ∀ k<32, 8*k+8≤Z := fun k hk => by have := hdr_lt_slot w 8 hk; omega_using [hZ, this]
  obtain first : WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 14)) .rax]) s fun t =>
      t.mem=s.mem.writeW (off B carryOffset) (0 : BitVec 64) ∧ Keep [.rax] s t := by
    apply WP.keep [.rax] (Q := fun t => t.mem=s.mem.writeW (off B carryOffset) (0 : BitVec 64)) _ rfl
    xrun [State.ea,hdr,hd,hdrOff,hs.st (bound (sFn 14) (by decide)),carryOffset]; rfl
  unfold AdxTiledSquare.rowInit
  rw [show ([.mov32 .rax (.imm 0),.store (hdr (sFn 14)) .rax,.mov .rax (.mem (hdr (sFn 12))),
    .alu .add .rax (.imm 8),.store (hdr (sFn 13)) .rax] : List Instr)=
    [.mov32 .rax (.imm 0),.store (hdr (sFn 14)) .rax]++
    [.mov .rax (.mem (hdr (sFn 12))),.alu .add .rax (.imm 8),.store (hdr (sFn 13)) .rax] from rfl,
    WP.block_append_iff]
  refine WP.mono first fun u ⟨mu,ku⟩ => ?_
  obtain ou : Outside B carryOffset 8 s.mem u.mem := by rw [mu]; exact writeW_outside _ _ _ (by decide)
  obtain iu : word u.mem B (8*sFn 12)=BitVec.ofNat 64 i := by rw [ou.word (by decide) (by decide)]; exact hidx
  obtain su := hs.congr ku.2.2
  obtain second : WP isa (.block [.mov .rax (.mem (hdr (sFn 12))),.alu .add .rax (.imm 8),.store (hdr (sFn 13)) .rax]) u
      fun t => t.mem=u.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (i+8)) ∧ Keep [.rax] u t := by
    apply WP.keep [.rax] (Q := fun t => t.mem=u.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (i+8))) _ rfl
    xrun [State.ea,hdr,(ku.gpr (by decide)).trans hd,hdrOff,su.ld (bound (sFn 12) (by decide)),
      su.st (bound (sFn 13) (by decide)),iu,show (8 : BitVec 32).signExtend 64=8 from rfl,BitVec.ofNat_add]
    rfl
  refine WP.mono second fun t ⟨mt,kt⟩ => ?_
  obtain ot : Outside B (8*sFn 13) 8 u.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by decide)
  refine ⟨?_,?_,(ou.mono (o' := 8*sFn 13) (n' := 16) (by decide) (by decide)).trans
    (ot.mono (by omega_using []) (by omega_using [])),(ku.trans kt).mono (by simp)⟩
  · rw [ot.word (by decide) (by decide),mu,word_writeW_self]
  · rw [mt,word_writeW_self]

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareCounter -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem nextRow_ok {s : State} {B : Addr} {Z w j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw8 : 8≤w) (hj : j+8 < 2^64) (hw : w < 2^64)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 j) :
    WP isa (.block AdxTiledSquare.nextRow) s fun t =>
      t.mem = s.mem.writeW (off B (8*sFn 12)) (BitVec.ofNat 64 (j+8)) ∧
      t.zf = some (decide (j+8=w-8)) ∧ Keep [.rax,.rcx] s t := by
  have hn := hs.nowrap
  obtain hiZ : 8*sFn 12+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 12 < 32 by decide); omega_using [hZ, this]
  obtain hwZ : 8*sW+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_using [hZ, this]
  unfold AdxTiledSquare.nextRow
  rw [show ([.mov .rax (.mem (hdr (sFn 12))), .alu .add .rax (.imm 8),
      .store (hdr (sFn 12)) .rax, .mov .rcx (.mem (hdr sW)), .alu .sub .rcx (.imm 8), .alu .cmp .rax (.reg .rcx)] : List Instr) =
      [.mov .rax (.mem (hdr (sFn 12))), .alu .add .rax (.imm 8), .store (hdr (sFn 12)) .rax] ++
      [.mov .rcx (.mem (hdr sW)),.alu .sub .rcx (.imm 8),.alu .cmp .rax (.reg .rcx)] from rfl, WP.block_append_iff]
  obtain first : WP isa (.block [.mov .rax (.mem (hdr (sFn 12))), .alu .add .rax (.imm 8),
      .store (hdr (sFn 12)) .rax]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (j+8) ∧
      t.mem = s.mem.writeW (off B (8*sFn 12)) (BitVec.ofNat 64 (j+8)) ∧ Keep [.rax] s t := by
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (j+8) ∧
      t.mem = s.mem.writeW (off B (8*sFn 12)) (BitVec.ofNat 64 (j+8))) ?_ rfl)
      fun t ⟨⟨a,b⟩,k⟩ => ⟨a,b,k⟩
    xrun [State.ea,hdr,hd,hdrOff,hs.ld hiZ,hs.st hiZ,hidx,
      show (8 : BitVec 32).signExtend 64 = 8 from rfl,BitVec.ofNat_add]
    exact ⟨rfl,rfl⟩
  refine WP.mono first fun a ⟨ra,ma,ka⟩ => ?_
  obtain sa := hs.congr ka.2.2
  obtain wa : word a.mem B (8*sW) = BitVec.ofNat 64 w := by
    rw [ma,(writeW_outside s.mem B (BitVec.ofNat 64 (j+8)) (by omega_using [hn, hiZ] : 8*sFn 12+8 ≤ 2^64)).word
      (by decide : 8*sW+8 ≤ 8*sFn 12 ∨ 8*sFn 12+8 ≤ 8*sW) (by omega_using [hn, hwZ]),hh.hw]
  obtain sub : BitVec.ofNat 64 w - (8 : BitVec 64) = BitVec.ofNat 64 (w-8) := by
    obtain add : BitVec.ofNat 64 (w-8)+(8 : BitVec 64)=BitVec.ofNat 64 w := by
      change BitVec.ofNat 64 (w-8)+BitVec.ofNat 64 8=BitVec.ofNat 64 w
      rw [← BitVec.ofNat_add,show w-8+8=w by omega_using [hw8]]
    rw [← add]
    exact BitVec.add_sub_cancel _ _
  refine WP.mono (WP.keep [.rax,.rcx] (Q := fun t => t.mem = a.mem ∧ t.zf = some (decide (j+8=w-8))) ?_ rfl)
    fun t ⟨⟨mt,zt⟩,kt⟩ => ⟨mt.trans ma,zt,(ka.trans kt).mono (by simp)⟩
  xrun [State.ea,hdr,(ka.gpr (by decide)).trans hd,hdrOff,sa.ld hwZ,wa,ra,show (8 : BitVec 32).signExtend 64=8 from rfl,sub,ofNat_sub_beq hj (by omega_using [hw] : w-8<2^64)]

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareRow -/
section

/-! A complete raw multiplication row, including carry propagation. -/
namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges frame_hdr frame_ops input_preserved)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

open VG.Impl.Bignum.X86_64.AdxRect8 (handOffset)
open VG.Proof.MlKem.X86_64 (WP.keep)

theorem lastTest_ok {s : State} {B : Addr} {Z w i : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hi : i+16 < 2^64) (hw : w < 2^64)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i) :
    WP isa (.block AdxTiledSquare.lastTest) s fun t =>
      t.mem = s.mem ∧ t.zf = some (decide (i+16=w)) ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  obtain hiZ : 8*sFn 12+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 12 < 32 by decide); omega_using [hZ, this]
  obtain hwZ : 8*sW+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_using [hZ, this]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧ t.zf = some (decide (i+16=w))) ?_ rfl)
    fun t ⟨⟨mt,zt⟩,kt⟩ => ⟨mt,zt,kt⟩
  unfold AdxTiledSquare.lastTest
  xrun [State.ea,hdr,hd,hdrOff,hs.ld hiZ,hs.ld hwZ,hidx,hh.hw,
    show (16 : BitVec 32).signExtend 64 = 16 from rfl,
    show BitVec.ofNat 64 i + 16 = BitVec.ofNat 64 (i+16) by
      rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,← BitVec.ofNat_add],
    ofNat_sub_beq hi hw]

theorem hand_ok {s : State} {B : Addr} {Z w : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hZ : slot w 8 ≤ Z) :
    WP isa (.block [.mov .rax (.mem (hdr (sFn 14))),.store (hdr (sFn 15)) .rax]) s fun t =>
      t.mem = s.mem.writeW (off B handOffset) (word s.mem B carryOffset) ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  obtain h15 : 8*sFn 15+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 15 < 32 by decide); omega_using [hZ, this]
  obtain h14 : 8*sFn 14+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 14 < 32 by decide); omega_using [hZ, this]
  refine WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B handOffset) (word s.mem B carryOffset)) ?_ rfl
  xrun [State.ea,hdr,hd,hdrOff,hs.ld h14,hs.st h15,carryOffset,handOffset]

private theorem combine {X Y Z P C Q D : Nat}
    (h : Y+P*C=X+D) (t : Z+Q=Y+P*C) : Z+Q=X+D := by omega_using [h, t]

/-- A square's row `i`: its contribution, and the carry `σ` the row before
handed it at word `i + w`; it hands its own at word `i + w + 8` in `sFn 15`,
but the last, which propagates it to the top. -/
theorem row_ok {s : State} {B : Addr} {Z w a i n σ : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hTail : w=i+8+8*n) (hn : 0<n)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hσ : (word s.mem B handOffset).toNat = σ) (hσ2 : σ ≤ 2) :
    WP isa (AdxTiledSquare.row ca) s fun t =>
      t.zf = some (decide (i+8=w-8)) ∧ word t.mem B (8*sFn 12) = BitVec.ofNat 64 (i+8) ∧
      (word t.mem B handOffset).toNat ≤ 2 ∧
      (∃ c, wv t.mem B (rawBase w) (2*w) +
          (2 : Nat)^(64*(i+w+8))*(if i+16=w then 0 else (word t.mem B handOffset).toNat) +
          (2 : Nat)^(128*w)*c =
        wv s.mem B (rawBase w) (2*w)+(2 : Nat)^(64*(i+w))*σ +
          (2 : Nat)^(64*(i+(i+8)))*wv s.mem B (slot w a+8*i) 8*wv s.mem B (slot w a+8*(i+8)) (8*n)) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  obtain Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega_using [hZ, nowrap]
  obtain rawZ : rawBase w+16*w ≤ Z := by unfold rawBase slot aAcc at *; omega_using [hZ]
  unfold AdxTiledSquare.row
  refine WP.seq (WP.mono (rowInit_ok hs hd hZ hidx) fun u ⟨cu,ju,ou,ku⟩ => ?_)
  obtain fu : Frm B (ranges w) s.mem u.mem := by
    intro x hx
    apply ou x
    have := hx (8*sFn 12,32) (by simp [ranges])
    simp only [sFn] at *; omega_using [this]
  obtain iu : word u.mem B (8*sFn 12) = BitVec.ofNat 64 i := by
    rw [ou.word (by decide) (by decide)]; exact hidx
  have σu : (word u.mem B handOffset).toNat = σ := by
    rw [ou.word (by unfold handOffset sFn; omega_using []) (by unfold handOffset sFn; omega_using [])]; exact hσ
  obtain rawU : wv u.mem B (rawBase w) (2*w) = wv s.mem B (rawBase w) (2*w) :=
    ou.wv (by unfold rawBase slot hdrBytes sFn; omega_using []) (by omega_using [nowrap, rawZ])
  refine WP.seq (WP.mono (AdxRect8.rowS_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd)
    (frame_hdr hh fu) (frame_ops hv fu) pa pa hZ hw (by omega_using [hTail]) ha ha ha1 ha2 ha1 ha2
    hTail hn iu ju (by rw [cu]; rfl) σu hσ2) fun v hv => ?_)
  obtain fv : Frm B (ranges w) u.mem v.mem := by
    intro x hx
    apply hv.frame x
    intro r hr
    simp only [AdxRect8.rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    obtain hr0 := hx (rawBase w,16*w) (by simp [ranges])
    obtain hr1 := hx (8*sFn 12,32) (by simp [ranges])
    rcases hr with rfl | rfl | rfl <;> simp only [] <;> simp only [carryOffset,sFn] at * <;> omega_using [hr0, hr1]
  obtain ptr : v.gpr .rsi = off B (rawBase w+8*(i+w)) := by
    obtain p := hv.endPtr.resolve_left (by omega_using [hn])
    rw [show i+(i+8)+8*n=i+w by omega_using [hTail]] at p
    exact p
  have rowEq := hv.val
  rw [show i+(i+8)+8*(n+1)=i+w+8 by omega_using [hTail],rawU,
    input_preserved ha ha1 ha2 (by omega_using [hTail]) Z64 fu,
    input_preserved ha ha1 ha2 (by omega_using [hTail] : (i+8)+8*n ≤ w) Z64 fu] at rowEq
  obtain f0 : Frm B (ranges w) s.mem v.mem := fu.trans fv
  have σv : (word v.mem B handOffset).toNat = σ := by
    rw [hv.frame.word_eq (by
      intro r hr
      simp only [AdxRect8.rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inl (by unfold rawBase handOffset sFn slot hdrBytes aAcc; omega_using [])
      · exact Or.inr (by unfold carryOffset handOffset sFn; omega_using [])
      · exact Or.inr (by unfold handOffset sFn; omega_using [])) (by unfold handOffset sFn; omega_using [])]
    exact σu
  -- the carry: through the words above for the last row, handed otherwise
  obtain tailStep : WP isa AdxTiledSquare.tail v fun x =>
      word x.mem B (8*sFn 12) = BitVec.ofNat 64 i ∧ (word x.mem B handOffset).toNat ≤ 2 ∧
      (∃ c, wv x.mem B (rawBase w) (2*w) +
          (2 : Nat)^(64*(i+w+8))*(if i+16=w then 0 else (word x.mem B handOffset).toNat) +
          (2 : Nat)^(128*w)*c =
        wv s.mem B (rawBase w) (2*w)+(2 : Nat)^(64*(i+w))*σ +
          (2 : Nat)^(64*(i+(i+8)))*wv s.mem B (slot w a+8*i) 8*wv s.mem B (slot w a+8*(i+8)) (8*n)) ∧
      Frm B (ranges w) v.mem x.mem ∧ Keep mmRegs v x := by
    unfold AdxTiledSquare.tail
    refine WP.seq (WP.mono (lastTest_ok hv.scr hv.rdi hv.hdr hZ (by omega_using [hTail, nowrap, rawZ]) (by omega_using [nowrap, rawZ]) hv.indexI)
      fun y ⟨my,zy,ky⟩ => ?_)
    obtain sy := hv.scr.congr ky.2.2
    by_cases hl : i+16=w
    · refine WP.ite true (by simp [eval,zy,hl]) (fun _ => ?_) (by intro h; cases h)
      refine WP.mono (AdxTiledProduct.tail_ok sy ((ky.gpr (by decide)).trans hv.rdi) (my ▸ hv.hdr) hZ hw
        hTail (my ▸ hv.indexI) ((ky.gpr (by decide)).trans ptr)) fun x ⟨⟨c,eq⟩,ox,kx⟩ => ?_
      obtain fx : Frm B (ranges w) y.mem x.mem := Frm.of_outside ox (by simp [ranges])
      obtain hx : word x.mem B handOffset = word v.mem B handOffset := by
        rw [ox.word (by unfold rawBase slot hdrBytes handOffset sFn; omega_using []) (by unfold handOffset sFn; omega_using []),my]
      refine ⟨?_,?_,⟨c,?_⟩,my ▸ fx,(ky.trans kx).mono (by decide)⟩
      · rw [ox.word (by unfold rawBase slot hdrBytes sFn; omega_using []) (by decide),my]; exact hv.indexI
      · rw [hx,σv]; exact hσ2
      · rw [my] at eq
        simp only [hl,ite_true,Nat.mul_zero,Nat.add_zero]
        exact combine rowEq eq
    · refine WP.ite false (by simp [eval,zy,hl]) (by intro h; cases h) (fun _ => ?_)
      refine WP.mono (hand_ok sy ((ky.gpr (by decide)).trans hv.rdi) hZ) fun x ⟨mx,kx⟩ => ?_
      obtain ox : Outside B handOffset 8 y.mem x.mem := by
        rw [mx]; exact writeW_outside _ _ _ (by unfold handOffset sFn; omega_using [])
      obtain fx : Frm B (ranges w) y.mem x.mem := by
        intro z hz
        apply ox z
        have := hz (8*sFn 12,32) (by simp [ranges])
        unfold handOffset; simp only [sFn] at *; omega_using [this]
      obtain hx : (word x.mem B handOffset).toNat = (word v.mem B carryOffset).toNat := by
        rw [mx,word_writeW_self,my]
      refine ⟨?_,by rw [hx]; exact hv.carry,⟨0,?_⟩,my ▸ fx,(ky.trans kx).mono (by decide)⟩
      · rw [ox.word (by unfold handOffset sFn; omega_using []) (by decide),my]; exact hv.indexI
      · rw [ox.wv (by unfold rawBase slot hdrBytes handOffset sFn; omega_using []) (by omega_using [nowrap, rawZ]),my]
        simp only [hl,ite_false,hx,Nat.mul_zero,Nat.add_zero]
        exact rowEq
  refine WP.seq (WP.mono tailStep fun x ⟨ix,σx,⟨c,val⟩,fx,kx⟩ => ?_)
  obtain f : Frm B (ranges w) s.mem x.mem := f0.trans fx
  obtain hx : Hdr x.mem B w mi := frame_hdr hh f
  refine WP.mono (nextRow_ok (hv.scr.congr kx.2.2) ((kx.gpr (by decide)).trans hv.rdi)
    hx hZ (by omega_using [hTail]) (by omega_using [hTail, nowrap, rawZ]) (by omega_using [nowrap, rawZ]) ix) fun t ⟨mt,zt,kt⟩ => ?_
  obtain ot : Outside B (8*sFn 12) 8 x.mem t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by decide)
  obtain ft : Frm B (ranges w) x.mem t.mem := by
    intro y hy
    apply ot y
    have := hy (8*sFn 12,32) (by simp [ranges]); omega_using [this]
  obtain ht : word t.mem B handOffset = word x.mem B handOffset :=
    ot.word (by unfold handOffset sFn; omega_using []) (by unfold handOffset sFn; omega_using [])
  refine ⟨zt,?_,by rw [ht]; exact σx,⟨c,?_⟩,frame_hdr hx ft,f.trans ft,
    (((ku.trans hv.keep).trans kx).trans kt).mono (by decide)⟩
  · rw [mt,word_writeW_self]
  · rw [ot.wv (by unfold rawBase slot hdrBytes sFn; omega_using []) (by omega_using [nowrap, rawZ] : rawBase w+8*(2*w) ≤ 2^64),ht]
    exact val

/-- `row_ok` for `row1`, whose carry goes through the words above. -/
theorem row1_ok {s : State} {B : Addr} {Z w a i n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hTail : w=i+8+8*n) (hn : 0<n)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i) :
    WP isa (AdxTiledSquare.row1 ca) s fun t =>
      t.zf = some (decide (i+8=w-8)) ∧ word t.mem B (8*sFn 12) = BitVec.ofNat 64 (i+8) ∧
      (∃ c, wv t.mem B (rawBase w) (2*w)+(2 : Nat)^(128*w)*c =
        wv s.mem B (rawBase w) (2*w)+(2 : Nat)^(64*(i+(i+8)))*wv s.mem B (slot w a+8*i) 8*wv s.mem B (slot w a+8*(i+8)) (8*n)) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  obtain Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega_using [hZ, nowrap]
  obtain rawZ : rawBase w+16*w ≤ Z := by unfold rawBase slot aAcc at *; omega_using [hZ]
  unfold AdxTiledSquare.row1
  refine WP.seq (WP.mono (rowInit_ok hs hd hZ hidx) fun u ⟨cu,ju,ou,ku⟩ => ?_)
  obtain fu : Frm B (ranges w) s.mem u.mem := by
    intro x hx
    apply ou x
    have := hx (8*sFn 12,32) (by simp [ranges])
    simp only [sFn] at *; omega_using [this]
  obtain iu : word u.mem B (8*sFn 12) = BitVec.ofNat 64 i := by
    rw [ou.word (by decide) (by decide)]; exact hidx
  obtain rawU : wv u.mem B (rawBase w) (2*w) = wv s.mem B (rawBase w) (2*w) :=
    ou.wv (by unfold rawBase slot hdrBytes sFn; omega_using []) (by omega_using [nowrap, rawZ])
  refine WP.seq (WP.mono (AdxRect8.row_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd)
    (frame_hdr hh fu) (frame_ops hv fu) pa pa hZ hw (by omega_using [hTail]) ha ha ha1 ha2 ha1 ha2
    hTail hn iu ju (by rw [cu]; rfl)) fun v hv => ?_)
  obtain fv : Frm B (ranges w) u.mem v.mem := by
    intro x hx
    apply hv.frame x
    intro r hr
    simp only [AdxRect8.rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    obtain hr0 := hx (rawBase w,16*w) (by simp [ranges])
    obtain hr1 := hx (8*sFn 12,32) (by simp [ranges])
    rcases hr with rfl | rfl | rfl <;> simp only [] <;> simp only [carryOffset,sFn] at * <;> omega_using [hr0, hr1]
  obtain ptr : v.gpr .rsi = off B (rawBase w+8*(i+w)) := by
    obtain p := hv.endPtr.resolve_left (by omega_using [hn])
    rw [show i+(i+8)+8*n=i+w by omega_using [hTail]] at p
    exact p
  refine WP.seq (WP.mono (AdxTiledProduct.tail_ok hv.scr hv.rdi hv.hdr hZ hw hTail hv.indexI ptr)
    fun x ⟨⟨c,eq⟩,ox,kx⟩ => ?_)
  obtain fx : Frm B (ranges w) v.mem x.mem := Frm.of_outside ox (by simp [ranges])
  obtain f : Frm B (ranges w) s.mem x.mem := (fu.trans fv).trans fx
  obtain hx : Hdr x.mem B w mi := frame_hdr hh f
  obtain ix : word x.mem B (8*sFn 12) = BitVec.ofNat 64 i := by
    rw [ox.word (by unfold rawBase slot hdrBytes sFn; omega_using []) (by decide)]
    exact hv.indexI
  have rowEq := hv.val
  rw [show i+(i+8)+8*(n+1)=i+w+8 by omega_using [hTail],rawU,
    input_preserved ha ha1 ha2 (by omega_using [hTail]) Z64 fu,
    input_preserved ha ha1 ha2 (by omega_using [hTail] : (i+8)+8*n ≤ w) Z64 fu,Nat.add_zero] at rowEq
  obtain val : wv x.mem B (rawBase w) (2*w)+2^(128*w)*c =
      wv s.mem B (rawBase w) (2*w)+2^(64*(i+(i+8)))*wv s.mem B (slot w a+8*i) 8*
        wv s.mem B (slot w a+8*(i+8)) (8*n) := combine rowEq eq
  refine WP.mono (nextRow_ok (hv.scr.congr kx.2.2) ((kx.gpr (by decide)).trans hv.rdi)
    hx hZ (by omega_using [hTail]) (by omega_using [hTail, nowrap, rawZ]) (by omega_using [nowrap, rawZ]) ix) fun t ⟨mt,zt,kt⟩ => ?_
  obtain ot : Outside B (8*sFn 12) 8 x.mem t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by decide)
  obtain ft : Frm B (ranges w) x.mem t.mem := by
    intro y hy
    apply ot y
    have := hy (8*sFn 12,32) (by simp [ranges]); omega_using [this]
  refine ⟨zt,?_,⟨c,?_⟩,frame_hdr hx ft,f.trans ft,(((ku.trans hv.keep).trans kx).trans kt).mono (by decide)⟩
  · rw [mt,word_writeW_self]
  · rw [ot.wv (by unfold rawBase slot hdrBytes sFn; omega_using []) (by omega_using [nowrap, rawZ] : rawBase w+8*(2*w) ≤ 2^64)]
    exact val

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

end

end

/-! ### `Bignum.X86_64.AdxTri8Block`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTri8Row0`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTri8Sum`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTri8RowCore`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTri8Chain`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTri8Word`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem word_ok (s : State) {k : Nat} {hi prev col : Reg} {v : BitVec 64} {c o : Bool}
    (hm : readSrc s (.mem (at_ .rbp (8*k)))=some v) (hc : s.cf=some c) (ho : s.of=some o)
    (h1 : hi≠.rsi) (h2 : col≠hi) (h3 : col≠.rsi)
    (h4 : prev≠hi) (h5 : prev≠.rsi) (h6 : prev≠col) :
    WP isa (.block (AdxTri8.word k hi prev col)) s fun t => ∃ c' o' : Bool,
      t.cf=some c' ∧ t.of=some o' ∧
      (t.gpr col).toNat+2^64*((t.gpr hi).toNat+c'.toNat+o'.toNat)=
        (s.gpr col).toNat+(s.gpr .rdx).toNat*v.toNat+(s.gpr prev).toNat+c.toNat+o.toNat ∧
      Keeps [hi,.rsi,col] s t := by
  rw [show AdxTri8.word k hi prev col = [.mulx hi .rsi (.mem (at_ .rbp (8*k)))] ++
    AdxDualAdd.word col (.reg .rsi) (.reg prev) from rfl,WP.block_append_iff]
  refine WP.mono (mulx_ok s hm (fun _ h => nomatch h) h1) fun a ⟨ea,ca,oa,ka⟩ => ?_
  refine WP.mono (AdxDualAdd.word_ok a (a := .reg .rsi) (b := .reg prev) (vb := a.gpr prev) rfl
    (fun u ku => by simp only [readSrc]; rw [ku.gpr (by simp [h6])])
    (fun _ h => nomatch h) (fun _ h => nomatch h) (ca.trans hc) (oa.trans ho))
    fun t ⟨ct,ot,hct,hot,eq,kt⟩ => ?_
  have colA : a.gpr col=s.gpr col := ka.gpr (by simp [h2,h3])
  have prevA : a.gpr prev=s.gpr prev := ka.gpr (by simp [h4,h5])
  have hiT : t.gpr hi=a.gpr hi := kt.gpr (by simp [Ne.symm h2])
  rw [colA,prevA] at eq
  refine ⟨ct,ot,hct,hot,?_,(ka.trans kt).mono (by simp)⟩
  rw [hiT]
  omega_using [ea, eq]

theorem close_ok (s : State) {hi col : Reg} {c o : Bool}
    (hc : s.cf=some c) (ho : s.of=some o) (hz : s.gpr col=0) (hne : hi≠col) :
    WP isa (.block (AdxTri8.close hi col)) s fun t => ∃ c' o' : Bool,
      t.cf=some c' ∧ t.of=some o' ∧
      (t.gpr col).toNat+2^64*(c'.toNat+o'.toNat)=
        (s.gpr col).toNat+(s.gpr hi).toNat+c.toNat+o.toNat ∧ Keeps [col] s t := by
  change WP isa (.block (AdxDualAdd.word col (.reg col) (.reg hi))) s _
  refine WP.mono (AdxDualAdd.word_ok s (a := .reg col) (b := .reg hi) (vb := s.gpr hi) rfl
    (fun t kt => by simp only [readSrc]; rw [kt.gpr (by simp [hne])])
    (fun _ h => nomatch h) (fun _ h => nomatch h) hc ho) fun t ⟨ct,ot,hct,hot,eq,kt⟩ => ?_
  rw [hz] at eq ⊢
  simp only [show (0 : BitVec 64).toNat=0 from rfl,Nat.add_zero,Nat.zero_add] at eq ⊢
  exact ⟨ct,ot,hct,hot,eq,kt⟩

end VG.Proof.Bignum.X86_64.AdxTri8

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

def value (s : State) : List Reg → Nat
  | [] => 0
  | r::rs => (s.gpr r).toNat+2^64*value s rs

def Safe (r : Reg) : Prop := r≠.rsi ∧ r≠.rbp ∧ r≠.rdx ∧ r≠.rcx

theorem value_congr {s t : State} {rs : List Reg} (h : ∀ r ∈ rs, t.gpr r=s.gpr r) : value t rs=value s rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [value,value,h r (by simp),ih (fun r hr => h r (by simp [hr]))]

private theorem append_arith {L L' R H C O X P D U U' Q F A Ci Oi : Nat}
    (word : L'+R*(H+C+O)=L+X*D+P+Ci+Oi)
    (tail : U'+Q*F=U+X*A+H+C+O) :
    L'+R*U'+(R*Q)*F=(L+R*U)+X*(D+R*A)+P+Ci+Oi := by grind

theorem chain_ok (rs : List Reg) {s : State} {B : Addr} {Z e k : Nat}
    {hi other prev : Reg} {c o : Bool}
    (hs : Scr s B Z) (hp : s.gpr .rbp=off B e) (htop : value s rs<2^(64*(rs.length-1)))
    (hZ : e+8*(k+(rs.length-1)) ≤ Z) (hn : rs≠[]) (hd : rs.Nodup)
    (hh : Safe hi) (ho' : Safe other) (hne : hi≠other) (hp1 : prev≠hi) (hp2 : prev≠.rsi)
    (hrs : ∀ r ∈ rs, Safe r ∧ r≠hi ∧ r≠other ∧ r≠prev)
    (hc : s.cf=some c) (ho : s.of=some o) :
    WP isa (.block (AdxTri8.chain k hi other prev rs)) s fun t => ∃ c' o' : Bool,
      t.cf=some c' ∧ t.of=some o' ∧
      value t rs+2^(64*rs.length)*(c'.toNat+o'.toNat)=
        value s rs+(s.gpr .rdx).toNat*wv s.mem B (e+8*k) (rs.length-1)+
          (s.gpr prev).toNat+c.toNat+o.toNat ∧ Keeps ([hi,other,.rsi]++rs) s t := by
  induction rs generalizing s k hi other prev c o with
  | nil => exact False.elim (hn rfl)
  | cons col rs ih =>
    cases rs with
    | nil =>
      have cp := (hrs col (by simp)).2.2.2
      have hz : s.gpr col=0 := by
        apply BitVec.eq_of_toNat_eq
        simp only [value,List.length_cons,List.length_nil,Nat.sub_self,Nat.mul_zero,Nat.pow_zero] at htop
        simp only [show (0 : BitVec 64).toNat=0 from rfl]; omega_using [htop]
      refine WP.mono (close_ok s hc ho hz (Ne.symm cp)) fun t ⟨ct,ot,hct,hot,eq,kt⟩ => ?_
      refine ⟨ct,ot,hct,hot,?_,kt.mono (by simp)⟩
      simpa only [value,List.length_cons,List.length_nil,Nat.mul_one,Nat.sub_self,wv,
        Nat.mul_zero,Nat.add_zero] using eq
    | cons next rest =>
      have cs := hrs col (by simp)
      have nd : col∉next::rest ∧ (next::rest).Nodup := List.nodup_cons.mp hd
      have hkZ : e+8*k+8 ≤ Z := by simp only [List.length_cons] at hZ; omega_using [hZ]
      have hm : readSrc s (.mem (at_ .rbp (8*k)))=some (word s.mem B (e+8*k)) :=
        readSrc_word hs (AdxRotate8.ea_at hp (8*k)) hkZ
      simp only [AdxTri8.chain]
      rw [WP.block_append_iff]
      refine WP.mono (word_ok s hm hc ho hh.1 cs.2.1 cs.1.1 hp1 hp2 cs.2.2.2.symm)
        fun a ⟨ca,oa,hca,hoa,eq,ka⟩ => ?_
      have pa : a.gpr .rbp=off B e := (ka.gpr (by simp [Ne.symm hh.2.1,Ne.symm cs.1.2.1])).trans hp
      have tailPres : value a (next::rest)=value s (next::rest) := value_congr (by
        intro r hr
        have h := hrs r (by simp [hr])
        exact ka.gpr (by simp [h.2.1,h.1.1,show r≠col by intro e; subst r; exact nd.1 hr]))
      have topA : value a (next::rest)<2^(64*((next::rest).length-1)) := by
        rw [tailPres]
        have e1 : value s (col::next::rest)=(s.gpr col).toNat+2^64*value s (next::rest) := rfl
        have e2 : 64*((col::next::rest).length-1)=64+64*((next::rest).length-1) := by
          simp only [List.length_cons]; omega_using []
        rw [e1,e2,Nat.pow_add] at htop
        exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) htop)
      refine WP.mono (ih (hs.congr ka.2.2.2) pa topA (by simp only [List.length_cons] at *; omega_using [hZ])
        (by simp) nd.2 ho' hh hne.symm hne hh.1 ?_ hca hoa) fun t ⟨ct,ot,hct,hot,et,kt⟩ => ?_
      · intro r hr
        have h := hrs r (by simp [hr])
        exact ⟨h.1,h.2.2.1,h.2.1,h.2.1⟩
      have caPres : a.gpr .rdx=s.gpr .rdx := ka.gpr (by simp [Ne.symm hh.2.2.1,Ne.symm cs.1.2.2.1])
      have colPres : t.gpr col=a.gpr col := kt.gpr (by simp [cs.2.1,cs.2.2.1,cs.1.1,nd.1])
      rw [caPres,ka.2.1,tailPres] at et
      refine ⟨ct,ot,hct,hot,?_,(ka.trans kt).mono (by
        intro r hr
        simp only [List.mem_append] at hr ⊢
        rcases hr with h | h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl <;> simp
        · rcases h with h | h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl | rfl <;> simp
          · exact Or.inr (List.mem_cons_of_mem _ h))⟩
      rw [show value t (col::next::rest)=(t.gpr col).toNat+2^64*value t (next::rest) from rfl,
        show value s (col::next::rest)=(s.gpr col).toNat+2^64*value s (next::rest) from rfl,colPres,show 64*(col::next::rest).length=64+64*(next::rest).length by simp; omega_using [],Nat.pow_add]
      have split : wv s.mem B (e+8*k) ((col::next::rest).length-1)=
          (word s.mem B (e+8*k)).toNat+2^64*wv s.mem B (e+8*(k+1)) ((next::rest).length-1) := by
        rw [show (col::next::rest).length-1=1+((next::rest).length-1) by simp; omega_using [],wv_add]
        simp only [wv,Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.pow_zero,Nat.one_mul,Nat.mul_one]
        rw [show e+8*k+8=e+8*(k+1) by omega_using []]
      rw [split]
      exact append_arith eq et

end VG.Proof.Bignum.X86_64.AdxTri8

end

end

/-! ### `Bignum.X86_64.AdxTri8Value`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64

private theorem digit_bound {R Q A V : Nat} (ha : A<R) (hv : V<Q) : A+R*V<R*Q := by
  have h : R*V ≤ R*(Q-1) := Nat.mul_le_mul_left R (by omega_using [hv])
  have e : R+R*(Q-1)=R*Q := by
    calc
      _ = R*1+R*(Q-1) := by rw [Nat.mul_one]
      _ = R*(1+(Q-1)) := (Nat.mul_add ..).symm
      _ = R*Q := by rw [show 1+(Q-1)=Q by omega_using [hv]]
  omega_using [ha, h, e]

theorem value_lt (s : State) (rs : List Reg) : value s rs<2^(64*rs.length) := by
  induction rs with
  | nil => simp only [value,List.length_nil,Nat.mul_zero,Nat.pow_zero]; decide
  | cons r rs ih =>
    rw [value,List.length_cons,show 64*(rs.length+1)=64+64*rs.length by omega_using [],Nat.pow_add]
    exact digit_bound (s.gpr r).isLt ih

theorem value_append (s : State) (rs tail : List Reg) :
    value s (rs++tail)=value s rs+2^(64*rs.length)*value s tail := by
  induction rs with
  | nil => simp only [List.nil_append,value,List.length_nil,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add]
  | cons r rs ih =>
    simp only [List.cons_append,value,List.length_cons,ih]
    rw [show 64*(rs.length+1)=64+64*rs.length by omega_using [],Nat.pow_add]
    rw [Nat.mul_add,Nat.add_assoc,Nat.mul_assoc]

theorem value_zero_top {s : State} {rs : List Reg} {top : Reg} (hz : s.gpr top=0) :
    value s (rs++[top])<2^(64*((rs++[top]).length-1)) := by
  rw [value_append]
  simp only [value,hz,show (0 : BitVec 64).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero,
    List.length_append,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_sub_cancel]
  exact value_lt s rs

end VG.Proof.Bignum.X86_64.AdxTri8

end

end


/-! ## AdxTri8Closed -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

private theorem mac_bound {R Q X U V : Nat} (hx : X<R) (hu : U<Q) (hv : V<Q) : V+X*U<R*Q := by
  have h : X*U ≤ (R-1)*(Q-1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have e : (Q-1)+(R-1)*(Q-1)+R=R*Q := by
    calc
      _ = ((R-1)+1)*(Q-1)+R := by rw [Nat.add_mul,Nat.one_mul]; omega_arith
      _ = R*(Q-1)+R := by rw [Nat.sub_add_cancel (by omega_arith : 1≤R)]
      _ = R*((Q-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
      _ = R*Q := by rw [Nat.sub_add_cancel (by omega_arith : 1≤Q)]
  omega_arith

private theorem no_carry {L Q C V : Nat} (h : L+Q*C=V) (hb : V<Q) : L=V := by
  have hc : C=0 := by
    by_contra ne
    have : Q ≤ Q*C := Nat.le_mul_of_pos_right _ (by omega_arith)
    omega_arith
  simpa only [hc,Nat.mul_zero,Nat.add_zero] using h

theorem last_mem (col : Reg) (rest : List Reg) : AdxTri8.last col rest ∈ col::rest := by
  induction rest generalizing col with
  | nil => simp [AdxTri8.last]
  | cons r rs ih => exact List.mem_cons_of_mem _ (ih r)

theorem dropLast_last (col : Reg) (rest : List Reg) :
    (col::rest).dropLast++[AdxTri8.last col rest]=col::rest := by
  induction rest generalizing col with
  | nil => rfl
  | cons r rs ih => simp only [AdxTri8.last,List.dropLast_cons_cons,List.cons_append,ih]

theorem last_ne {col next : Reg} {rest : List Reg} (hd : (col::next::rest).Nodup) :
    AdxTri8.last col (next::rest)≠col := by
  intro h
  have m := last_mem next rest
  rw [show AdxTri8.last col (next::rest)=AdxTri8.last next rest from rfl] at h
  rw [h] at m
  exact (List.nodup_cons.mp hd).1 m

/-- The value of the columns once their top one is zero: that of the others. -/
theorem value_top_zero {s : State} {col : Reg} {rest : List Reg}
    (hz : s.gpr (AdxTri8.last col rest)=0) :
    value s (col::rest)=value s (col::rest).dropLast := by
  conv => lhs; rw [← dropLast_last col rest]
  rw [value_append]
  simp only [value,hz,show (0 : BitVec 64).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero]

theorem xorZero_ok (s : State) (r : Reg) :
    WP isa (.block [.alu32 .xor r (.reg r)]) s fun t =>
      t.gpr r=0 ∧ t.cf=some false ∧ t.of=some false ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu32,readSrc32,Option.bind_some,
    State.setReg32,Option.some.injEq,exists_eq_left']
  refine ⟨?_,rfl,rfl,fun r' hr => ?_,rfl,rfl,rfl⟩
  · simp only [RegUpd.gpr_setReg_self,BitVec.xor_self]; rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr,RegUpd.gpr_arithFlags]

theorem xorRax_ok (s : State) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax)]) s fun t =>
      t.gpr .rax=0 ∧ t.cf=some false ∧ t.of=some false ∧ Keeps [.rax] s t := xorZero_ok s .rax

theorem wordF_ok (s : State) {k : Nat} {hi col : Reg} {v : BitVec 64} {c : Bool}
    (hm : readSrc s (.mem (at_ .rbp (8*k)))=some v) (hc : s.cf=some c)
    (h1 : hi≠.rsi) (h2 : col≠hi) (h3 : col≠.rsi) :
    WP isa (.block (AdxTri8.wordF k hi col)) s fun t => ∃ c' : Bool,
      t.cf=some c' ∧ t.of=s.of ∧
      (t.gpr col).toNat+2^64*((t.gpr hi).toNat+c'.toNat)=
        (s.gpr col).toNat+(s.gpr .rdx).toNat*v.toNat+c.toNat ∧ Keeps [hi,.rsi,col] s t := by
  rw [show AdxTri8.wordF k hi col=[.mulx hi .rsi (.mem (at_ .rbp (8*k)))]++[.adcx col (.reg .rsi)] from rfl,
    WP.block_append_iff]
  refine WP.mono (mulx_ok s hm (fun _ h => nomatch h) h1) fun a ⟨ea,ca,oa,ka⟩ => ?_
  refine WP.mono (adcx_ok a (src := .reg .rsi) (v := a.gpr .rsi) rfl (fun _ h => nomatch h) (ca.trans hc))
    fun t ⟨ct,hct,ot,eq,kt⟩ => ?_
  have colA : a.gpr col=s.gpr col := ka.gpr (by simp [h2,h3])
  have hiT : t.gpr hi=a.gpr hi := kt.gpr (by simp [Ne.symm h2])
  refine ⟨ct,hct,ot.trans oa,?_,(ka.trans kt).mono (by simp)⟩
  rw [hiT]
  rw [colA] at eq
  omega_arith

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8RowCore -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem last_not_mem_dropLast {col : Reg} {rest : List Reg} (hd : (col::rest).Nodup) :
    AdxTri8.last col rest ∉ (col::rest).dropLast := by
  intro m
  have h := hd
  rw [← dropLast_last col rest,List.nodup_append] at h
  exact h.2.2 _ m _ (by simp) rfl

private theorem row_arith {Ct Cb Hc c1 Vb X v1 W Tt P O : Nat}
    (first : Ct+2^64*(Hc+c1)=Cb+X*v1)
    (tail : Tt+P*O=Vb+X*W+Hc+c1) :
    Ct+2^64*Tt+(2^64*P)*O=Cb+2^64*Vb+X*(v1+2^64*W) := by grind

/-- A row over `col::rest` (two columns or more): its top column is zeroed
first, so the result is the value of the others plus the row's products. -/
theorem rowCore_ok (col : Reg) (rest : List Reg) {s : State} {B : Addr} {Z e i : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rbp=off B e)
    (hZ : e+8*(i+(col::rest).length) ≤ Z) (hn : rest≠[]) (hd : (col::rest).Nodup)
    (hrs : ∀ r ∈ col::rest, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx) :
    WP isa (.block (AdxTri8.rowCore i col rest)) s fun t =>
      value t (col::rest)=value s (col::rest).dropLast+
        (word s.mem B (e+8*i)).toNat*wv s.mem B (e+8*(i+1)) rest.length ∧
      Keeps (([.rdx,.rax,.rbx,.rsi] : List Reg)++col::rest) s t := by
  cases rest with
  | nil => exact absurd rfl hn
  | cons next rest =>
  have nd := List.nodup_cons.mp hd
  have cs := hrs col (by simp)
  have zm := last_mem col (next::rest)
  have zs := hrs _ zm
  have zc : AdxTri8.last col (next::rest)≠col := last_ne hd
  have zl : AdxTri8.last col (next::rest)=AdxTri8.last next rest := rfl
  have len : (col::next::rest).length=rest.length+2 := by simp
  have hm := readSrc_word hs (AdxRotate8.ea_at hp (8*i)) (by omega_using [hZ, len])
  unfold AdxTri8.rowCore
  rw [WP.block_append_iff]
  rw [show ([.mov .rdx (.mem (at_ .rbp (8*i))),.alu32 .xor (AdxTri8.last col (next::rest))
      (.reg (AdxTri8.last col (next::rest)))] : List Instr)=
    [.mov .rdx (.mem (at_ .rbp (8*i)))] ++ [.alu32 .xor (AdxTri8.last col (next::rest))
      (.reg (AdxTri8.last col (next::rest)))] from rfl,WP.block_append_iff]
  refine WP.mono (movMem_ok s hm) fun a ⟨pa,_,_,ka⟩ => ?_
  refine WP.mono (xorZero_ok a _) fun b ⟨zb,cb,ob,kb⟩ => ?_
  have kab := ka.trans kb
  have vb : value b (col::next::rest)=value s (col::next::rest).dropLast := by
    rw [value_top_zero zb]
    apply value_congr
    intro r hr
    have hr' : r ∈ col::next::rest := by
      rw [← dropLast_last col (next::rest)]; exact List.mem_append_left _ hr
    have h := hrs r hr'
    refine kab.gpr ?_
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨h.1.2.2.1,?_⟩
    intro e; subst e
    exact last_not_mem_dropLast hd hr
  have xb : b.gpr .rdx=word s.mem B (e+8*i) :=
    (kb.gpr (by simp only [List.mem_cons,List.not_mem_nil,or_false]; exact zs.1.2.2.1.symm)).trans pa
  have sb := hs.congr kab.2.2.2
  have pb : b.gpr .rbp=off B e := (kab.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,zs.1.2.1.symm⟩)).trans hp
  have hm1 := readSrc_word sb (AdxRotate8.ea_at pb (8*(i+1))) (by omega_using [hZ, len])
  rw [WP.block_append_iff]
  refine WP.mono (wordF_ok b hm1 cb (by decide) cs.2.2.1 cs.1.1) fun c ⟨c1,cc,oc,eqF,kc⟩ => ?_
  have pc : c.gpr .rbp=off B e := (kc.gpr (by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,by decide,cs.1.2.1.symm⟩)).trans pb
  have nrC : value c (next::rest)=value b (next::rest) := value_congr fun r hr => by
    have h := hrs r (by simp [hr])
    refine kc.gpr ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨h.2.2.1,h.1.1,fun e => by subst e; exact nd.1 hr⟩
  have zcz : c.gpr (AdxTri8.last next rest)=0 := by
    rw [← zl]
    refine (kc.gpr ?_).trans zb
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨zs.2.2.1,zs.1.1,zc⟩
  have topC : value c (next::rest)<2^(64*((next::rest).length-1)) := by
    have h := value_zero_top (s := c) (rs := (next::rest).dropLast) zcz
    rwa [dropLast_last next rest] at h
  refine WP.mono (chain_ok (next::rest) (hs.congr (kab.trans kc).2.2.2) pc topC
    (by simp only [List.length_cons] at hZ ⊢; omega_using [hZ]) (by simp) nd.2
    (by unfold Safe; decide) (by unfold Safe; decide) (by decide) (by decide) (by decide)
    (fun r h => let q := hrs r (by simp [h]); ⟨q.1,q.2.1,q.2.2.1,q.2.2.1⟩) cc
    (oc.trans ob)) fun t ⟨c',o',_,_,eqT,kt⟩ => ?_
  have xc : c.gpr .rdx=b.gpr .rdx := kc.gpr (by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,by decide,cs.1.2.2.1.symm⟩)
  have colT : t.gpr col=c.gpr col := kt.gpr (r := col) (by
    intro h
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with (h|h|h)|h
    exacts [cs.2.1 h,cs.2.2.1 h,cs.1.1 h,nd.1 (List.mem_cons.mpr h)])
  have mc : c.mem=s.mem := kc.2.1.trans kab.2.1
  rw [xc,xb,mc,nrC] at eqT
  rw [xb,kab.2.1,show (false : Bool).toNat=0 from rfl,Nat.add_zero] at eqF
  rw [show (false : Bool).toNat=0 from rfl,Nat.add_zero] at eqT
  have dl : (col::next::rest).dropLast=col::(next::rest).dropLast := List.dropLast_cons_cons
  have colB : b.gpr col=s.gpr col := kab.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨cs.1.2.2.1,zc.symm⟩)
  have vb' : (b.gpr col).toNat+2^64*value b (next::rest)=value s (col::next::rest).dropLast := vb
  have l1 : (next::rest).length-1=rest.length := by simp
  have l2 : (next::rest).length=rest.length+1 := by simp
  rw [l1,l2] at eqT
  have split : wv s.mem B (e+8*(i+1)) (rest.length+1)=
      (word s.mem B (e+8*(i+1))).toNat+2^64*wv s.mem B (e+8*(i+2)) rest.length := by
    rw [Nat.add_comm rest.length 1,wv_add]
    simp only [wv,Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.pow_zero,Nat.one_mul]
    rw [show e+8*(i+1)+8=e+8*(i+2) by omega_arith]
  have total := row_arith eqF eqT
  rw [← split,vb',← colT] at total
  have vt : value t (col::next::rest)=(t.gpr col).toNat+2^64*value t (next::rest) := rfl
  have eqV : value t (col::next::rest)+(2^64*2^(64*(rest.length+1)))*(c'.toNat+o'.toNat)=
      value s (col::next::rest).dropLast+(word s.mem B (e+8*i)).toNat*wv s.mem B (e+8*(i+1)) (rest.length+1) := by
    rw [vt]; exact total
  have vl : value s (col::next::rest).dropLast<2^(64*(rest.length+1)) := by
    have h := value_lt s (col::next::rest).dropLast
    rwa [List.length_dropLast,show (col::next::rest).length-1=rest.length+1 by simp] at h
  have bound : value s (col::next::rest).dropLast+
      (word s.mem B (e+8*i)).toNat*wv s.mem B (e+8*(i+1)) (rest.length+1)<2^64*2^(64*(rest.length+1)) :=
    mac_bound (word s.mem B (e+8*i)).isLt (wv_lt s.mem B (e+8*(i+1)) (rest.length+1)) vl
  rw [l2]
  refine ⟨no_carry eqV bound,(kab.trans (kc.trans kt)).mono ?_⟩
  intro r hr
  have zm' := zm
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr zm' ⊢
  grind

end VG.Proof.Bignum.X86_64.AdxTri8

end

end

end

/-! ## AdxTri8Store -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem headBases_ok {s : State} {B : Addr} {Z w I : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) :
    WP isa (.block AdxTri8.headBases) s fun t =>
      t.gpr .rcx=off B (slot w aAcc+16*I) ∧ t.mem=s.mem ∧ Keep [.rsi,.rcx] s t := by
  have ld : ∀ k<32, InRegions (s.rd++s.wr) (off B (8*k)) 8 := fun k hk =>
    hs.ld (by have := hdr_lt_slot w 8 hk; omega_using [hZ, this])
  have sh : BitVec.ofNat 64 I <<< (4 : Nat)=BitVec.ofNat 64 (16*I) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 I*BitVec.ofNat 64 16=BitVec.ofNat 64 (16*I)
    rw [← BitVec.ofNat_mul,Nat.mul_comm]
  have add : BitVec.ofNat 64 (16*I)+off B (slot w aAcc)=off B (slot w aAcc+16*I) := by
    rw [BitVec.add_comm]; exact off_off ..
  refine WP.mono (WP.keep [.rsi,.rcx] (Q := fun t => t.gpr .rcx=off B (slot w aAcc+16*I) ∧ t.mem=s.mem) ?_ rfl)
    fun t ⟨⟨p,m⟩,k⟩ => ⟨p,m,k⟩
  unfold AdxTri8.headBases
  xrun [State.ea,hdr,hd,hdrOff,ld (sArr aAcc) (by decide),ld (sFn 12) (by decide),
    hh.harr aAcc (by decide),hI,sh,add]

theorem storeHead_ok {s : State} {B : Addr} {Z w I i : Nat} {lo hi : Reg}
    (hs : Scr s B Z) (hc : s.gpr .rcx=off B (slot w aAcc+16*I))
    (he : slot w aAcc+16*I+(16+8*(2*i+2))+8≤Z) :
    let e := slot w aAcc+16*I+(16+8*(2*i+1))
    WP isa (AdxTri8.storeHead i lo hi) s fun t =>
      wv t.mem B e 2=(s.gpr lo).toNat+2^64*(s.gpr hi).toNat ∧
      Outside B e 16 s.mem t.mem ∧ Keep [] s t := by
  dsimp only
  have nowrap := hs.nowrap
  unfold AdxTri8.storeHead
  refine WP.seq (WP.mono (AdxRotate8.storeAt_ok (p := .rcx) (r := lo) hs hc
    (by omega_using [he] : slot w aAcc+16*I+(16+8*(2*i+1))+8≤Z)) fun b ⟨vb,ob,kb⟩ => ?_)
  refine WP.mono (AdxRotate8.storeAt_ok (p := .rcx) (r := hi) (hs.congr kb.2.2)
    ((kb.gpr (by simp)).trans hc) he) fun t ⟨vt,ot,kt⟩ => ?_
  have low : word t.mem B (slot w aAcc+16*I+(16+8*(2*i+1)))=s.gpr lo := by
    rw [ot.word (by omega_using []) (by omega_using [he, nowrap]),vb]
  have high : word t.mem B (slot w aAcc+16*I+(16+8*(2*i+2)))=s.gpr hi :=
    vt.trans (kb.gpr (by simp))
  refine ⟨?_,(ob.mono (n' := 16) (by omega_using []) (by omega_using [])).trans (ot.mono (by omega_using []) (by omega_using [])),(kb.trans kt).mono (by simp)⟩
  rw [wv,wv,wv]
  simp only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.one_mul,Nat.zero_add,Nat.add_zero]
  rw [low,show slot w aAcc+16*I+(16+8*(2*i+1))+8=slot w aAcc+16*I+(16+8*(2*i+2)) by omega_using [],high]

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Row -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

private theorem split_arith {A B R T V : Nat} (h : A+R*(B+R*T)=V) :
    (A+R*B)+(R*R)*T=V := by grind

theorem rowStep_ok {s : State} {B : Addr} {Z w I i e : Nat}
    {lo hi : Reg} {tail : List Reg}
    (hs : Scr s B Z) (hc : s.gpr .rcx=off B (slot w aAcc+16*I)) (hp : s.gpr .rbp=off B e)
    (he : e+8*(i+(lo::hi::tail).length)≤Z)
    (hout : slot w aAcc+16*I+(16+8*(2*i+2))+8≤Z)
    (hr : (lo::hi::tail).Nodup)
    (hrs : ∀ r ∈ lo::hi::tail, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx ∧ r≠.rdi) :
    let out := slot w aAcc+16*I+(16+8*(2*i+1))
    WP isa (AdxTri8.rowStep i lo hi tail) s fun t =>
      wv t.mem B out 2+2^128*value t tail=
        value s (lo::hi::tail).dropLast+(word s.mem B (e+8*i)).toNat*wv s.mem B (e+8*(i+1)) ((lo::hi::tail).length-1) ∧
      Outside B out 16 s.mem t.mem ∧ Keep (([.rdx,.rax,.rbx,.rsi] : List Reg)++lo::hi::tail) s t := by
  dsimp only
  unfold AdxTri8.rowStep
  have baseSafe : ∀ r ∈ lo::hi::tail, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx :=
    fun r h => let q := hrs r h; ⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1⟩
  refine WP.seq (WP.mono (rowCore_ok lo (hi::tail) hs hp he (by simp) hr baseSafe)
    fun a ⟨va,ka⟩ => ?_)
  have sl := hrs lo (by simp)
  have sh := hrs hi (by simp)
  have ca : a.gpr .rcx=off B (slot w aAcc+16*I) := (ka.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨sl.2.2.2.1.symm,sh.2.2.2.1.symm,
      fun h => (hrs .rcx (by simp [h])).2.2.2.1 rfl⟩⟩)).trans hc
  refine WP.mono (storeHead_ok (hs.congr ka.2.2.2) ca hout) fun t ⟨vb,ob,kb⟩ => ?_
  have tailT : value t tail=value a tail := value_congr fun r h => kb.gpr (by simp)
  rw [ka.2.1] at ob
  refine ⟨?_,ob,(ka.keep.trans kb).mono (by simp)⟩
  rw [vb,tailT]
  simp only [value] at va
  have mul : (2 : Nat)^128=2^64*2^64 := by rw [← Nat.pow_add]
  rw [mul,show (lo::hi::tail).length-1=(hi::tail).length by simp]
  exact split_arith va

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Rotate -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

/-- All triangular accumulators stay in registers untouched by addressing. -/
def Regs (rs : List Reg) : Prop := rs.Nodup ∧
  ∀ r ∈ rs, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx ∧ r≠.rdi

theorem rotate_regs {lo hi : Reg} {tail : List Reg} (h : Regs (lo::hi::tail)) : Regs (tail++[lo]) := by
  refine ⟨?_,?_⟩
  · rw [List.nodup_append]
    refine ⟨h.1.tail.tail,by simp,?_⟩
    intro r hr q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    subst q
    intro eq
    subst r
    exact (List.nodup_cons.mp h.1).1 (by simp [hr])
  · intro r hr
    apply h.2 r
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    rcases hr with hr | rfl
    · exact Or.inr (Or.inr hr)
    · exact Or.inl rfl

theorem rotate_subset {lo hi : Reg} {tail : List Reg} :
    ∀ r ∈ tail++[lo], r∈lo::hi::tail := by
  intro r hr
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
  rcases hr with hr | rfl
  · exact Or.inr (Or.inr hr)
  · exact Or.inl rfl

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Sum -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

def rowSum (m : Mem) (B : Addr) (e : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | i, n+1 => (word m B (e+8*i)).toNat*wv m B (e+8*(i+1)) (n+1)+2^128*rowSum m B e (i+1) n

theorem rowSum_congr {m m' : Mem} {B : Addr} {e i n : Nat}
    (h : ∀ j≤n, word m' B (e+8*(i+j))=word m B (e+8*(i+j))) : rowSum m' B e i n=rowSum m B e i n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have w : wv m' B (e+8*(i+1)) (n+1)=wv m B (e+8*(i+1)) (n+1) := by
      apply wv_congr
      intro k hk
      rw [show e+8*(i+1)+8*k=e+8*(i+(k+1)) by omega_using []]
      exact h (k+1) (by omega_using [hk])
    have h0 := h 0 (by omega_using [])
    simp only [Nat.add_zero] at h0
    rw [rowSum,rowSum,h0,w,ih (by
      intro j hj
      rw [show (i+1)+j=i+(j+1) by omega_using []]
      exact h (j+1) (by omega_using [hj]))]

end VG.Proof.Bignum.X86_64.AdxTri8

end

end

end

/-! # The triangular block's first row, which writes its columns

`AdxTri8.row0Core` writes each low product straight into its column and adds
the high word before it in one carry chain, the last column taking the last
high word and the carry: the columns' old values do not matter, so nothing
clears them first. The pending high word plus the carry never exceeds
`2^64 - 1`, so the last column cannot overflow. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem word0_ok (s : State) {k : Nat} {hi prev col : Reg} {v : BitVec 64} {c : Bool}
    (hm : readSrc s (.mem (at_ .rbp (8*k))) = some v) (hc : s.cf = some c)
    (h1 : hi ≠ col) (h2 : prev ≠ hi) (h3 : prev ≠ col) :
    WP isa (.block (AdxTri8.word0 k hi prev col)) s fun t => ∃ c' : Bool,
      t.cf = some c' ∧
      (t.gpr col).toNat + 2^64*((t.gpr hi).toNat + c'.toNat) =
        (s.gpr .rdx).toNat*v.toNat + (s.gpr prev).toNat + c.toNat ∧
      Keeps [hi, col] s t := by
  rw [show AdxTri8.word0 k hi prev col =
    [.mulx hi col (.mem (at_ .rbp (8*k)))] ++ [.adcx col (.reg prev)] from rfl, WP.block_append_iff]
  refine WP.mono (mulx_ok s hm (fun _ h => nomatch h) h1) fun a ⟨ea, ca, _, ka⟩ => ?_
  refine WP.mono (adcx_ok a (src := .reg prev) rfl (fun _ h => nomatch h) (ca.trans hc))
    fun t ⟨ct, hct, _, et, kt⟩ => ?_
  have pa : a.gpr prev = s.gpr prev := ka.gpr (by simp [h2, h3])
  have hiT : t.gpr hi = a.gpr hi := kt.gpr (by simp [h1])
  rw [pa] at et
  refine ⟨ct, hct, ?_, (ka.trans kt).mono (by simp)⟩
  rw [hiT]
  omega_arith

theorem last0_ok (s : State) {col prev : Reg} {c : Bool} (hc : s.cf = some c) (hne : prev ≠ col)
    (hb : (s.gpr prev).toNat + c.toNat < 2^64) :
    WP isa (.block [.mov32 col (.imm 0), .adcx col (.reg prev)]) s fun t =>
      (t.gpr col).toNat = (s.gpr prev).toNat + c.toNat ∧ Keeps [col] s t := by
  rw [show ([.mov32 col (.imm 0), .adcx col (.reg prev)] : List Instr) =
    [.mov32 col (.imm 0)] ++ [.adcx col (.reg prev)] from rfl, WP.block_append_iff]
  refine WP.mono (movZero_ok s col) fun a ⟨za, ca, _, ka⟩ => ?_
  refine WP.mono (adcx_ok a (src := .reg prev) rfl (fun _ h => nomatch h) (ca.trans hc))
    fun t ⟨_, _, _, et, kt⟩ => ?_
  have pa : a.gpr prev = s.gpr prev := ka.gpr (by simp [hne])
  rw [za, pa] at et
  simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] at et
  exact ⟨by omega_arith, (ka.trans kt).mono (by simp)⟩

private theorem comb {L R H C X V P Ci W T : Nat}
    (hw : L + R*(H + C) = X*V + P + Ci) (ht : T = H + C + X*W) :
    L + R*T = P + Ci + X*(V + R*W) := by grind

private theorem comb2 {L R H X V W : Nat} (hw : L + R*H = X*V) : L + R*(H + X*W) = X*(V + R*W) := by
  grind

private theorem hi_bound {L R H C X V P Ci : Nat} (hR : R = 2^64) (hX : X < R) (hV : V < R)
    (hP : P + Ci < R) (hw : L + R*(H + C) = X*V + P + Ci) : H + C < R := by
  subst hR
  have m : X*V ≤ (2^64-1)*(2^64-1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have : 2^64*(H + C) ≤ 2^64*(2^64-1) := by omega_arith
  exact Nat.lt_of_le_of_lt (Nat.le_of_mul_le_mul_left this (by decide)) (by decide)

theorem chain0_ok (rs : List Reg) {s : State} {B : Addr} {Z e k : Nat}
    {hi other prev : Reg} {c : Bool}
    (hs : Scr s B Z) (hp : s.gpr .rbp = off B e)
    (hZ : e + 8*(k + (rs.length - 1)) ≤ Z) (hn : rs ≠ []) (hd : rs.Nodup)
    (hh : hi ≠ other) (hph : prev ≠ hi)
    (hx : hi ≠ .rdx ∧ hi ≠ .rbp ∧ other ≠ .rdx ∧ other ≠ .rbp)
    (hrs : ∀ r ∈ rs, r ≠ hi ∧ r ≠ other ∧ r ≠ prev ∧ r ≠ .rdx ∧ r ≠ .rbp)
    (hc : s.cf = some c) (hb : (s.gpr prev).toNat + c.toNat < 2^64) :
    WP isa (.block (AdxTri8.chain0 k hi other prev rs)) s fun t =>
      value t rs = (s.gpr prev).toNat + c.toNat +
        (s.gpr .rdx).toNat*wv s.mem B (e + 8*k) (rs.length - 1) ∧
      Keeps ([hi, other] ++ rs) s t := by
  induction rs generalizing s k hi other prev c with
  | nil => exact absurd rfl hn
  | cons col rest ih =>
    cases rest with
    | nil =>
      change WP isa (.block [.mov32 col (.imm 0), .adcx col (.reg prev)]) s _
      have hcol := hrs col (by simp)
      refine WP.mono (last0_ok s hc (Ne.symm hcol.2.2.1) hb) fun t ⟨et, kt⟩ => ?_
      refine ⟨?_, kt.mono (by simp)⟩
      simp only [value, et, List.length_cons, List.length_nil, Nat.sub_self, wv, Nat.mul_zero,
        Nat.add_zero]
    | cons next rest =>
      change WP isa (.block (AdxTri8.word0 k hi prev col ++
        AdxTri8.chain0 (k+1) other hi hi (next::rest))) s _
      rw [WP.block_append_iff]
      have hcol := hrs col (by simp)
      have hm := readSrc_word hs (AdxRotate8.ea_at hp (8*k))
        (show e + 8*k + 8 ≤ Z by simp only [List.length_cons] at hZ; omega_arith)
      refine WP.mono (word0_ok s hm hc (Ne.symm hcol.1) hph (Ne.symm hcol.2.2.1))
        fun a ⟨ca, hca, ea, ka⟩ => ?_
      have hda := List.nodup_cons.mp hd
      have rdxA : a.gpr .rdx = s.gpr .rdx := ka.gpr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm hx.1, Ne.symm hcol.2.2.2.1⟩)
      have rbpA : a.gpr .rbp = s.gpr .rbp := ka.gpr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm hx.2.1, Ne.symm hcol.2.2.2.2⟩)
      have bnd : (a.gpr hi).toNat + ca.toNat < 2^64 :=
        hi_bound rfl (s.gpr .rdx).isLt (word s.mem B (e + 8*k)).isLt hb ea
      refine WP.mono (ih (s := a) (k := k+1) (hi := other) (other := hi) (prev := hi) (c := ca)
        (hs.congr ka.2.2.2) (rbpA.trans hp)
        (by simp only [List.length_cons] at hZ ⊢; omega_arith) (by simp) hda.2 (Ne.symm hh) hh ⟨hx.2.2.1, hx.2.2.2, hx.1, hx.2.1⟩
        (fun r hr => let q := hrs r (List.mem_cons_of_mem _ hr); ⟨q.2.1, q.1, q.1, q.2.2.2.1, q.2.2.2.2⟩)
        hca bnd) fun t ⟨et, kt⟩ => ?_
      have colT : t.gpr col = a.gpr col := kt.gpr (by
        simp only [List.cons_append, List.nil_append, List.mem_cons, not_or]
        exact ⟨hcol.2.1, hcol.1, fun h => hda.1 (h ▸ by simp), fun h => hda.1 (by simp [h])⟩)
      rw [ka.2.1, rdxA] at et
      refine ⟨?_, (ka.trans kt).mono (by intro r hr; simp only [List.cons_append,
        List.nil_append, List.mem_cons] at hr ⊢; grind)⟩
      simp only [value, colT, List.length_cons, Nat.add_sub_cancel] at et ⊢
      have wsplit : wv s.mem B (e + 8*k) (rest.length + 1) =
          (word s.mem B (e + 8*k)).toNat + 2^64*wv s.mem B (e + 8*(k+1)) rest.length := by
        rw [show rest.length + 1 = 1 + rest.length by omega_arith, wv_add]
        simp only [wv, Nat.pow_zero, Nat.mul_zero, Nat.zero_add, Nat.one_mul, Nat.add_zero, Nat.mul_one]
        rw [show e + 8*k + 8 = e + 8*(k+1) by omega_arith]
      rw [wsplit]
      exact comb ea et

theorem row0Core_ok (rs : List Reg) {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rbp = off B e)
    (hZ : e + 8*rs.length ≤ Z) (hlen : 2 ≤ rs.length) (hd : rs.Nodup)
    (hrs : ∀ r ∈ rs, Safe r ∧ r ≠ .rax ∧ r ≠ .rbx ∧ r ≠ .rcx) :
    WP isa (.block (AdxTri8.row0Core rs)) s fun t =>
      value t rs = (word s.mem B (e + 8*0)).toNat*wv s.mem B (e + 8*(0+1)) (rs.length - 1) ∧
      Keeps (([.rdx,.rax,.rbx,.rsi] : List Reg)++rs) s t := by
  cases rs with
  | nil => simp at hlen
  | cons col rest =>
    simp only [List.length_cons] at hZ hlen
    have hcol := hrs col (by simp)
    change WP isa (.block (([.mov .rdx (.mem (at_ .rbp 0))] : List Instr) ++
      ((([.alu32 .xor .rax (.reg .rax)] : List Instr) ++ [.mulx .rbx col (.mem (at_ .rbp 8))]) ++
        AdxTri8.chain0 2 .rax .rbx .rbx rest))) s _
    rw [WP.block_append_iff]
    have h0 := readSrc_word hs (AdxRotate8.ea_at hp (8*0)) (show e + 8*0 + 8 ≤ Z by omega_arith)
    refine WP.mono (movMem_ok s h0) fun a ⟨pa, _, _, ka⟩ => ?_
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (xorRax_ok a) fun b ⟨zb, cb, _, kb⟩ => ?_
    have kab := ka.trans kb
    have rbpB : b.gpr .rbp = off B e := (kab.gpr (by decide)).trans hp
    have h1 := readSrc_word (hs.congr kab.2.2.2) (AdxRotate8.ea_at rbpB 8)
      (show e + 8 + 8 ≤ Z by omega_arith)
    rw [kab.2.1] at h1
    refine WP.mono (mulx_ok b h1 (fun _ h => nomatch h) (Ne.symm hcol.2.2.1))
      fun c' ⟨ec, cc, _, kc⟩ => ?_
    have rdxC : c'.gpr .rdx = word s.mem B (e + 8*0) := by
      rw [kc.gpr (by simp [Ne.symm hcol.1.2.2.1]), kb.gpr (by decide), pa]
    have rbpC : c'.gpr .rbp = off B e := (kc.gpr (by simp [Ne.symm hcol.1.2.1])).trans rbpB
    have hda := List.nodup_cons.mp hd
    have hrest : rest ≠ [] := by
      intro h; subst h; simp at hlen
    refine WP.mono (chain0_ok rest (k := 2) (hi := .rax) (other := .rbx) (prev := .rbx) (c := false)
      (hs.congr (kab.trans kc).2.2.2) rbpC
      (by omega_arith) hrest hda.2 (by decide) (by decide)
      ⟨by decide, by decide, by decide, by decide⟩
      (fun r hr => let q := hrs r (List.mem_cons_of_mem _ hr); ⟨q.2.1, q.2.2.1, q.2.2.1, q.1.2.2.1, q.1.2.1⟩)
      (cc.trans cb) (by simp only [Bool.toNat_false, Nat.add_zero]; exact (c'.gpr .rbx).isLt))
      fun t ⟨et, kt⟩ => ?_
    have colT : t.gpr col = c'.gpr col := kt.gpr (by
      simp only [List.cons_append, List.nil_append, List.mem_cons, not_or]
      exact ⟨hcol.2.1, hcol.2.2.1, hda.1⟩)
    have rdxB : b.gpr .rdx = word s.mem B (e + 8*0) := by rw [kb.gpr (by decide), pa]
    rw [rdxB] at ec
    rw [(kab.trans kc).2.1, rdxC] at et
    have sub : ∀ r ∈ (([.rdx] : List Reg) ++ [.rax]) ++ ([.rbx, col] ++ ([.rax, .rbx] ++ rest)),
        r ∈ ([.rdx,.rax,.rbx,.rsi] : List Reg) ++ col :: rest := by
      intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hr ⊢
      grind
    refine ⟨?_, ((kab.trans kc).trans kt).mono sub⟩
    have wsplit : wv s.mem B (e + 8*(0+1)) rest.length =
        (word s.mem B (e + 8)).toNat + 2^64*wv s.mem B (e + 8*2) (rest.length - 1) := by
      obtain ⟨n, hn⟩ : ∃ n, rest.length = n + 1 := ⟨rest.length - 1, by omega_arith⟩
      rw [hn, Nat.add_sub_cancel, show n + 1 = 1 + n by omega_arith, wv_add]
      simp only [wv, Nat.pow_zero, Nat.mul_zero, Nat.zero_add, Nat.one_mul, Nat.add_zero, Nat.mul_one]
    show (t.gpr col).toNat + 2^64*value t rest = _
    rw [colT, et, List.length_cons, Nat.add_sub_cancel, wsplit]
    simp only [Bool.toNat_false, Nat.add_zero]
    exact comb2 (by simpa only [show e + 8 = e + 8 * 1 by omega_arith] using ec)

private theorem split_arith0 {A B R T V : Nat} (h : A+R*(B+R*T)=V) :
    (A+R*B)+(R*R)*T=V := by grind

theorem rowStep0_ok {s : State} {B : Addr} {Z w I e : Nat}
    {lo hi : Reg} {tail : List Reg}
    (hs : Scr s B Z) (hc : s.gpr .rcx=off B (slot w aAcc+16*I)) (hp : s.gpr .rbp=off B e)
    (he : e+8*(lo::hi::tail).length≤Z)
    (hout : slot w aAcc+16*I+(16+8*(2*0+2))+8≤Z)
    (hr : (lo::hi::tail).Nodup)
    (hrs : ∀ r ∈ lo::hi::tail, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx ∧ r≠.rdi) :
    let out := slot w aAcc+16*I+(16+8*(2*0+1))
    WP isa (AdxTri8.rowStep0 lo hi tail) s fun t =>
      wv t.mem B out 2+2^128*value t tail=
        (word s.mem B (e+8*0)).toNat*wv s.mem B (e+8*(0+1)) ((lo::hi::tail).length-1) ∧
      Outside B out 16 s.mem t.mem ∧ Keep (([.rdx,.rax,.rbx,.rsi] : List Reg)++lo::hi::tail) s t := by
  dsimp only
  unfold AdxTri8.rowStep0
  have baseSafe : ∀ r ∈ lo::hi::tail, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx :=
    fun r h => let q := hrs r h; ⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1⟩
  refine WP.seq (WP.mono (row0Core_ok (lo::hi::tail) hs hp he (by simp) hr baseSafe)
    fun a ⟨va,ka⟩ => ?_)
  have sl := hrs lo (by simp)
  have sh := hrs hi (by simp)
  have ca : a.gpr .rcx=off B (slot w aAcc+16*I) := (ka.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨sl.2.2.2.1.symm,sh.2.2.2.1.symm,
      fun h => (hrs .rcx (by simp [h])).2.2.2.1 rfl⟩⟩)).trans hc
  refine WP.mono (storeHead_ok (hs.congr ka.2.2.2) ca hout) fun t ⟨vb,ob,kb⟩ => ?_
  have tailT : value t tail=value a tail := value_congr fun r h => kb.gpr (by simp)
  rw [ka.2.1] at ob
  refine ⟨?_,ob,(ka.keep.trans kb).mono (by simp)⟩
  rw [vb,tailT]
  simp only [value] at va
  have mul : (2 : Nat)^128=2^64*2^64 := by rw [← Nat.pow_add]
  rw [mul]
  exact split_arith0 va

end VG.Proof.Bignum.X86_64.AdxTri8

end

end

/-! ### `Bignum.X86_64.AdxTri8Math`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum

theorem rowSum_words (m : Mem) (B : Addr) (e i n : Nat) :
    rowSum m B e i n=Triangular.rows (2^64) (fun j => (word m B (e+8*(i+j))).toNat) n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have shift : (fun j => (word m B (e+8*(i+(j+1)))).toNat)=
        (fun j => (word m B (e+8*(i+1)+8*j)).toNat) := by
      funext j
      rw [show e+8*(i+(j+1))=e+8*(i+1)+8*j by omega_using []]
    have shift' : (fun j => (word m B (e+8*(i+1)+8*j)).toNat)=
        (fun j => (word m B (e+8*((i+1)+j))).toNat) := by
      funext j
      rw [show e+8*(i+1)+8*j=e+8*((i+1)+j) by omega_using []]
    rw [rowSum,Triangular.rows]
    simp only [Nat.add_zero]
    rw [shift,AdxSquare.value_words,shift',← ih,← Nat.pow_add]

theorem rowSum_cross (m : Mem) (B : Addr) (e n : Nat) :
    2^64*rowSum m B e 0 n=AdxSquare.crossValue m B e (n+1) := by
  rw [rowSum_words,Triangular.rows_cross]
  simp only [Nat.zero_add,AdxSquare.crossValue]

end VG.Proof.Bignum.X86_64.AdxTri8

end

end

/-! ## AdxTri8Rows -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def output (w I i : Nat) := slot w aAcc+16*I+(16+8*(2*i+1))

private theorem compose_arith {P R T V A S W : Nat}
    (h : P+R*T=V+A) (e : W=T+S) : P+R*W=V+(A+R*S) := by grind

/-- The rows from `i`, over the columns `rs` whose top one each row zeroes:
the value of the others, plus the rows' products. -/
theorem rows_ok (n : Nat) {s : State} {B : Addr} {Z w I i e : Nat} {rs : List Reg}
    (hs : Scr s B Z) (hc : s.gpr .rcx=off B (slot w aAcc+16*I)) (hp : s.gpr .rbp=off B e)
    (he : e+8*(i+n+1)≤Z) (hout : output w I i+16*n≤Z)
    (hsep : e+8*(i+n+1)≤output w I i ∨ output w I i+16*n≤e)
    (hr : Regs rs) (hlen : rs.length=n+1) :
    WP isa (AdxTri8.rows n i rs) s fun t =>
      wv t.mem B (output w I i) (2*n)=value s rs.dropLast+rowSum s.mem B e i n ∧
      Outside B (output w I i) (16*n) s.mem t.mem ∧
      Keep (([.rdx,.rax,.rbx,.rsi] : List Reg)++rs) s t := by
  have nowrap := hs.nowrap
  induction n generalizing s i rs with
  | zero =>
    change WP isa (.block []) s _
    apply WP.block_nil
    obtain vz : rs.dropLast=[] := by
      rw [List.dropLast_eq_take,hlen]; rfl
    exact ⟨by simp only [wv,rowSum,vz,value,Nat.zero_add],Outside.refl _ _ _ _,Keep.refl _ _⟩
  | succ n ih =>
    cases rs with
    | nil => simp only [List.length_nil] at hlen; omega_using [hlen]
    | cons lo rs =>
      cases rs with
      | nil => simp only [List.length_cons,List.length_nil] at hlen; omega_using [hlen]
      | cons hi tail =>
        obtain tl : tail.length=n := by simp only [List.length_cons] at hlen; omega_using [hlen]
        change WP isa (.seq (AdxTri8.rowStep i lo hi tail) (AdxTri8.rows n (i+1) (tail++[lo]))) s _
        refine WP.seq (WP.mono (rowStep_ok hs hc hp (by rw [hlen]; omega_using [he])
          (by unfold output at hout; omega_using [hout]) hr.1 hr.2)
          fun a ⟨va,oa,ka⟩ => ?_)
        change Outside B (output w I i) 16 s.mem a.mem at oa
        obtain sa := hs.congr ka.2.2
        obtain ca : a.gpr .rcx=off B (slot w aAcc+16*I) := (ka.gpr (by
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨by decide,⟨(hr.2 lo (by simp)).2.2.2.1.symm,(hr.2 hi (by simp)).2.2.2.1.symm,
            fun h => (hr.2 .rcx (by simp [h])).2.2.2.1 rfl⟩⟩)).trans hc
        obtain pa : a.gpr .rbp=off B e := (ka.gpr (by
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨by decide,⟨(hr.2 lo (by simp)).1.2.1.symm,(hr.2 hi (by simp)).1.2.1.symm,
            fun h => (hr.2 .rbp (by simp [h])).1.2.1 rfl⟩⟩)).trans hp
        obtain outNext : output w I (i+1)=output w I i+16 := by unfold output; omega_using []
        refine WP.mono (ih (i := i+1) sa ca pa (by omega_using [he])
          (by rw [outNext]; omega_using [hout]) (by rw [outNext]; omega_using [hsep]) (rotate_regs hr)
          (by simp only [List.length_append,List.length_cons,List.length_nil,tl]))
          fun t ⟨vt,ot,kt⟩ => ?_
        rw [List.dropLast_concat] at vt
        obtain input : rowSum a.mem B e (i+1) n=rowSum s.mem B e (i+1) n :=
          rowSum_congr fun j hj => oa.word (by omega_using [hsep, hj]) (by omega_using [nowrap, he, hj])
        rw [input] at vt
        obtain pre : wv t.mem B (output w I i) 2=wv a.mem B (output w I i) 2 :=
          ot.wv (by rw [outNext]; omega_using []) (by omega_using [nowrap, hout])
        obtain frames : Outside B (output w I i) (16*(n+1)) s.mem t.mem :=
          (oa.mono (by omega_using []) (by omega_using [])).trans (ot.mono (by rw [outNext]; omega_using []) (by rw [outNext]; omega_using []))
        refine ⟨?_,frames,(ka.trans kt).mono ?_⟩
        · rw [show 2*(n+1)=2+2*n by omega_using [],wv_add,pre,
            show output w I i+8*2=output w I (i+1) by rw [outNext],rowSum]
          change wv a.mem B (output w I i) 2+2^128*wv t.mem B (output w I (i+1)) (2*n)=_
          simp only [hlen,Nat.add_sub_cancel] at va
          exact compose_arith va vt
        · intro r hm
          simp only [List.mem_append] at hm ⊢
          rcases hm with old | new
          · exact old
          · rcases new with base | rot
            · exact Or.inl base
            · exact Or.inr (rotate_subset r (List.mem_append.mpr rot))

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Clear -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem columns_regs : Regs AdxTri8.columns := by
  unfold Regs Safe AdxTri8.columns
  decide

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Block -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem setup_ok {s : State} {B : Addr} {Z w a I : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) :
    WP isa (.block (AdxTri8.setup ca)) s fun t =>
      t.gpr .rbp=off B (slot w a+8*I) ∧ t.mem=s.mem ∧ Keep [.rax,.rbp] s t := by
  obtain ld : ∀ k<32, InRegions (s.rd++s.wr) (off B (8*k)) 8 := fun k hk =>
    hs.ld (by have := hdr_lt_slot w 8 hk; omega_using [hZ, this])
  obtain add : off B (slot w a)+BitVec.ofNat 64 (8*I)=off B (slot w a+8*I) := off_off ..
  refine WP.mono (WP.keep [.rax,.rbp] (Q := fun t => t.gpr .rbp=off B (slot w a+8*I) ∧ t.mem=s.mem) ?_ rfl)
    fun t ⟨⟨p,m⟩,k⟩ => ⟨p,m,k⟩
  unfold AdxTri8.setup
  xrun [State.ea,hdr,hd,hdrOff,ld (sArr ca) (by have := hv.lt pa; unfold sArr; omega_using [this]),ld (sFn 12) (by decide),
    show word s.mem B (8*sArr ca) = _ from hv.at pa,hI,AdxRect8.shift3,add]

theorem zero_ends {m : Mem} {B : Addr} {e n : Nat}
    (lo : word m B e=0) (hi : word m B (e+8*(n+1))=0) :
    wv m B e (n+2)=2^64*wv m B (e+8) n := by
  rw [show n+2=1+(n+1) by omega_using [],wv_add,wv_add]
  simp only [wv,lo,Nat.mul_zero,Nat.mul_one,Nat.add_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add]
  rw [show e+8+8*n=e+8*(n+1) by omega_using [],hi]
  simp only [show (0 : BitVec 64).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero,Nat.zero_add]

/-- `clearEnds`: the first and last of the block's sixteen output words are
zeroed. -/
theorem clearEnds_ok {s : State} {B : Addr} {Z w I : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) (he : slot w aAcc+16*I+144≤Z) :
    let e := slot w aAcc+16+16*I
    WP isa AdxTri8.clearEnds s fun t =>
      word t.mem B e=0 ∧ word t.mem B (e+120)=0 ∧
      (∀ d, 8≤d → d+8≤120 → word t.mem B (e+d)=word s.mem B (e+d)) ∧
      Outside B e 128 s.mem t.mem ∧ t.gpr .rcx=off B (slot w aAcc+16*I) ∧ Keep [.rsi,.rcx,.rax] s t := by
  dsimp only
  have nowrap := hs.nowrap
  unfold AdxTri8.clearEnds
  refine WP.seq (WP.mono (headBases_ok hs hd hh hZ hI) fun a₀ ⟨pa₀,ma₀,ka₀⟩ => ?_)
  rw [show ([Instr.mov32 .rax (.imm 0),.store (AdxRotate8.at_ .rcx 16) .rax] : List Instr)=
    [.mov32 .rax (.imm 0)]++[.store (AdxRotate8.at_ .rcx 16) .rax] from rfl]
  refine WP.seq (WP.block_append (WP.mono (movZero_ok a₀ .rax) fun a ⟨za,_,_,kz⟩ => ?_))
  obtain ka : Keep [.rsi,.rcx,.rax] s a := (ka₀.trans kz.keep).mono (by simp)
  obtain ma : a.mem=s.mem := kz.2.1.trans ma₀
  obtain pa : a.gpr .rcx=off B (slot w aAcc+16*I) := (kz.gpr (by decide)).trans pa₀
  refine WP.mono (AdxRotate8.storeAt_ok (p := .rcx) (r := .rax) (hs.congr ka.2.2) pa
    (by omega_using [he] : slot w aAcc+16*I+16+8≤Z)) fun b ⟨vb,ob,kb⟩ => ?_
  refine WP.mono (AdxRotate8.storeAt_ok (p := .rcx) (r := .rax) (hs.congr (ka.trans kb).2.2)
    ((kb.gpr (by simp)).trans pa) (by omega_using [he] : slot w aAcc+16*I+136+8≤Z)) fun t ⟨vt,ot,kt⟩ => ?_
  have r8a : a.gpr .rax=0 := za
  obtain r8b : b.gpr .rax=0 := (kb.gpr (by simp)).trans r8a
  rw [ma] at ob
  refine ⟨?_,?_,?_,(ob.mono (by omega_using []) (by omega_using [])).trans (ot.mono (by omega_using []) (by omega_using [])),
    (kt.gpr (by simp)).trans ((kb.gpr (by simp)).trans pa),((ka.trans kb).trans kt).mono (by simp)⟩
  · rw [show slot w aAcc+16+16*I=slot w aAcc+16*I+16 by omega_using [],ot.word (by omega_using []) (by omega_using [he, nowrap]),vb,r8a]
  · rw [show slot w aAcc+16+16*I+120=slot w aAcc+16*I+136 by omega_using [],vt,r8b]
  · intro d h1 h2
    rw [ot.word (by omega_using [h2]) (by omega_using [he, nowrap, h2]),ob.word (by omega_using [h1]) (by omega_using [he, nowrap, h2])]

theorem block_ok {s : State} {B : Addr} {Z w a I : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hIndex : I+8≤w)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) :
    WP isa (AdxTri8.block ca) s fun t =>
      wv t.mem B (slot w aAcc+16+16*I) 16=AdxSquare.crossValue s.mem B (slot w a+8*I) 8 ∧
      Outside B (slot w aAcc+16+16*I) 128 s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  obtain ar := AdxRect8.tile_ranges hIndex hIndex ha ha1 ha2
  obtain outZ : output w I 0+112≤Z := by unfold output at *; omega_using [hZ, ar]
  obtain endZ : slot w aAcc+16*I+144≤Z := by omega_using [hZ, ar]
  unfold AdxTri8.block
  refine WP.seq (WP.mono (setup_ok hs hd hZ hv pa hI) fun u ⟨pu,mu,ku⟩ => ?_)
  refine WP.seq (WP.mono (clearEnds_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd) (mu ▸ hh) hZ
    (mu ▸ hI) endZ) fun x ⟨lx,hx,_,ox,cx,kx⟩ => ?_)
  rw [mu] at ox
  obtain kux := ku.trans kx
  obtain px : x.gpr .rbp=off B (slot w a+8*I) := (kx.gpr (by decide)).trans pu
  have regs := columns_regs
  refine WP.seq (WP.mono (rowStep0_ok (lo := .r8) (hi := .r9) (tail := [.r10,.r11,.r12,.r13,.r14,.r15])
    (hs.congr kux.2.2) cx px (by simp only [List.length_cons,List.length_nil]; omega_using [hZ, ar])
    (by unfold output at outZ; omega_using [endZ]) regs.1 regs.2) fun y ⟨vy,oy,ky⟩ => ?_)
  change Outside B (output w I 0) 16 x.mem y.mem at oy
  obtain sy := hs.congr (kux.trans ky).2.2
  obtain cy : y.gpr .rcx=off B (slot w aAcc+16*I) := (ky.gpr (by decide)).trans cx
  obtain py : y.gpr .rbp=off B (slot w a+8*I) := (ky.gpr (by decide)).trans px
  have rot : AdxTri8.rotate AdxTri8.columns=[.r10,.r11,.r12,.r13,.r14,.r15]++[.r8] := rfl
  obtain outNext : output w I 1=output w I 0+16 := by unfold output; omega_using []
  refine WP.mono (rows_ok 6 (i := 1) sy cy py (by omega_using [hZ, ar])
    (by rw [outNext]; unfold output at outZ ⊢; omega_using [endZ]) (by unfold output; omega_using [ar])
    (by rw [rot]; exact rotate_regs regs) (by rw [rot]; rfl))
    fun t ⟨vt,ot,kt⟩ => ?_
  rw [rot,List.dropLast_concat] at vt
  obtain input : rowSum y.mem B (slot w a+8*I) 1 6=rowSum s.mem B (slot w a+8*I) 1 6 :=
    rowSum_congr fun j hj => by
      rw [oy.word (by unfold output; omega_using [ar, hj]) (by omega_using [hZ, nowrap, ar, hj]),ox.word (by omega_using [ar, hj]) (by omega_using [hZ, nowrap, ar, hj])]
  obtain e0 : word x.mem B (slot w a+8*I+8*0)=word s.mem B (slot w a+8*I+8*0) := ox.word (by omega_using [ar]) (by omega_using [hZ, nowrap, ar])
  obtain e1 : wv x.mem B (slot w a+8*I+8*(0+1)) 7=wv s.mem B (slot w a+8*I+8*(0+1)) 7 :=
    ox.wv (by omega_using [ar]) (by omega_using [hZ, nowrap, ar])
  obtain vy' : wv y.mem B (output w I 0) 2+2^128*value y [.r10,.r11,.r12,.r13,.r14,.r15]=
      (word s.mem B (slot w a+8*I+8*0)).toNat*wv s.mem B (slot w a+8*I+8*(0+1)) (6+1) := by
    rw [← e0, ← e1]; exact vy
  rw [input] at vt
  obtain pre : wv t.mem B (output w I 0) 2=wv y.mem B (output w I 0) 2 :=
    ot.wv (by rw [outNext]; omega_using []) (by omega_using [nowrap, outZ])
  obtain v14 : wv t.mem B (output w I 0) 14=rowSum s.mem B (slot w a+8*I) 0 7 := by
    rw [show 14=2+2*6 from rfl,wv_add,pre,show output w I 0+8*2=output w I 1 by rw [outNext],vt,
      show rowSum s.mem B (slot w a+8*I) 0 7=(word s.mem B (slot w a+8*I+8*0)).toNat*
        wv s.mem B (slot w a+8*I+8*(0+1)) (6+1)+2^128*rowSum s.mem B (slot w a+8*I) 1 6 from rfl,
      show 64*2=128 from rfl]
    omega_using [vy']
  obtain low : word t.mem B (slot w aAcc+16+16*I)=0 := by
    rw [ot.word (by unfold output; omega_using []) (by omega_using [nowrap, endZ]),oy.word (by unfold output; omega_using []) (by omega_using [nowrap, endZ]),lx]
  obtain high : word t.mem B (slot w aAcc+16+16*I+8*(14+1))=0 := by
    rw [ot.word (by unfold output; omega_using []) (by omega_using [nowrap, endZ]),oy.word (by unfold output; omega_using []) (by omega_using [nowrap, endZ]),hx]
  refine ⟨?_,ox.trans ((oy.mono (by unfold output; omega_using []) (by unfold output; omega_using [])).trans
    (ot.mono (by unfold output; omega_using []) (by unfold output; omega_using []))),
    ((kux.trans ky).trans kt).mono (by decide)⟩
  rw [show 16=14+2 from rfl,zero_ends low high,
    show slot w aAcc+16+16*I+8=output w I 0 by unfold output; omega_using [],v14]
  exact rowSum_cross s.mem B _ 7

end VG.Proof.Bignum.X86_64.AdxTri8

end

end

end

/-! ## AdxTri8FullBlock -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem fullBlock_ok {s : State} {B : Addr} {Z w a I : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hIndex : I+8≤w)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) :
    WP isa (AdxTri8.block ca) s fun t =>
      wv t.mem B (slot w aAcc+16+16*I) 16=AdxSquare.crossValue s.mem B (slot w a+8*I) 8 ∧
      Outside B (slot w aAcc+16+16*I) 128 s.mem t.mem ∧ Keep mmRegs s t :=
  block_ok hs hd hh hZ hv pa ha ha1 ha2 hIndex hI

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8BlocksFrame -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)

def diagonalRanges (w k : Nat) : List (Nat × Nat) := [(rawBase w,128*k),(8*sFn 12,8)]

def blockCross (m : Mem) (B : Addr) (e : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => blockCross m B e n+2^(1024*n)*AdxSquare.crossValue m B (e+64*n) 8

structure BlocksInv (s₀ : State) (B : Addr) (Z w a k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi=B
  indexI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 (8*k)
  keep : Keep mmRegs s₀ s
  frame : Frm B (diagonalRanges w k) s₀.mem s.mem
  val : wv s.mem B (rawBase w) (16*k)=blockCross s₀.mem B (slot w a) k

theorem diagonal_hdr {m m' : Mem} {B : Addr} {w k : Nat} {mi : BitVec 64}
    (hh : Hdr m B w mi) (hf : Frm B (diagonalRanges w k) m m') : Hdr m' B w mi := by
  have low (j : Nat) (hj : j<16) : word m' B (8*j)=word m B (8*j) := by
    apply hf.word_eq
    · intro r hr
      simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> simp only [rawBase,slot,hdrBytes,sFn] <;> omega_arith
    · omega_arith
  exact ⟨(low sW (by decide)).trans hh.hw,(low sMinv (by decide)).trans hh.hminv,
    fun j hj => (low (sArr j) (by unfold sArr; omega_arith)).trans (hh.harr j hj)⟩

theorem diagonal_ops {m m' : Mem} {B : Addr} {w k : Nat} {ps : List (Nat × Nat)}
    (hv : Ops m B w ps) (hf : Frm B (diagonalRanges w k) m m') : Ops m' B w ps :=
  hv.of_frm hf fun r hr => by
    simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;> simp only [rawBase,slot,hdrBytes,sFn] <;> omega_arith

theorem diagonal_input {m m' : Mem} {B : Addr} {w a k I : Nat}
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hk : 8*k≤w) (hi : I+8≤w)
    (hZ : slot w 8≤2^64) (hf : Frm B (diagonalRanges w k) m m') :
    AdxSquare.crossValue m' B (slot w a+8*I) 8=AdxSquare.crossValue m B (slot w a+8*I) 8 := by
  have ar := AdxRect8.tile_ranges hi hi ha ha1 ha2
  have s1 := slot_sep (w := w) ha1
  have s2 := slot_sep (w := w) ha2
  apply AdxSquare.crossValue_congr
  intro j hj
  apply hf.word_eq
  · intro r hr
    simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;>
      simp only [rawBase,slot,hdrBytes,sFn,aAcc,aTmp] at * <;> omega_arith
  · omega_arith

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8BlocksStep -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)

theorem blockStep_ok {s₀ s : State} {B : Addr} {Z w a k n : Nat} {mi : BitVec 64}
    {ps : List (Nat × Nat)} (hv : Ops s₀.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hZ : slot w 8≤Z) (hw : w<2^31) (hwN : w=8*n) (hk : k<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (h : BlocksInv s₀ B Z w a k mi s) :
    WP isa (.seq (AdxTri8.block ca) (.block AdxTri8.nextBlock)) s fun t =>
      t.zf=some (decide (k+1=n)) ∧ BlocksInv s₀ B Z w a (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8≤(2 : Nat)^64 := by omega_arith
  have ar := AdxRect8.tile_ranges (by omega_arith : 8*k+8≤w) (by omega_arith : 8*k+8≤w) ha ha1 ha2
  refine WP.seq (WP.mono (fullBlock_ok h.scr h.rdi h.hdr hZ (diagonal_ops hv h.frame) pa ha ha1 ha2 (by omega_arith) h.indexI)
    fun u ⟨vu,ou,ku⟩ => ?_)
  have indexU : word u.mem B (8*sFn 12)=BitVec.ofNat 64 (8*k) := by
    rw [ou.word (by unfold slot hdrBytes sFn; omega_arith) (by decide)]; exact h.indexI
  have headerU := h.hdr.of_outside ou (by unfold slot; omega_arith)
  refine WP.mono (AdxTiledProduct.nextRow_ok (h.scr.congr ku.2.2) ((ku.gpr (by decide)).trans h.rdi)
    headerU hZ (by omega_arith) (by omega_arith) indexU) fun t ⟨mt,zt,kt⟩ => ?_
  have ot : Outside B (8*sFn 12) 8 u.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by decide)
  have fu : Frm B (diagonalRanges w (k+1)) s.mem u.mem := by
    intro x hx
    apply ou x
    have := hx (rawBase w,128*(k+1)) (by simp [diagonalRanges])
    unfold rawBase at *; omega_arith
  have ft : Frm B (diagonalRanges w (k+1)) u.mem t.mem := Frm.of_outside ot (by simp [diagonalRanges])
  have old : Frm B (diagonalRanges w (k+1)) s₀.mem s.mem := by
    intro x hx
    apply h.frame x
    intro r hr
    simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · have := hx (rawBase w,128*(k+1)) (by simp [diagonalRanges]); simp only []; omega_arith
    · exact hx _ (by simp [diagonalRanges])
  have finalFrame := (old.trans fu).trans ft
  have low : wv u.mem B (rawBase w) (16*k)=wv s.mem B (rawBase w) (16*k) :=
    ou.wv (by unfold rawBase; omega_arith) (by unfold rawBase at *; omega_arith)
  have resultU : wv u.mem B (rawBase w+8*(16*k)) 16=
      AdxSquare.crossValue s₀.mem B (slot w a+64*k) 8 := by
    rw [show rawBase w+8*(16*k)=slot w aAcc+16+16*(8*k) by unfold rawBase; omega_arith,vu,
      diagonal_input ha ha1 ha2 (by omega_arith) (by omega_arith) Z64 h.frame,
      show slot w a+8*(8*k)=slot w a+64*k by omega_arith]
  refine ⟨?_,⟨h.scr.congr (ku.trans kt).2.2,diagonal_hdr h.hdr (fu.trans ft),
    ((ku.trans kt).gpr (by decide)).trans h.rdi,?_,(h.keep.trans (ku.trans kt)).mono (by decide),finalFrame,?_⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  · rw [mt,word_writeW_self,show 8*(k+1)=8*k+8 by omega_arith]
  · rw [ot.wv (by unfold rawBase slot hdrBytes sFn; omega_arith) (by unfold rawBase at *; omega_arith),
      show 16*(k+1)=16*k+16 by omega_arith,wv_add,low,h.val,resultU,blockCross]
    rw [show 64*(16*k)=1024*k by omega_arith]

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Blocks -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)

theorem blocks_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hw : w<2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) :
    WP isa (AdxTri8.blocks ca) s (BlocksInv s B Z w a n mi) := by
  have nowrap := hs.nowrap
  have iZ : 8*sFn 12+8≤Z := by
    have := hdr_lt_slot w 8 (show sFn 12<32 by decide); omega_arith
  have init : WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s fun t =>
      t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64) ∧ Keep [.rax] s t := by
    apply WP.keep [.rax] (Q := fun t => t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)) _ rfl
    xrun [State.ea,hdr,hd,hdrOff,hs.st iZ]; rfl
  unfold AdxTri8.blocks
  refine WP.seq (WP.mono init fun u ⟨mu,ku⟩ => ?_)
  have ou : Outside B (8*sFn 12) 8 s.mem u.mem := by rw [mu]; exact writeW_outside _ _ _ (by decide)
  have fu : Frm B (diagonalRanges w 0) s.mem u.mem := Frm.of_outside ou (by simp [diagonalRanges])
  have h0 : BlocksInv s B Z w a 0 mi u :=
    ⟨hs.congr ku.2.2,diagonal_hdr hh fu,(ku.gpr (by decide)).trans hd,by rw [mu,word_writeW_self]; rfl,
      ku.mono (by decide),fu,rfl⟩
  exact wp_upto (a := 0) (N := n) hn (BlocksInv s B Z w a · mi)
    (fun _ _ hk _ h => blockStep_ok hv pa hZ hw hwN hk ha ha1 ha2 h) (fun _ h => h) h0

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Chunks -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem crossValue_add (m : Mem) (B : Addr) (e p q : Nat) :
    AdxSquare.crossValue m B e (p+q)=AdxSquare.crossValue m B e p+
      2^(128*p)*AdxSquare.crossValue m B (e+8*p) q+
      2^(64*p)*wv m B e p*wv m B (e+8*p) q := by
  have shift : (fun i => (word m B (e+8*(p+i))).toNat)=
      (fun i => (word m B (e+8*p+8*i)).toNat) := by
    funext i
    rw [show e+8*(p+i)=e+8*p+8*i by omega_arith]
  unfold AdxSquare.crossValue
  rw [Triangular.cross_add,shift,AdxSquare.value_words,AdxSquare.value_words,
    ← Nat.pow_mul,← Nat.pow_mul,show 64*(2*p)=128*p by omega_arith]

def chunks (m : Mem) (B : Addr) (e : Nat) (j : Nat) := wv m B (e+64*j) 8

theorem chunks_value (m : Mem) (B : Addr) (e n : Nat) :
    Square.value (2^512) (chunks m B e) n=wv m B e (8*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Square.value,ih,show 8*(n+1)=8*n+8 by omega_arith,wv_add,← Nat.pow_mul 2 512 n]
    simp only [chunks,show 8*(8*n)=64*n by omega_arith,show 64*(8*n)=512*n by omega_arith]
    rw [Nat.mul_comm (wv m B (e+64*n) 8)]

private theorem sum_chunks {A C P D Q X Y : Nat} :
    (A+C)+P*D+Q*X*Y=(A+P*D)+(C+X*Y*Q) := by grind

theorem chunks_cross (m : Mem) (B : Addr) (e n : Nat) :
    AdxSquare.crossValue m B e (8*n)=blockCross m B e n+Square.cross (2^512) (chunks m B e) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 8*(n+1)=8*n+8 by omega_arith,crossValue_add,ih,blockCross,Square.cross,chunks_value,← Nat.pow_mul 2 512 n]
    simp only [chunks,show 8*(8*n)=64*n by omega_arith,show 128*(8*n)=1024*n by omega_arith,
      show 64*(8*n)=512*n by omega_arith]
    exact sum_chunks

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTiledSquareMath -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTri8 (chunks blockCross)

theorem chunks_tail_value (m : Mem) (B : Addr) (e k n : Nat) :
    Square.value (2^512) (fun j => chunks m B e (k+j)) n=wv m B (e+64*k) (8*n) := by
  have f : (fun j => chunks m B e (k+j))=chunks m B (e+64*k) := by
    funext j
    unfold chunks
    rw [show e+64*(k+j)=e+64*k+64*j by omega_arith]
  rw [f,AdxTri8.chunks_value]

def remaining (m : Mem) (B : Addr) (e n k : Nat) :=
  2^(1024*k)*Square.cross (2^512) (fun j => chunks m B e (k+j)) (n-k)

private theorem distribute {P R X V C : Nat} :
    P*(R*X*V+R*R*C)=(P*R)*X*V+(P*(R*R))*C := by grind

theorem remaining_step (m : Mem) (B : Addr) (e n k : Nat) (hk : k+1<n) :
    remaining m B e n k=2^(512*(2*k+1))*chunks m B e k*wv m B (e+64*(k+1)) (8*(n-k-1))+
      remaining m B e n (k+1) := by
  have shift : (fun j => chunks m B e (k+(j+1)))=(fun j => chunks m B e ((k+1)+j)) := by
    funext j
    rw [show k+(j+1)=(k+1)+j by omega_arith]
  have p1 : (2 : Nat)^(512*(2*k+1))=2^(1024*k)*2^512 := by
    rw [← Nat.pow_add 2 (1024*k) 512]
    apply congrArg (fun n : Nat => (2 : Nat)^n)
    omega_arith
  have p2 : (2 : Nat)^(1024*(k+1))=2^(1024*k)*(2^512*2^512) := by
    rw [← Nat.pow_add 2 512 512,← Nat.pow_add 2 (1024*k) (512+512)]
    apply congrArg (fun n : Nat => (2 : Nat)^n)
    omega_arith
  unfold remaining
  rw [show n-k=(n-k-1)+1 by omega_arith,Triangular.cross_head,shift,chunks_tail_value]
  simp only [Nat.add_zero]
  rw [show n-(k+1)=n-k-1 by omega_arith,p1,p2]
  generalize (2 : Nat)^(1024*k)=P, (2 : Nat)^512=R
  exact distribute

theorem remaining_end (m : Mem) (B : Addr) (e n : Nat) (hn : 0<n) : remaining m B e n (n-1)=0 := by
  unfold remaining
  rw [show n-(n-1)=1 by omega_arith]
  simp only [Square.cross,Square.value,Nat.zero_mul,Nat.add_zero,Nat.mul_zero]

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareRows -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges frame_hdr frame_ops input_preserved)
open VG.Proof.Bignum.X86_64.AdxTri8 (chunks)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- Before row `k`: the raw product, the carry the row before handed in
`sFn 15` (none after the last row), and the rows to come. -/
structure Inv (s₀ : State) (B : Addr) (Z w a n k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi=B
  indexI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 (8*k)
  hand : (word s.mem B AdxRect8.handOffset).toNat ≤ 2
  keep : Keep mmRegs s₀ s
  frame : Frm B (ranges w) s₀.mem s.mem
  val : ∃ c, wv s.mem B (rawBase w) (2*w) +
      2^(64*(8*k+w))*(if 8*k+8=w then 0 else (word s.mem B AdxRect8.handOffset).toNat) +
      2^(128*w)*c+remaining s₀.mem B (slot w a) n k=
    wv s₀.mem B (rawBase w) (2*w)+remaining s₀.mem B (slot w a) n 0

private theorem advance {W W' H H' R C D S S' T A : Nat}
    (prev : W+H+R*C+S=T) (step : W'+H'+R*D=W+H+A) (rest : S=A+S') : W'+H'+R*(C+D)+S'=T := by grind

theorem step_inv {s₀ s : State} {B : Addr} {Z w a n k : Nat} {mi : BitVec 64}
    {ps : List (Nat × Nat)} (hv : Ops s₀.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hZ : slot w 8≤Z) (hw : w<2^31) (hwN : w=8*n) (hk : k<n-1)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (h : Inv s₀ B Z w a n k mi s) :
    WP isa (AdxTiledSquare.row ca) s fun t => t.zf=some (decide (k+1=n-1)) ∧ Inv s₀ B Z w a n (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8≤(2 : Nat)^64 := by omega_arith
  refine WP.mono (row_ok h.scr h.rdi h.hdr (frame_ops hv h.frame) pa hZ hw (by omega_arith : w=8*k+8+8*(n-k-1))
    (by omega_arith) ha ha1 ha2 h.indexI rfl h.hand) fun t ⟨zt,it,σt,⟨d,eq⟩,ht,ft,kt⟩ => ?_
  rw [input_preserved ha ha1 ha2 (by omega_arith : 8*k+8≤w) Z64 h.frame,
    input_preserved ha ha1 ha2 (by omega_arith : (8*k+8)+8*(n-k-1)≤w) Z64 h.frame] at eq
  rw [show 64*(8*k+(8*k+8))=512*(2*k+1) by omega_arith,
    show slot w a+8*(8*k)=slot w a+64*k by omega_arith,
    show slot w a+8*(8*k+8)=slot w a+64*(k+1) by omega_arith] at eq
  obtain ⟨c,prev⟩ := h.val
  simp only [show (8*k+8=w) = False from eq_false (by omega_arith),ite_false] at prev
  refine ⟨?_,⟨h.scr.congr kt.2.2,ht,(kt.gpr (by decide)).trans h.rdi,?_,σt,
    (h.keep.trans kt).mono (by decide),h.frame.trans ft,c+d,?_⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  · simpa only [show 8*(k+1)=8*k+8 by omega_arith] using it
  · rw [show 8*(k+1)+8=8*k+16 by omega_arith,show 8*(k+1)+w=8*k+w+8 by omega_arith]
    exact advance prev eq (remaining_step s₀.mem B (slot w a) n k (by omega_arith))

theorem rows_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hw : w<2^31) (hwN : w=8*n) (hn : 1<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) :
    WP isa (AdxTiledSquare.rows ca) s fun t =>
      (∃ c, wv t.mem B (rawBase w) (2*w)+2^(128*w)*c=
        wv s.mem B (rawBase w) (2*w)+Square.cross (2^512) (chunks s.mem B (slot w a)) n) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have iZ : 8*sFn 12+8≤Z := by have := hdr_lt_slot w 8 (show sFn 12<32 by decide); omega_arith
  have hZ15 : 8*sFn 15+8≤Z := by have := hdr_lt_slot w 8 (show sFn 15<32 by decide); omega_arith
  have init : WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax,.store (hdr (sFn 15)) .rax]) s
      fun t => t.mem=(s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)).writeW (off B (8*sFn 15)) (0 : BitVec 64) ∧
        Keep [.rax] s t := by
    apply WP.keep [.rax] (Q := fun t => t.mem=(s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)).writeW
      (off B (8*sFn 15)) (0 : BitVec 64)) _ rfl
    xrun [State.ea,hdr,hd,hdrOff,hs.st iZ,hs.st hZ15]; rfl
  unfold AdxTiledSquare.rows
  refine WP.seq (WP.mono init fun u ⟨mu,ku⟩ => ?_)
  have o1 : Outside B (8*sFn 12) 8 s.mem (s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)) :=
    writeW_outside _ _ _ (by decide)
  have o2 : Outside B (8*sFn 15) 8 (s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)) u.mem := by
    rw [mu]; exact writeW_outside _ _ _ (by decide)
  have fu : Frm B (ranges w) s.mem u.mem := by
    intro x hx
    have := hx (8*sFn 12,32) (by simp [ranges])
    exact (o2 x (by simp only [sFn] at *; omega_arith)).trans (o1 x (by simp only [sFn] at *; omega_arith))
  have i0 : word u.mem B (8*sFn 12) = BitVec.ofNat 64 (8*0) := by
    rw [o2.word (by decide) (by decide),word_writeW_self]; rfl
  have h00 : word u.mem B AdxRect8.handOffset = 0 := by
    rw [mu]; exact word_writeW_self ..
  have h0 : Inv s B Z w a n 0 mi u :=
    ⟨hs.congr ku.2.2,frame_hdr hh fu,(ku.gpr (by decide)).trans hd,i0,by rw [h00]; decide,
      ku.mono (by decide),fu,0,by
        rw [h00,o2.wv (by unfold rawBase slot hdrBytes sFn; omega_arith) (by unfold rawBase slot aAcc at *; omega_arith),
          o1.wv (by unfold rawBase slot hdrBytes sFn; omega_arith) (by unfold rawBase slot aAcc at *; omega_arith)]
        simp⟩
  apply wp_upto (a := 0) (N := n-1) (by omega_arith) (Inv s B Z w a n · mi)
    (fun _ _ hk _ h => step_inv hv pa hZ hw hwN hk ha ha1 ha2 h) ?_ h0
  intro t h
  obtain ⟨c,eq⟩ := h.val
  simp only [show (8*(n-1)+8=w) = True from eq_true (by omega_arith),ite_true,Nat.mul_zero,Nat.add_zero] at eq
  rw [remaining_end s.mem B (slot w a) n (by omega_arith),Nat.add_zero] at eq
  simp only [remaining,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add,Nat.sub_zero] at eq
  exact ⟨⟨c,eq⟩,h.hdr,h.frame,h.keep⟩

/-- `Inv` for `rows1`, whose rows hand no carry on. -/
structure Inv1 (s₀ : State) (B : Addr) (Z w a n k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi=B
  indexI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 (8*k)
  keep : Keep mmRegs s₀ s
  frame : Frm B (ranges w) s₀.mem s.mem
  val : ∃ c, wv s.mem B (rawBase w) (2*w)+2^(128*w)*c+remaining s₀.mem B (slot w a) n k=
    wv s₀.mem B (rawBase w) (2*w)+remaining s₀.mem B (slot w a) n 0

private theorem advance1 {W W' R C D S S' T A : Nat}
    (prev : W+R*C+S=T) (step : W'+R*D=W+A) (rest : S=A+S') : W'+R*(C+D)+S'=T := by grind

theorem step1_inv {s₀ s : State} {B : Addr} {Z w a n k : Nat} {mi : BitVec 64}
    {ps : List (Nat × Nat)} (hv : Ops s₀.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hZ : slot w 8≤Z) (hw : w<2^31) (hwN : w=8*n) (hk : k<n-1)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (h : Inv1 s₀ B Z w a n k mi s) :
    WP isa (AdxTiledSquare.row1 ca) s fun t => t.zf=some (decide (k+1=n-1)) ∧ Inv1 s₀ B Z w a n (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8≤(2 : Nat)^64 := by omega_arith
  refine WP.mono (row1_ok h.scr h.rdi h.hdr (frame_ops hv h.frame) pa hZ hw (by omega_arith : w=8*k+8+8*(n-k-1))
    (by omega_arith) ha ha1 ha2 h.indexI) fun t ⟨zt,it,⟨d,eq⟩,ht,ft,kt⟩ => ?_
  rw [input_preserved ha ha1 ha2 (by omega_arith : 8*k+8≤w) Z64 h.frame,
    input_preserved ha ha1 ha2 (by omega_arith : (8*k+8)+8*(n-k-1)≤w) Z64 h.frame] at eq
  rw [show 64*(8*k+(8*k+8))=512*(2*k+1) by omega_arith,
    show slot w a+8*(8*k)=slot w a+64*k by omega_arith,
    show slot w a+8*(8*k+8)=slot w a+64*(k+1) by omega_arith] at eq
  obtain ⟨c,prev⟩ := h.val
  refine ⟨?_,⟨h.scr.congr kt.2.2,ht,(kt.gpr (by decide)).trans h.rdi,?_,
    (h.keep.trans kt).mono (by decide),h.frame.trans ft,c+d,?_⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  · simpa only [show 8*(k+1)=8*k+8 by omega_arith] using it
  · exact advance1 prev eq (remaining_step s₀.mem B (slot w a) n k (by omega_arith))

theorem rows1_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hw : w<2^31) (hwN : w=8*n) (hn : 1<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) :
    WP isa (AdxTiledSquare.rows1 ca) s fun t =>
      (∃ c, wv t.mem B (rawBase w) (2*w)+2^(128*w)*c=
        wv s.mem B (rawBase w) (2*w)+Square.cross (2^512) (chunks s.mem B (slot w a)) n) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have iZ : 8*sFn 12+8≤Z := by have := hdr_lt_slot w 8 (show sFn 12<32 by decide); omega_arith
  have init : WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s fun t =>
      t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64) ∧ Keep [.rax] s t := by
    apply WP.keep [.rax] (Q := fun t => t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)) _ rfl
    xrun [State.ea,hdr,hd,hdrOff,hs.st iZ]; rfl
  unfold AdxTiledSquare.rows1
  refine WP.seq (WP.mono init fun u ⟨mu,ku⟩ => ?_)
  have ou : Outside B (8*sFn 12) 8 s.mem u.mem := by rw [mu]; exact writeW_outside _ _ _ (by decide)
  have fu : Frm B (ranges w) s.mem u.mem := by
    intro x hx
    apply ou x
    have := hx (8*sFn 12,32) (by simp [ranges]); omega_arith
  have h0 : Inv1 s B Z w a n 0 mi u :=
    ⟨hs.congr ku.2.2,frame_hdr hh fu,(ku.gpr (by decide)).trans hd,by rw [mu,word_writeW_self]; rfl,
      ku.mono (by decide),fu,0,by
        rw [ou.wv (by unfold rawBase slot hdrBytes sFn; omega_arith) (by unfold rawBase slot aAcc at *; omega_arith),Nat.mul_zero,Nat.add_zero]⟩
  apply wp_upto (a := 0) (N := n-1) (by omega_arith) (Inv1 s B Z w a n · mi)
    (fun _ _ hk _ h => step1_inv hv pa hZ hw hwN hk ha ha1 ha2 h) ?_ h0
  intro t h
  obtain ⟨c,eq⟩ := h.val
  rw [remaining_end s.mem B (slot w a) n (by omega_arith),Nat.add_zero] at eq
  simp only [remaining,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add,Nat.sub_zero] at eq
  exact ⟨⟨c,eq⟩,h.hdr,h.frame,h.keep⟩

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareChoice -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges)
open VG.Proof.Bignum.X86_64.AdxTri8 (chunks)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

private theorem cross_one (r : Nat) (f : Nat → Nat) : Square.cross r f 1=0 := by
  simp only [Square.cross,Square.value,Nat.zero_mul,Nat.add_zero]

theorem rowsTest_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hw : w<2^31) :
    WP isa (.block [.mov .rax (.mem (hdr sW)),.alu .cmp .rax (.imm 8)]) s fun t =>
      t.zf=some (decide (w=8)) ∧ t.mem=s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf=some (decide (w=8)) ∧ t.mem=s.mem) ?_ rfl)
    fun t ⟨⟨z,m⟩,k⟩ => ⟨z,m,k⟩
  xrun [State.ea,hdr,hd,hdrOff,hs.ld (show 8*sW+8≤Z by have := hdr_lt_slot w 8 (show sW<32 by decide); omega_arith),
    hh.hw,show (8 : BitVec 32).signExtend 64=BitVec.ofNat 64 8 from rfl,ofNat_sub_beq (by omega_arith : w<2^64) (by decide : 8<2^64)]

theorem rowsTest16_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hw : w<2^31) :
    WP isa (.block [.mov .rax (.mem (hdr sW)),.alu .cmp .rax (.imm 16)]) s fun t =>
      t.zf=some (decide (w=16)) ∧ t.mem=s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf=some (decide (w=16)) ∧ t.mem=s.mem) ?_ rfl)
    fun t ⟨⟨z,m⟩,k⟩ => ⟨z,m,k⟩
  xrun [State.ea,hdr,hd,hdrOff,hs.ld (show 8*sW+8≤Z by have := hdr_lt_slot w 8 (show sW<32 by decide); omega_arith),
    hh.hw,show (16 : BitVec 32).signExtend 64=BitVec.ofNat 64 16 from rfl,ofNat_sub_beq (by omega_arith : w<2^64) (by decide : 16<2^64)]

theorem rowsChoice_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hw : w<2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) :
    WP isa (AdxTiledSquare.rowsChoice ca) s fun t =>
      (∃ c, wv t.mem B (rawBase w) (2*w)+2^(128*w)*c=
        wv s.mem B (rawBase w) (2*w)+Square.cross (2^512) (chunks s.mem B (slot w a)) n) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledSquare.rowsChoice
  have test := rowsTest_ok hs hd hh hZ hw
  refine WP.seq (WP.mono test fun u ⟨zu,mu,ku⟩ => ?_)
  by_cases h8 : w=8
  · refine WP.ite true (by simp [eval,zu,h8]) (fun _ => WP.block_nil ?_) (by intro h; cases h)
    have km : Keep mmRegs s u := ku.mono (by decide)
    refine ⟨⟨0,?_⟩,mu ▸ hh,?_,km⟩
    swap
    · rw [mu]; exact Frm.refl _ _ _
    have n1 : n=1 := by omega_arith
    rw [mu,n1]
    simp only [cross_one,Nat.mul_zero,Nat.add_zero]
  · refine WP.ite false (by simp [eval,zu,h8]) (by intro h; cases h) (fun _ => ?_)
    have su := hs.congr ku.2.2
    have du : u.gpr .rdi=B := (ku.gpr (by decide)).trans hd
    refine WP.seq (WP.mono (rowsTest16_ok su du (mu ▸ hh) hZ hw) fun v ⟨zv,mv,kv⟩ => ?_)
    have sv := su.congr kv.2.2
    have dv : v.gpr .rdi=B := (kv.gpr (by decide)).trans du
    have mv' : v.mem=s.mem := mv.trans mu
    by_cases h16 : w=16
    · refine WP.ite true (by simp [eval,zv,h16]) (fun _ => ?_) (by intro h; cases h)
      refine WP.mono (rows1_ok sv dv (mv' ▸ hh) hZ (mv' ▸ hv) pa hw hwN
        (by omega_arith) ha ha1 ha2) fun t ⟨vt,ht,ft,kt⟩ => ?_
      rw [mv'] at vt ft
      exact ⟨vt,ht,ft,((ku.trans kv).trans kt).mono (by decide)⟩
    · refine WP.ite false (by simp [eval,zv,h16]) (by intro h; cases h) (fun _ => ?_)
      refine WP.mono (rows_ok sv dv (mv' ▸ hh) hZ (mv' ▸ hv) pa hw hwN
        (by omega_arith) ha ha1 ha2) fun t ⟨vt,ht,ft,kt⟩ => ?_
      rw [mv'] at vt ft
      exact ⟨vt,ht,ft,((ku.trans kv).trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end
