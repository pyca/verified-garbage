import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
import VerifiedGarbage.Proof.Bignum.X86_64.OpAt

/-! ## AdxRect8Counter -/
section

namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem nextColumn_ok {s : State} {B : Addr} {Z w j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hj : j+8 < 2^64) (hw : w < 2^64)
    (hidx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j) :
    WP isa (.block AdxRect8.nextColumn) s fun t =>
      t.mem = s.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (j+8)) ∧
      t.zf = some (decide (j+8=w)) ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  have hiZ : 8*sFn 13+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 13 < 32 by decide); omega
  have hwZ : 8*sW+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sW < 32 by decide); omega
  unfold AdxRect8.nextColumn
  rw [show ([.mov .rax (.mem (hdr (sFn 13))), .alu .add .rax (.imm 8),
      .store (hdr (sFn 13)) .rax, .alu .cmp .rax (.mem (hdr sW))] : List Instr) =
      [.mov .rax (.mem (hdr (sFn 13))), .alu .add .rax (.imm 8), .store (hdr (sFn 13)) .rax] ++
      [.alu .cmp .rax (.mem (hdr sW))] from rfl, WP.block_append_iff]
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
    rw [ma,(writeW_outside s.mem B (BitVec.ofNat 64 (j+8)) (by omega : 8*sFn 13+8 ≤ 2^64)).word
      (by decide : 8*sW+8 ≤ 8*sFn 13 ∨ 8*sFn 13+8 ≤ 8*sW) (by omega),hh.hw]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = a.mem ∧ t.zf = some (decide (j+8=w))) ?_ rfl)
    fun t ⟨⟨mt,zt⟩,kt⟩ => ⟨mt.trans ma,zt,(ka.trans kt).mono (by simp)⟩
  xrun [State.ea,hdr,(ka.gpr (by decide)).trans hd,hdrOff,sa.ld hwZ,wa,ra,ofNat_sub_beq hj hw]

end VG.Proof.Bignum.X86_64.AdxRect8

end

/-! ## AdxRect8Frame -/
section

namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

/-- The tile's temporary header words do not overlap the Montgomery header. -/
theorem frame_hdr {m m' : Mem} {B : Addr} {w e n : Nat} {mi : BitVec 64}
    (hh : Hdr m B w mi) (he : hdrBytes ≤ e)
    (hf : Frm B [(e,n),(carryOffset,8),(8*sFn 13,8)] m m') : Hdr m' B w mi := by
  have low (k : Nat) (hk : k < 16) : word m' B (8*k) = word m B (8*k) := by
    apply hf.word_eq
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [] <;>
        unfold carryOffset sFn hdrBytes at * <;> omega
    · omega
  exact ⟨(low sW (by decide)).trans hh.hw,(low sMinv (by decide)).trans hh.hminv,
    fun k hk => (low (sArr k) (by unfold sArr; omega)).trans (hh.harr k hk)⟩

/-- Nor the slots of the operands' bases. -/
theorem frame_ops {m m' : Mem} {B : Addr} {w e n : Nat} {ps : List (Nat × Nat)}
    (hv : Ops m B w ps) (he : hdrBytes ≤ e)
    (hf : Frm B [(e,n),(carryOffset,8),(8*sFn 13,8)] m m') : Ops m' B w ps :=
  hv.of_frm hf fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [] <;> unfold carryOffset sFn hdrBytes at * <;> omega

/-- Two adjacent scratch arrays contain every rectangular tile. -/
theorem tile_ranges {w i j a : Nat} (hi : i+8 ≤ w) (hj : j+8 ≤ w)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    slot w a+8*i+64 ≤ slot w 8 ∧
    slot w aAcc+16+8*(i+j)+128 ≤ slot w 8 ∧
    (slot w a+8*i+64 ≤ slot w aAcc+16+8*(i+j) ∨
      slot w aAcc+16+8*(i+j)+128 ≤ slot w a+8*i) := by
  have sa := slot_le (w := w) ha
  have st := slot_le (w := w) (show aTmp < 8 by decide)
  have s1 := slot_sep (w := w) ha1
  have s2 := slot_sep (w := w) ha2
  unfold slot aAcc aTmp at *
  omega

end VG.Proof.Bignum.X86_64.AdxRect8

end
