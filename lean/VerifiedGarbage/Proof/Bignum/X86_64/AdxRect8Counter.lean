import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup

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
