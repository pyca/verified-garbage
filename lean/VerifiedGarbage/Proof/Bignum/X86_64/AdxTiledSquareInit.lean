import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow

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
  have bound : ∀ k<32, 8*k+8≤Z := fun k hk => by have := hdr_lt_slot w 8 hk; omega
  have first : WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 14)) .rax]) s fun t =>
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
  have ou : Outside B carryOffset 8 s.mem u.mem := by rw [mu]; exact writeW_outside _ _ _ (by decide)
  have iu : word u.mem B (8*sFn 12)=BitVec.ofNat 64 i := by rw [ou.word (by decide) (by decide)]; exact hidx
  have su := hs.congr ku.2.2
  have second : WP isa (.block [.mov .rax (.mem (hdr (sFn 12))),.alu .add .rax (.imm 8),.store (hdr (sFn 13)) .rax]) u
      fun t => t.mem=u.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (i+8)) ∧ Keep [.rax] u t := by
    apply WP.keep [.rax] (Q := fun t => t.mem=u.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (i+8))) _ rfl
    xrun [State.ea,hdr,(ku.gpr (by decide)).trans hd,hdrOff,su.ld (bound (sFn 12) (by decide)),
      su.st (bound (sFn 13) (by decide)),iu,show (8 : BitVec 32).signExtend 64=8 from rfl,BitVec.ofNat_add]
    rfl
  refine WP.mono second fun t ⟨mt,kt⟩ => ?_
  have ot : Outside B (8*sFn 13) 8 u.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by decide)
  refine ⟨?_,?_,(ou.mono (o' := 8*sFn 13) (n' := 16) (by decide) (by decide)).trans
    (ot.mono (by omega) (by omega)),(ku.trans kt).mono (by simp)⟩
  · rw [ot.word (by decide) (by decide),mu,word_writeW_self]
  · rw [mt,word_writeW_self]

end VG.Proof.Bignum.X86_64.AdxTiledSquare
