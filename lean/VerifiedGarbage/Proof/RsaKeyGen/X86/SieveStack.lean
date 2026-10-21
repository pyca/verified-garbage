module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Sieve
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Offset

/-! # Five disjoint native stack words retain the sieve's public geometry -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.RsaKeyGen.X86.Sieve

structure StackContext (p : BitVec 32) (s : State) : Prop where
  ws : Ws s (p.setWidth 64) 20
  sp : s.gpr .esp = p

theorem StackContext.base {p : BitVec 32} {s : State} (C : StackContext p s) :
    PtrAt s (p.setWidth 64) .esp 0 := by
  rw [PtrAt, C.sp, BitVec.toNat_setWidth, Nat.add_zero]
  have := p.isLt
  omega

theorem StackContext.keep {p : BitVec 32} {s t : State} (C : StackContext p s)
    {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs) : StackContext p t :=
  ⟨C.ws.of_keeps K, (K.1 .esp sp).trans C.sp⟩

theorem StackContext.address {p : BitVec 32} {s : State} (C : StackContext p s) (d : Nat) (fit : d < 20) :
    s.ea (slot d) = off (p.setWidth 64) d := by
  simpa only [slot, VG.Impl.Mont.X86.at_, Nat.zero_add] using ea_ptr C.ws C.base (d := d) (by omega)

theorem StackContext.access {p : BitVec 32} {s : State} (C : StackContext p s) (d : Nat) (fit : d + 4 ≤ 20) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) d) 4 := by
  change InRegions (s.rd ++ s.wr) (s.ea (slot d)) 4
  rw [C.address d (by omega)]
  exact ws_read C.ws fit


theorem StackContext.read {p : BitVec 32} {s : State} (C : StackContext p s) (d : Nat) (fit : d + 4 ≤ 20) :
    readSrc s (.mem (slot d)) = some (s.mem.readW (off (p.setWidth 64) d) 32) := by
  simpa only [slot, VG.Impl.Mont.X86.at_, Nat.zero_add] using readSrc_ptr C.ws C.base (d := d) (by omega)

theorem StackContext.store {p : BitVec 32} {s : State} (C : StackContext p s)
    (d : Nat) (fit : d + 4 ≤ 20) (r : Reg) :
    WP isa (.block [.store (slot d) r]) s fun t =>
      t.mem = s.mem.writeW (off (p.setWidth 64) d) (s.gpr r) ∧
      Outside (p.setWidth 64) d 4 s.mem t.mem ∧ Keeps [] s t ∧ StackContext p t := by
  refine wp_storeS (ea_ptr C.ws C.base (d := d) (by omega)) (ws_write C.ws (y := 0 + d) (n := 4) (by omega))
    fun t T => WP.block_nil ?_
  have K := T.keeps []
  refine ⟨?_, ?_, K, C.keep K (by decide)⟩
  · simpa only [Nat.zero_add] using T.mem
  · rw [T.mem, Nat.zero_add]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; omega)

theorem StackContext.readAfter {p : BitVec 32} {s t : State} (C : StackContext p s)
    {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs) {a b : Nat}
    (O : Outside (p.setWidth 64) a 4 s.mem t.mem) (fit : b + 4 ≤ 20)
    (apart : b + 4 ≤ a ∨ a + 4 ≤ b) :
    readSrc t (.mem (slot b)) = some (s.mem.readW (off (p.setWidth 64) b) 32) := by
  have read := (C.keep K sp).read b fit
  have same := BitVec.eq_of_toNat_eq (O.w32 (d := b) apart (by omega))
  rw [same] at read
  exact read

theorem StackContext.literal {p : BitVec 32} {s : State} (C : StackContext p s)
    (d : Nat) (fit : d + 4 ≤ 20) (value : BitVec 32) :
    WP isa (.block [.mov .eax (.imm value), .store (slot d) .eax]) s fun t =>
      t.mem = s.mem.writeW (off (p.setWidth 64) d) value ∧ Outside (p.setWidth 64) d 4 s.mem t.mem ∧
      Keeps [.eax] s t ∧ StackContext p t := by
  refine wp_movS rfl fun a A _ => ?_
  refine WP.mono ((C.keep A.keeps (by decide)).store d fit .eax) fun t ⟨M, O, K, Ct⟩ => ?_
  refine ⟨?_, ?_, A.keeps.widen K, Ct⟩
  · rw [M, A.mem, A.gpr]
  · rw [A.mem] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Sieve
