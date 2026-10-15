module

public import VerifiedGarbage.Impl.Dsa.X86.DigestPad
public import VerifiedGarbage.Proof.Dsa.X86.Bytes
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # One byte of a zero-prefixed digest copy -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86

def paddedByte (mem : Mem) (source : Addr) (len j : Nat) : Byte :=
  if j < 32 - len then 0 else mem (source + BitVec.ofNat 64 (j - (32 - len)))

theorem padLoad_ok {s : State} {source : BitVec 32} {len j : Nat}
    (hp : s.gpr .esi = source) (hj : j < 32) (hl : len ≤ 32)
    (fits : source.toNat + len ≤ 2 ^ 32)
    (read : ∀ i < len, InRegions (s.rd ++ s.wr) (source.setWidth 64 + BitVec.ofNat 64 i) 1) :
    WP isa (.block (if j < 32 - len then [.mov .eax (.imm 0)]
      else [.movzx8 .eax (at_ .esi (j - (32 - len)))])) s fun t =>
      t.gpr .eax = (paddedByte s.mem (source.setWidth 64) len j).setWidth 32 ∧
      Keeps [.eax] s t ∧ t.mem = s.mem := by
  by_cases H : j < 32 - len
  · rw [ite_eq_left H]
    exact wp_movS rfl fun t U _ => WP.block_nil
      ⟨by simp only [paddedByte, ite_eq_left H]; rw [U.gpr]; rfl, U.keeps, U.mem⟩
  · rw [ite_eq_right H]
    have Addr : s.ea (at_ .esi (j - (32 - len))) = source.setWidth 64 + BitVec.ofNat 64 (j - (32 - len)) := by
      change addr (s.gpr .esi) _ = _
      rw [hp]
      exact addr_eq (x := source) (k := j - (32 - len)) (by omega)
    have Read := read (j - (32 - len)) (by omega)
    let value := (s.mem (source.setWidth 64 + BitVec.ofNat 64 (j - (32 - len)))).setWidth 32
    refine VG.X86.Wp.cons (s' := s.setReg .eax value) ?_ (WP.block_nil ?_)
    · simp only [exec, Addr, State.load8, ite_eq_left Read, Option.map_some]
      rfl
    · have U := Upd.setReg s .eax value
      exact ⟨by simpa only [paddedByte, ite_eq_right H] using U.gpr, U.keeps, U.mem⟩

theorem digestPadByte_ok {s : State} {base : Addr} {size len j : Nat} {source : BitVec 32}
    (hs : Scr s base size) (space : DigestPad.output + 32 ≤ size)
    (hp : s.gpr .esi = source) (hj : j < 32) (hl : len ≤ 32)
    (fits : source.toNat + len ≤ 2 ^ 32)
    (read : ∀ i < len, InRegions (s.rd ++ s.wr) (source.setWidth 64 + BitVec.ofNat 64 i) 1) :
    WP isa (.block (DigestPad.byte len j)) s fun t =>
      t.mem = s.mem.writeW (off base (DigestPad.output + j)) (paddedByte s.mem (source.setWidth 64) len j) ∧
      Keeps [.eax] s t := by
  unfold DigestPad.byte
  refine WP.block_append (WP.mono (padLoad_ok hp hj hl fits read) fun u ⟨V, K, O⟩ => ?_)
  have S := hs.of_keeps K (by decide)
  refine VG.Proof.Weierstrass.X86.wp_store8' (S.ea (by omega)) (S.write (by omega)) fun t U => WP.block_nil ⟨?_, K.trans (U.keeps _)⟩
  rw [U.mem]
  change u.mem.writeW _ ((u.gpr .eax).setWidth 8) = _
  rw [V, O, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]

theorem digestPadByte_relCT (len j : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) (.block (DigestPad.byte len j))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold DigestPad.byte
  split
  · apply checkedBlockInvariant (τ' := { workspaceTaint true with regs := .ofList [.edi, .esi, .eax] }) ?_ rfl
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
    change taint.checkBlock (workspaceTaint true) [.mov .eax (.imm 0), .store8 (sc 0) .al] = _
    rfl
  · apply checkedBlockInvariant (τ' := workspaceTaint true) ?_ rfl
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
    change taint.checkBlock (workspaceTaint true) [.movzx8 .eax (at_ .esi 0), .store8 (sc 0) .al] = _
    rfl

end VG.Proof.Dsa.X86
