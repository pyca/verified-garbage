module

public import VerifiedGarbage.Impl.Bignum.Arm.RowStep
public import VerifiedGarbage.Proof.Bignum.Arm.Mac
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The memory and arithmetic effects of one ARMv7 Montgomery row step -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_str wp_mov op2_reg)

abbrev rowClobbers : List Reg := [.r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- A row step writes exactly one accumulator word. Its high word is the
carry for the next step; the accumulator and input addresses stay fixed. -/
theorem rowStep_ok (s : State) (a b : Addr)
    (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (hb : State.addr (s.gpr .r12 + BitVec.ofNat 32 0) = b)
    (hread : InRegions (s.rd ++ s.wr) b 4) (hwrite : InRegions s.wr a 4) :
    WP isa rowStep s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
        (s.gpr .r1).toNat * (s.mem.readW b 32).toNat +
          (s.mem.readW a 32).toNat + (s.gpr .r11).toNat ∧
      t.mem = s.mem.writeW a (t.gpr .r3) ∧ Rest rowClobbers s t := by
  rw [rowStep, WP.seq_iff]
  refine wp_ldr (by decide) hb hread fun s1 u1 => ?_
  refine wp_ldr (a := a) (by decide) (by rw [u1.other .r0 (by decide)]; exact ha)
    (by rw [u1.rd, u1.wr]; rcases hwrite with ⟨R, hR, haR⟩; exact ⟨R, List.mem_append_right _ hR, haR⟩) fun s2 u2 => ?_
  apply WP.block_nil
  rw [WP.seq_iff]
  refine WP.mono (mac_ok s2) ?_
  rintro s3 ⟨val, keep⟩
  have ptr : s3.gpr .r0 = s.gpr .r0 :=
    (keep.regs .r0 (by simp [clobbers])).trans
      ((u2.other .r0 (by decide)).trans (u1.other .r0 (by decide)))
  have mem3 : s3.mem = s.mem := keep.mem.trans (u2.mem.trans u1.mem)
  refine wp_str (a := a) (by decide) (by rw [ptr]; exact ha)
    (by rw [keep.wr, u2.wr, u1.wr]; exact hwrite) fun s4 u4 => ?_
  refine wp_mov (op2_reg _ _) fun s5 u5 => WP.block_nil ?_
  have out3 : s5.gpr .r3 = s3.gpr .r3 :=
    (u5.other .r3 (by decide)).trans (congrFun u4.gpr .r3)
  have carry : s5.gpr .r11 = s3.gpr .r4 := u5.gpr.trans (congrFun u4.gpr .r4)
  refine ⟨?_, ?_, ?_⟩
  · rw [out3, carry, val, u2.other .r1 (by decide), u1.other .r1 (by decide),
      u2.other .r2 (by decide), u1.gpr, u2.gpr, u1.mem,
      u2.other .r11 (by decide), u1.other .r11 (by decide)]
  · rw [u5.mem, u4.mem, mem3, out3]
  · have rest : Rest clobbers s2 s3 := ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩
    refine ((u1.rest (ws := rowClobbers) (by simp [rowClobbers])).trans
      (u2.rest (by simp [rowClobbers]))).trans
      ((rest.mono ?_).trans ((u4.rest _).trans (u5.rest (by simp [rowClobbers]))))
    intro r hr
    cases r <;> simp_all [clobbers, rowClobbers]

end VG.Proof.Bignum.Arm
