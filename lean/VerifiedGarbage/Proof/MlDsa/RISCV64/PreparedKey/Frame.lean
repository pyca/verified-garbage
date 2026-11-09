module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.PreparedKey.Entry
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Base
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA on RISC-V: the frame and the cache's arguments of the entries

What the entries of the kernels (`Impl/MlDsa/RISCV64/PreparedKey/Entry.lean`)
do around their call: the cache's arguments (`cacheArgs_ok`), and the frame of
16 bytes at `sp - 16`, which keeps the return address at `sp - 8` and changes
nothing else (`pushed_frame`, `slot_read`), and which the regions of the
arguments, apart from the stack below the stack pointer, are apart from
(`bytes_pushed`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.PreparedKey

open VG VG.RISCV64 VG.RISCV64.RegUpd
open VG.Impl.MlDsa.RISCV64.PreparedKey
open VG.Impl.MlDsa.RISCV64.KeyGen (Arg)
open VG.Spec.Sha3 (bytesAt)

/-- What the cache's arguments leave: `vp` in `cp` and `vl` in `cl`, and the
rest of `s`. -/
structure ArgsSet (cp cl : Reg) (vp vl : BitVec 64) (s u : State) : Prop where
  vcp : u.gpr cp = vp
  vcl : u.gpr cl = vl
  other : ∀ r, r ≠ cp → r ≠ cl → u.gpr r = s.gpr r
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp

/-- The cache's pointer: `a0 + off` for a prepared key, and `a0` (the cache
empty) otherwise. -/
def cpVal (s : State) (off : Nat) : Bool → BitVec 64
  | true => s.gpr .a0 + BitVec.ofNat 64 off
  | false => s.gpr .a0

/-- The cache's length. -/
def clVal (len : Nat) : Bool → BitVec 64
  | true => BitVec.ofNat 64 len
  | false => 0

theorem cacheArgs_ok {cp cl : Reg} (hcp : cp ≠ .a0) (hne : cl ≠ cp) {off len : Nat} (ho : off < 2 ^ 31 - 2048)
    (hl : len < 2 ^ 31 - 2048) (q : Bool) (s : State) :
    WP isa (.block (cacheArgs cp cl off len q)) s (ArgsSet cp cl (cpVal s off q) (clVal len q) s) := by
  cases q with
  | true =>
    rw [cacheArgs, WP.block_append_iff, Arg.instrs, WP.block_append_iff]
    refine WP.mono (KeyGen.loadImm_ok cp ho s) fun s₁ e₁ => ?_
    subst e₁
    refine Steps.WP.cons exec_add (WP.block_nil ?_)
    refine WP.mono (KeyGen.loadImm_ok cl hl _) fun u e => ?_
    subst e
    refine ⟨?_, gpr_write_self .., fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_of_ne _ _ hne.symm, gpr_write_self, gpr_write_of_ne _ _ (Ne.symm hcp), gpr_write_self,
        cpVal]
    · rw [gpr_write_of_ne _ _ h2, gpr_write_of_ne _ _ h1, gpr_write_of_ne _ _ h1]
  | false =>
    rw [cacheArgs]
    exact Steps.wp_mv fun u₁ v₁ => Steps.wp_li (imm := 0) (by decide) fun u₂ v₂ => WP.block_nil
      ⟨by rw [v₂.other _ hne.symm, v₁.gpr]; rfl, by rw [v₂.gpr]; rfl,
        fun r h1 h2 => by rw [v₂.other _ h2, v₁.other _ h1],
        by rw [v₂.mem, v₁.mem], by rw [v₂.rd, v₁.rd], by rw [v₂.wr, v₁.wr], by rw [v₂.sp, v₁.sp]⟩

/-- The frame's push changes memory only in the frame. -/
theorem pushed_frame (r : Reg) (s : State) : Frame [⟨s.sp - 16, 16⟩] s.mem (pushed r s).mem := by
  refine (Frame.refl _ _).write (List.mem_singleton_self _) _ ?_
  simp only [Region.Contains]
  rw [show s.sp - 16 + 8 - (s.sp - 16) = 8 from by bv_omega]
  decide

/-- The return address, in the frame's slot. -/
theorem slot_read (r : Reg) (s : State) : (pushed r s).mem.read (s.sp - 16 + 8) 8 = s.gpr r :=
  read_write_self _ _ _

/-- The frame lies in the stack below the stack pointer. -/
theorem frame_sub {s : State} {N : Nat} (hN : 16 ≤ N) :
    Region.Sub ⟨s.sp - 16, 16⟩ (below s.sp N) := by
  have e : s.sp - 16 = (s.sp - BitVec.ofNat 64 N) + BitVec.ofNat 64 (N - 16) := by
    have := s.sp.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (16 : BitVec 64).toNat = 16 from rfl]
    omega
  rw [e]
  exact Offset.sub_base _ (by omega)

/-- The bytes of a region apart from the stack below the stack pointer, after
the push. -/
theorem bytes_pushed {r : Reg} {s : State} {N : Nat} (hN : 16 ≤ N) {R : Region}
    (hR : R.len ≤ 2 ^ 64) (hd : (below s.sp N).Disjoint R) :
    bytesAt (pushed r s).mem R.base R.len = bytesAt s.mem R.base R.len :=
  Proof.MlKem.bytesAt_frame (pushed_frame r s) (fun r' hr' => by
    rw [List.mem_singleton] at hr'; subst hr'
    exact (hd.sub_left (frame_sub hN)).symm) hR

end VG.Proof.MlDsa.RISCV64.PreparedKey
