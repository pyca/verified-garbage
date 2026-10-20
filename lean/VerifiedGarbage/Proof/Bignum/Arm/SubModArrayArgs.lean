module

public import VerifiedGarbage.Impl.Bignum.Arm.SubModArray
public import VerifiedGarbage.Proof.Bignum.Arm.Bases
import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayArgs
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Prepare public native pointers for modular subtraction -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem subModArrayArgs_ok (s : State) {base : BitVec 32} {size w o a b : Nat}
    {arr : Nat → Nat} {inv : BitVec 32} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ws : Workspace s base size) (fit : 128 ≤ size) (header : NativeHeader s.mem base w arr inv)
    (ptr : s.gpr .r0 = base) :
    WP isa (subModArrayArgs o a b) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (arr o) ∧ t.gpr .r10 = base + BitVec.ofNat 32 (arr a) ∧
      t.gpr .r12 = base + BitVec.ofNat 32 (arr b) ∧ t.gpr .r9 = base + BitVec.ofNat 32 (arr 0) ∧
      t.gpr .lr = BitVec.ofNat 32 (2 * w) ∧ t.mem = s.mem ∧ Rest [.r0, .r9, .r10, .r12, .lr] s t := by
  rw [subModArrayArgs, WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) 64) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read (by omega)) fun u load => WP.block_nil ?_
  refine WP.mono (selectArrayArgs_ok u ho ha hb (ws.congr load.wr) fit
    (by rw [load.mem]; exact header) ((load.other .r0 (by decide)).trans ptr)) ?_
  rintro t ⟨out, first, second, count, mem, rest⟩
  have modulus : u.gpr .r9 = base + BitVec.ofNat 32 (arr 0) :=
    load.gpr.trans (header.array 0 (by decide))
  exact ⟨out, first, second, (rest.gpr .r9 (by simp)).trans modulus, count, mem.trans load.mem,
    (load.rest (by simp)).trans (rest.mono (by simp))⟩

end VG.Proof.Bignum.Arm
