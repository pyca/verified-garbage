module

public import VerifiedGarbage.Impl.Gcm.RISCV64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
meta import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# GHASH on RISC-V: the contract

Untrusted: everything here is checked by Lean. `vg_ghash`'s per-target
contract (`ghashX`) in the frame of 2048 bytes below the stack pointer, and
its constant-time proof (`ghash_ct`). As on PPC64LE
(`Proof/Gcm/PPC64LE/Ghash.lean`), callers take its correctness as a
hypothesis (`GhashLaw`): its proof (`Law.lean`) imports the polynomial algebra
of `Proof/Gcm/Poly.lean`, which the AES-GCM, AES-GCM-SIV and SM4-GCM proofs then need
not import, and the registration files supply it.
-/

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64 VG.WriteBytes
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul ofBytes)

/-! ## Blocks as words -/

/-- The block of the high word `a` and the low word `b`. -/
abbrev w2 (a b : BitVec 64) : Block := a ++ b

/-- The block of `H`, from its 16 bytes at `p`. -/
abbrev hOf (m : Mem) (p : Addr) : Block := w2 (ByteLoad.be64 m p 0) (ByteLoad.be64 m p 8)

theorem be8 (z : BitVec 64) :
    ((z >>> 56).setWidth 8 ++ (z >>> 48).setWidth 8 ++ (z >>> 40).setWidth 8 ++ (z >>> 32).setWidth 8 ++
      (z >>> 24).setWidth 8 ++ (z >>> 16).setWidth 8 ++ (z >>> 8).setWidth 8 ++ (z >>> 0).setWidth 8 :
        BitVec 64) = z := by
  apply BitVec.eq_of_toNat_eq
  simp only [Proof.Gcm.toNat_append, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have := z.isLt
  omega

/-- A block, as the two words `loadBE64` reads. -/
theorem blockAt_hOf (m : Mem) (p : Addr) : blockAt m p = hOf m p := by
  simp only [blockAt, Spec.Aes.bytesAt, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, Proof.Gcm.ofBytes_16]
  rfl

/-- The block of the bytes of two words, the high word first. -/
theorem ofBytes_beBytes (z0 z1 : BitVec 64) :
    ofBytes (ByteLoad.beBytes 8 z0 ++ ByteLoad.beBytes 8 z1) = w2 z0 z1 := by
  simp only [ByteLoad.beBytes, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, Proof.Gcm.ofBytes_16, Nat.reduceMul, Nat.reduceSub]
  rw [be8 z0, be8 z1]

/-! ## `Y` back -/

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {zs : List Byte} {n : Nat} (hn : zs.length = n)
    (h : n < 2 ^ 64) : Spec.Aes.bytesAt (writeBytes m q zs) q n = zs := by
  subst hn
  refine List.ext_getElem (by simp [Spec.Aes.bytesAt]) fun i h₁ h₂ => ?_
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Mem.sub_ofNat_toNat q (show i < 2 ^ 64 by simp [Spec.Aes.bytesAt] at h₁; omega)]
  simp [Spec.Aes.bytesAt] at h₁
  simp [h₁, List.getD_eq_getElem?_getD]

/-- The block the two `storeBE`s write. -/
theorem blockAt_store (m : Mem) (q : Addr) (z0 z1 : BitVec 64) :
    blockAt (writeBytes (writeBytes m (q + BitVec.ofNat 64 0) (ByteLoad.beBytes 8 z0)) (q + BitVec.ofNat 64 8)
      (ByteLoad.beBytes 8 z1)) q = w2 z0 z1 := by
  have e := writeBytes_append m q (ByteLoad.beBytes 8 z0) (ByteLoad.beBytes 8 z1)
    (by simp [ByteLoad.beBytes_length])
  rw [ByteLoad.beBytes_length] at e
  rw [BitVec.add_zero, e, blockAt,
    bytesAt_writeBytes_self _ _ (by simp [ByteLoad.beBytes_length]) (by decide), ofBytes_beBytes]

/-! ## The contract -/

/-- The contract the proof of `vg_ghash` is written against, with the frame
of 2048 bytes below the stack pointer. -/
def ghashX : Contract isa where
  pre s :=
    let h : Region := ⟨s.gpr .a0, 16⟩
    let y : Region := ⟨s.gpr .a1, 16⟩
    let data : Region := ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩
    let scratch : Region := ⟨s.gpr .a4, 256⟩
    let stack : Region := ⟨s.sp - BitVec.ofNat 64 2048, 2048⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch] ∧ y.Disjoint data ∧
    stack.Disjoint h ∧ stack.Disjoint y ∧ stack.Disjoint data ∧
    (s.gpr .a1).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 16 * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    s.sp.toNat % 16 = 0 ∧ 2048 ≤ s.sp.toNat
  post s s' :=
    blockAt s'.mem (s.gpr .a1) =
      ghashFrom (blockAt s.mem (s.gpr .a0)) (blockAt s.mem (s.gpr .a1))
        (blocksAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

end VG.Proof.Gcm.RISCV64

end

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64 VG.WriteBytes
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul ofBytes)

/-- `vg_ghash` meets its contract: what `Law.lean` proves, which callers take
as a hypothesis so that they do not import its algebra. -/
class GhashLaw : Prop where
  correct : ∀ s, ghashX.pre s →
    ∃ t s', Exec isa ghash s t s' ∧ abiPreserved s s' ∧ ghashX.post s s'

theorem ghash_correct [GhashLaw] (s : State) (hs : ghashX.pre s) :
    ∃ t s', Exec isa ghash s t s' ∧ abiPreserved s s' ∧ ghashX.post s s' :=
  GhashLaw.correct s hs

theorem ghash_ct : ConstantTime isa ghashX.pre ghashX.pub ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

end VG.Proof.Gcm.RISCV64
