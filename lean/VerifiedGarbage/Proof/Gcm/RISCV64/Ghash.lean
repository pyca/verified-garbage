module

public import VerifiedGarbage.Impl.Gcm.RISCV64
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.BE64
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# GHASH on RISC-V: its contract, and constant time

Untrusted: everything here is checked by Lean. `vg_ghash`'s callers are proven
from `GhashLaw`, which `Law.lean` proves, so that they need not import its
algebra.
-/

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64
open VG.RISCV64.ByteLoad (be64 beBytes)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ofBytes)

/-- The contract of `vg_ghash(h = a0, y = a1, data = a2, n = a3,
scratch = a4)`, which uses the 2048 bytes below the stack pointer. -/
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
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

/-- `vg_ghash` meets its contract (`instGhashLaw`, `Law.lean`). -/
class GhashLaw : Prop where
  ok : ∀ s, ghashX.pre s → ∃ t s', Exec isa Impl.Gcm.RISCV64.ghash s t s' ∧ abiPreserved s s' ∧ ghashX.post s s'

theorem ghash_correct [GhashLaw] (s : State) (h : ghashX.pre s) :
    ∃ t s', Exec isa Impl.Gcm.RISCV64.ghash s t s' ∧ abiPreserved s s' ∧ ghashX.post s s' := GhashLaw.ok s h

theorem ghash_ct : ConstantTime isa ghashX.pre ghashX.pub Impl.Gcm.RISCV64.ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨h6, fun r hr => ?_⟩
  rw [Taint.mem_ofRegs] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-! ## Blocks as two big-endian doublewords -/

/-- A block from its two doublewords, the first first. -/
abbrev w2 (a b : BitVec 64) : Block := a ++ b

/-- The block at `p`, as two `loadBE64`s load it. -/
def hOf (m : Mem) (p : Addr) : Block := w2 (be64 m p 0) (be64 m p 8)

theorem blockAt_hOf (m : Mem) (p : Addr) : blockAt m p = hOf m p := by
  have h : Spec.Aes.bytesAt m p 16 =
      [m (p + BitVec.ofNat 64 0), m (p + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 2), m (p + BitVec.ofNat 64 3),
        m (p + BitVec.ofNat 64 4), m (p + BitVec.ofNat 64 5), m (p + BitVec.ofNat 64 6), m (p + BitVec.ofNat 64 7),
        m (p + BitVec.ofNat 64 8), m (p + BitVec.ofNat 64 9), m (p + BitVec.ofNat 64 10), m (p + BitVec.ofNat 64 11),
        m (p + BitVec.ofNat 64 12), m (p + BitVec.ofNat 64 13), m (p + BitVec.ofNat 64 14),
        m (p + BitVec.ofNat 64 15)] := rfl
  rw [blockAt, h, ofBytes_16]
  rfl

theorem blockAt_store (m : Mem) (q : Addr) (z0 z1 : BitVec 64) :
    blockAt (WriteBytes.writeBytes (WriteBytes.writeBytes m (q + BitVec.ofNat 64 0) (beBytes 8 z0))
      (q + BitVec.ofNat 64 8) (beBytes 8 z1)) q = w2 z0 z1 := by
  open VG.RISCV64.BE64 in
  rw [blockAt_hOf, hOf, be64_eq, be64_eq, writeBytes_beBytes, writeBytes_beBytes, Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (Offset.sep q (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide))
      (by decide), Mem.readW_writeW_self64, Proof.Gcm.byteRev64_byteRev64, Proof.Gcm.byteRev64_byteRev64]

end VG.Proof.Gcm.RISCV64
