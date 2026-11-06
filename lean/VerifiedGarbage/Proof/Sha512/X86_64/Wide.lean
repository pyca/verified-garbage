module

public import VerifiedGarbage.Proof.Sha512.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Sha512.X86_64.Compress
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SHA-512 compression on x86-64 with the shared contract's scratch space

`compressWideX86_64` is `compressX86_64` with the 1328 bytes of scratch space
that the streaming functions pass the compression function
(`Impl.Sha512.X86_64.Stream.params`).
-/

@[expose] public section

namespace VG.Proof.Sha512

open VG.X86_64 in
/-- `compressX86_64` with 1328 bytes of scratch. -/
def compressWideX86_64 : Contract X86_64.isa :=
  { compressX86_64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .rdi, 64⟩
      let blocks : Region := ⟨s.gpr .rsi, 128 * (s.gpr .rdx).toNat⟩
      let scratch : Region := ⟨s.gpr .rcx, 1328⟩
      let ret : Region := ⟨s.gpr .rsp, 8⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch }

end VG.Proof.Sha512

namespace VG.Proof.Sha512.X86_64

open _root_.VG.X86_64

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub176 (a : Addr) : Region.Sub ⟨a, 176⟩ ⟨a, 1328⟩ := Region.sub_prefix (by decide)

/-- A state satisfying `compressWideX86_64.pre`. -/
def wideSat : State := { satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩] }

end VG.Proof.Sha512.X86_64
