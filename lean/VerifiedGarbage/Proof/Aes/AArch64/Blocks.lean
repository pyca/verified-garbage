module

public import VerifiedGarbage.Proof.Aes.Rounds
public import VerifiedGarbage.Proof.Aes.AArch64.Ecb
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Aes.AArch64.Ctr32
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Aes.AArch64.Ecb
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Aes.AArch64.Ctr32
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES on whole blocks on AArch64: the contract

The AArch64 contract of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`
(`blocksAArch64`), a state satisfying it (`blocksSat`), the moves of the
arguments (`blocksSetup_ok`), and the data after the last group, as states
(`statesAt_of_ecbInv`).
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.AArch64 in
/-- AArch64 contract for `vg_aes_encrypt_blocks(schedule: *const [u8; 240],
rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])` (and
`vg_aes_decrypt_blocks`, with `f` the inverse cipher): replaces each of the
`n` blocks at `data` with `f rounds w` of it, for the key schedule `w`.

The code may read `schedule` (240 bytes) and read and write `data` (`16 n`
bytes) and `scratch` (2048 bytes, whose contents on exit are unspecified).
These may not overlap each other, and `data` may not wrap around the end of
the address space. `rounds` is 10, 12 or 14. The pointers, `rounds` and `n`
are public; the key schedule and the data are secret. -/
def blocksAArch64 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 2048⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x2).toNat + 16 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      (Spec.Aes.statesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat).map
        (f (s.gpr .x1).toNat (Spec.Aes.bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1))))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

theorem blocksSetup_ok (s : State) :
    ∃ s', runBlock isa blocksSetup s = some s' ∧ s'.gpr .x5 = s.gpr .x4 ∧ s'.gpr .x4 = s.gpr .x3 ∧
      s'.gpr .x3 = s.gpr .x2 ∧ (∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by rw [blocksSetup, movR, movR, movR, runBlock_cons, exec_addImm_x (by decide),
    runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
    exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  exact ⟨by simp [State.write, State.read], by simp [State.write, State.read],
    by simp [State.write, State.read], fun r h1 h2 h3 => by simp [State.write, h1, h2, h3],
    rfl, rfl, rfl, rfl⟩

/-- The data after the last group, as states. -/
theorem statesAt_of_ecbInv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n n F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_left (show 16 * j + t < 16 * n by omega_arith),
    show (16 * j + t) / 16 = j by omega_arith, show (16 * j + t) % 16 = t by omega_arith, getD_eq _ ht]

/-! ## The two functions -/

/-- A state satisfying the precondition (one block). -/
def blocksSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

end VG.Proof.Aes.AArch64
