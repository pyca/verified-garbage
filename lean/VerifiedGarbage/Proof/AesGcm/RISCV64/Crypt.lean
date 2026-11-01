module

import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
public import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.Ghash1
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Spec.Gcm

/-!
# AES-GCM on RISC-V: counter mode over a piece (`crypt`)

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcm/PPC64LE/Crypt.lean`, `CryptOk.lean`): `crypt` XORs the
keystream, from byte `P` of the text on, into the `s5` bytes at `s4`, where
`s6` is `P mod 16` and the state holds the counter block and the keystream
block for `P` bytes (`Proof.Gcm.Ctr`): the rest of the keystream block
(`cryptHead`), whole blocks with `vg_aes_ctr32` (`cryptWhole`), then a new
keystream block for the last bytes (`cryptTail`). The number of rounds is in
`s3`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- A buffer of `n` bytes at `D` that the code may read and write, apart from
the context, the state and `W`. -/
structure DataW (c st w : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  ok : DataOk st w s D n
  wr : Covers [⟨D, n⟩] s.wr
  ctx : (⟨c, 256⟩ : Region).Disjoint ⟨D, n⟩

theorem DataW.of_eq {c st w : Addr} {s s' : State} {D : Addr} {n : Nat}
    (h : DataW c st w s D n) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    DataW c st w s' D n :=
  ⟨h.ok.of_eq hrd hwr hsp, by rw [hwr]; exact h.wr, h.ctx⟩

theorem DataW.sub {c st w : Addr} {s : State} {D : Addr} {n : Nat} (h : DataW c st w s D n)
    {j k : Nat} (hjk : j + k ≤ n) (hk : 0 < k) : DataW c st w s (D + BitVec.ofNat 64 j) k :=
  ⟨h.ok.sub hjk hk, covers_off h.wr hjk h.ok.lt, h.ctx.sub_right (Offset.sub_base _ hjk)⟩

theorem DataW.take {c st w : Addr} {s : State} {D : Addr} {n : Nat} (h : DataW c st w s D n)
    {k : Nat} (hk : k ≤ n) : DataW c st w s D k :=
  ⟨h.ok.take hk, covers_prefix h.wr hk, h.ctx.sub_right (Region.sub_prefix hk)⟩

/-- The cipher of the key schedule in the context, for `R` rounds. -/
abbrev ciphOf (m : Mem) (C : Addr) (R : Nat) : Block → Block :=
  aesWith R (bytesAt m C (16 * (R + 1)))

/-- The regions `crypt` writes. -/
abbrev crFrame (st w D : Addr) (n : Nat) : List Region :=
  [⟨D, n⟩, ⟨st + BitVec.ofNat 64 48, 32⟩, ⟨w + BitVec.ofNat 64 512, 2048⟩]

/-- Before `crypt`: `P` bytes of text so far, `n` bytes at `D` to go, `R`
rounds in `s3`. -/
structure CrIn (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (icb : Block) (P : Nat) (D : Addr) (n : Nat)
    (s : State) : Prop where
  env : Env V sp s
  s4 : s.gpr .s4 = D
  s5 : s.gpr .s5 = BitVec.ofNat 64 n
  s6 : s.gpr .s6 = BitVec.ofNat 64 (P % 16)
  s3 : V .s3 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  data : DataW (V .s2) (V .s1) (V .s0) s D n

/-- Part of the way: `j` bytes done, from `m₀`. -/
structure CrMid (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (icb : Block) (P : Nat) (D : Addr) (n : Nat)
    (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env V sp s
  le : j ≤ n
  s4 : s.gpr .s4 = D + BitVec.ofNat 64 j
  s5 : s.gpr .s5 = BitVec.ofNat 64 (n - j)
  s3 : V .s3 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  data : DataW (V .s2) (V .s1) (V .s0) s D n
  ctr : Ctr m₀ (V .s1 + BitVec.ofNat 64 48) (V .s1 + BitVec.ofNat 64 64) (ciphOf m₀ (V .s2) R) icb P →
    Ctr s.mem (V .s1 + BitVec.ofNat 64 48) (V .s1 + BitVec.ofNat 64 64) (ciphOf m₀ (V .s2) R) icb (P + j)
  done : Ctr m₀ (V .s1 + BitVec.ofNat 64 48) (V .s1 + BitVec.ofNat 64 64) (ciphOf m₀ (V .s2) R) icb P →
    bytesAt s.mem D j = xorKs (ciphOf m₀ (V .s2) R) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (crFrame (V .s1) (V .s0) D n) m₀ s.mem

/-- After `crypt`. -/
structure CrOut (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (icb : Block) (P : Nat) (D : Addr) (n : Nat)
    (m₀ : Mem) (s : State) : Prop where
  env : Env V sp s
  ctr : Ctr m₀ (V .s1 + BitVec.ofNat 64 48) (V .s1 + BitVec.ofNat 64 64) (ciphOf m₀ (V .s2) R) icb P →
    Ctr s.mem (V .s1 + BitVec.ofNat 64 48) (V .s1 + BitVec.ofNat 64 64) (ciphOf m₀ (V .s2) R) icb (P + n)
  out : Ctr m₀ (V .s1 + BitVec.ofNat 64 48) (V .s1 + BitVec.ofNat 64 64) (ciphOf m₀ (V .s2) R) icb P →
    bytesAt s.mem D n = xorKs (ciphOf m₀ (V .s2) R) icb P (bytesAt m₀ D n)
  frame : Frame (crFrame (V .s1) (V .s0) D n) m₀ s.mem

section
variable {c st w : Addr} (L : Lay c st w)
include L

theorem ctx_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW c st w s D n) :
    ∀ r ∈ crFrame st w D n, (⟨c, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))

omit L in
theorem ciph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨c, 256⟩ : Region).Disjoint r) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ciphOf m' c R = ciphOf m c R := by
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  simp only [ciphOf]
  rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]

end

/-- `[D, D + j)` and `[D + j, D + n)` are apart. -/
theorem split_disj {D : Addr} {j n : Nat} (hj : j ≤ n) (hn : n < 2 ^ 64) :
    (⟨D, j⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 j, n - j⟩ := by
  have := Offset.disjoint D (d := 0) (n := j) (e := j) (k := n - j) (.inl (by omega)) (by omega) (by omega)
  simpa using this

/-- The bytes done so far and the next ones. -/
theorem done_append {m m₀ : Mem} {ciph : Block → Block} {icb : Block} {P : Nat} {D : Addr} {j l : Nat}
    (h₁ : bytesAt m D j = xorKs ciph icb P (bytesAt m₀ D j))
    (h₂ : bytesAt m (D + BitVec.ofNat 64 j) l = xorKs ciph icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) l)) :
    bytesAt m D (j + l) = xorKs ciph icb P (bytesAt m₀ D (j + l)) := by
  rw [bytesAt_add, bytesAt_add, Proof.Gcm.xorKs_append, h₁, h₂, length_bytesAt]

end VG.Proof.AesGcm.RISCV64
