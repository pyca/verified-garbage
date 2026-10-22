module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Crypt
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Callee
public import VerifiedGarbage.Proof.Gcm.Ctr

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.CtrCipher

/-!
# SM4-GCM on x86-64: where everything is, and counter mode over a piece

Untrusted: everything here is checked by Lean. The layout is AES-GCM's
(`Proof/AesGcm/X86_64/Env.lean`, `Lay`), with the stack below `SP` that the
calls of `vg_sm4_ctr32` and `vg_sm4_expand_key` use, `stkN` bytes, apart
from the context, the state and `W` (`Lay4`) and from the data (`DataW4`).
`crypt` XORs the keystream, from byte `P` of the text on, into the `rbp`
bytes at `r12`, as AES-GCM's (`Proof/AesGcm/X86_64/Crypt.lean`), with SM4
under the context's schedule as the cipher (`ciphOf`) and no number of rounds.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.Gcm (Ctr xorKs)
open VG.Proof.AesGcm.X86_64 (Lay Env DataOk DataW)

/-- AES-GCM's layout (`Lay`), and the stack the calls use below `SP`, apart
from the context, the state and `W`. -/
structure Lay4 (Ctx St W SP : Addr) : Prop where
  lay : Lay Ctx St W SP
  sp : stkN ≤ SP.toNat
  kc : (below SP stkN).Disjoint ⟨Ctx, 256⟩
  ks : (below SP stkN).Disjoint ⟨St, 80⟩
  kw : (below SP stkN).Disjoint ⟨W, 2560⟩

/-- A buffer of `n` bytes at `D` that the code may read and write
(`DataW`), apart from the stack the calls use too. -/
structure DataW4 (Ctx St W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  dw : DataW Ctx St W SP s D n
  stk : (below SP stkN).Disjoint ⟨D, n⟩

namespace DataW4

variable {Ctx St W SP : Addr} {s : State} {D : Addr} {n : Nat}

theorem of_eq {s' : State} (h : DataW4 Ctx St W SP s D n) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    DataW4 Ctx St W SP s' D n :=
  ⟨h.dw.of_eq hrd hwr, h.stk⟩

theorem drop (h : DataW4 Ctx St W SP s D n) {k : Nat} (hk : k ≤ n) :
    DataW4 Ctx St W SP s (D + BitVec.ofNat 64 k) (n - k) :=
  ⟨h.dw.drop hk, h.stk.sub_right (Offset.sub_base D (by omega))⟩

theorem take (h : DataW4 Ctx St W SP s D n) {k : Nat} (hk : k ≤ n) : DataW4 Ctx St W SP s D k :=
  ⟨h.dw.take hk, h.stk.sub_right (Region.sub_prefix hk)⟩

end DataW4

/-- The cipher of the key schedule in the context's first 128 bytes. -/
abbrev ciphOf (m : Mem) (Ctx : Addr) : Block → Block := Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt m Ctx)

/-- The regions `crypt` writes. -/
abbrev crFrame (St SP D : Addr) (n : Nat) : List Region :=
  [⟨D, n⟩, ⟨St + BitVec.ofNat 64 48, 32⟩, below SP stkN]

/-- Before `crypt`: `P` bytes of text so far, `n` bytes at `D` to go. -/
structure CrIn (Ctx St W SP : Addr) (icb : Block) (P : Nat) (D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  r12 : s.gpr .r12 = D
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  rbx : s.gpr .rbx = BitVec.ofNat 64 (P % 16)
  data : DataW4 Ctx St W SP s D n

/-- Part of the way: `j` bytes done, from `m₀`. -/
structure CrMid (Ctx St W SP : Addr) (icb : Block) (P : Nat) (D : Addr) (n : Nat) (m₀ : Mem)
    (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  le : j ≤ n
  r12 : s.gpr .r12 = D + BitVec.ofNat 64 j
  rbp : s.gpr .rbp = BitVec.ofNat 64 (n - j)
  data : DataW4 Ctx St W SP s D n
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb (P + j)
  done : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb P →
    bytesAt s.mem D j = xorKs (ciphOf m₀ Ctx) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (crFrame St SP D n) m₀ s.mem

/-- After `crypt`. -/
structure CrOut (Ctx St W SP : Addr) (icb : Block) (P : Nat) (D : Addr) (n : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb (P + n)
  out : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb P →
    bytesAt s.mem D n = xorKs (ciphOf m₀ Ctx) icb P (bytesAt m₀ D n)
  frame : Frame (crFrame St SP D n) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP)
include L

theorem ctx_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW4 Ctx St W SP s D n) :
    ∀ r ∈ crFrame St SP D n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.dw.ctx
  · exact L.lay.cs.sub_right (Lay.stSub (by decide))
  · exact L.kc.symm

omit L in
theorem ciph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨Ctx, 256⟩ : Region).Disjoint r) : ciphOf m' Ctx = ciphOf m Ctx := by
  simp only [ciphOf]
  rw [Proof.Sm4.scheduleAt_congr fun i hi =>
    hf.bytes (R := ⟨Ctx, 128⟩) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide)))
      (by show 128 ≤ 2 ^ 64; omega) hi]

end

end VG.Proof.Sm4Gcm.X86_64
