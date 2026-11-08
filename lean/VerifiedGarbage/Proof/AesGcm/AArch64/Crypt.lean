module

public import VerifiedGarbage.Proof.Gcm.Ctr
public import VerifiedGarbage.Proof.AesGcm.AArch64.Absorb
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM on AArch64: counter mode over a piece (`crypt`)

Untrusted: everything here is checked by Lean. `crypt` XORs the keystream,
from byte `P` of the text on, into the `x24` bytes at `x23`, where `x25` is
`P mod 16` and the state holds the counter block and the keystream block for
`P` bytes (`Proof.Gcm.Ctr`): the rest of the keystream block and the
arguments for the whole blocks (`crSeg1_ok`), the whole blocks with
`vg_aes_ctr32` (`ctrCall1_ok`), the arguments for a new keystream block
(`crSeg2_ok`), a new keystream block if there are bytes left (`ctrCall2_ok`),
and the last bytes (`crTail_ok`); `crypt_ok` puts them together.

`cryptAlG to` is `cryptAl`, `crypt` from the start of a keystream block, in
place (`to = false`) or out of place (`to = true`): then it reads the text
at `D` (`x23`), which it only needs to read, and writes the output at `O`
(`x26`), a writable buffer apart from it (`OutAt`), the whole blocks with
`vg_aes_ctr32_to` and the last bytes XORed into the keystream block and
copied from it (`crTailG_ok`); `cryptAlG_ok`. The structures (`CrInG`, …,
`CrOutG`) take `to` and the output `O`; in place, `O = D`, and `CrIn`, …,
`CrOut` are them with `to = false` and `O = D`.
-/
@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- A buffer of `n` bytes at `D` that the code may read and write, apart from
the context, the state and `W`. -/
structure DataW (Ctx St W : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  ok : DataOk St W s D n
  wr : Covers [⟨D, n⟩] s.wr
  ctx : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩

theorem DataW.of_eq {Ctx St W : Addr} {s s' : State} {D : Addr} {n : Nat} (h : DataW Ctx St W s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DataW Ctx St W s' D n :=
  ⟨h.ok.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.ctx⟩

theorem DataW.drop {Ctx St W : Addr} {s : State} {D : Addr} {n : Nat} (h : DataW Ctx St W s D n)
    {k : Nat} (hk : k ≤ n) : DataW Ctx St W s (D + BitVec.ofNat 64 k) (n - k) :=
  ⟨h.ok.drop hk, covers_off h.wr (by omega_arith) h.ok.lt, h.ctx.sub_right (Offset.sub_base D (by omega_arith))⟩

theorem DataW.take {Ctx St W : Addr} {s : State} {D : Addr} {n : Nat} (h : DataW Ctx St W s D n)
    {k : Nat} (hk : k ≤ n) : DataW Ctx St W s D k :=
  ⟨h.ok.take hk, covers_prefix h.wr hk, h.ctx.sub_right (Region.sub_prefix hk)⟩

/-- The cipher of the key schedule in the context, for `R` rounds. -/
abbrev ciphOf (m : Mem) (Ctx : Addr) (R : Nat) : Block → Block :=
  aesWith R (bytesAt m Ctx (16 * (R + 1)))

/-- The regions `crypt` writes. -/
abbrev crFrame (St W D : Addr) (n : Nat) : List Region :=
  [⟨D, n⟩, ⟨St + BitVec.ofNat 64 48, 32⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]

/-- The bytes `crypt` XORs with the rest of the current keystream block. -/
abbrev crHead (o n : Nat) : Nat := if o = 0 then 0 else min (16 - o) n

/-- `[D, D + j)` and `[D + j, D + n)` are apart. -/
theorem split_disj {D : Addr} {j n : Nat} (hj : j ≤ n) (hn : n < 2 ^ 64) :
    (⟨D, j⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 j, n - j⟩ := by
  have := Offset.disjoint D (d := 0) (n := j) (e := j) (k := n - j) (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  simpa using this

/-- The bytes done so far and the next ones. -/
theorem done_append {m m₀ : Mem} {ciph : Block → Block} {icb : Block} {P : Nat} {D O : Addr} {j l : Nat}
    (h₁ : bytesAt m O j = xorKs ciph icb P (bytesAt m₀ D j))
    (h₂ : bytesAt m (O + BitVec.ofNat 64 j) l = xorKs ciph icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) l)) :
    bytesAt m O (j + l) = xorKs ciph icb P (bytesAt m₀ D (j + l)) := by
  rw [bytesAt_add, bytesAt_add, Proof.Gcm.xorKs_append, h₁, h₂, length_bytesAt]

theorem disjoint_zero_right {r : Region} {a : Addr} : r.Disjoint ⟨a, 0⟩ := fun _ _ h => by
  simp only [Region.Contains] at h; omega_arith

theorem zero_xor' (x : Block) : (0 : Block) ^^^ x = x := by simp

theorem ctr32_single (ciph : Block → Block) (icb x : Block) : Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

/-- With a whole number of blocks, the keystream block does not matter. -/
theorem Ctr.of_aligned {m m' : Mem} {cb ks : Addr} {ciph : Block → Block} {icb : Block} {n : Nat}
    (h : Ctr m cb ks ciph icb n) (h0 : n % 16 = 0) (hc : blockAt m' cb = blockAt m cb) :
    Ctr m' cb ks ciph icb n :=
  ⟨hc.trans h.1, fun h1 => absurd h0 h1⟩

/-- Whole blocks, from a whole number of blocks, out of place: `ctr_whole`
with the output at `op` and the text at `dp`. -/
theorem ctr_whole_to {m m' : Mem} {cb ks dp op : Addr} {ciph : Block → Block} {icb : Block} {n nb : Nat}
    (h : Ctr m cb ks ciph icb n) (h0 : n % 16 = 0)
    (hd : blocksAt m' op nb = Spec.Gcm.ctr32 ciph (blockAt m cb) (blocksAt m dp nb))
    (hc : blockAt m' cb = Nat.repeat Spec.Gcm.inc32 nb (blockAt m cb)) :
    bytesAt m' op (16 * nb) = xorKs ciph icb n (bytesAt m dp (16 * nb)) ∧ Ctr m' cb ks ciph icb (n + 16 * nb) := by
  have hcb : blockAt m cb = Nat.repeat Spec.Gcm.inc32 (n / 16) icb := by rw [h.1]; congr 1; omega
  refine ⟨?_, ?_, fun h1 => absurd (by omega) h1⟩
  · refine Proof.Gcm.list_ext (by simp [Proof.Gcm.length_xorKs, Proof.Cmac.bytesAt_length]) fun k hk => ?_
    simp only [Proof.Cmac.bytesAt_length] at hk
    rw [Proof.Gcm.getD_xorKs _ _ _ _ (by rw [Proof.Cmac.bytesAt_length]; exact hk), Proof.Gcm.getD_bytesAt' _ _ hk,
      Proof.Gcm.getD_bytesAt' _ _ hk]
    have hq : k / 16 < nb := by omega
    have e₁ := congrArg (fun L => L.getD (k / 16) 0) hd
    rw [Proof.Gcm.ctr32_getD _ _ _ (by rw [Proof.Gcm.length_blocksAt]; exact hq), Proof.Gcm.blocksAt_getD _ _ _ hq,
      Proof.Gcm.blocksAt_getD _ _ _ hq] at e₁
    have ea : ∀ p : Addr, p + BitVec.ofNat 64 k = p + BitVec.ofNat 64 (16 * (k / 16)) + BitVec.ofNat 64 (k % 16) :=
      fun p => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [ea op, ea dp, Proof.Gcm.bytes_toBytes_blockAt m' _ (by omega), Proof.Gcm.bytes_toBytes_blockAt m _ (by omega), e₁,
      Proof.Aes.toBytes_xor _ _ (by omega), Proof.Gcm.ksByte, hcb, ← Proof.Gcm.repeat_add,
      show (n + k) / 16 = k / 16 + n / 16 by omega, show (n + k) % 16 = k % 16 by omega]
  · rw [hc, hcb, ← Proof.Gcm.repeat_add]; congr 1; omega

/-- The output: in place (`to = false`) the text itself (`O = D`); out of
place a writable buffer of `n` bytes at `O`, apart from the text, with
`x26` at byte `j` of it. -/
def OutAt (to : Bool) (Ctx St W : Addr) (s : State) (D O : Addr) (n j : Nat) : Prop :=
  cond to (DataW Ctx St W s O n ∧ (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩ ∧ s.gpr .x26 = O + BitVec.ofNat 64 j)
    (O = D)

theorem OutAt.eq {Ctx St W : Addr} {s : State} {D O : Addr} {n j : Nat} (h : OutAt false Ctx St W s D O n j) :
    O = D := h

theorem OutAt.mkTo {Ctx St W : Addr} {s : State} {D O : Addr} {n j : Nat} (hw : DataW Ctx St W s O n)
    (hd : (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩) (h26 : s.gpr .x26 = O + BitVec.ofNat 64 j) :
    OutAt true Ctx St W s D O n j := And.intro hw (And.intro hd h26)

theorem OutAt.of_eq {to : Bool} {Ctx St W : Addr} {s s' : State} {D O : Addr} {n j : Nat}
    (h : OutAt to Ctx St W s D O n j) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (h26 : s'.gpr .x26 = s.gpr .x26) : OutAt to Ctx St W s' D O n j := by
  cases to
  · exact h
  · obtain ⟨hw, hd, x26⟩ := h
    exact OutAt.mkTo (hw.of_eq hrd hwr) hd (h26.trans x26)

/-- The text: in place written (`DataW`), out of place only read (`DataOk`). -/
theorem dataOk_of {to : Bool} {Ctx St W : Addr} {s : State} {D : Addr} {n : Nat}
    (h : cond to (DataOk St W s D n) (DataW Ctx St W s D n)) : DataOk St W s D n := by
  cases to
  · exact DataW.ok h
  · exact h

theorem data_of_eq {to : Bool} {Ctx St W : Addr} {s s' : State} {D : Addr} {n : Nat}
    (h : cond to (DataOk St W s D n) (DataW Ctx St W s D n)) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    cond to (DataOk St W s' D n) (DataW Ctx St W s' D n) := by
  cases to
  · exact DataW.of_eq h hrd hwr
  · exact DataOk.of_eq h hrd hwr

/-- The output is writable, in place or not. -/
theorem OutAt.dataW {to : Bool} {Ctx St W : Addr} {s : State} {D O : Addr} {n j : Nat}
    (h : OutAt to Ctx St W s D O n j) (hd : cond to (DataOk St W s D n) (DataW Ctx St W s D n)) :
    DataW Ctx St W s O n := by
  cases to
  · have e : O = D := h
    subst e
    exact hd
  · obtain ⟨hw, -, -⟩ := h
    exact hw

/-- Bytes of the output before byte `c` of the text are apart from the text
from `c` on (in place, as parts of one buffer). -/
theorem OutAt.disj {to : Bool} {Ctx St W : Addr} {s : State} {D O : Addr} {n j : Nat}
    (h : OutAt to Ctx St W s D O n j) (hn : n < 2 ^ 64) {a b c d : Nat} (hab : a + b ≤ c) (hcd : c + d ≤ n) :
    (⟨O + BitVec.ofNat 64 a, b⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 c, d⟩ := by
  cases to
  · have e : O = D := h
    subst e
    exact Offset.disjoint _ (.inl hab) (by omega_arith) (by omega_arith)
  · obtain ⟨-, hd, -⟩ := h
    exact (hd.symm.sub_left (Offset.sub_base O (by omega_arith))).sub_right (Offset.sub_base D hcd)

/-- `Kept` but for `x26`, which out of place holds the output. -/
def KeptTo (k : Reg → BitVec 64) (s : State) : Prop := ∀ r ∈ [Reg.x22, .x27, .x28], s.gpr r = k r

theorem keptG_of_eq26 {to : Bool} {k : Reg → BitVec 64} {s s' : State} (h : cond to (KeptTo k s) (Kept k s))
    (hg : ∀ r ∈ [Reg.x22, .x27, .x28], s'.gpr r = s.gpr r) (h26 : to = false → s'.gpr .x26 = s.gpr .x26) :
    cond to (KeptTo k s') (Kept k s') := by
  cases to
  · have h' : Kept k s := h
    show Kept k s'
    exact h'.of_eq fun r hr => by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hg _ (by decide)
      · exact h26 rfl
      · exact hg _ (by decide)
      · exact hg _ (by decide)
  · have h' : KeptTo k s := h
    show KeptTo k s'
    exact fun r hr => (hg r hr).trans (h' r hr)

theorem keptG_of_eq {to : Bool} {k : Reg → BitVec 64} {s s' : State} (h : cond to (KeptTo k s) (Kept k s))
    (hg : ∀ r ∈ keptRegs, s'.gpr r = s.gpr r) : cond to (KeptTo k s') (Kept k s') :=
  keptG_of_eq26 h (fun r hr => hg r (by
    simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)) (fun _ => hg _ (by decide))

theorem keptG_of_saved {to : Bool} {k : Reg → BitVec 64} {s s' : State} (h : cond to (KeptTo k s) (Kept k s))
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) : cond to (KeptTo k s') (Kept k s') :=
  keptG_of_eq h fun r hr => hg r (by
    simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
    simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)

/-- Before `crypt`: `P` bytes of text so far, `n` bytes at `D` to go, `R`
rounds, the output at `O`. -/
structure CrInG (to : Bool) (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R P : Nat) (D O : Addr) (n : Nat)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : cond to (KeptTo k s) (Kept k s)
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x23 : s.gpr .x23 = D
  x24 : s.gpr .x24 = BitVec.ofNat 64 n
  x25 : s.gpr .x25 = BitVec.ofNat 64 (P % 16)
  data : cond to (DataOk St W s D n) (DataW Ctx St W s D n)
  outAt : OutAt to Ctx St W s D O n 0

abbrev CrIn (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R P : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  CrInG false Ctx St W SP k R P D D n s

/-- Part of the way: `j` bytes done, from `m₀`. -/
structure CrMidG (to : Bool) (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat)
    (D O : Addr) (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : cond to (KeptTo k s) (Kept k s)
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  le : j ≤ n
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 j
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - j)
  x25 : s.gpr .x25 = BitVec.ofNat 64 (P % 16)
  data : cond to (DataOk St W s D n) (DataW Ctx St W s D n)
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P + j)
  done : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem O j = xorKs (ciphOf m₀ Ctx R) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (crFrame St W O n) m₀ s.mem
  outAt : OutAt to Ctx St W s D O n j

abbrev CrMid (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat) (D : Addr)
    (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop :=
  CrMidG false Ctx St W SP k R icb P D D n m₀ j s

/-- Before the first call: `CrMidG` but for `x23` and `x24` (and out of
place `x26`), which have moved past the whole blocks, and the call's
arguments. -/
structure Cr1G (to : Bool) (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat)
    (D O : Addr) (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : cond to (KeptTo k s) (Kept k s)
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  le : j ≤ n
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16))
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16)))
  x25 : s.gpr .x25 = BitVec.ofNat 64 (P % 16)
  data : cond to (DataOk St W s D n) (DataW Ctx St W s D n)
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P + j)
  done : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem O j = xorKs (ciphOf m₀ Ctx R) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (crFrame St W O n) m₀ s.mem
  call : cond to
    (CtrToCall s Ctx (St + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (O + BitVec.ofNat 64 j)
      (W + BitVec.ofNat 64 512) R ((n - j) / 16))
    (CtrCall s Ctx (St + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (W + BitVec.ofNat 64 512) R
      ((n - j) / 16))
  outAt : OutAt to Ctx St W s D O n (j + 16 * ((n - j) / 16))

abbrev Cr1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat) (D : Addr)
    (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop :=
  Cr1G false Ctx St W SP k R icb P D D n m₀ j s

/-- After `crypt`. Out of place, the keystream block holds the text XORed
in, so the counter mode's state is not kept. -/
structure CrOutG (to : Bool) (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat)
    (D O : Addr) (n : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : cond to (KeptTo k s) (Kept k s)
  x25 : s.gpr .x25 = BitVec.ofNat 64 (P % 16)
  ctr : cond to True
    (Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
      Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P + n))
  out : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem O n = xorKs (ciphOf m₀ Ctx R) icb P (bytesAt m₀ D n)
  frame : Frame (crFrame St W O n) m₀ s.mem
  outAt : cond to (DataW Ctx St W s O n ∧ (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩) (O = D)

abbrev CrOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat) (D : Addr)
    (n : Nat) (m₀ : Mem) (s : State) : Prop :=
  CrOutG false Ctx St W SP k R icb P D D n m₀ s

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

theorem ctx_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW Ctx St W s D n) :
    ∀ r ∈ crFrame St W D n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))

omit L in
theorem ciph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨Ctx, 256⟩ : Region).Disjoint r) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ciphOf m' Ctx R = ciphOf m Ctx R := by
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  simp only [ciphOf]
  rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega_arith)]

/-- The arguments of a call of `vg_aes_ctr32` on the counter block at
`St + 48`, `nb` blocks at `D'` (within the data, or the keystream block). -/
theorem ctrCall_of {R : Nat} {s : State} (he : Env Ctx St W SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D' : Addr} {nb : Nat}
    (h0 : s.gpr .x0 = Ctx) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = St + BitVec.ofNat 64 48)
    (h3 : s.gpr .x3 = D') (h4 : s.gpr .x4 = BitVec.ofNat 64 nb) (h5 : s.gpr .x5 = W + BitVec.ofNat 64 512)
    (hwrap : D'.toNat + 16 * nb ≤ 2 ^ 64)
    (hkd : (⟨Ctx, 240⟩ : Region).Disjoint ⟨D', 16 * nb⟩)
    (hcd : (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨D', 16 * nb⟩)
    (hds : (⟨D', 16 * nb⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩)
    (hdw : Covers [⟨D', 16 * nb⟩] s.wr) :
    CtrCall s Ctx (St + BitVec.ofNat 64 48) D' (W + BitVec.ofNat 64 512) R nb := by
  refine ⟨h0, h1, h2, h3, h4, h5, hR, hwrap, by omega_arith,
    (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)), hkd,
    L.cw'.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Lay.wSub (by decide)),
    hcd, L.st_w (by decide) (.inr ⟨by decide, by decide⟩), hds, ?_, ?_⟩
  · refine covers_cons ?_ (covers_cons (covers_left (he.perm.stC (by decide))) (covers_cons
      (covers_left hdw) (covers_left (he.perm.wC (by decide)))))
    exact fun a m' ⟨r, hr, hc'⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact he.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega_arith⟩
  · exact covers_cons (he.perm.stC (by decide)) (covers_cons hdw (he.perm.wC (by decide)))

omit L in
theorem ctrArgs_eq (rest : List Instr) :
    ctrArgs ++ rest = mov .x0 .x21 :: mov .x1 .x22 :: ptr .x2 .x20 48 :: ptr .x5 .x19 scrO :: rest := rfl

/-- The arguments of a call of `vg_aes_ctr32_to` on the counter block at
`St + 48`, `nb` blocks read at `D'` and written at `O'`. -/
theorem ctrToCall_of {R : Nat} {s : State} (he : Env Ctx St W SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D' O' : Addr} {nb : Nat}
    (h0 : s.gpr .x0 = Ctx) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = St + BitVec.ofNat 64 48)
    (h3 : s.gpr .x3 = D') (h4 : s.gpr .x4 = BitVec.ofNat 64 nb) (h5 : s.gpr .x5 = W + BitVec.ofNat 64 512)
    (h6 : s.gpr .x6 = O')
    (hwrap : D'.toNat + 16 * nb ≤ 2 ^ 64) (hwrapO : O'.toNat + 16 * nb ≤ 2 ^ 64)
    (hko : (⟨Ctx, 240⟩ : Region).Disjoint ⟨O', 16 * nb⟩)
    (hcd : (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨D', 16 * nb⟩)
    (hco : (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨O', 16 * nb⟩)
    (hdo : (⟨D', 16 * nb⟩ : Region).Disjoint ⟨O', 16 * nb⟩)
    (hds : (⟨D', 16 * nb⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩)
    (hos : (⟨O', 16 * nb⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩)
    (hdr : Covers [⟨D', 16 * nb⟩] (s.rd ++ s.wr)) (how : Covers [⟨O', 16 * nb⟩] s.wr) :
    CtrToCall s Ctx (St + BitVec.ofNat 64 48) D' O' (W + BitVec.ofNat 64 512) R nb := by
  refine ⟨h0, h1, h2, h3, h4, h5, h6, hR, hwrap, hwrapO, by omega_arith,
    (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)), hko,
    L.cw'.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Lay.wSub (by decide)),
    hcd, hco, L.st_w (by decide) (.inr ⟨by decide, by decide⟩), hdo, hds, hos, ?_, ?_⟩
  · refine covers_cons ?_ (covers_cons hdr (covers_cons (covers_left (he.perm.stC (by decide))) (covers_cons
      (covers_left how) (covers_left (he.perm.wC (by decide))))))
    exact fun a m' ⟨r, hr, hc'⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact he.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega_arith⟩
  · exact covers_cons (he.perm.stC (by decide)) (covers_cons how (he.perm.wC (by decide)))

/-- The arguments of the first call, from the text from byte `j` on and the
output: `nb` whole blocks at `D + j`, written in place or at `O + j`. -/
theorem crCallG_of {to : Bool} {R : Nat} {s : State} (he : Env Ctx St W SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D O : Addr} {n j j' nb : Nat} (hle : j ≤ n) (h16 : 16 * nb ≤ n - j)
    (hd : cond to (DataOk St W s D n) (DataW Ctx St W s D n)) (ho : OutAt to Ctx St W s D O n j')
    (h0 : s.gpr .x0 = Ctx) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = St + BitVec.ofNat 64 48)
    (h3 : s.gpr .x3 = D + BitVec.ofNat 64 j) (h4 : s.gpr .x4 = BitVec.ofNat 64 nb)
    (h5 : s.gpr .x5 = W + BitVec.ofNat 64 512) (h6 : to = true → s.gpr .x6 = O + BitVec.ofNat 64 j) :
    cond to
      (CtrToCall s Ctx (St + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (O + BitVec.ofNat 64 j)
        (W + BitVec.ofNat 64 512) R nb)
      (CtrCall s Ctx (St + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (W + BitVec.ofNat 64 512) R nb) := by
  cases to
  · have hdj := (DataW.drop hd hle).take (k := 16 * nb) h16
    exact ctrCall_of L he hR h0 h1 h2 h3 h4 h5 hdj.ok.wrap
      (hdj.ctx.sub_left (Region.sub_prefix (by decide))) (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
      (hdj.ok.w.sub_right (Lay.wSub (by decide))) hdj.wr
  · have hd' : DataOk St W s D n := hd
    have hn := hd'.lt
    obtain ⟨hw, hdo, -⟩ := ho
    have hdj := (hd'.drop hle).take (k := 16 * nb) h16
    have hoj := (hw.drop hle).take (k := 16 * nb) h16
    exact ctrToCall_of L he hR h0 h1 h2 h3 h4 h5 (h6 rfl) hdj.wrap hoj.ok.wrap
      (hoj.ctx.sub_left (Region.sub_prefix (by decide))) (hdj.st.sub_right (Lay.stSub (by decide))).symm
      (hoj.ok.st.sub_right (Lay.stSub (by decide))).symm
      ((hdo.sub_left (Offset.sub_base D (by omega_arith))).sub_right (Offset.sub_base O (by omega_arith)))
      (hdj.w.sub_right (Lay.wSub (by decide))) (hoj.ok.w.sub_right (Lay.wSub (by decide))) hdj.rd hoj.wr

omit L in
/-- A call of `vg_aes_ctr32` in place, or of `vg_aes_ctr32_to`: what
`vg_aes_ctr32_to` leaves. -/
theorem ctrCallG_post (v : GcmImpl) {to : Bool} {s : State} {K C D O S : Addr} {R n : Nat}
    (h : cond to (CtrToCall s K C D O S R n) (CtrCall s K C D S R n)) (ho : to = false → O = D) :
    WP isa (ctrCallG v.callees to) s (CtrToPost s K C D O S R n) := by
  cases to
  · obtain rfl := ho rfl
    exact WP.mono (ctr_call v.ctr h) fun _ g => ⟨g.rd, g.wr, g.sp, g.saved, g.frame, g.out, g.ctr⟩
  · exact ctrTo_call v.ctr h

/-- The rest of the keystream block, and the arguments for the whole blocks. -/
theorem crSeg1_ok {k : Reg → BitVec 64} {R P : Nat} {icb : Block} {D : Addr} {n : Nat} {s : State}
    (h : CrIn Ctx St W SP k R P D n s) :
    WP isa crSeg1 s (Cr1 Ctx St W SP k R icb P D n s.mem (crHead (P % 16) n)) := by
  have hlt : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.ok.lt
  have he := h.env
  have hkn : crHead (P % 16) n ≤ n := by
    simp only [crHead]; split
    · omega_arith
    · exact Nat.min_le_right _ _
  have hk16 : P % 16 + crHead (P % 16) n ≤ 16 := by
    simp only [crHead]; split
    · omega_arith
    · have := Nat.min_le_left (16 - P % 16) n; omega_arith
  -- `x10 := crHead`.
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => s₁.gpr .x10 = BitVec.ofNat 64 (crHead (P % 16) n) ∧
      Regs minRegs s s₁)
    (WP.ite (decide (P % 16 = 0)) (eval_zero h.x25 (by omega_arith)) (fun ht => ?_) (fun hf => ?_))
    fun s₁ ⟨x10₁, r₁⟩ => ?_)
  · have h0 : P % 16 = 0 := by simpa using ht
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'; exact ⟨by simp [gpr_write, crHead, h0], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · have h0 : P % 16 ≠ 0 := by simpa using hf
    exact WP.mono (minK_ok s h.x25 h.x24 hlt hn') fun s' ⟨x10', g', m', sp', rd', wr'⟩ =>
      ⟨by rw [x10']; simp [crHead, h0], ⟨g', m', sp', rd', wr'⟩⟩
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, r₂⟩ : ∃ s₂, runBlock isa
      [.add .x .x11 .x20 .x25, ptr .x11 .x11 64, mov .x12 .x23, mov .x13 .x10] s₁ = some s₂ ∧
      s₂.gpr .x11 = St + BitVec.ofNat 64 (64 + P % 16) ∧ s₂.gpr .x12 = D ∧
      s₂.gpr .x13 = BitVec.ofNat 64 (crHead (P % 16) n) ∧ Regs [.x11, .x12, .x13] s₁ s₂ := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, r₁.others .x20 (by decide), r₁.others .x25 (by decide), he.x20, h.x25,
        add_ofNat_assoc, Nat.add_comm]
    · simp [gpr_write, r₁.others .x23 (by decide), h.x23]
    · simp [gpr_write, x10₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have r₁₂ := r₁.comp r₂
  have hdk := h.data.take hkn
  have lp : LoopPre s₂ (St + BitVec.ofNat 64 (64 + P % 16)) D (crHead (P % 16) n) := by
    refine ⟨by omega_arith, ?_, ?_, ?_⟩
    · rw [r₁₂.rd, r₁₂.wr]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [r₁₂.wr]; exact hdk.wr
    · exact (hdk.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.seq (WP.mono (xorB_ok s₂ x11₂ x12₂ x13₂ lp) fun s₃ ⟨m₃, g₃, sp₃, rd₃, wr₃⟩ => ?_)
  rw [r₁₂.mem] at m₃
  have gg₃ : ∀ r, r ∉ minRegs ++ [.x11, .x12, .x13] ++ loopRegs → s₃.gpr r = s.gpr r := fun r hr => by
    rw [g₃ r (fun h' => hr (List.mem_append_right _ h')), r₁₂.others r (fun h' => hr (List.mem_append_left _ h'))]
  have e10 : s₃.gpr .x10 = BitVec.ofNat 64 (crHead (P % 16) n) := by
    rw [g₃ _ (by decide), r₂.others _ (by decide), x10₁]
  generalize hj : crHead (P % 16) n = j at *
  generalize hnb : (n - j) / 16 = nb
  have h16 : 16 * nb ≤ n - j := by omega_arith
  obtain ⟨s₄, run₄, x3₄, x4₄, x0₄, x1₄, x2₄, x5₄, x23₄, x24₄, r₄⟩ : ∃ s₄, runBlock isa
      ([.add .x .x23 .x23 .x10, .sub .x .x24 .x24 .x10, .lsr .x .x4 .x24 4, mov .x3 .x23] ++ ctrArgs ++
        [.lsl .x .x9 .x4 4, .add .x .x23 .x23 .x9, .sub .x .x24 .x24 .x9]) s₃ = some s₄ ∧
      s₄.gpr .x3 = D + BitVec.ofNat 64 j ∧ s₄.gpr .x4 = BitVec.ofNat 64 nb ∧ s₄.gpr .x0 = Ctx ∧
      s₄.gpr .x1 = BitVec.ofNat 64 R ∧ s₄.gpr .x2 = St + BitVec.ofNat 64 48 ∧
      s₄.gpr .x5 = W + BitVec.ofNat 64 512 ∧ s₄.gpr .x23 = D + BitVec.ofNat 64 (j + 16 * nb) ∧
      s₄.gpr .x24 = BitVec.ofNat 64 (n - (j + 16 * nb)) ∧
      Regs [.x23, .x24, .x4, .x3, .x0, .x1, .x2, .x5, .x9] s₃ s₄ := by
    have e23 := gg₃ .x23 (by decide); have e24 := gg₃ .x24 (by decide)
    refine ⟨_, by rw [List.append_assoc, ctrArgs_eq]; arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, e10, e23, h.x23]
    · simp [gpr_write, e10, e24, h.x24, ofNat_sub hkn hn', lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega_arith), hnb]
    · simp [gpr_write, gg₃ .x21 (by decide), he.x21]
    · simp [gpr_write, gg₃ .x22 (by decide), h.x22]
    · simp [gpr_write, gg₃ .x20 (by decide), he.x20]
    · simp [gpr_write, gg₃ .x19 (by decide), he.x19]
    · simp [gpr_write, e10, e23, e24, h.x23, h.x24, ofNat_sub hkn hn',
        lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega_arith), hnb, lsl4_ofNat, add_ofNat_assoc]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, e10, e24, h.x24, BitVec.setWidth_eq,
        ofNat_sub hkn hn', lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega_arith), hnb, lsl4_ofNat]
      rw [ofNat_sub (by omega_arith) (by omega_arith)]
      congr 1
      omega_arith
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have ggA : ∀ r, r ∉ minRegs ++ [.x11, .x12, .x13] ++ loopRegs ++ [.x23, .x24, .x4, .x3, .x0, .x1, .x2, .x5, .x9] →
      s₄.gpr r = s.gpr r := fun r hr => by
    rw [r₄.others r (fun h' => hr (List.mem_append_right _ h')), gg₃ r (fun h' => hr (List.mem_append_left _ h'))]
  have hsp : s₄.sp = s.sp := by rw [r₄.sp, sp₃, r₁₂.sp]
  have hrd : s₄.rd = s.rd := by rw [r₄.rd, rd₃, r₁₂.rd]
  have hwr : s₄.wr = s.wr := by rw [r₄.wr, wr₃, r₁₂.wr]
  have he₄ : Env Ctx St W SP s₄ := he.keep (fun r hr => ggA r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) hsp hrd hwr
  have hd₄ : DataW Ctx St W s₄ D n := h.data.of_eq hrd hwr
  have hm₄ : s₄.mem = writeBytes s.mem D (xorBytes s.mem D (St + BitVec.ofNat 64 (64 + P % 16)) j) := by
    rw [r₄.mem, m₃]
  have hxl := length_xorBytes s.mem D (St + BitVec.ofNat 64 (64 + P % 16)) j
  have fw : Frame [⟨D, j⟩] s.mem s₄.mem := by rw [hm₄]; exact writeBytes_frame' _ hxl
  have hdisjst : ∀ r ∈ [(⟨D, j⟩ : Region)], (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨St + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(hdk.ok.st.sub_right (Lay.stSub (by decide))).symm, (hdk.ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  have hdj := (hd₄.drop hkn).take (k := 16 * nb) h16
  refine ⟨he₄, h.kept.of_eq fun r hr => ggA r (by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [ggA _ (by decide), h.x22], h.rounds, hkn, by rw [hnb]; exact x23₄, by rw [hnb]; exact x24₄,
    by rw [ggA _ (by decide), h.x25], hd₄, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro hc₀
    by_cases h0 : P % 16 = 0
    · have hj0 : j = 0 := by rw [← hj]; simp [crHead, h0]
      subst hj0
      exact hc₀.congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
        (blockAt_frame fw fun r hr => (hdisjst r hr).2)
    · exact (hc₀.head h0 hk16).congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
        (blockAt_frame fw fun r hr => (hdisjst r hr).2)
  · intro hc₀
    by_cases h0 : P % 16 = 0
    · have hj0 : j = 0 := by rw [← hj]; simp [crHead, h0]
      subst hj0
      rfl
    · have e := bytesAt_writeBytes_self s.mem D (xorBytes s.mem D (St + BitVec.ofNat 64 (64 + P % 16)) j)
        (by rw [hxl]; omega_arith)
      rw [hxl] at e
      rw [hm₄, e, xorBytes]
      have := Proof.Gcm.ctr_head hc₀ h0 (d := bytesAt s.mem D j) (by rw [length_bytesAt]; exact hk16)
      rw [length_bytesAt, add_ofNat_assoc] at this
      exact this
  · exact bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (split_disj hkn hn').symm) (by omega_arith)
  · by_cases h0 : P % 16 = 0
    · have hj0 : j = 0 := by rw [← hj]; simp [crHead, h0]
      exact .inr (by omega_arith)
    · by_cases hkk : j = n
      · exact .inl (by omega_arith)
      · refine .inr ?_
        rw [← hj] at hkk ⊢
        simp only [crHead, h0, ↓reduceIte] at hkk ⊢
        omega_arith
  · exact fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hkn⟩
  · rw [hnb]
    exact ctrCall_of L he₄ h.rounds x0₄ x1₄ x2₄ x3₄ x4₄ x5₄ hdj.ok.wrap
      (hdj.ctx.sub_left (Region.sub_prefix (by decide))) (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
      (hdj.ok.w.sub_right (Lay.wSub (by decide))) hdj.wr

/-- The first call: the whole blocks. -/
theorem ctrCallG1_ok (v : GcmImpl) {to : Bool} {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat}
    {D O : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State} (h : Cr1G to Ctx St W SP k R icb P D O n m₀ j s)
    (hc : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R) :
    WP isa (ctrCallG v.callees to) s fun s' =>
      CrMidG to Ctx St W SP k R icb P D O n m₀ (j + 16 * ((n - j) / 16)) s' ∧ n - (j + 16 * ((n - j) / 16)) < 16 := by
  have hdk := dataOk_of h.data
  have hn' := hdk.lt
  have hle := h.le
  have hdO := OutAt.dataW h.outAt h.data
  refine WP.mono (ctrCallG_post v h.call fun hf => by subst hf; rw [OutAt.eq h.outAt]) fun s₃ g => ?_
  have ho := h.outAt
  generalize hnb : (n - j) / 16 = nb at *
  have h16 : 16 * nb ≤ n - j := by omega_arith
  have gout : blocksAt s₃.mem (O + BitVec.ofNat 64 j) nb = Spec.Gcm.ctr32 (ciphOf m₀ Ctx R)
      (blockAt s.mem (St + BitVec.ofNat 64 48)) (blocksAt s.mem (D + BitVec.ofNat 64 j) nb) := by
    rw [← hc]; exact g.out
  have gctr := g.ctr
  -- The whole blocks, if there are any.
  have hcw : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
      bytesAt s₃.mem (O + BitVec.ofNat 64 j) (16 * nb) =
        xorKs (ciphOf m₀ Ctx R) icb (P + j) (bytesAt s.mem (D + BitVec.ofNat 64 j) (16 * nb)) ∧
      Ctr s₃.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P + j + 16 * nb) := by
    intro hc₀
    by_cases h0 : nb = 0
    · subst h0
      have hks : blockAt s₃.mem (St + BitVec.ofNat 64 64) = blockAt s.mem (St + BitVec.ofNat 64 64) :=
        blockAt_frame g.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact L.st_st (.inr (by decide)) (by decide) (by decide)
          · exact disjoint_zero_right
          · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      refine ⟨by simp [bytesAt, xorKs], ?_⟩
      simp only [Nat.mul_zero, Nat.add_zero]
      exact (h.ctr hc₀).congr (by rw [gctr]; rfl) hks
    · have hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega_arith)
      exact ctr_whole_to (h.ctr hc₀) hw gout gctr
  refine ⟨⟨h.env.of_saved g.saved g.sp g.rd g.wr, keptG_of_saved h.kept g.saved,
    by rw [g.saved _ (by decide) (by decide), h.x22], h.rounds,
    by omega_arith, by rw [g.saved _ (by decide) (by decide), h.x23, hnb],
    by rw [g.saved _ (by decide) (by decide), h.x24, hnb],
    by rw [g.saved _ (by decide) (by decide), h.x25], data_of_eq h.data g.rd g.wr,
    fun hc₀ => by rw [← Nat.add_assoc]; exact (hcw hc₀).2, fun hc₀ => ?_, ?_, ?_, ?_,
    OutAt.of_eq ho g.rd g.wr (g.saved _ (by decide) (by decide))⟩, by omega_arith⟩
  · -- The bytes done.
    have hj16 : bytesAt s₃.mem (O + BitVec.ofNat 64 j) (16 * nb) =
        xorKs (ciphOf m₀ Ctx R) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * nb)) := by
      rw [(hcw hc₀).1]
      congr 1
      have e := congrArg (List.take (16 * nb)) h.rest
      rwa [bytesAt_take _ _ h16, bytesAt_take _ _ h16] at e
    have hOj := hdO.take h.le
    have hjd : bytesAt s₃.mem O j = bytesAt s.mem O j := bytesAt_frame g.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hOj.ok.st.sub_right (Lay.stSub (by decide))
      · exact split_disj (D := O) (j := j) (n := n) h.le hn' |>.sub_right (Region.sub_prefix (by omega_arith))
      · exact hOj.ok.w.sub_right (Lay.wSub (by decide))) (by omega_arith)
    exact done_append (hjd.trans (h.done hc₀)) hj16
  · -- The bytes left.
    have hdis : ∀ r ∈ [⟨St + BitVec.ofNat 64 48, 16⟩, ⟨O + BitVec.ofNat 64 j, 16 * nb⟩,
        ⟨W + BitVec.ofNat 64 512, 2048⟩],
        (⟨D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ : Region).Disjoint r := by
      have hrest := hdk.drop (k := j + 16 * nb) (by omega_arith)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hrest.st.sub_right (Lay.stSub (by decide))
      · exact (OutAt.disj h.outAt hn' (Nat.le_refl _) (by omega_arith)).symm
      · exact hrest.w.sub_right (Lay.wSub (by decide))
    rw [bytesAt_frame g.frame hdis (by omega_arith)]
    have e := congrArg (List.drop (16 * nb)) h.rest
    rw [bytesAt_drop _ _ h16, bytesAt_drop _ _ h16, add_ofNat_assoc,
      show n - j - 16 * nb = n - (j + 16 * nb) by omega_arith] at e
    exact e
  · by_cases h0 : n - j = 0
    · exact .inl (by omega_arith)
    · exact .inr (by have := h.whole.resolve_left h0; omega_arith)
  · refine h.frame.trans (g.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., (Offset.sub_base O (by omega_arith))⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩

/-- The first call in place: the whole blocks. -/
theorem ctrCall1_ok (v : GcmImpl) {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : Cr1 Ctx St W SP k R icb P D n m₀ j s)
    (hc : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R) :
    WP isa (ctrCall v.callees) s fun s' =>
      CrMid Ctx St W SP k R icb P D n m₀ (j + 16 * ((n - j) / 16)) s' ∧ n - (j + 16 * ((n - j) / 16)) < 16 :=
  ctrCallG1_ok L v h hc

end

/-- Before the second call: a zero keystream block if there are bytes left,
and the call's arguments. -/
structure Cr2G (to : Bool) (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat)
    (D O : Addr) (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : cond to (KeptTo k s) (Kept k s)
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  le : j ≤ n
  lt16 : n - j < 16
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 j
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - j)
  x25 : s.gpr .x25 = BitVec.ofNat 64 (P % 16)
  data : cond to (DataOk St W s D n) (DataW Ctx St W s D n)
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P + j)
  ks0 : n - j ≠ 0 → blockAt s.mem (St + BitVec.ofNat 64 64) = 0
  done : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem O j = xorKs (ciphOf m₀ Ctx R) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (crFrame St W O n) m₀ s.mem
  call : CtrCall s Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 512) R
    (if n - j = 0 then 0 else 1)
  outAt : OutAt to Ctx St W s D O n j

abbrev Cr2 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat) (D : Addr)
    (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop :=
  Cr2G false Ctx St W SP k R icb P D D n m₀ j s

/-- After the second call: a new keystream block, if there are bytes left. -/
structure Cr3G (to : Bool) (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat)
    (D O : Addr) (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : cond to (KeptTo k s) (Kept k s)
  le : j ≤ n
  lt16 : n - j < 16
  x23 : s.gpr .x23 = D + BitVec.ofNat 64 j
  x24 : s.gpr .x24 = BitVec.ofNat 64 (n - j)
  x25 : s.gpr .x25 = BitVec.ofNat 64 (P % 16)
  data : cond to (DataOk St W s D n) (DataW Ctx St W s D n)
  ctr0 : n - j = 0 → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P + j)
  ctr1 : n - j ≠ 0 → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    ∃ mc : Mem, Ctr mc (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P + j) ∧
      blockAt s.mem (St + BitVec.ofNat 64 64) = ciphOf m₀ Ctx R (blockAt mc (St + BitVec.ofNat 64 48)) ∧
      blockAt s.mem (St + BitVec.ofNat 64 48) = Spec.Gcm.inc32 (blockAt mc (St + BitVec.ofNat 64 48))
  done : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem O j = xorKs (ciphOf m₀ Ctx R) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (crFrame St W O n) m₀ s.mem
  outAt : OutAt to Ctx St W s D O n j

abbrev Cr3 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block) (P : Nat) (D : Addr)
    (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop :=
  Cr3G false Ctx St W SP k R icb P D D n m₀ j s

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- The arguments for a new keystream block. -/
theorem crSeg2_ok {to : Bool} {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D O : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : CrMidG to Ctx St W SP k R icb P D O n m₀ j s) (hj : n - j < 16) :
    WP isa crSeg2 s (Cr2G to Ctx St W SP k R icb P D O n m₀ j) := by
  have hdk := dataOk_of h.data
  have hdO := OutAt.dataW h.outAt h.data
  have hn' := hdk.lt
  have hle := h.le
  have he := h.env
  have w₁ := he.perm.stW (show 64 + 8 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 72 + 8 ≤ 80 by decide)
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => s₁.gpr .x4 = BitVec.ofNat 64 (if n - j = 0 then 0 else 1) ∧
      Others [.x4, .x9] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      (n - j = 0 → s₁.mem = s.mem) ∧
      (n - j ≠ 0 → s₁.mem = (s.mem.writeW (St + BitVec.ofNat 64 64) (0 : BitVec 64)).writeW
        (St + BitVec.ofNat 64 72) (0 : BitVec 64)))
    (WP.ite (decide (n - j = 0)) (eval_zero h.x24 (by omega_arith)) (fun ht => ?_) (fun hf => ?_))
    fun s₁ ⟨x4₁, g₁, sp₁, rd₁, wr₁, m0₁, m1₁⟩ => ?_)
  · have h0 : n - j = 0 := by simpa using ht
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'
      exact ⟨by simp [gpr_write, h0], by others_tac, rfl, rfl, rfl, fun _ => rfl, fun h' => absurd h0 h'⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    exact WP.run ⟨_, by arun [he.x20, w₁, w₂], rfl⟩ fun s' hs' => by
      subst hs'
      refine ⟨by simp [gpr_write, h0], by others_tac, rfl, rfl, rfl, fun h' => absurd h' h0, fun _ => ?_⟩
      simp only [mem_write]
      rfl
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x5₂, x3₂, r₂⟩ : ∃ s₂, runBlock isa (ctrArgs ++ [ptr .x3 .x20 64]) s₁ =
      some s₂ ∧ s₂.gpr .x0 = Ctx ∧ s₂.gpr .x1 = BitVec.ofNat 64 R ∧ s₂.gpr .x2 = St + BitVec.ofNat 64 48 ∧
      s₂.gpr .x5 = W + BitVec.ofNat 64 512 ∧ s₂.gpr .x3 = St + BitVec.ofNat 64 64 ∧
      Regs [.x0, .x1, .x2, .x5, .x3] s₁ s₂ := by
    refine ⟨_, by rw [ctrArgs_eq]; arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, g₁ .x21 (by decide), he.x21]
    · simp [gpr_write, g₁ .x22 (by decide), h.x22]
    · simp [gpr_write, g₁ .x20 (by decide), he.x20]
    · simp [gpr_write, g₁ .x19 (by decide), he.x19]
    · simp [gpr_write, g₁ .x20 (by decide), he.x20]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have gg : ∀ r, r ∉ [Reg.x4, .x9] ++ [.x0, .x1, .x2, .x5, .x3] → s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (fun h' => hr (List.mem_append_right _ h')), g₁ r (fun h' => hr (List.mem_append_left _ h'))]
  have hsp : s₂.sp = s.sp := by rw [r₂.sp, sp₁]
  have hrd : s₂.rd = s.rd := by rw [r₂.rd, rd₁]
  have hwr : s₂.wr = s.wr := by rw [r₂.wr, wr₁]
  have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => gg r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) hsp hrd hwr
  -- The memory: the keystream block zeroed if there are bytes left.
  have fz : Frame [⟨St + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by
    rw [r₂.mem]
    by_cases h0 : n - j = 0
    · rw [m0₁ h0]; exact Frame.refl _ _
    · rw [m1₁ h0, show St + BitVec.ofNat 64 72 = St + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 by
        rw [BitVec.add_assoc]; rfl]
      exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ {X : Addr}, DataOk St W s X n →
      ∀ r ∈ [(⟨St + BitVec.ofNat 64 64, 16⟩ : Region)], (⟨X, n⟩ : Region).Disjoint r := by
    intro X hX r hr; simp only [List.mem_singleton] at hr; subst hr; exact hX.st.sub_right (Lay.stSub (by decide))
  have hdD : ∀ {X : Addr}, DataOk St W s X n → ∀ (q : Addr) (l : Nat), Region.Sub ⟨q, l⟩ ⟨X, n⟩ → l ≤ n →
      bytesAt s₂.mem q l = bytesAt s.mem q l :=
    fun hX q l hs hl => bytesAt_frame fz (fun r hr => (dD hX r hr).sub_left hs) (by omega_arith)
  refine ⟨he₂, keptG_of_eq h.kept fun r hr => gg r (by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [gg _ (by decide), h.x22], h.rounds, h.le, hj, by rw [gg _ (by decide), h.x23],
    by rw [gg _ (by decide), h.x24], by rw [gg _ (by decide), h.x25], data_of_eq h.data hrd hwr, fun hc₀ => ?_, ?_,
    fun hc₀ => by rw [hdD hdO.ok _ _ (Region.sub_prefix h.le) h.le]; exact h.done hc₀,
    by rw [hdD hdk _ _ (Offset.sub_base D (by omega_arith)) (by omega_arith)]; exact h.rest, h.whole,
    h.frame.trans (fz.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩), ?_,
    OutAt.of_eq h.outAt hrd hwr (gg _ (by decide))⟩
  · have hcb : blockAt s₂.mem (St + BitVec.ofNat 64 48) = blockAt s.mem (St + BitVec.ofNat 64 48) :=
      blockAt_frame fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by decide)) (by decide) (by decide)
    by_cases h0 : n - j = 0
    · exact (h.ctr hc₀).congr hcb (by rw [r₂.mem, m0₁ h0])
    · exact Ctr.of_aligned (h.ctr hc₀) (h.whole.resolve_left h0) hcb
  · intro h0
    rw [r₂.mem, m1₁ h0, show St + BitVec.ofNat 64 72 = St + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 by
      rw [BitVec.add_assoc]; rfl, Spec.Gcm.blockAt, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  · have hnb : (if n - j = 0 then 0 else 1) ≤ 1 := by split <;> omega_arith
    exact ctrCall_of L he₂ h.rounds x0₂ x1₂ x2₂ x3₂ (by rw [r₂.others _ (by decide), x4₁]) x5₂
      (by have := L.sw; rw [BitVec.toNat_add, toNat_ofNat_of_lt (by decide)]; omega_arith)
      ((L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by omega_arith)))
      (L.st_st (.inl (by decide)) (by decide) (by omega_arith))
      (L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)) (he₂.perm.stC (by omega_arith))

/-- The second call: a new keystream block, if there are bytes left. -/
theorem ctrCall2_ok (v : GcmImpl) {to : Bool} {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat}
    {D O : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State} (h : Cr2G to Ctx St W SP k R icb P D O n m₀ j s)
    (hc : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R) :
    WP isa (ctrCall v.callees) s (Cr3G to Ctx St W SP k R icb P D O n m₀ j) := by
  have hdk := dataOk_of h.data
  have hdO := OutAt.dataW h.outAt h.data
  have hn' := hdk.lt
  have hle := h.le
  refine WP.mono (ctr_call v.ctr h.call) fun s₃ g => ?_
  have dD : ∀ {X : Addr}, DataOk St W s X n → ∀ r ∈ [⟨St + BitVec.ofNat 64 48, 16⟩,
      ⟨St + BitVec.ofNat 64 64, 16 * (if n - j = 0 then 0 else 1)⟩,
      ⟨W + BitVec.ofNat 64 512, 2048⟩], (⟨X, n⟩ : Region).Disjoint r := by
    intro X hX r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hX.st.sub_right (Lay.stSub (by decide))
    · exact hX.st.sub_right (Lay.stSub (by split <;> omega_arith))
    · exact hX.w.sub_right (Lay.wSub (by decide))
  have hdD : ∀ {X : Addr}, DataOk St W s X n → ∀ (q : Addr) (l : Nat), Region.Sub ⟨q, l⟩ ⟨X, n⟩ → l ≤ n →
      bytesAt s₃.mem q l = bytesAt s.mem q l :=
    fun hX q l hs hl => bytesAt_frame g.frame (fun r hr => (dD hX r hr).sub_left hs) (by omega_arith)
  refine ⟨h.env.of_saved g.saved g.sp g.rd g.wr, keptG_of_saved h.kept g.saved, h.le, h.lt16,
    by rw [g.saved _ (by decide) (by decide), h.x23], by rw [g.saved _ (by decide) (by decide), h.x24],
    by rw [g.saved _ (by decide) (by decide), h.x25], data_of_eq h.data g.rd g.wr, fun h0 hc₀ => ?_,
    fun h0 hc₀ => ?_,
    fun hc₀ => by rw [hdD hdO.ok _ _ (Region.sub_prefix h.le) h.le]; exact h.done hc₀,
    by rw [hdD hdk _ _ (Offset.sub_base D (by omega_arith)) (by omega_arith)]; exact h.rest, h.whole,
    h.frame.trans (g.frame.sub fun r hr => ?_),
    OutAt.of_eq h.outAt g.rd g.wr (g.saved _ (by decide) (by decide))⟩
  · have gc := g.ctr
    simp only [h0, ↓reduceIte] at gc
    have hks : blockAt s₃.mem (St + BitVec.ofNat 64 64) = blockAt s.mem (St + BitVec.ofNat 64 64) :=
      blockAt_frame g.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.st_st (.inr (by decide)) (by decide) (by decide)
        · simp only [h0, ↓reduceIte]; exact disjoint_zero_right
        · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    exact (h.ctr hc₀).congr gc hks
  · refine ⟨s.mem, h.ctr hc₀, ?_, ?_⟩
    · have go := g.out
      simp only [h0, ↓reduceIte, blocksAt_one, ctr32_single, List.cons.injEq, and_true] at go
      rw [go, h.ks0 h0, zero_xor', show Spec.Gcm.aesWith R (bytesAt s.mem Ctx (16 * (R + 1))) =
        ciphOf s.mem Ctx R from rfl, hc]
    · have gc := g.ctr
      simp only [h0, ↓reduceIte] at gc
      rw [gc]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by split <;> omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩

omit L in
/-- After the last bytes are XORed with the new keystream block (by `crTail`,
or by any code leaving that memory and the registers `CrOut` reads). -/
theorem crOut_of_xor {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s s₂ : State} (h : Cr3 Ctx St W SP k R icb P D n m₀ j s)
    (m₂ : s₂.mem = writeBytes s.mem (D + BitVec.ofNat 64 j)
      (xorBytes s.mem (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 64) (n - j)))
    (gg : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x25, .x26, .x27, .x28], s₂.gpr r = s.gpr r)
    (sp₂ : s₂.sp = s.sp) (rd₂ : s₂.rd = s.rd) (wr₂ : s₂.wr = s.wr) :
    CrOut Ctx St W SP k R icb P D n m₀ s₂ := by
  have hn' := h.data.ok.lt
  have hle := h.le
  have hj := h.lt16
  have he := h.env
  have hdj := h.data.drop h.le
  have hxl := length_xorBytes s.mem (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 64) (n - j)
  have fw : Frame [⟨D + BitVec.ofNat 64 j, n - j⟩] s.mem s₂.mem := by rw [m₂]; exact writeBytes_frame' _ hxl
  have dst : ∀ r ∈ [(⟨D + BitVec.ofNat 64 j, n - j⟩ : Region)], (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨St + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(hdj.ok.st.sub_right (Lay.stSub (by decide))).symm, (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  have hD : bytesAt s₂.mem D j = bytesAt s.mem D j := bytesAt_frame fw (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact split_disj h.le hn') (by omega_arith)
  -- The tail, from a new keystream block.
  have htail : n - j ≠ 0 → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
      bytesAt s₂.mem (D + BitVec.ofNat 64 j) (n - j) =
        xorKs (ciphOf m₀ Ctx R) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) ∧
      Ctr s₂.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P + n) := by
    intro h0 hc₀
    obtain ⟨mc, hmc, hks, hcb⟩ := h.ctr1 h0 hc₀
    have hw : (P + j) % 16 = 0 := h.whole.resolve_left h0
    obtain ⟨t₁, t₂⟩ := Proof.Gcm.ctr_tail hmc hw hks hcb (d := bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j))
      (by rw [length_bytesAt]; omega_arith) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at t₁ t₂
    refine ⟨?_, ?_⟩
    · have e := bytesAt_writeBytes_self s.mem (D + BitVec.ofNat 64 j)
        (xorBytes s.mem (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 64) (n - j)) (by rw [hxl]; omega_arith)
      rw [hxl] at e
      rw [m₂, e, xorBytes, t₁, h.rest]
    · rw [show P + n = P + j + (n - j) by omega_arith]
      exact t₂.congr (blockAt_frame fw fun r hr => (dst r hr).1) (blockAt_frame fw fun r hr => (dst r hr).2)
  refine ⟨he.keep (fun r hr => gg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂,
    h.kept.of_eq fun r hr => gg r (by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [gg _ (by decide), h.x25], fun hc₀ => ?_, fun hc₀ => ?_, ?_, rfl⟩
  · by_cases h0 : n - j = 0
    · have hjn : j = n := by omega_arith
      subst hjn
      exact (h.ctr0 h0 hc₀).congr (blockAt_frame fw fun r hr => (dst r hr).1)
        (blockAt_frame fw fun r hr => (dst r hr).2)
    · exact (htail h0 hc₀).2
  · by_cases h0 : n - j = 0
    · have hjn : j = n := by omega_arith
      subst hjn
      rw [hD]; exact h.done hc₀
    · rw [show n = j + (n - j) by omega_arith]
      exact done_append (hD.trans (h.done hc₀)) (htail h0 hc₀).1
  · exact h.frame.trans (fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base D (by omega_arith)⟩)

omit L in
/-- The last bytes, with the new keystream block. -/
theorem crTail_ok {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : Cr3 Ctx St W SP k R icb P D n m₀ j s) :
    WP isa crTail s (CrOut Ctx St W SP k R icb P D n m₀) := by
  have hn' := h.data.ok.lt
  have hle := h.le
  have hj := h.lt16
  have he := h.env
  have hdj := h.data.drop h.le
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, r₁⟩ : ∃ s₁, runBlock isa [ptr .x11 .x20 64, mov .x12 .x23, mov .x13 .x24] s =
      some s₁ ∧ s₁.gpr .x11 = St + BitVec.ofNat 64 64 ∧ s₁.gpr .x12 = D + BitVec.ofNat 64 j ∧
      s₁.gpr .x13 = BitVec.ofNat 64 (n - j) ∧ Regs [.x11, .x12, .x13] s s₁ := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, he.x20]
    · simp [gpr_write, h.x23]
    · simp [gpr_write, h.x24]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp : LoopPre s₁ (St + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 j) (n - j) := by
    refine ⟨by omega_arith, ?_, ?_, ?_⟩
    · rw [r₁.rd, r₁.wr]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [r₁.wr]; exact hdj.wr
    · exact (hdj.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.mono (xor_ok s₁ x11₁ x12₁ x13₁ lp) fun s₂ ⟨m₂, g₂, sp₂, rd₂, wr₂⟩ => ?_
  rw [r₁.mem] at m₂
  refine crOut_of_xor h m₂ (fun r hr => ?_) (by rw [sp₂, r₁.sp]) (by rw [rd₂, r₁.rd]) (by rw [wr₂, r₁.wr])
  have hr' : r ∉ [Reg.x11, .x12, .x13] ++ loopRegs := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [g₂ r (fun h' => hr' (List.mem_append_right _ h')), r₁.others r (fun h' => hr' (List.mem_append_left _ h'))]

omit L in
/-- The last bytes, in place or not: in place `crTail`; out of place the
last bytes of the text XORed into the keystream block, and copied from it to
the output. -/
theorem crTailG_ok (to : Bool) {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D O : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : Cr3G to Ctx St W SP k R icb P D O n m₀ j s) :
    WP isa (crTailG to) s (CrOutG to Ctx St W SP k R icb P D O n m₀) := by
  cases to
  · have e : O = D := h.outAt
    subst e
    exact crTail_ok h
  have hdk : DataOk St W s D n := h.data
  obtain ⟨hw, hdo, x26⟩ := h.outAt
  have hn' := hdk.lt
  have hle := h.le
  have hj := h.lt16
  have he := h.env
  have hdj := hdk.drop h.le
  have hwj := hw.drop h.le
  -- The text's last bytes XORed into the keystream block.
  obtain ⟨s₁, run₁, x12₁, x11₁, x13₁, r₁⟩ : ∃ s₁, runBlock isa [ptr .x12 .x20 64, mov .x11 .x23, mov .x13 .x24] s =
      some s₁ ∧ s₁.gpr .x12 = St + BitVec.ofNat 64 64 ∧ s₁.gpr .x11 = D + BitVec.ofNat 64 j ∧
      s₁.gpr .x13 = BitVec.ofNat 64 (n - j) ∧ Regs [.x12, .x11, .x13] s s₁ := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, he.x20]
    · simp [gpr_write, h.x23]
    · simp [gpr_write, h.x24]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp₁ : LoopPre s₁ (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 64) (n - j) := by
    refine ⟨by omega_arith, ?_, ?_, ?_⟩
    · rw [r₁.rd, r₁.wr]; exact hdj.rd
    · rw [r₁.wr]; exact he.perm.stC (by omega_arith)
    · exact hdj.st.sub_right (Lay.stSub (by omega_arith))
  refine WP.seq (WP.mono (xor_ok s₁ x11₁ x12₁ x13₁ lp₁) fun s₂ ⟨m₂, g₂, sp₂, rd₂, wr₂⟩ => ?_)
  rw [r₁.mem] at m₂
  have nl : ∀ r, r ∉ loopRegs → r ∉ [Reg.x12, .x11, .x13] := fun r hr h' => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
    rcases h' with rfl | rfl | rfl <;> simp)
  have g12 : ∀ r, r ∉ loopRegs → s₂.gpr r = s.gpr r := fun r hr => by
    rw [g₂ r hr, r₁.others r (nl r hr)]
  -- Copied to the output.
  obtain ⟨s₃, run₃, x11₃, x12₃, x13₃, r₃⟩ : ∃ s₃, runBlock isa [mov .x11 .x26, ptr .x12 .x20 64, mov .x13 .x24] s₂ =
      some s₃ ∧ s₃.gpr .x11 = O + BitVec.ofNat 64 j ∧ s₃.gpr .x12 = St + BitVec.ofNat 64 64 ∧
      s₃.gpr .x13 = BitVec.ofNat 64 (n - j) ∧ Regs [.x11, .x12, .x13] s₂ s₃ := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, g12 .x26 (by decide), x26]
    · simp [gpr_write, g12 .x20 (by decide), he.x20]
    · simp [gpr_write, g12 .x24 (by decide), h.x24]
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have lp₃ : LoopPre s₃ (St + BitVec.ofNat 64 64) (O + BitVec.ofNat 64 j) (n - j) := by
    refine ⟨by omega_arith, ?_, ?_, ?_⟩
    · rw [r₃.rd, r₃.wr, rd₂, wr₂, r₁.rd, r₁.wr]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [r₃.wr, wr₂, r₁.wr]; exact hwj.wr
    · exact (hwj.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.mono (copy_ok s₃ x12₃ x11₃ x13₃ lp₃) fun s₄ ⟨m₄, g₄, sp₄, rd₄, wr₄⟩ => ?_
  rw [r₃.mem] at m₄
  have gg : ∀ r, r ∉ loopRegs → s₄.gpr r = s.gpr r := fun r hr => by
    rw [g₄ r hr, r₃.others r (fun h' => nl r hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
      rcases h' with rfl | rfl | rfl <;> simp)), g12 r hr]
  have hrd : s₄.rd = s.rd := by rw [rd₄, r₃.rd, rd₂, r₁.rd]
  have hwr : s₄.wr = s.wr := by rw [wr₄, r₃.wr, wr₂, r₁.wr]
  have hxl := length_xorBytes s.mem (St + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 j) (n - j)
  have f₂ : Frame [⟨St + BitVec.ofNat 64 64, n - j⟩] s.mem s₂.mem := by rw [m₂]; exact writeBytes_frame' _ hxl
  have f₄ : Frame [⟨O + BitVec.ofNat 64 j, n - j⟩] s₂.mem s₄.mem := by
    rw [m₄]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have fw : Frame [⟨St + BitVec.ofNat 64 64, n - j⟩, ⟨O + BitVec.ofNat 64 j, n - j⟩] s.mem s₄.mem :=
    (f₂.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      (f₄.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hwk := hw.take h.le
  have hO : bytesAt s₄.mem O j = bytesAt s.mem O j := bytesAt_frame fw (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hwk.ok.st.sub_right (Lay.stSub (by omega_arith))
    · exact split_disj h.le hn') (by omega_arith)
  -- The tail, from a new keystream block.
  have htail : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
      bytesAt s₄.mem (O + BitVec.ofNat 64 j) (n - j) =
        xorKs (ciphOf m₀ Ctx R) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) := by
    intro hc₀
    by_cases h0 : n - j = 0
    · rw [h0]; simp [bytesAt, xorKs]
    obtain ⟨mc, hmc, hks, hcb⟩ := h.ctr1 h0 hc₀
    have hw0 : (P + j) % 16 = 0 := h.whole.resolve_left h0
    obtain ⟨t₁, -⟩ := Proof.Gcm.ctr_tail hmc hw0 hks hcb (d := bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j))
      (by rw [length_bytesAt]; omega_arith) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at t₁
    have e₂ : bytesAt s₂.mem (St + BitVec.ofNat 64 64) (n - j) =
        xorBytes s.mem (St + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 j) (n - j) := by
      have e := bytesAt_writeBytes_self s.mem (St + BitVec.ofNat 64 64)
        (xorBytes s.mem (St + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 j) (n - j)) (by rw [hxl]; omega_arith)
      rw [hxl] at e
      rw [m₂, e]
    have e₄ := bytesAt_writeBytes_self s₂.mem (O + BitVec.ofNat 64 j)
      (bytesAt s₂.mem (St + BitVec.ofNat 64 64) (n - j)) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at e₄
    rw [m₄, e₄, e₂, xorBytes, List.zipWith_comm_of_comm (fun x y => BitVec.xor_comm x y), t₁, h.rest]
  refine ⟨he.keep (fun r hr => gg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) (by rw [sp₄, r₃.sp, sp₂, r₁.sp]) hrd hwr,
    keptG_of_eq h.kept fun r hr => gg r (by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [gg _ (by decide), h.x25], True.intro, fun hc₀ => ?_, ?_, And.intro (hw.of_eq hrd hwr) hdo⟩
  · rw [show n = j + (n - j) by omega_arith]
    exact done_append (hO.trans (h.done hc₀)) (htail hc₀)
  · exact h.frame.trans (fw.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by omega_arith)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub_base O (by omega_arith)⟩)

omit L in
/-- From the start of a keystream block, nothing done yet. -/
theorem CrInG.mid {to : Bool} {k : Reg → BitVec 64} {R P : Nat} {icb : Block} {D O : Addr} {n : Nat} {s : State}
    (h : CrInG to Ctx St W SP k R P D O n s) (hP : P % 16 = 0) :
    CrMidG to Ctx St W SP k R icb P D O n s.mem 0 s :=
  ⟨h.env, h.kept, h.x22, h.rounds, Nat.zero_le _, by rw [h.x23]; simp, by rw [h.x24, Nat.sub_zero], h.x25,
    h.data, fun hc => by simpa using hc, fun _ => by simp [bytesAt, Proof.Gcm.xorKs_nil], rfl,
    .inr (by omega_arith), Frame.refl _ _, h.outAt⟩

omit L in
theorem CrIn.mid {k : Reg → BitVec 64} {R P : Nat} {icb : Block} {D : Addr} {n : Nat} {s : State}
    (h : CrIn Ctx St W SP k R P D n s) (hP : P % 16 = 0) : CrMid Ctx St W SP k R icb P D n s.mem 0 s :=
  CrInG.mid h hP

/-- The arguments for the whole blocks, from part of the way; out of place
also the output (`x6`), and `x26` past the whole blocks. -/
theorem crArgsG_ok (to : Bool) {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D O : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : CrMidG to Ctx St W SP k R icb P D O n m₀ j s) :
    WP isa (.block (crArgsG to)) s (Cr1G to Ctx St W SP k R icb P D O n m₀ j) := by
  have hn' := (dataOk_of h.data).lt
  have he := h.env
  have hle := h.le
  generalize hnb : (n - j) / 16 = nb
  have h16 : 16 * nb ≤ n - j := by omega_arith
  obtain ⟨s₄, run₄, x3₄, x4₄, x0₄, x1₄, x2₄, x5₄, x23₄, x24₄, x9₄, r₄⟩ : ∃ s₄, runBlock isa crArgs s = some s₄ ∧
      s₄.gpr .x3 = D + BitVec.ofNat 64 j ∧ s₄.gpr .x4 = BitVec.ofNat 64 nb ∧ s₄.gpr .x0 = Ctx ∧
      s₄.gpr .x1 = BitVec.ofNat 64 R ∧ s₄.gpr .x2 = St + BitVec.ofNat 64 48 ∧
      s₄.gpr .x5 = W + BitVec.ofNat 64 512 ∧ s₄.gpr .x23 = D + BitVec.ofNat 64 (j + 16 * nb) ∧
      s₄.gpr .x24 = BitVec.ofNat 64 (n - (j + 16 * nb)) ∧ s₄.gpr .x9 = BitVec.ofNat 64 (16 * nb) ∧
      Regs [.x4, .x3, .x0, .x1, .x2, .x5, .x9, .x23, .x24] s s₄ := by
    refine ⟨_, by rw [crArgs, List.append_assoc, ctrArgs_eq]; arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, h.x23]
    · simp [gpr_write, h.x24, lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega_arith), hnb]
    · simp [gpr_write, he.x21]
    · simp [gpr_write, h.x22]
    · simp [gpr_write, he.x20]
    · simp [gpr_write, he.x19]
    · simp [gpr_write, h.x23, h.x24, lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega_arith), hnb, lsl4_ofNat,
        add_ofNat_assoc]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h.x24, BitVec.setWidth_eq,
        lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega_arith), hnb, lsl4_ofNat]
      rw [ofNat_sub (by omega_arith) (by omega_arith)]
      congr 1
      omega_arith
    · simp [gpr_write, h.x24, lsr_ofNat _ _ (show n - j < 2 ^ 64 by omega_arith), hnb, lsl4_ofNat]
  -- Out of place, the output too.
  obtain ⟨s₅, w₅, r₅, o₅, x6₅, k₅⟩ : ∃ s₅, (∀ Q : State → Prop, Q s₅ →
        WP isa (.block (cond to [mov .x6 .x26, .add .x .x26 .x26 .x9] [])) s₄ Q) ∧ Regs [.x6, .x26] s₄ s₅ ∧
      OutAt to Ctx St W s₅ D O n (j + 16 * nb) ∧ (to = true → s₅.gpr .x6 = O + BitVec.ofNat 64 j) ∧
      (to = false → s₅.gpr .x26 = s₄.gpr .x26) := by
    cases to
    · exact ⟨s₄, fun _ hq => WP.block_nil hq, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, h.outAt, nofun, fun _ => rfl⟩
    · obtain ⟨hw, hdo, x26⟩ := h.outAt
      have e26 : s₄.gpr .x26 = O + BitVec.ofNat 64 j := by rw [r₄.others _ (by decide), x26]
      obtain ⟨s₅, run₅, x6₅, x26₅, r₅⟩ : ∃ s₅, runBlock isa [mov .x6 .x26, .add .x .x26 .x26 .x9] s₄ = some s₅ ∧
          s₅.gpr .x6 = O + BitVec.ofNat 64 j ∧ s₅.gpr .x26 = O + BitVec.ofNat 64 (j + 16 * nb) ∧
          Regs [.x6, .x26] s₄ s₅ := by
        refine ⟨_, by arun [], ?_⟩
        refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
        · simp [gpr_write, e26]
        · simp [gpr_write, e26, x9₄, add_ofNat_assoc]
      exact ⟨s₅, fun _ hq => WP.of_runBlock ⟨s₅, run₅, hq⟩, r₅,
        OutAt.mkTo (hw.of_eq (r₅.rd.trans r₄.rd) (r₅.wr.trans r₄.wr)) hdo x26₅, fun _ => x6₅, nofun⟩
  show WP isa (.block (crArgs ++ cond to [mov .x6 .x26, .add .x .x26 .x26 .x9] [])) s _
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₄, run₄, w₅ _ ?_⟩)
  have gg : ∀ r, r ∉ [Reg.x4, .x3, .x0, .x1, .x2, .x5, .x9, .x23, .x24, .x6, .x26] → s₅.gpr r = s.gpr r :=
    fun r hr => by
      rw [r₅.others r (fun h' => hr (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
          rcases h' with rfl | rfl <;> simp)),
        r₄.others r (fun h' => hr (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
          rcases h' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))]
  have hsp : s₅.sp = s.sp := r₅.sp.trans r₄.sp
  have hrd : s₅.rd = s.rd := r₅.rd.trans r₄.rd
  have hwr : s₅.wr = s.wr := r₅.wr.trans r₄.wr
  have hm : s₅.mem = s.mem := r₅.mem.trans r₄.mem
  have he₅ : Env Ctx St W SP s₅ := he.keep (fun r hr => gg r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) hsp hrd hwr
  have hd₅ := data_of_eq h.data hrd hwr
  refine ⟨he₅, keptG_of_eq26 h.kept (fun r hr => gg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) (fun hf => (k₅ hf).trans (r₄.others _ (by decide))),
    by rw [gg _ (by decide), h.x22], h.rounds, hle,
    by rw [hnb, r₅.others _ (by decide)]; exact x23₄, by rw [hnb, r₅.others _ (by decide)]; exact x24₄,
    by rw [gg _ (by decide), h.x25], hd₅, fun hc => by rw [hm]; exact h.ctr hc,
    fun hc => by rw [hm]; exact h.done hc, by rw [hm]; exact h.rest, h.whole,
    by rw [hm]; exact h.frame, ?_, by rw [hnb]; exact o₅⟩
  rw [hnb]
  exact crCallG_of L he₅ h.rounds hle h16 hd₅ o₅ (by rw [r₅.others _ (by decide)]; exact x0₄)
    (by rw [r₅.others _ (by decide)]; exact x1₄) (by rw [r₅.others _ (by decide)]; exact x2₄)
    (by rw [r₅.others _ (by decide)]; exact x3₄) (by rw [r₅.others _ (by decide)]; exact x4₄)
    (by rw [r₅.others _ (by decide)]; exact x5₄) x6₅

/-- The arguments for the whole blocks in place, from part of the way. -/
theorem crArgs_ok {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : CrMid Ctx St W SP k R icb P D n m₀ j s) :
    WP isa (.block crArgs) s (Cr1 Ctx St W SP k R icb P D n m₀ j) := by
  have := crArgsG_ok L false h
  rwa [crArgsG, Bool.cond_false, List.append_nil] at this

omit L in
theorem cryptAlG_false (c : Callees) : cryptAlG c false = cryptAl c := by
  simp only [cryptAlG, crArgsG, ctrCallG, crTailG, Bool.cond_false, List.append_nil, cryptAl]

/-- `cryptAlG`: `crypt` from the start of a keystream block, in place or
out of place. -/
theorem cryptAlG_ok (v : GcmImpl) (to : Bool) {k : Reg → BitVec 64} {R P : Nat} {icb : Block} {D O : Addr}
    {n : Nat} {s : State} (h : CrInG to Ctx St W SP k R P D O n s) (hP : P % 16 = 0) :
    WP isa (cryptAlG v.callees to) s (CrOutG to Ctx St W SP k R icb P D O n s.mem) := by
  have hc : ∀ {m' : Mem}, Frame (crFrame St W O n) s.mem m' → ciphOf m' Ctx R = ciphOf s.mem Ctx R :=
    fun hf => ciph_frame hf (ctx_crFrame L (OutAt.dataW h.outAt h.data)) h.rounds
  exact WP.seq (WP.mono (crArgsG_ok L to (h.mid (icb := icb) hP)) fun s₁ h₁ =>
    WP.seq (WP.mono (ctrCallG1_ok L v h₁ (hc h₁.frame)) fun s₂ ⟨h₂, hlt⟩ =>
    WP.seq (WP.mono (crSeg2_ok L h₂ hlt) fun s₃ h₃ =>
    WP.seq (WP.mono (ctrCall2_ok L v h₃ (hc h₃.frame)) fun s₄ h₄ => crTailG_ok to h₄))))

/-- `cryptAl`: `crypt` from the start of a keystream block. -/
theorem cryptAl_ok (v : GcmImpl) {k : Reg → BitVec 64} {R P : Nat} {icb : Block} {D : Addr} {n : Nat}
    {s : State} (h : CrIn Ctx St W SP k R P D n s) (hP : P % 16 = 0) :
    WP isa (cryptAl v.callees) s (CrOut Ctx St W SP k R icb P D n s.mem) := by
  rw [← cryptAlG_false]
  exact cryptAlG_ok L v false h hP

/-- `crypt`. -/
theorem crypt_ok (v : GcmImpl) {k : Reg → BitVec 64} {R P : Nat} {icb : Block} {D : Addr} {n : Nat} {s : State}
    (h : CrIn Ctx St W SP k R P D n s) :
    WP isa (crypt v.callees) s (CrOut Ctx St W SP k R icb P D n s.mem) := by
  have hc : ∀ {m' : Mem}, Frame (crFrame St W D n) s.mem m' → ciphOf m' Ctx R = ciphOf s.mem Ctx R :=
    fun hf => ciph_frame hf (ctx_crFrame L h.data) h.rounds
  exact WP.seq (WP.mono (crSeg1_ok L (icb := icb) h) fun s₁ h₁ =>
    WP.seq (WP.mono (ctrCall1_ok L v h₁ (hc h₁.frame)) fun s₂ ⟨h₂, hlt⟩ =>
    WP.seq (WP.mono (crSeg2_ok L h₂ hlt) fun s₃ h₃ =>
    WP.seq (WP.mono (ctrCall2_ok L v h₃ (hc h₃.frame)) fun s₄ h₄ => crTail_ok h₄))))

end

end VG.Proof.AesGcm.AArch64
