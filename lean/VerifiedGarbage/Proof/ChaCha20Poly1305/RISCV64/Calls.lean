module

import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Xor
public import VerifiedGarbage.Proof.Poly1305.RISCV64.Init
public import VerifiedGarbage.Proof.Poly1305.RISCV64.Update
public import VerifiedGarbage.Proof.Poly1305.RISCV64.Finalize
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
import VerifiedGarbage.Proof.ChaCha20.RISCV64.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
meta import VerifiedGarbage.Proof.ChaCha20.RISCV64.Block
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Init
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Update
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Finalize
meta import VerifiedGarbage.Proof.ChaCha20.RISCV64.Xor
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64
public import VerifiedGarbage.Impl.ChaCha20.RISCV64.Xor
public import VerifiedGarbage.Impl.Poly1305.RISCV64
public import VerifiedGarbage.Spec.ChaCha20

/-!
# ChaCha20-Poly1305 on RISC-V: the calls

Each call of a verified function, from its proof (`WP.call`): what it needs
of the state it is called from, and what holds when it returns. A call
stores nothing in memory, so the callee changes memory only within the
regions it may write; it keeps the callee-saved registers, and `a0`, which
no instruction of any callee writes.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64

open VG VG.RISCV64
open VG.Spec.Poly1305 (Repr Buffered bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are neither callee-saved nor `a0`. -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  a0 : s'.gpr .a0 = s.gpr .a0
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

/-- No instruction of `c` writes `a0`. -/
def KeepsA0 (c : Prog isa) : Prop := ∀ i ∈ instrs c, dstOf i ≠ some .a0

theorem KeepsA0.of_all {c : Prog isa} (h : ((instrs c).all fun i => dstOf i != some .a0) = true) :
    KeepsA0 c := fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem block_a0 : KeepsA0 Impl.ChaCha20.RISCV64.block :=
  KeepsA0.of_all (by rw [← Code.allInstrs_eq]; decide +kernel)
theorem xor_a0 : KeepsA0 Impl.ChaCha20.RISCV64.Xor.xor :=
  KeepsA0.of_all (by rw [← Code.allInstrs_eq]; decide +kernel)
theorem init_a0 : KeepsA0 Impl.Poly1305.RISCV64.init :=
  KeepsA0.of_all (by rw [← Code.allInstrs_eq]; lit_decide)
theorem update_a0 : KeepsA0 Impl.Poly1305.RISCV64.update :=
  KeepsA0.of_all (by rw [← Code.allInstrs_eq]; lit_decide)
theorem finalize_a0 : KeepsA0 Impl.Poly1305.RISCV64.finalize :=
  KeepsA0.of_all (by rw [← Code.allInstrs_eq]; lit_decide)

theorem kept_of {c : Prog isa} (hc : KeepsA0 c) {rs : List Region} {s s' : State}
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hf : Frame rs s.mem s'.mem)
    (hcs : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hk : ∀ r, r ∉ linkRegs → (∀ i ∈ instrs c, dstOf i ≠ some r) → s'.gpr r = s.gpr r) :
    Kept rs s s' := ⟨hcs, hk .a0 (by decide) hc, hsp, hrd, hwr, hf⟩

/-! ## `vg_chacha20_block` -/

theorem block_call {s : State} {S B : Addr} (h0 : s.gpr .a0 = S) (h1 : s.gpr .a1 = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩) (hSa : S.toNat % 4 = 0) (hBa : B.toNat % 4 = 0)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨B, 256⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨B, 256⟩] s s' →
      stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.RISCV64.block) s Q := by
  have c0 : s.callEntry.gpr .a0 = S := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = B := (State.callEntry_gpr _ (by decide)).trans h1
  refine WP.call (k := Proof.ChaCha20.blockRISCV64) Proof.ChaCha20.RISCV64.block_verified.1
    (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_ Proof.ChaCha20.RISCV64.Xor.block_noFrames
  · simp only [Proof.ChaCha20.blockRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, hdj, hSa, hBa⟩
  · intro s' hrd hwr hsp hf hcs hk hpost
    refine hQ s' (kept_of block_a0 hrd hwr hsp hf hcs hk) ?_
    simpa only [Proof.ChaCha20.blockRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1] using hpost

/-! ## `vg_chacha20_xor` -/

theorem xor_call {s : State} {S D B : Addr} {n : Nat} (h0 : s.gpr .a0 = S) (h1 : s.gpr .a1 = D)
    (h2 : s.gpr .a2 = BitVec.ofNat 64 n) (h3 : s.gpr .a3 = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩)
    (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hD : D.toNat + n ≤ 2 ^ 64)
    (hSa : S.toNat % 4 = 0) (hBa : B.toNat % 4 = 0)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s s' →
      Spec.ChaCha20.bytesAt s'.mem D n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem D n)
          (keystream (stateAt s.mem S) n) → Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.RISCV64.Xor.xor) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have c0 : s.callEntry.gpr .a0 = S := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = D := (State.callEntry_gpr _ (by decide)).trans h1
  have c2 : s.callEntry.gpr .a2 = BitVec.ofNat 64 n := (State.callEntry_gpr _ (by decide)).trans h2
  have c3 : s.callEntry.gpr .a3 = B := (State.callEntry_gpr _ (by decide)).trans h3
  refine WP.call (k := Proof.ChaCha20.xorRISCV64) Proof.ChaCha20.RISCV64.Xor.xor_correct
    (rd := []) (wr := [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) ?_ hc hw ?_ (by decide +kernel)
  · simp only [Proof.ChaCha20.xorRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hD, hSa, hBa⟩
  · intro s' hrd hwr hsp hf hcs hk hpost
    simp only [Proof.ChaCha20.xorRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, hn'] at hpost
    exact hQ s' (kept_of xor_a0 hrd hwr hsp hf hcs hk) hpost

/-! ## `vg_poly1305_init` -/

theorem init_call {s : State} {P K : Addr} (h0 : s.gpr .a0 = P) (h1 : s.gpr .a1 = K)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨K, 32⟩)
    (hc : Covers ([⟨K, 32⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨P, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩] s s' → Repr s'.mem P (bytesAt s.mem K 32) [] → Q s') :
    WP isa (.call "vg_poly1305_init" Impl.Poly1305.RISCV64.init) s Q := by
  have c0 : s.callEntry.gpr .a0 = P := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = K := (State.callEntry_gpr _ (by decide)).trans h1
  refine WP.call (k := Proof.Poly1305.initRISCV64) Proof.Poly1305.RISCV64.init_verified.1
    (rd := [⟨K, 32⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_ (by lit_decide)
  · simp only [Proof.Poly1305.initRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, hdj⟩
  · intro s' hrd hwr hsp hf hcs hk hpost
    refine hQ s' (kept_of init_a0 hrd hwr hsp hf hcs hk) ?_
    simpa only [Proof.Poly1305.initRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1] using hpost

/-! ## `vg_poly1305_update` -/

theorem update_call {s : State} {P D : Addr} {c : BitVec 64} {n : Nat} (h0 : s.gpr .a0 = P)
    (h1 : s.gpr .a1 = c) (h2 : s.gpr .a2 = D) (h3 : s.gpr .a3 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨D, n⟩) (hPa : P.toNat % 8 = 0)
    (hc : Covers ([⟨D, n⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨P, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩] s s' →
      (∀ key msg, Buffered s.mem P key msg → c.toNat % 16 = msg.length % 16 →
        Buffered s'.mem P key (msg ++ bytesAt s.mem D n)) → Q s') :
    WP isa (.call "vg_poly1305_update" Impl.Poly1305.RISCV64.update) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have c0 : s.callEntry.gpr .a0 = P := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = c := (State.callEntry_gpr _ (by decide)).trans h1
  have c2 : s.callEntry.gpr .a2 = D := (State.callEntry_gpr _ (by decide)).trans h2
  have c3 : s.callEntry.gpr .a3 = BitVec.ofNat 64 n := (State.callEntry_gpr _ (by decide)).trans h3
  refine WP.call (k := Proof.Poly1305.updateRISCV64) Proof.Poly1305.RISCV64.update_verified.1
    (rd := [⟨D, n⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_ (by lit_decide)
  · simp only [Proof.Poly1305.updateRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c2, c3, hn']
    exact ⟨trivial, trivial, hdj, hPa⟩
  · intro s' hrd hwr hsp hf hcs hk hpost
    refine hQ s' (kept_of update_a0 hrd hwr hsp hf hcs hk) ?_
    simpa only [Proof.Poly1305.updateRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3, hn'] using hpost

/-! ## `vg_poly1305_finalize` -/

theorem finalize_call {s : State} {P O : Addr} {c : BitVec 64} (h0 : s.gpr .a0 = P)
    (h1 : s.gpr .a1 = c) (h2 : s.gpr .a2 = O)
    (hPO : (⟨P, 128⟩ : Region).Disjoint ⟨O, 16⟩) (hPa : P.toNat % 8 = 0)
    (hc : Covers ([] ++ [⟨P, 128⟩, ⟨O, 16⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨P, 128⟩, ⟨O, 16⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩, ⟨O, 16⟩] s s' →
      (∀ key msg, Buffered s.mem P key msg → c.toNat % 16 = msg.length % 16 →
        bytesAt s'.mem O 16 = mac key msg) → Q s') :
    WP isa (.call "vg_poly1305_finalize" Impl.Poly1305.RISCV64.finalize) s Q := by
  have c0 : s.callEntry.gpr .a0 = P := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = c := (State.callEntry_gpr _ (by decide)).trans h1
  have c2 : s.callEntry.gpr .a2 = O := (State.callEntry_gpr _ (by decide)).trans h2
  refine WP.call (k := Proof.Poly1305.finalizeRISCV64) Proof.Poly1305.RISCV64.finalize_verified.1
    (rd := []) (wr := [⟨P, 128⟩, ⟨O, 16⟩]) ?_ hc hw ?_ (by lit_decide)
  · simp only [Proof.Poly1305.finalizeRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c2]
    exact ⟨trivial, trivial, hPO, hPa⟩
  · intro s' hrd hwr hsp hf hcs hk hpost
    refine hQ s' (kept_of finalize_a0 hrd hwr hsp hf hcs hk) ?_
    simpa only [Proof.Poly1305.finalizeRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2] using hpost

end VG.Proof.ChaCha20Poly1305.RISCV64
