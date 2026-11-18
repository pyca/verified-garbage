module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
import VerifiedGarbage.Proof.Gcm.Be64
public import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee

/-! ### `AesGcm.RISCV64.Absorb`, which this module and modules that import it used -/

section

/-! ### `AesGcm.RISCV64.Ghash1`, which this module and modules that import it used -/

section

/-!
# AES-GCM on RISC-V: GHASH over blocks of the state, `T` or the data

Untrusted: everything here is checked by Lean. As on PPC64LE: `ghCall_ok`
is a call of `vg_ghash` from a state whose registers are its arguments (the
hash subkey at `ctx + 240`, the accumulator at `st + yo`, the working space
at `W + 512`), and `ghash1 yo b o` continues the accumulator over the block
at `P = b + o` (`ghash1_ok`). The call may also change the 2048 bytes below
the stack pointer, which are apart from everything the pieces keep.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

theorem frozen_preserved : ∀ r ∈ frozen, r ∈ preserved := by decide

/-- An environment, after code that keeps the nonvolatile registers. -/
theorem Env.of_saved {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (h : Env V sp s)
    (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env V sp s' :=
  h.keep (fun r hr => hg r (frozen_preserved r hr)) hsp hrd hwr

/-- What a call of `vg_ghash` from `s` leaves in `s'`, for the accumulator at
`Y`, the working space at `w + 512` and the data `ds` (as blocks). -/
structure GhOut (s : State) (c w : Addr) (Y : Addr) (ds : List Block) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  spk : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩, below s.sp 2048] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem (c + BitVec.ofNat 64 240)) (blockAt s.mem Y) ds

theorem GhOut.env {s s' : State} {c w : Addr} {Y : Addr} {ds : List Block} {V : Reg → BitVec 64}
    {sp : Addr} (h : GhOut s c w Y ds s') (he : Env V sp s) : Env V sp s' :=
  he.of_saved h.saved h.spk h.rd h.wr

theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [blockAt m p] := by
  simp [blocksAt]

/-- The arguments of a call of `vg_ghash`, for `n` blocks at `P`. -/
theorem ghCall_mk {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0)) {yo : Nat}
    (hyo : yo = 0 ∨ yo = 16) {s : State} (he : Env V sp s) {P : Addr} {n : Nat}
    (h3 : s.gpr .a0 = V .s2 + BitVec.ofNat 64 240) (h4 : s.gpr .a1 = V .s1 + BitVec.ofNat 64 yo)
    (h5 : s.gpr .a2 = P) (h6 : s.gpr .a3 = BitVec.ofNat 64 n) (h7 : s.gpr .a4 = V .s0 + BitVec.ofNat 64 512)
    (hn : n < 2 ^ 64)
    (hpy : (⟨V .s1 + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16 * n⟩)
    (_hpw : (⟨P, 16 * n⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 512, 256⟩)
    (hpk : (⟨P, 16 * n⟩ : Region).Disjoint (below s.sp 2048)) (hpf : P.toNat + 16 * n ≤ 2 ^ 64)
    (hpr : Covers [⟨P, 16 * n⟩] (s.rd ++ s.wr)) :
    GhCall s (V .s2 + BitVec.ofNat 64 240) (V .s1 + BitVec.ofNat 64 yo) P
      (V .s0 + BitVec.ofNat 64 512) n := by
  have hk := he.stk
  refine ⟨h3, h4, h5, h6, h7, hn, hpy, (hk.c.sub_left (Lay.ctxSub (by decide))).symm,
    (hk.st.sub_left (Lay.stSub (by omega_using [hyo]))).symm, hpk.symm, ?_, hpf, hk.al, hk.ge, ?_, ?_⟩
  · have := L.sw; rw [Offset.toNat_add_ofNat]; omega_using [hyo, this]
  · exact Covers.cons (he.perm.ctxC (by decide)) (Covers.cons hpr
      (Covers.cons (covers_left (he.perm.stC (by omega_using [hyo]))) (covers_left (he.perm.wC (by decide)))))
  · exact Covers.cons (he.perm.stC (by omega_using [hyo])) (he.perm.wC (by decide))

/-- The call itself, from a state whose registers are its arguments, for `n`
blocks at `P`. -/
theorem ghCall_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0)) {yo : Nat}
    (hyo : yo = 0 ∨ yo = 16) {s : State} (he : Env V sp s) {P : Addr} {n : Nat}
    (h3 : s.gpr .a0 = V .s2 + BitVec.ofNat 64 240) (h4 : s.gpr .a1 = V .s1 + BitVec.ofNat 64 yo)
    (h5 : s.gpr .a2 = P) (h6 : s.gpr .a3 = BitVec.ofNat 64 n) (h7 : s.gpr .a4 = V .s0 + BitVec.ofNat 64 512)
    (hn : n < 2 ^ 64)
    (hpy : (⟨V .s1 + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16 * n⟩)
    (hpw : (⟨P, 16 * n⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 512, 256⟩)
    (hpk : (⟨P, 16 * n⟩ : Region).Disjoint (below s.sp 2048)) (hpf : P.toNat + 16 * n ≤ 2 ^ 64)
    (hpr : Covers [⟨P, 16 * n⟩] (s.rd ++ s.wr)) :
    WP isa ghCall s (GhOut s (V .s2) (V .s0) (V .s1 + BitVec.ofNat 64 yo) (blocksAt s.mem P n)) :=
  WP.mono (gh_call (ghCall_mk L hyo he h3 h4 h5 h6 h7 hn hpy hpw hpk hpf hpr)) fun _ h =>
    ⟨h.rd, h.wr, h.sp, h.saved, h.frame, h.out⟩

/-- `ghash1`'s arguments, for the block at `P = b + o`. -/
theorem ghArgs_ok {V : Reg → BitVec 64} {sp : Addr} {yo : Nat}
    (hyo : yo = 0 ∨ yo = 16) {s : State} (he : Env V sp s) (b : Reg) (o : Nat)
    (hb : b = .s1 ∨ b = .s0) (ho : o < 2048) {P : Addr} (hP : s.gpr b + BitVec.ofNat 64 o = P) :
    WP isa (.block [.addi .a0 .s2 240, .addi .a1 .s1 yo, .addi .a2 b o, .li .a3 1,
      .addi .a4 .s0 scrO]) s (fun s₁ : State => s₁.gpr .a0 = V .s2 + BitVec.ofNat 64 240 ∧
        s₁.gpr .a1 = V .s1 + BitVec.ofNat 64 yo ∧ s₁.gpr .a2 = P ∧ s₁.gpr .a3 = BitVec.ofNat 64 1 ∧
        s₁.gpr .a4 = V .s0 + BitVec.ofNat 64 512 ∧
        (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .a4 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁) := by
  have h29 := he.s2; have h30 := he.s1; have h31 := he.s0
  refine Steps.wp_addi (by decide) fun s₁ u₁ => Steps.wp_addi (by omega_using [hyo]) fun s₂ u₂ =>
    Steps.wp_addi ho fun s₃ u₃ => Steps.wp_li (by decide) fun s₄ u₄ =>
    Steps.wp_addi (by decide) fun s₅ u₅ => WP.block_nil ?_
  have hb' : b ≠ .a0 ∧ b ≠ .a1 := by rcases hb with rfl | rfl <;> decide
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r a b c d e => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, h29]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h30]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ hb'.2,
      u₁.other _ hb'.1, hP]
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h31]; rfl
  · rw [u₅.other _ e, u₄.other _ d, u₃.other _ c, u₂.other _ b, u₁.other _ a]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- `ghash1 yo b o`, for the block at `P = b + o`. -/
theorem ghash1_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0)) {yo : Nat}
    (hyo : yo = 0 ∨ yo = 16) {s : State} (he : Env V sp s) (b : Reg) (o : Nat)
    (hb : b = .s1 ∨ b = .s0) (ho : o < 2048) {P : Addr} (hP : s.gpr b + BitVec.ofNat 64 o = P)
    (hpy : (⟨V .s1 + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hpw : (⟨P, 16⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 512, 256⟩)
    (hpk : (⟨P, 16⟩ : Region).Disjoint (below sp 2048)) (hpf : P.toNat + 16 ≤ 2 ^ 64)
    (hpr : Covers [⟨P, 16⟩] (s.rd ++ s.wr)) :
    WP isa (ghash1 yo b o) s (GhOut s (V .s2) (V .s0) (V .s1 + BitVec.ofNat 64 yo) [blockAt s.mem P]) := by
  have hargs := ghArgs_ok hyo he b o hb ho hP
  refine WP.seq (WP.mono hargs fun s₁ ⟨h3, h4, h5, h6, h7, hkeep, hk⟩ => ?_)
  have he₁ : Env V sp s₁ := he.keep (fun r hr => hkeep r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
  refine WP.mono (ghCall_ok L hyo he₁ (P := P) (n := 1) h3 h4 h5 h6 h7 (by decide)
    (by simpa using hpy) (by simpa using hpw) (by rw [he₁.sp]; simpa using hpk) (by simpa using hpf)
    (by rw [hk.rd, hk.wr]; simpa using hpr)) fun s' h => ?_
  exact ⟨h.rd.trans hk.rd, h.wr.trans hk.wr, h.spk.trans hk.sp,
    fun r hr => by
      rw [h.saved r hr]
      exact hkeep r (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide),
    by rw [← hk.sp, ← hk.mem]; exact h.frame, by rw [h.out, blocksAt_one, hk.mem]⟩

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: GHASH absorbing a piece (`absorb`)

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcm/PPC64LE/Absorb.lean`): `absorb yo` absorbs the `s5` bytes at
`s4` into GHASH, with the accumulator at `st + yo` and the `s6` buffered
bytes at `st + 32` (`absorb_ok`): it fills the buffer (`headPre_ok`,
`head_ok`), absorbs whole blocks (`whole_ok`) and buffers the rest
(`tail_ok`), by the steps of `Proof/Gcm/Stream.lean`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Proof.Gcm (Absorbed)

/-- Branching on a register holding `n`. -/
theorem eval_zero {s : State} {r : Reg} {n : Nat} (h : s.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    isa.eval (.zero r) s = some (decide (n = 0)) :=
  Steps.eval_zero_ofNat s r hn h

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Proof.Cmac.bytesAt_frame hf hd hn

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, bytesAt_frame hf hd (by decide)]

/-- The regions `absorb` writes, with the stack below `sp` that `vg_ghash`'s
frame uses. -/
abbrev absFrame (st w : Addr) (yo : Nat) (sp : Addr) : List Region :=
  [⟨st + BitVec.ofNat 64 yo, 16⟩, ⟨st + BitVec.ofNat 64 32, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩,
    below sp 2048]

/-- Before `absorb yo`: GHASH has absorbed `x` (with hash subkey `H`), and
`s4`, `s5`, `s6` hold the data, its length and `len(x) mod 16`. -/
structure AbsIn (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (x : List Byte) (D : Addr)
    (n : Nat) (s : State) : Prop where
  env : Env V sp s
  s4 : s.gpr .s4 = D
  s5 : s.gpr .s5 = BitVec.ofNat 64 n
  s6 : s.gpr .s6 = BitVec.ofNat 64 (x.length % 16)
  data : DataOk (V .s1) (V .s0) s D n
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H

/-- Part of the way: `j` bytes absorbed, from `m₀`. -/
structure AbsMid (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (x : List Byte) (D : Addr)
    (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env V sp s
  le : j ≤ n
  s4 : s.gpr .s4 = D + BitVec.ofNat 64 j
  s5 : s.gpr .s5 = BitVec.ofNat 64 (n - j)
  data : DataOk (V .s1) (V .s0) s D n
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (V .s1 + BitVec.ofNat 64 yo) (V .s1 + BitVec.ofNat 64 32) H x →
    Absorbed s.mem (V .s1 + BitVec.ofNat 64 yo) (V .s1 + BitVec.ofNat 64 32) H
      (x ++ bytesAt m₀ D j)
  whole : n - j = 0 ∨ (x.length + j) % 16 = 0
  frame : Frame (absFrame (V .s1) (V .s0) yo sp) m₀ s.mem

/-- After: everything absorbed, from `x₀` absorbed in `m₀` to `x`. -/
structure AbsOut (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  abs : Absorbed m₀ (V .s1 + BitVec.ofNat 64 yo) (V .s1 + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (V .s1 + BitVec.ofNat 64 yo) (V .s1 + BitVec.ofNat 64 32) H x
  frame : Frame (absFrame (V .s1) (V .s0) yo sp) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0)) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L in
/-- The data is apart from what `absorb` writes. -/
theorem data_absFrame {s : State} {D : Addr} {n : Nat} (hd : DataOk (V .s1) (V .s0) s D n)
    (hsp : s.sp = sp) : ∀ r ∈ absFrame (V .s1) (V .s0) yo sp, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by omega_arith))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · rw [← hsp]; exact hd.sk

/-- The hash subkey is apart from what `absorb` writes. -/
theorem ctx_absFrame (hk : StkOk (V .s2) (V .s1) (V .s0) sp) : ∀ r ∈ absFrame (V .s1) (V .s0) yo sp,
    (⟨V .s2 + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega_arith)
  · exact L.ctx_st (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact hk.c.sub_left (Lay.ctxSub (by decide))

omit L hyo in
/-- A write within the buffer is within what `absorb` writes. -/
theorem buf_absFrame {m m' : Mem} {o k : Nat} (h : Frame [⟨V .s1 + BitVec.ofNat 64 (32 + o), k⟩] m m')
    (hk : o + k ≤ 16) : Frame (absFrame (V .s1) (V .s0) yo sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by omega_arith) (by omega_arith)⟩

omit L hyo in
theorem gh_absFrame {m m' : Mem} (h : Frame [⟨V .s1 + BitVec.ofNat 64 yo, 16⟩,
    ⟨V .s0 + BitVec.ofNat 64 512, 256⟩, below sp 2048] m m') : Frame (absFrame (V .s1) (V .s0) yo sp) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

/-- The hash subkey is apart from what a call of `vg_ghash` writes. -/
theorem ctx_ghFrame (hk : StkOk (V .s2) (V .s1) (V .s0) sp) : ∀ r ∈ [(⟨V .s1 + BitVec.ofNat 64 yo, 16⟩ : Region),
    ⟨V .s0 + BitVec.ofNat 64 512, 256⟩, below sp 2048],
    (⟨V .s2 + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega_arith)
  · exact L.ctx_w (by decide) (by decide)
  · exact hk.c.sub_left (Lay.ctxSub (by decide))

end

/-- After `headPre`: `k = min (16 - o, n)` bytes copied into the buffer, the
arguments advanced, and `a3` zero iff the buffer is full. -/
structure HeadMid (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (x : List Byte) (D : Addr)
    (n : Nat) (m₀ : Mem) (k : Nat) (s : State) : Prop where
  env : Env V sp s
  kmin : k = min (16 - x.length % 16) n
  k1 : 1 ≤ k
  k16 : x.length % 16 + k ≤ 16
  kn : k ≤ n
  s4 : s.gpr .s4 = D + BitVec.ofNat 64 k
  s5 : s.gpr .s5 = BitVec.ofNat 64 (n - k)
  a3 : s.gpr .a3 = BitVec.ofNat 64 (x.length % 16 + k) - BitVec.ofNat 64 16
  data : DataOk (V .s1) (V .s0) s D n
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H
  buf : bytesAt s.mem (V .s1 + BitVec.ofNat 64 32) (x.length % 16 + k) =
    bytesAt m₀ (V .s1 + BitVec.ofNat 64 32) (x.length % 16) ++ bytesAt m₀ D k
  hY : blockAt s.mem (V .s1 + BitVec.ofNat 64 yo) = blockAt m₀ (V .s1 + BitVec.ofNat 64 yo)
  fw : Frame [⟨V .s1 + BitVec.ofNat 64 (32 + x.length % 16), k⟩] m₀ s.mem

/-- `a3 = a - 16` is zero iff `a = 16`, for `a ≤ 16`. -/
theorem eval_sub16 {s : State} {a : Nat} (h : s.gpr .a3 = BitVec.ofNat 64 a - BitVec.ofNat 64 16)
    (ha : a ≤ 16) : isa.eval (.zero .a3) s = some (decide (a = 16)) := by
  show some (s.gpr .a3 == 0) = _
  rw [h]
  congr 1
  by_cases h16 : a = 16
  · subst h16; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 16 ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, toNat64 (by omega_arith), toNat64 (by omega_arith)] at this
      simp at this; omega_arith
    simp only [h16, decide_false, beq_eq_false_iff_ne.mpr this]

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0)) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- Filling the buffer: `minLen`, the copy and the comparison with 16. -/
theorem headPre_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : AbsIn V sp yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa headPre s (fun s' => ∃ k, HeadMid V sp yo H x D n s.mem k s') := by
  obtain hlt : x.length % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn64 : n < 2 ^ 64 := h.data.lt
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.s6 h.s5 (by omega_arith) hn64) fun s₁ ⟨h5, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - x.length % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h5
  obtain hk1 : 1 ≤ k := by omega_arith
  obtain hk16 : x.length % 16 + k ≤ 16 := by omega_arith
  obtain hkn : k ≤ n := by omega_arith
  obtain e30 : s₁.gpr .s1 = V .s1 := (hg _ (by decide) (by decide)).trans he.s1
  obtain e24 : s₁.gpr .s4 = D := (hg _ (by decide) (by decide)).trans h.s4
  obtain e25 : s₁.gpr .s5 = BitVec.ofNat 64 n := (hg _ (by decide) (by decide)).trans h.s5
  obtain e26 : s₁.gpr .s6 = BitVec.ofNat 64 (x.length % 16) := (hg _ (by decide) (by decide)).trans h.s6
  obtain h₂ : WP isa (.block [.addi .a1 .s1 32, .add .a1 .a1 .s6, mov .a0 .s4, .add .s4 .s4 .a2,
      .sub .s5 .s5 .a2, .add .s6 .s6 .a2]) s₁ (fun s₂ : State =>
      s₂.gpr .a0 = D ∧ s₂.gpr .a1 = V .s1 + BitVec.ofNat 64 (32 + x.length % 16) ∧
      s₂.gpr .s4 = D + BitVec.ofNat 64 k ∧ s₂.gpr .s5 = BitVec.ofNat 64 (n - k) ∧
      s₂.gpr .s6 = BitVec.ofNat 64 (x.length % 16 + k) ∧ s₂.gpr .a2 = BitVec.ofNat 64 k ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s₂.gpr r = s₁.gpr r) ∧
      Keeps s₁ s₂) := by
    crun [e30, e24, e25, e26, h5, mov]
    exact ⟨by rw [add_ofNat_assoc], ofNat_sub64 hkn hn64, ofNat_add64 _ _,
      fun r a b c d e => by simp [a, b, c, d, e], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨h3, h4, h24, h25, h26, h5', hg₂, hk₂⟩ => ?_)
  obtain hk₂' := hk.trans hk₂
  obtain lp : LoopPre s₂ D (V .s1 + BitVec.ofNat 64 (32 + x.length % 16)) k := by
    refine ⟨h3, h4, h5', hk1, by omega_arith, ?_, ?_, ?_⟩
    · rw [hk₂'.rd, hk₂'.wr]; exact (h.data.take hkn).rd
    · rw [hk₂'.wr]; exact he.perm.stC (by omega_arith)
    · exact (h.data.take hkn).st.sub_right (Lay.stSub (by omega_arith))
  refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_)
  rw [hk₂'.mem] at hm₃
  have g₃ : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s₃.gpr r = s₂.gpr r := lo.other
  obtain e26' : s₃.gpr .s6 = BitVec.ofNat 64 (x.length % 16 + k) :=
    (g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h26
  obtain h₄ : WP isa (.block [.addi .a3 .s6 (-16)]) s₃ (fun s₄ : State =>
      s₄.gpr .a3 = BitVec.ofNat 64 (x.length % 16 + k) - BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .a3 → s₄.gpr r = s₃.gpr r) ∧ Keeps s₃ s₄) := by
    crun [e26']
    exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono h₄ fun s₄ ⟨h6, g₄, hk₄⟩ => ?_
  obtain g : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s₄.gpr r = s₂.gpr r :=
    fun r a b c d e => by rw [g₄ r e, g₃ r a b c d e]
  obtain k4rd : s₄.rd = s₂.rd := by rw [hk₄.rd, lo.keeps.1]
  obtain k4wr : s₄.wr = s₂.wr := by rw [hk₄.wr, lo.keeps.2.1]
  obtain k4sp : s₄.sp = s₂.sp := by rw [hk₄.sp, lo.keeps.2.2]
  -- The bytes copied, and the buffer.
  obtain hdk := length_bytesAt s.mem D k
  obtain fw : Frame [⟨V .s1 + BitVec.ofNat 64 (32 + x.length % 16), k⟩] s.mem s₄.mem := by
    rw [hk₄.mem, hm₃]; exact writeBytes_frame' _ hdk
  refine ⟨k, he.keep (fun r hr => by
      rw [g r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide),
        hg₂ r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide),
        hg r (by revert r; decide) (by revert r; decide)])
      (by rw [k4sp, hk₂'.sp]) (by rw [k4rd, hk₂'.rd]) (by rw [k4wr, hk₂'.wr]),
    hk'.symm, hk1, hk16, hkn, ?_, ?_, h6, h.data.of_eq (by rw [k4rd, hk₂'.rd]) (by rw [k4wr, hk₂'.wr]) (by rw [k4sp, hk₂'.sp]),
    ?_, ?_, ?_, fw⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h24]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h25]
  · rw [blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by omega_arith), h.hH]
  · rw [hk₄.mem, hm₃, show V .s1 + BitVec.ofNat 64 (32 + x.length % 16) =
        V .s1 + BitVec.ofNat 64 32 + BitVec.ofNat 64 (x.length % 16) from (add_ofNat_assoc _ _ _).symm]
    have := bytesAt_writeBytes s.mem (V .s1 + BitVec.ofNat 64 32) (x.length % 16)
      (bytesAt s.mem D k) (by rw [hdk]; omega_arith)
    rwa [hdk] at this
  · exact blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by omega_arith)) (by omega_arith) (by omega_arith)

/-- After `headPre`: the buffer absorbed if full. -/
theorem headPost_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {k : Nat} {s : State}
    (h : HeadMid V sp yo H x D n m₀ k s) :
    WP isa (.ite (.zero .a3) (ghash1 yo .s1 32) (.block [])) s
      (fun s' => ∃ j, j = k ∧ AbsMid V sp yo H x D n m₀ j s') := by
  have he := h.env
  obtain hk1 := h.k1; have hk16 := h.k16; have hkn := h.kn; have hkm := h.kmin
  obtain hdk := length_bytesAt m₀ D k
  refine WP.ite (decide (x.length % 16 + k = 16)) (eval_sub16 h.a3 hk16) (fun ht => ?_) (fun hf => ?_)
  · -- The buffer is full: absorbed.
    obtain h16 : x.length % 16 + k = 16 := by simpa using ht
    refine WP.mono (ghash1_ok L hyo he .s1 32 (.inl rfl) (by decide) (P := V .s1 + BitVec.ofNat 64 32)
      (by rw [he.s1]) (Lay.st_st (.inl (by omega_arith)) (by omega_arith) (by decide))
      (L.st_w (by decide) (.inr ⟨by decide, by decide⟩))
      (he.stk'.st.sub_left (Lay.stSub (d := 32) (n := 16) (by decide)))
      (by have := L.sw; rw [Offset.toNat_add_ofNat]; omega_using [this])
      (covers_left (he.perm.stC (by decide))))
      fun s₅ g => ?_
    refine ⟨k, rfl, g.env he, hkn, by rw [g.saved _ (by decide)]; exact h.s4,
      by rw [g.saved _ (by decide)]; exact h.s5, h.data.of_eq g.rd g.wr g.spk, ?_, ?_, .inr (by omega_arith), ?_⟩
    · rw [blockAt_frame (he.sp ▸ g.frame) (ctx_ghFrame L hyo he.stk'), h.hH]
    · intro ha
      refine Proof.Gcm.absorb_complete ha (by rw [hdk]; exact h16)
        (B := bytesAt s.mem (V .s1 + BitVec.ofNat 64 32) 16) ?_ ?_
      · rw [← h16, h.buf, ha.2]
      · rw [g.out, h.hY, h.hH]; rfl
    · exact (buf_absFrame (yo := yo) (V := V) h.fw hk16).trans (gh_absFrame (he.sp ▸ g.frame))
  · -- Not full: the data is used up.
    obtain h16 : x.length % 16 + k < 16 := by simp at hf; omega_arith
    refine WP.block_nil ⟨k, rfl, he, hkn, h.s4, h.s5, h.data, h.hH, fun ha => ?_, .inl (by omega_arith),
      buf_absFrame (yo := yo) (V := V) h.fw hk16⟩
    exact Proof.Gcm.absorb_fill ha (by rw [hdk]; exact h16) h.hY (by rw [hdk]; exact h.buf)

/-- Filling the buffer. -/
theorem head_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : AbsIn V sp yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa (absorbHead yo) s (fun s' => ∃ j, j = min (16 - x.length % 16) n ∧
      AbsMid V sp yo H x D n s.mem j s') :=
  WP.seq (WP.mono (headPre_ok L hyo h hn ho) fun _ ⟨_, hm⟩ =>
    WP.mono (headPost_ok L hyo hm) fun _ ⟨j, hj, h'⟩ => ⟨j, hj.trans hm.kmin, h'⟩)

omit L hyo in
/-- The split of the rest into whole blocks and the last bytes. -/
theorem split_ok {s : State} {D : Addr} {n j : Nat} (hj : j ≤ n) (hn : n < 2 ^ 64)
    (h24 : s.gpr .s4 = D + BitVec.ofNat 64 j) (h25 : s.gpr .s5 = BitVec.ofNat 64 (n - j)) :
    WP isa (.block splitWhole) s fun s' =>
      s'.gpr .a2 = D + BitVec.ofNat 64 j ∧ s'.gpr .a3 = BitVec.ofNat 64 ((n - j) / 16) ∧
      s'.gpr .s4 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .s5 = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16))) ∧
      (∀ r, r ≠ .t0 → r ≠ .a2 → r ≠ .a3 → r ≠ .a5 → r ≠ .a6 → r ≠ .s4 → r ≠ .s5 →
        s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain hand := and15 (BitVec.ofNat 64 (n - j))
  rw [toNat64 (by omega_arith)] at hand
  obtain hsub : BitVec.ofNat 64 (n - j) - BitVec.ofNat 64 ((n - j) % 16) =
      BitVec.ofNat 64 (16 * ((n - j) / 16)) := by
    rw [ofNat_sub64 (Nat.mod_le _ _) (by omega_arith)]; congr 1; omega_arith
  simp only [splitWhole]
  crun [h24, h25, mov, hand, hsub, shr4 (show n - j < 2 ^ 64 by omega_arith), add_ofNat_assoc]
  refine ⟨by congr 1; omega_arith, fun r _ b c d e f g => by simp [b, c, d, e, f, g],
    ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The whole blocks. -/
theorem whole_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid V sp yo H x D n m₀ j s) (hm₀ : bytesAt s.mem D n = bytesAt m₀ D n) :
    WP isa (absorbWhole yo) s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧
      AbsMid V sp yo H x D n m₀ j' s' ∧ n - j' < 16) := by
  have hn' := h.data.lt
  have he := h.env
  refine WP.seq (WP.mono (split_ok h.le hn' h.s4 h.s5) fun s₁ ⟨h5, h6, h24, h25, hg₁, hk₁⟩ => ?_)
  generalize hnb : (n - j) / 16 = nb at h6 h24 h25
  obtain h16 : 16 * nb ≤ n - j := by omega_arith
  obtain he₁ : Env V sp s₁ := he.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr
  obtain hd₁ : DataOk (V .s1) (V .s0) s₁ D n := h.data.of_eq hk₁.rd hk₁.wr hk₁.sp
  refine WP.ite (decide (nb = 0)) (eval_zero h6 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, by omega_arith, ⟨he₁, h.le, by rw [h24]; rfl, by rw [h25]; rfl, hd₁,
      by rw [hk₁.mem]; exact h.hH, fun ha => by rw [hk₁.mem]; exact h.abs ha, h.whole,
      by rw [hk₁.mem]; exact h.frame⟩, by omega_arith⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    obtain hw : (x.length + j) % 16 = 0 := h.whole.resolve_left (by omega_arith)
    obtain hdj := h.data.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
    obtain h29 := he₁.s2; have h30 := he₁.s1; have h31 := he₁.s0
    obtain hyo' : yo < 2048 := by omega_arith
    obtain h₂ : WP isa (.block [.addi .a0 .s2 240, .addi .a1 .s1 yo, .addi .a4 .s0 scrO]) s₁
        (fun s₂ : State => s₂.gpr .a0 = V .s2 + BitVec.ofNat 64 240 ∧
          s₂.gpr .a1 = V .s1 + BitVec.ofNat 64 yo ∧ s₂.gpr .a4 = V .s0 + BitVec.ofNat 64 512 ∧
          (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a4 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂) := by
      refine Steps.wp_addi (by decide) fun t₁ u₁ => Steps.wp_addi (by omega_using [hyo]) fun t₂ u₂ =>
        Steps.wp_addi (by decide) fun t₃ u₃ => WP.block_nil ?_
      refine ⟨?_, ?_, ?_, fun r a b d => ?_, ?_, ?_, ?_, ?_⟩
      · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h29]
      · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h30]
      · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h31]; rfl
      · rw [u₃.other _ d, u₂.other _ b, u₁.other _ a]
      · rw [u₃.mem, u₂.mem, u₁.mem]
      · rw [u₃.rd, u₂.rd, u₁.rd]
      · rw [u₃.wr, u₂.wr, u₁.wr]
      · rw [u₃.sp, u₂.sp, u₁.sp]
    refine WP.seq (WP.mono h₂ fun s₂ ⟨h3', h4', h7', hg₂, hk₂⟩ => ?_)
    obtain he₂ : Env V sp s₂ := he₁.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
    refine WP.mono (ghCall_ok L hyo he₂ (P := D + BitVec.ofNat 64 j) (n := nb) h3' h4'
      (by rw [hg₂ _ (by decide) (by decide) (by decide), h5])
      (by rw [hg₂ _ (by decide) (by decide) (by decide), h6]) h7' (by omega_arith)
      (hdj.st.sub_right (Lay.stSub (by omega_arith))).symm (hdj.w.sub_right (Lay.wSub (by decide)))
      (by rw [hk₂.sp, hk₁.sp]; exact hdj.sk) hdj.fit
      (by rw [hk₂.rd, hk₂.wr, hk₁.rd, hk₁.wr]; exact hdj.rd)) fun s₃ g => ?_
    refine ⟨j + 16 * nb, by omega_arith, ⟨g.env he₂, by omega_arith, ?_, ?_,
      hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr) (g.spk.trans hk₂.sp), ?_, ?_, .inr (by omega_arith),
      ?_⟩, by omega_arith⟩
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide), h24]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide), h25]
    · rw [blockAt_frame (he₂.sp ▸ g.frame) (ctx_ghFrame L hyo he₂.stk'), hk₂.mem, hk₁.mem]; exact h.hH
    · intro ha
      obtain ex : x ++ bytesAt m₀ D (j + 16 * nb) =
          (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * nb) := by
        rw [bytesAt_add, List.append_assoc]
      rw [ex]
      refine Proof.Gcm.absorb_whole (h.abs ha) (by simp [length_bytesAt]; omega_arith)
        (by simp [length_bytesAt]) ?_
      rw [g.out, hk₂.mem, hk₁.mem, h.hH, Proof.Gcm.blocksAt_eq]
      congr 2
      -- The data is as in `m₀`.
      obtain e₁ := congrArg (fun l => l.drop j) hm₀
      obtain e₂ : ∀ m : Mem, (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) :=
        fun m => by
          rw [show n = j + (n - j) by omega_arith, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
            Nat.add_sub_cancel_left]
      simp only [e₂] at e₁
      obtain e₃ := congrArg (fun l => l.take (16 * nb)) e₁
      obtain e₄ : ∀ m : Mem, (bytesAt m (D + BitVec.ofNat 64 j) (n - j)).take (16 * nb) =
          bytesAt m (D + BitVec.ofNat 64 j) (16 * nb) := fun m => by
        rw [show n - j = 16 * nb + (n - j - 16 * nb) by omega_arith, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _)]
      simp only [e₄] at e₃
      exact e₃
    · have := g.frame; rw [hk₂.mem, hk₁.mem, he₂.sp] at this; exact h.frame.trans (gh_absFrame this)

omit L in
/-- The last bytes, buffered. -/
theorem tail_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid V sp yo H x D n m₀ j s) (hj : n - j < 16) (hm₀ : bytesAt s.mem D n = bytesAt m₀ D n) :
    WP isa absorbTail s (AbsOut V sp yo H x (x ++ bytesAt m₀ D n) m₀) := by
  have hn' := h.data.lt
  have he := h.env
  refine WP.ite (decide (n - j = 0)) (eval_zero h.s5 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega_arith
    subst h0
    exact WP.block_nil ⟨he, h.abs, h.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    obtain hw : (x.length + j) % 16 = 0 := h.whole.resolve_left h0
    obtain hdj := h.data.sub (j := j) (k := n - j) (by omega_arith) (by omega_arith)
    have h30 := he.s1
    obtain h₂ : WP isa (.block [mov .a0 .s4, .addi .a1 .s1 32, mov .a2 .s5]) s (fun s₂ : State =>
        s₂.gpr .a0 = D + BitVec.ofNat 64 j ∧ s₂.gpr .a1 = V .s1 + BitVec.ofNat 64 32 ∧
        s₂.gpr .a2 = BitVec.ofNat 64 (n - j) ∧
        (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂) := by
      crun [mov, h.s4, h.s5, h30]
      exact ⟨fun r a b d => by simp [a, b, d], ⟨rfl, rfl, rfl, rfl⟩⟩
    refine WP.seq (WP.mono h₂ fun s₂ ⟨h3', h4', h5', hg₂, hk₂⟩ => ?_)
    obtain lp : LoopPre s₂ (D + BitVec.ofNat 64 j) (V .s1 + BitVec.ofNat 64 32) (n - j) := by
      refine ⟨h3', h4', h5', by omega_arith, by omega_arith, ?_, ?_, ?_⟩
      · rw [hk₂.rd, hk₂.wr]; exact hdj.rd
      · rw [hk₂.wr]; exact he.perm.stC (by omega_arith)
      · exact hdj.st.sub_right (Lay.stSub (by omega_arith))
    refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
    rw [hk₂.mem] at hm₃
    obtain hlen := length_bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j)
    obtain fw : Frame [⟨V .s1 + BitVec.ofNat 64 32, n - j⟩] s.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame' _ hlen
    refine ⟨he.keep (fun r hr => by
      rw [lo.other r (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide) (by revert r; decide),
        hg₂ r (by revert r; decide) (by revert r; decide) (by revert r; decide)])
        (lo.keeps.2.2.trans hk₂.sp) (lo.keeps.1.trans hk₂.rd) (lo.keeps.2.1.trans hk₂.wr), ?_, ?_⟩
    · intro ha
      obtain ex : x ++ bytesAt m₀ D n =
          (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
        rw [List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' h.le]
      obtain ed : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) =
          bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
        obtain e₁ := congrArg (fun l => l.drop j) hm₀
        obtain e₂ : ∀ m : Mem, (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) :=
          fun m => by
            rw [show n = j + (n - j) by omega_arith, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
              Nat.add_sub_cancel_left]
        simpa only [e₂] using e₁
      rw [ex, ← ed]
      refine Proof.Gcm.absorb_tail (h.abs ha) (by simp [length_bytesAt]; omega_arith) (by rw [hlen]; omega_arith) ?_ ?_
      · rw [blockAt_frame fw fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Lay.st_st (.inl (by omega_arith)) (by omega_arith) (by omega_arith)]
      · rw [hm₃]; exact bytesAt_writeBytes_self _ _ _ (by rw [hlen]; omega_arith)
    · exact h.frame.trans ((fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by omega_arith)⟩))

omit L in
theorem AbsMid.data_eq {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid V sp yo H x D n m₀ j s) : bytesAt s.mem D n = bytesAt m₀ D n :=
  bytesAt_frame h.frame (data_absFrame hyo h.data h.env.sp) (by have := h.data.lt; omega_arith)

/-- After the first test: the buffer filled if it holds bytes. -/
theorem absorbFill_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : AbsIn V sp yo H x D n s) (h0 : n ≠ 0) :
    WP isa (absorbFill yo) s (fun s' => ∃ j, j = (if x.length % 16 = 0 then 0 else min (16 - x.length % 16) n) ∧
      AbsMid V sp yo H x D n s.mem j s') := by
  refine WP.ite (decide (x.length % 16 = 0)) (eval_zero h.s6 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have ho : x.length % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, by simp [ho], h.env, by omega_arith, by rw [h.s4, BitVec.add_zero],
      by rw [h.s5, Nat.sub_zero], h.data, h.hH, fun ha => by simpa [bytesAt] using ha, .inr (by omega_arith),
      Frame.refl _ _⟩
  · have ho : x.length % 16 ≠ 0 := by simpa using hf
    exact WP.mono (head_ok L hyo h h0 ho) fun _ ⟨j, hj, hm⟩ => ⟨j, by simp only [ho, ite_false]; exact hj, hm⟩

/-- `absorb yo`. -/
theorem absorb_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : AbsIn V sp yo H x D n s) :
    WP isa (absorb yo) s (AbsOut V sp yo H x (x ++ bytesAt s.mem D n) s.mem) := by
  have hn' := h.data.lt
  refine WP.ite (decide (n = 0)) (eval_zero h.s5 hn') (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨h.env, fun ha => by simpa [bytesAt] using ha, Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.seq (WP.mono (absorbFill_ok L hyo h h0) fun s' ⟨j, _, hj⟩ => ?_)
    refine WP.seq (WP.mono (whole_ok L hyo hj (hj.data_eq hyo)) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact tail_ok hyo hj' hlt (hj'.data_eq hyo)

end

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: padding the buffer (`flush`) and the lengths block (`lens`)

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcm/PPC64LE/Flush.lean`): `flush yo` pads the `s6` buffered bytes
with zeros in `T` and absorbs them (`flush_ok`); `lens yo` stores the
lengths block of `s4` and `s6` bytes in `T`, a byte at a time, and absorbs
it (`lens_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom zeros padLen)
open VG.Proof.Gcm (Absorbed lensBlock)

/-- The regions `flush` and `lens` write, with the stack below `sp` that
`vg_ghash`'s frame uses. -/
abbrev tFrame (st w : Addr) (yo : Nat) (sp : Addr) : List Region :=
  [⟨st + BitVec.ofNat 64 yo, 16⟩, ⟨w + BitVec.ofNat 64 96, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩,
    below sp 2048]

theorem gh_tFrame {st w : Addr} {yo : Nat} {sp : Addr} {m m' : Mem}
    (h : Frame [⟨st + BitVec.ofNat 64 yo, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩, below sp 2048] m m') :
    Frame (tFrame st w yo sp) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

theorem tFrame_T {st w : Addr} {yo : Nat} {sp : Addr} {m m' : Mem}
    (h : Frame [⟨w + BitVec.ofNat 64 96, 16⟩] m m') : Frame (tFrame st w yo sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

theorem write_8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW]; exact congrArg (m.write a 8) (BitVec.setWidth_eq _).symm

/-- The 16 bytes after zeroing. -/
theorem zeroT_bytes (m : Mem) (p : Addr) :
    bytesAt ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) p 16 = zeros 16 := by
  rw [Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl

/-- Before `flush yo` (or `lens yo`). -/
structure FlIn (V : Reg → BitVec 64) (sp : Addr) (H : Block) (s : State) : Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H

/-- After `flush yo`: GHASH has absorbed `x`, from `x₀` absorbed in `m₀`. -/
structure FlOut (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (V .s1 + BitVec.ofNat 64 yo) (V .s1 + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (V .s1 + BitVec.ofNat 64 yo) (V .s1 + BitVec.ofNat 64 32) H x
  frame : Frame (tFrame (V .s1) (V .s0) yo sp) m₀ s.mem

/-- After the copy of the `o` buffered bytes to `T`, padded with zeros. -/
structure FlMid (V : Reg → BitVec 64) (sp : Addr) (yo : Nat) (H : Block) (o : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H
  hT : bytesAt s.mem (V .s0 + BitVec.ofNat 64 96) 16 =
    bytesAt m₀ (V .s1 + BitVec.ofNat 64 32) o ++ zeros (16 - o)
  hY : blockAt s.mem (V .s1 + BitVec.ofNat 64 yo) = blockAt m₀ (V .s1 + BitVec.ofNat 64 yo)
  frame : Frame [⟨V .s0 + BitVec.ofNat 64 96, 16⟩] m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0)) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit hyo in
/-- `T` zeroed. -/
theorem zeroT_ok {s : State} (he : Env V sp s) :
    WP isa (.block [.li .t0 0, .store .d .t0 .s0 tO, .store .d .t0 .s0 (tO + 8)]) s fun s' =>
      s'.mem = (s.mem.writeW (V .s0 + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
        (V .s0 + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h31 := he.s0
  have w₀ := he.perm.wW (show 96 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 104 + 8 ≤ 2560 by decide)
  have a₀ := L.wal8 (d := 96) (by decide) (by decide)
  have a₁ := L.wal8 (d := 104) (by decide) (by decide)
  crun [tO, h31, w₀, w₁, a₀, a₁, write_8]
  exact ⟨by rw [add_ofNat_assoc], fun r a => by simp [a]⟩

/-- The `o` buffered bytes copied to `T`, padded with zeros. -/
theorem flushCopy_ok {H : Block} {o : Nat} {s : State} (h : FlIn V sp H s)
    (h26 : s.gpr .s6 = BitVec.ofNat 64 o) (ho : o < 16) (h0 : o ≠ 0) :
    WP isa (.seq (.block flushPre) copyLoop) s (FlMid V sp yo H o s.mem) := by
  have he := h.env
  have h30 := he.s1; have h31 := he.s0
  refine WP.seq (WP.block_append (WP.mono (zeroT_ok L he) fun s₁ ⟨hm₁, hg₁, hrd₁, hwr₁, hsp₁⟩ => ?_))
  have e30 : s₁.gpr .s1 = V .s1 := (hg₁ _ (by decide)).trans h30
  have e31 : s₁.gpr .s0 = V .s0 := (hg₁ _ (by decide)).trans h31
  have e26 : s₁.gpr .s6 = BitVec.ofNat 64 o := (hg₁ _ (by decide)).trans h26
  have h₂ : WP isa (.block [.addi .a0 .s1 32, .addi .a1 .s0 tO, mov .a2 .s6]) s₁ (fun s₂ : State =>
      s₂.gpr .a0 = V .s1 + BitVec.ofNat 64 32 ∧ s₂.gpr .a1 = V .s0 + BitVec.ofNat 64 96 ∧
      s₂.gpr .a2 = BitVec.ofNat 64 o ∧ (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₂.gpr r = s₁.gpr r) ∧
      Keeps s₁ s₂) := by
    crun [tO, e30, e31, e26, mov, Int.reduceNatCast']
    exact ⟨fun r a b d => by simp [a, b, d], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono h₂ fun s₂ ⟨h3, h4, h5, hg₂, hk₂⟩ => ?_
  have lp : LoopPre s₂ (V .s1 + BitVec.ofNat 64 32) (V .s0 + BitVec.ofNat 64 96) o := by
    refine ⟨h3, h4, h5, by omega_arith, by omega_arith, ?_, ?_, ?_⟩
    · rw [hk₂.rd, hk₂.wr, hrd₁, hwr₁]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [hk₂.wr, hwr₁]; exact he.perm.wC (by omega_arith)
    · exact L.st_w (by omega_arith) (.inr ⟨by decide, by omega_arith⟩)
  refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [hk₂.mem] at hm₃
  -- The memory so far.
  have fz : Frame [⟨V .s0 + BitVec.ofNat 64 96, 16⟩] s.mem s₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have hB₁ : bytesAt s₁.mem (V .s1 + BitVec.ofNat 64 32) o = bytesAt s.mem (V .s1 + BitVec.ofNat 64 32) o :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩))
      (by omega_arith)
  have hlen := length_bytesAt s₁.mem (V .s1 + BitVec.ofNat 64 32) o
  have fc : Frame [⟨V .s0 + BitVec.ofNat 64 96, o⟩] s₁.mem s₃.mem := by
    rw [hm₃]; exact writeBytes_frame' _ hlen
  have f₃ : Frame [⟨V .s0 + BitVec.ofNat 64 96, 16⟩] s.mem s₃.mem :=
    fz.trans (fc.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)
  refine ⟨he.keep (fun r hr => by
      rw [lo.other r (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide) (by revert r; decide),
        hg₂ r (by revert r; decide) (by revert r; decide) (by revert r; decide),
        hg₁ r (by revert r; decide)])
      (by rw [lo.keeps.2.2, hk₂.sp, hsp₁]) (by rw [lo.keeps.1, hk₂.rd, hrd₁])
      (by rw [lo.keeps.2.1, hk₂.wr, hwr₁]), ?_, ?_, ?_, f₃⟩
  · rw [blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), h.hH]
  · rw [hm₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega_arith) (by decide), hlen, hB₁]
    congr 1
    have := zeroT_bytes s.mem (V .s0 + BitVec.ofNat 64 96)
    rw [← hm₁, show (16 : Nat) = o + (16 - o) by omega_arith, bytesAt_add] at this
    have e := congrArg (List.drop o) this
    rw [List.drop_left' (length_bytesAt _ _ _)] at e
    rw [e, show o + (16 - o) = 16 by omega_arith, Spec.Gcm.zeros, List.drop_replicate]
    rfl
  · exact blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)

/-- The padded buffer absorbed. -/
theorem flushGh_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {H : Block} {x : List Byte} {m₀ : Mem} {s : State}
    (h : FlMid V sp yo H (x.length % 16) m₀ s) (h0 : x.length % 16 ≠ 0) :
    WP isa (ghash1 yo .s0 tO) s (FlOut V sp yo H x (x ++ zeros (padLen x.length)) m₀) := by
  have he := h.env
  refine WP.mono (ghash1_ok L hyo he .s0 96 (.inr rfl) (by decide) (P := V .s0 + BitVec.ofNat 64 96)
    (by rw [he.s0]) (L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩))
    (Lay.w_w (.inl (by decide)) (by decide) (by decide))
    (he.stk'.w.sub_left (Lay.wSub (d := 96) (n := 16) (by decide))) (L.w_fit (by decide) (by decide))
    (covers_left (he.perm.wC (by decide))))
    fun s₄ g => ?_
  refine ⟨g.env he, ?_, ?_, ?_⟩
  · rw [blockAt_frame (he.sp ▸ g.frame) (ctx_ghFrame L hyo he.stk'), h.hH]
  · intro ha
    refine Proof.Gcm.absorb_pad ha h0 (B := bytesAt s.mem (V .s0 + BitVec.ofNat 64 96) 16) h.hT ?_
    rw [g.out, h.hY, h.hH]; rfl
  · exact (tFrame_T h.frame).trans (gh_tFrame (he.sp ▸ g.frame))

/-- `flush yo`. -/
theorem flush_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {H : Block} {x : List Byte} {s : State} (h : FlIn V sp H s)
    (h26 : s.gpr .s6 = BitVec.ofNat 64 (x.length % 16)) :
    WP isa (flush yo) s (FlOut V sp yo H x (x ++ zeros (padLen x.length)) s.mem) := by
  have hlt := Nat.mod_lt x.length (show 16 > 0 by decide)
  refine WP.ite (decide (x.length % 16 = 0)) (eval_zero h26 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : x.length % 16 = 0 := by simpa using ht
    rw [Proof.Gcm.padLen_of_mod h0]
    exact WP.block_nil ⟨h.env, h.hH, fun ha => by simpa [zeros] using ha, Frame.refl _ _⟩
  · have h0 : x.length % 16 ≠ 0 := by simpa using hf
    exact WP.seq (WP.mono (flushCopy_ok L hyo (o := x.length % 16) h h26 hlt h0) fun s₃ hm =>
      flushGh_ok L hyo hm h0)

end

/-- The bytes `storeBE 8` stores of a 64-bit word, as GCM's `[x]₆₄`. -/
theorem beBytes_be64 (v : BitVec 64) : ByteLoad.beBytes 8 v = Spec.Gcm.be64 v.toNat := by
  simp only [ByteLoad.beBytes, Spec.Gcm.be64]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show 8 * (8 - 1 - j) = 8 * (7 - j) by omega_using [], Nat.pow_mul]

/-- The 8 bytes of `[8 r]₆₄`. -/
theorem beBytes_lens (x : BitVec 64) : ByteLoad.beBytes 8 (x <<< 3) = Spec.Gcm.be64 (8 * x.toNat) := by
  have : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    simp only [Nat.reducePow, Nat.mul_comm]
  rw [beBytes_be64, this, BitVec.toNat_ofNat, Proof.Gcm.be64_mod]

/-- `[8 s4]₆₄ ‖ [8 s6]₆₄`, the lengths block, stored in `T` a byte at a time. -/
theorem lensStore_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) :
    WP isa (.block Impl.AesGcm.RISCV64.lensBlock) s fun s' =>
      s'.mem = writeBytes (writeBytes s.mem (V .s0 + BitVec.ofNat 64 96)
          (ByteLoad.beBytes 8 (s.gpr .s4 <<< 3)))
        (V .s0 + BitVec.ofNat 64 104) (ByteLoad.beBytes 8 (s.gpr .s6 <<< 3)) ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .t0 → s'.gpr r = s.gpr r) ∧ Keeps' s s' := by
  have h31 := he.s0
  rw [Impl.AesGcm.RISCV64.lensBlock, List.append_assoc, WP.block_append_iff]
  refine Steps.wp_sll (by decide) fun s₁ u₁ => Steps.wp_sll (by decide) fun s₂ u₂ => WP.block_nil ?_
  rw [WP.block_append_iff]
  have hw : ∀ off, off + 8 ≤ 2560 → ∀ j < 8,
      InRegions s₂.wr (s₂.gpr .s0 + BitVec.ofNat 64 (off + j)) 1 := fun off ho j hj => by
    rw [u₂.wr, u₁.wr, u₂.other _ (by decide), u₁.other _ (by decide), h31]
    exact he.perm.wW (by omega_using [ho, hj])
  refine WP.mono (ByteLoad.storeBE_ok (s := s₂) (v := .a0) (tmp := .t0) (n := .s0) (off := tO) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (hw 96 (by decide))) fun s₃ e₃ => ?_
  subst e₃
  refine WP.mono (ByteLoad.storeBE_ok (v := .a1) (tmp := .t0) (n := .s0) (off := tO + 8) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa [RegUpd.gpr_write, RegUpd.wr_write] using hw (tO + 8) (by decide))) fun s₄ e₄ => ?_
  subst e₄
  have a0 : s₂.gpr .a0 = s.gpr .s4 <<< 3 := by rw [u₂.other _ (by decide), u₁.gpr]
  have a1 : s₂.gpr .a1 = s.gpr .s6 <<< 3 := by rw [u₂.gpr, u₁.other _ (by decide)]
  have b0 : s₂.gpr .s0 = V .s0 := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h31]
  have m2 : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨?_, fun r a b c d e => ?_, ⟨?_, ?_, ?_⟩⟩
  · simp only [RegUpd.mem_write, RegUpd.gpr_write_of_ne _ _ (show Reg.s0 ≠ .t0 by decide),
      RegUpd.gpr_write_of_ne _ _ (show Reg.a1 ≠ .t0 by decide), a0, a1, b0, m2, tO, Nat.reduceAdd]
  · simp only [RegUpd.gpr_write_of_ne _ _ e]; rw [u₂.other _ b, u₁.other _ a]
  · simp only [RegUpd.rd_write]; exact u₂.rd.trans u₁.rd
  · simp only [RegUpd.wr_write]; exact u₂.wr.trans u₁.wr
  · simp only [RegUpd.sp_write]; exact u₂.sp.trans u₁.sp

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0)) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- The lengths block of `s4` and `s6` bytes, absorbed. -/
theorem lens_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {H : Block} {s : State} (he : Env V sp s)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H) :
    WP isa (lens yo) s fun s' => Env V sp s' ∧
      blockAt s'.mem (V .s2 + BitVec.ofNat 64 240) = H ∧
      blockAt s'.mem (V .s1 + BitVec.ofNat 64 yo) = ghashFrom H (blockAt s.mem (V .s1 + BitVec.ofNat 64 yo))
        [Spec.Gcm.ofBytes (lensBlock (s.gpr .s4).toNat (s.gpr .s6).toNat)] ∧
      (∀ r, r ∈ preserved → s'.gpr r = s.gpr r) ∧
      Frame (tFrame (V .s1) (V .s0) yo sp) s.mem s'.mem := by
  refine WP.seq (WP.mono (lensStore_ok he) fun s₂ ⟨hm₂, hg₂, hk₂⟩ => ?_)
  have he₂ : Env V sp s₂ := he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  have hlen := ByteLoad.beBytes_length 8 (s.gpr .s4 <<< 3)
  have hcat := writeBytes_append s.mem (V .s0 + BitVec.ofNat 64 96) (ByteLoad.beBytes 8 (s.gpr .s4 <<< 3))
    (ByteLoad.beBytes 8 (s.gpr .s6 <<< 3)) (by simp [ByteLoad.beBytes_length])
  rw [hlen, add_ofNat_assoc] at hcat
  rw [hcat] at hm₂
  have fT : Frame [⟨V .s0 + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact writeBytes_frame' _ (by simp [ByteLoad.beBytes_length])
  have hT : bytesAt s₂.mem (V .s0 + BitVec.ofNat 64 96) 16 =
      lensBlock (s.gpr .s4).toNat (s.gpr .s6).toNat := by
    rw [hm₂, bytesAt_writeBytes_self' _ _ (by simp [ByteLoad.beBytes_length]) (by decide), beBytes_lens,
      beBytes_lens]; rfl
  have hY₂ : blockAt s₂.mem (V .s1 + BitVec.ofNat 64 yo) = blockAt s.mem (V .s1 + BitVec.ofNat 64 yo) :=
    blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  have hH₂ : blockAt s₂.mem (V .s2 + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), hH]
  refine WP.mono (ghash1_ok L hyo he₂ .s0 96 (.inr rfl) (by decide) (P := V .s0 + BitVec.ofNat 64 96)
    (by rw [he₂.s0]) (L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩))
    (Lay.w_w (.inl (by decide)) (by decide) (by decide))
    (he₂.stk'.w.sub_left (Lay.wSub (d := 96) (n := 16) (by decide))) (L.w_fit (by decide) (by decide))
    (covers_left (he₂.perm.wC (by decide))))
    fun s₃ g => ?_
  refine ⟨g.env he₂, ?_, ?_, fun r hr => by
      rw [g.saved r hr]; exact hg₂ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide), ?_⟩
  · rw [blockAt_frame (he₂.sp ▸ g.frame) (ctx_ghFrame L hyo he₂.stk'), hH₂]
  · have hb : blockAt s₂.mem (V .s0 + BitVec.ofNat 64 96) =
        Spec.Gcm.ofBytes (lensBlock (s.gpr .s4).toNat (s.gpr .s6).toNat) := by
      rw [blockAt, hT]
    rw [g.out, hY₂, hH₂, hb]
  · have := g.frame; rw [he₂.sp] at this; exact (tFrame_T fT).trans (gh_tFrame this)

end

end VG.Proof.AesGcm.RISCV64
