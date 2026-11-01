module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env

/-!
# AES-GCM on RISCV64: GHASH over blocks of the state, `T` or the data

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
    (hk.st.sub_left (Lay.stSub (by omega))).symm, hpk.symm, ?_, hpf, hk.al, hk.ge, ?_, ?_⟩
  · have := L.sw; rw [Offset.toNat_add_ofNat]; omega
  · exact Covers.cons (he.perm.ctxC (by decide)) (Covers.cons hpr
      (Covers.cons (covers_left (he.perm.stC (by omega))) (covers_left (he.perm.wC (by decide)))))
  · exact Covers.cons (he.perm.stC (by omega)) (he.perm.wC (by decide))

/-- The call itself, from a state whose registers are its arguments, for `n`
blocks at `P`. -/
theorem ghCall_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0)) {yo : Nat}
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
  refine Steps.wp_addi (by decide) fun s₁ u₁ => Steps.wp_addi (by omega) fun s₂ u₂ =>
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
theorem ghash1_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0)) {yo : Nat}
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
