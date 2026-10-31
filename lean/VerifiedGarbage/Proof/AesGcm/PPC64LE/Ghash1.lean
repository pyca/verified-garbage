module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Callee
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env

/-!
# AES-GCM on PPC64LE: GHASH over blocks of the state, `T` or the data

Untrusted: everything here is checked by Lean. As on ARMv7: `ghCall_ok` is
a call of `vg_ghash` from a state whose registers are its arguments (the
hash subkey at `ctx + 240`, the accumulator at `st + yo`, the working space
at `W + 512`), and `ghash1 yo b o` continues the accumulator over the block
at `P = b + o` (`ghash1_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
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
  frame : Frame [⟨Y, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem (c + BitVec.ofNat 64 240)) (blockAt s.mem Y) ds

theorem GhOut.env {s s' : State} {c w : Addr} {Y : Addr} {ds : List Block} {V : Reg → BitVec 64}
    {sp : Addr} (h : GhOut s c w Y ds s') (he : Env V sp s) : Env V sp s' :=
  he.of_saved h.saved h.spk h.rd h.wr

theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [blockAt m p] := by
  simp [blocksAt]

/-- The arguments of a call of `vg_ghash`, for `n` blocks at `P`. -/
theorem ghCall_mk {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31)) {yo : Nat}
    (hyo : yo = 0 ∨ yo = 16) {s : State} (he : Env V sp s) {P : Addr} {n : Nat}
    (h3 : s.gpr .r3 = V .r29 + BitVec.ofNat 64 240) (h4 : s.gpr .r4 = V .r30 + BitVec.ofNat 64 yo)
    (h5 : s.gpr .r5 = P) (h6 : s.gpr .r6 = BitVec.ofNat 64 n) (h7 : s.gpr .r7 = V .r31 + BitVec.ofNat 64 512)
    (hn : n < 2 ^ 64)
    (hpy : (⟨V .r30 + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16 * n⟩)
    (hpw : (⟨P, 16 * n⟩ : Region).Disjoint ⟨V .r31 + BitVec.ofNat 64 512, 256⟩)
    (hpr : Covers [⟨P, 16 * n⟩] (s.rd ++ s.wr)) :
    GhCall s (V .r29 + BitVec.ofNat 64 240) (V .r30 + BitVec.ofNat 64 yo) P
      (V .r31 + BitVec.ofNat 64 512) n := by
  refine ⟨h3, h4, h5, h6, h7, hn, L.ctx_st (by decide) (by omega), L.ctx_w (by decide) (by decide),
    hpy, L.st_w (by omega) (.inr ⟨by decide, by decide⟩), hpw, ?_, ?_⟩
  · exact Covers.cons (he.perm.ctxC (by decide)) (Covers.cons hpr
      (Covers.cons (covers_left (he.perm.stC (by omega))) (covers_left (he.perm.wC (by decide)))))
  · exact Covers.cons (he.perm.stC (by omega)) (he.perm.wC (by decide))

/-- The call itself, from a state whose registers are its arguments, for `n`
blocks at `P`. -/
theorem ghCall_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31)) {yo : Nat}
    (hyo : yo = 0 ∨ yo = 16) {s : State} (he : Env V sp s) {P : Addr} {n : Nat}
    (h3 : s.gpr .r3 = V .r29 + BitVec.ofNat 64 240) (h4 : s.gpr .r4 = V .r30 + BitVec.ofNat 64 yo)
    (h5 : s.gpr .r5 = P) (h6 : s.gpr .r6 = BitVec.ofNat 64 n) (h7 : s.gpr .r7 = V .r31 + BitVec.ofNat 64 512)
    (hn : n < 2 ^ 64)
    (hpy : (⟨V .r30 + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16 * n⟩)
    (hpw : (⟨P, 16 * n⟩ : Region).Disjoint ⟨V .r31 + BitVec.ofNat 64 512, 256⟩)
    (hpr : Covers [⟨P, 16 * n⟩] (s.rd ++ s.wr)) :
    WP isa ghCall s (GhOut s (V .r29) (V .r31) (V .r30 + BitVec.ofNat 64 yo) (blocksAt s.mem P n)) :=
  WP.mono (gh_call (ghCall_mk L hyo he h3 h4 h5 h6 h7 hn hpy hpw hpr)) fun _ h =>
    ⟨h.rd, h.wr, h.sp, h.saved, h.frame, h.out⟩

/-- `ghash1`'s arguments, for the block at `P = b + o`. -/
theorem ghArgs_ok {V : Reg → BitVec 64} {sp : Addr} {yo : Nat}
    (hyo : yo = 0 ∨ yo = 16) {s : State} (he : Env V sp s) (b : Reg) (o : Nat)
    (hb : b = .r30 ∨ b = .r31) (ho : o < 2 ^ 15) {P : Addr} (hP : s.gpr b + BitVec.ofNat 64 o = P) :
    WP isa (.block [.addi .r3 .r29 240, .addi .r4 .r30 yo, .addi .r5 b o, .li .r6 1,
      .addi .r7 .r31 scrO]) s (fun s₁ : State => s₁.gpr .r3 = V .r29 + BitVec.ofNat 64 240 ∧
        s₁.gpr .r4 = V .r30 + BitVec.ofNat 64 yo ∧ s₁.gpr .r5 = P ∧ s₁.gpr .r6 = BitVec.ofNat 64 1 ∧
        s₁.gpr .r7 = V .r31 + BitVec.ofNat 64 512 ∧
        (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁) := by
  have h29 := he.r29; have h30 := he.r30; have h31 := he.r31
  have hyo' : yo < 2 ^ 15 := by omega
  rcases hb with rfl | rfl <;>
  · crun [scrO, h29, h30, h31, hyo', ho, hP]
    exact ⟨by rw [← hP]; simp only [h30, h31], fun r a b c d e => by simp [a, b, c, d, e], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- `ghash1 yo b o`, for the block at `P = b + o`. -/
theorem ghash1_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31)) {yo : Nat}
    (hyo : yo = 0 ∨ yo = 16) {s : State} (he : Env V sp s) (b : Reg) (o : Nat)
    (hb : b = .r30 ∨ b = .r31) (ho : o < 2 ^ 15) {P : Addr} (hP : s.gpr b + BitVec.ofNat 64 o = P)
    (hpy : (⟨V .r30 + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hpw : (⟨P, 16⟩ : Region).Disjoint ⟨V .r31 + BitVec.ofNat 64 512, 256⟩)
    (hpr : Covers [⟨P, 16⟩] (s.rd ++ s.wr)) :
    WP isa (ghash1 yo b o) s (GhOut s (V .r29) (V .r31) (V .r30 + BitVec.ofNat 64 yo) [blockAt s.mem P]) := by
  have hargs := ghArgs_ok hyo he b o hb ho hP
  refine WP.seq (WP.mono hargs fun s₁ ⟨h3, h4, h5, h6, h7, hkeep, hk⟩ => ?_)
  have he₁ : Env V sp s₁ := he.keep (fun r hr => hkeep r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
  refine WP.mono (ghCall_ok L hyo he₁ (P := P) (n := 1) h3 h4 h5 h6 h7 (by decide)
    (by simpa using hpy) (by simpa using hpw) (by rw [hk.rd, hk.wr]; simpa using hpr)) fun s' h => ?_
  exact ⟨h.rd.trans hk.rd, h.wr.trans hk.wr, h.spk.trans hk.sp,
    fun r hr => by
      rw [h.saved r hr]
      exact hkeep r (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide),
    hk.mem ▸ h.frame, by rw [h.out, blocksAt_one, hk.mem]⟩

end VG.Proof.AesGcm.PPC64LE
