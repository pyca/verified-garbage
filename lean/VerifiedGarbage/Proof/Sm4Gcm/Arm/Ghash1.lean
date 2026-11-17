module

public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Env
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Run
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Sm4Gcm.Arm
public import VerifiedGarbage.Proof.Framework.Block

/-! ### `Sm4Gcm.Arm.Blocks`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: small blocks shared by the pieces

Untrusted: everything here is checked by Lean. `cmp r, #0` (`cmp0_ok`), and
`minLen`: `r3 := min (16 - r6, r5)`, from the carry of a comparison
(`minLen_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm

/-- `cmp r, #0` sets `Z` iff `r` holds 0. -/
theorem cmp0_ok (s : State) (r : Reg) {n : Nat} (h : s.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    ∃ s', runBlock isa [.cmp r (imm 0)] s = some s' ∧ s'.z = decide (n = 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [z_subFlags, h]; rw [z_cmp hn (by decide)]
  all_goals rfl

/-- `cmp r, #k`. -/
theorem cmpk_ok (s : State) (r : Reg) {n k : Nat} (h : s.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32)
    (hk : k < 2 ^ 32) (he : encodable (BitVec.ofNat 32 k) = true) :
    ∃ s', runBlock isa [.cmp r (imm k)] s = some s' ∧ s'.z = decide (n = k) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [he], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [z_subFlags, h]; rw [z_cmp hn hk]
  all_goals rfl

/-- What a block that keeps everything but some registers leaves. -/
structure Keeps (s s' : State) : Prop where
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

/-- `r3 := min (16 - r6, r5)`. -/
theorem minLen_ok (s : State) {o n : Nat} (h6 : s.gpr .r6 = BitVec.ofNat 32 o)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (ho : o ≤ 16) (hn : n < 2 ^ 32) :
    WP isa minLen s fun s' => s'.gpr .r3 = BitVec.ofNat 32 (min (16 - o) n) ∧
      (∀ r, r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨s₁, run₁, h₁⟩ : ∃ s₁, runBlock isa [.mov .r3 (imm 16), .dp .sub .r3 .r3 (.reg .r6), .cmp .r5 (.reg .r3),
      .mov .r12 (imm 0), .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r3 = BitVec.ofNat 32 (16 - o) ∧ s₁.z = !decide (16 - o ≤ n) ∧
      (∀ r, r ≠ .r3 → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h6, ofNat_sub32 ho (by decide)]
    · simp only [z_subFlags, c_subFlags, gpr_setReg, z_setReg, c_setReg, ite_true, ite_false, reduceCtorEq,
        h5, h6, ofNat_sub32 ho (by decide), toNat32 hn, toNat32 (show 16 - o < 2 ^ 32 by omega_using [])]
      cases decide (16 - o ≤ n) <;> rfl
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hr3, hz, hg, hk⟩ := h₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (!decide (16 - o ≤ n)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · refine WP.run (Q := fun s' => s' = s₁.setReg .r3 (s₁.gpr .r5)) ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, fun r h₁ h₂ => ?_, hk.trans ⟨rfl, rfl, rfl, rfl⟩⟩
    · rw [gpr_setReg_self, hg .r5 (by decide) (by decide), h5]
      simp at ht; rw [Nat.min_eq_right (by omega_using [ht])]
    · simp only [gpr_setReg, h₁, ite_false]; exact hg r h₁ h₂
  · refine WP.block_nil ⟨?_, hg, hk⟩
    simp at hf; rw [hr3, Nat.min_eq_left (by omega_using [hf])]

end VG.Proof.Sm4Gcm.Arm

end

end

/-!
# SM4-GCM on ARMv7: GHASH over blocks of the state, `T` or the data

Untrusted: everything here is checked by Lean. `ghCall_ok` is the frame of a
call of `vg_ghash` from a state whose registers are its arguments (the hash
subkey at `ctx + 240`, the accumulator at `st + yo`, the working space at
`W + 512`), and `ghash1 yo b o` continues the accumulator over the block at
`P = b + o` (`ghash1_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- What a call of `vg_ghash` from `s` leaves in `s'`, for the accumulator
at `Y`, the working space at `W + 512` and the data `ds` (as blocks). -/
structure GhOut (s : State) (c w sp : BitVec 32) (Y : Addr) (ds : List Block) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  spk : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) (blockAt s.mem Y) ds

theorem GhOut.env {s s' : State} {c st w sp k7 k8 : BitVec 32} {Y : Addr} {ds : List Block}
    (h : GhOut s c w sp Y ds s') (he : Env c st w sp k7 k8 s) : Env c st w sp k7 k8 s' :=
  he.of_saved h.saved h.spk h.rd h.wr

theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [blockAt m p] := by
  simp [blocksAt]

/-- The arguments of a call, from a state whose registers are its arguments,
for `n` blocks at the 32-bit pointer `P`. -/
theorem ghCall_mk {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env c st w sp k7 k8 s) {P : BitVec 32} {n : Nat}
    (h0 : s.gpr .r0 = c + BitVec.ofNat 32 240) (h1 : s.gpr .r1 = st + BitVec.ofNat 32 yo)
    (h2 : s.gpr .r2 = P) (h3 : s.gpr .r3 = BitVec.ofNat 32 n) (h12 : s.gpr .r12 = w + BitVec.ofNat 32 512)
    (hfit : P.toNat + 16 * n ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16 * n⟩)
    (hpw : (⟨State.addr P, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below sp).Disjoint ⟨State.addr P, 16 * n⟩) (hpr : Covers [⟨State.addr P, 16 * n⟩] (s.rd ++ s.wr)) :
    GhCall s (c + BitVec.ofNat 32 240) (st + BitVec.ofNat 32 yo) P (w + BitVec.ofNat 32 512) n := by
  have eH := L.cA (d := 240) (by decide)
  have eY := L.stA (d := yo) (by omega_using [hyo])
  have eS := L.wA (d := 512) (by decide)
  have hk := he.sp
  refine ⟨h0, h1, h2, h3, h12, by rw [hk]; exact L.sp8, by rw [L.cN (by decide)]; have := L.cw; omega_using [this],
    by rw [L.stN (by omega_using [hyo])]; have := L.sw; omega_using [hyo, this], hfit, by rw [L.wN (by decide)]; have := L.ww; omega_using [this],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [eH, eY, eS, hk]
  · exact L.ctx_st (by decide) (by omega_using [hyo])
  · exact L.ctx_w (by decide) (by decide)
  · exact hpy
  · exact L.st_w (by omega_using [hyo]) (.inr ⟨by decide, by decide⟩)
  · exact hpw
  · exact L.stk_ctx (by decide)
  · exact L.stk_st (by omega_using [hyo])
  · exact hpk
  · exact L.stk_w (by decide)
  · exact covers_cons (he.perm.ctxC (by decide)) hpr
  · exact covers_cons (he.perm.stC (by omega_using [hyo])) (he.perm.wC (by decide))

/-- The call itself, from a state whose registers are its arguments, for
`n` blocks at the 32-bit pointer `P`. -/
theorem ghCall_ok [VG.Proof.Gcm.Arm.GhashLaw] {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env c st w sp k7 k8 s) {P : BitVec 32} {n : Nat}
    (h0 : s.gpr .r0 = c + BitVec.ofNat 32 240) (h1 : s.gpr .r1 = st + BitVec.ofNat 32 yo)
    (h2 : s.gpr .r2 = P) (h3 : s.gpr .r3 = BitVec.ofNat 32 n) (h12 : s.gpr .r12 = w + BitVec.ofNat 32 512)
    (hfit : P.toNat + 16 * n ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16 * n⟩)
    (hpw : (⟨State.addr P, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below sp).Disjoint ⟨State.addr P, 16 * n⟩) (hpr : Covers [⟨State.addr P, 16 * n⟩] (s.rd ++ s.wr)) :
    WP isa ghFrame s (GhOut s c w sp (State.addr st + BitVec.ofNat 64 yo) (blocksAt s.mem (State.addr P) n)) := by
  have eH := L.cA (d := 240) (by decide)
  have eY := L.stA (d := yo) (by omega_using [hyo])
  have eS := L.wA (d := 512) (by decide)
  have hc := ghCall_mk L hyo he h0 h1 h2 h3 h12 hfit hpy hpw hpk hpr
  refine WP.mono (gh_call hc) fun s' h => ⟨h.rd, h.wr, h.sp, h.saved, ?_, ?_⟩
  · have f := h.frame; rw [eY, eS, he.sp] at f; exact f
  · have o := h.out; rw [eH, eY] at o; exact o

/-- The arguments of `ghash1`. -/
theorem ghArgs_ok {c st w sp k7 k8 : BitVec 32} {s : State} (he : Env c st w sp k7 k8 s) (yo : Nat) (b : Reg) (o : Nat)
    (hb : b = .r10 ∨ b = .r11) (hyo : encodable (BitVec.ofNat 32 yo) = true)
    (ho : encodable (BitVec.ofNat 32 o) = true) :
    ∃ s', runBlock isa [addI .r0 .r9 hO, addI .r1 .r10 yo, addI .r2 b o, .mov .r3 (imm 1),
        addI .r12 .r11 scrO] s = some s' ∧
      s'.gpr .r0 = c + BitVec.ofNat 32 240 ∧ s'.gpr .r1 = st + BitVec.ofNat 32 yo ∧
      s'.gpr .r2 = s.gpr b + BitVec.ofNat 32 o ∧ s'.gpr .r3 = BitVec.ofNat 32 1 ∧
      s'.gpr .r12 = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  rcases hb with rfl | rfl
  all_goals
    refine ⟨_, by arun [hyo, ho], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h9]
    · simp [gpr_setReg, h10]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h11]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩

/-- `ghash1 yo b o`, for the block at `P = b + o`. -/
theorem ghash1_ok [VG.Proof.Gcm.Arm.GhashLaw] {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env c st w sp k7 k8 s) (b : Reg) (o : Nat) (hb : b = .r10 ∨ b = .r11)
    (ho : encodable (BitVec.ofNat 32 o) = true) {P : BitVec 32}
    (hP : s.gpr b + BitVec.ofNat 32 o = P) (hfit : P.toNat + 16 ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16⟩)
    (hpw : (⟨State.addr P, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below sp).Disjoint ⟨State.addr P, 16⟩) (hpr : Covers [⟨State.addr P, 16⟩] (s.rd ++ s.wr)) :
    WP isa (ghash1 yo b o) s (GhOut s c w sp (State.addr st + BitVec.ofNat 64 yo) [blockAt s.mem (State.addr P)]) := by
  obtain ⟨s₁, run₁, h0, h1, h2, h3, h12, hkeep, hk⟩ := ghArgs_ok he yo b o hb
    (by rcases hyo with rfl | rfl <;> decide) ho
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide))
    hk.sp hk.rd hk.wr
  refine WP.mono (ghCall_ok L hyo he₁ (P := P) (n := 1) h0 h1 (by rw [h2, hP]) h3 h12 (by omega_using [hfit])
    (by simpa using hpy) (by simpa using hpw) (by simpa using hpk)
    (by rw [hk.rd, hk.wr]; simpa using hpr)) fun s' h => ?_
  exact ⟨h.rd.trans hk.rd, h.wr.trans hk.wr, h.spk.trans hk.sp,
    fun r hr hl => by
      rw [h.saved r hr hl]
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hl | exact hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide),
    hk.mem ▸ h.frame, by rw [h.out, blocksAt_one, hk.mem]⟩

end VG.Proof.Sm4Gcm.Arm
