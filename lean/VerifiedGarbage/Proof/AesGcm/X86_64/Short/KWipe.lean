module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Mid
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM's short path on x86-64: the keystream wiped

Untrusted: everything here is checked by Lean. `kWipe` stores `zmm4` to the
`⌈(nc + 1) / 4⌉` groups of `K` (`kWipe_ok`), writing nothing else and
leaving every register but `rax`, `rdx` and `zmm4`; what it stores does not
matter to the proofs, so `SM` holds after it (`SM.kWipe`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Proof.AesGcm.X86_64

/-- The count of `K`'s groups in `rax`, `rdx` at `K` and `zmm4` written. -/
theorem kWipeSetup_ok {W : Addr} {nc : Nat} (s : State) (h15 : s.gpr .r15 = W)
    (hnc : s.mem.readW (W + BitVec.ofNat 64 280) 64 = BitVec.ofNat 64 nc) (hnc32 : nc < 32)
    (r280 : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 280) 8) :
    WP isa (.block kWipeSetup) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 ((nc + 4) / 4) ∧ t.gpr .rdx = W + BitVec.ofNat 64 1024 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm4] s t := by
  have e₁ : BitVec.ofNat 64 nc + BitVec.ofNat 64 4 = BitVec.ofNat 64 (nc + 4) := ofNat_add_ofNat _ _
  have e₂ : BitVec.ofNat 64 (nc + 4) >>> 2 = BitVec.ofNat 64 ((nc + 4) / 4) := shr2 _ (by omega)
  apply WP.of_runBlock
  refine ⟨_, by xrun [kWipeSetup, ptr, imm, execShift, h15, hnc, r280, ncO, kO, e₁, e₂], ?_⟩
  refine ⟨?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, fun r hr l hl => ?_⟩
  · simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, e₁, e₂]
  · simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h15]
  · simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h₁, h₂]
  · simp only [List.mem_singleton] at hr
    simp only [VOp.exec]
    rw [State.zlane_setV_ne _ _ hr]
    rfl

/-- A group of `K` zeroed: the 64 bytes at `rdx`. -/
theorem kWipeStep_ok (t : State) {a : Addr} (hrdx : t.gpr .rdx = a) (hw : InRegions t.wr a 64) :
    WP isa (.block kWipeBody) t fun t' =>
      Frame [⟨a, 64⟩] t.mem t'.mem ∧ t'.gpr .rdx = a + BitVec.ofNat 64 64 ∧
        t'.gpr .rax = t.gpr .rax - 1 ∧ t'.zf = some (t.gpr .rax - 1 == 0) ∧
        (∀ r, r ≠ .rdx → r ≠ .rax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ ZKeep [] t t' := by
  have e : t.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int) = a := by
    rw [hrdx, BitVec.ofInt_natCast, BitVec.add_zero]
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [kWipeBody, imm, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      State.store512_eq, State.ea, e, hw, ite_true, Option.bind_some]
    rfl, ?_⟩
  refine ⟨(Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _), ?_, ?_, ?_, ?_, rfl, rfl,
    fun _ _ _ _ => rfl⟩
  · simp [gpr_setReg, gpr_arithFlags, hrdx]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [zf_arithFlags, gpr_setReg, gpr_arithFlags]
  · intro r h₁ h₂; simp [gpr_setReg, gpr_arithFlags, h₁, h₂]

/-- `kWipe`: the `⌈(nc + 1) / 4⌉` groups of `K` written, nothing else, and
every register but `rax`, `rdx` and `zmm4` kept. -/
theorem kWipe_ok {W : Addr} {nc : Nat} (s : State) (h15 : s.gpr .r15 = W)
    (hnc : s.mem.readW (W + BitVec.ofNat 64 280) 64 = BitVec.ofNat 64 nc) (hnc32 : nc < 32)
    (hw : Covers [⟨W, 2560⟩] s.wr) :
    WP isa kWipe s fun t =>
      Frame [⟨W + BitVec.ofNat 64 1024, 512⟩] s.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [.xmm4] s t := by
  have wR : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 d) n :=
    fun h => in_off hw h (by decide)
  refine WP.seq (WP.mono (kWipeSetup_ok s h15 hnc hnc32 (in_left (wR (by decide))))
    fun s₁ ⟨ax₁, dx₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  have hnk : 1 ≤ (nc + 4) / 4 ∧ (nc + 4) / 4 ≤ 8 := by omega_arith
  generalize (nc + 4) / 4 = nk at ax₁ hnk ⊢
  have hwK : ∀ k < nk, InRegions s.wr (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (64 * k)) 64 := fun k hk => by
    rw [BitVec.add_assoc, ofNat_add_ofNat]; exact wR (by omega_arith)
  generalize hK : W + BitVec.ofNat 64 1024 = K at dx₁ hwK ⊢
  refine WP.loop (M := isa) (body := .block kWipeBody) (c := .ne)
    (fun (m : Nat) (t : State) => ∃ k, m = nk - k ∧ k < nk ∧
      t.gpr .rdx = K + BitVec.ofNat 64 (64 * k) ∧ t.gpr .rax = BitVec.ofNat 64 (nk - k) ∧
      Frame [⟨K, 512⟩] s.mem t.mem ∧ (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [.xmm4] s t) ?_ (nk - 0) s₁
    ⟨0, rfl, by omega_arith, by rw [dx₁]; simp, ax₁, by rw [m₁]; exact Frame.refl _ _, g₁, rd₁, wr₁, z₁⟩
  rintro m t ⟨k, rfl, hk, dxt, axt, ft, gt, rdt, wrt, zt⟩
  refine WP.mono (kWipeStep_ok t dxt (by rw [wrt]; exact hwK k hk))
    fun t' ⟨f', dx', ax', zf', g', rd', wr', z'⟩ => ?_
  have hax : t.gpr .rax - 1 = BitVec.ofNat 64 (nk - (k + 1)) := by
    rw [axt, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub (by omega_arith) (by omega_arith)]; congr 1
  have f'' : Frame [⟨K, 512⟩] s.mem t'.mem := ft.trans (f'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base K (by omega_arith)⟩)
  have gt' : ∀ r, r ≠ .rax → r ≠ .rdx → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₂ h₁, gt r h₁ h₂]
  have zt' : ZKeep [.xmm4] s t' := zt.trans (z'.mono (by simp))
  have hz : t'.zf = some (decide (nk - k = 1)) := by
    rw [zf', axt, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, sub_beq (a := nk - k) (b := 1) (by omega_arith)
      (by omega_arith)]
  by_cases he' : k + 1 = nk
  · left
    exact ⟨by simp [eval, hz]; omega_arith, f'', gt', by rw [rd', rdt], by rw [wr', wrt], zt'⟩
  · right
    refine ⟨by simp [eval, hz]; omega_arith, nk - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, ?_,
      by rw [ax', hax], f'', gt', by rw [rd', rdt], by rw [wr', wrt], zt'⟩
    rw [dx', show 64 * (k + 1) = 64 * k + 64 by omega_arith, ← ofNat_add_ofNat, BitVec.add_assoc]

end VG.Proof.AesGcm.X86_64.Short
