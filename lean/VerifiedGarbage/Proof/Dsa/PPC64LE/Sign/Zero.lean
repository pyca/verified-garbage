module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# DSA signing on PPC64LE: a key that fails the checks

`zeroLoop_ok`: the loop that zeroes `N` octets, which key derivation shares
(`Derive/Zero.lean`). `zeroOut_ok`: `out`'s `2 q_len` octets (`out` from the
header's word `hOut`) are zeroed, and `r3 := 0`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign

/-- The registers `zeroOut` writes. -/
def zeroRegs : List Reg := [.r0, .r3, .r16, .r17]

/-- The zeroing loop: `N > 0` octets at `out` (`r16`, `N` in `r17`) := 0
(`r0`). -/
theorem zeroLoop_ok {s : State} {out : Addr} {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 64) (ho : Scr s out N)
    (h0 : s.gpr .r0 = 0) (h16 : s.gpr .r16 = off out 0) (h17 : s.gpr .r17 = BitVec.ofNat 64 N) :
    WP isa (Precompute.countLoop .r17 [.stb .r0 .r16 0, .addi .r16 .r16 1]) s fun t =>
      (Spec.Rsa.bytesAt t.mem out N = List.replicate N 0 ∧ Outside out 0 N s.mem t.mem) ∧
        Keep [.r16, .r17] s t := by
  have hno := ho.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r0 = 0 ∧ t.gpr .r16 = off out i ∧ Outside out 0 i s.mem t.mem ∧
      (∀ i' < i, t.mem (off out i') = 0) ∧ Keep [.r16, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.stb .r0 .r16 0, .addi .r16 .r16 1] ++
      ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := N) hN' hN Inv (fun i hi t ⟨t0, t16, tout, tz, tk⟩ hc => ?_)
    ⟨h0, h16, Outside.refl _ _ _ _, fun _ h => absurd h (by omega), Keep.refl _ _⟩ h17)
    fun t ⟨_, _, tout, tz, tk⟩ => ⟨⟨?_, tout⟩, tk⟩
  · have hst : WP isa (.block [.stb .r0 .r16 0, .addi .r16 .r16 1, .subi .r17 .r17 1]) t fun t' =>
        t' = (({ t with mem := t.mem.write (off out i) 1 ((0 : BitVec 64).setWidth 8) } :
          State).write .r16 (off out (i + 1))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1) := by
      prun [t0, t16, exec_stb (show Reg.r16 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        (ho.congr tk.wr).st (d := i) (n := 1) (by omega)]
    refine WP.mono hst fun t' e => ?_
    subst e
    have hw1 := write1_outside t.mem out (d := i) ((0 : BitVec 64).setWidth 8) (by omega)
    refine ⟨⟨by gsimp; exact t0, by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; exact (tout.mono (Nat.le_refl _) (by omega)).trans (hw1.mono (by omega) (by omega))
    · intro i' hi'
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · rw [hw1 _ (by rw [Bignum.PPC64LE.ofs_off0 out (by omega)]; omega)]; exact tz i' hi'
      · rw [write1_self]; rfl
    · exact tk.trans' (((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono
  · refine List.eq_replicate_iff.mpr ⟨by simp [Spec.Rsa.bytesAt], fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact tz i (List.mem_range.mp hi)

theorem zeroOut_ok {s : State} {L : Lay} {key sig dig out : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hw : word s.mem L.S hOut = out) (ho : Scr s out (2 * L.ql)) :
    WP isa zeroOut s fun t =>
      (Spec.Rsa.bytesAt t.mem out (2 * L.ql) = List.replicate (2 * L.ql) 0 ∧
        Outside out 0 (2 * L.ql) s.mem t.mem ∧ t.gpr .r3 = 0) ∧ Keep zeroRegs s t := by
  have hZ := hL.z256
  have hql := hL.ql
  have hno := ho.nowrap
  unfold zeroOut
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  have hld : InRegions (s.rd ++ s.wr) (s.gpr .r21 + BitVec.ofNat 64 hOut) 8 := by
    rw [hr.r21]; exact hs.ld (show hOut + 8 ≤ L.Z by simp only [hOut]; omega)
  refine WP.mono (WP.keep [.r16] (Q := fun u => u.gpr .r16 = out ∧ u.mem = s.mem)
    (by prun [exec_ld (by decide) hld]; rw [hr.r21]; exact hw) (by decide)) fun s₁ ⟨⟨a16, m1⟩, k1⟩ => ?_
  refine WP.mono (getQ_ok (hr.keep k1) .r17) fun s₂ ⟨⟨a17, m2⟩, k2⟩ => ?_
  refine WP.mono (WP.keep [.r0, .r17] (Q := fun u => u.gpr .r0 = 0 ∧ u.gpr .r16 = off out 0 ∧
      u.gpr .r17 = BitVec.ofNat 64 (2 * L.ql) ∧ u.mem = s.mem)
    (by
      prun [a17, (k2.gpr .r16 (by decide)).trans a16, m2, m1]
      simp only [off, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.two_mul, and_self]
      exact ⟨rfl, trivial⟩) (by decide)) fun s₃ ⟨⟨b0, b16, b17, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  refine WP.seq (WP.mono (zeroLoop_ok (N := 2 * L.ql) (by omega) (by omega) (ho.congr k13.wr) b0 b16 b17)
    fun t ⟨⟨tz, tout⟩, tk⟩ => ?_)
  refine WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = 0 ∧ u.mem = t.mem) (by prun []; rfl) (by decide))
    fun u ⟨⟨u3, mu⟩, ku⟩ => ⟨⟨by rw [mu]; exact tz, by rw [mu, ← m3]; exact tout, u3⟩,
      ((k13.trans tk).trans ku).mono (by decide)⟩

end VG.Proof.Dsa.PPC64LE
