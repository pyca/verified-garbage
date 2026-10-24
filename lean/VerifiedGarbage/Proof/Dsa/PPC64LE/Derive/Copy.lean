module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad

/-!
# DSA key derivation on PPC64LE: the masked copy

`maskCopy_ok`: the `N` octets at `src`, each and'ed with the mask of `c` in
`r20`, to `dst`, a buffer apart from them: `dst` gets the octets if `c`,
else zeros.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE

theorem mask_byte (v : BitVec 64) (c : Bool) : (v &&& mask c).setWidth 8 = if c then v.setWidth 8 else 0 := by
  cases c
  · have : mask false = 0#64 := rfl
    rw [this, BitVec.and_zero]; rfl
  · have : mask true = BitVec.allOnes 64 := rfl
    rw [this, BitVec.and_allOnes]; rfl

/-- The registers `maskCopy` writes. -/
def maskCopyRegs : List Reg := [.r0, .r14, .r16, .r17]

/-- `maskCopy`: the `N` octets at `src` (`r14`), and'ed with the mask of `c`
(`r20`), to `dst` (`r16`); the pointers past them. -/
theorem maskCopy_ok {s : State} {src dst : Addr} {N : Nat} {c : Bool} (hN : 0 < N) (hN' : N < 2 ^ 64)
    (ho : Scr s dst N) (hrd : ∀ i < N, InRegions (s.rd ++ s.wr) (off src i) 1)
    (hsep : ∀ i < N, ∀ x, ofs dst x < N → off src i ≠ x)
    (h14 : s.gpr .r14 = src) (h16 : s.gpr .r16 = dst) (h17 : s.gpr .r17 = BitVec.ofNat 64 N)
    (h20 : s.gpr .r20 = mask c) :
    WP isa Derive.maskCopy s fun t =>
      (Spec.Rsa.bytesAt t.mem dst N = (if c then Spec.Rsa.bytesAt s.mem src N else List.replicate N 0) ∧
        Outside dst 0 N s.mem t.mem ∧ t.gpr .r14 = off src N ∧ t.gpr .r16 = off dst N) ∧
        Keep maskCopyRegs s t := by
  have hno := ho.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off src i ∧ t.gpr .r16 = off dst i ∧ Outside dst 0 i s.mem t.mem ∧
      (∀ i' < i, t.mem (off dst i') = if c then s.mem (off src i') else 0) ∧ Keep maskCopyRegs s t
  unfold Derive.maskCopy Precompute.countLoop
  refine WP.mono (wp_countdown (body := .block ([.lbz .r0 .r14 0, .logic .and .r0 .r0 .r20, .stb .r0 .r16 0,
      .addi .r14 .r14 1, .addi .r16 .r16 1] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := N) hN' hN Inv (fun i hi t ⟨t14, t16, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [h14, off, BitVec.add_zero], by rw [h16, off, BitVec.add_zero], Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega), Keep.refl _ _⟩ h17)
    fun t ⟨t14, t16, tout, tb, tk⟩ => ⟨⟨?_, tout, t14, t16⟩, tk⟩
  · have t20 : t.gpr .r20 = mask c := (tk.gpr .r20 (by decide)).trans h20
    have hst : WP isa (.block [.lbz .r0 .r14 0, .logic .and .r0 .r0 .r20, .stb .r0 .r16 0, .addi .r14 .r14 1,
        .addi .r16 .r16 1, .subi .r17 .r17 1]) t fun t' =>
        (t'.gpr .r14 = off src (i + 1) ∧ t'.gpr .r16 = off dst (i + 1) ∧
          t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.write (off dst i) 1 ((((t.mem.read (off src i) 1).setWidth 64) &&& mask c).setWidth 8)) ∧
          Keep maskCopyRegs t t' := by
      refine WP.keep _ ?_ (by decide)
      prun [t14, t16, t20, exec_lbz' (show Reg.r14 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        exec_stb (show Reg.r16 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        (by rw [tk.rd, tk.wr]; exact hrd i hi : InRegions (t.rd ++ t.wr) (off src i) 1),
        (ho.congr tk.wr).st (d := i) (n := 1) (by omega)]
    refine WP.mono hst fun t' ⟨⟨a14, a16, a17, am⟩, ka⟩ => ⟨⟨a14, a16, ?_, ?_, tk.trans' ka⟩, a17⟩
    · have hw1 := write1_outside t.mem dst (d := i)
        ((((t.mem.read (off src i) 1).setWidth 64) &&& mask c).setWidth 8) (by omega)
      rw [am]; exact (tout.mono (Nat.le_refl _) (by omega)).trans (hw1.mono (by omega) (by omega))
    · intro i' hi'
      have hw1 := write1_outside t.mem dst (d := i)
        ((((t.mem.read (off src i) 1).setWidth 64) &&& mask c).setWidth 8) (by omega)
      rw [am]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · rw [hw1 _ (by rw [Bignum.PPC64LE.ofs_off0 dst (by omega)]; omega)]; exact tb i' hi'
      · have hs : t.mem (off src i') = s.mem (off src i') := by
          refine tout _ (Or.inr ?_)
          by_contra hcon
          exact hsep i' hi (off src i') (by omega) rfl
        rw [write1_self, mask_byte, read_one', hs]
  · rw [Spec.Rsa.bytesAt]
    rw [show (List.range N).map (fun i => t.mem (dst + BitVec.ofNat 64 i)) =
        (List.range N).map (fun i => if c then s.mem (off src i) else 0) from
      List.map_congr_left fun i hi => tb i (List.mem_range.mp hi)]
    cases c
    · refine List.eq_replicate_iff.mpr ⟨by simp, fun b hb => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
      rfl
    · rfl

end VG.Proof.Dsa.PPC64LE
