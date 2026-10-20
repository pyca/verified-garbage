module

public import VerifiedGarbage.Proof.Dsa.X86_64.Product
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks

/-! # Frames for construction of the joint exponentiation table -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The base arrays used by table construction may change; the modulus may not. -/
structure JointCtx (t : State) (P : Addr) (w n : Nat) (minv : BitVec 64) : Prop where
  mod : ModCtx t P (slot w 8) w minv n
  scrT : Scr t P (slot w 8 + tabBytes w)

theorem JointCtx.exp {t : State} {P : Addr} {w n : Nat} {minv : BitVec 64}
    (h : JointCtx t P w n minv) :
    CExpCtx t P w minv n (wv t.mem P (slot w aR2) w) :=
  ⟨h.mod.good, h.scrT, h.mod.modulus, h.mod.inverse, rfl⟩

/-- The table lies past all eight base arrays. -/
theorem joint_arrays_entry {P : Addr} {w j : Nat} {xs : List Nat} {m m' : Mem}
    (hf : Arrays P w xs m m') (hxs : ∀ k ∈ xs, k < 8)
    (hn : P.toNat + (slot w 8 + tabBytes w) ≤ 2 ^ 64) (hj : j < 16) :
    wv m' P (slot w (8 + j)) w = wv m P (slot w (8 + j)) w := by
  apply hf.wv_eq
  · intro k hk
    right
    have h1 := slot_le (w := w) (hxs k hk)
    have h2 := slot_mono w (show 8 ≤ 8 + j by omega)
    omega
  · have := ent_le w hj; omega

/-- Copying a base array keeps the modulus, header, table, and other arrays. -/
theorem jointCopy_ok {t : State} {P : Addr} {w n : Nat} {minv : BitVec 64}
    (hc : JointCtx t P w n minv) (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    {o a : Nat} (ho : o < 8) (ha : a < 8) (hoa : o ≠ a) (hon : o ≠ aN) :
    WP isa (seqs (Crt.copyArr o a)) t fun u => JointCtx u P w n minv ∧
      wv u.mem P (slot w o) w = wv t.mem P (slot w a) w ∧
      Arrays P w [o] t.mem u.mem ∧ Keep mmRegs t u := by
  refine WP.mono (copyArr_ok hc.mod.good (Nat.le_refl _) (by omega) (by omega) ho ha hoa)
    fun u ⟨hv, hf, hk⟩ => ?_
  have hfa : Arrays P w [o] t.mem u.mem := Arrays.of_outside (List.mem_singleton_self o) hf
    (Nat.le_refl _) (by omega)
  have hn := hc.mod.good.scr.nowrap
  have hg : Good u P (slot w 8) w minv := ⟨hc.mod.good.scr.congr hk.2.2,
    (hk.gpr (by decide)).trans hc.mod.good.rdi, hfa.hdr hc.mod.good.hdr⟩
  refine ⟨⟨⟨hg, ?_, ?_⟩, hc.scrT.congr hk.2.2⟩, hv, hfa, hk⟩
  · exact (hfa.wv_of_not_mem (by decide) (by simpa using Ne.symm hon) hn).trans hc.mod.modulus
  · rw [hfa.word0_of_not_mem (by decide) (by simpa using Ne.symm hon) hn (by omega)]
    exact hc.mod.inverse

/-- A selected-backend product also preserves the complete table. -/
theorem jointProduct_ok (M : Mont) {t : State} {P : Addr} {w n : Nat} {minv : BitVec 64}
    (hc : JointCtx t P w n minv) (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    {o a b : Nat} (huse : MmUse o a b) (hb : wv t.mem P (slot w b) w < n) :
    WP isa (M.mm o a b) t fun u => JointCtx u P w n minv ∧
      wv u.mem P (slot w o) w < n ∧
      wv u.mem P (slot w o) w * 2 ^ (64 * w) % n =
        wv t.mem P (slot w a) w * wv t.mem P (slot w b) w % n ∧
      Arrays P w [aAcc, aTmp, o] t.mem u.mem ∧ Keep mmRegs t u :=
  WP.mono (mont_step M hc.mod (Nat.le_refl _) hw (by omega) huse hb)
    fun u ⟨hc', hl, hv, hf, hk⟩ => ⟨⟨hc', hc.scrT.congr hk.2.2⟩, hl, hv, hf, hk⟩

end VG.Proof.Dsa.X86_64
