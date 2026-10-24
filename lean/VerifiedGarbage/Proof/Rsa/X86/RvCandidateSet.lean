module

public import VerifiedGarbage.Proof.Rsa.X86.RvMont
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Rsa.X86.RvWindowOps
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.TCB.X86.Isa

/-! # Initializing one candidate -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem candSet_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat}
    (h : KS g s0 A liveM AW [wR] V slotsExp s) (zero : A aZ = 0)
    (candidate : V sCand < 100) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.candSet s fun t =>
      KS g s0 (upd (upd A mG (V sCand + 2)) mY (A aO)) liveExp
        (upd AW wRc (AW wR)) [wRc, wR] V slotsExp t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.candSet
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_w (o := mG) (a := aZ) (by decide) (by simp [liveM]) (by decide)
    (by decide)) fun s1 ⟨h1, _, _⟩ => ?_)
  rw [zero] at h1
  refine WP.seq (wp_movS (h1.readSlot (by simp [slotsExp] : sCand ∈ slotsExp)) fun s2 U _ => ?_)
  have h2 := h1.of_rest U.keeps (by decide) U.mem
  refine wp_addS rfl fun s3 D _ => ?_
  have h3 := h2.of_rest D.keeps (by decide) D.mem
  have number : (s3.gpr .ecx).toNat = V sCand + 2 := by
    rw [D.gpr, U.gpr, BitVec.toNat_add, BitVec.toNat_ofNat]
    change (V sCand % 2 ^ 32 + 2) % 2 ^ 32 = _
    omega
  refine VG.Proof.Rsa.X86.KeyRt.lowPtr_ok h3.rt (j := mG) (by decide) fun u hu K m p => ?_
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeLow_ok hu (j := mG) (by decide) p)
    fun s4 ⟨_, keep, val, rest, _⟩ => ?_
  rw [m, kw_nar] at keep val
  rw [K.1 _ (by decide)] at val
  have r4 : Keeps opRegs s3 s4 := (K.mono (by decide)).trans (rest.mono (by decide))
  have h4 := h3.write_w keep (by decide : mG < nArr) (by simp) r4 val (by decide) (by simp)
  rw [number, h3.arrs mG (by simp), upd_self] at h4
  simp only [Nat.zero_div, Nat.mul_zero, Nat.add_zero, upd_twice] at h4
  refine WP.seq (WP.mono (h4.copy_w (o := mY) (a := aO) (by decide) (by simp [liveM]) (by decide)
    (by decide)) fun s5 ⟨h5, _, _⟩ => ?_)
  rw [upd_ne _ _ (by decide : aO ≠ mG)] at h5
  refine WP.mono (h5.copy_W (o := wRc) (a := wR) (by decide) (by simp) (by decide)
    (by decide)) fun t ⟨ht, _⟩ => ?_
  exact ht.mono (by intro j hj; exact ⟨by simp only [liveExp, liveM, List.mem_cons, List.not_mem_nil, or_false] at *; grind, rfl⟩)
    (by simp) (by intro d hd; exact ⟨hd, rfl⟩)

end VG.Proof.Rsa.X86.Recover
