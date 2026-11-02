module
public import VerifiedGarbage.Impl.Bignum.Arm.SetSmallFn
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Bignum.Arm.SetSmallArgs
import VerifiedGarbage.Proof.Bignum.Arm.SetSmall
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Small-integer initialization through the shared RSA array layout -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf numAt Layout)
open VG.Proof.X25519.Arm (Rest)

theorem outside_workspace {m m' : Mem} {base : Addr} {size o n : Nat}
    (outside : Outside base o n m m') (fit : o + n ≤ size) : Frame [⟨base, size⟩] m m' := by
  intro a ha
  have h := ha ⟨base, size⟩ (by simp)
  change ¬ ((a - base).toNat + 1 ≤ size) at h
  exact outside a (by simp only [ofs]; omega)

theorem outside_array_keeps {m m' : Mem} {base : Addr} {len w o : Nat}
    (outside : Outside base (arrAt w o) (8 * w) m m') (size : 8 * len < 2 ^ 64) :
    Proof.Rsa.Mont.Keeps base len w o m m' := by
  intro i hi separate
  have sep := separate o (by simp)
  apply outside
  change (base + BitVec.ofNat 64 i - base).toNat < arrAt w o ∨
    arrAt w o + 8 * w ≤ (base + BitVec.ofNat 64 i - base).toNat
  rw [Mem.sub_ofNat_toNat _ (by omega)]
  omega

theorem setSmallFnBody_ok (s : State) {base : BitVec 32} {len o : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (ho : o < 8) (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o) :
    WP isa setSmallFnBody s fun t =>
      let w := wOf s.mem (State.addr base)
      numAt t.mem (State.addr base) w o = (s.gpr .r5).toNat ∧
      w32 t.mem (State.addr base) (arrAt w o) = (s.gpr .r5).toNat ∧
      Outside (State.addr base) (arrAt w o) (8 * w) s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let w := wOf s.mem (State.addr base)
  have hw : 2 ≤ w := layout.1
  have fits : arrAt w 8 ≤ 8 * len := layout.2.2.1
  have arrayFits := Nat.le_trans (array_end_le ho) fits
  have bound : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base ws.nowrap (Nat.le_refl _) layout
  rw [setSmallFnBody, WP.seq_iff]
  refine WP.mono (setSmallArgs_ok s ws bound header ho ptr index) ?_
  rintro u ⟨p0, p4, count, zero, mem, rest⟩
  have ctx : ZeroCtx u base (8 * len) (arrAt w o) (2 * w) :=
    ⟨ws.nowrap, by omega, by rw [rest.wr]; exact ⟨_, ws.writable, Region.contains_self _ _⟩⟩
  refine WP.mono (setSmall_ok u ctx (by omega) p0 p4 count zero) ?_
  rintro t ⟨value, low, outside, keep⟩
  rw [mem] at outside
  rw [rest.gpr .r5 (by decide)] at value low
  have eq : 4 * (2 * w) = 8 * w := by omega
  rw [eq] at outside
  exact ⟨by simpa only [numAt_native] using value, low, outside,
    outside_workspace outside (by omega),
    (rest.mono (by decide)).trans (keep.mono (by decide))⟩

theorem setSmallFn_ok (s : State) {base : BitVec 32} {len o : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (ho : o < 8) (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o)
    (read : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (sep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa setSmallFn s fun t =>
      let w := wOf s.mem (State.addr base)
      numAt t.mem (State.addr base) w o = (s.gpr .r5).toNat ∧
      w32 t.mem (State.addr base) (arrAt w o) = (s.gpr .r5).toNat ∧
      Outside (State.addr base) (arrAt w o) (8 * w) s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t ∧ t.gpr .r0 = base := by
  rw [setSmallFn, WP.seq_iff]
  refine WP.mono (setSmallFnBody_ok s ws layout ho ptr index) ?_
  rintro u ⟨value, low, outside, frame, rest⟩
  refine WP.mono (restoreBase_ok u
    (by rw [rest.rd, rest.wr, rest.sp]; exact read) (saved_base_kept frame sep saved rest.sp)) ?_
  rintro t ⟨out, mem, keep⟩
  rw [← mem] at value low outside frame
  exact ⟨value, low, outside, frame, rest.trans (keep.mono (by decide)), out⟩

end VG.Proof.Bignum.Arm
