module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
public import VerifiedGarbage.Spec.HashId
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP on x86-64: the selectors

`selPrologue` copies the selectors, stack arguments `jH` and `jG`, to
their slots, and stores the lengths of the hash functions they name
(`selW`): `selPro_ok`, for hash functions `hs` whose keys are distinct and
below `2^31` (`Keys`) and whose digests are at most 64 bytes (`HsOk`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Dispatch.X86_64 (FlagsOnly)

/-- The hash functions' digest lengths: `HashId.mgf1`'s `hLen` of the key,
at most 64. -/
def lenOf (k : Nat) : Nat := ((Spec.HashId.mgf1 k).map (·.len)).getD 0

/-- The hash functions a selector chooses among: distinct keys below `2^31`,
each with the digest length of the hash function `HashId.mgf1` names, at
most 64 bytes. -/
structure HsOk (hs : List (Nat × Stream)) : Prop extends Keys hs where
  len : ∀ p ∈ hs, p.2.D = lenOf p.1
  le : ∀ p ∈ hs, p.2.D ≤ 64

/-- The slots `selPrologue` stores to, over `W`: the selectors `kH` and
`kG`, `H`'s length `D` and the three lengths computed from it, and `G`'s
`DG`. -/
def selW (W : Nat → BitVec 64) (kH kG D DG : Nat) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd W 37 (BitVec.ofNat 64 kH)) 39 (BitVec.ofNat 64 D))
    40 (BitVec.ofNat 64 (D + 1))) 41 (BitVec.ofNat 64 (2 * D + 1))) 42 (BitVec.ofNat 64 (2 * D + 2)))
    38 (BitVec.ofNat 64 kG)) 43 (BitVec.ofNat 64 DG)

theorem frame_wF {F : Addr} (hF : F.toNat + frameBytes + 8 ≤ 2 ^ 64) {m m' : Mem}
    (hf : Frame [⟨F, frameBytes⟩] m m') {d : Nat} (hd : d + 8 ≤ frameBytes) (v : BitVec 64) :
    Frame [⟨F, frameBytes⟩] m (m'.writeW (off F d) v) :=
  hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- A stack argument, read at `off F (frameBytes + 8 + 8 j)`, to the slot `d`. -/
theorem argSlot_ok {u : State} {F : Addr} (hsp : u.gpr .rsp = F) (hsc : Scr u F frameBytes) {j d : Nat}
    {v : BitVec 64} (hin : InRegions (u.rd ++ u.wr) (off F (frameBytes + 8 + 8 * j)) 8)
    (hv : u.mem.readW (off F (frameBytes + 8 + 8 * j)) 64 = v) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block (argSlot j d)) u fun u' => Keep [.rax] u u' ∧ u'.gpr .rax = v ∧
      u'.mem = u.mem.writeW (off F d) v := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.gpr .rax = v ∧ u'.mem = u.mem.writeW (off F d) v) ?_ rfl)
    fun u' ⟨⟨a, b⟩, k⟩ => ⟨k, a, b⟩
  xrun [argSlot, arg, ea_sp, hsp, hin, hv, hsc.st (d := d) hd]

theorem zx64 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `consts D`: the four lengths from `hLen = D`. -/
theorem consts_ok {u : State} {F : Addr} (hsp : u.gpr .rsp = F) (hsc : Scr u F frameBytes) {D : Nat}
    (hD : D ≤ 64) :
    WP isa (.block (consts D)) u fun u' => Keep [.rax] u u' ∧
      u'.mem = (((u.mem.writeW (off F sHD) (BitVec.ofNat 64 D)).writeW (off F sH1) (BitVec.ofNat 64 (D + 1))).writeW
        (off F sH2) (BitVec.ofNat 64 (2 * D + 1))).writeW (off F sH3) (BitVec.ofNat 64 (2 * D + 2)) := by
  refine WP.mono (WP.keep [.rax] ?_ rfl) fun u' ⟨a, k⟩ => ⟨k, a⟩
  xrun [consts, im, ea_sp, hsp, hsc.st (d := sHD) (by decide), hsc.st (d := sH1) (by decide),
    hsc.st (d := sH2) (by decide), hsc.st (d := sH3) (by decide), zx64 (show D < 2 ^ 32 by omega),
    zx64 (show D + 1 < 2 ^ 32 by omega), zx64 (show 2 * D + 1 < 2 ^ 32 by omega),
    zx64 (show 2 * D + 2 < 2 ^ 32 by omega)]

/-- MGF1's length `D`. -/
theorem gd_ok {u : State} {F : Addr} (hsp : u.gpr .rsp = F) (hsc : Scr u F frameBytes) {D : Nat}
    (hD : D ≤ 64) :
    WP isa (.block [.mov32 .rax (im D), .store (sp sGD) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off F sGD) (BitVec.ofNat 64 D) := by
  refine WP.mono (WP.keep [.rax] ?_ rfl) fun u' ⟨a, k⟩ => ⟨k, a⟩
  xrun [im, ea_sp, hsp, hsc.st (d := sGD) (by decide), zx64 (show D < 2 ^ 32 by omega)]

theorem keep_of_flags {u u' : State} (h : FlagsOnly u u') : Keep [] u u' :=
  ⟨fun r _ => h.gpr r, h.rd, h.wr⟩

variable (hs : List (Nat × Stream))

/-- `selPrologue`: the selectors to their slots, and the lengths of the
hash functions they name, `(kH, HH)` and `(kG, GG)` of `hs`. -/
theorem selPro_ok (hok : HsOk hs) {kH kG : Nat} {HH GG : Stream} (hkH : (kH, HH) ∈ hs) (hkG : (kG, GG) ∈ hs)
    {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W)
    {jH jG : Nat} (hinH : InRegions (u.rd ++ u.wr) (off F (frameBytes + 8 + 8 * jH)) 8)
    (hinG : InRegions (u.rd ++ u.wr) (off F (frameBytes + 8 + 8 * jG)) 8)
    (harg : ∀ m', Frame [⟨F, frameBytes⟩] u.mem m' →
      m'.readW (off F (frameBytes + 8 + 8 * jH)) 64 = BitVec.ofNat 64 kH ∧
        m'.readW (off F (frameBytes + 8 + 8 * jG)) 64 = BitVec.ofNat 64 kG) :
    WP isa (selPrologue hs jH jG) u fun u' => Lay u' F S ∧ Keep [.rax] u u' ∧
      Rep u'.mem F S V (selW W kH kG HH.D GG.D) ∧ Frame [⟨F, frameBytes⟩] u.mem u'.mem := by
  have G' := L.geo
  have hF := L.Fw
  have hsc := L.frScr
  have hDH := hok.le _ hkH
  have hDG := hok.le _ hkG
  -- `Scr` and the stack pointer, for a state keeping the registers and regions of `u`
  have scK : ∀ {rs} {t : State}, Keep rs u t → .rsp ∉ rs → t.gpr .rsp = F ∧ Scr t F frameBytes :=
    fun k hr => ⟨(k.gpr hr).trans L.rsp, Scr.of_mem (k.2.2 ▸ L.fr) (by omega)⟩
  refine WP.seq (WP.mono (argSlot_ok L.rsp hsc hinH (harg _ (Frame.refl _ _)).1 (d := sSelH) (by decide))
    fun u1 ⟨k1, ax1, m1⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (u2 : State) => Lay u2 F S ∧ Keep [.rax] u u2 ∧
      u2.mem = ((((u.mem.writeW (off F sSelH) (BitVec.ofNat 64 kH)).writeW (off F sHD) (BitVec.ofNat 64 HH.D)).writeW
        (off F sH1) (BitVec.ofNat 64 (HH.D + 1))).writeW (off F sH2) (BitVec.ofNat 64 (2 * HH.D + 1))).writeW
        (off F sH3) (BitVec.ofNat 64 (2 * HH.D + 2))) ?_ fun u2 ⟨L2, k2, m2⟩ => ?_)
  · refine chainD_wp hok.toKeys (f := fun H => .block (consts H.D)) hkH ax1 fun s' hs' => ?_
    have k' := (k1.trans (keep_of_flags hs')).mono (rs' := [.rax]) (by decide)
    obtain ⟨sp', sc'⟩ := scK k' (by decide)
    refine WP.mono (consts_ok sp' sc' hDH) fun u2 ⟨k2, m2⟩ => ?_
    have k12 := (k'.trans k2).mono (rs' := [.rax]) (by decide)
    have R2 : Rep u2.mem F S V (upd (upd (upd (upd (upd W 37 (BitVec.ofNat 64 kH)) 39 (BitVec.ofNat 64 HH.D))
        40 (BitVec.ofNat 64 (HH.D + 1))) 41 (BitVec.ofNat 64 (2 * HH.D + 1))) 42 (BitVec.ofNat 64 (2 * HH.D + 2))) := by
      rw [m2, hs'.mem, m1]
      exact ((((R.wf G' (k := 37) (by decide) (BitVec.ofNat 64 kH)).wf G' (k := 39) (by decide) _).wf G'
        (k := 40) (by decide) _).wf G' (k := 41) (by decide) _).wf G' (k := 42) (by decide) _
    exact ⟨L.of_rep' R R2 (by simp [upd]) (k12.gpr (by decide)) k12.2.2, k12, by rw [m2, hs'.mem, m1]⟩
  have f2 : Frame [⟨F, frameBytes⟩] u.mem u2.mem := by
    rw [m2]
    exact frame_wF hF (frame_wF hF (frame_wF hF (frame_wF hF (frame_wF hF (Frame.refl _ _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _) (by decide) _
  have hinG2 : InRegions (u2.rd ++ u2.wr) (off F (frameBytes + 8 + 8 * jG)) 8 := by
    rw [k2.2.1, k2.2.2]; exact hinG
  refine WP.seq (WP.mono (argSlot_ok L2.rsp L2.frScr hinG2 (harg _ f2).2 (d := sSelG) (by decide))
    fun u3 ⟨k3, ax3, m3⟩ => ?_)
  refine chainD_wp hok.toKeys (f := fun G => .block [.mov32 .rax (im G.D), .store (sp sGD) .rax]) hkG ax3
    fun s' hs' => ?_
  have k' := (k3.trans (keep_of_flags hs')).mono (rs' := [.rax]) (by decide)
  have k13 := (k2.trans k').mono (rs' := [.rax]) (by decide)
  obtain ⟨sp', sc'⟩ := scK k13 (by decide)
  refine WP.mono (gd_ok sp' sc' hDG) fun u4 ⟨k4, m4⟩ => ?_
  have k14 := (k13.trans k4).mono (rs' := [.rax]) (by decide)
  have R4 : Rep u4.mem F S V (selW W kH kG HH.D GG.D) := by
    rw [m4, hs'.mem, m3, m2]
    exact ((((((R.wf G' (k := 37) (by decide) (BitVec.ofNat 64 kH)).wf G' (k := 39) (by decide) _).wf G'
      (k := 40) (by decide) _).wf G' (k := 41) (by decide) _).wf G' (k := 42) (by decide) _).wf G' (k := 38)
      (by decide) _).wf G' (k := 43) (by decide) _
  refine ⟨L.of_rep' R R4 (by simp [selW, upd]) ((k14.gpr (by decide)).trans rfl) k14.2.2, k14, R4, ?_⟩
  rw [m4, hs'.mem, m3]
  exact frame_wF hF (frame_wF hF f2 (by decide) _) (by decide) _

end VG.Proof.RsaOaep.X86_64
