module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Prepared.Powers
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.Gcm.Prepared8Contract
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM on AArch64: `vg_aes_gcm_derive_prepared8`

Untrusted: everything here is checked by Lean. The 256 bytes at `src`
copied to `dst` one 16-byte block at a time (`copy_ok`), then the 8 prepared
powers of the copied hash subkey (`powers_ok`), which write only bytes 256
to 383 of `dst` (`derive_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH)
open VG.Proof.Gcm (PreparedPowers8Repr)

/-- `vg_aes_gcm_derive_prepared8(src = x0, dst = x1)`. -/
def derivePrepared8AArch64 : Contract isa where
  pre s :=
    let src : Region := ⟨s.gpr .x0, 256⟩
    let dst : Region := ⟨s.gpr .x1, 384⟩
    s.rd = [src] ∧ s.wr = [dst] ∧ src.Disjoint dst ∧
      (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 384 ≤ 2 ^ 64
  post s s' := bytesAt s'.mem (s.gpr .x1) 256 = bytesAt s.mem (s.gpr .x0) 256 ∧
    PreparedPowers8Repr s'.mem (s.gpr .x1)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

namespace Prepared

open VG.Proof.AesGcm.AArch64.Prepared (Slots Inv slot slotPow ifp ifn)
open VG.Impl.AesGcm.AArch64.Prepared (PL cp copyN)

/-! ## The copy -/

/-- After the first `n` blocks, from `s₀`. -/
structure CopyInv (s₀ : State) (n : Nat) (s : State) : Prop where
  le : n ≤ 16
  blocks : ∀ j < n, s.mem.read (s₀.gpr .x1 + BitVec.ofNat 64 (16 * j)) 16 =
    s₀.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 (16 * j)) 16
  frame : Frame [⟨s₀.gpr .x1, 384⟩] s₀.mem s.mem
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem cp_ok {s₀ s : State} (hp : derivePrepared8AArch64.pre s₀) {n : Nat} (hn : n < 16)
    (hI : CopyInv s₀ n s) : WP isa (.block (cp n)) s (CopyInv s₀ (n + 1)) := by
  obtain ⟨hrd, hwr, hd, hb0, hb1⟩ := hp
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * n)) 16 := by
    rw [hI.rd, hI.wr, hI.gpr, hrd]
    exact in_off (covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _))) (by omega)
      (by decide)
  have hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * n)) 16 := by
    rw [hI.wr, hI.gpr, hwr]
    exact in_off (covers_of_mem (List.mem_singleton_self _)) (by omega) (by decide)
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrq (by omega) (by omega) hin, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (t := PL) (n := .x1) (off := 16 * n) (by omega) (by omega)
    (by simp only [wr_setV, gpr_setV]; exact hout), ?_⟩
  refine WP.block_nil ⟨by omega, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setV, gpr_setV, v_setV, ite_true, hI.gpr]
    rcases (by omega : j = n ∨ j < n) with rfl | hj'
    · rw [read_write16, ← hI.gpr]
      refine hI.frame.read (r := ⟨s₀.gpr .x0, 256⟩) ?_ (fun r hr => ?_) (by decide)
      · rw [hI.gpr]; exact Offset.contains_base _ (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr; exact hd
    · rw [Mem.read_write_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact hI.blocks j hj'
  · simp only [mem_setV, gpr_setV, v_setV, ite_true]
    rw [hI.gpr]
    exact hI.frame.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · simp only [gpr_setV]; exact hI.gpr
  · simp only [rd_setV]; exact hI.rd
  · simp only [wr_setV]; exact hI.wr
  · show s.sp = s₀.sp; exact hI.sp

theorem copy_ok {s₀ : State} (hp : derivePrepared8AArch64.pre s₀) :
    ∀ n ≤ 16, WP isa (.block (copyN n)) s₀ (CopyInv s₀ n)
  | 0, _ => WP.block_nil ⟨by omega, fun _ hj => absurd hj (by omega), Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [copyN, WP.block_append_iff]
    exact WP.mono (copy_ok hp n (by omega)) fun _ hI => cp_ok hp (by omega) hI

/-- 256 bytes, from their 16 blocks. -/
theorem bytesAt_of_blocks {m m' : Mem} {p q : Addr}
    (h : ∀ j < 16, m'.read (p + BitVec.ofNat 64 (16 * j)) 16 = m.read (q + BitVec.ofNat 64 (16 * j)) 16) :
    bytesAt m' p 256 = bytesAt m q 256 := by
  unfold Spec.Aes.bytesAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have e : ∀ a : Addr, a + BitVec.ofNat 64 i =
      a + BitVec.ofNat 64 (16 * (i / 16)) + BitVec.ofNat 64 (i % 16) := fun a => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod]
  rw [e p, e q, ← Mem.extractLsb'_read m' _ (n := 16) (Nat.mod_lt _ (by decide)),
    ← Mem.extractLsb'_read m _ (n := 16) (Nat.mod_lt _ (by decide)), h _ (by omega)]

/-! ## The powers -/

/-- The slots, as `Proof.Gcm.PreparedPowers8Repr` reads them. -/
theorem repr8_of_slots {H : Block} {Ctx : Addr} {m : Mem} (hs : Slots H Ctx m 8) (hH : ctxH m Ctx = H) :
    PreparedPowers8Repr m Ctx := by
  intro k hk
  have e : ∀ j < 8, m.readW (slot Ctx j) 128 = pp H (slotPow j) := fun j hj => by
    rw [Mem.readW, show 128 / 8 = 16 from rfl, hs j hj (.inl hj)]; rfl
  rw [hH]
  refine ⟨?_, ?_⟩
  · have := e (2 * k) (by omega)
    rw [slot, show 256 + 16 * (2 * k) = 256 + 32 * k by omega, slotPow, ifp (by omega)] at this
    exact this
  · have := e (2 * k + 1) (by omega)
    rw [slot, show 256 + 16 * (2 * k + 1) = 272 + 32 * k by omega, slotPow, ifn (by omega)] at this
    exact this

theorem preserved_not_mem : ∀ r ∈ preserved, r ∉ [Reg.x0, .x5, .x6, .x7, .x9, .x10, .x11] := by
  decide

end Prepared

/-- `vg_aes_gcm_derive_prepared8`. -/
theorem derive_wp (hP : PrepPow) {s : State} (hp : derivePrepared8AArch64.pre s) :
    WP isa Impl.AesGcm.AArch64.Prepared.derive s fun s' =>
      GprAbi s s' ∧ derivePrepared8AArch64.post s s' := by
  have hp' := hp
  obtain ⟨hrd, hwr, hd, hb0, hb1⟩ := hp'
  refine WP.seq (WP.mono (Prepared.copy_ok hp 16 (Nat.le_refl _)) fun s₅ hC => ?_)
  have pC : Covers [⟨s.gpr .x1, 384⟩] s₅.wr := by
    rw [hC.wr, hwr]; exact covers_of_mem (List.mem_singleton_self _)
  refine WP.mono (Prepared.powers_ok hP (by rw [hC.gpr]) rfl pC) fun s' hI => ?_
  have hf : Frame [⟨s.gpr .x1 + BitVec.ofNat 64 256, 128⟩] s₅.mem s'.mem := hI.frame
  have hlo : ∀ r ∈ [(⟨s.gpr .x1 + BitVec.ofNat 64 256, 128⟩ : Region)],
      (⟨s.gpr .x1, 256⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (Offset.disjoint_base _ (by decide) (by omega)).symm
  refine ⟨⟨fun r hr => ?_, by rw [hI.sp, hC.sp]⟩, ?_, ?_⟩
  · rw [hI.gpr r (Prepared.preserved_not_mem r hr), hC.gpr]
  · show bytesAt s'.mem (s.gpr .x1) 256 = bytesAt s.mem (s.gpr .x0) 256
    rw [bytesAt_frame hf hlo (by decide)]
    refine Prepared.bytesAt_of_blocks fun j hj => ?_
    exact hC.blocks j hj
  · show PreparedPowers8Repr s'.mem (s.gpr .x1)
    refine Prepared.repr8_of_slots hI.slots ?_
    show blockAt s'.mem (s.gpr .x1 + BitVec.ofNat 64 240) = blockAt s₅.mem (s.gpr .x1 + BitVec.ofNat 64 240)
    exact blockAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by omega) (by omega))

end VG.Proof.AesGcm.AArch64
