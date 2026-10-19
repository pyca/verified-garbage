module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Base
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Aes
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.GhBits
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Proof.Gcm.Stream

/-!
# Interleaved counter mode and GHASH on AArch64: one batch

Untrusted: everything here is checked by Lean. From the loops' invariant
(`LInv`): `aesStep`, the counter mode of batch `c` (the text blocks at
`x9 + o`); `stores_ok`, the eight blocks it computes stored there; and
`ghStep`, GHASH of the eight blocks at `x9`, the blocks `hb (8 h + j)`, for
any `ghPart` that is GHASH (`Gh8Ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv keyStream)
open VG.Proof.Aes.AArch64.Aese (Fr vbyte_readW inRegions_wr exec_strq)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly rev64b_read)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom ctr32)
open VG.Impl.Gcm.AArch64.Stitch

/-! ## Storing a batch -/

/-- A block of the text XORed with the keystream, stored. -/
theorem dataInv_store1 {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {v : BitVec 128}
    (hn : 16 * n < 2 ^ 64) (hk : k < n) (h : DataInv m₀ m D n k ks)
    (hv : ∀ t < 16, vbyte v t = ks (16 * k + t) ^^^ m₀ (D + BitVec.ofNat 64 (16 * k + t))) :
    DataInv m₀ (m.write (D + BitVec.ofNat 64 (16 * k)) 16 v) D n (k + 1) ks ∧
      Frame [⟨D, 16 * n⟩] m (m.write (D + BitVec.ofNat 64 (16 * k)) 16 v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · show (if _ then _ else _) = _
    rw [Proof.Aes.AArch64.off_toNat D (by omega) (by omega)]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, ite_eq_left (show i < 16 * (k + 1) by omega)]
        show vbyte _ _ = _
        rw [hv _ h2, show 16 * k + (i - 16 * k) = i by omega, BitVec.xor_comm]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 16 * k by omega),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega), h i hi,
        ite_eq_left (show i < 16 * k by omega), ite_eq_left (show i < 16 * (k + 1) by omega)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx ⟨D, 16 * n⟩ (List.mem_singleton_self _)
    show (if _ then _ else _) = _
    rw [ite_eq_right]
    intro hlt
    apply hx'
    have e := Offset.toNat_sub_add x D (d := 16 * k) (by omega)
    rw [Offset.sub_add_eq] at hlt
    have := (x - D).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 * k < 2 ^ 64 by omega)] at hlt
    omega

/-- The eight blocks of batch `c` stored at `x9 + o`. -/
theorem stores_ok {s₀ : State} (hp : KPre s₀) {c o : Nat} (hc : c < nb s₀) (ho : o ≤ 128) (ho16 : o % 16 = 0)
    (u : State) (hx9 : u.gpr .x9 + BitVec.ofNat 64 o = dp s₀ + BitVec.ofNat 64 (128 * c))
    (hdata : DataInv s₀.mem u.mem (dp s₀) (8 * nb s₀) (8 * c) (kst s₀)) (hwr : u.wr = s₀.wr)
    (hv : ∀ j < 8, ∀ t < 16, vbyte (u.v (breg j)) t =
      kst s₀ (16 * (8 * c + j) + t) ^^^ s₀.mem (dp s₀ + BitVec.ofNat 64 (16 * (8 * c + j) + t))) :
    WP isa (.block (stores o)) u fun u' =>
      DataInv s₀.mem u'.mem (dp s₀) (8 * nb s₀) (8 * (c + 1)) (kst s₀) ∧ Frame [dR s₀] u.mem u'.mem ∧
        u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have hn := hp.n16
  refine WP.mono (wp_range_flatMap (M := isa) (fun j u' =>
      DataInv s₀.mem u'.mem (dp s₀) (8 * nb s₀) (8 * c + j) (kst s₀) ∧ Frame [dR s₀] u.mem u'.mem ∧
        u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr)
    (fun j u₁ hj ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_) 8 (Nat.le_refl _) u
    ⟨hdata, Frame.refl _ _, rfl, rfl, rfl, rfl, rfl⟩) fun u' ⟨d, f, g, v, sp, rd, wr⟩ =>
      ⟨by rw [show 8 * (c + 1) = 8 * c + 8 by omega]; exact d, f, g, v, sp, rd, wr⟩
  have ha : u₁.gpr .x9 + BitVec.ofNat 64 (o + 16 * j) = dp s₀ + BitVec.ofNat 64 (16 * (8 * c + j)) := by
    rw [g₁, ← Offset.add_add, hx9, Offset.add_add_eq _ (show 128 * c + 16 * j = 16 * (8 * c + j) by omega)]
  have hw : InRegions u₁.wr (u₁.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16 := by
    rw [ha, wr₁, hwr]
    exact CallLay.inRegions_sub hp.d_in (by omega) (by omega)
  rw [WP.block_cons_iff]
  refine ⟨_, exec_strq (by omega) hw, WP.block_nil ?_⟩
  rw [ha]
  have hst := dataInv_store1 (v := u₁.v (breg j)) (by omega) (by omega) d₁ fun t ht => by
    rw [v₁, hv j hj t ht]
  refine ⟨hst.1, f₁.trans ?_, g₁, v₁, sp₁, rd₁, wr₁⟩
  exact hst.2.sub fun r hr => ⟨dR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega)⟩

/-! ## Counter mode -/

/-- Counter mode of batch `c`, from the text at `x9 + o`. -/
theorem aesStep {s₀ : State} (hp : KPre s₀) {hb : Nat → Block} {c h o : Nat} {s : State}
    (hI : LInv s₀ hb c h s) (hc : c < nb s₀) (ho : 128 * h + o = 128 * c) (ho' : o ≤ 128) (ho16 : o % 16 = 0) :
    WP isa (.block (aesPart (rounds s₀) o)) s fun t =>
      (∀ j < 8, ∀ tt < 16, vbyte (t.v (breg j)) tt =
        kst s₀ (16 * (8 * c + j) + tt) ^^^ s₀.mem (dp s₀ + BitVec.ofNat 64 (16 * (8 * c + j) + tt))) ∧
      t.read .w .x10 = ctr0 s₀ + BitVec.ofNat 32 (8 * (c + 1)) ∧ Fr [.x10, .x12] aesV s t := by
  have hn := hp.n16
  have hR := hp.rounds
  have g21 : s.gpr .x21 = kc s₀ := hI.gpr _ (by decide)
  have g20 : s.gpr .x20 = stp s₀ := hI.gpr _ (by decide)
  have rdwr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hI.rd, hI.wr]
  have hx9 : ∀ j, s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j) = dp s₀ + BitVec.ofNat 64 (16 * (8 * c + j)) :=
    fun j => by rw [hI.x9, Offset.add_add_eq _ (show 128 * h + (o + 16 * j) = 16 * (8 * c + j) by omega)]
  have hcb : cbk s = icb s₀ := by rw [cbk, cbA, g20]; exact hp.c_frame hI.frame
  have hA : APre (rounds s₀) o (8 * c) s := {
    rounds := hR
    o_le := ho'
    keys := fun r hr => by
      rw [rdwr, kp, g21]; exact CallLay.inRegions_sub hp.k_in (by omega) (by omega)
    ctr := by
      rw [rdwr, cbA, g20, BitVec.add_zero]
      exact inRegions_wr hp.c_in
    data := fun j hj => by
      rw [rdwr, hx9]
      exact inRegions_wr (CallLay.inRegions_sub hp.d_in (by omega) (by omega))
    x10 := by rw [hI.x10, c0, hcb] }
  refine WP.mono (aesPart_ok hA ho16) fun t ⟨out, x10, fr⟩ => ⟨fun j hj tt htt => ?_, ?_, fr⟩
  · rw [out j hj tt htt, sch, kp, g21, hp.sch_frame hI.frame, hcb, hx9, Offset.add_add, hI.data _ (by omega),
      ite_eq_right (by omega)]
    exact congrArg _ BitVec.xor_zero
  · rw [x10, c0, hcb, show 8 * c + 8 = 8 * (c + 1) by omega]

/-! ## GHASH -/

/-- GHASH of the eight blocks at `x9`, the blocks `hb (8 h + j)`. -/
theorem ghStep {s₀ : State} (hp : KPre s₀) (gh : Gh8Ok) {hb : Nat → Block} {h : Nat} {t : State}
    (hy : t.v Y = ext8 (yh s₀ hb (8 * h)) (yh s₀ hb (8 * h)))
    (hc : t.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly)
    (hx9 : t.gpr .x9 = dp s₀ + BitVec.ofNat 64 (128 * h)) (hh : h < nb s₀)
    (hx19 : t.gpr .x19 = wp s₀) (hrdwr : t.rd ++ t.wr = s₀.rd ++ s₀.wr)
    (hf : Frame [dR s₀] s₀.mem t.mem)
    (hb' : ∀ j < 8, blockAt t.mem (dp s₀ + BitVec.ofNat 64 (16 * (8 * h + j))) = hb (8 * h + j)) :
    WP isa (.block ghPart) t fun u =>
      u.v Y = ext8 (yh s₀ hb (8 * (h + 1))) (yh s₀ hb (8 * (h + 1))) ∧ VOnly ghV t u := by
  have hn := hp.n16
  have ha : ∀ j, t.gpr .x9 + BitVec.ofNat 64 (16 * j) = dp s₀ + BitVec.ofNat 64 (16 * (8 * h + j)) :=
    fun j => by rw [hx9, Offset.add_add_eq _ (show 128 * h + 16 * j = 16 * (8 * h + j) by omega)]
  have ht : ∀ o, o + 16 ≤ 192 → t.gpr .x19 + BitVec.ofNat 64 (512 + o) =
      wp s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 o := fun o _ => by rw [hx19, Offset.add_add]
  have hin : GhIn t := {
    blk := fun j hj => by
      rw [hrdwr, ha]; exact inRegions_wr (CallLay.inRegions_sub hp.d_in (by omega) (by omega))
    sw := fun k hk1 hk8 => by
      rw [hrdwr, show sOff k = 512 + 16 * (k - 1) from rfl, ht _ (by omega)]
      exact CallLay.inRegions_sub hp.t_in (by omega) (by omega)
    key := fun p hp' => by
      rw [hrdwr, show kOff p = 512 + (128 + 16 * p) by unfold kOff tbl; omega, ht _ (by omega)]
      exact CallLay.inRegions_sub hp.t_in (by omega) (by omega) }
  refine WP.mono (ghPart_ok t hin hc) fun u ⟨e, o⟩ => ⟨?_, o⟩
  rw [e, hy, gh8V_congr rfl (b' := fun j => ext8 (hb (8 * h + j)) (hb (8 * h + j)))
    (S' := fun k => ext8 (Pmull.pp (hk s₀) k) (Pmull.pp (hk s₀) k))
    (KP' := fun p => kpack (hk s₀) (pk p) (pl p))
    (fun j hj => by rw [blkV, ha, rev64b_read, hb' j hj])
    (fun k hk1 hk8 => by
      rw [tblV, read_eq_readW, show sOff k = 512 + 16 * (k - 1) from rfl, ht _ (by omega), hp.t_frame hf (by omega),
        Offset.add_add, show 512 + 16 * (k - 1) = sOff k from rfl]
      exact hp.tbl.sw k hk1 hk8)
    (fun p hp' => by
      rw [tblV, read_eq_readW, show kOff p = 512 + (128 + 16 * p) by unfold kOff tbl; omega, ht _ (by omega), hp.t_frame hf (by omega),
        Offset.add_add, show 512 + (128 + 16 * p) = kOff p by unfold kOff tbl; omega]
      exact hp.tbl.key p hp'), gh, yh, yh, show 8 * (h + 1) = 8 * h + 8 by omega, range_map_add hb (8 * h),
    ghashFrom_append]

end VG.Proof.Gcm.AArch64.Stitch
