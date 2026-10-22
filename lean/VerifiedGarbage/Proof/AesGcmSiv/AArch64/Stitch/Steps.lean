module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Aes
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Gh
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Base
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: one batch

Untrusted: everything here is checked by Lean. The loops of
`Impl.AesGcmSiv.AArch64.Stitch` run on the data at `D`, `nb` batches of
eight blocks, with the working space `W` in `x19` and the encryption key's
schedule `K` in `x15`, from the memory `m₀` (`Ctx`), which holds the counter
block at `W + 96` and the table of keys of `H` at `W + tblO` (`KPre`).
`aesStep` is the counter mode of a batch (the blocks of the keystream `ks`,
RFC 8452's counter blocks), `stores_ok` the eight blocks it computes
stored, and `ghStep` GHASH of a batch (POLYVAL's blocks, as numbers).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv)
open VG.Proof.Aes.AArch64.Aese (Fr vbyte_readW inRegions_wr exec_strq st)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly pp)
open VG.Proof.Gcm.AArch64.Stitch (aesV gh8V kpack Gh8Ok read_eq_readW range_map_add ghashFrom_append gh8V_congr
  dataInv_store1)
open VG.Spec.Gcm (Block ghashFrom)
open VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Impl.Gcm.AArch64.Stitch (breg Y C pk pl stores)

/-- What the loops run on. -/
structure Ctx where
  /-- The working space (`x19`). -/
  W : Addr
  /-- The encryption key's schedule (`x15`). -/
  K : Addr
  /-- The data. -/
  D : Addr
  /-- The rounds. -/
  nr : Nat
  /-- The batches of eight blocks. -/
  nb : Nat
  /-- GHASH's key, of which the table holds the powers. -/
  H : Block
  /-- The memory before the loops. -/
  m₀ : Mem
  rd : List Region
  wr : List Region

namespace Ctx
variable (σ : Ctx)

abbrev dR : Region := ⟨σ.D, 128 * σ.nb⟩
abbrev kR : Region := ⟨σ.K, 16 * (σ.nr + 1)⟩
abbrev cR : Region := ⟨σ.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO, 16⟩
abbrev tR : Region := ⟨σ.W + BitVec.ofNat 64 tblO, 192⟩
/-- The key schedule, and the counter block's first word. -/
abbrev sch : List Byte := Spec.Aes.bytesAt σ.m₀ σ.K (16 * (σ.nr + 1))
abbrev c0 : BitVec 32 := σ.m₀.readW (σ.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) 32
/-- Counter block `q`, and the keystream, byte by byte. -/
abbrev cv (q : Nat) : BitVec 128 :=
  setLane (σ.m₀.readW (σ.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) 128) 32 0 (σ.c0 + BitVec.ofNat 32 q)
abbrev ks (i : Nat) : Byte := (Spec.Aes.cipher σ.nr σ.sch (st (σ.cv (i / 16)))).getD (i % 16) 0
/-- Block `i` of the data as it was, as a number, and decrypted. -/
abbrev blockO (i : Nat) : Block := σ.m₀.readW (σ.D + BitVec.ofNat 64 (16 * i)) 128

end Ctx

/-- The table of keys of `H` at `W + tblO` (as AES-GCM's,
`Proof.Gcm.AArch64.Stitch.TblOk`). -/
structure TblOk (m : Mem) (W : Addr) (H : Block) : Prop where
  sw : ∀ k, 1 ≤ k → k ≤ 8 → m.readW (W + BitVec.ofNat 64 (sOff k)) 128 = ext8 (pp H k) (pp H k)
  key : ∀ p < 4, m.readW (W + BitVec.ofNat 64 (kOff p)) 128 = kpack H (pk p) (pl p)

/-- What the counter mode of the loops needs of the context. -/
structure KPreC (σ : Ctx) : Prop where
  rounds : σ.nr = 10 ∨ σ.nr = 12 ∨ σ.nr = 14
  nb1 : 1 ≤ σ.nb
  n16 : 128 * σ.nb < 2 ^ 64
  k_in : InRegions (σ.rd ++ σ.wr) σ.K (16 * (σ.nr + 1))
  c_in : InRegions (σ.rd ++ σ.wr) (σ.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) 16
  d_in : InRegions σ.wr σ.D (128 * σ.nb)
  d_k : σ.dR.Disjoint σ.kR
  d_c : σ.dR.Disjoint σ.cR
  wrap_c : σ.W.toNat + Impl.AesGcmSiv.AArch64.cbO + 16 ≤ 2 ^ 64
  wrap_k : σ.K.toNat + 16 * (σ.nr + 1) ≤ 2 ^ 64

/-- What the loops need of the context, with the table of keys. -/
structure KPre (σ : Ctx) : Prop extends KPreC σ where
  t_in : InRegions (σ.rd ++ σ.wr) (σ.W + BitVec.ofNat 64 tblO) 192
  d_t : σ.dR.Disjoint σ.tR
  wrap_t : σ.W.toNat + tblO + 192 ≤ 2 ^ 64
  tbl : TblOk σ.m₀ σ.W σ.H

namespace KPreC
variable {σ : Ctx} (hp : KPreC σ)
include hp

theorem k_frame {m : Mem} (hf : Frame [σ.dR] σ.m₀ m) : Spec.Aes.bytesAt m σ.K (16 * (σ.nr + 1)) = σ.sch :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.d_k.symm) (by have := hp.wrap_k; omega)

theorem c_frame {m : Mem} (hf : Frame [σ.dR] σ.m₀ m) {w : Nat} (hw : w = 32 ∨ w = 128) :
    m.readW (σ.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) w =
      σ.m₀.readW (σ.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) w := by
  rcases hw with rfl | rfl
  · exact hf.readW (r := σ.cR) (by simp [Region.Contains])
      (by simp only [List.mem_singleton, forall_eq]; exact hp.d_c.symm) (by decide)
  · exact hf.readW (r := σ.cR) (by simp [Region.Contains])
      (by simp only [List.mem_singleton, forall_eq]; exact hp.d_c.symm) (by decide)

end KPreC

namespace KPre
variable {σ : Ctx} (hp : KPre σ)
include hp

theorem t_frame {m : Mem} (hf : Frame [σ.dR] σ.m₀ m) {o : Nat} (ho : o + 16 ≤ 192) :
    m.readW (σ.W + BitVec.ofNat 64 tblO + BitVec.ofNat 64 o) 128 =
      σ.m₀.readW (σ.W + BitVec.ofNat 64 tblO + BitVec.ofNat 64 o) 128 :=
  hf.readW (r := σ.tR) (Offset.contains_base _ (by omega) (by have := hp.wrap_t; omega))
    (by simp only [List.mem_singleton, forall_eq]; exact hp.d_t.symm) (by decide)

end KPre

theorem inRegions_app {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem Ctx.ks_eq (σ : Ctx) (q : Nat) {t : Nat} (ht : t < 16) :
    σ.ks (16 * q + t) = (Spec.Aes.cipher σ.nr σ.sch (st (σ.cv q))).getD t 0 := by
  simp only [Ctx.ks]
  rw [show (16 * q + t) / 16 = q by omega, show (16 * q + t) % 16 = t by omega]

/-! ## Storing a batch -/

/-- The eight blocks of batch `c` stored at `x9 + o`. -/
theorem stores_ok {σ : Ctx} (hp : KPreC σ) {c o : Nat} (hc : c < σ.nb) (ho : o ≤ 128) (ho16 : o % 16 = 0)
    (u : State) (hx9 : u.gpr .x9 + BitVec.ofNat 64 o = σ.D + BitVec.ofNat 64 (128 * c))
    (hdata : DataInv σ.m₀ u.mem σ.D (8 * σ.nb) (8 * c) σ.ks) (hwr : u.wr = σ.wr)
    (hv : ∀ j < 8, ∀ t < 16, vbyte (u.v (breg j)) t =
      σ.ks (16 * (8 * c + j) + t) ^^^ σ.m₀ (σ.D + BitVec.ofNat 64 (16 * (8 * c + j) + t))) :
    WP isa (.block (stores o)) u fun u' =>
      DataInv σ.m₀ u'.mem σ.D (8 * σ.nb) (8 * (c + 1)) σ.ks ∧ Frame [σ.dR] u.mem u'.mem ∧
        u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have hn := hp.n16
  refine WP.mono (wp_range_flatMap (M := isa) (fun j u' =>
      DataInv σ.m₀ u'.mem σ.D (8 * σ.nb) (8 * c + j) σ.ks ∧ Frame [σ.dR] u.mem u'.mem ∧
        u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr)
    (fun j u₁ hj ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_) 8 (Nat.le_refl _) u
    ⟨hdata, Frame.refl _ _, rfl, rfl, rfl, rfl, rfl⟩) fun u' ⟨d, f, g, v, sp, rd, wr⟩ =>
      ⟨by rw [show 8 * (c + 1) = 8 * c + 8 by omega]; exact d, f, g, v, sp, rd, wr⟩
  have ha : u₁.gpr .x9 + BitVec.ofNat 64 (o + 16 * j) = σ.D + BitVec.ofNat 64 (16 * (8 * c + j)) := by
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
  exact hst.2.sub fun r hr => ⟨σ.dR, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega)⟩

/-! ## Counter mode -/

/-- Counter mode of batch `c`, from the data at `x9 + o`. -/
theorem aesStep (e3 : Bool) {σ : Ctx} (hp : KPreC σ) {c o : Nat} {s : State} (hc : c < σ.nb) (ho' : o ≤ 128) (ho16 : o % 16 = 0)
    (hx9 : ∀ j, s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j) = σ.D + BitVec.ofNat 64 (16 * (8 * c + j)))
    (hx10 : s.read .w .x10 = σ.c0 + BitVec.ofNat 32 (8 * c))
    (hx19 : s.gpr .x19 = σ.W) (hx15 : s.gpr .x15 = σ.K) (hrdwr : s.rd ++ s.wr = σ.rd ++ σ.wr)
    (hf : Frame [σ.dR] σ.m₀ s.mem) (hdata : DataInv σ.m₀ s.mem σ.D (8 * σ.nb) (8 * c) σ.ks) :
    WP isa (.block (aesPart e3 σ.nr o)) s fun t =>
      (∀ j < 8, ∀ tt < 16, vbyte (t.v (breg j)) tt =
        σ.ks (16 * (8 * c + j) + tt) ^^^ σ.m₀ (σ.D + BitVec.ofNat 64 (16 * (8 * c + j) + tt))) ∧
      t.read .w .x10 = σ.c0 + BitVec.ofNat 32 (8 * (c + 1)) ∧ Fr [.x10, .x12] aesV s t := by
  have hn := hp.n16
  have hR := hp.rounds
  have hc0 : c0 s = σ.c0 := by rw [c0, cbA, hx19, hp.c_frame hf (.inl rfl)]
  have hA : APre σ.nr o (8 * c) s := {
    rounds := hR
    o_le := ho'
    keys := fun r hr => by
      rw [hrdwr, hx15]; exact CallLay.inRegions_sub hp.k_in (by omega) (by omega)
    ctr := by rw [hrdwr, cbA, hx19]; exact hp.c_in
    data := fun j hj => by
      rw [hrdwr, hx9]
      exact inRegions_app (CallLay.inRegions_sub (off := 16 * (8 * c + j)) (l := 16) (n := 128 * σ.nb) hp.d_in (by omega) (by omega))
    x10 := by rw [hx10, hc0] }
  refine WP.mono (aesPart_ok e3 hA ho16) fun t ⟨out, x10, fr⟩ => ⟨fun j hj tt htt => ?_, ?_, fr⟩
  · rw [out j hj tt htt, sch, hx15, hp.k_frame hf, hx9, Offset.add_add, hdata _ (by omega),
      ite_eq_right (by omega), show ∀ b : Byte, b ^^^ 0 = b from fun _ => BitVec.xor_zero]
    have hcv : cvec s (8 * c) j = σ.cv (8 * c + j) := by
      simp only [cvec, Ctx.cv]
      rw [cbA, hx19, hp.c_frame hf (.inr rfl), ← hc0, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [hcv, σ.ks_eq _ htt]
  · rw [x10, hc0, show 8 * c + 8 = 8 * (c + 1) by omega]

/-! ## POLYVAL -/

/-- GHASH from `y`, by `H`, of the first `n` blocks of `hb`. -/
abbrev yh (H y : Block) (hb : Nat → Block) (n : Nat) : Block := ghashFrom H y ((List.range n).map hb)

/-- GHASH of the eight blocks at `x9`, the blocks `hb (8 h + j)` as numbers. -/
theorem ghStep (e3 : Bool) {σ : Ctx} (hp : KPre σ) (gh : Gh8Ok) {y : Block} {hb : Nat → Block} {h : Nat} {t : State}
    (hy : t.v Y = ext8 (yh σ.H y hb (8 * h)) (yh σ.H y hb (8 * h)))
    (hc : t.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly)
    (hx9 : t.gpr .x9 = σ.D + BitVec.ofNat 64 (128 * h)) (hh : h < σ.nb)
    (hx19 : t.gpr .x19 = σ.W) (hrdwr : t.rd ++ t.wr = σ.rd ++ σ.wr)
    (hf : Frame [σ.dR] σ.m₀ t.mem)
    (hb' : ∀ j < 8, t.mem.readW (σ.D + BitVec.ofNat 64 (16 * (8 * h + j))) 128 = hb (8 * h + j)) :
    WP isa (.block (ghPart e3)) t fun u =>
      u.v Y = ext8 (yh σ.H y hb (8 * (h + 1))) (yh σ.H y hb (8 * (h + 1))) ∧ VOnly Proof.Gcm.AArch64.Stitch.ghV t u := by
  have hn := hp.n16
  have ha : ∀ j, t.gpr .x9 + BitVec.ofNat 64 (16 * j) = σ.D + BitVec.ofNat 64 (16 * (8 * h + j)) :=
    fun j => by rw [hx9, Offset.add_add_eq _ (show 128 * h + 16 * j = 16 * (8 * h + j) by omega)]
  have ht : ∀ o, o + 16 ≤ 192 → t.gpr .x19 + BitVec.ofNat 64 (tblO + o) =
      σ.W + BitVec.ofNat 64 tblO + BitVec.ofNat 64 o := fun o _ => by rw [hx19, Offset.add_add]
  have hin : GhIn t := {
    blk := fun j hj => by
      rw [hrdwr, ha]
      exact inRegions_app (CallLay.inRegions_sub (off := 16 * (8 * h + j)) (l := 16) (n := 128 * σ.nb) hp.d_in (by omega) (by omega))
    sw := fun k hk1 hk8 => by
      rw [hrdwr, show sOff k = tblO + 16 * (k - 1) from rfl, ht _ (by omega)]
      exact CallLay.inRegions_sub hp.t_in (by omega) (by omega)
    key := fun p hp' => by
      rw [hrdwr, show kOff p = tblO + (128 + 16 * p) by unfold kOff; omega, ht _ (by omega)]
      exact CallLay.inRegions_sub hp.t_in (by omega) (by omega) }
  refine WP.mono (ghPart_ok e3 t hin hc) fun u ⟨e, o⟩ => ⟨?_, o⟩
  rw [e, hy, gh8V_congr rfl (b' := fun j => ext8 (hb (8 * h + j)) (hb (8 * h + j)))
    (S' := fun k => ext8 (pp σ.H k) (pp σ.H k))
    (KP' := fun p => kpack σ.H (pk p) (pl p))
    (fun j hj => by rw [blkV, ha, read_eq_readW, hb' j hj])
    (fun k hk1 hk8 => by
      rw [tblV, read_eq_readW, show sOff k = tblO + 16 * (k - 1) from rfl, ht _ (by omega), hp.t_frame hf (by omega),
        Offset.add_add, show tblO + 16 * (k - 1) = sOff k from rfl]
      exact hp.tbl.sw k hk1 hk8)
    (fun p hp' => by
      rw [tblV, read_eq_readW, show kOff p = tblO + (128 + 16 * p) by unfold kOff; omega, ht _ (by omega),
        hp.t_frame hf (by omega), Offset.add_add, show tblO + (128 + 16 * p) = kOff p by unfold kOff; omega]
      exact hp.tbl.key p hp'), gh, yh, yh, show 8 * (h + 1) = 8 * h + 8 by omega, range_map_add hb (8 * h),
    ghashFrom_append]

/-! ## The pointer and the count -/

theorem adv_ok {D : Addr} {nb : Nat} {u : State} {h c : Nat} (hc : c < nb)
    (hx9 : u.gpr .x9 = D + BitVec.ofNat 64 (128 * h))
    (hx11 : u.gpr .x11 = BitVec.ofNat 64 (nb - c)) :
    WP isa (.block adv) u fun u' =>
      u'.gpr .x9 = D + BitVec.ofNat 64 (128 * (h + 1)) ∧
      u'.gpr .x11 = BitVec.ofNat 64 (nb - (c + 1)) ∧
      (∀ r, r ≠ .x9 → r ≠ .x11 → u'.gpr r = u.gpr r) ∧ u'.v = u.v ∧ u'.mem = u.mem ∧
      u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  rw [adv, WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine ⟨?_, ?_, fun r h9 h11 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [gpr_write_of_ne _ _ _ (by decide), gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, BitVec.setWidth_eq, hx9]
    rw [Offset.add_add_eq _ (show 128 * h + 128 = 128 * (h + 1) by omega)]
  · rw [gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, BitVec.setWidth_eq, gpr_write_of_ne _ _ _ (show Reg.x11 ≠ Reg.x9 by decide), hx11]
    rw [Offset.ofNat_sub_ofNat (by omega), show nb - c - 1 = nb - (c + 1) by omega]
  · rw [gpr_write_of_ne _ _ _ h11, gpr_write_of_ne _ _ _ h9]

end VG.Proof.AesGcmSiv.AArch64.Stitch
