module

import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Final
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tbl
public import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Spec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM on AArch64, interleaved: the first bytes

Untrusted: everything here is checked by Lean. After `front`, from a state of
`SIn`: `stitched [] tb enc` (`Impl.AesGcm.AArch64.Stitch`) encrypts the first
`pre n = 128 ⌊n / 128⌋` bytes of the text and continues `Y` over their
ciphertext, as `vg_aes_ctr32` and `vg_ghash` would, for any `tb` that writes
the table of keys (`TbOk`) and any `ghPart` that is GHASH (`Gh8Ok`):
`stitchE_ok`; `stitched [] tb dec` decrypts them and continues `Y` over them
as they were: `stitchD_ok`. Both leave `SMid`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (gpr_write gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm (Ctr xorKs)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghash blocks)
open VG.Proof.Gcm (blocks_append)
open VG.Proof.Gcm.AArch64.Stitch (KPre EPost DPost TblOk Gh8Ok)

/-- The bytes the interleaved loop takes. -/
abbrev pre (n : Nat) : Nat := 128 * (n / 128)

/-- What the interleaved loop writes: `Y`, the counter block, the bytes it
takes and the table of keys. -/
abbrev sFrame (St W D : Addr) (n : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 16, 16⟩, ⟨St + BitVec.ofNat 64 48, 16⟩, ⟨D, pre n⟩, tblR W]

/-- Before the interleaved loop, after `front`: `x` absorbed into `Y`, the
counter block `icb`, `n` bytes at `D`. -/
structure SIn (Ctx St W SP : Addr) (H : Block) (x : List Byte) (icb : Block) (R : Nat) (D : Addr)
    (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x23 : s.gpr .x23 = D
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  data : DataW Ctx St W s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = icb
  y : blockAt s.mem (St + BitVec.ofNat 64 16) = ghash H (blocks x)
  xm : x.length % 16 = 0

/-- `tb` writes the table of keys of `H`, from a state with the registers,
memory and regions of `s`. -/
def TbOk (Ctx St W SP : Addr) (H : Block) (tb : List Instr) (s : State) : Prop :=
  ∀ u : State, Env Ctx St W SP u → u.mem = s.mem → u.rd = s.rd → u.wr = s.wr →
    (∀ r, r ≠ .x9 → u.gpr r = s.gpr r) →
    WP isa (.block tb) u fun t => TblOk t.mem W H ∧ Frame [tblR W] u.mem t.mem ∧
      (∀ r, r ≠ .x5 → t.gpr r = u.gpr r) ∧ t.sp = u.sp ∧ t.rd = u.rd ∧ t.wr = u.wr

/-- After the interleaved loop, from `s`: the first `pre n` bytes encrypted
(or decrypted), the counter past them, and `Y` continued over `c`. -/
structure SMid (Ctx St W SP : Addr) (H : Block) (x : List Byte) (icb : Block) (R : Nat) (D : Addr)
    (n : Nat) (c : Mem → List Byte) (s t : State) : Prop where
  env : Env Ctx St W SP t
  gpr : ∀ r, r ∉ [Reg.x5, .x9, .x10, .x11, .x12, .x13, .x14] → t.gpr r = s.gpr r
  data : bytesAt t.mem D (pre n) = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D (pre n))
  ctr : Ctr t.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx R) icb (pre n)
  y : blockAt t.mem (St + BitVec.ofNat 64 16) = ghash H (blocks (x ++ c t.mem))
  frame : Frame (sFrame St W D n) s.mem t.mem
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- The loops' precondition, from the environment and the table. -/
theorem kpre_of {t : State} {R : Nat} {D : Addr} {n : Nat} (he : Env Ctx St W SP t)
    (h22 : t.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) (h23 : t.gpr .x23 = D)
    (h26 : t.gpr .x26 = BitVec.ofNat 64 n) (hd : DataW Ctx St W t D n) (h1 : 128 ≤ n)
    (tok : TblOk t.mem W (blockAt t.mem (Ctx + BitVec.ofNat 64 240))) : KPre t := by
  have hn := hd.ok.lt
  have hnb : Gcm.AArch64.Stitch.nb t = n / 128 := by
    simp only [Gcm.AArch64.Stitch.nb, h26, toNat_ofNat_of_lt hn]
  have hp : 128 * (n / 128) ≤ n := Nat.mul_div_le n 128
  obtain ⟨e19, e20, e21, -, perm⟩ := he
  subst e19 e20 e21 h23
  refine ⟨by simp only [Gcm.AArch64.Stitch.rounds, h22, toNat_ofNat_of_lt (show R < 2 ^ 64 by omega)]; exact hR,
    by rw [hnb]; omega,
    perm.ctx _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩,
    perm.stW (d := 16) (n := 16) (by decide), perm.stW (d := 48) (n := 16) (by decide),
    by rw [hnb]; exact covers_prefix hd.wr hp _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩,
    perm.wR (d := 512) (n := 192) (by decide), ?_, ?_, ?_, ?_,
    Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
    by rw [hnb]; change (t.gpr .x23).toNat + 128 * (n / 128) ≤ 2 ^ 64; have := hd.ok.wrap; omega, L.cw,
    by change (t.gpr .x19).toNat + 704 ≤ 2 ^ 64; have := L.ww; omega,
    by change (t.gpr .x20).toNat + 64 ≤ 2 ^ 64; have := L.sw; omega, tok⟩
  · simp only [Gcm.AArch64.Stitch.dR, Gcm.AArch64.Stitch.kR, hnb]
    exact hd.ctx.symm.sub_left (Region.sub_prefix hp)
  · simp only [Gcm.AArch64.Stitch.dR, Gcm.AArch64.Stitch.yR, hnb]
    exact (hd.ok.st.sub_left (Region.sub_prefix hp)).sub_right (Lay.stSub (by decide))
  · simp only [Gcm.AArch64.Stitch.dR, Gcm.AArch64.Stitch.cR, hnb]
    exact (hd.ok.st.sub_left (Region.sub_prefix hp)).sub_right (Lay.stSub (by decide))
  · simp only [Gcm.AArch64.Stitch.dR, Gcm.AArch64.Stitch.tR, hnb]
    exact (hd.ok.w.sub_left (Region.sub_prefix hp)).sub_right (Lay.wSub (by decide))

/-- The table is apart from the context, the state and the data. -/
theorem tbl_ctx : ∀ r ∈ [tblR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact L.cw'.sub_right (Lay.wSub (by decide))

theorem tbl_st {d k : Nat} (h : d + k ≤ 80) : ∀ r ∈ [tblR W], (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact (L.sb.sub_left (Lay.stSub h)).sub_right (Offset.sub W (by decide) (by decide))

/-- The interleaved loop `k`, the table written first if there are any
batches of eight blocks, given what `k` leaves from a state of `KPre`. -/
theorem stitch_core {H : Block} {x : List Byte} {icb : Block} {R : Nat} {D : Addr} {n : Nat} {s : State}
    {tb : List Instr} (htb : TbOk Ctx St W SP H tb s) (hs : SIn Ctx St W SP H x icb R D n s)
    {k : Prog isa} {c : Mem → List Byte} (h0 : n / 128 = 0 → ∀ m, c m = [])
    (hk : ∀ t, KPre t → Env Ctx St W SP t → Frame [tblR W] s.mem t.mem →
      (∀ r, r ≠ .x5 → r ≠ .x9 → t.gpr r = s.gpr r) → t.sp = s.sp → t.rd = s.rd → t.wr = s.wr →
      WP isa k t (SMid Ctx St W SP H x icb R D n c s)) :
    WP isa (Impl.AesGcm.AArch64.Stitch.stitched [] tb k) s (SMid Ctx St W SP H x icb R D n c s) := by
  have hn := hs.data.ok.lt
  rw [Impl.AesGcm.AArch64.Stitch.stitched, WP.seq_iff, WP.block_cons_iff]
  refine ⟨_, exec_lsr_x (sh := 7) (by decide), WP.block_nil ?_⟩
  generalize hs₁ : s.write .x .x9 (s.read .x .x26 >>> 7) = s₁
  have e9 : s₁.gpr .x9 = BitVec.ofNat 64 (n / 128) := by
    rw [← hs₁, gpr_write_self]
    simp only [State.read, BitVec.setWidth_eq, Size.bits, hs.x26]
    exact Gcm.AArch64.Stitch.ushr7 hn
  have g₁ : ∀ r, r ≠ .x9 → s₁.gpr r = s.gpr r := fun r h => by rw [← hs₁, gpr_write_of_ne _ _ _ h]
  have m₁ : s₁.mem = s.mem := by rw [← hs₁, mem_write]
  have sp₁ : s₁.sp = s.sp := by rw [← hs₁, sp_write]
  have rd₁ : s₁.rd = s.rd := by rw [← hs₁, rd_write]
  have wr₁ : s₁.wr = s.wr := by rw [← hs₁, wr_write]
  have he₁ : Env Ctx St W SP s₁ := hs.env.keep (fun r hr => g₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  refine WP.ite _ (Proof.Aes.AArch64.Aese.eval_zero e9 (by omega)) (fun h => ?_) (fun h => ?_)
  · have hz : n / 128 = 0 := by simpa using h
    have hp : pre n = 0 := by simp only [pre, hz]
    refine WP.block_nil ⟨he₁, fun r hr => g₁ r (by simp at hr; exact hr.2.1), ?_, ?_, ?_, ?_, sp₁, rd₁, wr₁⟩
    · rw [hp]; rfl
    · rw [hp, m₁]; exact Proof.Gcm.ctr_zero _ _ _ _ hs.cb
    · rw [h0 hz, List.append_nil, m₁]; exact hs.y
    · rw [m₁]; exact Frame.refl _ _
  · have h1 : 128 ≤ n := by
      have : ¬ n / 128 = 0 := by simpa using h
      omega
    rw [List.nil_append, WP.seq_iff]
    refine WP.mono (htb s₁ he₁ m₁ rd₁ wr₁ g₁) fun t ⟨tok, ft, gt, spt, rdt, wrt⟩ => ?_
    rw [m₁] at ft
    have gts : ∀ r, r ≠ .x5 → r ≠ .x9 → t.gpr r = s.gpr r := fun r h5 h9 => by rw [gt r h5, g₁ r h9]
    have het : Env Ctx St W SP t := hs.env.keep (fun r hr => gts r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) (by rw [spt, sp₁]) (by rw [rdt, rd₁]) (by rw [wrt, wr₁])
    have hH : blockAt t.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [blockAt_frame ft fun r hr => (tbl_ctx L r hr).sub_left (Lay.ctxSub (by decide)), hs.hH]
    refine hk t (kpre_of L het (by rw [gts _ (by decide) (by decide), hs.x22]) hs.rounds
      (by rw [gts _ (by decide) (by decide), hs.x23]) (by rw [gts _ (by decide) (by decide), hs.x26])
      (hs.data.of_eq (by rw [rdt, rd₁]) (by rw [wrt, wr₁])) h1 (hH ▸ tok)) het ft gts (by rw [spt, sp₁])
      (by rw [rdt, rd₁]) (by rw [wrt, wr₁])

/-- `SMid`, from what the loops leave. -/
theorem smid_of {H : Block} {x : List Byte} {icb : Block} {R : Nat} {D : Addr} {n : Nat} {s t t' : State}
    {c : Mem → List Byte} (hs : SIn Ctx St W SP H x icb R D n s) (het : Env Ctx St W SP t)
    (ft : Frame [tblR W] s.mem t.mem) (gt : ∀ r, r ≠ .x5 → r ≠ .x9 → t.gpr r = s.gpr r)
    (spt : t.sp = s.sp) (rdt : t.rd = s.rd) (wrt : t.wr = s.wr)
    (pd : blocksAt t'.mem (Gcm.AArch64.Stitch.dp t) (8 * Gcm.AArch64.Stitch.nb t) =
        Spec.Gcm.ctr32 (Gcm.AArch64.Stitch.ciph t) (Gcm.AArch64.Stitch.icb t)
          (blocksAt t.mem (Gcm.AArch64.Stitch.dp t) (8 * Gcm.AArch64.Stitch.nb t)))
    (pc : blockAt t'.mem (Gcm.AArch64.Stitch.stp t + BitVec.ofNat 64 48) =
        Nat.repeat Spec.Gcm.inc32 (8 * Gcm.AArch64.Stitch.nb t) (Gcm.AArch64.Stitch.icb t))
    (pf : Frame [Gcm.AArch64.Stitch.yR t, Gcm.AArch64.Stitch.cR t, Gcm.AArch64.Stitch.dR t] t.mem t'.mem)
    (pg : ∀ r, r ∉ Gcm.AArch64.Stitch.kRegs → t'.gpr r = t.gpr r) (psp : t'.sp = t.sp) (prd : t'.rd = t.rd)
    (pwr : t'.wr = t.wr) (hy : blockAt t'.mem (St + BitVec.ofNat 64 16) = ghash H (blocks (x ++ c t'.mem))) :
    SMid Ctx St W SP H x icb R D n c s t' := by
  have hn := hs.data.ok.lt
  have hR := hs.rounds
  have hRb : 16 * (R + 1) ≤ 256 := by omega
  have e20 : t.gpr .x20 = St := het.x20
  have e21 : t.gpr .x21 = Ctx := het.x21
  have e22 : t.gpr .x22 = BitVec.ofNat 64 R := by rw [gt _ (by decide) (by decide), hs.x22]
  have e23 : t.gpr .x23 = D := by rw [gt _ (by decide) (by decide), hs.x23]
  have e26 : t.gpr .x26 = BitVec.ofNat 64 n := by rw [gt _ (by decide) (by decide), hs.x26]
  simp only [Gcm.AArch64.Stitch.stp, Gcm.AArch64.Stitch.dp, Gcm.AArch64.Stitch.nb, Gcm.AArch64.Stitch.kc,
    Gcm.AArch64.Stitch.rounds, Gcm.AArch64.Stitch.icb, Gcm.AArch64.Stitch.ciph, Gcm.AArch64.Stitch.ksch,
    Gcm.AArch64.Stitch.yR, Gcm.AArch64.Stitch.cR, Gcm.AArch64.Stitch.dR, e20, e21, e22, e23, e26,
    toNat_ofNat_of_lt hn, toNat_ofNat_of_lt (show R < 2 ^ 64 by omega)] at pd pc pf
  have hk : bytesAt t.mem Ctx (16 * (R + 1)) = bytesAt s.mem Ctx (16 * (R + 1)) :=
    bytesAt_frame ft (fun r hr => (tbl_ctx L r hr).sub_left (Region.sub_prefix hRb)) (by omega)
  have hpn : pre n ≤ n := Nat.mul_div_le n 128
  have hD : ∀ r ∈ [tblR W], (⟨D, pre n⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hs.data.ok.w.sub_left (Region.sub_prefix hpn)).sub_right (Lay.wSub (by decide))
  have hcb : blockAt t.mem (St + BitVec.ofNat 64 48) = icb := by
    rw [blockAt_frame ft (tbl_st L (by decide)), hs.cb]
  rw [hk] at pd
  obtain ⟨hd, hc⟩ := Proof.Gcm.ctr_whole (ks := St + BitVec.ofNat 64 64) (ciph := ciphOf s.mem Ctx R) (icb := icb)
    (Proof.Gcm.ctr_zero _ _ _ _ hcb) (by decide) pd pc
  rw [show 16 * (8 * (n / 128)) = pre n by simp only [pre]; omega] at hd hc
  rw [Nat.zero_add] at hc
  have g' : ∀ r, r ∉ [Reg.x5, .x9, .x10, .x11, .x12, .x13, .x14] → t'.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [pg r (by simp [Gcm.AArch64.Stitch.kRegs, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2]), gt r hr.1 hr.2.1]
  refine ⟨het.keep (fun r hr => pg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) psp prd pwr, g', ?_, hc, hy, ?_,
    by rw [psp, spt], by rw [prd, rdt], by rw [pwr, wrt]⟩
  · rw [hd, bytesAt_frame ft hD (by omega)]
  · refine (ft.mono fun r hr => ?_).trans (pf.mono fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp

/-- `seal`'s interleaved loop. -/
theorem stitchE_ok (gh : Gh8Ok) {H : Block} {x : List Byte} {icb : Block} {R : Nat} {D : Addr} {n : Nat}
    {s : State} {tb : List Instr} (htb : TbOk Ctx St W SP H tb s) (hs : SIn Ctx St W SP H x icb R D n s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.stitched [] tb Impl.Gcm.AArch64.Stitch.enc) s
      (SMid Ctx St W SP H x icb R D n (fun m => bytesAt m D (pre n)) s) := by
  refine stitch_core L htb hs (fun hz m => by simp only [pre, hz]; rfl)
    fun t hp het ft gt spt rdt wrt => WP.mono (Gcm.AArch64.Stitch.enc_ok hp gh) fun t' q => ?_
  have hn := hs.data.ok.lt
  have py := q.y
  have hH : blockAt t.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ft fun r hr => (tbl_ctx L r hr).sub_left (Lay.ctxSub (by decide)), hs.hH]
  have hY : blockAt t.mem (St + BitVec.ofNat 64 16) = ghash H (blocks x) := by
    rw [blockAt_frame ft (tbl_st L (by decide)), hs.y]
  simp only [Gcm.AArch64.Stitch.stp, Gcm.AArch64.Stitch.dp, Gcm.AArch64.Stitch.nb, Gcm.AArch64.Stitch.kc,
    Gcm.AArch64.Stitch.hk, Gcm.AArch64.Stitch.y₀, het.x20, het.x21, gt .x23 (by decide) (by decide),
    gt .x26 (by decide) (by decide), hs.x23, hs.x26, toNat_ofNat_of_lt hn, hH, hY] at py
  refine smid_of L hs het ft gt spt rdt wrt q.data q.ctr q.frame q.gpr q.sp q.rd q.wr ?_
  rw [py, Proof.Gcm.blocksAt_eq, show 16 * (8 * (n / 128)) = pre n by simp only [pre]; omega, Spec.Gcm.ghash,
    Spec.Gcm.ghash, blocks_append hs.xm, Proof.Gcm.ghashFrom_append]

/-- `open`'s interleaved loop. -/
theorem stitchD_ok (gh : Gh8Ok) {H : Block} {x : List Byte} {icb : Block} {R : Nat} {D : Addr} {n : Nat}
    {s : State} {tb : List Instr} (htb : TbOk Ctx St W SP H tb s) (hs : SIn Ctx St W SP H x icb R D n s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.stitched [] tb Impl.Gcm.AArch64.Stitch.dec) s
      (SMid Ctx St W SP H x icb R D n (fun _ => bytesAt s.mem D (pre n)) s) := by
  refine stitch_core L htb hs (fun hz m => by simp only [pre, hz]; rfl)
    fun t hp het ft gt spt rdt wrt => WP.mono (Gcm.AArch64.Stitch.dec_ok hp gh) fun t' q => ?_
  have hn := hs.data.ok.lt
  have py := q.y
  have hH : blockAt t.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ft fun r hr => (tbl_ctx L r hr).sub_left (Lay.ctxSub (by decide)), hs.hH]
  have hY : blockAt t.mem (St + BitVec.ofNat 64 16) = ghash H (blocks x) := by
    rw [blockAt_frame ft (tbl_st L (by decide)), hs.y]
  have hpn : pre n ≤ n := Nat.mul_div_le n 128
  have hD : bytesAt t.mem D (pre n) = bytesAt s.mem D (pre n) := bytesAt_frame ft (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hs.data.ok.w.sub_left (Region.sub_prefix hpn)).sub_right (Lay.wSub (by decide))) (by omega)
  simp only [Gcm.AArch64.Stitch.stp, Gcm.AArch64.Stitch.dp, Gcm.AArch64.Stitch.nb, Gcm.AArch64.Stitch.kc,
    Gcm.AArch64.Stitch.hk, Gcm.AArch64.Stitch.y₀, het.x20, het.x21, gt .x23 (by decide) (by decide),
    gt .x26 (by decide) (by decide), hs.x23, hs.x26, toNat_ofNat_of_lt hn, hH, hY] at py
  refine smid_of L hs het ft gt spt rdt wrt q.data q.ctr q.frame q.gpr q.sp q.rd q.wr ?_
  rw [py, Proof.Gcm.blocksAt_eq, show 16 * (8 * (n / 128)) = pre n by simp only [pre]; omega, hD, Spec.Gcm.ghash,
    Spec.Gcm.ghash, blocks_append hs.xm, Proof.Gcm.ghashFrom_append]

end

/-! ## The rest's pointers and counts -/

theorem shl7 {q : Nat} (h : 128 * q < 2 ^ 64) : BitVec.ofNat 64 q <<< 7 = BitVec.ofNat 64 (128 * q) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega)]
  omega

theorem whole_eq {u : State} {n : Nat} (h26 : u.gpr .x26 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    (u.gpr .x26 >>> 7) <<< 7 = BitVec.ofNat 64 (pre n) := by
  rw [h26, Gcm.AArch64.Stitch.ushr7 hn, shl7 (by have := Nat.mul_div_le n 128; omega)]

/-- `seal`'s pointers past the first bytes. -/
theorem afterE_ok {u : State} {D : Addr} {n : Nat} (h23 : u.gpr .x23 = D)
    (h26 : u.gpr .x26 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    ∃ t, runBlock isa (Impl.AesGcm.AArch64.Stitch.whole ++
      ([.add .x .x23 .x23 .x9, Impl.AesGcm.AArch64.mov .x27 .x23, .sub .x .x24 .x26 .x9,
        Impl.AesGcm.AArch64.imm .x25 0] : List Instr)) u = some t ∧
      t.gpr .x23 = D + BitVec.ofNat 64 (pre n) ∧ t.gpr .x27 = D + BitVec.ofNat 64 (pre n) ∧
      t.gpr .x24 = BitVec.ofNat 64 (n - pre n) ∧ t.gpr .x25 = BitVec.ofNat 64 (pre n % 16) ∧
      Regs [.x9, .x23, .x27, .x24, .x25] u t := by
  have e9 := whole_eq h26 hn
  have hp : pre n ≤ n := Nat.mul_div_le n 128
  refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.whole], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp [gpr_write, e9, h23]
  · simp [gpr_write, e9, h23]
  · rw [h26] at e9
    simp [gpr_write, h26]
    rw [e9, Offset.ofNat_sub_ofNat hp]
  · simp [gpr_write, pre]
    rw [show 128 * (n / 128) % 16 = 0 by omega]

/-- `seal`'s pointers for hashing the rest. -/
theorem absArgsE_ok {u : State} {D : Addr} {n : Nat} (h27 : u.gpr .x27 = D + BitVec.ofNat 64 (pre n))
    (h26 : u.gpr .x26 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    ∃ t, runBlock isa ([Impl.AesGcm.AArch64.mov .x23 .x27] ++ Impl.AesGcm.AArch64.Stitch.whole ++
      ([.sub .x .x24 .x26 .x9] : List Instr)) u = some t ∧
      t.gpr .x23 = D + BitVec.ofNat 64 (pre n) ∧ t.gpr .x24 = BitVec.ofNat 64 (n - pre n) ∧
      Regs [.x23, .x9, .x24] u t := by
  have e9 := whole_eq h26 hn
  rw [h26] at e9
  have hp : pre n ≤ n := Nat.mul_div_le n 128
  refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.whole], ?_⟩
  refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp [gpr_write, h27]
  · simp [gpr_write, h26]
    rw [e9, Offset.ofNat_sub_ofNat hp]

/-- `open`'s pointers past the first bytes. -/
theorem afterD_ok {u : State} {D : Addr} {n : Nat} (h23 : u.gpr .x23 = D)
    (h26 : u.gpr .x26 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    ∃ t, runBlock isa (Impl.AesGcm.AArch64.Stitch.whole ++
      ([.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, Impl.AesGcm.AArch64.imm .x25 0] : List Instr)) u = some t ∧
      t.gpr .x23 = D + BitVec.ofNat 64 (pre n) ∧
      t.gpr .x24 = BitVec.ofNat 64 (n - pre n) ∧ t.gpr .x25 = BitVec.ofNat 64 0 ∧
      Regs [.x9, .x23, .x24, .x25] u t := by
  have e9 := whole_eq h26 hn
  have hp : pre n ≤ n := Nat.mul_div_le n 128
  refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.whole], ?_⟩
  refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp [gpr_write, e9, h23]
  · rw [h26] at e9
    simp [gpr_write, h26]
    rw [e9, Offset.ofNat_sub_ofNat hp]
  · simp [gpr_write]

end VG.Proof.AesGcm.AArch64.Stitch
