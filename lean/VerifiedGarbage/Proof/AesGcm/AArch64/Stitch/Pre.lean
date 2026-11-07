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
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Front

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
open VG.Proof.Gcm.AArch64.Stitch (KPre KPreM EPost DPost TblOk Gh8Ok)

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

/-- `SIn` for the decryption from the `n` bytes at `D` to `O`: over them
(`to` false, `O = D`), or out of place (`to`), to `O` in `x15`, apart from
them. -/
structure SInM (Ctx St W SP : Addr) (H : Block) (x : List Byte) (icb : Block) (R : Nat) (D O : Addr)
    (n : Nat) (to : Bool) (s : State) : Prop where
  env : Env Ctx St W SP s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x23 : s.gpr .x23 = D
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  src : DataOk St W s D n
  out : DataW Ctx St W s O n
  mode : cond to (s.gpr .x15 = O ∧ (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩) (O = D)
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = icb
  y : blockAt s.mem (St + BitVec.ofNat 64 16) = ghash H (blocks x)
  xm : x.length % 16 = 0

theorem SIn.toM {Ctx St W SP : Addr} {H : Block} {x : List Byte} {icb : Block} {R : Nat} {D : Addr} {n : Nat}
    {s : State} (h : SIn Ctx St W SP H x icb R D n s) : SInM Ctx St W SP H x icb R D D n false s :=
  ⟨h.env, h.x22, h.rounds, h.x23, h.x26, h.data.ok, h.data, rfl, h.hH, h.cb, h.y, h.xm⟩

/-- After the interleaved loop, from `s`: the first `pre n` bytes at `D`
encrypted (or decrypted) to `O`, the counter past them, and `Y` continued
over `c`. -/
structure SMid (Ctx St W SP : Addr) (H : Block) (x : List Byte) (icb : Block) (R : Nat) (D O : Addr)
    (n : Nat) (c : Mem → List Byte) (s t : State) : Prop where
  env : Env Ctx St W SP t
  gpr : ∀ r, r ∉ [Reg.x5, .x9, .x10, .x11, .x12, .x13, .x14, .x15] → t.gpr r = s.gpr r
  data : bytesAt t.mem O (pre n) = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D (pre n))
  ctr : Ctr t.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx R) icb (pre n)
  y : blockAt t.mem (St + BitVec.ofNat 64 16) = ghash H (blocks (x ++ c t.mem))
  frame : Frame (sFrame St W O n) s.mem t.mem
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem notMem_k15 {r : Reg} (h : r ∉ [Reg.x5, .x9, .x10, .x11, .x12, .x13, .x14, .x15]) :
    r ∉ Reg.x15 :: Gcm.AArch64.Stitch.kRegs := by
  simp only [Gcm.AArch64.Stitch.kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h ⊢
  exact ⟨h.2.2.2.2.2.2.2, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- The loops' precondition, from the environment and the table. -/
theorem kpre_of {t : State} {R : Nat} {D O : Addr} {n : Nat} {to : Bool} (he : Env Ctx St W SP t)
    (h22 : t.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) (h23 : t.gpr .x23 = D)
    (h26 : t.gpr .x26 = BitVec.ofNat 64 n) (hd : DataOk St W t D n)
    (ho : DataW Ctx St W t O n) (hm : cond to (t.gpr .x15 = O ∧ (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩) (O = D))
    (h1 : 128 ≤ n) (tok : TblOk t.mem W (blockAt t.mem (Ctx + BitVec.ofNat 64 240))) : KPreM t to := by
  have hn := hd.lt
  have hnb : Gcm.AArch64.Stitch.nb t = n / 128 := by
    simp only [Gcm.AArch64.Stitch.nb, h26, toNat_ofNat_of_lt hn]
  have hp : 128 * (n / 128) ≤ n := Nat.mul_div_le n 128
  have hop : Gcm.AArch64.Stitch.op t to = O := by
    cases to with
    | false => exact h23.trans hm.symm
    | true => exact hm.1
  obtain ⟨e19, e20, e21, -, perm⟩ := he
  subst e19 e20 e21 h23
  have hR' : Gcm.AArch64.Stitch.rounds t = R := by
    simp only [Gcm.AArch64.Stitch.rounds, h22, toNat_ofNat_of_lt (show R < 2 ^ 64 by omega_arith)]
  exact {
    rounds := hR' ▸ hR
    nb1 := by rw [hnb]; omega_arith
    k_in := perm.ctx _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
    y_in := perm.stW (d := 16) (n := 16) (by decide)
    c_in := perm.stW (d := 48) (n := 16) (by decide)
    d_in := by rw [hnb]; exact covers_prefix hd.rd hp _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
    o_in := by
      rw [hnb, hop]; exact covers_prefix ho.wr hp _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
    t_in := perm.wR (d := 512) (n := 192) (by decide)
    o_k := by
      simp only [Gcm.AArch64.Stitch.oR, Gcm.AArch64.Stitch.kR, hnb, hop]
      exact ho.ctx.symm.sub_left (Region.sub_prefix hp)
    o_y := by
      simp only [Gcm.AArch64.Stitch.oR, Gcm.AArch64.Stitch.yR, hnb, hop]
      exact (ho.ok.st.sub_left (Region.sub_prefix hp)).sub_right (Lay.stSub (by decide))
    o_c := by
      simp only [Gcm.AArch64.Stitch.oR, Gcm.AArch64.Stitch.cR, hnb, hop]
      exact (ho.ok.st.sub_left (Region.sub_prefix hp)).sub_right (Lay.stSub (by decide))
    o_t := by
      simp only [Gcm.AArch64.Stitch.oR, Gcm.AArch64.Stitch.tR, hnb, hop]
      exact (ho.ok.w.sub_left (Region.sub_prefix hp)).sub_right (Lay.wSub (by decide))
    d_o := fun h => by
      subst h
      obtain ⟨-, hdo⟩ := hm
      simp only [Gcm.AArch64.Stitch.dR, Gcm.AArch64.Stitch.oR, hnb, hop]
      exact (hdo.sub_left (Region.sub_prefix hp)).sub_right (Region.sub_prefix hp)
    y_c := Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    wrap_d := by rw [hnb]; change (t.gpr .x23).toNat + 128 * (n / 128) ≤ 2 ^ 64; have := hd.wrap; omega_arith
    wrap_o := by rw [hnb, hop]; have := ho.ok.wrap; omega_arith
    wrap_k := L.cw
    wrap_t := by change (t.gpr .x19).toNat + 704 ≤ 2 ^ 64; have := L.ww; omega_arith
    wrap_s := by change (t.gpr .x20).toNat + 64 ≤ 2 ^ 64; have := L.sw; omega_arith
    tbl := tok }

/-- The table is apart from the context, the state and the data. -/
theorem tbl_ctx : ∀ r ∈ [tblR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact L.cw'.sub_right (Lay.wSub (by decide))

theorem tbl_st {d k : Nat} (h : d + k ≤ 80) : ∀ r ∈ [tblR W], (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact (L.sb.sub_left (Lay.stSub h)).sub_right (Offset.sub W (by decide) (by decide))

/-- The interleaved loop `k`, the table written first if there are any
batches of eight blocks, given what `k` leaves from a state of `KPreM`. -/
theorem stitch_core {H : Block} {x : List Byte} {icb : Block} {R : Nat} {D O : Addr} {n : Nat} {to : Bool}
    {s : State} {tb : List Instr} (htb : TbOk Ctx St W SP H tb s) (hs : SInM Ctx St W SP H x icb R D O n to s)
    {k : Prog isa} {c : Mem → List Byte} (h0 : n / 128 = 0 → ∀ m, c m = [])
    (hk : ∀ t, KPreM t to → Env Ctx St W SP t → Frame [tblR W] s.mem t.mem →
      (∀ r, r ≠ .x5 → r ≠ .x9 → t.gpr r = s.gpr r) → t.sp = s.sp → t.rd = s.rd → t.wr = s.wr →
      WP isa k t (SMid Ctx St W SP H x icb R D O n c s)) :
    WP isa (Impl.AesGcm.AArch64.Stitch.stitched [] tb k) s (SMid Ctx St W SP H x icb R D O n c s) := by
  have hn := hs.src.lt
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
  refine WP.ite _ (Proof.Aes.AArch64.Aese.eval_zero e9 (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have hz : n / 128 = 0 := by simpa using h
    have hp : pre n = 0 := by simp only [pre, hz]
    refine WP.block_nil ⟨he₁, fun r hr => g₁ r (by simp at hr; exact hr.2.1), ?_, ?_, ?_, ?_, sp₁, rd₁, wr₁⟩
    · rw [hp]; rfl
    · rw [hp, m₁]; exact Proof.Gcm.ctr_zero _ _ _ _ hs.cb
    · rw [h0 hz, List.append_nil, m₁]; exact hs.y
    · rw [m₁]; exact Frame.refl _ _
  · have h1 : 128 ≤ n := by
      have : ¬ n / 128 = 0 := by simpa using h
      omega_arith
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
    have hm : cond to (t.gpr .x15 = O ∧ (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩) (O = D) := by
      have := hs.mode
      cases to with
      | false => exact this
      | true => exact ⟨by rw [gts _ (by decide) (by decide)]; exact this.1, this.2⟩
    refine hk t (kpre_of L het (by rw [gts _ (by decide) (by decide), hs.x22]) hs.rounds
      (by rw [gts _ (by decide) (by decide), hs.x23]) (by rw [gts _ (by decide) (by decide), hs.x26])
      (hs.src.of_eq (by rw [rdt, rd₁]) (by rw [wrt, wr₁])) (hs.out.of_eq (by rw [rdt, rd₁]) (by rw [wrt, wr₁]))
      hm h1 (hH ▸ tok)) het ft gts (by rw [spt, sp₁]) (by rw [rdt, rd₁]) (by rw [wrt, wr₁])

/-- `SMid`, from what the loops leave. -/
theorem smid_of {H : Block} {x : List Byte} {icb : Block} {R : Nat} {D O : Addr} {n : Nat} {to : Bool}
    {s t t' : State} {c : Mem → List Byte} (hs : SInM Ctx St W SP H x icb R D O n to s)
    (het : Env Ctx St W SP t)
    (ft : Frame [tblR W] s.mem t.mem) (gt : ∀ r, r ≠ .x5 → r ≠ .x9 → t.gpr r = s.gpr r)
    (spt : t.sp = s.sp) (rdt : t.rd = s.rd) (wrt : t.wr = s.wr)
    (pd : blocksAt t'.mem (Gcm.AArch64.Stitch.op t to) (8 * Gcm.AArch64.Stitch.nb t) =
        Spec.Gcm.ctr32 (Gcm.AArch64.Stitch.ciph t) (Gcm.AArch64.Stitch.icb t)
          (blocksAt t.mem (Gcm.AArch64.Stitch.dp t) (8 * Gcm.AArch64.Stitch.nb t)))
    (pc : blockAt t'.mem (Gcm.AArch64.Stitch.stp t + BitVec.ofNat 64 48) =
        Nat.repeat Spec.Gcm.inc32 (8 * Gcm.AArch64.Stitch.nb t) (Gcm.AArch64.Stitch.icb t))
    (pf : Frame [Gcm.AArch64.Stitch.yR t, Gcm.AArch64.Stitch.cR t, Gcm.AArch64.Stitch.oR t to] t.mem t'.mem)
    (pg : ∀ r, r ∉ Gcm.AArch64.Stitch.kRegsT to → t'.gpr r = t.gpr r) (psp : t'.sp = t.sp) (prd : t'.rd = t.rd)
    (pwr : t'.wr = t.wr) (hy : blockAt t'.mem (St + BitVec.ofNat 64 16) = ghash H (blocks (x ++ c t'.mem))) :
    SMid Ctx St W SP H x icb R D O n c s t' := by
  have hn := hs.src.lt
  have hR := hs.rounds
  have hRb : 16 * (R + 1) ≤ 256 := by omega_arith
  have e20 : t.gpr .x20 = St := het.x20
  have e21 : t.gpr .x21 = Ctx := het.x21
  have e22 : t.gpr .x22 = BitVec.ofNat 64 R := by rw [gt _ (by decide) (by decide), hs.x22]
  have e23 : t.gpr .x23 = D := by rw [gt _ (by decide) (by decide), hs.x23]
  have e26 : t.gpr .x26 = BitVec.ofNat 64 n := by rw [gt _ (by decide) (by decide), hs.x26]
  have hop : Gcm.AArch64.Stitch.op t to = O := by
    have := hs.mode
    cases to with
    | false => exact e23.trans this.symm
    | true => exact (gt _ (by decide) (by decide)).trans this.1
  rw [hop] at pd
  simp only [Gcm.AArch64.Stitch.oR, hop] at pf
  simp only [Gcm.AArch64.Stitch.stp, Gcm.AArch64.Stitch.dp, Gcm.AArch64.Stitch.nb, Gcm.AArch64.Stitch.kc,
    Gcm.AArch64.Stitch.rounds, Gcm.AArch64.Stitch.icb, Gcm.AArch64.Stitch.ciph, Gcm.AArch64.Stitch.ksch,
    Gcm.AArch64.Stitch.yR, Gcm.AArch64.Stitch.cR, e20, e21, e22, e23, e26,
    toNat_ofNat_of_lt hn, toNat_ofNat_of_lt (show R < 2 ^ 64 by omega_arith)] at pd pc pf
  have hk : bytesAt t.mem Ctx (16 * (R + 1)) = bytesAt s.mem Ctx (16 * (R + 1)) :=
    bytesAt_frame ft (fun r hr => (tbl_ctx L r hr).sub_left (Region.sub_prefix hRb)) (by omega_arith)
  have hpn : pre n ≤ n := Nat.mul_div_le n 128
  have hD : ∀ r ∈ [tblR W], (⟨D, pre n⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hs.src.w.sub_left (Region.sub_prefix hpn)).sub_right (Lay.wSub (by decide))
  have hcb : blockAt t.mem (St + BitVec.ofNat 64 48) = icb := by
    rw [blockAt_frame ft (tbl_st L (by decide)), hs.cb]
  rw [hk] at pd
  obtain ⟨hd, hc⟩ := Proof.Gcm.ctr_wholeTo (ks := St + BitVec.ofNat 64 64) (ciph := ciphOf s.mem Ctx R) (icb := icb)
    (Proof.Gcm.ctr_zero _ _ _ _ hcb) (by decide) pd pc
  rw [show 16 * (8 * (n / 128)) = pre n by simp only [pre]; omega_arith] at hd hc
  rw [Nat.zero_add] at hc
  have g' : ∀ r, r ∉ [Reg.x5, .x9, .x10, .x11, .x12, .x13, .x14, .x15] → t'.gpr r = s.gpr r := fun r hr => by
    have h59 : r ≠ .x5 ∧ r ≠ .x9 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact ⟨hr.1, hr.2.1⟩
    rw [pg r (Gcm.AArch64.Stitch.notMem_kRegsT _ (notMem_k15 hr)), gt r h59.1 h59.2]
  refine ⟨het.keep (fun r hr => pg r (Gcm.AArch64.Stitch.notMem_kRegsT _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide))) psp prd pwr, g', ?_, hc, hy, ?_,
    by rw [psp, spt], by rw [prd, rdt], by rw [pwr, wrt]⟩
  · rw [hd, bytesAt_frame ft hD (by omega_arith)]
  · refine (ft.mono fun r hr => ?_).trans (pf.mono fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp

/-- `seal`'s interleaved loop. -/
theorem stitchE_ok (gh : Gh8Ok) {H : Block} {x : List Byte} {icb : Block} {R : Nat} {D : Addr} {n : Nat}
    {s : State} {tb : List Instr} (htb : TbOk Ctx St W SP H tb s) (hs : SIn Ctx St W SP H x icb R D n s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.stitched [] tb Impl.Gcm.AArch64.Stitch.enc) s
      (SMid Ctx St W SP H x icb R D D n (fun m => bytesAt m D (pre n)) s) := by
  refine stitch_core L htb hs.toM (fun hz m => by simp only [pre, hz]; rfl)
    fun t hp het ft gt spt rdt wrt => WP.mono (Gcm.AArch64.Stitch.enc_ok hp.toKPre gh) fun t' q => ?_
  have hn := hs.data.ok.lt
  have py := q.y
  have hH : blockAt t.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ft fun r hr => (tbl_ctx L r hr).sub_left (Lay.ctxSub (by decide)), hs.hH]
  have hY : blockAt t.mem (St + BitVec.ofNat 64 16) = ghash H (blocks x) := by
    rw [blockAt_frame ft (tbl_st L (by decide)), hs.y]
  simp only [Gcm.AArch64.Stitch.stp, Gcm.AArch64.Stitch.dp, Gcm.AArch64.Stitch.nb, Gcm.AArch64.Stitch.kc,
    Gcm.AArch64.Stitch.hk, Gcm.AArch64.Stitch.y₀, het.x20, het.x21, gt .x23 (by decide) (by decide),
    gt .x26 (by decide) (by decide), hs.x23, hs.x26, toNat_ofNat_of_lt hn, hH, hY] at py
  refine smid_of L hs.toM het ft gt spt rdt wrt q.data q.ctr q.frame q.gpr q.sp q.rd q.wr ?_
  rw [py, Proof.Gcm.blocksAt_eq, show 16 * (8 * (n / 128)) = pre n by simp only [pre]; omega_arith, Spec.Gcm.ghash,
    Spec.Gcm.ghash, blocks_append hs.xm, Proof.Gcm.ghashFrom_append]

/-- `open`'s interleaved loop, from the text at `D` to `O`: over it, or out of
place. -/
theorem stitchDM_ok (gh : Gh8Ok) {H : Block} {x : List Byte} {icb : Block} {R : Nat} {D O : Addr} {n : Nat}
    {to : Bool} {s : State} {tb : List Instr} (htb : TbOk Ctx St W SP H tb s)
    (hs : SInM Ctx St W SP H x icb R D O n to s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.stitched [] tb (Impl.Gcm.AArch64.Stitch.dec to)) s
      (SMid Ctx St W SP H x icb R D O n (fun _ => bytesAt s.mem D (pre n)) s) := by
  refine stitch_core L htb hs (fun hz m => by simp only [pre, hz]; rfl)
    fun t hp het ft gt spt rdt wrt => WP.mono (Gcm.AArch64.Stitch.decM_ok hp gh) fun t' q => ?_
  have hn := hs.src.lt
  have py := q.y
  have hH : blockAt t.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ft fun r hr => (tbl_ctx L r hr).sub_left (Lay.ctxSub (by decide)), hs.hH]
  have hY : blockAt t.mem (St + BitVec.ofNat 64 16) = ghash H (blocks x) := by
    rw [blockAt_frame ft (tbl_st L (by decide)), hs.y]
  have hpn : pre n ≤ n := Nat.mul_div_le n 128
  have hD : bytesAt t.mem D (pre n) = bytesAt s.mem D (pre n) := bytesAt_frame ft (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hs.src.w.sub_left (Region.sub_prefix hpn)).sub_right (Lay.wSub (by decide))) (by omega_arith)
  simp only [Gcm.AArch64.Stitch.stp, Gcm.AArch64.Stitch.dp, Gcm.AArch64.Stitch.nb, Gcm.AArch64.Stitch.kc,
    Gcm.AArch64.Stitch.hk, Gcm.AArch64.Stitch.y₀, het.x20, het.x21, gt .x23 (by decide) (by decide),
    gt .x26 (by decide) (by decide), hs.x23, hs.x26, toNat_ofNat_of_lt hn, hH, hY] at py
  refine smid_of L hs het ft gt spt rdt wrt q.data q.ctr q.frame q.gpr q.sp q.rd q.wr ?_
  rw [py, Proof.Gcm.blocksAt_eq, show 16 * (8 * (n / 128)) = pre n by simp only [pre]; omega_arith, hD, Spec.Gcm.ghash,
    Spec.Gcm.ghash, blocks_append hs.xm, Proof.Gcm.ghashFrom_append]

/-- `open`'s interleaved loop, in place. -/
theorem stitchD_ok (gh : Gh8Ok) {H : Block} {x : List Byte} {icb : Block} {R : Nat} {D : Addr} {n : Nat}
    {s : State} {tb : List Instr} (htb : TbOk Ctx St W SP H tb s) (hs : SIn Ctx St W SP H x icb R D n s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.stitched [] tb Impl.Gcm.AArch64.Stitch.dec) s
      (SMid Ctx St W SP H x icb R D D n (fun _ => bytesAt s.mem D (pre n)) s) :=
  stitchDM_ok L gh htb hs.toM

end

/-! ## The rest's pointers and counts -/

theorem shl7 {q : Nat} (h : 128 * q < 2 ^ 64) : BitVec.ofNat 64 q <<< 7 = BitVec.ofNat 64 (128 * q) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega_arith)]
  omega_arith

theorem whole_eq {u : State} {n : Nat} (h26 : u.gpr .x26 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    (u.gpr .x26 >>> 7) <<< 7 = BitVec.ofNat 64 (pre n) := by
  rw [h26, Gcm.AArch64.Stitch.ushr7 hn, shl7 (by have := Nat.mul_div_le n 128; omega_arith)]

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
    rw [show 128 * (n / 128) % 16 = 0 by omega_arith]

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

/-! ## `open`'s first bytes, in place or out of place -/

/-- What `decPart` writes: `Y`, the counter block, the text and the table. -/
abbrev sFrameN (St W D : Addr) (n : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 16, 16⟩, ⟨St + BitVec.ofNat 64 48, 16⟩, ⟨D, n⟩, tblR W]

/-- What `decPart tb to` leaves, from `s`: the first `pre n` bytes of the
ciphertext at `S` decrypted to the text at `D`, the rest of the ciphertext
after them there, the counter past them, `Y` continued over them, and `D`
the text (`x23`). -/
structure DecP (Ctx St W SP : Addr) (H : Block) (x : List Byte) (icb : Block) (R : Nat) (S D : Addr)
    (n : Nat) (s t : State) : Prop where
  env : Env Ctx St W SP t
  gpr : ∀ r, r ∉ [Reg.x5, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x23] → t.gpr r = s.gpr r
  x23 : t.gpr .x23 = D
  data : bytesAt t.mem D (pre n) = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem S (pre n))
  rest : bytesAt t.mem (D + BitVec.ofNat 64 (pre n)) (n - pre n) =
    bytesAt s.mem (S + BitVec.ofNat 64 (pre n)) (n - pre n)
  ctr : Ctr t.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx R) icb (pre n)
  y : blockAt t.mem (St + BitVec.ofNat 64 16) = ghash H (blocks (x ++ bytesAt s.mem S (pre n)))
  frame : Frame (sFrameN St W D n) s.mem t.mem
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- `tailTo`'s arguments: the rest's length, and where it starts in the
ciphertext (`x23`) and in the destination (at `W + dataO`). -/
theorem tailArgs_run {Ctx St W SP : Addr} {s : State} {S D : Addr} {n : Nat} (he : Env Ctx St W SP s)
    (h23 : s.gpr .x23 = S) (h26 : s.gpr .x26 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64)
    (hsl : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D) :
    ∃ u₁, runBlock isa (Impl.AesGcm.AArch64.Stitch.whole ++
        ([.ldr .x .x11 .x19 Impl.AesGcm.AArch64.dataO, .add .x .x11 .x11 .x9, .add .x .x12 .x23 .x9,
          .sub .x .x13 .x26 .x9] : List Instr)) s = some u₁ ∧
      u₁.gpr .x11 = D + BitVec.ofNat 64 (pre n) ∧ u₁.gpr .x12 = S + BitVec.ofNat 64 (pre n) ∧
      u₁.gpr .x13 = BitVec.ofNat 64 (n - pre n) ∧ Regs [.x9, .x11, .x12, .x13] s u₁ := by
  have hpn : pre n ≤ n := Nat.mul_div_le n 128
  have q₁ := he.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have e₁ : s.mem.read (W + 232#64) 8 = D := by
    rw [show s.mem.read (W + 232#64) 8 = s.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, hsl]
  have e₉ := whole_eq h26 hn
  rw [h26] at e₉
  refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.whole, he.x19, q₁], ?_⟩
  refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp [gpr_write, e₁, e₉, h26]
  · simp [gpr_write, e₉, h23, h26]
  · simp [gpr_write, h26]
    rw [e₉, Offset.ofNat_sub_ofNat hpn]

/-- The destination, kept at `W + dataO`, loaded into `r`. -/
theorem ldrSlot_run {Ctx St W SP : Addr} {s : State} {D : Addr} (r : Reg) (he : Env Ctx St W SP s)
    (hsl : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D) :
    ∃ u, runBlock isa [.ldr .x r .x19 Impl.AesGcm.AArch64.dataO] s = some u ∧ u.gpr r = D ∧ Regs [r] s u := by
  have q₂ := he.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have e₂ : s.mem.read (W + 232#64) 8 = D := by
    rw [show s.mem.read (W + 232#64) 8 = s.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, hsl]
  refine ⟨_, by arun [he.x19, q₂], ?_⟩
  refine ⟨by simp [gpr_write, e₂], ⟨fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩⟩
  have h' : r' ≠ r := fun h => hr' (h ▸ List.mem_singleton_self _)
  simp [gpr_write, h']

/-- What `decPart tb to` needs, from `s`: the ciphertext at `S` (`x23`), the
text at `D` (kept at `W + dataO`), over it (`S = D`) or apart from it, and
what `SIn` needs of the rest, with a `tb` that writes the table from any state
whose memory differs from `s`'s only in the text. -/
structure DecIn (Ctx St W SP : Addr) (H : Block) (x : List Byte) (icb : Block) (R : Nat) (S D : Addr) (n : Nat)
    (to : Bool) (tb : List Instr) (s : State) : Prop where
  tbOk : ∀ u : State, Env Ctx St W SP u → u.rd = s.rd → u.wr = s.wr → Frame [⟨D, n⟩] s.mem u.mem →
    TbOk Ctx St W SP H tb u
  env : Env Ctx St W SP s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x23 : s.gpr .x23 = S
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  src : DataOk St W s S n
  out : DataW Ctx St W s D n
  mode : cond to ((⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (S = D)
  slot : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = icb
  y : blockAt s.mem (St + BitVec.ofNat 64 16) = ghash H (blocks x)
  xm : x.length % 16 = 0

/-- Out of place, after `tailTo` from `s`: what the loop needs, the rest
copied to the text, and nothing else written. -/
structure TailIn (Ctx St W SP : Addr) (H : Block) (x : List Byte) (icb : Block) (R : Nat) (S D : Addr) (n : Nat)
    (tb : List Instr) (s u : State) : Prop where
  sin : SInM Ctx St W SP H x icb R S D n true u
  tbOk : TbOk Ctx St W SP H tb u
  frame : Frame [⟨D, n⟩] s.mem u.mem
  gpr : ∀ r, r ∉ [Reg.x9, .x11, .x12, .x13, .x14, .x15] → u.gpr r = s.gpr r
  rest : bytesAt u.mem (D + BitVec.ofNat 64 (pre n)) (n - pre n) =
    bytesAt s.mem (S + BitVec.ofNat 64 (pre n)) (n - pre n)
  ciph : ciphOf u.mem Ctx R = ciphOf s.mem Ctx R
  src : bytesAt u.mem S (pre n) = bytesAt s.mem S (pre n)
  slot : u.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sp : u.sp = s.sp
  rd : u.rd = s.rd
  wr : u.wr = s.wr

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

omit L in
/-- Out of place, `tailTo`: the rest copied from the ciphertext to the text,
and the text in `x15`. -/
theorem tailPre_ok {H : Block} {x : List Byte} {icb : Block} {R : Nat} {S D : Addr} {n : Nat} {s : State}
    {tb : List Instr} (i : DecIn Ctx St W SP H x icb R S D n true tb s) :
    WP isa Impl.AesGcm.AArch64.Stitch.tailTo s (TailIn Ctx St W SP H x icb R S D n tb s) := by
  have hn := i.out.ok.lt
  have hpn : pre n ≤ n := Nat.mul_div_le n 128
  have hSD : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩ := i.mode
  unfold Impl.AesGcm.AArch64.Stitch.tailTo
  obtain ⟨u₁, run₁, x11₁, x12₁, x13₁, r₁⟩ := tailArgs_run i.env i.x23 i.x26 hn i.slot
  refine WP.seq (WP.of_runBlock ⟨u₁, run₁, ?_⟩)
  have hlp : LoopPre u₁ (S + BitVec.ofNat 64 (pre n)) (D + BitVec.ofNat 64 (pre n)) (n - pre n) :=
    ⟨by simp only [pre]; omega_arith, by rw [r₁.rd, r₁.wr]; exact (i.src.drop hpn).rd,
      by rw [r₁.wr]; exact (i.out.drop hpn).wr,
      (hSD.sub_left (Offset.sub_base S (by omega_arith))).sub_right (Offset.sub_base D (by omega_arith))⟩
  refine WP.seq (WP.mono (copy_ok u₁ x12₁ x11₁ x13₁ hlp) fun u₂ ⟨m₂, g₂, sp₂, rd₂, wr₂⟩ => ?_)
  generalize hL : bytesAt u₁.mem (S + BitVec.ofNat 64 (pre n)) (n - pre n) = Lr at m₂
  have hLl : Lr.length = n - pre n := by rw [← hL, length_bytesAt]
  have f₂ : Frame [⟨D, n⟩] s.mem u₂.mem := by
    rw [m₂, r₁.mem]
    exact (writeBytes_frame' _ hLl).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base D (by omega_arith)⟩
  have gs₂ : ∀ r, r ∉ [Reg.x9, .x11, .x12, .x13, .x14, .x15] → u₂.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₂ r (by simp [loopRegs, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
      r₁.others r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1])]
  have he₂ : Env Ctx St W SP u₂ := i.env.keep (fun r hr => gs₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) (by rw [sp₂, r₁.sp]) (by rw [rd₂, r₁.rd]) (by rw [wr₂, r₁.wr])
  have dWD : ∀ r ∈ [(⟨D, n⟩ : Region)], (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (i.out.ok.w.sub_right (Lay.wSub (by decide))).symm
  have sl₂ : u₂.mem.readW (W + BitVec.ofNat 64 232) 64 = D := by
    rw [slot_kept f₂ dWD (by decide) (by decide), i.slot]
  obtain ⟨u₃, run₃, x15₃, r₃⟩ := ldrSlot_run .x15 he₂ sl₂
  refine WP.of_runBlock ⟨u₃, run₃, ?_⟩
  have he₃ := he₂.of_regs r₃
  have gs₃ : ∀ r, r ∉ [Reg.x9, .x11, .x12, .x13, .x14, .x15] → u₃.gpr r = s.gpr r := fun r hr => by
    rw [r₃.others r (fun h => hr (by simp at h; simp [h])), gs₂ r hr]
  have m₃ : u₃.mem = u₂.mem := r₃.mem
  have f₃ : Frame [⟨D, n⟩] s.mem u₃.mem := by rw [m₃]; exact f₂
  have dS : ∀ {E : Addr} {k : Nat}, Region.Sub ⟨E, k⟩ ⟨S, n⟩ → ∀ r ∈ [(⟨D, n⟩ : Region)],
      (⟨E, k⟩ : Region).Disjoint r := fun hE r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hSD.sub_left hE
  have dC : ∀ r ∈ [(⟨D, n⟩ : Region)], (⟨Ctx, 256⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact i.out.ctx
  have dSt : ∀ {a k : Nat}, a + k ≤ 80 → ∀ r ∈ [(⟨D, n⟩ : Region)],
      (⟨St + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (i.out.ok.st.sub_right (Lay.stSub h)).symm
  have rd₃ : u₃.rd = s.rd := by rw [r₃.rd, rd₂, r₁.rd]
  have wr₃ : u₃.wr = s.wr := by rw [r₃.wr, wr₂, r₁.wr]
  have hw := bytesAt_writeBytes_self u₁.mem (D + BitVec.ofNat 64 (pre n)) Lr (by omega_arith)
  rw [hLl] at hw
  exact {
    sin := {
      env := he₃
      x22 := by rw [gs₃ _ (by decide), i.x22]
      rounds := i.rounds
      x23 := by rw [gs₃ _ (by decide), i.x23]
      x26 := by rw [gs₃ _ (by decide), i.x26]
      src := i.src.of_eq rd₃ wr₃
      out := i.out.of_eq rd₃ wr₃
      mode := ⟨x15₃, hSD⟩
      hH := by rw [blockAt_frame f₃ fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide)), i.hH]
      cb := by rw [blockAt_frame f₃ (dSt (by decide)), i.cb]
      y := by rw [blockAt_frame f₃ (dSt (by decide)), i.y]
      xm := i.xm }
    tbOk := i.tbOk u₃ he₃ rd₃ wr₃ f₃
    frame := f₃
    gpr := gs₃
    rest := by rw [m₃, m₂, hw, ← hL, r₁.mem]
    ciph := ciph_frame f₃ dC i.rounds
    src := bytesAt_frame f₃ (dS (Region.sub_prefix hpn)) (by omega_arith)
    slot := by rw [m₃]; exact sl₂
    sp := by rw [r₃.sp, sp₂, r₁.sp]
    rd := rd₃
    wr := wr₃ }

/-- `decPart tb to`, from the ciphertext at `S` (`x23`) to the text at `D`
(kept at `W + dataO`): in place (`S = D`), the loop; out of place (`S`
apart from `D`), the rest copied to `D` (`tailTo`), then the loop to `D`. -/
theorem decPart_ok (gh : Gh8Ok) {H : Block} {x : List Byte} {icb : Block} {R : Nat} {S D : Addr} {n : Nat}
    {to : Bool} {s : State} {tb : List Instr} (i : DecIn Ctx St W SP H x icb R S D n to tb s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.decPart tb to) s (DecP Ctx St W SP H x icb R S D n s) := by
  have hn := i.out.ok.lt
  have hpn : pre n ≤ n := Nat.mul_div_le n 128
  -- The rest of the text, apart from what the loop writes.
  have dR : ∀ {E : Addr}, (⟨E, n⟩ : Region).Disjoint ⟨St, 80⟩ → (⟨E, n⟩ : Region).Disjoint ⟨W, 2560⟩ →
      ∀ r ∈ sFrame St W E n, (⟨E + BitVec.ofNat 64 (pre n), n - pre n⟩ : Region).Disjoint r := by
    intro E hst hw r hr
    have sub : Region.Sub ⟨E + BitVec.ofNat 64 (pre n), n - pre n⟩ ⟨E, n⟩ := Offset.sub_base E (by omega_arith)
    simp only [sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hst.sub_left sub).sub_right (Lay.stSub (by decide))
    · exact (hst.sub_left sub).sub_right (Lay.stSub (by decide))
    · exact (Offset.base_disjoint E (Nat.le_refl _) (by omega_arith)).symm
    · exact (hw.sub_left sub).sub_right (Lay.wSub (by decide))
  have fsub : ∀ {E : Addr}, ∀ r ∈ sFrame St W E n, ∃ r' ∈ sFrameN St W E n, Region.Sub r r' := by
    intro E r hr
    simp only [sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.sub_prefix hpn⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
        fun _ h => h⟩
  cases to with
  | false =>
    have hSD : S = D := i.mode
    subst hSD
    have hs : SInM Ctx St W SP H x icb R S S n false s :=
      ⟨i.env, i.x22, i.rounds, i.x23, i.x26, i.src, i.out, rfl, i.hH, i.cb, i.y, i.xm⟩
    refine WP.mono (stitchDM_ok L gh (i.tbOk s i.env rfl rfl (Frame.refl _ _)) hs) fun t q => ?_
    exact {
      env := q.env
      gpr := fun r hr => q.gpr r fun h => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h | h | h | h | h | h | h <;> simp [h])
      x23 := by rw [q.gpr _ (by decide), i.x23]
      data := q.data
      rest := bytesAt_frame q.frame (dR i.out.ok.st i.out.ok.w) (by omega_arith)
      ctr := q.ctr
      y := q.y
      frame := q.frame.sub fsub
      sp := q.sp
      rd := q.rd
      wr := q.wr }
  | true =>
    simp only [Impl.AesGcm.AArch64.Stitch.decPart, cond]
    refine WP.seq (WP.mono (tailPre_ok i) fun u₃ T => ?_)
    refine WP.seq (WP.mono (stitchDM_ok L gh T.tbOk T.sin) fun u₄ q => ?_)
    -- The text, `D`, in `x23`.
    have dSl : ∀ r ∈ sFrame St W D n, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
      intro r hr
      simp only [sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact (L.st_w (a := 48) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact ((i.out.ok.w.sub_left (Region.sub_prefix hpn)).sub_right (Lay.wSub (by decide))).symm
      · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    have sl₄ : u₄.mem.readW (W + BitVec.ofNat 64 232) 64 = D := by
      rw [slot_kept q.frame dSl (by decide) (by decide), T.slot]
    obtain ⟨u₅, run₅, x23₅, r₅⟩ := ldrSlot_run .x23 q.env sl₄
    refine WP.of_runBlock ⟨u₅, run₅, ?_⟩
    have m₅ : u₅.mem = u₄.mem := r₅.mem
    exact {
      env := q.env.of_regs r₅
      gpr := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [r₅.others r (by simp [hr.2.2.2.2.2.2.2.2]),
          q.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
            hr.2.2.2.2.2.2.2.1]),
          T.gpr r (by simp [hr.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1])]
      x23 := x23₅
      data := by rw [m₅, q.data, T.ciph, T.src]
      rest := by rw [m₅, bytesAt_frame q.frame (dR i.out.ok.st i.out.ok.w) (by omega_arith), T.rest]
      ctr := by rw [m₅, ← T.ciph]; exact q.ctr
      y := by rw [m₅, q.y, T.src]
      frame := by
        rw [m₅]
        exact (T.frame.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩).trans
          (q.frame.sub fsub)
      sp := by rw [r₅.sp, q.sp, T.sp]
      rd := by rw [r₅.rd, q.rd, T.rd]
      wr := by rw [r₅.wr, q.wr, T.wr] }

end

end VG.Proof.AesGcm.AArch64.Stitch
