module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
public import VerifiedGarbage.Impl.Gcm.AArch64.Stitch
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave
public import VerifiedGarbage.Proof.Framework.AArch64.InterleaveFootprints
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Loop
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.SealBuffers
public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tbl
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Pre
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.Absorb

@[expose] public section

/-! The out-of-place gather derives its interleaved GHASH table directly
from the hash subkey in the ordinary AES context. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.Gcm.AArch64.Pmull
open VG.Proof.AesGcm.AArch64.Stitch (PT tblR tbl_ok)
open VG.Impl.Gcm.AArch64.Pmull (tReg sReg)
open VG.Impl.AesGcm.AArch64.DirectGather (tableFromKey)

structure DirectTablePost (s t : State) : Prop where
  tbl : TblOk t.mem (s.gpr .x19) (Spec.Gcm.ctxH s.mem (s.gpr .x21))
  frame : Frame [tblR (s.gpr .x19)] s.mem t.mem
  gpr : ∀ r, r ≠ .x0 → r ≠ .x5 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- The two algebraic facts used by the stitched machine proof. Registration
supplies them once, keeping polynomial algebra out of the descriptor loop. -/
structure GatherLaws : Prop where
  hash : Gh8Ok
  table : ∀ {s : State}, InRegions (s.rd ++ s.wr) (s.gpr .x21 + BitVec.ofNat 64 240) 16 →
    InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 512) 192 → WP isa (.block tableFromKey) s (DirectTablePost s)

end VG.Proof.Gcm.AArch64.Stitch

/-! Construct the gather sealing kernel's precondition using the ordinary
AES-GCM caller layout and the table derived in the workspace. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64.Stitch (tblR kpre_of tbl_ctx tbl_st pre sFrame)
open VG.Impl.AesGcm.AArch64.DirectGather (tableFromKey)
open VG.Impl.Gcm.AArch64.Stitch (setup byRounds encToLoop finish sealCall)
open VG.Spec.Gcm (Block blockAt blocksAt)

structure BatchIn (Wn : Nat) (Ctx St W SP D O : Addr) (R n : Nat) (s : State) : Prop where
  env : Env Wn Ctx St W SP s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  x23 : s.gpr .x23 = D
  x24 : s.gpr .x24 = BitVec.ofNat 64 n
  x26 : s.gpr .x26 = O
  src : DataOk Wn St W s D n
  dst : DataW Wn Ctx St W s O n
  apart : (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩

/-- The kernel uses x15 for input, x23 for output, and x26 for the available length. -/
structure BatchArgs (Wn : Nat) (Ctx St W SP D O : Addr) (R n : Nat) (s : State) : Prop where
  env : Env Wn Ctx St W SP s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  x15 : s.gpr .x15 = D
  x23 : s.gpr .x23 = O
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  src : DataOk Wn St W s D n
  dst : DataW Wn Ctx St W s O n
  apart : (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩

theorem BatchArgs.sealPre {Wn R n : Nat} {Ctx St W SP D O : Addr} {s : State}
    (h : BatchArgs Wn Ctx St W SP D O R n s) (L : Lay Wn Ctx St W) (hn : 128 ≤ n)
    (tok : TblOk s.mem W (blockAt s.mem (Ctx + BitVec.ofNat 64 240))) : SealToPre s := by
  have hpre := kpre_of («to» := false) L h.env h.x22 h.rounds h.x23 h.x26 h.dst.ok h.dst
    (show O = O from rfl) hn tok h.env.perm.hWn
  have hnb : nb s = n / 128 := by simp only [nb, h.x26, toNat_ofNat_of_lt h.src.lt]
  have hpn := Nat.mul_div_le n 128
  refine ⟨hpre.toKPre, ?_, ?_, ?_⟩
  · rw [h.x15, hnb]
    exact covers_prefix h.src.rd hpn _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  · simp only [dR, dp, hnb, h.x15, h.x23]
    exact Or.inr ((h.apart.sub_left (Region.sub_prefix hpn)).sub_right (Region.sub_prefix hpn))
  · rw [h.x15, hnb]; have := h.src.wrap; omega

/-- The complete eight-block kernel and its table, with the original
source, key, and counter in its postcondition. -/
structure BatchMid (Ctx St W D O : Addr) (R n : Nat) (s t : State) : Prop where
  data : blocksAt t.mem O (8 * (n / 128)) = Spec.Gcm.ctr32 (ciphOf s.mem Ctx R)
    (blockAt s.mem (St + BitVec.ofNat 64 48)) (blocksAt s.mem D (8 * (n / 128)))
  ctr : blockAt t.mem (St + BitVec.ofNat 64 48) =
    Nat.repeat Spec.Gcm.inc32 (8 * (n / 128)) (blockAt s.mem (St + BitVec.ofNat 64 48))
  y : blockAt t.mem (St + BitVec.ofNat 64 16) = Spec.Gcm.ghashFrom (Spec.Gcm.ctxH s.mem Ctx)
    (blockAt s.mem (St + BitVec.ofNat 64 16)) (blocksAt t.mem O (8 * (n / 128)))
  src : t.gpr .x15 = D + BitVec.ofNat 64 (pre n)
  dst : t.gpr .x9 = O + BitVec.ofNat 64 (pre n)
  frame : Frame (sFrame St W O n) s.mem t.mem
  gpr : ∀ r, r ≠ .x0 → r ≠ .x5 → r ∉ kRegsT true → (hl : r ∉ linkRegs := by decide) → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem batchTableSeal_ok {Wn R n : Nat} {Ctx St W SP D O : Addr} {s : State}
    (h : BatchArgs Wn Ctx St W SP D O R n s) (L : Lay Wn Ctx St W) (hn : 128 ≤ n) (gh : GatherLaws) :
    WP isa (.seq (.block tableFromKey) sealCall) s
      (BatchMid Ctx St W D O R n s) := by
  rw [WP.seq_iff]
  have hW := h.env.perm.hWn
  refine WP.mono (gh.table (by rw [h.env.x21]; exact h.env.perm.ctxR (by decide))
    (by rw [h.env.x19]; exact h.env.perm.wWn (by omega))) fun u q => ?_
  have keep (r : Reg) (hr : r ∈ [Reg.x19, .x20, .x21]) : u.gpr r = s.gpr r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact q.gpr _ (by decide) (by decide)
  have hu : BatchArgs Wn Ctx St W SP D O R n u :=
    ⟨h.env.keep keep q.sp q.rd q.wr, h.rounds, (q.gpr _ (by decide) (by decide)).trans h.x22,
      (q.gpr _ (by decide) (by decide)).trans h.x15, (q.gpr _ (by decide) (by decide)).trans h.x23,
      (q.gpr _ (by decide) (by decide)).trans h.x26, h.src.of_eq q.rd q.wr, h.dst.of_eq q.rd q.wr, h.apart⟩
  have F : Frame [tblR W] s.mem u.mem := h.env.x19 ▸ q.frame
  have H : blockAt u.mem (Ctx + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx :=
    blockAt_frame F fun r hr => (tbl_ctx L r hr).sub_left (Lay.ctxSub (by decide))
  have hp := hu.sealPre L hn (by rw [H]; simpa only [h.env.x19, h.env.x21] using q.tbl)
  refine WP.mono (sealCall_ok hp gh.hash) fun t z => ?_
  have en : nb u = n / 128 := by simp only [nb, hu.x26, toNat_ofNat_of_lt h.src.lt]
  have eR : rounds u = R := by simp only [rounds, hu.x22, toNat_rounds hu.rounds]
  have ekey : ciph u = ciphOf s.mem Ctx R := by
    unfold ciph ksch kc ciphOf
    rw [eR, hu.env.x21, bytesAt_frame F (fun r hr => (tbl_ctx L r hr).sub_left
      (Region.sub_prefix (by have := h.rounds; omega))) (by have := h.rounds; omega)]
  have ectr : icb u = blockAt s.mem (St + BitVec.ofNat 64 48) := by
    unfold icb stp; rw [hu.env.x20, blockAt_frame F (tbl_st L (by decide))]
  have ey : y₀ u = blockAt s.mem (St + BitVec.ofNat 64 16) := by
    unfold y₀ stp; rw [hu.env.x20, blockAt_frame F (tbl_st L (by decide))]
  have eh : hk u = Spec.Gcm.ctxH s.mem Ctx := by simpa only [hk, kc, hu.env.x21] using H
  have pfx : 16 * (8 * (n / 128)) ≤ n := by have := Nat.mul_div_le n 128; omega
  have esrc : blocksAt u.mem D (8 * (n / 128)) = blocksAt s.mem D (8 * (n / 128)) :=
    blocksAt_frame F (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.src.w.sub_left (Region.sub_prefix pfx)).sub_right (Lay.wSub (by omega)))
      (by have := h.src.lt; omega)
  refine ⟨by simpa only [en, dp, hu.x23, hu.x15, ekey, ectr, esrc] using z.data,
    by simpa only [en, stp, hu.env.x20, ectr] using z.ctr,
    by simpa only [en, stp, hu.env.x20, dp, hu.x23, eh, ey] using z.y,
    by simpa only [pre, en, hu.x15] using z.src, by simpa only [pre, en, dp, hu.x23] using z.dst,
    ?_, fun r h0 h5 hr hl => (z.gpr r (by simpa only [List.mem_append, not_or] using And.intro hr hl)).trans (q.gpr r h0 h5),
    z.sp.trans q.sp, z.rd.trans q.rd,
    z.wr.trans q.wr⟩
  have f := z.frame
  simp only [yR, cR, dR, dp, stp, hu.env.x20, hu.x23, en] at f
  exact (F.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst r; simp)).trans
    (f.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp)

end VG.Proof.Gcm.AArch64.Stitch

/-! Gather's register shuffles and ciphertext hash cursor around the
interleaved kernel. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64.Stitch (pre sFrame)
open VG.Impl.AesGcm.AArch64 (mov imm)
open VG.Impl.AesGcm.AArch64.DirectGather (tableFromKey hashO)
open VG.Impl.Gcm.AArch64.Stitch (setup byRounds encToLoop finish sealCall)
open VG.Spec.Gcm (blockAt blocksAt)

theorem batchArgs_ok {Wn R n : Nat} {Ctx St W SP D O : Addr} {s : State}
    (h : BatchIn Wn Ctx St W SP D O R n s) :
    WP isa (.block [mov .x15 .x23, mov .x23 .x26, mov .x26 .x24]) s fun u =>
      BatchArgs Wn Ctx St W SP D O R n u ∧ Regs [.x15, .x23, .x26] s u := by
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine And.symm ?_
  suffices g : Regs [.x15, .x23, .x26] s _ by
    refine ⟨g, ?_⟩
    refine ⟨h.env.keep (fun r hr => g.others r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) g.sp g.rd g.wr, h.rounds,
      (g.others _ (by decide)).trans h.x22, ?_, ?_, ?_, h.src.of_eq g.rd g.wr, h.dst.of_eq g.rd g.wr, h.apart⟩
    · simp [gpr_write, h.x23]
    · simp [gpr_write, h.x26]
    · simp [gpr_write, h.x24]
  exact ⟨by others_tac, rfl, rfl, rfl, rfl⟩

theorem and127 (x : BitVec 64) : x &&& BitVec.ofNat 64 127 = BitVec.ofNat 64 (x.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 127) (by decide),
    show (127 : Nat) = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

abbrev cursorCode : List Instr := [mov .x26 .x9, mov .x23 .x15, imm .x10 127,
  .logic .and .x .x24 .x24 .x10, .str .x .x26 .x19 hashO]

structure CursorPost (s t : State) : Prop where
  src : t.gpr .x23 = s.gpr .x15
  dst : t.gpr .x26 = s.gpr .x9
  rest : t.gpr .x24 = BitVec.ofNat 64 ((s.gpr .x24).toNat % 128)
  mem : t.mem = s.mem.writeW (s.gpr .x19 + BitVec.ofNat 64 hashO) (s.gpr .x9)
  gpr : ∀ r, r ∉ [Reg.x26, .x23, .x10, .x24] → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem cursor_ok {s : State} (hw : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 hashO) 8) :
    WP isa (.block cursorCode) s (CursorPost s) := by
  change InRegions s.wr (s.gpr .x19 + 352#64) 8 at hw
  refine WP.of_runBlock ⟨_, by arun [cursorCode, hashO, hw], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_write]
  · simp [gpr_write]
  · simpa [gpr_write] using and127 (s.gpr .x24)
  · simp [Mem.writeW, hashO]
  · others_tac

abbrev batchCode : Prog isa :=
  .seq (.block ([mov .x15 .x23, mov .x23 .x26, mov .x26 .x24] ++ tableFromKey))
    (.seq VG.Impl.Gcm.AArch64.Stitch.sealCall (.block cursorCode))

structure BatchOut (Ctx St W D O : Addr) (R n : Nat) (s t : State) : Prop where
  data : blocksAt t.mem O (8 * (n / 128)) = Spec.Gcm.ctr32 (ciphOf s.mem Ctx R)
    (blockAt s.mem (St + BitVec.ofNat 64 48)) (blocksAt s.mem D (8 * (n / 128)))
  ctr : blockAt t.mem (St + BitVec.ofNat 64 48) =
    Nat.repeat Spec.Gcm.inc32 (8 * (n / 128)) (blockAt s.mem (St + BitVec.ofNat 64 48))
  y : blockAt t.mem (St + BitVec.ofNat 64 16) = Spec.Gcm.ghashFrom (Spec.Gcm.ctxH s.mem Ctx)
    (blockAt s.mem (St + BitVec.ofNat 64 16)) (blocksAt t.mem O (8 * (n / 128)))
  src : t.gpr .x23 = D + BitVec.ofNat 64 (pre n)
  dst : t.gpr .x26 = O + BitVec.ofNat 64 (pre n)
  rest : t.gpr .x24 = BitVec.ofNat 64 (n % 128)
  hashPtr : t.mem.readW (W + BitVec.ofNat 64 hashO) 64 = O + BitVec.ofNat 64 (pre n)
  frame : Frame (⟨W + BitVec.ofNat 64 hashO, 8⟩ :: sFrame St W O n) s.mem t.mem
  saved : ∀ r ∈ preserved, r ≠ .x23 → r ≠ .x24 → r ≠ .x26 → r ≠ .x30 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- One or more complete batches, after pending ciphertext has been hashed.
The tail of the fragment remains in the caller's cursor registers. -/
theorem batchCode_ok {Wn R n : Nat} {Ctx St W SP D O : Addr} {s : State}
    (h : BatchIn Wn Ctx St W SP D O R n s) (L : Lay Wn Ctx St W) (hn : 128 ≤ n) (gh : GatherLaws) :
    WP isa batchCode s (BatchOut Ctx St W D O R n s) := by
  rw [batchCode, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (batchArgs_ok h) fun u ⟨ha, a⟩ => ?_
  have continuation := fun t (z : BatchMid Ctx St W D O R n u t) => show
      WP isa (.block cursorCode) t (BatchOut Ctx St W D O R n s) from by
    have hw : t.gpr .x19 = W := (z.gpr _ (by decide) (by decide) (by decide)).trans ha.env.x19
    have wr := z.wr.trans a.wr
    have writable := h.env.perm.wWn (d := hashO) (n := 8) (by have := L.hWn; unfold hashO; omega)
    refine WP.mono (cursor_ok (by rw [wr, hw]; exact writable)) fun v c => ?_
    have F : Frame [⟨W + BitVec.ofNat 64 hashO, 8⟩] t.mem v.mem := by
      rw [c.mem, hw]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hyc (k : Nat) (hk : k + 16 ≤ 80) : ∀ r ∈ [⟨W + BitVec.ofNat 64 hashO, 8⟩],
        (⟨St + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact L.st_w hk (by unfold hashO; decide)
    have pfx : 16 * (8 * (n / 128)) ≤ n := by have := Nat.mul_div_le n 128; omega
    have esrc : blocksAt v.mem O (8 * (n / 128)) = blocksAt t.mem O (8 * (n / 128)) :=
      blocksAt_frame F (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.dst.ok.w.sub_left (Region.sub_prefix pfx)).sub_right (Lay.wSub (by have := L.hWn; unfold hashO; omega)))
        (by have := h.src.lt; omega)
    refine ⟨by rw [esrc, z.data, a.mem],
      by rw [blockAt_frame F (hyc 48 (by decide)), z.ctr, a.mem],
      by rw [blockAt_frame F (hyc 16 (by decide)), z.y, a.mem, esrc],
      c.src.trans z.src, c.dst.trans z.dst, ?_, ?_, ?_, ?_, c.sp.trans (z.sp.trans a.sp),
      c.rd.trans (z.rd.trans a.rd), c.wr.trans wr⟩
    · rw [c.rest, z.gpr _ (by decide) (by decide) (by decide), a.others _ (by decide), h.x24,
        toNat_ofNat_of_lt h.src.lt]
    · rw [c.mem, hw, Mem.readW_writeW_self64, z.dst]
    · rw [← a.mem]
      exact (z.frame.mono (fun r hr => List.mem_cons_of_mem _ hr)).trans
        (F.mono (fun r hr => by simp only [List.mem_singleton] at hr; exact List.mem_cons.mpr (.inl hr)))
    · intro r hr h23 h24 h26 h30
      have h5 : r ≠ .x5 := fun e => by subst r; contradiction
      have h0 : r ≠ .x0 := fun e => by subst r; contradiction
      have hsmall (j : Reg) (hj : j ∉ preserved) : r ≠ j := fun e => hj (e ▸ hr)
      rw [c.gpr, z.gpr r h0 h5 _ (preserved_not_link r hr h30), a.others]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hsmall _ (by decide), h23, h26⟩
      · simp only [kRegsT, Bool.cond_true, kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hsmall _ (by decide), hsmall _ (by decide), hsmall _ (by decide), hsmall _ (by decide),
          hsmall _ (by decide), hsmall _ (by decide), hsmall _ (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h26, h23, hsmall _ (by decide), h24⟩
  exact WP.mono (WP.seq_iff.mp (WP.mono (batchTableSeal_ok ha L hn gh) continuation))
    (fun _ next => WP.seq next)

end VG.Proof.Gcm.AArch64.Stitch

/-! Hash complete ciphertext blocks left between the previous interleaved
batch and the current block-aligned destination. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64 (ghArgs)
open VG.Impl.AesGcm.AArch64.DirectGather (hashPending hashO)
open VG.Spec.Gcm (blockAt blocksAt)

theorem pendingCursor {Wn n : Nat} {Ctx St W SP P : Addr} {s : State}
    (he : Env Wn Ctx St W SP s) (slot : s.mem.readW (W + BitVec.ofNat 64 hashO) 64 = P)
    (stop : s.gpr .x26 = P + BitVec.ofNat 64 (16*n)) (data : DataOk Wn St W s P (16*n)) :
    ∃ u, runBlock isa [.ldr .x .x2 .x19 hashO, .sub .x .x3 .x26 .x2, .lsr .x .x3 .x3 4] s = some u ∧
      u.gpr .x2 = P ∧ u.gpr .x3 = BitVec.ofNat 64 n ∧ Regs [.x2, .x3] s u := by
  have rd := he.perm.wRn (d := hashO) (n := 8) (by have := he.perm.hWn; unfold hashO; omega)
  change InRegions (s.rd ++ s.wr) (W + 352#64) 8 at rd
  have load : s.mem.read (W + 352#64) 8 = P := slot
  refine ⟨_, by arun [he.x19, rd, hashO], ?_⟩
  refine ⟨?_, ?_, by others_tac, rfl, rfl, rfl, rfl⟩
  · simpa [gpr_write] using load
  · simp only [gpr_write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
      load, stop, BitVec.add_comm P, BitVec.add_sub_cancel]
    rw [lsr_ofNat _ _ data.lt, show 16 * n / 2 ^ 4 = n by omega]

theorem pendingGhArgs {Wn : Nat} {Ctx St W SP : Addr} {u : State} (env : Env Wn Ctx St W SP u) :
    ∃ t, runBlock isa (ghArgs 16) u = some t ∧
      t.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧ t.gpr .x1 = St + BitVec.ofNat 64 16 ∧
      t.gpr .x4 = W + BitVec.ofNat 64 512 ∧ Regs [.x0, .x1, .x4] u t := by
    refine ⟨_, by arun [ghArgs], ?_⟩
    refine ⟨?_, ?_, ?_, by others_tac, rfl, rfl, rfl, rfl⟩ <;>
      simp [gpr_write, env.x19, env.x20, env.x21]

theorem pendingGhCall {Wn n : Nat} {Ctx St W SP P : Addr} {u t : State}
    (L : Lay Wn Ctx St W) (env : Env Wn Ctx St W SP u) (data : DataOk Wn St W u P (16*n))
    (e2 : u.gpr .x2 = P) (e3 : u.gpr .x3 = BitVec.ofNat 64 n) (e0 : t.gpr .x0 = Ctx+240#64)
    (e1 : t.gpr .x1 = St+16#64) (e4 : t.gpr .x4 = W+512#64) (rt : Regs [.x0,.x1,.x4] u t) :
    GhCall t (Ctx+240#64) (St+16#64) P (W+512#64) n := by
  have et := env.keep (fun j hj => rt.others j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> decide)) rt.sp rt.rd rt.wr
  exact ghCall_of L (.inr rfl) et e0 e1 ((rt.others _ (by decide)).trans e2)
      ((rt.others _ (by decide)).trans e3) e4 data.lt (data.st.symm.sub_left (Lay.stSub (by decide)))
      (data.w.sub_right (Lay.wSub (by have := L.hWn; omega))) (by rw [rt.rd, rt.wr]; exact data.rd)

theorem hashPending_ok (v : GcmImpl) {Wn n : Nat} {Ctx St W SP P : Addr} {s : State}
    (L : Lay Wn Ctx St W) (he : Env Wn Ctx St W SP s)
    (slot : s.mem.readW (W + BitVec.ofNat 64 hashO) 64 = P)
    (stop : s.gpr .x26 = P + BitVec.ofNat 64 (16 * n)) (data : DataOk Wn St W s P (16 * n)) :
    WP isa (hashPending v.callees) s (GhPost s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 16)
      P (W + BitVec.ofNat 64 512) n) := by
  obtain ⟨u, run, e2, e3, r⟩ := pendingCursor he slot stop data
  have env := he.keep (fun j hj => r.others j (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide)) r.sp r.rd r.wr
  refine WP.seq (WP.of_runBlock ⟨u, run, ?_⟩)
  refine WP.ite _ (Proof.Aes.AArch64.Aese.eval_zero e3 (by have := data.lt; omega)) (fun hz => ?_) (fun _ => ?_)
  · obtain rfl : n = 0 := by simpa using hz
    refine WP.block_nil ⟨r.rd, r.wr, r.sp, fun j hj _ => r.others j ?_, r.mem ▸ Frame.refl _ _, ?_⟩
    · intro hj'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl | rfl <;> contradiction
    · rw [r.mem]; rfl
  · obtain ⟨t, run', e0, e1, e4, rt⟩ := pendingGhArgs env
    refine WP.seq (WP.of_runBlock ⟨t, run', ?_⟩)
    have hcall := pendingGhCall L env (data.of_eq r.rd r.wr) e2 e3 e0 e1 e4 rt
    refine WP.mono (gh_call v.gh hcall) fun z q => ⟨q.rd.trans (rt.rd.trans r.rd), q.wr.trans (rt.wr.trans r.wr),
      q.sp.trans (rt.sp.trans r.sp), fun j hj h30 => ?_, ?_, ?_⟩
    · rw [q.saved j hj h30, rt.others, r.others] <;>
        intro hj' <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hj' <;>
        repeat' first | contradiction | rcases hj' with rfl | hj'
    · simpa only [rt.mem, r.mem] using q.frame
    · simpa only [rt.mem, r.mem] using q.out

end VG.Proof.Gcm.AArch64.Stitch

/-! The actual length guard, pending GHASH, and interleaved batches of one
gather descriptor. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.DirectGather (batches hashO)
open VG.Spec.Gcm (blockAt blocksAt)

abbrev batchTest (n : Nat) : BitVec 64 :=
  (BitVec.ofNat 64 n + BitVec.ofNat 64 (1024 - Impl.AesGcm.AArch64.Stitch.minLen)) >>> 10

theorem batchTest_len {n : Nat} (h : batchTest n ≠ 0) : 128 ≤ n := by
  by_cases hn : 128 ≤ n
  · exact hn
  exfalso
  apply h
  unfold batchTest Impl.AesGcm.AArch64.Stitch.minLen
  rw [ofNat_add_ofNat, lsr_ofNat _ _ (by omega)]
  have : (n + (1024 - 768)) / 2 ^ 10 = 0 := by omega
  rw [this]; rfl

structure PendingIn (Wn : Nat) (St W P O : Addr) (k : Nat) (s : State) : Prop where
  slot : s.mem.readW (W + BitVec.ofNat 64 hashO) 64 = P
  stop : O = P + BitVec.ofNat 64 (16 * k)
  data : DataOk Wn St W s P (16 * k)

/-- Either the size guard skipped this fragment, or its pending ciphertext was
hashed from the original accumulator before the complete batches ran. -/
def BatchesPost (Ctx St W D O P : Addr) (R n k : Nat) (s t : State) : Prop :=
  (batchTest n = 0 ∧ Regs [.x9] s t) ∨
  (batchTest n ≠ 0 ∧ ∃ u, GhPost s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 16) P
    (W + BitVec.ofNat 64 512) k u ∧ BatchOut Ctx St W D O R n u t)

theorem batchGuard {Wn R n : Nat} {Ctx St W SP D O : Addr} {s : State}
    (h : BatchIn Wn Ctx St W SP D O R n s) :
    ∃ a, runBlock isa [.addImm .x .x9 .x24 (1024 - Impl.AesGcm.AArch64.Stitch.minLen),
      .lsr .x .x9 .x9 10] s = some a ∧ a.gpr .x9 = batchTest n ∧ Regs [.x9] s a := by
  refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.minLen], ?_⟩
  exact ⟨by simp [batchTest, gpr_write, h.x24, Impl.AesGcm.AArch64.Stitch.minLen],
    by others_tac, rfl, rfl, rfl, rfl⟩

theorem batches_ok (v : GcmImpl) {Wn R n k : Nat} {Ctx St W SP D O P : Addr} {s : State}
    (h : BatchIn Wn Ctx St W SP D O R n s) (L : Lay Wn Ctx St W) (gh : GatherLaws)
    (pending : batchTest n ≠ 0 → PendingIn Wn St W P O k s) :
    WP isa (batches v.callees) s (BatchesPost Ctx St W D O P R n k s) := by
  obtain ⟨a, run, test, r⟩ := batchGuard h
  have keep (j : Reg) (hj : j ∈ preserved) : a.gpr j = s.gpr j := r.others j (by
    simp only [List.mem_singleton]; intro e; subst j; contradiction)
  have ea := h.env.of_saved (fun j hj _ => keep j hj) r.sp r.rd r.wr
  refine WP.seq (WP.of_runBlock ⟨a, run, ?_⟩)
  have eval : AArch64.eval (.zero .x .x9) a = some (decide (batchTest n = 0)) := by
    change some (a.gpr .x9 == (0 : BitVec 64)) = _
    rw [test]
    by_cases hz : batchTest n = 0
    · rw [hz]; rfl
    · rw [beq_eq_false_iff_ne.mpr hz, decide_eq_false hz]
  refine WP.ite _ eval (fun z => ?_) (fun nz => ?_)
  · exact WP.block_nil (.inl ⟨by simpa using z, r⟩)
  · have hn : batchTest n ≠ 0 := by simpa using nz
    have hp := pending hn
    refine WP.seq (WP.mono (hashPending_ok v L ea (r.mem ▸ hp.slot)
      ((keep _ (by decide)).trans (h.x26.trans hp.stop)) (hp.data.of_eq r.rd r.wr)) fun u p => ?_)
    have saved (j : Reg) (hj : j ∈ preserved) (h30 : j ≠ .x30) :
        u.gpr j = s.gpr j := (p.saved j hj h30).trans (keep j hj)
    have rd := p.rd.trans r.rd
    have wr := p.wr.trans r.wr
    have g : GhPost s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 16) P
        (W + BitVec.ofNat 64 512) k u :=
      ⟨rd, wr, p.sp.trans r.sp, saved, r.mem ▸ p.frame, by simpa only [r.mem] using p.out⟩
    have hu : BatchIn Wn Ctx St W SP D O R n u :=
      ⟨h.env.of_saved saved g.sp rd wr, h.rounds, (saved _ (by decide) (by decide)).trans h.x22,
        (saved _ (by decide) (by decide)).trans h.x23, (saved _ (by decide) (by decide)).trans h.x24,
        (saved _ (by decide) (by decide)).trans h.x26, h.src.of_eq rd wr, h.dst.of_eq rd wr, h.apart⟩
    exact WP.mono (batchCode_ok hu L (batchTest_len hn) gh) fun t out => .inr ⟨hn, u, g, out⟩

end VG.Proof.Gcm.AArch64.Stitch
