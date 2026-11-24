module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.TagMask
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Tag
meta import VerifiedGarbage.Impl.Gcm.AArch64.Stitch

/-! Encrypt a live counter into the final partial block’s keystream buffer. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Tag
open VG VG.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.Impl.AesGcm.AArch64.Contiguous.Tag (counter)
open VG.Proof.Gcm.AArch64.Stitch (sch)
open VG.Impl.Gcm.AArch64.Stitch (byRounds)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_taint)

structure CounterOut (nr : Nat) (s t : State) : Prop where
  bytes : ∃ v : BitVec 128, st v = Spec.Aes.cipher nr (sch nr s) (st (s.mem.readW (s.gpr .x20+48#64) 128)) ∧
    t.mem = s.mem.write (s.gpr .x20+64#64) 16 v
  reg : ∀ r, r ≠ .x13 → r ≠ .x14 → t.gpr r = s.gpr r
  vec : ∀ r, r ∉ changed → t.v r = s.v r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem counter_ok {nr : Nat} (rounds : nr = 10 ∨ nr = 12 ∨ nr = 14) (s : State)
    (roundReg : s.gpr .x22 = BitVec.ofNat 64 nr) (key : keyReadable nr s)
    (ctrRead : InRegions (s.rd++s.wr) (s.gpr .x20+48#64) 16)
    (outWrite : InRegions s.wr (s.gpr .x20+64#64) 16) :
    WP isa (byRounds counter) s (CounterOut nr s) := by
  apply Stitch.byRoundsG_ok rounds roundReg
  intro u ug um uv usp ur uw
  have stp := ug .x20 (by decide) (by decide)
  have kp := ug .x21 (by decide) (by decide)
  have keys : keyReadable nr u := by simpa only [keyReadable,ur,uw,kp] using key
  have rd : InRegions (u.rd++u.wr) (u.gpr .x20+48#64) 16 := by rwa [ur,uw,stp]
  unfold counter
  rw [WP.block_append_iff]
  refine (maskAt_ok (offset := 48) (by decide) (by omega_using [rounds]) u keys rd).mono ?_
  intro b ⟨val,frame⟩
  have wr : InRegions b.wr (b.gpr .x20+64#64) 16 := by rwa [frame.wr,uw,frame.gpr,stp]
  refine WP.block_cons_iff.mpr ⟨_,exec_strq (s := b) (t := .v28) (n := .x20) (off := 64) (by decide) wr,WP.block_nil ?_⟩
  refine ⟨⟨b.v .v28,?_,?_⟩,fun r h j => (congrFun frame.gpr r).trans (ug r h j),
    fun r h => (frame.v r h).trans (congrFun uv r),frame.sp.trans usp,frame.rd.trans ur,frame.wr.trans uw⟩
  · have ks : Proof.Gcm.AArch64.Stitch.sch nr u = Proof.Gcm.AArch64.Stitch.sch nr s := by
      unfold Proof.Gcm.AArch64.Stitch.sch Proof.Gcm.AArch64.Stitch.kp
      rw [um,kp]
    rw [ks,um,stp] at val
    exact val
  · change b.mem.write (b.gpr .x20 + 64#64) 16 _ = _
    rw [frame.mem,um,frame.gpr,stp]

private theorem cipherStore (m : Mem) (dst src : Addr) (v : BitVec 128) (nr : Nat) (keys : List Byte)
    (enc : st v = Spec.Aes.cipher nr keys (st (m.readW src 128))) :
    Spec.Gcm.blockAt (m.write dst 16 v) dst = Spec.Gcm.aesWith nr keys (Spec.Gcm.blockAt m src) := by
  apply Proof.Aes.block_ext
  intro i hi
  have stored : (m.write dst 16 v).readW dst 128 = v := Proof.Gcm.AArch64.Pmull.read_write16 m dst v
  rw [Proof.Aes.toBytes_blockAt _ _ hi,← Proof.Aes.Vector.vbyte_readW (m.write dst 16 v) dst hi,
    stored,← Proof.Aes.Vector.getD_st _ hi,enc,
    Spec.Gcm.aesWith,inputState,Proof.Aes.toBytes_ofBytes (by simp) hi,Proof.Aes.getD_eq _ hi,
    List.getD_eq_getElem?_getD,Vector.getElem?_toList,Vector.getElem?_eq_getElem hi,Option.getD_some]

theorem counterAt_ok {wn nr : Nat} {Ctx St W SP : Addr} {s : State} (e : Env wn Ctx St W SP s)
    (rounds : nr=10 ∨ nr=12 ∨ nr=14) (roundReg : s.gpr .x22=BitVec.ofNat 64 nr) :
    WP isa (byRounds counter) s fun t => CounterOut nr s t ∧ Frame [⟨St+64#64,16⟩] s.mem t.mem ∧
      Spec.Gcm.blockAt t.mem (St+64#64) = ciphOf s.mem Ctx nr (Spec.Gcm.blockAt s.mem (St+48#64)) := by
  have keys : keyReadable nr s := by
    intro j hj
    rw [e.x21]
    exact e.perm.ctxR (by omega_using [rounds,hj])
  refine (counter_ok rounds s roundReg keys (by rw [e.x20]; exact e.perm.stR (by decide))
    (by rw [e.x20]; exact e.perm.stW (by decide))).mono ?_
  intro t h
  obtain ⟨v,cipher,mem⟩ := h.bytes
  rw [e.x20] at cipher mem
  refine ⟨h,mem ▸ (Frame.refl _ _).write (r := ⟨St+64#64,16⟩) (by simp) v (Region.contains_self _ _),?_⟩
  rw [mem]
  simpa only [Proof.Gcm.AArch64.Stitch.sch,Proof.Gcm.AArch64.Stitch.kp,e.x21] using
    cipherStore s.mem (St+64#64) (St+48#64) v nr _ cipher

theorem counter_rel {s t : State} (sp : s.sp=t.sp)
    (stp : s.gpr .x20=t.gpr .x20) (key : s.gpr .x21=t.gpr .x21) (rounds : s.gpr .x22=t.gpr .x22) :
    RelCT isa (Eq2 s t) (byRounds counter) TT := by
  apply rel_taint [.x20,.x21,.x22] sp (by agree_tac [stp,key,rounds])
  exact ⟨_,by taint_decide⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Tag
