module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.PreparedEntry
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericStream
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Pre
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesGcm.AArch64.CalleePw
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The prepared AES and AES/SHA3 records use the same two-pointer CTR
remainder. The SHA3 record skips the groups already encrypted and hashed. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous
open DirectGather.Generic (Encrypted aligned_ok)
open VG.Proof.Gcm (Ctr)
open VG.Spec.Gcm (Block)

abbrev done (fused : Bool) (n : Nat) := if fused then Stitch.pre n else 0
abbrev tailRegs : List Reg := [.x9,.x23,.x24,.x25,.x26,.x27]

theorem done_le (fused : Bool) (n : Nat) : done fused n ≤ n := by
  cases fused
  · exact Nat.zero_le _
  · exact Nat.mul_div_le n 128

theorem done_mod (fused : Bool) (n : Nat) : done fused n % 16 = 0 := by
  cases fused
  · rfl
  · change (128*(n/128))%16 = 0; omega

structure TailArgs (fused : Bool) (n : Nat) (D O : Addr) (s t : State) : Prop extends Regs tailRegs s t where
  src : t.gpr .x23 = word D (done fused n)
  dst : t.gpr .x26 = word O (done fused n)
  start : t.gpr .x27 = word O (done fused n)
  len : t.gpr .x24 = BitVec.ofNat 64 (n-done fused n)
  cursor : t.gpr .x25 = 0

theorem remainder_ok (fused : Bool) {s : State} {n : Nat} {D O W : Addr}
    (src : s.gpr .x23 = D) (len : s.gpr .x26 = BitVec.ofNat 64 n) (hn : n < 2^64)
    (key : s.gpr .x19 = W) (rd : InRegions (s.rd++s.wr) (word W dstO) 8)
    (out : s.mem.readW (word W dstO) 64 = O) :
    WP isa (.block (remainder fused)) s (TailArgs fused n D O s) := by
  have dst : s.mem.read (W+320#64) 8 = O := out
  have read : InRegions (s.rd++s.wr) (W+320#64) 8 := rd
  have bits := Stitch.whole_eq len hn
  have hp : Stitch.pre n ≤ n := Nat.mul_div_le n 128
  cases fused
  · refine WP.of_runBlock ⟨_,by arun [remainder,dstO,key,read,dst],?_⟩
    refine ⟨⟨by others_tac, rfl,rfl,rfl,rfl⟩,?_,?_,?_,?_,?_⟩ <;> simp [gpr_write,src,len,word,done]
  · refine WP.of_runBlock ⟨_,by arun [remainder,Impl.AesGcm.AArch64.Stitch.whole,dstO,key,read,dst],?_⟩
    refine ⟨⟨by others_tac, rfl,rfl,rfl,rfl⟩,?_,?_,?_,?_,?_⟩
    · simp [gpr_write,src,bits,word,done]
    · simp [gpr_write,bits,word,done]
    · simp [gpr_write,bits,word,done]
    · rw [len] at bits
      simp [gpr_write,len,done,bits,Offset.ofNat_sub_ofNat hp]
    · simp [gpr_write]

theorem TailArgs.crIn {wn n R : Nat} {fused : Bool} {Ctx St W SP D O : Addr} {s r : State}
    (p : TailArgs fused n D O s r) (en : Env wn Ctx St W SP s)
    (rr : VG.Proof.AesGcm.AArch64.rounds (s.gpr .x22)) (nr : (s.gpr .x22).toNat = R)
    (sd : DataOk wn St W s D n) (od : DataW wn Ctx St W s O n) (mode : BufferLayout D O n) :
    CrInG wn true Ctx St W SP r.gpr R (done fused n) (word D (done fused n)) (word O (done fused n)) (n-done fused n) r := by
  have h := done_le fused n
  refine ⟨en.of_regs p.toRegs,fun _ _ => rfl,?_,?_,p.src,p.len,?_,(sd.drop h).of_eq p.rd p.wr,
    (od.drop h).of_eq p.rd p.wr,mode.sub (by omega),?_⟩
  · rw [← nr]; simpa using p.others .x22 (by decide)
  · rw [← nr]; exact rr
  · rw [done_mod]; exact p.cursor
  · simpa only [BitVec.add_zero] using p.dst

theorem encrypt_remainder {wn : Nat} (v : GcmImpl) (fused : Bool) {s : State} {n R : Nat}
    {D O Ctx St W SP : Addr} {iv : Block} (L : Lay wn Ctx St W) (en : Env wn Ctx St W SP s)
    (src : s.gpr .x23 = D) (len : s.gpr .x26 = BitVec.ofNat 64 n) (rounds : VG.Proof.AesGcm.AArch64.rounds (s.gpr .x22))
    (nr : (s.gpr .x22).toNat = R)
    (sd : DataOk wn St W s D n) (od : DataW wn Ctx St W s O n) (mode : BufferLayout D O n)
    (out : s.mem.readW (word W dstO) 64 = O)
    (ctr : Ctr s.mem (St+48) (St+64) (ciphOf s.mem Ctx R) iv (done fused n))
    (hv : v.ctr.scratch ≤ wn-512) :
    WP isa (.seq (.block (remainder fused)) (Impl.AesGcm.AArch64.DirectGather.aligned v.callees)) s fun t =>
      ∃ r, TailArgs fused n D O s r ∧ Encrypted wn Ctx St W SP r.gpr R iv (done fused n)
        (word D (done fused n)) (word O (done fused n)) (n-done fused n) s.mem t ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  have h := done_le fused n
  obtain bounds := en.perm.hWn
  refine WP.seq ((remainder_ok fused src len sd.lt en.x19 (in_left (rd := s.rd)
    (in_off en.perm.w (by change 320+8 ≤ wn; omega) (by omega))) out).mono ?_)
  intro r p
  have args := p.crIn en rounds nr sd od mode
  have ci := p.mem ▸ ctr
  refine (WP.with_rdwr (aligned_ok L v args (done_mod ..) ci hv)).mono ?_
  intro t ⟨text,rd,wr⟩
  exact ⟨r,p,p.mem ▸ text,rd.trans p.rd,wr.trans p.wr⟩

theorem authArgs_ok (fused : Bool) {s : State} {n : Nat} {O W : Addr} (hn : n < 2^64)
    (start : s.gpr .x27 = word O (done fused n)) (work : s.gpr .x19 = W)
    (read : InRegions (s.rd++s.wr) (word W lenO) 8)
    (length : s.mem.readW (word W lenO) 64 = BitVec.ofNat 64 n) :
    WP isa (.block (authArgs fused)) s fun t =>
      t.gpr .x26 = BitVec.ofNat 64 n ∧ t.gpr .x23 = word O (done fused n) ∧
      t.gpr .x24 = BitVec.ofNat 64 (n-done fused n) ∧ Regs [.x9,.x23,.x24,.x26] s t := by
  have mem : s.mem.read (W+240#64) 8 = BitVec.ofNat 64 n := length
  change InRegions _ (W+240#64) 8 at read
  cases fused
  · refine WP.of_runBlock ⟨_,by arun [authArgs,lenO,work,read,mem],?_⟩
    exact ⟨by simp [gpr_write],by simp [gpr_write,start],by simp [gpr_write,done],⟨by others_tac,rfl,rfl,rfl,rfl⟩⟩
  · have bits : (BitVec.ofNat 64 n >>> 7) <<< 7 = BitVec.ofNat 64 (Stitch.pre n) := by
      rw [Proof.Gcm.AArch64.Stitch.ushr7 hn,Stitch.shl7 (by have := Nat.mul_div_le n 128; omega)]
    refine WP.of_runBlock ⟨_,by arun [authArgs,Impl.AesGcm.AArch64.Stitch.whole,lenO,work,read,mem],?_⟩
    exact ⟨by simp [gpr_write],by simp [gpr_write,start],
      by simp [gpr_write,bits,done,Offset.ofNat_sub_ofNat (Nat.mul_div_le n 128)],⟨by others_tac,rfl,rfl,rfl,rfl⟩⟩

/-- Construct the GHASH call on all unstitched whole blocks of ciphertext. -/
theorem authCallArgs {wn : Nat} (fused : Bool) {s : State} {n : Nat} {Ctx St W SP O : Addr}
    {H : Block} {x : List Byte} (L : Lay wn Ctx St W) (env : Env wn Ctx St W SP s)
    (od : DataOk wn St W s O n) (start : s.gpr .x27 = word O (done fused n))
    (length : s.mem.readW (word W lenO) 64 = BitVec.ofNat 64 n) (hh : Spec.Gcm.blockAt s.mem (word Ctx 240) = H)
    (aligned : x.length % 16 = 0) :
    WP isa (.block (authRemainder fused)) s fun t =>
      ∃ u, Regs [.x9,.x23,.x24,.x26] s u ∧ u.gpr .x26 = BitVec.ofNat 64 n ∧
        Abs3 wn Ctx St W SP u.gpr 16 H x (word O (done fused n)) (n-done fused n) (u.gpr .x25).toNat s.mem 0 t ∧ t.mem = s.mem := by
  have hn := done_le fused n
  rw [authRemainder,WP.block_append_iff]
  refine (authArgs_ok fused od.lt start env.x19 (env.perm.wR (by decide)) length).mono ?_
  intro u ⟨n26,d23,n24,regs⟩
  have m : AbsMid wn Ctx St W SP u.gpr 16 H x (word O (done fused n)) (n-done fused n)
      (u.gpr .x25).toNat s.mem 0 u := by
    refine ⟨env.of_regs regs,fun _ _ => rfl,Nat.zero_le _,by simpa only [BitVec.add_zero] using d23,
      by simpa only [Nat.sub_zero] using n24,by simp,(od.drop hn).of_eq regs.rd regs.wr,
      regs.mem ▸ hh,?_,.inr (by simpa only [Nat.add_zero] using aligned),regs.mem ▸ Frame.refl _ _⟩
    intro ha
    simpa only [regs.mem,Spec.Aes.bytesAt,List.range_zero,List.map_nil,List.append_nil] using ha
  exact (absSeg2_mem L (.inr rfl) m).mono fun t ⟨post,mem⟩ => ⟨u,regs,n26,post,mem.trans regs.mem⟩

theorem authCall {wn : Nat} (v : GcmImpl) (g : GhashWithImpl) (fused : Bool) {s : State} {n : Nat}
    {Ctx St W SP O P : Addr} {H : Block} {x : List Byte} (L : Lay wn Ctx St W) (env : Env wn Ctx St W SP s)
    (od : DataOk wn St W s O n) (start : s.gpr .x27 = word O (done fused n))
    (length : s.mem.readW (word W lenO) 64 = BitVec.ofNat 64 n) (hh : Spec.Gcm.blockAt s.mem (word Ctx 240) = H)
    (aligned : x.length % 16 = 0) (pw : GhWCall s Ctx (word St 16) (word W 512) P)
    (slot : s.mem.readW (word s.sp 16) 64 = P) (read : InRegions (s.rd++s.wr) (word s.sp 16) 8) :
    let k := n-done fused n
    WP isa (.seq (.block (authRemainder fused)) (Impl.AesGcm.AArch64.Fast.pwSel v.callees 16 g.fn)) s fun t =>
      ∃ u, Regs [.x9,.x23,.x24,.x26] s u ∧ u.gpr .x26 = BitVec.ofNat 64 n ∧
        AbsMid wn Ctx St W SP u.gpr 16 H x (word O (done fused n)) k (u.gpr .x25).toNat s.mem (16*(k/16)) t ∧
        k-16*(k/16) < 16 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.seq ((WP.with_rdwr (authCallArgs fused L env od start length hh aligned)).mono ?_)
  intro a ⟨⟨u,r,n26,h,mem⟩,rd,wr⟩
  have sp := h.env.sp.trans env.sp.symm
  have p : GhWCall a Ctx (word St 16) (word W 512) P :=
    ⟨by rw [rd,wr]; exact pw.reads,pw.yp,pw.sp,mem ▸ pw.repr⟩
  refine (WP.with_rdwr (absCall2With_ok L (.inr rfl) h (pwSel_call v g (k := 16) (by decide)
    (by rw [sp,mem]; exact slot) (by rw [sp,rd,wr]; exact read) h.call p))).mono ?_
  intro t ⟨⟨m,lt⟩,tr,tw⟩
  simp only [Nat.zero_add,Nat.sub_zero] at m lt
  exact ⟨u,r,n26,m,lt,tr.trans rd,tw.trans wr⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared
