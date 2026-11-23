module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.DirectGather
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Ctr32
import VerifiedGarbage.Proof.AesGcm.PPC64LE.J0
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Continuing a partially consumed POWER8 counter block across descriptors -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.WriteBytes
open VG.Impl.AesGcm.PPC64LE.DirectGather (head)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block)
open VG.Proof.Gcm (Ctr xorKs)

def headRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r21, .r24, .r25]

theorem head_wp {V : Reg → BitVec 64} {sp S E : Addr} {P n : Nat} {icb : Block} {ciph : Block → Block}
    {s : State} (env : Env V sp s) (hS : s.gpr .r24 = S) (hE : s.gpr .r21 = E)
    (count : s.gpr .r25 = BitVec.ofNat 64 n) (off : s.gpr .r26 = BitVec.ofNat 64 (P % 16))
    (src : DataOk (V .r30) (V .r31) s S n) (dst : DataW (V .r29) (V .r30) (V .r31) s E n)
    (sep : (⟨S,n⟩ : Region).Disjoint ⟨E,n⟩) (hn : n ≠ 0) (hP : P % 16 ≠ 0)
    (ctr : Ctr s.mem (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64) ciph icb P) :
    let k := min (16-P%16) n
    WP isa head s fun t =>
      (t.gpr .r24 = S + BitVec.ofNat 64 k ∧ t.gpr .r21 = E + BitVec.ofNat 64 k ∧
       t.gpr .r25 = BitVec.ofNat 64 (n-k) ∧ Frame [⟨E,k⟩] s.mem t.mem ∧
       Ctr t.mem (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64) ciph icb (P+k) ∧
       bytesAt t.mem E k = xorKs ciph icb P (bytesAt s.mem S k)) ∧ Keep headRegs s t := by
  intro k
  refine WP.keep headRegs ?_ (by decide)
  have hp : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have kPos : 1 ≤ k := by dsimp [k]; omega_using [hn,hp]
  have kLe : k ≤ n := Nat.min_le_right _ _
  have rest : P % 16 + k ≤ 16 := by dsimp [k]; omega_using [hp]
  refine WP.seq (WP.mono (minLen_ok s off count (by omega_using [hp]) src.lt) fun u ⟨h5, regs, hu⟩ => ?_)
  have r30 := (regs .r30 (by decide) (by decide)).trans env.r30
  have r24 := (regs .r24 (by decide) (by decide)).trans hS
  have r21 := (regs .r21 (by decide) (by decide)).trans hE
  have r25 := (regs .r25 (by decide) (by decide)).trans count
  have r26 := (regs .r26 (by decide) (by decide)).trans off
  change u.gpr .r5 = BitVec.ofNat 64 k at h5
  let A := V .r30 + BitVec.ofNat 64 (64 + P % 16)
  have prepare : WP isa (.block [.addi .r3 .r30 64, .add .r3 .r3 .r26, mov .r4 .r24, mov .r7 .r21,
      .add .r21 .r21 .r5, .add .r24 .r24 .r5, .sub .r25 .r25 .r5]) u fun v =>
      v.gpr .r3 = A ∧ v.gpr .r4 = S ∧ v.gpr .r7 = E ∧ v.gpr .r5 = BitVec.ofNat 64 k ∧
      v.gpr .r24 = S + BitVec.ofNat 64 k ∧ v.gpr .r21 = E + BitVec.ofNat 64 k ∧
      v.gpr .r25 = BitVec.ofNat 64 (n-k) ∧ Keeps u v := by
    crun [r30,r25,r26,r24,r21,h5,mov,BitVec.or_self]
    exact ⟨by rw [add_ofNat_assoc], ofNat_sub64 kLe src.lt, ⟨rfl,rfl,rfl,rfl,rfl⟩⟩
  refine WP.seq (WP.mono prepare fun v ⟨v3,v4,v7,v5,v24,v21,v25,hv⟩ => ?_)
  have same := hu.trans hv
  have out := dst.take kLe
  have xp : XorPre true v A S E k := by
    refine ⟨v3,v4,fun _ => v7,v5,kPos,by have := src.lt; omega_using [kLe,this],?_,?_,?_,?_,(fun h => nomatch h),.inr ?_⟩
    · rw [same.rd,same.wr]; exact covers_left (env.perm.stC (by omega_using [rest]))
    · rw [same.rd,same.wr]; exact (src.take kLe).rd
    · rw [same.wr]; exact out.wr
    · exact (out.ok.st.sub_right (Lay.stSub (by omega_using [rest]))).symm
    · exact (sep.sub_left (Region.sub_prefix kLe)).sub_right (Region.sub_prefix kLe)
  refine WP.mono (xorLoopWith_ok true v xp) fun t post => ?_
  have hm := post.mem
  rw [same.mem] at hm
  have hxl := length_xorBytes s.mem S A k
  have fw : Frame [⟨E,k⟩] s.mem t.mem := by rw [hm]; exact writeBytes_frame' _ hxl
  refine ⟨(post.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +revert)).trans v24,
    (post.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +revert)).trans v21,
    (post.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +revert)).trans v25, fw, ?_, ?_⟩
  · apply (ctr.head hP rest).congr
    · apply blockAt_frame fw
      simpa only [List.mem_singleton, forall_eq] using (out.ok.st.sub_right (Lay.stSub (by decide : 48+16≤80))).symm
    · apply blockAt_frame fw
      simpa only [List.mem_singleton, forall_eq] using (out.ok.st.sub_right (Lay.stSub (by decide : 64+16≤80))).symm
  · have outBytes := bytesAt_writeBytes_self s.mem E (xorBytes s.mem S A k) (by rw [hxl]; exact out.ok.lt)
    rw [hxl] at outBytes
    rw [hm,outBytes,xorBytes]
    have correct := Proof.Gcm.ctr_head ctr hP (d := bytesAt s.mem S k) (by rw [length_bytesAt]; exact rest)
    rw [length_bytesAt,add_ofNat_assoc] at correct
    exact correct

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Counter batches writing a POWER8 gather piece to the output -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.Proof.Aes.PPC64LE.Crypto
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block)
open VG.Proof.Gcm (Ctr xorKs)

/-- Widen the batch's permissions to the enclosing gather operation. -/
theorem ctrTo_wp {V : Reg → BitVec 64} {sp S E : Addr} {P nb R : Nat} {icb : Block} {s : State}
    (env : Env V sp s) (h3 : s.gpr .r3 = V .r29) (h4 : s.gpr .r4 = BitVec.ofNat 64 R)
    (h5 : s.gpr .r5 = V .r30 + BitVec.ofNat 64 48) (h6 : s.gpr .r6 = S)
    (h7 : s.gpr .r7 = BitVec.ofNat 64 nb) (h26 : s.gpr .r26 = E-S)
    (src : DataOk (V .r30) (V .r31) s S (16*nb)) (dst : DataW (V .r29) (V .r30) (V .r31) s E (16*nb))
    (sep : (⟨S,16*nb⟩ : Region).Disjoint ⟨E,16*nb⟩) (rounds : R=10 ∨ R=12 ∨ R=14)
    (aligned : P % 16 = 0)
    (ctr : Ctr s.mem (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64)
      (ciphOf s.mem (V .r29) R) icb P) :
    WP isa (Impl.Aes.PPC64LE.Crypto.ctrData .r26) s fun t =>
      Keep ctrGprs s t ∧ Frame [⟨V .r30 + BitVec.ofNat 64 48,16⟩,⟨E,16*nb⟩] s.mem t.mem ∧
      bytesAt t.mem E (16*nb) = xorKs (ciphOf s.mem (V .r29) R) icb P (bytesAt s.mem S (16*nb)) ∧
      Ctr t.mem (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64)
        (ciphOf s.mem (V .r29) R) icb (P+16*nb) := by
  let C := V .r30 + BitVec.ofNat 64 48
  let rd : List Region := [⟨V .r29,240⟩,⟨S,16*nb⟩]
  let wr : List Region := [⟨C,16⟩,⟨E,16*nb⟩]
  let u := s.withRegions rd wr
  have hnb : nb < 2^64 := by have := src.lt; omega_using [this]
  have r4 : (u.gpr .r4).toNat = R := by change (s.gpr .r4).toNat = _; rw [h4,toNat_rounds rounds]
  have r7 : (u.gpr .r7).toNat = nb := by change (s.gpr .r7).toNat = _; rw [h7,toNat64 hnb]
  have r3 : u.gpr .r3 = V .r29 := h3
  have r5 : u.gpr .r5 = C := h5
  have r6 : u.gpr .r6 = S := h6
  have post := ctrData_wp .r26 E u (fun t h => (h.effects.keep.gpr (by decide)).trans (by rw [r6]; exact h26))
    (by decide) (.inr (by rwa [r6,r7]))
    (by rw [r3]; simp [u,rd,wr]) (by rw [r5]; simp [u,wr]) (by rw [r7]; simp [u,wr])
    (by rw [r6,r7]; simp [u,rd,wr]) (by rw [r3,r7]; exact dst.ctx.sub_left (Region.sub_prefix (by decide)))
    (by rw [r5,r7]; exact (dst.ok.st.sub_right (Lay.stSub (by decide))).symm)
    (by rw [r7]; exact Nat.le_of_lt src.lt) (by rwa [r4])
  obtain ⟨tr,v,hx,keep,frame,cipher,cb⟩ := post
  have hc : Covers (rd ++ wr) (s.rd ++ s.wr) := Covers.cons (covers_prefix env.perm.ctx (by decide))
    (Covers.cons src.rd (Covers.cons (covers_left (env.perm.stC (by decide))) (Covers.cons (covers_left dst.wr) Covers.nil)))
  have hw : Covers wr s.wr := Covers.cons (env.perm.stC (by decide)) (Covers.cons dst.wr Covers.nil)
  have ex := Exec.widen hx hc hw
  rw [r7,r5] at frame
  rw [r7,r4,r3,r5,r6] at cipher
  rw [r5,r7] at cb
  obtain ⟨out,advance⟩ := Proof.Gcm.ctr_wholeTo ctr aligned cipher cb
  exact ⟨tr,v.withRegions s.rd s.wr,ex,⟨keep.1,rfl,rfl⟩,frame,out,advance⟩

def wholeRegs : List Reg :=
  [.r0,.r3,.r4,.r5,.r6,.r7,.r8,.r9,.r10,.r11,.r12,.r21,.r24,.r25,.r26]

theorem whole_wp {V : Reg → BitVec 64} {sp S E : Addr} {P n R : Nat} {icb : Block} {s : State}
    (env : Env V sp s) (hS : s.gpr .r24 = S) (hE : s.gpr .r21 = E)
    (count : s.gpr .r25 = BitVec.ofNat 64 n) (rounds : R = 10 ∨ R = 12 ∨ R = 14)
    (hR : V .r28 = BitVec.ofNat 64 R)
    (src : DataOk (V .r30) (V .r31) s S n) (dst : DataW (V .r29) (V .r30) (V .r31) s E n)
    (sep : (⟨S,n⟩ : Region).Disjoint ⟨E,n⟩) (aligned : n = 0 ∨ P % 16 = 0)
    (ctr : Ctr s.mem (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64)
      (ciphOf s.mem (V .r29) R) icb P) :
    let k := 16*(n/16)
    WP isa Impl.AesGcm.PPC64LE.DirectGather.whole s fun t =>
      (t.gpr .r24 = S + BitVec.ofNat 64 k ∧ t.gpr .r21 = E + BitVec.ofNat 64 k ∧
       t.gpr .r25 = BitVec.ofNat 64 (n-k) ∧ Frame [⟨V .r30 + BitVec.ofNat 64 48,16⟩,⟨E,k⟩] s.mem t.mem ∧
       bytesAt t.mem E k = xorKs (ciphOf s.mem (V .r29) R) icb P (bytesAt s.mem S k) ∧
       Ctr t.mem (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64)
         (ciphOf s.mem (V .r29) R) icb (P+k)) ∧ Keep wholeRegs s t := by
  intro k
  refine WP.keep wholeRegs ?_ (by decide)
  let nb := n/16
  have small : nb < 2^64 := by dsimp [nb]; have := src.lt; omega_using [this]
  have kLe : k ≤ n := by dsimp [k]; omega
  let pre := s.write .r7 (BitVec.ofNat 64 nb)
  have start : WP isa (.block [.lsr .d .r7 .r25 4]) s (· = pre) := by
    crun [pre,nb,count,shr4 src.lt]
  refine WP.seq (WP.mono start fun u eq => ?_)
  subst u
  have r7 : pre.gpr .r7 = BitVec.ofNat 64 nb := by simp [pre,State.write]
  refine WP.ite (decide (nb=0)) (eval_zero r7 small) (fun hz => ?_) (fun hn => ?_)
  · have hz' : nb = 0 := by simpa using hz
    have hk : k=0 := by change 16*nb=0; rw [hz',Nat.mul_zero]
    refine WP.block_nil ?_
    simp only [hk,add_ofNat_zero,Nat.sub_zero,Nat.add_zero]
    exact ⟨hS,hE,count,Frame.refl _ _,by simp [bytesAt,Proof.Gcm.xorKs_nil],ctr⟩
  · have nonzero : nb ≠ 0 := by simpa using hn
    have ha : P%16=0 := aligned.resolve_left (fun h => nonzero (by simp [nb,h]))
    have shift : BitVec.ofNat 64 nb <<< 4 = BitVec.ofNat 64 k := by
      rw [BitVec.shiftLeft_eq_mul_twoPow]
      change BitVec.ofNat 64 nb * BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_mul,Nat.mul_comm]
    have q21 : pre.gpr .r21=E := hE
    have q24 : pre.gpr .r24=S := hS
    have q25 : pre.gpr .r25=BitVec.ofNat 64 n := count
    have q28 : pre.gpr .r28=BitVec.ofNat 64 R := env.r28.trans hR
    have q29 : pre.gpr .r29=V .r29 := env.r29
    have q30 : pre.gpr .r30=V .r30 := env.r30
    let prep : List Instr := [mov .r6 .r24, .sub .r26 .r21 .r24, .lsl .r11 .r7 4, .add .r21 .r21 .r11,
        .add .r24 .r24 .r11, .sub .r25 .r25 .r11] ++ ctrArgs 48
    have setup : WP isa (.block prep) pre fun u =>
        u.gpr .r3=V .r29 ∧ u.gpr .r4=BitVec.ofNat 64 R ∧ u.gpr .r5=V .r30+BitVec.ofNat 64 48 ∧
        u.gpr .r6=S ∧ u.gpr .r7=BitVec.ofNat 64 nb ∧ u.gpr .r26=E-S ∧
        u.gpr .r21=E+BitVec.ofNat 64 k ∧ u.gpr .r24=S+BitVec.ofNat 64 k ∧ u.gpr .r25=BitVec.ofNat 64 (n-k) ∧
        u.gpr .r29=V .r29 ∧ u.gpr .r30=V .r30 ∧ u.gpr .r31=V .r31 ∧ Keeps pre u := by
      have q31 : pre.gpr .r31=V .r31 := env.r31
      simp only [prep,ctrArgs,List.cons_append,List.nil_append]
      crun [mov,BitVec.or_self,q21,q24,q25,q28,q29,q30,q31,r7,shift,ofNat_sub64 kLe src.lt]
      exact ⟨rfl,rfl,rfl,rfl,rfl⟩
    refine WP.seq (WP.mono setup fun u ⟨u3,u4,u5,u6,u7,u26,u21,u24,u25,u29,u30,u31,kept⟩ => ?_)
    have hu : Env u.gpr sp u := ⟨fun _ _ => rfl,kept.sp.trans env.sp,by
      rw [u29,u30,u31]; exact env.perm.of_eq kept.rd kept.wr⟩
    have x := ctrTo_wp (V := u.gpr) (P := P) (R := R) (nb := nb) hu (u3.trans u29.symm) u4
      (by rwa [u30]) u6 u7 u26 (by rw [u30,u31]; exact (src.take kLe).of_eq kept.rd kept.wr)
      (by rw [u29,u30,u31]; exact (dst.take kLe).of_eq kept.rd kept.wr)
      ((sep.sub_left (Region.sub_prefix kLe)).sub_right (Region.sub_prefix kLe)) rounds ha
      (by rw [u29,u30,kept.mem]; exact ctr)
    refine WP.mono x fun t ⟨hkeep,frame,out,advance⟩ => ?_
    rw [u29,kept.mem] at out advance
    rw [u30] at frame advance
    rw [kept.mem] at frame
    exact ⟨(hkeep.gpr (by decide)).trans u24,(hkeep.gpr (by decide)).trans u21,
      (hkeep.gpr (by decide)).trans u25,frame,out,advance⟩

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Appending direct ciphertext from a POWER8 gather piece -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block)
open VG.Proof.Gcm (xorKs Ctr)

/-- The output cursor is the sole otherwise frozen register advanced by the piece. -/
def cursors (V : Reg → Addr) (E : Addr) (r : Reg) : Addr := if r = .r21 then E else V r

/-- Input/output ranges for one descriptor. Its input may be read, but the
only written non-stack range is the corresponding interval in the output. -/
structure Range (V : Reg → Addr) (entry : State) (S E : Addr) (n : Nat) : Prop where
  src : DataOk (V .r30) (V .r31) entry S n
  dst : DataW (V .r29) (V .r30) (V .r31) entry E n
  sep : (⟨S,n⟩ : Region).Disjoint ⟨E,n⟩

structure Progress (V : Reg → Addr) (sp : Addr) (R : Nat) (icb : Block) (P : Nat) (S E : Addr)
    (n : Nat) (entry : State) (j : Nat) (s : State) : Prop where
  le : j ≤ n
  env : Env (cursors V (E + BitVec.ofNat 64 j)) sp s
  rd : s.rd = entry.rd
  wr : s.wr = entry.wr
  ptr : s.gpr .r24 = S + BitVec.ofNat 64 j
  left : s.gpr .r25 = BitVec.ofNat 64 (n-j)
  ctr : Ctr s.mem (V .r30+BitVec.ofNat 64 48) (V .r30+BitVec.ofNat 64 64) (ciphOf entry.mem (V .r29) R) icb (P+j)
  out : bytesAt s.mem E j = xorKs (ciphOf entry.mem (V .r29) R) icb P (bytesAt entry.mem S j)
  frame : Frame (crFrame (V .r30) (V .r31) E j) entry.mem s.mem

variable {V : Reg → Addr} {sp S E : Addr} {R P n j k : Nat} {icb : Block} {entry s t : State}

theorem Range.remaining (a : Range V entry S E n) (p : Progress V sp R icb P S E n entry j s) :
    Range V s (S + BitVec.ofNat 64 j) (E + BitVec.ofNat 64 j) (n-j) :=
  ⟨(a.src.drop p.le).of_eq p.rd p.wr, (a.dst.drop p.le).of_eq p.rd p.wr,
   (a.sep.sub_left (Offset.sub_base _ (by have := p.le; omega_using [this]))).sub_right
     (Offset.sub_base _ (by have := p.le; omega_using [this]))⟩

theorem Progress.ciph (p : Progress V sp R icb P S E n entry j s) (a : Range V entry S E n)
    (L : Lay (V .r29) (V .r30) (V .r31)) (rounds : R=10 ∨ R=12 ∨ R=14) :
    ciphOf s.mem (V .r29) R = ciphOf entry.mem (V .r29) R := by
  refine ciph_frame p.frame (fun r hr => ?_) rounds
  simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact a.dst.ctx.sub_right (Region.sub_prefix p.le)
  · exact L.cs.sub_right (Lay.stSub (by decide))

/-- Compose two adjacent portions while retaining the original source bytes
and the ciphertext already written. -/
theorem Progress.join (p : Progress V sp R icb P S E n entry j s) (a : Range V entry S E n)
    (hjk : j+k ≤ n)
    (out : bytesAt t.mem (E+BitVec.ofNat 64 j) k = xorKs (ciphOf entry.mem (V .r29) R) icb (P+j)
      (bytesAt s.mem (S+BitVec.ofNat 64 j) k))
    (frame : Frame (crFrame (V .r30) (V .r31) (E+BitVec.ofNat 64 j) k) s.mem t.mem) :
    bytesAt t.mem E (j+k) = xorKs (ciphOf entry.mem (V .r29) R) icb P (bytesAt entry.mem S (j+k)) ∧
      Frame (crFrame (V .r30) (V .r31) E (j+k)) entry.mem t.mem := by
  have subS : Region.Sub ⟨S+BitVec.ofNat 64 j,k⟩ ⟨S,n⟩ := Offset.sub_base _ hjk
  have subE : Region.Sub ⟨E,j⟩ ⟨E,n⟩ := Region.sub_prefix p.le
  have subW : Region.Sub ⟨V .r30+BitVec.ofNat 64 48,32⟩ ⟨V .r30,80⟩ := Lay.stSub (by decide)
  have hsep := (split_disj (D := E) p.le a.dst.ok.lt).sub_right (Region.sub_prefix (by omega_using [hjk] : k≤n-j))
  have keptE : bytesAt t.mem E j = bytesAt s.mem E j := by
    refine bytesAt_frame frame (fun r hr => ?_) (by have hn := a.dst.ok.lt; have hj := p.le; omega_using [hn,hj])
    simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hsep
    · exact (a.dst.ok.st.sub_left subE).sub_right subW
  have keptS : bytesAt s.mem (S+BitVec.ofNat 64 j) k = bytesAt entry.mem (S+BitVec.ofNat 64 j) k := by
    refine bytesAt_frame p.frame (fun r hr => ?_) (by have := a.src.lt; omega_using [hjk,this])
    simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact (a.sep.sub_left subS).sub_right subE
    · exact (a.src.st.sub_left subS).sub_right subW
  refine ⟨done_appendTo (keptE.trans p.out) (by rwa [←keptS]),?_⟩
  apply Frame.trans (p.frame.sub ?_) (frame.sub ?_)
  · intro r hr
    simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_,List.mem_cons_self ..,Region.sub_prefix (Nat.le_add_right _ _)⟩
    · exact ⟨_,by simp [crFrame],fun _ h => h⟩
  · intro r hr
    simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_,List.mem_cons_self ..,Offset.sub_base _ (Nat.le_refl _)⟩
    · exact ⟨_,by simp [crFrame],fun _ h => h⟩

theorem Progress.extend (p : Progress V sp R icb P S E n entry j s) (a : Range V entry S E n)
    (hjk : j+k ≤ n)
    (env : Env (cursors V (E + BitVec.ofNat 64 (j+k))) sp t)
    (rd : t.rd=s.rd) (wr : t.wr=s.wr)
    (ptr : t.gpr .r24=S+BitVec.ofNat 64 (j+k)) (left : t.gpr .r25=BitVec.ofNat 64 (n-(j+k)))
    (ctr : Ctr t.mem (V .r30+BitVec.ofNat 64 48) (V .r30+BitVec.ofNat 64 64) (ciphOf entry.mem (V .r29) R)
      icb (P+j+k))
    (out : bytesAt t.mem (E+BitVec.ofNat 64 j) k = xorKs (ciphOf entry.mem (V .r29) R) icb (P+j)
      (bytesAt s.mem (S+BitVec.ofNat 64 j) k))
    (frame : Frame (crFrame (V .r30) (V .r31) (E+BitVec.ofNat 64 j) k) s.mem t.mem) :
    Progress V sp R icb P S E n entry (j+k) t := by
  obtain ⟨cipher,mem⟩ := p.join a hjk out frame
  exact ⟨hjk,env,rd.trans p.rd,wr.trans p.wr,ptr,left,by rwa [← Nat.add_assoc],cipher,mem⟩

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Encrypt one gather descriptor, including both partial counter blocks -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block)
open VG.Proof.Gcm (xorKs Ctr)
variable {V : Reg → Addr} {sp S E : Addr} {R P n j : Nat} {icb : Block} {o s t : State}

/-- All the frozen registers besides the output cursor retain their values. -/
theorem advanceEnv {A B : Addr} (env : Env (cursors V A) sp s) (p : t.gpr .r21=B)
    (regs : Keep wholeRegs s t) (hs : t.sp=s.sp) : Env (cursors V B) sp t := by
  refine ⟨?_,hs.trans env.sp,env.perm.of_eq regs.2.1 regs.2.2⟩
  intro r hr
  by_cases h : r=.r21
  · subst h; exact p
  · rw [cursors,ite_eq_right h,regs.gpr (by revert r; decide),env.fr r hr,cursors,ite_eq_right h]

theorem atWhole (p : Progress V sp R icb P S E n o j s) (a : Range V o S E n)
    (L : Lay (V .r29) (V .r30) (V .r31)) (rounds : R=10 ∨ R=12 ∨ R=14)
    (hR : V .r28=BitVec.ofNat 64 R) (aligned : n-j=0 ∨ (P+j)%16=0) :
    let k := 16*((n-j)/16)
    WP isa Impl.AesGcm.PPC64LE.DirectGather.whole s
      (Progress V sp R icb P S E n o (j+k)) := by
  intro k
  have ra := a.remaining p
  have he : s.gpr .r21=E+BitVec.ofNat 64 j := p.env.fr _ (by decide)
  have old := p.ciph a L rounds
  have ct : Ctr s.mem (V .r30+BitVec.ofNat 64 48) (V .r30+BitVec.ofNat 64 64)
      (ciphOf s.mem (V .r29) R) icb (P+j) := by rw [old]; exact p.ctr
  obtain ⟨tr,t,hx,⟨ptr,dest,left,frame,cipher,ctr⟩,keep⟩ :=
    whole_wp p.env p.ptr he p.left rounds hR ra.src ra.dst ra.sep aligned ct
  refine ⟨tr,t,hx,p.extend a (by dsimp [k]; have := p.le; omega_using [this]) ?_ keep.2.1 keep.2.2 ?_ ?_ ?_ ?_ ?_⟩
  · apply advanceEnv p.env _ keep (Exec.sp hx)
    exact dest.trans (add_ofNat_assoc ..)
  · exact ptr.trans (add_ofNat_assoc ..)
  · rw [left]; congr 1; omega
  · change Ctr t.mem _ _ (ciphOf s.mem (V .r29) R) _ _ at ctr
    rwa [old] at ctr
  · change bytesAt t.mem _ k = xorKs (ciphOf s.mem (V .r29) R) _ _ _ at cipher
    rwa [old] at cipher
  · refine frame.sub (fun r hr => ?_)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Region.sub_prefix (by decide : 16≤32)⟩
    · exact ⟨_,List.mem_cons_self ..,fun _ h => h⟩

theorem atHead (p : Progress V sp R icb P S E n o 0 s) (a : Range V o S E n)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 (P%16)) (hn : n≠0) (hP : P%16≠0) :
    let k := min (16-P%16) n
    WP isa Impl.AesGcm.PPC64LE.DirectGather.head s (Progress V sp R icb P S E n o k) := by
  intro k
  have he : s.gpr .r21=E := (p.env.fr .r21 (by decide)).trans (add_ofNat_zero _)
  have hS : s.gpr .r24=S := p.ptr.trans (add_ofNat_zero _)
  have h0 : s.gpr .r25=BitVec.ofNat 64 n := by simpa only [Nat.sub_zero] using p.left
  have ct := p.ctr
  rw [Nat.add_zero] at ct
  obtain ⟨tr,t,hx,⟨ptr,dest,left,frame,ctr,cipher⟩,keep⟩ := head_wp p.env hS he h0 h26
    (a.src.of_eq p.rd p.wr) (a.dst.of_eq p.rd p.wr) a.sep hn hP ct
  have advance : Progress V sp R icb P S E n o (0+k) t := by
    refine p.extend a (by rw [Nat.zero_add]; exact Nat.min_le_right _ _) ?_ keep.2.1 keep.2.2 ?_ ?_ ?_ ?_ ?_
    · rw [Nat.zero_add]
      exact advanceEnv p.env dest (keep.mono (by decide)) (Exec.sp hx)
    · rwa [Nat.zero_add]
    · rwa [Nat.zero_add]
    · rwa [Nat.add_zero]
    · simpa only [Nat.add_zero,add_ofNat_zero] using cipher
    · rw [add_ofNat_zero]
      exact frame.mono (by simp [crFrame,k])
  exact ⟨tr,t,hx,Nat.zero_add k ▸ advance⟩

/-- Final state of a descriptor. The source and all previous ciphertext are
outside its write set. r24/r25 become free as the loop reads the next descriptor. -/
structure PieceOut (V : Reg → Addr) (sp : Addr) (R : Nat) (icb : Block) (P : Nat) (S E : Addr) (n : Nat)
    (o t : State) : Prop where
  env : Env (cursors V (E+BitVec.ofNat 64 n)) sp t
  rd : t.rd=o.rd
  wr : t.wr=o.wr
  ctr : Ctr t.mem (V .r30+BitVec.ofNat 64 48) (V .r30+BitVec.ofNat 64 64)
    (ciphOf o.mem (V .r29) R) icb (P+n)
  cipher : bytesAt t.mem E n = xorKs (ciphOf o.mem (V .r29) R) icb P (bytesAt o.mem S n)
  frame : Frame (crFrame (V .r30) (V .r31) E n) o.mem t.mem

theorem atTail (p : Progress V sp R icb P S E n o j s) (a : Range V o S E n)
    (L : Lay (V .r29) (V .r30) (V .r31)) (rounds : R=10 ∨ R=12 ∨ R=14)
    (hR : V .r28=BitVec.ofNat 64 R) (aligned : n-j=0 ∨ (P+j)%16=0) (tail : n-j<16) :
    WP isa (.seq (.block [mov .r26 .r21, .add .r21 .r21 .r25]) (cryptTailWith true)) s
      (PieceOut V sp R icb P S E n o) := by
  let k := n-j
  have hsum : j+k=n := Nat.add_sub_of_le p.le
  have old := p.ciph a L rounds
  have he : s.gpr .r21=E+BitVec.ofNat 64 j := p.env.fr _ (by decide)
  have hc := p.left
  let u := (s.write .r26 (s.gpr .r21)).write .r21 (s.gpr .r21+s.gpr .r25)
  have prep : WP isa (.block [mov .r26 .r21, .add .r21 .r21 .r25]) s (· = u) := by
    crun [u,mov,BitVec.or_self]
  obtain ⟨tr,t,hx,rfl,keep⟩ := WP.keep wholeRegs prep (by decide)
  have cursor : u.gpr .r21 = E + BitVec.ofNat 64 n := by
    change s.gpr .r21 + s.gpr .r25 = _
    rw [he,hc,add_ofNat_assoc,Nat.add_sub_of_le p.le]
  have env := advanceEnv p.env cursor keep (Exec.sp hx)
  have ra := a.remaining p
  have tin : TailIn true (cursors V (E+BitVec.ofNat 64 n)) sp R icb (P+j) (S+BitVec.ofNat 64 j)
      (E+BitVec.ofNat 64 j) k (ciphOf o.mem (V .r29) R) True u :=
    ⟨env,p.ptr,p.left,fun _ => he,hR,rounds,aligned,ra.src.of_eq (s' := u) rfl rfl,ra.dst.of_eq (s' := u) rfl rfl,
      (fun h => nomatch h),.inr ra.sep,old,fun _ => p.ctr⟩
  obtain ⟨tr',t,ex,out⟩ := cryptTailWith_ok (V := cursors V (E+BitVec.ofNat 64 n)) L tin tail
  have joined := p.join a (k := k) (Nat.le_of_eq hsum) (out.out trivial) out.frame
  rw [hsum] at joined
  have ctr := out.ctr trivial
  rw [Nat.add_assoc,hsum] at ctr
  exact ⟨_,t,VG.Exec.seq hx ex,out.env,(VG.PPC64LE.Exec.rdwr ex).1.trans p.rd,(VG.PPC64LE.Exec.rdwr ex).2.1.trans p.wr,ctr,joined.1,joined.2⟩

theorem afterHead (p : Progress V sp R icb P S E n o j s) (a : Range V o S E n)
    (L : Lay (V .r29) (V .r30) (V .r31)) (rounds : R=10 ∨ R=12 ∨ R=14)
    (hR : V .r28=BitVec.ofNat 64 R) (aligned : n-j=0 ∨ (P+j)%16=0) :
    WP isa (.seq Impl.AesGcm.PPC64LE.DirectGather.whole
      (.seq (.block [mov .r26 .r21, .add .r21 .r21 .r25]) (cryptTailWith true))) s
      (PieceOut V sp R icb P S E n o) := by
  refine WP.seq (WP.mono (atWhole p a L rounds hR aligned) fun t q => atTail q a L rounds hR ?_ ?_)
  · rcases aligned with hz | ha
    · left; omega_using [hz]
    · right; omega_using [ha]
  · omega

theorem piece_wp (env : Env (cursors V E) sp s) (hS : s.gpr .r24=S)
    (hn : s.gpr .r25=BitVec.ofNat 64 n) (cursor : E=V .r27+BitVec.ofNat 64 P) (fit : P<2^64)
    (a : Range V s S E n) (L : Lay (V .r29) (V .r30) (V .r31))
    (rounds : R=10 ∨ R=12 ∨ R=14) (hR : V .r28=BitVec.ofNat 64 R)
    (ctr : Ctr s.mem (V .r30+BitVec.ofNat 64 48) (V .r30+BitVec.ofNat 64 64)
      (ciphOf s.mem (V .r29) R) icb P) :
    WP isa Impl.AesGcm.PPC64LE.DirectGather.piece s (PieceOut V sp R icb P S E n s) := by
  refine WP.ite (decide (n=0)) (eval_zero hn a.src.lt) (fun hz => ?_) (fun hf => ?_)
  · obtain rfl : n=0 := by simpa using hz
    exact WP.block_nil ⟨by rwa [add_ofNat_zero],rfl,rfl,by rwa [Nat.add_zero],
      by simp [bytesAt,Proof.Gcm.xorKs_nil],Frame.refl _ _⟩
  · have nz : n≠0 := by simpa using hf
    have e21 : s.gpr .r21 = E := env.fr _ (by decide)
    have e27 : s.gpr .r27 = V .r27 := env.fr _ (by decide)
    have diff : s.gpr .r21 - s.gpr .r27=BitVec.ofNat 64 P := by
      rw [e21,e27,cursor,Offset.add_sub_cancel_left]
    have low := and15 (BitVec.ofNat 64 P)
    rw [toNat64 fit] at low
    let u := ((s.write .r26 (s.gpr .r21-s.gpr .r27)).write .r0 15).write .r26 (BitVec.ofNat 64 (P%16))
    have start : WP isa (.block [.sub .r26 .r21 .r27, .li .r0 15, .logic .and .r26 .r26 .r0]) s (· = u) := by
      crun [u,diff,low]
    obtain ⟨tr,t,ex,rfl,keep⟩ := WP.keep [.r0,.r26] start (by decide)
    have p0 : Progress V sp R icb P S E n s 0 u := by
      refine ⟨Nat.zero_le _,?_,rfl,rfl,by rwa [add_ofNat_zero],by rwa [Nat.sub_zero],
        by rwa [Nat.add_zero],by simp [bytesAt,Proof.Gcm.xorKs_nil],Frame.refl _ _⟩
      rw [add_ofNat_zero]
      exact env.keep (fun r hr => keep.gpr (by revert r; decide)) (Exec.sp ex) rfl rfl
    have off : u.gpr .r26=BitVec.ofNat 64 (P%16) := by simp [u,State.write]
    refine WP.seq ⟨tr,u,ex,?_⟩
    refine WP.seq (WP.mono (Q := fun t => ∃ j, Progress V sp R icb P S E n s j t ∧ (n-j=0 ∨ (P+j)%16=0)) ?_
      (fun t ⟨j,q,aligned⟩ => afterHead q a L rounds hR aligned))
    refine WP.ite (decide (P%16=0)) (eval_zero off (by omega)) (fun hz => ?_) (fun hne => ?_)
    · exact WP.block_nil ⟨0,p0,.inr (by simpa only [Nat.add_zero,decide_eq_true_eq] using hz)⟩
    · have hP : P%16≠0 := by simpa using hne
      refine WP.mono (atHead p0 a off nz hP) fun t q => ⟨_,q,?_⟩
      omega_using [hP]

end VG.Proof.AesGcm.PPC64LE.DirectGather
