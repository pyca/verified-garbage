module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Nonce
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.AadCopy
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Bulk
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Stream

/-! # Absorbing AAD after contiguous POWER seal nonce setup -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.WriteBytes
open VG.Impl.AesGcm.PPC64LE.Contiguous
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
variable {V : Reg → BitVec 64} {sp : Addr}

private theorem padded_after_write {m : Mem} {T : Addr} {bs : List Byte} {n : Nat} (hlen : bs.length=n) (hn : n<16)
    (hz : bytesAt m T 16 = zeros 16) :
    bytesAt (writeBytes m T bs) T 16 = bs ++ zeros (16-n) := by
  rw [bytesAt_writeBytes_prefix _ _ _ (by omega) (by decide),hlen]
  congr 1
  rw [show (16 : Nat) = n + (16-n) by omega,bytesAt_add] at hz
  have suffix := congrArg (List.drop n) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at suffix
  simpa only [show n + (16-n)=16 by omega,zeros,List.drop_replicate] using suffix

private theorem nonempty_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] (L : Lay (V .r29) (V .r30) (V .r31))
    {H : Block} {iv : List Byte} {m : Mem} {s : State} (jo : J0Out V sp H iv m s)
    (hA : DataOk (V .r30) (V .r31) s (V .r21) (V .r22).toNat)
    (small : (V .r22).toNat<16) (pos : (V .r22).toNat ≠ 0) :
    WP isa (.seq (.block ([.li .r0 0,.store .d .r0 .r31 tO,.store .d .r0 .r31 (tO+8)] ++ aadCopyArgs))
      (.seq aadCopy (ghash1 16 .r31 tO))) s
      (OA V sp H iv (bytesAt m (V .r21) (V .r22).toNat) m) := by
  let n := (V .r22).toNat
  let T := V .r31 + BitVec.ofNat 64 96
  have h21 := jo.env.fr .r21 (by decide)
  have h22 := jo.env.ofNat (r := .r22) (by decide)
  have ht : (⟨V .r21,n⟩ : Region).Disjoint ⟨T,16⟩ := hA.w.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.block_append (WP.mono (zeroT_ok jo.env) fun u ⟨mem,regs,rd,wr,spk,_⟩ => ?_))
  have fz : Frame [⟨T,16⟩] s.mem u.mem := by rw [mem]; exact Proof.Cmac.frame_store2 _ _ _
  have init : WP isa (.block aadCopyArgs) u fun v => v.gpr .r3 = V .r21 ∧ v.gpr .r4 = T ∧
      v.gpr .r5 = BitVec.ofNat 64 n ∧ Keeps u v ∧ Keep [.r3,.r4,.r5] u v := by
    have p := (regs .r21 (by decide)).trans h21
    have q := (regs .r31 (by decide)).trans jo.env.r31
    have l := (regs .r22 (by decide)).trans h22
    crun [aadCopyArgs,mov,BitVec.or_self,p,q,l,tO,T,n]
    exact ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,fun r hr => by
      simp only [List.mem_cons,not_or] at hr
      simp [hr.1,hr.2.1,hr.2.2],rfl,rfl⟩
  refine WP.mono init fun v ⟨p,q,l,kv,kg⟩ => ?_
  have ha := hA.of_eq (kv.rd.trans rd) (kv.wr.trans wr)
  refine WP.seq (WP.mono (WP.with_rdwr (copy_short_wp p q l hA.lt ha.rd ?_ (ht.sub_right (Region.sub_prefix (Nat.le_of_lt small)))))
    fun z ⟨copy,rz,wz,sz⟩ => ?_)
  · rw [kv.wr,wr]
    exact jo.env.perm.wC (by change 96+n ≤ 288; omega)
  have env := jo.env.keep (s' := z) (fun r hr => by
    rw [copy.regs.gpr (by revert r; decide),kg.gpr (by revert r; decide),regs r (by revert r; decide)])
    (sz.trans (kv.sp.trans spk)) (rz.trans (kv.rd.trans rd)) (wz.trans (kv.wr.trans wr))
  have source : bytesAt v.mem (V .r21) n = bytesAt m (V .r21) n := by
    rw [kv.mem,bytesAt_frame fz (fun _ hr => List.mem_singleton.mp hr ▸ ht) (by omega)]
    exact bytesAt_frame jo.frame (data_j0 hA) (Nat.le_of_lt hA.lt)
  have fc : Frame [⟨T,16⟩] u.mem z.mem := by
    rw [copy.mem,kv.mem]
    exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; simpa [Region.Contains] using (Nat.le_of_lt small))
  have f := fz.trans fc
  have zb : bytesAt v.mem T 16 = zeros 16 := by rw [kv.mem,mem]; exact zeroT_bytes _ _
  have padded : bytesAt z.mem T 16 = bytesAt m (V .r21) n ++ zeros (16-n) := by
    rw [copy.mem,padded_after_write (length_bytesAt _ _ _) small zb,source]
  have ctx : blockAt z.mem (V .r29+BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame f (fun _ hr => List.mem_singleton.mp hr ▸ L.ctx_w (by decide) (by decide)),jo.hH]
  have y : blockAt z.mem (V .r30+BitVec.ofNat 64 16) = 0 := by
    rw [blockAt_frame f (fun _ hr => List.mem_singleton.mp hr ▸ L.st_w (by decide) (.inr ⟨by decide,by decide⟩)),jo.y]
  refine WP.mono (ghash1_ok L (.inr rfl) env .r31 96 (.inr rfl) (by decide) (P := T) (by rw [env.r31])
    (L.st_w (by decide) (.inr ⟨by decide,by decide⟩)) (covers_left (env.perm.wC (by decide)))) fun out g => ?_
  have frame := (tFrame_T (st := V .r30) (w := V .r31) (yo := 16) f).trans (gh_tFrame g.frame)
  have keep : ∀ {d : Nat}, (d=0 ∨ d=48) → blockAt out.mem (V .r30+BitVec.ofNat 64 d) = blockAt s.mem (V .r30+BitVec.ofNat 64 d) :=
    fun hd => blockAt_frame frame (stb_t16 L hd)
  refine ⟨g.env env,by rw [blockAt_frame g.frame (ctx_ghFrame L (.inr rfl)),ctx],
    ?_,by rw [keep (.inr rfl),jo.cb],?_,jo.frame.trans (frame.sub t16_j0)⟩
  · have k := keep (.inl (rfl : 0=0))
    simpa using k.trans (by simpa using jo.j0)
  · let bs := bytesAt m (V .r21) n ++ zeros (padLen n)
    have pad : padLen n = 16-n := by unfold padLen; omega
    have eq : bs = bytesAt z.mem T 16 := by rw [padded]; simp [bs,pad]
    have len : bs.length=16 := by rw [eq,length_bytesAt]
    have abs := Proof.Gcm.absorb_whole (b := V .r30+BitVec.ofNat 64 32)
      (Proof.Gcm.absorbed_nil H y) (d := bs) (by decide) (by rw [len])
      (m' := out.mem) (by rw [g.out,ctx,Proof.Gcm.blocks_single len,eq]; rfl)
    simpa only [List.nil_append,length_bytesAt] using abs

theorem aad_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] (L : Lay (V .r29) (V .r30) (V .r31))
    {H : Block} {iv : List Byte} {m : Mem} {s : State} (jo : J0Out V sp H iv m s)
    (hA : DataOk (V .r30) (V .r31) s (V .r21) (V .r22).toNat) :
    WP isa aadC s (OA V sp H iv (bytesAt m (V .r21) (V .r22).toNat) m) := by
  let n := (V .r22).toNat
  let t := s.write .r11 (BitVec.ofNat 64 (n / 16))
  have e22 := jo.env.ofNat (r := .r22) (by decide)
  have step : WP isa (.block [.lsr .d .r11 .r22 4]) s (· = t) := by
    crun [e22,DirectGather.shrNat 4 hA.lt,t,n]
  refine WP.seq (WP.mono step fun u hu => ?_)
  subst u
  have env := jo.env.keep (s' := t) (fun r hr => by have ne : r ≠ .r11 := by revert r; decide
                                                    simp [t,State.write,ne]) rfl rfl rfl
  have jout : J0Out V sp H iv m t := { jo with env }
  have data := hA.of_eq (s' := t) rfl rfl
  refine WP.ite (decide (n/16 = 0)) (eval_zero (s := t) (r := .r11) (by rfl) (by have := hA.lt; omega))
    (fun h => ?_) (fun _ => aadAfterNonce_ok L jout data)
  have hdiv : n/16=0 := by simpa using h
  have small : n<16 := by omega
  refine WP.ite (decide (n=0)) (eval_zero (env.ofNat (r := .r22) (by decide)) hA.lt)
    (fun empty => ?_) (fun nonempty => nonempty_wp L jout data small (by simpa using nonempty))
  have hz : (V .r22).toNat = 0 := by simpa using empty
  apply WP.block_nil
  refine ⟨env,jo.hH,jo.j0,jo.cb,?_,jo.frame⟩
  rw [hz]
  simpa [bytesAt,padLen,zeros] using (Proof.Gcm.absorbed_nil (m := t.mem) (b := V .r30+BitVec.ofNat 64 32) H jo.y)

/-- Prepare the nonce and authenticate the padded AAD for either payload layout. -/
theorem nonce_aad_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] (L : Lay (V .r29) (V .r30) (V .r31))
    {H : Block} {Np : Addr} {n : Nat} {s : State} (iv : J0In V sp H Np n s)
    (hA : DataOk (V .r30) (V .r31) s (V .r21) (V .r22).toNat) :
    WP isa (.seq nonceC aadC) s
      (OA V sp H (bytesAt s.mem Np n) (bytesAt s.mem (V .r21) (V .r22).toNat) s.mem) :=
  WP.seq (WP.mono (WP.with_rdwr (nonce_wp L iv)) fun _ ⟨jo,rd,wr,_⟩ => aad_wp L jo (hA.of_eq rd wr))

end VG.Proof.AesGcm.PPC64LE.Contiguous
