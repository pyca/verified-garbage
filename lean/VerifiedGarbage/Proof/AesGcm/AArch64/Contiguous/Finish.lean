module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Remainder
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Authenticate the partial ciphertext block and lengths for either layout.
The wide final load may reach into the already encrypted prefix. Its entire
range lies inside the destination, even when the unstitched suffix is short. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared

open VG VG.AArch64 VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Impl.Gcm.AArch64.Pmull (Y loadRev)
open VG.Proof.Gcm.AArch64.Pmull
open VG.Spec.Gcm (Block blockAt ofBytes)
open VG.Spec.Aes (bytesAt)
open Fast (KeyAt padStep)

abbrev finishProgram : Prog isa := .seq (.block (Impl.AesGcm.AArch64.Fast.hReload ++ loadRev Y .x20 16 ++
    [mov .x13 .x24,mov .x12 .x23])) (.seq Impl.AesGcm.AArch64.Fast.padMulT (.block Impl.AesGcm.AArch64.Fast.lensTag))

theorem finish_ok {wn R n j al : Nat} {Ctx W SP O : Addr} {s : State} {H : Block}
    (mk : MulKey) (L : Lay wn Ctx (word W 16) W) (e : Env wn Ctx (word W 16) W SP s)
    (od : DataOk wn (word W 16) W s O n) (key : KeyAt H s.mem W)
    (hj : j ≤ n) (hl : n-j < 16) (ha : al < 2^64) (alen : s.mem.readW (word W alenO) 64 = BitVec.ofNat 64 al)
    (r22 : s.gpr .x22 = BitVec.ofNat 64 R) (rounds : R = 10 ∨ R = 12 ∨ R = 14)
    (r23 : s.gpr .x23 = word O j) (r24 : s.gpr .x24 = BitVec.ofNat 64 (n-j))
    (r26 : s.gpr .x26 = BitVec.ofNat 64 n) :
    let y := padStep H (blockAt s.mem (word (word W 16) 16)) (bytesAt s.mem (word O j) (n-j))
    WP isa finishProgram s fun t => ∃ k m, k .x28 = s.gpr .x28 ∧
      Tag1 wn Ctx (word W 16) W SP k 0 R (Spec.Gcm.mul (y ^^^ ofBytes (Proof.Gcm.lensBlock al n)) H)
        (blockAt s.mem (word W 16)) m t ∧ Frame (Fast.wsR wn W) s.mem m := by
  have lim := L.hWn
  refine WP.seq ((Fast.reloadTail_ok e key r24 r23).mono ?_)
  intro a ⟨ea,ka,ya,x13,x12,ra⟩
  have full := od.of_eq ra.rd ra.wr
  have tail := full.drop hj
  have n26 := (ra.others .x26 (by decide)).trans r26
  refine WP.seq ((WP.with_rdwr (Fast.padMulT_ok mk ea ka ya x12 x13 (by omega) tail.rd
    (tail.w.sub_right (Lay.wSub (by omega))) n26 od.lt
    (Fast.pad_big full.rd od.lt (by congr 2; omega) hl))).mono ?_)
  intro b ⟨⟨yb,kb,eb,gb,fb,_⟩,_,_⟩
  rw [ra.mem] at fb yb
  have len : b.mem.read (W+224#64) 8 = BitVec.ofNat 64 al := (fb.readW (r := slotR W 224)
    (Region.contains_self _ _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)) (by decide)).trans alen
  unfold Impl.AesGcm.AArch64.Fast.lensTag Impl.AesGcm.AArch64.Fast.lensTagAt
  rw [WP.block_append_iff]
  refine (Fast.finishLengths_ok mk eb kb yb ((gb _ (by decide)).trans n26) len ha od.lt).mono ?_
  intro c ⟨ec,yc,gc,_,_,m,ft,fy⟩
  have regs (r : Reg) (hr : r ∈ [Reg.x22,.x28]) : c.gpr r = s.gpr r := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> rw [gc _ (by decide),gb _ (by decide),ra.others _ (by decide)]
  have dT : ∀ r ∈ [(⟨word W 96,16⟩ : Region)], (⟨word W 16,16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact st0_w L ⟨by decide,by omega⟩
  have jc : blockAt c.mem (word W 16) = blockAt s.mem (word W 16) := by
    rw [blockAt_frame fy (fun r hr => by simp only [List.mem_singleton] at hr; subst r
                                         exact st0_disj L (by decide) (by decide)),blockAt_frame ft dT,blockAt_frame fb dT]
  have f : Frame (Fast.wsR wn W) s.mem c.mem := by
    refine (fb.sub fun r hr => ?_).trans ((ft.sub fun r hr => ?_).trans (fy.sub fun r hr => ?_))
    all_goals simp only [List.mem_singleton] at hr; subst r
    · exact Fast.sub_low (by decide)
    · exact Fast.sub_low (by decide)
    · exact Fast.sub_low' (by decide)
  exact (tagSeg_ok L (o := 0) (.inl rfl) ec (fun _ _ => rfl : Kept c.gpr c)
    ((regs _ (by decide)).trans r22) rounds).mono fun t post =>
      ⟨c.gpr,c.mem,regs _ (by decide),yc ▸ jc ▸ post,f⟩

abbrev paddedAad (aad : List Byte) := aad ++ Spec.Gcm.zeros (Spec.Gcm.padLen aad.length)

theorem suffixHash {wn n p j o : Nat} {Ctx St W SP O : Addr} {H : Block} {k : Reg → Addr}
    {m : Mem} {t : State} {aad : List Byte} (L : Lay wn Ctx St W)
    (od : DataOk wn St W t O n) (hp : p ≤ n) (pmod : p%16 = 0) (jmod : j%16 = 0)
    (last : n-p-j < 16)
    (start : blockAt m (word St 16) = Spec.Gcm.ghash H (Spec.Gcm.blocks (paddedAad aad ++ bytesAt m O p)))
    (h : AbsMid wn Ctx St W SP k 16 H (paddedAad aad ++ bytesAt m O p) (word O p) (n-p) o m j t) :
    let q := p+j
    padStep H (blockAt t.mem (word St 16)) (bytesAt t.mem (word O q) (n-q)) =
      Spec.Gcm.ghash H (Spec.Gcm.blocks (Proof.Gcm.padded aad (bytesAt m O n))) := by
  have hj := h.le
  have align : (paddedAad aad ++ bytesAt m O p).length % 16 = 0 := by
    simp only [paddedAad,List.length_append,length_bytesAt,Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod aad.length; omega
  have absorbed : Proof.Gcm.Absorbed m (word St 16) (word St 32) H (paddedAad aad ++ bytesAt m O p) := by
    refine ⟨?_,?_⟩
    · rw [Proof.Gcm.whole_of_mod align,List.take_length]; exact start
    · rw [align,Proof.Gcm.whole_of_mod align,List.drop_length]; rfl
  have y := (h.abs absorbed).whole_eq (by simp only [List.length_append,length_bytesAt] at align ⊢; omega)
  rw [List.append_assoc,← bytesAt_add] at y
  have ht : n-(p+j)<16 := by omega
  have eq := bytesAt_frame h.frame (data_absFrame L (.inr rfl) (od.drop (show p+j ≤ n by omega)))
    (show n-(p+j) ≤ 2^64 by have := od.lt; omega)
  dsimp only
  rw [eq,y,← Fast.ghash_padded _ _ _ _ (by rw [length_bytesAt]; omega) (by rw [length_bytesAt]; exact ht),
    ← bytesAt_add,Nat.add_sub_cancel' (show p+j ≤ n by omega)]

/-- Encrypt the authenticated hash, write the tag and restore all preserved GPRs. -/
theorem return_ok {wn R : Nat} {Ctx W Tg : Addr} {o s : State} {m : Mem} {k : Reg → Addr} {Yv J : Block}
    (v : GcmImpl) (L : Lay wn Ctx (word W 16) W) (h : Tag1 wn Ctx (word W 16) W o.sp k 0 R Yv J m s)
    (work : v.ctr.scratch ≤ wn-512) (tag : Covers [⟨Tg,16⟩] s.wr) (x28 : k .x28 = Tg)
    (saved : SavedAt m W o) (dis : (⟨Tg,16⟩ : Region).Disjoint (workR wn W)) :
    WP isa (.seq (ctrCall v.callees) (.seq (.block tagOut) (.block restore))) s fun t =>
      bytesAt t.mem Tg 16 = Spec.Gcm.toBytes (Yv ^^^ ciphOf m Ctx R J) ∧
      GprAbi o t ∧ Frame (⟨Tg,16⟩ :: Fast.wsR wn W) m t.mem := by
  have lim := L.hWn
  refine WP.seq ((WP.with_rdwr (tagCall_ok L v (.inl rfl) h work)).mono ?_)
  intro u ⟨hu,_,wr⟩
  have fu : Frame (Fast.wsR wn W) m u.mem := hu.frame.sub fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact Fast.sub_low (by decide)
    · exact Fast.sub_low (by decide)
    · exact Fast.sub_low (by decide)
    · exact Fast.sub_scr (by omega)
  refine WP.seq ((tagOut_ok hu.env.x19 ((hu.kept _ (by decide)).trans x28)
    (covers_left hu.env.perm.w) (wr ▸ tag) (dis.sub_right (Region.sub_prefix (by omega)))).mono ?_)
  intro z ⟨out,fz,gz,sp,rd,zw⟩
  have ez := hu.env.keep (fun r hr => gz _ (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;
                                                rcases hr with rfl|rfl|rfl <;> decide)) sp rd zw
  have sz : SavedAt z.mem W o := (saved.frame fu (Fast.saved_wsR lim)).frame fz (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact (dis.sub_right (Lay.wSub (by omega))).symm)
  refine (exit_ok ez.x19 ez.sp (covers_left ez.perm.w) sz).mono ?_
  intro t ⟨abi,mem,_,_,_⟩
  rw [mem]
  exact ⟨out.trans (by simpa using hu.out),abi,
    (fu.mono (fun _ hr => List.mem_cons_of_mem _ hr)).trans (fz.mono (fun _ hr => List.mem_singleton.mp hr ▸ List.mem_cons_self ..))⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared
