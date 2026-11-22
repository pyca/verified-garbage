module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GeneralFrame
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericStream
public import VerifiedGarbage.Proof.AesGcm.AArch64.Front
public import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Absorb
import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Proof.AesGcm.AArch64.Flush
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-! General gather sealing: nonce and AAD, encrypted fragments, the final
pending ciphertext and the tag. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.AesGcm.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.Gcm (Absorbed)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)

abbrev aadPad (a : List Byte) := a ++ Spec.Gcm.zeros (Spec.Gcm.padLen a.length)
abbrev aadFrame (St W : Addr) := frontFrame St W ++ tFrame St W 16

structure AadReady (Wn : Nat) (Ctx St W SP : Addr) (H : Block) (iv a : List Byte) (s u : State) : Prop where
  env : Env Wn Ctx St W SP u
  x22 : u.gpr .x22 = s.gpr .x22
  j0 : blockAt u.mem St = Spec.Gcm.j0 H iv
  hH : blockAt u.mem (Ctx + BitVec.ofNat 64 240) = H
  cb : blockAt u.mem (St + BitVec.ofNat 64 48) = Spec.Gcm.inc32 (Spec.Gcm.j0 H iv)
  hash : blockAt u.mem (St + BitVec.ofNat 64 16) = Spec.Gcm.ghash H (Spec.Gcm.blocks (aadPad a))
  frame : Frame (aadFrame St W) s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem aadReady_ok {Wn nl al : Nat} {Ctx St W SP Np A : Addr} {H : Block} {s : State} (L : Lay Wn Ctx St W)
    (v : GcmImpl) (he : Env Wn Ctx St W SP s) (h23 : s.gpr .x23 = Np)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 nl) (h26 : s.gpr .x26 = BitVec.ofNat 64 nl) (h27 : s.gpr .x27 = 0)
    (hnon : DataOk Wn St W s Np nl) (haad : DataOk Wn St W s A al)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    {rest : Prog isa} {Q : State → Prop}
    (hr : ∀ u, AadReady Wn Ctx St W SP H (bytesAt s.mem Np nl) (bytesAt s.mem A al) s u → WP isa rest u Q) :
    WP isa (.seq (j0 v.callees) <| .seq (oneAad v.callees) <|
      .seq (.block [.ldr .x .x25 .x19 alenO, imm .x9 15, .logic .and .x .x25 .x25 .x9]) <|
      .seq (flush v.callees 16) rest) s Q := by
  refine aadFront_ok L v he (fun _ _ => rfl) h23 h24 h26 h27 hnon haad hH sA sL fun a f => ?_
  have hl := (slot_kept f.frame (slots_frontFrame L) (d := 224) (by decide) (by decide)).trans sL
  have rd := f.env.perm.wR (d := 224) (n := 8) (by decide)
  obtain ⟨b,run,off,r⟩ : ∃ b, runBlock isa [.ldr .x .x25 .x19 alenO, imm .x9 15, .logic .and .x .x25 .x25 .x9] a =
      some b ∧ b.gpr .x25 = BitVec.ofNat 64 (al % 16) ∧ Regs [.x25,.x9] a b := by
    refine ⟨_, by arun [f.env.x19,rd], ?_⟩
    refine ⟨?_, by others_tac, rfl,rfl,rfl,rfl⟩
    simp only [gpr_write,ite_true,ite_false,reduceCtorEq,BitVec.setWidth_eq]
    rw [show a.mem.read (W+224#64) 8 = a.mem.readW (W+224#64) 64 from rfl, hl,
      show BitVec.setWidth 64 (15#16) <<< (16*0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt haad.lt]
  refine WP.seq (WP.of_runBlock ⟨b,run,?_⟩)
  have eb := f.env.of_regs r
  refine WP.seq (WP.mono (WP.with_rdwr (flush_ok L (.inr rfl) v (x := bytesAt s.mem A al) eb
    (fun _ _ => rfl) off (by rw [length_bytesAt]) (r.mem ▸ f.hH))) fun u ⟨⟨q,key,abs⟩,ru,wu⟩ => ?_)
  have f' := q.frame
  rw [r.mem] at f'
  have complete := (abs (r.mem ▸ f.abs)).whole_eq (by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
  refine hr u ⟨q.env, (q.kept _ (by decide)).trans ((r.others _ (by decide)).trans f.x22), ?_, key, ?_, complete,
    (f.frame.mono (fun _ hx => List.mem_append_left _ hx)).trans (f'.mono (fun _ hx => List.mem_append_right _ hx)),
    ru.trans (r.rd.trans f.rd), wu.trans (r.wr.trans f.wr)⟩
  · rw [blockAt_frame f' fun rr hx => ?_, f.j0]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact st0_disj L (by decide) (by decide)
    · exact st0_w L ⟨by decide,by have := L.hWn; omega⟩
    · exact st0_w L ⟨by decide,by have := L.hWn; omega⟩
  · rw [blockAt_frame f' (fun rr hx => (acc_tFrame_free L rr hx).sub_left (Region.sub_prefix (by decide))), f.cb]

/-- Flush complete hash blocks and buffer the trailing bytes, irrespective
of the counter-mode offset currently in x25. -/
theorem absorbRemainder_ok {Wn n : Nat} {Ctx St W SP D : Addr} {H : Block} {x : List Byte} {s : State}
    (L : Lay Wn Ctx St W) (v : GcmImpl) (he : Env Wn Ctx St W SP s) (h23 : s.gpr .x23 = D)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 n) (data : DataOk Wn St W s D n)
    (key : blockAt s.mem (Ctx+240) = H) (whole : x.length % 16 = 0) :
    WP isa (absorbAl v.callees 16) s fun t =>
      AbsOut Wn Ctx St W SP s.gpr 16 H x (x ++ bytesAt s.mem D n) (s.gpr .x25).toNat s.mem t ∧
      t.gpr .x24 = BitVec.ofNat 64 (n%16) := by
  have mid : AbsMid Wn Ctx St W SP s.gpr 16 H x D n (s.gpr .x25).toNat s.mem 0 s :=
    ⟨he,fun _ _ => rfl, Nat.zero_le _,by simpa using h23,by simpa using h24, by simp, data,key,
      fun ha => by simpa [bytesAt] using ha, .inr (by simpa using whole), Frame.refl _ _⟩
  refine WP.seq (WP.mono (absSeg2_ok L (.inr rfl) mid) fun u b => ?_)
  refine WP.seq (WP.mono (absCall2_ok L (.inr rfl) v b) fun z ⟨q,lo⟩ => ?_)
  refine WP.mono (WP.gprs (absTail_ok L (.inr rfl) q lo) (rs := [.x24]) (by decide) (by decide)) fun t ⟨a,g⟩ => ?_
  exact ⟨a, by rw [g _ (by simp), q.x24]; congr 1; omega⟩

abbrev tailCode (c : Callees) : Prog isa :=
  .seq (.block [.ldr .x .x23 .x19 Impl.AesGcm.AArch64.DirectGather.hashO, .sub .x .x24 .x26 .x23]) <|
  .seq (absorbAl c 16) <| .seq (.block [mov .x25 .x24]) (flush c 16)

abbrev tailFrame (St W : Addr) := absFrame St W 16 ++ tFrame St W 16

theorem padBoth (a c : List Byte) :
    aadPad a ++ c ++ Spec.Gcm.zeros (Spec.Gcm.padLen (aadPad a ++ c).length) = Proof.Gcm.padded a c := by
  by_cases h : c = []
  · subst c
    rw [List.append_nil, Proof.Gcm.padLen_of_mod (by
      simp only [aadPad,List.length_append,Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)]
    simp only [Spec.Gcm.zeros,List.replicate_zero,List.append_nil]; rfl
  · rw [Proof.Gcm.padded,Proof.Gcm.ghashInput_of_ne h]

theorem tailCode_ok {Wn n j : Nat} {Ctx St W SP O : Addr} {H : Block} {a : List Byte} {s : State}
    (v : GcmImpl) (L : Lay Wn Ctx St W) (he : Env Wn Ctx St W SP s)
    (data : DataOk Wn St W s O n) (hb : 16*j ≤ n)
    (x26 : s.gpr .x26 = O + BitVec.ofNat 64 n)
    (slot : s.mem.readW (W+352) 64 = O + BitVec.ofNat 64 (16*j))
    (key : blockAt s.mem (Ctx+240) = H)
    (hy : blockAt s.mem (St+16) =
      Spec.Gcm.ghashFrom H (Spec.Gcm.ghash H (Spec.Gcm.blocks (aadPad a))) (blocksAt s.mem O j)) :
    WP isa (tailCode v.callees) s fun u => Env Wn Ctx St W SP u ∧ u.gpr .x22 = s.gpr .x22 ∧
      blockAt u.mem (St+16) = Spec.Gcm.ghash H (Spec.Gcm.blocks (Proof.Gcm.padded a (bytesAt s.mem O n))) ∧
      Frame (tailFrame St W) s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  let X := aadPad a ++ bytesAt s.mem O (16*j)
  have alMod : (aadPad a).length % 16 = 0 := by
    simp only [aadPad, List.length_append,Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have xMod : X.length % 16 = 0 := by change ((aadPad a) ++ _).length % 16 = 0; rw [List.length_append,length_bytesAt]; omega
  have absorbed : Absorbed s.mem (St+16) (St+32) H X := by
    unfold Absorbed
    rw [Proof.Gcm.whole_of_mod xMod,List.take_length,List.drop_length,xMod]
    refine ⟨?_,rfl⟩
    unfold X
    rw [hy,Proof.Gcm.blocksAt_eq,Proof.Gcm.blocks_append alMod]
    simp only [Spec.Gcm.ghash,Proof.Gcm.ghashFrom_append]
  have w := he.perm.wR (d := 352) (n := 8) (by decide)
  obtain ⟨b,run,e23,e24,r⟩ : ∃ b, runBlock isa [.ldr .x .x23 .x19 Impl.AesGcm.AArch64.DirectGather.hashO,
      .sub .x .x24 .x26 .x23] s = some b ∧ b.gpr .x23 = O + BitVec.ofNat 64 (16*j) ∧
      b.gpr .x24 = BitVec.ofNat 64 (n-16*j) ∧ Regs [.x23,.x24] s b := by
    refine ⟨_, by arun [he.x19,Impl.AesGcm.AArch64.DirectGather.hashO,w], ?_⟩
    have load : s.mem.read (W+352#64) 8 = O+BitVec.ofNat 64 (16*j) := slot
    refine ⟨by simp [gpr_write,load], ?_, by others_tac,rfl,rfl,rfl,rfl⟩
    simp only [gpr_write,ite_true,ite_false,reduceCtorEq,BitVec.setWidth_eq,load,x26]
    rw [Offset.add_sub_add_left, ofNat_sub hb data.lt]
  refine WP.seq (WP.of_runBlock ⟨b,run,?_⟩)
  refine WP.seq (WP.mono (WP.with_rdwr (absorbRemainder_ok L v (he.of_regs r) e23 e24
    ((data.drop hb).of_eq r.rd r.wr) (r.mem ▸ key) xMod)) fun c ⟨⟨q,off⟩,rc,wc⟩ => ?_)
  have f := q.frame
  rw [r.mem] at f
  have acc := q.abs (r.mem ▸ absorbed)
  have split : X ++ bytesAt b.mem (O+BitVec.ofNat 64 (16*j)) (n-16*j) = aadPad a ++ bytesAt s.mem O n := by
    unfold X
    rw [r.mem,List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' hb]
  rw [split] at acc
  have hf : blockAt c.mem (Ctx+240) = H := (blockAt_frame f (ctx_absFrame L (.inr rfl))).trans key
  obtain ⟨d,run',e25,r'⟩ : ∃ d, runBlock isa [mov .x25 .x24] c = some d ∧
      d.gpr .x25 = BitVec.ofNat 64 ((n-16*j)%16) ∧ Regs [.x25] c d := by
    refine ⟨_,by arun [],?_⟩
    exact ⟨by simp [gpr_write,off],by others_tac,rfl,rfl,rfl,rfl⟩
  refine WP.seq (WP.of_runBlock ⟨d,run',?_⟩)
  refine WP.mono (WP.with_rdwr (flush_ok L (.inr rfl) v (q.env.of_regs r') (fun _ _ => rfl)
    (x := aadPad a ++ bytesAt s.mem O n) e25 (by rw [List.length_append,length_bytesAt]; omega)
    (r'.mem ▸ hf))) fun t ⟨⟨end_,_,done⟩,rt,wt⟩ => ?_
  have hfinal := done (r'.mem ▸ acc)
  rw [padBoth] at hfinal
  have f' := end_.frame
  rw [r'.mem] at f'
  refine ⟨end_.env, (end_.kept _ (by decide)).trans ((r'.others _ (by decide)).trans ((q.kept _ (by decide)).trans
    (r.others _ (by decide)))), hfinal.whole_eq (Proof.Gcm.length_padded _ _),
    (f.mono (fun _ hx => List.mem_append_left _ hx)).trans (f'.mono (fun _ hx => List.mem_append_right _ hx)),
    rt.trans (r'.rd.trans (rc.trans r.rd)), wt.trans (r'.wr.trans (wc.trans r.wr))⟩

abbrev generalScratch (Wn : Nat) (W : Addr) : List Region := [⟨W,128⟩,⟨W+BitVec.ofNat 64 512,Wn-512⟩]

theorem scratchFrame_Of {Wn : Nat} {W : Addr} {m m' : Mem} {rs : List Region} (f : Frame rs m m')
    (bounds : ∀ r ∈ rs, (∃ d n, r = ⟨W + BitVec.ofNat 64 d,n⟩ ∧ d+n ≤ 128) ∨
      (∃ n, r = ⟨W + BitVec.ofNat 64 512,n⟩ ∧ n ≤ Wn-512)) : Frame (generalScratch Wn W) m m' :=
  f.sub fun r hr => by
    rcases bounds r hr with ⟨d,n,rfl,h⟩|⟨n,rfl,h⟩
    · exact ⟨_,List.mem_cons_self ..,Offset.sub_base _ h⟩
    · exact ⟨_,by simp [generalScratch],Region.sub_prefix h⟩

theorem scratchFrame_Aad {Wn : Nat} {W : Addr} {m m' : Mem}
    (f : Frame (aadFrame (W+BitVec.ofNat 64 16) W) m m') (hw : 768 ≤ Wn) : Frame (generalScratch Wn W) m m' := by
  refine scratchFrame_Of f fun r hr => ?_
  simp only [aadFrame,frontFrame,j0Frame,tFrame,absFrame,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false,Offset.add_add] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | exact .inl ⟨_,_,rfl,by decide⟩ | exact .inr ⟨_,rfl,by omega⟩

theorem scratchFrame_tail {Wn : Nat} {W : Addr} {m m' : Mem}
    (f : Frame (tailFrame (W+BitVec.ofNat 64 16) W) m m') (hw : 768 ≤ Wn) : Frame (generalScratch Wn W) m m' := by
  refine scratchFrame_Of f fun r hr => ?_
  simp only [tailFrame,tFrame,absFrame,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false,
    Offset.add_add] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | exact .inl ⟨_,_,rfl,by decide⟩ | exact .inr ⟨_,rfl,by omega⟩

theorem scratchFrame_tag {Wn : Nat} {W : Addr} {m m' : Mem}
    (f : Frame (tagFrame Wn (W+BitVec.ofNat 64 16) W 0) m m') : Frame (generalScratch Wn W) m m' := by
  refine scratchFrame_Of f fun r hr => ?_
  simp only [tagFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl <;>
    first | exact .inl ⟨_,_,rfl,by decide⟩ | exact .inr ⟨_,rfl,Nat.le_refl _⟩

theorem scratchFrame_work {Wn : Nat} {W : Addr} {m m' : Mem} (f : Frame (generalScratch Wn W) m m')
    (hw : 768 ≤ Wn) : Frame [⟨W,Wn⟩] m m' := f.sub fun r hr => by
  simp only [generalScratch,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨_,List.mem_singleton_self _,Region.sub_prefix (by omega)⟩
  · exact ⟨_,List.mem_singleton_self _,Offset.sub_base _ (by omega)⟩

theorem protected_scratch {Wn : Nat} {W : Addr} (hW : Wn ≤ 2560) {d n : Nat} (lo : 128 ≤ d) (hi : d+n ≤ 512) :
    ∀ r ∈ generalScratch Wn W, (⟨W+BitVec.ofNat 64 d,n⟩ : Region).Disjoint r := by
  intro r hr; simp only [generalScratch,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact Offset.disjoint_base _ lo (by omega)
  · exact Offset.disjoint _ (.inl hi) (by omega) (by omega)

theorem scratch_slot {Wn : Nat} {W : Addr} {m m' : Mem} (f : Frame (generalScratch Wn W) m m')
    (hw : Wn ≤ 2560) {d : Nat} (lo : 128 ≤ d) (hi : d+8 ≤ 512) :
    m'.readW (W+BitVec.ofNat 64 d) 64 = m.readW (W+BitVec.ofNat 64 d) 64 :=
  f.readW (Region.contains_self _ _) (protected_scratch hw lo hi) (by decide)

abbrev finalCode (c : Callees) : Prog isa :=
  .seq (.block finPrep) <| .seq (tag c 0) (.block ([.ldr .x .x28 .x19 tlO] ++ tagOut ++ restore))

theorem finalCode_ok {wn R : Nat} {Ctx W O Tg : Addr} {s₀ s : State} {H J : Block} {aad cipher : List Byte}
    (v : GcmImpl) (L : Lay wn Ctx (W+16) W) (he : Env wn Ctx (W+16) W s₀.sp s)
    (h22 : s.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h25 : s.gpr .x25 = BitVec.ofNat 64 (s.gpr .x25).toNat := by simp)
    (al : s.mem.readW (W+224) 64 = BitVec.ofNat 64 aad.length)
    (len : s.mem.readW (W+240) 64 = BitVec.ofNat 64 cipher.length)
    (tg : s.mem.readW (W+248) 64 = Tg) (save : SavedAt s.mem W s₀)
    (out : Covers [⟨Tg,16⟩] s.wr) (tw : (⟨Tg,16⟩ : Region).Disjoint ⟨W,wn⟩)
    (ow : (⟨O,cipher.length⟩ : Region).Disjoint ⟨W,wn⟩) (ot : (⟨O,cipher.length⟩ : Region).Disjoint ⟨Tg,16⟩)
    (aadLt : aad.length < 2^64) (outLt : cipher.length < 2^64) (outData : bytesAt s.mem O cipher.length = cipher)
    (hk : blockAt s.mem (Ctx+240) = H) (hj : blockAt s.mem (W+16) = J)
    (hy : blockAt s.mem ((W+16)+16) = Spec.Gcm.ghash H (Spec.Gcm.blocks (Proof.Gcm.padded aad cipher)))
    (hv : v.ctr.scratch ≤ wn-512) :
    WP isa (finalCode v.callees) s fun u => GprAbi s₀ u ∧ bytesAt u.mem O cipher.length = cipher ∧
      bytesAt u.mem Tg 16 = Spec.Gcm.toBytes
        (Spec.Gcm.ghashFrom H (Spec.Gcm.ghash H (Spec.Gcm.blocks (Proof.Gcm.padded aad cipher)))
          [Spec.Gcm.ofBytes (Proof.Gcm.lensBlock aad.length cipher.length)] ^^^ ciphOf s.mem Ctx R J) := by
  have hw := L.hWn
  refine WP.seq (WP.mono (finPrep_ok he.x19 (covers_left he.perm.w) al len hw) fun b ⟨x26,x27,r⟩ => ?_)
  have eb := he.of_regs r
  refine WP.seq (WP.mono (WP.with_rdwr (tag_ok L v (.inl rfl) eb (fun _ _ => rfl)
    ((r.others _ (by decide)).trans h22) hR ((r.others _ (by decide)).trans h25) hv)) fun c ⟨q,rd,wr⟩ => ?_)
  have f := scratchFrame_tag q.frame
  rw [r.mem] at f
  have saved := save.frame f (protected_scratch hw.2 (by decide) (by decide))
  have hTag := q.out
  change bytesAt c.mem (W+0#64) 16 = _ at hTag
  change blockAt s.mem (Ctx + 240#64) = H at hk
  change blockAt s.mem ((W+16)+16#64) = _ at hy
  rw [BitVec.add_zero,r.mem,hk,hj,hy,x26,x27,toNat_ofNat_of_lt aadLt,toNat_ofNat_of_lt outLt] at hTag
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (ldr28_ok q.env ((scratch_slot f hw.2 (d := 248) (by decide) (by decide)).trans tg)) fun d ⟨x28,r'⟩ => ?_
  have ed := q.env.of_regs r'
  have writable : Covers [⟨Tg,16⟩] d.wr := by rw [r'.wr,wr,r.wr]; exact out
  rw [WP.block_append_iff]
  refine WP.mono (tagOut_ok ed.x19 x28 (covers_left ed.perm.w) writable
    (tw.sub_right (Region.sub_prefix (by omega))) ⟨by omega,hw.2⟩) fun t ⟨tag',ff,g,sp,rd',wr'⟩ => ?_
  have et := ed.keep (fun j hj => g _ (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide)) sp rd' wr'
  have S : SavedAt d.mem W s₀ := r'.mem ▸ saved
  have S' := S.frame ff fun rr hrr => by
    simp only [List.mem_singleton] at hrr; subst rr
    exact (tw.sub_right (Lay.wSub (d := 128) (by omega))).symm
  refine WP.mono (exit_ok et.x19 et.sp (covers_left et.perm.w) S' (by omega)) fun u ⟨abi,mem,_⟩ => ?_
  refine ⟨abi,?_,by rw [mem,tag',r'.mem,hTag]⟩
  rw [mem,bytesAt_frame ff (by simpa only [List.mem_singleton,forall_eq] using ot) (Nat.le_of_lt outLt),r'.mem,
    bytesAt_frame (scratchFrame_work f hw.1) (by simpa only [List.mem_singleton,forall_eq] using ow) (Nat.le_of_lt outLt),outData]

end VG.Proof.AesGcm.AArch64.DirectGather
