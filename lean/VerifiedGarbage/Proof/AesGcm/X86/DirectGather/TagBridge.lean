module

public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Start
public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Step
import VerifiedGarbage.Proof.Framework.Offset

public section
namespace VG.Proof.AesGcm.X86.DirectGather
open VG VG.X86 VG.Impl.AesGcm.X86
open VG.Spec.Gcm
open VG.Proof.Gcm

/-- Unary facts shared by the functional and leakage proofs at the text boundary. -/
structure BeforeText (p : BitVec 32 × (Nat → BitVec 32)) (s e ent aad u : State) : Prop where
  initial : Gather.Lay s
  prepared : Prepared s e
  publicArgs : pubSw 12 8 e=p
  entry : OEnt 2560 p e ent
  auth : OAad 2560 p e aad
  authFrame : Frame (oF 2560 p) ent.mem aad.mem
  setup : SetupPost aad (work s) (SP s) 9 10 rO tglO (w64 (work s)+BitVec.ofNat 64 xlO) u

theorem BeforeText.start {p s e ent aad u} (h : BeforeText p s e ent aad u) :
  TextInput 2560 (text s) u ∧ TextAt 2560 (text s) u (Spec.Gcm.inc32 (jOf p e)) 0 u ∧
    Frame [Gather.stkR s] s.mem u.mem := by
  obtain ⟨l,hp,rfl,he,ha,fr,setup⟩ := h
  have b := begun l hp he ha fr setup
  refine ⟨b.input,?_,start_frame l hp b.frame⟩
  exact ⟨b.input.env,rfl,rfl,by simpa [text,Text.desc,atByte] using b.ptr,b.count,b.off,
    Frame.refl _ _,b.ctr,rfl⟩

abbrev TagBridge : Prop := ∀ {p s e ent aad u y z}, BeforeText p s e ent aad u →
  TextInput 2560 (text s) u → TextAt 2560 (text s) u (Spec.Gcm.inc32 (jOf p e)) (text s).count y →
  SetupPost y (work s) (SP s) 6 7 dataO lenO (w64 (SP s)) z → OTIn 2560 p e z

private theorem loopFrame {s t u : State}
    (h : SetupPost t (work s) (SP s) 9 10 rO tglO (w64 (work s)+BitVec.ofNat 64 xlO) u) :
    Frame ((text s).frame 2560 (Gather.L s)) t.mem u.mem :=
  h.frame.mono (by simp [slotSetupFrame,Text.frame,crFrame,text,rO,tglO,xlO])

theorem tagFrame {s u z : State}
    (h : SetupPost u (work s) (SP s) 6 7 dataO lenO (w64 (SP s)) z) :
    Frame ((text s).frame 2560 (Gather.L s)) u.mem z.mem := by
  apply h.frame.sub
  intro r hr
  simp only [slotSetupFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨w64 (work s)+168#64,8⟩,by simp [Text.frame,text],Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨w64 (work s)+168#64,8⟩,by simp [Text.frame,text],Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_,by simp [Text.frame,text],fun _ h => h⟩

private theorem argAfterText {s e u y : State} {icb : Block} (l : Gather.Lay s) (h : Prepared s e)
    (b : Begun s e u) (atEnd : TextAt 2560 (text s) u icb (text s).count y) (i : Nat) (hi : i<11) :
    y.mem.readW (argA (SP s) i) 32=arg s (Impl.AesGcm.X86.DirectGather.sourceSlot i) := by
  have op := h.op l
  have sp : e.gpr .esp=SP s := h.regs _ (by decide)
  have sub := argA_sub (n:=12) (SP:=SP s) (i:=i) (by omega_using [hi]) (by rw [←sp]; exact op.fg)
  have wa := op.w_a.symm
  have da := op.d_a.symm
  rw [←argsR_eq,sp,h.scratch] at wa
  rw [←argsR_eq,sp,h.arg_eq 6 (by decide),h.arg_eq 7 (by decide)] at da
  have out : Text.Outside 2560 (text s) ⟨argA (SP s) i,4⟩ := by
    refine ⟨wa.sub_left sub,?_,?_⟩
    · change Region.Disjoint ⟨addr (SP s) (4+4*i),4⟩ ⟨w64 (SP s),4⟩
      rw [norm l (by omega_using [hi])]
      exact Offset.disjoint_base _ (by omega) (by omega_using [hi])
    · change Region.Disjoint ⟨addr (SP s) (4+4*i),4⟩ (below (SP s) 32)
      rw [norm l (by omega_using [hi]),←below_eq (sp ▸ op.sp)]
      change Region.Disjoint _ ⟨w64 (SP s)-BitVec.ofNat 64 32,32⟩
      rw [show w64 (SP s)+BitVec.ofNat 64 (4+4*i) =
        (w64 (SP s)-BitVec.ofNat 64 32)+BitVec.ofNat 64 (32+(4+4*i)) by
          rw [BitVec.ofNat_add (n:=64) (x:=32) (y:=4+4*i),←BitVec.add_assoc,BitVec.sub_add_cancel]]
      exact Offset.disjoint_base _ (by omega) (by omega_using [hi])
  have fr := atEnd.frame
  rw [b.input.total] at fr
  change (argsR (SP s) 12).Disjoint ⟨w64 (text s).O,(text s).len⟩ at da
  exact (fr.readW (r:=⟨argA (SP s) i,4⟩) (w:=32) (Region.contains_self _ _) (out.frame b.input.lay (da.sub_left sub)) (by decide)).trans
    (private_arg_kept l h b.frame i hi)

private theorem authBlock {s e u : State} (h : Prepared s e) (p : TextInput 2560 (text s) u)
    (G : OL 2560 (pub e)) {d : Nat} (hd : d+16≤48) :
    ∀ r ∈ (text s).frame 2560 (Gather.L s),
      (⟨w64 (stOf ((pub e).2 8))+BitVec.ofNat 64 d,16⟩ : Region).Disjoint r := by
  have z := h.params
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · apply st_crFrameO G hd r
    simpa only [z.w,z.sp,z.d,z.l,text,Text.st,Gather.L] using hr
  · rw [st_eq G,z.w]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (p.argW.sub_right (Lay.wSub (by omega_using [hd]))).symm
    all_goals exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)

theorem tagBridge_ok : TagBridge := by
  intro p s e ent aad u y z hb input hy setup
  obtain ⟨l,h,rfl,he,ha,fa,ls⟩ := hb
  let p := pub e
  have b := begun l h he ha fa ls
  have par := h.params
  have G := (h.op l).ol rfl (by decide) (p:=pub e) rfl
  have ft := hy.frame
  rw [input.total] at ft
  have fr : Frame ((text s).frame 2560 (Gather.L s)) aad.mem z.mem :=
    ((loopFrame ls).trans ft).trans (tagFrame setup)
  have o := ha.o
  have regs {r : Reg} (hr : r≠.eax) : z.gpr r=y.gpr r := setup.regs r hr
  have rd := setup.rd.trans (hy.rd.trans ls.rd)
  have wr := setup.wr.trans (hy.wr.trans ls.wr)
  have sl {k : Nat} (lo : 128≤k) (hi : k+4≤240)
      (n1 : k+4≤160 ∨ 164≤k) (n2 : k+4≤168 ∨ 176≤k)
      (n3 : k+4≤180 ∨ 184≤k) (n4 : k+4≤196 ∨ 200≤k) :
      slotv z.mem ((pub e).2 8) k=slotv aad.mem ((pub e).2 8) k := by
    rw [par.w]; exact slot_frame fr (input.frameSlot (Nat.le_refl _) lo hi n1 n2 n3 n4)
  have ctx : ∀ r ∈ (text s).frame 2560 (Gather.L s), (⟨w64 ((pub e).2 0),256⟩ : Region).Disjoint r := by
    rw [par.c]; exact input.outsideCtx.frame input.lay input.ctxDst
  have ad : ∀ r ∈ (text s).frame 2560 (Gather.L s),
      (⟨w64 ((pub e).2 4),((pub e).2 5).toNat⟩ : Region).Disjoint r := by
    change ∀ r ∈ _, (⟨w64 (arg e 4),(arg e 5).toNat⟩ : Region).Disjoint r
    rw [h.arg_eq 4 (by decide),h.arg_eq 5 (by decide)]
    exact ((zones l).outside l.ba).frame input.lay l.ad
  have htag : OEnv 2560 (pub e) e z := by
    refine ⟨o.env.keep ?_ ?_ ?_ rd wr ?_,⟨?_,o.rounds.2⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_ ,
      rd.trans o.rd,wr.trans o.wr,?_,?_,?_⟩
    · rw [regs (by decide),hy.env.ebp,o.env.ebp,par.w]; rfl
    · rw [regs (by decide),hy.env.esi,o.env.esi,par.w]; rfl
    · rw [regs (by decide),hy.env.esp,o.env.esp,par.sp]; rfl
    · exact sl (k:=ctxO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact (sl (k:=roundsO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans o.rounds.1
    · exact (sl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans o.aadO
    · exact (sl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans o.alO
    · rw [par.w,par.d]
      exact setup.first.trans (argAfterText l h b hy 6 (by decide))
    · rw [par.w,par.l]
      exact setup.second.trans (argAfterText l h b hy 7 (by decide))
    · exact (sl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans o.zO
    · exact (sl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans o.nlO
    · exact (sl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans o.tp
    · rcases o.saved with ⟨rbx,rsi,rdi,rbp⟩
      exact ⟨(sl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rbx,
        (sl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rsi,
        (sl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rdi,
        (sl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rbp⟩
    · rw [par.sp]; exact setup.zero.trans h.ret.symm
    · rw [ciph_frame fr ctx G.rounds]; exact o.ciph
    · rw [show Hk z.mem ((pub e).2 0)=Hk aad.mem ((pub e).2 0) from
        blockAt_frame fr (fun r hr => (ctx r hr).sub_left (Lay.ctxSub (by decide)))]
      exact o.hk
    · rw [bytesAt_frame fr ad (by omega_using [G.fa])]; exact o.aad
    · rw [rd,wr]; exact o.nIn
    · rw [rd,wr]; exact o.aIn
    · rw [rd,wr]; exact o.dIn
  refine ⟨htag,?_,?_⟩
  · have j := blockAt_frame fr (authBlock h input G (d:=0) (by decide))
    rw [BitVec.add_zero] at j
    exact j.trans ha.j
  · have hl : (xA (pub e) e).length%16=0 := by
      simp only [xA,List.length_append,length_bytesAt,length_zeros]
      exact length_pad_mod _
    exact ha.y.congr (blockAt_frame fr (authBlock h input G (d:=16) (by decide))) (by rw [hl]; rfl)

end VG.Proof.AesGcm.X86.DirectGather
end
