module

-- separate module: Ciphertext, tag and ABI restoration use only the functional payload postcondition. They can be checked separately from taint certificates.

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Body
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt

/-! # Ciphertext, tag and ABI of contiguous RISC-V seal -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH encryptWith blockAt)

private theorem saved_payload {p : Args} {s : State} (h : ArgsAt p s) :
    ∀ r ∈ payloadFrame p.st p.work p.dst p.sp p.len.toNat,(savedR p.work).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · rcases List.mem_append.mp hr with hr|hr
    · simp only [dataFrame,maskFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl
      · exact (h.dstWrite.ok.w.sub_right (Lay.wSub (by decide))).symm
      · exact saved_w (by decide) (.inr (by decide))
      · simpa using h.lay.saved_st (d := 0) (k := 16) (by decide)
      · exact saved_w (by decide) (.inr (by decide))
    · exact saved_crFrame h.lay h.dstWrite r hr
  · exact saved_otFrame h.lay h.stk (.inl rfl) r hr

private theorem payload_apart {p : Args} {R : Region}
    (d : R.Disjoint ⟨p.dst,p.len.toNat⟩) (w : R.Disjoint ⟨p.work,2560⟩) (b : R.Disjoint (below p.sp 2048)) :
    ∀ r ∈ payloadFrame p.st p.work p.dst p.sp p.len.toNat,R.Disjoint r := by
  intro r hr
  have work {d k : Nat} (hk : d+k≤2560) := w.sub_right (Lay.wSub (W := p.work) hk)
  rcases List.mem_append.mp hr with hr|hr
  · rcases List.mem_append.mp hr with hr|hr
    · simp only [dataFrame,maskFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl
      · exact d
      · exact work (by decide)
      · exact work (by decide)
      · exact work (by decide)
    · simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact d
      · exact (work (d := 16) (k := 80) (by decide)).sub_right (Offset.sub_base p.st (d := 48) (n := 32) (k := 80) (by decide))
      · exact work (by decide)
  · simp only [otFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact work (by decide)
    · exact work (by decide)
    · exact work (by decide)
    · exact work (by decide)
    · exact b

theorem exitArgs {p : Args} {s u t : State} (h : ArgsAt p s) (prep : Prepared p s u)
    (z : PayloadOut (p.regs true) p.sp p.src p.dst p.rounds (ctxH s.mem p.ctx) (bytesAt s.mem p.aad p.aadLen.toNat) u t)
    (rd : t.rd=u.rd) (wr : t.wr=u.wr) : ExitArgs t s p.work p.tag := by
  have both := z.env.sp.trans h.sp.symm
  have w := wr.trans prep.keeps.wr
  have r := rd.trans prep.keeps.rd
  refine ⟨z.env.fr .s0 (by decide),both,by rw [both];have := h.shape.spAlign;omega,
    by rw [both,r,w];exact h.shape.slot 1 (by decide),?_,by rw [r,w];exact covers_left h.shape.work,
    h.shape.workAlign,w ▸ h.tagWrite,h.tagWork,prep.saved.frame z.frame (saved_payload h)⟩
  rw [both]
  have sub : (⟨s.sp+BitVec.ofNat 64 8,8⟩ : Region).Sub (args s 4) :=
    Offset.sub s.sp (d := 8) (n := 8) (e := 0) (k := 32) (by decide) (by decide)
  exact (slot_keep z.frame (fun q hq => (payload_apart h.stackData h.stackWork h.stackBelow q hq).sub_left sub)).trans
    ((slot_keep prep.frame (fun q hq => (before_apart h.stackWork h.stackBelow q hq).sub_left sub)).trans h.shape.tagPtr)

abbrev BodyOut (p : Args) (s t : State) := abiPreserved s t ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
  (bytesAt t.mem p.dst p.len.toNat,bytesAt t.mem p.tag 16) =
    encryptWith (ciphOf s.mem p.ctx p.rounds) (ctxH s.mem p.ctx) 16 (bytesAt s.mem p.iv p.ivLen.toNat)
      (bytesAt s.mem p.src p.len.toNat) (bytesAt s.mem p.aad p.aadLen.toNat) ∧
  Frame (beforeFrame p ++ payloadFrame p.st p.work p.dst p.sp p.len.toNat ++ [⟨p.tag,16⟩]) s.mem t.mem

theorem body_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {p : Args} {s : State} (h : ArgsAt p s) :
    WP isa VG.Impl.AesGcm.RISCV64.Contiguous.body s (BodyOut p s) := by
  apply WP.seq
  refine WP.mono (begin_wp h) fun t a => WP.seq (WP.mono (aad_wp h a) fun v b => ?_)
  apply WP.seq
  refine WP.mono (prepare_wp h b) fun u prep => WP.seq (WP.mono (WP.with_rdwr' (payload_wp h.lay prep.payload prep.cut))
    fun x ⟨out,rd,wr⟩ => WP.mono (exit_wp (exitArgs h prep out rd wr)) fun y ⟨abi,tag,fr,r,w⟩ => ?_)
  have ct : bytesAt y.mem p.dst p.len.toNat=bytesAt x.mem p.dst p.len.toNat := bytesAt_frame fr (fun q hq => by
    obtain rfl := List.mem_singleton.mp hq;exact h.tagData.symm) (Nat.le_of_lt p.len.isLt)
  have src := bytesAt_frame prep.frame (before_apart h.srcRead.w (h.sp ▸ h.srcRead.sk)) (Nat.le_of_lt p.len.isLt)
  have cx := ciph_frame prep.frame (before_apart h.lay.cw' h.stk.c) h.rounds
  have data := out.data
  have mac := out.tag
  simp only [Args.regs] at data mac
  rw [cx,prep.j,src] at data
  rw [cx,prep.j] at mac
  refine ⟨abi,r.trans (rd.trans prep.keeps.rd),w.trans (wr.trans prep.keeps.wr),?_,?_⟩
  · rw [Proof.Gcm.encryptWith_eq,ct,data,tag,mac,Proof.Gcm.fullTag_eq,←data]; simp only [length_bytesAt]
  · exact ((prep.frame.mono (fun _ hr => List.mem_append_left _ (List.mem_append_left _ hr))).trans
      (out.frame.mono (fun _ hr => List.mem_append_left _ (List.mem_append_right _ hr)))).trans
        (fr.mono (fun _ hr => List.mem_append_right _ hr))

end VG.Proof.AesGcm.RISCV64.Contiguous
