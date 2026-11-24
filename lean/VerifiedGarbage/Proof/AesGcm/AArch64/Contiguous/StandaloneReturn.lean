module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneFront
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneTag
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.Ctr

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.Impl.AesGcm.AArch64 VG.Spec.Gcm
open VG.Proof.Gcm (xorKs)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm.AArch64.Stitch (batchFrame)
variable {wn : Nat} {W : Addr} {s a b t z : State}

abbrev ptBytes (s : State) := bytesAt s.mem (s.gpr .x6) (stackArg s 0).toNat
abbrev ctBytes (s t : State) := bytesAt t.mem (s.gpr .x7) (stackArg s 0).toNat
abbrev origKey (s : State) := ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat

structure ReturnPrep (wn : Nat) (W : Addr) (s t : State) : Prop where
  j : blockAt t.mem (W+16#64) = J s
  key : ciphOf t.mem (s.gpr .x0) (s.gpr .x1).toNat = origKey s
  hash : ctxH t.mem (s.gpr .x0) = ctxH s.mem (s.gpr .x0)
  alen : t.mem.readW (W+224#64) 64 = s.gpr .x5
  len : t.mem.readW (W+240#64) 64 = stackArg s 0
  tag : t.mem.readW (W+248#64) 64 = stackArg s 1
  saved : SavedAt t.mem W s
  cipher : ctBytes s t = xorKs (origKey s) (inc32 (J s)) 0 (ptBytes s)

theorem after_slot {d k : Nat} (c : Inner wn W s) (start : 112 ≤ d) (stop : d+k ≤ 352) :
    ∀ r ∈ batchFrame wn (s.gpr .x7) (W+16#64) W (stackArg s 0).toNat,
      (⟨W+BitVec.ofNat 64 d,k⟩ : Region).Disjoint r := by
  have L := c.lay
  have bounds := L.hWn
  have sub : (⟨W+BitVec.ofNat 64 d,k⟩ : Region).Sub (workR wn W) := Offset.sub_base W (by omega)
  intro r hr
  simp only [batchFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact (c.dst.ok.w.sub_right sub).symm
  · exact (L.st_wn (by decide) (.inr ⟨by omega,by omega⟩)).symm
  · exact (L.st_wn (by decide) (.inr ⟨by omega,by omega⟩)).symm
  · exact Offset.disjoint W (.inl stop) (by omega) (by decide)
  · exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)

theorem after_j (c : Inner wn W s) :
    ∀ r ∈ batchFrame wn (s.gpr .x7) (W+16#64) W (stackArg s 0).toNat, (⟨W+16#64,16⟩ : Region).Disjoint r := by
  have L := c.lay
  have bounds := L.hWn
  intro r hr
  simp only [batchFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact (c.dst.ok.st.sub_right (Region.sub_prefix (by decide))).symm
  · exact st0_disj L (by decide) (by decide)
  · exact st0_disj L (by decide) (by decide)
  · exact st0_w L ⟨by decide,by change 352+8≤wn; omega⟩
  · exact st0_w L ⟨by decide,by omega⟩

theorem returnPrep (c : Inner wn W s) (f : FrontOut wn W s a)
    (e : EncOut wn (s.gpr .x1).toNat (stackArg s 0).toNat (s.gpr .x0) (W+16#64) W s.sp
      (s.gpr .x6) (s.gpr .x7) (inc32 (J s)) (aadHash s) a b)
    (pad : Frame (padFrame (W+16#64) W) b.mem t.mem) : ReturnPrep wn W s t := by
  have L := c.lay
  have bounds := L.hWn
  have pf := pad.sub (pad_sub _ _)
  have wpad : Frame [workR wn W] b.mem t.mem :=
    pf.sub fun r hr => ⟨_,.head _,frontFrame_work W bounds r (List.mem_append_left _ hr)⟩
  have onlyWork {r : Region} (h : r.Disjoint (workR wn W)) : ∀ q ∈ [workR wn W],r.Disjoint q :=
    by simpa only [List.mem_singleton,forall_eq] using h
  have inKey := ciph_frame f.frame (onlyWork L.cw') c.nr
  have keyApart := batch_apart bounds.1 c.dst.ctx L.cs L.cw'
  have key := (ciph_frame wpad (onlyWork L.cw') c.nr).trans ((ciph_frame e.frame keyApart c.nr).trans inKey)
  have sub := Lay.ctxSub (Ctx := s.gpr .x0) (d := 240) (n := 16) (by decide)
  have hr := L.cw'.sub_left sub
  have h := (blockAt_frame wpad (onlyWork hr)).trans ((blockAt_frame e.frame (fun r h => (keyApart r h).sub_left sub)).trans (blockAt_frame f.frame (onlyWork hr)))
  have ct := (bytesAt_frame wpad (onlyWork c.dst.ok.w) (Nat.le_of_lt c.dst.ok.lt)).trans e.cipher
  rw [inKey,bytesAt_frame f.frame (onlyWork c.src.w) (Nat.le_of_lt c.src.lt)] at ct
  have jp : blockAt t.mem (W+16#64) = blockAt b.mem (W+16#64) := by simpa using blockAt_frame pad (pad_blk L (d := 0) (.inl rfl))
  have slot (d : Nat) (hd : 112 ≤ d) (k : d+8≤352) :
      t.mem.readW (W+BitVec.ofNat 64 d) 64 = a.mem.readW (W+BitVec.ofNat 64 d) 64 :=
    (pf.readW (r := slotR W d) (Region.contains_self _ _) (slot_jf L hd (by omega)) (by decide)).trans
      (e.frame.readW (r := slotR W d) (Region.contains_self _ _) (after_slot c hd k) (by decide))
  exact ⟨jp.trans ((blockAt_frame e.frame (after_j c)).trans f.j),key,h,
    (slot 224 (by decide) (by decide)).trans f.alen,(slot 240 (by decide) (by decide)).trans f.len,
    (slot 248 (by decide) (by decide)).trans f.tag,
    (f.saved.frame e.frame (after_slot c (by decide : 112 ≤ 128) (by decide : 128+88≤352))).frame pf (saved_j0Frame L),ct⟩

abbrev sealed (s t z : State) :=
  encryptWith (origKey s) (ctxH s.mem (s.gpr .x0)) 16 (nonce s) (ptBytes s) (aadBytes s) =
    (ctBytes s t,bytesAt z.mem (stackArg s 1) 16)

theorem finishReturn (c : Inner wn W s) (h : ReturnPrep wn W s t) (env : Env wn (s.gpr .x0) (W+16#64) W s.sp z)
    (direct : Frame (directFrame wn (W+16#64) W (stackArg s 1)) t.mem z.mem) (post : sealed s t z) :
    WP isa (.block restore) z (fun x => GprAbi s x ∧ result s x) := by
  have L := c.lay
  have bounds := L.hWn
  have sch : ∀ r ∈ directFrame wn (W+16#64) W (stackArg s 1),(savedR W).Disjoint r := by
    intro r hr
    rcases List.mem_append.mp hr with h|h
    · exact saved_tFrame L (.inr rfl) r h
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl
      · exact (st0_saved L).symm
      · exact (c.tagData.ok.w.sub_right (Offset.sub_base W (by change 128+88≤wn; omega))).symm
      · exact Offset.disjoint W (.inl (by decide)) (by decide) (by omega)
  have dst : ∀ r ∈ directFrame wn (W+16#64) W (stackArg s 1),(dstR s).Disjoint r := by
    intro r hr
    rcases List.mem_append.mp hr with h|h
    · have rsub := pad_sub (W+16#64) W r (List.mem_append_right _ h)
      obtain ⟨q,hq,sub⟩ := rsub
      exact (c.dst.ok.w.sub_right (frontFrame_work W bounds q (List.mem_append_left _ hq))).sub_right sub
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl
      · exact c.dst.ok.st.sub_right (Region.sub_prefix (by decide))
      · exact c.dstTag
      · exact c.dst.ok.w.sub_right (Offset.sub_base W (by omega))
  have hold := bytesAt_frame direct dst (Nat.le_of_lt c.dst.ok.lt)
  refine (exit_ok env.x19 env.sp (covers_left env.perm.w) (h.saved.frame direct sch) (by omega)).mono ?_
  intro x ⟨abi,mem,_,_,_⟩
  exact ⟨abi,by unfold result; rw [mem,hold]; exact post⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
