module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.DirectGather.BindLoop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.RISCV64.DirectGather.CT
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Impl.AesGcm.RISCV64.Fn
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.DirectGather.CT
meta import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
import VerifiedGarbage.Proof.Gcm.SealGather

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather
open VG VG.RISCV64
open GatherBs (Bs Cnt Dst dR stkR)

theorem beforeTagApart {s e : State} (h : Caller s) (he : Ready s e) {k n : Nat}
    (end_ : k+n ≤ 4672) (ctr : k+n ≤ 2168 ∨ 2200 ≤ k)
    (subkey : k+n ≤ 2616 ∨ 4664 ≤ k) (cursors : k+n ≤ 2352 ∨ 2368 ≤ k) :
    ∀ r ∈ (loopArgs s e).frame, (⟨Bs s + BitVec.ofNat 64 k,n⟩ : Region).Disjoint r := by
  intro r hr
  change r ∈ [⟨Dst s,GatherBs.gl s (Cnt s)⟩,⟨e.gpr .s1+48,32⟩,⟨e.gpr .s0+512,2048⟩,
    ⟨e.gpr .s0+248,8⟩,⟨e.gpr .s0+256,8⟩] at hr
  rw [he.s1,he.s0,h.layout.hgl] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact h.layout.bd.sub_left (Offset.sub_base _ end_)
  all_goals simp only [statePtr,work_eq h.layout,Offset.add_add]
  · rw [BitVec.add_assoc]
    exact Offset.disjoint (Bs s) (e := 2168) ctr (by omega_using [end_]) (by decide)
  · rw [BitVec.add_assoc]
    exact Offset.disjoint (Bs s) (e := 2616) subkey (by omega_using [end_]) (by decide)
  · rw [BitVec.add_assoc]
    exact Offset.disjoint (Bs s) (e := 2352) (by omega_using [cursors]) (by omega_using [end_]) (by decide)
  · rw [BitVec.add_assoc]
    exact Offset.disjoint (Bs s) (e := 2360) (by omega_using [cursors]) (by omega_using [end_]) (by decide)

theorem tagArgLoop {s e : State} (h : Caller s) (he : Ready s e) :
    ∀ r ∈ (loopArgs s e).frame, (⟨frameSp s + 16,8⟩ : Region).Disjoint r := by
  rw [frameSp_eq h.layout,show (Bs s + 2064 +16) = Bs s + BitVec.ofNat 64 2080 from Offset.add_add (Bs s) 2064 16]; exact beforeTagApart (k := 2080) h he (by decide) (.inl (by decide)) (.inl (by decide)) (.inl (by decide))

theorem stateLoop {s e : State} (h : Caller s) (he : Ready s e) {d n : Nat} (hn : d+n ≤ 48) :
    ∀ r ∈ (loopArgs s e).frame, (⟨statePtr s + BitVec.ofNat 64 d,n⟩ : Region).Disjoint r := by
  simp only [statePtr,work_eq h.layout,Offset.add_add]
  apply beforeTagApart h he <;> omega_using [hn]

theorem savedLoop {s e : State} (h : Caller s) (he : Ready s e) :
    ∀ r ∈ (loopArgs s e).frame, (savedR (work s)).Disjoint r := by
  simp only [savedR,work_eq h.layout,Offset.add_add]
  apply beforeTagApart h he <;> decide

theorem tagFrameSub {s : State} (h : Caller s) :
    ∀ r ∈ otFrame (statePtr s) (work s) 0 (frameSp s), r.Sub (stkR s) := by
  intro r hr
  simp only [otFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact fun a ha => scratch_sub h a (Offset.sub_base (work s) (by decide : 16+48 ≤ 2560) a ha)
  · exact fun a ha => scratch_sub h a (Offset.sub_base (work s) (by decide : 96+16 ≤ 2560) a ha)
  · exact fun a ha => scratch_sub h a (Offset.sub_base (work s) (by decide : 0+16 ≤ 2560) a ha)
  · exact fun a ha => scratch_sub h a (Offset.sub_base (work s) (by decide : 512+2048 ≤ 2560) a ha)
  · exact below_sub h

theorem tagArgOT {s : State} (h : Caller s) :
    ∀ r ∈ otFrame (statePtr s) (work s) 0 (frameSp s), (⟨frameSp s+16,8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [otFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  all_goals rw [frameSp_eq h.layout,show (Bs s + 2064 +16) = Bs s + BitVec.ofNat 64 2080 from Offset.add_add (Bs s) 2064 16]
  · simp only [statePtr,work_eq h.layout,Offset.add_add]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  all_goals first | rw [work_eq h.layout,Offset.add_add]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
                  | rw [← frameSp_eq h.layout,below_eq h]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)

end VG.Proof.AesGcm.RISCV64.DirectGather

end

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather
open VG VG.RISCV64 VG.Spec.Gcm VG.Proof.Gcm VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open GatherBs (C Rn Cnt L Dst Tg pt)
abbrev ciphertext (s : State) := gctr (ctxCiph s.mem (C s) (Rn s)) (inc32 (J s)) (pt s (Cnt s))
abbrev authTag (s : State) := fullTag (ctxCiph s.mem (C s) (Rn s)) (H s) (nonce s) (aadBytes s) (ciphertext s)

structure Tagged (s z : State) : Prop extends ExitInput s z where
  saved : SavedAt z.mem (DirectGather.work s) s
  data : bytesAt z.mem (Dst s) (L s) = ciphertext s
  output : bytesAt z.mem (DirectGather.work s) 16 = authTag s

theorem tag_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s e t : State} (h : Caller s) (he : Ready s e)
    (ht : LoopAt (loopArgs s e) e (Cnt s) t) : WP isa (oneTagB true 0) t (Tagged s) := by
  obtain ⟨⟨V,v2,v1,v0,v3,v7,v10,v11,env,_,dw,_,dest⟩,bk⟩ := tagInput h he ht
  change V .s1 = statePtr s at v1
  have layout := (layoutOf h).v v2 v1 v0
  have hc := inputLoopApart h he (r := GatherBs.cR s) (by simp [inputs])
  have hashKey : blockAt t.mem (V .s2 + 240) = H s := by
    rw [v2]; exact (blockAt_frame ht.frame (fun r hr => (hc _ hr).sub_left (Lay.ctxSub (d := 240) (by decide)))).trans he.hashKey
  have small := Nat.mod_lt (aadBytes s ++ zeros (padLen (aadBytes s).length)).length (by decide : 0 < 16)
  have abs := he.abs.congr (blockAt_frame ht.frame (stateLoop h he (d := 16) (by decide)))
    (bytesAt_frame ht.frame (stateLoop h he (d := 32) (by omega_using [small])) (by omega_using [small]))
  rw [← v1] at abs
  have data := dw
  change DataOk (statePtr s) (work s) t (Dst s) (L s) at data
  rw [← v1,← v0] at data
  change DataOk _ _ t (Dst s) (stackArg s 1).toNat at data
  rw [← v11] at data
  have key := bk
  rw [← v7,← v2,← v1,← v0] at key
  have tag := oneTagB_ok (bs := true) layout (o := 0) (.inl rfl) env v3 h.layout.hR hashKey
    (by rw [v10]; exact (length_bytesAt ..).symm) abs data (v0 ▸ dest) (fun _ => key)
  refine WP.mono (WP.with_rdwr' tag) fun z ⟨oz,_,wr⟩ => ?_
  have f := oz.frame
  rw [v1,v0] at f
  have d := ht.output
  change bytesAt t.mem (Dst s) (GatherBs.gl s (Cnt s)) = gctr (ciphOf e.mem (e.gpr .s2) (Rn s)) (inc32 (J s)) (pt s (Cnt s)) at d
  have ce := ciph_keep (c := C s) he.frame (fun r hr => (List.mem_singleton.mp hr) ▸ h.layout.bc.symm) h.layout.hR
  rw [h.layout.hgl,he.s2,ce] at d
  have j : blockAt t.mem (statePtr s) = J s := by
    rw [blockAt_frame ht.frame (by simpa using stateLoop h he (d := 0) (n := 16) (by decide)),he.j]
  refine ⟨⟨oz.env.s0.trans v0,oz.env.sp,wr.trans (ht.wr.trans he.wr),
    (slot_keep f (tagArgOT h)).trans ((slot_keep ht.frame (tagArgLoop h he)).trans he.tagPtr)⟩,
    (he.saved.frame ht.frame (savedLoop h he)).frame f (saved_otFrame (layoutOf h) (stackOf h) (.inl rfl)),?_,?_⟩
  · rw [bytesAt_frame f (fun r hr => h.layout.bd.symm.sub_right (tagFrameSub h r hr)) (Nat.le_of_lt (stackArg s 1).isLt)]
    exact d
  · have tagBytes := oz.out
    rw [v0,v1,v2,v11,BitVec.add_zero,j,ciph_frame ht.frame hc h.layout.hR,ce,← Proof.Gcm.fullTag_eq] at tagBytes
    change bytesAt z.mem (work s) 16 = fullTag _ _ _ _ (bytesAt t.mem (Dst s) (L s)) at tagBytes
    rw [d] at tagBytes; exact tagBytes

end VG.Proof.AesGcm.RISCV64.DirectGather

end


/-! # Calling convention, constant time and residue for direct gather seal -/

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.RISCV64.Scrub VG.Impl.AesGcm.RISCV64 VG.Impl.AesGcm.RISCV64.DirectGather
open VG.Proof.AesGcm.RISCV64.GatherBs
open VG.Spec.Aes (bytesAt)

abbrev BodyPost (s z : State) :=
  (∀ r ∈ preserved, z.gpr r = s.gpr r) ∧ z.gpr .ra = s.gpr .ra ∧ gatherPost s z

theorem direct_wp (bodyWP : ∀ {s t : State}, Caller s → Prepared s t → WP isa body t (BodyPost s))
    {s : State} (hs : gatherPre s) : WP isa sealGather s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := caller hs
  have lim := h.layout.w₁
  refine WP.allocLe (by decide) (by omega : 2608 ≤ s.sp.toNat) ?_
  obtain ⟨prep,done⟩ := prepared_run h.layout
  refine WP.seq ⟨_,_,Exec.block_iff.mpr prep,?_⟩
  refine WP.mono (WP.with_rdwr (bodyWP h done)) fun z ⟨⟨g,ra,post⟩,_,_,sp⟩ m u fm => ?_
  refine ⟨⟨g,?_,ra⟩,?_⟩
  · change z.sp + BitVec.ofNat 64 2608 = s.sp
    rw [sp,done.sp]; exact BitVec.sub_add_cancel _ _
  · have sub : Region.Sub ⟨frameSp s,2608⟩ (stkR s) := by
      rw [frameSp_eq h.layout]; exact Offset.sub_base _ (by decide : 2064+2608≤4672)
    change VG.Spec.Gcm.encryptWith _ _ _ _ _ _ = (bytesAt m (Dst s) (L s),bytesAt m (Tg s) 16)
    have fr : Frame [⟨frameSp s,2608⟩] z.mem m := fm
    rw [bytesAt_frame fr (fun r hr => (List.mem_singleton.mp hr) ▸ h.layout.bd.symm.sub_right sub)
      (Nat.le_of_lt (stackArg s 1).isLt),
      bytesAt_frame fr (fun r hr => (List.mem_singleton.mp hr) ▸ h.layout.bt.symm.sub_right sub) (by decide)]
    exact post

theorem direct_verified (bodyWP : ∀ {s t : State}, Caller s → Prepared s t → WP isa body t (BodyPost s))
    (ct : ConstantTime isa gatherPre gatherPub sealGather) :
    Verified target sealGather (Proof.AesGcm.sealGatherBitslicedRoundsContract abi 4672) :=
  by
    apply Verified.of_correct (k := GatherBs.gatherBsRISCV64) (T := target) (c := sealGather) _ ct gather_implies
    intro s h
    exact direct_wp (s := s) bodyWP h

theorem direct_scrubbed (v : Verified target sealGather (Proof.AesGcm.sealGatherBitslicedRoundsContract abi 4672)) :
    VerifiedScrubbed target Impl.AesGcm.RISCV64.Fn.sealGatherBs (Spec.Gcm.sealGatherBitslicedContract abi 4672) 0 :=
  verifiedScrubbedSel (api := Spec.Gcm.sealGatherBitslicedApi) (W := 4672)
    { code := sealGather, verified := Proof.AesGcm.sealGatherBitsliced_keyed v }
    [(2048, [(0, 256)]), (2048, [(0, 256)]), (160, [(0, 20)])] []
    (gatherBsOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

end VG.Proof.AesGcm.RISCV64.DirectGather

end

/-! # Write the authentication tag and restore the caller's registers -/

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open GatherBs (Tg Dst L tgR dR gatherPost)

theorem exit_wp {s t : State} (h : Caller s) (v : Tagged s t) : WP isa exitCode t (BodyPost s) := by
  unfold exitCode exitHead
  rw [List.append_assoc, WP.block_append_iff]
  refine Steps.wp_addSp (imm := 0) (by decide) fun x ux => ?_
  have al := (stackOf h).al
  refine Steps.wp_ld (a := frameSp s+16) (off := 16) (by decide)
    (by rw [ux.gpr,BitVec.add_zero,v.sp]; rfl) (Spill.al8 (d := 16) (by omega) (by decide))
    (by rw [ux.wr]; apply in_left; rw [v.wr]; exact ⟨_,.head _,
      Offset.contains_base _ (by decide : 16+8 ≤ 2608) (by decide)⟩) fun y uy => WP.block_nil ?_
  have hT : y.gpr .s9 = Tg s := uy.gpr.trans (ux.mem ▸ v.tag)
  have hW : y.gpr .s0 = work s :=
    (uy.other .s0 (by decide)).trans ((ux.other .s0 (by decide)).trans v.work)
  have wr : y.wr = (allocated s).wr := uy.wr.trans (ux.wr.trans v.wr)
  have cov : Covers [tgR s] y.wr :=
    covers_mem (wr ▸ List.mem_cons_of_mem _ (h.layout.pre.2.1 ▸ List.mem_cons_of_mem _ (.head _)))
  have apart := (h.layout.bt.sub_left (scratch_sub h))
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.copyBytes_ok (tmp := .t0) (src := .s0) (dst := .s9) (soff := 0) (doff := 0) (n := 16)
    (by decide) (by decide) (by decide) (by decide) (fun i hi => ?_) (fun i hi => ?_) (fun i hi bad => ?_))
    fun z cp => ?_
  · rw [Nat.zero_add,hW]; exact in_left (in_off (coversWork wr) (by omega) (by decide))
  · rw [Nat.zero_add,hT]; exact in_off (p := Tg s) (k := 16) cov (by omega) (by decide)
  · rw [Nat.zero_add,hW,hT,BitVec.add_zero] at bad
    exact apart _ (Offset.contains_base _ (by omega) (by omega)) bad
  have ztag : bytesAt z.mem (Tg s) 16 = authTag s := by
    refine Eq.trans ?_ v.output
    unfold bytesAt
    apply List.map_congr_left
    intro i hi
    have b := cp.copied i (List.mem_range.mp hi)
    simpa only [hT,hW,Nat.zero_add,uy.mem,ux.mem] using b
  have fr := cp.frame
  rw [hT,BitVec.add_zero] at fr
  have sv : SavedAt z.mem (work s) (allocated s) := by
    have saved := v.saved
    have same : y.mem = t.mem := uy.mem.trans ux.mem
    rw [← same] at saved
    exact saved.frame fr (fun r hr => (List.mem_singleton.mp hr) ▸ apart.sub_left (Lay.wSub (by decide)))
  have ct : bytesAt z.mem (Dst s) (L s) = ciphertext s := by
    have apartTag : ∀ r ∈ [tgR s], (dR s).Disjoint r :=
      fun r hr => (List.mem_singleton.mp hr) ▸ h.outputsApart
    rw [bytesAt_frame (p := Dst s) (n := L s) fr apartTag (Nat.le_of_lt (stackArg s 1).isLt),
      uy.mem,ux.mem]
    exact v.data
  have sp : z.sp = frameSp s := cp.sp.trans (uy.sp.trans (ux.sp.trans v.sp))
  have ptr : z.gpr .s0 = work s := (cp.gpr .s0 (by decide)).trans hW
  have writable : Covers [⟨work s,2560⟩] z.wr := coversWork (s := s) (cp.wr.trans wr)
  have finish := restore_ok (s := z) (s₀ := allocated s) (w := work s) ptr (layoutOf h).wal
    (covers_left writable) sv sp
  refine WP.mono finish fun y' ⟨abi,mem,_,_,_⟩ => ?_
  refine ⟨abi.1,abi.2.2,?_⟩
  unfold gatherPost
  rw [mem,ct,ztag]
  exact VG.Proof.Gcm.encryptWith_eq ..

end VG.Proof.AesGcm.RISCV64.DirectGather

end

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64.DirectGather

theorem body_wp [VG.Proof.Gcm.RISCV64.GhashLaw]
    {s t : State} (h : Caller s) (ht : Prepared s t) : WP isa body t (BodyPost s) := by
  refine WP.seq (WP.mono (start_wp h.layout ht) fun a ha => ?_)
  refine WP.seq (WP.mono (WP.with_rdwr' (aad_wp h ha)) fun b ⟨hb,rd,wr⟩ => ?_)
  refine WP.seq (WP.mono (ready_wp h ha hb rd wr) fun e he => ?_)
  refine WP.seq (WP.mono (pieces_wp (loopInput h he) (loopAt0 h he)) fun u hu => ?_)
  exact WP.seq (WP.mono (tag_wp h he hu) fun z hz => exit_wp h hz)

theorem timing [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa GatherBs.gatherPre GatherBs.gatherPub sealGather :=
  complete_ct fun _ _ _ h he ht => WP.mono (tag_wp h he ht) fun _ hz => hz.toExitInput

theorem sealGather_scrubbed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    VerifiedScrubbed target Impl.AesGcm.RISCV64.Fn.sealGatherBs (Spec.Gcm.sealGatherBitslicedContract abi 4672) 0 :=
  direct_scrubbed (direct_verified body_wp timing)

end VG.Proof.AesGcm.RISCV64.DirectGather

end
