module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Return
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.FinishCT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.StartCT
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealEntry
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Contract
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Verified
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Frame
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Verified
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks.Lit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Lit
import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-! # The direct gather entry meets its ciphertext, tag and ABI obligations -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Proof.AesGcm.PPC64LE.Gather
open VG.Impl.AesGcm.PPC64LE.DirectGather
open VG.Impl.StackScratch.PPC64LE

theorem release {s e y : State} (h : GatherSplit.Layout s) (p : Args s e) (abi : abiPreserved e y)
    (post : gatherPost s y) (m : Mem) (us : Nat → BitVec 64) (fl : Frame [stack s] y.mem m) :
    abiPreserved s { freed 1280 y with mem:=m,unknowns:=us } ∧ gatherPost s { freed 1280 y with mem:=m,unknowns:=us } := by
  have keep : ∀ r∈preserved,r≠Reg.r0 ∧ r≠Reg.r12 := by decide
  constructor
  · apply abiPreserved_lost
    simp only [abiPreserved,freed_gpr_eq,freed_sp_eq,freed_lr_eq]
    obtain ⟨gpr,sp,lr⟩ := abi
    refine ⟨fun r hr => (gpr r hr).trans (p.regs r (keep r hr).1 (keep r hr).2),?_,lr.trans p.lr⟩
    rw [sp,p.sp]; exact base_old s
  · have same {r : Region} (dis : r.Disjoint (stack s)) :
        VG.Spec.Aes.bytesAt m r.base r.len=VG.Spec.Aes.bytesAt y.mem r.base r.len :=
      List.map_congr_left fun i hi => lost_byte fl dis (List.mem_range.mp hi)
    have d := same (stack_disjoint h (r:=dR s) (by simp)).symm
    have t := same (stack_disjoint h (r:=tgR s) (by simp)).symm
    show _=(VG.Spec.Aes.bytesAt m (Dst s) (L s),VG.Spec.Aes.bytesAt m (Tg s) 16)
    change VG.Spec.Aes.bytesAt m (Dst s) (L s)=_ at d
    change VG.Spec.Aes.bytesAt m (Tg s) 16=_ at t
    rw [d,t]; exact post

theorem code_wp [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] {s : State}
    (h : GatherSplit.Layout s) : WP isa code s (fun y => abiPreserved s y ∧ gatherPost s y) := by
  obtain ⟨run,pp⟩ := args_run h
  unfold code withStackScratchArgs
  refine WP.alloc ⟨by decide,by decide,by decide⟩ (by omega_using [h.space]) ?_
  refine WP.seq (WP.mono (show WP isa (.block (setArgs 1280 3)) (allocated 1280 s) (Args s) from
    ⟨_,_,.block run,pp⟩) fun e p => ?_)
  unfold body
  refine WP.seq (WP.mono p.one fun t q => ?_)
  refine WP.seq (WP.mono (WP.with_rdwr (aad_wp h p q)) fun v ⟨oa,rd,wr,_⟩ => ?_)
  refine WP.seq (WP.mono (loadArgs_wp p q oa wr) fun u b => ?_)
  obtain init := start h p q oa rd wr b
  refine WP.seq (WP.mono (pieces_exact init.input init.atZero) fun z loop => ?_)
  refine WP.seq (WP.mono (init.finish h loop) fun x done => ?_)
  refine WP.mono (prepared h p init loop done) fun _ ⟨abi,post⟩ => release h p abi post

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # The timing contract of the direct gather implementation -/
@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Proof.AesGcm.PPC64LE.Gather
open VG.Impl.AesGcm.PPC64LE.DirectGather
open VG.Impl.StackScratch.PPC64LE
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq ct_of)

variable {s d e f u v z t : State}

theorem startPublic (hp : gatherPub s d) (p : Start s e u) (q : Start d f v) :
    LoopPublic (argsFor s u) (argsFor d v) u v := by
  obtain ⟨key,rnds,_,_,_,_,desc,n,sp,dst,_,_,mem⟩ := hp
  have bases : base s=base d := congrArg (· - 1280) sp
  refine ⟨bases,desc,congrArg BitVec.toNat n,⟨p.dst.trans (dst.trans q.dst.symm),
    p.r28.trans (rnds.trans q.r28.symm),p.r29.trans (key.trans q.r29.symm),
    p.r30.trans ((congrArg (· + 144) bases).trans q.r30.symm),
    p.r31.trans ((congrArg (· + 128) bases).trans q.r31.symm)⟩,?_⟩
  intro j hj
  change j<Cnt s*16 at hj
  change u.mem (Src s+BitVec.ofNat 64 j)=v.mem (Src s+BitVec.ofNat 64 j)
  have inside {s e u : State} (r : Start s e u) (hj : j<Cnt s*16) :
      s.mem (Src s+BitVec.ofNat 64 j)=u.mem (Src s+BitVec.ofNat 64 j) := by
    apply r.agree _ (List.mem_cons_self ..)
    exact Offset.contains_base _ (by omega_using [hj]) (by have f:=r.input.countFit; change Cnt s*16<2^64 at f; omega_using [f,hj])
  have hj' : j<Cnt d*16 := by simpa only [Cnt,n] using hj
  have ddesc : Src s=Src d := desc
  exact (inside p hj).symm.trans ((mem j hj).trans (by rw [ddesc]; exact inside q hj'))

theorem Start.returnI {b : Nat} (h : GatherSplit.Layout s) (p : Start s e u)
    (q : LoopAt (argsFor s u) u (Cnt s) b z) (f : Finished (argsFor s u) u z (iv s) (aad s) t) :
    SealEntry.ReturnI (work s) (Tg s) (base s) t := by
  refine ⟨(argsFor s u).finalV u,p.r31,p.tag,f.env,?_⟩
  rw [f.wr,q.wr,p.wr,h.base.pre.2.1]; exact Covers.of_mem (by simp)

variable [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]

theorem fromStart_rel (hp : gatherPub s d) (h : GatherSplit.Layout s) (g : GatherSplit.Layout d)
    (p : Start s e u) (q : Start d f v) :
    RelCT isa (Eq2 u v) (.seq pieces (.seq finish (.seq (.block Impl.AesGcm.PPC64LE.tagOut)
      (.block Impl.AesGcm.PPC64LE.restore)))) TT := by
  have pub := startPublic hp p q
  obtain ⟨_,_,_,_,_,aad,_,_,sp,_,_,tag,_⟩ := hp
  have count := pub.count
  have hash := (pub.hashed (Nat.le_refl _)).trans (congrArg ((argsFor d v).hashed v) count)
  refine rel_seq (pieces_rel pub p.input q.input p.atZero q.atZero) (pieces_exact p.input p.atZero)
    (pieces_exact q.input q.atZero) (fun z t x y => ?_)
  have y' := y
  rw [←hash] at y'
  have len {s e u : State} (h : GatherSplit.Layout s) (p : Start s e u) :
      ((argsFor s u).V .r23).toNat=(argsFor s u).pos u (Cnt s) := by
    change (u.gpr .r23).toNat=_; rw [p.len,p.total h]
  refine rel_seq (finish_rel pub p.input q.input x y' (p.r22.trans (aad.trans q.r22.symm)) (len h p) (len g q))
    (p.finish h x) (q.finish g y) (fun a b x' y' => ?_)
  have apart := (stack_disjoint h (r:=tgR s) (by simp)).symm
  have ret := q.returnI g y y'
  exact ct_at (SealEntry.return_ct (W:=work s) (T:=Tg s) (sp:=base s) (apart.sub_right (Offset.sub_base _ (by decide : 128+16≤1280))))
    (p.returnI h x x') (by simpa only [work,base,Tg,sp,tag] using ret)

theorem body_rel (hp : gatherPub s d) (h : GatherSplit.Layout s) (g : GatherSplit.Layout d) (p : Args s e) (q : Args d f) :
    RelCT isa (Eq2 e f) body TT := by
  have sp := hp.2.2.2.2.2.2.2.2.1
  have bs : base s=base d := congrArg (· - 1280) sp
  refine rel_seq (entry_rel hp p q) p.one q.one (fun t u x y => ?_)
  refine rel_seq (aad_rel hp h g p q x y) (WP.with_rdwr (aad_wp h p x)) (WP.with_rdwr (aad_wp g q y))
    (fun b c ⟨a,ar,aw,_⟩ ⟨j,jr,jw,_⟩ => ?_)
  have workEq : work s=work d := congrArg (· + 128) bs
  refine rel_seq (loadArgs_rel (a.env.sp.trans (p.sp.trans (bs.trans (q.sp.symm.trans j.env.sp.symm))))
    (a.env.r31.trans (x.r31.trans (workEq.trans (y.r31.symm.trans j.env.r31.symm)))))
    (loadArgs_wp p x a aw) (loadArgs_wp q y j jw) (fun v w b c => ?_)
  exact fromStart_rel hp h g (start h p x a ar aw b) (start g q y j jr jw c)

theorem timing : ConstantTime isa GatherSplit.contract.pre GatherSplit.contract.pub code := by
  refine VG.Proof.Gather.PPC64LE.ct_of fun s d hs hd hp => ?_
  have h := GatherSplit.layout_pre hs
  have g := GatherSplit.layout_pre hd
  have pub := Gather.gatherPub_of hp
  have sp := pub.2.2.2.2.2.2.2.2.1
  have bs : base s=base d := congrArg (· - 1280) sp
  refine (RelCT.alloc (bytes:=1280) (body:=.seq (.block (setArgs 1280 3)) body) (P:=Eq2 s d) (R:=TT) (fun a b ⟨rfl,rfl⟩ => sp)
    ((?_ : RelCT isa (Eq2 (allocated 1280 s) (allocated 1280 d)) _ TT).mono
      (fun a b ⟨s',d',⟨hs,hd⟩,ha,hb⟩ => by subst s' d'; exact ⟨ha,hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  obtain ⟨one,ea⟩ := args_run h
  obtain ⟨two,eb⟩ := args_run g
  refine rel_seq ?_ (WP.block ⟨_,one,ea⟩) (WP.block ⟨_,two,eb⟩)
    (fun _ _ p q => body_rel pub h g p q)
  rintro _ _ ta tb sa sb ⟨rfl,rfl⟩ ra rb
  rw [Exec.block_iff,one] at ra
  rw [Exec.block_iff,two] at rb
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ra)
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj rb)
  exact ⟨congrArg (fun ptr => setArgsTrace 1280 ptr 3) bs,trivial⟩

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Direct POWER8 AES-GCM gather seal -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE

theorem verified [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target Impl.AesGcm.PPC64LE.DirectGather.code GatherSplit.contract := by
  refine ⟨?_,timing,GatherSplit.sat_pre⟩
  intro s hs
  obtain ⟨t,z,ex,abi,post⟩ := code_wp (GatherSplit.layout_pre hs)
  exact ⟨t,z,ex,abi,Gather.gatherPost_of post⟩

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-!
# AES-GCM on PPC64LE, without secret residue

`vg_aes_gcm_init`, `vg_aes_gcm_seal`, `vg_aes_gcm_seal_gather`,
`vg_aes_gcm_open`, `vg_aes_gcm_open_to` and the streaming functions
`vg_aes_gcm_stream_init`, `_aad`, `_encrypt`, `_decrypt`, `_finish` and
`_verify`, each followed by `Impl.Scrub.PPC64LE.scrubTail`
(`PPC64LE.Scrub.verifiedScrubbedAll`), which clears the volatile registers and the
stack its frames used: each keeps its working space (the padded blocks,
the saved registers and the tags compared) in a frame it does not wipe
itself (`withStackScratch`, `withStackScratchArgs`, and the frames of
`vg_aes_gcm_seal_split` and `vg_aes_gcm_open_split`), which the tail wipes
whole. The functions they call need no working space, so `init` and the
streaming functions keep only 288 bytes, in a frame of 320; `seal`, `open`,
`seal_gather` and `open_to` keep their bulk helper's working space as well,
704 bytes at `W + 448` (its 640-byte kernel uses 624 of them), in frames of
1264 to 1552 bytes. Every one
may write every volatile register but CA (and `vg_aes_gcm_init` none of
`v12`–`v18`), so the tail clears them all. The functions they call
(`vg_aes_ctr32`, `vg_ghash`, `vg_aes_expand_key_scratch` and the split
blocks) are internal, and keep their code.

Their postconditions read the memory on return only within their buffers
(`PPC64LE.Scrub.PostOut`): the key context, the streaming state, the data,
the output and the tag, as the postconditions in terms of the key context
do (`Proof/AesGcm/Scratch.lean`), for every key whose context it is.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.AesGcm.PPC64LE
open VG.Proof.AesGcm (agree_of bytesAt_congr streamRepr_congr)

/-! ## Reading memory only within the buffers -/

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds (as RSA's,
`Rsa.PPC64LE.Scrub.postOut_of_local_pre`). -/
theorem postOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    have hpre' : Curry.apply (sig.words A.ptrBits) pre (vals s) (A.mem s) := by
      cases hal : A.alignsBufs
      · rw [hal] at hpre; exact hpre
      · rw [hal] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre' (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

/-- The `n` bytes at `p`, of a buffer of at least `n` bytes there on which
the memories agree. -/
theorem bytesAt_of {m₁ m₂ : Mem} {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n ≤ L) : Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n :=
  bytesAt_congr fun i hi => agree_of h i (by omega_using [hn, hi])

theorem len_le (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat := Nat.le_refl _

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Gcm.initContract PPC64LE.abi stack) (Spec.Gcm.initSig.retBits 64) :=
  postOut_of_local_pre ScrubAbi.plain (Proof.AesGcm.initPostOut_local _)

theorem streamInitOut (stack : Nat) :
    PostOut (Spec.Gcm.streamInitContract PPC64LE.abi stack) (Spec.Gcm.streamInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamInitPostOut_local _)

theorem streamAadOut (stack : Nat) :
    PostOut (Spec.Gcm.streamAadContract PPC64LE.abi stack) (Spec.Gcm.streamAadSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamAadPostOut_local _)

theorem streamEncryptOut (stack : Nat) :
    PostOut (Spec.Gcm.streamEncryptContract PPC64LE.abi stack) (Spec.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk _ _ iv a p hr hA hT _
      obtain ⟨g₁, g₂⟩ := h key hk iv a p hr hA hT
      exact ⟨streamRepr_congr (fun i hi => agree_of hb.2.1 i (by omega_using [hi])) g₁,
        (bytesAt_of hb.2.2 (len_le len)).trans g₂⟩

theorem streamDecryptOut (stack : Nat) :
    PostOut (Spec.Gcm.streamDecryptContract PPC64LE.abi stack) (Spec.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk _ _ iv a c hr hA hT _
      obtain ⟨g₁, g₂⟩ := h key hk iv a c hr hA hT
      exact ⟨streamRepr_congr (fun i hi => agree_of hb.2.1 i (by omega_using [hi])) g₁,
        (bytesAt_of hb.2.2 (len_le len)).trans g₂⟩

theorem streamFinishOut (stack : Nat) :
    PostOut (Spec.Gcm.streamFinishContract PPC64LE.abi stack) (Spec.Gcm.streamFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, tag], _ =>
      simp only [Spec.Gcm.streamFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk _ _ iv a c hr hA hT
      exact (bytesAt_of hb.2.2 (Nat.le_refl _)).trans (h key hk iv a c hr hA hT)

theorem streamVerifyOut (stack : Nat) :
    PostOut (Spec.Gcm.streamVerifyContract PPC64LE.abi stack) (Spec.Gcm.streamVerifySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, tag, tagLen], _ => exact h

theorem sealOut (stack : Nat) :
    PostOut (Spec.Gcm.sealContract PPC64LE.abi stack) (Spec.Gcm.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag], _ =>
      simp only [Spec.Gcm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      exact (h key hk).trans (Prod.ext (bytesAt_of hb.2.2.2.1 (len_le len)).symm
        (bytesAt_of hb.2.2.2.2 (Nat.le_refl _)).symm)

theorem openOut (stack : Nat) :
    PostOut (Spec.Gcm.openContract PPC64LE.abi stack) (Spec.Gcm.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag, tagLen], _ =>
      simp only [Spec.Gcm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      rw [show Spec.Aes.bytesAt m₂ (ArgWord.addr.ofRaw data) ((ArgWord.int abi.ptrBits).ofRaw len).toNat =
          Spec.Aes.bytesAt m₁ (ArgWord.addr.ofRaw data) ((ArgWord.int abi.ptrBits).ofRaw len).toNat from
        bytesAt_of hb.2.2.2.1 (len_le len)]
      exact h'

theorem sealGatherOut (stack : Nat) :
    PostOut (Spec.Gcm.sealGatherContract PPC64LE.abi stack) (Spec.Gcm.sealGatherSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, sc, dst, len, tag], _ =>
      simp only [Spec.Gcm.sealGatherSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk hl
      exact (h key hk hl).trans (Prod.ext (bytesAt_of hb.2.2.2.1 (len_le len)).symm
        (bytesAt_of hb.2.2.2.2 (Nat.le_refl _)).symm)

theorem openToOut (stack : Nat) :
    PostOut (Spec.Gcm.openToContract PPC64LE.abi stack) (Spec.Gcm.openToSig.retBits 64) :=
  postOut_of_local_pre ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, len, dst, dl, tag, tagLen], _ =>
      simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      obtain ⟨-, hd⟩ := hpre
      have hd' : ((ArgWord.int abi.ptrBits).ofRaw len).toNat ≤ dl.toNat := by
        rw [← hd]; exact len_le dl
      intro key hk
      have h' := h key hk
      rw [show Spec.Aes.bytesAt m₂ (ArgWord.addr.ofRaw dst) ((ArgWord.int abi.ptrBits).ofRaw len).toNat =
          Spec.Aes.bytesAt m₁ (ArgWord.addr.ofRaw dst) ((ArgWord.int abi.ptrBits).ofRaw len).toNat from
        bytesAt_of hb.2.2.2.2.1 hd']
      exact h'

/-! ## The registrations

Over the laws of `vg_ghash` (`Gcm.PPC64LE.GhashLaw`, `Gcm.PPC64LE.Vpmsum.FoldLaw`), which the registration
file gives, so that this module does not import their algebra. -/

variable [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]

/-- The volatile registers all but CA: what every function here may write. -/
def clearAll : Impl.Scrub.PPC64LE.Clear :=
  ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17,
      .v18, .v19]⟩

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] in
/-- `vg_aes_gcm_init` as emitted (`Impl.AesGcm.PPC64LE.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.AesGcm.PPC64LE.Fn.init
      (Spec.Gcm.initContract PPC64LE.abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.initApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r6 Impl.AesGcm.PPC64LE.init
      verified := init_framed }
    320 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (initOut _)
    (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] in
/-- `vg_aes_gcm_stream_init` as emitted (`Impl.AesGcm.PPC64LE.Fn.streamInit`)
meets its contract in constant time and returns without secret residue. -/
theorem streamInit_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.AesGcm.PPC64LE.Fn.streamInit
      (Spec.Gcm.streamInitContract PPC64LE.abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.streamInitApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r7 Impl.AesGcm.PPC64LE.streamInit
      verified := streamInit_framed }
    320 clearAll
    (streamInitOut _)
    (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] in
/-- `vg_aes_gcm_stream_aad` as emitted (`Impl.AesGcm.PPC64LE.Fn.streamAad`) meets
its contract in constant time and returns without secret residue. -/
theorem streamAad_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.AesGcm.PPC64LE.Fn.streamAad
      (Spec.Gcm.streamAadContract PPC64LE.abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.streamAadApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r8 Impl.AesGcm.PPC64LE.streamAad
      verified := streamAad_framed }
    320 clearAll
    (streamAadOut _)
    (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] in
/-- `vg_aes_gcm_stream_encrypt` as emitted
(`Impl.AesGcm.PPC64LE.Fn.streamEncrypt`) meets its contract in constant time
and returns without secret residue. -/
theorem streamEncrypt_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.AesGcm.PPC64LE.Fn.streamEncrypt
      (Spec.Gcm.streamEncryptContract PPC64LE.abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.streamEncryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r10 Impl.AesGcm.PPC64LE.streamEncrypt
      verified := Proof.AesGcm.streamEncrypt_keyed streamEncrypt_framed }
    320 clearAll
    (streamEncryptOut _)
    (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] in
/-- `vg_aes_gcm_stream_decrypt` as emitted
(`Impl.AesGcm.PPC64LE.Fn.streamDecrypt`) meets its contract in constant time
and returns without secret residue. -/
theorem streamDecrypt_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.AesGcm.PPC64LE.Fn.streamDecrypt
      (Spec.Gcm.streamDecryptContract PPC64LE.abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.streamDecryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r10 Impl.AesGcm.PPC64LE.streamDecrypt
      verified := Proof.AesGcm.streamDecrypt_keyed streamDecrypt_framed }
    320 clearAll
    (streamDecryptOut _)
    (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] in
/-- `vg_aes_gcm_stream_finish` as emitted (`Impl.AesGcm.PPC64LE.Fn.streamFinish`)
meets its contract in constant time and returns without secret residue. -/
theorem streamFinish_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.AesGcm.PPC64LE.Fn.streamFinish
      (Spec.Gcm.streamFinishContract PPC64LE.abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.streamFinishApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r9 Impl.AesGcm.PPC64LE.streamFinish
      verified := Proof.AesGcm.streamFinish_keyed streamFinish_framed }
    320 clearAll
    (streamFinishOut _)
    (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] in
/-- `vg_aes_gcm_stream_verify` as emitted (`Impl.AesGcm.PPC64LE.Fn.streamVerify`)
meets its contract in constant time and returns without secret residue. -/
theorem streamVerify_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.AesGcm.PPC64LE.Fn.streamVerify
      (Spec.Gcm.streamVerifyContract PPC64LE.abi 320) 32 :=
  verifiedScrubbedAll (api := Spec.Gcm.streamVerifyApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r10 Impl.AesGcm.PPC64LE.streamVerify
      verified := Proof.AesGcm.streamVerify_keyed streamVerify_framed }
    320 clearAll
    (streamVerifyOut _)
    (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] in
/-- `vg_aes_gcm_seal` as emitted (`Impl.AesGcm.PPC64LE.Fn.seal`) meets its
contract in constant time and returns without secret residue. -/
theorem seal_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    VerifiedScrubbed PPC64LE.target Impl.AesGcm.PPC64LE.Fn.seal
      (Spec.Gcm.sealContract PPC64LE.abi 1264) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.sealApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgs 1264 1 Impl.AesGcm.PPC64LE.SealFused.seal
      verified := Proof.AesGcm.seal_keyed seal_framed }
    1264 clearAll
    (sealOut _)
    (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] in
/-- `vg_aes_gcm_open` as emitted (`Impl.AesGcm.PPC64LE.Fn.open`) meets its
contract in constant time and returns without secret residue. -/
theorem open_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.AesGcm.PPC64LE.Fn.open
      (Spec.Gcm.openContract PPC64LE.abi 1280) 32 :=
  verifiedScrubbedAll (api := Spec.Gcm.openApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgs 1280 2 Impl.AesGcm.PPC64LE.open
      verified := Proof.AesGcm.open_keyed open_framed }
    1280 clearAll
    (openOut _)
    (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] in
/-- `vg_aes_gcm_seal_gather` as emitted (`Impl.AesGcm.PPC64LE.Fn.sealGather`)
meets its contract in constant time and returns without secret residue. -/
theorem sealGather_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    VerifiedScrubbed PPC64LE.target Impl.AesGcm.PPC64LE.Fn.sealGather
      (Spec.Gcm.sealGatherContract PPC64LE.abi 1552) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.sealGatherApi) {
      code := Impl.AesGcm.PPC64LE.DirectGather.code
      verified := Proof.AesGcm.sealGather_keyed DirectGather.verified }
    1280 clearAll
    (sealGatherOut _)
    (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] in
/-- `vg_aes_gcm_open_to` as emitted (`Impl.AesGcm.PPC64LE.Fn.openTo`) meets its
contract in constant time and returns without secret residue. -/
theorem openTo_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    VerifiedScrubbed PPC64LE.target Impl.AesGcm.PPC64LE.Fn.openTo
      (Spec.Gcm.openToContract PPC64LE.abi 1312) 32 :=
  verifiedScrubbedAll (api := Spec.Gcm.openToApi) {
      code := Impl.AesGcm.PPC64LE.OpenTo.openTo
      verified := Proof.AesGcm.openTo_keyed OpenTo.openTo_verified }
    1312 clearAll
    (openToOut _)
    (by dsimp only; lit_decide)

end VG.Proof.AesGcm.PPC64LE.Scrub
