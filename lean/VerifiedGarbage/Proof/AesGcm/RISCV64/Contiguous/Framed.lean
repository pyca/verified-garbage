module

-- separate module: The complete functional and two-run framed body are shared premises for the outer scrubbing proof.

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Call
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.Framework.RISCV64.CallWipe
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT

/-! # Public, contiguous RISC-V AES-GCM before the residue-clearing epilogue -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.StackScratch.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH encryptWith)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq)

abbrev framed : Prog isa := .frame (.alloc 2608) (.seq (.block (setArgsAt 2608 3 40)) VG.Impl.AesGcm.RISCV64.Contiguous.body) (.free 2608)
abbrev sealed (s t : State) := let p := callArgs s
  (bytesAt t.mem p.dst p.len.toNat,bytesAt t.mem p.tag 16) =
    encryptWith (ciphOf s.mem p.ctx p.rounds) (ctxH s.mem p.ctx) 16 (bytesAt s.mem p.iv p.ivLen.toNat)
      (bytesAt s.mem p.src p.len.toNat) (bytesAt s.mem p.aad p.aadLen.toNat)

theorem framed_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (h : Caller s) :
    WP isa framed s fun t => abiPreserved s t ∧ sealed s t := by
  let p := callArgs s
  obtain ⟨run,z⟩ := copied_run h
  refine WP.allocLe (by decide) (by have := h.space;omega : 2608≤s.sp.toNat) ?_
  refine WP.seq ⟨_,_,Exec.block_iff.mpr run,?_⟩
  refine WP.mono (body_wp (z.satisfies h)) fun u ⟨abi,_,_,out,_⟩ m _ fm => ?_
  have sep (r : Region) (hr : r∈p.regions) : r.Disjoint (frameR s) :=
    (h.apart r hr).sub_right (frame_sub s)
  have old (r : Region) (hr : r∈p.regions) : ∀ q∈[⟨(allocated s).sp,32⟩],r.Disjoint q := by
    intro q hq;obtain rfl := List.mem_singleton.mp hq;exact (sep r hr).sub_right (Region.sub_prefix (by decide))
  have dec (r : Region) (hr : r∈p.regions) : ∀ q∈[frameR s],r.Disjoint q :=
    fun q hq => List.mem_singleton.mp hq ▸ sep r hr
  have key := old ⟨p.ctx,256⟩ (by simp [Args.regions])
  have same (q : Region) (hr : q∈p.regions) (hn : q.len≤2^64) :=
    bytesAt_frame z.frame (old q hr) hn
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro r hr
    exact (abi.1 r hr).trans (z.regs r (fun e => by subst r;simp [preserved] at hr)
      (fun e => by subst r;simp [preserved] at hr))
  · change u.sp+BitVec.ofNat 64 2608=s.sp
    rw [abi.2.1,z.sp];exact BitVec.sub_add_cancel _ _
  · exact abi.2.2.trans (z.regs .ra (by decide) (by decide))
  · change (bytesAt m p.dst p.len.toNat,bytesAt m p.tag 16)=_
    change (_,_) = encryptWith (ciphOf (inner s).mem p.ctx p.rounds) (ctxH (inner s).mem p.ctx) 16
      (bytesAt (inner s).mem p.iv p.ivLen.toNat) (bytesAt (inner s).mem p.src p.len.toNat) (bytesAt (inner s).mem p.aad p.aadLen.toNat) at out
    have ch : ctxH (inner s).mem p.ctx=ctxH s.mem p.ctx := (ctxH_eq ..).trans (ctxH_keep z.frame key)
    rw [ciph_frame z.frame key h.rounds,ch,
      same ⟨p.iv,p.ivLen.toNat⟩ (by simp [Args.regions]) (Nat.le_of_lt p.ivLen.isLt),
      same ⟨p.aad,p.aadLen.toNat⟩ (by simp [Args.regions]) (Nat.le_of_lt p.aadLen.isLt),
      same ⟨p.src,p.len.toNat⟩ (by simp [Args.regions]) (Nat.le_of_lt p.len.isLt)] at out
    rw [bytesAt_frame fm (dec ⟨p.dst,p.len.toNat⟩ (by simp [Args.regions])) (Nat.le_of_lt p.len.isLt),
      bytesAt_frame fm (dec ⟨p.tag,16⟩ (by simp [Args.regions])) (by decide)]
    exact out

theorem framed_rel [VG.Proof.Gcm.RISCV64.GhashLaw] {s t : State} (a : Caller s) (b : Caller t)
    (pub : callArgs s=callArgs t) : RelCT isa (Eq2 s t) framed TT := by
  have shared := congrArg Args.sp pub
  obtain ⟨rs,es⟩ := copied_run a
  obtain ⟨rt,et⟩ := copied_run b
  have eqs : WP isa (.block (setArgsAt 2608 3 40)) (allocated s) (·=inner s) := ⟨_,_,Exec.block_iff.mpr rs,rfl⟩
  have eqt : WP isa (.block (setArgsAt 2608 3 40)) (allocated t) (·=inner t) := ⟨_,_,Exec.block_iff.mpr rt,rfl⟩
  refine (RelCT.alloc (bytes := 2608) (P := Eq2 s t) (R := TT)
    ((?_ : RelCT isa (Eq2 (allocated s) (allocated t)) _ TT).mono
      (fun x y ⟨i,j,⟨hi,hj⟩,hx,hy⟩ => by subst hi hj;exact ⟨hx,hy⟩) fun _ _ hp => hp)).mono
    (fun _ _ r => r) fun _ _ _ => trivial
  refine rel_seq ?_ eqs eqt fun x y (ex : x=inner s) (ey : y=inner t) => ?_
  · rintro _ _ tx ty _ _ ⟨rfl,rfl⟩ hx hy
    rw [Exec.block_iff,rs] at hx
    rw [Exec.block_iff,rt] at hy
    obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj hx)
    obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj hy)
    exact ⟨congrArg (fun u => setArgsTrace 2608 u 3) shared,trivial⟩
  · rw [ex,ey];exact body_rel (es.satisfies a) (pub ▸ et.satisfies b)

end VG.Proof.AesGcm.RISCV64.Contiguous
