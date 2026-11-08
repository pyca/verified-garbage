module

public import VerifiedGarbage.Proof.Scrypt.X86_64.PackedHalf
public import VerifiedGarbage.Proof.Scrypt.X86_64.BlockMixCT
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section
namespace VG.Proof.Scrypt.X86_64.Packed
open VG VG.X86_64 VG.Impl.Scrypt.X86_64.Packed
open VG.Proof.MdStream.X86_64 (wp_mov wp_addi wp_subi)
open VG.Proof.Scrypt.X86_64.Retained (memWords)

structure Tail (s t : State) : Prop where
 mem : t.mem=s.mem
 rd : t.rd=s.rd
 wr : t.wr=s.wr
 rbx : t.gpr .rbx=s.gpr .rbx+128
 rbp : t.gpr .rbp=s.gpr .rbp+64
 r12 : t.gpr .r12=s.gpr .r12+64
 r14 : t.gpr .r14=s.gpr .r14-1
 r15 : t.gpr .r15=s.gpr .r12
 keep : ∀ r, r≠.rbx → r≠.rbp → r≠.r12 → r≠.r14 → r≠.r15 → t.gpr r=s.gpr r
 zf : t.zf=some (s.gpr .r14-1==0)

theorem tail_ok (s : State) : WP isa (.block tail) s fun t => Tail s t ∧ t.xmm=s.xmm := by
 refine WP.mono (WP.vecKeep (by decide) ?_) fun _ h => ⟨h.1,h.2.1⟩
 unfold tail
 refine wp_mov fun a ua _ _ => wp_addi fun b ub => wp_addi fun c uc =>
  wp_addi fun d ud => wp_subi fun t ut hz => WP.block_nil ?_
 refine ⟨ut.mem.trans (ud.mem.trans (uc.mem.trans (ub.mem.trans ua.mem))),
  ut.rd.trans (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd))),
  ut.wr.trans (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr))),?_,?_,?_,?_,?_,?_,?_⟩
 · rw [ut.other _ (by decide),ud.other _ (by decide),uc.other _ (by decide),ub.gpr,ua.other _ (by decide)]; rfl
 · rw [ut.other _ (by decide),ud.other _ (by decide),uc.gpr,ub.other _ (by decide),ua.other _ (by decide)]; rfl
 · rw [ut.other _ (by decide),ud.gpr,uc.other _ (by decide),ub.other _ (by decide),ua.other _ (by decide)]; rfl
 · rw [ut.gpr,ud.other _ (by decide),uc.other _ (by decide),ub.other _ (by decide),ua.other _ (by decide)]; rfl
 · rw [ut.other _ (by decide),ud.other _ (by decide),uc.other _ (by decide),ub.other _ (by decide),ua.gpr]
 · intro r hb hp h12 h14 h15
   rw [ut.other r h14,ud.other r h12,uc.other r hp,ub.other r hb,ua.other r h15]
 · rw [hz,ud.other _ (by decide),uc.other _ (by decide),ub.other _ (by decide),ua.other _ (by decide)]; rfl

namespace BM
open VG.Proof.Scrypt.X86_64.BlockMix

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop extends BlockMix.Inv s₀ k s where
 words : Holds (memWords s.mem (xP s₀ k)) s

theorem Inv.frame_registers {s₀ s t : State} {k : Nat} (h : BlockMix.Inv s₀ k s) (f : F s t) :
 BlockMix.Inv s₀ k t := by
 rcases f with ⟨hg,hm,hr,hw⟩
 exact ⟨h.k_le,hr.trans h.rd,hw.trans h.wr,by rw [hg]; exact h.rsp,
  by rw [hg]; exact h.rbx,by rw [hg]; exact h.rbp,by rw [hg]; exact h.r12,
  by rw [hg]; exact h.r13,by rw [hg]; exact h.r14,by rw [hg]; exact h.r15,
  by rw [hm]; exact h.frame,by rw [hm]; exact h.saved,by rw [hm]; exact h.done,
  by rw [hm]; exact h.x⟩

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
 WP isa (.block (VG.Impl.Scrypt.X86_64.bmPrologue++load)) s₀ (Inv s₀ 0) := by
 rw [WP.block_append_iff]
 refine WP.mono (BlockMix.prologue_ok hp) fun s h => ?_
 have hi : InRegions (s.rd++s.wr) (s.gpr .r15) 64 := by
  rw [h.rd,h.wr,h.r15,xP,hp.rd,hp.wr]
  exact ⟨BlockMix.bR s₀,by simp,BlockMix.in_b hp (o:=128*rr s₀-64) (n:=64) (by have := hp.pos; omega)⟩
 exact WP.mono (load_ok hi) fun t ⟨f,ht⟩ =>
  ⟨Inv.frame_registers h f,by rw [f.mem]; rw [h.r15] at ht; exact ht⟩

end BM
end VG.Proof.Scrypt.X86_64.Packed

@[expose] public section
namespace VG.Proof.Scrypt.X86_64.Packed.BM
open VG VG.X86_64 VG.Impl.Scrypt.X86_64.Packed
open VG.Proof.Scrypt.X86_64.BlockMix
open VG.Proof.Scrypt.X86_64.Retained (memWords core_bytes)
open VG.Proof.Scrypt.Memory (InRegions.of_mem)

attribute [local irreducible] memWords

theorem body_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k<rr s₀) {s : State} (h : Inv s₀ k s) :
 WP isa body s fun t => Inv s₀ (k+1) t ∧ t.zf=some (BitVec.ofNat 64 (rr s₀-k)-1==0) := by
 have ie : InRegions (s.rd++s.wr) (bB s₀ k) 64 := by
  rw [h.rd,h.wr,hp.rd,hp.wr]
  exact ⟨BlockMix.bR s₀,by simp,in_b hp (by omega)⟩
 have we : InRegions s.wr (yE s₀ k) 64 := by
  rw [h.wr,hp.wr]
  exact ⟨yR s₀,by simp,in_y hp (by omega)⟩
 refine WP.seq (WP.mono (Packed.half_ok h.words (by rw [h.rbx]; exact plus_zero _) ie h.rbp we) fun a ha => ?_)
 obtain ⟨wa,ma,fa,ga,ra,wra⟩ := ha
 have ba : Spec.Scrypt.bytesAt a.mem (yE s₀ k) 64 = Spec.Scrypt.salsa
   (Spec.Pbkdf2.xorBytes (Spec.Scrypt.bytesAt s.mem (xP s₀ k) 64) (Spec.Scrypt.bytesAt s.mem (bB s₀ k) 64)) :=
  core_bytes (fun j hj => by have := congrArg (fun v : Vector Spec.Scrypt.Word 16 => v[j]'hj) ma; simpa only [memWords,Vector.getElem_ofFn] using this)
 have baddr : plus (bB s₀ k) 64 = bP s₀ + BitVec.ofNat 64 (64*(2*k+1)) := by
  rw [plus,bB,Memory.add_ofNat]; congr 2; omega
 let src := bP s₀+BitVec.ofNat 64 (64*(2*k+1))
 have io : InRegions (a.rd++a.wr) src 64 := by
  rw [ra,wra,h.rd,h.wr,hp.rd,hp.wr]
  exact ⟨BlockMix.bR s₀,by simp,in_b hp (by omega)⟩
 have wo : InRegions a.wr (yO s₀ k) 64 := by
  rw [wra,h.wr,hp.wr]
  exact ⟨yR s₀,by simp,in_y hp (by omega)⟩
 have wa' : Holds (memWords a.mem (yE s₀ k)) a := by rw [ma]; exact wa
 refine WP.seq (WP.mono (Packed.half_ok wa' (by rw [ga,h.rbx]; exact baddr) io
  (by rw [ga,h.r12]) wo) fun b hb => ?_)
 obtain ⟨wb,mb,fb,gb,rb,wrb⟩ := hb
 have bb : Spec.Scrypt.bytesAt b.mem (yO s₀ k) 64 = Spec.Scrypt.salsa
   (Spec.Pbkdf2.xorBytes (Spec.Scrypt.bytesAt a.mem (yE s₀ k) 64) (Spec.Scrypt.bytesAt a.mem src 64)) :=
  core_bytes (fun j hj => by have := congrArg (fun v : Vector Spec.Scrypt.Word 16 => v[j]'hj) mb; simpa only [memWords,Vector.getElem_ofFn] using this)
 have ffa : Frame [slot s₀ (64*k),⟨sc s₀,64⟩,stkR s₀] s.mem a.mem :=
  fa.mono (fun R hr => by simp only [List.mem_singleton] at hr; subst R; simp [slot,yE])
 have ffb : Frame [slot s₀ (64*(rr s₀+k)),⟨sc s₀,64⟩,stkR s₀] a.mem b.mem :=
  fb.mono (fun R hr => by simp only [List.mem_singleton] at hr; subst R; simp [slot,yO])
 obtain ⟨ff,saved,done⟩ := mem_ok hp hk h.toInv ffa ba ffb bb
 have wb' : Holds (memWords b.mem (yO s₀ k)) b := by rw [mb]; exact wb
 refine WP.mono (Packed.tail_ok b) fun t ⟨ht,hx⟩ => ?_
 have nextb : bB s₀ k+128=bB s₀ (k+1) := by
  change bP s₀+BitVec.ofNat 64 (128*k)+BitVec.ofNat 64 128=_
  rw [Memory.add_ofNat]; congr 2
 have nexte : yE s₀ k+64=yE s₀ (k+1) := by
  change yP s₀+BitVec.ofNat 64 (64*k)+BitVec.ofNat 64 64=_
  rw [Memory.add_ofNat]; congr 2
 have nexto : yO s₀ k+64=yO s₀ (k+1) := by
  change yP s₀+BitVec.ofNat 64 (64*(rr s₀+k))+BitVec.ofNat 64 64=_
  rw [Memory.add_ofNat]; congr 2
 have nextc : BitVec.ofNat 64 (rr s₀-k)-1=BitVec.ofNat 64 (rr s₀-(k+1)) := by
  have := r_lt hp
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub,Memory.toNat_ofNat_lt (by omega),Memory.toNat_ofNat_lt (by omega),
    show (1 : BitVec 64).toNat=1 from rfl]
  omega
 have zf := ht.zf
 rw [gb,ga,h.r14] at zf
 refine ⟨⟨⟨by omega,ht.rd.trans (rb.trans (ra.trans h.rd)),ht.wr.trans (wrb.trans (wra.trans h.wr)),
  ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩,zf⟩
 · rw [ht.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),gb,ga]; exact h.rsp
 · rw [ht.rbx,gb,ga,h.rbx,nextb]
 · rw [ht.rbp,gb,ga,h.rbp,nexte]
 · rw [ht.r12,gb,ga,h.r12,nexto]
 · rw [ht.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),gb,ga]; exact h.r13
 · rw [ht.r14,gb,ga,h.r14,nextc]
 · rw [ht.r15,gb,ga,h.r12]; rfl
 · rw [ht.mem]; exact ff
 · rw [ht.mem]; exact saved
 · rw [ht.mem]; exact done
 · rw [ht.mem]; change Spec.Scrypt.bytesAt b.mem (yO s₀ k) 64=_
   rw [(done k (by omega)).2]; rfl
 · rw [ht.mem]; exact wb'.keep (fun _ _ => congrFun hx _)

end VG.Proof.Scrypt.X86_64.Packed.BM
