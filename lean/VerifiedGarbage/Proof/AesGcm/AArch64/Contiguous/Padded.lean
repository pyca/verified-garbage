module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Standalone
public import VerifiedGarbage.Proof.AesGcm.AArch64.Absorb
public import VerifiedGarbage.Proof.AesGcm.AArch64.Flush
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.AArch64.RegUpd VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Absorbed)
open VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone
variable {wn n : Nat} {Ctx St W SP D : Addr} {k : Reg → Addr} {H : Block} {x : List Byte} {s : State}

/-- The final source fragment, padded to one full block, extends an aligned GHASH prefix. -/
theorem absorb_last {m m' : Mem} {y b : Addr} {pre part : List Byte}
    (ha : Absorbed m y b H pre) (aligned : pre.length % 16 = 0)
    (lo : 0 < part.length) (hi : part.length < 16)
    (hash : blockAt m' y = ghashFrom H (blockAt m y) [ofBytes (part ++ zeros (16-part.length))]) :
    Absorbed m' y b H ((pre ++ part) ++ zeros (padLen (pre ++ part).length)) := by
  have full : (part ++ zeros (16-part.length)).length = 16 := by
    simp only [List.length_append,Proof.Gcm.length_zeros]; omega
  have pad : padLen (pre ++ part).length = 16-part.length := by
    simp only [padLen,List.length_append]; omega
  rw [pad,List.append_assoc]
  apply Proof.Gcm.absorb_whole ha aligned (by rw [full])
  rw [Proof.Gcm.blocks_single full]
  exact hash

theorem hash_ok (v : GcmImpl) {P Y B S : Addr} {nb : Nat} (h : GhCall s P Y B S nb) :
    WP isa (hashBlocks v.callees) s (GhPost s P Y B S nb) := by
  refine WP.ite _ (eval_zero h.x3 (by have := h.n_lt; omega)) (fun z => ?_) (fun _ => gh_call v.gh h)
  have zn := of_decide_eq_true z
  refine WP.block_nil ⟨rfl,rfl,rfl,fun _ _ _ => rfl,Frame.refl _ _,?_⟩
  rw [zn]; rfl

/-- The complete blocks are consumed before the final source bytes are padded. -/
theorem initial
    (he : Env wn Ctx St W SP s) (hk : Kept k s) (src : s.gpr .x23 = D)
    (len : s.gpr .x24 = BitVec.ofNat 64 n) (data : DataOk wn St W s D n)
    (key : blockAt s.mem (Ctx+BitVec.ofNat 64 240) = H) (bound : x.length%16 = 0) :
    AbsMid wn Ctx St W SP k 16 H x D n (s.gpr .x25).toNat s.mem 0 s :=
  ⟨he,hk,Nat.zero_le _,by simpa using src,by simpa using len,by simp,data,key,
      fun h => by simpa [bytesAt] using h,.inr (by simpa using bound),Frame.refl _ _⟩

theorem whole_ok (L : Lay wn Ctx St W) (v : GcmImpl)
    (he : Env wn Ctx St W SP s) (hk : Kept k s) (src : s.gpr .x23 = D)
    (len : s.gpr .x24 = BitVec.ofNat 64 n) (data : DataOk wn St W s D n)
    (key : blockAt s.mem (Ctx+BitVec.ofNat 64 240) = H) (bound : x.length%16 = 0) :
    WP isa (.seq (.block (absSeg2 16)) (hashBlocks v.callees)) s
      (fun t => AbsMid wn Ctx St W SP k 16 H x D n (s.gpr .x25).toNat s.mem (16*(n/16)) t) := by
  have mid := initial he hk src len data key bound
  refine WP.seq ((absSeg2_ok L (.inr rfl) mid).mono fun u a => ?_)
  exact ((absCall2With_ok L (.inr rfl) a (hash_ok v a.call)).mono fun _ r => by simpa using r.1)

/-- Hash a nonempty tail from the original source into the padded scratch block. -/
theorem lastArgs_ok (L : Lay wn Ctx St W)
    (he : Env wn Ctx St W SP s) (hk : Kept k s) (src : s.gpr .x23 = D)
    (len : s.gpr .x24 = BitVec.ofNat 64 n) (hi : n<16)
    (data : DataOk wn St W s D n) :
    WP isa (.seq (.block [mov .x25 .x24]) (padSeg 16 [mov .x12 .x23])) s
      (Pad1 wn Ctx St W SP k 16 n D s.mem) := by
  have setup : WP isa (.block [mov .x25 .x24]) s (fun t => t.gpr .x25 = BitVec.ofNat 64 n ∧ Regs [.x25] s t) := by
    refine WP.of_runBlock ⟨_,by arun [],?_⟩
    refine ⟨?_,by others_tac,rfl,rfl,rfl,rfl⟩
    simpa [gpr_write] using len
  refine WP.seq (setup.mono fun t ⟨num,r⟩ => ?_)
  have kept := hk.of_eq fun q h => r.others q (by
    simp only [keptRegs,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> decide)
  have env := he.of_regs r
  have src' : t.gpr .x23 = D := (r.others _ (by decide)).trans src
  rw [←r.mem]
  apply padSeg_ok L (.inr rfl) env kept num hi
  · refine ⟨_,by arun [],?_⟩
    refine ⟨?_,by others_tac,rfl,rfl,rfl,rfl⟩
    simp [gpr_write,src']
  · rw [r.rd,r.wr]; exact data.rd
  · exact data.w.sub_right (Lay.wSub (by have := L.hWn; omega))

/-- Hash a nonempty tail from the original source into the padded scratch block. -/
theorem last_ok (L : Lay wn Ctx St W) (v : GcmImpl)
    (he : Env wn Ctx St W SP s) (hk : Kept k s) (src : s.gpr .x23 = D)
    (len : s.gpr .x24 = BitVec.ofNat 64 n) (lo : 0<n) (hi : n<16)
    (data : DataOk wn St W s D n) :
    WP isa (.seq (.block [mov .x25 .x24]) (.seq (padSeg 16 [mov .x12 .x23]) (ghCall v.callees))) s
      (TOut wn Ctx St W SP k 16 n
        (ghashFrom (blockAt s.mem (Ctx+BitVec.ofNat 64 240)) (blockAt s.mem (St+BitVec.ofNat 64 16))
          [ofBytes (bytesAt s.mem D n ++ zeros (16-n))]) s.mem) := by
  apply WP.assoc
  refine WP.seq ((lastArgs_ok L he hk src len hi data).mono fun t h => ?_)
  apply (padCall_ok L (.inr rfl) v h).mono
  intro u h
  simpa only [show ¬ n=0 by omega,↓reduceIte] using h

structure PaddedOut (wn : Nat) (C St W SP : Addr) (k : Reg → Addr) (H : Block) (txt : List Byte)
    (m : Mem) (t : State) : Prop where
  env : Env wn C St W SP t
  kept : Kept k t
  hash : Absorbed t.mem (St+BitVec.ofNat 64 16) (St+BitVec.ofNat 64 32) H (txt ++ zeros (padLen txt.length))
  frame : Frame (absFrame St W 16 ++ tFrame St W 16) m t.mem

theorem padded_ok (L : Lay wn Ctx St W) (v : GcmImpl)
    (he : Env wn Ctx St W SP s) (hk : Kept k s) (src : s.gpr .x23 = D)
    (len : s.gpr .x24 = BitVec.ofNat 64 n) (data : DataOk wn St W s D n)
    (key : blockAt s.mem (Ctx+BitVec.ofNat 64 240) = H) (bound : x.length%16 = 0)
    (ha : Absorbed s.mem (St+BitVec.ofNat 64 16) (St+BitVec.ofNat 64 32) H x) :
    WP isa (padded v.callees) s (PaddedOut wn Ctx St W SP k H (x++bytesAt s.mem D n) s.mem) := by
  unfold padded
  apply WP.assoc
  refine WP.seq ((whole_ok L v he hk src len data key bound).mono fun t h => ?_)
  let j := 16*(n/16)
  have le : j ≤ n := by dsimp [j]; omega
  have small : n-j < 16 := by dsimp [j]; omega
  have pre : (x ++ bytesAt s.mem D j).length%16=0 := by
    simp only [List.length_append,length_bytesAt,j]; omega
  have f : Frame (absFrame St W 16 ++ tFrame St W 16) s.mem t.mem :=
    h.frame.mono fun _ hr => List.mem_append_left _ hr
  have mid := h.abs ha
  change Absorbed t.mem _ _ H (x ++ bytesAt s.mem D j) at mid
  have xt : t.gpr .x24 = BitVec.ofNat 64 (n-j) := h.x24
  refine WP.ite _ (eval_zero xt (by omega)) (fun z => ?_) (fun z => ?_)
  · have zn := of_decide_eq_true z
    have je : n=j := by omega
    have hh : (x++bytesAt s.mem D n).length%16=0 := je ▸ pre
    refine WP.block_nil ⟨h.env,h.kept,?_,f⟩
    rw [Proof.Gcm.padLen_of_mod hh]
    rw [je]; simpa only [zeros,List.replicate_zero,List.append_nil] using mid
  · have nz : 0 < n-j := by have := of_decide_eq_false z; omega
    have rem := h.data.drop le
    have unchanged := bytesAt_frame h.frame (data_absFrame L (.inr rfl) rem) (by omega)
    have split : bytesAt s.mem D n = bytesAt s.mem D j ++ bytesAt s.mem (D+BitVec.ofNat 64 j) (n-j) := by
      exact (congrArg (bytesAt s.mem D) (show n = j+(n-j) by omega)).trans (bytesAt_add ..)
    refine (last_ok L v h.env h.kept h.x23 xt nz small rem).mono fun u a => ?_
    refine ⟨a.env,a.kept,?_,f.trans (a.frame.mono fun _ hr => List.mem_append_right _ hr)⟩
    rw [split,←List.append_assoc]
    apply absorb_last mid pre (by simpa only [length_bytesAt] using nz) (by simpa only [length_bytesAt] using small)
    have out := a.out
    change blockAt u.mem _ = ghashFrom (blockAt t.mem _) (blockAt t.mem _) [ofBytes (bytesAt t.mem (D+BitVec.ofNat 64 j) (n-j) ++ zeros (16-(n-j)))] at out
    simpa only [length_bytesAt,unchanged,h.hH] using out

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
