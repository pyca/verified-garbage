module

public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Select
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-! Copy a publicly indexed projective or affine entry to the point operand slots. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (st)
open VG.Proof.X448.AArch64 (Scr Keeps Outside off ofs word write8_eq read8_eq word_write_aligned)
open VG.Proof.Ed448.AArch64.Window (dst dst_bounds)

def copySpan (n:Nat) : Nat := if n≤16 then 192 else 384

private theorem span_le (n:Nat) : copySpan n≤384 := by
  unfold copySpan
  split <;> omega

private theorem dst_span {n w:Nat} (hn:n≤24) (hw:w<n) :
    832≤dst w ∧ dst w+8≤832+copySpan n := by
  simp only [copySpan,dst,VG.Impl.X448.AArch64.slot]
  split <;> omega

def copyWords (n a:Nat) : List Instr := (List.range n).flatMap fun w =>
  [.ldr .x .x4 .x8 (a+8*w),st .x4 (dst w)]

private theorem copyWord_ok {s:State} {base p:Addr} (hs:Scr s base)
    (hp:s.gpr .x8=p) {w a:Nat} (hw:w<24) (ha:a%8=0) (ha':a+8*w<32768)
    (hr:InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (a+8*w)) 8) :
    WP isa (.block [.ldr .x .x4 .x8 (a+8*w),st .x4 (dst w)]) s fun t =>
      t.mem=s.mem.writeW (off base (dst w)) (s.mem.readW (p+BitVec.ofNat 64 (a+8*w)) 64) ∧
      Keeps [.x4] s t := by
  obtain ⟨_,hd,hd8⟩:=dst_bounds hw
  have es:(a+8*w)%8=0 ∧ a+8*w<32768:=⟨by omega,ha'⟩
  have ed:(dst w)%8=0 ∧ dst w<32768:=⟨hd8,by omega⟩
  have wr:=hs.write (d:=dst w) (n:=8) (by omega)
  apply WP.of_runBlock
  simp only [st,runBlock_cons,runStep_some,runBlock_nil,exec,addr,Size.bytes,es,ed,and_self,
    ite_true,hp,hs.x3,State.read,Size.bits,BitVec.setWidth_eq,State.load,State.store,hr,wr,
    read8_eq,write8_eq,RegUpd.gpr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.wr_write,
    ite_false,reduceCtorEq,Option.bind_some,Option.map_some,Option.some.injEq,exists_eq_left']
  refine ⟨by trivial,⟨fun r h => ?_,rfl,rfl⟩⟩
  simp only [List.mem_singleton] at h
  simp only [RegUpd.gpr_write,h,ite_false]

theorem copyWords_ok {s:State} {base p:Addr} (hs:Scr s base) (hp:s.gpr .x8=p)
    {n a:Nat} (hn:n≤24) (ha:a%8=0) (ha':a+8*n≤32768)
    (hr:∀ w<n,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (a+8*w)) 8)
    (hfar:∀ w<n,∀ j<8,1216≤ofs base (p+BitVec.ofNat 64 (a+8*w)+BitVec.ofNat 64 j)) :
    WP isa (.block (copyWords n a)) s fun t =>
      (∀ w<n,word t.mem base (dst w)=s.mem.readW (p+BitVec.ofNat 64 (a+8*w)) 64) ∧
      Outside base 832 (copySpan n) s.mem t.mem ∧ Keeps [.x4] s t := by
  unfold copyWords
  let inv:=fun k (t:State) =>
    (∀ w<k,word t.mem base (dst w)=s.mem.readW (p+BitVec.ofNat 64 (a+8*w)) 64) ∧
    Outside base 832 (copySpan n) s.mem t.mem ∧ Keeps [.x4] s t
  refine wp_range_flatMap (M:=isa) (N:=n) inv (fun k t hk ⟨tv,fo,kt⟩ => ?_)
    n (Nat.le_refl _) s ⟨fun _ h => by omega,Outside.refl _ _ _ _,Keeps.refl _ _⟩
  have ht:=hs.of_keeps kt (by decide)
  refine WP.mono (copyWord_ok ht ((kt.1 _ (by decide)).trans hp) (by omega) ha (by omega)
    (by rw [kt.2.1,kt.2.2];exact hr k hk)) fun u ⟨um,ku⟩ => ?_
  obtain ⟨dlo,dhi,dal⟩:=dst_bounds (show k<24 by omega)
  have hsval:t.mem.readW (p+BitVec.ofNat 64 (a+8*k)) 64=
      s.mem.readW (p+BitVec.ofNat 64 (a+8*k)) 64 := by
    apply Mem.readW_congr
    intro j hj
    exact fo _ (Or.inr (by have := span_le n;have := hfar k hk j hj;omega))
  refine ⟨fun w hw => ?_,?_,kt.trans ku⟩
  · rw [um,hsval,word_write_aligned _ _ (d:=dst k) (e:=dst w) (by omega) (by have := dst_bounds (show w<24 by omega);omega)
      dal (dst_bounds (by omega)).2.2]
    by_cases he:w=k
    · subst w
      rw [ite_eq_left rfl]
    · have hne:dst w≠dst k := by
        simp only [dst,VG.Impl.X448.AArch64.slot]
        omega
      rw [ite_eq_right hne]
      exact tv w (by omega)
  · rw [um]
    have dh:=dst_span hn hk
    exact fo.trans ((VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega)).mono dh.1 dh.2)

end VG.Proof.Ed448.AArch64.Sparse
