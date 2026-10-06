import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareCounter
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail

/-! A complete raw multiplication row, including carry propagation. -/
namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges frame_hdr input_preserved)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

private theorem combine {X Y Z P C Q D : Nat}
    (h : Y+P*C=X+D) (t : Z+Q=Y+P*C) : Z+Q=X+D := by omega

theorem row_ok {s : State} {B : Addr} {Z w a i n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hTail : w=i+8+8*n) (hn : 0<n)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i) :
    WP isa (AdxTiledSquare.row a) s fun t =>
      t.zf = some (decide (i+8=w-8)) ∧ word t.mem B (8*sFn 12) = BitVec.ofNat 64 (i+8) ∧
      (∃ c, wv t.mem B (rawBase w) (2*w)+(2 : Nat)^(128*w)*c =
        wv s.mem B (rawBase w) (2*w)+(2 : Nat)^(64*(i+(i+8)))*wv s.mem B (slot w a+8*i) 8*wv s.mem B (slot w a+8*(i+8)) (8*n)) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega
  have rawZ : rawBase w+16*w ≤ Z := by unfold rawBase slot aAcc at *; omega
  unfold AdxTiledSquare.row
  refine WP.seq (WP.mono (rowInit_ok hs hd hZ hidx) fun u ⟨cu,ju,ou,ku⟩ => ?_)
  have fu : Frm B (ranges w) s.mem u.mem := by
    intro x hx
    apply ou x
    have := hx (8*sFn 12,32) (by simp [ranges])
    simp only [sFn] at *; omega
  have iu : word u.mem B (8*sFn 12) = BitVec.ofNat 64 i := by
    rw [ou.word (by decide) (by decide)]; exact hidx
  have rawU : wv u.mem B (rawBase w) (2*w) = wv s.mem B (rawBase w) (2*w) :=
    ou.wv (by unfold rawBase slot hdrBytes sFn; omega) (by omega)
  refine WP.seq (WP.mono (AdxRect8.row_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd)
    (frame_hdr hh fu) hZ hw (by omega) ha ha ha1 ha2 ha1 ha2
    hTail hn iu ju (by rw [cu]; rfl)) fun v hv => ?_)
  have fv : Frm B (ranges w) u.mem v.mem := by
    intro x hx
    apply hv.frame x
    intro r hr
    simp only [AdxRect8.rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    have hr0 := hx (rawBase w,16*w) (by simp [ranges])
    have hr1 := hx (8*sFn 12,32) (by simp [ranges])
    rcases hr with rfl | rfl | rfl <;> simp only [] <;> simp only [carryOffset,sFn] at * <;> omega
  have ptr : v.gpr .rsi = off B (rawBase w+8*(i+w)) := by
    have p := hv.endPtr.resolve_left (by omega)
    rw [show i+(i+8)+8*n=i+w by omega] at p
    exact p
  refine WP.seq (WP.mono (AdxTiledProduct.tail_ok hv.scr hv.rdi hv.hdr hZ hw hTail hv.indexI ptr)
    fun x ⟨⟨c,eq⟩,ox,kx⟩ => ?_)
  have fx : Frm B (ranges w) v.mem x.mem := Frm.of_outside ox (by simp [ranges])
  have f : Frm B (ranges w) s.mem x.mem := (fu.trans fv).trans fx
  have hx : Hdr x.mem B w mi := frame_hdr hh f
  have ix : word x.mem B (8*sFn 12) = BitVec.ofNat 64 i := by
    rw [ox.word (by unfold rawBase slot hdrBytes sFn; omega) (by decide)]
    exact hv.indexI
  have rowEq := hv.val
  rw [show i+(i+8)+8*(n+1)=i+w+8 by omega,rawU,
    input_preserved ha ha1 ha2 (by omega) Z64 fu,
    input_preserved ha ha1 ha2 (by omega : (i+8)+8*n ≤ w) Z64 fu] at rowEq
  have val : wv x.mem B (rawBase w) (2*w)+2^(128*w)*c =
      wv s.mem B (rawBase w) (2*w)+2^(64*(i+(i+8)))*wv s.mem B (slot w a+8*i) 8*
        wv s.mem B (slot w a+8*(i+8)) (8*n) := combine rowEq eq
  refine WP.mono (nextRow_ok (hv.scr.congr kx.2.2) ((kx.gpr (by decide)).trans hv.rdi)
    hx hZ (by omega) (by omega) (by omega) ix) fun t ⟨mt,zt,kt⟩ => ?_
  have ot : Outside B (8*sFn 12) 8 x.mem t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by decide)
  have ft : Frm B (ranges w) x.mem t.mem := by
    intro y hy
    apply ot y
    have := hy (8*sFn 12,32) (by simp [ranges]); omega
  refine ⟨zt,?_,⟨c,?_⟩,frame_hdr hx ft,f.trans ft,(((ku.trans hv.keep).trans kx).trans kt).mono (by decide)⟩
  · rw [mt,word_writeW_self]
  · rw [ot.wv (by unfold rawBase slot hdrBytes sFn; omega) (by omega : rawBase w+8*(2*w) ≤ 2^64)]
    exact val

end VG.Proof.Bignum.X86_64.AdxTiledSquare
