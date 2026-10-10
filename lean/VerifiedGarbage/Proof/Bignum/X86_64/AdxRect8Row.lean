import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
import VerifiedGarbage.Proof.Bignum.Rectangular

/-! ## AdxRect8At -/
section

/-! A tile in the existing Montgomery working space, for every valid array pair. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

theorem tileAt_ok {s : State} {B : Addr} {Z w i j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hi : i+8 ≤ w) (hj : j+8 ≤ w)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hjdx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j) :
    let e := slot w aAcc+16+8*(i+j)
    WP isa (AdxRect8.tileAt ca cb) s fun t =>
      wv t.mem B e 16 + 2^1024 * (word t.mem B carryOffset).toNat =
        wv s.mem B e 16 + wv s.mem B (slot w a+8*i) 8 * wv s.mem B (slot w b+8*j) 8 +
          2^512 * (word s.mem B carryOffset).toNat ∧
      (word t.mem B carryOffset).toNat ≤ 2 ∧
      ((word s.mem B carryOffset).toNat ≤ 1 → (word t.mem B carryOffset).toNat ≤ 1) ∧
      Hdr t.mem B w mi ∧ Frm B [(e,128),(carryOffset,8)] s.mem t.mem ∧ t.gpr .rsi = off B (e+64) ∧ Keep mmRegs s t := by
  dsimp only
  unfold AdxRect8.tileAt
  have ar := tile_ranges hi hj ha ha1 ha2
  have br := tile_ranges hj hi hb hb1 hb2
  have cb : carryOffset+8 ≤ slot w aAcc+16+8*(i+j) := by
    unfold carryOffset sFn slot hdrBytes aAcc; omega
  refine WP.seq (WP.mono (setup_ok hs hd hh hZ hv pa pb hidx hjdx)
    fun u ⟨ua,ub,uo,um,ku⟩ => ?_)
  refine WP.mono (tile_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd) ua ub uo
    (by omega) (by omega) (by omega) ar.2.2 (by omega) cb)
    fun t ⟨eq,bd,one,fr,ptr,kt⟩ => ?_
  rw [um] at eq one fr
  have fr' : Frm B [(slot w aAcc+16+8*(i+j),128),(carryOffset,8),(8*sFn 13,8)] s.mem t.mem :=
    fr.mono (by simp)
  exact ⟨eq,bd,one,frame_hdr hh (by unfold slot; omega) fr',fr,ptr,
    (ku.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.AdxRect8

end

/-! ## AdxRect8Step -/
section

/-! One complete rectangular row step advances the public column counter. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

theorem rowStep_ok {s : State} {B : Addr} {Z w i j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hi : i+8 ≤ w) (hj : j+8 ≤ w)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hjdx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j) :
    let e := slot w aAcc+16+8*(i+j)
    WP isa (AdxRect8.rowStep ca cb) s fun t =>
      t.zf = some (decide (j+8=w)) ∧
      word t.mem B (8*sFn 13) = BitVec.ofNat 64 (j+8) ∧
      wv t.mem B e 16 + 2^1024 * (word t.mem B carryOffset).toNat =
        wv s.mem B e 16 + wv s.mem B (slot w a+8*i) 8 * wv s.mem B (slot w b+8*j) 8 +
          2^512 * (word s.mem B carryOffset).toNat ∧
      (word t.mem B carryOffset).toNat ≤ 2 ∧
      ((word s.mem B carryOffset).toNat ≤ 1 → (word t.mem B carryOffset).toNat ≤ 1) ∧
      Hdr t.mem B w mi ∧ Frm B [(e,128),(carryOffset,8),(8*sFn 13,8)] s.mem t.mem ∧ t.gpr .rsi = off B (e+64) ∧ Keep mmRegs s t := by
  dsimp only
  unfold AdxRect8.rowStep
  have hn := hs.nowrap
  let e := slot w aAcc+16+8*(i+j)
  have eZ : e+128 ≤ Z := by have := tile_ranges hi hj ha ha1 ha2; omega
  have cZ : carryOffset+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 14 < 32 by decide)
    unfold carryOffset; omega
  have idxZ : 8*sFn 13+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 13 < 32 by decide); omega
  have eH : hdrBytes ≤ e := by unfold e slot; omega
  refine WP.seq (WP.mono (tileAt_ok hs hd hh hZ hi hj hv pa pb ha hb ha1 ha2 hb1 hb2 hidx hjdx)
    fun u ⟨eq,bd,one,hu,fr,ptr,ku⟩ => ?_)
  have ju : word u.mem B (8*sFn 13) = BitVec.ofNat 64 j := by
    rw [fr.word_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;>
        unfold carryOffset sFn e slot hdrBytes aAcc at * <;> omega) (by omega)]
    exact hjdx
  refine WP.mono (nextColumn_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd)
    hu hZ (by omega) (by omega) ju) fun t ⟨mt,zt,kt⟩ => ?_
  have ot : Outside B (8*sFn 13) 8 u.mem t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by omega)
  have vt : wv t.mem B e 16 = wv u.mem B e 16 :=
    ot.wv (by unfold sFn hdrBytes at *; omega) (by omega)
  have ct : word t.mem B carryOffset = word u.mem B carryOffset :=
    ot.word (by unfold carryOffset sFn; omega) (by omega)
  have fr' : Frm B [(e,128),(carryOffset,8),(8*sFn 13,8)] s.mem t.mem :=
    (fr.mono (by simp [e])).trans (Frm.of_outside ot (by simp))
  refine ⟨zt,?_,?_,?_,?_,frame_hdr hh eH fr',fr',(kt.gpr (by decide)).trans ptr,(ku.trans kt).mono (by decide)⟩
  · rw [mt,word_writeW_self]
  · dsimp only [e] at vt
    rw [vt,ct]; exact eq
  · rw [ct]; exact bd
  · rw [ct]; exact one

end VG.Proof.Bignum.X86_64.AdxRect8

end

/-! ## AdxRect8Embed -/
section

/-! Embed a local tile update in the full raw product without subtraction. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

/-- Unchanged words before and after the tile cancel from the value equation. -/
theorem embed {m m' : Mem} {B : Addr} {e d n : Nat} {extra : List (Nat × Nat)}
    (hn : d+16 ≤ n) (hZ : e+8*n ≤ (2 : Nat)^64) (hc : ∀ r ∈ extra, r.1+r.2 ≤ e)
    (hf : Frm B ((e+8*d,128)::extra) m m') :
    wv m' B e n + (2 : Nat)^(64*d)*wv m B (e+8*d) 16 =
      wv m B e n + (2 : Nat)^(64*d)*wv m' B (e+8*d) 16 := by
  have lo : wv m' B e d = wv m B e d := hf.wv_eq (by
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · simp only []; omega
    · have := hc r hr; omega) (by omega)
  have hi : wv m' B (e+8*(d+16)) (n-(d+16)) = wv m B (e+8*(d+16)) (n-(d+16)) :=
    hf.wv_eq (by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · simp only []; omega
      · have := hc r hr; omega) (by omega)
  have shape : n = d+(16+(n-(d+16))) := by omega
  rw [shape,wv_add,wv_add,wv_add,wv_add]
  rw [show e+8*d+8*16 = e+8*(d+16) by omega,lo,hi]
  simp only [show 64*16=1024 from rfl]
  generalize (2 : Nat)^1024 = Q
  exact (VG.Proof.Bignum.Rectangular.surround (A := wv m B e d) (P := (2 : Nat)^(64*d))
    (X := wv m B (e+8*d) 16) (X' := wv m' B (e+8*d) 16)
    (Q := Q) (Y := wv m B (e+8*(d+16)) (n-(d+16))))

/-- A tile's carry equation extends to the whole raw product. -/
theorem embed_value {m m' : Mem} {B : Addr} {e d n u v cin cout q r : Nat} {extra : List (Nat × Nat)}
    (hn : d+16 ≤ n) (hZ : e+8*n ≤ (2 : Nat)^64) (hc : ∀ r ∈ extra, r.1+r.2 ≤ e)
    (hf : Frm B ((e+8*d,128)::extra) m m')
    (ht : wv m' B (e+8*d) 16 + q*cout =
      wv m B (e+8*d) 16 + u*v + r*cin) :
    wv m' B e n + (2 : Nat)^(64*d)*q*cout =
      wv m B e n + (2 : Nat)^(64*d)*(u*v) + (2 : Nat)^(64*d)*r*cin := by
  have eq := embed hn hZ hc hf
  exact VG.Proof.Bignum.Rectangular.lift_value eq ht

end VG.Proof.Bignum.X86_64.AdxRect8

end

/-! ## AdxRect8RowInv -/
section

/-! The invariant keeps the full product plus its pending row carry exact. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

def rawBase (w : Nat) := slot w aAcc+16

def rowRanges (w : Nat) : List (Nat × Nat) :=
  [(rawBase w,16*w),(carryOffset,8),(8*sFn 13,8)]

structure RowInv (s₀ : State) (B : Addr) (Z w a b i j₀ k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi = B
  indexI : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i
  indexJ : word s.mem B (8*sFn 13) = BitVec.ofNat 64 (j₀+8*k)
  carry : (word s.mem B carryOffset).toNat ≤ 1
  keep : Keep mmRegs s₀ s
  frame : Frm B (rowRanges w) s₀.mem s.mem
  endPtr : k=0 ∨ s.gpr .rsi = off B (rawBase w+8*(i+j₀+8*k))
  val : wv s.mem B (rawBase w) (2*w) +
      (2 : Nat)^(64*(i+j₀+8*(k+1))) * (word s.mem B carryOffset).toNat =
    wv s₀.mem B (rawBase w) (2*w) +
      (2 : Nat)^(64*(i+j₀)) * wv s₀.mem B (slot w a+8*i) 8 * wv s₀.mem B (slot w b+8*j₀) (8*k)

/-- Input arrays remain disjoint from the entire raw product and its counters. -/
theorem input_preserved {m m' : Mem} {B : Addr} {w a i n : Nat}
    (ha : a < 8) (h1 : a ≠ aAcc) (h2 : a ≠ aTmp) (hi : i+n ≤ w)
    (hZ : slot w 8 ≤ (2 : Nat)^64) (hf : Frm B (rowRanges w) m m') :
    wv m' B (slot w a+8*i) n = wv m B (slot w a+8*i) n := by
  have sa := slot_le (w := w) ha
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  apply hf.wv_eq
  · intro r hr
    simp only [rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [] <;>
      simp only [rawBase,carryOffset,sFn,slot,hdrBytes,aAcc,aTmp] at * <;> omega
  · omega

theorem rowStep_inv {s₀ s : State} {B : Addr} {Z w a b i j₀ k n : Nat} {mi : BitVec 64}
    {ps : List (Nat × Nat)} (hv : Ops s₀.mem B w ps) {ca cb : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < (2 : Nat)^31) (hi : i+8 ≤ w)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hn : w = j₀+8*n) (hk : k < n)
    (h : RowInv s₀ B Z w a b i j₀ k mi s) :
    WP isa (AdxRect8.rowStep ca cb) s fun t =>
      t.zf = some (decide (k+1=n)) ∧ RowInv s₀ B Z w a b i j₀ (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega
  have rt := slot_le (w := w) (show aTmp < 8 by decide)
  have rawZ : rawBase w+8*(2*w) ≤ Z := by unfold rawBase slot aAcc aTmp at *; omega
  have hv' : Ops s.mem B w ps := hv.of_frm h.frame fun r hr => by
    simp only [rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [] <;>
      simp only [rawBase,carryOffset,sFn,slot,hdrBytes,aAcc] at * <;> omega
  refine WP.mono (rowStep_ok h.scr h.rdi h.hdr hZ hw hi (by omega) hv' pa pb
    ha hb ha1 ha2 hb1 hb2 h.indexI h.indexJ)
    fun t ⟨zt,jt,eq,_,carry,ht,ft,ptr,kt⟩ => ?_
  have localFrame : Frm B ((rawBase w+8*(i+(j₀+8*k)),128)::[(carryOffset,8),(8*sFn 13,8)]) s.mem t.mem := ft
  have wider : Frm B (rowRanges w) s.mem t.mem := by
    intro x hx
    apply localFrame x
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    have a0 := hx (rawBase w,16*w) (by simp [rowRanges])
    have a1 := hx (carryOffset,8) (by simp [rowRanges])
    have a2 := hx (8*sFn 13,8) (by simp [rowRanges])
    rcases hr with rfl | rfl | rfl <;> simp only [] <;> omega
  have it : word t.mem B (8*sFn 12) = BitVec.ofNat 64 i := by
    rw [wider.word_eq (by
      intro r hr
      simp only [rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [] <;>
        simp only [rawBase,carryOffset,sFn,slot,hdrBytes,aAcc] at * <;> omega) (by decide)]
    exact h.indexI
  have va := input_preserved ha ha1 ha2 hi Z64 h.frame
  have vb := input_preserved hb hb1 hb2 (by omega : j₀+8*k+8 ≤ w) Z64 h.frame
  rw [← show rawBase w = slot w aAcc+16 from rfl] at eq
  generalize hp : (2 : Nat)^1024 = Q at eq
  generalize hq : (2 : Nat)^512 = R at eq
  have full := by
    exact (embed_value (e := rawBase w)
      (u := wv s.mem B (slot w a+8*i) 8) (v := wv s.mem B (slot w b+8*(j₀+8*k)) 8)
      (cin := (word s.mem B carryOffset).toNat) (cout := (word t.mem B carryOffset).toNat)
      (by omega : i+(j₀+8*k)+16 ≤ 2*w) (by omega : rawBase w+8*(2*w) ≤ (2 : Nat)^64)
      (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> simp only [] <;>
          simp only [rawBase,carryOffset,sFn,slot,hdrBytes,aAcc] <;> omega) localFrame eq)
  rw [← hp,← hq,va,vb] at full
  refine ⟨?_,⟨h.scr.congr kt.2.2,ht,(kt.gpr (by decide)).trans h.rdi,it,?_,carry h.carry,
    (h.keep.trans kt).mono (by decide),h.frame.trans wider,?_,?_⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega))
  · simpa only [show j₀+8*(k+1)=(j₀+8*k)+8 by omega] using jt
  · apply Or.inr
    rw [ptr]
    apply congrArg (off B)
    unfold rawBase
    omega
  · have prev := h.val
    rw [show 8*(k+1)=8*k+8 by omega,wv_add]
    rw [show slot w b+8*j₀+8*(8*k)=slot w b+8*(j₀+8*k) by omega]
    rw [← Nat.pow_add 2 (64*(i+(j₀+8*k))) 1024,
      ← Nat.pow_add 2 (64*(i+(j₀+8*k))) 512] at full
    have p1 : 64*(i+(j₀+8*k))+1024 = 64*(i+j₀+8*((k+1)+1)) := by omega
    have p2 : 64*(i+(j₀+8*k))+512 = 64*(i+j₀+8*(k+1)) := by omega
    rw [p1,p2] at full
    rw [show 64*(i+(j₀+8*k))=64*(i+j₀)+64*(8*k) by omega,Nat.pow_add] at full
    exact VG.Proof.Bignum.Rectangular.extend_full prev full

end VG.Proof.Bignum.X86_64.AdxRect8

end

/-! ## AdxRect8Row -/
section

/-! Correctness and termination of a complete rectangular row. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

theorem row_ok {s : State} {B : Addr} {Z w a b i j₀ n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca cb : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hi : i+8 ≤ w)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hwN : w = j₀+8*n) (hn : 0 < n)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hjdx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j₀)
    (hc : (word s.mem B carryOffset).toNat = 0) :
    WP isa (AdxRect8.row ca cb) s (RowInv s B Z w a b i j₀ n mi) := by
  have h0 : RowInv s B Z w a b i j₀ 0 mi s :=
    ⟨hs,hh,hd,hidx,by simpa only [Nat.mul_zero,Nat.add_zero] using hjdx,
      by omega,Keep.refl _ _,Frm.refl _ _ _,Or.inl rfl,by
        simp only [hc,Nat.mul_zero,Nat.add_zero,wv]⟩
  unfold AdxRect8.row
  exact wp_upto (a := 0) (N := n) hn (RowInv s B Z w a b i j₀ · mi)
    (fun _ _ hk _ h => rowStep_inv hv pa pb hZ hw hi ha hb ha1 ha2 hb1 hb2 hwN hk h)
    (fun _ h => h) h0

end VG.Proof.Bignum.X86_64.AdxRect8

end
