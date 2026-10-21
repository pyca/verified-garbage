module
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledInit
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCross

import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Block
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.Triangular
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ## AdxTri8FullBlock -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem fullBlock_ok {s : State} {B : Addr} {Z w a I : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hIndex : I+8≤w)
    (hR : s.gpr .rax=BitVec.ofNat 64 I) :
    WP isa (AdxTri8.block ca) s fun t =>
      wv t.mem B (slot w aAcc+16+16*I) 16=AdxSquare.crossValue s.mem B (slot w a+8*I) 8 ∧
      Outside B (slot w aAcc+16+16*I) 128 s.mem t.mem ∧ Keep mmRegs s t :=
  block_ok hs hd hh hZ hv pa ha ha1 ha2 hIndex hR

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8BlocksFrame -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)

def diagonalRanges (w k : Nat) : List (Nat × Nat) := [(rawBase w,128*k),(8*sFn 12,8)]

def blockCross (m : Mem) (B : Addr) (e : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => blockCross m B e n+2^(1024*n)*AdxSquare.crossValue m B (e+64*n) 8

structure BlocksInv (s₀ : State) (B : Addr) (Z w a k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi=B
  indexI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 (8*k)
  /-- `rax` holds the index too: `block` reads it from there. -/
  raxI : s.gpr .rax=BitVec.ofNat 64 (8*k)
  keep : Keep mmRegs s₀ s
  frame : Frm B (diagonalRanges w k) s₀.mem s.mem
  val : wv s.mem B (rawBase w) (16*k)=blockCross s₀.mem B (slot w a) k

theorem diagonal_hdr {m m' : Mem} {B : Addr} {w k : Nat} {mi : BitVec 64}
    (hh : Hdr m B w mi) (hf : Frm B (diagonalRanges w k) m m') : Hdr m' B w mi := by
  have low (j : Nat) (hj : j<16) : word m' B (8*j)=word m B (8*j) := by
    apply hf.word_eq
    · intro r hr
      simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> simp only [rawBase,slot,hdrBytes,sFn] <;> omega_arith
    · omega_arith
  exact ⟨(low sW (by decide)).trans hh.hw,(low sMinv (by decide)).trans hh.hminv,
    fun j hj => (low (sArr j) (by unfold sArr; omega_arith)).trans (hh.harr j hj)⟩

theorem diagonal_ops {m m' : Mem} {B : Addr} {w k : Nat} {ps : List (Nat × Nat)}
    (hv : Ops m B w ps) (hf : Frm B (diagonalRanges w k) m m') : Ops m' B w ps :=
  hv.of_frm hf fun r hr => by
    simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;> simp only [rawBase,slot,hdrBytes,sFn] <;> omega_arith

theorem diagonal_input {m m' : Mem} {B : Addr} {w a k I : Nat}
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hk : 8*k≤w) (hi : I+8≤w)
    (hZ : slot w 8≤2^64) (hf : Frm B (diagonalRanges w k) m m') :
    AdxSquare.crossValue m' B (slot w a+8*I) 8=AdxSquare.crossValue m B (slot w a+8*I) 8 := by
  have ar := AdxRect8.tile_ranges hi hi ha ha1 ha2
  have s1 := slot_sep (w := w) ha1
  have s2 := slot_sep (w := w) ha2
  apply AdxSquare.crossValue_congr
  intro j hj
  apply hf.word_eq
  · intro r hr
    simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;>
      simp only [rawBase,slot,hdrBytes,sFn,aAcc,aTmp] at * <;> omega_arith
  · omega_arith

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8BlocksStep -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)

theorem blockStep_ok {s₀ s : State} {B : Addr} {Z w a k n : Nat} {mi : BitVec 64}
    {ps : List (Nat × Nat)} (hv : Ops s₀.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hZ : slot w 8≤Z) (hw : w<2^31) (hwN : w=8*n) (hk : k<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (h : BlocksInv s₀ B Z w a k mi s) :
    WP isa (.seq (AdxTri8.block ca) (.block AdxTri8.nextBlock)) s fun t =>
      t.zf=some (decide (k+1=n)) ∧ BlocksInv s₀ B Z w a (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8≤(2 : Nat)^64 := by omega_arith
  have ar := AdxRect8.tile_ranges (by omega_arith : 8*k+8≤w) (by omega_arith : 8*k+8≤w) ha ha1 ha2
  refine WP.seq (WP.mono (fullBlock_ok h.scr h.rdi h.hdr hZ (diagonal_ops hv h.frame) pa ha ha1 ha2 (by omega_arith) h.raxI)
    fun u ⟨vu,ou,ku⟩ => ?_)
  have indexU : word u.mem B (8*sFn 12)=BitVec.ofNat 64 (8*k) := by
    rw [ou.word (by unfold slot hdrBytes sFn; omega_arith) (by decide)]; exact h.indexI
  have headerU := h.hdr.of_outside ou (by unfold slot; omega_arith)
  refine WP.mono (AdxTiledProduct.nextRow_rax_ok (h.scr.congr ku.2.2) ((ku.gpr (by decide)).trans h.rdi)
    headerU hZ (by omega_arith) (by omega_arith) indexU) fun t ⟨mt,zt,rt,kt⟩ => ?_
  have ot : Outside B (8*sFn 12) 8 u.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by decide)
  have fu : Frm B (diagonalRanges w (k+1)) s.mem u.mem := by
    intro x hx
    apply ou x
    have := hx (rawBase w,128*(k+1)) (by simp [diagonalRanges])
    unfold rawBase at *; omega_arith
  have ft : Frm B (diagonalRanges w (k+1)) u.mem t.mem := Frm.of_outside ot (by simp [diagonalRanges])
  have old : Frm B (diagonalRanges w (k+1)) s₀.mem s.mem := by
    intro x hx
    apply h.frame x
    intro r hr
    simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · have := hx (rawBase w,128*(k+1)) (by simp [diagonalRanges]); simp only []; omega_arith
    · exact hx _ (by simp [diagonalRanges])
  have finalFrame := (old.trans fu).trans ft
  have low : wv u.mem B (rawBase w) (16*k)=wv s.mem B (rawBase w) (16*k) :=
    ou.wv (by unfold rawBase; omega_arith) (by unfold rawBase at *; omega_arith)
  have resultU : wv u.mem B (rawBase w+8*(16*k)) 16=
      AdxSquare.crossValue s₀.mem B (slot w a+64*k) 8 := by
    rw [show rawBase w+8*(16*k)=slot w aAcc+16+16*(8*k) by unfold rawBase; omega_arith,vu,
      diagonal_input ha ha1 ha2 (by omega_arith) (by omega_arith) Z64 h.frame,
      show slot w a+8*(8*k)=slot w a+64*k by omega_arith]
  refine ⟨?_,⟨h.scr.congr (ku.trans kt).2.2,diagonal_hdr h.hdr (fu.trans ft),
    ((ku.trans kt).gpr (by decide)).trans h.rdi,?_,?_,(h.keep.trans (ku.trans kt)).mono (by decide),finalFrame,?_⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  · rw [mt,word_writeW_self,show 8*(k+1)=8*k+8 by omega_arith]
  · rw [rt,show 8*(k+1)=8*k+8 by omega_arith]
  · rw [ot.wv (by unfold rawBase slot hdrBytes sFn; omega_arith) (by unfold rawBase at *; omega_arith),
      show 16*(k+1)=16*k+16 by omega_arith,wv_add,low,h.val,resultU,blockCross]
    rw [show 64*(16*k)=1024*k by omega_arith]

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Blocks -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)

theorem blocks_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hw : w<2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) :
    WP isa (AdxTri8.blocks ca) s (BlocksInv s B Z w a n mi) := by
  have nowrap := hs.nowrap
  have iZ : 8*sFn 12+8≤Z := by
    have := hdr_lt_slot w 8 (show sFn 12<32 by decide); omega_arith
  have init : WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s fun t =>
      (t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64) ∧ t.gpr .rax=0) ∧ Keep [.rax] s t := by
    apply WP.keep [.rax] (Q := fun t => t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64) ∧ t.gpr .rax=0) _ rfl
    xrun [State.ea,hdr,hd,hdrOff,hs.st iZ]; rfl
  unfold AdxTri8.blocks
  refine WP.seq (WP.mono init fun u ⟨⟨mu,ru⟩,ku⟩ => ?_)
  have ou : Outside B (8*sFn 12) 8 s.mem u.mem := by rw [mu]; exact writeW_outside _ _ _ (by decide)
  have fu : Frm B (diagonalRanges w 0) s.mem u.mem := Frm.of_outside ou (by simp [diagonalRanges])
  have h0 : BlocksInv s B Z w a 0 mi u :=
    ⟨hs.congr ku.2.2,diagonal_hdr hh fu,(ku.gpr (by decide)).trans hd,by rw [mu,word_writeW_self]; rfl,
      by rw [ru]; rfl,ku.mono (by decide),fu,rfl⟩
  exact wp_upto (a := 0) (N := n) hn (BlocksInv s B Z w a · mi)
    (fun _ _ hk _ h => blockStep_ok hv pa hZ hw hwN hk ha ha1 ha2 h) (fun _ h => h) h0

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Chunks -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem crossValue_add (m : Mem) (B : Addr) (e p q : Nat) :
    AdxSquare.crossValue m B e (p+q)=AdxSquare.crossValue m B e p+
      2^(128*p)*AdxSquare.crossValue m B (e+8*p) q+
      2^(64*p)*wv m B e p*wv m B (e+8*p) q := by
  have shift : (fun i => (word m B (e+8*(p+i))).toNat)=
      (fun i => (word m B (e+8*p+8*i)).toNat) := by
    funext i
    rw [show e+8*(p+i)=e+8*p+8*i by omega_arith]
  unfold AdxSquare.crossValue
  rw [Triangular.cross_add,shift,AdxSquare.value_words,AdxSquare.value_words,
    ← Nat.pow_mul,← Nat.pow_mul,show 64*(2*p)=128*p by omega_arith]

def chunks (m : Mem) (B : Addr) (e : Nat) (j : Nat) := wv m B (e+64*j) 8

theorem chunks_value (m : Mem) (B : Addr) (e n : Nat) :
    Square.value (2^512) (chunks m B e) n=wv m B e (8*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Square.value,ih,show 8*(n+1)=8*n+8 by omega_arith,wv_add,← Nat.pow_mul 2 512 n]
    simp only [chunks,show 8*(8*n)=64*n by omega_arith,show 64*(8*n)=512*n by omega_arith]
    rw [Nat.mul_comm (wv m B (e+64*n) 8)]

private theorem sum_chunks {A C P D Q X Y : Nat} :
    (A+C)+P*D+Q*X*Y=(A+P*D)+(C+X*Y*Q) := by grind

theorem chunks_cross (m : Mem) (B : Addr) (e n : Nat) :
    AdxSquare.crossValue m B e (8*n)=blockCross m B e n+Square.cross (2^512) (chunks m B e) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 8*(n+1)=8*n+8 by omega_arith,crossValue_add,ih,blockCross,Square.cross,chunks_value,← Nat.pow_mul 2 512 n]
    simp only [chunks,show 8*(8*n)=64*n by omega_arith,show 128*(8*n)=1024*n by omega_arith,
      show 64*(8*n)=512*n by omega_arith]
    exact sum_chunks

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTiledSquareMath -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTri8 (chunks blockCross)

theorem chunks_tail_value (m : Mem) (B : Addr) (e k n : Nat) :
    Square.value (2^512) (fun j => chunks m B e (k+j)) n=wv m B (e+64*k) (8*n) := by
  have f : (fun j => chunks m B e (k+j))=chunks m B (e+64*k) := by
    funext j
    unfold chunks
    rw [show e+64*(k+j)=e+64*k+64*j by omega_arith]
  rw [f,AdxTri8.chunks_value]

def remaining (m : Mem) (B : Addr) (e n k : Nat) :=
  2^(1024*k)*Square.cross (2^512) (fun j => chunks m B e (k+j)) (n-k)

private theorem distribute {P R X V C : Nat} :
    P*(R*X*V+R*R*C)=(P*R)*X*V+(P*(R*R))*C := by grind

theorem remaining_step (m : Mem) (B : Addr) (e n k : Nat) (hk : k+1<n) :
    remaining m B e n k=2^(512*(2*k+1))*chunks m B e k*wv m B (e+64*(k+1)) (8*(n-k-1))+
      remaining m B e n (k+1) := by
  have shift : (fun j => chunks m B e (k+(j+1)))=(fun j => chunks m B e ((k+1)+j)) := by
    funext j
    rw [show k+(j+1)=(k+1)+j by omega_arith]
  have p1 : (2 : Nat)^(512*(2*k+1))=2^(1024*k)*2^512 := by
    rw [← Nat.pow_add 2 (1024*k) 512]
    apply congrArg (fun n : Nat => (2 : Nat)^n)
    omega_arith
  have p2 : (2 : Nat)^(1024*(k+1))=2^(1024*k)*(2^512*2^512) := by
    rw [← Nat.pow_add 2 512 512,← Nat.pow_add 2 (1024*k) (512+512)]
    apply congrArg (fun n : Nat => (2 : Nat)^n)
    omega_arith
  unfold remaining
  rw [show n-k=(n-k-1)+1 by omega_arith,Triangular.cross_head,shift,chunks_tail_value]
  simp only [Nat.add_zero]
  rw [show n-(k+1)=n-k-1 by omega_arith,p1,p2]
  generalize (2 : Nat)^(1024*k)=P, (2 : Nat)^512=R
  exact distribute

theorem remaining_end (m : Mem) (B : Addr) (e n : Nat) (hn : 0<n) : remaining m B e n (n-1)=0 := by
  unfold remaining
  rw [show n-(n-1)=1 by omega_arith]
  simp only [Square.cross,Square.value,Nat.zero_mul,Nat.add_zero,Nat.mul_zero]

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareRows -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges frame_hdr frame_ops input_preserved)
open VG.Proof.Bignum.X86_64.AdxTri8 (chunks)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- Before row `k`: the raw product, the carry the row before handed in
`sFn 15` (none after the last row), and the rows to come. -/
structure Inv (s₀ : State) (B : Addr) (Z w a n k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi=B
  indexI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 (8*k)
  hand : (word s.mem B AdxRect8.handOffset).toNat ≤ 2
  keep : Keep mmRegs s₀ s
  frame : Frm B (ranges w) s₀.mem s.mem
  val : ∃ c, wv s.mem B (rawBase w) (2*w) +
      2^(64*(8*k+w))*(if 8*k+8=w then 0 else (word s.mem B AdxRect8.handOffset).toNat) +
      2^(128*w)*c+remaining s₀.mem B (slot w a) n k=
    wv s₀.mem B (rawBase w) (2*w)+remaining s₀.mem B (slot w a) n 0

private theorem advance {W W' H H' R C D S S' T A : Nat}
    (prev : W+H+R*C+S=T) (step : W'+H'+R*D=W+H+A) (rest : S=A+S') : W'+H'+R*(C+D)+S'=T := by grind

theorem step_inv {s₀ s : State} {B : Addr} {Z w a n k : Nat} {mi : BitVec 64}
    {ps : List (Nat × Nat)} (hv : Ops s₀.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hZ : slot w 8≤Z) (hw : w<2^31) (hwN : w=8*n) (hk : k<n-1)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (h : Inv s₀ B Z w a n k mi s) :
    WP isa (AdxTiledSquare.row ca) s fun t => t.zf=some (decide (k+1=n-1)) ∧ Inv s₀ B Z w a n (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8≤(2 : Nat)^64 := by omega_arith
  refine WP.mono (row_ok h.scr h.rdi h.hdr (frame_ops hv h.frame) pa hZ hw (by omega_arith : w=8*k+8+8*(n-k-1))
    (by omega_arith) ha ha1 ha2 h.indexI rfl h.hand) fun t ⟨zt,it,σt,⟨d,eq⟩,ht,ft,kt⟩ => ?_
  rw [input_preserved ha ha1 ha2 (by omega_arith : 8*k+8≤w) Z64 h.frame,
    input_preserved ha ha1 ha2 (by omega_arith : (8*k+8)+8*(n-k-1)≤w) Z64 h.frame] at eq
  rw [show 64*(8*k+(8*k+8))=512*(2*k+1) by omega_arith,
    show slot w a+8*(8*k)=slot w a+64*k by omega_arith,
    show slot w a+8*(8*k+8)=slot w a+64*(k+1) by omega_arith] at eq
  obtain ⟨c,prev⟩ := h.val
  simp only [show (8*k+8=w) = False from eq_false (by omega_arith),ite_false] at prev
  refine ⟨?_,⟨h.scr.congr kt.2.2,ht,(kt.gpr (by decide)).trans h.rdi,?_,σt,
    (h.keep.trans kt).mono (by decide),h.frame.trans ft,c+d,?_⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  · simpa only [show 8*(k+1)=8*k+8 by omega_arith] using it
  · rw [show 8*(k+1)+8=8*k+16 by omega_arith,show 8*(k+1)+w=8*k+w+8 by omega_arith]
    exact advance prev eq (remaining_step s₀.mem B (slot w a) n k (by omega_arith))

theorem rows_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hw : w<2^31) (hwN : w=8*n) (hn : 1<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) :
    WP isa (AdxTiledSquare.rows ca) s fun t =>
      (∃ c, wv t.mem B (rawBase w) (2*w)+2^(128*w)*c=
        wv s.mem B (rawBase w) (2*w)+Square.cross (2^512) (chunks s.mem B (slot w a)) n) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have iZ : 8*sFn 12+8≤Z := by have := hdr_lt_slot w 8 (show sFn 12<32 by decide); omega_arith
  have hZ15 : 8*sFn 15+8≤Z := by have := hdr_lt_slot w 8 (show sFn 15<32 by decide); omega_arith
  have init : WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax,.store (hdr (sFn 15)) .rax]) s
      fun t => t.mem=(s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)).writeW (off B (8*sFn 15)) (0 : BitVec 64) ∧
        Keep [.rax] s t := by
    apply WP.keep [.rax] (Q := fun t => t.mem=(s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)).writeW
      (off B (8*sFn 15)) (0 : BitVec 64)) _ rfl
    xrun [State.ea,hdr,hd,hdrOff,hs.st iZ,hs.st hZ15]; rfl
  unfold AdxTiledSquare.rows
  refine WP.seq (WP.mono init fun u ⟨mu,ku⟩ => ?_)
  have o1 : Outside B (8*sFn 12) 8 s.mem (s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)) :=
    writeW_outside _ _ _ (by decide)
  have o2 : Outside B (8*sFn 15) 8 (s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)) u.mem := by
    rw [mu]; exact writeW_outside _ _ _ (by decide)
  have fu : Frm B (ranges w) s.mem u.mem := by
    intro x hx
    have := hx (8*sFn 12,32) (by simp [ranges])
    exact (o2 x (by simp only [sFn] at *; omega_arith)).trans (o1 x (by simp only [sFn] at *; omega_arith))
  have i0 : word u.mem B (8*sFn 12) = BitVec.ofNat 64 (8*0) := by
    rw [o2.word (by decide) (by decide),word_writeW_self]; rfl
  have h00 : word u.mem B AdxRect8.handOffset = 0 := by
    rw [mu]; exact word_writeW_self ..
  have h0 : Inv s B Z w a n 0 mi u :=
    ⟨hs.congr ku.2.2,frame_hdr hh fu,(ku.gpr (by decide)).trans hd,i0,by rw [h00]; decide,
      ku.mono (by decide),fu,0,by
        rw [h00,o2.wv (by unfold rawBase slot hdrBytes sFn; omega_arith) (by unfold rawBase slot aAcc at *; omega_arith),
          o1.wv (by unfold rawBase slot hdrBytes sFn; omega_arith) (by unfold rawBase slot aAcc at *; omega_arith)]
        simp⟩
  apply wp_upto (a := 0) (N := n-1) (by omega_arith) (Inv s B Z w a n · mi)
    (fun _ _ hk _ h => step_inv hv pa hZ hw hwN hk ha ha1 ha2 h) ?_ h0
  intro t h
  obtain ⟨c,eq⟩ := h.val
  simp only [show (8*(n-1)+8=w) = True from eq_true (by omega_arith),ite_true,Nat.mul_zero,Nat.add_zero] at eq
  rw [remaining_end s.mem B (slot w a) n (by omega_arith),Nat.add_zero] at eq
  simp only [remaining,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add,Nat.sub_zero] at eq
  exact ⟨⟨c,eq⟩,h.hdr,h.frame,h.keep⟩

/-- `Inv` for `rows1`, whose rows hand no carry on. -/
structure Inv1 (s₀ : State) (B : Addr) (Z w a n k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi=B
  indexI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 (8*k)
  keep : Keep mmRegs s₀ s
  frame : Frm B (ranges w) s₀.mem s.mem
  val : ∃ c, wv s.mem B (rawBase w) (2*w)+2^(128*w)*c+remaining s₀.mem B (slot w a) n k=
    wv s₀.mem B (rawBase w) (2*w)+remaining s₀.mem B (slot w a) n 0

private theorem advance1 {W W' R C D S S' T A : Nat}
    (prev : W+R*C+S=T) (step : W'+R*D=W+A) (rest : S=A+S') : W'+R*(C+D)+S'=T := by grind

theorem step1_inv {s₀ s : State} {B : Addr} {Z w a n k : Nat} {mi : BitVec 64}
    {ps : List (Nat × Nat)} (hv : Ops s₀.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hZ : slot w 8≤Z) (hw : w<2^31) (hwN : w=8*n) (hk : k<n-1)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (h : Inv1 s₀ B Z w a n k mi s) :
    WP isa (AdxTiledSquare.row1 ca) s fun t => t.zf=some (decide (k+1=n-1)) ∧ Inv1 s₀ B Z w a n (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8≤(2 : Nat)^64 := by omega_arith
  refine WP.mono (row1_ok h.scr h.rdi h.hdr (frame_ops hv h.frame) pa hZ hw (by omega_arith : w=8*k+8+8*(n-k-1))
    (by omega_arith) ha ha1 ha2 h.indexI) fun t ⟨zt,it,⟨d,eq⟩,ht,ft,kt⟩ => ?_
  rw [input_preserved ha ha1 ha2 (by omega_arith : 8*k+8≤w) Z64 h.frame,
    input_preserved ha ha1 ha2 (by omega_arith : (8*k+8)+8*(n-k-1)≤w) Z64 h.frame] at eq
  rw [show 64*(8*k+(8*k+8))=512*(2*k+1) by omega_arith,
    show slot w a+8*(8*k)=slot w a+64*k by omega_arith,
    show slot w a+8*(8*k+8)=slot w a+64*(k+1) by omega_arith] at eq
  obtain ⟨c,prev⟩ := h.val
  refine ⟨?_,⟨h.scr.congr kt.2.2,ht,(kt.gpr (by decide)).trans h.rdi,?_,
    (h.keep.trans kt).mono (by decide),h.frame.trans ft,c+d,?_⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  · simpa only [show 8*(k+1)=8*k+8 by omega_arith] using it
  · exact advance1 prev eq (remaining_step s₀.mem B (slot w a) n k (by omega_arith))

theorem rows1_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hw : w<2^31) (hwN : w=8*n) (hn : 1<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) :
    WP isa (AdxTiledSquare.rows1 ca) s fun t =>
      (∃ c, wv t.mem B (rawBase w) (2*w)+2^(128*w)*c=
        wv s.mem B (rawBase w) (2*w)+Square.cross (2^512) (chunks s.mem B (slot w a)) n) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have iZ : 8*sFn 12+8≤Z := by have := hdr_lt_slot w 8 (show sFn 12<32 by decide); omega_arith
  have init : WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s fun t =>
      t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64) ∧ Keep [.rax] s t := by
    apply WP.keep [.rax] (Q := fun t => t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)) _ rfl
    xrun [State.ea,hdr,hd,hdrOff,hs.st iZ]; rfl
  unfold AdxTiledSquare.rows1
  refine WP.seq (WP.mono init fun u ⟨mu,ku⟩ => ?_)
  have ou : Outside B (8*sFn 12) 8 s.mem u.mem := by rw [mu]; exact writeW_outside _ _ _ (by decide)
  have fu : Frm B (ranges w) s.mem u.mem := by
    intro x hx
    apply ou x
    have := hx (8*sFn 12,32) (by simp [ranges]); omega_arith
  have h0 : Inv1 s B Z w a n 0 mi u :=
    ⟨hs.congr ku.2.2,frame_hdr hh fu,(ku.gpr (by decide)).trans hd,by rw [mu,word_writeW_self]; rfl,
      ku.mono (by decide),fu,0,by
        rw [ou.wv (by unfold rawBase slot hdrBytes sFn; omega_arith) (by unfold rawBase slot aAcc at *; omega_arith),Nat.mul_zero,Nat.add_zero]⟩
  apply wp_upto (a := 0) (N := n-1) (by omega_arith) (Inv1 s B Z w a n · mi)
    (fun _ _ hk _ h => step1_inv hv pa hZ hw hwN hk ha ha1 ha2 h) ?_ h0
  intro t h
  obtain ⟨c,eq⟩ := h.val
  rw [remaining_end s.mem B (slot w a) n (by omega_arith),Nat.add_zero] at eq
  simp only [remaining,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add,Nat.sub_zero] at eq
  exact ⟨⟨c,eq⟩,h.hdr,h.frame,h.keep⟩

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareChoice -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges)
open VG.Proof.Bignum.X86_64.AdxTri8 (chunks)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

private theorem cross_one (r : Nat) (f : Nat → Nat) : Square.cross r f 1=0 := by
  simp only [Square.cross,Square.value,Nat.zero_mul,Nat.add_zero]

theorem rowsTest_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hw : w<2^31) :
    WP isa (.block [.mov .rax (.mem (hdr sW)),.alu .cmp .rax (.imm 8)]) s fun t =>
      t.zf=some (decide (w=8)) ∧ t.mem=s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf=some (decide (w=8)) ∧ t.mem=s.mem) ?_ rfl)
    fun t ⟨⟨z,m⟩,k⟩ => ⟨z,m,k⟩
  xrun [State.ea,hdr,hd,hdrOff,hs.ld (show 8*sW+8≤Z by have := hdr_lt_slot w 8 (show sW<32 by decide); omega_arith),
    hh.hw,show (8 : BitVec 32).signExtend 64=BitVec.ofNat 64 8 from rfl,ofNat_sub_beq (by omega_arith : w<2^64) (by decide : 8<2^64)]

theorem rowsTest16_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hw : w<2^31) :
    WP isa (.block [.mov .rax (.mem (hdr sW)),.alu .cmp .rax (.imm 16)]) s fun t =>
      t.zf=some (decide (w=16)) ∧ t.mem=s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf=some (decide (w=16)) ∧ t.mem=s.mem) ?_ rfl)
    fun t ⟨⟨z,m⟩,k⟩ => ⟨z,m,k⟩
  xrun [State.ea,hdr,hd,hdrOff,hs.ld (show 8*sW+8≤Z by have := hdr_lt_slot w 8 (show sW<32 by decide); omega_arith),
    hh.hw,show (16 : BitVec 32).signExtend 64=BitVec.ofNat 64 16 from rfl,ofNat_sub_beq (by omega_arith : w<2^64) (by decide : 16<2^64)]

theorem rowsChoice_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hw : w<2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) :
    WP isa (AdxTiledSquare.rowsChoice ca) s fun t =>
      (∃ c, wv t.mem B (rawBase w) (2*w)+2^(128*w)*c=
        wv s.mem B (rawBase w) (2*w)+Square.cross (2^512) (chunks s.mem B (slot w a)) n) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledSquare.rowsChoice
  have test := rowsTest_ok hs hd hh hZ hw
  refine WP.seq (WP.mono test fun u ⟨zu,mu,ku⟩ => ?_)
  by_cases h8 : w=8
  · refine WP.ite true (by simp [eval,zu,h8]) (fun _ => WP.block_nil ?_) (by intro h; cases h)
    have km : Keep mmRegs s u := ku.mono (by decide)
    refine ⟨⟨0,?_⟩,mu ▸ hh,?_,km⟩
    swap
    · rw [mu]; exact Frm.refl _ _ _
    have n1 : n=1 := by omega_arith
    rw [mu,n1]
    simp only [cross_one,Nat.mul_zero,Nat.add_zero]
  · refine WP.ite false (by simp [eval,zu,h8]) (by intro h; cases h) (fun _ => ?_)
    have su := hs.congr ku.2.2
    have du : u.gpr .rdi=B := (ku.gpr (by decide)).trans hd
    refine WP.seq (WP.mono (rowsTest16_ok su du (mu ▸ hh) hZ hw) fun v ⟨zv,mv,kv⟩ => ?_)
    have sv := su.congr kv.2.2
    have dv : v.gpr .rdi=B := (kv.gpr (by decide)).trans du
    have mv' : v.mem=s.mem := mv.trans mu
    by_cases h16 : w=16
    · refine WP.ite true (by simp [eval,zv,h16]) (fun _ => ?_) (by intro h; cases h)
      refine WP.mono (rows1_ok sv dv (mv' ▸ hh) hZ (mv' ▸ hv) pa hw hwN
        (by omega_arith) ha ha1 ha2) fun t ⟨vt,ht,ft,kt⟩ => ?_
      rw [mv'] at vt ft
      exact ⟨vt,ht,ft,((ku.trans kv).trans kt).mono (by decide)⟩
    · refine WP.ite false (by simp [eval,zv,h16]) (by intro h; cases h) (fun _ => ?_)
      refine WP.mono (rows_ok sv dv (mv' ▸ hh) hZ (mv' ▸ hv) pa hw hwN
        (by omega_arith) ha ha1 ha2) fun t ⟨vt,ht,ft,kt⟩ => ?_
      rw [mv'] at vt ft
      exact ⟨vt,ht,ft,((ku.trans kv).trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end
