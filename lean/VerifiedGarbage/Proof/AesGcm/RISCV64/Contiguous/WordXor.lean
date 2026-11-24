module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
public import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! # Process eight plaintext bytes per aligned XOR step, with either buffer layout -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem xorBytes_add (m : Mem) (X K : Addr) (i j : Nat) :
    xorBytes m X K (i+j) = xorBytes m X K i ++ xorBytes m (X+BitVec.ofNat 64 i) (K+BitVec.ofNat 64 i) j := by
  simp only [xorBytes,Cmac.bytesAt_add]
  apply List.zipWith_append
  simp [bytesAt]

private theorem afterWritten {X O : Addr} {i n b : Nat} (alias : X=O ∨ (⟨X,n⟩ : Region).Disjoint ⟨O,n⟩)
    (bound : i+b≤n) (fit : n<2^64) :
    (⟨X+BitVec.ofNat 64 i,b⟩ : Region).Disjoint ⟨O,i⟩ := by
  rcases alias with rfl | apart
  · simpa using Offset.disjoint X (d := i) (n := b) (e := 0) (k := i) (.inr (by omega)) (by omega) (by omega)
  · exact (apart.sub_left (Offset.sub_base X bound)).sub_right (Region.sub_prefix (by omega))

theorem xorWord_append {m : Mem} {X K O : Addr} {i n : Nat} (h : Alias true X O n)
    (mask : (⟨K,n⟩ : Region).Disjoint ⟨O,n⟩) (bound : i+8≤n) (fit : n<2^64) :
    let v := writeBytes m O (xorBytes m X K i)
    v.writeW (O+BitVec.ofNat 64 i) (v.readW (X+BitVec.ofNat 64 i) 64 ^^^ v.readW (K+BitVec.ofNat 64 i) 64) =
      writeBytes m O (xorBytes m X K (i+8)) := by
  dsimp only
  let v := writeBytes m O (xorBytes m X K i)
  have f : Frame [⟨O,i⟩] m v := writeBytes_frame _ _ _ (by rw [length_xorBytes]; exact Region.contains_self _ _)
  have rd (A : Addr) (sep : (⟨A+BitVec.ofNat 64 i,8⟩ : Region).Disjoint ⟨O,i⟩) :
      v.readW (A+BitVec.ofNat 64 i) 64 = m.readW (A+BitVec.ofNat 64 i) 64 :=
    f.readW (r := ⟨_,8⟩) (Region.contains_self _ _) (fun _ hr => List.mem_singleton.mp hr ▸ sep) (by decide)
  change v.writeW _ (v.readW _ _ ^^^ v.readW _ _) = _
  rw [rd X (afterWritten h.buffers bound fit),rd K (afterWritten (.inr mask) bound fit)]
  change v.write _ 8 _ = _
  rw [write_eq_writeBytes]
  change writeBytes v _ (Cmac.le8 (m.readW (X+BitVec.ofNat 64 i) 64 ^^^ m.readW (K+BitVec.ofNat 64 i) 64)) = _
  rw [Cmac.le8_xor,Cmac.le8_readW,Cmac.le8_readW]
  have a := writeBytes_append m O (xorBytes m X K i) (xorBytes m (X+BitVec.ofNat 64 i) (K+BitVec.ofNat 64 i) 8)
    (by rw [length_xorBytes,length_xorBytes];omega)
  rw [length_xorBytes,←xorBytes_add] at a
  exact a

abbrev wordBody : List Instr :=
  [.load .d .t0 .a1 0,.load .d .a3 .a0 0,.logic .xor .t0 .t0 .a3,.store .d .t0 .a4 0,
   .addi .a0 .a0 8,.addi .a1 .a1 8,.addi .a4 .a4 8,.addi .a5 .a5 (-1)]

theorem wordStep {s : State} {X K O : Addr} {c : BitVec 64}
    (x : s.gpr .a1=X) (k : s.gpr .a0=K) (o : s.gpr .a4=O) (q : s.gpr .a5=c)
    (ax : X.toNat%8=0) (ak : K.toNat%8=0) (ao : O.toNat%8=0)
    (rx : InRegions (s.rd++s.wr) X 8) (rk : InRegions (s.rd++s.wr) K 8) (wo : InRegions s.wr O 8) :
    WP isa (.block wordBody) s fun t =>
      t.mem=s.mem.writeW O (s.mem.readW X 64 ^^^ s.mem.readW K 64) ∧
      t.gpr .a0=K+8 ∧ t.gpr .a1=X+8 ∧ t.gpr .a4=O+8 ∧ t.gpr .a5=c-1 ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a3 → r ≠ .a4 → r ≠ .a5 → t.gpr r=s.gpr r) ∧ Keeps' s t := by
  unfold wordBody
  crun [x,k,o,q,ax,ak,ao,rx,rk,wo,write_8]
  exact ⟨rfl,fun r a b c d e f => by simp [a,b,c,d,e,f],⟨rfl,rfl,rfl⟩⟩

abbrev off8 (A : Addr) (i : Nat) := A+BitVec.ofNat 64 (8*i)

private theorem next8 (A : Addr) (i : Nat) : off8 A i+8 = off8 A (i+1) := by
  change A+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 8=_
  rw [add_ofNat_assoc]; congr 2

structure WordState (s : State) (X K O : Addr) (q i : Nat) (t : State) : Prop where
  a0 : t.gpr .a0=off8 K i
  a1 : t.gpr .a1=off8 X i
  a4 : t.gpr .a4=off8 O i
  a5 : t.gpr .a5=BitVec.ofNat 64 (q-i)
  a2 : t.gpr .a2=s.gpr .a2
  saved : ∀ r ∈ preserved, t.gpr r=s.gpr r
  mem : t.mem=writeBytes s.mem O (xorBytes s.mem X K (8*i))
  keep : Keeps' s t

theorem wordLoop {s : State} {X K O : Addr} {q n : Nat} (qn : 8*q≤n) (pos : 0<q) (fit : n<2^64)
    (x : s.gpr .a1=X) (k : s.gpr .a0=K) (o : s.gpr .a4=O) (cq : s.gpr .a5=BitVec.ofNat 64 q)
    (ax : X.toNat%8=0) (ak : K.toNat%8=0) (ao : O.toNat%8=0)
    (rx : Covers [⟨X,n⟩] (s.rd++s.wr)) (rk : Covers [⟨K,n⟩] (s.rd++s.wr)) (wo : Covers [⟨O,n⟩] s.wr)
    (alias : Alias true X O n) (mask : (⟨K,n⟩ : Region).Disjoint ⟨O,n⟩) :
    WP isa (.loop (.block wordBody) (.nonzero .a5)) s (WordState s X K O q q) := by
  apply WP.loop (fun k t => ∃ i, k=q-i ∧ i<q ∧ WordState s X K O q i t) ?_ (q-0) _
    ⟨0,rfl,pos,⟨by simpa [off8] using k,by simpa [off8] using x,by simpa [off8] using o,by simpa using cq,
      rfl,fun _ _ => rfl,by simp [xorBytes,bytesAt,writeBytes_nil],⟨rfl,rfl,rfl⟩⟩⟩
  rintro l t ⟨i,rfl,hi,h⟩
  have within : 8*i+8≤n := by omega
  refine WP.mono (wordStep h.a1 h.a0 h.a4 h.a5 (Spill.al8 ax (by omega)) (Spill.al8 ak (by omega)) (Spill.al8 ao (by omega))
    (by rw [h.keep.rd,h.keep.wr];exact in_off rx within fit) (by rw [h.keep.rd,h.keep.wr];exact in_off rk within fit)
    (by rw [h.keep.wr];exact in_off wo within fit)) ?_
  rintro t' ⟨m,a0,a1,a4,a5,other,keep⟩
  have next : WordState s X K O q (i+1) t' := by
    refine ⟨a0.trans (next8 K i),a1.trans (next8 X i),a4.trans (next8 O i),a5.trans (dec64 hi (by omega)),
      (other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.a2,?_,?_,
      ⟨keep.rd.trans h.keep.rd,keep.wr.trans h.keep.wr,keep.sp.trans h.keep.sp⟩⟩
    · intro r hr
      exact (other r (by revert r;decide) (by revert r;decide) (by revert r;decide) (by revert r;decide)
        (by revert r;decide) (by revert r;decide)).trans (h.saved r hr)
    · rw [m,h.mem,Nat.mul_add,Nat.mul_one]
      exact xorWord_append alias mask within fit
  have ev : isa.eval (.nonzero .a5) t' = some !decide (i+1=q) := by
    change some (t'.gpr .a5 != 0) = _
    rw [next.a5,nz_dec hi (by omega)]
  by_cases last : i+1=q
  · exact .inl ⟨by rw [ev]; simp [last],last ▸ next⟩
  · exact .inr ⟨by rw [ev]; simp [last],q-(i+1),by omega,i+1,rfl,by omega,next⟩

structure TextOut (s : State) (K X O : Addr) (n : Nat) (t : State) : Prop where
  mem : t.mem=writeBytes s.mem O (xorBytes s.mem X K n)
  saved : ∀ r ∈ preserved, t.gpr r=s.gpr r
  keeps : Keeps' s t

private theorem suffix {s t : State} {X K O : Addr} {q r n : Nat} (size : 8*q+r=n) (fit : n<2^64)
    (a2 : t.gpr .a2=BitVec.ofNat 64 r) (h : WordState s X K O q q t)
    (rx : Covers [⟨X,n⟩] (s.rd++s.wr)) (rk : Covers [⟨K,n⟩] (s.rd++s.wr)) (wo : Covers [⟨O,n⟩] s.wr)
    (alias : Alias true X O n) (mask : (⟨K,n⟩ : Region).Disjoint ⟨O,n⟩) :
    WP isa VG.Impl.AesGcm.RISCV64.Contiguous.xorRemainder t (TextOut s K X O n) := by
  have ev : isa.eval (.zero .a2) t = some (decide (r=0)) := by
    change some (t.gpr .a2 == 0)=_
    rw [a2,Steps.ofNat_beq_zero (by omega)]
  apply WP.ite _ ev
  · intro z
    obtain rfl : r=0 := by simpa using z
    exact WP.block_nil ⟨by simpa [←size] using h.mem,h.saved,h.keep⟩
  · intro nz
    have pos : 0<r := by
      have : r≠0 := by simpa using nz
      omega
    have pre : XorPre true t (off8 K q) (off8 X q) (off8 O q) r :=
      ⟨h.a0,h.a1,h.a4,a2,pos,by omega,by rw [h.keep.rd,h.keep.wr];exact covers_off rk (by omega) fit,
        by rw [h.keep.rd,h.keep.wr];exact covers_off rx (by omega) fit,
        by rw [h.keep.wr];exact covers_off wo (by omega) fit,
        (mask.sub_left (Offset.sub_base K (by omega))).sub_right (Offset.sub_base O (by omega)),alias.drop (by omega)⟩
    refine WP.mono (xorLoopWith_ok _ _ pre) fun u ⟨mem,post⟩ => ⟨?_,?_,
      ⟨post.keeps.1.trans h.keep.rd,post.keeps.2.1.trans h.keep.wr,post.keeps.2.2.trans h.keep.sp⟩⟩
    · have frame : Frame [⟨O,8*q⟩] s.mem t.mem := by
        rw [h.mem]; exact writeBytes_frame _ _ _ (by rw [length_xorBytes]; exact Region.contains_self _ _)
      have read (A : Addr) (sep : A=O ∨ (⟨A,n⟩ : Region).Disjoint ⟨O,n⟩) :
          bytesAt t.mem (off8 A q) r=bytesAt s.mem (off8 A q) r :=
        bytesAt_frame frame (fun _ hr => List.mem_singleton.mp hr ▸ afterWritten sep (by omega) fit) (by omega)
      have v : xorBytes t.mem (off8 X q) (off8 K q) r=xorBytes s.mem (off8 X q) (off8 K q) r := by
        unfold xorBytes; rw [read X alias.buffers,read K (.inr mask)]
      rw [mem,v,h.mem,←size]
      have ap := writeBytes_append s.mem O (xorBytes s.mem X K (8*q)) (xorBytes s.mem (off8 X q) (off8 K q) r)
        (by rw [length_xorBytes,length_xorBytes];omega)
      rw [length_xorBytes] at ap
      rw [xorBytes_add]; exact ap
    · intro j hj
      exact (post.other j (by revert j;decide) (by revert j;decide) (by revert j;decide) (by revert j;decide)
        (by revert j;decide) (by revert j;decide)).trans (h.saved j hj)

private theorem lowThree (x : BitVec 64) : x &&& 7 = BitVec.ofNat 64 (x.toNat%8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,show (7 : BitVec 64).toNat = 2^3-1 from rfl,Nat.and_two_pow_sub_one_eq_mod,BitVec.toNat_ofNat]
  omega

private theorem shiftThree {n : Nat} (fit : n<2^64) : (BitVec.ofNat 64 n >>> 3)=BitVec.ofNat 64 (n/8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem xorQwords_wp {s : State} {K X O : Addr} {n : Nat} (h : XorPre true s K X O n)
    (ax : X.toNat%8=0) (ak : K.toNat%8=0) (ao : O.toNat%8=0) :
    WP isa VG.Impl.AesGcm.RISCV64.Contiguous.xorQwords s (TextOut s K X O n) := by
  have fit := h.lt
  apply WP.seq
  refine Steps.wp_srl (sh := 3) (by decide) fun v a => Steps.wp_andi (by decide) fun u b => WP.block_nil ?_
  have rq : u.gpr .a5=BitVec.ofNat 64 (n/8) := by
    rw [b.other _ (by decide),a.gpr,h.a2,shiftThree fit]
  have rr : u.gpr .a2=BitVec.ofNat 64 (n%8) := by
    rw [b.gpr,a.other _ (by decide),h.a2,show BitVec.ofInt 64 7=(7 : BitVec 64) from rfl,lowThree,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]
  have ku : Keeps s u := ⟨b.mem.trans a.mem,b.rd.trans a.rd,b.wr.trans a.wr,b.sp.trans a.sp⟩
  have gu (j : Reg) (x : j ≠ .a5) (y : j≠ .a2) : u.gpr j=s.gpr j := (b.other j y).trans (a.other j x)
  have ux := (gu .a1 (by decide) (by decide)).trans h.a1
  have uk := (gu .a0 (by decide) (by decide)).trans h.a0
  have uo : u.gpr .a4=O := (gu .a4 (by decide) (by decide)).trans h.out
  have rx : Covers [⟨X,n⟩] (u.rd++u.wr) := by rw [ku.rd,ku.wr];exact h.rdX
  have rk : Covers [⟨K,n⟩] (u.rd++u.wr) := by rw [ku.rd,ku.wr];exact h.rdK
  have wo : Covers [⟨O,n⟩] u.wr := ku.wr ▸ h.wr
  have ev : isa.eval (.zero .a5) u=some (decide (n/8=0)) := by
    change some (u.gpr .a5 == 0)=_
    rw [rq,Steps.ofNat_beq_zero (by omega)]
  have run : WP isa (.ite (.zero .a5) (.block []) (.loop (.block wordBody) (.nonzero .a5))) u
      (WordState u X K O (n/8) (n/8)) := by
    apply WP.ite _ ev
    · intro z
      have z' : n/8=0 := by simpa using z
      rw [z'] at rq ⊢
      exact WP.block_nil ⟨by simpa [off8] using uk,by simpa [off8] using ux,by simpa [off8] using uo,
        rq,rfl,fun _ _ => rfl,by simp [xorBytes,bytesAt,writeBytes_nil],⟨rfl,rfl,rfl⟩⟩
    · intro nz
      exact wordLoop (by omega) (by have : n/8 ≠ 0 := of_decide_eq_false nz; omega) fit ux uk uo rq ax ak ao rx rk wo h.alias h.disj
  apply WP.seq
  refine WP.mono run fun t w => WP.mono (suffix (show 8*(n/8)+n%8=n by omega) fit (w.a2.trans rr) w rx rk wo h.alias h.disj) ?_
  intro t' out
  exact ⟨by rw [out.mem,ku.mem],fun j hj => (out.saved j hj).trans (gu j (by revert j;decide) (by revert j;decide)),
    ⟨out.keeps.rd.trans ku.rd,out.keeps.wr.trans ku.wr,out.keeps.sp.trans ku.sp⟩⟩

/-- The data and mask read by the aligned and byte paths agree for either buffer layout. -/
theorem xorText_wp {s : State} {K X O : Addr} {n : Nat} (h : XorPre true s K X O n) (ak : K.toNat%8=0) :
    WP isa VG.Impl.AesGcm.RISCV64.Contiguous.xorText s (TextOut s K X O n) := by
  apply WP.seq
  refine Steps.wp_or fun v a => Steps.wp_andi (by decide) fun t b => WP.block_nil ?_
  have flag : t.gpr .t0 = (X ||| O) &&& 7 := by
    rw [b.gpr,a.gpr,h.a1,show s.gpr .a4=O from h.out];rfl
  have keep : Keeps s t := ⟨b.mem.trans a.mem,b.rd.trans a.rd,b.wr.trans a.wr,b.sp.trans a.sp⟩
  have g (j : Reg) (ne : j≠.t0) : t.gpr j=s.gpr j := (b.other j ne).trans (a.other j ne)
  have pre : XorPre true t K X O n := ⟨(g _ (by decide)).trans h.a0,(g _ (by decide)).trans h.a1,
    (g _ (by decide)).trans h.out,(g _ (by decide)).trans h.a2,h.pos,h.lt,
    by rw [keep.rd,keep.wr];exact h.rdK,by rw [keep.rd,keep.wr];exact h.rdX,keep.wr ▸ h.wr,h.disj,h.alias⟩
  have ev : isa.eval (.zero .t0) t = some (t.gpr .t0 == 0) := rfl
  apply WP.ite _ ev
  · intro z
    have zero := beq_iff_eq.mp z
    rw [flag,BitVec.and_or_distrib_right] at zero
    obtain ⟨zx,zo⟩ := BitVec.or_eq_zero_iff.mp zero
    rw [lowThree] at zx zo
    refine WP.mono (xorQwords_wp pre ((ofNat_eq_zero (by omega)).mp zx) ak ((ofNat_eq_zero (by omega)).mp zo)) fun u out => ?_
    exact ⟨by rw [out.mem,keep.mem],fun j hj => (out.saved j hj).trans (g j (by revert j;decide)),
      ⟨out.keeps.rd.trans keep.rd,out.keeps.wr.trans keep.wr,out.keeps.sp.trans keep.sp⟩⟩
  · intro _
    refine WP.mono (xorLoopWith_ok _ _ pre) fun u ⟨mem,out⟩ => ⟨by rw [mem,keep.mem],?_,
      ⟨out.keeps.1.trans keep.rd,out.keeps.2.1.trans keep.wr,out.keeps.2.2.trans keep.sp⟩⟩
    exact fun j hj => (out.other j (by revert j;decide) (by revert j;decide) (by revert j;decide)
      (by revert j;decide) (by revert j;decide) (by revert j;decide)).trans (g j (by revert j;decide))

end VG.Proof.AesGcm.RISCV64.Contiguous
