module

public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Compiled
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Fusion
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem
public import VerifiedGarbage.Impl.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Schedule
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.AbsorbPlan
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Permute
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Transport
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Pad
public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezeCode
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.WordSemantic
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Word
public import VerifiedGarbage.Impl.MlKem.AArch64.Top
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Link
import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Impl.MlKem.AArch64.FixedHash

/-! ### `MlKem.AArch64.FixedHash.CompiledShapes`, which only this module used -/

section

/-! # The fixed hash's shapes are their proof-oriented decompositions, for any permutation

Each shape's code with the permutation's calls erased (over `hole`) has the
normal form of its decomposition (`kernel_rfl`); with the holes filled by any
permutation `c` (`kernel_rfl`, with `c` a variable), so do the two
(`Fusion.Same.of_fillHoles`). -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-- The decomposition of a shape is its code, for any permutation `c`, from the
code with holes: both are it with the holes filled with `c`, and the two have
the same normal form. -/
theorem compiled_same {c : Impl.Sha3.AArch64.Callee} {sc : Reg} {st wk rate sfx : Nat}
    {ins outs : List Piece}
    (hc : compiled c sc st wk rate sfx ins outs =
      Code.fillHoles c.name c.code (compiled hole sc st wk rate sfx ins outs))
    (hh : Impl.MlKem.AArch64.FixedHash.code c sc st wk rate sfx ins outs =
      Code.fillHoles c.name c.code (Impl.MlKem.AArch64.FixedHash.code hole sc st wk rate sfx ins outs))
    (h : Fusion.normalize (compiled hole sc st wk rate sfx ins outs) =
      Fusion.normalize (Impl.MlKem.AArch64.FixedHash.code hole sc st wk rate sfx ins outs)) :
    Fusion.Same (compiled c sc st wk rate sfx ins outs)
      (Impl.MlKem.AArch64.FixedHash.code c sc st wk rate sfx ins outs) :=
  Fusion.Same.of_fillHoles hc hh h

theorem kgG768_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem prf768_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem enG768_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem deG768_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,2336,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,2336,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem kgG1024_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]) :=
 kgG768_compiled c

theorem enG1024_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩]) :=
 enG768_compiled c

theorem deG1024_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,3104,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,3104,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end VG.Proof.MlKem.AArch64.FixedHash

end

end

/-! ### `MlKem.AArch64.FixedHash.Schedules`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem kgG768_schedule : certified 72 [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩]=true := by decide +kernel

theorem prf768_schedule : certified 136 [⟨.x28,KEM.RB,33⟩]=true := by decide +kernel

theorem enG768_schedule : certified 72 [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩]=true := by decide +kernel

theorem deG768_schedule : certified 72 [⟨.x28,KEM.MB,32⟩,⟨.x25,2336,32⟩]=true := by decide +kernel

theorem kgG1024_schedule : certified 72 [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩]=true := by decide +kernel

theorem enG1024_schedule : certified 72 [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩]=true := by decide +kernel

theorem deG1024_schedule : certified 72 [⟨.x28,KEM.MB,32⟩,⟨.x25,3104,32⟩]=true := by decide +kernel

end VG.Proof.MlKem.AArch64.FixedHash

end

end

/-! ### `MlKem.AArch64.FixedHash.Finish`, which only this module used -/

section

/-! ### `MlKem.AArch64.FixedHash.PadState`, which only this module used -/

section

/-! # Padding preserves the hash workspace and establishes the permutation input -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64

theorem pad_kept {s : State} {sc : Reg} {st wk rate pos sfx : Nat}
    (hs : HSetup sc st wk rate s) (hp : pos<rate) (hoff : st+rate≤4096) :
    WP isa (.block (padCode sc st rate pos sfx)) s fun t=>
      Kept [STr sc st s] s t ∧ t.gpr .x30=s.gpr .x30 ∧
      Spec.Sha3.stateAt t.mem (s.gpr sc+BitVec.ofNat 64 st)=
        Proof.Sha3.xorByte (Proof.Sha3.xorByte (Spec.Sha3.stateAt s.mem (s.gpr sc+BitVec.ofNat 64 st))
          pos (BitVec.ofNat 8 sfx)) (rate-1) 128 := by
  have hr := Proof.Sha3.rate_bounds hs.hrate
  have ne : ∀r∈preserved,r≠Reg.x9 ∧ r≠Reg.x10 := by decide
  refine WP.mono (pad_ok (ne _ hs.hsc.1).1 (ne _ hs.hsc.1).2 (by omega_using [hp]) (by omega_using [hr]) hp hoff
    (fun a n h=>hs.cov a n (by
      obtain ⟨r,hr,hc⟩:=h
      exact ⟨r,List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr)),hc⟩))) fun t ⟨hk,hf,he⟩=>?_
  exact ⟨⟨fun r hr _=>hk.get r (by have hh:=ne r hr; simp [hh.1,hh.2]),
    hk.sp,hk.rd,hk.wr,hf,hk.vcs⟩,hk.get .x30 (by decide),he⟩

theorem pad_repr {s : State} {sc : Reg} {st wk rate pos sfx : Nat} {msg : List Byte}
    (hs : HSetup sc st wk rate s) (hoff : st+rate≤4096)
    (repr : Spec.Sha3.Repr s.mem (s.gpr sc+BitVec.ofNat 64 st) rate msg)
    (hp : pos=msg.length%rate) :
    WP isa (.block (padCode sc st rate pos sfx)) s fun t=>
      Kept [STr sc st s] s t ∧ t.gpr .x30=s.gpr .x30 ∧
      Spec.Sha3.keccakF (Spec.Sha3.stateAt t.mem (s.gpr sc+BitVec.ofNat 64 st))=
        Spec.Sha3.absorb rate (Spec.Sha3.pad rate (BitVec.ofNat 8 sfx) msg) := by
  have hr := Proof.Sha3.rate_bounds hs.hrate
  refine WP.mono (pad_kept hs (by rw [hp]; exact Nat.mod_lt _ (by omega_using [hr])) hoff) fun t ⟨hk,h30,he⟩=>?_
  refine ⟨hk,h30,?_⟩
  rw [he,hp,repr,Proof.Sha3.absorb_pad (by omega_using [hr]) (by omega_using [hr])]
  rfl

end VG.Proof.MlKem.AArch64.FixedHash

end

end

/-! ### `MlKem.AArch64.FixedHash.Squeeze`, which only this module used -/

section

/-! ### `MlKem.AArch64.FixedHash.SqueezeTransport`, which only this module used -/

section

/-! # Output pointers and permissions survive fixed word copies -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem squeeze_ne : ∀r∈preserved,r∉[Reg.x2,.x9] := by decide

theorem hsetup_copy {s t : State} {sc : Reg} {st wk rate : Nat}
    (h : HSetup sc st wk rate s) (k : Keep [.x2,.x9] s t) : HSetup sc st wk rate t := by
  have eq := k.get sc (squeeze_ne _ h.hsc.1)
  refine ⟨h.hsc,h.hst,h.hwk,h.hrate,?_,?_,?_,?_,?_⟩
  · simpa only [eq] using h.d
  · simpa only [k.sp] using h.sp16
  · simpa only [eq,stk,k.sp] using h.kst
  · simpa only [eq,stk,k.sp] using h.kwk
  · simpa only [eq,k.wr] using h.cov

theorem piece_copy {s t : State} {sc : Reg} {st wk rate : Nat} {p : Piece}
    (h : HSetup sc st wk rate s) (hp : PieceOk sc st wk s true p) (k : Keep [.x2,.x9] s t) :
    PieceOk sc st wk t true p := by
  have eq := k.get sc (squeeze_ne _ h.hsc.1)
  have eb := k.get p.base (squeeze_ne _ hp.base.1)
  refine ⟨hp.base,hp.off,hp.len,?_,?_,?_,?_⟩
  · simpa only [preg,STr,eq,eb] using hp.dst
  · simpa only [preg,WKr,eq,eb] using hp.dwk
  · simpa only [preg,stk,eb,k.sp] using hp.stk
  · simpa only [preg,eb,k.wr,↓reduceIte] using hp.cov

theorem preg_copy {s t : State} {sc : Reg} {st wk : Nat} {p : Piece}
    (hp : PieceOk sc st wk s true p) (k : Keep [.x2,.x9] s t) : preg t p=preg s p := by
  unfold preg
  rw [k.get p.base (squeeze_ne _ hp.base.1)]

theorem outs_copy {s t : State} {sc : Reg} {st wk : Nat} {ps : List Piece}
    (hp : ∀p∈ps,PieceOk sc st wk s true p) (k : Keep [.x2,.x9] s t)
    {m : Mem} {rate pos : Nat} {A : Spec.Sha3.State} : Outs t m rate A pos ps↔Outs s m rate A pos ps := by
  induction ps generalizing pos with
  | nil=>rfl
  | cons p ps ih=>
    simp only [Outs,k.get p.base (squeeze_ne _ (hp _ (by simp)).base.1)]
    exact and_congr Iff.rfl (ih (fun p hh=>hp p (by simp [hh])))

end VG.Proof.MlKem.AArch64.FixedHash

end

end

/-! ### `MlKem.AArch64.FixedHash.SqueezePiece`, which only this module used -/

section

/-! ### `MlKem.AArch64.FixedHash.SqueezeWords`, which only this module used -/

section

/-! # Copy a bounded sequence of state words without touching the source -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem

def WordCopies (s : State) (src dst : Addr) (len n : Nat) (t : State) : Prop :=
 Keep [.x2,.x9] s t ∧ Frame [⟨dst,len⟩] s.mem t.mem ∧
 ∀j<8*n,t.mem (dst+BitVec.ofNat 64 j)=s.mem (src+BitVec.ofNat 64 j)

theorem squeezeWords_ok {s : State} {sc base : Reg} {srcOff dstOff N : Nat}
    (sc2 : sc≠.x2) (sc9 : sc≠.x9) (b2 : base≠.x2) (b9 : base≠.x9)
    (sa : srcOff%8=0) (sf : srcOff+8*N≤32768) (df : dstOff+8*N≤65536)
    (read : ∀i<N,InRegions (s.rd++s.wr) (s.gpr sc+BitVec.ofNat 64 (srcOff+8*i)) 8)
    (write : ∀i<N,InRegions s.wr (s.gpr base+BitVec.ofNat 64 (dstOff+8*i)) 8)
    (apart : (⟨s.gpr sc+BitVec.ofNat 64 srcOff,8*N⟩:Region).Disjoint
      ⟨s.gpr base+BitVec.ofNat 64 dstOff,8*N⟩) :
    WP isa (.block ((List.range N).flatMap fun i=>
      ([.ldr .x .x9 sc (srcOff+8*i)] : List Instr) ++ ptrTo .x2 base (dstOff+8*i) ++ ([.str .x .x9 .x2 0] : List Instr))) s
      (WordCopies s (s.gpr sc+BitVec.ofNat 64 srcOff) (s.gpr base+BitVec.ofNat 64 dstOff) (8*N) N) := by
  let src := s.gpr sc+BitVec.ofNat 64 srcOff
  let dst := s.gpr base+BitVec.ofNat 64 dstOff
  refine wp_range_flatMap (M:=isa) (N:=N) (WordCopies s src dst (8*N)) ?_ N (Nat.le_refl _) s
    ⟨Keep.refl _ _,Frame.refl _ _,by intro j hj; omega⟩
  intro i a hi ha
  have asrc := ha.1.get sc (by simp [sc2,sc9])
  have adst := ha.1.get base (by simp [b2,b9])
  refine WP.mono (squeezeWord_ok (src:=srcOff+8*i) (off:=dstOff+8*i) b2 b9 (by omega_using [df, hi])
    ⟨by omega_using [sa],by omega_using [sf, hi]⟩
    (by rw [ha.1.rd,ha.1.wr,asrc]; exact read i hi)
    (by rw [ha.1.wr,adst]; exact write i hi)) fun t ht=>?_
  have mt : t.mem=a.mem.writeW (dst+BitVec.ofNat 64 (8*i)) (a.mem.readW (src+BitVec.ofNat 64 (8*i)) 64) := by
    have hh:=ht.2
    rw [adst,asrc,←ptr_add,←ptr_add] at hh
    exact hh
  have step : Frame [⟨dst+BitVec.ofNat 64 (8*i),8⟩] a.mem t.mem := by
    rw [mt]
    exact Frame.writeW (r:=⟨dst+BitVec.ofNat 64 (8*i),8⟩) (Frame.refl _ _) (by simp) _ (by simp [Region.Contains])
  refine ⟨(ha.1.trans ht.1).mono (by simp),?_,?_⟩
  · rw [mt]
    exact Frame.writeW (r:=⟨dst,8*N⟩) ha.2.1 (by simp) _ (Offset.contains_base dst (by omega_using [hi]) (by omega_using [sf, hi]))
  · intro j hj
    by_cases old : j<8*i
    · rw [bytes_frame step (p:=dst) (len:=8*i) (fun r hr=>by
        rw [List.mem_singleton.mp hr]
        exact Offset.base_disjoint dst (by omega_using []) (by omega_using [sf, hi])) (by omega_using [sf, hi]) j old]
      exact ha.2.2 j old
    · have hk : j-8*i<8 := by omega_using [hj]
      have out := squeezeWord_bytes a.mem (src+BitVec.ofNat 64 (8*i)) (dst+BitVec.ofNat 64 (8*i))
      rw [←mt] at out
      have byte := congrArg (fun bs : List Byte=>bs[j-8*i]?.getD 0) out
      simp only [←List.getD_eq_getElem?_getD,bytesAt_getD _ _ hk,ptr_add] at byte
      have idx : 8*i+(j-8*i)=j := by omega_using [old]
      rw [idx] at byte
      rw [byte]
      exact bytes_frame ha.2.1 (p:=src) (len:=8*N)
        (fun r hr=>by rw [List.mem_singleton.mp hr]; exact apart) (by omega_using [sf]) j (by omega_using [hi, hj])

end VG.Proof.MlKem.AArch64.FixedHash

end

end


/-! # One output piece is the consecutive bytes of the padded permutation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt stateAt squeezeFrom)

theorem bytesAt_squeeze {m : Mem} {p : Addr} {rate pos len : Nat}
    (hr : 0<rate) (hr200 : rate≤200) (fit : pos+len≤rate) :
    bytesAt m (p+BitVec.ofNat 64 pos) len=squeezeFrom rate (stateAt m p) pos len := by
  apply List.ext_getElem
  · rw [bytesAt_length,Proof.Sha3.length_squeezeFrom hr hr200]
  · intro i hi hj
    have ilt : i<len := by simpa only [bytesAt_length] using hi
    rw [bytesAt_getElem,Proof.Sha3.squeezeFrom_getElem hr hr200 _ ilt,
      Nat.div_eq_of_lt (by omega_using [fit, ilt] : pos+i<rate),Nat.mod_eq_of_lt (by omega_using [fit, ilt] : pos+i<rate)]
    change m _=Proof.Sha3.byteOf (stateAt m p) (pos+i)
    rw [Proof.Sha3.byteOf_stateAt _ _ (by omega_using [hr200, fit, ilt]),ptr_add]

theorem squeezePiece_ok {s : State} {sc : Reg} {st wk rate pos : Nat} {p : Piece}
    (hs : HSetup sc st wk rate s) (ho : PieceOk sc st wk s true p)
    (sa : st%8=0) (pa : pos%8=0) (sf : st+rate≤32768)
    (df : p.off+p.len≤65536) (len : p.len%8=0) (fit : pos+p.len≤rate) :
    WP isa (.block (squeezePieceCode sc st pos p)) s fun t=>
      Keep [.x2,.x9] s t ∧ Frame [preg s p] s.mem t.mem ∧
      bytesAt t.mem (s.gpr p.base+BitVec.ofNat 64 p.off) p.len=
        squeezeFrom rate (stateAt s.mem (s.gpr sc+BitVec.ofNat 64 st)) pos p.len := by
  have hr := Proof.Sha3.rate_bounds hs.hrate
  have ne : ∀r∈preserved,r≠Reg.x2 ∧ r≠Reg.x9 := by decide
  have div : 8*(p.len/8)=p.len := by omega_using [len]
  have sub : Region.Sub ⟨s.gpr sc+BitVec.ofNat 64 (st+pos),8*(p.len/8)⟩ (STr sc st s) := by
    rw [←ptr_add,div]
    exact Offset.sub_base _ (by omega_using [fit, hr])
  have rd : ∀i<p.len/8,InRegions (s.rd++s.wr) (s.gpr sc+BitVec.ofNat 64 (st+pos+8*i)) 8 := by
    intro i hi
    rw [Nat.add_assoc,←ptr_add]
    exact covers_rw' hs.cov _ _ ⟨STr sc st s,by simp [STr],Offset.contains_base _ (by omega_using [fit, hr, hi]) (by omega_using [sf, fit, hi])⟩
  have wr : ∀i<p.len/8,InRegions s.wr (s.gpr p.base+BitVec.ofNat 64 (p.off+8*i)) 8 := by
    intro i hi
    rw [←ptr_add]
    exact ho.covW _ _ ⟨preg s p,by simp,Offset.contains_base _ (by omega_using [hi]) (by omega_using [df, hi])⟩
  refine WP.mono (squeezeWords_ok (N:=p.len/8) (ne _ hs.hsc.1).1 (ne _ hs.hsc.1).2
    (ne _ ho.base.1).1 (ne _ ho.base.1).2 (by omega_using [sa, pa]) (by omega_using [sf, fit]) (by omega_using [df]) rd wr
    (by rw [div]; exact ho.dst.symm.sub_left (by simpa only [div] using sub))) fun t ht=>?_
  refine ⟨ht.1,by simpa only [div] using ht.2.1,?_⟩
  rw [←bytesAt_squeeze (by omega_using [hr] : 0<rate) (by omega_using [hr] : rate≤200) fit]
  apply List.ext_getElem
  · simp only [bytesAt_length]
  · intro i hi hj
    have hh := ht.2.2 i (by simpa only [bytesAt_length,div] using hi)
    simpa only [bytesAt_getElem,ptr_add] using hh

end VG.Proof.MlKem.AArch64.FixedHash

end

end


/-! # Complete fixed-length single-block squeezing into disjoint output pieces -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Spec.Sha3 (stateAt bytesAt)

theorem squeeze_ok {sc : Reg} {st wk rate : Nat} (ps : List Piece) :
    ∀{s : State} {pos : Nat}, HSetup sc st wk rate s→
    (∀p∈ps,PieceOk sc st wk s true p)→
    ps.Pairwise (fun p q=>(preg s p).Disjoint (preg s q))→
    st%8=0→pos%8=0→st+rate≤32768→
    (∀p∈ps,p.off+p.len≤65536 ∧ p.len%8=0)→
    pos+(ps.map Piece.len).sum≤rate→
    WP isa (.block (squeezeCode sc st pos ps)) s fun t=>
      Keep [.x2,.x9] s t ∧ Frame (ps.map (preg s)) s.mem t.mem ∧
      Outs s t.mem rate (stateAt s.mem (s.gpr sc+BitVec.ofNat 64 st)) pos ps := by
  induction ps with
  | nil=>
    intro s pos hs hp sep sa pa sf of fit
    exact WP.block_nil ⟨Keep.refl _ _,Frame.refl _ _,trivial⟩
  | cons p ps ih=>
    intro s pos hs hp sep sa pa sf of fit
    have pp := hp p (by simp)
    have num := of p (by simp)
    have fitp : pos+p.len≤rate := by simp only [List.map_cons,List.sum_cons] at fit; omega_using [fit]
    change WP isa (.block (squeezePieceCode sc st pos p ++ squeezeCode sc st (pos+p.len) ps)) s _
    rw [WP.block_append_iff]
    refine WP.mono (squeezePiece_ok hs pp sa pa sf num.1 num.2 fitp) fun a ha=>?_
    have hp' : ∀q∈ps,PieceOk sc st wk s true q := fun q hq=>hp q (by simp [hq])
    have pregEq : ∀q∈ps,preg a q=preg s q := fun q hq=>preg_copy (hp' q hq) ha.1
    have maps : ps.map (preg a)=ps.map (preg s) := List.map_congr_left pregEq
    have sepa : ps.Pairwise (fun p q=>(preg a p).Disjoint (preg a q)) := by
      apply sep.tail.imp_of_mem
      intro x y hx hy hxy
      simpa only [pregEq x hx,pregEq y hy] using hxy
    have state : stateAt a.mem (a.gpr sc+BitVec.ofNat 64 st)=stateAt s.mem (s.gpr sc+BitVec.ofNat 64 st) := by
      rw [ha.1.get sc (squeeze_ne _ hs.hsc.1)]
      apply Proof.Sha3.stateAt_congr
      exact bytes_frame ha.2.1 (fun r hr=>by rw [List.mem_singleton.mp hr]; exact pp.dst.symm) (by decide)
    refine WP.mono (ih (hsetup_copy hs ha.1) (fun q hq=>piece_copy hs (hp' q hq) ha.1) sepa
      sa (by omega_using [pa, num]) sf (fun q hq=>of q (by simp [hq]))
      (by simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using fit)) fun t ht=>?_
    have frame : Frame (ps.map (preg s)) a.mem t.mem := by simpa only [maps] using ht.2.1
    refine ⟨(ha.1.trans ht.1).mono (by simp),?_,?_,?_⟩
    · exact (ha.2.1.mono (by intro r hr; simp only [List.mem_singleton] at hr; rw [hr]; simp)).trans
        (frame.mono (by intro r hr; exact List.mem_cons_of_mem _ hr))
    · rw [bytesAt_frame frame (fun r hr=>by
          obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hr
          exact (List.pairwise_cons.mp sep).1 q hq ) (by have := pp.len; omega_using [num])]
      exact ha.2.2
    · have out := ht.2.2
      rw [state] at out
      exact (outs_copy hp' ha.1).mp out

theorem squeeze_kept {s : State} {sc : Reg} {st wk rate pos : Nat} {ps : List Piece}
    (hs : HSetup sc st wk rate s) (hp : ∀p∈ps,PieceOk sc st wk s true p)
    (sep : ps.Pairwise (fun p q=>(preg s p).Disjoint (preg s q)))
    (sa : st%8=0) (pa : pos%8=0) (sf : st+rate≤32768)
    (of : ∀p∈ps,p.off+p.len≤65536 ∧ p.len%8=0)
    (fit : pos+(ps.map Piece.len).sum≤rate) :
    WP isa (.block (squeezeCode sc st pos ps)) s fun t=>
      Kept (ps.map (preg s)) s t ∧ t.gpr .x30=s.gpr .x30 ∧
      Outs s t.mem rate (stateAt s.mem (s.gpr sc+BitVec.ofNat 64 st)) pos ps := by
  refine WP.mono (squeeze_ok ps hs hp sep sa pa sf of fit) fun t ⟨hk,hf,out⟩=>?_
  exact ⟨⟨fun r hr _=>hk.get r (squeeze_ne r hr),hk.sp,hk.rd,hk.wr,hf,hk.vcs⟩,
    hk.get .x30 (by decide),out⟩

end VG.Proof.MlKem.AArch64.FixedHash

end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt absorb pad)

theorem finish_ok (v : Proof.Sha3.AArch64.Permutation)
 {s₀ s : State} {sc : Reg} {st wk rate pos sfx : Nat} {msg : List Byte} {outs : List Piece}
 (hs : HSetup sc st wk rate s₀) (ha : st%8=0) (hb : st+rate≤4096)
 (hl : (wk+600)%8=0 ∧ wk+600<32768)
 (ho : ∀p∈outs,PieceOk sc st wk s₀ true p)
 (hp : outs.Pairwise (fun p q=>(preg s₀ p).Disjoint (preg s₀ q)))
 (hn : ∀p∈outs,p.off+p.len≤65536 ∧ p.len%8=0)
 (ht : (outs.map Piece.len).sum≤rate)
 (hk : Kept [STr sc st s₀,WKr sc wk s₀] s₀ s)
 (hm : stateAt s.mem (s₀.gpr sc+BitVec.ofNat 64 st)=Proof.Sha3.Rep rate msg)
 (hpos : pos=msg.length%rate)
 (hlink : s.mem.readW (linkSlot sc wk s₀) 64=s₀.gpr .x30) :
 WP isa (.seq (.block (padCode sc st rate pos sfx))
 (.seq (permute v.callee sc st wk)
 (.seq (.block (squeezeCode sc st 0 outs)) (.block [.ldr .x .x30 sc (wk+600)])))) s fun t=>
 Kept (STr sc st s₀::WKr sc wk s₀::outs.map (preg s₀)) s₀ t ∧
 t.gpr .x30=s₀.gpr .x30 ∧
 Outs s₀ t.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx) msg)) 0 outs := by
 have gs:=hk.rg
 have es:=gs.cs sc hs.hsc.1 hs.hsc.2
 refine WP.seq (WP.mono (pad_repr (hsetup_rg hs gs) hb (by rw [Proof.Sha3.repr_iff]; simpa only [es] using hm) hpos) fun a ⟨ka,_,ma⟩=>?_)
 simp only [STr,es] at ka
 rw [es] at ma
 have kaa:=hk.trans (ka.mono (by simp))
 have la : a.mem.readW (linkSlot sc wk s₀) 64=s₀.gpr .x30 := by
   rw [link_frame hs (ka.frame.mono (by simp)),hlink]
 refine WP.seq (WP.mono (permute_ok v hs kaa.rg) fun b ⟨kb,mb⟩=>?_)
 have kb' : Kept [STr sc st s₀,WKr sc wk s₀] a b := kb.sub (by
   intro r hr; rcases mem2' hr with rfl|rfl
   · exact ⟨_,by simp,fun _ h=>h⟩
   · exact ⟨WKr sc wk s₀,by simp,fun _ h=>Nat.le_trans h (show 512≤640 by decide)⟩)
 have kbb:=kaa.trans kb'
 have lb : b.mem.readW (linkSlot sc wk s₀) 64=s₀.gpr .x30 := by rw [link_frame hs kb.frame,la]
 have gb:=kbb.rg
 have eb:=gb.cs sc hs.hsc.1 hs.hsc.2
 have pe : ∀p∈outs,preg b p=preg s₀ p := fun p h=>preg_rg (ho p h) gb
 have maps : outs.map (preg b)=outs.map (preg s₀) := List.map_congr_left pe
 have pb : outs.Pairwise (fun p q=>(preg b p).Disjoint (preg b q)) :=
   by
   apply hp.imp_of_mem
   intro p q h₁ h₂ hh
   simpa only [pe p h₁,pe q h₂] using hh
 refine WP.seq (WP.mono (squeeze_kept (hsetup_rg hs gb) (fun p h=>piece_rg hs (ho p h) gb)
   pb ha (by decide) (by omega_using [hb]) hn (by simpa using ht)) fun c ⟨kc,_,oc⟩=>?_)
 rw [maps] at kc
 have kcc : Kept (STr sc st s₀::WKr sc wk s₀::outs.map (preg s₀)) s₀ c := (kbb.mono (by simp)).trans (kc.mono (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
 have lc : c.mem.readW (linkSlot sc wk s₀) 64=s₀.gpr .x30 := by
   rw [kc.frame.readW (w:=64) (r:=⟨linkSlot sc wk s₀,8⟩) (Region.contains_self _ _) ?_ (by decide),lb]
   intro r hr
   obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hr
   exact (ho p hp).dwk.symm.sub_left (Offset.sub_base _ (d:=600) (by decide))
 rw [eb,mb,ma] at oc
 have oc':= (outs_rg ho gb).mp oc
 refine WP.mono (restoreLink_ok hs kcc.rg hl) fun t ⟨kt,mt,lt⟩=>?_
 exact ⟨kcc.trans (kt.mono (by simp)),lt.trans lc,by simpa only [mt] using oc'⟩
end VG.Proof.MlKem.AArch64.FixedHash

end

end

/-! ### `MlKem.AArch64.FixedHash.Init`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt)

theorem zero_no_link (sc : Reg) (st : Nat) :
    ∀i∈instrs (.block (zeroState sc st) : Prog isa),clobbers i .x30 = false := by
  simp only [zeroState,ptrTo]
  split <;> simp [instrs,clobbers, dstOf]

theorem zeroSave_ok {sc : Reg} {st wk rate : Nat} {s₀ : State}
    (hS : HSetup sc st wk rate s₀)
    (hoff : (wk+600)%8=0 ∧ wk+600<32768) :
    WP isa (.block (zeroState sc st ++ ([.str .x .x30 sc (wk+600)] : List Instr))) s₀ fun t=>
      Kept [STr sc st s₀,WKr sc wk s₀] s₀ t ∧
      stateAt t.mem (s₀.gpr sc+BitVec.ofNat 64 st)=Spec.Sha3.zero ∧
      t.mem.readW (linkSlot sc wk s₀) 64=s₀.gpr .x30 := by
  rw [WP.block_append_iff]
  have hg : Rg s₀ s₀ := ⟨rfl,rfl,rfl,fun _ _ _=>rfl⟩
  refine WP.mono (Proof.Sha3.AArch64.WP.gprs (rs:=[.x30]) (hn:=.inl rfl) (zeroState_ok hS hg)
    (by intro r hr; rw [List.mem_singleton.mp hr]; exact zero_no_link sc st)) fun s₁ ⟨⟨hk,hz⟩,hl⟩=>?_
  refine WP.mono (saveLink_ok hS hk.rg hoff) fun t ⟨kt,_,saved,hstate⟩=>?_
  exact ⟨(hk.mono (by simp)).trans (kt.mono (by simp)),hstate.trans hz,
    saved.trans (hl .x30 (List.mem_singleton_self _))⟩
end VG.Proof.MlKem.AArch64.FixedHash

end

end


-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/FixedHash/AbsorbLoop.lean`, which only this module imported.
section

section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3 (Rep xorAt rep_append bytesAt_length)

theorem nextPos_mod {rate pos : Nat} {w : Bool} {msg : List Byte} {bs : List Byte}
 (hr : 0<rate) (hp : pos=msg.length%rate) (hb : bs.length=width w)
 (hf : pos+width w≤rate) : nextPos rate pos w=(msg++bs).length%rate := by
 rw [List.length_append,hb,Nat.add_mod,←hp]
 have hp' : pos<rate := by rw [hp]; exact Nat.mod_lt _ hr
 have eq : (pos+width w%rate)%rate=(pos+width w)%rate := by
   simpa only [Nat.mod_eq_of_lt hp'] using (Nat.add_mod pos (width w) rate).symm
 rw [eq]
 unfold nextPos
 split <;> rename_i h
 · rw [h,Nat.mod_self]
 · rw [Nat.mod_eq_of_lt (by omega)]

theorem compile_ok (v : Proof.Sha3.AArch64.Permutation)
 {s₀ : State} {sc : Reg} {st wk rate : Nat}
 (hS : HSetup sc st wk rate s₀) (ha : st%8=0) (hb : st+rate≤4096)
 {ps : List Piece} {i pos last : Nat} {acts : List Action}
 (valid : Valid rate ps i pos acts last) :
 ∀s msg, (∀p∈ps,PieceOk sc st wk s₀ false p) → (∀p∈ps,p.off+p.len≤65536) →
 Kept [STr sc st s₀,WKr sc wk s₀] s₀ s →
 stateAt s.mem (s₀.gpr sc+BitVec.ofNat 64 st)=Rep rate msg → pos=msg.length%rate →
 WP isa (compile v.callee sc st wk rate acts) s fun t=>
 Kept [STr sc st s₀,WKr sc wk s₀] s₀ t ∧
 stateAt t.mem (s₀.gpr sc+BitVec.ofNat 64 st)=Rep rate (msg++remainingBytes s₀ ps i) ∧
 last=(msg++remainingBytes s₀ ps i).length%rate ∧
 Frame [STr sc st s₀,⟨s₀.gpr sc+BitVec.ofNat 64 wk,512⟩] s.mem t.mem := by
 induction valid with
 | done pos =>
   intro s msg _ _ hk hm hp
   exact wp_nil ⟨hk,by simpa [remainingBytes] using hm,by simpa [remainingBytes] using hp,Frame.refl _ _⟩
 | @skip p ps pos acts last tail ih =>
   intro s msg hp ho hk hm hpos
   simpa only [remaining_skip] using ih s msg
     (fun q hq=>hp q (List.mem_cons_of_mem _ hq))
     (fun q hq=>ho q (List.mem_cons_of_mem _ hq)) hk hm hpos
 | @step p ps i pos w acts last hi hfit hw tail ih =>
   intro s msg hp ho hk hm hpos
   have pOk:=hp p (List.mem_cons_self ..)
   have pOff:=ho p (List.mem_cons_self ..)
   have hr:=(rate_bounds hS.hrate).1
   have hr':=(rate_bounds hS.hrate).2
   have bw : (chunkBytes s₀ p i (width w)).length=width w := bytesAt_length ..
   have rep := rep_append hr (by omega) msg (chunkBytes s₀ p i (width w))
     (by rw [bw]; cases w <;> decide) (by rw [bw,←hpos]; exact hfit)
   rw [bw,←hpos] at rep
   have nx := nextPos_mod hr hpos bw hfit
   dsimp only [compile,action]
   refine WP.seq (WP.mono (action_piece_ok hS pOk hk.rg hi pOff hfit hw ha hb) fun t ⟨kt,mt⟩=> ?_)
   have k':=hk.trans (kt.mono (by simp))
   rw [hm,chunkBytes_frame pOk hk hi] at mt
   have finish {u : State} (ku : Kept [STr sc st s₀,WKr sc wk s₀] s₀ u)
       (mu : stateAt u.mem (s₀.gpr sc+BitVec.ofNat 64 st)=
         Rep rate (msg++chunkBytes s₀ p i (width w))) :=
     ih u (msg++chunkBytes s₀ p i (width w)) hp ho ku mu nx
   by_cases he : pos+width w=rate
   · rw [ite_eq_left he]
     refine WP.seq (WP.mono (permute_ok v hS k'.rg) fun u ⟨ku,mu⟩=> ?_)
     have k'' := k'.trans (ku.sub (by
       intro r hh
       rcases mem2' hh with rfl|rfl
       · exact ⟨_,List.mem_cons_self ..,fun _ h=>h⟩
       · exact ⟨WKr sc wk s₀,by simp,fun _ h=>Nat.le_trans h (by decide : 512≤640)⟩))
     have out := finish k'' (by rw [mu,mt,rep,ite_eq_left he])
     refine WP.mono out fun fin ⟨kf,mf,pf,ff⟩=>⟨kf,?_,?_,?_⟩
     · simpa only [remaining_step s₀ p ps hi,List.append_assoc] using mf
     · simpa only [remaining_step s₀ p ps hi,List.append_assoc] using pf
     · exact (kt.frame.mono (by simp)).trans (ku.frame.trans ff)
   · rw [ite_eq_right he]
     have out := finish k' (by rw [mt,rep,ite_eq_right he])
     refine WP.mono out fun fin ⟨kf,mf,pf,ff⟩=>⟨kf,?_,?_,?_⟩
     · simpa only [remaining_step s₀ p ps hi,List.append_assoc] using mf
     · simpa only [remaining_step s₀ p ps hi,List.append_assoc] using pf
     · exact (kt.frame.mono (by simp)).trans ff
end VG.Proof.MlKem.AArch64.FixedHash
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/FixedHash/Correct.lean`, which only this module imported.
section

section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt absorb pad)

theorem compiled_ok (v : Proof.Sha3.AArch64.Permutation)
 {s₀ : State} {sc : Reg} {st wk rate sfx : Nat} {ins outs : List Piece}
 (hs : HSetup sc st wk rate s₀) (ha : st%8=0) (hb : st+rate≤4096)
 (hl : (wk+600)%8=0 ∧ wk+600<32768)
 (hi : ∀p∈ins,PieceOk sc st wk s₀ false p)
 (hio : ∀p∈ins,p.off+p.len≤65536)
 (valid : Valid rate ins 0 0 (schedule rate ins).1 (schedule rate ins).2)
 (ho : ∀p∈outs,PieceOk sc st wk s₀ true p)
 (hp : outs.Pairwise (fun p q=>(preg s₀ p).Disjoint (preg s₀ q)))
 (hn : ∀p∈outs,p.off+p.len≤65536 ∧ p.len%8=0)
 (ht : (outs.map Piece.len).sum≤rate) :
 WP isa (compiled v.callee sc st wk rate sfx ins outs) s₀ fun t=>
 Kept (STr sc st s₀::WKr sc wk s₀::outs.map (preg s₀)) s₀ t ∧
 t.gpr .x30=s₀.gpr .x30 ∧
 Outs s₀ t.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx)
   (ins.map (pbytes s₀)).flatten)) 0 outs := by
 dsimp only [compiled]
 refine WP.seq (WP.mono (zeroSave_ok hs hl) fun a ⟨ka,za,la⟩=>?_)
 refine WP.seq (WP.mono (compile_ok v hs ha hb valid a [] hi hio ka
   (by rw [Proof.Sha3.rep_nil]; exact za) (by simp)) fun b ⟨kb,mb,pb,fb⟩=>?_)
 simp only [List.nil_append,remaining_zero] at mb pb
 exact finish_ok v hs ha hb hl ho hp hn ht kb mb pb (by rw [link_frame hs fb,la])

/-- Original hash interface, with only the specialization's encoding and schedule checks added. -/
theorem code_ok (v : Proof.Sha3.AArch64.Permutation)
 {s₀ : State} {sc : Reg} {st wk rate sfx : Nat} {ins outs : List Piece}
 (hs : HSetup sc st wk rate s₀) (ha : st%8=0) (hb : st+rate≤4096)
 (hl : (wk+600)%8=0 ∧ wk+600<32768)
 (hi : ∀p∈ins,PieceOk sc st wk s₀ false p)
 (hio : ∀p∈ins,p.off+p.len≤65536)
 (valid : Valid rate ins 0 0 (schedule rate ins).1 (schedule rate ins).2)
 (ho : ∀p∈outs,PieceOk sc st wk s₀ true p)
 (hp : outs.Pairwise (fun p q=>(preg s₀ p).Disjoint (preg s₀ q)))
 (hn : ∀p∈outs,p.off+p.len≤65536 ∧ p.len%8=0)
 (ht : (outs.map Piece.len).sum≤rate)
 (same : Fusion.Same (compiled v.callee sc st wk rate sfx ins outs)
   (Impl.MlKem.AArch64.FixedHash.code v.callee sc st wk rate sfx ins outs)) :
 WP isa (Impl.MlKem.AArch64.FixedHash.code v.callee sc st wk rate sfx ins outs) s₀ fun t=>
 Kept (STr sc st s₀::WKr sc wk s₀::below s₀.sp 16::outs.map (preg s₀)) s₀ t ∧
 Outs s₀ t.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx)
   (ins.map (pbytes s₀)).flatten)) 0 outs := by
 apply same.wp.mp
 refine WP.mono (compiled_ok v hs ha hb hl hi hio valid ho hp hn ht) fun t ⟨hk,_,out⟩=>⟨hk.mono ?_,out⟩
 intro r hr
 simp only [List.mem_cons] at hr ⊢
 rcases hr with h|h|h
 · exact Or.inl h
 · exact Or.inr (Or.inl h)
 · exact Or.inr (Or.inr (Or.inr h))
end VG.Proof.MlKem.AArch64.FixedHash
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-! The fixed hash's shapes are correct for any permutation `v`. -/

theorem kgG768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound kgG768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (kgG768_compiled v.callee)

theorem prf768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound prf768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (prf768_compiled v.callee)

theorem enG768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound enG768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (enG768_compiled v.callee)

theorem deG768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,2336,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound deG768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (deG768_compiled v.callee)

theorem kgG1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound kgG1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (kgG1024_compiled v.callee)

theorem enG1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound enG1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (enG1024_compiled v.callee)

theorem deG1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,3104,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound deG1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (deG1024_compiled v.callee)

end VG.Proof.MlKem.AArch64.FixedHash
