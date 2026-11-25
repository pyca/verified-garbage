module
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.MlKem.Mem
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16

/-- The table `symbol`, of `n` bytes, holds the words `W`. -/
def TransformTable (s : State) (symbol : String) (n : Nat) (W : List (BitVec 64)) : Prop :=
 Ntt16.Holds s.mem (s.syms symbol) n W ∧
 Covers [⟨s.syms symbol,n⟩] (s.rd++s.wr) ∧
 ∀r∈s.wr,(Region.mk (s.syms symbol) n).Disjoint r

/-- The tables of `vg_mlkem16_ntt` and `vg_mlkem16_inv_ntt`. -/
structure TransformTables (s : State) : Prop where
 forward : TransformTable s Forward.name Ntt16.fwdBytes Forward.words
 inverse : TransformTable s Inverse.name Ntt16.invBytes Inverse.words
 forwardStack : (Ntt16.fwdRegion s).Disjoint (below s.sp 16)
 inverseStack : (Ntt16.invRegion s).Disjoint (below s.sp 16)

theorem TransformTable.apart {s : State} {symbol : String} {n : Nat} {W : List (BitVec 64)}
 (h : TransformTable s symbol n W) {r : Region} (hc : Covers [r] s.wr) :
 (Region.mk (s.syms symbol) n).Disjoint r := by
 intro addr ha hb
 have hi := hc addr 1 ⟨r,by simp,hb⟩
 obtain ⟨q,hq,hh⟩ := hi
 exact h.2.2 q hq addr ha hh

theorem TransformTable.frameFar {s t : State} {symbol : String} {n : Nat} {W : List (BitVec 64)} {rs : List Region}
 (h : TransformTable s symbol n W) (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr)
 (hf : Frame rs s.mem t.mem) (hd : ∀r∈rs,(Region.mk (s.syms symbol) n).Disjoint r) (hn : n < 2^32 := by decide) :
 TransformTable t symbol n W := by
 refine ⟨?_,by simpa only [hs,hr,hw] using h.2.1,by simpa only [hs,hw] using h.2.2⟩
 rw [hs]
 exact h.1.frame hf hd hn

theorem TransformTable.frame {s t : State} {symbol : String} {n : Nat} {W : List (BitVec 64)} {rs : List Region}
 (h : TransformTable s symbol n W) (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr)
 (hf : Frame rs s.mem t.mem) (hc : Covers rs s.wr) (hn : n < 2^32 := by decide) : TransformTable t symbol n W :=
 h.frameFar hs hr hw hf (fun r hh =>
   h.apart (fun a n ⟨q,hq,ha⟩=>hc a n ⟨q,by rw [List.mem_singleton.mp hq]; exact hh,ha⟩)) hn

/-- The table is ready for a transform of the polynomial at `f`. -/
theorem TransformTable.ready {s : State} {symbol : String} {n : Nat} {W : List (BitVec 64)}
 (h : TransformTable s symbol n W) {f w : Addr} (hc : Covers [⟨f,1024⟩,⟨w,1024⟩] s.wr) : Ntt16.Ready symbol n W s f w :=
 ⟨h.1,h.2.1,h.apart (Covers.head hc),h.apart (Covers.head (Covers.tail hc))⟩

theorem TransformTables.frame {s t : State} {rs : List Region} (h : TransformTables s)
 (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hsp : t.sp=s.sp)
 (hf : Frame rs s.mem t.mem) (hc : Covers rs s.wr) : TransformTables t :=
 ⟨h.forward.frame hs hr hw hf hc,h.inverse.frame hs hr hw hf hc,
   by simpa only [hs,hsp] using h.forwardStack,by simpa only [hs,hsp] using h.inverseStack⟩
theorem TransformTables.frameFar {s t : State} {rs : List Region} (h : TransformTables s)
 (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hsp : t.sp=s.sp)
 (hf : Frame rs s.mem t.mem)
 (hd : ∀r∈rs,(Ntt16.fwdRegion s).Disjoint r ∧ (Ntt16.invRegion s).Disjoint r) :
 TransformTables t :=
 ⟨h.forward.frameFar hs hr hw hf (fun r hr=>(hd r hr).1),
   h.inverse.frameFar hs hr hw hf (fun r hr=>(hd r hr).2),
   by simpa only [hs,hsp] using h.forwardStack,by simpa only [hs,hsp] using h.inverseStack⟩

end VG.Proof.MlKem.AArch64.Optimized
