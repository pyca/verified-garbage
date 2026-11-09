module

public import VerifiedGarbage.Proof.Scrypt.X86_64.PackedRound
public import VerifiedGarbage.Proof.Scrypt.X86_64.FusedLoop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Scrypt.X86_64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

-- separate module: keep vector/memory symbolic execution separate from the BlockMix loop proof.
/-! Loading, retaining, and storing the packed BlockMix state. -/

@[expose] public section
namespace VG.Proof.Scrypt.X86_64.Packed
open VG VG.X86_64 VG.Impl.Scrypt.X86_64.Packed
open VG.Impl.Scrypt.X86_64 (at_)
open VG.Proof.Scrypt.X86_64.Retained (memWords)

abbrev plus (p : Addr) (n : Nat) : Addr := p + BitVec.ofNat 64 n

theorem plus_zero (p : Addr) : plus p 0 = p := by simp [plus]

theorem access {rs : List Region} {p : Addr} (h : InRegions rs p 64)
 {off n : Nat} (ho : off+n≤64) : InRegions rs (plus p off) n :=
 Covers.one h _ _ ⟨_,by simp,Offset.contains_base p ho (by omega)⟩

theorem ea_at (s : State) (b : Reg) (d : Nat) :
 s.ea (at_ b d) = plus (s.gpr b) d := VG.Proof.Scrypt.X86_64.BlockMix.ea_at s b d

theorem wp_load128 {s : State} {d : XReg} {m : MemOp} {p : Addr} {is : List Instr} {Q : State → Prop}
 (ha : s.ea m = p) (hi : InRegions (s.rd++s.wr) p 16)
 (k : ∀ t, F s t → t.xmm d = s.mem.readW p 128 →
    (∀ r, r≠d → t.xmm r = s.xmm r) → WP isa (.block is) t Q) :
 WP isa (.block (.movdquLoad d m :: is)) s Q := by
 refine WP.block_cons_iff.mpr ⟨s.setXmm d (s.mem.readW p 128),?_,k _ ⟨rfl,rfl,rfl,rfl⟩
   (RegUpd.xmm_setXmm_self _ _ _) (fun r hr => RegUpd.xmm_setXmm_of_ne _ _ hr)⟩
 simp only [reduceExec,State.load128,ha,hi,ite_true,Option.map_some]

theorem raw_natural {v : Vector Spec.Scrypt.Word 16} {s : State} {m : Mem} {p : Addr}
 (h : ∀ r (_hr : r<4), s.xmm (naturalReg r) = m.readW (plus p (16*r)) 128)
 (hv : v = memWords m p) : Natural naturalReg v s := by
 subst v
 intro r hr q hq
 rw [dw,h r hr,dword_readW _ _ hq]
 simp only [memWords,Vector.getElem_ofFn,bufAt,ofInt_natCast]
 exact congrArg (fun a => m.readW a 32) (by
   simp only [plus,BitVec.add_assoc,← BitVec.ofNat_add]
   exact congrArg (fun n => p + BitVec.ofNat 64 n) (by omega))

theorem natural_load {s : State} {b : Reg} {off : Nat} {p : Addr}
 (hb : plus (s.gpr b) off = p) (hi : InRegions (s.rd++s.wr) p 64) :
 WP isa (.block (naturalLoad b off)) s fun t =>
  F s t ∧ Natural naturalReg (memWords s.mem p) t ∧
  ∀ r, r≠.xmm4 → r≠.xmm5 → r≠.xmm6 → r≠.xmm7 → t.xmm r = s.xmm r := by
 have addr {t : State} (f : F s t) (d : Nat) : t.ea (at_ b (off+d)) = plus p d := by
  rw [ea_at,f.gpr]
  simp only [plus,BitVec.ofNat_add,← BitVec.add_assoc]
  change plus (s.gpr b) off + BitVec.ofNat 64 d = plus p d
  rw [hb]
 have ha : s.ea (at_ b off) = p := by rw [ea_at,hb]
 unfold naturalLoad
 refine wp_load128 ha (by simpa only [plus_zero] using access hi (off:=0) (n:=16) (by decide)) fun a fa va ka => ?_
 refine wp_load128 (addr fa 16) (by rw [fa.rd,fa.wr]; exact access hi (by decide)) fun c fc vc kc => ?_
 refine wp_load128 (addr (fa.trans fc) 32) (by rw [fc.rd,fc.wr,fa.rd,fa.wr]; exact access hi (by decide)) fun d fd vd kd => ?_
 refine wp_load128 (addr ((fa.trans fc).trans fd) 48)
   (by rw [fd.rd,fd.wr,fc.rd,fc.wr,fa.rd,fa.wr]; exact access hi (by decide)) fun e fe ve ke => ?_
 refine WP.block_nil ⟨((fa.trans fc).trans fd).trans fe,?_,?_⟩
 · apply raw_natural (m:=s.mem) (p:=p) _ rfl
   intro r hr
   rcases cases4 hr with rfl|rfl|rfl|rfl
   · simp only [naturalReg,Nat.mul_zero,plus_zero]
     rw [ke _ (by decide),kd _ (by decide),kc _ (by decide),va]
   · simp only [naturalReg,Nat.mul_one]
     rw [ke _ (by decide),kd _ (by decide),vc,fa.mem]
   · simp only [naturalReg,show 16*2=32 from rfl]
     rw [ke _ (by decide),vd,fc.mem,fa.mem]
   · simp only [naturalReg,show 16*3=48 from rfl]
     rw [ve,fd.mem,fc.mem,fa.mem]
 · intro r h4 h5 h6 h7
   rw [ke r h7,kd r h6,kc r h5,ka r h4]

end VG.Proof.Scrypt.X86_64.Packed
