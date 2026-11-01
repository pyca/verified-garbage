module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.GatherSplit
public import VerifiedGarbage.Proof.Gather.PPC64LE.Loop
public import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the shared gather loop starts after the first plaintext piece.
/-! # Leave the first gather piece in its source buffer -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.Gather.PPC64LE (GatherPre)


def firstLen (s : State) : BitVec 64 := s.mem.readW (s.gpr .r7+8) 64


def skipped (s : State) : State :=
  (((s.write .r3 (firstLen s)).write .r9 (s.gpr .r9+firstLen s)).write .r7 (s.gpr .r7+16)).write .r8 (s.gpr .r8-1)


theorem skip_ok {s : State} {S D : Addr} {count total : Nat}
    (h : GatherPre s S D count total) (hc : 0<count) :
    WP isa (.block Impl.AesGcm.PPC64LE.GatherSplit.skip) s (· = skipped s) := by
  have hr : InRegions (s.rd++s.wr) (s.gpr .r7+BitVec.ofNat 64 8) 8 := by
    rw [h.r7]
    exact h.dsr _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base _ (by omega) (by decide)⟩
  rw [Impl.AesGcm.PPC64LE.GatherSplit.skip]
  let a := s.write .r3 (firstLen s)
  refine WP.block_cons_iff.mpr ⟨a,exec_load_d (n := .r7) (off := 8) (by decide) ⟨by decide,by decide⟩ hr,?_⟩
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec_add,
    exec_addi (n := .r7) (imm := 16) (by decide) (by decide),
    exec_subi (n := .r8) (imm := 1) (by decide) (by decide),RegUpd.gpr_write,reduceCtorEq,ite_false,
    Option.some.injEq,exists_eq_left']
  rfl


theorem first_bound {s : State} {S D : Addr} {count total : Nat}
    (h : GatherPre s S D count total) (hc : 0<count) : (firstLen s).toNat≤total := by
  have hn := h.len
  rw [show count=(count-1)+1 by omega,Proof.Gcm.gatheredLen_cons] at hn
  rw [firstLen,h.r7]
  omega


theorem first_listed {s : State} {S D : Addr} {count total : Nat}
    (h : GatherPre s S D count total) (hc : 0<count) :
    (⟨s.mem.readW S 64,(firstLen s).toNat⟩ : Region)∈Sig.listed 64 s.mem .u8 S count := by
  rw [show count=(count-1)+1 by omega,Proof.Gcm.listed_cons]
  rw [firstLen,h.r7]
  exact List.mem_cons_self


theorem tail_pre {s : State} {S D : Addr} {count total : Nat}
    (h : GatherPre s S D count total) (hc : 0<count) :
    GatherPre (skipped s) (S+16) (D+BitVec.ofNat 64 (firstLen s).toNat)
      (count-1) (total-(firstLen s).toNat) := by
  have hn := first_bound h hc
  have hlist : Sig.listed 64 s.mem .u8 S count=
      ⟨s.mem.readW S 64,(firstLen s).toNat⟩::Sig.listed 64 s.mem .u8 (S+16) (count-1) := by
    rw [show count=(count-1)+1 by omega,Proof.Gcm.listed_cons]
    rw [firstLen,h.r7]
    simp only [Nat.add_sub_cancel]
  have hlen := h.len
  rw [show count=(count-1)+1 by omega,Proof.Gcm.gatheredLen_cons] at hlen
  have hdsub : Region.Sub ⟨D+BitVec.ofNat 64 (firstLen s).toNat,total-(firstLen s).toNat⟩ ⟨D,total⟩ :=
    Offset.sub_base _ (by omega)
  have hssub : Region.Sub ⟨S+16,(count-1)*16⟩ ⟨S,count*16⟩ := Offset.sub_base _ (d := 16) (n := (count-1)*16) (k := count*16) (by omega)
  refine ⟨?_,?_,?_,by have := h.hcnt; omega,?_,by have := h.lt; omega,?_,?_,?_,?_,
    h.dsd.sub_left hssub |>.sub_right hdsub,?_⟩
  · simpa only [skipped,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true] using congrArg (·+16) h.r7
  · change s.gpr .r8-1=BitVec.ofNat 64 (count-1)
    rw [h.r8]
    change BitVec.ofNat 64 count-BitVec.ofNat 64 1=_
    exact Offset.ofNat_sub_ofNat (by omega)
  · change s.gpr .r9+firstLen s=D+BitVec.ofNat 64 (firstLen s).toNat
    rw [h.r9,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · by_cases hz : count-1=0
    · rw [hz,Nat.zero_mul,Nat.add_zero]
      exact Nat.le_of_lt (S+16).isLt
    · have hb : S.toNat+16<2^64 := by have := h.dw; omega
      change (S+16#64).toNat+(count-1)*16≤2^64
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by decide : 16<2^64),Nat.mod_eq_of_lt hb]
      have := h.dw
      omega
  · change Spec.Gcm.gatheredLen 64 s.mem (S+16) (count-1)=total-(firstLen s).toNat
    rw [firstLen,h.r7]
    omega
  · change Covers [⟨S+16,(count-1)*16⟩] (s.rd++s.wr)
    apply VG.Covers.trans (VG.Covers.of_sub ?_) h.dsr
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨⟨S,count*16⟩,List.mem_singleton_self _,16,rfl,by change 16+(count-1)*16≤count*16; omega⟩
  · intro r hr
    apply h.lsr
    rw [hlist]
    exact List.mem_cons_of_mem _ hr
  · exact VG.Proof.Gather.PPC64LE.covers_off h.dw' (by omega) h.lt
  · intro r hr
    exact (h.lsd r (by rw [hlist]; exact List.mem_cons_of_mem _ hr)).sub_right hdsub


end VG.Proof.AesGcm.PPC64LE.GatherSplit
