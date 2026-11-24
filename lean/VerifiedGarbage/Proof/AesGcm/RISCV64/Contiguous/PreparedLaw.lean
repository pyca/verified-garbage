module

-- separate module: The prepared GHASH arithmetic discharges a call law; keeping its instantiation here keeps generic record proofs independent of the multiplier.

import VerifiedGarbage.Proof.Gcm.RISCV64.Prepared.Verified
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.HashInput
public import VerifiedGarbage.Proof.Gcm.Holes.Words
import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # Prepared GHASH discharges the contiguous seal’s call law -/

public section
namespace VG.Proof.AesGcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.Proof.Gcm.RISCV64
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

def cachedContract (H : Block) : Contract isa where
  pre s := CachedPre H s ∧ 112 ≤ s.sp.toNat
  post := hashDone H
  pub := ghashX.pub

theorem cached_correct (product : VG.Proof.Gcm.Holes.MulLaw) {H : Block} (s : State) (h : (cachedContract H).pre s) :
    ∃ t s', Exec isa cachedHash s t s' ∧ abiPreserved s s' ∧ (cachedContract H).post s s' :=
  preparedHash_law product s h.1 h.2

def cachedEntry (s : State) (T Y D S : Addr) (n : Nat) :=
  s.callEntry.withRegions [⟨T,288⟩,⟨D,16*n⟩] [⟨Y,16⟩,⟨S,256⟩]

theorem cached_call_pre {s : State} {K Y D S T : Addr} {n : Nat} {H : Block}
    (g : GhCall s K Y D S n) (t : TableAt s T H) (hh : H = blockAt s.mem K) (e : State) (a0 : e.gpr .a0=T)
    (args : ∀ r, r ≠ .a0 → r ≠ .t0 → e.gpr r=s.gpr r) (mem : e.mem=s.mem) (sp : e.sp=s.sp) :
    (cachedContract H).pre (cachedEntry e T Y D S n) := by
  have ge : 112 ≤ s.sp.toNat := by omega_using [g.spge]
  have fo : CompactFrame (allocd 112 (cachedEntry e T Y D S n)).sp (allocd 112 (cachedEntry e T Y D S n)) := by
    refine ⟨?_,?_,List.mem_cons_self⟩
    · change (e.sp-BitVec.ofNat 64 112).toNat %16=0
      rw [sp,toNat_sub_ofNat' ge];omega_using [g.spal]
    · change (e.sp-BitVec.ofNat 64 112).toNat +112≤2^64
      rw [sp,toNat_sub_ofNat' ge]
      have := s.sp.isLt
      omega_using []
  have sf : (below s.sp 112).Sub (below s.sp 2048) := VG.RISCV64.below_sub (by decide) (by decide)
  have key : ∃ h0 h1, H=h0++h1 ∧ Tab (VG.Proof.Gcm.Holes.key0 h0 h1) (VG.Proof.Gcm.Holes.key1 h0 h1)
      (fun off => s.mem.readW (T+BitVec.ofNat 64 off) 64) := by
    obtain ⟨h0,h1,eq⟩ : ∃ h0 h1 : BitVec 64, H = h0 ++ h1 :=
      ⟨_,_,hh.trans (blockAt_hOf _ _)⟩
    refine ⟨h0,h1,eq,fun i hi j hj => ?_⟩
    have e := t.key i hi j hj
    rwa [ghashOperand_eq,eq,ghashKey0_append,ghashKey1_append] at e
  constructor
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,fo,?_⟩ <;>
      simp only [cachedEntry, State.withRegions_gpr, State.withRegions_sp, State.withRegions_rd,
        State.withRegions_wr, State.withRegions_mem, State.callEntry_mem, State.callEntry_sp, allocd,
        callEntry_gpr' _ (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a1 ∉ linkRegs),
        callEntry_gpr' _ (by decide : Reg.a2 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a3 ∉ linkRegs),
        callEntry_gpr' _ (by decide : Reg.a4 ∉ linkRegs), a0,args .a1 (by decide) (by decide),
        args .a2 (by decide) (by decide),args .a3 (by decide) (by decide),args .a4 (by decide) (by decide),
        g.a1,g.a2,g.a3,g.a4,toNat64 g.n_lt,sp,mem]
    exacts [t.al, (t.stack.sub_left sf), (g.ky.sub_left sf), (g.kd.sub_left sf), g.dfit, key]
  · change 112≤e.sp.toNat
    rwa [sp]

theorem cached_call_wp (product : VG.Proof.Gcm.Holes.MulLaw) {s : State} {K Y D S T : Addr} {n : Nat}
    (g : GhCall s K Y D S n) (t : TableAt s T (blockAt s.mem K)) (e : State) (a0 : e.gpr .a0=T)
    (args : ∀ r, r ≠ .a0 → r ≠ .t0 → e.gpr r=s.gpr r)
    (mem : e.mem=s.mem) (sp : e.sp=s.sp) (rd : e.rd=s.rd) (wr : e.wr=s.wr) :
    WP isa (.call "vg_ghash_prepared" cachedHash) e (GhPost s K Y D S n) := by
  let H := blockAt s.mem K
  refine WP.callAny (k:=cachedContract H) (cached_correct product) (rd:=[⟨T,288⟩,⟨D,16*n⟩]) (wr:=[⟨Y,16⟩,⟨S,256⟩])
    (cached_call_pre g t rfl e a0 args mem sp) ?_ (wr ▸ g.writes) ?_ (by change 112<2^64;decide)
  · rw [rd,wr]
    rintro a l ⟨r,hr,c⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact t.read _ _ ⟨_,List.mem_cons_self,c⟩
    all_goals exact g.reads _ _ ⟨_,by simp,c⟩
  · intro u hrd hwr hsp hf hcs post
    refine ⟨hrd.trans rd,hwr.trans wr,hsp.trans sp, fun r hr => (hcs _ hr).trans (args _ (by revert hr;revert r; decide) (by revert hr;revert r;decide)), ?_,?_⟩
    · rw [sp,mem] at hf
      exact VG.RISCV64.Frame.below_mono (wr:=[⟨Y,16⟩,⟨S,256⟩]) hf (by change 112≤2048;decide) (by decide)
    · simpa only [cachedContract,hashDone,State.withRegions_gpr,State.withRegions_mem,State.callEntry_mem,
        callEntry_gpr' _ (by decide : Reg.a1 ∉ linkRegs),callEntry_gpr' _ (by decide : Reg.a2 ∉ linkRegs),
        callEntry_gpr' _ (by decide : Reg.a3 ∉ linkRegs),args .a1 (by decide) (by decide),
        args .a2 (by decide) (by decide),args .a3 (by decide) (by decide),g.a1,g.a2,g.a3,toNat64 g.n_lt,mem] using post


theorem preparedInvocation_wp (product : VG.Proof.Gcm.Holes.MulLaw) {s : State} {K Y D S : Addr} {n : Nat}
    (g : GhCall s K Y D S n) (c : HashInput s (blockAt s.mem K)) :
    WP isa preparedInvocation s (GhPost s K Y D S n) :=
  WP.seq (WP.mono (loadPrepared_wp c) (fun e ⟨hp,hr,hm,hs,hd,hw⟩ => cached_call_wp product g c.table e hp hr hm hs hd hw))

end VG.Proof.AesGcm.RISCV64
