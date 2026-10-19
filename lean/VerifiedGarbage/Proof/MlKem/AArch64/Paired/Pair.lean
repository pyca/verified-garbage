module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Begin
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Finish

/-! # The complete paired matrix sampler -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem pair_iff {w16 : Bool} (L : KemLay) (kg : Bool) (a : Nat) (s : State) (Q : State→Prop) :
    WP isa (Impl.MlKem.AArch64.Paired.pair L kg a w16) s Q ↔
    WP isa (.seq (beginCode (if kg then KG.SB else KEM.SB) (if kg then KG.SS else KEM.SS)
      a (a+1) L.k ((if kg then KG.AH else KEM.AH)+1024*a)
      ((if kg then KG.AH else KEM.AH)+1024*(a+1)) w16) (finishCode w16)) s Q := by
  simp only [Impl.MlKem.AArch64.Paired.pair,beginCode,initialCode,finishCode,seqs,
    show [Instr.str .x .x3 .x19 1696,.str .x .x4 .x19 1704,.logic .and .x .x6 .x22 .x23]=
      [.str .x .x3 .x19 1696,.str .x .x4 .x19 1704]++[.logic .and .x .x6 .x22 .x23] from rfl,
    ]
  simp only [WP.seq_iff (M := isa),WP.block_append_iff (M := isa)]

theorem pairCode_ok {w16 : Bool} {s : State} {p seed outA outB table : Addr} {sb ss a b k oa ob : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0)
    (hoa : oa<65536) (hob : ob<65536)
    (hp : s.gpr .x28+BitVec.ofNat 64 ss=p) (hseed : s.gpr .x28+BitVec.ofNat 64 sb=seed)
    (houtA : s.gpr .x28+BitVec.ofNat 64 oa=outA) (houtB : s.gpr .x28+BitVec.ofNat 64 ob=outB)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hsep : (Region.mk seed 32).Disjoint ⟨p,2048⟩)
    (ctx : Context p outA outB table s) (ht : s.syms "VG_MLKEM_REJ_SHUFFLE"=table)
    (hb : s.gpr .x24=0 ∨ s.gpr .x24=1) :
    WP isa (.seq (beginCode sb ss a b k oa ob w16) (finishCode w16)) s
      (PairPostW w16 (seedState s.mem seed a k) (seedState s.mem seed b k) p outA outB s) := by
  refine WP.seq (WP.mono_syms (begin_ok hss hsb h8 hoa hob hp hseed houtA houtB hin hsep ctx ht)
    fun t h sy=>?_)
  exact finish_ok (h.keep.mono (by decide)) h.frame h.saved h.progress (by rw [sy]; exact ht)
    h.flag (h.keep.get .x24 (by decide)) hb

end VG.Proof.MlKem.AArch64.Paired
