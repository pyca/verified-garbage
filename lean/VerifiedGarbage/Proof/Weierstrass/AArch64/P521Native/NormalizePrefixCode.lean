module

-- separate module: The fifteen unrolled literal block identities are checked separately from the canonical-prefix invariant so changes to phase composition reuse the computational replay.

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizePrefixInv
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def normalizePrefixWork : Nat → Nat → Prog isa
  | _,0 => .block []
  | m,n+1 => .seq (normalizePrefixStep (216*m+144) (normalizePrefixSlot (m+1)) (normalizePrefixSlot m))
      (normalizePrefixWork (m+1) n)

theorem normalize_prefix_work_ok {base table : Addr} {W : Nat} (layout : NormalizeLayout base table W) :
    ∀n m {s : State} {X Y Z : Nat → Fin fieldPrime},1≤m → m+n≤16 →
      NormalizePrefixInv base table W m s X Y Z →
      WP isa (normalizePrefixWork m n) s fun t =>
        NormalizePrefixInv base table W (m+n) t X Y Z ∧ Outside base 0 W s.mem t.mem ∧
        t.gpr .x0=base ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
        (∀r∈preserved,t.gpr r=s.gpr r) ∧ t.v .v31=s.v .v31 ∧ Outside base 1216 6120 s.mem t.mem ∧ VG.Proof.Weierstrass.Unch base normalizePrefixWrites s.mem t.mem
  | 0,m,s,X,Y,Z,_,_,inv => WP.block_nil ⟨inv,Outside.refl _ _ _ _,inv.workspace.x0,rfl,rfl,rfl,fun _ _ => rfl,rfl,Outside.refl _ _ _ _,VG.Proof.Weierstrass.Unch.refl _ _ _⟩
  | n+1,m,s,X,Y,Z,one,limit,inv => by
    rw [normalizePrefixWork,WP.seq_iff]
    refine WP.mono (normalize_prefix_advance layout inv one (by omega_arith))
      fun u ⟨iu,ou,_,ru,wu,su,gu,vu,lowu,unchu⟩ => ?_
    refine WP.mono (normalize_prefix_work_ok layout n (m+1) (by omega_arith) (by omega_arith) iu)
      fun t ⟨it,ot,zero,rt,wt,st,gt,vt,lowt,uncht⟩ => ?_
    have hm : m+1+n=m+(n+1) := by omega_arith
    rw [hm] at it
    exact ⟨it,ou.trans ot,zero,rt.trans ru,wt.trans wu,st.trans su,
      fun r hr => (gt r hr).trans (gu r hr),vt.trans vu,lowu.trans lowt,fun x hx => (uncht x hx).trans (unchu x hx)⟩

theorem normalize_prefix_all_ok {base table : Addr} {W : Nat} {s : State} {X Y Z : Nat → Fin fieldPrime}
    (layout : NormalizeLayout base table W) (inv : NormalizePrefixInv base table W 1 s X Y Z) :
    WP isa (normalizePrefixWork 1 15) s fun t =>
      NormalizePrefixInv base table W 16 t X Y Z ∧ Outside base 0 W s.mem t.mem ∧
      t.gpr .x0=base ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      (∀r∈preserved,t.gpr r=s.gpr r) ∧ t.v .v31=s.v .v31 ∧ Outside base 1216 6120 s.mem t.mem ∧ VG.Proof.Weierstrass.Unch base normalizePrefixWrites s.mem t.mem :=
  normalize_prefix_work_ok layout 15 1 (by decide) (by decide) inv

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

theorem normalize_prefix_source_2 : outerBlock028=
    [.ldr .x .x20 .x0 3944]++(normalizeCopy 9 (216*1+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 2) (normalizePrefixSlot 1) 1360) := by lit_decide

theorem normalize_prefix_source_3 : outerBlock029=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*2+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 3) (normalizePrefixSlot 2) 1360) := by lit_decide

theorem normalize_prefix_source_4 : outerBlock030=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*3+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 4) (normalizePrefixSlot 3) 1360) := by lit_decide

theorem normalize_prefix_source_5 : outerBlock031=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*4+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 5) (normalizePrefixSlot 4) 1360) := by lit_decide

theorem normalize_prefix_source_6 : outerBlock032=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*5+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 6) (normalizePrefixSlot 5) 1360) := by lit_decide

theorem normalize_prefix_source_7 : outerBlock033=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*6+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 7) (normalizePrefixSlot 6) 1360) := by lit_decide

theorem normalize_prefix_source_8 : outerBlock034=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*7+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 8) (normalizePrefixSlot 7) 1360) := by lit_decide

theorem normalize_prefix_source_9 : outerBlock035=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*8+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 9) (normalizePrefixSlot 8) 1360) := by lit_decide

theorem normalize_prefix_source_10 : outerBlock036=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*9+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 10) (normalizePrefixSlot 9) 1360) := by lit_decide

theorem normalize_prefix_source_11 : outerBlock037=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*10+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 11) (normalizePrefixSlot 10) 1360) := by lit_decide

theorem normalize_prefix_source_12 : outerBlock038=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*11+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 12) (normalizePrefixSlot 11) 1360) := by lit_decide

theorem normalize_prefix_source_13 : outerBlock039=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*12+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 13) (normalizePrefixSlot 12) 1360) := by lit_decide

theorem normalize_prefix_source_14 : outerBlock040=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*13+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 14) (normalizePrefixSlot 13) 1360) := by lit_decide

theorem normalize_prefix_source_15 : outerBlock041=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*14+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 15) (normalizePrefixSlot 14) 1360) := by lit_decide

theorem normalize_prefix_source_16 : outerBlock042=
    [.umov .x .x30 .v29 0]++(normalizeCopy 9 (216*15+144) 1360++
      normalizeCallArgs (normalizePrefixSlot 16) (normalizePrefixSlot 15) 1360) := by lit_decide

theorem normalize_prefix_tail_source : outerBlock043=[.umov .x .x30 .v29 0] := by decide

def normalizePrefixMachine : Prog isa := sequence [
  .block outerBlock028,callNormalMul,
  .block outerBlock029,callNormalMul,
  .block outerBlock030,callNormalMul,
  .block outerBlock031,callNormalMul,
  .block outerBlock032,callNormalMul,
  .block outerBlock033,callNormalMul,
  .block outerBlock034,callNormalMul,
  .block outerBlock035,callNormalMul,
  .block outerBlock036,callNormalMul,
  .block outerBlock037,callNormalMul,
  .block outerBlock038,callNormalMul,
  .block outerBlock039,callNormalMul,
  .block outerBlock040,callNormalMul,
  .block outerBlock041,callNormalMul,
  .block outerBlock042,callNormalMul,
  .block outerBlock043]

private theorem wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem normalize_prefix_machine_wp {s : State} {Q : State → Prop} :
    WP isa normalizePrefixMachine s Q ↔
      WP isa (.seq (.block [.ldr .x .x20 .x0 3944]) (normalizePrefixWork 1 15)) s Q := by
  simp only [normalizePrefixMachine,sequence,List.foldr_cons,List.foldr_nil,
    normalizePrefixWork,normalizePrefixStep,normalizeMulStep,
    normalize_prefix_source_2,normalize_prefix_source_3,normalize_prefix_source_4,normalize_prefix_source_5,normalize_prefix_source_6,normalize_prefix_source_7,normalize_prefix_source_8,normalize_prefix_source_9,normalize_prefix_source_10,normalize_prefix_source_11,normalize_prefix_source_12,normalize_prefix_source_13,normalize_prefix_source_14,normalize_prefix_source_15,normalize_prefix_source_16,normalize_prefix_tail_source]
  simp only [Nat.reduceAdd,Nat.reduceMul]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_append_iff] | rw [VG.WP.block_nil_iff] | (apply wp_post_iff; intro t)

end VG.Proof.Weierstrass.AArch64.P521Native
