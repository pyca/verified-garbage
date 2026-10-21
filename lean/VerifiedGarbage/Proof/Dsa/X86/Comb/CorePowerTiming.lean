module

public import VerifiedGarbage.Proof.Dsa.X86.CorePowerTiming
public import VerifiedGarbage.Proof.Dsa.X86.Comb.CorePower
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
import VerifiedGarbage.Proof.Dsa.X86.Comb.CallTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.Call
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
import VerifiedGarbage.Proof.Dsa.X86.CorePowerLoad
import VerifiedGarbage.Proof.Dsa.X86.CoreStoreTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! Constant-time composition of byte staging, comb calls, and byte output. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

def PowerAgree (prepare : Bool) (base : Addr) (size len bl : Nat) (modulus : Field) (a b : Pointer)
    (s t : State) : Prop :=
  VG.Proof.Dsa.X86.PowerAgree base size len bl modulus a b s t ∧
  (prepare=true → operandValue s base (.input modulus) len=operandValue t base (.input modulus) len ∧
    operandValue s base a len=operandValue t base a len ∧ operandValue s base b bl=operandValue t base b bl) ∧
  (prepare=false → canonical ((len+7)/8) ((bl+3)/4) (operandValue s base (.input modulus) len)
    (operandValue s base a len) base s.mem ∧
    canonical ((len+7)/8) ((bl+3)/4) (operandValue t base (.input modulus) len)
      (operandValue t base a len) base t.mem)

theorem corePower_relCT (prepare : Bool) (base : Addr) (size len bl output : Nat)
    (modulus : Field) (a b : Pointer) (sup : Supported ((len+7)/8) ((bl+3)/4))
    (hz : VG.Impl.Dsa.X86.Layout.saved≤size) (hu : usedBytes≤size)
    (h4 : 4≤len) (hmax : len≤384) (hw4 : len%4=0) (he : 8≤bl) (hel : bl≤len) (hew : bl%4=0)
    (fits : (layout ((len+7)/8) ((bl+3)/4)).size≤size) :
    RelCT isa (PowerAgree prepare base size len bl modulus a b)
      (power prepare len bl modulus a b output) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨⟨⟨S,T,PM,PA,PB⟩,RS,RT,SP⟩,Pub,Priv⟩ E F
  have hn : (len+7)/8≤48 := by omega
  have ctx : contextBytes ((len+7)/8)≤size :=
    Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (Nat.le_trans (by decide) hu)
  have table := table_layout sup
  cases E with | seq Es Es => cases Es with | seq Cs Os =>
  cases F with | seq Et Et => cases Et with | seq Ct Ot =>
  have Head := (powerHead_relCT base size len bl modulus a b hz h4 hmax hw4
    _ _ _ _ _ _ ⟨S,T,PM,PA,PB⟩ Es Et).1
  obtain ⟨Ms,Gs,Xs,Fs,Ks⟩ := wp_result (coreLoadPower_ok S.scr hz rfl h4 hmax hw4 he hel hew
    S.modulusReady S.leftReady S.rightReady rfl ctx) Es
  obtain ⟨Mt,Gt,Xt,Ft,Kt⟩ := wp_result (coreLoadPower_ok T.scr hz rfl h4 hmax hw4 he hel hew
    T.modulusReady T.leftReady T.rightReady rfl ctx) Et
  have Ss := S.scr.of_keeps Ks (by decide)
  have Ts := T.scr.of_keeps Kt (by decide)
  have RSw := RS
  rw [← Ks.1 .esp (by decide)] at RSw
  have RTw := RT
  rw [← Kt.1 .esp (by decide)] at RTw
  have SPw : _ = _ := (Ks.1 .esp (by decide)).trans (SP.trans (Kt.1 .esp (by decide)).symm)
  have preserve {u v : State} (O : Outside base 0 (contextBytes ((len+7)/8)) u.mem v.mem)
      {m g : Nat} (C : canonical ((len+7)/8) ((bl+3)/4) m g base u.mem) :
      canonical ((len+7)/8) ((bl+3)/4) m g base v.mem := by
    apply canonical_outs sup C (Outs.of_outside (rs := [(0,contextBytes ((len+7)/8))]) O (by simp))
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact .inr (by simpa only [Nat.zero_add] using table.apart)
  have Ps := fun eq : prepare=false => preserve Fs (Priv eq).1
  have Pt := fun eq : prepare=false => preserve Ft (Priv eq).2
  simp only [operandValue] at Ps Pt
  rw [← Gs] at Ps
  rw [← Gt] at Pt
  have CallTrace := by
    cases prepare with
    | false => exact (privateCall_relCT sup base size _ _ _ _ _ _ ⟨Ss,Ts,RSw,RTw,SPw,trivial⟩ Cs Ct).1
    | true =>
      obtain ⟨M,G,X⟩ := Pub rfl
      exact (publicCall_relCT sup base size (operandValue s base (.input modulus) len)
        (operandValue s base a len) (operandValue s base b bl) fits S.large S.odd
        _ _ _ _ _ _ ⟨Ss,Ts,RSw,RTw,SPw,⟨Ms,Gs,Xs⟩,
          ⟨Mt.trans M.symm,Gt.trans G.symm,Xt.trans X.symm⟩⟩ Cs Ct).1
  obtain ⟨_,_,Kcs⟩ := wp_result (call_ok sup prepare Ss RSw fits hu Ms S.large S.odd Ps) Cs
  obtain ⟨_,_,Kct⟩ := wp_result (call_ok sup prepare Ts RTw fits hu Mt T.large T.odd Pt) Ct
  have DI : _ = _ := BitVec.eq_of_toNat_eq (Ss.edi_toNat.trans Ts.edi_toNat.symm)
  have Store := (coreStore_workspace_relCT len output _ _ _ _ _ _ (agree_regs (rs := [.edi]) (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    rw [Kcs.1 .edi (by decide),Kct.1 .edi (by decide)]
    exact DI)) Os Ot).1
  exact ⟨by simp only [Head,CallTrace,Store],trivial⟩

end VG.Proof.Dsa.X86.Comb
