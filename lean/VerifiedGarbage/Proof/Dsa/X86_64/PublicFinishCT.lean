module

public import VerifiedGarbage.Proof.Dsa.X86_64.PublicCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicCallCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.PublicPower
meta import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-! # Public exponent bytes across the DSA calling convention -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

/-- Two readable byte strings at the same address and width agree. -/
theorem source_unique {s : State} {B p : Addr} {Z : Nat} {a b : List Byte}
    (ha : Src s B Z p a) (hb : Src s B Z p b) (hlen : a.length = b.length) : a = b := by
  apply List.ext_getElem hlen
  intro i hi hj
  exact (ha.val i hi).symm.trans (hb.val i hj)

def PowerFinishPre (p : PowerFinishPublic × List Byte) (s : State) : Prop :=
  PowerCallPre (p.1.toPowerCallPublic, p.2) s ∧ FinishPre p.1.result s

theorem powerFinish_ct (M : Mont) (Sq : MontS) : RelCT isa (Two PowerFinishPre)
    (.seq (VG.Impl.Dsa.X86_64.PublicPower.power Sq.mm M.mm arg argLen arg2 arg2Len) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.1.result s)
    (two_map (fun p : PowerFinishPublic × List Byte => (p.1.toPowerCallPublic, p.2)) (fun _ _ h => h.1) (powerCall_ct M Sq)) ?_)
    (two_map (fun p : PowerFinishPublic × List Byte => p.1.result) (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨hc, hm, bb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hf⟩
  exact WP.mono (power_ok M Sq hc p.1.lower p.1.width48 p.1.fits p.1.upper p.1.greater p.1.odd
    hm.modulus hm.inverse (by decide) (by decide) (by decide) (by decide)
    hp hl hb (hbl ▸ p.1.basePositive) (hbl ▸ p.1.baseFits)
    hep hel he (helen ▸ p.1.expPositive) (helen ▸ p.1.expLimit))
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

def CallPre (a b output : Operand) (p : Call3Public × List Byte) (s : State) : Prop :=
  Call3Pre a b output p.1 s ∧ Src s p.1.x.B p.1.x.Z p.1.bytes.ptr p.2 ∧ p.2.length = p.1.bytes.len

theorem callHead_public {p : Call3Public × List Byte} {s : State} {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    (h : CallPre a b output p s) :
    WP isa (.block (callHead a b output p.1.x.o)) s (PowerFinishPre (p.1.toPowerFinishPublic, p.2)) := by
  obtain ⟨h, he, hlen⟩ := h
  refine WP.mono (callHead_run ha hb ho h) fun t ⟨⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hs, hes⟩, hf⟩, hfr, hk⟩ => ?_
  have het := arguments_source hfr hk (Nat.le_trans (by decide) p.1.extent) he
  have eqb := source_unique hes het (helen.trans hlen.symm)
  subst eb
  exact ⟨⟨hc, hm, bb, hp, hl, hep, hel, hbl, helen, hs, hes⟩, hf⟩

theorem corePublicPow_ct (M : Mont) (Sq : MontS) {a b output : Operand} {o : Nat}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (callHead a b output o)) hc).isSome = true) :
    RelCT isa (Two fun p s => CallPre a b output p s ∧ p.1.x.o = o)
      (Core.publicPow Sq.mm M.mm o a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output o))
    (.seq (VG.Impl.Dsa.X86_64.PublicPower.power Sq.mm M.mm arg argLen arg2 arg2Len) (seqs Core.finish))) _
  refine RelCT.seq (two_post (Ψ := fun p s => PowerFinishPre (p.1.toPowerFinishPublic, p.2) s)
    (two_map (fun p : Call3Public × List Byte => p.1) (fun _ _ h => h.1.1) (callHead_ct hT)) ?_)
    (two_map (fun p : Call3Public × List Byte => (p.1.toPowerFinishPublic, p.2)) (fun _ _ h => h) (powerFinish_ct M Sq))
  intro p s ⟨h, heq⟩
  rw [← heq]
  exact callHead_public ha hb ho h

def ReadyPublicPre (side : ModulusSide) (d : Nat) (a b : Operand)
    (p : ReadyCallPublic side d × List Byte) (s : State) : Prop :=
  ReadyCallPre side d a b p.1 s ∧ OperandBytes s p.1.layout.base activeBytes b p.2 ∧ p.2.length = p.1.exponentLen

theorem readyPublicPow_ct (M : Mont) (Sq : MontS) (side : ModulusSide) (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (hd : d < 2 ^ 31)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block (callHead a b ⟨.local d, side.lengthField⟩ side.offset)) hc).isSome = true) :
    RelCT isa (Two (ReadyPublicPre side d a b))
      (Core.publicPow Sq.mm M.mm side.offset a b ⟨.local d, side.lengthField⟩) (fun _ _ => True) := by
  apply two_map (fun p : ReadyCallPublic side d × List Byte => (p.1.call a b, p.2)) ?_
    (corePublicPow_ct M Sq (output := ⟨.local d, side.lengthField⟩) ha hb hd hT)
  intro p s ⟨h, he, hlen⟩
  refine ⟨⟨readyCall_pre hpa hpb h, ?_, hlen⟩, rfl⟩
  have hp := h.1.publicPointer b.pointer hpb
  simpa only [hp, ReadyCallPublic.call, PowerCallPublic.x] using he.source

end VG.Proof.Dsa.X86_64.PublicPower
