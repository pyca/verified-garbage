module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NativeParametersCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GenerateCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Dispatch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NativeParametersCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GenerateCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Dispatch
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration

/-! # Public parameter lengths select one of the three verified generators -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Mgf1.X86_64 (sp)


variable {checkName : String}

def DispatchBefore (n : Nat) (p : ParameterPublic) : State → Prop :=
  ParameterStart n p.context.geo.pLen p.context.geo.qLen p

def DispatchChecked (n len : Nat) (p : ParameterPublic) (s : State) : Prop :=
  DispatchBefore n p s ∧ s.gpr .rax = BitVec.ofNat 64 p.context.geo.pLen ∧
    isa.eval .e s = some (BitVec.ofNat 64 p.context.geo.pLen == BitVec.ofNat 64 len)

theorem dispatchBefore_congr {n : Nat} {p : ParameterPublic} {s t : State}
    (h : DispatchBefore n p s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) : DispatchBefore n p t := by
  obtain ⟨⟨W, hW, h16⟩, hf, hw, hp, hq⟩ := h
  exact ⟨⟨W, hW.congr hm hk, h16⟩, hf.congr (hk.gpr (by decide)) hk.2.2, hk.2.2.trans hw, hp, hq⟩

theorem dispatch_check (n : Nat) :
    RelCT isa (Two (DispatchBefore n)) (.block [.mov .rax (.mem (sp 136)), .alu .cmp .rax (.imm 128)])
      (Two (DispatchChecked n 128)) := by
  refine two_piece [.rsp] ?_ (by taint_decide) ?_
  · intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  · intro p s h
    obtain ⟨W, hm, _⟩ := h.1
    obtain ⟨V, R⟩ := hm.rep
    have h17 := (hm.slots 17 (by simp [generationSlots])).trans p.context.pLenSlot
    refine WP.mono (lengthTest_ok hm.layout R) fun t ⟨ha, hz, he, hk⟩ => ?_
    exact ⟨dispatchBefore_congr h he hk, ha.trans h17, by simp only [eval, hz, h17]; rfl⟩

def DispatchLarge (n : Nat) (p : ParameterPublic) (s : State) : Prop :=
  DispatchBefore n p s ∧ s.gpr .rax = BitVec.ofNat 64 p.context.geo.pLen ∧ p.context.geo.pLen ≠ 128

def DispatchLargeChecked (n : Nat) (p : ParameterPublic) (s : State) : Prop :=
  DispatchBefore n p s ∧ p.context.geo.pLen ≠ 128 ∧
    isa.eval .e s = some (BitVec.ofNat 64 p.context.geo.pLen == 256)

theorem dispatch_check256 (n : Nat) :
    RelCT isa (Two (DispatchLarge n)) (.block [.alu .cmp .rax (.imm 256)])
      (Two (DispatchLargeChecked n)) := by
  refine two_piece [.rax] ?_ (by taint_decide) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.2.1.trans ht.2.1.symm
  · intro p s ⟨h, ha, hn⟩
    refine WP.mono lengthTest256_ok fun t ⟨hz, he, hk⟩ => ?_
    exact ⟨dispatchBefore_congr h he hk, hn, by simp only [eval, hz, ha]⟩

theorem dispatch_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3) :
    RelCT isa (Two (DispatchBefore n)) (dispatch (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) (fun _ _ => True) := by
  unfold dispatch
  refine RelCT.seq (dispatch_check n) (two_ite (fun _ _ _ hs ht => hs.2.2.trans ht.2.2.symm) ?_ ?_)
  · apply two_map (fun p : ParameterPublic => p) ?_ (generate_ct (checkName := checkName) H M Sq T n hn 128 20 (Or.inl ⟨rfl, rfl⟩))
    intro p s h
    have hb := Option.some.inj (h.1.2.2.symm.trans h.2)
    rcases p.context.geo.lengths with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
    · simpa only [DispatchBefore, hp, hq] using h.1.1
    all_goals simp [hp] at hb
  · have tail : RelCT isa (Two (DispatchLarge n))
        (.seq (.block [.alu .cmp .rax (.imm 256)])
          (.ite .e (generate (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run 256 32)
            (generate (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run 384 32))) (fun _ _ => True) := by
      refine RelCT.seq (dispatch_check256 n) (two_ite (fun _ _ _ hs ht => hs.2.2.trans ht.2.2.symm) ?_ ?_)
      · apply two_map (fun p : ParameterPublic => p) ?_ (generate_ct (checkName := checkName) H M Sq T n hn 256 32 (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        intro p s h
        have hb := Option.some.inj (h.1.2.2.symm.trans h.2)
        rcases p.context.geo.lengths with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
        · exact False.elim (h.1.2.1 hp)
        · simpa only [DispatchBefore, hp, hq] using h.1.1
        · simp [hp] at hb
      · apply two_map (fun p : ParameterPublic => p) ?_ (generate_ct (checkName := checkName) H M Sq T n hn 384 32 (Or.inr (Or.inr ⟨rfl, rfl⟩)))
        intro p s h
        have hb := Option.some.inj (h.1.2.2.symm.trans h.2)
        rcases p.context.geo.lengths with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
        · exact False.elim (h.1.2.1 hp)
        · simp [hp] at hb
        · simpa only [DispatchBefore, hp, hq] using h.1.1
    apply two_map (fun p : ParameterPublic => p) ?_ tail
    intro p s h
    refine ⟨h.1.1, h.1.2.1, fun hp => ?_⟩
    have hb := Option.some.inj (h.1.2.2.symm.trans h.2)
    simp [hp] at hb

end VG.Proof.Dsa.X86_64.Generation
