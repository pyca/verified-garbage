module

public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Front
import VerifiedGarbage.Proof.Ecdsa.X86_64.Scalar
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Impl.EcKey.Validate.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Front
public import VerifiedGarbage.Spec.EcKey.Validate
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `EcKey.Validate.X86_64.Contract`, which this module and modules that import it used -/

section

/-! # The standalone validation contract on x86-64, by name -/

@[expose] public section

namespace VG.Proof.EcKey.Validate.X86_64

open VG VG.X86_64

/-- The signature's obligations needed by the correctness proof. -/
def keyContract (C : Spec.Weierstrass.Curve) : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .rdi, 2 * C.len + 1⟩
    let ws : Region := ⟨s.gpr .rsi, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [pk] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ ret.Disjoint ws ∧
      (s.gpr .rsi).toNat + 8192 ≤ 2 ^ 64
  post s s' := (s'.gpr .rax).setWidth 32 =
    if (Spec.EcKey.decodePublicKey C (Spec.EcKey.bytesAt s.mem (s.gpr .rdi) (2 * C.len + 1))).isSome
      then 1 else 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

/-- The exported contract requires all of these facts and nothing about
initial workspace contents or caller-provided curve constants. -/
theorem implies (I : Spec.EcKey.Instance)
    (hsat : ∃ s, (I.validatePublicKeyContract abi 8).pre s) :
    (keyContract I.curve).Implies (I.validatePublicKeyContract abi 8) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.validatePublicKeyContract,
      Spec.EcKey.Instance.validatePublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, keyContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.validatePublicKeyContract,
      Spec.EcKey.Instance.validatePublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, keyContract]
    exact h
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.validatePublicKeyContract,
      Spec.EcKey.Instance.validatePublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, keyContract]
  sat := hsat

/-- A witness used to check each curve's exported precondition. -/
def satState (len : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x8000 | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 2 * len + 1⟩]
  wr := [⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Validate.X86_64

end

end

/-! ### `EcKey.Validate.X86_64.Finish`, which only this module used -/

section

/-! # Return the existing validity flag and restore the calling convention -/

@[expose] public section

namespace VG.Proof.EcKey.Validate.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.Ecdsa.Verify.X86_64 (KeyOk)

/-- The finish is the same flag conversion and register restore used elsewhere. -/
theorem finish_eq (c : Cfg) : Impl.EcKey.Validate.X86_64.finish c =
    ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
    (([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++ Spill.restoreCode .rdi Cfg.saved) := rfl

/-- No new arithmetic: reuse the flag-bit and register-restore proofs. -/
theorem finish_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ s : State} {g : Reg → BitVec 64}
    (F : Front c s₀ g s) :
    WP isa (.block (Impl.EcKey.Validate.X86_64.finish c)) s fun s' =>
      (s'.gpr .rax).setWidth 32 = (if KeyOk c s₀ then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) := by
  have hsz : size = 8192 := rfl
  have hF : c.sl FLAG + 8 ≤ size := by
    have := sl_le c hc.n10 (i := FLAG) (by decide)
    have := hc.n0
    omega_arith
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (movRcx_mem_ok F.scr hF) fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (raxBit_ok s₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := (F.scr.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  have saved₂ : Spill.Saved s₂.mem (s₂.gpr .rdi) g Cfg.saved := by
    rw [hs₂.rdi, k₂.2.1, k₁.2.1]; exact F.saved
  refine WP.mono (Spill.restore_ok .rdi Cfg.saved g s₂ (by decide)
    (fun p hp => ?_) saved₂) fun s₃ ⟨saved₃, kept₃, _⟩ => ?_
  · have := saved_lt p hp
    rw [hs₂.rdi]
    exact ⟨_, List.mem_append_right _ hs₂.wr, Offset.contains_base _ (by omega_using [hsz, this]) (by omega_using [this])⟩
  · refine ⟨?_, fun r hr => (saved₃ r hr).trans (F.original r hr)⟩
    rw [kept₃ .rax (by decide), e₂, e₁, F.flag]
    simpa only [mask, decide_eq_true_eq] using (mask_bit (decide (KeyOk c s₀)))

end VG.Proof.EcKey.Validate.X86_64

end

end


/-!
# The standalone validator's correctness

Compose the existing decoder, point check, flag conversion, and register
restore. The bridge to the encoded-key specification is ECDH's existing
`decode_eq`; no new curve-arithmetic argument is needed.
-/

@[expose] public section

namespace VG.Proof.EcKey.Validate.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Proof.Ecdsa.Verify.X86_64 (KeyOk keyX keyY)
open VG.Spec.Weierstrass

/-- The check's existing validity predicate is precisely successful decoding. -/
theorem decode_key (c : Cfg) (s : State) :
    (Spec.EcKey.decodePublicKey c.C
      (Spec.EcKey.bytesAt s.mem (s.gpr .rdi) (2 * c.C.len + 1))).isSome = decide (KeyOk c s) := by
  have hlen : (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdi) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega_using []
  have hb0 : (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdi) (1 + 2 * c.C.len)).head? =
      some (s.mem (s.gpr .rdi)) := by rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s.mem (s.gpr .rdi) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s.mem (s.gpr .rdi) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hiff : Proof.Ecdh.Valid c.C (s.mem (s.gpr .rdi)) (keyX c s) (keyY c s) ↔ KeyOk c s := by
    constructor
    · rintro ⟨h4, hx, hy, hcv⟩; exact ⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩
    · rintro ⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩; exact ⟨h4, hx, hy, hcv⟩
  have hlen' : 2 * c.C.len + 1 = 1 + 2 * c.C.len := Nat.add_comm _ _
  change (Spec.EcKey.decodePublicKey c.C
    (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdi) (2 * c.C.len + 1))).isSome = _
  rw [hlen', Proof.Ecdh.decode_eq hlen hb0 hxv hyv]
  by_cases hk : KeyOk c s
  · rw [dite_eq_left (hiff.mpr hk)]
    exact (decide_eq_true_iff.mpr hk).symm
  · rw [dite_eq_right (mt hiff.mp hk)]
    exact (decide_eq_false_iff_not.mpr hk).symm

/-- Correctness of the inlined code, with the ABI's register restores. -/
theorem correct (c : Cfg) (hc : BaseCfgOk c)
    (hi : (Impl.EcKey.Validate.X86_64.validate c).InlineOk = true)
    (hmx : (Impl.EcKey.Validate.X86_64.validate c).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (hs : (keyContract c.C).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Validate.X86_64.validate c).inline s t s' ∧
      abiPreserved s s' ∧ (keyContract c.C).post s s' := by
  obtain ⟨hrd, hwr, hd, hret, hfit⟩ := hs
  have hp : Pre c s :=
    ⟨by rw [hrd, show 1 + 2 * c.C.len = 2 * c.C.len + 1 from Nat.add_comm _ _]; simp,
      by rw [hwr]; simp, by simpa only [Nat.add_comm] using hd, hfit⟩
  obtain ⟨t, s', he, hpost, saved⟩ := front_ok hc hp (fun g t F => finish_ok hc F)
  have he' : Exec isa (Impl.EcKey.Validate.X86_64.validate c).inline s t s' := he
  have hsp := Code.clobbers_rsp_of_inlineOk hi
  have F := (Exec.regions he' (Code.noCalls_inline hi)).2.2
  refine ⟨t, s', he', abiPreserved_of_exec (by rw [Code.allInstrs_inline]; exact hmx) he'
    ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact saved _ (by decide)
    · exact saved _ (by decide)
    · exact Exec.gpr hsp he'
    · exact saved _ (by decide)
    · exact saved _ (by decide)
    · exact saved _ (by decide)
    · exact saved _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hret) (by decide)
  · change (s'.gpr .rax).setWidth 32 = _
    rw [decode_key]
    simpa only [decide_eq_true_eq] using hpost

end VG.Proof.EcKey.Validate.X86_64
