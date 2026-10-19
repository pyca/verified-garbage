module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign

meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRetry
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawControl
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRetry
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Exp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawControl
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! Retry control reveals only the signer's low-word success bit and attempt budget. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomRetryPublic where
  B : Addr
  success : Bool
  attempts : Nat

def RandomRetryPre (p : RandomRetryPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧
  (s.gpr .rax).setWidth 32 = (if p.success then 1 else 0) ∧
  word s.mem p.B Random.oAttempts = BitVec.ofNat 64 p.attempts ∧
  0 < p.attempts ∧ p.attempts < 2 ^ 64

def RandomRetryMid (p : RandomRetryPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧ s.zf = some (!p.success) ∧
  word s.mem p.B Random.oAttempts = BitVec.ofNat 64 p.attempts ∧
  0 < p.attempts ∧ p.attempts < 2 ^ 64

private theorem header_ok {p : RandomRetryPublic} {s : State} (h : RandomRetryPre p s) :
    WP isa (.block [.mov32 .rax (.reg .rax), .store (Random.sp Random.oStatus) .rax,
      .alu .cmp .rax (.imm 0)]) s (RandomRetryMid p) := by
  obtain ⟨hs, hsp, ha, hn, hp, hb⟩ := h
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s.mem.writeW (off p.B Random.oStatus) (if p.success then (1 : BitVec 64) else 0) ∧
      t.zf = some (!p.success)) (by
      cases hx : p.success <;> xrun [random_ea_sp, hsp, hs.st (d := Random.oStatus) (by decide), hx, ha] <;> rfl) rfl)
    fun t ⟨⟨hm, hz⟩, hk⟩ => ?_
  refine ⟨hs.congr hk.2.2, (hk.gpr (by decide)).trans hsp, hz, ?_, hp, hb⟩
  rw [hm, (writeW_outside _ p.B _ (by decide)).word (by decide) (by decide)]
  exact hn

private theorem decrement_ok {p : RandomRetryPublic} {s : State} (h : RandomRetryMid p s) :
    WP isa (.block [.mov .rax (.mem (Random.sp Random.oAttempts)), .alu .sub .rax (.imm 1),
      .store (Random.sp Random.oAttempts) .rax]) s fun t =>
      t.gpr .rsp = p.B ∧ t.zf = some (decide (p.attempts = 1)) := by
  obtain ⟨hs, hsp, _, hn, hp, hb⟩ := h
  have hz : (BitVec.ofNat 64 (p.attempts - 1) == 0) = decide (p.attempts = 1) := by
    rw [ofNat64_beq_zero (by omega)]
    exact decide_eq_decide.mpr (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (p.attempts = 1)))
    (by xrun [random_ea_sp, hsp, hs.ld (d := Random.oAttempts) (by decide),
      hs.st (d := Random.oAttempts) (by decide), hn, ofNat64_pred hp hb, hz]) rfl)
    fun _ ⟨ht, hk⟩ => ⟨(hk.gpr (by decide)).trans hsp, ht⟩

theorem random_callFinish_ct : RelCT isa (Two RandomRetryPre) RandomSign.callFinish (fun _ _ => True) := by
  unfold RandomSign.callFinish
  refine RelCT.seq (two_piece (Ψ := RandomRetryMid) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => header_ok h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.2.1.trans ht.2.1.symm
  · refine two_ite (fun p s t hs ht => by simp only [eval, hs.2.2.1, ht.2.2.1]) ?_ ?_
    · refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rsp = p.B ∧
        s.zf = some (decide (p.attempts = 1))) [.rsp] ?_ (by taint_decide)
        (fun _ _ h => decrement_ok h.1)) ?_
      · intro p s t hs ht r hr
        rw [List.mem_singleton] at hr
        subst r
        exact hs.1.2.1.trans ht.1.2.1.symm
      · refine two_ite (fun p s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
        · apply two_taint [.rsp] ?_ (by taint_decide)
          intro p s t hs ht r hr
          rw [List.mem_singleton] at hr
          subst r
          exact hs.1.1.trans ht.1.1.symm
        · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.X86_64
