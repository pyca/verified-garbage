module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Aes
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # A cached-key GCM batch from one buffer to another -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZHTo
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch dp dR pR
  cR yR bAddr addr_eq in_sub sch_frame)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZHTo (batchTo)
open VG.Proof.Gcm.X86_64.StitchZTo hiding batchTo_ok
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

theorem batchTo_keeps (j : Nat) (g : Nat → List Instr)
    (hg : ∀ j, (g j).all Instr.keepsH = true) : (batchTo j g).all Instr.keepsH = true :=
  StitchZH.batch_keeps j g hg false true

theorem batchTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [⟨oAddr s₀ c, 256⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 16 ≤ nb s₀) {s : State} (hI : AInvTo s₀ c s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s)
    (hgh : ∀ j, (g j).all Instr.keepsH = true)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (op s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batchTo j g) s fun s' => AInvTo s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨oAddr s₀ c, 256⟩] s.mem s'.mem ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (StitchZH.batchM_ok (ix := true) (ld := true) hp.toM rfl (fun _ => rfl) g G hG Q hg hq hqx hc (hI.toM hp) hCache hgh
    (fun _ => hI.r8) hrdx hQ) fun _ ⟨hA, h⟩ => ⟨hA.toTo h.2.1 hI.r8, h⟩

end VG.Proof.Gcm.X86_64.StitchZHTo
