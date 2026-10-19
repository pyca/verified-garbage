module
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.AesOcb.AArch64.Args

import VerifiedGarbage.Proof.AesOcb.AArch64.CTBase
meta import VerifiedGarbage.Proof.AesOcb.AArch64.CTBase
import VerifiedGarbage.Proof.AesOcb.AArch64.NonceBlock
meta import VerifiedGarbage.Proof.AesOcb.AArch64.NonceBlock
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Aes.AArch64.Decrypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesOcb.AArch64.Contract
import VerifiedGarbage.Proof.AesOcb.AArch64.LNtz
import VerifiedGarbage.Proof.AesOcb.AArch64.Nonce
import VerifiedGarbage.Proof.AesOcb.AArch64.Offset0
import VerifiedGarbage.Proof.AesOcb.AArch64.PadTo
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Spec.Ocb.Contract
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Aes.AArch64.Decrypt
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesOcb.AArch64.Contract
meta import VerifiedGarbage.Proof.AesOcb.AArch64.LNtz
meta import VerifiedGarbage.Proof.AesOcb.AArch64.Nonce
meta import VerifiedGarbage.Proof.AesOcb.AArch64.Offset0
meta import VerifiedGarbage.Proof.AesOcb.AArch64.PadTo
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Cmac.Dbl32
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Ocb.Spec
meta import VerifiedGarbage.Proof.Ocb.State
meta import VerifiedGarbage.Spec.Ocb.Contract

/-!
# AES-OCB on AArch64: `Offset_0` is constant time

Untrusted: everything here is checked by Lean. `nonceBlock` loads the
nonce's address and length from `W`: its first block is split there, and the
rest runs from them (`nonceBlock_rel`); then the call (`callBlocks_rel`) and
`offset0`, whose shifts by `bottom` are masks, not branches (`nonce_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq)

theorem nonceBlock_rel {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁)
    (E₂ : Env K W D R n SP σ₂) {N : Addr} {nl : Nat}
    (hN₁ : σ₁.mem.readW (W + BitVec.ofNat 64 nO) 64 = N) (hN₂ : σ₂.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (hnl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl) :
    RelCT isa (Eq2 σ₁ σ₂) nonceBlock TT := by
  obtain ⟨s₁, run₁, x12₁, x13₁, g₁, -, -, sp₁, rd₁, wr₁⟩ := nonceHead_ok E₁.x19 E₁.perm.w hN₁ hnl₁
  obtain ⟨s₂, run₂, x12₂, x13₂, g₂, -, -, sp₂, rd₂, wr₂⟩ := nonceHead_ok E₂.x19 E₂.perm.w hN₂ hnl₂
  unfold nonceBlock
  refine rel_seq (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨s₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact rel_env (E₁.keep (fun r hr => g₁ r (envRegs_ne hr) (envRegs_ne hr) (envRegs_ne hr)) sp₁ rd₁ wr₁)
    (E₂.keep (fun r hr => g₂ r (envRegs_ne hr) (envRegs_ne hr) (envRegs_ne hr)) sp₂ rd₂ wr₂) [.x12, .x13]
    (by agree_tac [x12₁, x12₂, x13₁, x13₂]) ⟨_, by taint_decide⟩

theorem nonce_rel (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {σ₁ σ₂ : State}
    (E₁ : Env K W D R n SP σ₁) (E₂ : Env K W D R n SP σ₂) (hR : R = 10 ∨ R = 12 ∨ R = 14) {N : Addr} {nl t : Nat}
    (hN₁ : σ₁.mem.readW (W + BitVec.ofNat 64 nO) 64 = N) (hN₂ : σ₂.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (hnl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t)
    (htl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15)
    (ht : t < 2 ^ 64) (hB₁ : Buf W σ₁ N nl) (hB₂ : Buf W σ₂ N nl) :
    RelCT isa (Eq2 σ₁ σ₂) (nonce (callees v)) TT := by
  unfold nonce
  refine rel_seq (nonceBlock_rel E₁ E₂ hN₁ hN₂ hnl₁ hnl₂)
    (nonceBlock_ok L E₁.x19 E₁.perm.w hN₁ hnl₁ htl₁ h1 h15 ht hB₁)
    (nonceBlock_ok L E₂.x19 E₂.perm.w hN₂ hnl₂ htl₂ h1 h15 ht hB₂) fun τ₁ τ₂ P₁ P₂ => ?_
  have F₁ : Env K W D R n SP τ₁ := E₁.others P₁.gpr P₁.sp P₁.rd P₁.wr
  have F₂ : Env K W D R n SP τ₂ := E₂.others P₂.gpr P₂.sp P₂.rd P₂.wr
  refine rel_seq (callBlocks_rel v.encOk v.encCt L hR F₁ F₂ [] (by agree_tac []) ⟨_, by taint_decide⟩
      (oneBlock_ok F₁.x19 tmpO (by decide)) (oneBlock_ok F₂.x19 tmpO (by decide))
      (dstW L F₁.perm (d := tmpO) (n := 1) (by decide)) (dstW L F₂.perm (d := tmpO) (n := 1) (by decide)))
    (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₁ hR (oneBlock_ok F₁.x19 tmpO (by decide))
      (dstW L F₁.perm (d := tmpO) (n := 1) (by decide)))
    (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₂ hR (oneBlock_ok F₂.x19 tmpO (by decide))
      (dstW L F₂.perm (d := tmpO) (n := 1) (by decide))) fun u₁ u₂ Q₁ Q₂ => ?_
  exact rel_env (F₁.of_saved Q₁.saved Q₁.sp Q₁.rd Q₁.wr) (F₂.of_saved Q₂.saved Q₂.sp Q₂.rd Q₂.wr) []
    (by agree_tac []) ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64
