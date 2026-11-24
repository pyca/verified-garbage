module

import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.X86.Mac
public import VerifiedGarbage.Proof.AesCcm.X86.Run
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.AesCcm.X86.Mac
meta import VerifiedGarbage.Proof.AesCcm.X86.Run
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesCcm.X86.Entry
import VerifiedGarbage.Proof.AesCcm.X86.Blocks
meta import VerifiedGarbage.Proof.AesCcm.X86.Entry
meta import VerifiedGarbage.Proof.AesCcm.X86.Blocks
meta import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86.Top
meta import VerifiedGarbage.Proof.AesGcm.X86.Fn
public import VerifiedGarbage.Proof.AesCcm.X86.Absorb
public import VerifiedGarbage.Proof.AesCcm.X86.AadCT
import VerifiedGarbage.Proof.AesCcm.X86.Aad
meta import VerifiedGarbage.Proof.AesCcm.X86.Absorb
meta import VerifiedGarbage.Proof.AesCcm.X86.AadCT
meta import VerifiedGarbage.Proof.AesCcm.X86.Aad
import VerifiedGarbage.Proof.AesCcm.X86.Callee
meta import VerifiedGarbage.Proof.AesCcm.X86.Callee
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ccm
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Spec.Ccm
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
meta import VerifiedGarbage.Proof.AesGcm.X86.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86.Common
meta import VerifiedGarbage.Proof.AesGcm.X86.Env
meta import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesGcm.X86.Fn
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.AesCcm.Mac
meta import VerifiedGarbage.Proof.AesGcm.X86.Absorb
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
meta import VerifiedGarbage.Proof.Aes.X86.VariantProof
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.AesCcm.Ctr
meta import VerifiedGarbage.Proof.AesGcm.X86.Flush
meta import VerifiedGarbage.Proof.Cmac.Stream

/-! ### `AesCcm.X86.TopCT`, which this module and modules that import it used -/

section

/-! ### `AesCcm.X86.Seal`, which this module and modules that import it used -/

section

/-! ### `AesCcm.X86.Data`, which this module and modules that import it used -/

section

/-!
# AES-CCM on x86: the data (`data`)

Untrusted: everything here is checked by Lean. `data` takes the whole blocks of
the data a chunk at a time (`dataWhole_ok`): a chunk (`chunk_ok`) is chained
into the MAC state by a call of `vg_cmac_aes_update` (`updStep_ok`) and XORed
with the keystream from its counter by a call of `vg_aes_ctr32_to`
(`ctrStep_ok`), the plaintext chained either way; the counters' low 32 bits do
not wrap around, as there are fewer than 2²⁸ blocks. Then the last
`n mod 16` bytes, with `CIPH_K(Ctr₁₊ₙ/₁₆)`, which `vg_aes_ctr32_to` writes over
a zero block (`ctrTail_ok`): the data XORed with CCM's keystream from `Ctr₁`,
which is its encryption (`Proof.AesCcm.crypt_eq`), and the MAC state with the
plaintext, padded, chained (`data_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop splitWhole dO nO)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold zero4_bytes' length_bytesAt and_self_beq32
  XorPre XorPost xorLoop_ok xorBytes shr4 and15 runBlock_app_of covers_left covers_off)

/-- What `data` writes: `Ctrⱼ` and the keystream block at `[64, 96)`, the MAC
state and `B`, `[240, 2560)`, the stack and the data. -/
abbrev ctrR (W SP D : BitVec 32) (n y : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 64, 32⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 32, 16⟩, wC W,
    below SP 60, ⟨w64 D, n⟩]

/-- What `data` needs. -/
structure CtrCtx (K W SP : BitVec 32) (s : State) (R : Nat) (nonce : List Byte) (D : BitVec 32) (n y : Nat) : Prop where
  lay : Lay K W SP
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  h7 : 7 ≤ nonce.length
  h13 : nonce.length ≤ 13
  hn : n < 256 ^ (15 - nonce.length)
  hn32 : n < 2 ^ 32
  hy : y = 0 ∨ y = 96
  c0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0
  buf : Buf W SP s D n
  dw : Covers [⟨w64 D, n⟩] s.wr
  dk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩

namespace CtrCtx

variable {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {n y : Nat}
  (C : CtrCtx K W SP s R nonce D n y)
include C

/-- The parts of `W` that `data` does not write. -/
theorem disj {d k : Nat} (h : 48 ≤ d ∧ d + k ≤ 64 ∨ 112 ≤ d ∧ d + k ≤ 240) :
    ∀ r ∈ ctrR W SP D n y, (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  have hy := C.hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Lay.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact Lay.w_w (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Lay.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (C.lay.stk_w' (by omega_arith)).symm
  · exact (C.buf.w.sub_right (Lay.wSub (by omega_arith))).symm

theorem slot_kept {m : Mem} (hf : Frame (ctrR W SP D n y) s.mem m) {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) :
    slotv m W o = slotv s.mem W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (C.disj (.inr ⟨by omega_arith, h₂⟩)) (by decide)

theorem c0_kept {m : Mem} (hf : Frame (ctrR W SP D n y) s.mem m) :
    bytesAt m (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
  rw [Proof.AesGcm.X86.bytesAt_frame hf (C.disj (.inl (by decide))) (by decide), C.c0]

theorem ciph_kept {m : Mem} (hf : Frame (ctrR W SP D n y) s.mem m) :
    Spec.Ccm.ctxCiph m (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R := by
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases C.rounds with h | h | h <;> subst h <;> decide
  have hy := C.hy
  refine ctxCiph_frame hf (fun r hr => ?_) hRb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.k_w.sub_right (Lay.wSub (by omega_arith))
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.stk_k.symm
  · exact C.dk

end CtrCtx

/-- The plaintext of the `k` bytes at `D`, if they are it (`enc`) or
encrypted. -/
abbrev ptOf (K : BitVec 32) (s : State) (R : Nat) (nonce : List Byte) (D : BitVec 32) (enc : Bool) (k : Nat) :
    List Byte :=
  if enc then bytesAt s.mem (w64 D) k
  else xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) k)

/-- After `q` whole blocks, with the last bytes' address and length at `dO`
and `nO`, and nothing said of the MAC state. -/
structure CtrMid (K W SP : BitVec 32) (s : State) (R : Nat) (nonce : List Byte) (D : BitVec 32) (n y : Nat)
    (q : Nat) (t : State) : Prop where
  env : Env K W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (ctrR W SP D n y) s.mem t.mem
  dO : slotv t.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16))
  nO : slotv t.mem W nO = BitVec.ofNat 32 (n % 16)
  done : bytesAt t.mem (w64 D) (16 * q) =
    xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) (16 * q))
  rest : bytesAt t.mem (w64 D + BitVec.ofNat 64 (16 * q)) (n - 16 * q) =
    bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * q)) (n - 16 * q)

/-- The same, with the plaintext chained into the MAC state. -/
structure DataMid (K W SP : BitVec 32) (s : State) (R : Nat) (nonce : List Byte) (D : BitVec 32) (n y : Nat) (enc : Bool)
    (q : Nat) (t : State) : Prop extends CtrMid K W SP s R nonce D n y q t where
  mac : bytesAt t.mem (w64 W + BitVec.ofNat 64 y) 16 =
    Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
      (Spec.Cmac.blocks 16 (ptOf K s R nonce D enc (16 * q)))

/-! ## The calls of a chunk -/

/-- The arguments of `updStep y`'s call. -/
theorem updStepArgs_ok {K W SP : BitVec 32} {u : State} (L : Lay K W SP) (E : Env K W SP u) {R : Nat}
    (hK : slotv u.mem W ctxO = K) (hRo : slotv u.mem W roundsO = BitVec.ofNat 32 R) {P : BitVec 32} {k : Nat}
    (hq : slotv u.mem W qO = P) (hk : slotv u.mem W kO = BitVec.ofNat 32 k) (y : Nat) :
    ∃ u₁, runBlock isa (keyArgs y ++ ([.mov .ebx (slot qO), .mov .esi (slot kO)] : List Instr) ++ updScr) u = some u₁ ∧
      u₁.mem = u.mem ∧ u₁.gpr .eax = K ∧ u₁.gpr .ecx = BitVec.ofNat 32 R ∧ u₁.gpr .edx = W + BitVec.ofNat 32 y ∧
      u₁.gpr .ebx = P ∧ u₁.gpr .esi = BitVec.ofNat 32 k ∧ u₁.gpr .edi = W + BitVec.ofNat 32 384 ∧
      u₁.gpr .ebp = W ∧ u₁.gpr .esp = SP ∧ u₁.rd = u.rd ∧ u₁.wr = u.wr := by
  refine ⟨_, by crun [keyArgs, updScr, E.ebp, L.aW, E.perm.wR, hK, hRo, hq, hk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hK]
  · cregs [hRo]
  · cregs [E.ebp]
  · cregs [hq]
  · cregs [hk]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals rfl

/-- What a chunk's two calls write. -/
abbrev chR (W SP P : BitVec 32) (k y : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 384, 2176⟩,
    below SP 60, ⟨w64 P, 16 * k⟩]

/-- The `k` blocks at `P` chained into the MAC state at `W + y`. -/
theorem updStep_ok (v : Ctr32Impl) {K W SP : BitVec 32} {u : State} (L : Lay K W SP) (E : Env K W SP u) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv u.mem W ctxO = K) (hRo : slotv u.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : BitVec 32} {k : Nat} (hP : Buf W SP u P (16 * k)) (hk32 : 16 * k < 2 ^ 32)
    (hq : slotv u.mem W qO = P) (hk : slotv u.mem W kO = BitVec.ofNat 32 k) :
    WP isa (updStep v.callee v.suffix y) u fun u' => Env K W SP u' ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 384, 2176⟩, below SP 60] u.mem u'.mem ∧
      bytesAt u'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph u.mem (w64 K) R) (bytesAt u.mem (w64 W + BitVec.ofNat 64 y) 16)
          (Spec.Cmac.blocks 16 (bytesAt u.mem (w64 P) (16 * k))) := by
  obtain ⟨u₁, run₁, m₁, ax, cx, dx, bx, si, di, bp, sp, rd₁, wr₁⟩ := updStepArgs_ok L E hK hRo hq hk y
  refine WP.seq (WP.of_runBlock ⟨u₁, run₁, ?_⟩)
  obtain E₁ : Env K W SP u₁ := E.keep (by rw [bp, E.ebp]) (by rw [sp, E.esp]) rd₁ wr₁
  refine WP.mono (updCall_ok v L E₁ hR (by omega_arith) (srcBuf (hP.of_eq rd₁ wr₁))
    (hP.w.sub_right (Lay.wSub (by omega_arith))) hk32 ax cx dx bx si di)
    fun u₂ ⟨E₂, rd₂, wr₂, _, f₂, o₂⟩ => ⟨E₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [← m₁]; exact f₂, ?_⟩
  rw [o₂, Proof.Cmac.Stream.blocksAt_eq, m₁]

/-- The arguments of `ctrStep`'s call. -/
theorem ctrStepArgs_ok {K W SP : BitVec 32} {u : State} (L : Lay K W SP) (E : Env K W SP u) {R : Nat}
    (hK : slotv u.mem W ctxO = K) (hRo : slotv u.mem W roundsO = BitVec.ofNat 32 R) {P : BitVec 32} {k : Nat}
    (hq : slotv u.mem W qO = P) (hk : slotv u.mem W kO = BitVec.ofNat 32 k) :
    ∃ u₁, runBlock isa (keyArgs c1O ++ ([.mov .ebx (slot qO), .mov .edi (slot kO)] : List Instr)) u = some u₁ ∧
      u₁.mem = u.mem ∧ u₁.gpr .eax = K ∧ u₁.gpr .ecx = BitVec.ofNat 32 R ∧ u₁.gpr .edx = W + BitVec.ofNat 32 64 ∧
      u₁.gpr .ebx = P ∧ u₁.gpr .edi = BitVec.ofNat 32 k ∧ u₁.gpr .ebp = W ∧ u₁.gpr .esp = SP ∧ u₁.rd = u.rd ∧
      u₁.wr = u.wr := by
  refine ⟨_, by crun [keyArgs, E.ebp, L.aW, E.perm.wR, hK, hRo, hq, hk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hK]
  · cregs [hRo]
  · cregs [E.ebp]
  · cregs [hq]
  · cregs [hk]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- The counter block at `W + 64`. -/
abbrev cnt (m : Mem) (W : BitVec 32) : Spec.Gcm.Block := Spec.Gcm.blockAt m (w64 W + BitVec.ofNat 64 64)

/-- `Ctrⱼ`, as `vg_aes_ctr32_to` increments it from `Ctr₀`. -/
abbrev ctrInc (nonce : List Byte) (j : Nat) : Spec.Gcm.Block :=
  Nat.repeat Spec.Gcm.inc32 j (Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce 0))

theorem ctrInc_eq {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {j : Nat}
    (hj : j < 256 ^ (15 - nonce.length)) (hj32 : j < 2 ^ 32) :
    ctrInc nonce j = Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce j) := by
  have h := Proof.AesCcm.repeat_inc32_ctrBlock h7 h13 (j := 0) (k := j + 1) (by omega_using [hj32]) (by omega_using [hj])
    j (Nat.lt_succ_self j)
  rwa [Nat.zero_add] at h

/-- The `k` blocks at `P` XORed with the keystream from the counter block,
which is incremented. -/
theorem ctrStep_ok (v : Ctr32Impl) {K W SP : BitVec 32} {u : State} (L : Lay K W SP) (E : Env K W SP u) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv u.mem W ctxO = K) (hRo : slotv u.mem W roundsO = BitVec.ofNat 32 R)
    {k : Nat} {P : BitVec 32} (hP : Buf W SP u P (16 * k))
    (hPw : Covers [⟨w64 P, 16 * k⟩] u.wr) (hPk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 P, 16 * k⟩)
    (hq : slotv u.mem W qO = P) (hk : slotv u.mem W kO = BitVec.ofNat 32 k) :
    WP isa (ctrStep v.callee) u fun u' => Env K W SP u' ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 P, 16 * k⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 60]
        u.mem u'.mem ∧
      (∀ nonce : List Byte, 7 ≤ nonce.length → nonce.length ≤ 13 → ∀ j, j + k ≤ 256 ^ (15 - nonce.length) →
        j + k ≤ 2 ^ 32 → cnt u.mem W = ctrInc nonce j →
        bytesAt u'.mem (w64 P) (16 * k) =
          xorFrom (Spec.Ccm.ctxCiph u.mem (w64 K) R) nonce j (bytesAt u.mem (w64 P) (16 * k))) ∧
      cnt u'.mem W = Nat.repeat Spec.Gcm.inc32 k (cnt u.mem W) := by
  obtain ⟨u₁, run₁, m₁, ax, cx, dx, bx, di, bp, sp, rd₁, wr₁⟩ := ctrStepArgs_ok L E hK hRo hq hk
  refine WP.seq (WP.of_runBlock ⟨u₁, run₁, ?_⟩)
  obtain E₁ : Env K W SP u₁ := E.keep (by rw [bp, E.ebp]) (by rw [sp, E.esp]) rd₁ wr₁
  obtain d64 : (⟨w64 P, 16 * k⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ := hP.w.sub_right (Lay.wSub (by decide))
  refine WP.mono (ctrCall_ok v L E₁ hR (c := 64) (by decide) (srcBuf (hP.of_eq rd₁ wr₁)) d64 hPk (by rw [wr₁]; exact hPw)
    ax cx dx bx di) fun u₂ ⟨E₂, rd₂, wr₂, _, f₂, o₂, n₂⟩ => ?_
  rw [m₁] at f₂ o₂ n₂
  refine ⟨E₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], f₂, fun nonce h7 h13 j hj hj32 hc => ?_, n₂⟩
  exact Proof.AesCcm.ctr32_ccm (m := u.mem) (m' := u₂.mem) (K := w64 K) (C := w64 W + BitVec.ofNat 64 64)
    (D := w64 P) (R := R) (nonce := nonce) (by omega_arith) (j := j) (k := k)
    (fun i hi => by
      show Nat.repeat Spec.Gcm.inc32 i (cnt u.mem W) = _
      rw [hc, ← Proof.Gcm.repeat_add, Nat.add_comm i j]
      exact ctrInc_eq h7 h13 (by omega_arith) (by omega_arith)) o₂

/-! ## A chunk -/

/-- What the two calls of a chunk leave: the `k` blocks at `P` XORed with the
keystream from `Ctrⱼ`, and the plaintext chained. -/
structure ChunkPost (K W SP : BitVec 32) (u : State) (R : Nat) (nonce : List Byte) (P : BitVec 32) (k j y : Nat) (enc : Bool)
    (u' : State) : Prop where
  env : Env K W SP u'
  rd : u'.rd = u.rd
  wr : u'.wr = u.wr
  frame : Frame (chR W SP P k y) u.mem u'.mem
  out : bytesAt u'.mem (w64 P) (16 * k) =
    xorFrom (Spec.Ccm.ctxCiph u.mem (w64 K) R) nonce j (bytesAt u.mem (w64 P) (16 * k))
  mac : bytesAt u'.mem (w64 W + BitVec.ofNat 64 y) 16 =
    Spec.Cmac.chain (Spec.Ccm.ctxCiph u.mem (w64 K) R) (bytesAt u.mem (w64 W + BitVec.ofNat 64 y) 16)
      (Spec.Cmac.blocks 16 (if enc then bytesAt u.mem (w64 P) (16 * k)
        else xorFrom (Spec.Ccm.ctxCiph u.mem (w64 K) R) nonce j (bytesAt u.mem (w64 P) (16 * k))))
  cnt : cnt u'.mem W = Nat.repeat Spec.Gcm.inc32 k (cnt u.mem W)

/-- What a chunk starts from: the chunk's slots. -/
structure ChunkPre (K W SP : BitVec 32) (u : State) (R : Nat) (nonce : List Byte) (P : BitVec 32) (k j y : Nat) : Prop where
  lay : Lay K W SP
  env : Env K W SP u
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hy : y = 0 ∨ y = 96
  ctx : slotv u.mem W ctxO = K
  ro : slotv u.mem W roundsO = BitVec.ofNat 32 R
  h7 : 7 ≤ nonce.length
  h13 : nonce.length ≤ 13
  k0 : 0 < k
  hj : j + k ≤ 256 ^ (15 - nonce.length)
  k32 : 16 * k < 2 ^ 32
  hj32 : j + k ≤ 2 ^ 32
  buf : Buf W SP u P (16 * k)
  pw : Covers [⟨w64 P, 16 * k⟩] u.wr
  pk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 P, 16 * k⟩
  q : slotv u.mem W qO = P
  k : slotv u.mem W kO = BitVec.ofNat 32 k

/-- A part of `W` that the calls of a chunk do not write. -/
theorem chR_w {K W SP : BitVec 32} (L : Lay K W SP) {u : State} {P : BitVec 32} {k y : Nat} (hy : y = 0 ∨ y = 96)
    (hP : Buf W SP u P (16 * k)) {d l : Nat} (h : 48 ≤ d ∧ d + l ≤ 64 ∨ 112 ≤ d ∧ d + l ≤ 384) :
    ∀ r ∈ chR W SP P k y, (⟨w64 W + BitVec.ofNat 64 d, l⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Lay.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact Lay.w_w (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (L.stk_w' (by omega_arith)).symm
  · exact (hP.w.sub_right (Lay.wSub (by omega_arith))).symm

theorem chR_k {K W SP : BitVec 32} (L : Lay K W SP) {P : BitVec 32} {k y : Nat} (hy : y = 0 ∨ y = 96)
    (hP : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 P, 16 * k⟩) :
    ∀ r ∈ chR W SP P k y, (⟨w64 K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by omega_arith))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.stk_k.symm
  · exact hP

/-- What a chunk starts from, after its first call. -/
theorem ChunkPre.next {K W SP : BitVec 32} {u u' : State} {R : Nat} {nonce : List Byte} {P : BitVec 32} {k j y : Nat}
    (C : ChunkPre K W SP u R nonce P k j y) (E : Env K W SP u') (rd : u'.rd = u.rd) (wr : u'.wr = u.wr)
    (f : Frame (chR W SP P k y) u.mem u'.mem) : ChunkPre K W SP u' R nonce P k j y := by
  have sl : ∀ o, 112 ≤ o → o + 4 ≤ 384 → slotv u'.mem W o = slotv u.mem W o := fun o h₁ h₂ =>
    f.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _)
      (chR_w C.lay C.hy C.buf (.inr ⟨h₁, h₂⟩)) (by decide)
  exact
    { lay := C.lay
      env := E
      rounds := C.rounds
      hy := C.hy
      h7 := C.h7
      h13 := C.h13
      k0 := C.k0
      hj := C.hj
      k32 := C.k32
      hj32 := C.hj32
      buf := C.buf.of_eq rd wr
      pw := by rw [wr]; exact C.pw
      pk := C.pk
      ctx := by rw [sl _ (by decide) (by decide)]; exact C.ctx
      ro := by rw [sl _ (by decide) (by decide)]; exact C.ro
      q := by rw [sl _ (by decide) (by decide)]; exact C.q
      k := by rw [sl _ (by decide) (by decide)]; exact C.k }

theorem updF {W SP P : BitVec 32} {k y : Nat} {m m' : Mem}
    (f : Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 384, 2176⟩, below SP 60] m m') :
    Frame (chR W SP P k y) m m' := f.mono (by simp)

theorem ctrF {W SP P : BitVec 32} {k y : Nat} {m m' : Mem}
    (f : Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 P, 16 * k⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 60] m m') :
    Frame (chR W SP P k y) m m' := f.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨⟨w64 W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The two calls of a chunk. -/
theorem chunkCalls_ok (v : Ctr32Impl) {K W SP : BitVec 32} {u : State} {R : Nat} {nonce : List Byte} {P : BitVec 32}
    {k j y : Nat} (C : ChunkPre K W SP u R nonce P k j y) (hc : cnt u.mem W = ctrInc nonce j) (enc : Bool) {rest : Prog isa} {Q : State → Prop}
    (hQ : ∀ u', ChunkPost K W SP u R nonce P k j y enc u' → WP isa rest u' Q) :
    WP isa (if enc then .seq (updStep v.callee v.suffix y) (.seq (ctrStep v.callee) rest)
      else .seq (ctrStep v.callee) (.seq (updStep v.callee v.suffix y) rest)) u Q := by
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases C.rounds with h | h | h <;> subst h <;> decide
  have hy := C.hy
  have hk := C.k32
  obtain cnt_upd : ∀ {m m' : Mem}, Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 384, 2176⟩,
      below SP 60] m m' → cnt m' W = cnt m W := fun f =>
    congrArg Spec.Gcm.ofBytes (Proof.AesGcm.X86.bytesAt_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Lay.w_w (by omega_arith) (by omega_arith) (by omega_arith)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (C.lay.stk_w' (by decide)).symm) (by decide))
  obtain dP : ∀ {d l : Nat}, d + l ≤ 2560 → (⟨w64 P, 16 * k⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, l⟩ :=
    fun h => C.buf.w.sub_right (Lay.wSub h)
  cases enc
  · -- the keystream first
    rw [ite_eq_right Bool.false_ne_true]
    refine WP.seq (WP.mono (ctrStep_ok v C.lay C.env C.rounds C.ctx C.ro C.buf C.pw C.pk C.q
      C.k) fun u₁ ⟨E₁, rd₁, wr₁, f₁, o₁, n₁⟩ => ?_)
    replace o₁ := o₁ nonce C.h7 C.h13 j C.hj C.hj32 hc
    have C₁ := C.next E₁ rd₁ wr₁ (ctrF f₁)
    refine WP.seq (WP.mono (updStep_ok v C₁.lay C₁.env C₁.rounds C₁.ctx C₁.ro C₁.hy C₁.buf C₁.k32 C₁.q C₁.k)
      fun u₂ ⟨E₂, rd₂, wr₂, f₂, o₂⟩ => hQ u₂ ?_)
    refine ⟨E₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], (ctrF f₁).trans (updF f₂), ?_, ?_, (cnt_upd f₂).trans n₁⟩
    · rw [Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dP (by omega_arith)
        · exact dP (by decide)
        · exact C.buf.stk.symm) (by omega_arith), o₁]
    · rw [o₂, o₁, ctxCiph_frame (ctrF (y := y) f₁) (chR_k C.lay C.hy C.pk) hRb,
        Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact Lay.w_w (by omega_arith) (by omega_arith) (by decide)
          · exact (dP (by omega_arith)).symm
          · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
          · exact (C.lay.stk_w' (by omega_arith)).symm) (by decide)]
      rfl
  · -- the chaining first
    rw [ite_eq_left rfl]
    refine WP.seq (WP.mono (updStep_ok v C.lay C.env C.rounds C.ctx C.ro C.hy C.buf C.k32 C.q C.k)
      fun u₁ ⟨E₁, rd₁, wr₁, f₁, o₁⟩ => ?_)
    have C₁ := C.next E₁ rd₁ wr₁ (updF f₁)
    refine WP.seq (WP.mono (ctrStep_ok v C₁.lay C₁.env C₁.rounds C₁.ctx C₁.ro C₁.buf
      C₁.pw C₁.pk C₁.q C₁.k) fun u₂ ⟨E₂, rd₂, wr₂, f₂, o₂, n₂⟩ => hQ u₂ ?_)
    replace o₂ := o₂ nonce C.h7 C.h13 j C.hj C.hj32 ((cnt_upd f₁).trans hc)
    refine ⟨E₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], (updF f₁).trans (ctrF f₂), ?_, ?_, by rw [n₂, cnt_upd f₁]⟩
    · rw [o₂, ctxCiph_frame (updF (P := P) (k := k) f₁) (chR_k C.lay C.hy C.pk) hRb,
        Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact dP (by omega_arith)
          · exact dP (by decide)
          · exact C.buf.stk.symm) (by omega_arith)]
    · rw [Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact Lay.w_w (by omega_arith) (by omega_arith) (by decide)
          · exact (dP (by omega_arith)).symm
          · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
          · exact (C.lay.stk_w' (by omega_arith)).symm) (by decide), o₁]
      rfl

/-- The blocks of the chunk `pick` chooses of the `m` left. -/
def pickLen (c : Impl.Aes.X86.Ctr32) (m : Nat) : Nat :=
  if Impl.CmacAes.X86.hardware c then if m < 6 then m else 6 else m

theorem pickLen_pos (c : Impl.Aes.X86.Ctr32) {m : Nat} (h : 0 < m) : 0 < pickLen c m := by
  unfold pickLen; split
  · split <;> omega_arith
  · exact h

theorem pickLen_le (c : Impl.Aes.X86.Ctr32) (m : Nat) : pickLen c m ≤ m := by
  unfold pickLen; split
  · split <;> omega_arith
  · exact Nat.le_refl _

theorem pick_ok (c : Impl.Aes.X86.Ctr32) {K W SP : BitVec 32} {u : State} (L : Lay K W SP) (E : Env K W SP u) {m : Nat}
    (hm : slotv u.mem W mO = BitVec.ofNat 32 m) (hm32 : m < 2 ^ 32) :
    WP isa (pick c) u fun u' => u'.gpr .esi = BitVec.ofNat 32 (pickLen c m) ∧ u'.gpr .ebp = W ∧ u'.gpr .esp = SP ∧
      u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  unfold pick pickLen
  by_cases h : Impl.CmacAes.X86.hardware c = true
  · rw [ite_eq_left h, ite_eq_left h]
    obtain ⟨u₁, run₁, si₁, cf₁, bp₁, sp₁, m₁, rd₁, wr₁⟩ : ∃ u₁, runBlock isa
        [.mov .esi (slot mO), .alu .cmp .esi (imm 6)] u = some u₁ ∧ u₁.gpr .esi = BitVec.ofNat 32 m ∧
        u₁.cf = some (decide (m < 6)) ∧ u₁.gpr .ebp = W ∧ u₁.gpr .esp = SP ∧ u₁.mem = u.mem ∧ u₁.rd = u.rd ∧
        u₁.wr = u.wr := by
      refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hm], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · cregs [hm]
      · cmems [hm, toNat_ofNat32 hm32, toNat_ofNat32 (show 6 < 2 ^ 32 by decide)]
      · cregs [E.ebp]
      · cregs [E.esp]
      all_goals cmems []
    refine WP.seq (WP.of_runBlock ⟨u₁, run₁, ?_⟩)
    refine WP.ite (decide (m < 6)) (eval_b cf₁) (fun hb => ?_) (fun hb => ?_)
    · rw [ite_eq_left (of_decide_eq_true hb)]
      exact WP.block_nil ⟨si₁, bp₁, sp₁, m₁, rd₁, wr₁⟩
    · rw [ite_eq_right (of_decide_eq_false hb)]
      refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · cregs []
      · cregs [bp₁]
      · cregs [sp₁]
      · cmems [m₁]
      · cmems [rd₁]
      · cmems [wr₁]
  · rw [ite_eq_right h, ite_eq_right h]
    refine WP.of_runBlock ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hm], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cregs [hm]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []

/-- `advance`: the rest of the data, and ZF set if no block is left. -/
theorem advance_ok {K W SP : BitVec 32} {u : State} (L : Lay K W SP) (E : Env K W SP u) {D : BitVec 32} {q k m : Nat}
    (hk : slotv u.mem W kO = BitVec.ofNat 32 k)
    (hq : slotv u.mem W qO = D + BitVec.ofNat 32 (16 * q)) (hm : slotv u.mem W mO = BitVec.ofNat 32 (m - q))
    (hkm : k ≤ m - q) (hm32 : m < 2 ^ 32) :
    ∃ u', runBlock isa advance u = some u' ∧ Env K W SP u' ∧ Frame [⟨w64 W + BitVec.ofNat 64 288, 16⟩] u.mem u'.mem ∧
      slotv u'.mem W qO = D + BitVec.ofNat 32 (16 * (q + k)) ∧
      slotv u'.mem W mO = BitVec.ofNat 32 (m - (q + k)) ∧ u'.zf = some (decide (m - (q + k) = 0)) ∧ u'.rd = u.rd ∧
      u'.wr = u.wr := by
  obtain dbl : ∀ a : Nat, BitVec.ofNat 32 a + BitVec.ofNat 32 a = BitVec.ofNat 32 (2 * a) := fun a => by
    rw [← BitVec.ofNat_add]; exact congrArg _ (by omega_arith)
  obtain e₂ : BitVec.ofNat 32 (2 * (2 * (2 * (2 * k)))) + (D + BitVec.ofNat 32 (16 * q)) =
      D + BitVec.ofNat 32 (16 * (q + k)) := by
    rw [BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun a => D + BitVec.ofNat 32 a) (by omega_arith)
  obtain e₃ : BitVec.ofNat 32 (m - q) - BitVec.ofNat 32 k = BitVec.ofNat 32 (m - (q + k)) := by
    rw [Proof.AesGcm.X86.ofNat_sub32 hkm (by omega_arith)]; exact congrArg _ (by omega_arith)
  obtain ⟨u', run, mm, zf, bp, sp, rd, wr⟩ : ∃ u', runBlock isa advance u = some u' ∧
      u'.mem = (u.mem.writeW (w64 W + BitVec.ofNat 64 qO) (D + BitVec.ofNat 32 (16 * (q + k)))).writeW
        (w64 W + BitVec.ofNat 64 mO) (BitVec.ofNat 32 (m - (q + k))) ∧
      u'.zf = some (decide (m - (q + k) = 0)) ∧ u'.gpr .ebp = W ∧ u'.gpr .esp = SP ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
    refine ⟨_, by crun [advance, E.ebp, L.aW, E.perm.wR, E.perm.wW, hk, hq, hm], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hk, hq, hm, dbl, e₂, e₃]
    · cmems [hk, hq, hm]
      rw [Proof.AesGcm.X86.sub_beq32 (by omega_arith) (by omega_arith)]
      exact congrArg some (decide_eq_decide.mpr (by omega_arith))
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  refine ⟨u', run, E.keep (by rw [bp, E.ebp]) (by rw [sp, E.esp]) rd wr, ?_, ?_, ?_, zf, rd, wr⟩
  · rw [mm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 288) (n := 4) (e := 288) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 292) (n := 4) (e := 288) (k := 16) (by decide) (by decide) (by decide))
  · rw [mm, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [mm]; exact Mem.readW_writeW_self32 _ _ _

/-! ## The whole blocks -/

/-- After `q` whole blocks, at the start of a chunk. -/
structure DataLoop (K W SP : BitVec 32) (s : State) (R : Nat) (nonce : List Byte) (D : BitVec 32) (n y : Nat) (enc : Bool)
    (q : Nat) (t : State) : Prop extends DataMid K W SP s R nonce D n y enc q t where
  sq : slotv t.mem W qO = D + BitVec.ofNat 32 (16 * q)
  sm : slotv t.mem W mO = BitVec.ofNat 32 (n / 16 - q)
  cnt : cnt t.mem W = ctrInc nonce (q + 1)

/-- `W + [a, a + l)`, for parts of `[272, 304)`, is apart from another. -/
theorem mid_kept {W : BitVec 32} {d l : Nat} {m m' : Mem} (f : Frame [⟨w64 W + BitVec.ofNat 64 d, l⟩] m m') {o : Nat}
    (h : o + 4 ≤ d ∨ d + l ≤ o) (hd : d + l ≤ 2560) (ho : o + 4 ≤ 2560) : slotv m' W o = slotv m W o :=
  f.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w h ho hd) (by decide)

/-- The counter block, after a write elsewhere in `W`. -/
theorem cnt_kept {W : BitVec 32} {m m' : Mem} (f : Frame [⟨w64 W + BitVec.ofNat 64 288, 16⟩] m m') :
    cnt m' W = cnt m W :=
  congrArg Spec.Gcm.ofBytes (Proof.AesGcm.X86.bytesAt_frame f (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide))

/-- A state whose memory differs in the counter block and `[288, 304)` only. -/
theorem DataMid.mid {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {n y q : Nat}
    {enc : Bool} (C : CtrCtx K W SP s R nonce D n y) {t t' : State} (I : DataMid K W SP s R nonce D n y enc q t)
    (hq : 16 * q ≤ n) (E : Env K W SP t') (rd : t'.rd = t.rd) (wr : t'.wr = t.wr)
    (f : Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 288, 16⟩] t.mem t'.mem) :
    DataMid K W SP s R nonce D n y enc q t' := by
  have hy := C.hy
  have hn32 := C.hn32
  have sl : ∀ o, 112 ≤ o → o + 4 ≤ 288 → slotv t'.mem W o = slotv t.mem W o := fun o h₁ h₂ =>
    f.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
      · exact Lay.w_w (.inl h₂) (by omega_arith) (by decide)) (by decide)
  have dd : ∀ a l, a + l ≤ n → bytesAt t'.mem (w64 D + BitVec.ofNat 64 a) l =
      bytesAt t.mem (w64 D + BitVec.ofNat 64 a) l := fun a l h =>
    Proof.AesGcm.X86.bytesAt_frame f (fun r hr => by
      obtain sA : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base (w64 D) h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
      · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))) (by omega_arith)
  exact
    { env := E
      rd := rd.trans I.rd
      wr := wr.trans I.wr
      frame := I.frame.trans (f.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩)
      dO := by rw [sl _ (by decide) (by decide)]; exact I.dO
      nO := by rw [sl _ (by decide) (by decide)]; exact I.nO
      done := by
        have h := dd 0 (16 * q) (by omega_arith)
        rw [BitVec.add_zero] at h
        rw [h, I.done]
      rest := by rw [dd _ _ (by omega_arith), I.rest]
      mac := by
        rw [Proof.AesGcm.X86.bytesAt_frame f (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Lay.w_w (by omega_arith) (by omega_arith) (by decide)
          · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide), I.mac] }

/-- The plaintext of more bytes. -/
theorem ptOf_add {K : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {enc : Bool} (q l : Nat) :
    ptOf K s R nonce D enc (16 * q + l) = ptOf K s R nonce D enc (16 * q) ++
      (if enc then bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * q)) l
        else xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce (q + 1)
          (bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * q)) l)) := by
  cases enc
  · simp only [ptOf, Bool.false_eq_true, ↓reduceIte]
    rw [Proof.Cmac.Stream.bytesAt_append, Proof.AesCcm.xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 q]
  · simp only [ptOf, ↓reduceIte]
    rw [Proof.Cmac.Stream.bytesAt_append]

theorem length_ptOf {K : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {enc : Bool} (k : Nat) :
    (ptOf K s R nonce D enc k).length = k := by
  cases enc
  · simp only [ptOf, Bool.false_eq_true, ↓reduceIte]
    rw [Proof.AesCcm.length_xorFrom, length_bytesAt]
  · simp only [ptOf, ↓reduceIte]
    rw [length_bytesAt]

theorem ptOf_mod {K : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {enc : Bool} (q : Nat) :
    (ptOf K s R nonce D enc (16 * q)).length % 16 = 0 := by rw [length_ptOf, Nat.mul_mod_right]

/-- `kO` written, and what the chunk's calls need. -/
theorem chunkPre_ok {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n y : Nat} {enc : Bool} (C : CtrCtx K W SP s R nonce D n y) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) {q k : Nat} {t : State}
    (I : DataLoop K W SP s R nonce D n y enc q t) (hk0 : 0 < k) (hk : q + k ≤ n / 16) {u : State}
    (hsi : u.gpr .esi = BitVec.ofNat 32 k) (hbp : u.gpr .ebp = W) (hsp : u.gpr .esp = SP) (hm : u.mem = t.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) :
    ∃ u', runBlock isa [.store (at_ .ebp kO) .esi] u = some u' ∧
      ChunkPre K W SP u' R nonce (D + BitVec.ofNat 32 (16 * q)) k (q + 1) y ∧
      DataLoop K W SP s R nonce D n y enc q u' := by
  have L := C.lay
  have hn := C.hn
  have hn32 := C.hn32
  have Eu : Env K W SP u := I.env.keep (by rw [hbp, I.env.ebp]) (by rw [hsp, I.env.esp]) hrd hwr
  obtain ⟨u', run, mm, bp, sp, rd, wr⟩ : ∃ u', runBlock isa [.store (at_ .ebp kO) .esi] u = some u' ∧
      u'.mem = u.mem.writeW (w64 W + BitVec.ofNat 64 kO) (BitVec.ofNat 32 k) ∧ u'.gpr .ebp = W ∧ u'.gpr .esp = SP ∧
      u'.rd = u.rd ∧ u'.wr = u.wr := by
    refine ⟨_, by crun [hbp, L.aW, Eu.perm.wW], ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hsi]
    · cregs [hbp]
    · cregs [hsp]
    all_goals cmems []
  obtain f : Frame [⟨w64 W + BitVec.ofNat 64 296, 4⟩] t.mem u'.mem := by
    rw [mm, hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain f288 : Frame [⟨w64 W + BitVec.ofNat 64 288, 16⟩] t.mem u'.mem := f.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  obtain E' : Env K W SP u' := Eu.keep (by rw [bp, hbp]) (by rw [sp, hsp]) rd wr
  obtain rd' : u'.rd = t.rd := rd.trans hrd
  obtain wr' : u'.wr = t.wr := wr.trans hwr
  obtain M : DataMid K W SP s R nonce D n y enc q u' := I.toDataMid.mid C (by omega_arith) E' rd' wr' (f288.mono (by simp))
  obtain hq : slotv u'.mem W qO = D + BitVec.ofNat 32 (16 * q) := by
    rw [mid_kept f (.inl (by decide)) (by decide) (by decide)]; exact I.sq
  obtain hw : D.toNat + 16 * q < 2 ^ 32 := by have := C.buf.wrap; omega_arith
  obtain pQ : w64 (D + BitVec.ofNat 32 (16 * q)) = w64 D + BitVec.ofNat 64 (16 * q) := Buf.ptr hw
  obtain sQ : Region.Sub ⟨w64 (D + BitVec.ofNat 32 (16 * q)), 16 * k⟩ ⟨w64 D, n⟩ := by
    rw [pQ]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨u', run, ?_, { toDataMid := M, sq := hq, sm := ?_, cnt := (cnt_kept f288).trans I.cnt }⟩
  · exact
      { lay := L
        env := E'
        rounds := C.rounds
        hy := C.hy
        ctx := by rw [C.slot_kept M.frame (by decide) (by decide)]; exact hK
        ro := by rw [C.slot_kept M.frame (by decide) (by decide)]; exact hRo
        h7 := C.h7
        h13 := C.h13
        k0 := hk0
        hj := by omega_arith
        k32 := by omega_arith
        hj32 := by omega_arith
        buf := ((C.buf.drop (k := 16 * q) (by omega_arith) hw).take (by omega_arith)).of_eq M.rd M.wr
        pw := by
          rw [M.wr, pQ]; exact covers_off C.dw (by omega_arith) (by have := C.buf.lt; omega_arith)
        pk := C.dk.sub_right sQ
        q := hq
        k := by rw [mm]; exact Mem.readW_writeW_self32 _ _ _ }
  · rw [mid_kept f (.inl (by decide)) (by decide) (by decide)]; exact I.sm

/-- A chunk. -/
theorem chunk_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n y : Nat} {enc : Bool} (C : CtrCtx K W SP s R nonce D n y) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) {q : Nat} (hq : q < n / 16) {t : State}
    (I : DataLoop K W SP s R nonce D n y enc q t) :
    WP isa (chunk v.callee v.suffix enc y) t fun t' =>
      DataLoop K W SP s R nonce D n y enc (q + pickLen v.callee (n / 16 - q)) t' ∧
      t'.zf = some (decide (n / 16 - (q + pickLen v.callee (n / 16 - q)) = 0)) := by
  have L := C.lay
  have hn := C.hn
  have hn32 := C.hn32
  have hy := C.hy
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases C.rounds with h | h | h <;> subst h <;> decide
  refine WP.seq (WP.mono (pick_ok v.callee L I.env I.sm (by omega_arith)) fun u ⟨si, bp, sp, mu, rdu, wru⟩ => ?_)
  have hk0 := pickLen_pos v.callee (m := n / 16 - q) (by omega_arith)
  have hkm := pickLen_le v.callee (n / 16 - q)
  generalize pickLen v.callee (n / 16 - q) = k at si hk0 hkm ⊢
  obtain ⟨u₁, run₁, P₁, I₁⟩ := chunkPre_ok C hK hRo I hk0 (by omega_arith) si bp sp mu rdu wru
  refine WP.seq (WP.of_runBlock ⟨u₁, run₁, ?_⟩)
  refine chunkCalls_ok v P₁ I₁.cnt enc fun u₂ O => ?_
  obtain sl : ∀ o, 112 ≤ o → o + 4 ≤ 384 → slotv u₂.mem W o = slotv u₁.mem W o := fun o h₁ h₂ =>
    O.frame.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _)
      (chR_w L hy P₁.buf (.inr ⟨h₁, h₂⟩)) (by decide)
  obtain ⟨u₃, run₃, E₃, f₃, q₃, m₃, zf₃, rd₃, wr₃⟩ := advance_ok L O.env (D := D) (q := q) (k := k) (m := n / 16)
    (by rw [sl _ (by decide) (by decide)]; exact P₁.k)
    (by rw [sl _ (by decide) (by decide)]; exact I₁.sq) (by rw [sl _ (by decide) (by decide)]; exact I₁.sm)
    hkm (by omega_arith)
  refine WP.of_runBlock ⟨u₃, run₃, ?_, zf₃⟩
  obtain hw : D.toNat + 16 * q < 2 ^ 32 := by have := C.buf.wrap; omega_arith
  obtain pQ : w64 (D + BitVec.ofNat 32 (16 * q)) = w64 D + BitVec.ofNat 64 (16 * q) := Buf.ptr hw
  -- What the calls keep of the data.
  obtain dD : ∀ {a l : Nat}, a + l ≤ n → (a + l ≤ 16 * q ∨ 16 * (q + k) ≤ a) →
      bytesAt u₂.mem (w64 D + BitVec.ofNat 64 a) l = bytesAt u₁.mem (w64 D + BitVec.ofNat 64 a) l := fun {a l} h h' =>
    Proof.AesGcm.X86.bytesAt_frame O.frame (fun r hr => by
      obtain sA : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base (w64 D) h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
      · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by omega_arith))
      · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
      · exact (C.buf.stk.sub_right sA).symm
      · rw [pQ]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
  obtain ci : Spec.Ccm.ctxCiph u₁.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R := C.ciph_kept I₁.frame
  -- The chunk's blocks before it.
  obtain cB : bytesAt u₁.mem (w64 D + BitVec.ofNat 64 (16 * q)) (16 * k) =
      bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * q)) (16 * k) := by
    rw [Proof.AesCcm.bytesAt_prefix _ _ (show 16 * k ≤ n - 16 * q by omega_arith), I₁.rest,
      ← Proof.AesCcm.bytesAt_prefix _ _ (show 16 * k ≤ n - 16 * q by omega_arith)]
  have o := O.out
  have om := O.mac
  rw [pQ, ci, cB] at o om
  obtain fO : Frame (ctrR W SP D n y) u₁.mem u₂.mem := O.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨w64 D, n⟩, by simp, by rw [pQ]; exact Offset.sub_base _ (by omega_arith)⟩
  obtain M₂ : DataMid K W SP s R nonce D n y enc (q + k) u₂ :=
    { env := O.env
      rd := O.rd.trans I₁.rd
      wr := O.wr.trans I₁.wr
      frame := I₁.frame.trans fO
      dO := by rw [sl _ (by decide) (by decide)]; exact I₁.dO
      nO := by rw [sl _ (by decide) (by decide)]; exact I₁.nO
      done := by
        rw [Nat.mul_add, Proof.Cmac.Stream.bytesAt_append, Proof.Cmac.Stream.bytesAt_append, o,
          Proof.AesCcm.xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 q]
        have h := dD (a := 0) (l := 16 * q) (by omega_arith) (.inl (by omega_arith))
        rw [BitVec.add_zero] at h
        rw [h, I₁.done]
      rest := by
        rw [dD (by omega_arith) (.inr (Nat.le_refl _))]
        have e : ∀ m : Mem, bytesAt m (w64 D + BitVec.ofNat 64 (16 * (q + k))) (n - 16 * (q + k)) =
            (bytesAt m (w64 D + BitVec.ofNat 64 (16 * q)) (n - 16 * q)).drop (16 * k) := fun m => by
          rw [← Proof.AesCcm.bytesAt_suffix _ _ (show 16 * k ≤ n - 16 * q by omega_arith), add_ofNat_assoc,
            ← Nat.mul_add, show n - 16 * (q + k) = n - 16 * q - 16 * k by omega_arith]
        rw [e, e, I₁.rest]
      mac := by
        rw [om, I₁.mac, ← Proof.Cmac.chain_append, Nat.mul_add, ptOf_add,
          Proof.Cmac.Stream.blocks_append (ptOf_mod q)] }
  exact
    { toDataMid := M₂.mid C (by omega_arith) E₃ rd₃ wr₃ (f₃.mono (by simp)), sq := q₃, sm := m₃,
      cnt := by rw [cnt_kept f₃, O.cnt, I₁.cnt, ← Proof.Gcm.repeat_add, show k + (q + 1) = q + k + 1 by omega_arith] }

/-- The data and its length into `dO` and `nO`, and split. -/
theorem ctrSplit_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {D : BitVec 32} {n : Nat}
    (hDp : slotv s.mem W dataO = D) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) :
    ∃ s₁, runBlock isa (([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp nO) .eax] : List Instr) ++ splitWhole) s = some s₁ ∧
      s₁.gpr .ebx = D ∧ s₁.gpr .edi = BitVec.ofNat 32 (n / 16) ∧ s₁.zf = some (decide (n / 16 = 0)) ∧
      Env K W SP s₁ ∧ Frame [wC W] s.mem s₁.mem ∧ slotv s₁.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
      slotv s₁.mem W nO = BitVec.ofNat 32 (n % 16) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  obtain ⟨sa, runa, hma, hbpa, hspa, hrda, hwra⟩ : ∃ sa, runBlock isa
      [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO), .store (at_ .ebp nO) .eax] s =
        some sa ∧
      sa.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 dO) D).writeW (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 n) ∧
      sa.gpr .ebp = W ∧ sa.gpr .esp = SP ∧ sa.rd = s.rd ∧ sa.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hDp, hlen], ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hDp, hlen]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  obtain Ea : Env K W SP sa := E.keep (by rw [hbpa, E.ebp]) (by rw [hspa, E.esp]) hrda hwra
  obtain hda : slotv sa.mem W dO = D := by
    rw [hma, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  obtain hna : slotv sa.mem W nO = BitVec.ofNat 32 n := by rw [hma]; exact Mem.readW_writeW_self32 _ _ _
  obtain ⟨s₁, run₁, hbx, hdi, hzf, hbp, hsp, hm₁, hrd₁, hwr₁⟩ := split_ok L Ea hda hna hn32
  obtain cw : ∀ d, 240 ≤ d → d + 4 ≤ 2560 → (wC W).Contains (w64 W + BitVec.ofNat 64 d) 4 := fun d h₁ h₂ =>
    Offset.contains (w64 W) h₁ (by omega_arith) (by decide)
  refine ⟨s₁, runBlock_app_of runa run₁, hbx, hdi, hzf, Ea.keep (by rw [hbp, hbpa]) (by rw [hsp, hspa]) hrd₁ hwr₁,
    ?_, ?_, ?_, by rw [hrd₁, hrda], by rw [hwr₁, hwra]⟩
  · rw [hm₁, hma]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cw 272 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cw 276 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cw 276 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cw 272 (by decide) (by decide))
  · rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _
  · rw [hm₁, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _

/-- After the split, no block done. -/
theorem dataMid0 {K W SP : BitVec 32} {s s₁ : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n y : Nat} {enc : Bool} (C : CtrCtx K W SP s R nonce D n y) (E₁ : Env K W SP s₁) (f₁ : Frame [wC W] s.mem s₁.mem)
    (hd₁ : slotv s₁.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16))) (hn₁ : slotv s₁.mem W nO = BitVec.ofNat 32 (n % 16))
    (hrd₁ : s₁.rd = s.rd) (hwr₁ : s₁.wr = s.wr) : DataMid K W SP s R nonce D n y enc 0 s₁ := by
  have hn32 := C.hn32
  obtain fr₁ : Frame (ctrR W SP D n y) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wC W, by simp, fun _ h => h⟩
  have hy := C.hy
  obtain I₁ : DataMid K W SP s R nonce D n y enc 0 s₁ :=
    { env := E₁
      rd := hrd₁
      wr := hwr₁
      frame := fr₁
      dO := hd₁
      nO := hn₁
      done := rfl
      rest := Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (C.buf.w.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Lay.wSub (by decide))) (by omega_arith)
      mac := by
        rw [Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide)]
        rw [List.eq_nil_of_length_eq_zero (length_ptOf (16 * 0))]; rfl }
  exact I₁

/-- The slots of the first chunk. -/
theorem loopStart_ok {K W SP : BitVec 32} {s s₁ : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n y : Nat} {enc : Bool} (C : CtrCtx K W SP s R nonce D n y) (E₁ : Env K W SP s₁) (f₁ : Frame [wC W] s.mem s₁.mem)
    (hd₁ : slotv s₁.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16))) (hn₁ : slotv s₁.mem W nO = BitVec.ofNat 32 (n % 16))
    (hrd₁ : s₁.rd = s.rd) (hwr₁ : s₁.wr = s.wr) (hbx : s₁.gpr .ebx = D) (hdi : s₁.gpr .edi = BitVec.ofNat 32 (n / 16)) :
    ∃ s₂, runBlock isa (([.store (at_ .ebp qO) .ebx, .store (at_ .ebp mO) .edi, .mov .eax (imm 1)] : List Instr) ++ ctrAt)
      s₁ = some s₂ ∧ DataLoop K W SP s R nonce D n y enc 0 s₂ := by
  have L := C.lay
  have h13 := C.h13
  have I₁ := dataMid0 (enc := enc) C E₁ f₁ hd₁ hn₁ hrd₁ hwr₁
  obtain ⟨sa, runa, ma, ax, bpa, spa, rda, wra⟩ : ∃ sa, runBlock isa [.store (at_ .ebp qO) .ebx, .store (at_ .ebp mO) .edi,
      .mov .eax (imm 1)] s₁ = some sa ∧
      sa.mem = (s₁.mem.writeW (w64 W + BitVec.ofNat 64 qO) D).writeW (w64 W + BitVec.ofNat 64 mO)
        (BitVec.ofNat 32 (n / 16)) ∧ sa.gpr .eax = BitVec.ofNat 32 1 ∧
      sa.gpr .ebp = W ∧ sa.gpr .esp = SP ∧ sa.rd = s₁.rd ∧ sa.wr = s₁.wr := by
    refine ⟨_, by crun [E₁.ebp, L.aW, E₁.perm.wW], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hbx, hdi]
    · cregs []
    · cregs [E₁.ebp]
    · cregs [E₁.esp]
    all_goals cmems []
  obtain fa : Frame [⟨w64 W + BitVec.ofNat 64 288, 16⟩] s₁.mem sa.mem := by
    rw [ma]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 288) (n := 4) (e := 288) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 292) (n := 4) (e := 288) (k := 16) (by decide) (by decide) (by decide))
  obtain Ea : Env K W SP sa := E₁.keep (by rw [bpa, E₁.ebp]) (by rw [spa, E₁.esp]) rda wra
  have Ia := I₁.mid C (by omega_arith) Ea rda wra (fa.mono (by simp))
  obtain h1 : 1 < 256 ^ (15 - nonce.length) :=
    Nat.lt_of_lt_of_le (by decide : 1 < 256 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega_arith))
  obtain ⟨s₂, run₂, f₂, c₂, g₂, rd₂, wr₂⟩ := ctrAt_ok L Ea C.h7 C.h13 (C.c0_kept Ia.frame) h1 (by decide) ax
  obtain E₂ : Env K W SP s₂ := Ea.keep (g₂ _ (by decide) (by decide)) (g₂ _ (by decide) (by decide)) rd₂ wr₂
  obtain sl : ∀ o, 112 ≤ o → o + 4 ≤ 384 → slotv s₂.mem W o = slotv sa.mem W o := fun o h₁ h₂ =>
    mid_kept f₂ (.inr (by omega_arith)) (by decide) (by omega_arith)
  refine ⟨s₂, runBlock_app_of runa run₂,
    { toDataMid := Ia.mid C (by omega_arith) E₂ rd₂ wr₂ (f₂.mono (by simp))
      sq := ?_
      sm := ?_
      cnt := ?_ }⟩
  · rw [sl _ (by decide) (by decide), ma, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact (Mem.readW_writeW_self32 _ _ _).trans (BitVec.add_zero _).symm
  · rw [sl _ (by decide) (by decide), ma]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [ctrInc_eq C.h7 C.h13 h1 (by decide)]
    exact congrArg Spec.Gcm.ofBytes c₂

/-- The whole blocks of the data. -/
theorem dataWhole_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n y : Nat} {enc : Bool} (C : CtrCtx K W SP s R nonce D n y) (E : Env K W SP s) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hDp : slotv s.mem W dataO = D)
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) :
    WP isa (dataWhole v.callee v.suffix enc y) s (DataMid K W SP s R nonce D n y enc (n / 16)) := by
  have L := C.lay
  have hn32 := C.hn32
  obtain ⟨s₁, run₁, hbx, hdi, hzf, E₁, f₁, hd₁, hn₁, hrd₁, hwr₁⟩ := ctrSplit_ok L E hDp hlen C.hn32
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have I₁ := dataMid0 (enc := enc) C E₁ f₁ hd₁ hn₁ hrd₁ hwr₁
  refine WP.ite (decide (n / 16 = 0)) (eval_e hzf) (fun ht => WP.block_nil ?_) (fun hf => ?_)
  · rw [of_decide_eq_true ht]; exact I₁
  have h0 : n / 16 ≠ 0 := of_decide_eq_false hf
  obtain ⟨s₂, run₂, I₂⟩ := loopStart_ok (enc := enc) C E₁ f₁ hd₁ hn₁ hrd₁ hwr₁ hbx hdi
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ q, k = n / 16 - q ∧ q < n / 16 ∧ DataLoop K W SP s R nonce D n y enc q u) ?_
    (n / 16 - 0) _ ⟨0, rfl, by omega_arith, I₂⟩
  rintro k u ⟨q, rfl, hq, I⟩
  refine WP.mono (chunk_ok v C hK hRo hq I) fun u' ⟨I', zf'⟩ => ?_
  have hk0 := pickLen_pos v.callee (m := n / 16 - q) (by omega_arith)
  have hkm := pickLen_le v.callee (n / 16 - q)
  generalize pickLen v.callee (n / 16 - q) = k at I' zf' hk0 hkm
  by_cases he : n / 16 - (q + k) = 0
  · left
    obtain e : q + k = n / 16 := by omega_arith
    rw [e] at I'
    exact ⟨by show u'.zf.map _ = _; rw [zf']; simp [he], I'.toDataMid⟩
  · exact .inr ⟨by show u'.zf.map _ = _; rw [zf']; simp [he], n / 16 - (q + k), by omega_arith, q + k, rfl,
      by omega_arith, I'⟩

/-! ## The last bytes -/

/-- `Ctrⱼ`, `j = ⌊n / 16⌋ + 1`, at `W + 64`, the keystream block at `W + 80`
zeroed, and the arguments of `vg_aes_ctr32_to` to encrypt it. -/
theorem ctrTailArgs_ok {K W SP : BitVec 32} {t₀ : State} (L : Lay K W SP) (E₀ : Env K W SP t₀) {R : Nat}
    (hK₀ : slotv t₀.mem W ctxO = K) (hR₀ : slotv t₀.mem W roundsO = BitVec.ofNat 32 R) {n : Nat}
    (hl₀ : slotv t₀.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt t₀.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (hj : n / 16 + 1 < 256 ^ (15 - nonce.length)) :
    ∃ tc, runBlock isa (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++ zero4 ksO ++
        keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)) t₀ = some tc ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩] t₀.mem tc.mem ∧
      bytesAt tc.mem (w64 W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (n / 16 + 1) ∧
      bytesAt tc.mem (w64 W + BitVec.ofNat 64 80) 16 = Spec.Gcm.zeros 16 ∧
      tc.gpr .eax = K ∧ tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
      tc.gpr .esp = SP ∧ tc.rd = t₀.rd ∧ tc.wr = t₀.wr := by
  have hbp₀ := E₀.ebp
  have hsp₀ := E₀.esp
  obtain ⟨ta, runa, hma, haxa, hbpa, hspa, hrda, hwra⟩ : ∃ ta, runBlock isa
      [.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] t₀ = some ta ∧ ta.mem = t₀.mem ∧
      ta.gpr .eax = BitVec.ofNat 32 (n / 16 + 1) ∧ ta.gpr .ebp = W ∧ ta.gpr .esp = SP ∧ ta.rd = t₀.rd ∧
      ta.wr = t₀.wr := by
    refine ⟨_, by crun [hbp₀, L.aW, E₀.perm.wR, hl₀], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hl₀, shr4 hn32]; exact (BitVec.ofNat_add _ _).symm
    · cregs [hbp₀]
    · cregs [hsp₀]
    all_goals cmems []
  obtain Ea : Env K W SP ta := E₀.keep (by rw [hbpa, hbp₀]) (by rw [hspa, hsp₀]) hrda hwra
  obtain ⟨tb, runb, fb, hcb, hgb, hrdb, hwrb⟩ := ctrAt_ok L Ea h7 h13 (by rw [hma]; exact hc0) hj (by omega_arith) haxa
  obtain hbpb : tb.gpr .ebp = W := by rw [hgb .ebp (by decide) (by decide), hbpa]
  obtain hspb : tb.gpr .esp = SP := by rw [hgb .esp (by decide) (by decide), hspa]
  obtain Eb : Env K W SP tb := Ea.keep (by rw [hbpb, hbpa]) (by rw [hspb, hspa]) hrdb hwrb
  obtain kb : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv tb.mem W o = slotv t₀.mem W o := fun o h₁ h₂ => by
    show tb.mem.readW (w64 W + BitVec.ofNat 64 o) 32 = _
    rw [fb.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide))
      (by decide), hma]
  obtain hKb : slotv tb.mem W ctxO = K := by rw [kb _ (by decide) (by decide)]; exact hK₀
  obtain hRb' : slotv tb.mem W roundsO = BitVec.ofNat 32 R := by rw [kb _ (by decide) (by decide)]; exact hR₀
  obtain hz := zero4_fold tb.mem W 80
  simp only [Nat.reduceAdd] at hz
  obtain ⟨tc, runc, hmc, hax, hcx, hdx, hbx, hdi, hbpc, hspc, hrdc, hwrc⟩ : ∃ tc, runBlock isa
      (zero4 ksO ++ (keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr))) tb =
        some tc ∧ tc.mem = Cmac.zero4 tb.mem (w64 W + BitVec.ofNat 64 80) ∧ tc.gpr .eax = K ∧
      tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
      tc.gpr .esp = SP ∧ tc.rd = tb.rd ∧ tc.wr = tb.wr := by
    refine ⟨_, by crun [zero4, keyArgs, hbpb, L.aW, Eb.perm.wW, Eb.perm.wR, hKb, hRb'], ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · cmems [hz]
    · cregs [hKb]
    · cregs [hRb']
    · cregs [hbpb]
    · cregs [hbpb]
    · cregs []
    · cregs [hbpb]
    · cregs [hspb]
    all_goals cmems []
  obtain fz : Frame [⟨w64 W + BitVec.ofNat 64 80, 16⟩] tb.mem tc.mem := by rw [hmc]; exact Cmac.frame_store4 _ _ _ _ _
  refine ⟨tc, by
      simp only [List.append_assoc]
      exact runBlock_app_of runa (runBlock_app_of runb runc), ?_, ?_, by rw [hmc, zero4_bytes'],
    hax, hcx, hdx, hbx, hdi, hbpc, hspc, by rw [hrdc, hrdb, hrda], by rw [hwrc, hwrb, hwra]⟩
  · rw [← hma]
    exact (fb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩).trans
      (fz.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩)
  · rw [Proof.AesGcm.X86.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), hcb]

/-- The arguments of the XOR of the last bytes with the keystream block. -/
theorem xorArgs_ok {K W SP : BitVec 32} {td : State} (L : Lay K W SP) (Ed : Env K W SP td) {P : BitVec 32} {t : Nat}
    (hdd : slotv td.mem W dO = P) (hnd : slotv td.mem W nO = BitVec.ofNat 32 t) :
    ∃ te, runBlock isa
      [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)] td = some te ∧
      te.mem = td.mem ∧ te.gpr .edi = P ∧ te.gpr .edx = W + BitVec.ofNat 32 80 ∧
      te.gpr .ecx = BitVec.ofNat 32 t ∧ te.gpr .ebp = W ∧ te.gpr .esp = SP ∧ te.rd = td.rd ∧ te.wr = td.wr := by
  have hbpd := Ed.ebp
  refine ⟨_, by crun [hbpd, L.aW, Ed.perm.wR, hdd, hnd], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hdd]
  · cregs [hbpd]
  · cregs [hnd]
  · cregs [hbpd]
  · cregs [Ed.esp]
  all_goals cmems []

/-- The last `n mod 16` bytes, with `CIPH_K(Ctr₁₊ₙ/₁₆)`, after the whole blocks. -/
theorem ctrTail_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n y : Nat} (C : CtrCtx K W SP s R nonce D n y) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) {t : State}
    (I : CtrMid K W SP s R nonce D n y (n / 16) t) :
    WP isa (ctrTail v.callee) t
      fun t' => Env K W SP t' ∧ t'.rd = s.rd ∧ t'.wr = s.wr ∧ Frame (ctrR W SP D n y) s.mem t'.mem ∧
        bytesAt t'.mem (w64 D) n = xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) n) ∧
        Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 60, ⟨w64 D, n⟩]
          t.mem t'.mem := by
  have L := C.lay
  have E := I.env
  have hn32 := C.hn32
  obtain hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  obtain hrest := I.rest
  rw [show n - 16 * (n / 16) = n % 16 by omega_arith] at hrest
  obtain k₀ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv t.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    C.slot_kept I.frame h₁ h₂
  obtain ⟨t₀, run₀, hm₀, hzf, hbp₀, hsp₀, hrd₀, hwr₀⟩ := testN_ok L E (r := n % 16) (by omega_arith) I.nO
  refine WP.seq (WP.of_runBlock ⟨t₀, run₀, ?_⟩)
  obtain E₀ : Env K W SP t₀ := E.keep (by rw [hbp₀, E.ebp]) (by rw [hsp₀, E.esp]) hrd₀ hwr₀
  refine WP.ite (decide (n % 16 = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨t₀, rfl, E₀, by rw [hrd₀, I.rd], by rw [hwr₀, I.wr], by rw [hm₀]; exact I.frame, ?_,
      by rw [hm₀]; exact Frame.refl _ _⟩
    have hd := I.done
    rw [show 16 * (n / 16) = n by omega_arith] at hd
    rw [hm₀, hd]
  · have h0 : n % 16 ≠ 0 := of_decide_eq_false hf
    obtain hj : n / 16 + 1 < 256 ^ (15 - nonce.length) := by have := C.hn; omega_arith
    obtain ⟨tc, runc, ft, hcc, hz80, hax, hcx, hdx, hbx, hdi, hbpc, hspc, hrdc, hwrc⟩ :=
      ctrTailArgs_ok L E₀ (by rw [hm₀, k₀ _ (by decide) (by decide)]; exact hK)
        (by rw [hm₀, k₀ _ (by decide) (by decide)]; exact hRo) (by rw [hm₀, k₀ _ (by decide) (by decide)]; exact hlen)
        hn32 C.h7 C.h13 (by rw [hm₀]; exact C.c0_kept I.frame) hj
    refine WP.seq (WP.of_runBlock ⟨tc, runc, ?_⟩)
    obtain Ec : Env K W SP tc := E₀.keep (by rw [hbpc, hbp₀]) (by rw [hspc, hsp₀]) hrdc hwrc
    -- The keystream block.
    obtain hq := srcW (s := tc) L Ec.perm (t := 80) (k := 16 * 1) (by decide)
    obtain a80 : w64 (W + BitVec.ofNat 32 80) = w64 W + BitVec.ofNat 64 80 := L.aW (by decide)
    obtain hqc : (⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ := by
      rw [a80]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    obtain hqk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ := by
      rw [a80]; exact L.k_w.sub_right (Lay.wSub (by decide))
    obtain hqw : Covers [⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩] tc.wr := by rw [a80]; exact Ec.perm.wC (by decide)
    refine WP.seq (WP.mono (ctrCall_ok v L Ec C.rounds (c := 64) (by decide) hq hqc hqk hqw hax hcx hdx hbx hdi)
      fun td ⟨Ed, rdd, wrd, _, fd, od, _⟩ => ?_)
    -- What was written before the XOR.
    have fd' := fd
    rw [a80] at fd'
    obtain fbd : Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 60]
        t.mem td.mem := by
      rw [← hm₀]
      refine (ft.sub fun r hr => ?_).trans (fd'.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨below SP 60, by simp, fun _ h => h⟩
    obtain fR : Frame (ctrR W SP D n y) s.mem td.mem := I.frame.trans (fbd.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
    obtain kd : ∀ o, 96 ≤ o → o + 4 ≤ 384 → slotv td.mem W o = slotv t.mem W o := fun o h₁ h₂ =>
      fbd.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
        · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
        · exact (L.stk_w' (by omega_arith)).symm) (by decide)
    have hbpd : td.gpr .ebp = W := Ed.ebp
    -- The XOR.
    obtain ⟨te, rune, hme, hdie, hdxe, hcxe, hbpe, hspe, hrde, hwre⟩ :=
      xorArgs_ok L Ed (P := D + BitVec.ofNat 32 (16 * (n / 16))) (t := n % 16) (by rw [kd _ (by decide) (by decide)]; exact I.dO)
        (by rw [kd _ (by decide) (by decide)]; exact I.nO)
    refine WP.seq (WP.of_runBlock ⟨te, rune, ?_⟩)
    obtain rde : te.rd = s.rd := by rw [hrde, rdd, hrdc, hrd₀, I.rd]
    obtain wre : te.wr = s.wr := by rw [hwre, wrd, hwrc, hwr₀, I.wr]
    obtain hw : D.toNat + 16 * (n / 16) < 2 ^ 32 := by have := C.buf.wrap; omega_arith
    obtain pT : w64 (D + BitVec.ofNat 32 (16 * (n / 16))) = w64 D + BitVec.ofNat 64 (16 * (n / 16)) := Buf.ptr hw
    obtain sR : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ ⟨w64 D, n⟩ :=
      Offset.sub_base (w64 D) (d := 16 * (n / 16)) (n := n % 16) (k := n) (by omega_arith)
    obtain xp : XorPre te (W + BitVec.ofNat 32 80) (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) := by
      refine ⟨hdxe, hdie, hcxe, by omega_arith, by omega_arith, by rw [L.nW (by decide)]; have := L.fw; omega_arith,
        by rw [toNat_add32 hw]; have := C.buf.wrap; omega_arith, ?_, ?_, ?_⟩
      · rw [a80]; exact covers_left (Perm.wC (Ed.perm.of_eq hrde hwre) (d := 80) (n := n % 16) (by omega_arith))
      · rw [pT, wre]; exact covers_off C.dw (by omega_arith) (by have := C.buf.lt; omega_arith)
      · rw [a80, pT]; exact ((C.buf.w.sub_left sR).sub_right (Lay.wSub (d := 80) (n := n % 16) (by omega_arith))).symm
    refine WP.mono (xorLoop_ok te xp) fun tf P => ?_
    obtain ⟨xs, hxs⟩ : ∃ xs, xs = xorBytes te.mem (w64 (D + BitVec.ofNat 32 (16 * (n / 16))))
        (w64 (W + BitVec.ofNat 32 80)) (n % 16) := ⟨_, rfl⟩
    have hm₄ := P.mem
    rw [← hxs] at hm₄
    obtain hxl : xs.length = n % 16 := by simp [hxs, xorBytes, length_bytesAt]
    obtain fw : Frame [⟨w64 D, n⟩] te.mem tf.mem := by
      rw [hm₄, pT]
      exact writeBytes_frame _ _ _ (by
        rw [hxl]; exact Offset.contains_base (w64 D) (show 16 * (n / 16) + n % 16 ≤ n by omega_arith)
          (by have := C.buf.lt; omega_arith))
    refine ⟨E.keep (by rw [P.other _ (by decide) (by decide) (by decide) (by decide) (by decide), hbpe, E.ebp])
        (by rw [P.other _ (by decide) (by decide) (by decide) (by decide) (by decide), hspe, E.esp])
        (by rw [P.rd, rde, I.rd]) (by rw [P.wr, wre, I.wr]), by rw [P.rd, rde], by rw [P.wr, wre], ?_, ?_, ?_⟩
    · rw [← hme] at fR
      exact fR.trans (fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
    rotate_left
    · rw [← hme] at fbd
      exact (fbd.mono (by simp)).trans (fw.mono (by simp))
    · -- The bytes.
      obtain dD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 64, 32⟩ : Region),
          ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 60], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
        intro a l hl r hr
        obtain sA : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base (w64 D) hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
        · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
        · exact (C.buf.stk.sub_right sA).symm
      obtain h₁ : bytesAt te.mem (w64 D) (16 * (n / 16)) = bytesAt t.mem (w64 D) (16 * (n / 16)) := by
        rw [hme]
        have := Proof.AesGcm.X86.bytesAt_frame fbd (dD (a := 0) (l := 16 * (n / 16)) (by omega_arith)) (by omega_arith)
        rwa [BitVec.add_zero] at this
      obtain h₂ : bytesAt te.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
          bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
        rw [hme, Proof.AesGcm.X86.bytesAt_frame fbd (dD (by omega_arith)) (by omega_arith), hrest]
      obtain hBC : BlockCipher (Spec.Ccm.ctxCiph s.mem (w64 K) R) := fun x => Proof.Cmac.aesWith_length _ _ x
      obtain fRc : Frame (ctrR W SP D n y) s.mem tc.mem := I.frame.trans (by
        rw [← hm₀]
        exact ft.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
      obtain hks : bytesAt te.mem (w64 W + BitVec.ofNat 64 80) 16 =
          Spec.Ccm.ctxCiph s.mem (w64 K) R (Spec.Ccm.ctrBlock nonce (n / 16 + 1)) := by
        obtain hx := Proof.AesCcm.ctr32_ccm (m := tc.mem) (m' := td.mem) (K := w64 K) (C := w64 W + BitVec.ofNat 64 64)
          (D := w64 (W + BitVec.ofNat 32 80)) (R := R) (nonce := nonce) (by have := C.h13; omega_arith) (k := 1)
          (j := n / 16 + 1) (fun i hi => by
            rw [show i = 0 by omega_arith, Nat.add_zero]
            show Spec.Gcm.ofBytes _ = _
            rw [hcc]) od
        rw [Nat.mul_one, a80] at hx
        rw [hme, hx, hz80, C.ciph_kept fRc]
        exact Proof.AesCcm.xorFrom_zeros hBC _ _
      obtain ht := Proof.AesCcm.xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce (n / 16 + 1)
        (d := bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)) (by rw [length_bytesAt]; omega_arith)
      rw [length_bytesAt, hBC] at ht
      obtain ht' := ht.resolve_right (by omega_arith)
      rw [hm₄, pT, bytesAt_writeBytes_at te.mem (w64 D) xs (by rw [hxl]; omega_arith) (by have := C.buf.lt; omega_arith),
        List.drop_eq_nil_of_le (by rw [length_bytesAt, hxl]; omega_arith), List.append_nil,
        ← Proof.AesCcm.bytesAt_prefix te.mem (w64 D) hb, h₁, I.done, hxs, xorBytes, pT, a80, h₂,
        Proof.AesCcm.bytesAt_prefix te.mem (w64 W + BitVec.ofNat 64 80) (show n % 16 ≤ 16 by omega_arith), hks, ht']
      conv => rhs; rw [show n = 16 * (n / 16) + n % 16 from (Nat.div_add_mod n 16).symm]
      rw [Proof.Cmac.Stream.bytesAt_append, Proof.AesCcm.xorFrom_append _ _ _ (length_bytesAt _ _ _),
        Nat.add_comm 1 (n / 16)]

/-! ## The data -/

/-- What `data` leaves. -/
structure DataPost (K W SP : BitVec 32) (s : State) (R : Nat) (nonce : List Byte) (D : BitVec 32) (n y : Nat) (enc : Bool)
    (t : State) : Prop where
  env : Env K W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (ctrR W SP D n y) s.mem t.mem
  out : bytesAt t.mem (w64 D) n = xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) n)
  mac : bytesAt t.mem (w64 W + BitVec.ofNat 64 y) 16 =
    Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
      (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (ptOf K s R nonce D enc n)))

/-- The blocks of the plaintext, padded: the whole ones, then the last. -/
theorem blocks_ptOf {K : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {enc : Bool} (n : Nat) :
    Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (ptOf K s R nonce D enc n)) =
      Spec.Cmac.blocks 16 (ptOf K s R nonce D enc (16 * (n / 16))) ++
        (if n % 16 = 0 then [] else
          [(if enc then bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)
            else xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce (n / 16 + 1)
              (bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))) ++ Spec.Ccm.zeros (16 - n % 16)]) := by
  have e := ptOf_add (K := K) (s := s) (R := R) (nonce := nonce) (D := D) (enc := enc) (n / 16) (n % 16)
  rw [Nat.div_add_mod n 16] at e
  rw [Proof.AesCcm.blocks_pad16, length_ptOf]
  conv => lhs; rw [e]
  rw [List.take_left' (length_ptOf _), List.drop_left' (length_ptOf _)]

/-- What `absorbTail` writes, in what `data` does. -/
theorem tailR_ctr {W SP D : BitVec 32} {n y : Nat} {m m' : Mem} (f : Frame (tailR W SP y) m m') :
    Frame (ctrR W SP D n y) m m' := f.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What `absorbTail` keeps of `W`. -/
theorem tailR_slot {K W SP : BitVec 32} (L : Lay K W SP) {y : Nat} (hy : y = 0 ∨ y = 96) {m m' : Mem}
    (f : Frame (tailR W SP y) m m') {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 384) : slotv m' W o = slotv m W o :=
  f.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (by omega_arith) (by omega_arith) (by omega_arith)
    · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
    · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
    · exact (L.stk_w' (by omega_arith)).symm) (by decide)

/-- What `ctrTail` writes. -/
abbrev ctrTailR (W SP D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 64, 32⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 60, ⟨w64 D, n⟩]

/-- What `ctrTail` keeps of `W`. -/
theorem CtrCtx.tail_w {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {n y : Nat}
    (C : CtrCtx K W SP s R nonce D n y) {d l : Nat} (h : d + l ≤ 64 ∨ 96 ≤ d ∧ d + l ≤ 384) :
    ∀ r ∈ ctrTailR W SP D n, (⟨w64 W + BitVec.ofNat 64 d, l⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (C.lay.stk_w' (by omega_arith)).symm
  · exact (C.buf.w.sub_right (Lay.wSub (by omega_arith))).symm

/-- `absorbTail` keeps what the last bytes need. -/
theorem CtrMid.absorbed {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {n y : Nat}
    (C : CtrCtx K W SP s R nonce D n y) {t t' : State} {Y : List Byte} (I : CtrMid K W SP s R nonce D n y (n / 16) t)
    (A : Absorbed K W SP t y Y t') (f : Frame (tailR W SP y) t.mem t'.mem) :
    CtrMid K W SP s R nonce D n y (n / 16) t' := by
  have hy := C.hy
  have hn32 := C.hn32
  obtain hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  obtain d : ∀ {a l : Nat}, a + l ≤ n → bytesAt t'.mem (w64 D + BitVec.ofNat 64 a) l =
      bytesAt t.mem (w64 D + BitVec.ofNat 64 a) l := fun {a l} h =>
    Proof.AesGcm.X86.bytesAt_frame f (fun r hr => by
      obtain sA : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base (w64 D) h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by omega_arith))
      · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
      · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
      · exact (C.buf.stk.sub_right sA).symm) (by omega_arith)
  exact
    { env := A.env
      rd := A.rd.trans I.rd
      wr := A.wr.trans I.wr
      frame := I.frame.trans (tailR_ctr f)
      dO := by rw [tailR_slot C.lay hy f (by decide) (by decide)]; exact I.dO
      nO := by rw [tailR_slot C.lay hy f (by decide) (by decide)]; exact I.nO
      done := by
        have h := d (a := 0) (l := 16 * (n / 16)) (by omega_arith)
        rw [BitVec.add_zero] at h
        rw [h, I.done]
      rest := by rw [d (by omega_arith), I.rest] }

/-- The last bytes, as a buffer. -/
theorem CtrCtx.bufT {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {n y : Nat}
    (C : CtrCtx K W SP s R nonce D n y) {u : State} (hr : u.rd = s.rd) (hw : u.wr = s.wr) (h : 0 < n % 16) :
    Buf W SP u (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) := by
  have := (C.buf.drop (k := 16 * (n / 16)) (Nat.mul_div_le n 16) (by have := C.buf.wrap; omega_arith)).of_eq hr hw
  rwa [show n - 16 * (n / 16) = n % 16 by omega_arith] at this

/-- The data, and its plaintext chained. -/
theorem data_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n y : Nat} (enc : Bool) (C : CtrCtx K W SP s R nonce D n y) (E : Env K W SP s) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hDp : slotv s.mem W dataO = D)
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) :
    WP isa (data v.callee v.suffix enc y) s (DataPost K W SP s R nonce D n y enc) := by
  have L := C.lay
  have hy := C.hy
  have hn32 := C.hn32
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases C.rounds with h | h | h <;> subst h <;> decide
  obtain hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  refine WP.seq (WP.mono (dataWhole_ok v (enc := enc) C E hK hRo hDp hlen) fun t I => ?_)
  obtain pT : 0 < n % 16 → w64 (D + BitVec.ofNat 32 (16 * (n / 16))) = w64 D + BitVec.ofNat 64 (16 * (n / 16)) := fun h =>
    Buf.ptr (by have := C.buf.wrap; omega_arith)
  obtain dTail : ∀ {m m' : Mem}, Frame (tailR W SP y) m m' → ∀ {a l : Nat}, a + l ≤ n →
      bytesAt m' (w64 D + BitVec.ofNat 64 a) l = bytesAt m (w64 D + BitVec.ofNat 64 a) l := fun {_ _} f {a l} h =>
    Proof.AesGcm.X86.bytesAt_frame f (fun r hr => by
      obtain sA : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base (w64 D) h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by omega_arith))
      · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
      · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
      · exact (C.buf.stk.sub_right sA).symm) (by omega_arith)
  cases enc
  · -- decrypted, then chained
    rw [ite_eq_right Bool.false_ne_true]
    refine WP.seq (WP.mono (ctrTail_ok v C hK hRo hlen I.toCtrMid) fun t₁ ⟨E₁, rd₁, wr₁, f₁, o₁, g₁⟩ => ?_)
    obtain sl : ∀ o, 112 ≤ o → o + 4 ≤ 384 → slotv t₁.mem W o = slotv t.mem W o := fun o h₁ h₂ =>
      g₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (C.tail_w (.inr ⟨by omega_arith, h₂⟩))
        (by decide)
    obtain hY : bytesAt t₁.mem (w64 W + BitVec.ofNat 64 y) 16 = bytesAt t.mem (w64 W + BitVec.ofNat 64 y) 16 :=
      Proof.AesGcm.X86.bytesAt_frame g₁ (C.tail_w (by omega_arith)) (by decide)
    refine WP.mono (absorbTail_ok v L E₁ C.rounds (by rw [C.slot_kept f₁ (by decide) (by decide)]; exact hK)
      (by rw [C.slot_kept f₁ (by decide) (by decide)]; exact hRo) hy (Nat.mod_lt _ (by decide))
      (by rw [sl _ (by decide) (by decide)]; exact I.dO) (by rw [sl _ (by decide) (by decide)]; exact I.nO)
      (C.bufT rd₁ wr₁)) fun t₂ ⟨A₂, f₂⟩ => ?_
    refine ⟨A₂.env, by rw [A₂.rd, rd₁], by rw [A₂.wr, wr₁], f₁.trans (tailR_ctr f₂), ?_, ?_⟩
    · have h := dTail f₂ (a := 0) (l := n) (by omega_arith)
      rw [BitVec.add_zero] at h
      rw [h, o₁]
    · rw [A₂.out, hY, I.mac, C.ciph_kept f₁, ← Proof.Cmac.chain_append, blocks_ptOf]
      by_cases h0 : n % 16 = 0
      · simp only [h0, ↓reduceIte]
      · simp only [h0, Bool.false_eq_true, ↓reduceIte]
        rw [pT (by omega_arith)]
        have e₁ : bytesAt t₁.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
            (bytesAt t₁.mem (w64 D) n).drop (16 * (n / 16)) := by
          rw [← Proof.AesCcm.bytesAt_suffix _ _ hb, show n - 16 * (n / 16) = n % 16 by omega_arith]
        have e₂ := Proof.Cmac.Stream.bytesAt_append s.mem (w64 D) (16 * (n / 16)) (n % 16)
        rw [Nat.div_add_mod n 16] at e₂
        rw [e₁, o₁, e₂, Proof.AesCcm.xorFrom_append _ _ _ (length_bytesAt _ _ _),
          List.drop_left' (by rw [Proof.AesCcm.length_xorFrom, length_bytesAt]), Nat.add_comm 1]
  · -- chained, then encrypted
    rw [ite_eq_left rfl]
    refine WP.seq (WP.mono (absorbTail_ok v L I.env C.rounds (by rw [C.slot_kept I.frame (by decide) (by decide)]; exact hK)
      (by rw [C.slot_kept I.frame (by decide) (by decide)]; exact hRo) hy (Nat.mod_lt _ (by decide)) I.dO I.nO
      (C.bufT I.rd I.wr)) fun t₁ ⟨A₁, f₁⟩ => ?_)
    have I₁ := I.toCtrMid.absorbed C A₁ f₁
    refine WP.mono (ctrTail_ok v C hK hRo hlen I₁) fun t₂ ⟨E₂, rd₂, wr₂, f₂, o₂, g₂⟩ => ?_
    refine ⟨E₂, rd₂, wr₂, f₂, o₂, ?_⟩
    rw [Proof.AesGcm.X86.bytesAt_frame g₂ (C.tail_w (by omega_arith)) (by decide),
      A₁.out, I.mac, C.ciph_kept I.frame, ← Proof.Cmac.chain_append, blocks_ptOf]
    by_cases h0 : n % 16 = 0
    · simp only [h0, ↓reduceIte]
    · simp only [h0, ↓reduceIte]
      have hrest := I.rest
      rw [show n - 16 * (n / 16) = n % 16 by omega_arith] at hrest
      rw [pT (by omega_arith), hrest]

end VG.Proof.AesCcm.X86

end

end

/-! ### `AesCcm.X86.Top`, which this module and modules that import it used -/

section

/-! ### `AesCcm.X86.Args`, which this module and modules that import it used -/

section

/-! ### `AesCcm.X86.Contract`, which this module and modules that import it used -/

section

/-!
# AES-CCM on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The code is proved with its
working space as an eleventh argument, `work`, against the shared contracts
with it appended (`Proof/AesCcm/Scratch.lean`), which imply these
(`Verified.lean`); a frame allocates it (`Frame.lean`). The arguments are on the stack, from `[esp + 4]`
(cdecl), and may be overwritten (`writeArgs`); the calls push their
arguments and return addresses below `esp`: 60 bytes for a call of
`vg_cmac_aes_update` (its own 28 and the 32 of its calls of `vg_aes_ctr32_to`),
which no buffer overlaps, nor the return address.
-/

@[expose] public section

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The buffers of `vg_aes_ccm_seal(schedule, rounds, nonce, nonce_len, aad, aad_len, data, len, tag, tag_len, work)`
and `vg_aes_ccm_open`, with the same arguments. -/
abbrev schR (s : State) : Region := ⟨(arg s 0).setWidth 64, 240⟩
abbrev nonceR (s : State) : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
abbrev aadR (s : State) : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
abbrev dataR (s : State) : Region := ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩
abbrev tagR (s : State) : Region := ⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩
abbrev workR (s : State) : Region := ⟨(arg s 10).setWidth 64, 2560⟩
abbrev argsR' (s : State) : Region := ⟨argAddr s 0, 44⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev stackR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 60, 60⟩

/-- What both functions' preconditions say of the buffers and the
arguments, but for which may be written. -/
def oneLay (s : State) : Prop :=
  (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (workR s) ∧ (schR s).Disjoint (argsR' s) ∧
  (nonceR s).Disjoint (dataR s) ∧ (nonceR s).Disjoint (workR s) ∧ (nonceR s).Disjoint (argsR' s) ∧
  (aadR s).Disjoint (dataR s) ∧ (aadR s).Disjoint (workR s) ∧ (aadR s).Disjoint (argsR' s) ∧
  (dataR s).Disjoint (tagR s) ∧ (dataR s).Disjoint (workR s) ∧ (dataR s).Disjoint (argsR' s) ∧
  (tagR s).Disjoint (workR s) ∧ (tagR s).Disjoint (argsR' s) ∧ (workR s).Disjoint (argsR' s) ∧
  (retR s).Disjoint (schR s) ∧ (retR s).Disjoint (nonceR s) ∧ (retR s).Disjoint (aadR s) ∧
  (retR s).Disjoint (dataR s) ∧ (retR s).Disjoint (tagR s) ∧ (retR s).Disjoint (workR s) ∧
  (retR s).Disjoint (argsR' s) ∧
  (stackR s).Disjoint (schR s) ∧ (stackR s).Disjoint (nonceR s) ∧ (stackR s).Disjoint (aadR s) ∧
  (stackR s).Disjoint (dataR s) ∧ (stackR s).Disjoint (tagR s) ∧ (stackR s).Disjoint (workR s) ∧
  (stackR s).Disjoint (argsR' s) ∧
  (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
  (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧
  (arg s 10).toNat + 2560 ≤ 2 ^ 32 ∧ 60 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 48 ≤ 2 ^ 32 ∧
  ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) ∧
  valid (arg s 9).toNat (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat = true

/-- `seal` writes the tag. -/
def sealPre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s] ∧ s.wr = [dataR s, tagR s, workR s, argsR' s] ∧ oneLay s

/-- `open` reads it. -/
def openPre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s, tagR s] ∧ s.wr = [dataR s, workR s, argsR' s] ∧ oneLay s

/-- All eleven stack arguments are public, and the stack pointer. -/
def onePub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 11, arg s₁ i = arg s₂ i

/-- What `open` computes. -/
abbrev openRes (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (arg s 9).toNat
    (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
    (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) (bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat)

/-- `vg_aes_ccm_seal`. -/
def sealX86 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (arg s 9).toNat
        (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
        (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) =
      (bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat, bytesAt s'.mem ((arg s 8).setWidth 64) (arg s 9).toNat)
  pub := onePub

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) then [] else
  [if (openRes s).isSome then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openX86 : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧ bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = pt
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
      bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = zeros (arg s 7).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: the arguments

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`).
Between the entry and the exit, the pieces only write the parts of `W` in
`mutR`, the stack below `SP` and the data, so they keep the slots, the saved
registers, the key schedule, the nonce and the associated data.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 slotv argsR argsR_eq below_eq SavedAt savedR ofNat_toNat32)

/-- What `seal` and `open` are given: the key schedule at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`), the working
space at `W` and the stack pointer `SP`. -/
structure Args (s : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) : Prop where
  lay : Lay K W SP
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf W SP s N nl
  aad : Buf W SP s A al
  data : Buf W SP s D n
  tag : Buf W SP s T tl
  dw : Covers [⟨w64 D, n⟩] s.wr
  dk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩
  nd : (⟨w64 N, nl⟩ : Region).Disjoint ⟨w64 D, n⟩
  ad : (⟨w64 A, al⟩ : Region).Disjoint ⟨w64 D, n⟩
  td : (⟨w64 T, tl⟩ : Region).Disjoint ⟨w64 D, n⟩
  h7 : 7 ≤ nl
  h13 : nl ≤ 13
  t4 : 4 ≤ tl
  t16 : tl ≤ 16
  te : tl % 2 = 0
  hn : n < 256 ^ (15 - nl)
  al32 : al < 2 ^ 32
  n32 : n < 2 ^ 32
  retW : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  retD : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 D, n⟩
  retT : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 T, tl⟩
  args : Covers [argsR SP 11] (s.rd ++ s.wr)
  argsW : (argsR SP 11).Disjoint ⟨w64 W, 2560⟩
  fa : SP.toNat + 4 + 4 * 11 ≤ 2 ^ 32

/-- `Args`, from what both preconditions say, with the key schedule, the
nonce, the associated data and the tag readable and the data, the working
space and the arguments writable. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (mrd : ∀ r ∈ [schR s, nonceR s, aadR s, tagR s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [dataR s, workR s, argsR' s], Covers [r] s.wr) :
    Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat := by
  simp only [oneLay, stackR] at h
  obtain ⟨d1, d2, _, d4, d5, _, d7, d8, _, d10, d11, _, d13, _, d15, _, _, _, d19, d20, d21, _,
    b1, b2, b3, b4, b5, b6, _, f1, f2, f3, f4, f5, f6, hsp, hfa, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  rw [show (60 : Addr) = BitVec.ofNat 64 60 from rfl, below_eq hsp] at b1 b2 b3 b4 b5 b6
  exact {
    lay := ⟨f1, f6, hsp, d2, b1, b6⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), f2, d5, b2⟩
    aad := ⟨mrd _ (by simp), f3, d8, b3⟩
    data := ⟨Proof.AesGcm.X86.covers_left (mwr _ (by simp)), f4, d11, b4⟩
    tag := ⟨mrd _ (by simp), f5, d13, b5⟩
    dw := mwr _ (by simp)
    dk := d1
    nd := d4
    ad := d7
    td := d10.symm
    h7 := hn7
    h13 := hn13
    t4 := ht4
    t16 := ht16
    te := hte
    hn := hp
    al32 := BitVec.isLt _
    n32 := BitVec.isLt _
    retW := d21
    retD := d19
    retT := d20
    args := by rw [argsR_eq]; exact Proof.AesGcm.X86.covers_left (mwr _ (by simp))
    argsW := by rw [argsR_eq]; exact d15.symm
    fa := by omega_using [hfa] }

theorem args_of_seal {s : State} (h : sealPre s) :
    Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat := by
  obtain ⟨hrd, hwr, hl⟩ := h
  refine args_of_lay hl (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_right _ (by rw [hwr]; simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact covers_of_mem (by rw [hwr]; simp)

/-- In `seal`, the tag is writable. -/
theorem tag_wr {s : State} (h : sealPre s) : Covers [tagR s] s.wr :=
  covers_of_mem (by rw [h.2.1]; simp)

theorem args_of_open {s : State} (h : openPre s) :
    Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat := by
  obtain ⟨hrd, hwr, hl⟩ := h
  exact args_of_lay hl (fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr)))
    (fun r hr => covers_of_mem (by rw [hwr]; exact hr))

/-! ## What the pieces keep -/

section
variable {K W SP D : BitVec 32} {n : Nat} {m m' : Mem}

theorem saved_mut (L : Lay K W SP) (hD : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2560⟩)
    (hf : Frame (mutR W SP D n) m m') {s₀ : State} (S : SavedAt m W s₀) : SavedAt m' W s₀ :=
  S.frame hf fun r hr => (kept_mut L hD (d := 128) (k := 16) (.inl ⟨by decide, by decide⟩) r hr)

theorem ciph_mut (L : Lay K W SP) (hdk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hf : Frame (mutR W SP D n) m m') :
    Spec.Ccm.ctxCiph m' (w64 K) R = Spec.Ccm.ctxCiph m (w64 K) R :=
  ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact L.k_w.sub_right (Region.sub_prefix (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.stk_k.symm
    · exact hdk) (by rcases hR with h | h | h <;> subst h <;> decide)

theorem buf_mut {s : State} {P : BitVec 32} {len : Nat} (hP : Buf W SP s P len)
    (hPD : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 D, n⟩) (hf : Frame (mutR W SP D n) m m') :
    bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD) (by have := hP.lt; omega_using [this])

end

/-- Every region of `rs` is part of one of `mutR`. -/
abbrev InMut (W SP D : BitVec 32) (n : Nat) (rs : List Region) : Prop :=
  ∀ r ∈ rs, ∃ r' ∈ mutR W SP D n, Region.Sub r r'

theorem inMut_macR (W SP D : BitVec 32) (n : Nat) {y : Nat} (hy : y = 0 ∨ y = 96) : InMut W SP D n (macR W SP y) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, by rcases hy with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 60, by simp, fun _ h => h⟩

theorem inMut_ctrR (W SP D : BitVec 32) (n : Nat) {y : Nat} (hy : y = 0 ∨ y = 96) :
    InMut W SP D n (ctrR W SP D n y) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wA W, by simp, by rcases hy with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 60, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem frame_toMut {W SP D : BitVec 32} {n : Nat} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (h : InMut W SP D n rs) : Frame (mutR W SP D n) m m' := hf.sub h

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: the start of both functions

Untrusted: everything here is checked by Lean. `seal` and `open` both start
with the entry and `Ctr₀` (`start_ok`); after them, the slots hold the
arguments and `W + 48` holds `Ctr₀`, and the key schedule, the nonce, the
associated data, the data, the received tag and the return address are as
they were (`Started`). The pieces after them write only `mutR`, which keeps
all of that but the data (`Started.mut`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt ret_below ofNat_toNat32)

/-- After the entry and `Ctr₀`. -/
structure Started (s : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s' : State) : Prop where
  env : Env K W SP s'
  slots : Slots W K R N A D T nl al n tl s'.mem
  saved : SavedAt s'.mem W s
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  c0 : bytesAt s'.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0
  ciph : Spec.Ccm.ctxCiph s'.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R
  aadB : bytesAt s'.mem (w64 A) al = bytesAt s.mem (w64 A) al
  dataB : bytesAt s'.mem (w64 D) n = bytesAt s.mem (w64 D) n
  tagB : bytesAt s'.mem (w64 T) tl = bytesAt s.mem (w64 T) tl
  ret : s'.mem.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32

/-- The entry and `Ctr₀`. -/
theorem start_ok {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : arg s 0 = K)
    (a1 : arg s 1 = BitVec.ofNat 32 R) (a2 : arg s 2 = N) (a3 : arg s 3 = BitVec.ofNat 32 nl) (a4 : arg s 4 = A)
    (a5 : arg s 5 = BitVec.ofNat 32 al) (a6 : arg s 6 = D) (a7 : arg s 7 = BitVec.ofNat 32 n) (a8 : arg s 8 = T)
    (a9 : arg s 9 = BitVec.ofNat 32 tl) (a10 : arg s 10 = W) :
    WP isa (.seq ccmEntry ctrs) s (Started s K W SP N A D T R nl al n tl) := by
  have L := Ar.lay
  refine WP.seq (WP.mono (entry_ok a10 Ar.perm.w (by rw [hsp]; exact Ar.args) (by rw [hsp]; exact Ar.argsW)
    (by rw [hsp]; exact Ar.fa) L.fw) fun s₁ E₀ => ?_)
  have E₁ : Env K W SP s₁ := ⟨E₀.ebp, by rw [E₀.esp, hsp], Ar.perm.of_eq E₀.rd E₀.wr⟩
  have sl : ∀ p ∈ entryPs, slotv s₁.mem W p.2 = arg s p.1 := E₀.slots
  have S₁ : Slots W K R N A D T nl al n tl s₁.mem :=
    ⟨by rw [sl (0, ctxO) (by simp), a0], by rw [sl (1, roundsO) (by simp), a1],
      by rw [sl (2, nonceO) (by simp), a2], by rw [sl (3, nlenO) (by simp), a3],
      by rw [sl (4, aadO) (by simp), a4], by rw [sl (5, alenO) (by simp), a5],
      by rw [sl (6, dataO) (by simp), a6], by rw [sl (7, lenO) (by simp), a7],
      by rw [sl (9, Impl.AesGcm.X86.tglO) (by simp), a9], by rw [sl (8, Impl.AesGcm.X86.tpO) (by simp), a8]⟩
  have fE := E₀.frame
  have bE : ∀ {P : BitVec 32} {len : Nat}, Buf W SP s P len → bytesAt s₁.mem (w64 P) len = bytesAt s.mem (w64 P) len :=
    fun hP => Proof.AesGcm.X86.bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_using [this])
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  have cE : Spec.Ccm.ctxCiph s₁.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    ctxCiph_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  refine WP.mono (ctrs_ok L E₁ S₁.nonce S₁.nlen (Ar.nonce.of_eq E₀.rd E₀.wr) Ar.h7 Ar.h13)
    fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_
  have f₂' : Frame (mutR W SP D n) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  have b₂ : ∀ {P : BitVec 32} {len : Nat}, Buf W SP s P len → bytesAt s₂.mem (w64 P) len = bytesAt s₁.mem (w64 P) len :=
    fun hP => Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_using [this])
  refine ⟨E₂, slots_mut L Ar.data.w f₂' S₁, saved_mut L Ar.data.w f₂' E₀.saved, by rw [rd₂, E₀.rd],
    by rw [wr₂, E₀.wr], by rw [c₂, bE Ar.nonce], ?_, by rw [b₂ Ar.aad, bE Ar.aad], by rw [b₂ Ar.data, bE Ar.data],
    ?_, ?_⟩
  · rw [ctxCiph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb, cE]
  · rw [b₂ Ar.tag, bE Ar.tag]
  · rw [Proof.AesGcm.X86.ret_kept f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.retW.sub_right (Lay.wSub (by decide))),
      Proof.AesGcm.X86.ret_kept fE (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.retW.sub_right (Lay.wSub (by decide)))]

/-- What the pieces after the start keep. -/
theorem Started.mut {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) {s₁ : State} (St : Started s K W SP N A D T R nl al n tl s₁) {m : Mem}
    (hf : Frame (mutR W SP D n) s₁.mem m) :
    Slots W K R N A D T nl al n tl m ∧ SavedAt m W s ∧
      Spec.Ccm.ctxCiph m (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R ∧
      bytesAt m (w64 A) al = bytesAt s.mem (w64 A) al ∧ m.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32 := by
  have L := Ar.lay
  refine ⟨slots_mut L Ar.data.w hf St.slots, saved_mut L Ar.data.w hf St.saved,
    by rw [ciph_mut L Ar.dk Ar.rounds hf, St.ciph], by rw [buf_mut Ar.aad Ar.ad hf, St.aadB], ?_⟩
  rw [Proof.AesGcm.X86.ret_kept hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Ar.retW.sub_right (Region.sub_prefix (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact ret_below L.sp
    · exact Ar.retD), St.ret]

end VG.Proof.AesCcm.X86

end

end

/-! ### `AesCcm.X86.Mask`, which this module and modules that import it used -/

section

/-!
# AES-CCM on x86: masking the data, and the tag copied out

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of the
data with `0 − ok`: the data if `ok = 1`, zeros if `ok = 0` (`mask_ok`).
`tagOut` copies the first `tag_len` bytes of the tag at `W` to `tag`
(`tagOut_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop maskWords tglO tpO rO)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv in_of_covers covers_left succ_ofNat32 add_zero32 pred_count pred_beq bytesAt_succ
  maskWords_ok
  length_bytesAt and_self_beq32 WEnv padLoop_ok zero4_fold toNat_ofNat32 LoopPre CopyPost copyLoop_ok CT)

/-! ## `mask` -/

theorem mask_byte32 (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl, .alu .add .edi (imm 1),
    .alu .sub .ecx (imm 1)]

theorem maskStep_ok (s : State) {P : BitVec 32} {i n : Nat} {c : Bool} (hs : s.gpr .edi = P + BitVec.ofNat 32 i)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i)) (hb : s.gpr .ebx = 0 - (if c then 1 else 0))
    (eP : w64 (P + BitVec.ofNat 32 i) = w64 P + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 P + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 P + BitVec.ofNat 64 i) ((if c then s.mem (w64 P + BitVec.ofNat 64 i) else 0 : Byte)) ∧
      s'.gpr .edi = P + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [maskBody, add_zero32, hs, eP, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hb, mask_byte32]
  · cregs [hs, succ_ofNat32]
  · cregs [hc]
  · cmems [hc]
  · intro r h₁ h₂ h₃; cregs [h₁, h₂, h₃]
  all_goals cmems []

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`, for `ok` (at `W + okO`) 1 or 0. -/
theorem mask_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {D : BitVec 32} {n : Nat}
    (hDp : slotv s.mem W dataO = D) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32)
    (hD : Buf W SP s D n) (hDw : Covers [⟨w64 D, n⟩] s.wr) {c : Bool}
    (hok : slotv s.mem W okO = if c then 1 else 0) :
    WP isa mask s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) n else zeros n) := by
  obtain ⟨s₁, run₁, m₁, cx₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hlen]
    · cmems [hlen]; rw [and_self_beq32 hn32]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  have E₁ : Env K W SP s₁ := E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨E₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [Spec.Aes.bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  obtain ⟨s₂, run₂, m₂, bx₂, di₂, cx₂, bp₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧ s₂.mem = s.mem ∧
      s₂.gpr .ebx = 0 - (if c then 1 else 0) ∧ s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n ∧
      s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    have hok₁ : slotv s₁.mem W okO = if c then 1 else 0 := by rw [m₁]; exact hok
    have hd₁ : slotv s₁.mem W dataO = D := by rw [m₁]; exact hDp
    refine ⟨_, by crun [bp₁, L.aW, E₁.perm.wR, hok₁, hd₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [m₁]
    · cregs [hok₁]; rfl
    · cregs [hd₁]
    · cregs [cx₁]
    · cregs [bp₁]
    · cregs [sp₁]
    · cmems [rd₁]
    · cmems [wr₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hfD := hD.wrap
  refine WP.seq (WP.mono (maskWords_ok s₂ hn32 (by omega_arith) di₂ cx₂ bx₂ (by rw [rd₂, wr₂]; exact hD.rd)
    (by rw [wr₂]; exact hDw)) fun s₃ ⟨j₀, hj₀, hlt₀, di₃, cx₃, m₃, g₃, rd₃, wr₃⟩ => ?_)
  obtain ⟨s₄, run₄, g₄, m₄, zf₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa [.alu .test .ecx (.reg .ecx)] s₃ = some s₄ ∧
      s₄.gpr = s₃.gpr ∧ s₄.mem = s₃.mem ∧ s₄.zf = some (decide (n - j₀ = 0)) ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · cmems [cx₃]; rw [and_self_beq32 (by omega_arith)]
    · rfl
    · rfl
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  obtain mem₄ : s₄.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) j₀ else zeros j₀) := by
    rw [m₄, m₃, m₂]; rfl
  obtain gg₄ : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → s₄.gpr r = s₂.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₄, g₃ r h₁ h₂ h₃]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂]
  refine WP.ite (decide (n - j₀ = 0)) (eval_e zf₄) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · obtain rfl : j₀ = n := by have := of_decide_eq_true hb; omega_arith
    exact ⟨⟨by rw [gg₄ _ (by decide) (by decide) (by decide), bp₂],
      by rw [gg₄ _ (by decide) (by decide) (by decide), sp₂], E.perm.of_eq rd₄' wr₄'⟩, rd₄', wr₄', mem₄⟩
  obtain hj₁ : j₀ < n := by have := of_decide_eq_false hb; omega_arith
  refine WP.loop (M := isa) (body := .block maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .edi = D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (n - j) ∧
      t.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) j else zeros j) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t.gpr r = s₂.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - j₀) _
    ⟨j₀, rfl, hj₁, by rw [g₄, di₃], by rw [g₄, cx₃], mem₄, gg₄, rd₄', wr₄'⟩
  rintro k t ⟨j, rfl, hj, di, cx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', zf', g', rd', wr'⟩ := maskStep_ok t (P := D) (i := j) (n := n) (c := c) di cx
    (by rw [g _ (by decide) (by decide) (by decide), bx₂]) (w64_add (by omega_arith))
    (by rw [rd, wr]; exact in_of_covers hD.rd hj (by omega_arith))
    (by rw [wr]; exact in_of_covers hDw hj (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨w64 D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (w64 D + BitVec.ofNat 64 j) = s.mem (w64 D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 D) (show j < 2 ^ 64 by omega_arith)] at hcon; omega_arith
  have hmem : t'.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) (j + 1) else zeros (j + 1)) := by
    rw [mem', hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega_arith), length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by rw [zf', pred_beq hj hn32]
  have gg : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t'.gpr r = s₂.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  have E' : Env K W SP t' := ⟨by rw [gg _ (by decide) (by decide) (by decide), bp₂],
    by rw [gg _ (by decide) (by decide) (by decide), sp₂], E.perm.of_eq (by rw [rd', rd]) (by rw [wr', wr])⟩
  by_cases he : j + 1 = n
  · left
    exact ⟨by simp [eval, hz, he], E', by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, di',
      by rw [cx', pred_count hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The tag copied out -/

/-- `tagOut`: the first `t` bytes at `W` written to `tag` (kept at `W + tpO`). -/
theorem tagOut_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {T : BitVec 32} {t : Nat}
    (hv : slotv s.mem W tglO = BitVec.ofNat 32 t) (hT : slotv s.mem W tpO = T) (ht1 : 1 ≤ t) (ht : t ≤ 16)
    (Tb : Buf W SP s T t) (tw : Covers [⟨w64 T, t⟩] s.wr) :
    WP isa tagOut s fun s' => s'.mem = writeBytes s.mem (w64 T) (bytesAt s.mem (w64 W) t) ∧ Env K W SP s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, hm₁, hdi, hdx, hcx, hbp, hsp, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edi (.reg .ebp), .mov .edx (slot tpO), .mov .ecx (slot tglO)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .edi = W ∧ s₁.gpr .edx = T ∧ s₁.gpr .ecx = BitVec.ofNat 32 t ∧ s₁.gpr .ebp = W ∧
      s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hv, hT], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems []
    · cregs [E.ebp]
    · cregs [hT]
    · cregs [hv]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp : LoopPre s₁ W T t := ⟨hdi, hdx, hcx, ht1, by omega_arith, by have := L.fw; omega_arith, Tb.wrap,
    by rw [hrd₁, hwr₁]; simpa using covers_left (E.perm.wC (d := 0) (n := t) (by omega_arith)),
    by rw [hwr₁]; exact tw, (Tb.w.sub_right (Region.sub_prefix (by omega_arith))).symm⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s' P => ⟨by rw [P.mem, hm₁], ⟨?_, ?_, E.perm.of_eq ?_ ?_⟩, ?_, ?_⟩
  · rw [P.other _ (by decide) (by decide) (by decide) (by decide), hbp]
  · rw [P.other _ (by decide) (by decide) (by decide) (by decide), hsp]
  all_goals first | rw [P.rd, hrd₁] | rw [P.wr, hwr₁]

theorem tagOut_ct {K W SP T : BitVec 32} {t : Nat} {I : State → Prop} (L : Lay K W SP)
    (h : ∀ s, I s → Env K W SP s ∧ slotv s.mem W tglO = BitVec.ofNat 32 t ∧ slotv s.mem W tpO = T) :
    CT I tagOut := by
  refine CT.seq (J := fun s => s.gpr .edi = W ∧ s.gpr .edx = T ∧ s.gpr .ecx = BitVec.ofNat 32 t)
    (CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h _ h₁).1.ebp, (h _ h₂).1.ebp]) (by taint_decide))
    (fun s hs => ?_) (Proof.AesGcm.X86.copyLoop_ct fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2])
  obtain ⟨E, hv, hT⟩ := h s hs
  exact WP.of_runBlock ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hv, hT], by cregs [E.ebp], by cregs [hT], by cregs [hv]⟩

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `seal` is the start (the
entry and `Ctr₀`, `start_ok`), the MAC of the payload at `W` (`mac_ok`),
encrypted (`tag_ok`), counter mode over the data (`ctr_ok`), the tag copied
to `tag` (`tagOut_ok`) and the exit (`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt exit_ok ofNat_toNat32 length_bytesAt covers_left writeBytes_frame'
  bytesAt_writeBytes_self)

/-- What `tag y` writes, in `mutR`. -/
theorem inMut_tag (W SP D : BitVec 32) (n : Nat) {y : Nat} (hy : y = 0 ∨ y = 96) :
    InMut W SP D n [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, wC W, below SP 60] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wA W, by simp, by rcases hy with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  · exact ⟨wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 60, by simp, fun _ h => h⟩

/-- A buffer apart from `W` and the stack keeps its bytes across a frame of
parts of `W` and the stack. -/
theorem buf_kept' {W SP : BitVec 32} {s : State} {P : BitVec 32} {len : Nat} (hP : Buf W SP s P len)
    {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨w64 W, 2560⟩ ∨ r = below SP 60) {m m' : Mem}
    (hf : Frame rs m m') : bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    rcases hrs r hr with h | rfl
    · exact hP.w.sub_right h
    · exact hP.stk.symm) (by have := hP.lt; omega_using [this])

/-- `Ctr₀` is kept by a frame of parts of `W` apart from it. -/
theorem c0_kept {W : BitVec 32} {rs : List Region}
    (hrs : ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) {m m' : Mem} (hf : Frame rs m m') :
    bytesAt m' (w64 W + BitVec.ofNat 64 48) 16 = bytesAt m (w64 W + BitVec.ofNat 64 48) 16 :=
  Proof.AesGcm.X86.bytesAt_frame hf hrs (by decide)

/-- What the MAC and the data leave. -/
structure MacData (s : State) (K W SP N A D T : BitVec 32) (R nl al n tl y : Nat) (enc : Bool) (s₂ s' : State) : Prop where
  env : Env K W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (mutR W SP D n) s₂.mem s'.mem
  c0 : bytesAt s'.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0
  out : bytesAt s'.mem (w64 D) n =
    xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) 1 (bytesAt s.mem (w64 D) n)
  mac : bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
    Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (Spec.Cmac.zeros 16)
      (Spec.Ccm.format tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 A) al)
        (if enc then bytesAt s.mem (w64 D) n
          else xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) 1 (bytesAt s.mem (w64 D) n)))

/-- `Ctr₀` is kept by the MAC's pieces. -/
theorem macR_c0 {K W SP : BitVec 32} (L : Lay K W SP) {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∀ r ∈ macR W SP y, (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.w_w (by omega_using [hy]) (by decide) (by omega_using [hy])
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- The MAC of the nonce and the associated data, and the data. -/
theorem macData_ok (v : Ctr32Impl) {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) {s₂ : State} (St : Started s K W SP N A D T R nl al n tl s₂) {y : Nat}
    (hy : y = 0 ∨ y = 96) (enc : Bool) :
    WP isa (.seq (macPre v.callee v.suffix y) (data v.callee v.suffix enc y)) s₂
      (MacData s K W SP N A D T R nl al n tl y enc s₂) := by
  have L := Ar.lay
  obtain hnl := length_bytesAt s.mem (w64 N) nl
  obtain h7' : 7 ≤ (bytesAt s.mem (w64 N) nl).length := by rw [hnl]; exact Ar.h7
  obtain h13' : (bytesAt s.mem (w64 N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  obtain hy16 : y + 16 ≤ 2560 := by omega_using [hy]
  refine WP.seq (WP.mono (macPre_ok v L St.env Ar.rounds St.slots hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn
    Ar.n32 St.c0 hy (Ar.aad.of_eq St.rd St.wr)) fun s₃ A₃ => ?_)
  obtain f₃ : Frame (mutR W SP D n) s₂.mem s₃.mem := frame_toMut A₃.frame (inMut_macR W SP D n hy)
  obtain ⟨S₃, -, ci₃, -, -⟩ := St.mut Ar f₃
  obtain hc₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 := by
    rw [c0_kept (macR_c0 L hy) A₃.frame, St.c0]
  obtain rd₃ : s₃.rd = s.rd := by rw [A₃.rd, St.rd]
  obtain wr₃ : s₃.wr = s.wr := by rw [A₃.wr, St.wr]
  obtain hD₃ : bytesAt s₃.mem (w64 D) n = bytesAt s.mem (w64 D) n := by
    rw [buf_kept Ar.data hy16 A₃.frame, St.dataB]
  obtain C₃ : CtrCtx K W SP s₃ R (bytesAt s.mem (w64 N) nl) D n y :=
    ⟨L, Ar.rounds, h7', h13', by rw [hnl]; exact Ar.hn, Ar.n32, hy, hc₃, Ar.data.of_eq rd₃ wr₃,
      by rw [wr₃]; exact Ar.dw, Ar.dk⟩
  refine WP.mono (data_ok v enc C₃ A₃.env S₃.ctx S₃.rounds S₃.data S₃.len) fun s₄ P => ?_
  refine ⟨P.env, by rw [P.rd, rd₃], by rw [P.wr, wr₃], f₃.trans (frame_toMut P.frame (inMut_ctrR W SP D n hy)),
    C₃.c0_kept P.frame, by rw [P.out, ci₃, hD₃], ?_⟩
  rw [P.mac, A₃.out, ci₃, St.ciph, St.aadB, ← Proof.Cmac.chain_append]
  have e : ptOf K s₃ R (bytesAt s.mem (w64 N) nl) D enc n = if enc then bytesAt s.mem (w64 D) n
      else xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) 1 (bytesAt s.mem (w64 D) n) := by
    simp only [ptOf, ci₃, hD₃]
  have l : (if enc then bytesAt s.mem (w64 D) n
      else xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) 1 (bytesAt s.mem (w64 D) n)).length = n := by
    rw [← e, length_ptOf]
  rw [e, Proof.AesCcm.format_eq tl (by rw [hnl]; have := Ar.h13; omega_using [this]), l, length_bytesAt]

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' (v : Ctr32Impl) {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : arg s 0 = K)
    (a1 : arg s 1 = BitVec.ofNat 32 R) (a2 : arg s 2 = N) (a3 : arg s 3 = BitVec.ofNat 32 nl) (a4 : arg s 4 = A)
    (a5 : arg s 5 = BitVec.ofNat 32 al) (a6 : arg s 6 = D) (a7 : arg s 7 = BitVec.ofNat 32 n) (a8 : arg s 8 = T)
    (a9 : arg s 9 = BitVec.ofNat 32 tl) (a10 : arg s 10 = W) (tw : Covers [⟨w64 T, tl⟩] s.wr) :
    WP isa («seal» v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n)
        (bytesAt s.mem (w64 A) al) = (bytesAt s'.mem (w64 D) n, bytesAt s'.mem (w64 T) tl) := by
  have L := Ar.lay
  obtain hnl := length_bytesAt s.mem (w64 N) nl
  obtain h7' : 7 ≤ (bytesAt s.mem (w64 N) nl).length := by rw [hnl]; exact Ar.h7
  obtain h13' : (bytesAt s.mem (w64 N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  refine seq_assoc (WP.seq (WP.mono (start_ok Ar hsp a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) fun s₂ St => ?_))
  -- The MAC and the data.
  refine seq_assoc (WP.seq (WP.mono (macData_ok v Ar St (y := 0) (.inl rfl) true) fun s₃ M₃ => ?_))
  obtain ⟨S₃, -, ci₃, -, -⟩ := St.mut Ar M₃.frame
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L M₃.env Ar.rounds S₃.ctx S₃.rounds h7' h13' M₃.c0 (y := 0) (.inl rfl))
    fun s₅ ⟨E₅, rd₅, wr₅, f₅, h₅⟩ => ?_)
  obtain f₂₅ : Frame (mutR W SP D n) s₂.mem s₅.mem := M₃.frame.trans (frame_toMut f₅ (inMut_tag W SP D n (.inl rfl)))
  obtain ⟨S₅, sv₅, -, -, rt₅⟩ := St.mut Ar f₂₅
  obtain rd₅' : s₅.rd = s.rd := by rw [rd₅, M₃.rd]
  obtain wr₅' : s₅.wr = s.wr := by rw [wr₅, M₃.wr]
  obtain hD₅ : bytesAt s₅.mem (w64 D) n = bytesAt s₃.mem (w64 D) n :=
    buf_kept' Ar.data (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inl (Lay.wSub (by decide))
      · exact .inl (Lay.wSub (by decide))
      · exact .inl (Lay.wSub (by decide))
      · exact .inr rfl) f₅
  -- The tag copied out.
  refine WP.seq (WP.mono (tagOut_ok L E₅ S₅.tl S₅.tp (by have := Ar.t4; omega_using [this]) Ar.t16
    (Ar.tag.of_eq rd₅' wr₅') (by rw [wr₅']; exact tw)) fun s₆ ⟨m₆', E₆, rd₆, wr₆⟩ => ?_)
  obtain hTl : tl < 2 ^ 64 := by have := Ar.t16; omega_using [this]
  obtain fT : Frame [⟨w64 T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆']; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain tW : ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨w64 T, tl⟩ : Region)],
      (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (Ar.tag.w.sub_right (Lay.wSub hk)).symm
  obtain sv₆ : SavedAt s₆.mem W s := sv₅.frame fT (tW (by decide))
  obtain rt₆ : s₆.mem.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32 := by
    rw [Proof.AesGcm.X86.ret_kept fT (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.retT), rt₅]
  -- The exit.
  refine WP.mono (exit_ok (W := W) (s₀ := s) E₆.ebp (by rw [E₆.esp, hsp])
    (by rw [rd₆, wr₆, rd₅', wr₅']; exact covers_left Ar.perm.w) L.fw sv₆ (by rw [hsp]; exact rt₆))
    fun s₇ ⟨abi, m₇, _, _, _⟩ => ⟨abi, ?_⟩
  obtain hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (w64 K) R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  obtain e0 : w64 W + BitVec.ofNat 64 0 = w64 W := BitVec.add_zero _
  have o₃ := M₃.mac
  rw [e0] at h₅ o₃
  simp only [↓reduceIte] at o₃
  obtain hY := congrArg List.length o₃
  rw [length_bytesAt] at hY
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [m₇, Proof.AesGcm.X86.bytesAt_frame fT (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by have := Ar.data.lt; omega_using [this]), hD₅,
      M₃.out, crypt_eq (hBC _)]
  · have hT₇ : bytesAt s₇.mem (w64 T) tl = bytesAt s₅.mem (w64 W) tl := by
      have := bytesAt_writeBytes_self s₅.mem (w64 T) (bytesAt s₅.mem (w64 W) tl) (by rw [length_bytesAt]; omega_using [hTl])
      rw [length_bytesAt] at this
      rw [m₇, m₆', this]
    rw [hT₇, Proof.AesCcm.bytesAt_prefix s₅.mem (w64 W) Ar.t16, h₅, ci₃,
      take_xorFrom_zero (hBC _) _ (by rw [length_bytesAt]) Ar.t16, o₃,
      ← Proof.AesCcm.mac_eq _ _ (by rw [hnl]; have := Ar.h13; omega_using [this])]

end VG.Proof.AesCcm.X86

end

end

/-! ### `AesCcm.X86.DataCT`, which only this module used -/

section

/-!
# AES-CCM on x86: the data in constant time

Untrusted: everything here is checked by Lean. `data` branches on the length
of the data and on the blocks left, and addresses memory by `W` and the data's
address, all public (`data_ct`): a chunk is constant time from its address,
its counter and its length (`chunk_ct`), which the blocks left give.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop splitWhole dO nO)
open VG.Proof.AesGcm.X86 (CT w64 slotv toNat_ofNat32)

/-- What `data` starts from. -/
structure DataPre (K W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n y : Nat) (s : State) : Prop where
  env : Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  data : slotv s.mem W dataO = D
  len : slotv s.mem W lenO = BitVec.ofNat 32 n
  c : ∃ nonce, CtrCtx K W SP s R nonce D n y

/-- A loop whose measure's next value is `next`, its body constant time and
leaving the condition to loop back exactly while that is not 0. -/
theorem CT.loopTo {body : Prog isa} {c : Cond} (Inv : Nat → State → Prop) (next : Nat → Nat)
    (hb : ∀ n, CT (Inv n) body)
    (hw : ∀ n s, Inv n s → WP isa body s fun s' => next n < n ∧ isa.eval c s' = some (decide (next n ≠ 0)) ∧
      (next n ≠ 0 → Inv (next n) s'))
    (n : Nat) : CT (Inv n) (.loop body c) := by
  refine RelCT.loop (M := isa) (Q := fun _ _ => True) (fun n (s₁ s₂ : State) => Inv n s₁ ∧ Inv n s₂) (fun n => ?_) n
  have h := RelCT.wp (hb n) (F₁ := fun s' => next n < n ∧ isa.eval c s' = some (decide (next n ≠ 0)) ∧
      (next n ≠ 0 → Inv (next n) s')) (F₂ := fun s' => next n < n ∧ isa.eval c s' = some (decide (next n ≠ 0)) ∧
      (next n ≠ 0 → Inv (next n) s')) fun s₁ s₂ h => ⟨hw n s₁ h.1, hw n s₂ h.2⟩
  refine RelCT.mono h (fun _ _ h => h) fun s₁ s₂ ⟨_, ⟨hn, c₁, i₁⟩, ⟨_, c₂, i₂⟩⟩ => ⟨by rw [c₁, c₂], fun _ => trivial,
    fun ht => ?_⟩
  rw [c₁] at ht
  have h1 : next n ≠ 0 := by simpa using ht
  exact ⟨next n, hn, i₁ h1, i₂ h1⟩

/-! ## A chunk -/

/-- `ChunkPre`, for some nonce. -/
abbrev ChunkI (K W SP : BitVec 32) (R : Nat) (P : BitVec 32) (k j y : Nat) (u : State) : Prop :=
  ∃ nonce, ChunkPre K W SP u R nonce P k j y

theorem updStep_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {P : BitVec 32} {k j y : Nat} (hy : y = 0 ∨ y = 96) (hk : 16 * k < 2 ^ 32) :
    CT (ChunkI K W SP R P k j y) (updStep v.callee v.suffix y) := by
  have h₂ := updCall_ct v L hR (y := y) (Q := P) (n := k) (by omega_using [hy]) hk
    (I := fun u₁ => ∃ u, ChunkI K W SP R P k j y u ∧ u₁.mem = u.mem ∧ u₁.gpr .eax = K ∧ u₁.gpr .ecx = BitVec.ofNat 32 R ∧
      u₁.gpr .edx = W + BitVec.ofNat 32 y ∧ u₁.gpr .ebx = P ∧ u₁.gpr .esi = BitVec.ofNat 32 k ∧
      u₁.gpr .edi = W + BitVec.ofNat 32 384 ∧ u₁.gpr .ebp = W ∧ u₁.gpr .esp = SP ∧ u₁.rd = u.rd ∧ u₁.wr = u.wr)
    fun u₁ ⟨u, ⟨_, C⟩, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
      ⟨⟨bp, sp, C.env.perm.of_eq rd wr⟩, srcBuf (C.buf.of_eq rd wr),
        C.buf.w.sub_right (Lay.wSub (by omega_using [hy])), ax, cx, dx, bx, si, di⟩
  have blk : ∀ u, ChunkI K W SP R P k j y u → _ := fun u ⟨_, C⟩ => updStepArgs_ok L C.env C.ctx C.ro C.q C.k y
  rcases hy with rfl | rfl
  · exact CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, C⟩ => C.env.ebp) (by taint_decide) blk h₂
  · exact CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, C⟩ => C.env.ebp) (by taint_decide) blk h₂

theorem ctrStep_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {P : BitVec 32} {k j y : Nat} : CT (ChunkI K W SP R P k j y) (ctrStep v.callee) := by
  refine CT.block_seq (F := fun u u₁ => u₁.gpr .eax = K ∧ u₁.gpr .ecx = BitVec.ofNat 32 R ∧
      u₁.gpr .edx = W + BitVec.ofNat 32 64 ∧ u₁.gpr .ebx = P ∧ u₁.gpr .edi = BitVec.ofNat 32 k ∧ u₁.gpr .ebp = W ∧
      u₁.gpr .esp = SP ∧ u₁.rd = u.rd ∧ u₁.wr = u.wr)
    [.ebp] (pin_ebp fun _ ⟨_, C⟩ => C.env.ebp) (by taint_decide) (fun u ⟨_, C⟩ => ?_) ?_
  · obtain ⟨u₁, run, -, rest⟩ := ctrStepArgs_ok L C.env C.ctx C.ro C.q C.k
    exact ⟨u₁, run, rest⟩
  · exact ctrCall_ct v L hR (c := 64) (Q := P) (n := k) (by decide)
      fun u₁ ⟨u, ⟨_, C⟩, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ =>
        ⟨⟨bp, sp, C.env.perm.of_eq rd wr⟩, srcBuf (C.buf.of_eq rd wr), by rw [wr]; exact C.pw,
          C.buf.w.sub_right (Lay.wSub (by decide)), C.pk, ax, cx, dx, bx, di⟩

/-- `pick` branches on the blocks left. -/
theorem pick_ct (c : Impl.Aes.X86.Ctr32) {K W SP : BitVec 32} (L : Lay K W SP) {m : Nat} (hm32 : m < 2 ^ 32)
    {I : State → Prop} (hI : ∀ u, I u → Env K W SP u ∧ slotv u.mem W mO = BitVec.ofNat 32 m) : CT I (pick c) := by
  unfold pick
  by_cases h : Impl.CmacAes.X86.hardware c = true
  · rw [ite_eq_left h]
    refine CT.seq (J := fun u => u.cf = some (decide (m < 6)))
      (CT.taint [.ebp] (pin_ebp fun u hu => (hI u hu).1.ebp) (by taint_decide)) (fun u hu => ?_)
      (CT.ite (decide (m < 6)) (fun _ h => eval_b h) (fun _ => CT.nil)
        (fun _ => by exact CT.taint [] (fun _ _ _ _ _ h => by simp at h) (by taint_decide)))
    obtain ⟨E, hm⟩ := hI u hu
    exact WP.of_runBlock ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hm], by
      cmems [hm, toNat_ofNat32 hm32, toNat_ofNat32 (show 6 < 2 ^ 32 by decide)]⟩
  · rw [ite_eq_right h]
    exact CT.taint [.ebp] (pin_ebp fun u hu => (hI u hu).1.ebp) (by taint_decide)

/-- At the start of a chunk. -/
abbrev LoopI (K W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n y : Nat) (enc : Bool) (q : Nat) (t : State) : Prop :=
  ∃ s, DataPre K W SP R D n y s ∧ ∃ nonce, CtrCtx K W SP s R nonce D n y ∧ DataLoop K W SP s R nonce D n y enc q t

theorem chunk_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n y : Nat} (hy : y = 0 ∨ y = 96) (hn32 : n < 2 ^ 32) {enc : Bool} {q : Nat} (hq : q < n / 16) :
    CT (LoopI K W SP R D n y enc q) (chunk v.callee v.suffix enc y) := by
  have hk0 := pickLen_pos v.callee (m := n / 16 - q) (by omega_using [hq])
  have hkm := pickLen_le v.callee (n / 16 - q)
  unfold chunk
  refine CT.seq (J := fun u => ∃ t, LoopI K W SP R D n y enc q t ∧
      u.gpr .esi = BitVec.ofNat 32 (pickLen v.callee (n / 16 - q)) ∧ u.gpr .ebp = W ∧ u.gpr .esp = SP ∧ u.mem = t.mem ∧
      u.rd = t.rd ∧ u.wr = t.wr)
    (pick_ct v.callee L (m := n / 16 - q) (by omega_using [hn32]) fun t ⟨_, _, _, _, I⟩ => ⟨I.env, I.sm⟩)
    (fun t ⟨s, hs, nonce, C, I⟩ => WP.mono (pick_ok v.callee L I.env I.sm (by omega_using [hn32]))
      fun u h => ⟨t, ⟨s, hs, nonce, C, I⟩, h⟩) ?_
  generalize pickLen v.callee (n / 16 - q) = k at hk0 hkm ⊢
  have hk32 : 16 * k < 2 ^ 32 := by omega_using [hkm, hn32]
  refine CT.seq (J := ChunkI K W SP R (D + BitVec.ofNat 32 (16 * q)) k (q + 1) y)
    (CT.taint [.ebp] (pin_ebp fun _ ⟨_, _, _, bp, _⟩ => bp) (by taint_decide))
    (fun u ⟨t, ⟨s, hs, nonce, C, I⟩, si, bp, sp, mu, rd, wr⟩ => by
      obtain ⟨u', run, P, -⟩ := chunkPre_ok C hs.ctx hs.rounds I hk0 (by omega_using [hkm, hk0]) si bp sp mu rd wr
      exact WP.of_runBlock ⟨u', run, nonce, P⟩) ?_
  have upd := updStep_ct v L hR (P := D + BitVec.ofNat 32 (16 * q)) (j := q + 1) hy hk32
  have ctr := ctrStep_ct v L hR (P := D + BitVec.ofNat 32 (16 * q)) (k := k) (j := q + 1) (y := y)
  have adv : CT (fun u => u.gpr .ebp = W) (.block advance) := CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)
  have uw : ∀ u, ChunkI K W SP R (D + BitVec.ofNat 32 (16 * q)) k (q + 1) y u →
      WP isa (updStep v.callee v.suffix y) u (ChunkI K W SP R (D + BitVec.ofNat 32 (16 * q)) k (q + 1) y) :=
    fun u ⟨nonce, C⟩ => WP.mono (updStep_ok v C.lay C.env C.rounds C.ctx C.ro C.hy C.buf C.k32 C.q C.k)
      fun u' ⟨E, rd, wr, f, _⟩ => ⟨nonce, C.next E rd wr (updF f)⟩
  have cw : ∀ u, ChunkI K W SP R (D + BitVec.ofNat 32 (16 * q)) k (q + 1) y u →
      WP isa (ctrStep v.callee) u (ChunkI K W SP R (D + BitVec.ofNat 32 (16 * q)) k (q + 1) y) :=
    fun u ⟨nonce, C⟩ => WP.mono (ctrStep_ok v C.lay C.env C.rounds C.ctx C.ro C.buf
      C.pw C.pk C.q C.k) fun u' ⟨E, rd, wr, f, _⟩ => ⟨nonce, C.next E rd wr (ctrF f)⟩
  have bp : ∀ {c : Prog isa} {u : State}, WP isa c u (ChunkI K W SP R (D + BitVec.ofNat 32 (16 * q)) k (q + 1) y) →
      WP isa c u fun u => u.gpr .ebp = W := fun h => WP.mono h fun _ ⟨_, C⟩ => C.env.ebp
  cases enc
  · rw [ite_eq_right Bool.false_ne_true]
    exact CT.seq ctr cw (CT.seq upd (fun u h => bp (uw u h)) adv)
  · rw [ite_eq_left rfl]
    exact CT.seq upd uw (CT.seq ctr (fun u h => bp (cw u h)) adv)

/-! ## The whole blocks -/

theorem dataWhole_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n y : Nat} (hy : y = 0 ∨ y = 96) (hn32 : n < 2 ^ 32) {enc : Bool} :
    CT (DataPre K W SP R D n y) (dataWhole v.callee v.suffix enc y) := by
  refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide)
    (fun s hs => ctrSplit_ok L hs.env hs.data hs.len hn32) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : n / 16 ≠ 0 := of_decide_eq_false hf
  refine CT.seq (J := LoopI K W SP R D n y enc 0)
    (CT.taint [.ebp] (pin_ebp fun _ ⟨_, _, _, _, _, E₁, _⟩ => E₁.ebp) (by taint_decide))
    (fun s₁ ⟨s, hs, hbx, hdi, _, E₁, f₁, hd₁, hn₁, rd₁, wr₁⟩ => by
      obtain ⟨nonce, C⟩ := hs.c
      obtain ⟨s₂, run₂, I₂⟩ := loopStart_ok (enc := enc) C E₁ f₁ hd₁ hn₁ rd₁ wr₁ hbx hdi
      exact WP.of_runBlock ⟨s₂, run₂, s, hs, nonce, C, I₂⟩) ?_
  refine (CT.loopTo (fun k t => 0 < k ∧ k ≤ n / 16 ∧ LoopI K W SP R D n y enc (n / 16 - k) t)
    (fun k => k - pickLen v.callee k) (fun k => ?_) (fun k t ⟨hk0, hkm, s, hs, nonce, C, I⟩ => ?_) (n / 16)).mono
    fun t h => ⟨by omega_using [h0], Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  · by_cases hk : 0 < k ∧ k ≤ n / 16
    swap
    · exact RelCT.of_false fun _ _ h => hk ⟨h.1.1, h.1.2.1⟩
    exact (chunk_ct v L hR hy hn32 (q := n / 16 - k) (by omega_using [hk])).mono fun _ h => h.2.2
  · have e : n / 16 - (n / 16 - k) = k := by omega_using [hkm]
    have hp := pickLen_pos v.callee hk0
    have hl := pickLen_le v.callee k
    refine WP.mono (chunk_ok v C hs.ctx hs.rounds (by omega_using [hk0, hkm]) I) fun t' ⟨I', zf'⟩ => ?_
    rw [e] at I' zf'
    generalize pickLen v.callee k = l at I' zf' hp hl ⊢
    have e₂ : n / 16 - (n / 16 - k + l) = k - l := by omega_using [hkm, hl]
    rw [e₂] at zf'
    refine ⟨by omega_using [hp, hk0], by show t'.zf.map _ = _; rw [zf']; simp, fun h1 => ⟨by omega_using [h1], by omega_using [hkm], s, hs,
      nonce, C, ?_⟩⟩
    rw [show n / 16 - (k - l) = n / 16 - k + l by omega_using [hkm, hl]]
    exact I'

/-! ## The last bytes -/

/-- What the data's last bytes start from. -/
abbrev CtrTailPre (K W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n y : Nat) (t : State) : Prop :=
  ∃ s, DataPre K W SP R D n y s ∧ ∃ nonce, CtrCtx K W SP s R nonce D n y ∧ CtrMid K W SP s R nonce D n y (n / 16) t

theorem ctrTail_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n y : Nat} (hn32 : n < 2 ^ 32) :
    CT (CtrTailPre K W SP R D n y) (ctrTail v.callee) := by
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, I⟩ => I.env.ebp) (by taint_decide)
    (fun t ⟨_, _, _, _, I⟩ => testN_ok L I.env (r := n % 16) (by omega_using []) I.nO) ?_
  refine CT.ite (decide (n % 16 = 0)) (fun _ ⟨_, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : n % 16 ≠ 0 := of_decide_eq_false hf
  -- The arguments of the call making the keystream block.
  have blk : ∀ t₀ : State, (∃ t, CtrTailPre K W SP R D n y t ∧ t₀.mem = t.mem ∧ t₀.zf = some (decide (n % 16 = 0)) ∧
      t₀.gpr .ebp = W ∧ t₀.gpr .esp = SP ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr) →
      ∃ tc, runBlock isa (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++
          zero4 ksO ++ keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)) t₀ =
          some tc ∧
        Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩] t₀.mem tc.mem ∧
        tc.gpr .eax = K ∧ tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
        tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
        tc.gpr .esp = SP ∧ tc.rd = t₀.rd ∧ tc.wr = t₀.wr :=
    fun t₀ ⟨t, ⟨s, hs, nonce, C, I⟩, hm₀, _, hbp₀, hsp₀, hrd₀, hwr₀⟩ => by
      have E₀ : Env K W SP t₀ := I.env.keep (by rw [hbp₀, I.env.ebp]) (by rw [hsp₀, I.env.esp]) hrd₀ hwr₀
      have k₀ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv t₀.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
        rw [hm₀]; exact C.slot_kept I.frame h₁ h₂
      obtain ⟨tc, run, ft, -, -, rest⟩ := ctrTailArgs_ok L E₀ (by rw [k₀ _ (by decide) (by decide)]; exact hs.ctx)
        (by rw [k₀ _ (by decide) (by decide)]; exact hs.rounds) (by rw [k₀ _ (by decide) (by decide)]; exact hs.len)
        hn32 C.h7 C.h13 (by rw [hm₀]; exact C.c0_kept I.frame) (by have := C.hn; omega_using [h0, this])
      exact ⟨tc, run, ft, rest⟩
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, hbp, _⟩ => hbp) (by taint_decide) blk ?_
  -- The call.
  have a80 : w64 (W + BitVec.ofNat 32 80) = w64 W + BitVec.ofNat 64 80 := L.aW (by decide)
  have pre : ∀ tc : State, (∃ t₀ : State, (∃ t, CtrTailPre K W SP R D n y t ∧ t₀.mem = t.mem ∧
      t₀.zf = some (decide (n % 16 = 0)) ∧ t₀.gpr .ebp = W ∧ t₀.gpr .esp = SP ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩] t₀.mem tc.mem ∧
      tc.gpr .eax = K ∧ tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
      tc.gpr .esp = SP ∧ tc.rd = t₀.rd ∧ tc.wr = t₀.wr) →
      Env K W SP tc ∧ Src W SP tc (W + BitVec.ofNat 32 80) (16 * 1) ∧
      Covers [⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩] tc.wr ∧
      (⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ ∧
      (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ ∧ tc.gpr .eax = K ∧
      tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 :=
    fun tc ⟨t₀, ⟨t, ⟨_, _, _, _, I⟩, _, _, _, _, hrd₀, hwr₀⟩, _, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ => by
      have Ec : Env K W SP tc := ⟨bp, sp, I.env.perm.of_eq (by rw [rd, hrd₀]) (by rw [wr, hwr₀])⟩
      exact ⟨Ec, srcW L Ec.perm (by decide), by rw [a80]; exact Ec.perm.wC (by decide),
        by rw [a80]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide),
        by rw [a80]; exact L.k_w.sub_right (Lay.wSub (by decide)), ax, cx, dx, bx, di⟩
  refine CT.seq (J := fun td => Env K W SP td ∧ slotv td.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
      slotv td.mem W nO = BitVec.ofNat 32 (n % 16))
    (ctrCall_ct v L hR (c := 64) (by decide) pre) (fun tc h => ?_) ?_
  · obtain ⟨Ec, hq, hqw, hqc, hqk, ax, cx, dx, bx, di⟩ := pre tc h
    obtain ⟨t₀, ⟨t, ⟨_, _, _, _, I⟩, hm₀, _⟩, ft, _⟩ := h
    refine WP.mono (ctrCall_ok v L Ec hR (c := 64) (by decide) hq hqc hqk hqw ax cx dx bx di)
      fun td ⟨Ed, _, _, _, fd, _⟩ => ?_
    have fd' := fd
    rw [a80] at fd'
    have kd : ∀ o, 96 ≤ o → o + 4 ≤ 384 → slotv td.mem W o = slotv t.mem W o := fun o h₁ h₂ => by
      rw [← hm₀]
      exact ((ft.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans
        (fd'.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
          · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
          · exact ⟨⟨w64 W + BitVec.ofNat 64 384, 2048⟩, by simp, fun _ h => h⟩
          · exact ⟨below SP 60, by simp, fun _ h => h⟩) :
          Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 60]
            t₀.mem td.mem).readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
          · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
          · exact (L.stk_w' (by omega_using [h₂])).symm) (by decide)
    exact ⟨Ed, by rw [kd _ (by decide) (by decide)]; exact I.dO, by rw [kd _ (by decide) (by decide)]; exact I.nO⟩
  -- The XOR.
  refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide)
    (fun td hd => xorArgs_ok L hd.1 hd.2.1 hd.2.2) ?_
  exact Proof.AesGcm.X86.xorLoop_ct (pin3 fun _ ⟨_, _, _, hdi, hdx, hcx, _⟩ => ⟨hdi, hdx, hcx⟩)

/-- What `absorbTail` of the data's last bytes starts from. -/
theorem tailPre_of {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {n y : Nat}
    (C : CtrCtx K W SP s R nonce D n y) (hs : DataPre K W SP R D n y s) {t : State} (E : Env K W SP t)
    (f : Frame (ctrR W SP D n y) s.mem t.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (hd : slotv t.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16))) (hn : slotv t.mem W nO = BitVec.ofNat 32 (n % 16)) :
    TailPre K W SP R (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) t :=
  ⟨E, by rw [C.slot_kept f (by decide) (by decide)]; exact hs.ctx,
    by rw [C.slot_kept f (by decide) (by decide)]; exact hs.rounds, C.bufT rd wr, hd, hn⟩

/-- The data. -/
theorem data_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n y : Nat} (hy : y = 0 ∨ y = 96) (hn32 : n < 2 ^ 32) (enc : Bool) :
    CT (DataPre K W SP R D n y) (data v.callee v.suffix enc y) := by
  refine CT.seq (J := CtrTailPre K W SP R D n y) (dataWhole_ct v L hR hy hn32) (fun s hs => ?_) ?_
  · obtain ⟨nonce, C⟩ := hs.c
    exact WP.mono (dataWhole_ok v (enc := enc) C hs.env hs.ctx hs.rounds hs.data hs.len)
      fun t I => ⟨s, hs, nonce, C, I.toCtrMid⟩
  have tp : ∀ t, CtrTailPre K W SP R D n y t → TailPre K W SP R (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) t :=
    fun t ⟨s, hs, nonce, C, I⟩ => tailPre_of C hs I.env I.frame I.rd I.wr I.dO I.nO
  cases enc
  · rw [ite_eq_right Bool.false_ne_true]
    refine CT.seq (J := TailPre K W SP R (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16)) (ctrTail_ct v L hR hn32)
      (fun t ⟨s, hs, nonce, C, I⟩ => WP.mono (ctrTail_ok v C hs.ctx hs.rounds hs.len I)
        fun t₁ ⟨E₁, rd₁, wr₁, f₁, _, g₁⟩ => ?_) (absorbTail_ct v L hR hy (Nat.mod_lt _ (by decide)))
    have sl : ∀ o, 112 ≤ o → o + 4 ≤ 384 → slotv t₁.mem W o = slotv t.mem W o := fun o h₁ h₂ =>
      g₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (C.tail_w (.inr ⟨by omega_using [h₁], h₂⟩))
        (by decide)
    exact tailPre_of C hs E₁ f₁ rd₁ wr₁ (by rw [sl _ (by decide) (by decide)]; exact I.dO)
      (by rw [sl _ (by decide) (by decide)]; exact I.nO)
  · rw [ite_eq_left rfl]
    refine CT.seq (J := CtrTailPre K W SP R D n y) ((absorbTail_ct v L hR hy (Nat.mod_lt _ (by decide))).mono tp)
      (fun t h => ?_) (ctrTail_ct v L hR hn32)
    have T := tp t h
    obtain ⟨s, hs, nonce, C, I⟩ := h
    exact WP.mono (absorbTail_ok v L T.env hR T.ctx T.rounds hy (Nat.mod_lt _ (by decide)) T.d T.n T.buf)
      fun t₁ ⟨A₁, f₁⟩ => ⟨s, hs, nonce, C, I.absorbed C A₁ f₁⟩

end VG.Proof.AesCcm.X86

end

end

/-! ### `AesCcm.X86.MacCT`, which only this module used -/

section

/-!
# AES-CCM on x86: the CBC-MAC and the tag in constant time

Untrusted: everything here is checked by Lean. `b0`, `macPre` and `tag` branch
and address memory only by the slots, the lengths and `W`: all public
(`b0_ct`, `macPre_ct`, `tag_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 tglO dO nO)
open VG.Proof.AesGcm.X86 (CT w64 slotv)

/-- What the MAC's pieces keep: the slots, and the associated data readable. -/
structure MacMid (K W SP : BitVec 32) (R : Nat) (N A D T : BitVec 32) (nl al n tl : Nat) (s : State) : Prop where
  env : Env K W SP s
  slots : Slots W K R N A D T nl al n tl s.mem
  aad : Buf W SP s A al

theorem MacMid.next {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} {N A D T : BitVec 32} {nl al n tl : Nat} {s : State}
    (h : MacMid K W SP R N A D T nl al n tl s) {y : Nat} (hy : y = 0 ∨ y = 96) {s' : State} (E : Env K W SP s')
    (f : Frame (macR W SP y) s.mem s'.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    MacMid K W SP R N A D T nl al n tl s' :=
  ⟨E, h.slots.macR L hy f, h.aad.of_eq rd wr⟩

/-- What `b0` and `macPre` start from: also `Ctr₀` at `W + 48`. -/
structure MacPre (K W SP : BitVec 32) (R : Nat) (N A D T : BitVec 32) (nl al n tl : Nat) (s : State) : Prop
    extends MacMid K W SP R N A D T nl al n tl s where
  c0 : ∃ nonce : List Byte, nonce.length = nl ∧
    bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

theorem b0Blk_ct {y : Nat} (hy : y = 0 ∨ y = 96) {I : State → Prop}
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp], s₁.gpr r = s₂.gpr r) :
    CT I (.block (([.mov .ecx (slot c0O), .store (at_ .ebp blkO) .ecx, .mov .ecx (slot (c0O + 4)),
        .store (at_ .ebp (blkO + 4)) .ecx, .mov .ecx (slot (c0O + 8)), .store (at_ .ebp (blkO + 8)) .ecx,
        .store8 (at_ .ebp blkO) .al, .mov .eax (slot lenO), .bswap .eax, .alu .or .eax (slot (c0O + 12)),
        .store (at_ .ebp (blkO + 12)) .eax] : List Instr) ++ zero4 y)) := by
  rcases hy with rfl | rfl
  · exact CT.taint [.ebp] hr (by taint_decide)
  · exact CT.taint [.ebp] hr (by taint_decide)

theorem b0_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D T : BitVec 32} {nl al n tl : Nat} (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32) {y : Nat}
    (hy : y = 0 ∨ y = 96) :
    CT (MacPre K W SP R N A D T nl al n tl) (b0 v.callee v.suffix y) := by
  refine CT.assoc3 (CT.seq (J := fun s => Env K W SP s ∧ slotv s.mem W ctxO = K ∧
      slotv s.mem W roundsO = BitVec.ofNat 32 R) ?_ (fun s hs => ?_) (updBlock_ct v L hR hy fun _ h => h))
  · refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide)
      (fun s hs => b0Flags_ok L hs.env h13 ht4 hal hs.slots.tl hs.slots.nlen hs.slots.alen) ?_
    refine CT.seq (J := fun s => s.gpr .ebp = W)
      (CT.ite (decide (al = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil)
        (fun _ => by exact CT.taint [] (fun _ _ _ _ _ h => by simp at h) (by taint_decide)))
      (fun s₁ ⟨_, _, _, _, hzf, hbp, _⟩ => ?_) (b0Blk_ct hy (pin_ebp fun _ h => h))
    refine WP.ite (decide (al = 0)) (eval_e hzf) (fun _ => WP.of_runBlock ⟨s₁, rfl, hbp⟩) (fun _ => ?_)
    exact WP.of_runBlock ⟨_, by crun [], by cregs [hbp]⟩
  · obtain ⟨nonce, hnl, hc0⟩ := hs.c0
    refine WP.mono (b0Pre_ok L hs.env hnl h7 h13 ht4 ht16 hte hal hn hn32 hs.slots.tl hs.slots.nlen hs.slots.alen
      hs.slots.len hc0 hy) fun s₃ ⟨E₃, _, _, f₃, _⟩ => ?_
    have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
      f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
        · rcases hy with rfl | rfl
          · exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
          · exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)) (by decide)
    exact ⟨E₃, by rw [k₃ _ (by decide) (by decide)]; exact hs.slots.ctx,
      by rw [k₃ _ (by decide) (by decide)]; exact hs.slots.rounds⟩

theorem macPre_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D T : BitVec 32} {nl al n tl : Nat} (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32) {y : Nat}
    (hy : y = 0 ∨ y = 96) :
    CT (MacPre K W SP R N A D T nl al n tl) (macPre v.callee v.suffix y) := by
  refine CT.seq (J := MacMid K W SP R N A D T nl al n tl) (b0_ct v L hR h7 h13 ht4 ht16 hte hal hn hn32 hy)
    (fun s hs => ?_) ((aad_ct v L hR hy hal).mono fun s hs => ⟨hs.env, hs.slots.ctx, hs.slots.rounds, hs.slots.aad,
      hs.slots.alen, hs.aad⟩)
  obtain ⟨nonce, hnl, hc0⟩ := hs.c0
  exact WP.mono (b0_ok v L hs.env hR hs.slots hnl h7 h13 ht4 ht16 hte hal hn hn32 hc0 hy)
    fun s₁ ⟨E₁, f₁, _, rd, wr⟩ => hs.toMacMid.next L hy E₁ f₁ rd wr

/-- What `tag` starts from. -/
structure TagPre (K W SP : BitVec 32) (R : Nat) (s : State) : Prop where
  env : Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  c0 : ∃ nonce : List Byte, 7 ≤ nonce.length ∧ nonce.length ≤ 13 ∧
    bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

theorem tag_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) : CT (TagPre K W SP R) (tag v.callee y) := by
  have blk : ∀ s, TagPre K W SP R s → ∃ s₃, runBlock isa (([.mov .eax (imm 0)] : List Instr) ++ ctrAt ++ keyArgs c1O ++
      ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm y), .mov .edi (imm 1)] : List Instr)) s = some s₃ ∧
      s₃.gpr .eax = K ∧ s₃.gpr .ecx = BitVec.ofNat 32 R ∧ s₃.gpr .edx = W + BitVec.ofNat 32 64 ∧
      s₃.gpr .ebx = W + BitVec.ofNat 32 y ∧ s₃.gpr .edi = BitVec.ofNat 32 1 ∧ s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧
      s₃.rd = s.rd ∧ s₃.wr = s.wr := fun s hs => by
    obtain ⟨nonce, h7, h13, hc0⟩ := hs.c0
    obtain ⟨s₃, run, -, -, rest⟩ := tagArgs_ok L hs.env hs.ctx hs.rounds h7 h13 hc0 y
    exact ⟨s₃, run, rest⟩
  have h₂ := ctrCall_ct v L hR (c := 64) (Q := W + BitVec.ofNat 32 y) (n := 1) (by decide)
    (I := fun s' => ∃ s, TagPre K W SP R s ∧ s'.gpr .eax = K ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧
      s'.gpr .edx = W + BitVec.ofNat 32 64 ∧ s'.gpr .ebx = W + BitVec.ofNat 32 y ∧ s'.gpr .edi = BitVec.ofNat 32 1 ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    fun s₃ ⟨s, hs, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ => by
      have E₃ : Env K W SP s₃ := ⟨bp, sp, hs.env.perm.of_eq rd wr⟩
      obtain ⟨hq, hqw, hqc, hqk⟩ := tagCall_pre L E₃ hy
      exact ⟨E₃, hq, hqw, hqc, hqk, ax, cx, dx, bx, di⟩
  rcases hy with rfl | rfl
  · exact CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide) blk h₂
  · exact CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide) blk h₂

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: the start, and what the pieces after it keep, for
constant time

Untrusted: everything here is checked by Lean. The arguments and `esp` are
public (`pubOf`); from them, `seal` and `open` start (`Top`), the entry and
`Ctr₀` are constant time (`start_ct`), and after them each piece keeps `Run`,
from which the next one's precondition follows.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt tglO tpO)
open VG.Proof.AesGcm.X86 (CT w64 slotv argA argsR argA_contains ofNat_toNat32 length_bytesAt)

/-- What is public: `esp` and the arguments. -/
def pubOf (s : State) : BitVec 32 × (Nat → BitVec 32) := (s.gpr .esp, fun i => if i < 11 then arg s i else 0)

theorem pubOf_eq {s₁ s₂ : State} (h : onePub s₁ s₂) : pubOf s₁ = pubOf s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [pubOf, h₁, Prod.mk.injEq, true_and]
  funext i
  split
  · next hi => exact h₂ i hi
  · rfl

/-- `seal` and `open` from their arguments. -/
structure Top (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  args : Args s K W SP N A D T R nl al n tl
  sp : s.gpr .esp = SP
  a0 : arg s 0 = K
  a1 : arg s 1 = BitVec.ofNat 32 R
  a2 : arg s 2 = N
  a3 : arg s 3 = BitVec.ofNat 32 nl
  a4 : arg s 4 = A
  a5 : arg s 5 = BitVec.ofNat 32 al
  a6 : arg s 6 = D
  a7 : arg s 7 = BitVec.ofNat 32 n
  a8 : arg s 8 = T
  a9 : arg s 9 = BitVec.ofNat 32 tl
  a10 : arg s 10 = W

/-- `Top` for the public values `p`. -/
abbrev TopOf (p : BitVec 32 × (Nat → BitVec 32)) : State → Prop :=
  Top (p.2 0) (p.2 10) p.1 (p.2 2) (p.2 4) (p.2 6) (p.2 8) (p.2 1).toNat (p.2 3).toNat (p.2 5).toNat
    (p.2 7).toNat (p.2 9).toNat

theorem top_of {s : State}
    (h : Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat)
    {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubOf s = p) : TopOf p s := by
  subst hp
  simp only [pubOf, show (0 : Nat) < 11 from by decide, show (1 : Nat) < 11 from by decide,
    show (2 : Nat) < 11 from by decide, show (3 : Nat) < 11 from by decide, show (4 : Nat) < 11 from by decide,
    show (5 : Nat) < 11 from by decide, show (6 : Nat) < 11 from by decide, show (7 : Nat) < 11 from by decide,
    show (8 : Nat) < 11 from by decide, show (9 : Nat) < 11 from by decide, show (10 : Nat) < 11 from by decide,
    ↓reduceIte]
  exact ⟨h, rfl, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm,
    rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl⟩

/-! ## The start -/

theorem entry_ct {I : State → Prop} {W SP : BitVec 32}
    (h : ∀ s, I s → s.gpr .esp = SP ∧ arg s 10 = W ∧ Covers [argsR SP 11] (s.rd ++ s.wr) ∧
      SP.toNat + 4 + 4 * 11 ≤ 2 ^ 32) : CT I ccmEntry := by
  refine CT.seq (J := fun s => s.gpr .eax = W ∧ s.gpr .esp = SP)
    (CT.taint [.esp] (pin1 fun s h' => (h s h').1) (by taint_decide)) (fun s hs => ?_)
    (CT.taint [.eax, .esp] (pin2 fun _ h => h) (by taint_decide))
  obtain ⟨hSP, hW, rA, fa⟩ := h s hs
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 10) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.of_runBlock ⟨_, by crun [hSP, i₀], ?_, ?_⟩
  · rw [gpr_setReg_self, ← hSP]; exact hW
  · rw [gpr_setReg_of_ne _ _ (by decide), hSP]

theorem start_ct {K W SP N A D T : BitVec 32} {R nl al n tl : Nat} (L : Lay K W SP) (h13 : nl ≤ 13) :
    CT (Top K W SP N A D T R nl al n tl) (.seq ccmEntry ctrs) := by
  refine CT.seq (J := fun s₁ => ∃ s, Top K W SP N A D T R nl al n tl s ∧ Entered s W s₁)
    (entry_ct fun s hs => ⟨hs.sp, hs.a10, hs.args.args, hs.args.fa⟩)
    (fun s hs => WP.mono (entry_ok hs.a10 hs.args.perm.w (by rw [hs.sp]; exact hs.args.args)
      (by rw [hs.sp]; exact hs.args.argsW) (by rw [hs.sp]; exact hs.args.fa) L.fw) fun s₁ E => ⟨s, hs, E⟩)
    (ctrs_ct L h13 fun s₁ ⟨s, hs, E₀⟩ => ⟨⟨E₀.ebp, by rw [E₀.esp, hs.sp], hs.args.perm.of_eq E₀.rd E₀.wr⟩,
      by rw [E₀.slots (2, nonceO) (by simp), hs.a2], by rw [E₀.slots (3, nlenO) (by simp), hs.a3]⟩)

/-! ## What the pieces keep -/

/-- After the start, and the pieces after it. -/
structure Run (s₀ : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  env : Env K W SP s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  st : ∃ s₂, Started s₀ K W SP N A D T R nl al n tl s₂ ∧ Frame (mutR W SP D n) s₂.mem s.mem
  c0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s₀.mem (w64 N) nl) 0

section
variable {s₀ : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}

theorem Run.of_started {s₂ : State} (St : Started s₀ K W SP N A D T R nl al n tl s₂) :
    Run s₀ K W SP N A D T R nl al n tl s₂ :=
  ⟨St.env, St.rd, St.wr, ⟨s₂, St, Frame.refl _ _⟩, St.c0⟩

theorem Run.step {s : State} (h : Run s₀ K W SP N A D T R nl al n tl s) {s' : State} (E : Env K W SP s')
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) {rs : List Region} (f : Frame rs s.mem s'.mem) (hm : InMut W SP D n rs)
    (hc : ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) : Run s₀ K W SP N A D T R nl al n tl s' := by
  obtain ⟨s₂, St, f₂⟩ := h.st
  exact ⟨E, by rw [rd, h.rd], by rw [wr, h.wr], ⟨s₂, St, f₂.trans (frame_toMut f hm)⟩,
    by rw [Proof.AesGcm.X86.bytesAt_frame f hc (by decide), h.c0]⟩

theorem Run.slots {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s) :
    Slots W K R N A D T nl al n tl s.mem := by
  obtain ⟨s₂, St, f₂⟩ := h.st
  exact (St.mut Ar f₂).1

theorem Run.mac_pre {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s) :
    MacPre K W SP R N A D T nl al n tl s :=
  ⟨⟨h.env, h.slots Ar, Ar.aad.of_eq h.rd h.wr⟩,
    ⟨_, length_bytesAt _ _ _, h.c0⟩⟩

theorem Run.tag_pre {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s) :
    TagPre K W SP R s :=
  ⟨h.env, (h.slots Ar).ctx, (h.slots Ar).rounds,
    ⟨_, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13, h.c0⟩⟩

theorem Run.data_pre {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s)
    {y : Nat} (hy : y = 0 ∨ y = 96) : DataPre K W SP R D n y s :=
  ⟨h.env, (h.slots Ar).ctx, (h.slots Ar).rounds, (h.slots Ar).data, (h.slots Ar).len,
    ⟨_, ⟨Ar.lay, Ar.rounds, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13,
      by rw [length_bytesAt]; exact Ar.hn, Ar.n32, hy, h.c0, Ar.data.of_eq h.rd h.wr, by rw [h.wr]; exact Ar.dw,
      Ar.dk⟩⟩⟩

/-- After the MAC into `W + y`. -/
theorem Run.mac {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {Y : List Byte} {s' : State} (A' : Absorbed K W SP s y Y s') :
    Run s₀ K W SP N A D T R nl al n tl s' :=
  h.step A'.env A'.rd A'.wr A'.frame (inMut_macR W SP D n hy) (macR_c0 Ar.lay hy)

/-- After the tag at `W + y`. -/
theorem Run.tag {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {s' : State} (E : Env K W SP s') (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (f : Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, wC W, below SP 60] s.mem s'.mem) :
    Run s₀ K W SP N A D T R nl al n tl s' :=
  h.step E rd wr f (inMut_tag W SP D n hy) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · rcases hy with rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm

/-- After the data. -/
theorem Run.afterData {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {s' : State} (E : Env K W SP s') (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (f : Frame (ctrR W SP D n y) s.mem s'.mem) : Run s₀ K W SP N A D T R nl al n tl s' := by
  obtain ⟨_, _, _, _, _, _, C⟩ := h.data_pre Ar hy
  exact h.step E rd wr f (inMut_ctrR W SP D n hy) (C.disj (.inl (by decide)))

/-- The MAC of the nonce and the associated data, and the data: constant time
(`macPre_ct`, `data_ct`), and what they keep. -/
theorem Run.macData (v : Ctr32Impl) {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl)
    (h : Run s₀ K W SP N A D T R nl al n tl s) {y : Nat} (hy : y = 0 ∨ y = 96) (enc : Bool) :
    WP isa (macPre v.callee v.suffix y) s (fun s' => Run s₀ K W SP N A D T R nl al n tl s') ∧
      WP isa (data v.callee v.suffix enc y) s (fun s' => Run s₀ K W SP N A D T R nl al n tl s') := by
  refine ⟨WP.mono (macPre_ok v Ar.lay h.env Ar.rounds (h.slots Ar) (length_bytesAt _ _ _) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.al32 Ar.hn Ar.n32 h.c0 hy (Ar.aad.of_eq h.rd h.wr)) fun _ A' => h.mac Ar hy A', ?_⟩
  obtain ⟨E, hK, hRo, hDp, hlen, nonce, C⟩ := h.data_pre Ar hy
  exact WP.mono (data_ok v enc C E hK hRo hDp hlen) fun _ P => h.afterData Ar hy P.env P.rd P.wr P.frame

end

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: `vg_aes_ccm_seal` is constant time

Untrusted: everything here is checked by Lean. From the public values (the
arguments and `esp`), the start, the MAC, the tag, counter mode, the tag
copied out and the exit are each constant time (`seal_top_ct`); so is `seal`
(`seal_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (restore)
open VG.Proof.AesGcm.X86 (CT w64 length_bytesAt)

/-- `seal` from its arguments: `Top`, with the tag writable. -/
structure SealTop (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop
    extends Top K W SP N A D T R nl al n tl s where
  tw : Covers [⟨w64 T, tl⟩] s.wr

theorem seal_top_of {s : State} (h : sealPre s) {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubOf s = p) :
    SealTop (p.2 0) (p.2 10) p.1 (p.2 2) (p.2 4) (p.2 6) (p.2 8) (p.2 1).toNat (p.2 3).toNat (p.2 5).toNat
      (p.2 7).toNat (p.2 9).toNat s := by
  refine ⟨top_of (args_of_seal h) hp, ?_⟩
  subst hp
  simp only [pubOf, show (8 : Nat) < 11 from by decide, show (9 : Nat) < 11 from by decide, ↓reduceIte]
  exact tag_wr h

theorem seal_top_ct (v : Ctr32Impl) {K W SP N A D T : BitVec 32} {R nl al n tl : Nat} (z : State)
    (Tz : SealTop K W SP N A D T R nl al n tl z) :
    CT (SealTop K W SP N A D T R nl al n tl) («seal» v.callee v.suffix) := by
  have Ar := Tz.args
  have L := Ar.lay
  have h7' : ∀ m : Mem, 7 ≤ (bytesAt m (w64 N) nl).length := fun m => by rw [length_bytesAt]; exact Ar.h7
  have h13' : ∀ m : Mem, (bytesAt m (w64 N) nl).length ≤ 13 := fun m => by rw [length_bytesAt]; exact Ar.h13
  refine RelCT.assoc (CT.seq (J := fun s => ∃ s₀, SealTop K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((start_ct L Ar.h13).mono fun s hs => hs.toTop) (fun s hs => WP.mono (start_ok hs.args hs.sp hs.a0 hs.a1 hs.a2 hs.a3 hs.a4 hs.a5 hs.a6 hs.a7
      hs.a8 hs.a9 hs.a10) fun _ St => ⟨s, hs, Run.of_started St⟩) ?_)
  -- The MAC of the nonce and the associated data, and the data.
  refine CT.seq (J := fun s => ∃ s₀, SealTop K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((macPre_ct v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 (.inl rfl)).mono
      fun s ⟨_, Tp, h⟩ => h.mac_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (h.macData v Tp.args (.inl rfl) true).1 fun _ h' => ⟨s₀, Tp, h'⟩) ?_
  refine CT.seq (J := fun s => ∃ s₀, SealTop K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((data_ct v L Ar.rounds (.inl rfl) Ar.n32 true).mono fun s ⟨_, Tp, h⟩ => h.data_pre Tp.args (.inl rfl))
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (h.macData v Tp.args (.inl rfl) true).2 fun _ h' => ⟨s₀, Tp, h'⟩) ?_
  -- The tag.
  refine CT.seq (J := fun s => ∃ s₀, SealTop K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((tag_ct v L Ar.rounds (.inl rfl)).mono fun s ⟨_, Tp, h⟩ => h.tag_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (tag_ok v L h.env Ar.rounds (h.slots Tp.args).ctx (h.slots Tp.args).rounds (h7' _)
      (h13' _) h.c0 (.inl rfl)) fun _ ⟨E, rd, wr, f, _⟩ => ⟨s₀, Tp, h.tag Tp.args (.inl rfl) E rd wr f⟩) ?_
  -- The tag copied out.
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (tagOut_ct L fun s ⟨_, Tp, h⟩ => ⟨h.env, (h.slots Tp.args).tl, (h.slots Tp.args).tp⟩)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (tagOut_ok L h.env (h.slots Tp.args).tl (h.slots Tp.args).tp
      (by have := Ar.t4; omega_using [this]) Ar.t16 (Tp.args.tag.of_eq h.rd h.wr) (by rw [h.wr]; exact Tp.tw))
      fun _ ⟨_, E, _, _⟩ => E.ebp) ?_
  -- The exit.
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

theorem seal_ct (v : Ctr32Impl) : ConstantTime isa sealX86.pre sealX86.pub («seal» v.callee v.suffix) :=
  CT.constantTime pubOf (fun _ _ _ _ h => pubOf_eq h) fun p => by
    by_cases hex : ∃ s, sealX86.pre s ∧ pubOf s = p
    · obtain ⟨z, hz, hp⟩ := hex
      exact (seal_top_ct v z (seal_top_of hz hp)).mono fun s hs => seal_top_of hs.1 hs.2
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

end VG.Proof.AesCcm.X86
