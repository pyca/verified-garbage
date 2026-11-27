module

public import VerifiedGarbage.Proof.AesCcm.X86_64.Args
public import VerifiedGarbage.Proof.AesCcm.Ctr
public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesCcm.X86_64.Mac
import VerifiedGarbage.Proof.AesCcm.X86_64.Crypt
import VerifiedGarbage.Proof.AesCcm.X86_64.Tag
import VerifiedGarbage.Proof.AesCcm.X86_64.Ctrs
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.AesCcm.X86_64
public import VerifiedGarbage.Proof.AesCcm.X86_64.Env
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Spec.Ccm
import VerifiedGarbage.Proof.AesGcm.X86_64.CopyTag
public import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
import VerifiedGarbage.Proof.Cmac.Frame

/-! ### `AesCcm.X86_64.Cmp`, which this module and modules that import it used -/

section

/-!
# AES-CCM on x86-64: checking a received tag (`recv`, `cmp o`)

Untrusted: everything here is checked by Lean. These are AES-GCM's pieces,
with AES-CCM's working space: `recv` pads the `rbx` bytes of the received
tag at `rsi` with zeros at `W + 256` (`recv_ok`); `cmp o` pads the first `rbx`
bytes of the tag at `W + o` at `W + 240` and leaves 1 in `rax` if they are
the received ones, 0 if not (`cmp_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

variable [fp : Footprint]

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr recv cmp vO rO copyLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre copyTag_ok)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Proof.Cmac (le8)

omit fp in
/-- `xs` written over 16 zero bytes at `P`. -/
theorem pad_bytes (m : Mem) (P : Addr) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes ((m.writeW P (0 : BitVec 64)).writeW (P + BitVec.ofNat 64 8) (0 : BitVec 64)) P xs) P 16 =
      xs ++ zeros (16 - xs.length) := by
  have h := bytesAt_writeBytes_at ((m.writeW P (0 : BitVec 64)).writeW (P + BitVec.ofNat 64 8) (0 : BitVec 64)) P
    (o := 0) (n := 16) xs (by omega_using [hx]) (by decide)
  rw [BitVec.add_zero] at h
  rw [h, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero, List.take_zero, List.nil_append, Nat.zero_add]
  show xs ++ (Spec.Cmac.zeros 16).drop xs.length = _
  simp only [Spec.Cmac.zeros, List.drop_replicate, zeros]

omit fp in
theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun l => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  simp only [Proof.Cmac.getD_le8 _ (show i / 8 < 8 by omega_using [hi]), BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega_using [], decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega_using []] at e
  exact e

omit fp in
/-- Two blocks are equal iff the OR of the XORs of their words is 0. -/
theorem words_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)
      = 0) ↔ bytesAt m p 16 = bytesAt m q 16 := by
  rw [Proof.Cmac.bytesAt_split m p, Proof.Cmac.bytesAt_split m q, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW]
  constructor
  · intro h
    have h₁ : m.readW p 64 ^^^ m.readW q 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    have h₂ : m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    rw [BitVec.xor_eq_zero_iff.mp h₁, BitVec.xor_eq_zero_iff.mp h₂]
  · intro h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Proof.Cmac.length_le8, Proof.Cmac.length_le8])
    rw [le8_inj h₁, le8_inj h₂, BitVec.xor_self, BitVec.xor_self, BitVec.or_self]; rfl

omit fp in
theorem zero16_frame (m : Mem) (p : Addr) :
    Frame [⟨p, 16⟩] m ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) :=
  Proof.Cmac.frame_store2 _ _ _

omit fp in
theorem writeBytes_frame' (m : Mem) {q : Addr} {xs : List Byte} {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (writeBytes m q xs) :=
  writeBytes_frame m q xs (by rw [hn]; exact Region.contains_self _ _)

section
variable {K W SP : Addr} (L : Lay K W SP)
include L

omit L in
omit fp in
/-- `recv`: the `t` bytes of the received tag at `T` (in `rsi`), padded at `W + 256`. -/
theorem recv_ok {s : State} (he : Env K W SP s) {t : Nat} (hbx : s.gpr .rbx = BitVec.ofNat 64 t)
    (h1 : 1 ≤ t) (h16 : t ≤ 16) {T : Addr} (hsi : s.gpr .rsi = T) (hT : Covers [⟨T, t⟩] (s.rd ++ s.wr))
    (dW : (⟨T, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩) :
    WP isa recv s fun s' => Env K W SP s' ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s.mem T t ++ zeros (16 - t) ∧
      Frame [⟨W + BitVec.ofNat 64 256, 16⟩] s.mem s'.mem ∧ s'.gpr .rbx = s.gpr .rbx ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h15 := he.r15
  have w₁ := he.perm.wW (show 256 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 264 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hdi, hsi₁, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r15 rO) .rax, .store (at_ .r15 (rO + 8)) .rax] ++
        ptr .rdi .r15 rO ++ [.mov .rcx (.reg .rbx)]) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .rdi = W + BitVec.ofNat 64 256 ∧ s₁.gpr .rsi = T ∧ s₁.gpr .rcx = BitVec.ofNat 64 t ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [rO, h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, hsi]
    · simp [gpr_setReg, hbx]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env K W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have lp : LoopPre s₁ T (W + BitVec.ofNat 64 256) t :=
    ⟨hsi₁, hdi, hcx, h1, by omega_using [h16], by rw [hrd₁, hwr₁]; exact hT, he₁.perm.wC (by omega_using [h16]),
      dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (copyTag_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_
  have fz : Frame [⟨W + BitVec.ofNat 64 256, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact zero16_frame _ _
  have hR : bytesAt s₁.mem T t = bytesAt s.mem T t :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW) (by omega_using [h16])
  have hlen := length_bytesAt s₁.mem T t
  refine ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂, ?_, ?_, ?_,
    by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
  · rw [hm₂, hm₁, pad_bytes _ _ _ (by rw [length_bytesAt]; exact h16), length_bytesAt, ← hm₁, hR]
  · refine fz.trans ?_
    rw [hm₂]
    exact (writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  · rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide)]

omit fp in
/-- `cmp o`: 1 in `rax` iff the first `t` bytes of the tag at `W + o` are
the received tag `T`, padded at `W + 256`. -/
theorem cmp_ok {o : Nat} (ho : o + 16 ≤ 240) {s : State} (he : Env K W SP s) {t : Nat}
    (hbx : s.gpr .rbx = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16) {T : List Byte} (hTl : T.length = t)
    (hT : bytesAt s.mem (W + BitVec.ofNat 64 256) 16 = T ++ zeros (16 - t)) :
    WP isa (cmp o) s fun s' => Env K W SP s' ∧
      s'.gpr .rax = (if bytesAt s.mem (W + BitVec.ofNat 64 o) t = T then 1 else 0) ∧
      Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h15 := he.r15
  have w₁ := he.perm.wW (show 240 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 248 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r15 vO) .rax, .store (at_ .r15 (vO + 8)) .rax] ++
        ptr .rdi .r15 vO ++ ptr .rsi .r15 o ++ [.mov .rcx (.reg .rbx)]) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .rdi = W + BitVec.ofNat 64 240 ∧ s₁.gpr .rsi = W + BitVec.ofNat 64 o ∧
      s₁.gpr .rcx = BitVec.ofNat 64 t ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have hoi : o < 2 ^ 31 := by omega
    refine ⟨_, by crun [vO, h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, h15, imm_eq hoi]
    · simp [gpr_setReg, hbx]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env K W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have dW : (⟨W + BitVec.ofNat 64 o, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 240, 16⟩ :=
    L.w_w (.inl (by omega)) (by omega) (by decide)
  have lp : LoopPre s₁ (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 240) t :=
    ⟨hsi, hdi, hcx, h1, by omega, covers_left (he₁.perm.wC (by omega)), he₁.perm.wC (by omega),
      dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.seq (WP.mono (copyTag_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_)
  have fz : Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact zero16_frame _ _
  have hT' : bytesAt s₁.mem (W + BitVec.ofNat 64 o) t = bytesAt s.mem (W + BitVec.ofNat 64 o) t :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW) (by omega)
  have hlen := length_bytesAt s₁.mem (W + BitVec.ofNat 64 o) t
  have f₂ : Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s₂.mem := by
    refine fz.trans ?_
    rw [hm₂]
    exact (writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  have hV : bytesAt s₂.mem (W + BitVec.ofNat 64 240) 16 =
      bytesAt s.mem (W + BitVec.ofNat 64 o) t ++ zeros (16 - t) := by
    rw [hm₂, hm₁, pad_bytes _ _ _ (by rw [length_bytesAt]; exact h16), length_bytesAt, ← hm₁, hT']
  have hT₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 256) 16 = T ++ zeros (16 - t) := by
    rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide), hT]
  have he₂ : Env K W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂
  have r₁ := he₂.perm.wR (show 240 + 8 ≤ 2560 by decide)
  have r₂ := he₂.perm.wR (show 256 + 8 ≤ 2560 by decide)
  have r₃ := he₂.perm.wR (show 248 + 8 ≤ 2560 by decide)
  have r₄ := he₂.perm.wR (show 264 + 8 ≤ 2560 by decide)
  have h15₂ := he₂.r15
  generalize hX : (s₂.mem.readW (W + BitVec.ofNat 64 240) 64 ^^^ s₂.mem.readW (W + BitVec.ofNat 64 256) 64) |||
    (s₂.mem.readW (W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) 64 ^^^
      s₂.mem.readW (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) 64) = X
  have hXe : X = 0 ↔ bytesAt s.mem (W + BitVec.ofNat 64 o) t = T := by
    rw [← hX, words_eq, hV, hT₂]
    constructor
    · intro e; exact List.append_cancel_right e
    · intro e; rw [e]
  have e248 : W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 248 := add_ofNat_assoc ..
  have e264 : W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 264 := add_ofNat_assoc ..
  rw [e248, e264] at hX
  obtain ⟨s₃, run₃, hax, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      [.mov .rax (.mem (at_ .r15 vO)), .alu .xor .rax (.mem (at_ .r15 rO)),
        .mov .rdx (.mem (at_ .r15 (vO + 8))), .alu .xor .rdx (.mem (at_ .r15 (rO + 8))),
        .alu .or .rax (.reg .rdx), .alu .cmp .rax (imm 1), .mov32 .rax (imm 0), .alu32 .adc .rax (imm 0)] s₂ =
        some s₃ ∧ s₃.gpr .rax = (if X = 0 then 1 else 0) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], s₃.gpr r = s₂.gpr r) ∧
      s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [vO, rO, h15₂, r₁, r₂, r₃, r₄, execAlu32], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, cf_setReg, cf_arithFlags, ite_true, ite_false, reduceCtorEq, hX]
      by_cases e : X = 0
      · subst e; rfl
      · have : ¬ X.toNat < 1 := fun h => e (BitVec.eq_of_toNat_eq (by simp; omega))
        simp only [e, ite_false, show (1#64 : BitVec 64).toNat = 1 from rfl, this, decide_false]
        rfl
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  exact WP.of_runBlock ⟨s₃, run₃, he₂.keep hg₃ hrd₃ hwr₃, by rw [hax]; simp only [hXe], hm₃ ▸ f₂,
    by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁]⟩

end

end VG.Proof.AesCcm.X86_64

end

end

/-!
# AES-CCM on x86-64: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `mac y` followed by `tag y`
leaves the MAC of the payload at `D`, encrypted, at `W + y` (`macTag_ok`).
`seal` is `entry`, `Ctr₀` (`ctrs`), the encrypted MAC at `W`, counter mode
over the data (`ctr`), the tag copied to `tag` (`tagOut_ok`) and `restore`
(`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

variable [fp : Footprint]

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre copyTag_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

/-- What `mac y` and `tag y` write. -/
abbrev tagR (W SP : Addr) (y : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩,
    ⟨W + BitVec.ofNat 64 384, scratchBytes⟩, below SP 16]

theorem tagR_wR (W SP : Addr) {y : Nat} (hy : y + 16 ≤ 112) : ∀ r ∈ tagR W SP y, ∃ r' ∈ wR W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨wA W, by simp, Offset.sub_base W hy⟩
  · exact ⟨wC W, by simp, scratch_sub_tail W⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The MAC of the payload at `D`, encrypted with `CIPH_K(Ctr₀)`, at `W + y`. -/
theorem macTag_ok (v : UpdateImpl) [UpdateFits v] {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13)
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96)
    (hA : Buf K W SP s A al) (hD : Buf K W SP s D n) {Q : State → Prop}
    (hk : ∀ s', Env K W SP s' → s'.rd = s.rd → s'.wr = s.wr → Frame (tagR W SP y) s.mem s'.mem →
      bytesAt s'.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 →
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 0
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (Spec.Cmac.zeros 16)
          (Spec.Ccm.format tl nonce (bytesAt s.mem A al) (bytesAt s.mem D n))) → Q s') :
    WP isa (.seq (mac v.callee y) (tag v.ctr.callee y)) s Q := by
  obtain hy16 : y + 16 ≤ 112 := by omega_arith
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> subst h <;> decide
  refine WP.seq (WP.mono (mac_ok v L E S hR hnl h7 h13 ht4 ht16 hte hn hc0 hy hA hD) fun s₁ M => ?_)
  obtain fy : Frame (tagR W SP y) s.mem s₁.mem := M.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  obtain hRo₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [rounds_kept L hy M.frame]; exact S.rounds
  obtain hc₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [bytesAt_frame M.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rcases hy with rfl | rfl
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by have := tailBytes_le; have := scratchBytes_le; omega)
      · exact (L.stk_w' (by decide)).symm) (by decide), hc0]
  refine WP.mono (tag_ok v.ctr L M.env hR hRo₁ (by omega_arith) (by omega_arith) hc₁ hy)
    fun s₂ ⟨E₂, _, rd₂, wr₂, f₂, h₂⟩ => ?_
  refine hk s₂ E₂ (by rw [rd₂, M.rd]) (by rw [wr₂, M.wr]) (fy.trans (f₂.sub fun r hr => ?_)) ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rcases hy with rfl | rfl
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by have := tailBytes_le; have := scratchBytes_le; omega)
      · exact (L.stk_w' (by decide)).symm) (by decide), hc₁]
  · rw [h₂, M.out, ctxCiph_frame M.frame (k_macR L (by omega_arith)) hRb]

/-- The return address is outside what the functions write. -/
theorem ret_disj {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) : ∀ r ∈ entryR W :: mutR W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Region.sub_prefix (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by have := tailBytes_le; have := scratchBytes_le; omega))
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega_arith)
  · exact hD

omit fp in
/-- `tagOut`: the first `tl` bytes at `W` copied to the tag `T`, whose
address is at `SP + 24`. -/
theorem tagOut_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (S : Slots W R N A D nl al n tl s.mem) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) {T : Addr}
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTw : Covers [⟨T, tl⟩] s.wr) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa tagOut s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem T (bytesAt s.mem W tl) := by
  have h15 := E.r15
  have hsp := E.rsp
  obtain rt := E.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have htl := S.tl
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rdi (.mem (at_ .rsp 24)), .mov .rsi (.reg .r15), .mov .rcx (.mem (at_ .r15 tlO))] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .rdi = T ∧ s₁.gpr .rsi = W ∧ s₁.gpr .rcx = BitVec.ofNat 64 tl ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, hsp, rt, hTr], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, hsp, hT]
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, htl]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain E₁ : Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  obtain lp : LoopPre s₁ W T tl :=
    ⟨hsi, hdi, hcx, by omega_arith, by omega_arith, covers_left (by simpa using E₁.perm.wC (d := 0) (n := tl) (by omega_arith)),
      by rw [hwr₁]; exact hTw, (hTW.sub_right (Region.sub_prefix (by omega_arith))).symm⟩
  refine WP.mono (copyTag_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ⟨E₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂,
    by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁], by rw [hm₂, hm₁]⟩

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp'_frame (v : UpdateImpl) [UpdateFits v] {s : State} {K W SP N A D T : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (Tb : TagBuf W SP D n T tl) (hTw : Covers [⟨T, tl⟩] s.wr)
    (hTr : (⟨SP, 8⟩ : Region).Disjoint ⟨T, tl⟩) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («seal» v.callee v.ctr.callee) s fun s' => (gprPreserved s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem D n)
        (bytesAt s.mem A al) = (bytesAt s'.mem D n, bytesAt s'.mem T tl)) ∧ EntryFrame s s' W SP D n T tl := by
  have L := Ar.lay
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, E₁, S₁, sv₁, f₁, rd₁, wr₁⟩ :=
    entry_ok Ar.perm hsp Ar.args Ar.argsW hD hn hW htl hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_arith)
  obtain hK₁ : Spec.Ccm.ctxCiph s₁.mem K R = Spec.Ccm.ctxCiph s.mem K R :=
    ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  refine WP.seq ?_
  -- `Ctr₀`.
  refine WP.seq (WP.mono (ctrs_ok E₁ S₁ (Ar.nonce.of_eq rd₁ wr₁) Ar.h7 Ar.h13) fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  obtain f₂' : Frame (wR W SP) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  obtain S₂ := slots_mut L Ar.data.w (f₂'.sub (wR_mut W SP D n)) S₁
  -- The encrypted MAC at `W`.
  refine seq_assoc (WP.seq (macTag_ok v L E₂ S₂ Ar.rounds (length_bytesAt _ _ _) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.hn c₂ (y := 0) (.inl rfl) (Ar.aad.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁))
    (Ar.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)) fun s₃ E₃ rd₃ wr₃ f₃ c₃ h₃ => ?_))
  obtain f₁₃ : Frame (wR W SP) s₁.mem s₃.mem := f₂'.trans (f₃.sub (tagR_wR W SP (by decide)))
  obtain S₃ := slots_mut L Ar.data.w (f₁₃.sub (wR_mut W SP D n)) S₁
  -- Counter mode.
  obtain C₃ : CtrCtx K W SP s₃ R (bytesAt s.mem N nl) D n :=
    ⟨L, Ar.rounds, S₃.rounds, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13,
      by rw [length_bytesAt]; exact Ar.hn, c₃, Ar.data.of_eq (rd₃.trans (rd₂.trans rd₁)) (wr₃.trans (wr₂.trans wr₁)),
      by rw [wr₃, wr₂, wr₁]; exact Ar.dw, Ar.dk⟩
  refine WP.mono (ctr_ok v.ctr C₃ E₃ S₃) fun s₄ ⟨E₄, rd₄, wr₄, f₄, h₄⟩ => ?_
  obtain f₁₄ : Frame (mutR W SP D n) s₁.mem s₄.mem := (f₁₃.sub (wR_mut W SP D n)).trans (f₄.sub (ctrR_mut W SP D n))
  obtain fall : Frame (entryR W :: mutR W SP D n) s.mem s₄.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (f₁₄.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  obtain rd₀₄ : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  obtain wr₀₄ : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  -- The tag copied to `T`.
  obtain hT₄ : s₄.mem.readW (SP + BitVec.ofNat 64 24) 64 = T := by rw [argT_kept fall Ar.argsW Ar.argsD, hT]
  obtain hTr₄ : InRegions (s₄.rd ++ s₄.wr) (SP + BitVec.ofNat 64 24) 8 := by
    obtain h := in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [rd₀₄, wr₀₄]; exact h
  refine WP.seq (WP.mono (tagOut_ok E₄ (slots_mut L Ar.data.w f₁₄ S₁) Ar.t4 Ar.t16 hT₄ hTr₄
    (by rw [wr₀₄]; exact hTw) Tb.w) fun s₅ ⟨E₅, rd₅, wr₅, hm₅⟩ => ?_)
  obtain hx : (bytesAt s₄.mem W tl).length = tl := length_bytesAt _ _ _
  obtain f₅ : Frame [⟨T, tl⟩] s₄.mem s₅.mem := by rw [hm₅]; exact writeBytes_frame' _ hx
  -- `restore`.
  obtain sv₅ : Saved s₅.mem W s.gpr := fun p hp => by
    rw [← saved_mut L Ar.data.w f₁₄ sv₁ p hp]
    obtain hd : 112 ≤ p.2 ∧ p.2 + 8 ≤ 160 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact f₅.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Tb.w.sub_right (Lay.wSub (by omega_arith))).symm) (by decide)
  obtain ⟨s₆, run₆, hg₆, hm₆, hsp₆, _⟩ := restore_ok E₅ sv₅
  refine WP.of_runBlock ⟨s₆, run₆, ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₆ (.rbx, 112) (by decide)
    · exact hg₆ (.rbp, 120) (by decide)
    · rw [hsp₆, E₅.rsp, hsp]
    · exact hg₆ (.r12, 128) (by decide)
    · exact hg₆ (.r13, 136) (by decide)
    · exact hg₆ (.r14, 144) (by decide)
    · exact hg₆ (.r15, 152) (by decide)
  · rw [hm₆, hsp, f₅.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hTr) (by decide)]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The ciphertext and the tag.
    obtain hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m K R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
    obtain c₂' : Spec.Ccm.ctxCiph s₂.mem K R = Spec.Ccm.ctxCiph s.mem K R := by
      rw [ciph_mut L Ar.dk Ar.rounds (f₂'.sub (wR_mut W SP D n)), hK₁]
    obtain c₃' : Spec.Ccm.ctxCiph s₃.mem K R = Spec.Ccm.ctxCiph s.mem K R := by
      rw [ciph_mut L Ar.dk Ar.rounds (f₁₃.sub (wR_mut W SP D n)), hK₁]
    obtain a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := by rw [buf_wR Ar.aad f₂', hent Ar.aad]
    obtain d₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [buf_wR Ar.data f₂', hent Ar.data]
    obtain d₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by rw [buf_wR Ar.data f₁₃, hent Ar.data]
    obtain w₄ : bytesAt s₄.mem W tl = bytesAt s₃.mem W tl := bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · simpa using L.w_w (a := 0) (n := tl) (d := 64) (k := 32) (.inl (by have := Ar.t16; omega_arith))
          (by have := Ar.t16; omega_arith) (by decide)
      · simpa using L.w_w (a := 0) (n := tl) (d := 216) (k := 8) (.inl (by have := Ar.t16; omega_arith))
          (by have := Ar.t16; omega_arith) (by decide)
      · simpa using L.w_w (a := 0) (n := tl) (d := 384) (k := scratchBytes) (.inl (by have := Ar.t16; omega_arith))
          (by have := Ar.t16; omega_arith) (by have := tailBytes_le; have := scratchBytes_le; omega)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by have := Ar.t16; omega_arith))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by have := Ar.t16; omega_arith))).symm) (by have := Ar.t16; omega_arith)
    obtain d₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n :=
      bytesAt_frame f₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Tb.d.symm) (by have := Ar.data.lt; omega_arith)
    obtain t₅ : bytesAt s₅.mem T tl = bytesAt s₄.mem W tl := by
      obtain e := bytesAt_writeBytes_at s₄.mem T (o := 0) (n := tl) (bytesAt s₄.mem W tl) (by rw [hx]; omega_arith)
        (by have := Ar.t16; omega_arith)
      rw [BitVec.add_zero, List.take_zero, List.nil_append, Nat.zero_add,
        List.drop_eq_nil_of_le (by rw [length_bytesAt, hx]), List.append_nil] at e
      rw [hm₅, e]
    obtain e0 : W + BitVec.ofNat 64 0 = W := BitVec.add_zero W
    rw [e0] at h₃
    obtain hY := congrArg List.length h₃
    rw [length_bytesAt, length_xorFrom] at hY
    simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hm₆, d₅, h₄, c₃', d₃, crypt_eq (hBC _)]
    · rw [hm₆, t₅, w₄, bytesAt_prefix s₃.mem W Ar.t16, h₃, take_xorFrom_zero (hBC _) _ hY.symm Ar.t16,
        ← mac_eq _ _ (by rw [length_bytesAt]; have := Ar.h13; omega_arith), c₂', a₂, d₂]

  · obtain ⟨tp, p, ep, ap, mp⟩ := entryRestore_run run₁ E₁ sv₁ hsp
      (f₁.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hsp]; exact Ar.retW.sub_right (Lay.wSub (by decide))) (by decide))
    refine ⟨tp, p, ep, ap, ?_⟩
    rw [mp, hm₆]
    exact (f₁₄.mono (List.subset_append_left ..)).trans
      (f₅.mono (List.subset_append_right ..))

/-- `vg_aes_ccm_seal`. -/
theorem seal_wp_frame (v : UpdateImpl) [UpdateFits v] {s : State} (h : sealX86_64.pre s) :
    WP isa («seal» v.callee v.ctr.callee) s fun s' => (gprPreserved s s' ∧ sealX86_64.post s s') ∧
      EntryFrame s s' (stackArg s 4) (s.gpr .rsp) (stackArg s 0) (stackArg s 1).toNat
        (stackArg s 2) (stackArg s 3).toNat :=
  have A := args_of_seal h
  seal_wp'_frame v A.1.1 A.1.2 A.2.1 A.2.2 rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

theorem seal_wp (v : UpdateImpl) [UpdateFits v] {s : State} (h : sealX86_64.pre s) :
    WP isa («seal» v.callee v.ctr.callee) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' :=
  WP.mono (seal_wp_frame v h) (fun _ h => h.1)

end VG.Proof.AesCcm.X86_64
