module

public import VerifiedGarbage.Proof.AesSiv.Scratch
public import VerifiedGarbage.Proof.AesSiv.X86.Init
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.AesSiv.X86.Dec
import VerifiedGarbage.Proof.CmacAes.X86.Verified
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesSiv.X86.FinishCT
import VerifiedGarbage.Proof.AesSiv.X86.Finish
import VerifiedGarbage.Proof.AesSiv.X86.Run
meta import VerifiedGarbage.Proof.AesSiv.X86.Dec
meta import VerifiedGarbage.Proof.AesSiv.X86.FinishCT
meta import VerifiedGarbage.Proof.AesSiv.X86.Finish
meta import VerifiedGarbage.Proof.AesSiv.X86.Run
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops

/-! ### `AesSiv.X86.EncCT`, which only this module used -/

section

/-! ### `AesSiv.X86.CtrCT`, which only this module used -/

section

/-!
# AES-SIV on x86: CTR is constant time

Untrusted: everything here is checked by Lean. The branches of `ctr` are on
the length of the data, and the addresses on `ebp` and the data's address
(pinned where the XOR uses them); the calls of `vg_aes_ctr32_to` are constant
time by their contract.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop)
open VG.Proof.AesGcm.X86 (w64 slotv CT xorLoop_ct)

/-- What CTR starts from, but the counter: the data and its slots. -/
structure CtrPre (C W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env C W SP s
  dat : Dat C W SP s D n
  n32 : n < 2 ^ 32
  ctx : slotv s.mem W ctxO = C
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  data : slotv s.mem W dataO = D
  len : slotv s.mem W lenO = BitVec.ofNat 32 n

theorem ctrWhole_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat} :
    CT (CtrPre C W SP R D n) (ctrWhole v.callee) := by
  refine CT.block_seq [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => whole1_ok L hs.env hs.len hs.n32) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun s ⟨_, _, _, zf, _⟩ => eval_e zf) (fun _ => CT.nil) (fun _ => ?_)
  refine CT.block_seq [.ebp] (pin_ebp fun s₁ ⟨s, hs, _, _, g, _⟩ => by rw [g _ (by decide), hs.env.ebp])
    (by taint_decide) (fun s₁ ⟨s, hs, _, _, g, m, rd, wr⟩ =>
      ctrArgs_ok (C := C) (R := R) (D := D) L ⟨by rw [g _ (by decide), hs.env.ebp],
        by rw [g _ (by decide), hs.env.esp], hs.env.perm.of_eq rd wr⟩
        (by rw [m]; exact hs.ctx) (by rw [m]; exact hs.rounds) (by rw [m]; exact hs.data)) ?_
  exact ctrCall_ct v L hR (c := cbOff) (by decide) (D := D) (n := n / 16)
    fun s₂ ⟨s₁, ⟨s, hs, di₁, _, g₁, _, rd₁, wr₁⟩, ax, cx, dx, bx, g₂, _, rd₂, wr₂⟩ =>
      ⟨⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), hs.env.ebp],
        by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), hs.env.esp],
        hs.env.perm.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)⟩,
        (hs.dat.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)).dst (Nat.mul_div_le n 16) (by decide),
        ax, cx, dx, bx, by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), di₁]⟩

theorem tailArgs_ct {W : BitVec 32} {I : State → Prop} (hI : ∀ s, I s → s.gpr .ebp = W) :
    CT I (.block (zero4 ksOff ++ ctrArgs ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksOff),
      .mov .edi (imm 1)] : List Instr))) :=
  CT.taint [.ebp] (pin_ebp hI) (by taint_decide)

theorem ctrTail_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat} :
    CT (CtrPre C W SP R D n) (ctrTail v.callee) := by
  refine CT.block_seq [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => tail1_ok L hs.env hs.len hs.n32) ?_
  refine CT.ite (decide (n % 16 = 0)) (fun s ⟨_, _, _, zf, _⟩ => eval_e zf) (fun _ => CT.nil) (fun _ => ?_)
  -- After the call: the data and its slots.
  have pre₁ : ∀ s₁, (∃ s, CtrPre C W SP R D n s ∧ s₁.gpr .ecx = BitVec.ofNat 32 (n % 16) ∧
      s₁.zf = some (decide (n % 16 = 0)) ∧ (∀ r, r ≠ .ecx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr) → CtrPre C W SP R D n s₁ := fun s₁ ⟨s, hs, _, _, g, m, rd, wr⟩ =>
    ⟨⟨by rw [g _ (by decide), hs.env.ebp], by rw [g _ (by decide), hs.env.esp], hs.env.perm.of_eq rd wr⟩,
      hs.dat.of_eq rd wr, hs.n32, by rw [m]; exact hs.ctx, by rw [m]; exact hs.rounds, by rw [m]; exact hs.data,
      by rw [m]; exact hs.len⟩
  refine CT.seq (J := fun s₂ => ∃ s₁, CtrPre C W SP R D n s₁ ∧
      s₂.mem = Cmac.zero4 s₁.mem (w64 W + BitVec.ofNat 64 ksOff) ∧
      s₂.gpr .eax = C + BitVec.ofNat 32 272 ∧ s₂.gpr .ecx = BitVec.ofNat 32 R ∧
      s₂.gpr .edx = W + BitVec.ofNat 32 cbOff ∧ s₂.gpr .ebx = W + BitVec.ofNat 32 ksOff ∧
      s₂.gpr .edi = BitVec.ofNat 32 1 ∧ s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr)
    (tailArgs_ct fun s₁ h₁ => (pre₁ s₁ h₁).env.ebp)
    (fun s₁ h₁ => let ⟨s₂, run₂, h₂⟩ := tailArgs_ok' (R := R) L (pre₁ s₁ h₁).env (pre₁ s₁ h₁).ctx (pre₁ s₁ h₁).rounds
      WP.of_runBlock ⟨s₂, run₂, s₁, pre₁ s₁ h₁, h₂⟩) ?_
  refine CT.seq (J := fun s₃ => CtrPre C W SP R D n s₃)
    (ctrCall_ct v L hR (c := cbOff) (by decide) (D := W + BitVec.ofNat 32 ksOff) (n := 1)
      fun s₂ ⟨s₁, h₁, _, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ =>
        have P₂ := h₁.env.perm.of_eq rd wr
        ⟨⟨bp, sp, P₂⟩, dstW L P₂ (by decide) (by decide) (by decide), ax, cx, dx, bx, di⟩)
    (fun s₂ ⟨s₁, h₁, m₂, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ =>
      have P₂ := h₁.env.perm.of_eq rd wr
      WP.mono (ctrCall_ok v L ⟨bp, sp, P₂⟩ hR (c := cbOff) (by decide) (n := 1)
        (dstW L P₂ (by decide) (by decide) (by decide)) ax cx dx bx di) fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, _⟩ => by
        have f : Frame (ctrR W SP D n) s₁.mem s₃.mem := by
          refine (show Frame (ctrR W SP D n) s₁.mem s₂.mem by
            rw [m₂]; exact (Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩).trans ?_
          rw [L.aW (o := ksOff) (by decide)] at f₃
          exact f₃.sub fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
            · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
            · exact ⟨_, by simp, fun _ h => h⟩
            · exact ⟨_, by simp, fun _ h => h⟩
        have sl := fun {o : Nat} (a : 112 ≤ o) (b : o + 4 ≤ 256) => ctrR_slot L h₁.dat f a b
        exact ⟨E₃, h₁.dat.of_eq (rd₃.trans rd) (wr₃.trans wr), h₁.n32,
          by rw [sl (by decide) (by decide)]; exact h₁.ctx, by rw [sl (by decide) (by decide)]; exact h₁.rounds,
          by rw [sl (by decide) (by decide)]; exact h₁.data, by rw [sl (by decide) (by decide)]; exact h₁.len⟩) ?_
  refine CT.block_seq [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => xorArgs_ok L hs.env hs.data hs.len hs.n32) ?_
  exact xorLoop_ct (pin3 fun s ⟨_, _, cx, dx, di, _⟩ => ⟨di, dx, cx⟩)

/-- `ctr` is constant time from the data and its slots, whatever the counter. -/
theorem ctr_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat} :
    CT (fun s => CtrPre C W SP R D n s ∧ Spec.Siv.beNat (bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16) % 2 ^ 32 <
      2 ^ 31) (ctr v.callee) :=
  CT.seq (J := CtrPre C W SP R D n) ((ctrWhole_ct v L hR).mono fun _ h => h.1)
    (fun s ⟨h, hlow⟩ => WP.mono (ctrWhole_ok v L hR h.env h.dat h.n32 h.ctx h.rounds h.data h.len rfl (by have := h.n32; omega_using [hlow, this]))
      fun s₄ ⟨E₄, rd₄, wr₄, f₄, _⟩ =>
        have sl := fun {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 256) => ctrR_slot L h.dat f₄ h₁ h₂
        ⟨E₄, h.dat.of_eq rd₄ wr₄, h.n32, by rw [sl (by decide) (by decide)]; exact h.ctx,
          by rw [sl (by decide) (by decide)]; exact h.rounds, by rw [sl (by decide) (by decide)]; exact h.data,
          by rw [sl (by decide) (by decide)]; exact h.len⟩)
    (ctrTail_ct v L hR)

end VG.Proof.AesSiv.X86

end

end

/-!
# AES-SIV on x86: `encrypt` and `decrypt` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public arguments and the same descriptors of the components (`ETop`) leak
the same. The entry's block reads the stack arguments, which are public;
between the pieces, the correctness lemmas give each run the next piece's
invariant (from `Kept` since the entry); `decrypt` compares the IVs and
masks the data without a branch, so nothing it does depends on the result.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot restore)
open VG.Proof.AesGcm.X86 (CT w64 slotv argA argsR argA_contains and_self_beq32)

/-- The entry, with the components' addresses and lengths `ca`, `cl`. -/
structure ETop (C W SP A D T : BitVec 32) (R N n : Nat) (ca : Nat → BitVec 32) (cl : Nat → Nat) (s : State) :
    Prop where
  pre : EPre C W SP A D T R N n s
  comps : ∀ j < N, compA s.mem A j = ca j ∧ compL s.mem A j = cl j

theorem sivEntry_ct {I : State → Prop} {W SP : BitVec 32}
    (h : ∀ s, I s → s.gpr .esp = SP ∧ arg s 7 = W ∧ Covers [argsR SP 8] (s.rd ++ s.wr) ∧
      SP.toNat + 4 + 4 * 8 ≤ 2 ^ 32) : CT I sivEntry := by
  refine CT.seq (J := fun s => s.gpr .eax = W ∧ s.gpr .esp = SP)
    (CT.taint [.esp] (pin1 fun s h' => (h s h').1) (by taint_decide)) (fun s hs => ?_)
    (CT.taint [.eax, .esp] (pin2 fun _ h => h) (by taint_decide))
  obtain ⟨hSP, hW, rA, fa⟩ := h s hs
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 7) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.of_runBlock ⟨_, by crun [hSP, i₀], ?_, ?_⟩
  · rw [gpr_setReg_self, ← hSP]; exact hW
  · rw [gpr_setReg_of_ne _ _ (by decide), hSP]

theorem dataStr_ct {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    CT I (.block [.mov .eax (slot dataO), .store (at_ .ebp strO) .eax, .mov .eax (slot lenO),
      .store (at_ .ebp slenO) .eax]) :=
  CT.taint [.ebp] (pin_ebp h) (by taint_decide)

/-- `encS2v` is constant time. -/
theorem encS2v_ct (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    (L : Lay C W SP) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hN : N < 2 ^ 32) (hcl : ∀ j < N, cl j < 2 ^ 32) :
    CT (ETop C W SP A D T R N n ca cl) (encS2v v.callee v.suffix) := by
  refine CT.seq (J := fun s₁ => ∃ s, ETop C W SP A D T R N n ca cl s ∧ Entered s W s₁)
    (sivEntry_ct fun s hs => ⟨hs.pre.sp, hs.pre.a7, hs.pre.rA, hs.pre.fa⟩)
    (fun s hs => WP.mono (entry_wp hs.pre) fun s₁ en => ⟨s, hs, en⟩) ?_
  refine CT.seq (J := fun s₂ => ∃ s, ETop C W SP A D T R N n ca cl s ∧ AInv s C W SP A R N D n 0 s₂)
    ((start_ct v L hR).mono fun s₁ ⟨s, hs, en⟩ =>
      let K := (kept_of_entered hs.pre en).1
      ⟨K.env, K.slots.ctx, K.slots.rounds⟩)
    (fun s₁ ⟨s, hs, en⟩ => WP.mono (start_wp v hs.pre en) fun s₂ I => ⟨s, hs, I⟩) ?_
  refine CT.seq (J := fun s₃ => ∃ s, ETop C W SP A D T R N n ca cl s ∧ AInv s C W SP A R N D n N s₃)
    ((s2vAds_ct v L hR hN hcl).mono fun s₂ ⟨s, hs, I⟩ => ⟨s, D, n, hs.pre.ads, hs.comps, I⟩)
    (fun s₂ ⟨s, hs, I⟩ => WP.mono (s2vAds_ok v hs.pre.ads I) fun s₃ I' => ⟨s, hs, I'⟩) ?_
  exact dataStr_ct fun s₃ ⟨_, _, I⟩ => I.kept.env.ebp

/-- After `encS2v`. -/
abbrev EOut (C W SP A D T : BitVec 32) (R N n : Nat) (ca : Nat → BitVec 32) (cl : Nat → Nat) (s : State) : Prop :=
  ∃ s₀, ETop C W SP A D T R N n ca cl s₀ ∧ S2vOut C W SP A D R N n s₀ s

theorem encS2v_wp (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    {s : State} (h : ETop C W SP A D T R N n ca cl s) :
    WP isa (encS2v v.callee v.suffix) s (EOut C W SP A D T R N n ca cl) :=
  WP.mono (encS2v_ok v h.pre) fun _ O => ⟨s, h, O⟩

/-- The pieces after `encS2v`: `Kept` since an entry, with the regions
`ext`. -/
abbrev EKept (C W SP A D T : BitVec 32) (R N n : Nat) (ca : Nat → BitVec 32) (cl : Nat → Nat) (ext : List Region)
    (s : State) : Prop :=
  ∃ s₀, ETop C W SP A D T R N n ca cl s₀ ∧ Kept s₀ C W SP R D n ext s

theorem EKept.ctrPre {C W SP A D T : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    {ext : List Region} {s : State} (h : EKept C W SP A D T R N n ca cl ext s) : CtrPre C W SP R D n s :=
  let ⟨_, T, K⟩ := h
  ⟨K.env, T.pre.data.of_eq K.rd K.wr, T.pre.n32, K.slots.ctx, K.slots.rounds, K.slots.data, K.slots.len⟩

theorem counter_ct {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    CT I (.block (counter 0)) :=
  CT.taint [.ebp] (pin_ebp h) (by taint_decide)

/-- The counter `Q` from the IV, and `Kept`: what CTR starts from. -/
theorem counter_wp {C W SP A D T : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    {ext : List Region} (hext : ∀ r ∈ ext, r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩) {s : State}
    (h : EKept C W SP A D T R N n ca cl ext s) :
    WP isa (.block (counter 0)) s fun s' => (EKept C W SP A D T R N n ca cl ext s' ∧
      Spec.Siv.beNat (bytesAt s'.mem (w64 W + BitVec.ofNat 64 cbOff) 16) % 2 ^ 32 < 2 ^ 31) ∧ s'.wr = s.wr := by
  obtain ⟨s₀, T, K⟩ := h
  have L := T.pre.ads.lay
  obtain ⟨s₃, run₃, m₃, bp₃, sp₃, rd₃, wr₃⟩ := counter_ok L K.env
  have E₃ : Env C W SP s₃ := ⟨bp₃, sp₃, K.env.perm.of_eq rd₃ wr₃⟩
  have f₃ : Frame [⟨w64 W + BitVec.ofNat 64 cbOff, 16⟩] s.mem s₃.mem := by
    rw [m₃]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine WP.of_runBlock ⟨s₃, run₃, ⟨⟨s₀, T, K.step L hext E₃ rd₃ wr₃ f₃ counter_wR⟩, ?_⟩, wr₃⟩
  rw [m₃, counter_bytes]
  exact counter_low _

/-- `sivOut` is constant time: `siv`'s address, the stack argument 6, is the
same in both runs. -/
theorem sivOut_ct {C W SP T : BitVec 32} (L : Lay C W SP) {I : State → Prop}
    (h : ∀ s, I s → Env C W SP s ∧ s.mem.readW (argA SP 6) 32 = T ∧ InRegions (s.rd ++ s.wr) (argA SP 6) 4) :
    CT I sivOut := by
  refine CT.seq (J := fun s => s.gpr .edi = T)
    (CT.taint [.ebp, .esp] (pin2 fun s hs => ⟨(h s hs).1.ebp, (h s hs).1.esp⟩) (by taint_decide))
    (fun s hs => ?_) (CT.taint [.edi] (pin1 fun _ h => h) (by taint_decide))
  obtain ⟨E, hv, hin⟩ := h s hs
  exact WP.of_runBlock ⟨_, by crun [E.ebp, E.esp, L.aW, E.perm.wR, hin, hv], by cregs []⟩

/-- `sivIn` is constant time: `siv`'s address, the stack argument 6, is the
same in both runs. -/
theorem sivIn_ct {C W SP T : BitVec 32} {I : State → Prop}
    (h : ∀ s, I s → Env C W SP s ∧ s.mem.readW (argA SP 6) 32 = T ∧ InRegions (s.rd ++ s.wr) (argA SP 6) 4) :
    CT I sivIn := by
  refine CT.seq (J := fun s => s.gpr .edi = T ∧ s.gpr .ebp = W)
    (CT.taint [.esp] (pin1 fun s hs => (h s hs).1.esp) (by taint_decide))
    (fun s hs => ?_) (CT.taint [.edi, .ebp] (pin2 fun _ h => h) (by taint_decide))
  obtain ⟨E, hv, hin⟩ := h s hs
  exact WP.of_runBlock ⟨_, by crun [E.esp, hin, hv], by cregs [], by cregs [E.ebp]⟩

/-- `vg_aes_siv_encrypt` is constant time, with `siv` writable. -/
theorem encrypt_top_ct (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32}
    {cl : Nat → Nat} (z : State) (Tz : ETop C W SP A D T R N n ca cl z) :
    CT (fun s => ETop C W SP A D T R N n ca cl s ∧ Covers [⟨w64 T, 16⟩] s.wr) (encrypt v.callee v.suffix) := by
  have L := Tz.pre.ads.lay
  have hR := Tz.pre.ads.rounds
  have hcl : ∀ j < N, cl j < 2 ^ 32 := fun j hj => by rw [← (Tz.comps j hj).2]; exact BitVec.isLt _
  have hW16 : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := by
    simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
  have hext : ∀ r ∈ [(⟨w64 W, 16⟩ : Region)], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hW16
  have hDw : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    Tz.pre.data.buf.w.sub_right (Lay.wSub (by decide))
  have hext2 : ∀ r ∈ [(⟨w64 W, 16⟩ : Region), ⟨w64 D, n⟩], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hW16
      · exact hDw
  refine CT.seq (J := fun s => EOut C W SP A D T R N n ca cl s ∧ Covers [⟨w64 T, 16⟩] s.wr)
    ((encS2v_ct v L hR Tz.pre.ads.N32 hcl).mono fun s h => h.1)
    (fun s hs => WP.mono (encS2v_ok v hs.1.pre) fun s' O => ⟨⟨s, hs.1, O⟩, by rw [O.kept.wr]; exact hs.2⟩) ?_
  refine CT.seq (J := fun s => EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩] s ∧ Covers [⟨w64 T, 16⟩] s.wr)
    ((finish_ct v L hR Tz.pre.n32 (.inl rfl)).mono fun s ⟨⟨_, _, O⟩, _⟩ => O.pre)
    (fun s ⟨⟨s₀, T₀, O⟩, hc⟩ => WP.mono (finish_ok v L hR O.pre (out := 0) (.inl rfl)) fun s₂ F =>
      ⟨⟨s₀, T₀, (O.kept.widen _).step L (fun r hr => by
        simp only [List.nil_append, List.mem_singleton] at hr; subst hr; exact hW16)
        F.env F.rd F.wr F.frame (finR_wR (.inl ⟨rfl, by simp⟩))⟩, by rw [F.wr]; exact hc⟩) ?_
  refine CT.seq (J := fun s => (EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩] s ∧
      Spec.Siv.beNat (bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16) % 2 ^ 32 < 2 ^ 31) ∧
      Covers [⟨w64 T, 16⟩] s.wr)
    (counter_ct fun s ⟨⟨_, _, K⟩, _⟩ => K.env.ebp)
    (fun s hs => WP.mono (counter_wp hext hs.1) fun s' ⟨p, e⟩ => ⟨p, by rw [e]; exact hs.2⟩) ?_
  refine CT.seq (J := fun s => EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s ∧
      Covers [⟨w64 T, 16⟩] s.wr)
    ((ctr_ct v L hR).mono fun s ⟨⟨h, low⟩, _⟩ => ⟨h.ctrPre, low⟩)
    (fun s ⟨⟨⟨s₀, T₀, K⟩, low⟩, hc⟩ =>
      let P := (show EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩] s from ⟨s₀, T₀, K⟩).ctrPre
      WP.mono (ctr_ok v L hR P.env P.dat P.n32 P.ctx P.rounds P.data P.len rfl low)
        fun _ ⟨E, rd, wr, f, _⟩ => ⟨⟨s₀, T₀, (K.widen _).step L hext2 E rd wr f (ctrR_wR (by simp))⟩,
          by rw [wr]; exact hc⟩) ?_
  have arg6 : ∀ s, EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s →
      s.mem.readW (argA SP 6) 32 = T ∧ InRegions (s.rd ++ s.wr) (argA SP 6) 4 := fun s ⟨_, T₀, K⟩ =>
    Kept.arg6 T₀.pre K fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact T₀.pre.aw.sub_right (Region.sub_prefix (by decide))
      · exact T₀.pre.ad
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (sivOut_ct L fun s hs => ⟨(match hs.1 with | ⟨_, _, K⟩ => K.env), arg6 s hs.1⟩) ?_ ?_
  · intro s ⟨⟨s₀, T₀, K⟩, hc⟩
    obtain ⟨v6, i6⟩ := arg6 s ⟨s₀, T₀, K⟩
    exact WP.mono (sivOut_ok L K.env i6 v6 hc T₀.pre.tfit) fun _ ⟨_, _, bp, _⟩ => bp
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

/-! ## `decrypt` -/

theorem maskTest_ok {C W SP : BitVec 32} {s : State} (L : Lay C W SP) (E : Env C W SP s) {n : Nat}
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) :
    ∃ s₁, runBlock isa [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hlen]
  · cmems [hlen]; rw [and_self_beq32 hn32]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

theorem maskArgs_ok {C W SP : BitVec 32} {s₁ : State} (L : Lay C W SP) (E₁ : Env C W SP s₁) {D : BitVec 32} {n : Nat}
    (hd₁ : slotv s₁.mem W dataO = D) (cx₁ : s₁.gpr .ecx = BitVec.ofNat 32 n) :
    ∃ s₂, runBlock isa [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧
      s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n := by
  refine ⟨_, by crun [E₁.ebp, L.aW, E₁.perm.wR, hd₁], ?_, ?_⟩
  · cregs [hd₁]
  · cregs [cx₁]

theorem mask_ct {C W SP : BitVec 32} (L : Lay C W SP) {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32)
    {I : State → Prop}
    (h : ∀ s, I s → Env C W SP s ∧ slotv s.mem W dataO = D ∧ slotv s.mem W lenO = BitVec.ofNat 32 n) :
    CT I mask := by
  refine CT.block_seq [.ebp] (pin_ebp fun s hs => (h s hs).1.ebp) (by taint_decide)
    (fun s hs => maskTest_ok L (h s hs).1 (h s hs).2.2 hn32) ?_
  refine CT.ite (decide (n = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun _ => ?_
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, _, hbp, _⟩ => hbp) (by taint_decide)
    (fun s₁ ⟨s, hs, m₁, cx₁, _, bp₁, sp₁, rd₁, wr₁⟩ => maskArgs_ok L
      ⟨bp₁, sp₁, (h s hs).1.perm.of_eq rd₁ wr₁⟩ (by rw [m₁]; exact (h s hs).2.1) cx₁) ?_
  exact CT.taint [.edi, .ecx] (pin2 fun _ ⟨_, _, hdi, hcx⟩ => ⟨hdi, hcx⟩) (by taint_decide)

theorem compare_ct {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    CT I (.block compare) :=
  CT.taint [.ebp] (pin_ebp h) (by taint_decide)

/-- `vg_aes_siv_decrypt` is constant time. -/
theorem decrypt_top_ct (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32}
    {cl : Nat → Nat} (z : State) (Tz : ETop C W SP A D T R N n ca cl z) :
    CT (ETop C W SP A D T R N n ca cl) (decrypt v.callee v.suffix) := by
  have L := Tz.pre.ads.lay
  have hR := Tz.pre.ads.rounds
  have hcl : ∀ j < N, cl j < 2 ^ 32 := fun j hj => by rw [← (Tz.comps j hj).2]; exact BitVec.isLt _
  have hDw : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    Tz.pre.data.buf.w.sub_right (Lay.wSub (by decide))
  have hW16 : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := by
    simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
  have hext1 : ∀ r ∈ [(⟨w64 W, 16⟩ : Region)], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hW16
  have hextD : ∀ r ∈ [(⟨w64 W, 16⟩ : Region), ⟨w64 D, n⟩], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hW16
      · exact hDw
  refine CT.seq (J := EOut C W SP A D T R N n ca cl) (encS2v_ct v L hR Tz.pre.ads.N32 hcl)
    (fun s hs => encS2v_wp v hs) ?_
  -- The received IV copied from `siv`.
  have arg6 : ∀ s, EOut C W SP A D T R N n ca cl s →
      s.mem.readW (argA SP 6) 32 = T ∧ InRegions (s.rd ++ s.wr) (argA SP 6) 4 := fun s ⟨_, T₀, O⟩ =>
    Kept.arg6 T₀.pre O.kept (by simp)
  refine CT.seq (J := EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩])
    (sivIn_ct fun s hs => ⟨(match hs with | ⟨_, _, O⟩ => O.kept.env), arg6 s hs⟩)
    (fun s ⟨s₀, T₀, O⟩ => by
      obtain ⟨v6, i6⟩ := arg6 s ⟨s₀, T₀, O⟩
      exact WP.mono (sivIn_ok L O.kept.env i6 v6 (by rw [O.kept.rd, O.kept.wr]; exact T₀.pre.t_rd) T₀.pre.tfit)
        fun _ ⟨_, fIn, bp, sp, rd, wr⟩ => ⟨s₀, T₀, (O.kept.widen _).step L hext1
          ⟨bp, sp, O.kept.env.perm.of_eq rd wr⟩ rd wr fIn (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact .inr ⟨⟨w64 W, 16⟩, by simp, Offset.sub_base (k := 16) _ (by decide)⟩)⟩) ?_
  -- CTR.
  refine CT.seq (J := fun s => EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩] s ∧
      Spec.Siv.beNat (bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16) % 2 ^ 32 < 2 ^ 31)
    (counter_ct fun s ⟨_, _, K⟩ => K.env.ebp)
    (fun s hs => WP.mono (counter_wp hext1 hs) fun _ h => h.1) ?_
  refine CT.seq (J := EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩, ⟨w64 D, n⟩])
    ((ctr_ct v L hR).mono fun s ⟨h, low⟩ => ⟨h.ctrPre, low⟩)
    (fun s ⟨⟨s₀, T₀, K⟩, low⟩ =>
      let P := (show EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩] s from ⟨s₀, T₀, K⟩).ctrPre
      WP.mono (ctr_ok v L hR P.env P.dat P.n32 P.ctx P.rounds P.data P.len rfl low)
        fun _ ⟨E, rd, wr, f, _⟩ => ⟨s₀, T₀, (K.widen _).step L hextD E rd wr f (ctrR_wR (by simp))⟩) ?_
  -- S2V's end with the plaintext.
  refine CT.seq (J := fun s => EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s ∧ CmacPre C W SP R D n s)
    (dataStr_ct fun s ⟨_, _, K⟩ => K.env.ebp)
    (fun s ⟨s₀, T, K⟩ => by
      obtain ⟨s₄, run₄, P₄, K₄, _⟩ := dataStr_pre L K hextD (T.pre.data.buf.of_eq K.rd K.wr) T.pre.n32
      exact WP.of_runBlock ⟨s₄, run₄, ⟨s₀, T, K₄⟩, P₄⟩) ?_
  refine CT.seq (J := EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩, ⟨w64 D, n⟩])
    ((finish_ct v L hR Tz.pre.n32 (.inr rfl)).mono fun s h => h.2)
    (fun s ⟨⟨s₀, T, K⟩, P⟩ => WP.mono (finish_ok v L hR P (out := tOff) (.inr rfl)) fun _ F =>
      ⟨s₀, T, K.step L hextD F.env F.rd F.wr F.frame (finR_wR (.inr rfl))⟩) ?_
  -- The comparison and the mask.
  refine CT.seq (J := fun s => EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s ∧
      ∃ c : Bool, slotv s.mem W okO = if c then 1 else 0)
    (compare_ct fun s ⟨_, _, K⟩ => K.env.ebp)
    (fun s ⟨s₀, T, K⟩ => by
      obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ := compare_ok L K.env
      have E₆ : Env C W SP s₆ := K.env.keep (g₆ _ (by decide) (by decide)) (g₆ _ (by decide) (by decide)) rd₆ wr₆
      have f₆ : Frame [⟨w64 W + BitVec.ofNat 64 okO, 4⟩] s.mem s₆.mem := by
        rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
      refine WP.of_runBlock ⟨s₆, run₆, ⟨s₀, T, K.step L hextD E₆ rd₆ wr₆ f₆ fun r hr => ?_⟩,
        decide (bytesAt s.mem (w64 W) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 tOff) 16), ?_⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact .inl ⟨wS W, by simp, sub_wS (by decide) (by decide)⟩
      · rw [m₆, ← okVal_eq]; exact Mem.readW_writeW_self32 _ _ _) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (mask_ct L Tz.pre.n32 fun s ⟨⟨_, _, K⟩, _⟩ => ⟨K.env, K.slots.data, K.slots.len⟩)
    (fun s ⟨⟨s₀, T, K⟩, c, hc⟩ => WP.mono (mask_ok L K.env K.slots.data K.slots.len T.pre.n32
      (T.pre.data.buf.of_eq K.rd K.wr) (by rw [K.wr]; exact T.pre.data.wr) hc) fun _ ⟨E, _⟩ => E.ebp) ?_
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

end VG.Proof.AesSiv.X86

end

end

@[expose] public section

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.Impl.AesSiv.X86
open VG.Proof.AesGcm.X86 (w64 ofNat_toNat32 argsR)

theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)

theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)

theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem cov_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem below_eq60 {SP : BitVec 32} (h : 60 ≤ SP.toNat) : below SP 60 = ⟨w64 SP - BitVec.ofNat 64 60, 60⟩ := by
  simp only [below, Region.mk.injEq, and_true]
  exact VG.X86.Taint.sub_setWidth h

/-- The entry's public values, from the shared contracts' precondition. -/
abbrev ETopS (s : State) : Prop :=
  ETop (arg s 0) (arg s 7) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 1).toNat (arg s 3).toNat
    (arg s 5).toNat (compA s.mem (arg s 2)) (compL s.mem (arg s 2)) s

set_option linter.unusedSimpArgs false in
/-- The precondition of `encrypt`'s shared contract with the working space:
the entry's invariant, and `siv` writable and apart from the data. -/
theorem encPre_of {s : State} (h : (Proof.AesSiv.encryptScratchContract X86.abi 60).pre s) :
    ETopS s ∧ Covers [⟨w64 (arg s 6), 16⟩] s.wr ∧
      (⟨w64 (arg s 6), 16⟩ : Region).Disjoint ⟨w64 (arg s 4), (arg s 5).toNat⟩ := by
  sig_pre [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] at h
  sig_split h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, List.map_id', Sig.conj_cons,
    Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.filterMap_cons, List.filterMap_nil,
    List.append_nil, Sig.conj, List.append_eq, filter_true', filter_false', filterMap_some', filterMap_none',
    List.filter_map] at *
  rename_i sp56 fa cd cT rc rd rT rw fc fd fT fw hrd hwr hc1 hc2 hc3
  obtain ⟨cW, ⟨-, cA⟩, dT, dW, dDesc, ⟨dL, dA⟩, tW, -, ⟨-, -⟩, wDesc, ⟨wL, wA⟩, ⟨-, descA⟩, -⟩ := hc1
  obtain ⟨retDesc, ⟨retL, retA⟩, sC, sD, sT, sW, sDesc, sL, sA⟩ := hc2
  obtain ⟨descFit, lFit⟩ := hc3
  have bE := below_eq60 sp56
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have mC : (⟨w64 (arg s 0), 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mA : (⟨w64 (arg s 2), 8 * (arg s 3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mD : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mT : (⟨w64 (arg s 6), 16⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mW : (⟨w64 (arg s 7), 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have mR : (⟨argAddr s 0, 32⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have L : Lay (arg s 0) (arg s 7) (s.gpr .esp) := ⟨fc, fw, sp56, cW, by rw [bE]; exact sC, by rw [bE]; exact sW⟩
  refine ⟨⟨⟨⟨L, h, ⟨cov_mem (inRd mA), by rw [Nat.mul_comm]; exact descFit,
      by rw [Nat.mul_comm]; exact wDesc.symm, by rw [bE, Nat.mul_comm]; exact sDesc⟩, fun i hi => ?_, BitVec.isLt _⟩,
    ⟨⟨cov_mem (inWr mD), fd, dW, by rw [bE]; exact sD⟩, cov_mem mD, cd⟩,
    ⟨cov_mem (inRd mC), cov_mem mW⟩, rfl, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl,
    (ofNat_toNat32 _).symm, rfl, rfl, by rw [Proof.AesGcm.X86.argsR_eq]; exact cov_mem (inWr mR),
    by rw [Proof.AesGcm.X86.argsR_eq]; exact wA.symm, by rw [Proof.AesGcm.X86.argsR_eq]; exact dA.symm,
    by rw [bE, Proof.AesGcm.X86.argsR_eq]; exact sA, by omega_using [fa], rw, rd, rT, BitVec.isLt _, fT, cov_mem (inWr mT),
    tW, by rw [bE]; exact sT⟩, fun j hj => ⟨rfl, rfl⟩⟩, cov_mem mT, dT.symm⟩
  have hm := comp_mem s.mem (arg s 2) hi
  exact ⟨cov_mem (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))),
    by have := lFit _ hm; rwa [Proof.AesGcm.X86.toNat_w64] at this, (wL _ hm).symm, by rw [bE]; exact sL _ hm⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of `decrypt`'s shared contract with the working space:
the entry's invariant. -/
theorem decPre_of {s : State} (h : (Proof.AesSiv.decryptScratchContract X86.abi 60).pre s) : ETopS s := by
  sig_pre [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] at h
  sig_split h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, List.map_id', Sig.conj_cons,
    Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.filterMap_cons, List.filterMap_nil,
    List.append_nil, Sig.conj, List.append_eq, filter_true', filter_false', filterMap_some', filterMap_none',
    List.filter_map] at *
  rename_i sp56 fa cd rc rd rT rw fc fd fT fw hrd hwr hc1 hc2 hc3
  obtain ⟨cW, ⟨-, cA⟩, -, dW, dDesc, ⟨dL, dA⟩, tW, ⟨-, -⟩, wDesc, ⟨wL, wA⟩, ⟨-, descA⟩, -⟩ := hc1
  obtain ⟨retDesc, ⟨retL, retA⟩, sC, sD, sT, sW, sDesc, sL, sA⟩ := hc2
  obtain ⟨descFit, lFit⟩ := hc3
  have bE := below_eq60 sp56
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have mC : (⟨w64 (arg s 0), 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mT : (⟨w64 (arg s 6), 16⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mA : (⟨w64 (arg s 2), 8 * (arg s 3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have mD : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mW : (⟨w64 (arg s 7), 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mR : (⟨argAddr s 0, 32⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have L : Lay (arg s 0) (arg s 7) (s.gpr .esp) := ⟨fc, fw, sp56, cW, by rw [bE]; exact sC, by rw [bE]; exact sW⟩
  refine ⟨⟨⟨L, h, ⟨cov_mem (inRd mA), by rw [Nat.mul_comm]; exact descFit,
      by rw [Nat.mul_comm]; exact wDesc.symm, by rw [bE, Nat.mul_comm]; exact sDesc⟩, fun i hi => ?_, BitVec.isLt _⟩,
    ⟨⟨cov_mem (inWr mD), fd, dW, by rw [bE]; exact sD⟩, cov_mem mD, cd⟩,
    ⟨cov_mem (inRd mC), cov_mem mW⟩, rfl, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl,
    (ofNat_toNat32 _).symm, rfl, rfl, by rw [Proof.AesGcm.X86.argsR_eq]; exact cov_mem (inWr mR),
    by rw [Proof.AesGcm.X86.argsR_eq]; exact wA.symm, by rw [Proof.AesGcm.X86.argsR_eq]; exact dA.symm,
    by rw [bE, Proof.AesGcm.X86.argsR_eq]; exact sA, by omega_using [fa], rw, rd, rT, BitVec.isLt _, fT, cov_mem (inRd mT),
    tW, by rw [bE]; exact sT⟩, fun j hj => ⟨rfl, rfl⟩⟩
  have hm := comp_mem s.mem (arg s 2) hi
  exact ⟨cov_mem (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hm)))),
    by have := lFit _ hm; rwa [Proof.AesGcm.X86.toNat_w64] at this, (wL _ hm).symm, by rw [bE]; exact sL _ hm⟩

/-- Descriptors whose bytes are the same in two memories list the same
components. -/
theorem comp_eq {m₁ m₂ : Mem} {A : BitVec 32} {N : Nat}
    (h : ∀ i < N * 8, m₁ (w64 A + BitVec.ofNat 64 i) = m₂ (w64 A + BitVec.ofNat 64 i)) {j : Nat} (hj : j < N) :
    compA m₂ A j = compA m₁ A j ∧ compL m₂ A j = compL m₁ A j := by
  have r {d : Nat} (hd : d + 4 ≤ N * 8) : m₂.readW (w64 A + BitVec.ofNat 64 d) 32 =
      m₁.readW (w64 A + BitVec.ofNat 64 d) 32 := by
    have e := Mem.read_congr (m := m₂) (m' := m₁) (a := w64 A + BitVec.ofNat 64 d) (n := 32 / 8)
      fun k hk => by rw [Offset.add_add]; exact (h _ (by omega_using [hd, hk])).symm
    simp only [Mem.readW, e]
  exact ⟨r (by omega_using [hj]), by simp only [compL]; rw [r (by omega_using [hj])]⟩

/-- What two runs of `encrypt` or `decrypt` agree on: the stack pointer, the
arguments and the descriptors. -/
def EncPub (s₁ s₂ : State) : Prop :=
  (s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧
    arg s₁ 3 = arg s₂ 3 ∧ arg s₁ 4 = arg s₂ 4 ∧ arg s₁ 5 = arg s₂ 5 ∧ arg s₁ 6 = arg s₂ 6 ∧ arg s₁ 7 = arg s₂ 7) ∧
  ∀ i < (arg s₁ 3).toNat * 8, s₁.mem (w64 (arg s₁ 2) + BitVec.ofNat 64 i) =
    s₂.mem (w64 (arg s₁ 2) + BitVec.ofNat 64 i)

/-- The second run's entry invariant, with the first run's public values. -/
theorem encPre_pub {X : BitVec 32 → State → Prop} {s₁ s₂ : State} (E : ETopS s₂) (hX : X (arg s₂ 6) s₂)
    (hq : EncPub s₁ s₂) :
    ETop (arg s₁ 0) (arg s₁ 7) (s₁.gpr .esp) (arg s₁ 2) (arg s₁ 4) (arg s₁ 6) (arg s₁ 1).toNat (arg s₁ 3).toNat
      (arg s₁ 5).toNat (compA s₁.mem (arg s₁ 2)) (compL s₁.mem (arg s₁ 2)) s₂ ∧ X (arg s₁ 6) s₂ := by
  obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩, hd⟩ := hq
  refine ⟨⟨?_, fun j hj => comp_eq hd hj⟩, by rw [q7]; exact hX⟩
  rw [q0, q1, q2, q3, q4, q5, q6, q7, q8]
  exact E.pre

/-- A state satisfying the precondition of `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`: the key context at `0x1000`, 10 rounds, no associated
data (descriptors at `0x2000`), no data (at `0x3000`), `siv` at `0x5000` and
`work` at `0x4000`, as stack arguments at `0x8004`. -/
def encSat (rd wr : List Region) : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8015 then 0x30 else if a = 0x801d then 0x50 else if a = 0x8021 then 0x40 else 0
  rd := rd
  wr := wr

theorem encSat_args (rd wr : List Region) : arg (encSat rd wr) 0 = 0x1000 ∧ arg (encSat rd wr) 1 = 10 ∧
    arg (encSat rd wr) 2 = 0x2000 ∧ arg (encSat rd wr) 3 = 0 ∧ arg (encSat rd wr) 4 = 0x3000 ∧
    arg (encSat rd wr) 5 = 0 ∧ arg (encSat rd wr) 6 = 0x5000 ∧ arg (encSat rd wr) 7 = 0x4000 ∧
    argAddr (encSat rd wr) 0 = 0x8004 := by
  have h : arg (encSat [] []) 0 = 0x1000 ∧ arg (encSat [] []) 1 = 10 ∧ arg (encSat [] []) 2 = 0x2000 ∧
      arg (encSat [] []) 3 = 0 ∧ arg (encSat [] []) 4 = 0x3000 ∧ arg (encSat [] []) 5 = 0 ∧
      arg (encSat [] []) 6 = 0x5000 ∧ arg (encSat [] []) 7 = 0x4000 ∧ argAddr (encSat [] []) 0 = 0x8004 := by
    decide
  exact h

theorem encSat_pre : ∃ s, (Proof.AesSiv.encryptScratchContract X86.abi 60).pre s := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, e⟩ := encSat_args [⟨0x1000, 512⟩, ⟨0x2000, 0⟩]
    [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 32⟩]
  have esp : (encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩]
    [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 32⟩]).gpr .esp = 0x8000 := rfl
  sig_implies_sat [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, a7, e, esp]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 32⟩]

theorem decSat_pre : ∃ s, (Proof.AesSiv.decryptScratchContract X86.abi 60).pre s := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, e⟩ := encSat_args [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩]
    [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 32⟩]
  have esp : (encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩]
    [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 32⟩]).gpr .esp = 0x8000 := rfl
  sig_implies_sat [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, a7, e, esp]
    using encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 32⟩]

theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem encrypt_verified :
    Verified X86.target (encrypt v.callee v.suffix) (Proof.AesSiv.encryptScratchContract X86.abi 60) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, encSat_pre⟩
  · obtain ⟨E, hTw, hTd⟩ := encPre_of hs
    obtain ⟨t, s', he, hq⟩ := encrypt_wp v E.pre hTw hTd
    refine ⟨t, s', he, hq.1, ?_⟩
    sig_post [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Proof.AesSiv.encryptRoundsPost,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    exact fun _ => hq.2
  · sig_pub [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes] at hp
    sig_split hp
    rename_i q0 q1 q2 q3 q4 q5 q6 q7 q8
    obtain ⟨E₁, W₁, -⟩ := encPre_of h₁
    obtain ⟨E₂, W₂, -⟩ := encPre_of h₂
    exact (encrypt_top_ct v s₁ E₁ _ _ _ _ _ _
      ⟨⟨E₁, W₁⟩, encPre_pub (X := fun T s => Covers [⟨w64 T, 16⟩] s.wr) E₂ W₂
        ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩, hp⟩⟩ e₁ e₂).1

/-- The return value: the low word of `edx:eax`. -/
theorem setWidth_ret (a b : BitVec 32) : (a ++ b).setWidth 32 = b := BitVec.setWidth_append_eq_right

theorem decrypt_verified :
    Verified X86.target (decrypt v.callee v.suffix) (Proof.AesSiv.decryptScratchContract X86.abi 60) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, decSat_pre⟩
  · obtain ⟨t, s', he, hq⟩ := decrypt_wp v (decPre_of hs).pre
    refine ⟨t, s', he, hq.1, ?_⟩
    sig_post [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Proof.AesSiv.decryptRoundsPost,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_ret]
    exact fun _ => hq.2
  · sig_pub [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptLeak, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes] at hp
    sig_split hp
    rename_i q0 _ q1 q2 q3 q4 q5 q6 q7 q8
    exact (decrypt_top_ct v s₁ (decPre_of h₁) _ _ _ _ _ _
      ⟨decPre_of h₁, (encPre_pub (X := fun _ _ => True) (decPre_of h₂) trivial
        ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩, hp⟩).1⟩ e₁ e₂).1

/-! ## The working space on the stack -/

theorem encrypt_noEsp : (encrypt v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [encrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, sivOut, Code.allInstrs, noEsp_of (Proof.CmacAes.X86.update_nosp v),
    noEsp_of (Proof.CmacAes.X86.finalize_nosp v), noEsp_of v.nosp]
  decide +kernel

theorem decrypt_noEsp : (decrypt v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [decrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, mask, sivIn, Code.allInstrs, noEsp_of (Proof.CmacAes.X86.update_nosp v),
    noEsp_of (Proof.CmacAes.X86.finalize_nosp v), noEsp_of v.nosp]
  decide +kernel

theorem encrypt_stackUse : stackUse (encrypt v.callee v.suffix) ≤ 60 := by
  simp only [encrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, sivOut, stackUse, Proof.CmacAes.X86.update_stack v, Proof.CmacAes.X86.finalize_stack v, v.stack]
  decide +kernel

theorem decrypt_stackUse : stackUse (decrypt v.callee v.suffix) ≤ 60 := by
  simp only [decrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, mask, sivIn, stackUse, Proof.CmacAes.X86.update_stack v, Proof.CmacAes.X86.finalize_stack v, v.stack]
  decide +kernel

theorem encFrameSat_pre : ∃ s, (Proof.AesSiv.encryptRoundsContract X86.abi 2672).pre s := by
  implies_sat [Proof.AesSiv.encryptRoundsContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, Proof.AesSiv.encryptRoundsPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [encSat, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x8004, 28⟩]

theorem decFrameSat_pre : ∃ s, (Proof.AesSiv.decryptRoundsContract X86.abi 2672).pre s := by
  implies_sat [Proof.AesSiv.decryptRoundsContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Proof.AesSiv.decryptRoundsPost,
    Spec.Siv.decryptLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [encSat, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x8004, 28⟩]

/-- `encrypt` in a frame of 2612 bytes: the return address, the seven
argument slots, the working space's address and its 2576 bytes. -/
theorem encrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2612 7 (encrypt v.callee v.suffix))
      (Proof.AesSiv.encryptRoundsContract X86.abi 2672) :=
  X86.Verified.stackScratchL (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.encryptPre X86.abi.ptrBits) (post := Proof.AesSiv.encryptRoundsPost X86.abi.ptrBits)
    (wa := true) (stack := 60) (bytes := 2612) (encrypt_verified v) (by decide) (encrypt_noEsp v)
    (encrypt_stackUse v) (Proof.AesSiv.encryptPre_local _) (Proof.AesSiv.encryptPost_local _) (fun vs m m₁ m₂ r hl _ => Proof.AesSiv.encryptPostOut_local _ vs m m₁ m₂ r hl) encFrameSat_pre

/-- `decrypt` in a frame of 2612 bytes, as `encrypt`. -/
theorem decrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2612 7 (decrypt v.callee v.suffix))
      (Proof.AesSiv.decryptRoundsContract X86.abi 2672) :=
  X86.Verified.stackScratchL (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.decryptPre X86.abi.ptrBits) (post := Proof.AesSiv.decryptRoundsPost X86.abi.ptrBits)
    (wa := true) (stack := 60) (leak := some (Spec.Siv.decryptLeak X86.abi.ptrBits)) (bytes := 2612)
    (decrypt_verified v) (by decide) (decrypt_noEsp v) (decrypt_stackUse v) (Proof.AesSiv.decryptPre_local _)
    (Proof.AesSiv.decryptPost_local _) (fun vs m m₁ m₂ r hl _ => Proof.AesSiv.decryptPostOut_local _ vs m m₁ m₂ r hl) decFrameSat_pre (hleak := Proof.AesSiv.decryptLeak_local _)

/-! ## `vg_aes_siv_init` -/

/-- The regions of `initX86`: the key and the stack arguments read-only. -/
def initRd (s : State) : List Region := [⟨w64 (arg s 0), (arg s 1).toNat⟩, ⟨argAddr s 0, 16⟩]
def initWr (s : State) : List Region := [⟨w64 (arg s 2), 512⟩, ⟨w64 (arg s 3), 2560⟩]

theorem initPre_of {s : State} (h : (Proof.AesSiv.initScratchContract X86.abi 52).pre s) :
    initX86.pre (s.withRegions (initRd s) (initWr s)) ∧ s.rd = [⟨w64 (arg s 0), (arg s 1).toNat⟩] ∧
      s.wr = [⟨w64 (arg s 2), 512⟩, ⟨w64 (arg s 3), 2560⟩, ⟨argAddr s 0, 16⟩] := by
  sig_pre [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] at h
  sig_split h
  rename_i sp48 fa hrd hwr kc ks ka cs ca sa rk rc rs ra stk stc sts sta fk fc fs
  exact ⟨⟨rfl, rfl, kc, ks, ka, cs, ca, sa, rk, rc, rs, ra, stk, stc, sts, sta, fk, fc, fs, sp48, (by omega_using [fa] : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32), h⟩,
    hrd, hwr⟩

/-- A state satisfying `vg_aes_siv_init`'s precondition: a key of 32 bytes
at `0x1000`, the context at `0x2000` and the scratch buffer at `0x4000`, as
stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 32 else if a = 0x800d then 0x20
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 512⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 16⟩]

theorem initSat_pre : ∃ s, (Proof.AesSiv.initScratchContract X86.abi 52).pre s := by
  have a0 : arg initSat 0 = 0x1000 := by decide
  have a1 : arg initSat 1 = 32 := by decide
  have a2 : arg initSat 2 = 0x2000 := by decide
  have a3 : arg initSat 3 = 0x4000 := by decide
  have e : argAddr initSat 0 = 0x8004 := by decide
  have esp : initSat.gpr .esp = 0x8000 := rfl
  sig_implies_sat [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre,
    Spec.Siv.initPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, e, esp] using initSat

theorem init_verified :
    Verified X86.target (initCore v.expand v.callee v.suffix) (Proof.AesSiv.initScratchContract X86.abi 52) := by
  refine X86.Verified.narrowTo (k := initX86)
    ⟨fun s hs => init_wp v hs, init_ct v, initSat_pre.elim fun s hs => ⟨_, (initPre_of hs).1⟩⟩
    initRd initWr (fun s hs => (initPre_of hs).1) (fun s hs => ?_) (fun s hs => ?_) (fun s s' hs hq => ?_)
    (fun s₁ s₂ h₁ h₂ hp => ?_) initSat_pre
  · obtain ⟨-, hrd, hwr⟩ := initPre_of hs
    rw [hrd, hwr]
    exact Covers.of_mem fun r hr => by
      simp only [initRd, initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp
  · obtain ⟨-, -, hwr⟩ := initPre_of hs
    rw [hwr]
    exact Covers.of_mem fun r hr => by
      simp only [initWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  · sig_post [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
    exact hq
  · sig_pub [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at hp
    sig_split hp
    rename_i q0 q1 q2 q3
    refine ⟨q0, fun i hi => ?_⟩
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact q1
    · exact q2
    · exact q3
    · exact hp

theorem init_noEsp : (initCore v.expand v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [initCore, Impl.CmacAes.Stream.X86.call4, Code.allInstrs, noEsp_of v.expandNosp,
    noEsp_of (Proof.CmacAes.X86.subkeys_nosp v)]
  decide +kernel

theorem init_stackUse : stackUse (initCore v.expand v.callee v.suffix) ≤ 52 := by
  simp only [initCore, Impl.CmacAes.Stream.X86.call4, stackUse, v.expandStack, Proof.CmacAes.X86.subkeys_stack v]
  decide +kernel

/-- A state satisfying `vg_aes_siv_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with rd := [⟨0x1000, 32⟩], wr := [⟨0x2000, 512⟩, ⟨0x8004, 12⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract X86.abi 2632).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

/-- `initCore` in a frame of 2580 bytes: the return address, the three
argument slots and the 2560 bytes of working space. -/
theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2580 3 (initCore v.expand v.callee v.suffix))
      (Spec.Siv.initContract X86.abi 2632) :=
  X86.Verified.stackScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre X86.abi.ptrBits) (post := Spec.Siv.initPost X86.abi.ptrBits)
    (wa := true) (stack := 52) (bytes := 2580) (init_verified v) (by decide) (init_noEsp v)
    (init_stackUse v) (Proof.AesSiv.initPre_local _) (Proof.AesSiv.initPost_local _) (fun vs m m₁ m₂ r hl _ => Proof.AesSiv.initPostOut_local _ vs m m₁ m₂ r hl) initFrameSat_pre

/-! ## The stack pointer -/

theorem init_spSafe : (initCore v.expand v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [initCore, Impl.CmacAes.Stream.X86.call4, Code.all, v.expandSpSafe, Proof.CmacAes.X86.subkeys_spSafe v,
    Bool.and_true]
  decide +kernel

theorem encrypt_spSafe : (encrypt v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [encrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, sivOut, Code.all, Proof.CmacAes.X86.update_spSafe v, Proof.CmacAes.X86.finalize_spSafe v, v.spSafe,
    Bool.and_true]
  decide +kernel

theorem decrypt_spSafe : (decrypt v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [decrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, mask, sivIn, Code.all, Proof.CmacAes.X86.update_spSafe v, Proof.CmacAes.X86.finalize_spSafe v, v.spSafe,
    Bool.and_true]
  decide +kernel

end VG.Proof.AesSiv.X86
