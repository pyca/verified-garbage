module

import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.AesSiv.X86.Finish
public import VerifiedGarbage.Proof.AesSiv.X86.FinishLong
import VerifiedGarbage.Proof.AesSiv.X86.Run
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesSiv.X86
public import VerifiedGarbage.Proof.AesGcm.X86.Fn
public import VerifiedGarbage.Proof.AesSiv.X86.Callee
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesSiv.X86.S2v
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Spec

/-! ### `AesSiv.X86.Ctr`, which this module and modules that import it used -/

section

/-!
# AES-SIV on x86: CTR (`ctr`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesSiv/Arm/Ctr.lean`): `counter 0` sets the counter block at
`W + 96` to `Q`, the IV at `W` with bit 7 of its bytes 8 and 12 cleared
(`counter_bytes`, `Proof.AesSiv.counter_words4`). `ctrWhole` encrypts the
whole blocks of the data by one call of `vg_aes_ctr32_to` from `Q`, whose
counters do not wrap around (`Proof.AesSiv.counter_low`,
`Proof.AesSiv.repeat_inc32`), and which leaves `Q + nb` in the counter block
(`ctrWhole_ok`); `ctrTail` XORs the last bytes with the first bytes of the
keystream block of that counter, which `vg_aes_ctr32_to` computes on a zero
block at `W + 80` (`ctrTail_ok`). Together, CTR's output on the data
(`ctr_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt blocksAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 slotv zero4_fold length_bytesAt readW_writeW_off covers_off shr4
  and15 ofNat_sub32 XorPre XorPost xorLoop_ok xorBytes length_xorBytes CT)
open VG.Proof.Cmac (le4 store4)

/-- The data: `n` bytes at `D` the code may read and write, apart from the
key context, `W` and the stack below `SP`. -/
structure Dat (C W SP : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  buf : Buf W SP s D n
  wr : Covers [⟨w64 D, n⟩] s.wr
  c : (⟨w64 C, 512⟩ : Region).Disjoint ⟨w64 D, n⟩

theorem Dat.of_eq {C W SP : BitVec 32} {s s' : State} {D : BitVec 32} {n : Nat} (h : Dat C W SP s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Dat C W SP s' D n :=
  ⟨h.buf.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.c⟩

/-- The first `k` bytes of the data as `vg_aes_ctr32_to`'s. -/
theorem Dat.dst {C W SP : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : Dat C W SP s D n) {k : Nat}
    (hk : k ≤ n) {c : Nat} (hc : c + 16 ≤ 256) : Dst C W SP s D k c where
  wr := fun a m ⟨r, hr, hc'⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.wr a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega_arith⟩
  wrap := by have := h.buf.wrap; omega_arith
  dk := h.c.sub_right (Region.sub_prefix hk)
  dc := (h.buf.w.sub_left (Region.sub_prefix hk)).sub_right (Lay.wSub (by omega_arith))
  ds := (h.buf.w.sub_left (Region.sub_prefix hk)).sub_right (Lay.wSub (by decide))
  stk := h.buf.stk.sub_right (Region.sub_prefix hk)

/-- What CTR writes: the keystream and counter blocks, the working space of
`vg_aes_ctr32_to`, the stack below `SP` and the data. -/
abbrev ctrR (W SP D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 ksOff, 32⟩, ⟨w64 W + BitVec.ofNat 64 256, 2048⟩, below SP 60, ⟨w64 D, n⟩]

theorem beq_zero32 {a : Nat} (ha : a < 2 ^ 32) : (BitVec.ofNat 32 a == 0) = decide (a = 0) := by
  have := Proof.AesGcm.X86.and_self_beq32 ha
  rwa [BitVec.and_self] at this

/-! ## The counter -/

theorem counter_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) :
    ∃ s', runBlock isa (counter 0) s = some s' ∧
      s'.mem = store4 s.mem (w64 W + BitVec.ofNat 64 cbOff) (s.mem.readW (w64 W + BitVec.ofNat 64 0) 32)
        (s.mem.readW (w64 W + BitVec.ofNat 64 4) 32) (s.mem.readW (w64 W + BitVec.ofNat 64 8) 32 &&& qm4)
        (s.mem.readW (w64 W + BitVec.ofNat 64 12) 32 &&& qm4) ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [counter, E.ebp, L.aW, E.perm.wW, E.perm.wR], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [store4, add_ofNat_assoc, qm4]
    rfl
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `Q` at `W + 96`. -/
theorem counter_bytes (m : Mem) (W : BitVec 32) :
    bytesAt (store4 m (w64 W + BitVec.ofNat 64 cbOff) (m.readW (w64 W + BitVec.ofNat 64 0) 32)
        (m.readW (w64 W + BitVec.ofNat 64 4) 32) (m.readW (w64 W + BitVec.ofNat 64 8) 32 &&& qm4)
        (m.readW (w64 W + BitVec.ofNat 64 12) 32 &&& qm4)) (w64 W + BitVec.ofNat 64 cbOff) 16 =
      Spec.Siv.counter (bytesAt m (w64 W) 16) := by
  rw [Proof.Cmac.bytesAt_store4, counter_words4, BitVec.add_zero, Proof.Cmac.bytesAt_split4 m (w64 W), ← Proof.Cmac.le4_readW,
    ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW]

/-! ## The whole blocks -/

theorem whole1_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {n : Nat}
    (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .edi (slot lenO), .shift .shr .edi 4, .alu .test .edi (.reg .edi)] s = some s' ∧
      s'.gpr .edi = BitVec.ofNat 32 (n / 16) ∧ s'.zf = some (decide (n / 16 = 0)) ∧
      (∀ r, r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hsh := shr4 hn
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hl], ?_, ?_, fun r h₁ => ?_, ?_, ?_, ?_⟩
  · cregs [hl, hsh]
  · cmems [hl, hsh]; rw [Proof.AesGcm.X86.and_self_beq32 (by omega_arith)]
  · cregs []
  all_goals cmems []

theorem ctrArgs_ok {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {s : State} (E : Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) {D : BitVec 32}
    (hd : slotv s.mem W dataO = D) :
    ∃ s', runBlock isa (ctrArgs ++ ([.mov .ebx (slot dataO)] : List Instr)) s = some s' ∧
      s'.gpr .eax = C + BitVec.ofNat 32 272 ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧
      s'.gpr .edx = W + BitVec.ofNat 32 cbOff ∧ s'.gpr .ebx = D ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [ctrArgs, E.ebp, L.aW, E.perm.wR, hc, hr, hd], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_,
    ?_⟩
  · cregs [hc]
  · cregs [hr]
  · cregs [E.ebp]
  · cregs [hd]
  · cregs []
  all_goals cmems []

/-! ## The last bytes -/

theorem tail1_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {n : Nat}
    (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .ecx (slot lenO), .alu .and .ecx (imm 15)] s = some s' ∧
      s'.gpr .ecx = BitVec.ofNat 32 (n % 16) ∧ s'.zf = some (decide (n % 16 = 0)) ∧
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ha := and15 (BitVec.ofNat 32 n)
  rw [toNat_ofNat32 hn] at ha
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hl], ?_, ?_, fun r h₁ => ?_, ?_, ?_, ?_⟩
  · cregs [hl, ha]
  · cmems [hl, ha]; rw [beq_zero32 (by omega_arith)]
  · cregs []
  all_goals cmems []

theorem tailArgs_ok' {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {s : State} (E : Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) :
    ∃ s', runBlock isa (zero4 ksOff ++ ctrArgs ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksOff),
        .mov .edi (imm 1)] : List Instr)) s = some s' ∧
      s'.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 ksOff) ∧
      s'.gpr .eax = C + BitVec.ofNat 32 272 ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧
      s'.gpr .edx = W + BitVec.ofNat 32 cbOff ∧ s'.gpr .ebx = W + BitVec.ofNat 32 ksOff ∧
      s'.gpr .edi = BitVec.ofNat 32 1 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain z := zero4_fold s.mem W ksOff
  simp only [Nat.reduceAdd, ksOff] at z
  refine ⟨_, by crun [zero4, ctrArgs, E.ebp, L.aW, E.perm.wW, E.perm.wR, hc, hr], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · cmems [z]
  · cregs [hc]
  · cregs [hr]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs []
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

theorem xorArgs_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {D : BitVec 32} {n : Nat}
    (hd : slotv s.mem W dataO = D) (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .ecx (slot lenO), .alu .and .ecx (imm 15), .mov .edx (.reg .ebp),
        .alu .add .edx (imm ksOff), .mov .edi (slot dataO), .alu .add .edi (slot lenO),
        .alu .sub .edi (.reg .ecx)] s = some s' ∧
      s'.gpr .ecx = BitVec.ofNat 32 (n % 16) ∧ s'.gpr .edx = W + BitVec.ofNat 32 ksOff ∧
      s'.gpr .edi = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ha := and15 (BitVec.ofNat 32 n)
  rw [toNat_ofNat32 hn] at ha
  obtain hsub : D + BitVec.ofNat 32 n - BitVec.ofNat 32 (n % 16) = D + BitVec.ofNat 32 (16 * (n / 16)) := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, ofNat_sub32 (Nat.mod_le _ _) hn]
    congr 2; omega_arith
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hl, hd], ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_⟩
  · cregs [hl, ha]
  · cregs [E.ebp]
  · cregs [hl, ha, hd, hsub]
  · cregs []
  all_goals cmems []

/-! ## `ctrWhole` -/

theorem rounds_le {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : 16 * (R + 1) ≤ 240 := by omega_arith

/-- The whole blocks of the data, from the counter `q` at `W + 96`, whose last
32 bits do not wrap around. -/
theorem ctrWhole_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State} (E : Env C W SP s) {D : BitVec 32} {n : Nat}
    (hD : Dat C W SP s D n) (hn : n < 2 ^ 32) (hc : slotv s.mem W ctxO = C)
    (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hd : slotv s.mem W dataO = D)
    (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) {q : List Byte}
    (hq : bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16 = q)
    (hlow : Spec.Siv.beNat q % 2 ^ 32 + n / 16 + 1 ≤ 2 ^ 32) :
    WP isa (ctrWhole v.callee) s fun s' => Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (ctrR W SP D n) s.mem s'.mem ∧
      bytesAt s'.mem (w64 D) n =
        ctrPart (Spec.Siv.ctxCiph s.mem (w64 C) R) q (bytesAt s.mem (w64 D) n) (16 * (n / 16)) ∧
      blockAt s'.mem (w64 W + BitVec.ofNat 64 cbOff) =
        Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)) := by
  obtain hql : q.length = 16 := by rw [← hq, length_bytesAt]
  obtain hinc := repeat_inc32 hql (k := n / 16 + 1) (by omega_arith)
  obtain hcb : blockAt s.mem (w64 W + BitVec.ofNat 64 cbOff) = Spec.Gcm.ofBytes q := by
    rw [blockAt, hq]
  obtain ⟨s₁, run₁, di₁, zf₁, g₁, m₁, rd₁, wr₁⟩ := whole1_ok L E hl hn
  obtain E₁ : Env C W SP s₁ := ⟨by rw [g₁ _ (by decide), E.ebp], by rw [g₁ _ (by decide), E.esp], E.perm.of_eq rd₁ wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n / 16 = 0
  · refine WP.ite true (eval_e (by rw [zf₁]; simp [h0])) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨E₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_, ?_⟩
    · rw [m₁, h0, Nat.mul_zero, ctrPart_zero]
    · rw [m₁, hcb, h0, Nat.add_zero]
      have := hinc 0 (by omega_arith)
      rw [Nat.add_zero] at this
      exact this
  · refine WP.ite false (eval_e (by rw [zf₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    obtain hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
    obtain ⟨s₂, run₂, ax₂, cx₂, dx₂, bx₂, g₂, m₂, rd₂, wr₂⟩ := ctrArgs_ok (C := C) (R := R) (D := D) L E₁ (by rw [m₁]; exact hc)
      (by rw [m₁]; exact hr) (by rw [m₁]; exact hd)
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    obtain E₂ : Env C W SP s₂ := ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), E₁.ebp],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), E₁.esp], E₁.perm.of_eq rd₂ wr₂⟩
    obtain hD₂ := hD.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
    obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
    refine WP.mono (ctrCall_ok v L E₂ hR (c := cbOff) (by decide) (hD₂.dst hb (by decide)) ax₂ cx₂ dx₂ bx₂
      (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), di₁])) fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, o₃, c₃⟩ => ?_
    obtain hRb := rounds_le hR
    obtain fT : Frame (ctrR W SP D n) s.mem s₃.mem := by
      rw [← mem₂]
      exact f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨⟨w64 D, n⟩, by simp, Region.sub_prefix hb⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
    refine ⟨E₃, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], fT, ?_, ?_⟩
    · -- The whole blocks, then the rest as it was.
      obtain hc₃ := ctr32_ctrPart (m := s₂.mem) (m' := s₃.mem) (K := w64 C + BitVec.ofNat 64 272)
        (C := w64 W + BitVec.ofNat 64 cbOff) (D := w64 D) (R := R) (q := q) (k := n / 16)
        (fun i hi => by rw [mem₂, hcb]; exact hinc i (by omega_arith)) o₃
      obtain e := Proof.Cmac.Stream.bytesAt_append s₃.mem (w64 D) (16 * (n / 16)) (n - 16 * (n / 16))
      rw [show 16 * (n / 16) + (n - 16 * (n / 16)) = n by omega_arith] at e
      obtain e₀ := Proof.Cmac.Stream.bytesAt_append s.mem (w64 D) (16 * (n / 16)) (n - 16 * (n / 16))
      rw [show 16 * (n / 16) + (n - 16 * (n / 16)) = n by omega_arith] at e₀
      obtain rest : bytesAt s₃.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
          bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
        rw [← mem₂]
        refine Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => ?_) (by have := hD.buf.lt; omega_arith)
        obtain hsub : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ ⟨w64 D, n⟩ :=
          Offset.sub_base _ (by omega_arith)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by decide))
        · exact (Offset.base_disjoint (w64 D) (e := 16 * (n / 16)) (n := n - 16 * (n / 16))
            (k := 16 * (n / 16)) (by omega_arith) (by have := hD.buf.lt; omega_arith)).symm
        · exact (hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by decide))
        · exact (hD.buf.stk.sub_right hsub).symm
      obtain hpa := ctrPart_append (Spec.Siv.ctxCiph s.mem (w64 C) R) q (bytesAt s.mem (w64 D) (16 * (n / 16)))
        (bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)))
      rw [length_bytesAt] at hpa
      rw [e, hc₃, rest, e₀, hpa, mem₂]
      rfl
    · rw [c₃, mem₂, hcb]
      exact hinc (n / 16) (by omega_arith)

/-! ## `ctrTail` -/

/-- The last bytes of the data, XORed with the keystream block of the counter
`Q + nb` that `ctrWhole` left. -/
theorem ctrTail_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State} (E : Env C W SP s) {D : BitVec 32} {n : Nat}
    (hD : Dat C W SP s D n) (hn : n < 2 ^ 32) (hc : slotv s.mem W ctxO = C)
    (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hd : slotv s.mem W dataO = D)
    (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) {q x : List Byte} (hx : x.length = n)
    (hcb : blockAt s.mem (w64 W + BitVec.ofNat 64 cbOff) =
      Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)))
    (hdat : bytesAt s.mem (w64 D) n = ctrPart (Spec.Siv.ctxCiph s.mem (w64 C) R) q x (16 * (n / 16))) :
    WP isa (ctrTail v.callee) s fun s' => Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (ctrR W SP D n) s.mem s'.mem ∧
      bytesAt s'.mem (w64 D) n = ctrPart (Spec.Siv.ctxCiph s.mem (w64 C) R) q x n := by
  obtain ⟨s₁, run₁, cx₁, zf₁, g₁, m₁, rd₁, wr₁⟩ := tail1_ok L E hl hn
  obtain E₁ : Env C W SP s₁ := ⟨by rw [g₁ _ (by decide), E.ebp], by rw [g₁ _ (by decide), E.esp], E.perm.of_eq rd₁ wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n % 16 = 0
  · refine WP.ite true (eval_e (by rw [zf₁]; simp [h0])) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨E₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_⟩
    rw [m₁, hdat, show 16 * (n / 16) = n by omega_arith]
  · refine WP.ite false (eval_e (by rw [zf₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    obtain ⟨s₂, run₂, m₂, ax₂, cx₂, dx₂, bx₂, di₂, bp₂, sp₂, rd₂, wr₂⟩ := tailArgs_ok' (R := R) L E₁
      (by rw [m₁]; exact hc) (by rw [m₁]; exact hr)
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    obtain E₂ : Env C W SP s₂ := ⟨bp₂, sp₂, E₁.perm.of_eq rd₂ wr₂⟩
    refine WP.seq (WP.mono (ctrCall_ok v L E₂ hR (c := cbOff) (by decide) (n := 1)
      (dstW L E₂.perm (c := cbOff) (q := ksOff) (by decide) (by decide) (by decide)) ax₂ cx₂ dx₂ bx₂ di₂)
      fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, o₃, _⟩ => ?_)
    obtain hRb := rounds_le hR
    obtain hb : 16 * (n / 16) < n := by omega_arith
    obtain eK : w64 (W + BitVec.ofNat 32 ksOff) = w64 W + BitVec.ofNat 64 ksOff := L.aW (by decide)
    -- The keystream block.
    obtain f₂ : Frame [⟨w64 W + BitVec.ofNat 64 ksOff, 16⟩] s.mem s₂.mem := by
      rw [m₂, m₁]; exact Cmac.frame_store4 _ _ _ _ _
    obtain cb₂ : blockAt s₂.mem (w64 W + BitVec.ofNat 64 cbOff) =
        Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)) := by
      rw [blockAt, Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), ← blockAt, hcb]
    obtain sch₂ : bytesAt s₂.mem (w64 C + BitVec.ofNat 64 272) (16 * (R + 1)) =
        bytesAt s.mem (w64 C + BitVec.ofNat 64 272) (16 * (R + 1)) :=
      Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.c_w' (by omega_arith) (by decide)) (by omega_arith)
    obtain hks : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 ksOff) 16 =
        Proof.Siv.ksBlock (Spec.Siv.ctxCiph s.mem (w64 C) R) q (n / 16) := by
      rw [eK] at o₃
      obtain hx₃ := Proof.AesCcm.ctr32_bytes (m := s₂.mem) (m' := s₃.mem) (C := w64 W + BitVec.ofNat 64 cbOff)
        (D := w64 W + BitVec.ofNat 64 ksOff) (nb := 1) o₃
      rw [Nat.mul_one, m₂, Cmac.zero4_bytes, ← m₂, cb₂, xorKs_zeros, sch₂,
        Proof.Cmac.aesWith_bytes _ _ (length_be128 _)] at hx₃
      rw [hx₃]; rfl
    -- The arguments of the XOR.
    obtain f₂₃ : Frame [⟨w64 W + BitVec.ofNat 64 ksOff, 32⟩, ⟨w64 W + BitVec.ofNat 64 256, 2048⟩, below SP 60]
        s₂.mem s₃.mem := by
      rw [eK] at f₃
      exact f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
    obtain f₀₃ : Frame [⟨w64 W + BitVec.ofNat 64 ksOff, 32⟩, ⟨w64 W + BitVec.ofNat 64 256, 2048⟩, below SP 60]
        s.mem s₃.mem :=
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩).trans f₂₃
    obtain sl₃ : ∀ o, 176 ≤ o → o + 4 ≤ 256 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
      f₀₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Lay.w_w (.inr (by simp only [ksOff]; omega_arith)) (by omega_arith) (by decide)
        · exact Lay.w_w (.inl h₂) (by omega_arith) (by decide)
        · exact (L.stk_w' (by omega_arith)).symm) (by decide)
    obtain ⟨s₄, run₄, cx₄, dx₄, di₄, g₄, m₄, rd₄, wr₄⟩ := xorArgs_ok (D := D) L E₃
      (by rw [sl₃ _ (by decide) (by decide)]; exact hd) (by rw [sl₃ _ (by decide) (by decide)]; exact hl) hn
    refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
    obtain rd₀₄ : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
    obtain wr₀₄ : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
    have hwD : D.toNat + n ≤ 2 ^ 32 := hD.buf.wrap
    obtain eD : w64 (D + BitVec.ofNat 32 (16 * (n / 16))) = w64 D + BitVec.ofNat 64 (16 * (n / 16)) :=
      Buf.ptr (by omega_arith)
    obtain hsub : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ ⟨w64 D, n⟩ :=
      Offset.sub_base _ (by omega_arith)
    obtain xp : XorPre s₄ (W + BitVec.ofNat 32 ksOff) (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) := by
      refine ⟨dx₄, di₄, cx₄, by omega_arith, by omega_arith, by rw [L.nW (by decide)]; have := L.fw; simp only [ksOff]; omega_arith,
        by rw [Proof.AesGcm.X86.toNat_add32 (by omega_arith)]; omega_arith, ?_, ?_, ?_⟩
      · rw [eK, rd₀₄, wr₀₄]; exact Proof.AesGcm.X86.covers_left (E.perm.wC (by simp only [ksOff]; omega_arith))
      · rw [wr₀₄, eD]; exact covers_off hD.wr (by omega_arith) (by have := hD.buf.lt; omega_arith)
      · rw [eK, eD]; exact ((hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by simp only [ksOff]; omega_arith))).symm
    refine WP.mono (xorLoop_ok s₄ xp) fun s₅ x₅ => ?_
    have hm₅ := x₅.mem
    rw [eK, eD] at hm₅
    obtain hxl := length_xorBytes s₄.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16)))
      (w64 W + BitVec.ofNat 64 ksOff) (n % 16)
    obtain fw : Frame [⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] s₄.mem s₅.mem := by
      rw [hm₅]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
    refine ⟨⟨by rw [x₅.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₄ _ (by decide) (by decide) (by decide), E₃.ebp],
      by rw [x₅.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₄ _ (by decide) (by decide) (by decide), E₃.esp], E₃.perm.of_eq (x₅.rd.trans rd₄) (x₅.wr.trans wr₄)⟩,
      by rw [x₅.rd, rd₀₄], by rw [x₅.wr, wr₀₄], ?_, ?_⟩
    · refine ((f₀₃.sub fun r hr => ?_).trans (by rw [← m₄]; exact Frame.refl _ _)).trans (fw.sub fun r hr => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 D, n⟩, by simp, hsub⟩
    · have hcl : ∀ y, (Spec.Siv.ctxCiph s.mem (w64 C) R y).length = 16 :=
        fun y => Proof.Cmac.aesWith_length _ _ y
      obtain d₄ : bytesAt s₄.mem (w64 D) x.length = ctrPart (Spec.Siv.ctxCiph s.mem (w64 C) R) q x
          (16 * (n / 16)) := by
        rw [hx, m₄, Proof.AesGcm.X86.bytesAt_frame f₀₃ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact hD.buf.w.sub_right (Lay.wSub (by decide))
          · exact hD.buf.w.sub_right (Lay.wSub (by decide))
          · exact hD.buf.stk.symm) (by have := hD.buf.lt; omega_arith), hdat]
      obtain st := ctrPart_step (Spec.Siv.ctxCiph s.mem (w64 C) R) hcl q x s₄.mem (w64 D)
        (i := n / 16) (n := n % 16) (by have := hD.buf.lt; omega_arith) (by omega_arith) (by omega_arith) d₄
      obtain xb : xorBytes s₄.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (w64 W + BitVec.ofNat 64 ksOff) (n % 16) =
          Spec.Cmac.xor (bytesAt s₄.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))
            ((Proof.Siv.ksBlock (Spec.Siv.ctxCiph s.mem (w64 C) R) q (n / 16)).take (n % 16)) := by
        obtain tk := take_bytesAt s₄.mem (w64 W + BitVec.ofNat 64 ksOff) (a := n % 16) (b := 16 - n % 16)
        rw [show n % 16 + (16 - n % 16) = 16 by omega_arith] at tk
        rw [xorBytes, ← tk, m₄, hks]
        rfl
      rw [hx] at st
      rw [hm₅, xb, st, show 16 * (n / 16) + n % 16 = n by omega_arith]

/-! ## `ctr` -/

theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxCiph m' C R = Spec.Siv.ctxCiph m C R := by
  unfold Spec.Siv.ctxCiph Spec.Siv.schedCiph
  rw [Proof.AesGcm.X86.bytesAt_frame hf (p := C + 272)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 272) (n := 16 * (R + 1)) (by omega_arith))) (by omega_arith)]

theorem ctrR_c {C W SP : BitVec 32} (L : Lay C W SP) {s : State} {D : BitVec 32} {n : Nat} (hD : Dat C W SP s D n) :
    ∀ r ∈ ctrR W SP D n, (⟨w64 C, 512⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.c_w.sub_right (Lay.wSub (by decide))
  · exact L.c_w.sub_right (Lay.wSub (by decide))
  · exact L.stk_c.symm
  · exact hD.c

/-- The slots CTR keeps. -/
theorem ctrR_slot {C W SP : BitVec 32} (L : Lay C W SP) {s : State} {D : BitVec 32} {n : Nat}
    (hD : Dat C W SP s D n) {m m' : Mem} (hf : Frame (ctrR W SP D n) m m') {o : Nat} (h₁ : 112 ≤ o)
    (h₂ : o + 4 ≤ 256) : slotv m' W o = slotv m W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by simp only [ksOff]; omega_arith)) (by omega_arith) (by decide)
    · exact Lay.w_w (.inl h₂) (by omega_arith) (by decide)
    · exact (L.stk_w' (by omega_arith)).symm
    · exact (hD.buf.w.sub_right (Lay.wSub (d := o) (n := 4) (by omega_arith))).symm) (by decide)

/-- `ctr`: the data XORed with CTR's keystream from the counter `q` at
`W + 96`, whose last 32 bits are below `2³¹`. -/
theorem ctr_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State} (E : Env C W SP s) {D : BitVec 32} {n : Nat}
    (hD : Dat C W SP s D n) (hn : n < 2 ^ 32) (hc : slotv s.mem W ctxO = C)
    (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hd : slotv s.mem W dataO = D)
    (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) {q : List Byte}
    (hq : bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16 = q) (hlow : Spec.Siv.beNat q % 2 ^ 32 < 2 ^ 31) :
    WP isa (ctr v.callee) s fun s' => Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (ctrR W SP D n) s.mem s'.mem ∧
      bytesAt s'.mem (w64 D) n = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem (w64 C) R) q (bytesAt s.mem (w64 D) n) := by
  refine WP.seq (WP.mono (ctrWhole_ok v L hR E hD hn hc hr hd hl hq (by omega_arith))
    fun s₄ ⟨E₄, rd₄, wr₄, f₄, d₄, cb₄⟩ => ?_)
  obtain hRb := rounds_le hR
  obtain k₄ : Spec.Siv.ctxCiph s₄.mem (w64 C) R = Spec.Siv.ctxCiph s.mem (w64 C) R :=
    ctxCiph_frame f₄ (ctrR_c L hD) hRb
  obtain sl := fun {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 256) => ctrR_slot L hD f₄ h₁ h₂
  refine WP.mono (ctrTail_ok v L hR E₄ (hD.of_eq rd₄ wr₄) hn (by rw [sl (by decide) (by decide)]; exact hc)
    (by rw [sl (by decide) (by decide)]; exact hr) (by rw [sl (by decide) (by decide)]; exact hd)
    (by rw [sl (by decide) (by decide)]; exact hl) (x := bytesAt s.mem (w64 D) n) (length_bytesAt _ _ _) cb₄
    (by rw [k₄]; exact d₄)) fun s₅ ⟨E₅, rd₅, wr₅, f₅, d₅⟩ => ⟨E₅, by rw [rd₅, rd₄], by rw [wr₅, wr₄], f₄.trans f₅, ?_⟩
  rw [d₅, k₄]
  exact ctrPart_all _ (fun y => Proof.Cmac.aesWith_length _ _ y) q _ (by rw [length_bytesAt])

end VG.Proof.AesSiv.X86

end

end

/-! ### `AesSiv.X86.Enc`, which this module and modules that import it used -/

section

/-! ### `AesSiv.X86.Entry`, which only this module used -/

section

/-!
# AES-SIV on x86: the entry of `encrypt` and `decrypt`

Untrusted: everything here is checked by Lean. The entry (`entry_ok`) saves
our caller's registers in `W` (AES-GCM's `save_ok`), copies the stack
arguments into their slots (`keeps_ok`): the slots (`Slots`) hold the
arguments. The exit is AES-GCM's (`exit_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt)
open VG.Proof.AesGcm.X86 (w64 slotv argA argsR argA_contains argA_sub SavedAt save_ok KeepEnv keeps_ok keepR
  runBlock_app_of in_off)

/-- The arguments the entry copies, and where. -/
abbrev entryPs : List (Nat × Nat) :=
  [(0, ctxO), (1, roundsO), (2, adsO), (3, leftO), (4, dataO), (5, lenO)]

theorem sivEntry_eq : sivEntry = entry 7 (entryPs.flatMap (fun p => keep p.1 p.2)) := rfl

/-- What the entry leaves. -/
structure Entered (s : State) (W : BitVec 32) (s' : State) : Prop where
  ebp : s'.gpr .ebp = W
  esp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : SavedAt s'.mem W s
  slots : ∀ p ∈ entryPs, slotv s'.mem W p.2 = arg s p.1
  frame : Frame [⟨w64 W + BitVec.ofNat 64 128, 2432⟩] s.mem s'.mem

/-- The entry, from `W` (the stack argument 7). -/
theorem entry_ok {s : State} {W : BitVec 32} (hW : arg s 7 = W) (wW : Covers [⟨w64 W, 2560⟩] s.wr)
    (rA : Covers [argsR (s.gpr .esp) 8] (s.rd ++ s.wr)) (aw : (argsR (s.gpr .esp) 8).Disjoint ⟨w64 W, 2560⟩)
    (fa : (s.gpr .esp).toNat + 4 + 4 * 8 ≤ 2 ^ 32) (fw : W.toNat + 2560 ≤ 2 ^ 32) :
    WP isa sivEntry s (Entered s W) := by
  rw [sivEntry_eq]
  generalize hSP : s.gpr .esp = SP at rA aw fa
  obtain i₀ : InRegions (s.rd ++ s.wr) (argA SP 7) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.seq (WP.of_runBlock ⟨_, by crun [hSP, i₀], ?_⟩)
  obtain hax : (s.setReg .eax (s.mem.readW (argA SP 7) 32)).gpr .eax = W := by
    rw [gpr_setReg_self, ← hSP]; exact hW
  let s₀ := s.setReg .eax (s.mem.readW (argA SP 7) 32)
  try rewrite [show s.setReg .eax (s.mem.readW (argA SP 7) 32) = s₀ from rfl] at *
  have hs₀ : s₀ = s.setReg .eax (s.mem.readW (argA SP 7) 32) := rfl
  obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok s₀ hax (by rw [hs₀]; exact wW) fw
  obtain sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide), hSP]
  have f₁' : Frame [⟨w64 W + BitVec.ofNat 64 128, 16⟩] s.mem s₁.mem := f₁
  obtain argW : ∀ {i}, i < 8 → ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region)],
      (⟨argA SP i, 4⟩ : Region).Disjoint r := fun hi _ _ hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (aw.sub_left (argA_sub hi fa)).sub_right (Offset.sub_base _ hk)
  obtain hA₁ : ∀ i < 8, s₁.mem.readW (argA SP i) 32 = arg s i := fun i hi => by
    rw [f₁'.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (argW hi (by decide)) (by decide)]
    rw [arg, argAddr, hSP]
  obtain ke : KeepEnv W SP 8 s₁ := ⟨bp₁, sp₁, by rw [wr₁]; exact wW, by rw [rd₁, wr₁]; exact rA, aw, fa, fw⟩
  obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok entryPs (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) ke
  obtain bp₃ : s₃.gpr .ebp = W := by rw [g₃ _ (by decide), bp₁]
  obtain sp₃ : s₃.gpr .esp = SP := by rw [g₃ _ (by decide), sp₁]
  refine WP.of_runBlock ⟨_, runBlock_app_of run₁ run₃, ?_⟩
  -- What the entry wrote.
  obtain f₃' : Frame [⟨w64 W + BitVec.ofNat 64 128, 2432⟩] s.mem s₃.mem := by
    refine (f₁'.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  obtain hsv : SavedAt s₃.mem W s := by
    have := sv₁.frame f₃ fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    obtain ⟨a, b, c, d⟩ := this
    refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
      simp only [hs₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax),
        gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
  refine ⟨bp₃, by rw [sp₃, hSP], by rw [rd₃, rd₁]; rfl, by rw [wr₃, wr₁]; rfl, hsv, ?_, f₃'⟩
  intro p hp
  obtain e := sl₃ p hp
  obtain hp1 : p.1 < 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [hA₁ p.1 hp1] at e
  exact e

end VG.Proof.AesSiv.X86

end

end


/-!
# AES-SIV on x86: S2V of the associated data, and `vg_aes_siv_encrypt`

Untrusted: everything here is checked by Lean. `encS2v` saves our caller's
registers and keeps the arguments in `W` (`entry_ok`), sets S2V's first
state (`start_ok`), absorbs the components of associated data
(`s2vAds_ok`) and makes the data S2V's last string (`dataStr_ok`):
`encS2v_ok`. `encrypt` then finishes S2V with the plaintext into the IV at
`W` (`finish_ok`), sets the counter from it (`counter_ok`), encrypts the
plaintext with CTR (`ctr_ok`), copies the IV to `siv` (`sivOut_ok`) and
restores the registers (`encrypt_wp`):
`encryptWith` of the context's PRF and cipher (`Spec.Siv.encryptWith_eq`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot restore)
open VG.Proof.AesGcm.X86 (w64 slotv argsR SavedAt savedR exit_ok readW_writeW_off covers_left covers_off ret_below
  length_bytesAt CT argA argA_sub argA_contains w64_add)

/-- What `encrypt` and `decrypt` start from: the key context `C`, `R`
rounds, the `N` descriptors at `A`, the `n` bytes of data at `D`, `siv`
(16 bytes at `T`, which they may at least read) and the working space `W`,
the arguments on the stack at `SP`. -/
structure EPre (C W SP A D T : BitVec 32) (R N n : Nat) (s : State) : Prop where
  ads : AdCtx s C W SP A R N
  data : Dat C W SP s D n
  perm : Perm C W s
  sp : s.gpr .esp = SP
  a0 : arg s 0 = C
  a1 : arg s 1 = BitVec.ofNat 32 R
  a2 : arg s 2 = A
  a3 : arg s 3 = BitVec.ofNat 32 N
  a4 : arg s 4 = D
  a5 : arg s 5 = BitVec.ofNat 32 n
  a6 : arg s 6 = T
  a7 : arg s 7 = W
  rA : Covers [argsR SP 8] (s.rd ++ s.wr)
  aw : (argsR SP 8).Disjoint ⟨w64 W, 2576⟩
  ad : (argsR SP 8).Disjoint ⟨w64 D, n⟩
  as : (below SP 60).Disjoint (argsR SP 8)
  fa : SP.toNat + 4 + 4 * 8 ≤ 2 ^ 32
  ret : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 W, 2576⟩
  retD : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 D, n⟩
  retT : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 T, 16⟩
  n32 : n < 2 ^ 32
  tfit : T.toNat + 16 ≤ 2 ^ 32
  t_rd : Covers [⟨w64 T, 16⟩] (s.rd ++ s.wr)
  t_w : (⟨w64 T, 16⟩ : Region).Disjoint ⟨w64 W, 2576⟩
  t_stk : (below SP 60).Disjoint ⟨w64 T, 16⟩

/-- The data as S2V's last string. -/
theorem dataStr_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {D : BitVec 32} {n : Nat}
    (hd : slotv s.mem W dataO = D) (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) :
    ∃ s', runBlock isa [.mov .eax (slot dataO), .store (at_ .ebp strO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp slenO) .eax] s = some s' ∧
      s'.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 strO) D).writeW (w64 W + BitVec.ofNat 64 slenO)
        (BitVec.ofNat 32 n) ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hd, hl], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hd, hl]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- The data as S2V's last string: what `cmacOf` and `finish` start from. -/
theorem dataStr_pre {C W SP : BitVec 32} (L : Lay C W SP) {s₀ : State} {R : Nat} {D : BitVec 32} {n : Nat}
    {ext : List Region} {s : State} (K : Kept s₀ C W SP R D n ext s)
    (hext : ∀ r ∈ ext, r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩) (hD : Buf W SP s D n) (hn : n < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .eax (slot dataO), .store (at_ .ebp strO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp slenO) .eax] s = some s' ∧ CmacPre C W SP R D n s' ∧ Kept s₀ C W SP R D n ext s' ∧
      Frame [⟨w64 W + BitVec.ofNat 64 strO, 8⟩] s.mem s'.mem := by
  obtain ⟨s₄, run₄, m₄, bp₄, sp₄, rd₄, wr₄⟩ := dataStr_ok L K.env K.slots.data K.slots.len
  obtain E₄ : Env C W SP s₄ := ⟨bp₄, sp₄, K.env.perm.of_eq rd₄ wr₄⟩
  have c (d : Nat) (hd : d + 4 ≤ 8) : (⟨w64 W + BitVec.ofNat 64 strO, 8⟩ : Region).Contains
      (w64 W + BitVec.ofNat 64 strO + BitVec.ofNat 64 d) 4 := Offset.contains_base _ hd (by omega_arith)
  obtain c0 : (⟨w64 W + BitVec.ofNat 64 strO, 8⟩ : Region).Contains (w64 W + BitVec.ofNat 64 strO) (32 / 8) := by
    simpa using c 0 (by decide)
  obtain c4 : (⟨w64 W + BitVec.ofNat 64 strO, 8⟩ : Region).Contains (w64 W + BitVec.ofNat 64 slenO) (32 / 8) := by
    obtain e : w64 W + BitVec.ofNat 64 slenO = w64 W + BitVec.ofNat 64 strO + BitVec.ofNat 64 4 := by
      rw [Offset.add_add]
    rw [e]; exact c 4 (by decide)
  obtain f₄ : Frame [⟨w64 W + BitVec.ofNat 64 strO, 8⟩] s.mem s₄.mem := by
    rw [m₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c4
  obtain K₄ : Kept s₀ C W SP R D n ext s₄ := K.step L hext E₄ rd₄ wr₄ f₄ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact .inl ⟨wS W, by simp, sub_wS (by decide) (by decide)⟩
  refine ⟨s₄, run₄, ⟨E₄, K₄.slots.ctx, K₄.slots.rounds, ?_, ?_, hn, hD.of_eq rd₄ wr₄⟩, K₄, f₄⟩
  · rw [m₄, slotv, readW_writeW_off _ _ _ (.inl (by decide)) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [m₄]; exact Mem.readW_writeW_self32 _ _ _

/-- What `encS2v` leaves: the data as S2V's last string, and `D` S2V's state
of the components. -/
structure S2vOut (C W SP A D : BitVec 32) (R N n : Nat) (s s' : State) : Prop where
  pre : CmacPre C W SP R D n s'
  kept : Kept s C W SP R D n [] s'
  acc : bytesAt s'.mem (w64 W + BitVec.ofNat 64 dOff) 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.components 32 s.mem (w64 A) N)

/-- The entry's memory, as `Kept` (the slots are the arguments). -/
theorem kept_of_entered {C W SP A D T : BitVec 32} {R N n : Nat} {s s₁ : State} (h : EPre C W SP A D T R N n s)
    (en : Entered s W s₁) : Kept s C W SP R D n [] s₁ ∧ slotv s₁.mem W adsO = A ∧
      slotv s₁.mem W leftO = BitVec.ofNat 32 N := by
  have sl := en.slots
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at sl
  obtain ⟨c₁, r₁, a₁, l₁, d₁, n₁⟩ := sl
  refine ⟨{ env := ⟨en.ebp, by rw [en.esp, h.sp], h.perm.of_eq en.rd en.wr⟩
            rd := en.rd
            wr := en.wr
            slots := ⟨c₁.trans h.a0, r₁.trans h.a1, d₁.trans h.a4, n₁.trans h.a5⟩
            saved := en.saved
            big := en.frame.sub fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact ⟨⟨w64 W + BitVec.ofNat 64 16, 2560⟩, by simp, Offset.sub _ (by decide) (by decide)⟩ },
    a₁.trans h.a2, l₁.trans h.a3⟩

theorem entry_wp {C W SP A D T : BitVec 32} {R N n : Nat} {s : State} (h : EPre C W SP A D T R N n s) :
    WP isa sivEntry s (Entered s W) := by
  have L := h.ads.lay
  obtain wW : Covers [⟨w64 W, 2560⟩] s.wr := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.perm.w a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_arith⟩
  obtain aw : (argsR (s.gpr .esp) 8).Disjoint ⟨w64 W, 2560⟩ := by
    rw [h.sp]; exact h.aw.sub_right (Region.sub_prefix (by decide))
  exact entry_ok (s := s) (W := W) h.a7 wW (by rw [h.sp]; exact h.rA) aw (by rw [h.sp]; exact h.fa)
    (by have := L.fw; omega_arith)

/-- S2V's first state, after the entry. -/
theorem start_wp (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {s s₁ : State}
    (h : EPre C W SP A D T R N n s) (en : Entered s W s₁) :
    WP isa (start v.callee v.suffix) s₁ (AInv s C W SP A R N D n 0) := by
  have L := h.ads.lay
  obtain ⟨K₁, a₁, l₁⟩ := kept_of_entered h en
  refine WP.mono (start_ok v L h.ads.rounds K₁) fun s₂ ⟨K₂, f₂, st₂⟩ => ?_
  obtain k₂ : ∀ o, 176 ≤ o → o + 4 ≤ 200 → slotv s₂.mem W o = slotv s₁.mem W o := fun o h₁ h₂ =>
    f₂.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
      · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact (L.stk_w' (by omega_arith)).symm) (by decide)
  exact ⟨K₂, Nat.zero_le _, by rw [k₂ _ (by decide) (by decide), a₁, Nat.mul_zero]; exact (BitVec.add_zero _).symm,
    by rw [k₂ _ (by decide) (by decide), l₁, Nat.sub_zero], by rw [List.take_zero, Spec.Siv.s2vAcc, List.foldl_nil]; exact st₂⟩

/-- The data as S2V's last string, after S2V of the associated data. -/
theorem s2vEnd_ok {C W SP A D T : BitVec 32} {R N n : Nat} {s s₃ : State} (h : EPre C W SP A D T R N n s)
    (I : AInv s C W SP A R N D n N s₃) :
    ∃ s₄, runBlock isa [.mov .eax (slot dataO), .store (at_ .ebp strO) .eax, .mov .eax (slot lenO),
      .store (at_ .ebp slenO) .eax] s₃ = some s₄ ∧ S2vOut C W SP A D R N n s s₄ := by
  have L := h.ads.lay
  obtain ⟨s₄, run₄, P₄, K₄, f₄⟩ := dataStr_pre L I.kept (by simp) (h.data.buf.of_eq I.kept.rd I.kept.wr) h.n32
  refine ⟨s₄, run₄, P₄, K₄, ?_⟩
  rw [Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
    (by decide), I.acc, components_take_all]

theorem encS2v_ok (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {s : State}
    (h : EPre C W SP A D T R N n s) :
    WP isa (encS2v v.callee v.suffix) s (S2vOut C W SP A D R N n s) := by
  refine WP.seq (WP.mono (entry_wp h) fun s₁ en => ?_)
  refine WP.seq (WP.mono (start_wp v h en) fun s₂ I₀ => ?_)
  refine WP.seq (WP.mono (s2vAds_ok v h.ads I₀) fun s₃ I => ?_)
  obtain ⟨s₄, run₄, O⟩ := s2vEnd_ok h I
  exact WP.of_runBlock ⟨s₄, run₄, O⟩

/-! ## `vg_aes_siv_encrypt` -/

theorem Kept.widen {s₀ : State} {C W SP : BitVec 32} {R : Nat} {D : BitVec 32} {n : Nat} {ext : List Region}
    {s : State} (h : Kept s₀ C W SP R D n ext s) (e : Region) : Kept s₀ C W SP R D n (ext ++ [e]) s :=
  { h with big := h.big.mono fun r hr => by rw [← List.append_assoc]; exact List.mem_append_left _ hr }

/-- What `finish out` writes: the IV at `W` (which the pieces name in `ext`) or
the IV at `W + 112`, and parts of `W` the pieces write. -/
theorem finR_wR {W SP : BitVec 32} {out : Nat} {ext : List Region}
    (hout : out = 0 ∧ (⟨w64 W, 16⟩ : Region) ∈ ext ∨ out = 112) :
    ∀ r ∈ finR W SP out, (∃ r' ∈ wR W SP, Region.Sub r r') ∨ ∃ r' ∈ ext, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hout with ⟨rfl, he⟩ | rfl
    · exact .inr ⟨_, he, Offset.sub_base _ (by decide)⟩
    · exact .inl ⟨wA W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact .inl ⟨wA W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact .inl ⟨wB W, by simp, fun _ h => h⟩
  · exact .inl ⟨wS W, by simp, fun _ h => h⟩
  · exact .inl ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact .inl ⟨below SP 60, by simp, fun _ h => h⟩

theorem ctrR_wR {W SP D : BitVec 32} {n : Nat} {ext : List Region} (he : (⟨w64 D, n⟩ : Region) ∈ ext) :
    ∀ r ∈ ctrR W SP D n, (∃ r' ∈ wR W SP, Region.Sub r r') ∨ ∃ r' ∈ ext, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl ⟨wA W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact .inl ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact .inl ⟨below SP 60, by simp, fun _ h => h⟩
  · exact .inr ⟨_, he, fun _ h => h⟩

/-- The counter block: written by `counter`, in `wA`. -/
theorem counter_wR {W SP : BitVec 32} {e : List Region} :
    ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 cbOff, 16⟩ : Region)],
      (∃ r' ∈ wR W SP, Region.Sub r r') ∨ ∃ r' ∈ e, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact .inl ⟨wA W, by simp, Offset.sub _ (by decide) (by decide)⟩

/-- `siv`'s address, the stack argument 6, as on entry, after code that wrote
apart from the arguments. -/
theorem Kept.arg6 {C W SP A D T : BitVec 32} {R N n : Nat} {s₀ s : State} (h : EPre C W SP A D T R N n s₀)
    {ext : List Region} (K : Kept s₀ C W SP R D n ext s)
    (he : ∀ r ∈ ext, (argsR SP 8).Disjoint r) :
    s.mem.readW (argA SP 6) 32 = T ∧ InRegions (s.rd ++ s.wr) (argA SP 6) 4 := by
  obtain hs6 := argA_sub (SP := SP) (n := 8) (i := 6) (by decide) h.fa
  refine ⟨?_, by rw [K.rd, K.wr]; exact h.rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) h.fa⟩⟩
  rw [K.big.readW (r := ⟨argA SP 6, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · exact (h.aw.sub_left hs6).sub_right (Lay.wSub (by decide))
    · exact h.as.symm.sub_left hs6
    · exact (he r hr).sub_left hs6) (by decide), ← h.a6, arg, argAddr, h.sp]

/-- `sivOut`: the IV at `W` copied to `T`, the stack argument 6. -/
theorem sivOut_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {T : BitVec 32}
    (hin : InRegions (s.rd ++ s.wr) (argA SP 6) 4) (hv : s.mem.readW (argA SP 6) 32 = T)
    (tW : Covers [⟨w64 T, 16⟩] s.wr) (fT : T.toNat + 16 ≤ 2 ^ 32) :
    WP isa sivOut s fun s' => bytesAt s'.mem (w64 T) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 0) 16 ∧
      Frame [⟨w64 T, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain aT : ∀ {k}, k < 16 → w64 (T + BitVec.ofNat 32 k) = w64 T + BitVec.ofNat 64 k := fun hk => w64_add (by omega_arith)
  obtain tIn : ∀ {k}, k + 4 ≤ 16 → InRegions s.wr (w64 T + BitVec.ofNat 64 k) 4 := fun hk =>
    Proof.AesGcm.X86.in_off tW hk (by decide)
  obtain hs := Proof.AesGcm.X86.store4_eq s.mem T 0
  simp only [Nat.reduceAdd] at hs
  refine WP.seq (WP.of_runBlock ⟨_, by crun [E.ebp, E.esp, L.aW, E.perm.wR, hin, hv], ?_⟩)
  refine WP.of_runBlock ⟨_, by crun [aT, tIn], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hs]
    rw [show w64 T + 0#64 = w64 T from BitVec.add_zero _, Cmac.bytesAt_store4, Cmac.bytesAt_split4, Cmac.le4_readW,
      Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]
  · cmems [hs]
    rw [show w64 T + 0#64 = w64 T from BitVec.add_zero _]
    exact Cmac.frame_store4 _ _ _ _ _
  · cregs [E.ebp]
  · cregs [E.esp]
  · cmems []
  · cmems []

/-- `vg_aes_siv_encrypt`: the synthetic IV at `T` and the ciphertext in place. -/
theorem encrypt_wp (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {s : State}
    (h : EPre C W SP A D T R N n s) (hTw : Covers [⟨w64 T, 16⟩] s.wr)
    (hTd : (⟨w64 T, 16⟩ : Region).Disjoint ⟨w64 D, n⟩) :
    WP isa (encrypt v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.ctxCiph s.mem (w64 C) R)
          (Spec.Siv.components 32 s.mem (w64 A) N) (bytesAt s.mem (w64 D) n) =
        (bytesAt s'.mem (w64 T) 16, bytesAt s'.mem (w64 D) n) := by
  have L := h.ads.lay
  have hR := h.ads.rounds
  obtain hRb := rounds_le hR
  obtain hW16 : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := by
    simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
  obtain hDw : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    h.data.buf.w.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.mono (encS2v_ok v h) fun s₁ O => ?_)
  have K₁ := O.kept
  refine WP.seq (WP.mono (finish_ok v L hR O.pre (out := 0) (.inl rfl)) fun s₂ F => ?_)
  obtain K₂ : Kept s C W SP R D n [⟨w64 W, 16⟩] s₂ := (K₁.widen ⟨w64 W, 16⟩).step L
    (fun r hr => by simp only [List.nil_append, List.mem_singleton] at hr; subst hr; exact hW16)
    F.env F.rd F.wr F.frame (finR_wR (.inl ⟨rfl, by simp⟩))
  obtain ⟨s₃, run₃, m₃, bp₃, sp₃, rd₃, wr₃⟩ := counter_ok L F.env
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain E₃ : Env C W SP s₃ := ⟨bp₃, sp₃, F.env.perm.of_eq rd₃ wr₃⟩
  obtain f₃ : Frame [⟨w64 W + BitVec.ofNat 64 cbOff, 16⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  obtain K₃ : Kept s C W SP R D n [⟨w64 W, 16⟩] s₃ := K₂.step L
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hW16) E₃ rd₃ wr₃ f₃ counter_wR
  obtain hq : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 cbOff) 16 = Spec.Siv.counter (bytesAt s₂.mem (w64 W) 16) := by
    rw [m₃]; exact counter_bytes _ _
  obtain hD₃ : Dat C W SP s₃ D n := h.data.of_eq K₃.rd K₃.wr
  refine WP.seq (WP.mono (ctr_ok v L hR E₃ hD₃ h.n32 K₃.slots.ctx K₃.slots.rounds K₃.slots.data K₃.slots.len hq
    (counter_low _)) fun s₄ ⟨E₄, rd₄, wr₄, f₄, d₄⟩ => ?_)
  obtain K₄ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₄ := (K₃.widen _).step L (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hW16
      · exact hDw) E₄ rd₄ wr₄ f₄ (ctrR_wR (by simp))
  -- The IV copied to `siv`.
  obtain hs6 := argA_sub (SP := SP) (n := 8) (i := 6) (by decide) h.fa
  obtain v6 : s₄.mem.readW (argA SP 6) 32 = T := by
    rw [K₄.big.readW (r := ⟨argA SP 6, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (h.aw.sub_left hs6).sub_right (Lay.wSub (by decide))
      · exact h.as.symm.sub_left hs6
      · exact (h.aw.sub_left hs6).sub_right (Region.sub_prefix (by decide))
      · exact h.ad.sub_left hs6) (by decide), ← h.a6, arg, argAddr, h.sp]
  obtain i6 : InRegions (s₄.rd ++ s₄.wr) (argA SP 6) 4 := by
    rw [K₄.rd, K₄.wr]; exact h.rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) h.fa⟩
  refine WP.seq (WP.mono (sivOut_ok L K₄.env i6 v6 (by rw [K₄.wr]; exact hTw) h.tfit)
    fun s₅ ⟨iv₅, f₅, bp₅, sp₅, rd₅, wr₅⟩ => ?_)
  obtain hTW : (⟨w64 T, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    h.t_w.sub_right (Lay.wSub (by decide))
  obtain K₅ : Kept s C W SP R D n ([⟨w64 W, 16⟩, ⟨w64 D, n⟩] ++ [⟨w64 T, 16⟩]) s₅ := (K₄.widen _).step L
    (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hW16
      · exact hDw
      · exact hTW) ⟨bp₅, sp₅, K₄.env.perm.of_eq rd₅ wr₅⟩ rd₅ wr₅ f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, by simp, fun _ h => h⟩)
  obtain hret : s₅.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32 := by
    rw [h.sp]
    exact K₅.big.readW (r := ⟨w64 SP, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h.ret.sub_right (Lay.wSub (by decide))
      · exact ret_below L.sp
      · exact h.ret.sub_right (Region.sub_prefix (by decide))
      · exact h.retD
      · exact h.retT) (by decide)
  refine WP.mono (exit_ok K₅.env.ebp (by rw [K₅.env.esp, h.sp]) (covers_left (fun a m ⟨r, hr, hc⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact K₅.env.perm.w a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_arith⟩))
    (by have := L.fw; omega_arith) K₅.saved hret) fun s₆ ⟨ab, m₆, _, _, _⟩ => ⟨ab, ?_⟩
  obtain pD : bytesAt s₅.mem (w64 D) n = bytesAt s₄.mem (w64 D) n :=
    Proof.AesGcm.X86.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hTd.symm) (by have := h.data.buf.lt; omega_arith)
  -- The values.
  obtain dW : ∀ r ∈ ctrR W SP D n, (⟨w64 W, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
    · exact (h.data.buf.w.sub_right (Region.sub_prefix (by decide))).symm
  obtain iv : bytesAt s₄.mem (w64 W) 16 = bytesAt s₂.mem (w64 W) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₄ dW (by decide), Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)) (by decide)]
  obtain dc : ∀ r ∈ ([] : List Region), (⟨w64 C, 512⟩ : Region).Disjoint r := by simp
  obtain mac₁ : Spec.Siv.ctxMac s₁.mem (w64 C) R = Spec.Siv.ctxMac s.mem (w64 C) R := K₁.mac L hR dc
  obtain ciph₃ : Spec.Siv.ctxCiph s₃.mem (w64 C) R = Spec.Siv.ctxCiph s.mem (w64 C) R :=
    ctxCiph_frame K₃.big (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.c_w.sub_right (Lay.wSub (by decide))
      · exact L.stk_c.symm
      · exact L.c_w.sub_right (Region.sub_prefix (by decide))) hRb
  obtain dDW : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 16⟩ := h.data.buf.w.sub_right (Region.sub_prefix (by decide))
  obtain p₁ : bytesAt s₁.mem (w64 D) n = bytesAt s.mem (w64 D) n :=
    K₁.bytes h.data.buf.w h.data.buf.stk (by simp) (by have := h.data.buf.lt; omega_arith)
  obtain p₃ : bytesAt s₃.mem (w64 D) n = bytesAt s.mem (w64 D) n :=
    K₃.bytes h.data.buf.w h.data.buf.stk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dDW) (by have := h.data.buf.lt; omega_arith)
  have o₂ := F.out
  rw [BitVec.add_zero] at o₂
  rw [m₆, iv₅, BitVec.add_zero, pD, Spec.Siv.encryptWith_eq, Spec.Siv.sealWith, d₄, iv, o₂, mac₁, O.acc, p₁,
    ciph₃, p₃]

end VG.Proof.AesSiv.X86

end

end

/-!
# AES-SIV on x86: `vg_aes_siv_decrypt`

Untrusted: everything here is checked by Lean. `decrypt` copies the received
IV from `siv` to `W` (`sivIn_ok`) after S2V of the associated data, decrypts
the data with CTR from it, finishes S2V with the plaintext into `W + 112`,
compares the IVs without a branch and masks the data with the result
(`decrypt_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot restore maskWords)
open VG.Proof.AesGcm.X86 (exit_ok ret_below covers_left readW_writeW_off argA argA_sub argA_contains maskWords_ok)
open VG.Proof.AesGcm.X86 (w64 slotv bytes16_eq xor4_eq_zero w64_add in_of_covers succ_ofNat32 add_zero32 pred_count
  pred_beq bytesAt_succ length_bytesAt and_self_beq32 CT)

/-- `cmp eax, 1` and `adc` of 0 after the OR of the XORs of two blocks' words:
1 if they are equal, else 0. -/
theorem cmpAdc (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    0#32 + 0#32 + BitVec.setWidth 32 (BitVec.ofBool (decide
      ((a₀ ^^^ b₀ ||| a₁ ^^^ b₁ ||| a₂ ^^^ b₂ ||| a₃ ^^^ b₃).toNat < (1#32).toNat))) =
      BitVec.ofNat 32 (if a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ then 1 else 0) := by
  obtain e := xor4_eq_zero a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
  by_cases h : a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp only [and_self, ↓reduceIte, BitVec.xor_self, BitVec.or_self]
    decide
  · have h0 : (a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃) ≠ 0 := fun h' => h (e.mp h')
    obtain hne : ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat ≠ 0 := fun h' =>
      h0 (BitVec.eq_of_toNat_eq (by simpa using h'))
    obtain hlt : ¬ ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat < (1#32).toNat := by
      rw [BitVec.toNat_ofNat]; omega_arith
    simp only [h, ↓reduceIte, decide_eq_false hlt]
    rfl

/-- Whether the IVs at `W` and `W + 112` are equal, as a word. -/
abbrev okVal (m : Mem) (W : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (if bytesAt m (w64 W) 16 = bytesAt m (w64 W + BitVec.ofNat 64 tOff) 16 then 1 else 0)

theorem compare_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) :
    ∃ s', runBlock isa compare s = some s' ∧ s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 okO) (okVal s.mem W) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [Impl.AesSiv.X86.compare, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_, fun r h₁ h₂ => ?_, ?_, ?_⟩
  · cmems []
    rw [cmpAdc]
    simp only [okVal, bytes16_eq, BitVec.add_zero, add_ofNat_assoc, Nat.reduceAdd, tOff]
  · cregs []
  all_goals cmems []

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
    (if c then bytesAt m P j else Spec.Siv.zeros j).length = j := by
  cases c <;> simp [Spec.Siv.zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else Spec.Siv.zeros (j + 1)) =
      (if c then bytesAt m P j else Spec.Siv.zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [Spec.Siv.zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`, for `ok` (at `W + okO`) 1 or 0. -/
theorem mask_ok {C W SP : BitVec 32} {s : State} (L : Lay C W SP) (E : Env C W SP s) {D : BitVec 32} {n : Nat}
    (hDp : slotv s.mem W dataO = D) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32)
    (hD : Buf W SP s D n) (hDw : Covers [⟨w64 D, n⟩] s.wr) {c : Bool}
    (hok : slotv s.mem W okO = if c then 1 else 0) :
    WP isa mask s fun s' => Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) n else Spec.Siv.zeros n) := by
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
  obtain E₁ : Env C W SP s₁ := E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨E₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, writeBytes_nil]
  obtain hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  obtain ⟨s₂, run₂, m₂, bx₂, di₂, cx₂, bp₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧ s₂.mem = s.mem ∧
      s₂.gpr .ebx = 0 - (if c then 1 else 0) ∧ s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n ∧
      s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    obtain hok₁ : slotv s₁.mem W okO = if c then 1 else 0 := by rw [m₁]; exact hok
    obtain hd₁ : slotv s₁.mem W dataO = D := by rw [m₁]; exact hDp
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
  obtain mem₄ : s₄.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) j₀ else Spec.Siv.zeros j₀) := by
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
      t.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) j else Spec.Siv.zeros j) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t.gpr r = s₂.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - j₀) _
    ⟨j₀, rfl, hj₁, by rw [g₄, di₃], by rw [g₄, cx₃], mem₄, gg₄, rd₄', wr₄'⟩
  rintro k t ⟨j, rfl, hj, di, cx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', zf', g', rd', wr'⟩ := maskStep_ok t (P := D) (i := j) (n := n) (c := c) di cx
    (by rw [g _ (by decide) (by decide) (by decide), bx₂]) (w64_add (by omega_arith))
    (by rw [rd, wr]; exact in_of_covers hD.rd hj (by omega_arith))
    (by rw [wr]; exact in_of_covers hDw hj (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  obtain fr : Frame [⟨w64 D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  obtain hq : t.mem (w64 D + BitVec.ofNat 64 j) = s.mem (w64 D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 D) (show j < 2 ^ 64 by omega_arith)] at hcon; omega_arith
  obtain hmem : t'.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) (j + 1) else Spec.Siv.zeros (j + 1)) := by
    rw [mem', hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega_arith), length_mask]
  obtain hz : t'.zf = some (decide (j + 1 = n)) := by rw [zf', pred_beq hj hn32]
  obtain gg : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t'.gpr r = s₂.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  obtain E' : Env C W SP t' := ⟨by rw [gg _ (by decide) (by decide) (by decide), bp₂],
    by rw [gg _ (by decide) (by decide) (by decide), sp₂], E.perm.of_eq (by rw [rd', rd]) (by rw [wr', wr])⟩
  by_cases he : j + 1 = n
  · left
    exact ⟨by simp [eval, hz, he], E', by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, di',
      by rw [cx', pred_count hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩


/-! ## `vg_aes_siv_decrypt` -/

theorem okVal_eq (m : Mem) (W : BitVec 32) :
    okVal m W = if decide (bytesAt m (w64 W) 16 = bytesAt m (w64 W + BitVec.ofNat 64 tOff) 16) then 1 else 0 := by
  unfold okVal; split <;> simp_all

theorem retEax_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) :
    ∃ s', runBlock isa [.mov .eax (slot okO)] s = some s' ∧ s'.gpr .eax = slotv s.mem W okO ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR], ?_, fun r h₁ => ?_, ?_, ?_, ?_⟩
  · cregs []
  · cregs []
  all_goals cmems []

/-- `sivIn`: the IV at `T`, the stack argument 6, copied to `W`. -/
theorem sivIn_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {T : BitVec 32}
    (hin : InRegions (s.rd ++ s.wr) (argA SP 6) 4) (hv : s.mem.readW (argA SP 6) 32 = T)
    (tR : Covers [⟨w64 T, 16⟩] (s.rd ++ s.wr)) (fT : T.toNat + 16 ≤ 2 ^ 32) :
    WP isa sivIn s fun s' => bytesAt s'.mem (w64 W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (w64 T + BitVec.ofNat 64 0) 16 ∧
      Frame [⟨w64 W + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain aT : ∀ {k}, k < 16 → w64 (T + BitVec.ofNat 32 k) = w64 T + BitVec.ofNat 64 k := fun hk => w64_add (by omega_arith)
  obtain tIn : ∀ {k}, k + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (w64 T + BitVec.ofNat 64 k) 4 := fun hk =>
    Proof.AesGcm.X86.in_off tR hk (by decide)
  obtain hs := Proof.AesGcm.X86.store4_eq s.mem W 0
  simp only [Nat.reduceAdd] at hs
  refine WP.seq (WP.of_runBlock ⟨_, by crun [E.esp, hin, hv], ?_⟩)
  refine WP.of_runBlock ⟨_, by crun [aT, tIn, E.ebp, L.aW, E.perm.wW], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hs]
    rw [Cmac.bytesAt_store4, Cmac.bytesAt_split4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW,
      add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]
  · cmems [hs]
    exact Cmac.frame_store4 _ _ _ _ _
  · cregs [E.ebp]
  · cregs [E.esp]
  · cmems []
  · cmems []

/-- What a piece writes in `wR` or the data misses the IV at `W`. -/
theorem w16_dis {C W SP D : BitVec 32} {n : Nat} (L : Lay C W SP)
    (hD : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 D, n⟩) {rs : List Region}
    (hs : ∀ r ∈ rs, (∃ r' ∈ wR W SP, Region.Sub r r') ∨ ∃ r' ∈ [(⟨w64 D, n⟩ : Region)], Region.Sub r r') :
    ∀ r ∈ rs, (⟨w64 W, 16⟩ : Region).Disjoint r := by
  intro r hr
  rcases hs r hr with ⟨r', hr', hsub⟩ | ⟨r', hr', hsub⟩
  · refine Region.Disjoint.sub_right ?_ hsub
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 16) (k := 112) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 144) (k := 32) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 184) (k := 8) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 200) (k := 56) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 256) (k := 2320) (.inl (by decide)) (by decide)
        (by decide)
    · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact hD.sub_right hsub

/-- `vg_aes_siv_decrypt`: the plaintext and 1 if the IV at `T` is right,
zeros and 0 if not. -/
theorem decrypt_wp (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {s : State}
    (h : EPre C W SP A D T R N n s) :
    WP isa (decrypt v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      match Spec.Siv.decryptWith (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.ctxCiph s.mem (w64 C) R)
          (Spec.Siv.components 32 s.mem (w64 A) N) (bytesAt s.mem (w64 T) 16) (bytesAt s.mem (w64 D) n) with
      | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem (w64 D) n = pt
      | none => s'.gpr .eax = 0 ∧ bytesAt s'.mem (w64 D) n = Spec.Siv.zeros n := by
  have L := h.ads.lay
  have hR := h.ads.rounds
  obtain hRb := rounds_le hR
  obtain hDw : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    h.data.buf.w.sub_right (Lay.wSub (by decide))
  obtain hW16 : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := by
    simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
  obtain dDW : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 D, n⟩ :=
    (h.data.buf.w.sub_right (Region.sub_prefix (by decide))).symm
  obtain hext1 : ∀ r ∈ [(⟨w64 W, 16⟩ : Region)], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hW16
  obtain hext2 : ∀ r ∈ [(⟨w64 W, 16⟩ : Region), ⟨w64 D, n⟩], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hW16
      · exact hDw
  refine WP.seq (WP.mono (encS2v_ok v h) fun s₀ O => ?_)
  have K₀ := O.kept
  -- The received IV copied from `siv`.
  obtain hs6 := argA_sub (SP := SP) (n := 8) (i := 6) (by decide) h.fa
  obtain v6 : s₀.mem.readW (argA SP 6) 32 = T := by
    rw [K₀.big.readW (r := ⟨argA SP 6, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.aw.sub_left hs6).sub_right (Lay.wSub (by decide))
      · exact h.as.symm.sub_left hs6) (by decide), ← h.a6, arg, argAddr, h.sp]
  obtain i6 : InRegions (s₀.rd ++ s₀.wr) (argA SP 6) 4 := by
    rw [K₀.rd, K₀.wr]; exact h.rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) h.fa⟩
  refine WP.seq (WP.mono (sivIn_ok L K₀.env i6 v6 (by rw [K₀.rd, K₀.wr]; exact h.t_rd) h.tfit)
    fun s₁ ⟨iv₁, fIn, bp₁, sp₁, rd₁, wr₁⟩ => ?_)
  obtain K₁ : Kept s C W SP R D n [⟨w64 W, 16⟩] s₁ := (K₀.widen _).step L hext1
    ⟨bp₁, sp₁, K₀.env.perm.of_eq rd₁ wr₁⟩ rd₁ wr₁ fIn (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inr ⟨⟨w64 W, 16⟩, by simp, Offset.sub_base (k := 16) _ (by decide)⟩)
  obtain ivT : bytesAt s₁.mem (w64 W) 16 = bytesAt s.mem (w64 T) 16 := by
    rw [BitVec.add_zero, BitVec.add_zero] at iv₁
    rw [iv₁]
    exact K₀.bytes h.t_w h.t_stk (by simp) (by decide)
  -- CTR from the IV.
  obtain ⟨s₂, run₂, m₂, bp₂, sp₂, rd₂, wr₂⟩ := counter_ok L K₁.env
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain E₂ : Env C W SP s₂ := ⟨bp₂, sp₂, K₁.env.perm.of_eq rd₂ wr₂⟩
  obtain f₂ : Frame [⟨w64 W + BitVec.ofNat 64 cbOff, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  obtain K₂ : Kept s C W SP R D n [⟨w64 W, 16⟩] s₂ := K₁.step L hext1 E₂ rd₂ wr₂ f₂ counter_wR
  obtain hq : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 cbOff) 16 = Spec.Siv.counter (bytesAt s₁.mem (w64 W) 16) := by
    rw [m₂]; exact counter_bytes _ _
  refine WP.seq (WP.mono (ctr_ok v L hR E₂ (h.data.of_eq K₂.rd K₂.wr) h.n32 K₂.slots.ctx K₂.slots.rounds
    K₂.slots.data K₂.slots.len hq (counter_low _)) fun s₃ ⟨E₃, rd₃, wr₃, f₃, d₃⟩ => ?_)
  obtain K₃ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₃ :=
    (K₂.widen _).step L hext2 E₃ rd₃ wr₃ f₃ (ctrR_wR (by simp))
  -- S2V's end with the plaintext into `W + 112`.
  obtain ⟨s₄, run₄, P₄, K₄, f₄⟩ := dataStr_pre L K₃ hext2 (h.data.buf.of_eq K₃.rd K₃.wr) h.n32
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  refine WP.seq (WP.mono (finish_ok v L hR P₄ (out := tOff) (.inr rfl)) fun s₅ F => ?_)
  obtain K₅ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₅ :=
    K₄.step L hext2 F.env F.rd F.wr F.frame (finR_wR (.inr rfl))
  -- The comparison.
  obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ := compare_ok L F.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  obtain E₆ : Env C W SP s₆ := F.env.keep (g₆ _ (by decide) (by decide)) (g₆ _ (by decide) (by decide)) rd₆ wr₆
  obtain f₆ : Frame [⟨w64 W + BitVec.ofNat 64 okO, 4⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain K₆ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₆ := K₅.step L hext2 E₆ rd₆ wr₆ f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact .inl ⟨wS W, by simp, sub_wS (by decide) (by decide)⟩
  obtain hok : slotv s₆.mem W okO = okVal s₅.mem W := by rw [m₆]; exact Mem.readW_writeW_self32 _ _ _
  rw [okVal_eq] at hok
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₆ K₆.slots.data K₆.slots.len h.n32 (h.data.buf.of_eq K₆.rd K₆.wr)
    (by rw [K₆.wr]; exact h.data.wr) hok) fun s₇ ⟨E₇, rd₇, wr₇, m₇⟩ => ?_)
  obtain f₇ : Frame [⟨w64 D, n⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  obtain K₇ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₇ := K₆.step L hext2 E₇ rd₇ wr₇ f₇ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, by simp, fun _ h => h⟩
  -- The result, and the exit.
  rw [WP.block_append_iff]
  obtain ⟨s₈, run₈, ax₈, g₈, m₈, rd₈, wr₈⟩ := retEax_ok L E₇
  refine WP.of_runBlock ⟨s₈, run₈, ?_⟩
  obtain K₈ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₈ :=
    K₇.step L hext2 (E₇.keep (g₈ _ (by decide)) (g₈ _ (by decide)) rd₈ wr₈) rd₈ wr₈ (rs := [])
      (by rw [m₈]; exact Frame.refl _ _) (fun r hr => by simp at hr)
  obtain hret : s₈.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32 := by
    rw [h.sp]
    exact K₈.big.readW (r := ⟨w64 SP, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.ret.sub_right (Lay.wSub (by decide))
      · exact ret_below L.sp
      · exact h.ret.sub_right (Region.sub_prefix (by decide))
      · exact h.retD) (by decide)
  refine WP.mono (exit_ok K₈.env.ebp (by rw [K₈.env.esp, h.sp]) (covers_left (fun a m ⟨r, hr, hc⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact K₈.env.perm.w a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_arith⟩))
    (by have := L.fw; omega_arith) K₈.saved hret) fun s₉ ⟨ab, m₉, ax₉, _, _⟩ => ⟨ab, ?_⟩
  -- The values.
  obtain iv₅ : bytesAt s₅.mem (w64 W) 16 = bytesAt s.mem (w64 T) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame F.frame (w16_dis L dDW (finR_wR (.inr rfl))) (by decide),
      Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := strO) (k := 8) (.inl (by decide)) (by decide)
          (by decide)) (by decide),
      Proof.AesGcm.X86.bytesAt_frame f₃ (w16_dis L dDW (ctrR_wR (by simp))) (by decide),
      Proof.AesGcm.X86.bytesAt_frame f₂ (w16_dis L dDW counter_wR) (by decide), ivT]
  obtain dc : ∀ r ∈ [(⟨w64 W, 16⟩ : Region), ⟨w64 D, n⟩], (⟨w64 C, 512⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.c_w.sub_right (Region.sub_prefix (by decide))
    · exact h.data.c
  obtain mac₄ : Spec.Siv.ctxMac s₄.mem (w64 C) R = Spec.Siv.ctxMac s.mem (w64 C) R := K₄.mac L hR dc
  obtain ciph₂ : Spec.Siv.ctxCiph s₂.mem (w64 C) R = Spec.Siv.ctxCiph s.mem (w64 C) R :=
    ctxCiph_frame K₂.big (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.c_w.sub_right (Lay.wSub (by decide))
      · exact L.stk_c.symm
      · exact L.c_w.sub_right (Region.sub_prefix (by decide))) hRb
  obtain p₂ : bytesAt s₂.mem (w64 D) n = bytesAt s.mem (w64 D) n :=
    K₂.bytes h.data.buf.w h.data.buf.stk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dDW.symm) (by have := h.data.buf.lt; omega_arith)
  -- `D`, from `encS2v` to `finish`.
  obtain dD : ∀ {rs : List Region}, (∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 dOff, 16⟩ : Region).Disjoint r) →
      ∀ {m m' : Mem}, Frame rs m m' →
      bytesAt m' (w64 W + BitVec.ofNat 64 dOff) 16 = bytesAt m (w64 W + BitVec.ofNat 64 dOff) 16 :=
    fun hd _ _ hf => Proof.AesGcm.X86.bytesAt_frame hf hd (by decide)
  obtain acc₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 dOff) 16 =
      Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.components 32 s.mem (w64 A) N) := by
    rw [dD (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) f₄,
      dD (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm
        · exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm) f₃,
      dD (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) f₂,
      dD (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        fIn, O.acc]
  obtain pt₄ : bytesAt s₄.mem (w64 D) n = bytesAt s₃.mem (w64 D) n :=
    Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.data.buf.w.sub_right (Lay.wSub (by decide)))
      (by have := h.data.buf.lt; omega_arith)
  have o₅ := F.out
  rw [mac₄, acc₄, pt₄] at o₅
  have pt₃ := d₃
  rw [ciph₂, p₂, ivT] at pt₃
  -- The plaintext through the comparison.
  obtain pt₆ : bytesAt s₆.mem (w64 D) n = bytesAt s₃.mem (w64 D) n := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.data.buf.w.sub_right (Lay.wSub (by decide)))
        (by have := h.data.buf.lt; omega_arith)]
    exact Proof.AesGcm.X86.bytesAt_frame F.frame (fun r hr => (finR_buf h.data.buf (.inr rfl) r hr))
      (by have := h.data.buf.lt; omega_arith) |>.trans pt₄
  obtain hlm := length_mask s₆.mem (w64 D) (decide (bytesAt s₅.mem (w64 W) 16 =
    bytesAt s₅.mem (w64 W + BitVec.ofNat 64 tOff) 16)) n
  obtain out₇ : bytesAt s₇.mem (w64 D) n = if decide (bytesAt s₅.mem (w64 W) 16 =
      bytesAt s₅.mem (w64 W + BitVec.ofNat 64 tOff) 16) then bytesAt s₆.mem (w64 D) n else Spec.Siv.zeros n := by
    rw [m₇]
    have := Proof.AesGcm.X86.bytesAt_writeBytes_self s₆.mem (w64 D) _ (by rw [hlm]; have := h.data.buf.lt; omega_arith)
    rw [hlm] at this
    exact this
  obtain ok₇ : slotv s₇.mem W okO = slotv s₆.mem W okO :=
    f₇.readW (r := ⟨w64 W + BitVec.ofNat 64 okO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm) (by decide)
  obtain eax₉ : s₉.gpr .eax = if decide (bytesAt s₅.mem (w64 W) 16 =
      bytesAt s₅.mem (w64 W + BitVec.ofNat 64 tOff) 16) then 1 else 0 := by
    rw [ax₉, ax₈, ok₇, hok]
  rw [Spec.Siv.decryptWith_eq, Spec.Siv.openWith, ← pt₃]
  rw [m₉, m₈, out₇, eax₉, iv₅, o₅, pt₆]
  by_cases hc : Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (w64 C) R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.components 32 s.mem (w64 A) N))
      (bytesAt s₃.mem (w64 D) n) = bytesAt s.mem (w64 T) 16
  · simp only [hc, ↓reduceIte, decide_true]
    exact ⟨trivial, trivial⟩
  · have hc' : ¬ bytesAt s.mem (w64 T) 16 = Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (w64 C) R)
        (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.components 32 s.mem (w64 A) N))
        (bytesAt s₃.mem (w64 D) n) := fun e => hc e.symm
    simp only [hc, hc', ↓reduceIte, decide_false]
    exact ⟨rfl, rfl⟩

end VG.Proof.AesSiv.X86
