import VerifiedGarbage.Proof.AesSiv.X86.Callee
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.AesSiv.Ctr32

/-!
# AES-SIV on x86: CTR (`ctr`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesSiv/Arm/Ctr.lean`): `counter 0` sets the counter block at
`W + 96` to `Q`, the IV at `W` with bit 7 of its bytes 8 and 12 cleared
(`counter_bytes`, `Proof.AesSiv.counter_words4`). `ctrWhole` encrypts the
whole blocks of the data by one call of `vg_aes_ctr32` from `Q`, whose
counters do not wrap around (`Proof.AesSiv.counter_low`,
`Proof.AesSiv.repeat_inc32`), and which leaves `Q + nb` in the counter block
(`ctrWhole_ok`); `ctrTail` XORs the last bytes with the first bytes of the
keystream block of that counter, which `vg_aes_ctr32` computes on a zero
block at `W + 80` (`ctrTail_ok`). Together, CTR's output on the data
(`ctr_ok`).
-/

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

/-- The first `k` bytes of the data as `vg_aes_ctr32`'s. -/
theorem Dat.dst {C W SP : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : Dat C W SP s D n) {k : Nat}
    (hk : k ≤ n) {c : Nat} (hc : c + 16 ≤ 256) : Dst C W SP s D k c where
  wr := fun a m ⟨r, hr, hc'⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.wr a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
  wrap := by have := h.buf.wrap; omega
  dk := h.c.sub_right (Region.sub_prefix hk)
  dc := (h.buf.w.sub_left (Region.sub_prefix hk)).sub_right (Lay.wSub (by omega))
  ds := (h.buf.w.sub_left (Region.sub_prefix hk)).sub_right (Lay.wSub (by decide))
  stk := h.buf.stk.sub_right (Region.sub_prefix hk)

/-- What CTR writes: the keystream and counter blocks, the working space of
`vg_aes_ctr32`, the stack below `SP` and the data. -/
abbrev ctrR (W SP D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 ksOff, 32⟩, ⟨w64 W + BitVec.ofNat 64 256, 2048⟩, below SP 56, ⟨w64 D, n⟩]

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
  have hsh := shr4 hn
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hl], ?_, ?_, fun r h₁ => ?_, ?_, ?_, ?_⟩
  · cregs [hl, hsh]
  · cmems [hl, hsh]; rw [Proof.AesGcm.X86.and_self_beq32 (by omega)]
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
  have ha := and15 (BitVec.ofNat 32 n)
  rw [toNat_ofNat32 hn] at ha
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hl], ?_, ?_, fun r h₁ => ?_, ?_, ?_, ?_⟩
  · cregs [hl, ha]
  · cmems [hl, ha]; rw [beq_zero32 (by omega)]
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
  have z := zero4_fold s.mem W ksOff
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
  have ha := and15 (BitVec.ofNat 32 n)
  rw [toNat_ofNat32 hn] at ha
  have hsub : D + BitVec.ofNat 32 n - BitVec.ofNat 32 (n % 16) = D + BitVec.ofNat 32 (16 * (n / 16)) := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, ofNat_sub32 (Nat.mod_le _ _) hn]
    congr 2; omega
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hl, hd], ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_⟩
  · cregs [hl, ha]
  · cregs [E.ebp]
  · cregs [hl, ha, hd, hsub]
  · cregs []
  all_goals cmems []

/-! ## `ctrWhole` -/

theorem rounds_le {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : 16 * (R + 1) ≤ 240 := by omega

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
  have hql : q.length = 16 := by rw [← hq, length_bytesAt]
  have hinc := repeat_inc32 hql (k := n / 16 + 1) (by omega)
  have hcb : blockAt s.mem (w64 W + BitVec.ofNat 64 cbOff) = Spec.Gcm.ofBytes q := by
    rw [blockAt, hq]
  obtain ⟨s₁, run₁, di₁, zf₁, g₁, m₁, rd₁, wr₁⟩ := whole1_ok L E hl hn
  have E₁ : Env C W SP s₁ := ⟨by rw [g₁ _ (by decide), E.ebp], by rw [g₁ _ (by decide), E.esp], E.perm.of_eq rd₁ wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n / 16 = 0
  · refine WP.ite true (eval_e (by rw [zf₁]; simp [h0])) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨E₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_, ?_⟩
    · rw [m₁, h0, Nat.mul_zero, ctrPart_zero]
    · rw [m₁, hcb, h0, Nat.add_zero]
      have := hinc 0 (by omega)
      rw [Nat.add_zero] at this
      exact this
  · refine WP.ite false (eval_e (by rw [zf₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
    obtain ⟨s₂, run₂, ax₂, cx₂, dx₂, bx₂, g₂, m₂, rd₂, wr₂⟩ := ctrArgs_ok (C := C) (R := R) (D := D) L E₁ (by rw [m₁]; exact hc)
      (by rw [m₁]; exact hr) (by rw [m₁]; exact hd)
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : Env C W SP s₂ := ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), E₁.ebp],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), E₁.esp], E₁.perm.of_eq rd₂ wr₂⟩
    have hD₂ := hD.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
    have mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
    refine WP.mono (ctrCall_ok v L E₂ hR (c := cbOff) (by decide) (hD₂.dst hb (by decide)) ax₂ cx₂ dx₂ bx₂
      (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), di₁])) fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, o₃, c₃⟩ => ?_
    have hRb := rounds_le hR
    have fT : Frame (ctrR W SP D n) s.mem s₃.mem := by
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
      have hc₃ := ctr32_ctrPart (m := s₂.mem) (m' := s₃.mem) (K := w64 C + BitVec.ofNat 64 272)
        (C := w64 W + BitVec.ofNat 64 cbOff) (D := w64 D) (R := R) (q := q) (k := n / 16)
        (fun i hi => by rw [mem₂, hcb]; exact hinc i (by omega)) o₃
      have e := Proof.Cmac.Stream.bytesAt_append s₃.mem (w64 D) (16 * (n / 16)) (n - 16 * (n / 16))
      rw [show 16 * (n / 16) + (n - 16 * (n / 16)) = n by omega] at e
      have e₀ := Proof.Cmac.Stream.bytesAt_append s.mem (w64 D) (16 * (n / 16)) (n - 16 * (n / 16))
      rw [show 16 * (n / 16) + (n - 16 * (n / 16)) = n by omega] at e₀
      have rest : bytesAt s₃.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
          bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
        rw [← mem₂]
        refine Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => ?_) (by have := hD.buf.lt; omega)
        have hsub : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ ⟨w64 D, n⟩ :=
          Offset.sub_base _ (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by decide))
        · exact (Offset.base_disjoint (w64 D) (e := 16 * (n / 16)) (n := n - 16 * (n / 16))
            (k := 16 * (n / 16)) (by omega) (by have := hD.buf.lt; omega)).symm
        · exact (hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by decide))
        · exact (hD.buf.stk.sub_right hsub).symm
      have hpa := ctrPart_append (Spec.Siv.ctxCiph s.mem (w64 C) R) q (bytesAt s.mem (w64 D) (16 * (n / 16)))
        (bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)))
      rw [length_bytesAt] at hpa
      rw [e, hc₃, rest, e₀, hpa, mem₂]
      rfl
    · rw [c₃, mem₂, hcb]
      exact hinc (n / 16) (by omega)

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
  have E₁ : Env C W SP s₁ := ⟨by rw [g₁ _ (by decide), E.ebp], by rw [g₁ _ (by decide), E.esp], E.perm.of_eq rd₁ wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n % 16 = 0
  · refine WP.ite true (eval_e (by rw [zf₁]; simp [h0])) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨E₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_⟩
    rw [m₁, hdat, show 16 * (n / 16) = n by omega]
  · refine WP.ite false (eval_e (by rw [zf₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    obtain ⟨s₂, run₂, m₂, ax₂, cx₂, dx₂, bx₂, di₂, bp₂, sp₂, rd₂, wr₂⟩ := tailArgs_ok' (R := R) L E₁
      (by rw [m₁]; exact hc) (by rw [m₁]; exact hr)
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : Env C W SP s₂ := ⟨bp₂, sp₂, E₁.perm.of_eq rd₂ wr₂⟩
    refine WP.seq (WP.mono (ctrCall_ok v L E₂ hR (c := cbOff) (by decide) (n := 1)
      (dstW L E₂.perm (c := cbOff) (q := ksOff) (by decide) (by decide) (by decide)) ax₂ cx₂ dx₂ bx₂ di₂)
      fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, o₃, _⟩ => ?_)
    have hRb := rounds_le hR
    have hb : 16 * (n / 16) < n := by omega
    have eK : w64 (W + BitVec.ofNat 32 ksOff) = w64 W + BitVec.ofNat 64 ksOff := L.aW (by decide)
    -- The keystream block.
    have f₂ : Frame [⟨w64 W + BitVec.ofNat 64 ksOff, 16⟩] s.mem s₂.mem := by
      rw [m₂, m₁]; exact Cmac.frame_store4 _ _ _ _ _
    have cb₂ : blockAt s₂.mem (w64 W + BitVec.ofNat 64 cbOff) =
        Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)) := by
      rw [blockAt, Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), ← blockAt, hcb]
    have sch₂ : bytesAt s₂.mem (w64 C + BitVec.ofNat 64 272) (16 * (R + 1)) =
        bytesAt s.mem (w64 C + BitVec.ofNat 64 272) (16 * (R + 1)) :=
      Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.c_w' (by omega) (by decide)) (by omega)
    have hks : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 ksOff) 16 =
        Proof.Siv.ksBlock (Spec.Siv.ctxCiph s.mem (w64 C) R) q (n / 16) := by
      rw [eK] at o₃
      have hx₃ := Proof.AesCcm.ctr32_bytes (m := s₂.mem) (m' := s₃.mem) (C := w64 W + BitVec.ofNat 64 cbOff)
        (D := w64 W + BitVec.ofNat 64 ksOff) (nb := 1) o₃
      rw [Nat.mul_one, m₂, Cmac.zero4_bytes, ← m₂, cb₂, xorKs_zeros, sch₂,
        Proof.Cmac.aesWith_bytes _ _ (length_be128 _)] at hx₃
      rw [hx₃]; rfl
    -- The arguments of the XOR.
    have f₂₃ : Frame [⟨w64 W + BitVec.ofNat 64 ksOff, 32⟩, ⟨w64 W + BitVec.ofNat 64 256, 2048⟩, below SP 56]
        s₂.mem s₃.mem := by
      rw [eK] at f₃
      exact f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
    have f₀₃ : Frame [⟨w64 W + BitVec.ofNat 64 ksOff, 32⟩, ⟨w64 W + BitVec.ofNat 64 256, 2048⟩, below SP 56]
        s.mem s₃.mem :=
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩).trans f₂₃
    have sl₃ : ∀ o, 176 ≤ o → o + 4 ≤ 256 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
      f₀₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Lay.w_w (.inr (by simp only [ksOff]; omega)) (by omega) (by decide)
        · exact Lay.w_w (.inl h₂) (by omega) (by decide)
        · exact (L.stk_w' (by omega)).symm) (by decide)
    obtain ⟨s₄, run₄, cx₄, dx₄, di₄, g₄, m₄, rd₄, wr₄⟩ := xorArgs_ok (D := D) L E₃
      (by rw [sl₃ _ (by decide) (by decide)]; exact hd) (by rw [sl₃ _ (by decide) (by decide)]; exact hl) hn
    refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
    have rd₀₄ : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
    have wr₀₄ : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
    have hwD : D.toNat + n ≤ 2 ^ 32 := hD.buf.wrap
    have eD : w64 (D + BitVec.ofNat 32 (16 * (n / 16))) = w64 D + BitVec.ofNat 64 (16 * (n / 16)) :=
      Buf.ptr (by omega)
    have hsub : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ ⟨w64 D, n⟩ :=
      Offset.sub_base _ (by omega)
    have xp : XorPre s₄ (W + BitVec.ofNat 32 ksOff) (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) := by
      refine ⟨dx₄, di₄, cx₄, by omega, by omega, by rw [L.nW (by decide)]; have := L.fw; simp only [ksOff]; omega,
        by rw [Proof.AesGcm.X86.toNat_add32 (by omega)]; omega, ?_, ?_, ?_⟩
      · rw [eK, rd₀₄, wr₀₄]; exact Proof.AesGcm.X86.covers_left (E.perm.wC (by simp only [ksOff]; omega))
      · rw [wr₀₄, eD]; exact covers_off hD.wr (by omega) (by have := hD.buf.lt; omega)
      · rw [eK, eD]; exact ((hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by simp only [ksOff]; omega))).symm
    refine WP.mono (xorLoop_ok s₄ xp) fun s₅ x₅ => ?_
    have hm₅ := x₅.mem
    rw [eK, eD] at hm₅
    have hxl := length_xorBytes s₄.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16)))
      (w64 W + BitVec.ofNat 64 ksOff) (n % 16)
    have fw : Frame [⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] s₄.mem s₅.mem := by
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
      have d₄ : bytesAt s₄.mem (w64 D) x.length = ctrPart (Spec.Siv.ctxCiph s.mem (w64 C) R) q x
          (16 * (n / 16)) := by
        rw [hx, m₄, Proof.AesGcm.X86.bytesAt_frame f₀₃ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact hD.buf.w.sub_right (Lay.wSub (by decide))
          · exact hD.buf.w.sub_right (Lay.wSub (by decide))
          · exact hD.buf.stk.symm) (by have := hD.buf.lt; omega), hdat]
      have st := ctrPart_step (Spec.Siv.ctxCiph s.mem (w64 C) R) hcl q x s₄.mem (w64 D)
        (i := n / 16) (n := n % 16) (by have := hD.buf.lt; omega) (by omega) (by omega) d₄
      have xb : xorBytes s₄.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (w64 W + BitVec.ofNat 64 ksOff) (n % 16) =
          Spec.Cmac.xor (bytesAt s₄.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))
            ((Proof.Siv.ksBlock (Spec.Siv.ctxCiph s.mem (w64 C) R) q (n / 16)).take (n % 16)) := by
        have tk := take_bytesAt s₄.mem (w64 W + BitVec.ofNat 64 ksOff) (a := n % 16) (b := 16 - n % 16)
        rw [show n % 16 + (16 - n % 16) = 16 by omega] at tk
        rw [xorBytes, ← tk, m₄, hks]
        rfl
      rw [hx] at st
      rw [hm₅, xb, st, show 16 * (n / 16) + n % 16 = n by omega]

/-! ## `ctr` -/

theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxCiph m' C R = Spec.Siv.ctxCiph m C R := by
  unfold Spec.Siv.ctxCiph Spec.Siv.schedCiph
  rw [Proof.AesGcm.X86.bytesAt_frame hf (p := C + 272)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 272) (n := 16 * (R + 1)) (by omega))) (by omega)]

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
    · exact Lay.w_w (.inr (by simp only [ksOff]; omega)) (by omega) (by decide)
    · exact Lay.w_w (.inl h₂) (by omega) (by decide)
    · exact (L.stk_w' (by omega)).symm
    · exact (hD.buf.w.sub_right (Lay.wSub (d := o) (n := 4) (by omega))).symm) (by decide)

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
  refine WP.seq (WP.mono (ctrWhole_ok v L hR E hD hn hc hr hd hl hq (by omega))
    fun s₄ ⟨E₄, rd₄, wr₄, f₄, d₄, cb₄⟩ => ?_)
  have hRb := rounds_le hR
  have k₄ : Spec.Siv.ctxCiph s₄.mem (w64 C) R = Spec.Siv.ctxCiph s.mem (w64 C) R :=
    ctxCiph_frame f₄ (ctrR_c L hD) hRb
  have sl := fun {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 256) => ctrR_slot L hD f₄ h₁ h₂
  refine WP.mono (ctrTail_ok v L hR E₄ (hD.of_eq rd₄ wr₄) hn (by rw [sl (by decide) (by decide)]; exact hc)
    (by rw [sl (by decide) (by decide)]; exact hr) (by rw [sl (by decide) (by decide)]; exact hd)
    (by rw [sl (by decide) (by decide)]; exact hl) (x := bytesAt s.mem (w64 D) n) (length_bytesAt _ _ _) cb₄
    (by rw [k₄]; exact d₄)) fun s₅ ⟨E₅, rd₅, wr₅, f₅, d₅⟩ => ⟨E₅, by rw [rd₅, rd₄], by rw [wr₅, wr₄], f₄.trans f₅, ?_⟩
  rw [d₅, k₄]
  exact ctrPart_all _ (fun y => Proof.Cmac.aesWith_length _ _ y) q _ (by rw [length_bytesAt])

end VG.Proof.AesSiv.X86
