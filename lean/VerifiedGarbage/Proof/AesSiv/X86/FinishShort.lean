import VerifiedGarbage.Proof.AesSiv.X86.S2v
import VerifiedGarbage.Proof.AesSiv.Long

/-!
# AES-SIV on x86: finishing S2V with a short string

Untrusted: everything here is checked by Lean. For a last string `P` of
`L < 16` bytes, the tail at `W + 32` becomes `pad(P) ⊕ dbl(D)`
(`shortTail_ok`): it is zeroed, `P` copied onto it (`copyN_ok`) and `0x80`
appended; `D` is copied to `W + 160` and doubled there (`dblAt_wp`), and
XORed into the tail. Its CMAC, one complete block, from a zero state
(`shortMac_ok`), is S2V's result (`Siv.s2vFinish_short`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold length_bytesAt readW_writeW_off
  covers_left LoopPre CopyPost copyLoop_ok CT)

/-- A block copied, a word at a time, has the bytes of the original. -/
theorem copy4_bytes (m' m : Mem) (c p : Addr) :
    bytesAt (Cmac.store4 m' c (m.readW p 32) (m.readW (p + BitVec.ofNat 64 4) 32) (m.readW (p + BitVec.ofNat 64 8) 32)
      (m.readW (p + BitVec.ofNat 64 12) 32)) c 16 = bytesAt m p 16 := by
  rw [Cmac.bytesAt_store4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.bytesAt_split4]

/-! ## The tail zeroed, and the string copied onto it -/

theorem shortA_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {P : BitVec 32} {k : Nat}
    (hp : slotv s.mem W strO = P) (hk : slotv s.mem W slenO = BitVec.ofNat 32 k) :
    ∃ s', runBlock isa (zero4 tailOff ++ zero4 (tailOff + 16) ++
        ([.mov .edi (slot strO), .mov .edx (.reg .ebp), .alu .add .edx (imm tailOff), .mov .ecx (slot slenO)] :
          List Instr)) s = some s' ∧
      s'.mem = Cmac.zero4 (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 32)) (w64 W + BitVec.ofNat 64 48) ∧
      s'.gpr .edi = P ∧ s'.gpr .edx = W + BitVec.ofNat 32 32 ∧ s'.gpr .ecx = BitVec.ofNat 32 k ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have z₁ := zero4_fold s.mem W tailOff
  have z₂ := zero4_fold (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 tailOff)) W (tailOff + 16)
  simp only [Nat.reduceAdd, tailOff] at z₁ z₂
  refine ⟨_, by crun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hp, hk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [z₁, z₂]
  · cregs [hp]
  · cregs [E.ebp]
  · cregs [hk]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `copyN`: the `k` bytes at `P` copied to `Q` (none if `k = 0`). -/
theorem copyN_ok {s : State} {P Q : BitVec 32} {k : Nat} (hdi : s.gpr .edi = P) (hdx : s.gpr .edx = Q)
    (hcx : s.gpr .ecx = BitVec.ofNat 32 k) (hk : k < 2 ^ 32) (fP : P.toNat + k ≤ 2 ^ 32) (fQ : Q.toNat + k ≤ 2 ^ 32)
    (rP : Covers [⟨w64 P, k⟩] (s.rd ++ s.wr)) (wQ : Covers [⟨w64 Q, k⟩] s.wr)
    (d : (⟨w64 P, k⟩ : Region).Disjoint ⟨w64 Q, k⟩) :
    WP isa copyN s fun s' => s'.mem = writeBytes s.mem (w64 Q) (bytesAt s.mem (w64 P) k) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (WP.of_runBlock ⟨_, by crun [hcx], ?_⟩)
  refine WP.ite (decide (k = 0)) (eval_e (by cmems [hcx]; rw [Proof.AesGcm.X86.and_self_beq32 hk]))
    (fun hz => ?_) (fun hz => ?_)
  · have h0 : k = 0 := of_decide_eq_true hz
    subst h0
    refine WP.block_nil ⟨?_, fun r _ _ _ _ => ?_, ?_, ?_⟩
    · cmems []; simp only [Spec.Aes.bytesAt, List.range_zero, List.map_nil, writeBytes_nil]
    all_goals cmems []
  · have h0 : k ≠ 0 := of_decide_eq_false hz
    refine WP.mono (copyLoop_ok _ ⟨by cregs [hdi], by cregs [hdx], by cregs [hcx], by omega, hk, fP, fQ,
      by cmems []; exact rP, by cmems []; exact wQ, d⟩) fun s' c => ⟨?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_⟩
    · rw [c.mem]; cmems []
    · rw [c.other r h₁ h₂ h₃ h₄]; cregs []
    · rw [c.rd]; cmems []
    · rw [c.wr]; cmems []

/-! ## `0x80` appended, and `D` copied to `W + 160` -/

theorem b80 : (BitVec.ofNat 32 128).setWidth 8 = (0x80 : Byte) := by decide

/-- The memory after appending `0x80` to the `k` bytes at `W + 32` and
copying `D` to `W + 160`. -/
abbrev padMem (m : Mem) (W : BitVec 32) (k : Nat) : Mem :=
  let p := w64 W + BitVec.ofNat 64 dOff
  Cmac.store4 (m.writeW (w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 k) (0x80 : Byte))
    (w64 W + BitVec.ofNat 64 dbOff) (m.readW p 32) (m.readW (p + BitVec.ofNat 64 4) 32)
    (m.readW (p + BitVec.ofNat 64 8) 32) (m.readW (p + BitVec.ofNat 64 12) 32)

theorem shortB_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {k : Nat}
    (hk : slotv s.mem W slenO = BitVec.ofNat 32 k) (hk16 : k < 16) :
    ∃ s', runBlock isa [.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .mov .eax (imm 0x80),
        .store8 (at_ .edx tailOff) .al,
        .mov .eax (slot dOff), .store (at_ .ebp dbOff) .eax, .mov .eax (slot (dOff + 4)),
        .store (at_ .ebp (dbOff + 4)) .eax, .mov .eax (slot (dOff + 8)), .store (at_ .ebp (dbOff + 8)) .eax,
        .mov .eax (slot (dOff + 12)), .store (at_ .ebp (dbOff + 12)) .eax] s = some s' ∧
      s'.mem = padMem s.mem W k ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have pB : (W + BitVec.ofNat 32 k + BitVec.ofNat 32 tailOff).setWidth 64 =
      w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 k := by
    rw [add32_assoc, add_ofNat_assoc, Nat.add_comm]; exact L.aW (by simp only [tailOff]; omega)
  have wB : InRegions s.wr (w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 k) 1 := by
    rw [add_ofNat_assoc]; exact E.perm.wW (by omega)
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hk, pB, wB, b80], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hk, pB, b80, padMem, Cmac.store4, add_ofNat_assoc]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-! ## The tail -/

theorem xorTail_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) :
    ∃ s', runBlock isa (([.mov .edx (.reg .ebp)] : List Instr) ++ xorInto dbOff tailOff) s = some s' ∧
      s'.mem = Cmac.xor4Mem s.mem (w64 W + BitVec.ofNat 64 tailOff) (w64 W + BitVec.ofNat 64 dbOff)
        (w64 W + BitVec.ofNat 64 tailOff) ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [xorInto, E.ebp, L.aW, E.perm.wW, E.perm.wR], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [Cmac.xor4Mem, add_ofNat_assoc]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `shortTail`: the tail at `W + 32` is `dbl(D) ⊕ pad(P)`. -/
theorem shortTail_ok {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat} {s : State}
    (h : CmacPre C W SP R P k s) (hk16 : k < 16) :
    WP isa shortTail s fun s' => Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 144, 32⟩] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 32) 16 =
        Spec.Siv.xor (Spec.Siv.dbl (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16))
          (Spec.Siv.pad (bytesAt s.mem (w64 P) k)) := by
  have E := h.env
  have B := h.buf
  obtain ⟨s₁, run₁, m₁, di₁, dx₁, cx₁, bp₁, sp₁, rd₁, wr₁⟩ := shortA_ok L E h.str h.slen
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env C W SP s₁ := ⟨bp₁, sp₁, E.perm.of_eq rd₁ wr₁⟩
  have hw := L.fw
  refine WP.seq (WP.mono (copyN_ok di₁ dx₁ cx₁ h.k32 B.wrap (by rw [L.nW (by decide)]; omega)
    (by rw [rd₁, wr₁]; exact B.rd) (by rw [L.aW (by decide)]; exact E₁.perm.wC (by omega))
    (by rw [L.aW (by decide)]; exact B.w.sub_right (Lay.wSub (by omega)))) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  have E₂ : Env C W SP s₂ := ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), bp₁],
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), sp₁], E₁.perm.of_eq rd₂ wr₂⟩
  -- The length's slot, still.
  have f₁ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s.mem s₁.mem := by
    rw [m₁]
    exact ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩).trans
      ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩)
  have hlen : (bytesAt s₁.mem (w64 P) k).length = k := length_bytesAt _ _ _
  have f₂ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₁.mem s₂.mem := by
    rw [m₂, L.aW (by decide)]
    exact writeBytes_frame _ _ _ (by
      rw [hlen]; exact Offset.contains (w64 W) (d := 32) (n := k) (e := 32) (k := 32) (by omega) (by omega)
        (by omega))
  have f₁₂ := f₁.trans f₂
  have k₂ : slotv s₂.mem W slenO = BitVec.ofNat 32 k :=
    (f₁₂.readW (w := 32) (r := ⟨w64 W + BitVec.ofNat 64 slenO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)).trans h.slen
  -- `0x80`, `D` copied and doubled, and the XOR.
  obtain ⟨s₃, run₃, m₃, bp₃, sp₃, rd₃, wr₃⟩ := shortB_ok L E₂ k₂ hk16
  have E₃ : Env C W SP s₃ := ⟨bp₃, sp₃, E₂.perm.of_eq rd₃ wr₃⟩
  have e : (([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .mov .eax (imm 0x80),
        .store8 (at_ .edx tailOff) .al,
        .mov .eax (slot dOff), .store (at_ .ebp dbOff) .eax, .mov .eax (slot (dOff + 4)),
        .store (at_ .ebp (dbOff + 4)) .eax, .mov .eax (slot (dOff + 8)), .store (at_ .ebp (dbOff + 8)) .eax,
        .mov .eax (slot (dOff + 12)), .store (at_ .ebp (dbOff + 12)) .eax] : List Instr) ++ dblAt dbOff ++
        ([.mov .edx (.reg .ebp)] : List Instr) ++ xorInto dbOff tailOff) =
      [.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .mov .eax (imm 0x80),
        .store8 (at_ .edx tailOff) .al,
        .mov .eax (slot dOff), .store (at_ .ebp dbOff) .eax, .mov .eax (slot (dOff + 4)),
        .store (at_ .ebp (dbOff + 4)) .eax, .mov .eax (slot (dOff + 8)), .store (at_ .ebp (dbOff + 8)) .eax,
        .mov .eax (slot (dOff + 12)), .store (at_ .ebp (dbOff + 12)) .eax] ++
      (dblAt dbOff ++ (([.mov .edx (.reg .ebp)] : List Instr) ++ xorInto dbOff tailOff)) := by
    simp only [List.append_assoc]
  rw [e, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine dblAt_wp L E₃ (o := dbOff) (by decide) fun s₄ bp₄ sp₄ m₄ rd₄ wr₄ => ?_
  have E₄ : Env C W SP s₄ := ⟨bp₄, sp₄, E₃.perm.of_eq rd₄ wr₄⟩
  obtain ⟨s₅, run₅, m₅, bp₅, sp₅, rd₅, wr₅⟩ := xorTail_ok L E₄
  refine WP.of_runBlock ⟨s₅, run₅, ⟨bp₅, sp₅, E₄.perm.of_eq rd₅ wr₅⟩, by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁], ?_, ?_⟩
  · -- What it writes.
    have f₃ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 144, 32⟩] s₂.mem s₃.mem := by
      rw [m₃, padMem]
      exact ((Frame.refl _ _).writeW (List.mem_cons_self) _ (by
        rw [add_ofNat_assoc]; exact Offset.contains (w64 W) (d := 32 + k) (n := 1) (e := 32) (k := 32) (by omega)
          (by omega) (by omega))).trans ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 W + BitVec.ofNat 64 144, 32⟩, by simp, Offset.sub (d := dbOff) (n := 16) (e := 144) (k := 32) _
          (by decide) (by decide)⟩)
    have f₄ : Frame [⟨w64 W + BitVec.ofNat 64 144, 32⟩] s₃.mem s₄.mem := by
      rw [m₄]
      exact (Proof.CmacAes.X86.dblMem_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, by rw [BitVec.add_zero]; exact Offset.sub _ (by decide) (by decide)⟩
    have f₅ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₄.mem s₅.mem := by
      rw [m₅]
      exact (Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    exact ((f₁₂.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans f₃).trans
      ((f₄.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₅.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩))
  · -- `dbl(D) ⊕ pad(P)`.
    have d32 : (⟨w64 W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 160, 16⟩ :=
      Lay.w_w (.inl (by decide)) (by decide) (by decide)
    rw [m₅, show tailOff = 32 from rfl, show dbOff = 160 from rfl,
      Cmac.xor4Mem_bytes _ (Cmac.Sep4.of_disjoint d32) (Cmac.Sep4.self _)]
    have t₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 32) 16 = bytesAt s₃.mem (w64 W + BitVec.ofNat 64 32) 16 :=
      Proof.AesGcm.X86.bytesAt_frame (rs := [⟨w64 W + BitVec.ofNat 64 160 + BitVec.ofNat 64 0, 16⟩])
        (by rw [m₄]; exact Proof.CmacAes.X86.dblMem_frame _ _ _ _)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [BitVec.add_zero]; exact d32) (by decide)
    have q₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 160) 16 =
        Spec.Cmac.dbl 16 (bytesAt s₃.mem (w64 W + BitVec.ofNat 64 160) 16) := by
      have := Proof.CmacAes.X86.dblMem_bytes s₃.mem (w64 W + BitVec.ofNat 64 160) 0 0
      rw [BitVec.add_zero] at this
      rw [m₄]; exact this
    have q₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 160) 16 = bytesAt s₂.mem (w64 W + BitVec.ofNat 64 2560) 16 := by
      rw [m₃]; exact copy4_bytes _ _ _ _
    have t₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 32) 16 = bytesAt (s₂.mem.writeW
        (w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 k) (0x80 : Byte)) (w64 W + BitVec.ofNat 64 32) 16 := by
      rw [m₃]
      exact Proof.AesGcm.X86.bytesAt_frame (Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact d32) (by decide)
    have hz : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by
      have fz : Frame [⟨w64 W + BitVec.ofNat 64 48, 16⟩] (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 32)) s₁.mem := by
        rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
      rw [Proof.AesGcm.X86.bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide)]
      exact Cmac.zero4_bytes _ _
    have pad := Cmac.padded_bytes s₁.mem (w64 W + BitVec.ofNat 64 32) (bytesAt s₁.mem (w64 P) k)
      (by rw [hlen]; exact hk16) hz
    rw [hlen] at pad
    have hP : bytesAt s₁.mem (w64 P) k = bytesAt s.mem (w64 P) k :=
      Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact B.w.sub_right (Lay.wSub (by decide)))
        (by have := B.lt; omega)
    have hD : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 2560) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 2560) 16 :=
      Proof.AesGcm.X86.bytesAt_frame f₁₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide)
    rw [t₄, q₄, q₃, hD, t₃, m₂, L.aW (o := 32) (by decide), pad, hP, Siv.xor_eq, Spec.Siv.pad,
      show 16 - k - 1 = 15 - k by omega, length_bytesAt]
    rfl

/-! ## What `finish` leaves -/

/-- The parts of `W` `finish` writes: the output, the tail, the CMAC state and
`dbl(D)`, the variables, the working space of the functions called, and the
stack below `SP`. -/
abbrev finR (W SP : BitVec 32) (out : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 out, 16⟩, ⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 144, 32⟩, wS W,
    ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 56]

/-- What `finish out` leaves: S2V's end, from `D` and the string `P`, at
`W + out`. -/
structure FinPost (C W SP : BitVec 32) (R out : Nat) (P : BitVec 32) (k : Nat) (s s' : State) : Prop where
  env : Env C W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (finR W SP out) s.mem s'.mem
  out : bytesAt s'.mem (w64 W + BitVec.ofNat 64 out) 16 =
    Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (w64 C) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16)
      (bytesAt s.mem (w64 P) k)

theorem finR_c {C W SP : BitVec 32} (L : Lay C W SP) {out : Nat} (hout : out = 0 ∨ out = 112) :
    ∀ r ∈ finR W SP out, (⟨w64 C, 512⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.c_w.sub_right (Lay.wSub (by omega))
  · exact L.c_w.sub_right (Lay.wSub (by decide))
  · exact L.c_w.sub_right (Lay.wSub (by decide))
  · exact L.c_w.sub_right (Lay.wSub (by decide))
  · exact L.c_w.sub_right (Lay.wSub (by decide))
  · exact L.stk_c.symm

/-! ## The short case's call -/

theorem macPre_ok {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {s : State} (E : Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) {out : Nat}
    (hout : out = 0 ∨ out = 112) :
    ∃ s', runBlock isa (zero4 out ++ macArgs out ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm tailOff),
        .mov .esi (imm 16)] : List Instr)) s = some s' ∧
      s'.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 out) ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 out ∧
      s'.gpr .ebx = W + BitVec.ofNat 32 32 ∧ s'.gpr .esi = BitVec.ofNat 32 16 ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have z := zero4_fold s.mem W out
  rcases hout with rfl | rfl
  all_goals
    simp only [Nat.reduceAdd] at z
    refine ⟨_, by crun [zero4, macArgs, E.ebp, L.aW, E.perm.wW, E.perm.wR, hc, hr], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · cmems [z]
    · cregs [hc]
    · cregs [hr]
    · cregs [E.ebp]
    · cregs [E.ebp]
    · cregs []
    · cregs [E.ebp]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []

/-- A complete block's CMAC from the context's subkeys. -/
theorem ctxMac_block (m : Mem) (C : Addr) (R : Nat) {T : List Byte} (hT : T.length = 16) :
    Spec.Siv.ctxMac m C R T = Spec.Cmac.aesWith R (bytesAt m C (16 * (R + 1)))
      (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (bytesAt m (C + BitVec.ofNat 64 240) 16)
        (bytesAt m (C + BitVec.ofNat 64 256) 16) T) (Spec.Cmac.zeros 16)) := by
  have := Siv.cmacWith_split (Spec.Siv.schedCiph m C R) (bytesAt m (C + 240) 16) (bytesAt m (C + 256) 16)
    (msg := []) (last := T) (by decide) (by omega) (.inl rfl)
  simp only [List.nil_append] at this
  rw [Spec.Siv.ctxMac, this, Proof.Cmac.xor_comm]
  rfl

/-- The short case: the tail's CMAC, one complete block, into `W + out`. -/
theorem finishShort_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {k : Nat} {s : State} (h : CmacPre C W SP R P k s)
    (hk16 : k < 16) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (.seq shortTail (shortMac v.callee v.suffix out)) s (FinPost C W SP R out P k s) := by
  have hRb : R ≤ 14 := by omega
  refine WP.seq (WP.mono (shortTail_ok L h hk16) fun s₁ ⟨E₁, rd₁, wr₁, f₁, t₁⟩ => ?_)
  have k₁ : ∀ o, 176 ≤ o → o + 4 ≤ 200 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)) (by decide)
  obtain ⟨s₂, run₂, m₂, ax₂, cx₂, dx₂, bx₂, si₂, di₂, bp₂, sp₂, rd₂, wr₂⟩ := macPre_ok L E₁
    (by rw [k₁ _ (by decide) (by decide)]; exact h.ctx) (by rw [k₁ _ (by decide) (by decide)]; exact h.rounds) hout
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have E₂ : Env C W SP s₂ := ⟨bp₂, sp₂, E₁.perm.of_eq rd₂ wr₂⟩
  have dO : (⟨w64 W + BitVec.ofNat 64 out, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 32, 16⟩ := by
    rcases hout with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)
  refine WP.mono (finCall_ok v L E₂ hR (y := out) (.inl (by omega)) (P := W + BitVec.ofNat 32 32) (l := 16)
    (Nat.le_refl _) (srcW L E₂.perm (t := 32) (k := 16) (by decide))
    (by rw [L.aW (o := 32) (by decide)]; exact dO.symm) ax₂ cx₂ dx₂ bx₂ si₂ di₂)
    fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, o₃⟩ => ⟨E₃, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], ?_, ?_⟩
  · have fz : Frame [⟨w64 W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by
      rw [m₂]; exact Cmac.frame_store4 _ _ _ _ _
    refine ((f₁.sub fun r hr => ?_).trans (fz.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · have fz : Frame [⟨w64 W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by
      rw [m₂]; exact Cmac.frame_store4 _ _ _ _ _
    have hz : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
      rw [m₂]; exact Cmac.zero4_bytes _ _
    have hT : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 32) 16 = bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) 16 :=
      Proof.AesGcm.X86.bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dO.symm) (by decide)
    have hc : Spec.Siv.ctxMac s₂.mem (w64 C) R = Spec.Siv.ctxMac s.mem (w64 C) R :=
      (ctxMac_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.c_w.sub_right (Lay.wSub (by omega))) hRb).trans
      (ctxMac_frame f₁ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.c_w.sub_right (Lay.wSub (by decide))) hRb)
    rw [o₃, L.aW (o := 32) (by decide), hz, hT, Siv.s2vFinish_short _ _ (by rw [length_bytesAt]; exact hk16), ← t₁,
      ← hc, ctxMac_block _ _ _ (length_bytesAt _ _ _)]

end VG.Proof.AesSiv.X86
