module

public import VerifiedGarbage.Proof.AesSiv.Long
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.AesSiv.X86.S2v
import VerifiedGarbage.Proof.AesSiv.X86.Callee
import VerifiedGarbage.Proof.AesSiv.X86.Run
import VerifiedGarbage.Proof.AesSiv.CtrPart
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Cmac.Block

/-! ### `AesSiv.X86.FinishShort`, which this module and modules that import it used -/

section

/-!
# AES-SIV on x86: finishing S2V with a short string

Untrusted: everything here is checked by Lean. For a last string `P` of
`L < 16` bytes, the tail at `W + 32` becomes `pad(P) ⊕ dbl(D)`
(`shortTail_ok`): it is zeroed, `P` copied onto it (`copyN_ok`) and `0x80`
appended; `D` is copied to `W + 160` and doubled there (`dblAt_wp`), and
XORed into the tail. Its CMAC, one complete block, from a zero state
(`shortMac_ok`), is S2V's result (`Siv.s2vFinish_short`).
-/

@[expose] public section

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
  obtain z₁ := zero4_fold s.mem W tailOff
  obtain z₂ := zero4_fold (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 tailOff)) W (tailOff + 16)
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
    refine WP.mono (copyLoop_ok _ ⟨by cregs [hdi], by cregs [hdx], by cregs [hcx], by omega_arith, hk, fP, fQ,
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
  obtain pB : (W + BitVec.ofNat 32 k + BitVec.ofNat 32 tailOff).setWidth 64 =
      w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 k := by
    rw [add32_assoc, add_ofNat_assoc, Nat.add_comm]; exact L.aW (by simp only [tailOff]; omega_arith)
  obtain wB : InRegions s.wr (w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 k) 1 := by
    rw [add_ofNat_assoc]; exact E.perm.wW (by omega_arith)
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
  obtain E₁ : Env C W SP s₁ := ⟨bp₁, sp₁, E.perm.of_eq rd₁ wr₁⟩
  have hw := L.fw
  refine WP.seq (WP.mono (copyN_ok di₁ dx₁ cx₁ h.k32 B.wrap (by rw [L.nW (by decide)]; omega_arith)
    (by rw [rd₁, wr₁]; exact B.rd) (by rw [L.aW (by decide)]; exact E₁.perm.wC (by omega_arith))
    (by rw [L.aW (by decide)]; exact B.w.sub_right (Lay.wSub (by omega_arith)))) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  obtain E₂ : Env C W SP s₂ := ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), bp₁],
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), sp₁], E₁.perm.of_eq rd₂ wr₂⟩
  -- The length's slot, still.
  obtain f₁ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s.mem s₁.mem := by
    rw [m₁]
    exact ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩).trans
      ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩)
  obtain hlen : (bytesAt s₁.mem (w64 P) k).length = k := length_bytesAt _ _ _
  obtain f₂ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₁.mem s₂.mem := by
    rw [m₂, L.aW (by decide)]
    exact writeBytes_frame _ _ _ (by
      rw [hlen]; exact Offset.contains (w64 W) (d := 32) (n := k) (e := 32) (k := 32) (by omega_arith) (by omega_arith)
        (by omega_arith))
  obtain f₁₂ := f₁.trans f₂
  obtain k₂ : slotv s₂.mem W slenO = BitVec.ofNat 32 k :=
    (f₁₂.readW (w := 32) (r := ⟨w64 W + BitVec.ofNat 64 slenO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)).trans h.slen
  -- `0x80`, `D` copied and doubled, and the XOR.
  obtain ⟨s₃, run₃, m₃, bp₃, sp₃, rd₃, wr₃⟩ := shortB_ok L E₂ k₂ hk16
  obtain E₃ : Env C W SP s₃ := ⟨bp₃, sp₃, E₂.perm.of_eq rd₃ wr₃⟩
  obtain e : (([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .mov .eax (imm 0x80),
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
  obtain E₄ : Env C W SP s₄ := ⟨bp₄, sp₄, E₃.perm.of_eq rd₄ wr₄⟩
  obtain ⟨s₅, run₅, m₅, bp₅, sp₅, rd₅, wr₅⟩ := xorTail_ok L E₄
  refine WP.of_runBlock ⟨s₅, run₅, ⟨bp₅, sp₅, E₄.perm.of_eq rd₅ wr₅⟩, by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁], ?_, ?_⟩
  · -- What it writes.
    obtain f₃ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 144, 32⟩] s₂.mem s₃.mem := by
      rw [m₃, padMem]
      exact ((Frame.refl _ _).writeW (List.mem_cons_self) _ (by
        rw [add_ofNat_assoc]; exact Offset.contains (w64 W) (d := 32 + k) (n := 1) (e := 32) (k := 32) (by omega_arith)
          (by omega_arith) (by omega_arith))).trans ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 W + BitVec.ofNat 64 144, 32⟩, by simp, Offset.sub (d := dbOff) (n := 16) (e := 144) (k := 32) _
          (by decide) (by decide)⟩)
    obtain f₄ : Frame [⟨w64 W + BitVec.ofNat 64 144, 32⟩] s₃.mem s₄.mem := by
      rw [m₄]
      exact (Proof.CmacAes.X86.dblMem_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, by rw [BitVec.add_zero]; exact Offset.sub _ (by decide) (by decide)⟩
    obtain f₅ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₄.mem s₅.mem := by
      rw [m₅]
      exact (Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    exact ((f₁₂.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans f₃).trans
      ((f₄.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₅.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩))
  · -- `dbl(D) ⊕ pad(P)`.
    obtain d32 : (⟨w64 W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 160, 16⟩ :=
      Lay.w_w (.inl (by decide)) (by decide) (by decide)
    rw [m₅, show tailOff = 32 from rfl, show dbOff = 160 from rfl,
      Cmac.xor4Mem_bytes _ (Cmac.Sep4.of_disjoint d32) (Cmac.Sep4.self _)]
    obtain t₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 32) 16 = bytesAt s₃.mem (w64 W + BitVec.ofNat 64 32) 16 :=
      Proof.AesGcm.X86.bytesAt_frame (rs := [⟨w64 W + BitVec.ofNat 64 160 + BitVec.ofNat 64 0, 16⟩])
        (by rw [m₄]; exact Proof.CmacAes.X86.dblMem_frame _ _ _ _)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [BitVec.add_zero]; exact d32) (by decide)
    obtain q₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 160) 16 =
        Spec.Cmac.dbl 16 (bytesAt s₃.mem (w64 W + BitVec.ofNat 64 160) 16) := by
      have := Proof.CmacAes.X86.dblMem_bytes s₃.mem (w64 W + BitVec.ofNat 64 160) 0 0
      rw [BitVec.add_zero] at this
      rw [m₄]; exact this
    obtain q₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 160) 16 = bytesAt s₂.mem (w64 W + BitVec.ofNat 64 2560) 16 := by
      rw [m₃]; exact copy4_bytes _ _ _ _
    obtain t₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 32) 16 = bytesAt (s₂.mem.writeW
        (w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 k) (0x80 : Byte)) (w64 W + BitVec.ofNat 64 32) 16 := by
      rw [m₃]
      exact Proof.AesGcm.X86.bytesAt_frame (Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact d32) (by decide)
    obtain hz : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by
      obtain fz : Frame [⟨w64 W + BitVec.ofNat 64 48, 16⟩] (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 32)) s₁.mem := by
        rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
      rw [Proof.AesGcm.X86.bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide)]
      exact Cmac.zero4_bytes _ _
    obtain pad := Cmac.padded_bytes s₁.mem (w64 W + BitVec.ofNat 64 32) (bytesAt s₁.mem (w64 P) k)
      (by rw [hlen]; exact hk16) hz
    rw [hlen] at pad
    obtain hP : bytesAt s₁.mem (w64 P) k = bytesAt s.mem (w64 P) k :=
      Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact B.w.sub_right (Lay.wSub (by decide)))
        (by have := B.lt; omega_arith)
    obtain hD : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 2560) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 2560) 16 :=
      Proof.AesGcm.X86.bytesAt_frame f₁₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide)
    rw [t₄, q₄, q₃, hD, t₃, m₂, L.aW (o := 32) (by decide), pad, hP, Siv.xor_eq, Spec.Siv.pad,
      show 16 - k - 1 = 15 - k by omega_arith, length_bytesAt]
    rfl

/-! ## What `finish` leaves -/

/-- The parts of `W` `finish` writes: the output, the tail, the CMAC state and
`dbl(D)`, the variables, the working space of the functions called, and the
stack below `SP`. -/
abbrev finR (W SP : BitVec 32) (out : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 out, 16⟩, ⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 144, 32⟩, wS W,
    ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 60]

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
  · exact L.c_w.sub_right (Lay.wSub (by omega_arith))
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
  obtain z := zero4_fold s.mem W out
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
  have := Siv.macWith_split (Spec.Siv.schedCiph m C R) (bytesAt m (C + 240) 16) (bytesAt m (C + 256) 16)
    (msg := []) (last := T) (by decide) (by omega_arith) (.inl rfl)
  simp only [List.nil_append] at this
  rw [Spec.Siv.ctxMac, this, Proof.Cmac.xor_comm]
  rfl

/-- The short case: the tail's CMAC, one complete block, into `W + out`. -/
theorem finishShort_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {k : Nat} {s : State} (h : CmacPre C W SP R P k s)
    (hk16 : k < 16) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (.seq shortTail (shortMac v.callee v.suffix out)) s (FinPost C W SP R out P k s) := by
  obtain hRb : R ≤ 14 := by omega_arith
  refine WP.seq (WP.mono (shortTail_ok L h hk16) fun s₁ ⟨E₁, rd₁, wr₁, f₁, t₁⟩ => ?_)
  obtain k₁ : ∀ o, 176 ≤ o → o + 4 ≤ 200 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
      · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)) (by decide)
  obtain ⟨s₂, run₂, m₂, ax₂, cx₂, dx₂, bx₂, si₂, di₂, bp₂, sp₂, rd₂, wr₂⟩ := macPre_ok L E₁
    (by rw [k₁ _ (by decide) (by decide)]; exact h.ctx) (by rw [k₁ _ (by decide) (by decide)]; exact h.rounds) hout
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain E₂ : Env C W SP s₂ := ⟨bp₂, sp₂, E₁.perm.of_eq rd₂ wr₂⟩
  obtain dO : (⟨w64 W + BitVec.ofNat 64 out, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 32, 16⟩ := by
    rcases hout with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)
  refine WP.mono (finCall_ok v L E₂ hR (y := out) (.inl (by omega_arith)) (P := W + BitVec.ofNat 32 32) (l := 16)
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
    obtain hz : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
      rw [m₂]; exact Cmac.zero4_bytes _ _
    obtain hT : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 32) 16 = bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) 16 :=
      Proof.AesGcm.X86.bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dO.symm) (by decide)
    obtain hc : Spec.Siv.ctxMac s₂.mem (w64 C) R = Spec.Siv.ctxMac s.mem (w64 C) R :=
      (ctxMac_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.c_w.sub_right (Lay.wSub (by omega_arith))) hRb).trans
      (ctxMac_frame f₁ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.c_w.sub_right (Lay.wSub (by decide))) hRb)
    rw [o₃, L.aW (o := 32) (by decide), hz, hT, Siv.s2vFinish_short _ _ (by rw [length_bytesAt]; exact hk16), ← t₁,
      ← hc, ctxMac_block _ _ _ (length_bytesAt _ _ _)]

end VG.Proof.AesSiv.X86

end

end

/-!
# AES-SIV on x86: finishing S2V with a string of a block or more

Untrusted: everything here is checked by Lean. For a last string `P` of
`L ≥ 16` bytes, with `k = kOf L` and `j = jOf L` (`Proof/AesSiv/Long.lean`),
the last `T = L − 16 k` bytes of `P` are copied to the tail at `W + 32` and
`D` XORed into its last 16 (`longTail_ok`, `xorend4_mem`): the tail is
`P[16k..] xorend D`. Then the `k` blocks of `P` and the first `j` of the
tail are chained into a zero state at `W + out` and the rest of the tail
finalized (`longMac_ok`), which is S2V's end (`long_spec`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold length_bytesAt readW_writeW_off
  covers_left LoopPre CopyPost copyLoop_ok ofNat_sub32 CT shr4)

/-- `D` XORed into the last 16 of the `T` bytes at `B`, a word at a time. -/
theorem xorend4_mem (m : Mem) {B Q : Addr} {T : Nat} (hT : 16 ≤ T) (hw : B.toNat + T ≤ 2 ^ 64)
    (hd : (⟨B, T⟩ : Region).Disjoint ⟨Q, 16⟩) :
    bytesAt (Cmac.xor4Mem m (B + BitVec.ofNat 64 (T - 16)) Q (B + BitVec.ofNat 64 (T - 16))) B T =
      Spec.Siv.xorend (bytesAt m B T) (bytesAt m Q 16) := by
  obtain hc : Region.Sub ⟨B + BitVec.ofNat 64 (T - 16), 16⟩ ⟨B, T⟩ := Offset.sub_base B (by omega_arith)
  obtain e : T = (T - 16) + 16 := by omega_arith
  obtain hs := Proof.Cmac.Stream.bytesAt_append (Cmac.xor4Mem m (B + BitVec.ofNat 64 (T - 16)) Q
    (B + BitVec.ofNat 64 (T - 16))) B (T - 16) 16
  rw [← e] at hs
  rw [hs, Spec.Siv.xorend, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
  obtain tk := take_bytesAt m B (a := T - 16) (b := 16)
  obtain dr := drop_bytesAt m B (a := T - 16) (b := 16)
  rw [← e] at tk dr
  rw [tk, dr, Proof.AesGcm.X86.bytesAt_frame (Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint B (by omega_arith) (by omega_arith)) (by omega_arith),
    Cmac.xor4Mem_bytes m (c := B + BitVec.ofNat 64 (T - 16)) (p := Q) (q := B + BitVec.ofNat 64 (T - 16))
      (Cmac.Sep4.of_disjoint (hd.sub_left hc)) (Cmac.Sep4.self _), Siv.xor_eq,
    Proof.Cmac.xor_comm]

/-! ## The tail -/

theorem cmp17_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {k : Nat}
    (hk : slotv s.mem W slenO = BitVec.ofNat 32 k) (hk32 : k < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .eax (imm 0), .mov .ecx (slot slenO), .alu .cmp .ecx (imm 17)] s = some s' ∧
      s'.gpr .eax = BitVec.ofNat 32 0 ∧ s'.gpr .ecx = BitVec.ofNat 32 k ∧ s'.cf = some (decide (k < 17)) ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cregs []
  · cregs [hk]
  · cmems [hk, toNat_ofNat32 hk32]; rfl
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `16 k` in `eax`, from the comparison of the length with 17. -/
theorem kBranch_wp {s : State} {k : Nat} (hax : s.gpr .eax = BitVec.ofNat 32 0)
    (hcx : s.gpr .ecx = BitVec.ofNat 32 k) (hcf : s.cf = some (decide (k < 17))) (h16 : 16 ≤ k) (hk32 : k < 2 ^ 32) :
    WP isa (.ite .b (.block []) (.block [.mov .eax (.reg .ecx), .alu .sub .eax (imm 1),
        .alu .and .eax (imm 0xfffffff0), .alu .sub .eax (imm 16)])) s fun s' =>
      s'.gpr .eax = BitVec.ofNat 32 (16 * kOf k) ∧ s'.gpr .ecx = BitVec.ofNat 32 k ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.ite (decide (k < 17)) (eval_b hcf) (fun ht => ?_) (fun hf => ?_)
  · have h₁ := of_decide_eq_true ht
    refine WP.block_nil ⟨by rw [hax, kOf_lt h₁], hcx, fun _ _ => rfl, rfl, rfl, rfl⟩
  · have h₁ := of_decide_eq_false hf
    refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · cregs [hcx]
      rw [ofNat_sub32 (by omega_arith) hk32, Proof.AesSiv.X86.and_m16, toNat_ofNat32 (by omega_arith),
        ofNat_sub32 (by omega_arith) (by omega_arith), kOf_ge h₁]
      congr 1
      omega_arith
    · cregs [hcx]
    · cregs []
    all_goals cmems []

/-- `D` XORed into the last 16 of the `t` bytes of the tail. -/
theorem xorEnd_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {k b t : Nat}
    (hk : slotv s.mem W slenO = BitVec.ofNat 32 k) (hb : slotv s.mem W nbO = BitVec.ofNat 32 b)
    (ht : t = k - b) (hbk : b ≤ k) (hk32 : k < 2 ^ 32) (h16 : 16 ≤ t) (h32 : t ≤ 32) :
    ∃ s', runBlock isa (([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .alu .sub .edx (slot nbO)] :
        List Instr) ++ xorInto dOff (tailOff - 16)) s = some s' ∧
      s'.mem = Cmac.xor4Mem s.mem (w64 W + BitVec.ofNat 64 (t + 16)) (w64 W + BitVec.ofNat 64 dOff)
        (w64 W + BitVec.ofNat 64 (t + 16)) ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hdx : W + BitVec.ofNat 32 k - BitVec.ofNat 32 b = W + BitVec.ofNat 32 t := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, ofNat_sub32 hbk hk32, ht]
  refine ⟨_, by crun [xorInto, E.ebp, L.aW, E.perm.wW, E.perm.wR, hk, hb, hdx, add32_assoc], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hk, hb, hdx, add32_assoc, Cmac.xor4Mem, add_ofNat_assoc, Nat.add_assoc]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

theorem tailArgs_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {P a c : BitVec 32}
    (hax : s.gpr .eax = a) (hcx : s.gpr .ecx = c) (hp : slotv s.mem W strO = P) :
    ∃ s', runBlock isa [.store (at_ .ebp nbO) .eax, .mov .edi (slot strO), .alu .add .edi (.reg .eax),
        .alu .sub .ecx (.reg .eax), .mov .edx (.reg .ebp), .alu .add .edx (imm tailOff)] s = some s' ∧
      s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 nbO) a ∧ s'.gpr .edi = P + a ∧ s'.gpr .ecx = c - a ∧
      s'.gpr .edx = W + BitVec.ofNat 32 32 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hax, hp], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hax]
  · cregs [hax, hp]
  · cregs [hax, hcx]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `longTail`: the tail at `W + 32` is `P[16k..] xorend D`, and `16 k` at
`W + nbO`. -/
theorem longTail_ok {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat} {s : State}
    (h : CmacPre C W SP R P k s) (h16 : 16 ≤ k) :
    WP isa longTail s fun s' => Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩] s.mem s'.mem ∧
      slotv s'.mem W nbO = BitVec.ofNat 32 (16 * kOf k) ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 32) (k - 16 * kOf k) =
        Spec.Siv.xorend ((bytesAt s.mem (w64 P) k).drop (16 * kOf k))
          (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16) := by
  have E := h.env
  have B := h.buf
  have hk32 := h.k32
  obtain hT := kOf_tail h16
  obtain ⟨s₁, run₁, ax₁, cx₁, cf₁, bp₁, sp₁, m₁, rd₁, wr₁⟩ := cmp17_ok L E h.slen hk32
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (kBranch_wp ax₁ cx₁ cf₁ h16 hk32) fun s₂ ⟨ax₂, cx₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  obtain E₂ : Env C W SP s₂ := ⟨by rw [g₂ _ (by decide), bp₁], by rw [g₂ _ (by decide), sp₁],
    E.perm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩
  obtain ⟨s₃, run₃, m₃, di₃, cx₃, dx₃, bp₃, sp₃, rd₃, wr₃⟩ := tailArgs_ok L E₂ (P := P) ax₂ cx₂
    (by rw [m₂, m₁]; exact h.str)
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain E₃ : Env C W SP s₃ := ⟨bp₃, sp₃, E₂.perm.of_eq rd₃ wr₃⟩
  obtain hkk : 16 * kOf k ≤ k := by omega_arith
  obtain hwk : P.toNat + 16 * kOf k < 2 ^ 32 := by have := B.wrap; omega_arith
  obtain B₃ : Buf W SP s₃ (P + BitVec.ofNat 32 (16 * kOf k)) (k - 16 * kOf k) :=
    (B.drop hkk hwk).of_eq (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
  have hW := L.fw
  refine WP.seq (WP.mono (copyLoop_ok s₃ ⟨di₃, dx₃, by rw [cx₃, ofNat_sub32 hkk hk32], by omega_arith, by omega_arith, B₃.wrap,
    by rw [L.nW (o := 32) (by decide)]; omega_arith, B₃.rd, by rw [L.aW (by decide)]; exact E₃.perm.wC (by omega_arith),
    by rw [L.aW (by decide)]; exact B₃.w.sub_right (Lay.wSub (by omega_arith))⟩) fun s₄ c₄ => ?_)
  obtain E₄ : Env C W SP s₄ := ⟨by rw [c₄.other _ (by decide) (by decide) (by decide) (by decide), bp₃],
    by rw [c₄.other _ (by decide) (by decide) (by decide) (by decide), sp₃], E₃.perm.of_eq c₄.rd c₄.wr⟩
  -- The slots `xorEnd` reads.
  obtain f₃₄ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₃.mem s₄.mem := by
    rw [c₄.mem, L.aW (by decide)]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]; exact Offset.contains (w64 W) (d := 32) (n := k - 16 * kOf k) (e := 32) (k := 32)
        (by omega_arith) (by omega_arith) (by omega_arith))
  obtain k₄ : ∀ o, 64 ≤ o → o + 4 ≤ 2576 → slotv s₄.mem W o = slotv s₃.mem W o := fun o h₁ h₂ =>
    f₃₄.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide))
      (by decide)
  obtain nb₃ : slotv s₃.mem W nbO = BitVec.ofNat 32 (16 * kOf k) := by
    rw [m₃]; exact Mem.readW_writeW_self32 _ _ _
  obtain sl₃ : slotv s₃.mem W slenO = BitVec.ofNat 32 k := by
    rw [m₃, slotv, readW_writeW_off _ _ _ (by decide) (by decide) (by decide), m₂, m₁]; exact h.slen
  obtain ⟨s₅, run₅, m₅, bp₅, sp₅, rd₅, wr₅⟩ := xorEnd_ok L E₄ (by rw [k₄ _ (by decide) (by decide)]; exact sl₃)
    (by rw [k₄ _ (by decide) (by decide)]; exact nb₃) rfl hkk hk32 hT.1 hT.2
  -- What it writes.
  obtain f₃ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩] s.mem s₃.mem := by
    rw [m₃, m₂, m₁]
    exact (Frame.refl _ _).writeW (r := ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩) (by simp) _ (Region.contains_self _ _)
  obtain f₄ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩] s.mem s₄.mem :=
    f₃.trans (f₃₄.mono (by simp))
  obtain f₅ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₄.mem s₅.mem := by
    rw [m₅]
    exact (Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_arith)⟩
  refine WP.of_runBlock ⟨s₅, run₅, ⟨bp₅, sp₅, E₄.perm.of_eq rd₅ wr₅⟩,
    by rw [rd₅, c₄.rd, rd₃, rd₂, rd₁], by rw [wr₅, c₄.wr, wr₃, wr₂, wr₁], f₄.trans (f₅.mono (by simp)), ?_, ?_⟩
  · exact ((f₅.readW (w := 32) (r := ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)).trans (k₄ _ (by decide) (by decide))).trans nb₃
  · have e : w64 W + BitVec.ofNat 64 (k - 16 * kOf k + 16) =
        w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (k - 16 * kOf k - 16) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_arith
    obtain hw : (w64 W + BitVec.ofNat 64 32).toNat + (k - 16 * kOf k) ≤ 2 ^ 64 := by
      rw [← L.aW (o := 32) (by decide), Proof.AesGcm.X86.toNat_w64, L.nW (o := 32) (by decide)]; omega_arith
    obtain hd : (⟨w64 W + BitVec.ofNat 64 32, k - 16 * kOf k⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 dOff, 16⟩ :=
      Lay.w_w (.inl (by rw [show dOff = 2560 from rfl]; omega_arith)) (by omega_arith) (by decide)
    obtain hP : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 32) (k - 16 * kOf k) =
        (bytesAt s.mem (w64 P) k).drop (16 * kOf k) := by
      obtain hl : (bytesAt s₃.mem (w64 (P + BitVec.ofNat 32 (16 * kOf k))) (k - 16 * kOf k)).length < 2 ^ 64 := by
        rw [length_bytesAt]; omega_arith
      have := Proof.AesGcm.X86.bytesAt_writeBytes_self s₃.mem (w64 (W + BitVec.ofNat 32 32)) _ hl
      rw [length_bytesAt] at this
      rw [c₄.mem, ← L.aW (o := 32) (by decide), this, Buf.ptr hwk,
        ← drop_bytesAt s₃.mem (w64 P) (a := 16 * kOf k) (b := k - 16 * kOf k), Nat.add_sub_cancel' hkk,
        Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          rcases hr with rfl | rfl <;> exact B.w.sub_right (Lay.wSub (by decide)))
          (by have := B.lt; omega_arith)]
    obtain hD : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 dOff) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16 :=
      Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    rw [m₅, e, xorend4_mem _ hT.1 hw hd, hP, hD]

/-! ## The calls -/

/-- The zero state at `W + out`, and the arguments for the `k` blocks of `P`. -/
theorem lm1_ok {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {s : State} (E : Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) {P : BitVec 32}
    (hp : slotv s.mem W strO = P) {n : Nat} (hn : slotv s.mem W nbO = BitVec.ofNat 32 (16 * n))
    (hn32 : 16 * n < 2 ^ 32) {out : Nat} (hout : out = 0 ∨ out = 112) :
    ∃ s', runBlock isa (zero4 out ++ ([.mov .esi (slot nbO), .shift .shr .esi 4, .mov .ebx (slot strO)] :
        List Instr) ++ macArgs out) s = some s' ∧
      s'.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 out) ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 out ∧
      s'.gpr .ebx = P ∧ s'.gpr .esi = BitVec.ofNat 32 n ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain z := zero4_fold s.mem W out
  obtain hsh := shr4 hn32
  rw [Nat.mul_div_cancel_left _ (by decide)] at hsh
  rcases hout with rfl | rfl
  all_goals
    simp only [Nat.reduceAdd] at z
    refine ⟨_, by crun [zero4, macArgs, E.ebp, L.aW, E.perm.wW, E.perm.wR, hc, hr, hp, hn], ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [z]
    · cregs [hc]
    · cregs [hr]
    · cregs [E.ebp]
    · cregs [hp]
    · cregs [hn, hsh]
    · cregs [E.ebp]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []

theorem cmp17s_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {k : Nat}
    (hk : slotv s.mem W slenO = BitVec.ofNat 32 k) (hk32 : k < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .esi (imm 0), .mov .ecx (slot slenO), .alu .cmp .ecx (imm 17)] s = some s' ∧
      s'.gpr .esi = BitVec.ofNat 32 0 ∧ s'.cf = some (decide (k < 17)) ∧
      (∀ r, r ≠ .esi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hk], ?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · cregs []
  · cmems [hk, toNat_ofNat32 hk32]; rfl
  · cregs []
  all_goals cmems []

/-- `j` in `esi`. -/
theorem jBranch_wp {s : State} {k : Nat} (hsi : s.gpr .esi = BitVec.ofNat 32 0)
    (hcf : s.cf = some (decide (k < 17))) :
    WP isa (.ite .b (.block []) (.block [.mov .esi (imm 1)])) s fun s' =>
      s'.gpr .esi = BitVec.ofNat 32 (jOf k) ∧ (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.ite (decide (k < 17)) (eval_b hcf) (fun ht => ?_) (fun hf => ?_)
  · have h₁ := of_decide_eq_true ht
    refine WP.block_nil ⟨by rw [hsi]; simp [jOf, h₁], fun _ _ => rfl, rfl, rfl, rfl⟩
  · have h₁ := of_decide_eq_false hf
    refine WP.of_runBlock ⟨_, by crun [], ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · cregs []; simp [jOf, h₁]
    · cregs []
    all_goals cmems []

/-- `j` at `W + jO`, and the arguments for the first `j` blocks of the tail. -/
theorem lm3_ok {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {s : State} (E : Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) {j : Nat}
    (hsi : s.gpr .esi = BitVec.ofNat 32 j) {out : Nat} :
    ∃ s', runBlock isa (([.store (at_ .ebp jO) .esi, .mov .ebx (.reg .ebp), .alu .add .ebx (imm tailOff)] :
        List Instr) ++ macArgs out) s = some s' ∧
      s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 jO) (BitVec.ofNat 32 j) ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 out ∧
      s'.gpr .ebx = W + BitVec.ofNat 32 32 ∧ s'.gpr .esi = BitVec.ofNat 32 j ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain rd : ∀ o, o + 4 ≤ jO →
      slotv (s.mem.writeW (w64 W + BitVec.ofNat 64 jO) (BitVec.ofNat 32 j)) W o = slotv s.mem W o :=
    fun o h₁ => readW_writeW_off _ _ _ (.inl h₁) (by simp only [jO] at h₁; omega_arith) (by decide)
  obtain hc' := (rd ctxO (by decide)).trans hc
  obtain hr' := (rd roundsO (by decide)).trans hr
  refine ⟨_, by crun [macArgs, E.ebp, L.aW, E.perm.wW, E.perm.wR, hsi, hc', hr'], ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hsi]
  · cregs [hc']
  · cregs [hr']
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [hsi]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- The arguments for the rest of the tail. -/
theorem lm5_ok {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {s : State} (E : Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) {j k b : Nat}
    (hj : slotv s.mem W jO = BitVec.ofNat 32 j) (hk : slotv s.mem W slenO = BitVec.ofNat 32 k)
    (hb : slotv s.mem W nbO = BitVec.ofNat 32 b) (hj1 : j ≤ 1) (hbk : b + 16 * j ≤ k) (hk32 : k < 2 ^ 32)
    {out : Nat} :
    ∃ s', runBlock isa (([.mov .eax (slot jO), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
        .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .mov .esi (slot slenO),
        .alu .sub .esi (slot nbO), .alu .sub .esi (.reg .eax), .mov .ebx (.reg .ebp),
        .alu .add .ebx (imm tailOff), .alu .add .ebx (.reg .eax)] : List Instr) ++ macArgs out) s = some s' ∧
      s'.mem = s.mem ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 out ∧
      s'.gpr .ebx = W + BitVec.ofNat 32 (32 + 16 * j) ∧ s'.gpr .esi = BitVec.ofNat 32 (k - b - 16 * j) ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain h₁ := ofNat_sub32 (a := k) (b := b) (by omega_arith) hk32
  obtain h₂ := ofNat_sub32 (a := k - b) (b := 16 * j) (by omega_arith) (by omega_arith)
  rcases (by omega_arith : j = 0 ∨ j = 1) with rfl | rfl
  all_goals
    refine ⟨_, by crun [macArgs, E.ebp, L.aW, E.perm.wR, hc, hr, hj, hk, hb], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hc]
    · cregs [hr]
    · cregs [E.ebp]
    · cregs [E.ebp, hj]
      simp only [BitVec.reduceAdd]
      rw [add32_assoc]
    · cregs [hj, hk, hb]
      simp only [BitVec.reduceAdd]
      rw [h₁]
      exact h₂
    · cregs [E.ebp]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals rfl

/-! ## The long case -/

/-- What `longMac` writes: the output, `j`, the working space of the functions
called and the stack below `SP`. -/
abbrev macR (W SP : BitVec 32) (out : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 out, 16⟩, ⟨w64 W + BitVec.ofNat 64 jO, 4⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩,
    below SP 60]

theorem out_macR {W SP : BitVec 32} {out : Nat} :
    ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 out, 16⟩ : Region)], ∃ r' ∈ macR W SP out, Region.Sub r r' :=
  fun r hr => ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self, fun _ h => h⟩

theorem jO_macR {W SP : BitVec 32} {out : Nat} :
    ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 jO, 4⟩ : Region)], ∃ r' ∈ macR W SP out, Region.Sub r r' :=
  fun r hr => ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
    fun _ h => h⟩

theorem macR_finR {W SP : BitVec 32} {out : Nat} : ∀ r ∈ macR W SP out, ∃ r' ∈ finR W SP out, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨wS W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem call_macR {W SP : BitVec 32} {out : Nat} :
    ∀ r ∈ [⟨w64 W + BitVec.ofNat 64 out, 16⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 60],
      ∃ r' ∈ macR W SP out, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

theorem finR_buf {W SP : BitVec 32} {s : State} {P : BitVec 32} {k : Nat} (B : Buf W SP s P k) {out : Nat}
    (hout : out = 0 ∨ out = 112) : ∀ r ∈ finR W SP out, (⟨w64 P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B.w.sub_right (Lay.wSub (by omega_arith))
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.stk.symm

/-- The tail, apart from what `longMac` writes. -/
theorem tail_macR {C W SP : BitVec 32} (L : Lay C W SP) {out t : Nat} (hout : out = 0 ∨ out = 112) (ht : t ≤ 32) :
    ∀ r ∈ macR W SP out, (⟨w64 W + BitVec.ofNat 64 32, t⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.w_w (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Lay.w_w (.inl (by simp only [jO]; omega_arith)) (by omega_arith) (by decide)
  · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (L.stk_w' (by omega_arith)).symm

theorem slot_macR' {C W SP : BitVec 32} (L : Lay C W SP) {out : Nat} (hout : out = 0 ∨ out = 112) {m m' : Mem}
    (hf : Frame [⟨w64 W + BitVec.ofNat 64 out, 16⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 60] m m')
    {o : Nat} (h₁ : 176 ≤ o) (h₂ : o + 4 ≤ 256) : slotv m' W o = slotv m W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact Lay.w_w (.inl h₂) (by omega_arith) (by decide)
    · exact (L.stk_w' (by omega_arith)).symm) (by decide)

/-- The slots `longMac` reads. -/
theorem slot_macR {C W SP : BitVec 32} (L : Lay C W SP) {out : Nat} (hout : out = 0 ∨ out = 112) {m m' : Mem}
    (hf : Frame (macR W SP out) m m') {o : Nat} (h₁ : 176 ≤ o) (h₂ : o + 4 ≤ jO) :
    slotv m' W o = slotv m W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by omega_arith)) (by simp only [jO] at h₂; omega_arith) (by omega_arith)
    · exact Lay.w_w (.inl h₂) (by simp only [jO] at h₂; omega_arith) (by decide)
    · exact Lay.w_w (.inl (by simp only [jO] at h₂; omega_arith)) (by simp only [jO] at h₂; omega_arith) (by decide)
    · exact (L.stk_w' (by simp only [jO] at h₂; omega_arith)).symm) (by decide)

/-- The slots a call keeps. -/
theorem slot_call {C W SP : BitVec 32} (L : Lay C W SP) {out : Nat} (hout : out = 0 ∨ out = 112) {m m' : Mem}
    (hf : Frame [⟨w64 W + BitVec.ofNat 64 out, 16⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 60] m m')
    {o : Nat} (h₁ : 176 ≤ o) (h₂ : o + 4 ≤ 256) : slotv m' W o = slotv m W o :=
  slot_macR' L hout hf h₁ h₂

/-- The long case: `k` blocks of `P`, `j` of the tail, and the rest of the
tail, into `W + out`. -/
theorem finishLong_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {k : Nat} {s : State} (h : CmacPre C W SP R P k s)
    (h16 : 16 ≤ k) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (.seq longTail (longMac v.callee v.suffix out)) s (FinPost C W SP R out P k s) := by
  obtain hRb : R ≤ 14 := by omega_arith
  have hk32 := h.k32
  have B := h.buf
  obtain hT := kOf_tail h16
  obtain hJ := jOf_rest h16
  obtain hj1 := jOf_le k
  obtain hkk : 16 * kOf k ≤ k := by omega_arith
  obtain hyo : StOk out := by rcases hout with rfl | rfl <;> decide
  refine WP.seq (WP.mono (longTail_ok L h h16) fun s₁ ⟨E₁, rd₁, wr₁, f₁, nb₁, t₁⟩ => ?_)
  obtain k₁ : ∀ o, 176 ≤ o → o + 4 ≤ 208 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
      · exact Lay.w_w (.inl h₂) (by omega_arith) (by decide)) (by decide)
  -- The `k` blocks of `P`.
  obtain ⟨s₂, run₂, m₂, ax₂, cx₂, dx₂, bx₂, si₂, di₂, bp₂, sp₂, rd₂, wr₂⟩ := lm1_ok (C := C) (R := R) (P := P) L E₁
    (by rw [k₁ _ (by decide) (by decide)]; exact h.ctx) (by rw [k₁ _ (by decide) (by decide)]; exact h.rounds)
    (by rw [k₁ _ (by decide) (by decide)]; exact h.str) nb₁ (by omega_arith) hout
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain E₂ : Env C W SP s₂ := ⟨bp₂, sp₂, E₁.perm.of_eq rd₂ wr₂⟩
  obtain B₂ : Buf W SP s₂ P (16 * kOf k) := (B.take hkk).of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  refine WP.seq (WP.mono (updCall_ok v L E₂ hR (y := out) hyo (srcBuf B₂)
    (B₂.w.sub_right (Lay.wSub (by omega_arith))) (by omega_arith) ax₂ cx₂ dx₂ bx₂ si₂ di₂)
    fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, o₃⟩ => ?_)
  obtain fz : Frame [⟨w64 W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact Cmac.frame_store4 _ _ _ _ _
  obtain f₁₃ : Frame (macR W SP out) s₁.mem s₃.mem :=
    (fz.sub out_macR).trans (f₃.sub call_macR)
  -- `j`.
  obtain k₃ : ∀ o, 176 ≤ o → o + 4 ≤ 208 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    (slot_macR L hout f₁₃ h₁ (by simp only [jO]; omega_arith)).trans (k₁ o h₁ h₂)
  obtain nb₃ : slotv s₃.mem W nbO = BitVec.ofNat 32 (16 * kOf k) :=
    (slot_macR L hout f₁₃ (o := nbO) (by decide) (by decide)).trans nb₁
  obtain ⟨s₄, run₄, si₄, cf₄, g₄, m₄, rd₄, wr₄⟩ := cmp17s_ok L E₃
    (by rw [k₃ _ (by decide) (by decide)]; exact h.slen) hk32
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  obtain E₄ : Env C W SP s₄ := ⟨by rw [g₄ _ (by decide) (by decide), E₃.ebp],
    by rw [g₄ _ (by decide) (by decide), E₃.esp], E₃.perm.of_eq rd₄ wr₄⟩
  refine WP.seq (WP.mono (jBranch_wp si₄ cf₄) fun s₅ ⟨si₅, g₅, m₅, rd₅, wr₅⟩ => ?_)
  obtain E₅ : Env C W SP s₅ := ⟨by rw [g₅ _ (by decide), E₄.ebp], by rw [g₅ _ (by decide), E₄.esp],
    E₄.perm.of_eq rd₅ wr₅⟩
  obtain k₅ : ∀ o, slotv s₅.mem W o = slotv s₃.mem W o := fun o => by rw [m₅, m₄]
  obtain ⟨s₆, run₆, m₆, ax₆, cx₆, dx₆, bx₆, si₆, di₆, bp₆, sp₆, rd₆, wr₆⟩ := lm3_ok (out := out) L E₅
    (by rw [k₅, k₃ _ (by decide) (by decide)]; exact h.ctx)
    (by rw [k₅, k₃ _ (by decide) (by decide)]; exact h.rounds) si₅
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  obtain E₆ : Env C W SP s₆ := ⟨bp₆, sp₆, E₅.perm.of_eq rd₆ wr₆⟩
  obtain f₃₆ : Frame [⟨w64 W + BitVec.ofNat 64 jO, 4⟩] s₃.mem s₆.mem := by
    rw [m₆, m₅, m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  -- The first `j` blocks of the tail.
  refine WP.seq (WP.mono (updCall_ok v L E₆ hR (y := out) hyo (n := jOf k)
    (srcW L E₆.perm (t := 32) (k := 16 * jOf k) (by omega_arith))
    (by rw [L.aW (o := 32) (by decide)]; exact Lay.w_w (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
    ax₆ cx₆ dx₆ bx₆ si₆ di₆) fun s₇ ⟨E₇, rd₇, wr₇, _, f₇, o₇⟩ => ?_)
  obtain f₃₇ : Frame (macR W SP out) s₃.mem s₇.mem :=
    (f₃₆.sub jO_macR).trans (f₇.sub call_macR)
  obtain k₇ : ∀ o, 176 ≤ o → o + 4 ≤ 208 → slotv s₇.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    (slot_call L hout f₇ h₁ (by omega_arith)).trans ((slot_macR L hout (f₃₆.sub jO_macR)
      h₁ (by simp only [jO]; omega_arith)).trans (k₃ o h₁ h₂))
  obtain nb₇ : slotv s₇.mem W nbO = BitVec.ofNat 32 (16 * kOf k) :=
    (slot_call L hout f₇ (o := nbO) (by decide) (by decide)).trans ((slot_macR L hout
      (f₃₆.sub jO_macR) (o := nbO) (by decide) (by decide)).trans nb₃)
  obtain j₇ : slotv s₇.mem W jO = BitVec.ofNat 32 (jOf k) :=
    (slot_call L hout f₇ (o := jO) (by decide) (by decide)).trans (by rw [m₆]; exact Mem.readW_writeW_self32 _ _ _)
  -- The rest of the tail.
  obtain ⟨s₈, run₈, m₈, ax₈, cx₈, dx₈, bx₈, si₈, di₈, bp₈, sp₈, rd₈, wr₈⟩ := lm5_ok (out := out) L E₇
    (by rw [k₇ _ (by decide) (by decide)]; exact h.ctx) (by rw [k₇ _ (by decide) (by decide)]; exact h.rounds) j₇
    (by rw [k₇ _ (by decide) (by decide)]; exact h.slen) nb₇ hj1 (by omega_arith) hk32
  refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  obtain E₈ : Env C W SP s₈ := ⟨bp₈, sp₈, E₇.perm.of_eq rd₈ wr₈⟩
  refine WP.mono (finCall_ok v L E₈ hR (y := out) hyo (P := W + BitVec.ofNat 32 (32 + 16 * jOf k))
    (l := k - 16 * kOf k - 16 * jOf k) (by omega_arith)
    (srcW L E₈.perm (t := 32 + 16 * jOf k) (k := k - 16 * kOf k - 16 * jOf k) (by omega_arith))
    (by rw [L.aW (by omega_arith)]; exact Lay.w_w (by omega_arith) (by omega_arith) (by omega_arith)) ax₈ cx₈ dx₈ bx₈ si₈ di₈)
    fun s₉ ⟨E₉, rd₉, wr₉, _, f₉, o₉⟩ => ?_
  -- What it writes.
  obtain f₁₉ : Frame (macR W SP out) s₁.mem s₉.mem :=
    (f₁₃.trans f₃₇).trans (by rw [← m₈]; exact f₉.sub call_macR)
  obtain F₁ : Frame (finR W SP out) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨wS W, by simp, Offset.sub _ (by decide) (by decide)⟩
  obtain F : ∀ {m : Mem}, Frame (macR W SP out) s₁.mem m → Frame (finR W SP out) s.mem m :=
    fun hm => F₁.trans (hm.sub macR_finR)
  refine ⟨E₉, by rw [rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₉, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁], F f₁₉, ?_⟩
  -- S2V's end.
  have hC {d n : Nat} (hd : d + n ≤ 512) {m : Mem} (hm : Frame (macR W SP out) s₁.mem m) :
      bytesAt m (w64 C + BitVec.ofNat 64 d) n = bytesAt s.mem (w64 C + BitVec.ofNat 64 d) n :=
    Proof.AesGcm.X86.bytesAt_frame (F hm) (fun r hr => (finR_c L hout r hr).sub_left (Offset.sub_base _ hd))
      (by omega_arith)
  have hTl {n : Nat} (hn : n ≤ 32) {m : Mem} (hm : Frame (macR W SP out) s₁.mem m) :
      bytesAt m (w64 W + BitVec.ofNat 64 32) n = bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) n :=
    Proof.AesGcm.X86.bytesAt_frame hm (tail_macR L hout hn) (by omega_arith)
  obtain f₁₂ : Frame (macR W SP out) s₁.mem s₂.mem := fz.sub out_macR
  obtain f₁₆ : Frame (macR W SP out) s₁.mem s₆.mem :=
    f₁₃.trans (f₃₆.sub jO_macR)
  obtain f₁₈ : Frame (macR W SP out) s₁.mem s₈.mem := by rw [m₈]; exact f₁₃.trans f₃₇
  obtain sch₈ := hC (d := 0) (n := 16 * (R + 1)) (by omega_arith) f₁₈
  obtain sch₆ := hC (d := 0) (n := 16 * (R + 1)) (by omega_arith) f₁₆
  obtain sch₂ := hC (d := 0) (n := 16 * (R + 1)) (by omega_arith) f₁₂
  obtain k1 := hC (d := 240) (n := 16) (by decide) f₁₈
  obtain k2 := hC (d := 256) (n := 16) (by decide) f₁₈
  rw [BitVec.add_zero] at sch₈ sch₆ sch₂
  -- The state after each call.
  obtain hz : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂]; exact Cmac.zero4_bytes _ _
  obtain s₆o : bytesAt s₆.mem (w64 W + BitVec.ofNat 64 out) 16 = bytesAt s₃.mem (w64 W + BitVec.ofNat 64 out) 16 :=
    Proof.AesGcm.X86.bytesAt_frame f₃₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by simp only [jO]; omega_arith)) (by omega_arith) (by decide)) (by decide)
  obtain pP : bytesAt s₂.mem (w64 P) (16 * kOf k) = (bytesAt s.mem (w64 P) k).take (16 * kOf k) := by
    rw [Proof.AesGcm.X86.bytesAt_frame (F f₁₂) (fun r hr => (finR_buf B hout r hr).sub_left
      (Region.sub_prefix hkk)) (by have := B.lt; omega_arith)]
    have := take_bytesAt s.mem (w64 P) (a := 16 * kOf k) (b := k - 16 * kOf k)
    rw [Nat.add_sub_cancel' hkk] at this
    exact this.symm
  -- The tail.
  obtain tl : (Spec.Siv.xorend ((bytesAt s.mem (w64 P) k).drop (16 * kOf k))
      (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16)).length = k - 16 * kOf k := by
    rw [← t₁, length_bytesAt]
  obtain pT : bytesAt s₆.mem (w64 W + BitVec.ofNat 64 32) (16 * jOf k) =
      (Spec.Siv.xorend ((bytesAt s.mem (w64 P) k).drop (16 * kOf k))
        (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16)).take (16 * jOf k) := by
    rw [hTl (by omega_arith) f₁₆, ← t₁]
    have := take_bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) (a := 16 * jOf k) (b := k - 16 * kOf k - 16 * jOf k)
    rw [Nat.add_sub_cancel' hJ.1] at this
    exact this.symm
  obtain dT : bytesAt s₈.mem (w64 (W + BitVec.ofNat 32 (32 + 16 * jOf k))) (k - 16 * kOf k - 16 * jOf k) =
      (Spec.Siv.xorend ((bytesAt s.mem (w64 P) k).drop (16 * kOf k))
        (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16)).drop (16 * jOf k) := by
    rw [← t₁, L.aW (by omega_arith), ← hTl (by omega_arith) f₁₈]
    have := drop_bytesAt s₈.mem (w64 W + BitVec.ofNat 64 32) (a := 16 * jOf k) (b := k - 16 * kOf k - 16 * jOf k)
    rw [Nat.add_sub_cancel' hJ.1, BitVec.add_assoc, BitVec.ofNat_add_ofNat] at this
    exact this.symm
  obtain spec := long_spec (Spec.Siv.schedCiph s.mem (w64 C) R) (bytesAt s.mem (w64 C + 240) 16)
    (bytesAt s.mem (w64 C + 256) 16) (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (w64 P) k)
    (length_bytesAt _ _ _) (by rw [length_bytesAt]; exact h16)
  rw [length_bytesAt] at spec
  rw [o₉, m₈, o₇, s₆o, o₃, hz, Proof.Cmac.Stream.blocksAt_eq, Proof.Cmac.Stream.blocksAt_eq, pP,
    L.aW (o := 32) (by decide), pT, ← m₈, dT, sch₈, sch₆, sch₂, k1, k2, Spec.Siv.ctxMac, ← spec]
  rfl

end VG.Proof.AesSiv.X86
