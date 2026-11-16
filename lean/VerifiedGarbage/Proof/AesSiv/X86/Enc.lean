module

public import VerifiedGarbage.Impl.AesSiv.X86
public import VerifiedGarbage.Proof.AesGcm.X86.Fn
import VerifiedGarbage.Proof.AesSiv.X86.Run
import VerifiedGarbage.Proof.AesSiv.X86.Env
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesSiv.X86.Ctr
public import VerifiedGarbage.Proof.AesSiv.X86.FinishShort
public import VerifiedGarbage.Proof.AesSiv.X86.S2v
import VerifiedGarbage.Proof.AesSiv.X86.Finish
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesGcm.X86.Loops

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
