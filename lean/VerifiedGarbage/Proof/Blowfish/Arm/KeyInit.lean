module
public import VerifiedGarbage.Proof.Blowfish.Arm.Run

import VerifiedGarbage.Proof.Blowfish.Arm.Ecb
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# Blowfish on ARMv7: the initial schedule

`initSchedule_run`: the 4168 bytes of the initial schedule's image, copied
from the table at `initSym` into the schedule at `r2`, seven words a step
(`copyWords_run`: the loads, then the stores) and six at the end.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

theorem copyReg_nodup : ∀ i < 7, ∀ j < 7, copyReg i = copyReg j → i = j := by decide

theorem copyReg_mem : ∀ i < 7, copyReg i ∈ copyRegs := by decide

theorem ldr_exec (u : State) (t b : Reg) {off : Nat} (ho : off < 4096)
    (hr : InRegions (u.rd ++ u.wr) (State.addr (u.gpr b + BitVec.ofNat 32 off)) 4) :
    exec (.ldr t b off) u = some (u.setReg t (u.mem.readW (State.addr (u.gpr b + BitVec.ofNat 32 off)) 32)) := by
  simp only [exec, ho, ↓reduceIte, State.load32, hr, Option.map_some]

theorem str_exec (u : State) (t b : Reg) {off : Nat} (ho : off < 4096)
    (hw : InRegions u.wr (State.addr (u.gpr b + BitVec.ofNat 32 off)) 4) :
    exec (.str t b off) u = some (withMem u (u.mem.writeW (State.addr (u.gpr b + BitVec.ofNat 32 off)) (u.gpr t))) := by
  simp only [exec, ho, ↓reduceIte, store32_eq, hw]

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem map_range_succ {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = (List.range n).map f ++ ([f n] : List α) := by
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The loads of `copyWords k`: word `i` at `S + 4 i` into `copyReg i`. -/
theorem copyLoads_run (u : State) {S : BitVec 32} (h9 : u.gpr .r9 = S) :
    ∀ k ≤ 7, (∀ i < k, InRegions (u.rd ++ u.wr) (State.addr (S + BitVec.ofNat 32 (4 * i))) 4) →
    WP isa (.block ((List.range k).map fun i => Instr.ldr (copyReg i) .r9 (4 * i))) u fun t =>
      (∀ i < k, t.gpr (copyReg i) = u.mem.readW (State.addr (S + BitVec.ofNat 32 (4 * i))) 32) ∧
      t.mem = u.mem ∧ Keep copyRegs u t := by
  intro k hk hr
  induction k with
  | zero => exact WP.block_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), rfl, Keep.refl _ _⟩
  | succ k ih =>
    rw [map_range_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) fun i hi => hr i (by omega)) fun t ⟨tg, tm, tk⟩ => ?_
    have t9 : t.gpr .r9 = S := by rw [tk.gpr (by decide), h9]
    have hrt : InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r9 + BitVec.ofNat 32 (4 * k))) 4 := by
      rw [keep_reads tk, t9]; exact hr k (by omega)
    refine WP.of_runBlock ⟨_, by rw [runBlock_cons, ldr_exec t _ _ (by omega) hrt, runStep_some, runBlock_nil], ?_⟩
    refine ⟨fun i hi => ?_, by rw [mem_setReg, tm], ?_⟩
    · by_cases e : i = k
      · subst e; rw [gpr_setReg_self, t9, tm]
      · rw [gpr_setReg_of_ne _ _ (fun h => e (copyReg_nodup i (by omega) k (by omega) h)), tg i (by omega)]
    · refine ⟨fun r hr' => ?_, tk.2.1, tk.2.2.1, tk.2.2.2⟩
      rw [gpr_setReg_of_ne _ _ (fun (h : r = copyReg k) => hr' (h ▸ copyReg_mem k (by omega))), tk.gpr hr']

/-- The stores of `copyWords k`: `copyReg i`, holding `w i`, at `D + 4 i`,
within `N` bytes from `D`. -/
theorem copyStores_run (v : State) {D : BitVec 32} {N : Nat} (h11 : v.gpr .r11 = D)
    (fit : D.toNat + N ≤ 2 ^ 32) (hw : InRegions v.wr (State.addr D) N) (w : Nat → BitVec 32) :
    ∀ k ≤ 7, 4 * k ≤ N → (∀ i < k, v.gpr (copyReg i) = w i) →
    WP isa (.block ((List.range k).map fun i => Instr.str (copyReg i) .r11 (4 * i))) v fun t =>
      (∀ o < 4 * k, t.mem (State.addr D + BitVec.ofNat 64 o) = (w (o / 4)).extractLsb' (8 * (o % 4)) 8) ∧
      Frame [⟨State.addr D, N⟩] v.mem t.mem ∧ Keep [] v t := by
  intro k hk hN hv
  induction k with
  | zero => exact WP.block_nil ⟨fun o ho => absurd ho (by omega), Frame.refl _ _, Keep.refl _ _⟩
  | succ k ih =>
    rw [map_range_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) (by omega) fun i hi => hv i (by omega)) fun t ⟨tb, tf, tk⟩ => ?_
    have ea : State.addr (t.gpr .r11 + BitVec.ofNat 32 (4 * k)) = State.addr D + BitVec.ofNat 64 (4 * k) := by
      rw [tk.gpr (by decide), h11]; exact addr_add (by omega)
    have hwt : InRegions t.wr (State.addr (t.gpr .r11 + BitVec.ofNat 32 (4 * k))) 4 := by
      rw [ea, tk.2.2.1]; exact inRegions_off hw (by omega)
    refine WP.of_runBlock ⟨_, by rw [runBlock_cons, str_exec t _ _ (by omega) hwt, runStep_some, runBlock_nil], ?_⟩
    have tv : t.gpr (copyReg k) = w k := by rw [tk.gpr (List.not_mem_nil), hv k (by omega)]
    rw [ea, tv]
    refine ⟨fun o ho => ?_, ?_, ⟨fun r hr => tk.gpr hr, tk.2.1, tk.2.2.1, tk.2.2.2⟩⟩
    · rw [mem_store]
      by_cases hl : o < 4 * k
      · rw [writeW32_other _ (Offset.disjoint _ (by omega) (by omega) (by omega)), tb o hl]
      · rw [show o = 4 * k + (o - 4 * k) by omega, ← Offset.add_add, st_byte _ _ _ (by omega),
          show (4 * k + (o - 4 * k)) / 4 = k by omega, show (4 * k + (o - 4 * k)) % 4 = o - 4 * k by omega]
    · rw [mem_store]
      exact tf.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

/-- `copyWords k`: `4 k` bytes from `S` (readable) to `D` (writable). -/
theorem copyWords_run (u : State) {S D : BitVec 32} {k : Nat} (hk : k ≤ 7) (h9 : u.gpr .r9 = S)
    (h11 : u.gpr .r11 = D) (fitS : S.toNat + 4 * k ≤ 2 ^ 32) (fitD : D.toNat + 4 * k ≤ 2 ^ 32)
    (hr : InRegions (u.rd ++ u.wr) (State.addr S) (4 * k)) (hw : InRegions u.wr (State.addr D) (4 * k)) :
    WP isa (.block (copyWords k)) u fun t =>
      (∀ o < 4 * k, t.mem (State.addr D + BitVec.ofNat 64 o) = u.mem (State.addr S + BitVec.ofNat 64 o)) ∧
      Frame [⟨State.addr D, 4 * k⟩] u.mem t.mem ∧ Keep copyRegs u t := by
  unfold copyWords
  rw [WP.block_append_iff]
  have ea : ∀ i < k, State.addr (S + BitVec.ofNat 32 (4 * i)) = State.addr S + BitVec.ofNat 64 (4 * i) :=
    fun i hi => addr_add (by omega)
  refine WP.mono (copyLoads_run u h9 k hk fun i hi => by
    rw [ea i hi]; exact inRegions_off hr (by omega)) fun v ⟨vg, vm, vk⟩ => ?_
  refine WP.mono (copyStores_run v (by rw [vk.gpr (by decide), h11]) fitD (by rw [vk.2.2.1]; exact hw)
    (fun i => u.mem.readW (State.addr (S + BitVec.ofNat 32 (4 * i))) 32) k hk (by omega) vg)
    fun t ⟨tb, tf, tk⟩ => ⟨fun o ho => ?_, by rw [← vm]; exact tf, (vk.trans tk).mono (by simp)⟩
  rw [tb o ho, ea _ (by omega), ← Mem.readW_byte _ _ (Nat.mod_lt _ (by decide)), Offset.add_add,
    show 4 * (o / 4) + o % 4 = o by omega]

/-- What the copy assumes: the table at `T`, holding the initial schedule's
image, readable and apart from the schedule at `K`, which is writable. -/
structure CopyEnv (T K : BitVec 32) (u₀ : State) : Prop where
  fitT : T.toNat + 4168 ≤ 2 ^ 32
  fitK : K.toNat + 4168 ≤ 2 ^ 32
  table : ∀ o < 4168, u₀.mem (State.addr T + BitVec.ofNat 64 o) = initByte o
  rdT : InRegions (u₀.rd ++ u₀.wr) (State.addr T) 4168
  wrK : InRegions u₀.wr (State.addr K) 4168
  sep : Region.Disjoint ⟨State.addr T, 4168⟩ ⟨State.addr K, 4168⟩

/-- The registers the copy changes. -/
def copyKeep : List Reg := copyRegs ++ [.r9, .r11, .r12]

/-- After `n` steps of seven words, from `u₀`. -/
structure CopyInv (T K : BitVec 32) (u₀ : State) (n : Nat) (t : State) : Prop where
  le : n ≤ 148
  r9 : t.gpr .r9 = T + BitVec.ofNat 32 (28 * n)
  r11 : t.gpr .r11 = K + BitVec.ofNat 32 (28 * n)
  r12 : t.gpr .r12 = BitVec.ofNat 32 (148 - n)
  keep : Keep copyKeep u₀ t
  bytes : ∀ o < 28 * n, t.mem (State.addr K + BitVec.ofNat 64 o) = initByte o
  frame : Frame [⟨State.addr K, 4168⟩] u₀.mem t.mem

/-- The copy's result. -/
structure InitInv (u₀ : State) (K : BitVec 32) (t : State) : Prop where
  bytes : ∀ o < 4168, t.mem (State.addr K + BitVec.ofNat 64 o) = initByte o
  frame : Frame [⟨State.addr K, 4168⟩] u₀.mem t.mem
  keep : Keep copyKeep u₀ t

/-- `copyWords k` at step `n` of the copy: the table's bytes from offset
`28 n` to the schedule. -/
theorem copyAt_run {T K : BitVec 32} {u₀ : State} (E : CopyEnv T K u₀) {n k : Nat} (hk : k ≤ 7)
    (hnk : 28 * n + 4 * k ≤ 4168) {t : State} (I : CopyInv T K u₀ n t) :
    WP isa (.block (copyWords k)) t fun t' =>
      (∀ o < 28 * n + 4 * k, t'.mem (State.addr K + BitVec.ofNat 64 o) = initByte o) ∧
      Frame [⟨State.addr K, 4168⟩] u₀.mem t'.mem ∧ Keep copyRegs t t' := by
  have fT := E.fitT
  have fK := E.fitK
  have eT : State.addr (T + BitVec.ofNat 32 (28 * n)) = State.addr T + BitVec.ofNat 64 (28 * n) :=
    addr_add (by omega)
  have eK : State.addr (K + BitVec.ofNat 32 (28 * n)) = State.addr K + BitVec.ofNat 64 (28 * n) :=
    addr_add (by omega)
  have fS : (T + BitVec.ofNat 32 (28 * n)).toNat + 4 * k ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 28 * n) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  have fD : (K + BitVec.ofNat 32 (28 * n)).toNat + 4 * k ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 28 * n) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  refine WP.mono (copyWords_run t hk I.r9 I.r11 fS fD
    (by rw [eT, keep_reads I.keep]; exact inRegions_off E.rdT (by omega))
    (by rw [eK, I.keep.2.2.1]; exact inRegions_off E.wrK (by omega)))
    fun t' ⟨tb, tf, tk⟩ => ⟨fun o ho => ?_, I.frame.trans (tf.sub fun r hr => ?_), tk⟩
  · by_cases hl : o < 28 * n
    · rw [← I.bytes o hl]
      refine tf _ fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      rw [eK]
      exact fun h => (Offset.disjoint _ (d := o) (n := 1) (e := 28 * n) (k := 4 * k) (by omega) (by omega)
        (by omega)) _ (Region.contains_self _ _) h
    · rw [show o = 28 * n + (o - 28 * n) by omega, ← Offset.add_add, ← eK, tb _ (by omega), eT,
        Offset.add_add, ← E.table _ (by omega)]
      refine I.frame _ fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact E.sep _ (Offset.contains_base _ (by omega) (by omega))
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, by rw [eK]; exact Offset.sub_base _ (by omega)⟩

/-- One step of seven words. -/
theorem copyStep_run {T K : BitVec 32} {u₀ : State} (E : CopyEnv T K u₀) {n : Nat} (hn : n < 148) {t : State}
    (I : CopyInv T K u₀ n t) :
    WP isa (.block copyStep) t fun t' =>
      CopyInv T K u₀ (n + 1) t' ∧ t'.z = (BitVec.ofNat 32 (148 - (n + 1)) == 0#32) := by
  unfold copyStep
  rw [WP.block_append_iff]
  refine WP.mono (copyAt_run E (k := 7) (by decide) (by omega) I) fun v ⟨vb, vf, vk⟩ => ?_
  have v9 : v.gpr .r9 = T + BitVec.ofNat 32 (28 * n) := by rw [vk.gpr (by decide), I.r9]
  have v11 : v.gpr .r11 = K + BitVec.ofNat 32 (28 * n) := by rw [vk.gpr (by decide), I.r11]
  have v12 : v.gpr .r12 = BitVec.ofNat 32 (148 - n) := by rw [vk.gpr (by decide), I.r12]
  have h12 : BitVec.ofNat 32 (148 - n) - 1#32 = BitVec.ofNat 32 (148 - (n + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine WP.mono (WP.keep [.r9, .r11, .r12] (Q := fun t' => t'.gpr .r9 = T + BitVec.ofNat 32 (28 * (n + 1)) ∧
      t'.gpr .r11 = K + BitVec.ofNat 32 (28 * (n + 1)) ∧ t'.gpr .r12 = BitVec.ofNat 32 (148 - (n + 1)) ∧
      t'.z = (BitVec.ofNat 32 (148 - (n + 1)) == 0#32) ∧ t'.mem = v.mem)
    (by brun [v9, v11, v12, ofs_add, h12]; refine ⟨?_, ?_⟩ <;> congr 2) (by decide))
    fun t' ⟨⟨a9, a11, a12, az, am⟩, ak⟩ => ⟨⟨by omega, a9, a11, a12, (I.keep.trans (vk.trans ak)).mono
      (by decide), fun o ho => by rw [am]; exact vb o (by omega), by rw [am]; exact vf⟩, az⟩

theorem initSchedule_run (u₀ : State) {K : BitVec 32} (h2 : u₀.gpr .r2 = K)
    (E : CopyEnv (u₀.syms initSym) K u₀) : WP isa initSchedule u₀ (InitInv u₀ K) := by
  unfold initSchedule
  apply WP.seq
  refine WP.mono (WP.keep [.r9, .r11, .r12] (Q := fun t => t.gpr .r9 = u₀.syms initSym ∧
      t.gpr .r11 = K + BitVec.ofNat 32 0 ∧ t.gpr .r12 = BitVec.ofNat 32 148 ∧ t.mem = u₀.mem)
    (by brun [h2, syms_setReg]) (by decide)) fun u₁ ⟨⟨a9, a11, a12, am⟩, ak⟩ => ?_
  have I0 : CopyInv (u₀.syms initSym) K u₀ 0 u₁ :=
    ⟨by decide, by rw [a9, Nat.mul_zero, BitVec.add_zero], by rw [a11], by rw [a12], ak.mono (by decide),
      fun o ho => absurd ho (by omega), by rw [am]; exact Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (WP.loop (M := isa) (Q := CopyInv (u₀.syms initSym) K u₀ 148)
    (fun (m : Nat) (v : State) => ∃ n, n < 148 ∧ m = 148 - n ∧ CopyInv (u₀.syms initSym) K u₀ n v) ?_ 148 u₁
    ⟨0, by decide, rfl, I0⟩) fun v J => ?_
  · intro m v ⟨n, hn, hm, J⟩
    refine WP.mono (copyStep_run E hn J) fun v' ⟨J', hz⟩ => ?_
    rw [eval_ne, hz]
    by_cases e : n + 1 = 148
    · left
      exact ⟨by rw [e]; rfl, e ▸ J'⟩
    · right
      have nz : BitVec.ofNat 32 (148 - (n + 1)) ≠ 0#32 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
      exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega, n + 1, by omega, rfl, J'⟩
  · refine WP.mono (copyAt_run E (k := 6) (by decide) (by decide) J) fun t ⟨tb, tf, tk⟩ =>
      ⟨fun o ho => tb o (by omega), tf, (J.keep.trans tk).mono (by decide)⟩

end VG.Proof.Blowfish.Arm
