import VerifiedGarbage.Proof.RsaPss.AArch64.SignChecks
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee

/-!
# RSASSA-PSS signing on AArch64: the call of `vg_rsa_private_checked`

`privArgs_ok`: after the encoding into `EM` (`Main`), the call's stack
arguments are set from the slots and the function's stack arguments, and its
registers (`AtCall`); `call_ok`: the call writes the signature of `EM` to
`out` and keeps the frame (`AfterCall`).
-/

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil wp_movz wp_add wp_addImm wp_subImm)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp wp_mov setWidth_ofNat16 PrivChecked PrivOk PrivLay privRd
  privWr privCall)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytes_apart)
open VG.Proof.RsaPss.AArch64 (off)

/-- The working space. -/
abbrev scr (s : State) : Addr := stackArg s 11

/-- What the code writes before the call: the frame, the working space, and
the stack below the frame the hash function's `init` uses. -/
abbrev wrS (s : State) : List Region := [⟨fb s, frameBytes⟩, sR s, below (fb s) 16]

theorem wrS_disj {K : Nat} {s : State} (hK : 16 ≤ K) {R : Region} (hk : (kR K s).Disjoint R)
    (hs : R.Disjoint (sR s)) : ∀ r ∈ wrS s, R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hk.sub_left (frame_sub0 K s)).symm
  · exact hs
  · exact (hk.sub_left fun a h => below_sub K s a
      (Offset.sub_below (fb s) (a := 16) (b := K) (n := 16) (m := K) hK (by omega) a h)).symm

/-- A stack argument, in memory changed only where the code writes. -/
theorem arg_frameW {D K : Nat} {s : State} (hp : PreS D K s) (hK : 16 ≤ K) {m : Mem} (h : Frame (wrS s) s.mem m)
    {j : Nat} (hj : j < 13) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := aR s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega))
    (wrS_disj hK hp.ka hp.sa.symm) (by decide)

/-- After the encoding: `EM` holds `em`. -/
structure Main (s : State) (em : List Byte) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x20 : t.gpr .x20 = scr s
  x23 : t.gpr .x23 = s.gpr .x3
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame (wrS s) s.mem t.mem
  fr : Fr s t.mem
  em : Spec.Rsa.bytesAt t.mem (off (scr s) oEm) (s.gpr .x3).toNat = em

/-- The call's stack arguments. -/
def argv (s : State) : List (BitVec 64) :=
  [s.gpr .x6, s.gpr .x7, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5,
    stackArg s 6, stackArg s 7, off (scr s) oRsa, stackArg s 12 - BitVec.ofNat 64 1024]

/-- At the call. -/
structure AtCall (s : State) (em : List Byte) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x0 : t.gpr .x0 = s.gpr .x0
  x1 : t.gpr .x1 = s.gpr .x3
  x2 : t.gpr .x2 = s.gpr .x2
  x3 : t.gpr .x3 = s.gpr .x3
  x4 : t.gpr .x4 = s.gpr .x4
  x5 : t.gpr .x5 = s.gpr .x5
  x6 : t.gpr .x6 = off (scr s) oEm
  x7 : t.gpr .x7 = s.gpr .x3
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  args : ∀ i < 12, stackArg t i = (argv s).getD i 0
  mem : Frame (wrS s) s.mem t.mem
  fr : Fr s t.mem
  em : Spec.Rsa.bytesAt t.mem (off (scr s) oEm) (s.gpr .x3).toNat = em

/-! ## The stack arguments -/

/-- After copying `n` of the function's stack arguments from `v₀`. -/
structure Copied (s v₀ : State) (n : Nat) (v : State) : Prop where
  sp : v.sp = v₀.sp
  rd : v.rd = v₀.rd
  wr : v.wr = v₀.wr
  g : ∀ r, r ≠ .x9 → v.gpr r = v₀.gpr r
  vc : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (v₀.v r).extractLsb' 0 64
  mem : Frame [⟨fb s + BitVec.ofNat 64 16, 64⟩] v₀.mem v.mem
  args : ∀ i < n, v.mem.readW (fb s + BitVec.ofNat 64 (16 + 8 * i)) 64 = stackArg s i

theorem copies_ok {D K : Nat} {s v₀ : State} (hp : PreS D K s) (hK : 16 ≤ K) (hsp : v₀.sp = fb s) (h16 : v₀.gpr .x16 = fb s)
    (hrd : v₀.rd = s.rd) (hwr : v₀.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : Frame (wrS s) s.mem v₀.mem) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun j => [arg .x9 j, .str .x .x9 .x16 (16 + 8 * j)])) v₀
      (Copied s v₀ n) := by
  intro n hn
  induction n with
  | zero =>
    exact wp_nil ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun v hv => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, arg]
    have a₁ : v.sp + BitVec.ofNat 64 (frameBytes + 8 * n) = stackArgAddr s n := by
      rw [hv.sp, hsp, stackArgAddr_fb]
    have hmv : Frame (wrS s) s.mem v.mem := hm.trans (hv.mem.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨fb s, frameBytes⟩, List.mem_cons_self, Offset.sub_base _ (by decide)⟩)
    refine wp_ldrSp (by unfold frameBytes; omega) (by
      rw [a₁, hv.rd, hrd]; exact arg_in hp (Covers.left (Covers.refl _)) (by omega)) fun v₁ o₁ e₁ => ?_
    rw [a₁, arg_frameW hp hK hmv (by omega)] at e₁
    have x16 : v₁.gpr .x16 = fb s := by rw [o₁.get .x16, hv.g .x16 (by decide), h16]
    refine wp_strx (a := fb s + BitVec.ofNat 64 (16 + 8 * n)) (by omega) (by rw [x16])
      (by rw [o₁.wr, hv.wr, hwr]; exact in_frame _ _ (by unfold frameBytes; omega)) fun v₂ m₂ => wp_nil ?_
    have mem₂ : v₂.mem = v.mem.writeW (fb s + BitVec.ofNat 64 (16 + 8 * n)) (stackArg s n) := by
      rw [m₂.mem, o₁.mem, e₁]
    refine ⟨by rw [m₂.sp, o₁.sp, hv.sp], by rw [m₂.rd, o₁.rd, hv.rd], by rw [m₂.wr, o₁.wr, hv.wr],
      fun r hr => by rw [m₂.gpr, o₁.gpr r (by simpa using hr), hv.g r hr],
      fun r hr => by rw [m₂.vcs r hr, o₁.vcs r hr, hv.vc r hr], ?_, fun i hi => ?_⟩
    · rw [mem₂]
      exact hv.mem.writeW (List.mem_singleton_self _) _ (by
        rw [show 16 + 8 * n = 16 + 8 * n from rfl, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc]
        exact Offset.contains_base _ (by omega) (by omega))
    · rw [mem₂]
      rcases (by omega : i < n ∨ i = n) with h | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hv.args i h]
      · exact Mem.readW_writeW_self64 _ _ _

theorem fr_args (s : State) : ∀ r ∈ [(⟨fb s, 96⟩ : Region)], (frA s).Disjoint r ∧ (frB s).Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨Offset.disjoint_base _ (by decide) (by decide), Offset.disjoint_base _ (by decide) (by decide)⟩

theorem privArgs_ok {D K : Nat} {s t : State} (hp : PreS D K s) (hK : 16 ≤ K) {em : List Byte}
    (hm : Main s em t) : WP isa (.block privArgs) t (AtCall s em) := by
  have hk2 := hp.k2
  unfold privArgs ld
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  have rsl : ∀ {u : State} {d : Nat}, u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      d + 8 ≤ frameBytes → InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr hd => by
    rw [hsp, hrd, hwr]; exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega)))
  have sp₁ : u₁.sp = fb s := by rw [o₁.sp, hm.sp]
  have rd₁ : u₁.rd = s.rd := by rw [o₁.rd, hm.rd]
  have wr₁ : u₁.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₁.wr, hm.wr]
  refine wp_ldrSp (by decide) (rsl sp₁ rd₁ wr₁ (by decide)) fun u₂ o₂ e₂ => ?_
  rw [sp₁, o₁.mem, hm.fr.rs (.x6, sP) (by simp [regSlots])] at e₂
  refine wp_strx (a := fb s + BitVec.ofNat 64 0) (by decide) (by rw [o₂.get .x16, e₁])
    (by rw [o₂.wr, wr₁]; exact in_frame _ _ (by decide)) fun u₃ m₃ => ?_
  have sp₃ : u₃.sp = fb s := by rw [m₃.sp, o₂.sp, sp₁]
  have rd₃ : u₃.rd = s.rd := by rw [m₃.rd, o₂.rd, rd₁]
  have wr₃ : u₃.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [m₃.wr, o₂.wr, wr₁]
  have fA₃ : Frame [(⟨fb s, 96⟩ : Region)] t.mem u₃.mem := by
    rw [m₃.mem, o₂.mem, o₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine wp_ldrSp (by decide) (rsl sp₃ rd₃ wr₃ (by decide)) fun u₄ o₄ e₄ => ?_
  rw [sp₃, (hm.fr.frame fA₃ (fun r hr => ((fr_args s) r hr).1) (fun r hr => ((fr_args s) r hr).2)).rs (.x7, sPl)
    (by simp [regSlots])] at e₄
  refine wp_strx (a := fb s + BitVec.ofNat 64 8) (by decide) (by rw [o₄.get .x16, m₃.gpr, o₂.get .x16, e₁])
    (by rw [o₄.wr, wr₃]; exact in_frame _ _ (by decide)) fun u₅ m₅ => ?_
  have frX : ∀ {m : Mem}, Frame [(⟨fb s, 96⟩ : Region)] t.mem m → Fr s m := fun h =>
    hm.fr.frame h (fun r hr => ((fr_args s) r hr).1) (fun r hr => ((fr_args s) r hr).2)
  have wX : ∀ {m : Mem}, Frame [(⟨fb s, 96⟩ : Region)] t.mem m → Frame (wrS s) s.mem m := fun h =>
    hm.mem.trans (h.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨fb s, frameBytes⟩, List.mem_cons_self, Region.sub_prefix (by decide)⟩)
  have sp₅ : u₅.sp = fb s := by rw [m₅.sp, o₄.sp, sp₃]
  have rd₅ : u₅.rd = s.rd := by rw [m₅.rd, o₄.rd, rd₃]
  have wr₅ : u₅.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [m₅.wr, o₄.wr, wr₃]
  have fA₅ : Frame [(⟨fb s, 96⟩ : Region)] t.mem u₅.mem := by
    rw [m₅.mem, o₄.mem]
    exact fA₃.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have x16₅ : u₅.gpr .x16 = fb s := by rw [m₅.gpr, o₄.get .x16, m₃.gpr, o₂.get .x16, e₁]
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok hp hK (v₀ := u₅) sp₅ x16₅ rd₅ wr₅ (wX fA₅) 8 (Nat.le_refl _)) fun v hv => ?_
  have sp₆ : v.sp = fb s := by rw [hv.sp, sp₅]
  have rd₆ : v.rd = s.rd := by rw [hv.rd, rd₅]
  have wr₆ : v.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [hv.wr, wr₅]
  have fA₆ : Frame [(⟨fb s, 96⟩ : Region)] t.mem v.mem := fA₅.trans (hv.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)
  have g₆ : ∀ r, r ≠ .x9 → r ≠ .x16 → v.gpr r = t.gpr r := fun r h₁ h₂ => by
    rw [hv.g r h₁, m₅.gpr, o₄.gpr r (by simpa using h₁), m₃.gpr, o₂.gpr r (by simpa using h₁),
      o₁.gpr r (by simpa using h₂)]
  refine wp_movz fun u₇ o₇ e₇ => wp_add fun u₈ o₈ e₈ => ?_
  have x9₈ : u₈.gpr .x9 = off (scr s) oRsa := by
    rw [e₈, o₇.get .x20, g₆ .x20 (by decide) (by decide), hm.x20, e₇, setWidth_ofNat16 (by decide)]
  refine wp_strx (a := fb s + BitVec.ofNat 64 80) (by decide)
    (by rw [o₈.get .x16, o₇.get .x16, hv.g .x16 (by decide), x16₅])
    (by rw [o₈.wr, o₇.wr, wr₆]; exact in_frame _ _ (by decide)) fun u₉ m₉ => ?_
  have fA₉ : Frame [(⟨fb s, 96⟩ : Region)] t.mem u₉.mem := by
    rw [m₉.mem, o₈.mem, o₇.mem]
    exact fA₆.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have sp₉ : u₉.sp = fb s := by rw [m₉.sp, o₈.sp, o₇.sp, sp₆]
  have rd₉ : u₉.rd = s.rd := by rw [m₉.rd, o₈.rd, o₇.rd, rd₆]
  have wr₉ : u₉.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [m₉.wr, o₈.wr, o₇.wr, wr₆]
  refine wp_ldrSp (by decide) (rsl sp₉ rd₉ wr₉ (by decide)) fun u₁₀ o₁₀ e₁₀ => ?_
  rw [sp₉, (frX fA₉).scr] at e₁₀
  refine wp_subImm (by decide) fun u₁₁ o₁₁ e₁₁ => ?_
  refine wp_strx (a := fb s + BitVec.ofNat 64 88) (by decide)
    (by rw [o₁₁.get .x16, o₁₀.get .x16, m₉.gpr, o₈.get .x16, o₇.get .x16, hv.g .x16 (by decide), x16₅])
    (by rw [o₁₁.wr, o₁₀.wr, wr₉]; exact in_frame _ _ (by decide)) fun u₁₂ m₁₂ => ?_
  have fA₁₂ : Frame [(⟨fb s, 96⟩ : Region)] t.mem u₁₂.mem := by
    rw [m₁₂.mem, o₁₁.mem, o₁₀.mem]
    exact fA₉.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have sp₁₂ : u₁₂.sp = fb s := by rw [m₁₂.sp, o₁₁.sp, o₁₀.sp, sp₉]
  have rd₁₂ : u₁₂.rd = s.rd := by rw [m₁₂.rd, o₁₁.rd, o₁₀.rd, rd₉]
  have wr₁₂ : u₁₂.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [m₁₂.wr, o₁₁.wr, o₁₀.wr, wr₉]
  have F₁₂ := frX fA₁₂
  refine wp_ldrSp (by decide) (rsl sp₁₂ rd₁₂ wr₁₂ (by decide)) fun u₁₃ o₁₃ e₁₃ => wp_mov fun u₁₄ o₁₄ e₁₄ => ?_
  rw [sp₁₂, F₁₂.rs (.x0, sOut) (by simp [regSlots])] at e₁₃
  have rd₁₄ : u₁₄.rd = s.rd := by rw [o₁₄.rd, o₁₃.rd, rd₁₂]
  have wr₁₄ : u₁₄.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₁₄.wr, o₁₃.wr, wr₁₂]
  have sp₁₄ : u₁₄.sp = fb s := by rw [o₁₄.sp, o₁₃.sp, sp₁₂]
  have mem₁₄ : u₁₄.mem = u₁₂.mem := by rw [o₁₄.mem, o₁₃.mem]
  refine wp_ldrSp (by decide) (rsl sp₁₄ rd₁₄ wr₁₄ (by decide)) fun u₁₅ o₁₅ e₁₅ => wp_mov fun u₁₆ o₁₆ e₁₆ => ?_
  rw [sp₁₄, mem₁₄, F₁₂.rs (.x2, sN) (by simp [regSlots])] at e₁₅
  have rd₁₆ : u₁₆.rd = s.rd := by rw [o₁₆.rd, o₁₅.rd, rd₁₄]
  have wr₁₆ : u₁₆.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₁₆.wr, o₁₅.wr, wr₁₄]
  have sp₁₆ : u₁₆.sp = fb s := by rw [o₁₆.sp, o₁₅.sp, sp₁₄]
  have mem₁₆ : u₁₆.mem = u₁₂.mem := by rw [o₁₆.mem, o₁₅.mem, mem₁₄]
  refine wp_ldrSp (by decide) (rsl sp₁₆ rd₁₆ wr₁₆ (by decide)) fun u₁₇ o₁₇ e₁₇ => ?_
  rw [sp₁₆, mem₁₆, F₁₂.rs (.x4, sE) (by simp [regSlots])] at e₁₇
  have rd₁₇ : u₁₇.rd = s.rd := by rw [o₁₇.rd, rd₁₆]
  have wr₁₇ : u₁₇.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₁₇.wr, wr₁₆]
  have sp₁₇ : u₁₇.sp = fb s := by rw [o₁₇.sp, sp₁₆]
  have mem₁₇ : u₁₇.mem = u₁₂.mem := by rw [o₁₇.mem, mem₁₆]
  refine wp_ldrSp (by decide) (rsl sp₁₇ rd₁₇ wr₁₇ (by decide)) fun u₁₈ o₁₈ e₁₈ => ?_
  rw [sp₁₇, mem₁₇, F₁₂.rs (.x5, sEl) (by simp [regSlots])] at e₁₈
  refine wp_addImm (by decide) fun u₁₉ o₁₉ e₁₉ => wp_mov fun u₂₀ o₂₀ e₂₀ => wp_nil ?_
  have mem₂₀ : u₂₀.mem = u₁₂.mem := by rw [o₂₀.mem, o₁₉.mem, o₁₈.mem, mem₁₇]
  have sp₂₀ : u₂₀.sp = fb s := by rw [o₂₀.sp, o₁₉.sp, o₁₈.sp, sp₁₇]
  have x23 : u₁₂.gpr .x23 = s.gpr .x3 := by
    rw [m₁₂.gpr, o₁₁.get .x23, o₁₀.get .x23, m₉.gpr, o₈.get .x23, o₇.get .x23, g₆ .x23 (by decide) (by decide),
      hm.x23]
  have x20 : u₁₂.gpr .x20 = scr s := by
    rw [m₁₂.gpr, o₁₁.get .x20, o₁₀.get .x20, m₉.gpr, o₈.get .x20, o₇.get .x20, g₆ .x20 (by decide) (by decide),
      hm.x20]
  have hm₁₂ : u₁₂.mem = (v.mem.writeW (fb s + BitVec.ofNat 64 80) (off (scr s) oRsa)).writeW
      (fb s + BitVec.ofNat 64 88) (stackArg s 12 - BitVec.ofNat 64 1024) := by
    rw [m₁₂.mem, o₁₁.mem, o₁₀.mem, m₉.mem, o₈.mem, o₇.mem, x9₈, e₁₁, e₁₀]
  have hm₅ : u₅.mem = (u₁.mem.writeW (fb s + BitVec.ofNat 64 0) (s.gpr .x6)).writeW (fb s + BitVec.ofNat 64 8)
      (s.gpr .x7) := by
    rw [m₅.mem, o₄.mem, e₄, m₃.mem, o₂.mem, e₂]
  have rv : ∀ {d : Nat}, d + 8 ≤ 80 → u₁₂.mem.readW (fb s + BitVec.ofNat 64 d) 64 = v.mem.readW (fb s + BitVec.ofNat 64 d) 64 :=
    fun hd => by
      rw [hm₁₂, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by decide)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by decide)) (by decide)]
  have r5 : ∀ {d : Nat}, d + 8 ≤ 16 → v.mem.readW (fb s + BitVec.ofNat 64 d) 64 = u₅.mem.readW (fb s + BitVec.ofNat 64 d) 64 :=
    fun hd => hv.mem.readW (r := ⟨fb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by decide)) (by decide)
  have args : ∀ i < 12, u₂₀.mem.readW (u₂₀.sp + BitVec.ofNat 64 (8 * i)) 64 = (argv s).getD i 0 := by
    intro i hi
    rw [mem₂₀, sp₂₀]
    rcases (by omega : i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i < 10) ∨ i = 10 ∨ i = 11) with rfl | rfl | h | rfl | rfl
    · rw [rv (by decide), r5 (by decide), hm₅, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide)
        (by decide)) (by decide), Mem.readW_writeW_self64]; rfl
    · rw [rv (by decide), r5 (by decide), hm₅, Mem.readW_writeW_self64]; rfl
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
      rw [show 8 * (j + 2) = 16 + 8 * j by omega, rv (by omega), hv.args j (by omega)]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rw [hm₁₂, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]; rfl
    · rw [hm₁₂, Mem.readW_writeW_self64]; rfl
  have hemR : (kR K s).Disjoint ⟨off (scr s) oEm, (s.gpr .x3).toNat⟩ :=
    hp.ks.sub_right (Offset.sub_base _ (by have := hp.hs; unfold oEm; omega))
  refine ⟨sp₂₀, by rw [o₂₀.rd, o₁₉.rd, o₁₈.rd, rd₁₇], by rw [o₂₀.wr, o₁₉.wr, o₁₈.wr, wr₁₇], ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fun r hr => ?_, args, by rw [mem₂₀]; exact wX fA₁₂, by rw [mem₂₀]; exact F₁₂, ?_⟩
  · rw [o₂₀.get .x0, o₁₉.get .x0, o₁₈.get .x0, o₁₇.get .x0, o₁₆.get .x0, o₁₅.get .x0, o₁₄.get .x0, e₁₃]
  · rw [o₂₀.get .x1, o₁₉.get .x1, o₁₈.get .x1, o₁₇.get .x1, o₁₆.get .x1, o₁₅.get .x1, e₁₄, o₁₃.get .x23, x23]
  · rw [o₂₀.get .x2, o₁₉.get .x2, o₁₈.get .x2, o₁₇.get .x2, o₁₆.get .x2, e₁₅]
  · rw [o₂₀.get .x3, o₁₉.get .x3, o₁₈.get .x3, o₁₇.get .x3, e₁₆, o₁₅.get .x23, o₁₄.get .x23, o₁₃.get .x23, x23]
  · rw [o₂₀.get .x4, o₁₉.get .x4, o₁₈.get .x4, e₁₇]
  · rw [o₂₀.get .x5, o₁₉.get .x5, e₁₈]
  · rw [o₂₀.get .x6, e₁₉, o₁₈.get .x20, o₁₇.get .x20, o₁₆.get .x20, o₁₅.get .x20, o₁₄.get .x20, o₁₃.get .x20,
      x20]
  · rw [e₂₀, o₁₉.get .x23, o₁₈.get .x23, o₁₇.get .x23, o₁₆.get .x23, o₁₅.get .x23, o₁₄.get .x23, o₁₃.get .x23,
      x23]
  · rw [o₂₀.vcs r hr, o₁₉.vcs r hr, o₁₈.vcs r hr, o₁₇.vcs r hr, o₁₆.vcs r hr, o₁₅.vcs r hr, o₁₄.vcs r hr,
      o₁₃.vcs r hr, m₁₂.vcs r hr, o₁₁.vcs r hr, o₁₀.vcs r hr, m₉.vcs r hr, o₈.vcs r hr, o₇.vcs r hr, hv.vc r hr,
      m₅.vcs r hr, o₄.vcs r hr, m₃.vcs r hr, o₂.vcs r hr, o₁.vcs r hr, hm.v r hr]
  · rw [mem₂₀, ← hm.em]
    have s96 : Region.Sub ⟨fb s, 96⟩ (kR K s) := by
      have := frame_sub K s (d := 0) (n := 96) (by decide); rwa [BitVec.add_zero] at this
    exact bytes_apart (R := ⟨off (scr s) oEm, (s.gpr .x3).toNat⟩) fA₁₂ (hemR.symm.sub_right s96)
      (by dsimp only; omega)

/-! ## The call -/

/-- `EM`, and the call's working space. -/
abbrev emR (s : State) : Region := ⟨off (scr s) oEm, (s.gpr .x3).toNat⟩
abbrev scR (s : State) : Region := ⟨off (scr s) oRsa, (stackArg s 12 - BitVec.ofNat 64 1024).toNat * 8⟩

theorem scr_toNat {D K : Nat} {s : State} (hp : PreS D K s) :
    (stackArg s 12 - BitVec.ofNat 64 1024).toNat = (stackArg s 12).toNat - 1024 := by
  have := hp.hs
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := (stackArg s 12).isLt
  omega

theorem em_sub {D K : Nat} {s : State} (hp : PreS D K s) : Region.Sub (emR s) (sR s) :=
  Offset.sub_base _ (by have := hp.hs; have := hp.k2; unfold oEm; omega)

theorem sc_sub {D K : Nat} {s : State} (hp : PreS D K s) : Region.Sub (scR s) (sR s) :=
  Offset.sub_base _ (by rw [scr_toNat hp]; have := hp.hs; unfold oRsa; omega)

theorem a96_sub (K : Nat) (s : State) : Region.Sub ⟨fb s, 96⟩ (kR K s) := by
  have := frame_sub K s (d := 0) (n := 96) (by decide); rwa [BitVec.add_zero] at this

theorem privOk_of (c : PrivChecked) {D K : Nat} {s t : State} (hp : PreS D K s) (hcK : c.stack ≤ K)
    {em : List Byte} (ha : AtCall s em t) : PrivOk c.stack t := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hcl := c.le
  have hpos := c.pos
  have hws : (scr s).toNat + (stackArg s 12).toNat * 8 ≤ 2 ^ 64 := hp.ws
  have hsc := scr_toNat hp
  have hhs := hp.hs
  have hK : Region.Sub ⟨fb s - BitVec.ofNat 64 c.stack, c.stack⟩ (kR K s) := fun a h =>
    (Offset.sub_below (fb s) (a := c.stack) (b := K) (n := c.stack) (m := K) hcK (by omega) a h) |>
      fun h' => by
        have e : fb s - BitVec.ofNat 64 K = kb K s := by rw [fb_eq K, BitVec.add_sub_cancel]
        rw [e] at h'
        exact Region.sub_prefix (by unfold stk; omega) a h'
  have a0 : stackArg t 0 = s.gpr .x6 := ha.args 0 (by decide)
  have a1 : stackArg t 1 = s.gpr .x7 := ha.args 1 (by decide)
  have a2 : stackArg t 2 = stackArg s 0 := ha.args 2 (by decide)
  have a3 : stackArg t 3 = stackArg s 1 := ha.args 3 (by decide)
  have a4 : stackArg t 4 = stackArg s 2 := ha.args 4 (by decide)
  have a5 : stackArg t 5 = stackArg s 3 := ha.args 5 (by decide)
  have a6 : stackArg t 6 = stackArg s 4 := ha.args 6 (by decide)
  have a7 : stackArg t 7 = stackArg s 5 := ha.args 7 (by decide)
  have a8 : stackArg t 8 = stackArg s 6 := ha.args 8 (by decide)
  have a9 : stackArg t 9 = stackArg s 7 := ha.args 9 (by decide)
  have a10 : stackArg t 10 = off (scr s) oRsa := ha.args 10 (by decide)
  have a11 : stackArg t 11 = stackArg s 12 - BitVec.ofNat 64 1024 := ha.args 11 (by decide)
  have ol : (s.gpr .x3).toNat = (s.gpr .x1).toNat := hp.ol.symm
  have hO : (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = oR s := by rw [ol]
  have s96 := a96_sub K s
  have hSem := em_sub hp
  have hSsc := sc_sub hp
  have hwem : (off (scr s) oEm).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEm at *; omega
  have hwsc : (off (scr s) oRsa).toNat + (stackArg s 12 - BitVec.ofNat 64 1024).toNat * 8 ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; rw [hsc]; unfold oRsa at *; omega
  refine ⟨?hl, ?hrd, ?hwr, ?hk, ?h1, ?h7, ?he1, ?he2, ?hp1, ?hp2, ?hq1, ?hq2, ?hdp, ?hqi, ?hdq, ?hs⟩
  case hl =>
    rw [ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, ha.sp, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, hO]
    exact {
      sp1 := by unfold stk at *; omega
      sp2 := by omega
      on := hp.on
      oe := hp.oe
      oi := hp.os.sub_right hSem
      op := hp.op
      oq := hp.oq
      odp := hp.odp
      odq := hp.odq
      oqi := hp.oqi
      os := hp.os.sub_right hSsc
      oa := (hp.ko.sub_left s96).symm
      ns := hp.ns.sub_right hSsc
      es := hp.es.sub_right hSsc
      is := Offset.disjoint _ (Or.inl (by unfold oEm oRsa; omega)) (by unfold oEm; omega)
        (by rw [hsc]; unfold oRsa; omega)
      ps := hp.ps.sub_right hSsc
      qs := hp.qs.sub_right hSsc
      dps := hp.dps.sub_right hSsc
      dqs := hp.dqs.sub_right hSsc
      qis := hp.qis.sub_right hSsc
      sa := ((hp.ks.sub_left s96).symm.sub_left hSsc)
      ko := hp.ko.sub_left hK
      kn := hp.kn.sub_left hK
      ke := hp.ke.sub_left hK
      ki := (hp.ks.sub_left hK).sub_right hSem
      kp := hp.kp.sub_left hK
      kq := hp.kq.sub_left hK
      kdp := hp.kdp.sub_left hK
      kdq := hp.kdq.sub_left hK
      kqi := hp.kqi.sub_left hK
      ks := (hp.ks.sub_left hK).sub_right hSsc
      ka := (Offset.base_disjoint_below (fb s) (n := c.stack) (k := 96) (by omega)).symm
      wo := hp.wo
      wn := hp.wn
      we := hp.we
      wi := hwem
      wp := hp.wp
      wq := hp.wq
      wdp := hp.wdp
      wdq := hp.wdq
      wqi := hp.wqi
      ws := hwsc }
  case hrd =>
    simp only [privRd]
    rw [ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, ha.sp, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, ha.rd, ha.wr]
    have hm : ∀ r ∈ [nR s, eR s, pR s, qR s, dpR s, dqR s, qiR s, dgR D s, slR s, aR s],
        Covers [r] (s.rd ++ (⟨fb s, frameBytes⟩ :: s.wr)) :=
      fun r hr => Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
        hp.hrd)
    refine Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp)) (Covers.cons
      (Covers.right (Covers.one ⟨sR s, List.mem_cons_of_mem _ hp.hws,
        Offset.contains_base _ (by unfold oEm; omega) (by unfold oEm; omega)⟩))
      (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp))
      (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp))
      (Covers.right (Covers.one ?_)))))))))
    simpa using in_frame s s.wr (d := 0) (n := 96) (by decide)
  case hwr =>
    simp only [privWr]
    rw [ha.x0, ha.x1, a10, a11, ha.wr, hO]
    exact Covers.cons (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ hp.hwo)
      (Covers.one ⟨sR s, List.mem_cons_of_mem _ hp.hws,
        Offset.contains_base _ (by rw [hsc]; unfold oRsa; omega) (by unfold oRsa; omega)⟩)
  case hk => rw [ha.x3]; exact ⟨hk1, hk2⟩
  case h1 => rw [ha.x1, ha.x3]
  case h7 => rw [ha.x7, ha.x3]
  case he1 => rw [ha.x5]; exact hp.e1
  case he2 => rw [ha.x5, ha.x3]; exact hp.e2
  case hp1 => rw [a1]; exact hp.p1
  case hp2 => rw [a1, ha.x3]; exact hp.p2
  case hq1 => rw [a3]; exact hp.q1
  case hq2 => rw [a3, ha.x3]; exact hp.q2
  case hdp => rw [a5, a1]; exact hp.hdp
  case hqi => rw [a9, a1]; exact hp.hqi
  case hdq => rw [a7, a3]; exact hp.hdq
  case hs => rw [a11, ha.x3, hsc]; unfold Spec.Rsa.scratchWords; omega

end VG.Proof.RsaPss.AArch64.Sgn
