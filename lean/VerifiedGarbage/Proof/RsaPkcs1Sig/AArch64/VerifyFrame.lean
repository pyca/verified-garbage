import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyPre
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp

/-!
# `vg_rsa_pkcs1_verify` on AArch64: the frame and the call's arguments

The frame of `frameBytes` bytes at `fb s = sp - frameBytes`, below which the
callee uses `K` bytes: all of it is the stack the function uses, `kR K s`,
from `kb K s`. `pubArgs_ok`: the first block saves the registers, keeps the
values needed after the call, and sets up the call (`AtCall`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Ver

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Verify
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp wp_mov wp_movw)

/-! ## Addresses -/

/-- The frame's base. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The base of the stack the function uses. -/
abbrev kb (K : Nat) (s : State) : Addr := s.sp - BitVec.ofNat 64 (stk K)

theorem fb_eq (K : Nat) (s : State) : fb s = kb K s + BitVec.ofNat 64 K := by
  unfold fb kb
  rw [Offset.sub_ofNat_eq s.sp (show frameBytes ≤ stk K by unfold stk; omega)]
  rw [show stk K - frameBytes = K by unfold stk; omega]

theorem off_fb (K : Nat) (s : State) (d : Nat) :
    fb s + BitVec.ofNat 64 d = kb K s + BitVec.ofNat 64 (K + d) := by
  rw [fb_eq K, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem kb_toNat {K : Nat} {s : State} (hp : PreV K s) :
    (kb K s).toNat + stk K = s.sp.toNat ∧ s.sp.toNat + 24 ≤ 2 ^ 64 := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]
  constructor <;> omega

theorem fb_toNat {K : Nat} {s : State} (hp : PreV K s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stk at this; omega

/-- A region of the frame is in the stack the function uses. -/
theorem frame_sub (K : Nat) (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR K s) := by
  rw [off_fb K]; exact Offset.sub_base _ (by unfold stk; omega)

theorem frame_sub0 (K : Nat) (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (kR K s) := by
  have := frame_sub K s (d := 0) (n := frameBytes) (by omega)
  rwa [BitVec.add_zero] at this

/-- The stack below the frame, which the callee uses. -/
theorem below_fb (K : Nat) (s : State) : below (fb s) K = ⟨kb K s, K⟩ := by
  simp only [below, fb_eq K, BitVec.add_sub_cancel]

theorem below_sub (K : Nat) (s : State) : Region.Sub (below (fb s) K) (kR K s) := by
  rw [below_fb]; exact Region.sub_prefix (by unfold stk; omega)

/-- The stack arguments, from the frame. -/
theorem stackArgAddr_fb (s : State) (j : Nat) :
    stackArgAddr s j = fb s + BitVec.ofNat 64 (frameBytes + 8 * j) := by
  rw [stackArgAddr, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- Regions the frame's stores keep: those disjoint from the stack used. -/
theorem keep_of_frame {K : Nat} {s : State} {R : Region} (hR : (kR K s).Disjoint R) : ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region)], R.Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (hR.sub_left (frame_sub0 K s)).symm

/-! ## The block before the call -/

/-- At the call: the registers saved in their slots, `k`, `hash`, `digest`
and `digest_len` kept in `x19`–`x22`, and the arguments of
`vg_rsa_public_checked` set up. -/
structure AtCall (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x0 : t.gpr .x0 = fb s + BitVec.ofNat 64 oEM1
  x1 : t.gpr .x1 = s.gpr .x1
  x2 : t.gpr .x2 = s.gpr .x0
  x3 : t.gpr .x3 = s.gpr .x1
  x4 : t.gpr .x4 = s.gpr .x2
  x5 : t.gpr .x5 = s.gpr .x3
  x6 : t.gpr .x6 = s.gpr .x7
  x7 : t.gpr .x7 = s.gpr .x1
  x19 : t.gpr .x19 = s.gpr .x1
  x20 : t.gpr .x20 = ((s.gpr .x4).setWidth 32).setWidth 64
  x21 : t.gpr .x21 = s.gpr .x5
  x22 : t.gpr .x22 = s.gpr .x6
  hi : ∀ r ∈ [Reg.x23, .x24, .x25, .x26, .x27, .x28], t.gpr r = s.gpr r
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  a0 : stackArg t 0 = stackArg s 1
  a1 : stackArg t 1 = stackArg s 2

theorem saved_offs : ∀ p ∈ saved, 16 ≤ p.2 ∧ p.2 + 8 ≤ 16 + 40 := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

/-- Slots holding the values of `g` hold those of `g'` if they agree on the
saved registers. -/
theorem Saved.congr {B : Addr} {g g' : Reg → BitVec 64} {l : List (Reg × Nat)} {m : Mem}
    (h : Spill.Saved B g l m) (e : ∀ p ∈ l, g p.1 = g' p.1) : Spill.Saved B g' l m :=
  fun p hp => (h p hp).trans (e p hp)

/-- A word of the frame written, apart from the slots, keeps them. -/
theorem Saved.write {s : State} {g : Reg → BitVec 64} {m : Mem} (h : Spill.Saved (fb s) g saved m)
    {d : Nat} (hd : d + 8 ≤ 16) (v : BitVec 64) :
    Spill.Saved (fb s) g saved (m.writeW (fb s + BitVec.ofNat 64 d) v) :=
  h.frame_in saved_offs (Frame.writeW (Frame.refl [⟨fb s + BitVec.ofNat 64 d, 8⟩] m) (List.mem_singleton_self _) v
    (Region.contains_self _ _)) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem wr_frame {s t : State} (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) {d n : Nat}
    (h : d + n ≤ frameBytes) : InRegions t.wr (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, by rw [hwr]; exact List.mem_cons_self .., Offset.contains_base _ h (by unfold frameBytes at h; omega)⟩

theorem in_frame (s : State) (rs : List Region) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (⟨fb s, frameBytes⟩ :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by unfold frameBytes at h; omega)⟩

theorem contains_fb (s : State) {n : Nat} (h : n ≤ frameBytes) :
    (⟨fb s, frameBytes⟩ : Region).Contains (fb s) n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem in_frame0 (s : State) (rs : List Region) {n : Nat} (h : n ≤ frameBytes) :
    InRegions (⟨fb s, frameBytes⟩ :: rs) (fb s) n := by
  simpa using in_frame s rs (d := 0) (by omega)

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

/-- The stack arguments are readable. -/
theorem arg_in {K : Nat} {s : State} (hp : PreV K s) {rs : List Region} (hrd : Covers s.rd rs) {j : Nat}
    (hj : j < 3) : InRegions rs (stackArgAddr s j) 8 :=
  hrd _ _ ⟨aR s, by rw [hp.hrd]; simp, by
    rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frame {K : Nat} {s : State} (hp : PreV K s) {m : Mem} (h : Frame [⟨fb s, frameBytes⟩] s.mem m)
    {j : Nat} (hj : j < 3) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := aR s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega))
    (keep_of_frame hp.ka) (by decide)

theorem pubArgs_ok {K : Nat} {s u : State} (hp : PreV K s) (hsp : u.sp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : u.mem = s.mem) (hg : ∀ r, r ≠ .x8 → u.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block pubArgs) u (AtCall s) := by
  unfold pubArgs save
  simp only [List.cons_append, List.append_assoc]
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  have hin : ∀ p ∈ saved, InRegions u₁.wr (u₁.gpr .x16 + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [e₁, o₁.wr]; exact wr_frame hwr (by have := saved_offs p hp'; unfold frameBytes; omega)
  refine Spill.save_ok (b := .x16) (l := saved) saved_ho hin ?_
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : State, u₂ = { u₁ with mem := Spill.saveMem u₁.mem (u₁.gpr .x16) u₁.gpr saved } :=
    ⟨_, rfl⟩
  rw [← hu₂]
  have m₂ : Frame [⟨fb s, frameBytes⟩] s.mem u₂.mem := by
    rw [hu₂, e₁, o₁.mem, hm]
    exact Spill.saveMem_frame_base (fun p hp' => by have := saved_offs p hp'; unfold frameBytes; omega)
      (by decide) _ _ _
  have sv₂ : Spill.Saved (fb s) s.gpr saved u₂.mem := by
    rw [hu₂, e₁]
    refine Saved.congr (Spill.saveMem_saved (by decide) _ _ _) fun p hp' => ?_
    have : p.1 ≠ .x16 ∧ p.1 ≠ .x8 := by revert p; decide
    rw [o₁.get p.1 (by simpa using this.1), hg _ this.2]
  simp only [List.nil_append, copyArg, List.cons_append]
  refine wp_mov fun u₃ o₃ e₃ => wp_movw fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ => wp_mov fun u₆ o₆ e₆ => ?_
  have O₆ : Only [.x19, .x20, .x21, .x22] u₂ u₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  have sp₆ : u₆.sp = fb s := by rw [O₆.sp, hu₂]; show u₁.sp = _; rw [o₁.sp, hsp]
  have rd₆ : u₆.rd = s.rd := by rw [O₆.rd, hu₂]; show u₁.rd = _; rw [o₁.rd, hrd]
  have wr₆ : u₆.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [O₆.wr, hu₂]; show u₁.wr = _; rw [o₁.wr, hwr]
  have a₁ : u₆.sp + BitVec.ofNat 64 (frameBytes + 8 * 1) = stackArgAddr s 1 := by rw [sp₆, stackArgAddr_fb]
  have in₁ : InRegions (u₆.rd ++ u₆.wr) (stackArgAddr s 1) 8 := by
    rw [rd₆]; exact arg_in hp (Covers.left (Covers.refl _)) (by decide)
  refine wp_ldrSp (by decide) (by rw [a₁]; exact in₁) fun u₇ o₇ e₇ => ?_
  rw [a₁, O₆.mem, arg_frame hp m₂ (by decide)] at e₇
  have g₂ : ∀ r, u₂.gpr r = u₁.gpr r := fun r => by rw [hu₂]
  have x16₇ : u₇.gpr .x16 = fb s := by rw [o₇.get .x16, O₆.get .x16, g₂, e₁]
  refine wp_strx (by decide) (by rw [x16₇, BitVec.add_zero]) (by rw [o₇.wr, wr₆]; exact in_frame0 _ _ (by decide))
    fun u₈ m₈ => ?_
  have m₈' : Frame [⟨fb s, frameBytes⟩] s.mem u₈.mem := by
    rw [m₈.mem, o₇.mem, O₆.mem]
    exact m₂.writeW (List.mem_singleton_self _) _ (contains_fb s (by decide))
  have a₂ : u₈.sp + BitVec.ofNat 64 (frameBytes + 8 * 2) = stackArgAddr s 2 := by
    rw [m₈.sp, o₇.sp, sp₆, stackArgAddr_fb]
  have in₂ : InRegions (u₈.rd ++ u₈.wr) (stackArgAddr s 2) 8 := by
    rw [m₈.rd, o₇.rd, rd₆]; exact arg_in hp (Covers.left (Covers.refl _)) (by decide)
  refine wp_ldrSp (by decide) (by rw [a₂]; exact in₂) fun u₉ o₉ e₉ => ?_
  rw [a₂, arg_frame hp m₈' (by decide)] at e₉
  have x16₉ : u₉.gpr .x16 = fb s := by rw [o₉.get .x16, m₈.gpr, x16₇]
  refine wp_strx (by decide) (by rw [x16₉]) (by rw [o₉.wr, m₈.wr, o₇.wr, wr₆]; exact in_frame _ _ (by decide))
    fun u₁₀ m₁₀ => ?_
  refine wp_mov fun u₁₁ o₁₁ e₁₁ => wp_mov fun u₁₂ o₁₂ e₁₂ => wp_mov fun u₁₃ o₁₃ e₁₃ =>
    wp_mov fun u₁₄ o₁₄ e₁₄ => wp_mov fun u₁₅ o₁₅ e₁₅ => wp_mov fun u₁₆ o₁₆ e₁₆ =>
    wp_addSp (by decide) fun u₁₇ o₁₇ e₁₇ => wp_nil ?_
  have h₁₀ : ∀ r, r ∉ [Reg.x8, .x16, .x19, .x20, .x21, .x22] → u₁₀.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [m₁₀.gpr, o₉.gpr r (by simpa using hr.1), m₈.gpr, o₇.gpr r (by simpa using hr.1),
      O₆.gpr r (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]), g₂, o₁.gpr r (by simpa using hr.2.1),
      hg r hr.1]
  have hO : Only [.x4, .x5, .x2, .x3, .x6, .x7, .x0] u₁₀ u₁₇ :=
    (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans o₁₇)))))).mono
  have k₁₉ : ∀ r ∈ [Reg.x19, .x20, .x21, .x22], u₁₇.gpr r = u₆.gpr r := by
    intro r hr
    have : r ∉ [Reg.x4, .x5, .x2, .x3, .x6, .x7, .x0] ∧ r ≠ .x8 := by revert r; decide
    rw [hO.gpr r this.1, m₁₀.gpr, o₉.gpr r (by simpa using this.2), m₈.gpr, o₇.gpr r (by simpa using this.2)]
  have sp₁₀ : u₁₀.sp = fb s := by rw [m₁₀.sp, o₉.sp, m₈.sp, o₇.sp, sp₆]
  have u₁₆sp : u₁₆.sp = fb s := by
    rw [o₁₆.sp, o₁₅.sp, o₁₄.sp, o₁₃.sp, o₁₂.sp, o₁₁.sp, sp₁₀]
  have mem₁₀ : u₁₀.mem = (u₈.mem).writeW (fb s + BitVec.ofNat 64 8) (stackArg s 2) := by
    rw [m₁₀.mem, o₉.mem, e₉]
  have mem₈ : u₈.mem = (u₂.mem).writeW (fb s) (stackArg s 1) := by
    rw [m₈.mem, o₇.mem, O₆.mem, e₇]
  have g₂' : ∀ r, u₂.gpr r = u.gpr r ∨ r = .x16 := fun r => by
    by_cases h : r = .x16
    · exact .inr h
    · exact .inl (by rw [g₂, o₁.gpr r (by simpa using h)])
  refine ⟨?sp, ?rd, ?wr, ?x0, ?x1, ?x2, ?x3, ?x4, ?x5, ?x6, ?x7, ?x19, ?x20, ?x21, ?x22, ?hi, ?v, ?mem, ?sv, ?a0,
    ?a1⟩
  case sp => rw [o₁₇.sp, u₁₆sp]
  case rd => rw [hO.rd, m₁₀.rd, o₉.rd, m₈.rd, o₇.rd, rd₆]
  case wr => rw [hO.wr, m₁₀.wr, o₉.wr, m₈.wr, o₇.wr, wr₆]
  case x0 => rw [e₁₇, u₁₆sp]
  case x1 => rw [hO.get .x1, h₁₀ .x1 (by decide)]
  case x2 => rw [o₁₇.get .x2, o₁₆.get .x2, o₁₅.get .x2, o₁₄.get .x2, e₁₃, o₁₂.get .x0, o₁₁.get .x0,
    h₁₀ .x0 (by decide)]
  case x3 => rw [o₁₇.get .x3, o₁₆.get .x3, o₁₅.get .x3, e₁₄, o₁₃.get .x1, o₁₂.get .x1, o₁₁.get .x1,
    h₁₀ .x1 (by decide)]
  case x4 => rw [o₁₇.get .x4, o₁₆.get .x4, o₁₅.get .x4, o₁₄.get .x4, o₁₃.get .x4, o₁₂.get .x4, e₁₁,
    h₁₀ .x2 (by decide)]
  case x5 => rw [o₁₇.get .x5, o₁₆.get .x5, o₁₅.get .x5, o₁₄.get .x5, o₁₃.get .x5, e₁₂, o₁₁.get .x3,
    h₁₀ .x3 (by decide)]
  case x6 => rw [o₁₇.get .x6, o₁₆.get .x6, e₁₅, o₁₄.get .x7, o₁₃.get .x7, o₁₂.get .x7, o₁₁.get .x7,
    h₁₀ .x7 (by decide)]
  case x7 => rw [o₁₇.get .x7, e₁₆, o₁₅.get .x1, o₁₄.get .x1, o₁₃.get .x1, o₁₂.get .x1, o₁₁.get .x1,
    h₁₀ .x1 (by decide)]
  case x19 => rw [k₁₉ .x19 (by decide), o₆.get .x19, o₅.get .x19, o₄.get .x19, e₃, g₂, o₁.get .x1,
    hg .x1 (by decide)]
  case x20 => rw [k₁₉ .x20 (by decide), o₆.get .x20, o₅.get .x20, e₄, o₃.get .x4, g₂, o₁.get .x4,
    hg .x4 (by decide)]
  case x21 => rw [k₁₉ .x21 (by decide), o₆.get .x21, e₅, o₄.get .x5, o₃.get .x5, g₂, o₁.get .x5,
    hg .x5 (by decide)]
  case x22 => rw [k₁₉ .x22 (by decide), e₆, o₅.get .x6, o₄.get .x6, o₃.get .x6, g₂, o₁.get .x6,
    hg .x6 (by decide)]
  case hi =>
    intro r hr
    have : r ∉ [Reg.x4, .x5, .x2, .x3, .x6, .x7, .x0] ∧ r ∉ [Reg.x8, .x16, .x19, .x20, .x21, .x22] := by
      revert r; decide
    rw [hO.gpr r this.1, h₁₀ r this.2]
  case v =>
    intro r hr
    rw [hO.vcs r hr, m₁₀.vcs r hr, o₉.vcs r hr, m₈.vcs r hr, o₇.vcs r hr, O₆.vcs r hr, hu₂]
    show (u₁.v r).extractLsb' 0 64 = _
    rw [o₁.vcs r hr, hv r hr]
  case mem =>
    rw [hO.mem, mem₁₀]
    exact m₈'.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  case sv =>
    rw [hO.mem, mem₁₀, mem₈]
    exact Saved.write (d := 8) (Saved.write (d := 0) (by simpa using sv₂) (by decide) _ |> fun h => by
      simpa using h) (by decide) _
  case a0 =>
    show (u₁₇.mem).readW (u₁₇.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
    rw [o₁₇.sp, u₁₆sp, hO.mem, mem₁₀]
    simp only [Nat.mul_zero, BitVec.add_zero]
    rw [Mem.readW_writeW_sep (Offset.sep_base (fb s) (by decide) (by decide)) (by decide), mem₈]
    exact Mem.readW_writeW_self64 _ _ _
  case a1 =>
    show (u₁₇.mem).readW (u₁₇.sp + BitVec.ofNat 64 (8 * 1)) 64 = _
    rw [o₁₇.sp, u₁₆sp, hO.mem, mem₁₀]
    exact Mem.readW_writeW_self64 _ _ _

end VG.Proof.RsaPkcs1Sig.AArch64.Ver
