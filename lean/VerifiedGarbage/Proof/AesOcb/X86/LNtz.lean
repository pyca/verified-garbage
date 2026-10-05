import VerifiedGarbage.Proof.AesOcb.X86.Blk

/-!
# AES-OCB on x86: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `edi`), shifted right
once more each time (at `W + kO`), is even: `ntz(i)` times (`lNtz_ok`). The
invariant: after `j` doublings, `W + lO` holds `L_j`, `W + kO` holds
`i / 2^j`, which is positive, and `ntz(i) = j + ntz(i / 2^j)`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq toNat_ofNat32 runBlock_app_of)

theorem even_zf32 {v : Nat} (hv : v < 2 ^ 32) :
    (BitVec.ofNat 32 v &&& 1#32 == 0) = decide (v % 2 = 0) := by
  have : BitVec.ofNat 32 v &&& 1#32 = BitVec.ofNat 32 (v % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, toNat_ofNat32 hv, toNat_ofNat32 (by decide), Nat.and_one_is_mod,
      toNat_ofNat32 (by omega)]
  rw [this]
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> rw [h] <;> decide

theorem shr1_32 {v : Nat} (hv : v < 2 ^ 32) : BitVec.ofNat 32 v >>> 1 = BitVec.ofNat 32 (v / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat32 hv, toNat_ofNat32 (by omega), Nat.shiftRight_eq_div_pow]

/-- The regions `lNtz` writes. -/
abbrev lNtzR (p : Prm) : List Region := [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩]

theorem inMut_lNtzR (p : Prm) : InMut p (lNtzR p) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))

/-- What `lNtz` leaves. -/
structure LNtzPost (p : Prm) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame (lNtzR p) s.mem s'.mem
  val : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 lO) = lAt l (ntz i)
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem LNtzPost.env {p : Prm} (L : Lay p) {l : Block} {i : Nat} {s s' : State} (E : Env p s)
    (h : LNtzPost p l i s s') : Env p s' :=
  E.mut L (by rw [h.gpr _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [h.gpr _ (by decide) (by decide) (by decide), E.esp]) h.rd h.wr (frame_toMut h.frame (inMut_lNtzR p))

/-- What a step leaves: `W + lO` written as `h` says, then `W + kO`. -/
theorem lNtz_frame {p : Prm} {m m' : Mem} (h : Frame [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩] m m')
    (v : BitVec 32) : Frame (lNtzR p) m (m'.writeW (w64 p.W + BitVec.ofNat 64 kO) v) :=
  (h.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).writeW (r := ⟨_, 4⟩)
    (by simp) v (Region.contains_self _ _)

theorem lO_kO (p : Prm) : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩ : Region)],
    (⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩ : Region).Disjoint r := by
  simp only [List.mem_singleton, forall_eq]
  exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem block_writeK (p : Prm) (m : Mem) (v : BitVec 32) :
    blockAtMem (m.writeW (w64 p.W + BitVec.ofNat 64 kO) v) (w64 p.W + BitVec.ofNat 64 lO) =
      blockAtMem m (w64 p.W + BitVec.ofNat 64 lO) :=
  Proof.Ocb.blockAtMem_frame ((Frame.refl _ m).writeW (List.mem_singleton_self _) v (Region.contains_self _ _))
    (lO_kO p)

theorem readK_dbl (p : Prm) (m : Mem) :
    (dblMem m (w64 p.W) lO (w64 p.W) lO).readW (w64 p.W + BitVec.ofNat 64 kO) 32 =
      m.readW (w64 p.W + BitVec.ofNat 64 kO) 32 :=
  (dblMem_frame m _ lO _ lO).readW (Region.contains_self _ _) (by
    simp only [List.mem_singleton, forall_eq]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by decide)

/-- One step of `lNtz`'s loop: `W + lO` doubled, `W + kO` halved, and ZF set
if what is left is even. -/
theorem lNtzStep_ok {p : Prm} (L : Lay p) {t : State} (Et : Env p t) {k : Nat} (hk : k < 2 ^ 32)
    (kt : slotv t.mem p.W kO = BitVec.ofNat 32 k) :
    ∃ t₂, runBlock isa (dbl .ebp lO lO ++ [.mov .eax (slot kO), .shift .shr .eax 1, .store (at_ .ebp kO) .eax,
        .alu .test .eax (imm 1)]) t = some t₂ ∧
      Frame (lNtzR p) t.mem t₂.mem ∧
      blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 lO) = double (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 lO)) ∧
      slotv t₂.mem p.W kO = BitVec.ofNat 32 (k / 2) ∧ t₂.zf = some (decide (k / 2 % 2 = 0)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₂.gpr r = t.gpr r) ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr := by
  obtain ⟨t₁, runt₁, m₁', g₁', rd₁', wr₁'⟩ := dblW_ok L Et (s := lO) (d := lO) (by decide) (by decide) (.inl rfl)
  have Et₁ : Env p t₁ := Et.mut L (by rw [g₁' _ (by decide) (by decide) (by decide), Et.ebp])
    (by rw [g₁' _ (by decide) (by decide) (by decide), Et.esp]) rd₁' wr₁'
    (frame_toMut (by rw [m₁']; exact dblMem_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  have kt₁ : t₁.mem.readW (w64 p.W + BitVec.ofNat 64 kO) 32 = BitVec.ofNat 32 k := by
    rw [m₁', readK_dbl, ← slotv_eq, kt]
  obtain ⟨t₂, runt₂, m₂', zf₂', g₂'', rd₂', wr₂'⟩ : ∃ t₂,
      runBlock isa [.mov .eax (slot kO), .shift .shr .eax 1, .store (at_ .ebp kO) .eax,
        .alu .test .eax (imm 1)] t₁ = some t₂ ∧
      t₂.mem = t₁.mem.writeW (w64 p.W + BitVec.ofNat 64 kO) (BitVec.ofNat 32 (k / 2)) ∧
      t₂.zf = some (decide (k / 2 % 2 = 0)) ∧
      (∀ r, r ≠ .eax → t₂.gpr r = t₁.gpr r) ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    refine ⟨_, by grun [Et₁.ebp, kt₁, L.aW, Et₁.perm.wR, Et₁.perm.wW], by gmems [kt₁, shr1_32 hk], ?_,
      fun r h => by gregs [h], by gmems [], by gmems []⟩
    gmems [kt₁, shr1_32 hk, even_zf32 (show k / 2 < 2 ^ 32 by omega)]
  refine ⟨t₂, runBlock_app_of runt₁ runt₂, ?_, ?_, ?_, zf₂', fun r h1 h2 h3 => by rw [g₂'' r h1, g₁' r h1 h2 h3],
    by rw [rd₂', rd₁'], by rw [wr₂', wr₁']⟩
  · rw [m₂', m₁']; exact lNtz_frame (dblMem_frame _ _ _ _ _) _
  · rw [m₂', block_writeK, m₁', dblMem_block]
  · rw [m₂']; simp only [slotv_eq]; gmems []

/-- The head of `lNtz`: `L_0` copied to `W + lO`, `i` to `W + kO`, and ZF
set if `i` is even. -/
theorem lNtzHead_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {i : Nat} (hi' : i < 2 ^ 32)
    (hdi : s.gpr .edi = BitVec.ofNat 32 i) :
    ∃ s₂, runBlock isa (copy16 l0O lO ++ [.mov .eax (.reg .edi), .store (at_ .ebp kO) .eax, .alu .test .eax (imm 1)])
        s = some s₂ ∧
      Frame (lNtzR p) s.mem s₂.mem ∧
      blockAtMem s₂.mem (w64 p.W + BitVec.ofNat 64 lO) = blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) ∧
      slotv s₂.mem p.W kO = BitVec.ofNat 32 i ∧ s₂.zf = some (decide (i % 2 = 0)) ∧
      (∀ r, r ≠ .eax → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := copy16_ok L E (s := l0O) (d := lO) (by decide) (by decide) (by decide)
  have E₁ : Env p s₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (frame_toMut (by rw [m₁]; exact copyMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  have hdi₁ : s₁.gpr .edi = BitVec.ofNat 32 i := by rw [g₁ _ (by decide), hdi]
  obtain ⟨s₂, run₂, m₂, k₂, zf₂, g₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [.mov .eax (.reg .edi), .store (at_ .ebp kO) .eax, .alu .test .eax (imm 1)] s₁ = some s₂ ∧
      s₂.mem = s₁.mem.writeW (w64 p.W + BitVec.ofNat 64 kO) (BitVec.ofNat 32 i) ∧
      slotv s₂.mem p.W kO = BitVec.ofNat 32 i ∧ s₂.zf = some (decide (i % 2 = 0)) ∧
      (∀ r, r ≠ .eax → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by grun [E₁.ebp, hdi₁, L.aW, E₁.perm.wW], by gmems [hdi₁], ?_, ?_, fun r h => by gregs [h],
      by gmems [], by gmems []⟩
    · simp only [slotv_eq]; gmems [hdi₁]
    · gmems [hdi₁, even_zf32 hi']
  refine ⟨s₂, runBlock_app_of run₁ run₂, ?_, ?_, k₂, zf₂, fun r h => by rw [g₂ r h, g₁ r h], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  · rw [m₂, m₁]; exact lNtz_frame (copyMem16_frame _ _ _ _ _) _
  · rw [m₂, block_writeK, m₁, copyMem16_block]

theorem lNtz_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {l : Block} {i : Nat} (hi : 0 < i)
    (hi' : i < 2 ^ 32) (hdi : s.gpr .edi = BitVec.ofNat 32 i)
    (hl0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (LNtzPost p l i s) := by
  obtain ⟨s₂, run₂, fr₂, v₂, k₂, zf₂, g₂, rd₂, wr₂⟩ := lNtzHead_ok L E hi' hdi
  have g₂' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₂.gpr r = s.gpr r := fun r h _ _ => g₂ r h
  rw [hl0] at v₂
  have post_of : ∀ t : State, Frame (lNtzR p) s.mem t.mem →
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 lO) = lAt l (ntz i) →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) →
      t.rd = s.rd → t.wr = s.wr → LNtzPost p l i s t := fun t fr v g rd wr => ⟨fr, v, g, rd, wr⟩
  unfold lNtz
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.ite (decide (i % 2 = 0)) (eval_e zf₂) (fun hb => ?_)
    (fun hb => WP.block_nil (post_of s₂ fr₂ ?_ g₂' rd₂ wr₂))
  rotate_left
  · rw [v₂, Proof.Ocb.ntz_odd (by simpa using hb)]
  have he : i % 2 = 0 := of_decide_eq_true hb
  refine WP.loop (M := isa) (c := .e)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ slotv t.mem p.W kO = BitVec.ofNat 32 (i / 2 ^ j) ∧
      Frame (lNtzR p) s.mem t.mem ∧ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 lO) = lAt l j ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ 0) _
    ⟨0, rfl, by simpa using hi, by simpa using he, by simp, by simpa using k₂, fr₂, v₂,
      g₂', rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, kt, fr, v, g, rd, wr⟩
  have hv : i / 2 ^ j < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  have Et : Env p t := E.mut L (by rw [g _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [g _ (by decide) (by decide) (by decide), E.esp]) rd wr (frame_toMut fr (inMut_lNtzR p))
  have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  obtain ⟨t₂, runt, frt, vt, kt', zf₂', g₂'', rd₂', wr₂'⟩ := lNtzStep_ok L Et hv kt
  rw [← e] at kt' zf₂'
  refine WP.of_runBlock ⟨t₂, runt, ?_⟩
  have fr' : Frame (lNtzR p) s.mem t₂.mem := fr.trans frt
  have v' : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by
    rw [vt, v]; rfl
  have g' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 => by rw [g₂'' r h1 h2 h3, g r h1 h2 h3]
  have hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(eval_e zf₂').trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega, j + 1, rfl,
      by rw [e]; omega, hodd, hntz', kt', fr', v', g', by rw [rd₂', rd], by rw [wr₂', wr]⟩
  · left
    refine ⟨(eval_e zf₂').trans (by simp [hodd]), post_of t₂ fr' ?_ g' (by rw [rd₂', rd])
      (by rw [wr₂', wr])⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega)]

end VG.Proof.AesOcb.X86
