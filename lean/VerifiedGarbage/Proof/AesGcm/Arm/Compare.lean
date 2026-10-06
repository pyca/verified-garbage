import VerifiedGarbage.Proof.AesGcm.Arm.Entry

/-!
# AES-GCM on ARMv7: checking a received tag

Untrusted: everything here is checked by Lean. `tagLenOk` sets `Z` iff the
tag length in `r6` is not one §5.2.1.2 allows (`tagLenOk_ok`); `recv` and
`cmp o` copy the received tag (at `tag`) and the computed one (at `W + o`),
`r6` bytes of each, padded with zeros, to `W + 256` and `W + 240` (`recv_ok`,
`cmp_ok`), and `cmpTail` sets `r0` to 1 if they are equal and 0 if not,
without a branch (`cmpTail_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le4 store4)

theorem shr31 (y : BitVec 32) : (y >>> 31).toNat = if y.msb then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  have := y.isLt
  by_cases h : 2 ^ (32 - 1) ≤ y.toNat
  · rw [decide_eq_true h]; simp only [ite_true]; simp only [Nat.reduceSub] at h; omega
  · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ite_false]; simp only [Nat.reduceSub] at h; omega

theorem msb_or_neg (x : BitVec 32) : (x ||| (0 - x)) >>> 31 = if x = 0 then 0 else 1 := by
  apply BitVec.eq_of_toNat_eq
  have z0 : (0 : BitVec 32).toNat = 0 := rfl
  rw [shr31, BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide (x := 0 - x), BitVec.toNat_sub, z0,
    Nat.add_zero]
  have := x.isLt
  by_cases h : x = 0
  · subst h; decide
  · have hx : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have : 2 ^ (32 - 1) ≤ x.toNat ∨ 2 ^ (32 - 1) ≤ (2 ^ 32 - x.toNat) % 2 ^ 32 := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp only [h, ite_false, Bool.or_eq_true, decide_eq_true_eq]
    simp only [this, ite_true]; rfl
theorem le4_inj {x y : BitVec 32} (h : le4 x = le4 y) : x = y := by
  have e : ∀ k < 4, x.extractLsb' (8 * k) 8 = y.extractLsb' (8 * k) 8 := fun k hk => by
    have := congrArg (fun l => l.getD k 0) h
    simpa only [Cmac.getD_le4 _ hk] using this
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := congrArg (fun v => v.getLsbD (j % 8)) (e (j / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 from Nat.mod_lt _ (by decide), decide_true,
    Bool.true_and] at this
  rwa [show 8 * (j / 8) + j % 8 = j by omega] at this

/-- `chk k`: `r0 := 1` if `r6 = k`. -/
theorem chk_ok (k : Nat) (hk : k < 2 ^ 32) (he : encodable (BitVec.ofNat 32 k) = true) {s : State} {tl : Nat}
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (htl : tl < 2 ^ 32) {p : Bool}
    (h0 : s.gpr .r0 = if p then 1 else 0) :
    WP isa (chk k) s fun s' => s'.gpr .r0 = (if (tl == k || p) then 1 else 0) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨s₁, run₁, hz, hg, hm, hrd, hwr, hsp⟩ := cmpk_ok s .r6 h6 htl hk he
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite _ (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have e : tl = k := by simpa using ht
    refine WP.of_runBlock ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg, e]
    · intro r hr; simp [gpr_setReg, hr, hg]
    · exact ⟨hm, hrd, hwr, hsp⟩
  · have e : tl ≠ k := by simpa using hf
    refine WP.block_nil ⟨?_, fun r _ => by rw [hg], ⟨hm, hrd, hwr, hsp⟩⟩
    rw [hg, h0]; simp [e]

theorem tagLenOk_eq (tl : Nat) :
    (tl == 16 || (tl == 15 || (tl == 14 || (tl == 13 || (tl == 12 || (tl == 8 || (tl == 4 || false))))))) =
      Spec.Gcm.tagLenOk tl := by
  simp only [Spec.Gcm.tagLenOk]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, Bool.or_false]
  omega

/-- `tagLenOk`: `Z` clear iff the tag length is allowed. -/
theorem tagLenOk_ok {s : State} {tl : Nat} (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (htl : tl < 2 ^ 32) :
    WP isa tagLenOk s fun s' => s'.z = !Spec.Gcm.tagLenOk tl ∧ (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨s₀, run₀, h0₀, hg₀, hk₀⟩ : ∃ s₀, runBlock isa [.mov .r0 (imm 0)] s = some s₀ ∧
      s₀.gpr .r0 = (if false then 1 else 0) ∧ (∀ r, r ≠ .r0 → s₀.gpr r = s.gpr r) ∧ Keeps s s₀ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  have g6 : ∀ {s' : State}, (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) → s'.gpr .r6 = BitVec.ofNat 32 tl :=
    fun hg => by rw [hg _ (by decide), h6]
  refine WP.seq (WP.mono (chk_ok 4 (by decide) (by decide) (g6 hg₀) htl h0₀) fun s₁ ⟨h0₁, hg₁, hk₁⟩ => ?_)
  have hg₁' : ∀ r, r ≠ .r0 → s₁.gpr r = s.gpr r := fun r hr => (hg₁ r hr).trans (hg₀ r hr)
  refine WP.seq (WP.mono (chk_ok 8 (by decide) (by decide) (g6 hg₁') htl h0₁) fun s₂ ⟨h0₂, hg₂, hk₂⟩ => ?_)
  have hg₂' : ∀ r, r ≠ .r0 → s₂.gpr r = s.gpr r := fun r hr => (hg₂ r hr).trans (hg₁' r hr)
  refine WP.seq (WP.mono (chk_ok 12 (by decide) (by decide) (g6 hg₂') htl h0₂) fun s₃ ⟨h0₃, hg₃, hk₃⟩ => ?_)
  have hg₃' : ∀ r, r ≠ .r0 → s₃.gpr r = s.gpr r := fun r hr => (hg₃ r hr).trans (hg₂' r hr)
  refine WP.seq (WP.mono (chk_ok 13 (by decide) (by decide) (g6 hg₃') htl h0₃) fun s₄ ⟨h0₄, hg₄, hk₄⟩ => ?_)
  have hg₄' : ∀ r, r ≠ .r0 → s₄.gpr r = s.gpr r := fun r hr => (hg₄ r hr).trans (hg₃' r hr)
  refine WP.seq (WP.mono (chk_ok 14 (by decide) (by decide) (g6 hg₄') htl h0₄) fun s₅ ⟨h0₅, hg₅, hk₅⟩ => ?_)
  have hg₅' : ∀ r, r ≠ .r0 → s₅.gpr r = s.gpr r := fun r hr => (hg₅ r hr).trans (hg₄' r hr)
  refine WP.seq (WP.mono (chk_ok 15 (by decide) (by decide) (g6 hg₅') htl h0₅) fun s₆ ⟨h0₆, hg₆, hk₆⟩ => ?_)
  have hg₆' : ∀ r, r ≠ .r0 → s₆.gpr r = s.gpr r := fun r hr => (hg₆ r hr).trans (hg₅' r hr)
  refine WP.seq (WP.mono (chk_ok 16 (by decide) (by decide) (g6 hg₆') htl h0₆) fun s₇ ⟨h0₇, hg₇, hk₇⟩ => ?_)
  have hg₇' : ∀ r, r ≠ .r0 → s₇.gpr r = s.gpr r := fun r hr => (hg₇ r hr).trans (hg₆' r hr)
  have hk : Keeps s s₇ := hk₀.trans (hk₁.trans (hk₂.trans (hk₃.trans (hk₄.trans (hk₅.trans (hk₆.trans hk₇))))))
  rw [tagLenOk_eq] at h0₇
  refine WP.of_runBlock ⟨_, by arun [], ?_, ?_, ?_⟩
  · simp only [z_subFlags, h0₇]
    cases Spec.Gcm.tagLenOk tl <;> rfl
  · intro r hr; simp only [gpr_subFlags]; exact hg₇' r hr
  · exact ⟨hk.mem, hk.rd, hk.wr, hk.sp⟩

theorem store4_zero_tail (m : Mem) (p : Addr) {k : Nat} (hk : k ≤ 16) :
    bytesAt (store4 m p 0 0 0 0) (p + BitVec.ofNat 64 k) (16 - k) = zeros (16 - k) := by
  have h := store4_zero_bytes m p
  rw [show (16 : Nat) = k + (16 - k) by omega, bytesAt_add,
    show zeros (k + (16 - k)) = zeros k ++ zeros (16 - k) by rw [zeros, zeros, zeros, List.replicate_append_replicate]] at h
  exact (List.append_inj h (by simp [length_bytesAt, Proof.Gcm.length_zeros])).2

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

/-- A copy of `tl` bytes from `S` to `W + d`, which holds 16 zero bytes. -/
theorem padCopy_ok {s : State} (he : Env c st w sp k7 k8 s) {S : BitVec 32} {d tl : Nat}
    (hd : d + 16 ≤ 2560) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (hSr : Covers [⟨State.addr S, tl⟩] (s.rd ++ s.wr))
    (hSf : S.toNat + tl ≤ 2 ^ 32) (hSd : (⟨State.addr S, tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 16⟩)
    {m₀ : Mem} (hm : s.mem = store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (hr1 : s.gpr .r1 = S)
    (hr2 : s.gpr .r2 = w + BitVec.ofNat 32 d) (hr3 : s.gpr .r3 = BitVec.ofNat 32 tl) :
    WP isa copyLoop s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 d) 16 =
        bytesAt m₀ (State.addr S) tl ++ zeros (16 - tl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ s'.mem ∧ LoopOut s S (w + BitVec.ofNat 32 d) tl s' := by
  have eD := L.wA (d := d) (by omega)
  have ww := L.ww
  have lp : LoopPre s S (w + BitVec.ofNat 32 d) tl := by
    refine ⟨hr1, hr2, hr3, h1, by omega, hSf, by rw [L.wN (by omega)]; omega, hSr, ?_, ?_⟩
    · rw [eD]; exact he.perm.wC (by omega)
    · rw [eD]; exact hSd.sub_right (Region.sub_prefix h16)
  refine WP.mono (copyLoop_ok s lp) fun s' ⟨hm', lo⟩ => ?_
  rw [hm, eD] at hm'
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) :=
    Cmac.frame_store4 _ _ _ _ _
  have hx : bytesAt (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (State.addr S) tl =
      bytesAt m₀ (State.addr S) tl :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hSd) (by omega)
  rw [hx] at hm'
  have hlen := length_bytesAt m₀ (State.addr S) tl
  refine ⟨?_, ?_, lo⟩
  · rw [hm', bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by omega), hlen, store4_zero_tail _ _ h16]
  · rw [hm']
    exact fz.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)

/-- `zero16 d`: the 16 bytes at `W + d` zeroed. -/
theorem zero16_ok {s : State} (he : Env c st w sp k7 k8 s) {d : Nat} (hd : d + 16 ≤ 2560) (ed₁ : d + 12 < 4096) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 d) 0 0 0 0 ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have w₀ := he.perm.wW (show d + 4 ≤ 2560 by omega)
  have w₁ := he.perm.wW (show d + 4 + 4 ≤ 2560 by omega)
  have w₂ := he.perm.wW (show d + 8 + 4 ≤ 2560 by omega)
  have w₃ := he.perm.wW (show d + 12 + 4 ≤ 2560 by omega)
  have e₀ := L.wA (d := d) (by omega)
  have e₁ := L.wA (d := d + 4) (by omega)
  have e₂ := L.wA (d := d + 8) (by omega)
  have e₃ := L.wA (d := d + 12) (by omega)
  have o₀ : d < 4096 := by omega
  have o₁ : d + 4 < 4096 := by omega
  have o₂ : d + 8 < 4096 := by omega
  refine ⟨_, by simp only [zero16]; arun [h11, e₀, e₁, e₂, e₃, w₀, w₁, w₂, w₃, o₀, o₁, o₂, ed₁], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]; rfl
  · intro r a; simp [gpr_setReg, a]
  · rfl
  · rfl
  · rfl

omit L in
/-- The four words at `p`, as bytes. -/
theorem bytes_words (m : Mem) (p : Addr) : bytesAt m p 16 = le4 (m.readW p 32) ++ le4 (m.readW (p + BitVec.ofNat 64 4) 32) ++
    le4 (m.readW (p + BitVec.ofNat 64 8) 32) ++ le4 (m.readW (p + BitVec.ofNat 64 12) 32) := by
  rw [Cmac.bytesAt_split4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW]

omit L in
theorem words_eq_iff (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    le4 a₀ ++ le4 a₁ ++ le4 a₂ ++ le4 a₃ = le4 b₀ ++ le4 b₁ ++ le4 b₂ ++ le4 b₃ ↔
      a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  constructor
  · intro h
    have l := Cmac.length_le4
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [l])
    obtain ⟨h₁, h₃⟩ := List.append_inj h₁ (by simp [l])
    obtain ⟨h₁, h₄⟩ := List.append_inj h₁ (by simp [l])
    exact ⟨le4_inj h₁, le4_inj h₄, le4_inj h₃, le4_inj h₂⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

omit L in
theorem cmp_value (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    BitVec.ofNat 32 1 - ((((a₀ ^^^ b₀ ||| a₁ ^^^ b₁) ||| a₂ ^^^ b₂) ||| a₃ ^^^ b₃) |||
      (BitVec.ofNat 32 0 - (((a₀ ^^^ b₀ ||| a₁ ^^^ b₁) ||| a₂ ^^^ b₂) ||| a₃ ^^^ b₃))) >>> 31 =
    if a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ then 1 else 0 := by
  rw [show BitVec.ofNat 32 0 = 0 from rfl, msb_or_neg]
  by_cases h : a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp
  · have : ¬(((a₀ ^^^ b₀ ||| a₁ ^^^ b₁) ||| a₂ ^^^ b₂) ||| a₃ ^^^ b₃) = 0 := by
      intro e
      simp only [show (0 : BitVec 32) = 0#32 from rfl, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff] at e
      exact h ⟨e.1.1.1, e.1.1.2, e.1.2, e.2⟩
    simp only [this, h, ite_false]; rfl

omit L in
theorem runBlock_app (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

omit L in
theorem runBlock_app_of {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_app, h₁]; exact h₂

/-- `cmpTail`: `r0` is 1 iff the 16 bytes at `W + 240` and `W + 256` are equal. -/
theorem cmpTail_ok {s : State} (he : Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa cmpTail s = some s' ∧
      s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 240) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 then 1 else 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h11 := he.r11
  have r₀ := he.perm.wR (show 240 + 4 ≤ 2560 by decide)
  have r₁ := he.perm.wR (show 244 + 4 ≤ 2560 by decide)
  have r₂ := he.perm.wR (show 248 + 4 ≤ 2560 by decide)
  have r₃ := he.perm.wR (show 252 + 4 ≤ 2560 by decide)
  have q₀ := he.perm.wR (show 256 + 4 ≤ 2560 by decide)
  have q₁ := he.perm.wR (show 260 + 4 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 264 + 4 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 268 + 4 ≤ 2560 by decide)
  let m := s.mem
  let a := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (240 + 4 * k)) 32
  let b := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (256 + 4 * k)) 32
  obtain ⟨s₁, run₁, g₁, h0₁, k₁⟩ : ∃ s₁, runBlock isa (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) s =
      some s₁ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₁.gpr r = s.gpr r) ∧
      s₁.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [xorW, vO, rO]; arun [h11, L.wA, r₀, r₁, q₀, q₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide) (by decide) (by decide), h11]
  have hm₁ := k₁.mem
  obtain ⟨s₂, run₂, g₂, h0₂, k₂⟩ : ∃ s₂, runBlock isa (xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++
      [.dp .orr .r0 .r0 (.reg .r1)]) s₁ = some s₂ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s₁.gpr r) ∧
      s₂.gpr .r0 = ((a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ||| a 2 ^^^ b 2) ||| a 3 ^^^ b 3 ∧ Keeps s₁ s₂ := by
    rw [← k₁.rd, ← k₁.wr] at r₂ r₃ q₂ q₃
    refine ⟨_, by simp only [xorW, vO, rO]; arun [h11₁, L.wA, r₂, r₃, q₂, q₃, hm₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m, h0₁, hm₁]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨s₃, run₃, g₃, h0₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
      .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)] s₂ =
      some s₃ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₃.gpr r = s₂.gpr r) ∧
      s₃.gpr .r0 = BitVec.ofNat 32 1 - ((s₂.gpr .r0 ||| (BitVec.ofNat 32 0 - s₂.gpr .r0)) >>> 31) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · intro r x y; simp [gpr_setReg, x, y]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, Op2.eval]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨s₃, ?_, ?_, ?_, k₁.trans (k₂.trans k₃)⟩
  · rw [show cmpTail = (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      ((xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31),
        .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)]) from rfl]
    exact runBlock_app_of run₁ (runBlock_app_of run₂ run₃)
  · rw [h0₃, h0₂, cmp_value, bytes_words, bytes_words]
    simp only [add_ofNat_assoc]
    congr 1
    simp only [a, b, m]
    exact propext (words_eq_iff _ _ _ _ _ _ _ _).symm
  · intro r x y z; rw [g₃ r x y, g₂ r x y z, g₁ r x y z]

/-- `recv`: the received tag (`r6` bytes at `T`, the stack argument at `[sp + 16]`), padded
with zeros at `W + 256`. -/
theorem recv_ok {s : State} (he : Env c st w sp k7 k8 s) {T : BitVec 32} {tl : Nat}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = T)
    (hTr : Covers [⟨State.addr T, tl⟩] (s.rd ++ s.wr)) (hTf : T.toNat + tl ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa recv s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (State.addr T) tl ++ zeros (16 - tl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 256, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₀, run₀, h1₀, g₀, k₀⟩ : ∃ s₀, runBlock isa [.ldrSp .r1 16] s = some s₀ ∧ s₀.gpr .r1 = T ∧
      (∀ r, r ≠ .r1 → s₀.gpr r = s.gpr r) ∧ Keeps s s₀ := by
    refine ⟨_, by arun [hTi, hTv], ?_, ?_, ?_⟩
    · simp [gpr_setReg, hTv]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₀ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₀ _ (by decide)) k₀.sp k₀.rd k₀.wr
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁⟩ := zero16_ok L he₀ (d := rO) (by decide) (by decide)
  have h11 : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he₀.r11]
  obtain ⟨s₂, run₂, h2₂, h3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r2 .r11 rO, .mov .r3 (.reg .r6)] s₁ = some s₂ ∧
      s₂.gpr .r2 = w + BitVec.ofNat 32 256 ∧ s₂.gpr .r3 = BitVec.ofNat 32 tl ∧
      (∀ r, r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [rO]; arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, g₁ .r6 (by decide), g₀ .r6 (by decide), h6]
    · intro r x y; simp [gpr_setReg, x, y]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have run : runBlock isa (.ldrSp .r1 16 :: zero16 rO ++ [addI .r2 .r11 rO, .mov .r3 (.reg .r6)]) s = some s₂ :=
    runBlock_app_of (a := [.ldrSp .r1 16]) run₀ (runBlock_app_of run₁ run₂)
  refine WP.seq (WP.of_runBlock ⟨s₂, run, ?_⟩)
  have he₂ := he₀.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide), g₁ _ (by decide)]) (k₂.sp.trans sp₁) (k₂.rd.trans rd₁)
      (k₂.wr.trans wr₁)
  have h1₂ : s₂.gpr .r1 = T := by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), h1₀]
  have hTr₂ : Covers [⟨State.addr T, tl⟩] (s₂.rd ++ s₂.wr) := by
    rw [k₂.rd, k₂.wr, rd₁, wr₁, k₀.rd, k₀.wr]; exact hTr
  refine WP.mono (padCopy_ok L he₂ (d := 256) (by decide) h1 h16 hTr₂ hTf hTd (m₀ := s.mem)
    (by rw [k₂.mem, hm₁, k₀.mem]; rfl) h1₂ h2₂ h3₂) fun s₃ ⟨hb, hf, lo⟩ => ?_
  refine ⟨hb, hf, fun r a b d e f => ?_, lo.rd.trans (k₂.rd.trans (rd₁.trans k₀.rd)),
    lo.wr.trans (k₂.wr.trans (wr₁.trans k₀.wr)), lo.sp.trans (k₂.sp.trans (sp₁.trans k₀.sp))⟩
  rw [lo.other r a b d e f, g₂ r d e, g₁ r a, g₀ r b]

/-- `cmp o`: the first `r6` bytes of the tag at `W + o`, padded with zeros at
`W + 240`, compared with the received tag at `W + 256`. -/
theorem cmp_ok {s : State} (he : Env c st w sp k7 k8 s) {o : Nat} (ho : o = 0 ∨ o = 112) {tl : Nat}
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa (cmp o) s fun s' => s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 o) tl ++ zeros (16 - tl) =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 then 1 else 0) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 240, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁⟩ := zero16_ok L he (d := vO) (by decide) (by decide)
  have h11 : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
  have eo : encodable (BitVec.ofNat 32 o) = true := by rcases ho with rfl | rfl <;> decide
  obtain ⟨s₂, run₂, h1₂, h2₂, h3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r1 .r11 o, addI .r2 .r11 vO,
      .mov .r3 (.reg .r6)] s₁ = some s₂ ∧ s₂.gpr .r1 = w + BitVec.ofNat 32 o ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 240 ∧
      s₂.gpr .r3 = BitVec.ofNat 32 tl ∧ (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [vO]; arun [eo], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, g₁ .r6 (by decide), h6]
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, runBlock_app_of run₁ run₂, ?_⟩)
  have he₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide)]) (k₂.sp.trans sp₁) (k₂.rd.trans rd₁)
      (k₂.wr.trans wr₁)
  have hSr : Covers [⟨State.addr (w + BitVec.ofNat 32 o), tl⟩] (s₂.rd ++ s₂.wr) := by
    rw [L.wA (by omega)]; exact covers_left (he₂.perm.wC (by omega))
  have hSd : (⟨State.addr (w + BitVec.ofNat 32 o), tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 240, 16⟩ := by
    rw [L.wA (by omega)]; exact Lay.w_w (by omega) (by omega) (by decide)
  refine WP.seq (WP.mono (padCopy_ok L he₂ (d := 240) (by decide) h1 h16 hSr (by rw [L.wN (by omega)]; have := L.ww; omega) hSd
    (m₀ := s.mem) (by rw [k₂.mem, hm₁]; rfl) h1₂ h2₂ h3₂) fun s₃ ⟨hb, hf, lo⟩ => ?_)
  rw [L.wA (by omega)] at hb
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) lo.sp lo.rd lo.wr
  obtain ⟨s₄, run₄, h0₄, g₄, k₄⟩ := cmpTail_ok L he₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_, ?_, fun r a b d e f => ?_, k₄.rd.trans (lo.rd.trans (k₂.rd.trans rd₁)),
    k₄.wr.trans (lo.wr.trans (k₂.wr.trans wr₁)), k₄.sp.trans (lo.sp.trans (k₂.sp.trans sp₁))⟩
  · have h256 : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 :=
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide)
    rw [h0₄, hb, h256]
  · rw [k₄.mem]; exact hf
  · rw [g₄ r a b d, lo.other r a b d e f, g₂ r b d e, g₁ r a]

end

end VG.Proof.AesGcm.Arm
