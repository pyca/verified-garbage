import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Select
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop

/-!
# The `zmm` comb: the digits and their signs

`zdigits` reads the even chunk `2j` (as `combIndex` counts it, through
`rbx = j + 26`) and the odd chunk `2j + 1`, as `combStep` does: their
magnitudes into `r10` and `r8`, the masks of their signs to `SGB` and `SGA`
(from `rdx`, which `combSign` leaves holding the mask), and the table `j`
into `r9`. `zsign` puts the two masks into the halves of `zmm15`.
-/

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Zmm VG.Proof.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (sc)
open VG.Impl.X25519.X86_64.Ifma (y)
open VG.Proof.X25519.X86_64 (off ofs Keeps Outside)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw qword_app0 qword_app1)

/-- Memory kept but at the offsets of `P` from `b`. -/
def MemOff (b : Addr) (P : Nat → Prop) (m m' : Mem) : Prop := ∀ a, ¬ P (ofs b a) → m' a = m a

theorem MemOff.refl (b : Addr) (P : Nat → Prop) (m : Mem) : MemOff b P m m := fun _ _ => rfl

theorem MemOff.trans {b : Addr} {P : Nat → Prop} {m₁ m₂ m₃ : Mem} (h₁ : MemOff b P m₁ m₂)
    (h₂ : MemOff b P m₂ m₃) : MemOff b P m₁ m₃ := fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem MemOff.mono {b : Addr} {P Q : Nat → Prop} {m m' : Mem} (h : MemOff b P m m')
    (hpq : ∀ q, P q → Q q) : MemOff b Q m m' := fun a ha => h a fun hp => ha (hpq _ hp)

private theorem sign_fact : ∀ n < 32,
    ((BitVec.ofNat 64 n - (16 : BitVec 32).signExtend 64 ^^^
        0#64 - (BitVec.ofBool (decide ((BitVec.ofNat 64 n).toNat <
          ((16 : BitVec 32).signExtend 64).toNat))).setWidth 64) -
      (0#64 - (BitVec.ofBool (decide ((BitVec.ofNat 64 n).toNat <
        ((16 : BitVec 32).signExtend 64).toNat))).setWidth 64) = BitVec.ofNat 64 (mag n)) ∧
    0#64 - (BitVec.ofBool (decide ((BitVec.ofNat 64 n).toNat <
      ((16 : BitVec 32).signExtend 64).toNat))).setWidth 64 = signMask n := by
  decide +kernel

/-- From the chunk `n` in `rax`: its magnitude into `g`, and the mask of its sign to the
quadword at `d` (and to `combSignMask`). -/
theorem zsignDig_ok {s : State} {base : Addr} (hs : Scratch s base) {n : Nat} (hn : n < 32)
    (hax : s.gpr .rax = BitVec.ofNat 64 n) (g : Reg) (hg : g ≠ .rax ∧ g ≠ .rdx ∧ g ≠ .rdi) {d : Nat}
    (hd : 1160 ≤ d ∧ d + 8 ≤ 8192) :
    WP isa (.block (combSign ++ ([.mov g (.reg .rax), .store (sc d) .rdx] : List Instr))) s fun t =>
      t.gpr g = BitVec.ofNat 64 (mag n) ∧ t.mem.readW (off base d) 64 = signMask n ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ g → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      MemOff base (fun q => (combSignMask ≤ q ∧ q < combSignMask + 8) ∨ (d ≤ q ∧ q < d + 8)) s.mem t.mem ∧
      t.syms = s.syms := by
  have hw : InRegions s.wr (off base combSignMask) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by simp only [combSignMask]; omega) (by simp only [combSignMask]; omega)⟩
  have hw' : InRegions s.wr (off base d) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [combSign, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, State.store64, Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_setReg, RegUpd.cf_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hs.rdi, hax, hw, ite_true, ite_false, reduceCtorEq,
    BitVec.sub_self, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', Ne.symm hg.2.2, Ne.symm hg.2.1, hw']
  refine ⟨(sign_fact n hn).1, ?_, fun r h1 h2 h3 => ?_, ?_⟩
  · rw [Mem.readW_writeW_self64]; exact (sign_fact n hn).2
  · simp only [h1, h2, h3, ite_false]
  refine ⟨rfl, trivial, fun a ha => ?_, rfl⟩
  simp only [not_or, not_and, Nat.not_lt] at ha
  have hx := (a - base).isLt
  show ((s.mem.writeW (off base combSignMask) _).writeW (off base d) _) a = s.mem a
  simp only [Mem.writeW, Mem.write, off, sub_off]
  simp only [ofs, combSignMask] at ha
  rw [ite_eq_right ?_, ite_eq_right ?_]
  · simp only [combSignMask]; omega
  · omega


/-- `rbx += k`. -/
theorem rbxAdd_ok (s : State) {c k : Nat} (hk : k < 64) (hb : s.gpr .rbx = BitVec.ofNat 64 c) :
    WP isa (.block [.alu .add .rbx (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (c + k) ∧ Keeps [.rbx] s t ∧ t.syms = s.syms := by
  have he : (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by
    have : ∀ k < 64, (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by decide
    exact this k hk
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, hb, he, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true]
  refine ⟨by rw [BitVec.ofNat_add], ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `rbx -= k`. -/
theorem rbxSub_ok (s : State) {c k : Nat} (hc : k < 64) (hk : k ≤ c) (hb : s.gpr .rbx = BitVec.ofNat 64 c) :
    WP isa (.block [.alu .sub .rbx (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (c - k) ∧ Keeps [.rbx] s t ∧ t.syms = s.syms := by
  have he : (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by
    have : ∀ k < 64, (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by decide
    exact this k hc
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, hb, he, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true]
  refine ⟨by rw [Offset.ofNat_sub_ofNat hk], ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem combIdx_even {j : Nat} (hj : j < 26) : combIdx (j + 26) = 2 * j ∧ combTblIdx (j + 26) = j := by
  unfold combIdx combTblIdx; constructor <;> split <;> omega

theorem combIdx_odd {j : Nat} (hj : j < 26) : combIdx j = 2 * j + 1 ∧ combTblIdx j = j := by
  unfold combIdx combTblIdx; constructor <;> split <;> omega

/-- The offsets `zdigits` writes: the sign's mask and the slots `SGA` and `SGB`. -/
def DigOff (q : Nat) : Prop :=
  (combSignMask ≤ q ∧ q < combSignMask + 8) ∨ (SGA ≤ q ∧ q < SGA + 8) ∨ (SGB ≤ q ∧ q < SGB + 8)

theorem zdigits_scal : scalCode zdigits = true := by decide

/-- The two chunks of step `j`: their magnitudes into `r8` (odd) and `r10` (even), the masks of
their signs to `SGA` and `SGB`, and the table `j` into `r9`. -/
theorem zdigits_ok {s : State} {base : Addr} (hs : Scratch s base) {S j : Nat} (hj : j < 26)
    (hS : S < 2 ^ 256) (hb : s.gpr .rbx = BitVec.ofNat 64 j)
    (hbits : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa zdigits s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (mag (nib S (2 * j + 1))) ∧
      t.gpr .r10 = BitVec.ofNat 64 (mag (nib S (2 * j))) ∧ t.gpr .r9 = BitVec.ofNat 64 j ∧
      t.gpr .rbx = BitVec.ofNat 64 j ∧
      t.mem.readW (off base SGA) 64 = signMask (nib S (2 * j + 1)) ∧
      t.mem.readW (off base SGB) 64 = signMask (nib S (2 * j)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ MemOff base DigOff s.mem t.mem := by
  obtain ⟨e1, e2⟩ := combIdx_even hj
  obtain ⟨o1, o2⟩ := combIdx_odd hj
  rw [zdigits]
  refine WP.seq (WP.mono (rbxAdd_ok s (k := 26) (by decide) hb) fun s₁ ⟨b₁, k₁, _⟩ => ?_)
  have hs₁ : Scratch s₁ base := hs.of_keeps k₁ (by decide)
  refine WP.seq (WP.mono (combIndex_ok s₁ (c := j + 26) (by omega) b₁) fun s₂ ⟨c₂, r₂, k₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.seq (WP.mono (combChunk_ok (S := S) hs₂ (c := j + 26) (by omega) hS
    (by rw [k₂.1 _ (by decide)]; exact b₁) c₂ (fun q hq => by rw [k₂.2.1, k₁.2.1]; exact hbits q hq))
    fun s₃ ⟨a₃, k₃⟩ => ?_)
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [e1] at a₃
  refine WP.seq ?_
  · rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (rbxSub_ok s₃ (c := j + 26) (k := 26) (by decide) (by omega)
      (by rw [k₃.1 _ (by decide), k₂.1 _ (by decide)]; exact b₁)) fun s₄ ⟨b₄, k₄, _⟩ => ?_
    have hs₄ := hs₃.of_keeps k₄ (by decide)
    refine WP.mono (zsignDig_ok hs₄ (n := nib S (2 * j)) (Nat.mod_lt _ (by decide))
      (by rw [k₄.1 _ (by decide)]; exact a₃) .r10 (by decide) (d := SGB) (by unfold SGB; omega))
      fun s₅ ⟨g₅, m₅, k₅, rd₅, wr₅, o₅, _⟩ => ?_
    have hs₅ : Scratch s₅ base := ⟨by rw [k₅ _ (by decide) (by decide) (by decide)]; exact hs₄.rdi,
      by rw [wr₅]; exact hs₄.wr, hs.nowrap⟩
    have bits₅ : ∀ q < 256, s₅.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) := fun q hq => by
      rw [o₅ _ (by simp only [ofs, off]; rw [Mem.sub_ofNat_toNat _ (by omega)]; unfold SGB combSignMask; omega),
        k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
      exact hbits q hq
    have b₅ : s₅.gpr .rbx = BitVec.ofNat 64 j := by
      rw [k₅ _ (by decide) (by decide) (by decide), b₄]; rfl
    refine WP.seq (WP.mono (combIndex_ok s₅ (c := j) (by omega) b₅) fun s₆ ⟨c₆, r₆, k₆⟩ => ?_)
    have hs₆ := hs₅.of_keeps k₆ (by decide)
    refine WP.seq (WP.mono (combChunk_ok (S := S) hs₆ (c := j) (by omega) hS
      (by rw [k₆.1 _ (by decide)]; exact b₅) c₆ (fun q hq => by rw [k₆.2.1]; exact bits₅ q hq))
      fun s₇ ⟨a₇, k₇⟩ => ?_)
    have hs₇ := hs₆.of_keeps k₇ (by decide)
    rw [o1] at a₇
    refine WP.mono (zsignDig_ok hs₇ (n := nib S (2 * j + 1)) (Nat.mod_lt _ (by decide)) a₇ .r8 (by decide)
      (d := SGA) (by unfold SGA; omega)) fun t ⟨g₈, m₈, k₈, rd₈, wr₈, o₈, _⟩ => ?_
    have gk : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → t.gpr r = s₅.gpr r :=
      fun r h1 h2 h3 h4 h5 => by
        rw [k₈ r h1 h3 h4, k₇.1 r (by simp [h1, h3]), k₆.1 r (by simp [h2, h5])]
    refine ⟨g₈, ?_, ?_, ?_, m₈, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_⟩
    · rw [gk _ (by decide) (by decide) (by decide) (by decide) (by decide), g₅]
    · rw [k₈ _ (by decide) (by decide) (by decide), k₇.1 _ (by decide), r₆, o2]
    · rw [gk _ (by decide) (by decide) (by decide) (by decide) (by decide), b₅]
    · rw [← m₅]
      refine Mem.readW_congr fun i hi => ?_
      rw [o₈ _ ?_, k₇.2.1, k₆.2.1]
      simp only [ofs, off, Offset.add_ofNat_add_ofNat]
      rw [Mem.sub_ofNat_toNat _ (by unfold SGB; omega)]; unfold SGB SGA combSignMask; omega
    · by_cases hr : r = .rbx
      · subst hr
        rw [gk _ (by decide) (by decide) (by decide) (by decide) (by decide), b₅, hb]
      · rw [gk r h1 h2 h3 h4 h5, k₅ r h1 h3 h6, k₄.1 r (by simp [hr]), k₃.1 r (by simp [h1, h3]),
          k₂.1 r (by simp [h2, h5]), k₁.1 r (by simp [hr])]
    · rw [rd₈, k₇.2.2.1, k₆.2.2.1, rd₅, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
    · rw [wr₈, k₇.2.2.2, k₆.2.2.2, wr₅, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
    · intro a ha
      rw [o₈ a (fun h => ha (by unfold DigOff; omega)), k₇.2.1, k₆.2.1, o₅ a (fun h => ha (by unfold DigOff; omega)),
        k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]

/-- `rcx` = the quadword at `d`. -/
theorem loadQ_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    WP isa (.block [.mov .rcx (.mem (sc d))]) s fun t =>
      t.gpr .rcx = s.mem.readW (off base d) 64 ∧ Keeps [.rcx] s t ∧ (∀ r i, t.zlane r i = s.zlane r i) ∧
        t.syms = s.syms := by
  have hr : InRegions (s.rd ++ s.wr) (off base d) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, hs.rdi, hr, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, fun _ _ => rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- The masks of the signs: `SGA` in half 0 and `SGB` in half 1 of `zmm15`. -/
theorem zsign_ok {s : State} {base : Addr} (hs : Scratch s base) {mA mB : BitVec 64}
    (ha : s.mem.readW (off base SGA) 64 = mA) (hb : s.mem.readW (off base SGB) 64 = mB) :
    WP isa (.block zsign) s fun t =>
      (∀ h < 2, ∀ k < 4, zq t (xr 15) h k = if h = 0 then mA else mB) ∧
      ZVKeep [.rcx] (fun r => r = xr 14 ∨ r = xr 15) s t := by
  rw [zsign, show ([.mov .rcx (.mem (sc SGA)), .vop (.vmovq (y 14) .rcx), .zop (.vpbroadcastq (y 14) (y 14)),
      .mov .rcx (.mem (sc SGB)), .vop (.vmovq (y 15) .rcx), .zop (.vpbroadcastq (y 15) (y 15)), zlo 15 14 15] :
      List Instr) = [.mov .rcx (.mem (sc SGA))] ++ ([.vop (.vmovq (y 14) .rcx), .zop (.vpbroadcastq (y 14) (y 14))] ++
      ([.mov .rcx (.mem (sc SGB))] ++ [.vop (.vmovq (y 15) .rcx), .zop (.vpbroadcastq (y 15) (y 15)),
        zlo 15 14 15])) from rfl, WP.block_append_iff]
  refine WP.mono (loadQ_ok hs (d := SGA) (by unfold SGA; omega)) fun s₁ ⟨c₁, k₁, z₁, y₁⟩ => ?_
  let s₂ := (ZOp.vpbroadcastq (y 14) (y 14)).exec ((VOp.vmovq (y 14) .rcx).exec s₁)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  have hs₂ : Scratch s₂ base := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadQ_ok hs₂ (d := SGB) (by unfold SGB; omega)) fun s₃ ⟨c₃, k₃, z₃, y₃⟩ => ?_
  let s₄ := (ZOp.vshufi32x4 (y 15) (y 14) (y 15) 0x44).exec
    ((ZOp.vpbroadcastq (y 15) (y 15)).exec ((VOp.vmovq (y 15) .rcx).exec s₃))
  refine WP.of_runBlock ⟨s₄, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, zlo]; rfl, ?_⟩
  have m₂ : s₂.mem = s.mem := k₁.2.1
  have l₄ : ∀ r, ∀ i < 4, s₄.zlane r i = if r = y 15 then (if i < 2 then mA ++ mA else mB ++ mB)
      else if r = y 14 then mA ++ mA else s.zlane r i := by
    intro r i hi
    simp only [s₄, zlane_zlo _ _ _ _ _ hi, zlane_dup _ _ _ _ hi, zlane_dup _ _ _ _ (show i - 2 < 4 by omega), z₃,
      s₂, c₃, c₁, ha]
    rw [show s₂.mem = s.mem from m₂, hb]
    have n1514 : y 15 ≠ y 14 := by decide
    by_cases h15 : r = y 15
    · subst h15; simp [n1514.symm]
    · by_cases h14 : r = y 14
      · subst h14; simp [n1514.symm]
      · simp [h15, h14, z₁]
  refine ⟨fun h hh k hk => ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr i hi => ?_, ?_⟩⟩
  · simp only [zq, show xr 15 = y 15 from rfl, l₄ _ _ (show 2 * h + k / 2 < 4 by omega), ite_true]
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> simp
  · show s₃.gpr r = s.gpr r
    rw [k₃.1 r hr]; exact k₁.1 r hr
  · show s₃.mem = s.mem; rw [k₃.2.1]; exact m₂
  · show s₃.rd = s.rd; rw [k₃.2.2.1]; exact k₁.2.2.1
  · show s₃.wr = s.wr; rw [k₃.2.2.2]; exact k₁.2.2.2
  · simp only [not_or, show xr 14 = y 14 from rfl, show xr 15 = y 15 from rfl] at hr
    rw [l₄ _ _ hi, ite_eq_right hr.2, ite_eq_right hr.1]
  · show s₃.syms = s.syms; rw [y₃]; exact y₁

end VG.Proof.Ed25519.X86_64.Zmm
