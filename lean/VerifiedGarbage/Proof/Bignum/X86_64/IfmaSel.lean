import VerifiedGarbage.Proof.Bignum.X86_64.AmmSpec
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-!
# RSA with AVX512_IFMA on x86-64: reading an entry of the table

`select p` reads the top 4 bits `v` of the quadword at `oV` of prime `p`'s
region and copies entry `v` of the table (160 bytes at `oTab + 160 v`) to
`oS`, reading every entry and keeping entry `v` under a mask
(`select_ok`).
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum.X86_64 (off word ofs Outside off_off Scr)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oTab oS oV mask52)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw qword256_ymm qw_vbin qw_vpbroadcastq qw_vmovq qw_load qw_lane qword_and
  qword_or)
open VG.Proof.MlKem.X86_64 (Keep)

/-- All ones if `c`. -/
def selMask (c : Bool) : BitVec 64 := if c then BitVec.allOnes 64 else 0

theorem lt_one_iff (x : BitVec 64) : decide (x.toNat < (1 : BitVec 64).toNat) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ← BitVec.toNat_inj,
    show (1 : BitVec 64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl]
  constructor <;> intro h <;> omega

theorem xor_zero_iff {x y : BitVec 64} : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    have := congrArg (· ^^^ y) h
    simpa [BitVec.xor_assoc] using this
  · rintro rfl
    simp

theorem ofNat64_inj' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · rintro rfl; rfl

/-- The mask of entry `i`. -/
theorem selMask_ok {s : State} {i v : Nat} (hi : i < 16) (hv : v < 16)
    (hc : s.gpr .rcx = BitVec.ofNat 64 i) (hd : s.gpr .rdx = BitVec.ofNat 64 v) :
    WP isa (.block [.mov .rax (.reg .rcx), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1),
      .alu .sbb .rax (.reg .rax)]) s fun s' => s'.gpr .rax = selMask (decide (i = v)) ∧ Keep [.rax] s s' ∧
        s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' => s'.gpr .rax = selMask (decide (i = v)) ∧
    s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr) (by
    xrun [hc, hd]
    and_intros
    any_goals rfl
    rw [lt_one_iff, show decide (BitVec.ofNat 64 i ^^^ BitVec.ofNat 64 v = 0) = decide (i = v) from
      decide_eq_decide.mpr (xor_zero_iff.trans (ofNat64_inj' (by omega) (by omega)))]
    cases decide (i = v) <;> rfl) rfl) fun s' ⟨⟨h, m, x, y, z⟩, k⟩ => ⟨h, k, m, x, y, z⟩


theorem ea_r {s : State} {r : Reg} {a : Addr} (h : s.gpr r = a) (d : Nat) :
    s.ea (VG.Impl.Rsa.X86_64.CrtIfma.at_ r d) = a + BitVec.ofNat 64 d := by
  simp only [State.ea, VG.Impl.Rsa.X86_64.CrtIfma.at_, h]
  exact congrArg _ (BitVec.ofInt_natCast ..)

theorem crt_xr_lt : ∀ k < 5, VG.Impl.Rsa.X86_64.CrtIfma.xr k ≠ .xmm5 ∧ VG.Impl.Rsa.X86_64.CrtIfma.xr k ≠ .xmm6 := by
  decide

/-- Entry `k`'s 32 bytes at `r8`, under the mask in `xmm5`, OR'ed into `xr k`. -/
theorem selGroup_ok {t : State} {k : Nat} (hk : k < 5) {a : Addr} (h8 : t.gpr .r8 = a)
    (hin : InRegions (t.rd ++ t.wr) (a + BitVec.ofNat 64 (32 * k)) 32) {msk : BitVec 64}
    (hm : ∀ j < 4, qw t .xmm5 j = msk) :
    WP isa (.block [.vmovdquLoad .l256 .xmm6 (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r8 (32 * k)),
        .vop (.vbin .vpand .l256 .xmm6 .xmm6 .xmm5),
        .vop (.vbin .vpor .l256 (VG.Impl.Rsa.X86_64.CrtIfma.xr k) (VG.Impl.Rsa.X86_64.CrtIfma.xr k) .xmm6)]) t
      fun t' => (∀ j < 4, qw t' (VG.Impl.Rsa.X86_64.CrtIfma.xr k) j =
          qw t (VG.Impl.Rsa.X86_64.CrtIfma.xr k) j ||| (t.mem.readW (a + BitVec.ofNat 64 (32 * k + 8 * j)) 64 &&& msk)) ∧
        (∀ r, r ≠ VG.Impl.Rsa.X86_64.CrtIfma.xr k → r ≠ .xmm6 → ∀ j < 4, qw t' r j = qw t r j) ∧
        t'.gpr = t.gpr ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mxcsr = t.mxcsr := by
  obtain ⟨h5, h6⟩ := crt_xr_lt k hk
  rw [WP.block_cons_iff]
  refine ⟨t.setV .l256 .xmm6 ((t.mem.readW (a + BitVec.ofNat 64 (32 * k)) 256).extractLsb' 0 128)
    ((t.mem.readW (a + BitVec.ofNat 64 (32 * k)) 256).extractLsb' 128 128),
    by simp only [exec, ea_r h8, State.load256, hin, ite_true, Option.map_some], ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ⟨fun j hj => ?_, fun r r1 r2 j hj => ?_, rfl, rfl, rfl, rfl, rfl⟩⟩
  · have h65 : XReg.xmm5 ≠ XReg.xmm6 := by decide
    simp only [qw_vbin, VBinOp.sse, XBinOp.eval, qword_or, qword_and, qw_lane, ite_true, h6, h65, ite_false,
      qw_load _ _ _ _ hj, hm j hj, BitVec.add_assoc, BitVec.ofNat_add]
  · simp only [qw_vbin, r1, r2, ite_false, qw_load _ _ _ _ hj]


/-- The five groups of an entry. -/
def selGroups (n : Nat) : List Instr :=
  (List.range n).flatMap fun k => [.vmovdquLoad .l256 .xmm6 (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r8 (32 * k)),
    .vop (.vbin .vpand .l256 .xmm6 .xmm6 .xmm5),
    .vop (.vbin .vpor .l256 (VG.Impl.Rsa.X86_64.CrtIfma.xr k) (VG.Impl.Rsa.X86_64.CrtIfma.xr k) .xmm6)]

theorem crt_xr_inj : ∀ k < 5, ∀ k' < 5, VG.Impl.Rsa.X86_64.CrtIfma.xr k = VG.Impl.Rsa.X86_64.CrtIfma.xr k' → k = k' := by
  decide

theorem selGroups_ok {t : State} {a : Addr} (h8 : t.gpr .r8 = a)
    (hin : ∀ k < 5, InRegions (t.rd ++ t.wr) (a + BitVec.ofNat 64 (32 * k)) 32) {msk : BitVec 64}
    (hm : ∀ j < 4, qw t .xmm5 j = msk) :
    ∀ n ≤ 5, WP isa (.block (selGroups n)) t fun t' =>
      (∀ k < 5, ∀ j < 4, qw t' (VG.Impl.Rsa.X86_64.CrtIfma.xr k) j = if k < n then
          qw t (VG.Impl.Rsa.X86_64.CrtIfma.xr k) j ||| (t.mem.readW (a + BitVec.ofNat 64 (32 * k + 8 * j)) 64 &&& msk)
        else qw t (VG.Impl.Rsa.X86_64.CrtIfma.xr k) j) ∧
      (∀ j < 4, qw t' .xmm5 j = msk) ∧
      t'.gpr = t.gpr ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mxcsr = t.mxcsr := by
  intro n
  induction n with
  | zero => intro _; exact WP.block_nil ⟨fun k _ j _ => by simp, hm, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    intro hn
    rw [selGroups, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t₁ ⟨v₁, m₁, g₁, me₁, rd₁, wr₁, x₁⟩ => ?_
    refine WP.mono (selGroup_ok (k := n) (a := a) (by omega) (by rw [congrFun g₁]; exact h8)
      (by rw [rd₁, wr₁]; exact hin n (by omega)) m₁) fun t₂ ⟨v₂, o₂, g₂, me₂, rd₂, wr₂, x₂⟩ =>
        ⟨fun k hk j hj => ?_, fun j hj => ?_, g₂.trans g₁, me₂.trans me₁, rd₂.trans rd₁, wr₂.trans wr₁, x₂.trans x₁⟩
    · by_cases hkn : k = n
      · subst hkn
        rw [v₂ j hj, v₁ k hk j hj, me₁]
        simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
      · have hne : VG.Impl.Rsa.X86_64.CrtIfma.xr k ≠ VG.Impl.Rsa.X86_64.CrtIfma.xr n :=
          fun h => hkn (crt_xr_inj k hk n (by omega) h)
        rw [o₂ _ hne (crt_xr_lt k hk).2 j hj, v₁ k hk j hj]
        by_cases hlt : k < n
        · simp only [hlt, show k < n + 1 by omega, ite_true]
        · simp only [hlt, show ¬ k < n + 1 by omega, ite_false]
    · rw [o₂ _ (fun h => (crt_xr_lt n (by omega)).1 h.symm) (by decide) j hj, m₁ j hj]


theorem qw_eq_of {s s' : State} (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) (r : XReg) (k : Nat) :
    qw s' r k = qw s r k := by
  unfold qw State.lane; rw [hx, hy]

theorem sx160 : BitVec.signExtend 64 (160 : BitVec 32) = BitVec.ofNat 64 160 := by decide

/-- The entry's end: the next entry, `ZF` after the last. -/
theorem selTail_ok {s : State} {base : Addr} {i : Nat} (hi : i < 16)
    (h8 : s.gpr .r8 = base + BitVec.ofNat 64 (160 * i)) (hc : s.gpr .rcx = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .add .r8 (.imm 160), .alu .add .rcx (.imm 1), .alu .cmp .rcx (.imm 16)]) s fun s' =>
      s'.gpr .r8 = base + BitVec.ofNat 64 (160 * (i + 1)) ∧ s'.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧
      s'.zf = some (decide (i + 1 = 16)) ∧ Keep [.r8, .rcx] s s' ∧
      s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8, .rcx] (Q := fun s' =>
    s'.gpr .r8 = base + BitVec.ofNat 64 (160 * (i + 1)) ∧ s'.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧
      s'.zf = some (decide (i + 1 = 16)) ∧ s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [h8, hc, sx160, ofNat_add_one]
    and_intros
    any_goals rfl
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
    · rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_sub_beq (by omega) (by decide)]) rfl)
    fun s' ⟨⟨a, b, c, d, e, f, g⟩, k⟩ => ⟨a, b, c, k, d, e, f, g⟩


/-- After entries below `i` of the table at `base`, `v` the entry to read. -/
structure SelInv (t₀ : State) (base : Addr) (v i : Nat) (t : State) : Prop where
  r8 : t.gpr .r8 = base + BitVec.ofNat 64 (160 * i)
  rcx : t.gpr .rcx = BitVec.ofNat 64 i
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → t.gpr r = t₀.gpr r
  mem : t.mem = t₀.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  mxcsr : t.mxcsr = t₀.mxcsr
  acc : ∀ k < 5, ∀ j < 4, qw t (VG.Impl.Rsa.X86_64.CrtIfma.xr k) j =
    if v < i then t₀.mem.readW (base + BitVec.ofNat 64 (160 * v + 32 * k + 8 * j)) 64 else 0

def selBody : List Instr :=
  [.mov .rax (.reg .rcx), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
    .vop (.vmovq .xmm5 .rax), .vop (.vpbroadcastq .l256 .xmm5 .xmm5)] ++
  ((List.range 5).flatMap fun k => [.vmovdquLoad .l256 .xmm6 (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r8 (32 * k)),
    .vop (.vbin .vpand .l256 .xmm6 .xmm6 .xmm5),
    .vop (.vbin .vpor .l256 (VG.Impl.Rsa.X86_64.CrtIfma.xr k) (VG.Impl.Rsa.X86_64.CrtIfma.xr k) .xmm6)]) ++
  [.alu .add .r8 (.imm 160), .alu .add .rcx (.imm 1), .alu .cmp .rcx (.imm 16)]

theorem selMask_and (w : BitVec 64) (c : Bool) : (w &&& selMask c) = if c then w else 0 := by
  cases c
  · simp [selMask]
  · simp only [selMask, ite_true, BitVec.and_allOnes]

theorem zero_or64 (x : BitVec 64) : 0 ||| x = x := by simp
theorem or_zero64 (x : BitVec 64) : x ||| 0 = x := by simp

/-- Entry `i`. -/
theorem selIter_ok {t₀ t : State} {base : Addr} {v i : Nat} (hv : v < 16) (hi : i < 16)
    (hd : t₀.gpr .rdx = BitVec.ofNat 64 v)
    (hin : ∀ i < 16, ∀ k < 5, InRegions (t₀.rd ++ t₀.wr) (base + BitVec.ofNat 64 (160 * i + 32 * k)) 32)
    (h : SelInv t₀ base v i t) :
    WP isa (.block selBody) t fun t' => SelInv t₀ base v (i + 1) t' ∧ t'.zf = some (decide (i + 1 = 16)) := by
  rw [show selBody = [.mov .rax (.reg .rcx), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1),
    .alu .sbb .rax (.reg .rax)] ++ ([.vop (.vmovq .xmm5 .rax), .vop (.vpbroadcastq .l256 .xmm5 .xmm5)] ++
    (selGroups 5 ++ [.alu .add .r8 (.imm 160), .alu .add .rcx (.imm 1), .alu .cmp .rcx (.imm 16)])) from rfl,
    WP.block_append_iff]
  have hdx : t.gpr .rdx = BitVec.ofNat 64 v := (h.gpr _ (by decide) (by decide) (by decide)).trans hd
  refine WP.mono (selMask_ok hi hv h.rcx hdx) fun t₁ ⟨m₁, k₁, me₁, x₁, y₁, mx₁⟩ => ?_
  rw [List.cons_append, List.cons_append, List.nil_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  generalize ht₂ : (VOp.vpbroadcastq .l256 .xmm5 .xmm5).exec ((VOp.vmovq .xmm5 .rax).exec t₁) = t₂
  have q₂ : ∀ r j, j < 4 → qw t₂ r j = if r = .xmm5 then selMask (decide (i = v)) else qw t r j := fun r j hj => by
    rw [← ht₂, qw_vpbroadcastq]
    by_cases hr : r = .xmm5
    · subst hr; simp only [qw_vmovq _ _ _ _ (show 0 < 4 by decide), ite_true, m₁]
    · simp only [hr, ite_false, qw_vmovq _ _ _ _ hj, qw_eq_of x₁ y₁]
  have g₂ : t₂.gpr = t₁.gpr := by rw [← ht₂]; rfl
  have e₂ : t₂.mem = t.mem ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr ∧ t₂.mxcsr = t.mxcsr := by
    rw [← ht₂]; exact ⟨me₁, k₁.2.1, k₁.2.2, mx₁⟩
  have r8₂ : t₂.gpr .r8 = base + BitVec.ofNat 64 (160 * i) := by
    rw [g₂, k₁.gpr (by decide)]; exact h.r8
  rw [WP.block_append_iff]
  refine WP.mono (selGroups_ok (a := base + BitVec.ofNat 64 (160 * i)) (msk := selMask (decide (i = v))) r8₂ (fun k hk => by
      rw [e₂.2.1, e₂.2.2.1, h.rd, h.wr, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hin i hi k hk)
    (fun j hj => by simp only [q₂ _ j hj, ite_true]) 5 (Nat.le_refl _))
    fun t₃ ⟨v₃, _, g₃, me₃, rd₃, wr₃, x₃⟩ => ?_
  refine WP.mono (selTail_ok (base := base) hi (by rw [g₃]; exact r8₂)
    (by rw [g₃, g₂, k₁.gpr (by decide)]; exact h.rcx))
    fun t₄ ⟨r8₄, rcx₄, z₄, k₄, me₄, x₄, y₄, mx₄⟩ => ⟨⟨r8₄, rcx₄, fun r r1 r2 r3 => ?_, ?_, ?_, ?_, ?_,
      fun k hk j hj => ?_⟩, z₄⟩
  · rw [k₄.gpr (by simp [r2, r3]), g₃, g₂, k₁.gpr (by simp [r1])]; exact h.gpr r r1 r2 r3
  · rw [me₄, me₃, e₂.1, h.mem]
  · rw [k₄.2.1, rd₃, e₂.2.1, h.rd]
  · rw [k₄.2.2, wr₃, e₂.2.2.1, h.wr]
  · rw [mx₄, x₃, e₂.2.2.2, h.mxcsr]
  · have hx5 := (crt_xr_lt k hk).1
    rw [qw_eq_of x₄ y₄, v₃ k hk j hj]
    simp only [hk, ite_true, q₂ _ j hj, hx5, ite_false]
    rw [h.acc k hk j hj, e₂.1, h.mem, selMask_and]
    by_cases hiv : i = v
    · subst hiv
      simp only [Nat.lt_irrefl, ite_false, decide_true, ite_true, Nat.lt_succ_self, zero_or64]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
    · simp only [hiv, decide_false, Bool.false_eq_true, ite_false, or_zero64]
      by_cases hlt : v < i
      · simp only [hlt, show v < i + 1 by omega, ite_true]
      · simp only [hlt, show ¬ v < i + 1 by omega, ite_false]


/-- The loop over the sixteen entries, from entry `16 - n`. -/
theorem selLoop_ok {t₀ : State} {base : Addr} {v : Nat} (hv : v < 16) (hd : t₀.gpr .rdx = BitVec.ofNat 64 v)
    (hin : ∀ i < 16, ∀ k < 5, InRegions (t₀.rd ++ t₀.wr) (base + BitVec.ofNat 64 (160 * i + 32 * k)) 32) :
    ∀ n t, 1 ≤ n → n ≤ 16 → SelInv t₀ base v (16 - n) t →
      WP isa (.loop (.block selBody) .ne) t (SelInv t₀ base v 16) := by
  intro n t h1 h16 hI
  refine WP.loop (M := isa) (body := .block selBody) (c := .ne) (Q := SelInv t₀ base v 16)
    (fun n t => 1 ≤ n ∧ n ≤ 16 ∧ SelInv t₀ base v (16 - n) t) ?_ n t ⟨h1, h16, hI⟩
  intro n t ⟨h1, h16, hI⟩
  refine WP.mono (selIter_ok hv (by omega) hd hin hI) fun t' ⟨hI', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · exact .inl ⟨by simp, hI'⟩
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (16 - n + 1 = 16) by omega), Bool.not_false], n - 1,
      by omega, by omega, by omega, by rw [show 16 - (n - 1) = 16 - n + 1 by omega]; exact hI'⟩


/-- The zeroing of the five accumulators. -/
def zeros5 : List Instr :=
  (List.range 5).map fun r => .vop (.vbin .vpxor .l256 (VG.Impl.Rsa.X86_64.CrtIfma.xr r)
    (VG.Impl.Rsa.X86_64.CrtIfma.xr r) (VG.Impl.Rsa.X86_64.CrtIfma.xr r))

def checkZeros5 : Bool :=
  match Sym.init.run (fun _ => 0) zeros5 with
  | some σ => (List.range 5).all fun r => decide (σ.reg r = .zero)
  | none => false

theorem checkZeros5_ok : checkZeros5 = true := by decide +kernel

theorem zeros5_ok {s : State} :
    WP isa (.block zeros5) s fun s' =>
      (∀ r < 5, ∀ t < 4, qw s' (VG.Impl.Rsa.X86_64.CrtIfma.xr r) t = 0) ∧ Keeps s s' := by
  have h := checkZeros5_ok
  unfold checkZeros5 at h
  split at h
  · rename_i σ hσ
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    refine WP.mono (run_ok (fun b d n hn hd => absurd hd (by omega)) hσ) fun s' hs => ⟨fun r hr t ht => ?_,
      ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
    · rw [xr_eq r (by omega), hs.reg _ t ht, xi_xr r (by omega), h r hr]; rfl
  · cases h

theorem shr60 (w : BitVec 64) : w >>> 60 = BitVec.ofNat 64 (w.toNat / 2 ^ 60) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by have := w.isLt; omega)]

/-- Writes of 32 bytes within `[o, o + n)` leave the rest. -/
theorem wrList_outside' (B : Addr) {o n : Nat} (hn : o + n ≤ 2 ^ 63) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem), (∀ x ∈ l, o ≤ x.1 ∧ x.1 + 32 ≤ o + n) →
      Outside B o n m (wrList m B l)
  | [], m, _ => Outside.refl B o n m
  | (e, v) :: rest, m, h => by
    have he := h (e, v) (List.mem_cons_self ..)
    exact ((writeW256_outside m B v (by omega)).mono he.1 (by omega)).trans
      (wrList_outside' B hn rest _ fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- The nibble `select` reads: the top 4 bits of the quadword at `oV`. -/
def nib (m : Mem) (B : Addr) (p : Nat) : Nat := (word m B (D * p + oV)).toNat / 2 ^ 60

theorem nib_lt (m : Mem) (B : Addr) (p : Nat) : nib m B p < 16 := by
  unfold nib; have := (word m B (D * p + oV)).isLt; omega

/-- `[S] := T_v` for prime `p`. -/
theorem select_ok {s : State} {B : Addr} {p : Nat} (hp : p < 2) (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D)) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (VG.Impl.Rsa.X86_64.CrtIfma.select p)) s fun s' =>
      (∀ l < 20, limb s'.mem B (D * p + oS) l = limb s.mem B (D * p + oTab + 160 * nib s.mem B p) l) ∧
      Outside B (D * p + oS) 160 s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : D = 3712 := rfl
  have hn := hs.nowrap
  have hDp : D * p ≤ 3712 := by rw [hD]; omega
  have rdS : ∀ d n, 0 < n → d + n ≤ 2 * D → InRegions (s.rd ++ s.wr) (off B d) n := fun d n hn hd =>
    let ⟨_, h, c⟩ := hs.region hd hn; ⟨_, List.mem_append_right _ h, c⟩
  let v := nib s.mem B p
  have hv : v < 16 := nib_lt _ _ _
  let base := off B (D * p + oTab)
  refine WP.seq ?_
  rw [List.append_assoc]
  refine setOff (c := D * p + oTab) (by simp only [oTab]; omega) fun s₁ u₁ => ?_
  rw [hB] at u₁
  change WP isa (.block (([.mov .rdx (.mem (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx (D * p + oV))), .shift .shr .rdx 60,
    .mov32 .rcx (.imm 0)] : List Instr) ++ zeros5)) s₁ _
  rw [WP.block_append_iff]
  have rbx₁ : s₁.gpr .rbx = B := by rw [u₁.other _ (by decide), hB]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 v ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧ t.xmm = s₁.xmm ∧ t.ymmHi = s₁.ymmHi ∧ t.mxcsr = s.mxcsr) (by
    have hld : InRegions (s₁.rd ++ s₁.wr) (B + BitVec.ofNat 64 (D * p + oV)) 8 := by
      rw [u₁.rd, u₁.wr]; exact rdS _ 8 (by decide) (by simp only [VG.Impl.Rsa.X86_64.CrtIfma.oV]; omega)
    xrun [ea_r rbx₁, hld, u₁.mem, shr60]
    and_intros
    any_goals rfl
    · exact u₁.mxcsr) rfl) fun s₂ ⟨⟨dx₂, cx₂, me₂, x₂, y₂, mx₂⟩, k₂⟩ => ?_
  refine WP.mono zeros5_ok fun s₃ ⟨z₃, k₃⟩ => ?_
  have hin : ∀ i < 16, ∀ k < 5, InRegions (s₃.rd ++ s₃.wr) (base + BitVec.ofNat 64 (160 * i + 32 * k)) 32 :=
    fun i hi k hk => by
      rw [k₃.rd, k₃.wr, k₂.2.1, k₂.2.2, u₁.rd, u₁.wr, off_add]
      exact rdS _ 32 (by decide) (by simp only [oTab]; omega)
  have dx₃ : s₃.gpr .rdx = BitVec.ofNat 64 v := by rw [k₃.gpr _ (by decide)]; exact dx₂
  have i₀ : SelInv s₃ base v (16 - 16) s₃ := ⟨by
      rw [k₃.gpr _ (by decide), k₂.gpr (by decide), u₁.self]; exact (BitVec.add_zero _).symm,
    by rw [k₃.gpr _ (by decide)]; exact cx₂, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl,
    fun k hk j hj => by rw [z₃ k hk j hj]; simp⟩
  refine WP.seq (WP.mono (selLoop_ok hv dx₃ hin 16 s₃ (by decide) (Nat.le_refl _) i₀) fun s₄ h₄ => ?_)
  let L : List (Nat × XReg) := (List.range 5).map fun k => (D * p + oS + 32 * k, VG.Impl.Rsa.X86_64.CrtIfma.xr k)
  have rbx₄ : s₄.gpr .rbx = B := by
    rw [h₄.gpr _ (by decide) (by decide) (by decide), k₃.gpr _ (by decide), k₂.gpr (by decide), rbx₁]
  have wr₄ : s₄.wr = s.wr := by rw [h₄.wr, k₃.wr, k₂.2.2, u₁.wr]
  have rd₄ : s₄.rd = s.rd := by rw [h₄.rd, k₃.rd, k₂.2.1, u₁.rd]
  have me₄ : s₄.mem = s.mem := by rw [h₄.mem, k₃.mem, me₂]
  change WP isa (.block (storeCode .rbx L)) s₄ _
  have hL : ∀ x ∈ L, D * p + oS ≤ x.1 ∧ x.1 + 32 ≤ D * p + oS + 160 := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hk; dsimp only; omega
  refine WP.mono (stores_gen L s₄ rbx₄ fun x hx => by
    have := hL x hx
    rw [wr₄]; exact let ⟨_, h, c⟩ := hs.region (d := x.1) (n := 32) (by simp only [oS] at this ⊢; omega) (by decide);
      ⟨_, h, c⟩) fun s' hs' => ?_
  subst hs'
  refine ⟨fun l hl => ?_, ?_, fun r r1 r2 r3 r4 => ?_, rd₄, wr₄, ?_⟩
  · have hk : l % 5 < 5 := Nat.mod_lt _ (by decide)
    have ht : l / 5 < 4 := by omega
    have e := word_wrList_unique B (e := D * p + oS + 32 * (l % 5)) (t := l / 5)
      (v := s₄.ymm (VG.Impl.Rsa.X86_64.CrtIfma.xr (l % 5))) ht (by simp only [oS]; omega)
      (L.map fun x => (x.1, s₄.ymm x.2)) s₄.mem
      (List.mem_map.2 ⟨(D * p + oS + 32 * (l % 5), VG.Impl.Rsa.X86_64.CrtIfma.xr (l % 5)),
        List.mem_map.2 ⟨l % 5, List.mem_range.2 hk, rfl⟩, rfl⟩)
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hy
        rw [List.mem_range] at hk'; dsimp only; simp only [oS]; omega)
      (fun x hx he => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hy
        rw [List.mem_range] at hk'; dsimp only at he ⊢
        rw [show k = l % 5 by omega])
    have q := h₄.acc (l % 5) hk (l / 5) ht
    rw [← qword256_ymm s₄ _ ht] at q
    simp only [hv, ite_true] at q
    show (word (wrList s₄.mem B _) B (D * p + oS + VG.Impl.Rsa.X86_64.CrtIfma.off l)).toNat = _
    rw [off_lim l, ← Nat.add_assoc, e]
    refine congrArg BitVec.toNat (q.trans ?_)
    rw [k₃.mem, me₂, off_add]
    exact congrArg (fun d => s.mem.readW (off B d) 64) (by rw [off_lim l]; omega)
  · have o := wrList_outside' B (o := D * p + oS) (n := 160) (by simp only [oS]; omega)
      (L.map fun x => (x.1, s₄.ymm x.2)) s₄.mem fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact hL y hy
    exact fun x hx => (o x hx).trans (congrFun me₄ x)
  · show s₄.gpr r = _
    rw [h₄.gpr _ r1 r2 r4, k₃.gpr _ r1, k₂.gpr (by simp [r2, r3]), u₁.other _ r4]
  · show s₄.mxcsr = _
    rw [h₄.mxcsr, k₃.mxcsr, mx₂]

end VG.Proof.Bignum.X86_64.AmmSym
