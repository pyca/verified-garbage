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

end VG.Proof.Bignum.X86_64.AmmSym
