import VerifiedGarbage.Proof.Bignum.X86_64.AmmSpec

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

end VG.Proof.Bignum.X86_64.AmmSym
