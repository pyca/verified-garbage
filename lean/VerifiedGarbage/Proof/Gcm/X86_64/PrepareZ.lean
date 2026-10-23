module

public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareCT
public import VerifiedGarbage.Impl.Gcm.X86_64.PrepareZ
import VerifiedGarbage.Proof.Gcm.X86_64.Prepare16
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pow
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Bcast
import VerifiedGarbage.Proof.Framework.X86_64.ZFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Preparing a key context's powers on 512-bit registers

`prepare_ok`: `PrepareZ.prepare` writes the 48 prepared powers. Pairs 0–7
are `Prepare16.prepare16`'s (`Prepare16.setup_ok`, `Prepare16.plan_ok`); each
table (`StitchZ.table_ok`, with `r11` at pair 0) multiplies pairs 0–7, lane
by lane, by the power it broadcasts (`H'¹⁶`, then `H'³²`, which the first
table stored), and a reduced product of two prepared powers is the prepared
power of their sum (`prod_prepared`). `prepare_verified`:
`Spec.Gcm.prepareContract`, with the constant time of `PrepareCT.lean`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.PrepareZ

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.PrepareZ (table prepare)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB eq_prepared x_φ_prepared φ_reduceB)
open VG.Proof.Gcm.X86_64.Stitch (setupG_ok' storesK_ok in_sub_int)
open VG.Proof.Gcm.X86_64.Prepare (PrepOk stored vzu_ok pregs_rev_length verified_of)
open VG.Spec.Gcm (Block hpow)

/-- A reduced product of two prepared powers is the prepared power of their
sum. -/
theorem prod_prepared {H a b : Block} {m n : Nat} (ha : a = Spec.Gcm.preparedPower (hpow H m))
    (hb : b = Spec.Gcm.preparedPower (hpow H n)) :
    reduceB (Prod.zero.acc a b) = Spec.Gcm.preparedPower (hpow H (m + n)) := by
  apply eq_prepared
  rw [φ_reduceB, Prod.val_acc, Prod.val_zero, zero_add, pow_add, ← x_φ_prepared H m, ← x_φ_prepared H n, ha, hb]
  grind

/-- `mov r11, rdi; add r11, 256`. -/
theorem r11_ok (s : State) :
    WP isa (.block [.mov .r11 (.reg .rdi), .alu .add .r11 (.imm 256)]) s fun s' =>
      s'.gpr .r11 = s.gpr .rdi + BitVec.ofNat 64 256 ∧ (∀ q, q ≠ .r11 → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.zlane x l = s.zlane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : BitVec.signExtend 64 (256 : BitVec 32) = BitVec.ofNat 64 256 := by decide
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, State.setReg, e, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, fun q hq => by simp only [hq, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `PrepareZ.prepare`: the 48 prepared powers of the hash subkey at `C + 240`
into pairs 0–23 of the context at `C`, nothing else written. -/
theorem prepare_ok {s₀ : State} (hw : InRegions s₀.wr (s₀.gpr .rdi) 1024)
    (hwrap : (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64) :
    WP isa prepare s₀ (PrepOk s₀) := by
  set C := s₀.gpr .rdi with hC
  set H := Spec.Gcm.ctxH s₀.mem C with hH
  have hk : InRegions (s₀.rd ++ s₀.wr) C 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, by simp only [Region.Contains] at hc ⊢; omega_arith⟩
  simp only [prepare, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Prepare16.setup_ok s₀ hw hwrap) fun s₁ ⟨hi₁, g₁, rd₁, wr₁⟩ => ?_
  -- Pairs 0–7.
  rw [WP.block_append_iff]
  refine WP.mono (Prepare16.plan_ok _ _ _ s₁ Prepare16.plan_valid hi₁) fun s₂ ⟨⟨_, hi₂⟩, g₂, rd₂, wr₂⟩ => ?_
  have P0' : ∀ i < 8, ∀ l < 2, s₂.mem.readW (C + BitVec.ofNat 64 (256 + 32 * i + 16 * l)) 128 =
      Spec.Gcm.preparedPower (hpow H (2 * i + 2 - l)) := fun i hi l hl =>
    (hi₂.st i (Prepare16.plan_stored i hi)).2 l hl
  -- The reduction constant in every lane of `zmm1`.
  rw [WP.block_append_iff]
  refine WP.mono (Proof.AesGcm.X86_64.Short.bcast_ok .xmm1 s₂) fun s₃ ⟨b₃, f₃⟩ => ?_
  have h1₃ : ∀ l < 4, s₃.zlane .xmm1 l = poly := fun l hl => by
    rw [b₃ l hl]
    have := hi₂.h1 0 (by decide)
    simpa [State.lane] using this
  -- `r11` at pair 0.
  rw [WP.block_append_iff]
  refine WP.mono (r11_ok s₃) fun s₄ ⟨e₄, g₄, z₄, m₄, rd₄, wr₄⟩ => ?_
  have c₄ : s₄.gpr .rdi = C := by rw [g₄ _ (by decide), f₃.gpr, g₂ _ (by decide), g₁ _ (by decide)]
  have q₄ : s₄.gpr .r11 = C + BitVec.ofNat 64 256 := by rw [e₄, f₃.gpr, g₂ _ (by decide), g₁ _ (by decide)]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, f₃.wr, wr₂, wr₁]
  have mem₄ : s₄.mem = s₂.mem := by rw [m₄, f₃.mem]
  have hin₄ : InRegions s₄.wr (s₄.gpr .r11) 768 := by
    rw [wr₄', q₄]; exact Stitch.in_sub hw (by decide)
  have h1₄ : ∀ l < 4, s₄.zlane .xmm1 l = poly := fun l hl => by rw [z₄]; exact h1₃ l hl
  -- The address of pair `i`, lane `l`, from `r11`.
  have addr : ∀ o i l : Nat, C + BitVec.ofNat 64 256 + BitVec.ofNat 64 (o + (32 * i + 16 * l)) =
      C + BitVec.ofNat 64 (256 + o + 32 * i + 16 * l) := fun o i l => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  -- The powers at `r11`, as `table_ok` reads them.
  have src₄ : ∀ k < 4, ∀ l < 4, StitchZ.pw16 s₄ k l =
      Spec.Gcm.preparedPower (hpow H (2 * (2 * k + l / 2) + 2 - l % 2)) := fun k hk l hl => by
    have := P0' (2 * k + l / 2) (by omega_arith) (l % 2) (by omega_arith)
    rw [StitchZ.pw16, q₄, mem₄, show 64 * k + 16 * l = 0 + (32 * (2 * k + l / 2) + 16 * (l % 2)) by omega_arith, addr]
    rw [show 256 + 0 + 32 * (2 * k + l / 2) + 16 * (l % 2) = 256 + 32 * (2 * k + l / 2) + 16 * (l % 2) by omega_arith]
    exact this
  -- Pairs 8–15.
  rw [WP.block_append_iff]
  refine WP.mono (StitchZ.table_ok 256 224 (L := 768) (by decide) (by decide) (by decide) (by decide) s₄ hin₄ h1₄)
    fun s₅ ⟨g₅, rd₅, wr₅, f₅, e₅, x₅⟩ => ?_
  have v16 : s₄.mem.readW (C + BitVec.ofNat 64 256 + BitVec.ofNat 64 224) 128 =
      Spec.Gcm.preparedPower (hpow H 16) := by
    have := P0' 7 (by decide) 0 (by decide)
    rw [mem₄, show (224 : Nat) = 0 + (32 * 7 + 16 * 0) by rfl, addr]
    exact this
  have T1 : ∀ k < 4, ∀ l < 4, s₅.mem.readW (C + BitVec.ofNat 64 (256 + 256 + 64 * k + 16 * l)) 128 =
      Spec.Gcm.preparedPower (hpow H (2 * (2 * k + l / 2) + 2 - l % 2 + 16)) := fun k hk l hl => by
    have := e₅ k hk l hl
    rw [q₄, show 256 + 64 * k + 16 * l = 256 + (32 * (2 * k + l / 2) + 16 * (l % 2)) by omega_arith, addr,
      src₄ k hk l hl, v16, prod_prepared rfl rfl] at this
    rw [show 256 + 256 + 64 * k + 16 * l = 256 + 256 + 32 * (2 * k + l / 2) + 16 * (l % 2) by omega_arith]
    exact this
  -- Pairs 16–23.
  have q₅ : s₅.gpr .r11 = C + BitVec.ofNat 64 256 := by rw [g₅, q₄]
  have h1₅ : ∀ l < 4, s₅.zlane .xmm1 l = poly := fun l hl => by
    rw [x₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl]; exact h1₄ l hl
  rw [WP.block_append_iff]
  refine WP.mono (StitchZ.table_ok 512 480 (L := 768) (by decide) (by decide) (by decide) (by decide) s₅
    (by rw [g₅, wr₅]; exact hin₄) h1₅) fun s₆ ⟨g₆, rd₆, wr₆, f₆, e₆, x₆⟩ => ?_
  -- The first table kept the powers at `r11`.
  have src₅ : ∀ k < 4, ∀ l < 4, StitchZ.pw16 s₅ k l = StitchZ.pw16 s₄ k l := fun k hk l hl => by
    simp only [StitchZ.pw16, g₅]
    exact StitchZ.keep256 f₅ (by omega_arith) (by decide) (by omega_arith)
  have v32 : s₅.mem.readW (C + BitVec.ofNat 64 256 + BitVec.ofNat 64 480) 128 =
      Spec.Gcm.preparedPower (hpow H 32) := by
    have := T1 3 (by decide) 2 (by decide)
    rw [ show (480 : Nat) = 256 + (32 * 7 + 16 * 0) by rfl, addr]
    exact this
  have T2 : ∀ k < 4, ∀ l < 4, s₆.mem.readW (C + BitVec.ofNat 64 (256 + 512 + 64 * k + 16 * l)) 128 =
      Spec.Gcm.preparedPower (hpow H (2 * (2 * k + l / 2) + 2 - l % 2 + 32)) := fun k hk l hl => by
    have := e₆ k hk l hl
    rw [q₅, show 512 + 64 * k + 16 * l = 512 + (32 * (2 * k + l / 2) + 16 * (l % 2)) by omega_arith, addr,
      src₅ k hk l hl, src₄ k hk l hl, v32, prod_prepared rfl rfl] at this
    rw [show 256 + 512 + 64 * k + 16 * l = 256 + 512 + 32 * (2 * k + l / 2) + 16 * (l % 2) by omega_arith]
    exact this
  refine WP.mono (vzu_ok s₆) fun s ⟨g, m, rd, wr⟩ => ⟨fun k hk l hl => ?_, ?_, fun r hr h11 => ?_, ?_, ?_⟩
  · -- Each pair from its table, kept by the later one.
    rw [m]
    have keep : ∀ {t t' : State} {o : Nat}, Frame [⟨C + BitVec.ofNat 64 256 + BitVec.ofNat 64 o, 256⟩] t.mem t'.mem →
        256 + 32 * k + 16 * l + 16 ≤ 256 + o ∨ 256 + o + 256 ≤ 256 + 32 * k + 16 * l → o + 256 ≤ 768 →
        t'.mem.readW (C + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 =
          t.mem.readW (C + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 := fun {t t' o} f h ho => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add] at f
      exact StitchZ.keep256 f (by omega_arith) (by omega_arith) (by omega_arith)
    rw [q₅] at f₆
    rw [q₄] at f₅
    rcases (by omega_arith : k < 8 ∨ (8 ≤ k ∧ k < 16) ∨ 16 ≤ k) with h | ⟨h, h'⟩ | h
    · rw [keep f₆ (by omega_arith) (by decide), keep f₅ (by omega_arith) (by decide), mem₄]
      exact P0' k h l hl
    · rw [keep f₆ (by omega_arith) (by decide)]
      have := T1 ((k - 8) / 2) (by omega_arith) (2 * ((k - 8) % 2) + l) (by omega_arith)
      rw [show 256 + 256 + 64 * ((k - 8) / 2) + 16 * (2 * ((k - 8) % 2) + l) = 256 + 32 * k + 16 * l by omega_arith,
        show 2 * (2 * ((k - 8) / 2) + (2 * ((k - 8) % 2) + l) / 2) + 2 - (2 * ((k - 8) % 2) + l) % 2 + 16 =
          2 * k + 2 - l by omega_arith] at this
      exact this
    · have := T2 ((k - 16) / 2) (by omega_arith) (2 * ((k - 16) % 2) + l) (by omega_arith)
      rw [show 256 + 512 + 64 * ((k - 16) / 2) + 16 * (2 * ((k - 16) % 2) + l) = 256 + 32 * k + 16 * l by omega_arith,
        show 2 * (2 * ((k - 16) / 2) + (2 * ((k - 16) % 2) + l) / 2) + 2 - (2 * ((k - 16) % 2) + l) % 2 + 32 =
          2 * k + 2 - l by omega_arith] at this
      exact this
  · rw [m]
    have sub : ∀ {a : Nat}, a + 256 ≤ 1024 → 256 ≤ a → ∀ r ∈ [(⟨C + BitVec.ofNat 64 a, 256⟩ : Region)],
        ∃ r' ∈ [(⟨C + BitVec.ofNat 64 256, 768⟩ : Region)], Region.Sub r r' := fun h h' r hr =>
      ⟨_, List.mem_singleton_self _, by obtain rfl := List.mem_singleton.mp hr; exact Offset.sub C h' (by omega_arith)⟩
    have e5 : C + BitVec.ofNat 64 256 + BitVec.ofNat 64 256 = C + BitVec.ofNat 64 512 := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have e6 : C + BitVec.ofNat 64 256 + BitVec.ofNat 64 512 = C + BitVec.ofNat 64 768 := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [q₄, e5] at f₅
    rw [q₅, e6] at f₆
    exact ((hi₂.fr.sub (sub (by decide) (by decide))).trans (by rw [← mem₄]; exact f₅.sub (sub (by decide) (by decide)))).trans
      (f₆.sub (sub (by decide) (by decide)))
  · rw [g, g₆, g₅, g₄ r h11, f₃.gpr, g₂ r hr, g₁ r hr]
  · rw [rd, rd₆, rd₅, rd₄, f₃.rd, rd₂, rd₁]
  · rw [wr, wr₆, wr₅, wr₄']

theorem prepare_verified : Verified X86_64.target prepare (Spec.Gcm.prepareContract X86_64.abi) :=
  verified_of prepare (fun _ hw hwrap => prepare_ok hw hwrap) (by decide +kernel) Prepare.prepareZ_ct

end VG.Proof.Gcm.X86_64.PrepareZ
