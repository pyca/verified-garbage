module

-- separate module: the indices and the prologue, which `ForsSign` does not rebuild when it changes

public import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on x86-64: `forsSign`, its indices

`index t`: index `t` of `base_2b(md, a, k)` from three bytes of `md`
(`index_ok`), and the block of all `k` (`indices_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Fors

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Fors

/-- Three bytes, most significant first, shifted and masked. -/
theorem idx_val (x₀ x₁ x₂ : Byte) {sh a : Nat} (ha : a < 31) :
    ((((x₀.setWidth 64 <<< 16) ||| (x₁.setWidth 64 <<< 8)) ||| x₂.setWidth 64) >>> sh) &&&
        (BitVec.ofNat 32 (2 ^ a - 1)).signExtend 64 =
      BitVec.ofNat 64 ((x₀.toNat * 65536 + x₁.toNat * 256 + x₂.toNat) / 2 ^ sh % 2 ^ a) := by
  have h₀ := x₀.isLt
  have h₁ := x₁.isLt
  have h₂ := x₂.isLt
  have hm : 2 ^ a - 1 < 2 ^ 31 := by have := Nat.pow_lt_pow_right (show 1 < 2 by decide) ha; omega_using [this]
  rw [Levels.sx_ofNat hm]
  apply BitVec.eq_of_toNat_eq
  have e : (x₀.toNat <<< 16 ||| x₁.toNat <<< 8) ||| x₂.toNat = x₀.toNat * 65536 + x₁.toNat * 256 + x₂.toNat := by
    rw [show 16 = 8 + 8 from rfl, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add_eq_or_of_lt h₁,
      ← Nat.shiftLeft_add_eq_or_of_lt h₂, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    omega_using []
  have b₀ : x₀.toNat <<< 16 < 2 ^ 64 := by rw [Nat.shiftLeft_eq]; omega_using [h₀]
  have b₁ : x₁.toNat <<< 8 < 2 ^ 64 := by rw [Nat.shiftLeft_eq]; omega_using [h₁]
  have hlt : x₀.toNat * 65536 + x₁.toNat * 256 + x₂.toNat < 2 ^ 64 := by omega_using [h₀, h₁, h₂]
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show x₀.toNat < 2 ^ 64 by omega_using [h₀]), Nat.mod_eq_of_lt (show x₁.toNat < 2 ^ 64 by omega_using [h₁]),
    Nat.mod_eq_of_lt (show x₂.toNat < 2 ^ 64 by omega_using [h₂]), Nat.mod_eq_of_lt b₀, Nat.mod_eq_of_lt b₁, e,
    Nat.mod_eq_of_lt (show 2 ^ a - 1 < 2 ^ 64 by omega_using [hm]), Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (show (x₀.toNat * 65536 + x₁.toNat * 256 + x₂.toNat) / 2 ^ sh % 2 ^ a < 2 ^ 64 by
      have := Nat.mod_lt ((x₀.toNat * 65536 + x₁.toNat * 256 + x₂.toNat) / 2 ^ sh) (Nat.two_pow_pos a)
      have : 2 ^ a < 2 ^ 31 := Nat.pow_lt_pow_right (by decide) ha
      omega_using [this])]

/-- The value of index `t` from the digest's bytes in `m`. -/
abbrev ixv (m : Mem) (S : Addr) (a t : Nat) : Nat :=
  ((m (at' S (Layout.oDigest + t * a / 8))).toNat * 65536 + (m (at' S (Layout.oDigest + t * a / 8 + 1))).toNat * 256 +
    (m (at' S (Layout.oDigest + t * a / 8 + 2))).toNat) / 2 ^ (24 - t * a % 8 - a) % 2 ^ a

theorem index_ok {S : Addr} {a t : Nat} {u : State} (ha : a ≤ 14) (ht : t * a / 8 + 3 ≤ 64) (ht' : t < 40)
    (hbx : u.gpr .rbx = S) (hbp : u.gpr .rbp = at' S Layout.oDigest) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr) :
    WP isa (.block (index a t)) u fun u' =>
      (∀ g, g ≠ .rax → g ≠ .rcx → u'.gpr g = u.gpr g) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧
      u'.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (ixv u.mem S a t) ∧
      Frame [⟨at' S (Layout.oFidx + 8 * t), 8⟩] u.mem u'.mem := by
  have eD : Layout.oDigest = 30304 := rfl
  have eF : Layout.oFidx = 31328 := rfl
  have hq := Nat.mod_lt (t * a) (show 0 < 8 by decide)
  refine WP.mono_mx (by simp [Code.allInstrs_eq, instrs, index, loadsMxcsr]) (Q := fun u' => u'.mxcsr = u.mxcsr → _) ?_
    fun _ h hm => h hm
  have hin : ∀ (v : State), v.rd = u.rd → v.wr = u.wr → ∀ j, j < 3 →
      InRegions (v.rd ++ v.wr) (at' S (Layout.oDigest + t * a / 8 + j)) 1 := fun v hr hw' j hj => by
    rw [hr, hw']; exact Levels.in_scr' hw (by rw [eD]; omega_using [ht, hj])
  have ea : ∀ (v : State), v.gpr .rbp = at' S Layout.oDigest → ∀ j,
      v.ea (Impl.Sha3.X86_64.at_ .rbp (t * a / 8 + j)) = at' S (Layout.oDigest + t * a / 8 + j) := fun v h j => by
    rw [Proof.Sha3.X86_64.ea_at, h, Levels.add_add, Nat.add_assoc]
  simp only [index]
  refine Proof.Sha3.X86_64.wp_movzx8 (a := at' S (Layout.oDigest + t * a / 8))
    (by rw [Proof.Sha3.X86_64.ea_at, hbp, Levels.add_add]) (by simpa using hin u rfl rfl 0 (by decide))
    fun u₁ e₁ => Levels.wp_shl (by decide) (by decide) fun u₂ e₂ => ?_
  have bp₂ : u₂.gpr .rbp = at' S Layout.oDigest := by rw [e₂.other _ (by decide), e₁.other _ (by decide), hbp]
  refine Proof.Sha3.X86_64.wp_movzx8 (ea u₂ bp₂ 1) (hin u₂ (by rw [e₂.rd, e₁.rd]) (by rw [e₂.wr, e₁.wr]) 1 (by decide))
    fun u₃ e₃ => Levels.wp_shl (by decide) (by decide) fun u₄ e₄ => wp_orr fun u₅ e₅ => ?_
  have bp₅ : u₅.gpr .rbp = at' S Layout.oDigest := by
    rw [e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide), bp₂]
  refine Proof.Sha3.X86_64.wp_movzx8 (ea u₅ bp₅ 2)
    (hin u₅ (by rw [e₅.rd, e₄.rd, e₃.rd, e₂.rd, e₁.rd]) (by rw [e₅.wr, e₄.wr, e₃.wr, e₂.wr, e₁.wr]) 2 (by decide))
    fun u₆ e₆ => wp_orr fun u₇ e₇ => Levels.wp_shr (by omega_using [hq, ha]) (by omega_using []) fun u₈ e₈ =>
    wp_andi fun u₉ e₉ => ?_
  have hbx₉ : u₉.gpr .rbx = S := by
    rw [e₉.other _ (by decide), e₈.other _ (by decide), e₇.other _ (by decide), e₆.other _ (by decide),
      e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide),
      e₁.other _ (by decide), hbx]
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oFidx + 8 * t)) (by rw [Proof.Sha3.X86_64.ea_at, hbx₉])
    (by rw [e₉.wr, e₈.wr, e₇.wr, e₆.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr, e₁.wr]
        exact Levels.in_scr hw (by rw [eF]; omega_using [ht'])) fun u' g' m' r' w' => WP.block_nil fun hmx => ?_
  have hm₉ : u₉.mem = u.mem := by
    rw [e₉.mem, e₈.mem, e₇.mem, e₆.mem, e₅.mem, e₄.mem, e₃.mem, e₂.mem, e₁.mem]
  have hax : u₉.gpr .rax = BitVec.ofNat 64 (ixv u.mem S a t) := by
    rw [e₉.gpr, e₈.gpr, e₇.gpr, e₆.other .rax (by decide), e₆.gpr, e₅.gpr, e₄.other .rax (by decide), e₄.gpr, e₃.gpr,
      e₃.other .rax (by decide), e₂.gpr, e₁.gpr, e₅.mem, e₄.mem, e₃.mem, e₂.mem, e₁.mem,
      idx_val _ _ _ (by omega_using [ha])]
  refine ⟨fun g h₀ h₁ => by
      rw [g', e₉.other _ h₀, e₈.other _ h₀, e₇.other _ h₀, e₆.other _ h₁, e₅.other _ h₀, e₄.other _ h₁, e₃.other _ h₁,
        e₂.other _ h₀, e₁.other _ h₀],
    by rw [r', e₉.rd, e₈.rd, e₇.rd, e₆.rd, e₅.rd, e₄.rd, e₃.rd, e₂.rd, e₁.rd],
    by rw [w', e₉.wr, e₈.wr, e₇.wr, e₆.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr, e₁.wr], hmx,
    by rw [m', Mem.readW_writeW_self64, hax], ?_⟩
  rw [m', hm₉]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- The block of the indices: all `k`, then tree 0 with its signature at `sig`. -/
theorem indices_ok {S : Addr} {a k : Nat} {u : State} (ha : a ≤ 14) (hk : k ≤ 35) (hka : k * a ≤ 8 * 61)
    (hbx : u.gpr .rbx = S) (hbp : u.gpr .rbp = at' S Layout.oDigest) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr) :
    WP isa (.block (indices a k)) u fun u' =>
      (∀ g, g ≠ .rax → g ≠ .rcx → u'.gpr g = u.gpr g) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧
      (∀ i < k, u'.mem.readW (at' S (Layout.oFidx + 8 * i)) 64 = BitVec.ofNat 64 (ixv u.mem S a i)) ∧
      u'.mem.readW (at' S (Layout.oVar 2 0)) 64 = 0 ∧ u'.mem.readW (at' S (Layout.oVar 2 4)) 64 = 0 ∧
      u'.mem.readW (at' S (Layout.oVar 2 1)) 64 = u.gpr .r14 ∧
      Frame [⟨at' S Layout.oFidx, 320⟩, ⟨at' S (Layout.oVar 2 0), 40⟩] u.mem u'.mem := by
  have eF : Layout.oFidx = 31328 := rfl
  have eD : Layout.oDigest = 30304 := rfl
  let P : Nat → State → Prop := fun c v =>
    (∀ g, g ≠ .rax → g ≠ .rcx → v.gpr g = u.gpr g) ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.mxcsr = u.mxcsr ∧
    (∀ i < c, v.mem.readW (at' S (Layout.oFidx + 8 * i)) 64 = BitVec.ofNat 64 (ixv u.mem S a i)) ∧
    (∀ q, q < 2 ^ 16 → q < Layout.oFidx → v.mem (at' S q) = u.mem (at' S q)) ∧
    Frame [⟨at' S Layout.oFidx, 320⟩] u.mem v.mem
  unfold indices
  refine WP.block_append (WP.mono (wp_flatMap (P := P) k ⟨fun _ _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega_using []),
    fun _ _ _ => rfl, Frame.refl _ _⟩ fun c hc v ⟨g, r, w, mx, fi, kd, f⟩ => ?_) fun v ⟨g, r, w, mx, fi, kd, f⟩ => ?_)
  · have hca : c * a / 8 + 3 ≤ 64 := by
      have := Nat.mul_le_mul_right a (show c ≤ k by omega_using [hc]); omega_using [this, hka]
    refine WP.mono (index_ok (S := S) ha hca (by omega_using [hc, hk]) (by rw [g _ (by decide) (by decide), hbx])
      (by rw [g _ (by decide) (by decide), hbp]) (by rw [w]; exact hw)) fun v' ⟨g', r', w', mx', e', f'⟩ => ?_
    have hix : ixv v.mem S a c = ixv u.mem S a c := by
      simp only [ixv]
      rw [kd _ (by rw [eD]; omega_using [hca]) (by rw [eD, eF]; omega_using [hca]),
        kd _ (by rw [eD]; omega_using [hca]) (by rw [eD, eF]; omega_using [hca]),
        kd _ (by rw [eD]; omega_using [hca]) (by rw [eD, eF]; omega_using [hca])]
    have kf : ∀ q, q < 2 ^ 16 → (q < Layout.oFidx + 8 * c ∨ Layout.oFidx + 8 * c + 8 ≤ q) →
        v'.mem (at' S q) = v.mem (at' S q) := fun q hq h => keepS f' fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dS S (by omega_using [h]) (by omega_using [hq]) (by rw [eF]; omega_using [hc, hk])
    refine ⟨fun g'' h₀ h₁ => by rw [g' _ h₀ h₁, g _ h₀ h₁], by rw [r', r], by rw [w', w], by rw [mx', mx],
      fun i hi => ?_, fun q hq h => by rw [kf q hq (.inl (by omega_using [h])), kd q hq h], ?_⟩
    · by_cases e : i = c
      · subst e; rw [e', hix]
      · rw [← fi i (by omega_using [hi, e])]
        exact Mem.readW_congr fun j hj => by
          rw [Levels.add_add]; exact kf _ (by rw [eF]; omega_using [hi, hj, hk, hc])
            (by omega_using [hi, hj, e])
    · exact f.trans (f'.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega_using []) (by rw [eF]; omega_using [hc, hk])⟩)
  · have hb : v.gpr .rbx = S := by rw [g _ (by decide) (by decide), hbx]
    refine WP.mono_mx (by rfl) (Q := fun v' => v'.mxcsr = v.mxcsr → _) ?_ fun _ h hm => h hm
    refine Proof.Sha3.X86_64.wp_mov32i fun v₁ e₁ => ?_
    have hb₁ : v₁.gpr .rbx = S := by rw [e₁.other _ (by decide), hb]
    refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 2 0)) (by rw [var, Proof.Sha3.X86_64.ea_at, hb₁])
      (by rw [e₁.wr, w]; exact Levels.in_scr hw (by rw [oVar2]; omega_using [])) fun v₂ g₂ m₂ r₂ w₂ => ?_
    refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 2 4)) (by rw [var, Proof.Sha3.X86_64.ea_at, g₂, hb₁])
      (by rw [w₂, e₁.wr, w]; exact Levels.in_scr hw (by rw [oVar2]; omega_using [])) fun v₃ g₃ m₃ r₃ w₃ => ?_
    refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 2 1)) (by rw [var, Proof.Sha3.X86_64.ea_at, g₃, g₂, hb₁])
      (by rw [w₃, w₂, e₁.wr, w]; exact Levels.in_scr hw (by rw [oVar2]; omega_using [])) fun v₄ g₄ m₄ r₄ w₄ =>
      WP.block_nil fun hmx => ?_
    have sp : ∀ i j, i ≠ j → i < 9 → j < 9 → Mem.Sep (at' S (Layout.oVar 2 i)) (64 / 8) (at' S (Layout.oVar 2 j)) (64 / 8) :=
      fun i j h hi hj => Offset.sep S (by rw [oVar2, oVar2]; omega_using [h]) (by rw [oVar2]; omega_using [hi])
        (by rw [oVar2]; omega_using [hj])
    have hax : v₁.gpr .rax = 0 := by rw [e₁.gpr]; rfl
    have c : ∀ i, i < 5 → (⟨at' S (Layout.oVar 2 0), 40⟩ : Region).Contains (at' S (Layout.oVar 2 i)) (64 / 8) := fun i hi => by
      rw [show at' S (Layout.oVar 2 i) = at' S (Layout.oVar 2 0) + BitVec.ofNat 64 (8 * i) by rw [Levels.add_add, oVar2, oVar2]]
      exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
    have dfv : ∀ i, Region.Disjoint ⟨at' S (Layout.oFidx + 8 * i), 8⟩ ⟨at' S (Layout.oVar 2 0), 40⟩ ∨ k ≤ i := fun i => by
      by_cases h : i < k
      · exact .inl (dS S (.inr (by rw [oVar2, eF]; omega_using [])) (by rw [eF]; omega_using [h, hk]) (by rw [oVar2]; omega_using []))
      · exact .inr (by omega_using [h])
    have spF : ∀ i, i < k → ∀ j, j < 9 → Mem.Sep (at' S (Layout.oFidx + 8 * i)) (64 / 8) (at' S (Layout.oVar 2 j)) (64 / 8) :=
      fun i hi j hj => Offset.sep S (by rw [oVar2, eF]; omega_using [hj]) (by rw [eF]; omega_using [hi, hk])
        (by rw [oVar2]; omega_using [hj])
    refine ⟨fun g'' h₀ h₁ => by rw [g₄, g₃, g₂, e₁.other _ h₀, g _ h₀ h₁], by rw [r₄, r₃, r₂, e₁.rd, r],
      by rw [w₄, w₃, w₂, e₁.wr, w], by rw [hmx, mx], fun i hi => ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₄, Mem.readW_writeW_sep (spF i hi 1 (by decide)) (by decide), m₃,
        Mem.readW_writeW_sep (spF i hi 4 (by decide)) (by decide), m₂,
        Mem.readW_writeW_sep (spF i hi 0 (by decide)) (by decide), e₁.mem, fi i hi]
    · rw [m₄, Mem.readW_writeW_sep (sp 0 1 (by decide) (by decide) (by decide)) (by decide), m₃,
        Mem.readW_writeW_sep (sp 0 4 (by decide) (by decide) (by decide)) (by decide), m₂, Mem.readW_writeW_self64, hax]
    · rw [m₄, Mem.readW_writeW_sep (sp 4 1 (by decide) (by decide) (by decide)) (by decide), m₃, Mem.readW_writeW_self64,
        g₂, hax]
    · rw [m₄, Mem.readW_writeW_self64, g₃, g₂, e₁.other _ (by decide), g _ (by decide) (by decide)]
    · rw [m₄, m₃, m₂, e₁.mem]
      exact (((f.mono fun r hr => by simp at hr; simp [hr]).writeW (r := ⟨at' S (Layout.oVar 2 0), 40⟩) (by simp) _
        (c 0 (by decide))).writeW (r := ⟨at' S (Layout.oVar 2 0), 40⟩) (by simp) _ (c 4 (by decide))).writeW
        (r := ⟨at' S (Layout.oVar 2 0), 40⟩) (by simp) _ (c 1 (by decide))

/-! ## The prologue and the epilogue -/

theorem oSave2 (i : Nat) : Layout.oSave 2 i = 2656 + 8 * i := rfl

/-- After the prologue. -/
structure ProP (s t : State) : Prop where
  bx : t.gpr .rbx = s.gpr .rdi
  r14 : t.gpr .r14 = s.gpr .rsi
  r12 : t.gpr .r12 = s.gpr .rdx
  bp : t.gpr .rbp = at' (s.gpr .rdi) Layout.oDigest
  r15 : t.gpr .r15 = at' (s.gpr .rdi) Layout.oMsg
  sp : t.gpr .rsp = s.gpr .rsp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mx : t.mxcsr = s.mxcsr
  saved : ∀ i < 6, t.mem.readW (at' (s.gpr .rdi) (Layout.oSave 2 i)) 64 = s.gpr (Impl.SlhDsa.X86_64.savedRegs.getD i .rbx)
  frame : Frame [⟨at' (s.gpr .rdi) (Layout.oSave 2 0), 48⟩] s.mem t.mem

theorem pro_ok {s : State} (hw : (⟨s.gpr .rdi, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block pro) s (ProP s) := by
  have hc : ∀ j < 6, Region.Contains ⟨at' (s.gpr .rdi) (Layout.oSave 2 0), 48⟩ (at' (s.gpr .rdi) (2656 + 8 * j)) 8 :=
    fun j hj => by
      rw [oSave2, show at' (s.gpr .rdi) (2656 + 8 * j) = at' (s.gpr .rdi) (2656 + 8 * 0) + BitVec.ofNat 64 (8 * j) by
        rw [Levels.add_add]]
      exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  refine WP.mono_mx (by rfl) (Q := fun t => t.mxcsr = s.mxcsr → ProP s t) ?_ fun _ h hm => h hm
  unfold pro
  refine WP.block_append (WP.mono (Levels.wp_rangeMap (P := fun j t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ i < j, t.mem.readW (at' (s.gpr .rdi) (Layout.oSave 2 i)) 64 = s.gpr (Impl.SlhDsa.X86_64.savedRegs.getD i .rbx)) ∧
      Frame [⟨at' (s.gpr .rdi) (Layout.oSave 2 0), 48⟩] s.mem t.mem) 6
    ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega_using []), Frame.refl _ _⟩ fun j hj t ⟨g, r, w, sv, f⟩ => ?_) fun t ht => ?_)
  · refine Proof.Sha3.X86_64.wp_store (a := at' (s.gpr .rdi) (Layout.oSave 2 j)) (by rw [Proof.Sha3.X86_64.ea_at, g]) (by
      rw [w, oSave2]; exact Levels.in_scr hw (by omega_using [hj])) fun t' g' m' r' w' => WP.block_nil ?_
    refine ⟨by rw [g', g], by rw [r', r], by rw [w', w], fun i hi => ?_, ?_⟩
    · rw [m']
      by_cases e : i = j
      · subst e; rw [Mem.readW_writeW_self64, g]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by rw [oSave2, oSave2]; omega_using [e, hi, hj]) (by rw [oSave2]; omega_using [hi, hj])
          (by rw [oSave2]; omega_using [hj])) (by decide), sv i (by omega_using [hi, e])]
    · rw [m']
      exact f.writeW (List.mem_singleton_self _) _ (by rw [oSave2]; exact hc j hj)
  obtain ⟨g, r, w, sv, f⟩ := ht
  refine Proof.Sha3.X86_64.wp_mov fun t₁ u₁ => Proof.Sha3.X86_64.wp_mov fun t₂ u₂ => Proof.Sha3.X86_64.wp_mov fun t₃ u₃ =>
    Proof.Sha3.X86_64.wp_mov fun t₄ u₄ => Proof.Sha3.X86_64.wp_addi fun t₅ u₅ => Proof.Sha3.X86_64.wp_mov fun t₆ u₆ =>
    Proof.Sha3.X86_64.wp_addi fun t₇ u₇ => WP.block_nil fun hmx => ?_
  have hm : t₇.mem = t.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, r],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, w], hmx, fun i hi => by rw [hm]; exact sv i hi, by rw [hm]; exact f⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, g]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), g]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), g]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), g, Levels.sx_ofNat (by decide)]
  · rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), g, Levels.sx_ofNat (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g]

/-- The epilogue: the callee-saved registers from frame 2. -/
theorem restore_ok {σ t : State} {S : Addr} (hbx : t.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr)
    (hsv : ∀ i < 6, t.mem.readW (at' S (Layout.oSave 2 i)) 64 = σ.gpr (Impl.SlhDsa.X86_64.savedRegs.getD i .rbx))
    (hsp : t.gpr .rsp = σ.gpr .rsp) {Q : State → Prop}
    (k : ∀ t', t'.mem = t.mem → t'.mxcsr = t.mxcsr → t'.rd = t.rd → t'.wr = t.wr → (∀ r ∈ calleeSaved, t'.gpr r = σ.gpr r) → Q t') :
    WP isa (.block (Impl.SlhDsa.X86_64.restoreRegs 2)) t Q := by
  have hin : ∀ (u : State), u.rd = t.rd → u.wr = t.wr → ∀ i < 6, InRegions (u.rd ++ u.wr) (at' S (Layout.oSave 2 i)) 8 :=
    fun u hr hw' i hi => by rw [hr, hw']; exact Levels.in_scr' hw (by rw [oSave2]; omega_using [hi])
  refine WP.mono_mx rfl (Q := fun u => u.mxcsr = t.mxcsr → Q u) ?_ fun _ h hm => h hm
  rw [show Impl.SlhDsa.X86_64.restoreRegs 2 = [Instr.mov .r15 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 2 5))),
    .mov .r14 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 2 4))), .mov .r13 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 2 3))),
    .mov .r12 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 2 2))), .mov .rbp (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 2 1))),
    .mov .rbx (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 2 0)))] from rfl]
  refine Proof.Sha3.X86_64.wp_movm (by rw [Proof.Sha3.X86_64.ea_at, hbx]) (hin t rfl rfl 5 (by decide)) fun t₁ u₁ => ?_
  refine Proof.Sha3.X86_64.wp_movm (by rw [Proof.Sha3.X86_64.ea_at, u₁.other _ (by decide), hbx]) (hin _ u₁.rd u₁.wr 4 (by decide)) fun t₂ u₂ => ?_
  refine Proof.Sha3.X86_64.wp_movm (by rw [Proof.Sha3.X86_64.ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) 3 (by decide)) fun t₃ u₃ => ?_
  refine Proof.Sha3.X86_64.wp_movm (by rw [Proof.Sha3.X86_64.ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) 2 (by decide)) fun t₄ u₄ => ?_
  refine Proof.Sha3.X86_64.wp_movm (by rw [Proof.Sha3.X86_64.ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 1 (by decide)) fun t₅ u₅ => ?_
  refine Proof.Sha3.X86_64.wp_movm (by rw [Proof.Sha3.X86_64.ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 0 (by decide))
    fun t₆ u₆ => WP.block_nil fun hmx => ?_
  have hm₁ : t₁.mem = t.mem := u₁.mem
  have hm₂ : t₂.mem = t.mem := by rw [u₂.mem, hm₁]
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, hm₂]
  have hm₄ : t₄.mem = t.mem := by rw [u₄.mem, hm₃]
  have hm₅ : t₅.mem = t.mem := by rw [u₅.mem, hm₄]
  refine k t₆ (by rw [u₆.mem, hm₅]) hmx (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) fun r hr => ?_
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [u₆.gpr, hm₅]; exact hsv 0 (by decide)
  · rw [u₆.other _ (by decide), u₅.gpr, hm₄]; exact hsv 1 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hsp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hm₃]; exact hsv 2 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hm₂]
    exact hsv 3 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hm₁]
    exact hsv 4 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
    exact hsv 5 (by decide)

end VG.Proof.SlhDsa.X86_64.Fors
