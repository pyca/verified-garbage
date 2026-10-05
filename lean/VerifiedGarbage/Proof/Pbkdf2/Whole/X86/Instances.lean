import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
import VerifiedGarbage.Proof.Framework.TaintBatch

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Key`. -/
section

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the prologue and the key

The prologue saves our caller's registers in `scratch` (`save_ok`, which is
`VG.Proof.Pbkdf2.Stream.X86.save_ok` for any amount of working space before the
save area); then the key is the password, or its digest if it is longer than a
block (`key_ok`): either gives the same `K₀` (`KeyAt`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK SavedRegs saveR InitArgs UpdArgs FinArgs init_frame upd_frame fin_frame
  saveList_ok saveMem_frameR saveMem_read saved_mem saved_pairwise zero_append_ofNat)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_mov wp_movi wp_movm wp_cmpi wp_test wp_addi wp_bswap wp_store)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey)

variable {F : Fns}

/-- Saving the registers, with `scratch` in `eax`: `VG.Proof.Pbkdf2.Stream.X86.save_ok`, for any `H.W`. -/
theorem save_ok (H : VG.Impl.Pbkdf2.Stream.X86.Hash) {s : State} {sc : BitVec 32} {L : Nat} (hax : s.gpr .eax = sc)
    (hsc : ⟨sc.setWidth 64, L⟩ ∈ s.wr) (hL : 8 * H.W + 16 ≤ L) (hfit : sc.toNat + L ≤ 2 ^ 32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      Frame [saveR H sc] s.mem s'.mem → SavedRegs H sc s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  rw [Pbkdf2.Stream.X86.save_eq]
  refine saveList_ok H.saved s Q (fun p hp => ?_) fun s' g rd wr m => k s' g rd wr ?_ ?_
  · obtain ⟨h₁, h₂⟩ := saved_mem H hp
    rw [hax]
    exact ⟨by omega, ⟨_, hsc, VG.Proof.Sha256.X86.contains_offset (by omega) (by omega)⟩⟩
  · rw [m, hax]
    exact saveMem_frameR _ _ _ _ (by omega) _ _ fun p hp => saved_mem H hp
  · intro p hp
    rw [m, hax]
    exact saveMem_read _ _ _ _ (saved_pairwise H) (fun q hq => by have := saved_mem H hq; omega) p hp

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F)
include hp hz

/-! ## The prologue -/

theorem prologue_ok : WP isa (.block F.prologue) s₀ (VG.Proof.Pbkdf2.Whole.X86.KR F s₀) := by
  have hL := end_le hz; have := layout (F := F)
  have hsc := sc_mem hp
  simp only [Fns.prologue, List.cons_append]
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 7) (argW rfl 7) (VG.Proof.Pbkdf2.Whole.X86.argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine VG.Proof.Pbkdf2.Whole.X86.save_ok F.L (sc := VG.Proof.Pbkdf2.Whole.X86.scr s₀) (L := F.L8) u₁.gpr (by rw [u₁.wr]; exact hsc)
    (by show 8 * F.W + 16 ≤ F.L8; omega) hp.nsc fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₃ u₃ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  refine ⟨by rw [u₃.rd, rd₂, u₁.rd], by rw [u₃.wr, wr₂, u₁.wr], by rw [u₃.other _ (by decide), e₂ _ (by decide)],
    by rw [u₃.gpr, g₂, u₁.gpr]; rfl, ?_, ?_⟩
  · rw [u₃.mem]
    exact sv₂.of_eq F.L fun r hr => u₁.other r (by
      simp only [Pbkdf2.Stream.X86.savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)
  · rw [u₃.mem, ← u₁.mem]
    exact f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.Whole.X86.scR s₀ F, by simp, sv_sub hz⟩

/-! ## The stack and `scratch`, while `KR` holds -/

omit hz in
theorem stk48_sub {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) : Region.Sub (Pbkdf2.Stream.X86.stk s) (VG.Proof.Pbkdf2.Whole.X86.stkR s₀) := by
  rw [Pbkdf2.Stream.X86.stk, hk.esp]; exact below_sub (by decide) hp.sp76

omit hz in
/-- A region of `scratch` is apart from the stack below `esp`. -/
theorem b76 {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {R : Region} (hR : Region.Sub R (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F)) :
    (stk s).Disjoint R := by
  rw [hk.stkE]; exact hp.b_s.sub_right hR

omit hz in
theorem b48 {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {R : Region} (hR : Region.Sub R (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F)) :
    (Pbkdf2.Stream.X86.stk s).Disjoint R :=
  (hp.b_s.sub_left (VG.Proof.Pbkdf2.Whole.X86.stk48_sub hp hk)).sub_right hR

omit hz in
/-- A part of `scratch`, as `Covers.of_sub` takes it. -/
theorem cov_part {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {o n : Nat} (h : o + n ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨VG.Proof.Pbkdf2.Whole.X86.scR s₀ F, by rw [hk.wr]; exact sc_mem hp, o, rfl, h⟩

omit hz in
theorem cov_low {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {k : Nat} (h : k ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (lowR s₀ k).base = r'.base + BitVec.ofNat 64 off ∧ off + (lowR s₀ k).len ≤ r'.len :=
  ⟨VG.Proof.Pbkdf2.Whole.X86.scR s₀ F, by rw [hk.wr]; exact sc_mem hp, 0, by simp, by simp only [Nat.zero_add]; exact h⟩

omit hz in
theorem cov_pw {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) : Covers [pwR s₀] (s.rd ++ s.wr) :=
  Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))

omit hz in
theorem cov_salt {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) : Covers [saltR s₀] (s.rd ++ s.wr) :=
  Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))

/-! ## Hashing a password longer than a block -/

variable (hH : HashOK F.H)
include hH

omit hp hz hH in
/-- `edi ← scratch + stWO`. -/
theorem hk1_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stWO)) s fun t =>
      VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stWO ∧ t.mem = s.mem := by
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stWO)]
  exact scr_ok hk fun s₁ u₁ => WP.block_nil ⟨hk.upd (by decide) u₁, u₁.gpr, u₁.mem⟩

omit hH in
theorem hk2_args {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    InitArgs (H := F.H) s .edi (dO s₀ F.stWO) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D
  have ea := dO_addr hp (o := F.stWO) (by omega)
  refine ⟨hdi, by decide, by rw [hk.esp]; have := hp.sp76; omega, ?_, ?_, ?_⟩
  · rw [ea]; exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (by omega)
  · rw [ea]; exact VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (part_sub (by omega))
  · rw [dO_toNat hp (by omega)]; have := hp.nsc; omega

theorem hk2_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    WP isa (F.H.callInit .edi) s fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ hH.SH.Repr t.mem (A s₀ F.stWO) [] ∧
      t.gpr .edi = s.gpr .edi := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S
  have ea := dO_addr hp (o := F.stWO) (by omega)
  refine init_frame hH (VG.Proof.Pbkdf2.Whole.X86.hk2_args hp hz hk hdi) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, by rw [← ea]; exact r, a.cs _ (by decide)⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩

omit hz hH in
/-- `update`'s arguments: the password. -/
theorem hk3_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    WP isa (.block [.mov .eax (.imm 0), .mov .esi (.imm 0), .mov .ecx (Fns.argM 1), .mov .edx (Fns.argM 0)]) s
      fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stWO ∧ t.gpr .esi = 0 ∧ t.gpr .eax = 0 ∧
        t.gpr .ecx = VG.X86.arg s₀ 1 ∧ t.gpr .edx = pw s₀ ∧ t.mem = s.mem := by
  refine VG.Proof.Sha256.X86.Stream.wp_movi fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_movi fun s₂ u₂ => ?_
  have k₂ := (hk.upd (by decide) u₁).upd (by decide) u₂
  refine wp_arg hp k₂ (by decide) fun s₃ u₃ => ?_
  have k₃ := k₂.upd (by decide) u₃
  refine wp_arg hp k₃ (by decide) fun s₄ u₄ => WP.block_nil ?_
  refine ⟨k₃.upd (by decide) u₄, ?_, ?_, ?_, ?_, u₄.gpr, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.gpr]

theorem hk4_args {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hsi : s.gpr .esi = 0)
    (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = VG.X86.arg s₀ 1) (hdx : s.gpr .edx = pw s₀) :
    UpdArgs hH s .esi .edi (dO s₀ F.stWO) (pw s₀) (VG.Proof.Pbkdf2.Whole.X86.scr s₀) 0 (pwl s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  exact
    { hst := hdi
      hlo := hsi
      eax := hax
      ecx := by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      hl := by decide
      hlen := (VG.X86.arg s₀ 1).isLt
      sp48 := by rw [hk.esp]; have := hp.sp76; omega
      cd := VG.Proof.Pbkdf2.Whole.X86.cov_pw hp hk
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_low hp hk (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega) (by omega)).symm
      d_st := by rw [ea]; exact hp.pw_s.sub_right (part_sub (by omega))
      d_sc := hp.pw_s.sub_right (low_sub (by omega))
      b_st := by rw [ea]; exact VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (part_sub (by omega))
      b_d := hp.b_pw.sub_left (VG.Proof.Pbkdf2.Whole.X86.stk48_sub hp hk)
      b_sc := VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nd := hp.npw
      nsc := by have := hp.nsc; omega }

theorem hk4_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hsi : s.gpr .esi = 0)
    (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = VG.X86.arg s₀ 1) (hdx : s.gpr .edx = pw s₀)
    (hr : hH.SH.Repr s.mem (A s₀ F.stWO) []) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)) s
      fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ hH.SH.Repr t.mem (A s₀ F.stWO) (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀)) ∧
        t.gpr .edi = s.gpr .edi := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  refine upd_frame hH (VG.Proof.Pbkdf2.Whole.X86.hk4_args hp hz hH hk hdi hsi hax hcx hdx) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, ?_, a.cs _ (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · have := r [] (by rw [ea]; exact hr) rfl
    rwa [List.nil_append, ea, hk.pwBytes hp] at this

omit hz hH in
/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    WP isa (.block (([.mov .eax (Fns.argM 1), .mov .ecx (.imm 0)] : List Instr) ++
      VG.Impl.Pbkdf2.Stream.X86.scr .edx F.hkO)) s
      fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stWO ∧ t.gpr .eax = VG.X86.arg s₀ 1 ∧ t.gpr .ecx = 0 ∧
        t.gpr .edx = dO s₀ F.hkO ∧ t.mem = s.mem := by
  simp only [List.cons_append, List.nil_append]
  refine wp_arg hp hk (by decide) fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_movi fun s₂ u₂ => ?_
  have k₂ := (hk.upd (by decide) u₁).upd (by decide) u₂
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.hkO)]
  refine scr_ok k₂ fun s₃ u₃ => WP.block_nil ⟨k₂.upd (by decide) u₃, ?_, ?_, ?_, u₃.gpr, by
    rw [u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr]

theorem hk6_args {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hax : s.gpr .eax = VG.X86.arg s₀ 1)
    (hcx : s.gpr .ecx = 0) (hdx : s.gpr .edx = dO s₀ F.hkO) :
    FinArgs hH s .edi (dO s₀ F.stWO) (dO s₀ F.hkO) (VG.Proof.Pbkdf2.Whole.X86.scr s₀) (VG.X86.arg s₀ 1) 0 := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have eh := dO_addr hp (o := F.hkO) (by omega)
  exact
    { hst := hdi
      eax := hax
      ecx := hcx
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      sp48 := by rw [hk.esp]; have := hp.sp76; omega
      cw := by
        rw [ea, eh]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_low hp hk (by omega)
      st_o := by rw [ea, eh]; exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega) (by omega)).symm
      o_sc := by rw [eh]; exact (low_disj hz (k := hH.Wb) (by omega) (by omega)).symm
      b_st := by rw [ea]; exact VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (part_sub (by omega))
      b_o := by rw [eh]; exact VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (part_sub (by omega))
      b_sc := VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      no := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nsc := by have := hp.nsc; omega }

theorem hk6_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hax : s.gpr .eax = VG.X86.arg s₀ 1)
    (hcx : s.gpr .ecx = 0) (hdx : s.gpr .edx = dO s₀ F.hkO)
    (hr : hH.SH.Repr s.mem (A s₀ F.stWO) (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀))) :
    WP isa (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call F.H.finN F.H.finC) (.pop .eax 5)) s
      fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧
        bytesAt t.mem (A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have eh := dO_addr hp (o := F.hkO) (by omega)
  refine fin_frame hH (VG.Proof.Pbkdf2.Whole.X86.hk6_args hp hz hH hk hdi hax hcx hdx) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
    · exact .inr ⟨_, _, by rw [eh], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · rw [bytesAt_take _ _ hz.D.2.1, ← eh]
    exact r _ (by rw [ea]; exact hr) (by rw [bytesAt_length]; exact Nat.lt_trans (VG.X86.arg s₀ 1).isLt (by decide))
      (by rw [bytesAt_length, ← zero_append_ofNat (VG.X86.arg s₀ 1).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp hz hH in
theorem hk7_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.hkO ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 F.H.D))] : List Instr))) s
      fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ t.gpr .edx = dO s₀ F.hkO ∧ t.gpr .ecx = BitVec.ofNat 32 F.H.D ∧ t.mem = s.mem :=
  scr_ok hk fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_movi fun s₂ u₂ => WP.block_nil ⟨(hk.upd (by decide) u₁).upd (by decide) u₂,
    by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr, by rw [u₂.mem, u₁.mem]⟩

theorem hashKey_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) :
    WP isa F.hashKey s fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ t.gpr .edx = dO s₀ F.hkO ∧ t.gpr .ecx = BitVec.ofNat 32 F.H.D ∧
      bytesAt t.mem (A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀)) := by
  unfold Fns.hashKey
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk1_ok hk) fun s₁ ⟨k₁, d₁, _⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂, e₂⟩ => ?_)
  have d₂ : s₂.gpr .edi = dO s₀ F.stWO := e₂.trans d₁
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk3_ok hp k₂ d₂) fun s₃ ⟨k₃, d₃, i₃, a₃, c₃, x₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk4_ok hp hz hH k₃ d₃ i₃ a₃ c₃ x₃ (by rw [m₃]; exact r₂)) fun s₄ ⟨k₄, r₄, e₄⟩ => ?_)
  have d₄ : s₄.gpr .edi = dO s₀ F.stWO := e₄.trans d₃
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk5_ok hp k₄ d₄) fun s₅ ⟨k₅, d₅, a₅, c₅, x₅, m₅⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk6_ok hp hz hH k₅ d₅ a₅ c₅ x₅ (by rw [m₅]; exact r₄)) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk7_ok k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

/-! ## The key -/

omit hH in
theorem cmp_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) :
    WP isa (.block F.cmpPw) s fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ t.gpr .ecx = VG.X86.arg s₀ 1 ∧
      t.cf = some (decide (pwl s₀ < F.H.B + 1)) ∧ t.mem = s.mem := by
  have := hz.B
  refine wp_arg hp hk (by decide) fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_cmpi fun s₂ f₂ c₂ _ => WP.block_nil ?_
  refine ⟨(hk.upd (by decide) u₁).same f₂.rd f₂.wr (fun r _ => by rw [f₂.gpr]) f₂.mem, by rw [f₂.gpr, u₁.gpr], ?_,
    by rw [f₂.mem, u₁.mem]⟩
  rw [c₂, u₁.gpr, toNat_ofNat32 (by omega)]

omit hp hz in
theorem hash_len {k : List Byte} {m : Mem} {p : Addr} (h : bytesAt m p F.H.D = hH.SH.H.hash k) :
    (hH.SH.H.hash k).length = F.H.D := by
  rw [← h, bytesAt_length]

omit hp in
/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash {k : List Byte} (hk : F.H.B < k.length) (hl : (hH.SH.H.hash k).length = F.H.D) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hB := hH.hB; have := hz.DB
  simp only [blockKey, hB, hl, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ F.H.B < F.H.D by omega))]

end

/-- Where the key is, and its length. -/
abbrev kp (F : Fns) (s₀ : State) : BitVec 32 := if pwl s₀ < F.H.B + 1 then pw s₀ else dO s₀ F.hkO
abbrev kl (F : Fns) (s₀ : State) : Nat := if pwl s₀ < F.H.B + 1 then pwl s₀ else F.H.D

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F) (hH : HashOK F.H)
include hp hz hH

theorem key_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) :
    WP isa F.key s fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ t.gpr .edx = VG.Proof.Pbkdf2.Whole.X86.kp F s₀ ∧ t.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Whole.X86.kl F s₀) ∧
      blockKey hH.SH.H (bytesAt t.mem ((VG.Proof.Pbkdf2.Whole.X86.kp F s₀).setWidth 64) (VG.Proof.Pbkdf2.Whole.X86.kl F s₀)) =
        blockKey hH.SH.H (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀)) := by
  unfold Fns.key
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.cmp_ok hp hz hk) fun s₁ ⟨k₁, c₁, f₁, _⟩ => ?_)
  refine WP.ite (decide (F.H.B + 1 ≤ pwl s₀)) (by
    show (s₁.cf.map (!·)) = _
    rw [f₁]; simp only [Option.map_some, ← decide_not, Nat.not_lt])
    (fun hT => ?_) fun hF => ?_
  · have hlt : ¬ pwl s₀ < F.H.B + 1 := by have := of_decide_eq_true hT; omega
    simp only [VG.Proof.Pbkdf2.Whole.X86.kp, VG.Proof.Pbkdf2.Whole.X86.kl, hlt, ↓reduceIte]
    refine WP.mono (VG.Proof.Pbkdf2.Whole.X86.hashKey_ok hp hz hH k₁) fun t ⟨k, d, c, b⟩ => ⟨k, d, c, ?_⟩
    have := hz.D
    rw [show (dO s₀ F.hkO).setWidth 64 = A s₀ F.hkO from dO_addr hp (by have := end_le hz; have := layout (F := F); omega),
      b, VG.Proof.Pbkdf2.Whole.X86.blockKey_hash hz hH (by rw [bytesAt_length]; omega) (VG.Proof.Pbkdf2.Whole.X86.hash_len hH b)]
  · have hlt : pwl s₀ < F.H.B + 1 := by have := of_decide_eq_false hF; omega
    simp only [VG.Proof.Pbkdf2.Whole.X86.kp, VG.Proof.Pbkdf2.Whole.X86.kl, hlt, ↓reduceIte]
    refine wp_arg hp k₁ (by decide) fun s₂ u₂ => WP.block_nil ⟨k₁.upd (by decide) u₂, u₂.gpr, ?_, ?_⟩
    · rw [u₂.other _ (by decide), c₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [u₂.mem, k₁.pwBytes hp]

end

/-! ## Where the key is -/

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F)
include hp hz

/-- The key's region is the password, or the hashed password in `scratch`. -/
theorem key_cases : (VG.Proof.Pbkdf2.Whole.X86.kp F s₀ = pw s₀ ∧ VG.Proof.Pbkdf2.Whole.X86.kl F s₀ = pwl s₀ ∧ pwl s₀ ≤ F.H.B) ∨
    ((VG.Proof.Pbkdf2.Whole.X86.kp F s₀).setWidth 64 = A s₀ F.hkO ∧ VG.Proof.Pbkdf2.Whole.X86.kl F s₀ = F.H.D) := by
  by_cases h : pwl s₀ < F.H.B + 1
  · exact .inl ⟨by simp [VG.Proof.Pbkdf2.Whole.X86.kp, h], by simp [VG.Proof.Pbkdf2.Whole.X86.kl, h], by omega⟩
  · refine .inr ⟨?_, by simp [VG.Proof.Pbkdf2.Whole.X86.kl, h]⟩
    simp only [VG.Proof.Pbkdf2.Whole.X86.kp, h, ↓reduceIte]
    exact dO_addr hp (by have := end_le hz; have := layout (F := F); have := hz.D; omega)

theorem kl_le : VG.Proof.Pbkdf2.Whole.X86.kl F s₀ ≤ F.H.B := by
  have := hz.DB
  rcases VG.Proof.Pbkdf2.Whole.X86.key_cases hp hz with ⟨-, h, h'⟩ | ⟨-, h⟩ <;> omega

theorem key_toNat : (VG.Proof.Pbkdf2.Whole.X86.kp F s₀).toNat + VG.Proof.Pbkdf2.Whole.X86.kl F s₀ ≤ 2 ^ 32 := by
  by_cases h : pwl s₀ < F.H.B + 1
  · simp only [VG.Proof.Pbkdf2.Whole.X86.kp, VG.Proof.Pbkdf2.Whole.X86.kl, h, ↓reduceIte]; exact hp.npw
  · simp only [VG.Proof.Pbkdf2.Whole.X86.kp, VG.Proof.Pbkdf2.Whole.X86.kl, h, ↓reduceIte]
    have := end_le hz; have := layout (F := F); have := hz.D
    rw [dO_toNat hp (by omega)]
    have := hp.nsc; omega

/-- The key is apart from the parts of `scratch` after the hashed password,
from the working space, and from the stack below `esp`. -/
theorem key_disj {R : Region} (hR : Region.Sub R (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F))
    (hd : R.Disjoint (sR s₀ F.hkO F.H.D)) : Region.Disjoint ⟨(VG.Proof.Pbkdf2.Whole.X86.kp F s₀).setWidth 64, VG.Proof.Pbkdf2.Whole.X86.kl F s₀⟩ R := by
  rcases VG.Proof.Pbkdf2.Whole.X86.key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.pw_s.sub_right hR
  · rw [h, h']; exact hd.symm

theorem key_stk {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) : (stk s).Disjoint ⟨(VG.Proof.Pbkdf2.Whole.X86.kp F s₀).setWidth 64, VG.Proof.Pbkdf2.Whole.X86.kl F s₀⟩ := by
  rw [hk.stkE]
  rcases VG.Proof.Pbkdf2.Whole.X86.key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.b_pw
  · rw [h, h']; exact hp.b_s.sub_right (part_sub (by have := end_le hz; have := layout (F := F); have := hz.D; omega))

theorem key_cov {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) : Covers [⟨(VG.Proof.Pbkdf2.Whole.X86.kp F s₀).setWidth 64, VG.Proof.Pbkdf2.Whole.X86.kl F s₀⟩] (s.rd ++ s.wr) := by
  rcases VG.Proof.Pbkdf2.Whole.X86.key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact VG.Proof.Pbkdf2.Whole.X86.cov_pw hp hk
  · rw [h, h']
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', off, e, l⟩ := VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (o := F.hkO) (n := F.H.D)
        (by have := end_le hz; have := layout (F := F); have := hz.D; omega)
      exact ⟨r', List.mem_append_right _ hr', off, e, l⟩

end

end VG.Proof.Pbkdf2.Whole.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Setup`. -/
section

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: HMAC's states for the key, and the salt

HMAC's `init` makes the key's inner and outer states; the inner one is copied
and absorbs the salt (`setup_ok`), which gives the three states every block
starts from (`States`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_ copy)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK UpdArgs upd_frame CopyInv Copied copy_ok cclob)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length writeBytes_at bytesAt_getD' xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad)

variable {F : Fns}

/-- `K₀`, the password padded (or hashed and padded) to a block. -/
abbrev K0 (hF : FnsOK F) (s₀ : State) : List Byte :=
  blockKey hF.hH.SH.H (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀))

abbrev saltB (s₀ : State) : List Byte := bytesAt s₀.mem ((salt s₀).setWidth 64) (sl s₀)

/-- The key's states, and the inner one after the salt. -/
structure States (hF : FnsOK F) (s₀ : State) (m : Mem) : Prop where
  st0 : hF.hH.SH.Repr m (A s₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad)
  st1 : hF.hH.SH.Repr m (A s₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) opad)
  stS : hF.hH.SH.Repr m (A s₀ F.stSO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad ++ VG.Proof.Pbkdf2.Whole.X86.saltB s₀)

/-- The representation is kept by what writes elsewhere. -/
theorem repr_keep (hH : HashOK F.H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, F.H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, F.H.S⟩) hd (by show F.H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr

/-- The three states are kept by what writes elsewhere: after them in `scratch`. -/
theorem States.keep {hF : FnsOK F} {s₀ : State} (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F) {m m' : Mem} (h : VG.Proof.Pbkdf2.Whole.X86.States hF s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ F.st0O (3 * F.H.S)) r) :
    VG.Proof.Pbkdf2.Whole.X86.States hF s₀ m' := by
  have hl := layout (F := F); have he := end_le hz; have := hz.D
  have sub : ∀ o, F.st0O ≤ o → o + F.H.S ≤ F.st0O + 3 * F.H.S →
      Region.Sub (sR s₀ o F.H.S) (sR s₀ F.st0O (3 * F.H.S)) := fun o h₁ h₂ =>
    Offset.sub _ h₁ h₂
  refine ⟨VG.Proof.Pbkdf2.Whole.X86.repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega) (by omega))) h.st0,
    VG.Proof.Pbkdf2.Whole.X86.repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega) (by omega))) h.st1,
    VG.Proof.Pbkdf2.Whole.X86.repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega) (by omega))) h.stS⟩

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F)
include hp hz

/-- A copy of `n > 0` bytes within `scratch`, after the save area. -/
theorem copy_part_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {a b n : Nat} (hn : 0 < n) (ha : a + n ≤ F.L8)
    (hb : b + n ≤ F.L8) (hb' : 8 * F.W + 16 ≤ b) (hab : a + n ≤ b ∨ b + n ≤ a) :
    WP isa (copy .ebp a .ebp b n) s fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ (∀ r ∉ cclob, t.gpr r = s.gpr r) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (A s₀ b) (bytesAt s.mem (A s₀ a) n) := by
  have hL := L8_le hz; have := hp.nsc; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (copy_ok (src := .ebp) (dst := .ebp) (by decide) (by decide) hn (by omega)
    (by rw [hk.ebp]; omega) (by rw [hk.ebp]; omega)
    (fun j hj => by
      rw [hk.ebp]
      exact ⟨VG.Proof.Pbkdf2.Whole.X86.scR s₀ F, List.mem_append_right _ (by rw [hk.wr]; exact sc_mem hp),
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => by
      rw [hk.ebp]
      exact ⟨VG.Proof.Pbkdf2.Whole.X86.scR s₀ F, by rw [hk.wr]; exact sc_mem hp,
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [hk.ebp]; exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz hab ha hb)) fun t c => ?_
  rw [hk.ebp] at c
  have f : Frame [sR s₀ b n] s.mem t.mem := by
    rw [c.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  exact ⟨hk.write hz c.rd c.wr (fun r hr => c.other r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> decide))
    hb' hb f, c.other, c.mem⟩

omit hp hz in
/-- After such a copy, the bytes at `b` are those at `a`. -/
theorem copied_byte {m : Mem} {a b n : Nat} (hn : n ≤ 2 ^ 32) (i : Nat) (hi : i < n) :
    VG.WriteBytes.writeBytes m (A s₀ b) (bytesAt m (A s₀ a) n) (A s₀ b + BitVec.ofNat 64 i) = m (A s₀ a + BitVec.ofNat 64 i) := by
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega), bytesAt_getD' _ _ hi]

end

/-- After the key: where it is, and its `K₀`. -/
structure Keyed (hF : FnsOK F) (s₀ s : State) : Prop where
  kr : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s
  edx : s.gpr .edx = VG.Proof.Pbkdf2.Whole.X86.kp F s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Whole.X86.kl F s₀)
  k0 : blockKey hF.hH.SH.H (bytesAt s.mem ((VG.Proof.Pbkdf2.Whole.X86.kp F s₀).setWidth 64) (VG.Proof.Pbkdf2.Whole.X86.kl F s₀)) = VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F) (hF : FnsOK F)
include hp hz hF

theorem keyed_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) : WP isa F.key s (VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀) :=
  WP.mono (VG.Proof.Pbkdf2.Whole.X86.key_ok hp hz hF.hH hk) fun _ ⟨k, d, c, b⟩ => ⟨k, d, c, b⟩

omit hp hz in
theorem su1_ok {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.st0O ++ VG.Impl.Pbkdf2.Stream.X86.scr .esi F.st1O)) s
      fun t => VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀ t ∧ t.gpr .edi = dO s₀ F.st0O ∧ t.gpr .esi = dO s₀ F.st1O := by
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have k₁ := h.kr.upd (by decide) u₁
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .esi F.st1O)]
  refine scr_ok k₁ fun s₂ u₂ => WP.block_nil ⟨⟨k₁.upd (by decide) u₂, ?_, ?_, ?_⟩, ?_, u₂.gpr⟩
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.edx]
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
  · rw [u₂.mem, u₁.mem]; exact h.k0
  · rw [u₂.other _ (by decide), u₁.gpr]

theorem su2_args {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀ s) (hdi : s.gpr .edi = dO s₀ F.st0O)
    (hsi : s.gpr .esi = dO s₀ F.st1O) :
    HiArgs hF.hH.SH hF.Wi s (dO s₀ F.st0O) (dO s₀ F.st1O) (VG.Proof.Pbkdf2.Whole.X86.kp F s₀) (VG.Proof.Pbkdf2.Whole.X86.scr s₀) (VG.Proof.Pbkdf2.Whole.X86.kl F s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWi; have hS := hF.hH.hS
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  have hk := h.kr
  have kd : ∀ o n, o + n ≤ F.hkO → F.st0O ≤ o →
      Region.Disjoint ⟨(VG.Proof.Pbkdf2.Whole.X86.kp F s₀).setWidth 64, VG.Proof.Pbkdf2.Whole.X86.kl F s₀⟩ (sR s₀ o n) := fun o n h₁ h₂ =>
    VG.Proof.Pbkdf2.Whole.X86.key_disj hp hz (part_sub (by omega)) (VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl h₁) (by omega) (by omega))
  have kls : Region.Disjoint ⟨(VG.Proof.Pbkdf2.Whole.X86.kp F s₀).setWidth 64, VG.Proof.Pbkdf2.Whole.X86.kl F s₀⟩ (lowR s₀ (hF.Wi * 8)) :=
    VG.Proof.Pbkdf2.Whole.X86.key_disj hp hz (low_sub (by omega)) (low_disj hz (by omega) (by omega))
  exact
    { edi := hdi
      esi := hsi
      edx := h.edx
      ecx := h.ecx
      ebp := hk.ebp
      klB := by rw [hF.hH.hB]; exact VG.Proof.Pbkdf2.Whole.X86.kl_le hp hz
      kl32 := by have := VG.Proof.Pbkdf2.Whole.X86.kl_le hp hz; have := hz.B; omega
      sp := by rw [hk.esp]; exact hp.sp76
      cr := VG.Proof.Pbkdf2.Whole.X86.key_cov hp hz hk
      cw := by
        rw [hS, e0, e1]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_low hp hk (by omega)
      i_o := by rw [hS, e0, e1]; exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      i_k := by rw [hS, e0]; exact (kd _ _ (by omega) (by omega)).symm
      i_s := by rw [hS, e0]; exact (low_disj hz (by omega) (by omega)).symm
      o_k := by rw [hS, e1]; exact (kd _ _ (by omega) (by omega)).symm
      o_s := by rw [hS, e1]; exact (low_disj hz (by omega) (by omega)).symm
      k_s := kls
      b_i := by rw [hS, e0]; exact VG.Proof.Pbkdf2.Whole.X86.b76 hp hk (part_sub (by omega))
      b_o := by rw [hS, e1]; exact VG.Proof.Pbkdf2.Whole.X86.b76 hp hk (part_sub (by omega))
      b_k := VG.Proof.Pbkdf2.Whole.X86.key_stk hp hz hk
      b_s := VG.Proof.Pbkdf2.Whole.X86.b76 hp hk (low_sub (by omega))
      ni := by rw [hS, dO_toNat hp (by omega)]; have := hp.nsc; omega
      no := by rw [hS, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nk := VG.Proof.Pbkdf2.Whole.X86.key_toNat hp hz
      nsc := by have := hp.nsc; omega }

theorem su2_ok {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀ s) (hdi : s.gpr .edi = dO s₀ F.st0O)
    (hsi : s.gpr .esi = dO s₀ F.st1O) :
    WP isa (.frame (.push hi5) (.call F.hiN F.hiC) (.pop .eax hi5.length)) s fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) opad) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWi; have hS := hF.hH.hS
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  refine hi_frame hF.hi hF.hiSp hF.hiSU (VG.Proof.Pbkdf2.Whole.X86.su2_args hp hz hF h hdi hsi) fun s' a r0 r1 => ⟨?_, ?_, ?_⟩
  · refine h.kr.call hp hz a fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [e0, hS], by omega, by omega⟩
    · exact .inr ⟨_, _, by rw [e1, hS], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · rw [h.k0, e0] at r0; exact r0
  · rw [h.k0, e1] at r1; exact r1

omit hF in
theorem K0_length (hF : FnsOK F) {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀ s) : (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀).length = F.H.B := by
  have := VG.Proof.Pbkdf2.Whole.X86.kl_le hp hz
  rw [← h.k0]
  simp only [blockKey, hF.hH.hB, bytesAt_length, show ¬ F.H.B < VG.Proof.Pbkdf2.Whole.X86.kl F s₀ by omega, ↓reduceIte,
    List.length_append, List.length_replicate]
  omega

/-- The key's inner state, copied for the salt. -/
theorem su3_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (r0 : hF.hH.SH.Repr s.mem (A s₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad))
    (r1 : hF.hH.SH.Repr s.mem (A s₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) opad)) :
    WP isa (copy .ebp F.st0O .ebp F.stSO F.H.S) s fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) opad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.stSO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have hL := L8_le hz
  refine WP.mono (VG.Proof.Pbkdf2.Whole.X86.copy_part_ok hp hz hk hz.S.1 (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨k, _, m⟩ => ?_
  have f : Frame [sR s₀ F.stSO F.H.S] s.mem t.mem := by
    rw [m]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨k, VG.Proof.Pbkdf2.Whole.X86.repr_keep hF.hH f (fun r hr => ?_) r0, VG.Proof.Pbkdf2.Whole.X86.repr_keep hF.hH f (fun r hr => ?_) r1, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · refine hF.hH.repr _ _ _ _ _ (fun i hi => ?_) r0
    rw [m]; exact VG.Proof.Pbkdf2.Whole.X86.copied_byte (by omega) i hi

omit hz hF in
/-- `update`'s arguments: the salt. -/
theorem su4_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stSO ++ ([.mov .eax (.imm 0),
      .mov .esi (.imm (BitVec.ofNat 32 F.H.B)), .mov .ecx (Fns.argM 3), .mov .edx (Fns.argM 2)] : List Instr))) s
      fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stSO ∧ t.gpr .esi = BitVec.ofNat 32 F.H.B ∧ t.gpr .eax = 0 ∧
        t.gpr .ecx = VG.X86.arg s₀ 3 ∧ t.gpr .edx = salt s₀ ∧ t.mem = s.mem := by
  refine scr_ok hk fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_movi fun s₂ u₂ => VG.Proof.Sha256.X86.Stream.wp_movi fun s₃ u₃ => ?_
  have k₃ := ((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃
  refine wp_arg hp k₃ (by decide) fun s₄ u₄ => ?_
  have k₄ := k₃.upd (by decide) u₄
  refine wp_arg hp k₄ (by decide) fun s₅ u₅ => WP.block_nil ?_
  refine ⟨k₄.upd (by decide) u₅, ?_, ?_, ?_, ?_, u₅.gpr, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr]

omit hF in
/-- The salt is apart from `scratch`, so `B + salt_len` does not wrap around. -/
theorem salt_fit : F.H.B + 4 + sl s₀ < 2 ^ 32 := by
  have h₁ : (saltR s₀).base.toNat + (saltR s₀).len ≤ 2 ^ 32 := by
    show ((salt s₀).setWidth 64).toNat + sl s₀ ≤ _; rw [toNat_setWidth64]; exact hp.nsa
  have h₂ : (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F).base.toNat + (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F).len ≤ 2 ^ 32 := by
    show ((VG.Proof.Pbkdf2.Whole.X86.scr s₀).setWidth 64).toNat + F.L8 ≤ _; rw [toNat_setWidth64]; exact hp.nsc
  have h : sl s₀ + (F.W + F.H.S) * 8 ≤ 2 ^ 32 := Pbkdf2.Whole.len_add_le hp.sa_s h₁ h₂
  have := hz.B; have := hz.S; have := hz.BS
  omega

theorem su5_args {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stSO)
    (hsi : s.gpr .esi = BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = VG.X86.arg s₀ 3)
    (hdx : s.gpr .edx = salt s₀) :
    UpdArgs hF.hH s .esi .edi (dO s₀ F.stSO) (salt s₀) (VG.Proof.Pbkdf2.Whole.X86.scr s₀) (BitVec.ofNat 32 F.H.B) (sl s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stSO) (by omega)
  exact
    { hst := hdi
      hlo := hsi
      eax := hax
      ecx := by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      hl := by decide
      hlen := (VG.X86.arg s₀ 3).isLt
      sp48 := by rw [hk.esp]; have := hp.sp76; omega
      cd := VG.Proof.Pbkdf2.Whole.X86.cov_salt hp hk
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_low hp hk (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hF.hH.Wb) (by omega) (by omega)).symm
      d_st := by rw [ea]; exact hp.sa_s.sub_right (part_sub (by omega))
      d_sc := hp.sa_s.sub_right (low_sub (by omega))
      b_st := by rw [ea]; exact VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (part_sub (by omega))
      b_d := hp.b_sa.sub_left (VG.Proof.Pbkdf2.Whole.X86.stk48_sub hp hk)
      b_sc := VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nd := hp.nsa
      nsc := by have := hp.nsc; omega }

theorem su5_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stSO)
    (hsi : s.gpr .esi = BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = VG.X86.arg s₀ 3)
    (hdx : s.gpr .edx = salt s₀) (hkl : (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀).length = F.H.B)
    (r0 : hF.hH.SH.Repr s.mem (A s₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad))
    (r1 : hF.hH.SH.Repr s.mem (A s₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) opad))
    (rS : hF.hH.SH.Repr s.mem (A s₀ F.stSO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad)) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)) s
      fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ VG.Proof.Pbkdf2.Whole.X86.States hF s₀ t.mem := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stSO) (by omega)
  refine upd_frame hF.hH (VG.Proof.Pbkdf2.Whole.X86.su5_args hp hz hF hk hdi hsi hax hcx hdx) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  all_goals have f := a.frame
  all_goals rw [ea] at f
  · refine VG.Proof.Pbkdf2.Whole.X86.repr_keep hF.hH f (fun r hr => ?_) r0
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega)) (by omega) (by omega)
    · exact low_disj hz (by omega) (by omega) |>.symm
    · exact (VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (part_sub (by omega))).symm
  · refine VG.Proof.Pbkdf2.Whole.X86.repr_keep hF.hH f (fun r hr => ?_) r1
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega)) (by omega) (by omega)
    · exact low_disj hz (by omega) (by omega) |>.symm
    · exact (VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (part_sub (by omega))).symm
  · have := r (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad) (by rw [ea]; exact rS) (by
      rw [xorPad_length, hkl, Pbkdf2.Stream.X86.zero_append_ofNat (by have := hz.B; omega)])
    rw [ea, hk.saltBytes hp] at this
    exact this

theorem setup_ok {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀ s) :
    WP isa F.setup s fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ VG.Proof.Pbkdf2.Whole.X86.States hF s₀ t.mem ∧ (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀).length = F.H.B := by
  have hkl := VG.Proof.Pbkdf2.Whole.X86.K0_length hp hz hF h
  unfold Fns.setup
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.su1_ok hF h) fun s₁ ⟨k₁, d₁, i₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.su2_ok hp hz hF k₁ d₁ i₁) fun s₂ ⟨k₂, r0, r1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.su3_ok hp hz hF k₂ r0 r1) fun s₃ ⟨k₃, r0, r1, rS⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.su4_ok hp k₃) fun s₄ ⟨k₄, d₄, i₄, a₄, c₄, x₄, m₄⟩ => ?_)
  exact WP.mono (VG.Proof.Pbkdf2.Whole.X86.su5_ok hp hz hF k₄ d₄ i₄ a₄ c₄ x₄ hkl (m₄ ▸ r0) (m₄ ▸ r1) (m₄ ▸ rS))
    fun t ⟨k, st⟩ => ⟨k, st, hkl⟩

end

end VG.Proof.Pbkdf2.Whole.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Block`. -/
section

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: a block of the output, up to `U₁`

After `k` blocks of the output (`Inv`), `out` holds the first `done k` bytes
of `T₁ ‖ … ‖ T_k`, `ebx` is `done k`, and `scratch` holds `INT (k + 1)`,
byte-reversed. A step copies the salted inner state into the working state,
absorbs `INT (k + 1)` into it (`update`) and computes `U₁` with HMAC's
`finalize`.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_ copy)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK UpdArgs upd_frame cclob zero_append_ofNat)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm wp_addi wp_store wp_bswap wp_test)
open VG.Proof.Hmac.Generic.Common (bytes_keep)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad hmacBlockKey)

variable {F : Fns}

/-- The pseudorandom function: HMAC keyed with the password. -/
abbrev prf (hF : FnsOK F) (s₀ : State) : List Byte → List Byte := hmacBlockKey hF.hH.SH.H (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀)

/-- `T₁ ‖ … ‖ T_k`, `T_i`, the number of blocks and the bytes written after `k` of them. -/
abbrev Gk (hF : FnsOK F) (s₀ : State) (k : Nat) : List Byte := Whole.G (VG.Proof.Pbkdf2.Whole.X86.prf hF s₀) (VG.Proof.Pbkdf2.Whole.X86.saltB s₀) (cc s₀) k
abbrev Tk (hF : FnsOK F) (s₀ : State) (i : Nat) : List Byte := Whole.Tb (VG.Proof.Pbkdf2.Whole.X86.prf hF s₀) (VG.Proof.Pbkdf2.Whole.X86.saltB s₀) (cc s₀) i
abbrev nbk (F : Fns) (s₀ : State) : Nat := Whole.nb F.H.D (ol s₀)
abbrev dn (F : Fns) (s₀ : State) (k : Nat) : Nat := Whole.done F.H.D (ol s₀) k

/-- After `k` blocks of the output. -/
structure Inv (hF : FnsOK F) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s
  st : VG.Proof.Pbkdf2.Whole.X86.States hF s₀ s.mem
  k0l : (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀).length = F.H.B
  ebx : s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Whole.X86.dn F s₀ k)
  intW : s.mem.readW (A s₀ F.intO) 32 = byteRev32 (BitVec.ofNat 32 (k + 1))
  glen : (VG.Proof.Pbkdf2.Whole.X86.Gk hF s₀ k).length = k * F.H.D
  outB : bytesAt s.mem ((VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64) (VG.Proof.Pbkdf2.Whole.X86.dn F s₀ k) = (VG.Proof.Pbkdf2.Whole.X86.Gk hF s₀ k).take (VG.Proof.Pbkdf2.Whole.X86.dn F s₀ k)

/-- The registers `Inv` fixes. -/
abbrev iregs : List Reg := [.esp, .ebp, .ebx]

/-- Where a step writes, before it copies `T` out: the working space, or
the parts of `scratch` from the working state up to `INT (i)`. -/
def Wks (F : Fns) (s₀ : State) (r : Region) : Prop :=
  (∃ k, r = lowR s₀ k ∧ k ≤ 8 * F.W) ∨ ∃ o n, r = sR s₀ o n ∧ F.stWO ≤ o ∧ o + n ≤ F.intO

section
variable {hF : FnsOK F} {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F)
include hp hz

omit hp in
theorem Wks.disj {r : Region} (h : VG.Proof.Pbkdf2.Whole.X86.Wks F s₀ r) :
    (svR F s₀).Disjoint r ∧ Region.Sub r (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F) ∧ (sR s₀ F.st0O (3 * F.H.S)).Disjoint r ∧
      (sR s₀ F.intO 4).Disjoint r := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D
  rcases h with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
  · exact ⟨sv_low hz hk, low_sub (by omega), (low_disj hz (by omega) (by omega)).symm,
      (low_disj hz (by omega) (by omega)).symm⟩
  · exact ⟨sv_disj hz (by omega) (by omega_using [h₂, he]), part_sub (by omega),
      VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega)) (by omega) (by omega), VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inr (by omega)) (by omega) (by omega)⟩

/-- `Inv` survives writes where a step writes, and to the stack below `esp`. -/
theorem Inv.keep {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ VG.Proof.Pbkdf2.Whole.X86.iregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, VG.Proof.Pbkdf2.Whole.X86.Wks F s₀ r ∨ r = VG.Proof.Pbkdf2.Whole.X86.stkR s₀) : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s' := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D
  have hsb : (VG.Proof.Pbkdf2.Whole.X86.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F) := hp.b_s
  refine ⟨h.kr.keep hrd hwr (fun r hr => hg r (by simp only [List.mem_cons] at hr ⊢; grind)) hf
    (fun r hr => ?_) (fun r hr => ?_), h.st.keep hz hf (fun r hr => ?_), h.k0l, by rw [hg _ (by simp), h.ebx],
    ?_, h.glen, ?_⟩
  · rcases hw r hr with hw | rfl
    · exact (hw.disj hz).1
    · exact (hsb.sub_right (sv_sub hz)).symm
  · rcases hw r hr with hw | rfl
    · exact ⟨_, by simp, (hw.disj hz).2.1⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rcases hw r hr with hw | rfl
    · exact (hw.disj hz).2.2.1
    · exact (hsb.sub_right (part_sub (by omega))).symm
  · rw [← h.intW]
    refine hf.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases hw r hr with hw | rfl
    · exact (hw.disj hz).2.2.2
    · exact (hsb.sub_right (part_sub (by omega))).symm
  · rw [← h.outB]
    have osub : Region.Sub ⟨(VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64, VG.Proof.Pbkdf2.Whole.X86.dn F s₀ k⟩ (VG.Proof.Pbkdf2.Whole.X86.outR s₀) :=
      Region.sub_prefix (Nat.min_le_right _ _)
    refine bytes_keep hf (fun r hr => ?_) (by
      have h1 : VG.Proof.Pbkdf2.Whole.X86.dn F s₀ k ≤ ol s₀ := Nat.min_le_right _ _; have hp_no := hp.no; omega_using [hp_no, h1])
    rcases hw r hr with hw | rfl
    · exact (hp.o_s.sub_left osub).sub_right (hw.disj hz).2.1
    · exact hp.b_o.symm.sub_left osub

theorem Inv.upd {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) {d : Reg} (hd : d ∉ VG.Proof.Pbkdf2.Whole.X86.iregs) {v : BitVec 32}
    (u : VG.Proof.Sha256.X86.Stream.Upd s s' d v) : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s' :=
  h.keep hp hz u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp)

theorem Inv.same {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ VG.Proof.Pbkdf2.Whole.X86.iregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s' :=
  h.keep hp hz hrd hwr hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- After a call that writes where a step writes. -/
theorem Inv.after {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, VG.Proof.Pbkdf2.Whole.X86.Wks F s₀ r) : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s' := by
  have f := ha.frame
  rw [h.kr.stkE] at f
  refine h.keep hp hz ha.rd ha.wr (fun r hr => ha.cs r (by simp only [List.mem_cons] at hr ⊢; simp [calleeSaved]; grind))
    f fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact .inl (hw r hr)
  · simp only [List.mem_singleton] at hr; exact .inr hr

/-! ## The loop's start -/

omit hp hz in
theorem bswap_eq (x : BitVec 32) : bswap x = byteRev32 x := rfl

omit hz in
theorem ea_scr {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {o : Nat} (ho : o < F.L8) :
    s.ea (VG.Impl.Pbkdf2.Stream.X86.at_ .ebp o) = A s₀ o := by
  rw [show s.ea (VG.Impl.Pbkdf2.Stream.X86.at_ .ebp o) = (dO s₀ o).setWidth 64 by
    show (s.gpr .ebp + BitVec.ofNat 32 o).setWidth 64 = _; rw [hk.ebp]]
  exact dO_addr hp ho

/-- `INT (1)`, no bytes written, and whether `out_len` is 0. -/
theorem loopInit_ok {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hst : VG.Proof.Pbkdf2.Whole.X86.States hF s₀ s.mem) (hkl : (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀).length = F.H.B) :
    WP isa (.block F.loopInit) s fun t => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ 0 t ∧ t.zf = some (decide (ol s₀ = 0)) := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D
  unfold Fns.loopInit
  refine VG.Proof.Sha256.X86.Stream.wp_movi fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_bswap fun s₂ u₂ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_store (a := A s₀ F.intO) (VG.Proof.Pbkdf2.Whole.X86.ea_scr hp ((hk.upd (by decide) u₁).upd (by decide) u₂) (by omega_using [he]))
    (by rw [u₂.wr, u₁.wr]; exact in_sc hp hz hk.wr (by omega)) fun s₃ m₃ => ?_
  have f₃ : Frame [sR s₀ F.intO 4] s.mem s₃.mem := by
    rw [m₃.mem, u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₃ : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s₃ := hk.write hz (by rw [m₃.rd, u₂.rd, u₁.rd]) (by rw [m₃.wr, u₂.wr, u₁.wr])
    (fun r hr => by
      rw [m₃.gpr, u₂.other r (by simp only [List.mem_cons] at hr; rcases hr with rfl | rfl | h <;> simp_all),
        u₁.other r (by simp only [List.mem_cons] at hr; rcases hr with rfl | rfl | h <;> simp_all)])
    (by omega) (by omega) f₃
  refine VG.Proof.Sha256.X86.Stream.wp_movi fun s₄ u₄ => wp_arg hp (k₃.upd (by decide) u₄) (by decide) fun s₅ u₅ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_test fun s₆ f₆ z₆ => WP.block_nil ⟨⟨?_, ?_, hkl, ?_, ?_, by simp [VG.Proof.Pbkdf2.Whole.X86.Gk, Whole.G], ?_⟩, ?_⟩
  · exact ((k₃.upd (by decide) u₄).upd (by decide) u₅).same f₆.rd f₆.wr (fun r _ => by rw [f₆.gpr]) f₆.mem
  · rw [f₆.mem, u₅.mem, u₄.mem]
    exact hst.keep hz f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr]; simp [VG.Proof.Pbkdf2.Whole.X86.dn, Whole.done]
  · rw [f₆.mem, u₅.mem, u₄.mem, m₃.mem, Mem.readW_writeW_self32, u₂.gpr, u₁.gpr]; rfl
  · simp [VG.Proof.Pbkdf2.Whole.X86.dn, Whole.done, bytesAt]
  · rw [z₆, u₅.gpr, Pbkdf2.Stream.X86.test_z]

/-! ## A step: the working state, and `INT (i)` -/

/-- The salted inner state, copied into the working state. -/
theorem b1_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) :
    WP isa (copy .ebp F.stSO .ebp F.stWO F.H.S) s fun t => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad ++ VG.Proof.Pbkdf2.Whole.X86.saltB s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D
  refine WP.mono (VG.Proof.Pbkdf2.Whole.X86.copy_part_ok hp hz h.kr hz.S.1 (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨kt, g, m⟩ => ⟨?_, ?_⟩
  · have f : Frame [sR s₀ F.stWO F.H.S] s.mem t.mem := by
      rw [m]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    exact h.keep hp hz (kt.rd.trans h.kr.rd.symm) (kt.wr.trans h.kr.wr.symm) (fun r hr => g r (by
      simp only [VG.Proof.Pbkdf2.Whole.X86.iregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (.inr ⟨_, _, rfl, Nat.le_refl _, by omega⟩)
  · refine hF.hH.repr _ _ _ _ _ (fun i hi => ?_) h.st.stS
    rw [m]; exact VG.Proof.Pbkdf2.Whole.X86.copied_byte (by omega) i hi

/-- `update`'s arguments: the working state, `B + salt_len`, `INT (i)`. -/
theorem b2_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) :
    WP isa (.block F.updArgs) s fun t => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k t ∧ t.gpr .edi = dO s₀ F.stWO ∧
      t.gpr .esi = VG.X86.arg s₀ 3 + BitVec.ofNat 32 F.H.B ∧ t.gpr .eax = 0 ∧ t.gpr .ecx = BitVec.ofNat 32 4 ∧
      t.gpr .edx = dO s₀ F.intO ∧ t.mem = s.mem := by
  simp only [Fns.updArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have i₁ := h.upd hp hz (by decide) u₁
  refine wp_arg hp i₁.kr (by decide) fun s₂ u₂ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₃ u₃ => VG.Proof.Sha256.X86.Stream.wp_movi fun s₄ u₄ => VG.Proof.Sha256.X86.Stream.wp_movi fun s₅ u₅ => ?_
  have i₅ := (((i₁.upd hp hz (by decide) u₂).upd hp hz (by decide) u₃).upd hp hz (by decide) u₄).upd hp hz
    (by decide) u₅
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.intO)]
  refine scr_ok i₅.kr fun s₆ u₆ => WP.block_nil ⟨i₅.upd hp hz (by decide) u₆, ?_, ?_, ?_, ?_, u₆.gpr, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₆.other _ (by decide), u₅.gpr]; rfl
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b3_args {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) (hdi : s.gpr .edi = dO s₀ F.stWO)
    (hsi : s.gpr .esi = VG.X86.arg s₀ 3 + BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = BitVec.ofNat 32 4)
    (hdx : s.gpr .edx = dO s₀ F.intO) :
    UpdArgs hF.hH s .esi .edi (dO s₀ F.stWO) (dO s₀ F.intO) (VG.Proof.Pbkdf2.Whole.X86.scr s₀) (VG.X86.arg s₀ 3 + BitVec.ofNat 32 F.H.B) 4 := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have := hF.hH.hWb
  have hk := h.kr
  have ea := dO_addr hp (o := F.stWO) (by omega_using [he, hl])
  have ei := dO_addr hp (o := F.intO) (by omega_using [he])
  exact
    { hst := hdi
      hlo := hsi
      eax := hax
      ecx := hcx
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      hl := by decide
      hlen := by decide
      sp48 := by rw [hk.esp]; have hp_sp76 := hp.sp76; omega
      cd := by
        rw [ei]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          obtain ⟨r', hr', off, e, l⟩ := VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (o := F.intO) (n := 4) (by omega)
          exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_low hp hk (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hF.hH.Wb) (by omega) (by omega)).symm
      d_st := by rw [ei, ea]; exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inr (by omega)) (by omega) (by omega)
      d_sc := by rw [ei]; exact (low_disj hz (k := hF.hH.Wb) (by omega) (by omega)).symm
      b_st := by rw [ea]; exact VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (part_sub (by omega))
      b_d := by rw [ei]; exact VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (part_sub (by omega))
      b_sc := VG.Proof.Pbkdf2.Whole.X86.b48 hp hk (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega
      nd := by rw [dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he]
      nsc := by have hp_nsc := hp.nsc; omega }

/-- `update` with `INT (k + 1)`. -/
theorem b3_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) (hdi : s.gpr .edi = dO s₀ F.stWO)
    (hsi : s.gpr .esi = VG.X86.arg s₀ 3 + BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = BitVec.ofNat 32 4)
    (hdx : s.gpr .edx = dO s₀ F.intO)
    (hr : hF.hH.SH.Repr s.mem (A s₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad ++ VG.Proof.Pbkdf2.Whole.X86.saltB s₀)) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)) s
      fun t => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k t ∧
        hF.hH.SH.Repr t.mem (A s₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad ++ VG.Proof.Pbkdf2.Whole.X86.saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have ei := dO_addr hp (o := F.intO) (by omega)
  have hsf := VG.Proof.Pbkdf2.Whole.X86.salt_fit hp hz
  refine upd_frame hF.hH (VG.Proof.Pbkdf2.Whole.X86.b3_args hp hz h hdi hsi hax hcx hdx) fun s' a r => ⟨h.after hp hz (After.of_hmac (by
    rw [h.kr.esp]; exact hp.sp76) a) fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], Nat.le_refl _, by omega⟩
    · exact .inl ⟨_, rfl, by omega_using [this, hz_W]⟩
  · have := r _ (by rw [ea]; exact hr) (by
      rw [List.length_append, xorPad_length, h.k0l, bytesAt_length,
        show VG.X86.arg s₀ 3 + BitVec.ofNat 32 F.H.B = BitVec.ofNat 32 (F.H.B + sl s₀) by
          rw [Nat.add_comm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        zero_append_ofNat (by omega)])
    rwa [ea, ei, Whole.bytes_rev_int h.intW] at this

/-! ## A step: `U₁` -/

omit hp hz in
theorem FnsOK.reprOK (hF : FnsOK F) : ReprOK hF.hH.SH := fun m m' p q msg hb =>
  hF.hH.repr m m' p q msg (fun i hi => hb i (by rw [hF.hH.hS]; exact hi))

omit hp hz in
theorem add_ofNat_eq (x : BitVec 32) {n : Nat} (h : x.toNat + n < 2 ^ 32) :
    x + BitVec.ofNat 32 n = BitVec.ofNat 32 (x.toNat + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := h
  omega

/-- HMAC's `finalize`'s arguments. -/
theorem b4_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) :
    WP isa (.block F.finArgs) s fun t => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k t ∧ t.gpr .edx = dO s₀ F.stWO ∧
      t.gpr .esi = dO s₀ F.st1O ∧ t.gpr .eax = VG.X86.arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4) ∧ t.gpr .ecx = 0 ∧
      t.gpr .edi = dO s₀ F.uO ∧ t.mem = s.mem := by
  simp only [Fns.finArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have i₁ := h.upd hp hz (by decide) u₁
  refine scr_ok i₁.kr fun s₂ u₂ => ?_
  have i₂ := i₁.upd hp hz (by decide) u₂
  refine wp_arg hp i₂.kr (by decide) fun s₃ u₃ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₄ u₄ => VG.Proof.Sha256.X86.Stream.wp_movi fun s₅ u₅ => ?_
  have i₅ := ((i₂.upd hp hz (by decide) u₃).upd hp hz (by decide) u₄).upd hp hz (by decide) u₅
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.uO)]
  refine scr_ok i₅.kr fun s₆ u₆ => WP.block_nil ⟨i₅.upd hp hz (by decide) u₆, ?_, ?_, ?_, ?_, u₆.gpr, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr]
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b5_args {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) (hdx : s.gpr .edx = dO s₀ F.stWO)
    (hsi : s.gpr .esi = dO s₀ F.st1O) (hax : s.gpr .eax = VG.X86.arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4))
    (hcx : s.gpr .ecx = 0) (hdi : s.gpr .edi = dO s₀ F.uO) :
    HfArgs hF.hH.SH hF.Wf s (dO s₀ F.stWO) (dO s₀ F.st1O) (VG.X86.arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4)) 0
      (dO s₀ F.uO) (VG.Proof.Pbkdf2.Whole.X86.scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have hF_hWf := hF.hWf; have hS := hF.hH.hS; have hD := hF.hH.hD
  have hk := h.kr
  have ew := dO_addr hp (o := F.stWO) (by omega_using [he, hl])
  have e1 := dO_addr hp (o := F.st1O) (by omega_using [he, hl])
  have eu := dO_addr hp (o := F.uO) (by omega)
  exact
    { edx := hdx
      esi := hsi
      eax := hax
      ecx := hcx
      edi := hdi
      ebp := hk.ebp
      sp := by rw [hk.esp]; exact hp.sp76
      cr := by
        rw [hS, e1]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          obtain ⟨r', hr', off, e, l⟩ := VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (o := F.st1O) (n := F.H.S) (by omega_using [he, hl])
          exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [hS, hD, ew, eu]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (by omega)
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (by omega_using [he, hl])
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_low hp hk (by omega_using [hF_hWf, he, hl])
      i_u := by rw [hS, ew, e1]; exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inr (by omega)) (by omega) (by omega)
      i_o := by rw [hS, hD, ew, eu]; exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      i_s := by rw [hS, ew]; exact (low_disj hz (by omega) (by omega)).symm
      u_o := by rw [hS, hD, e1, eu]; exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      u_s := by rw [hS, e1]; exact (low_disj hz (by omega_using [hF_hWf, hl]) (by omega)).symm
      o_s := by rw [hD, eu]; exact (low_disj hz (by omega_using [hF_hWf, hl]) (by omega)).symm
      b_i := by rw [hS, ew]; exact VG.Proof.Pbkdf2.Whole.X86.b76 hp hk (part_sub (by omega))
      b_u := by rw [hS, e1]; exact VG.Proof.Pbkdf2.Whole.X86.b76 hp hk (part_sub (by omega))
      b_o := by rw [hD, eu]; exact VG.Proof.Pbkdf2.Whole.X86.b76 hp hk (part_sub (by omega))
      b_s := VG.Proof.Pbkdf2.Whole.X86.b76 hp hk (low_sub (by omega))
      ni := by rw [hS, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nu := by rw [hS, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      no := by rw [hD, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nsc := by have hp_nsc := hp.nsc; omega_using [hp_nsc, hF_hWf, he, hl] }

/-- HMAC's `finalize`: `U₁ = PRF (salt ‖ INT (k + 1))`. -/
theorem b5_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) (hdx : s.gpr .edx = dO s₀ F.stWO)
    (hsi : s.gpr .esi = dO s₀ F.st1O) (hax : s.gpr .eax = VG.X86.arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4))
    (hcx : s.gpr .ecx = 0) (hdi : s.gpr .edi = dO s₀ F.uO)
    (hr : hF.hH.SH.Repr s.mem (A s₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) ipad ++ VG.Proof.Pbkdf2.Whole.X86.saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.frame (.push hf6) (.call F.hfN F.hfC) (.pop .eax hf6.length)) s fun t => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.uO) F.H.D = VG.Proof.Pbkdf2.Whole.X86.prf hF s₀ (VG.Proof.Pbkdf2.Whole.X86.saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have hF_hWf := hF.hWf; have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have ew := dO_addr hp (o := F.stWO) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  have eu := dO_addr hp (o := F.uO) (by omega)
  have hsf := VG.Proof.Pbkdf2.Whole.X86.salt_fit hp hz
  refine hf_frame (FnsOK.reprOK hF) (by rw [hS]; omega) hF.hf hF.hfSp hF.hfSU (VG.Proof.Pbkdf2.Whole.X86.b5_args hp hz h hdx hsi hax hcx hdi)
    fun s' a post => ⟨h.after hp hz a fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [ew, hS], Nat.le_refl _, by omega⟩
    · exact .inr ⟨_, _, by rw [eu, hD], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega_using [hF_hWf]⟩
  · have := post (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) (VG.Proof.Pbkdf2.Whole.X86.saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) (by rw [h.k0l, hB])
      (by rw [h.k0l, List.length_append, bytesAt_length]; simp only [Spec.Pbkdf2.int, List.length_cons,
        List.length_nil]; omega_using [hsf])
      (by rw [ew, ← List.append_assoc]; exact hr)
      (by
        rw [List.length_append, bytesAt_length, hB,
          show VG.X86.arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4) = BitVec.ofNat 32 (F.H.B + (sl s₀ + 4)) by
            rw [VG.Proof.Pbkdf2.Whole.X86.add_ofNat_eq _ (by have : sl s₀ = (VG.X86.arg s₀ 3).toNat := rfl; omega_using [this, hsf]),
              show (VG.X86.arg s₀ 3).toNat + (F.H.B + 4) = F.H.B + (sl s₀ + 4) by
                have : sl s₀ = (VG.X86.arg s₀ 3).toNat := rfl; omega_using [this]],
          zero_append_ofNat (by omega_using [hsf])]
        simp only [Spec.Pbkdf2.int, List.length_cons, List.length_nil])
      (by rw [e1]; exact h.st.st1)
    rwa [eu, hD] at this

end

end VG.Proof.Pbkdf2.Whole.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Loop`. -/
section

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the rest of a block, the loop, and `pbkdf2`

A step copies `U₁` into `T`, runs `iterate` for the rest of the chain, copies
as much of `T` as the output still needs (`copyR_ok`, a byte copy of a length
in a register), and moves on to the next block; after the last one, `out`
holds the derived key.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_ copy)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK cclob count_loop nm ea_at addr3 ofNat_succ32)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_add wp_addi wp_sub wp_subi wp_cmp wp_cmpi
  wp_store wp_bswap wp_movzx8 wp_store8 sub_beq sub_ofNat)
open VG.Proof.Hmac.Generic.Common (bytes_keep writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad hmacBlockKey)

/-! ## A byte copy of a length in a register -/

/-- After `k` bytes of a copy from `A` to `B`. -/
structure CopyRInv (s : State) (A B : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r ∉ cclob, t.gpr r = s.gpr r
  ecx : t.gpr .ecx = BitVec.ofNat 32 k
  mem : t.mem = VG.WriteBytes.writeBytes s.mem B (bytesAt s.mem A k)

/-- The loop copying `n = esi > 0` bytes from `[ebp + so]` to `[edi]`, with
`ecx` the index. -/
theorem copyR_ok {so n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 32) {s : State} (hsi : s.gpr .esi = BitVec.ofNat 32 n)
    (hcx : s.gpr .ecx = 0)
    (hsw : (s.gpr .ebp).toNat + so + n ≤ 2 ^ 32) (hdw : (s.gpr .edi).toNat + n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) ((s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨(s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 so, n⟩ ⟨(s.gpr .edi).setWidth 64, n⟩) :
    WP isa (.loop (.block [.mov .eax (.reg .ebp), .alu .add .eax (.reg .ecx), .movzx8 .edx (VG.Impl.Pbkdf2.Stream.X86.at_ .eax so),
      .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store8 (VG.Impl.Pbkdf2.Stream.X86.at_ .eax 0) .dl,
      .alu .add .ecx (.imm 1), .alu .cmp .ecx (.reg .esi)]) .ne) s
      (VG.Proof.Pbkdf2.Whole.X86.CopyRInv s ((s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 so) ((s.gpr .edi).setWidth 64) n) := by
  generalize eA : (s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 so = A at hin hsep ⊢
  generalize eB : (s.gpr .edi).setWidth 64 = B at hout hsep ⊢
  have i0 : VG.Proof.Pbkdf2.Whole.X86.CopyRInv s A B 0 s :=
    ⟨rfl, rfl, fun _ _ => rfl, hcx, by rw [bytesAt, List.range_zero, List.map_nil, VG.WriteBytes.writeBytes_nil]⟩
  refine count_loop hn (VG.Proof.Pbkdf2.Whole.X86.CopyRInv s A B) (fun k hk t h => ?_) i0
  have gb := h.other .ebp (by decide)
  have gd := h.other .edi (by decide)
  have gs := h.other .esi (by decide)
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun t₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_add fun t₂ u₂ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movzx8 (a := A + BitVec.ofNat 64 k)
    (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), gb, h.ecx, addr3 (by omega), eA])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₃ u₃ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun t₄ u₄ => VG.Proof.Sha256.X86.Stream.wp_add fun t₅ u₅ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₅.gpr, u₄.gpr, u₄.other .ecx (by decide), u₃.other .ecx (by decide), u₂.other .ecx (by decide),
      u₁.other .ecx (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gd, h.ecx,
      addr3 (by omega), eB]
        exact congrArg (· + BitVec.ofNat 64 k) (BitVec.add_zero _))
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₆ m₆ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_addi fun t₇ u₇ => VG.Proof.Sha256.X86.Stream.wp_cmp fun t₈ f₈ _ z₈ => WP.block_nil ?_
  have h7 : t₇.gpr .ecx = BitVec.ofNat 32 (k + 1) := by
    rw [u₇.gpr, m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ecx, ofNat_succ32]
  refine ⟨⟨by rw [f₈.rd, u₇.rd, m₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [f₈.wr, u₇.wr, m₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r hr => by
      rw [f₈.gpr, u₇.other r (nm hr .ecx), m₆.gpr, u₅.other r (nm hr .eax), u₄.other r (nm hr .eax),
        u₃.other r (nm hr .edx), u₂.other r (nm hr .eax), u₁.other r (nm hr .eax), h.other r hr],
    by rw [f₈.gpr, h7], ?_⟩, ?_⟩
  · have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
    have v : (t₅.gpr .edx).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, h.mem]
      simp only [VG.WriteBytes.writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega), ↓reduceIte]
      ext i hi; simp
    have e' := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega_using [hk, hn'])
    rw [hl] at e'
    rw [f₈.mem, u₇.mem, m₆.mem, show Reg8.dl.reg = .edx from rfl, v, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
      h.mem, bytesAt_snoc', e']
  · rw [z₈, h7, u₇.other _ (by decide), m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gs, hsi, VG.Proof.Sha256.X86.Stream.sub_beq (by omega) hn']

variable {F : Fns}

section
variable {hF : FnsOK F} {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F)
include hp hz

/-! ## A step: `T`, from `U₁` and `iterate` -/

/-- `T ← U₁`. -/
theorem b6_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) {u : List Byte} (hu : bytesAt s.mem (A s₀ F.uO) F.H.D = u) :
    WP isa (copy .ebp F.uO .ebp F.tO F.H.D) s fun t => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.uO) F.H.D = u ∧ bytesAt t.mem (A s₀ F.tO) F.H.D = u := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D
  refine WP.mono (VG.Proof.Pbkdf2.Whole.X86.copy_part_ok hp hz h.kr hz.D.1 (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨kt, g, m⟩ => ?_
  have f : Frame [sR s₀ F.tO F.H.D] s.mem t.mem := by
    rw [m]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨h.keep hp hz (kt.rd.trans h.kr.rd.symm) (kt.wr.trans h.kr.wr.symm) (fun r hr => g r (by
      simp only [VG.Proof.Pbkdf2.Whole.X86.iregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (.inr ⟨_, _, rfl, by omega, by omega⟩), ?_, ?_⟩
  · rw [bytes_keep f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega)) (by omega) (by omega))
      (by omega_using [hz_D])]
    exact hu
  · rw [m, Hmac.Generic.Common.bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hz_D])]
    exact hu

/-- `iterate`'s arguments: the key's states, `U`, `c - 1` and `T`. -/
theorem b7_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) :
    WP isa (.block F.iterArgs) s fun t => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k t ∧ t.gpr .esi = dO s₀ F.st0O ∧
      t.gpr .eax = dO s₀ F.uO ∧ t.gpr .ecx = VG.X86.arg s₀ 4 - 1 ∧ t.gpr .edx = dO s₀ F.tO ∧ t.mem = s.mem := by
  simp only [Fns.iterArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have i₁ := h.upd hp hz (by decide) u₁
  refine scr_ok i₁.kr fun s₂ u₂ => ?_
  have i₂ := i₁.upd hp hz (by decide) u₂
  refine wp_arg hp i₂.kr (by decide) fun s₃ u₃ => VG.Proof.Sha256.X86.Stream.wp_subi fun s₄ u₄ _ => ?_
  have i₄ := (i₂.upd hp hz (by decide) u₃).upd hp hz (by decide) u₄
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.tO)]
  refine scr_ok i₄.kr fun s₅ u₅ => WP.block_nil ⟨i₄.upd hp hz (by decide) u₅, ?_, ?_, ?_, u₅.gpr, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b8_args {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) (hsi : s.gpr .esi = dO s₀ F.st0O)
    (hax : s.gpr .eax = dO s₀ F.uO) (hcx : s.gpr .ecx = VG.X86.arg s₀ 4 - 1) (hdx : s.gpr .edx = dO s₀ F.tO) :
    ItArgs hF.hH.SH hF.Wt s (dO s₀ F.st0O) (dO s₀ F.uO) (VG.X86.arg s₀ 4 - 1) (dO s₀ F.tO) (VG.Proof.Pbkdf2.Whole.X86.scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have hF_hWt := hF.hWt; have hS := hF.hH.hS; have hD := hF.hH.hD
  have hk := h.kr
  have e0 := dO_addr hp (o := F.st0O) (by omega_using [he, hl])
  have eu := dO_addr hp (o := F.uO) (by omega_using [he, hl])
  have et := dO_addr hp (o := F.tO) (by omega)
  exact
    { esi := hsi
      eax := hax
      ecx := hcx
      edx := hdx
      ebp := hk.ebp
      sp := by rw [hk.esp]; exact hp.sp76
      cr := by
        rw [hS, hD, e0, eu]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · obtain ⟨r', hr', off, e, l⟩ := VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (o := F.st0O) (n := 2 * F.H.S) (by omega_using [he, hl])
            exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
          · obtain ⟨r', hr', off, e, l⟩ := VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (o := F.uO) (n := F.H.D) (by omega_using [he, hl])
            exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [hD, et]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_part hp hk (by omega_using [he, hl])
          · exact VG.Proof.Pbkdf2.Whole.X86.cov_low hp hk (by omega_using [hF_hWt, he, hl])
      k_t := by rw [hS, hD, e0, et]; exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega_using [hl])) (by omega) (by omega)
      k_s := by rw [hS, e0]; exact (low_disj hz (by omega_using [hF_hWt, hl]) (by omega)).symm
      u_t := by rw [hD, eu, et]; exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega_using [hl])) (by omega) (by omega)
      u_s := by rw [hD, eu]; exact (low_disj hz (by omega) (by omega)).symm
      t_s := by rw [hD, et]; exact (low_disj hz (by omega_using [hF_hWt, hl]) (by omega)).symm
      b_k := by rw [hS, e0]; exact VG.Proof.Pbkdf2.Whole.X86.b76 hp hk (part_sub (by omega))
      b_u := by rw [hD, eu]; exact VG.Proof.Pbkdf2.Whole.X86.b76 hp hk (part_sub (by omega))
      b_t := by rw [hD, et]; exact VG.Proof.Pbkdf2.Whole.X86.b76 hp hk (part_sub (by omega))
      b_s := VG.Proof.Pbkdf2.Whole.X86.b76 hp hk (low_sub (by omega))
      nk := by rw [hS, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nu := by rw [hD, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nt := by rw [hD, dO_toNat hp (by omega)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nsc := by have hp_nsc := hp.nsc; omega_using [hp_nsc, hF_hWt, he, hl] }

/-- `iterate`: `T_{k + 1}`. -/
theorem b8_ok {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) (hsi : s.gpr .esi = dO s₀ F.st0O)
    (hax : s.gpr .eax = dO s₀ F.uO) (hcx : s.gpr .ecx = VG.X86.arg s₀ 4 - 1) (hdx : s.gpr .edx = dO s₀ F.tO)
    (hu : bytesAt s.mem (A s₀ F.uO) F.H.D = VG.Proof.Pbkdf2.Whole.X86.prf hF s₀ (VG.Proof.Pbkdf2.Whole.X86.saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (ht : bytesAt s.mem (A s₀ F.tO) F.H.D = VG.Proof.Pbkdf2.Whole.X86.prf hF s₀ (VG.Proof.Pbkdf2.Whole.X86.saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.frame (.push it5) (.call F.itN F.itC) (.pop .eax it5.length)) s fun t => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.tO) F.H.D = VG.Proof.Pbkdf2.Whole.X86.Tk hF s₀ (k + 1) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have hF_hWt := hF.hWt; have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have eu := dO_addr hp (o := F.uO) (by omega)
  have et := dO_addr hp (o := F.tO) (by omega)
  refine it_frame (FnsOK.reprOK hF) (by rw [hS]; omega_using [hz_S]) (by rw [hD]; omega_using [hz_D]) hF.it hF.itSp hF.itSU
    (VG.Proof.Pbkdf2.Whole.X86.b8_args hp hz h hsi hax hcx hdx) fun s' a post => ⟨h.after hp hz a fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [et, hD], by omega_using [hl], by omega⟩
    · exact .inl ⟨_, rfl, by omega_using [hF_hWt]⟩
  · have := post (VG.Proof.Pbkdf2.Whole.X86.K0 hF s₀) (by rw [h.k0l, hB]) (by rw [e0]; exact h.st.st0)
      (by rw [e0, hS, Hmac.Generic.Common.add_ofNat_add]; exact h.st.st1)
    rw [et, hD, eu, hu, ht] at this
    rw [this]
    have hc := hp.c0
    rw [show (VG.X86.arg s₀ 4 - 1).toNat = cc s₀ - 1 by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 1 ≤ (VG.X86.arg s₀ 4).toNat; exact hc)]; rfl]
    rfl

/-! ## A step: copying `T` out -/

omit hp hz in
theorem arg_ofNat (i : Nat) : VG.X86.arg s₀ i = BitVec.ofNat 32 (VG.X86.arg s₀ i).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The bytes of `T` the output still needs. -/
theorem outLen_ok {k : Nat} (hk : k * F.H.D < ol s₀) {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) :
    WP isa F.outLen s fun t => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k t ∧
      t.gpr .ecx = BitVec.ofNat 32 (min (ol s₀ - k * F.H.D) F.H.D) ∧ t.mem = s.mem := by
  have hD := hz.D; have hol : ol s₀ < 2 ^ 32 := (VG.X86.arg s₀ 6).isLt
  have hdn : VG.Proof.Pbkdf2.Whole.X86.dn F s₀ k = k * F.H.D := by show min _ _ = _; omega
  unfold Fns.outLen
  refine WP.seq (wp_arg hp h.kr (by decide) fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_sub fun s₂ u₂ _ => VG.Proof.Sha256.X86.Stream.wp_cmpi fun s₃ f₃ c₃ _ =>
    WP.block_nil ?_)
  have i₃ := ((h.upd hp hz (by decide) u₁).upd hp hz (by decide) u₂).same hp hz f₃.rd f₃.wr
    (fun r _ => by rw [f₃.gpr]) f₃.mem
  have e₃ : s₃.gpr .ecx = BitVec.ofNat 32 (ol s₀ - k * F.H.D) := by
    rw [f₃.gpr, u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.ebx, hdn, VG.Proof.Pbkdf2.Whole.X86.arg_ofNat 6,
      VG.Proof.Sha256.X86.Stream.sub_ofNat (by have : ol s₀ = (VG.X86.arg s₀ 6).toNat := rfl; omega)]
  have m₃ : s₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  have cf : s₃.cf = some (decide (ol s₀ - k * F.H.D < F.H.D)) := by
    rw [c₃, ← f₃.gpr, e₃, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
  refine WP.ite (decide (ol s₀ - k * F.H.D < F.H.D)) (by show s₃.cf = _; rw [cf]) (fun hT => WP.block_nil ?_)
    fun hF' => VG.Proof.Sha256.X86.Stream.wp_movi fun s₄ u₄ => WP.block_nil ⟨i₃.upd hp hz (by decide) u₄, ?_, by rw [u₄.mem, m₃]⟩
  · have : ol s₀ - k * F.H.D < F.H.D := of_decide_eq_true hT
    exact ⟨i₃, by rw [e₃, Nat.min_eq_left (Nat.le_of_lt this)], m₃⟩
  · have : ¬ ol s₀ - k * F.H.D < F.H.D := of_decide_eq_false hF'
    rw [u₄.gpr, Nat.min_eq_right (by omega)]

/-- Copying `n` bytes of `T` to `out` after the `k D` written. -/
theorem outLoop_ok {k n : Nat} (hn : 0 < n) (hkn : k * F.H.D + n ≤ ol s₀) (hnD : n ≤ F.H.D) {s : State}
    (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) (hcx : s.gpr .ecx = BitVec.ofNat 32 n) (hkD : k * F.H.D < ol s₀) :
    WP isa F.outLoop s fun t => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ t ∧ t.gpr .ebx = s.gpr .ebx ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      t.mem = VG.WriteBytes.writeBytes s.mem ((VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D))
        (bytesAt s.mem (A s₀ F.tO) n) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hD := hz.D
  have hol : ol s₀ < 2 ^ 32 := (VG.X86.arg s₀ 6).isLt
  have hdn : VG.Proof.Pbkdf2.Whole.X86.dn F s₀ k = k * F.H.D := by show min _ _ = _; omega_using [hkn]
  have hno := hp.no
  have eO : (VG.Proof.Pbkdf2.Whole.X86.out s₀ + BitVec.ofNat 32 (k * F.H.D)).setWidth 64 = (VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D) :=
    Pbkdf2.Stream.X86.setWidth_add (by have : ol s₀ = (VG.X86.arg s₀ 6).toNat := rfl; omega_using [hno, hkn, hn])
  have tO' : (VG.Proof.Pbkdf2.Whole.X86.out s₀ + BitVec.ofNat 32 (k * F.H.D)).toNat = (VG.Proof.Pbkdf2.Whole.X86.out s₀).toNat + k * F.H.D :=
    Pbkdf2.Stream.X86.toNat_add_ofNat (by have : ol s₀ = (VG.X86.arg s₀ 6).toNat := rfl; omega)
  have osub : Region.Sub ⟨(VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩ (VG.Proof.Pbkdf2.Whole.X86.outR s₀) :=
    Offset.sub_base _ hkn
  unfold Fns.outLoop
  refine WP.seq (VG.Proof.Sha256.X86.Stream.wp_mov fun s₁ u₁ => wp_arg hp (h.kr.upd (by decide) u₁) (by decide) fun s₂ u₂ => VG.Proof.Sha256.X86.Stream.wp_add fun s₃ u₃ =>
    VG.Proof.Sha256.X86.Stream.wp_movi fun s₄ u₄ => WP.block_nil ?_)
  have k₄ := (((h.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  have e₄si : s₄.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hcx]
  have e₄di : s₄.gpr .edi = VG.Proof.Pbkdf2.Whole.X86.out s₀ + BitVec.ofNat 32 (k * F.H.D) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ebx, hdn]
  have e₄bx : s₄.gpr .ebx = s.gpr .ebx := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hL := L8_le hz; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (VG.Proof.Pbkdf2.Whole.X86.copyR_ok (so := F.tO) hn (by omega_using [hD, hnD]) e₄si u₄.gpr
    (by rw [k₄.ebp]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl, hnD]) (by rw [e₄di, tO']; omega_using [hno, hkn])
    (fun j hj => by
      rw [k₄.ebp]
      exact ⟨VG.Proof.Pbkdf2.Whole.X86.scR s₀ F, List.mem_append_right _ (by rw [k₄.wr]; exact sc_mem hp),
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega_using [hj, hL, he, hl, hnD])⟩)
    (fun j hj => by
      rw [e₄di, eO]
      exact ⟨VG.Proof.Pbkdf2.Whole.X86.outR s₀, by rw [k₄.wr, hp.wr]; simp, by
        rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega_using [hj, hkn]) (by omega_using [hj, hol, hkn])⟩)
    (by rw [k₄.ebp, e₄di, eO]
        exact (hp.o_s.sub_left osub).symm.sub_left (part_sub (F := F) (by omega_using [he, hl, hnD])))) fun t c => ?_
  rw [k₄.ebp, e₄di, eO] at c
  have cm : t.mem = VG.WriteBytes.writeBytes s.mem ((VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D))
      (bytesAt s.mem (A s₀ F.tO) n) := by rw [c.mem, m₄]
  have f : Frame [⟨(VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩] s₄.mem t.mem := by
    rw [cm, m₄]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨k₄.keep c.rd c.wr (fun r hr => c.other r (by
      simp only [VG.Proof.Pbkdf2.Whole.X86.kregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide))
    (rs := [⟨(VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩]) f
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.o_s.sub_left osub).symm.sub_left (sv_sub hz))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, osub⟩),
    by rw [c.other _ (by decide), e₄bx], by rw [c.other _ (by decide), e₄si], cm⟩

/-- The rest of a step: as much of `T` as the output needs, copied out,
`INT (k + 2)`, and whether that was the last block. -/
theorem tail_ok {k : Nat} (hk : k < VG.Proof.Pbkdf2.Whole.X86.nbk F s₀) {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s)
    (ht : bytesAt s.mem (A s₀ F.tO) F.H.D = VG.Proof.Pbkdf2.Whole.X86.Tk hF s₀ (k + 1)) :
    WP isa (.seq F.outLen (.seq F.outLoop (.block F.advance))) s fun t =>
      VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ (k + 1) t ∧ t.zf = some (decide (k + 1 = VG.Proof.Pbkdf2.Whole.X86.nbk F s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hD := hz.D
  have hol : ol s₀ < 2 ^ 32 := (VG.X86.arg s₀ 6).isLt
  have hno := hp.no
  have hkD : k * F.H.D < ol s₀ := (Whole.lt_nb hD.1).1 hk
  have hdn : VG.Proof.Pbkdf2.Whole.X86.dn F s₀ k = k * F.H.D := by show min _ _ = _; omega
  generalize en : min (ol s₀ - k * F.H.D) F.H.D = n
  have hn : 0 < n := by omega_using [en, hkD, hD]
  have hkn : k * F.H.D + n ≤ ol s₀ := by omega_using [en, hkD]
  have hnD : n ≤ F.H.D := by omega_using [en]
  have hdn' : VG.Proof.Pbkdf2.Whole.X86.dn F s₀ (k + 1) = k * F.H.D + n := by show min _ _ = _; rw [Nat.succ_mul]; omega_using [en, hkD]
  have osub : Region.Sub ⟨(VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩ (VG.Proof.Pbkdf2.Whole.X86.outR s₀) :=
    Offset.sub_base _ hkn
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.outLen_ok hp hz hkD h) fun s₁ ⟨i₁, c₁, m₁⟩ => ?_)
  rw [en] at c₁
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.outLoop_ok hp hz hn hkn hnD i₁ c₁ hkD) fun s₂ ⟨k₂, b₂, e₂, m₂⟩ => ?_)
  unfold Fns.advance
  refine VG.Proof.Sha256.X86.Stream.wp_add fun s₃ u₃ => ?_
  have k₃ := k₂.upd (by decide) u₃
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := A s₀ F.intO) (VG.Proof.Pbkdf2.Whole.X86.ea_scr hp k₃ (by omega_using [he])) (by
      obtain ⟨r, hr, c⟩ := in_sc hp hz k₃.wr (o := F.intO) (n := 4) (by omega)
      exact ⟨r, List.mem_append_right _ hr, c⟩)
    fun s₄ u₄ => VG.Proof.Sha256.X86.Stream.wp_bswap fun s₅ u₅ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₆ u₆ => VG.Proof.Sha256.X86.Stream.wp_bswap fun s₇ u₇ => ?_
  have k₇ := (((k₃.upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆).upd (by decide) u₇
  refine VG.Proof.Sha256.X86.Stream.wp_store (a := A s₀ F.intO) (VG.Proof.Pbkdf2.Whole.X86.ea_scr hp k₇ (by omega)) (in_sc hp hz k₇.wr (by omega)) fun s₈ m₈ => ?_
  have fr₈ : Frame [sR s₀ F.intO 4] s₇.mem s₈.mem := by
    rw [m₈.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₈ := k₇.write hz m₈.rd m₈.wr (fun r _ => by rw [m₈.gpr]) (by omega) (by omega) fr₈
  refine wp_arg hp k₈ (by decide) fun s₉ u₉ => VG.Proof.Sha256.X86.Stream.wp_cmp fun s₁₀ f₁₀ _ z₁₀ => WP.block_nil ?_
  have m₁₀ : s₁₀.mem = s₂.mem.writeW (A s₀ F.intO) (s₇.gpr .eax) := by
    rw [f₁₀.mem, u₉.mem, m₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have fr₂ : Frame [sR s₀ F.intO 4] s₂.mem s₁₀.mem := by
    rw [m₁₀]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fr₁ : Frame [⟨(VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have dI : (sR s₀ F.intO 4).Disjoint ⟨(VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩ :=
    ((hp.o_s.sub_left osub).sub_right (part_sub (by omega))).symm
  have r₂ : s₂.mem.readW (A s₀ F.intO) 32 = byteRev32 (BitVec.ofNat 32 (k + 1)) := by
    rw [← i₁.intW]
    exact fr₁.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dI) (by decide)
  have e₇ : s₇.gpr .eax = byteRev32 (BitVec.ofNat 32 (k + 1 + 1)) := by
    rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.mem, r₂, VG.Proof.Pbkdf2.Whole.X86.bswap_eq, VG.Proof.Pbkdf2.Whole.X86.bswap_eq, Whole.byteRev32_byteRev32, ofNat_succ32]
  have e₉ : s₉.gpr .ebx = BitVec.ofNat 32 (k * F.H.D + n) := by
    rw [u₉.other _ (by decide), m₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, b₂, e₂, i₁.ebx, hdn, ← BitVec.ofNat_add]
  have hg : (VG.Proof.Pbkdf2.Whole.X86.Gk hF s₀ (k + 1)) = VG.Proof.Pbkdf2.Whole.X86.Gk hF s₀ k ++ VG.Proof.Pbkdf2.Whole.X86.Tk hF s₀ (k + 1) := Whole.G_succ _ _ _ _
  have tl : (VG.Proof.Pbkdf2.Whole.X86.Tk hF s₀ (k + 1)).length = F.H.D := by rw [← ht, bytesAt_length]
  refine ⟨⟨(k₈.upd (by decide) u₉).same f₁₀.rd f₁₀.wr (fun r _ => by rw [f₁₀.gpr]) f₁₀.mem, ?_, i₁.k0l,
    by rw [f₁₀.gpr, e₉, hdn'], by rw [m₁₀, Mem.readW_writeW_self32, e₇], ?_, ?_⟩, ?_⟩
  · refine i₁.st.keep hz (rs := [⟨(VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩, sR s₀ F.intO 4])
      ((fr₁.mono (by simp)).trans (fr₂.mono (by simp))) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.o_s.sub_left osub).sub_right (part_sub (by omega_using [he, hl]))).symm
    · exact VG.Proof.Pbkdf2.Whole.X86.part_disj hz (Or.inl (by omega_using [hl])) (by omega) (by omega)
  · rw [hg, List.length_append, i₁.glen, tl, Nat.succ_mul]
  · have osub' : Region.Sub ⟨(VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64, k * F.H.D + n⟩ (VG.Proof.Pbkdf2.Whole.X86.outR s₀) := Region.sub_prefix hkn
    rw [hdn', bytes_keep fr₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.o_s.sub_left osub').sub_right (part_sub (by omega))) (by omega_using [en, hkD, hol]), m₂]
    have bw := VG.Proof.Sha256.Stream.bytesAt_writeBytes s₁.mem ((VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64) (k * F.H.D) (bytesAt s₁.mem (A s₀ F.tO) n)
      (by rw [bytesAt_length]; omega_using [en, hkD, hol])
    rw [bytesAt_length] at bw
    have ob := i₁.outB
    rw [hdn] at ob
    rw [bw, ob, Hmac.Generic.Common.bytesAt_take _ _ hnD, m₁, ht, hg, List.take_append,
      i₁.glen, Nat.add_sub_cancel_left, List.take_of_length_le (l := VG.Proof.Pbkdf2.Whole.X86.Gk hF s₀ k) (i := k * F.H.D) (by rw [i₁.glen]),
      List.take_of_length_le (l := VG.Proof.Pbkdf2.Whole.X86.Gk hF s₀ k) (i := k * F.H.D + n) (by rw [i₁.glen]; omega_using [])]
  · rw [z₁₀, e₉, u₉.gpr, VG.Proof.Pbkdf2.Whole.X86.arg_ofNat 6, VG.Proof.Sha256.X86.Stream.sub_beq (by omega_using [en, hkD, hol]) (by omega)]
    have e1 : k + 1 < VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ ↔ (k + 1) * F.H.D < ol s₀ := Whole.lt_nb hD.1
    rw [Nat.succ_mul] at e1
    have : (VG.X86.arg s₀ 6).toNat = ol s₀ := rfl
    refine congrArg some (decide_eq_decide.2 ⟨fun h1 => ?_, fun h1 => ?_⟩)
    · by_contra h2
      have := e1.1 (by omega_using [h2, hk])
      omega
    · have : ¬ (k * F.H.D + F.H.D < ol s₀) := fun h' => absurd (e1.2 h') (by omega)
      omega

/-! ## The loop and `pbkdf2` -/

/-- A block of the output. -/
theorem block_ok {k : Nat} (hk : k < VG.Proof.Pbkdf2.Whole.X86.nbk F s₀) {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) :
    WP isa F.block s fun t => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ (k + 1) t ∧ t.zf = some (decide (k + 1 = VG.Proof.Pbkdf2.Whole.X86.nbk F s₀)) := by
  unfold Fns.block
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.b1_ok hp hz h) fun s₁ ⟨i₁, r₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.b2_ok hp hz i₁) fun s₂ ⟨i₂, di, si, ax, cx, dx, m₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.b3_ok hp hz i₂ di si ax cx dx (by rw [m₂]; exact r₁)) fun s₃ ⟨i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.b4_ok hp hz i₃) fun s₄ ⟨i₄, dx, si, ax, cx, di, m₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.b5_ok hp hz i₄ dx si ax cx di (by rw [m₄]; exact r₃)) fun s₅ ⟨i₅, u₅⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.b6_ok hp hz i₅ u₅) fun s₆ ⟨i₆, u₆, t₆⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.b7_ok hp hz i₆) fun s₇ ⟨i₇, si, ax, cx, dx, m₇⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.b8_ok hp hz i₇ si ax cx dx (by rw [m₇]; exact u₆) (by rw [m₇]; exact t₆))
    fun s₈ ⟨i₈, t₈⟩ => ?_)
  exact VG.Proof.Pbkdf2.Whole.X86.tail_ok hp hz hk i₈ t₈

/-- The loop over the blocks of the output, if there are any. -/
theorem loop_ok {s : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ 0 s) (hz' : s.zf = some (decide (ol s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop F.block .ne)) s (VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ (VG.Proof.Pbkdf2.Whole.X86.nbk F s₀)) := by
  have hD := hz.D
  have e0 : VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ = 0 ↔ ol s₀ = 0 := Whole.nb_zero hD.1
  refine WP.ite (decide (ol s₀ = 0)) (by show VG.X86.eval .e s = _; rw [VG.Proof.Sha256.X86.Stream.eval_e, hz'])
    (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · rw [e0.2 (of_decide_eq_true h0)]; exact h
  · have hpos : 0 < VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ := by
      have := of_decide_eq_false h0; have : VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ ≠ 0 := fun e => this (e0.1 e); omega
    exact count_loop hpos (VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀) (fun k hk t ht => VG.Proof.Pbkdf2.Whole.X86.block_ok hp hz hk ht) h

theorem correct : WP isa F.pbkdf2 s₀ fun s' => abiPreserved s₀ s' ∧ (pbkG hF.hH.SH (F.W + F.H.S)).post s₀ s' := by
  have hD := hz.D
  unfold Fns.pbkdf2
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.prologue_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.keyed_ok (hF := hF) hp hz k₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.setup_ok hp hz hF h₂) fun s₃ ⟨k₃, st₃, kl₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.loopInit_ok hp hz k₃ st₃ kl₃) fun s₄ ⟨i₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Whole.X86.loop_ok hp hz i₄ z₄) fun s₅ h₅ => ?_)
  have k₅ := h₅.kr
  have hL := L8_le hz; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (Pbkdf2.Stream.X86.restore_ok F.L k₅.ebp k₅.saved (by rw [k₅.wr]; exact sc_mem hp)
    (show 8 * F.W + 16 ≤ F.L8 by have hz_fits := hz.fits; omega) hp.nsc)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm]; exact k₅.ret hp⟩, ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), k₅.esp]
    · exact hg r (Pbkdf2.Stream.X86.callee_saved r hr he)
  · have ob := h₅.outB
    have e : VG.Proof.Pbkdf2.Whole.X86.dn F s₀ (VG.Proof.Pbkdf2.Whole.X86.nbk F s₀) = ol s₀ := Whole.done_nb hD.1
    rw [e] at ob
    show Spec.Pbkdf2.pbkdf2Hmac _ _ _ _ _ = some (bytesAt s'.mem _ _)
    unfold Spec.Pbkdf2.pbkdf2Hmac
    rw [hF.hH.hD]
    exact Whole.pbkdf2_eq (VG.Proof.Pbkdf2.Whole.X86.prf hF s₀) (VG.Proof.Pbkdf2.Whole.X86.saltB s₀) hp.olD (by rw [hm, ob])

end

end VG.Proof.Pbkdf2.Whole.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.X86.CT`. -/
section

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: constant time

As for `iterate` (`Proof/Pbkdf2/Md/X86/IterateCT.lean`): the pieces of code
between the calls are checked by the taint analysis (`Checks`, which the
kernel evaluates for each hash function), with the arguments, `esp`, `ebp`
and, in the loop over the blocks, `ebx` public (`piece`); the calls are
related by their contracts (`init_rel`, `upd_rel`, `fin_rel`, `hi_rel`,
`hf_rel`, `it_rel`), whose public arguments are the same in two runs with the
same public arguments (`PubEq`). The branches (whether the password is hashed,
and the loop over the blocks) depend only on the lengths.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_ copy)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK argTaint ArgsOut agree_argTaint rel_agree rel_wp init_rel upd_rel fin_rel)
open VG.Proof.Sha256.X86.Stream (eval_e eval_ne)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad)
open VG.Proof.Hmac.Common (bytesAt_length)

/-- A piece of code the taint analysis accepts with the arguments and `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (argTaint rs (4 + 4 * 8)) c hc).isSome = true

/-- The taint checks of the pieces of `pbkdf2` between its calls. -/
structure Checks (F : Fns) : Prop where
  pro : VG.Proof.Pbkdf2.Whole.X86.Ck [] (.block F.prologue)
  cmp : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp] (.block F.cmpPw)
  hk1 : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp] (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stWO))
  hk3 : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp] (.block [.mov .eax (.imm 0), .mov .esi (.imm 0), .mov .ecx (Fns.argM 1), .mov .edx (Fns.argM 0)])
  hk5 : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp] (.block ([.mov .eax (Fns.argM 1), .mov .ecx (.imm 0)] ++ VG.Impl.Pbkdf2.Stream.X86.scr .edx F.hkO))
  hk7 : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp]
    (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.hkO ++ [.mov .ecx (.imm (BitVec.ofNat 32 F.H.D))]))
  short : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp] (.block [.mov .edx (Fns.argM 0)])
  su1 : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp] (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.st0O ++ VG.Impl.Pbkdf2.Stream.X86.scr .esi F.st1O))
  su3 : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp] (copy .ebp F.st0O .ebp F.stSO F.H.S)
  su4 : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp] (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stSO ++ [.mov .eax (.imm 0),
      .mov .esi (.imm (BitVec.ofNat 32 F.H.B)), .mov .ecx (Fns.argM 3), .mov .edx (Fns.argM 2)]))
  init : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp] (.block F.loopInit)
  b1 : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp, .ebx] (copy .ebp F.stSO .ebp F.stWO F.H.S)
  b2 : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp, .ebx] (.block F.updArgs)
  b4 : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp, .ebx] (.block F.finArgs)
  b6 : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp, .ebx] (copy .ebp F.uO .ebp F.tO F.H.D)
  b7 : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp, .ebx] (.block F.iterArgs)
  tail : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp, .ebx] (.seq F.outLen (.seq F.outLoop (.block F.advance)))
  restore : VG.Proof.Pbkdf2.Whole.X86.Ck [.ebp] (.block F.L.restore)

/-- The public arguments of two runs are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : VG.Proof.Pbkdf2.Whole.X86.E s₀ = VG.Proof.Pbkdf2.Whole.X86.E s₀'
  args : ∀ i < 8, VG.X86.arg s₀ i = VG.X86.arg s₀' i

variable {F : Fns}

section
variable {s₀ s₀' : State} (hq : VG.Proof.Pbkdf2.Whole.X86.PubEq s₀ s₀')
include hq

theorem PubEq.a {i : Nat} (hi : i < 8) : VG.X86.arg s₀' i = VG.X86.arg s₀ i := (hq.args i hi).symm

/-- `s₀'`'s public values are `s₀`'s. -/
macro "pub_simp" hq:term " at " h:ident : tactic => `(tactic|
  simp only [dO, A, scr, pw, salt, pwl, sl, ol, cc, out, kp, kl, nbk, dn, PubEq.a $hq (i := 0) (by decide),
    PubEq.a $hq (i := 1) (by decide), PubEq.a $hq (i := 2) (by decide), PubEq.a $hq (i := 3) (by decide),
    PubEq.a $hq (i := 4) (by decide), PubEq.a $hq (i := 5) (by decide), PubEq.a $hq (i := 6) (by decide),
    PubEq.a $hq (i := 7) (by decide)] at $h:ident)

theorem PubEq.E' : VG.Proof.Pbkdf2.Whole.X86.E s₀' = VG.Proof.Pbkdf2.Whole.X86.E s₀ := hq.esp.symm
theorem PubEq.scrEq : VG.Proof.Pbkdf2.Whole.X86.scr s₀' = VG.Proof.Pbkdf2.Whole.X86.scr s₀ := hq.a (by decide)
theorem PubEq.pwlEq : pwl s₀' = pwl s₀ := by show (VG.X86.arg s₀' 1).toNat = _; rw [hq.a (by decide)]
theorem PubEq.olEq : ol s₀' = ol s₀ := by show (VG.X86.arg s₀' 6).toNat = _; rw [hq.a (by decide)]
theorem PubEq.nbkEq : VG.Proof.Pbkdf2.Whole.X86.nbk F s₀' = VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ := by show Whole.nb _ (ol s₀') = _; rw [hq.olEq]
theorem PubEq.dnEq (k : Nat) : VG.Proof.Pbkdf2.Whole.X86.dn F s₀' k = VG.Proof.Pbkdf2.Whole.X86.dn F s₀ k := by show Whole.done _ (ol s₀') k = _; rw [hq.olEq]

end

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : VG.Proof.Pbkdf2.Whole.X86.Pre F t) {s : State} (hsp : s.gpr .esp = VG.Proof.Pbkdf2.Whole.X86.E t) (hwr : s.wr = t.wr) :
    ArgsOut 8 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 8⟩ : Region) = ⟨(VG.Proof.Pbkdf2.Whole.X86.E t).setWidth 64, 4 + 32⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_o h.o_a.symm
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_s h.s_a.symm

section
variable {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hp' : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀') (hq : VG.Proof.Pbkdf2.Whole.X86.PubEq s₀ s₀')
include hp hp' hq

/-- A piece of code the taint analysis accepts, between states that keep `KR`. -/
theorem piece {rs : List Reg} {c : Prog isa} (P G : State → State → Prop)
    (hk : ∀ {t₀ s}, P t₀ s → VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s)
    (hag : ∀ s s', P s₀ s → P s₀' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : VG.Proof.Pbkdf2.Whole.X86.Ck rs c) (hw : ∀ {t₀}, VG.Proof.Pbkdf2.Whole.X86.Pre F t₀ → ∀ s, P t₀ s → WP isa c s (G t₀)) :
    RelCT isa (fun s s' => P s₀ s ∧ P s₀' s') c fun s s' => G s₀ s ∧ G s₀' s' :=
  rel_agree _ (fun s s' h h' => agree_argTaint (hag s s' h h')
      (by rw [(hk h).esp, (hk h').esp, hq.esp])
      (VG.Proof.Pbkdf2.Whole.X86.args_out hp (hk h).esp (hk h).wr) (VG.Proof.Pbkdf2.Whole.X86.args_out hp' (hk h').esp (hk h').wr)
      fun i hi => by rw [(hk h).argEq hp hi, (hk h').argEq hp' hi, hq.args i hi]) hc (hw hp) (hw hp')

omit hp hp' in
theorem ag_ebp {s s' : State} (h : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (h' : VG.Proof.Pbkdf2.Whole.X86.KR F s₀' s') : ∀ r ∈ [Reg.ebp], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [h.ebp, h'.ebp, hq.scrEq]

end

/-! ## The key -/

/-- The password is longer than a block. -/
abbrev Long (F : Fns) (t₀ : State) : Prop := F.H.B + 1 ≤ pwl t₀

/-- The pieces of hashing the password: the state for its digest, then
`update` with the password, then `finalize`. -/
abbrev Hk1 (F : Fns) (t₀ s : State) : Prop := (VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stWO) ∧ VG.Proof.Pbkdf2.Whole.X86.Long F t₀
abbrev Hk2 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s ∧ hH.SH.Repr s.mem (A t₀ F.stWO) [] ∧ s.gpr .edi = dO t₀ F.stWO) ∧ VG.Proof.Pbkdf2.Whole.X86.Long F t₀
abbrev Hk3 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stWO ∧ s.gpr .esi = 0 ∧ s.gpr .eax = 0 ∧ s.gpr .ecx = VG.X86.arg t₀ 1 ∧
    s.gpr .edx = pw t₀ ∧ hH.SH.Repr s.mem (A t₀ F.stWO) []) ∧ VG.Proof.Pbkdf2.Whole.X86.Long F t₀
abbrev Hk4 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s ∧ hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem ((pw t₀).setWidth 64) (pwl t₀)) ∧
    s.gpr .edi = dO t₀ F.stWO) ∧ VG.Proof.Pbkdf2.Whole.X86.Long F t₀
abbrev Hk5 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stWO ∧ s.gpr .eax = VG.X86.arg t₀ 1 ∧ s.gpr .ecx = 0 ∧ s.gpr .edx = dO t₀ F.hkO ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem ((pw t₀).setWidth 64) (pwl t₀))) ∧ VG.Proof.Pbkdf2.Whole.X86.Long F t₀
abbrev Hk6 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s ∧ bytesAt s.mem (A t₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt t₀.mem ((pw t₀).setWidth 64) (pwl t₀))) ∧
    VG.Proof.Pbkdf2.Whole.X86.Long F t₀

/-- After `cmp`. -/
abbrev Cmp (F : Fns) (t₀ s : State) : Prop :=
  VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s ∧ s.gpr .ecx = VG.X86.arg t₀ 1 ∧ s.cf = some (decide (pwl t₀ < F.H.B + 1))

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hp' : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀') (hq : VG.Proof.Pbkdf2.Whole.X86.PubEq s₀ s₀') (hc : VG.Proof.Pbkdf2.Whole.X86.Checks F)
include hp hp' hq hc

theorem hashKey_rel :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Long F s₀) ∧ (VG.Proof.Pbkdf2.Whole.X86.KR F s₀' s' ∧ VG.Proof.Pbkdf2.Whole.X86.Long F s₀')) F.hashKey
      fun s s' => VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀' s' := by
  have hz := hF.sizes
  have hl := layout (F := F); have he := end_le hz; have := hz.D
  unfold Fns.hashKey
  have r1 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (fun t₀ s => VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Long F t₀) (VG.Proof.Pbkdf2.Whole.X86.Hk1 F) (fun h => h.1)
    (fun s s' h h' => VG.Proof.Pbkdf2.Whole.X86.ag_ebp hq h.1 h'.1) hc.hk1
    (fun _ s h => WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk1_ok h.1) fun t ⟨k, d, _⟩ => ⟨⟨k, d⟩, h.2⟩)
  have r2 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.X86.Hk1 F s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Hk1 F s₀' s') (F.H.callInit .edi)
      fun s s' => VG.Proof.Pbkdf2.Whole.X86.Hk2 hF.hH s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Hk2 hF.hH s₀' s' :=
    rel_wp (init_rel hF.hH (sp := VG.Proof.Pbkdf2.Whole.X86.E s₀) (st := dO s₀ F.stWO) fun s s' ⟨⟨⟨k, d⟩, _⟩, ⟨⟨k', d'⟩, _⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.X86.hk2_args hp hz k d, by have := VG.Proof.Pbkdf2.Whole.X86.hk2_args hp' hz k' d'; pub_simp hq at this; exact this, k.esp,
          by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk2_ok hp hz hF.hH k d) fun t ⟨k', r, e⟩ => ⟨⟨k', r, e.trans d⟩, l⟩)
      (fun s ⟨⟨k, d⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk2_ok hp' hz hF.hH k d) fun t ⟨k', r, e⟩ => ⟨⟨k', r, e.trans d⟩, l⟩)
  have r3 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.X86.Hk2 hF.hH) (VG.Proof.Pbkdf2.Whole.X86.Hk3 hF.hH) (fun h => h.1.1) (fun s s' h h' => VG.Proof.Pbkdf2.Whole.X86.ag_ebp hq h.1.1 h'.1.1) hc.hk3
    (fun hp₀ s ⟨⟨k, r, d⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk3_ok hp₀ k d) fun t ⟨k', d', i, a, c, x, m⟩ =>
      ⟨⟨k', d', i, a, c, x, by rw [m]; exact r⟩, l⟩)
  have r4 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.X86.Hk3 hF.hH s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Hk3 hF.hH s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6))
      fun s s' => VG.Proof.Pbkdf2.Whole.X86.Hk4 hF.hH s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Hk4 hF.hH s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := VG.Proof.Pbkdf2.Whole.X86.E s₀) fun s s' ⟨⟨⟨k, d, i, a, c, x, _⟩, _⟩, ⟨⟨k', d', i', a', c', x', _⟩, _⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.X86.hk4_args hp hz hF.hH k d i a c x,
          by have := VG.Proof.Pbkdf2.Whole.X86.hk4_args hp' hz hF.hH k' d' i' a' c' x'; pub_simp hq at this; exact this,
          k.esp, by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d, i, a, c, x, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk4_ok hp hz hF.hH k d i a c x r) fun t ⟨k', r', e⟩ =>
        ⟨⟨k', r', e.trans d⟩, l⟩)
      (fun s ⟨⟨k, d, i, a, c, x, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk4_ok hp' hz hF.hH k d i a c x r) fun t ⟨k', r', e⟩ =>
        ⟨⟨k', r', e.trans d⟩, l⟩)
  have r5 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.X86.Hk4 hF.hH) (VG.Proof.Pbkdf2.Whole.X86.Hk5 hF.hH) (fun h => h.1.1) (fun s s' h h' => VG.Proof.Pbkdf2.Whole.X86.ag_ebp hq h.1.1 h'.1.1) hc.hk5
    (fun hp₀ s ⟨⟨k, r, d⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk5_ok hp₀ k d) fun t ⟨k', d', a, c, x, m⟩ =>
      ⟨⟨k', d', a, c, x, by rw [m]; exact r⟩, l⟩)
  have r6 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.X86.Hk5 hF.hH s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Hk5 hF.hH s₀' s')
      (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call F.H.finN F.H.finC) (.pop .eax 5))
      fun s s' => VG.Proof.Pbkdf2.Whole.X86.Hk6 hF.hH s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Hk6 hF.hH s₀' s' :=
    rel_wp (fin_rel hF.hH (sp := VG.Proof.Pbkdf2.Whole.X86.E s₀) fun s s' ⟨⟨⟨k, d, a, c, x, _⟩, _⟩, ⟨⟨k', d', a', c', x', _⟩, _⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.X86.hk6_args hp hz hF.hH k d a c x,
          by have := VG.Proof.Pbkdf2.Whole.X86.hk6_args hp' hz hF.hH k' d' a' c' x'; pub_simp hq at this; exact this,
          k.esp, by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d, a, c, x, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk6_ok hp hz hF.hH k d a c x r) fun t h => ⟨h, l⟩)
      (fun s ⟨⟨k, d, a, c, x, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk6_ok hp' hz hF.hH k d a c x r) fun t h => ⟨h, l⟩)
  have r7 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.X86.Hk6 hF.hH) (VG.Proof.Pbkdf2.Whole.X86.Keyed hF) (fun h => h.1.1) (fun s s' h h' => VG.Proof.Pbkdf2.Whole.X86.ag_ebp hq h.1.1 h'.1.1) hc.hk7
    (fun {t₀} hp₀ s ⟨⟨k, b⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.hk7_ok k) fun t ⟨k', d, c, m⟩ => by
      have hlt : ¬ pwl t₀ < F.H.B + 1 := by omega
      have ekp : VG.Proof.Pbkdf2.Whole.X86.kp F t₀ = dO t₀ F.hkO := by simp only [VG.Proof.Pbkdf2.Whole.X86.kp, hlt, ↓reduceIte]
      have ekl : VG.Proof.Pbkdf2.Whole.X86.kl F t₀ = F.H.D := by simp only [VG.Proof.Pbkdf2.Whole.X86.kl, hlt, ↓reduceIte]
      refine ⟨k', by rw [ekp]; exact d, by rw [ekl]; exact c, ?_⟩
      rw [ekp, ekl, dO_addr hp₀ (by omega), m, b, VG.Proof.Pbkdf2.Whole.X86.blockKey_hash hz hF.hH (by rw [bytesAt_length]; omega)
        (VG.Proof.Pbkdf2.Whole.X86.hash_len hF.hH b)])
  exact r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))

theorem key_rel :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.KR F s₀' s') F.key fun s s' => VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀' s' := by
  have hz := hF.sizes
  unfold Fns.key
  have rc := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (fun t₀ s => VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s) (VG.Proof.Pbkdf2.Whole.X86.Cmp F) id (fun s s' h h' => VG.Proof.Pbkdf2.Whole.X86.ag_ebp hq h h') hc.cmp
    (fun hp₀ s k => WP.mono (VG.Proof.Pbkdf2.Whole.X86.cmp_ok hp₀ hz k) fun t ⟨k', c, f, _⟩ => ⟨k', c, f⟩)
  have ev : ∀ {t₀ t : State}, VG.Proof.Pbkdf2.Whole.X86.Cmp F t₀ t → isa.eval .ae t = some (decide (F.H.B + 1 ≤ pwl t₀)) := by
    intro t₀ t h
    show t.cf.map (!·) = _
    rw [h.2.2]; simp only [Option.map_some, ← decide_not, Nat.not_lt]
  refine rc.seq (RelCT.ite (fun s s' h => by rw [ev h.1, ev h.2, hq.pwlEq]) ?_ ?_)
  · refine (VG.Proof.Pbkdf2.Whole.X86.hashKey_rel hp hp' hq hc).mono (fun s s' h => ?_) fun _ _ h => h
    have := of_decide_eq_true ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
    exact ⟨⟨h.1.1.1, this⟩, h.1.2.1, by show F.H.B + 1 ≤ pwl s₀'; rw [hq.pwlEq]; exact this⟩
  · refine (VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (fun t₀ s => VG.Proof.Pbkdf2.Whole.X86.Cmp F t₀ s ∧ pwl t₀ < F.H.B + 1) (VG.Proof.Pbkdf2.Whole.X86.Keyed hF) (fun h => h.1.1)
      (fun s s' h h' => VG.Proof.Pbkdf2.Whole.X86.ag_ebp hq h.1.1 h'.1.1) hc.short (fun {t₀} hp₀ s ⟨⟨k, c, _⟩, hlt⟩ => ?_)).mono
      (fun s s' h => ?_) fun _ _ h => h
    · have ekp : VG.Proof.Pbkdf2.Whole.X86.kp F t₀ = pw t₀ := by simp only [VG.Proof.Pbkdf2.Whole.X86.kp, hlt, ↓reduceIte]
      have ekl : VG.Proof.Pbkdf2.Whole.X86.kl F t₀ = pwl t₀ := by simp only [VG.Proof.Pbkdf2.Whole.X86.kl, hlt, ↓reduceIte]
      refine wp_arg hp₀ k (by decide) fun s₂ u₂ => WP.block_nil ⟨k.upd (by decide) u₂, by rw [u₂.gpr, ekp], ?_, ?_⟩
      · rw [u₂.other _ (by decide), c, ekl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rw [u₂.mem, ekp, ekl, k.pwBytes hp₀]
    · have := of_decide_eq_false ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
      have hlt : pwl s₀ < F.H.B + 1 := by omega
      exact ⟨⟨h.1.1, hlt⟩, h.1.2, by rw [hq.pwlEq]; exact hlt⟩

end

/-! ## HMAC's states for the key, and the salt -/

abbrev Su1 (hF : FnsOK F) (t₀ s : State) : Prop :=
  VG.Proof.Pbkdf2.Whole.X86.Keyed hF t₀ s ∧ s.gpr .edi = dO t₀ F.st0O ∧ s.gpr .esi = dO t₀ F.st1O
abbrev Su2 (hF : FnsOK F) (t₀ s : State) : Prop :=
  VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s ∧ hF.hH.SH.Repr s.mem (A t₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀) opad) ∧ (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀).length = F.H.B
abbrev Su3 (hF : FnsOK F) (t₀ s : State) : Prop :=
  VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s ∧ hF.hH.SH.Repr s.mem (A t₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀) opad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.stSO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀) ipad) ∧ (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀).length = F.H.B
abbrev Su4 (hF : FnsOK F) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stSO ∧ s.gpr .esi = BitVec.ofNat 32 F.H.B ∧ s.gpr .eax = 0 ∧
    s.gpr .ecx = VG.X86.arg t₀ 3 ∧ s.gpr .edx = salt t₀) ∧
  hF.hH.SH.Repr s.mem (A t₀ F.st0O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.st1O) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀) opad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.stSO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀) ipad) ∧ (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀).length = F.H.B
/-- After the setup. -/
abbrev Su5 (hF : FnsOK F) (t₀ s : State) : Prop :=
  VG.Proof.Pbkdf2.Whole.X86.KR F t₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.States hF t₀ s.mem ∧ (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀).length = F.H.B

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hp' : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀') (hq : VG.Proof.Pbkdf2.Whole.X86.PubEq s₀ s₀') (hc : VG.Proof.Pbkdf2.Whole.X86.Checks F)
include hp hp' hq hc

theorem setup_rel :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Keyed hF s₀' s') F.setup fun s s' => VG.Proof.Pbkdf2.Whole.X86.Su5 hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Su5 hF s₀' s' := by
  have hz := hF.sizes
  unfold Fns.setup
  have r1 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.X86.Keyed hF) (VG.Proof.Pbkdf2.Whole.X86.Su1 hF) (fun h => h.kr) (fun s s' h h' => VG.Proof.Pbkdf2.Whole.X86.ag_ebp hq h.kr h'.kr) hc.su1
    (fun _ s h => VG.Proof.Pbkdf2.Whole.X86.su1_ok hF h)
  have r2 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.X86.Su1 hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Su1 hF s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call F.hiN F.hiC) (.pop .eax 5))
      fun s s' => VG.Proof.Pbkdf2.Whole.X86.Su2 hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Su2 hF s₀' s' :=
    rel_wp (hi_rel hF.hi (sp := VG.Proof.Pbkdf2.Whole.X86.E s₀) fun s s' ⟨⟨h, d, i⟩, ⟨h', d', i'⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.X86.su2_args hp hz hF h d i,
          by have := VG.Proof.Pbkdf2.Whole.X86.su2_args hp' hz hF h' d' i'; pub_simp hq at this; exact this,
          h.kr.esp, by rw [h'.kr.esp, hq.E']⟩)
      (fun s ⟨h, d, i⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.su2_ok hp hz hF h d i) fun t ⟨k, r0, r1⟩ => ⟨k, r0, r1, VG.Proof.Pbkdf2.Whole.X86.K0_length hp hz hF h⟩)
      (fun s ⟨h, d, i⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.su2_ok hp' hz hF h d i) fun t ⟨k, r0, r1⟩ => ⟨k, r0, r1, VG.Proof.Pbkdf2.Whole.X86.K0_length hp' hz hF h⟩)
  have r3 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.X86.Su2 hF) (VG.Proof.Pbkdf2.Whole.X86.Su3 hF) (fun h => h.1) (fun s s' h h' => VG.Proof.Pbkdf2.Whole.X86.ag_ebp hq h.1 h'.1) hc.su3
    (fun hp₀ s ⟨k, r0, r1, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.su3_ok hp₀ hz hF k r0 r1) fun t ⟨k', r0', r1', rS⟩ =>
      ⟨k', r0', r1', rS, l⟩)
  have r4 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.X86.Su3 hF) (VG.Proof.Pbkdf2.Whole.X86.Su4 hF) (fun h => h.1) (fun s s' h h' => VG.Proof.Pbkdf2.Whole.X86.ag_ebp hq h.1 h'.1) hc.su4
    (fun hp₀ s ⟨k, r0, r1, rS, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.su4_ok hp₀ k) fun t ⟨k', d, i, a, c, x, m⟩ =>
      ⟨⟨k', d, i, a, c, x⟩, m ▸ r0, m ▸ r1, m ▸ rS, l⟩)
  have r5 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.X86.Su4 hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Su4 hF s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6))
      fun s s' => VG.Proof.Pbkdf2.Whole.X86.Su5 hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Su5 hF s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := VG.Proof.Pbkdf2.Whole.X86.E s₀) fun s s' ⟨⟨⟨k, d, i, a, c, x⟩, _⟩, ⟨⟨k', d', i', a', c', x'⟩, _⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.X86.su5_args hp hz hF k d i a c x,
          by have := VG.Proof.Pbkdf2.Whole.X86.su5_args hp' hz hF k' d' i' a' c' x'; pub_simp hq at this; exact this,
          k.esp, by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d, i, a, c, x⟩, r0, r1, rS, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.su5_ok hp hz hF k d i a c x l r0 r1 rS)
        fun t ⟨k', st⟩ => ⟨k', st, l⟩)
      (fun s ⟨⟨k, d, i, a, c, x⟩, r0, r1, rS, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.su5_ok hp' hz hF k d i a c x l r0 r1 rS)
        fun t ⟨k', st⟩ => ⟨k', st, l⟩)
  exact r1.seq (r2.seq (r3.seq (r4.seq r5)))

theorem loopInit_rel :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.X86.Su5 hF s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Su5 hF s₀' s') (.block F.loopInit) fun s s' =>
      (VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ 0 s ∧ s.zf = some (decide (ol s₀ = 0))) ∧ (VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀' 0 s' ∧ s'.zf = some (decide (ol s₀' = 0))) :=
  VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.X86.Su5 hF) (fun t₀ s => VG.Proof.Pbkdf2.Whole.X86.Inv hF t₀ 0 s ∧ s.zf = some (decide (ol t₀ = 0))) (fun h => h.1)
    (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.X86.ag_ebp hq h.1 h'.1) hc.init
    (fun hp₀ _ ⟨k, st, l⟩ => VG.Proof.Pbkdf2.Whole.X86.loopInit_ok hp₀ hF.sizes k st l)

end

/-! ## A block of the output -/

/-- The pieces of a block. -/
abbrev Bk (hF : FnsOK F) (k : Nat) (P : State → State → Prop) (t₀ s : State) : Prop :=
  (VG.Proof.Pbkdf2.Whole.X86.Inv hF t₀ k s ∧ P t₀ s) ∧ k < VG.Proof.Pbkdf2.Whole.X86.nbk F t₀
abbrev Bk1 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.X86.Bk hF k fun t₀ s =>
  hF.hH.SH.Repr s.mem (A t₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀) ipad ++ VG.Proof.Pbkdf2.Whole.X86.saltB t₀)
abbrev Bk2 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.X86.Bk hF k fun t₀ s =>
  (s.gpr .edi = dO t₀ F.stWO ∧ s.gpr .esi = VG.X86.arg t₀ 3 + BitVec.ofNat 32 F.H.B ∧ s.gpr .eax = 0 ∧
    s.gpr .ecx = BitVec.ofNat 32 4 ∧ s.gpr .edx = dO t₀ F.intO) ∧
  hF.hH.SH.Repr s.mem (A t₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀) ipad ++ VG.Proof.Pbkdf2.Whole.X86.saltB t₀)
abbrev Bk3 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.X86.Bk hF k fun t₀ s =>
  hF.hH.SH.Repr s.mem (A t₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀) ipad ++ VG.Proof.Pbkdf2.Whole.X86.saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk4 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.X86.Bk hF k fun t₀ s =>
  (s.gpr .edx = dO t₀ F.stWO ∧ s.gpr .esi = dO t₀ F.st1O ∧ s.gpr .eax = VG.X86.arg t₀ 3 + BitVec.ofNat 32 (F.H.B + 4) ∧
    s.gpr .ecx = 0 ∧ s.gpr .edi = dO t₀ F.uO) ∧
  hF.hH.SH.Repr s.mem (A t₀ F.stWO) (xorPad (VG.Proof.Pbkdf2.Whole.X86.K0 hF t₀) ipad ++ VG.Proof.Pbkdf2.Whole.X86.saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk5 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.X86.Bk hF k fun t₀ s =>
  bytesAt s.mem (A t₀ F.uO) F.H.D = VG.Proof.Pbkdf2.Whole.X86.prf hF t₀ (VG.Proof.Pbkdf2.Whole.X86.saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk6 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.X86.Bk hF k fun t₀ s =>
  bytesAt s.mem (A t₀ F.uO) F.H.D = VG.Proof.Pbkdf2.Whole.X86.prf hF t₀ (VG.Proof.Pbkdf2.Whole.X86.saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    bytesAt s.mem (A t₀ F.tO) F.H.D = VG.Proof.Pbkdf2.Whole.X86.prf hF t₀ (VG.Proof.Pbkdf2.Whole.X86.saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk7 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.X86.Bk hF k fun t₀ s =>
  (s.gpr .esi = dO t₀ F.st0O ∧ s.gpr .eax = dO t₀ F.uO ∧ s.gpr .ecx = VG.X86.arg t₀ 4 - 1 ∧ s.gpr .edx = dO t₀ F.tO) ∧
  bytesAt s.mem (A t₀ F.uO) F.H.D = VG.Proof.Pbkdf2.Whole.X86.prf hF t₀ (VG.Proof.Pbkdf2.Whole.X86.saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    bytesAt s.mem (A t₀ F.tO) F.H.D = VG.Proof.Pbkdf2.Whole.X86.prf hF t₀ (VG.Proof.Pbkdf2.Whole.X86.saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk8 (hF : FnsOK F) (k : Nat) := VG.Proof.Pbkdf2.Whole.X86.Bk hF k fun t₀ s => bytesAt s.mem (A t₀ F.tO) F.H.D = VG.Proof.Pbkdf2.Whole.X86.Tk hF t₀ (k + 1)

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hp' : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀') (hq : VG.Proof.Pbkdf2.Whole.X86.PubEq s₀ s₀') (hc : VG.Proof.Pbkdf2.Whole.X86.Checks F)
include hp hp' hq hc

omit hp hp' hc in
theorem ag_loop {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s) (h' : VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀' k s') :
    ∀ r ∈ [Reg.ebp, .ebx], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h.kr.ebp, h'.kr.ebp, hq.scrEq]
  · rw [h.ebx, h'.ebx, hq.dnEq]

theorem block_rel (k : Nat) :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s ∧ k < VG.Proof.Pbkdf2.Whole.X86.nbk F s₀) ∧ (VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀' k s' ∧ k < VG.Proof.Pbkdf2.Whole.X86.nbk F s₀')) F.block
      fun s s' => (VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ (k + 1) s ∧ s.zf = some (decide (k + 1 = VG.Proof.Pbkdf2.Whole.X86.nbk F s₀))) ∧
        (VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀' (k + 1) s' ∧ s'.zf = some (decide (k + 1 = VG.Proof.Pbkdf2.Whole.X86.nbk F s₀'))) := by
  have hz := hF.sizes
  unfold Fns.block
  have r1 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (fun t₀ s => VG.Proof.Pbkdf2.Whole.X86.Inv hF t₀ k s ∧ k < VG.Proof.Pbkdf2.Whole.X86.nbk F t₀) (VG.Proof.Pbkdf2.Whole.X86.Bk1 hF k) (fun h => h.1.kr)
    (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.X86.ag_loop hq h.1 h'.1) hc.b1
    (fun hp₀ _ ⟨i, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.b1_ok hp₀ hz i) fun _ ⟨i', r⟩ => ⟨⟨i', r⟩, l⟩)
  have r2 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.X86.Bk1 hF k) (VG.Proof.Pbkdf2.Whole.X86.Bk2 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.X86.ag_loop hq h.1.1 h'.1.1) hc.b2
    (fun hp₀ _ ⟨⟨i, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.b2_ok hp₀ hz i) fun _ ⟨i', d, si, a, c, x, m⟩ =>
      ⟨⟨i', ⟨d, si, a, c, x⟩, by rw [m]; exact r⟩, l⟩)
  have r3 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.X86.Bk2 hF k s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Bk2 hF k s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6))
      fun s s' => VG.Proof.Pbkdf2.Whole.X86.Bk3 hF k s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Bk3 hF k s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := VG.Proof.Pbkdf2.Whole.X86.E s₀) fun s s' ⟨⟨⟨i, ⟨d, si, a, c, x⟩, _⟩, _⟩, ⟨⟨i', ⟨d', si', a', c', x'⟩, _⟩, _⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.X86.b3_args hp hz i d si a c x,
          by have := VG.Proof.Pbkdf2.Whole.X86.b3_args hp' hz i' d' si' a' c' x'; pub_simp hq at this; exact this,
          i.kr.esp, by rw [i'.kr.esp, hq.E']⟩)
      (fun _ ⟨⟨i, ⟨d, si, a, c, x⟩, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.b3_ok hp hz i d si a c x r) fun _ h => ⟨h, l⟩)
      (fun _ ⟨⟨i, ⟨d, si, a, c, x⟩, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.b3_ok hp' hz i d si a c x r) fun _ h => ⟨h, l⟩)
  have r4 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.X86.Bk3 hF k) (VG.Proof.Pbkdf2.Whole.X86.Bk4 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.X86.ag_loop hq h.1.1 h'.1.1) hc.b4
    (fun hp₀ _ ⟨⟨i, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.b4_ok hp₀ hz i) fun _ ⟨i', x, si, a, c, d, m⟩ =>
      ⟨⟨i', ⟨x, si, a, c, d⟩, by rw [m]; exact r⟩, l⟩)
  have r5 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.X86.Bk4 hF k s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Bk4 hF k s₀' s')
      (.frame (.push [.ebp, .edi, .ecx, .eax, .esi, .edx]) (.call F.hfN F.hfC) (.pop .eax 6))
      fun s s' => VG.Proof.Pbkdf2.Whole.X86.Bk5 hF k s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Bk5 hF k s₀' s' :=
    rel_wp (hf_rel hF.hf (sp := VG.Proof.Pbkdf2.Whole.X86.E s₀) fun s s' ⟨⟨⟨i, ⟨x, si, a, c, d⟩, _⟩, _⟩, ⟨⟨i', ⟨x', si', a', c', d'⟩, _⟩, _⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.X86.b5_args hp hz i x si a c d,
          by have := VG.Proof.Pbkdf2.Whole.X86.b5_args hp' hz i' x' si' a' c' d'; pub_simp hq at this; exact this,
          i.kr.esp, by rw [i'.kr.esp, hq.E']⟩)
      (fun _ ⟨⟨i, ⟨x, si, a, c, d⟩, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.b5_ok hp hz i x si a c d r) fun _ h => ⟨h, l⟩)
      (fun _ ⟨⟨i, ⟨x, si, a, c, d⟩, r⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.b5_ok hp' hz i x si a c d r) fun _ h => ⟨h, l⟩)
  have r6 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.X86.Bk5 hF k) (VG.Proof.Pbkdf2.Whole.X86.Bk6 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.X86.ag_loop hq h.1.1 h'.1.1) hc.b6
    (fun hp₀ _ ⟨⟨i, u⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.b6_ok hp₀ hz i u) fun _ ⟨i', u', t'⟩ => ⟨⟨i', u', t'⟩, l⟩)
  have r7 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.X86.Bk6 hF k) (VG.Proof.Pbkdf2.Whole.X86.Bk7 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.X86.ag_loop hq h.1.1 h'.1.1) hc.b7
    (fun hp₀ _ ⟨⟨i, u, t⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.b7_ok hp₀ hz i) fun _ ⟨i', si, a, c, x, m⟩ =>
      ⟨⟨i', ⟨si, a, c, x⟩, by rw [m]; exact u, by rw [m]; exact t⟩, l⟩)
  have r8 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.X86.Bk7 hF k s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Bk7 hF k s₀' s')
      (.frame (.push [.ebp, .edx, .ecx, .eax, .esi]) (.call F.itN F.itC) (.pop .eax 5))
      fun s s' => VG.Proof.Pbkdf2.Whole.X86.Bk8 hF k s₀ s ∧ VG.Proof.Pbkdf2.Whole.X86.Bk8 hF k s₀' s' :=
    rel_wp (it_rel hF.it (sp := VG.Proof.Pbkdf2.Whole.X86.E s₀) fun s s' ⟨⟨⟨i, ⟨si, a, c, x⟩, _⟩, _⟩, ⟨⟨i', ⟨si', a', c', x'⟩, _⟩, _⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Whole.X86.b8_args hp hz i si a c x,
          by have := VG.Proof.Pbkdf2.Whole.X86.b8_args hp' hz i' si' a' c' x'; pub_simp hq at this; exact this,
          i.kr.esp, by rw [i'.kr.esp, hq.E']⟩)
      (fun _ ⟨⟨i, ⟨si, a, c, x⟩, u, t⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.b8_ok hp hz i si a c x u t) fun _ h => ⟨h, l⟩)
      (fun _ ⟨⟨i, ⟨si, a, c, x⟩, u, t⟩, l⟩ => WP.mono (VG.Proof.Pbkdf2.Whole.X86.b8_ok hp' hz i si a c x u t) fun _ h => ⟨h, l⟩)
  have r9 := VG.Proof.Pbkdf2.Whole.X86.piece hp hp' hq (VG.Proof.Pbkdf2.Whole.X86.Bk8 hF k) (fun t₀ s => VG.Proof.Pbkdf2.Whole.X86.Inv hF t₀ (k + 1) s ∧ s.zf = some (decide (k + 1 = VG.Proof.Pbkdf2.Whole.X86.nbk F t₀)))
    (fun h => h.1.1.kr) (fun _ _ h h' => VG.Proof.Pbkdf2.Whole.X86.ag_loop hq h.1.1 h'.1.1) hc.tail
    (fun hp₀ _ ⟨⟨i, t⟩, l⟩ => VG.Proof.Pbkdf2.Whole.X86.tail_ok hp₀ hz l i t)
  exact (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9)))))))).mono (fun _ _ h => h)
    fun _ _ h => h

/-- The loop's invariant in two runs, with `n` blocks left. -/
abbrev LoopI (hF : FnsOK F) (s₀ s₀' : State) (n : Nat) (s s' : State) : Prop :=
  ∃ k, n = VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ - k ∧ k < VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ ∧ VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ k s ∧ VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀' k s'

theorem step_rel (n : Nat) :
    RelCT isa (VG.Proof.Pbkdf2.Whole.X86.LoopI hF s₀ s₀' n) F.block fun s s' =>
      isa.eval .ne s = isa.eval .ne s' ∧
      (isa.eval .ne s = some false → VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ (VG.Proof.Pbkdf2.Whole.X86.nbk F s₀) s ∧ VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀' (VG.Proof.Pbkdf2.Whole.X86.nbk F s₀') s') ∧
      (isa.eval .ne s = some true → ∃ m < n, VG.Proof.Pbkdf2.Whole.X86.LoopI hF s₀ s₀' m s s') := by
  rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨k, rfl, hk, i, i'⟩ e₁ e₂
  obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := VG.Proof.Pbkdf2.Whole.X86.block_rel hp hp' hq hc k _ _ _ _ _ _
    ⟨⟨i, hk⟩, ⟨i', by rw [hq.nbkEq]; exact hk⟩⟩ e₁ e₂
  refine ⟨ht, ?_⟩
  show isa.eval .ne s₁' = isa.eval .ne s₂' ∧ _
  have e : isa.eval .ne s₁' = some (!decide (k + 1 = VG.Proof.Pbkdf2.Whole.X86.nbk F s₀)) := by
    show VG.X86.eval .ne _ = _; rw [VG.Proof.Sha256.X86.Stream.eval_ne, z]; rfl
  have e' : isa.eval .ne s₂' = some (!decide (k + 1 = VG.Proof.Pbkdf2.Whole.X86.nbk F s₀)) := by
    show VG.X86.eval .ne _ = _; rw [VG.Proof.Sha256.X86.Stream.eval_ne, z', hq.nbkEq]; rfl
  rw [e, e']
  refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
  · have hl : k + 1 = VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ := by simpa using hf
    exact ⟨hl ▸ j, by rw [hq.nbkEq, ← hl]; exact j'⟩
  · have hl : k + 1 ≠ VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ := by simpa using ht
    exact ⟨VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ - (k + 1), by omega, k + 1, rfl, by omega, j, j'⟩

omit hp hp' hq hc in
theorem skip_check : ∃ hc, (VG.Taint.check taint (τr []) (.block []) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem loop_rel :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ 0 s ∧ s.zf = some (decide (ol s₀ = 0))) ∧
        (VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀' 0 s' ∧ s'.zf = some (decide (ol s₀' = 0))))
      (.ite .e (.block []) (.loop F.block .ne))
      fun s s' => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ (VG.Proof.Pbkdf2.Whole.X86.nbk F s₀) s ∧ VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀' (VG.Proof.Pbkdf2.Whole.X86.nbk F s₀') s' := by
  have hD := hF.sizes.D
  have e0 : VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ = 0 ↔ ol s₀ = 0 := Whole.nb_zero hD.1
  have ev : ∀ {t : State} {o : Nat}, t.zf = some (decide (o = 0)) → isa.eval .e t = some (decide (o = 0)) :=
    fun h => by show VG.X86.eval .e _ = _; rw [VG.Proof.Sha256.X86.Stream.eval_e, h]
  refine RelCT.ite (fun s s' h => by rw [ev h.1.2, ev h.2.2, hq.olEq]) ?_ ?_
  · by_cases e : ol s₀ = 0
    · have n0 : VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ = 0 := e0.2 e
      have n0' : VG.Proof.Pbkdf2.Whole.X86.nbk F s₀' = 0 := by rw [hq.nbkEq]; exact n0
      exact (rel_agree (c := .block [])
        (F := fun s => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ 0 s ∧ s.zf = some (decide (ol s₀ = 0)))
        (F' := fun s => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀' 0 s ∧ s.zf = some (decide (ol s₀' = 0)))
        (G := VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ (VG.Proof.Pbkdf2.Whole.X86.nbk F s₀)) (G' := VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀' (VG.Proof.Pbkdf2.Whole.X86.nbk F s₀')) (τr [])
        (fun _ _ _ _ => agree_regs (by simp)) VG.Proof.Pbkdf2.Whole.X86.skip_check
        (fun _ h => WP.block_nil (n0 ▸ h.1)) (fun _ h => WP.block_nil (n0' ▸ h.1))).mono (fun _ _ h => h.1)
        fun _ _ h => h
    · intro _ _ _ _ _ _ h
      have z := h.2
      rw [ev h.1.1.2] at z
      exact absurd (by simpa using z) e
  · refine (RelCT.loop (M := isa) (VG.Proof.Pbkdf2.Whole.X86.LoopI hF s₀ s₀') (VG.Proof.Pbkdf2.Whole.X86.step_rel hp hp' hq hc) (VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ - 0)).mono
      (fun s s' h => ?_) fun _ _ h => h
    have z := h.2
    rw [ev h.1.1.2] at z
    have e : ol s₀ ≠ 0 := by simpa using z
    have : VG.Proof.Pbkdf2.Whole.X86.nbk F s₀ ≠ 0 := fun h => e (e0.1 h)
    exact ⟨0, rfl, by omega, h.1.1.1, h.1.2.1⟩

include hF in
/-- `pbkdf2` in two runs with the same public arguments. -/
theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') F.pbkdf2 fun _ _ => True := by
  have hz := hF.sizes
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.Pbkdf2.Whole.X86.KR F s₀) (G' := VG.Proof.Pbkdf2.Whole.X86.KR F s₀')
    (argTaint [] (4 + 4 * 8)) (fun s s' e e' => by
        rw [e, e']
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (VG.Proof.Pbkdf2.Whole.X86.args_out hp rfl rfl) (VG.Proof.Pbkdf2.Whole.X86.args_out hp' rfl rfl)
          hq.args) hc.pro
    (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Whole.X86.prologue_ok hp hz) (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Whole.X86.prologue_ok hp' hz)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀ (VG.Proof.Pbkdf2.Whole.X86.nbk F s₀) s ∧ VG.Proof.Pbkdf2.Whole.X86.Inv hF s₀' (VG.Proof.Pbkdf2.Whole.X86.nbk F s₀') s') (.block F.L.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (argTaint [.ebp] (4 + 4 * 8)) (fun s s' h => agree_argTaint (VG.Proof.Pbkdf2.Whole.X86.ag_ebp hq h.1.kr h.2.kr)
      (by rw [h.1.kr.esp, h.2.kr.esp, hq.esp]) (VG.Proof.Pbkdf2.Whole.X86.args_out hp h.1.kr.esp h.1.kr.wr) (VG.Proof.Pbkdf2.Whole.X86.args_out hp' h.2.kr.esp h.2.kr.wr)
      fun i hi => by rw [h.1.kr.argEq hp hi, h.2.kr.argEq hp' hi, hq.args i hi]) hr
  unfold Fns.pbkdf2
  exact pro.seq ((VG.Proof.Pbkdf2.Whole.X86.key_rel hp hp' hq hc).seq ((VG.Proof.Pbkdf2.Whole.X86.setup_rel hp hp' hq hc).seq ((VG.Proof.Pbkdf2.Whole.X86.loopInit_rel hp hp' hq hc).seq
    ((VG.Proof.Pbkdf2.Whole.X86.loop_rel hp hp' hq hc).seq restore))))

end

/-- `pbkdf2` is verified against `pbkN`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verifiedN (hF : FnsOK F) (hc : VG.Proof.Pbkdf2.Whole.X86.Checks F) (hsat : ∃ s, (pbkN hF.hH.SH (F.W + F.H.S)).pre s) :
    Verified X86.target F.pbkdf2 (pbkN hF.hH.SH (F.W + F.H.S)) := by
  refine ⟨fun s hs => VG.Proof.Pbkdf2.Whole.X86.correct (VG.Proof.Pbkdf2.Whole.X86.pre_of hF hs) hF.sizes, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2⟩ := hpub
  exact (VG.Proof.Pbkdf2.Whole.X86.ct (hF := hF) (VG.Proof.Pbkdf2.Whole.X86.pre_of hF h₁) (VG.Proof.Pbkdf2.Whole.X86.pre_of hF h₂) ⟨h1, h2⟩ hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `pbkdf2` is verified against the shared contract, given the taint checks
and a state satisfying the shared contract. -/
theorem verified (hF : FnsOK F) (hc : VG.Proof.Pbkdf2.Whole.X86.Checks F) {S : Spec.Hmac.StreamingHash} {W : Nat} (hS : hF.hH.SH = S)
    (hW : F.W + F.H.S = W) (hsat : ∃ s, (Spec.Pbkdf2.pbkdf2ScratchContract S W X86.abi 76).pre s) :
    Verified X86.target F.pbkdf2 (Spec.Pbkdf2.pbkdf2ScratchContract S W X86.abi 76) := by
  subst hS hW
  have imp := pbkImp hF.hH.SH (F.W + F.H.S) hsat
  have gsat : ∃ s, (pbkG hF.hH.SH (F.W + F.H.S)).pre s := hsat.elim fun s h => ⟨s, imp.pre s h⟩
  exact (verified_pbkG _ _ (VG.Proof.Pbkdf2.Whole.X86.verifiedN hF hc (gsat.elim fun s h => ⟨_, pbkN_pre _ _ h⟩)) gsat).of_implies imp

/-- Memory holding the arguments `0x1000, 0, 0x1100, 0, 1, 0x1200, 0, 0x2000`
of `pbkdf2` at `0x8004`. -/
def pbkMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x800D then 0x11 else if a = 0x8014 then 0x01 else
  if a = 0x8019 then 0x12 else if a = 0x8021 then 0x20 else 0

/-- A state satisfying `pbkdf2`'s precondition with `8 W` bytes of scratch
space: an empty password, salt and output, and one iteration. -/
def pbkSat (W : Nat) : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Pbkdf2.Whole.X86.pbkMem
  rd := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩]
  wr := [⟨0x1200, 0⟩, ⟨0x2000, W * 8⟩, ⟨0x8004, 32⟩]

/-! ## Hash functions with a backend for each implementation of their compression function

The code differs between backends only in the functions it calls, so its
taint checks are evaluated once, on the code without them (`shapeOf`), for
every backend (`Sha256.lean`, `Sha1.lean`). -/

/-- `F` without the names and code of the functions it calls: the code
between the calls depends on nothing else. -/
def shapeOf (F : Fns) : Fns :=
  ⟨⟨F.H.B, F.H.S, F.H.D, F.H.F, F.H.W, "", .block [], "", .block [], "", .block []⟩, F.W, "", .block [], "",
    .block [], "", .block []⟩

theorem checks_of_shape {F : Fns} (h : VG.Proof.Pbkdf2.Whole.X86.Checks (VG.Proof.Pbkdf2.Whole.X86.shapeOf F)) : VG.Proof.Pbkdf2.Whole.X86.Checks F :=
  ⟨h.pro, h.cmp, h.hk1, h.hk3, h.hk5, h.hk7, h.short, h.su1, h.su3, h.su4, h.init, h.b1, h.b2, h.b4, h.b6, h.b7,
    h.tail, h.restore⟩

end VG.Proof.Pbkdf2.Whole.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit`. -/
section

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the functions it calls, and its code as literals

For each hash function of `Proof/Pbkdf2/Md/X86/Hashes.lean`, the functions
`pbkdf2` calls (`Fns`): its streaming functions, HMAC's `init` and
`finalize` and PBKDF2's `iterate` (`Impl/Pbkdf2/Md/X86.lean`) for it, by the names they are registered with; and
`pbkdf2` as a literal (`materialize_code`, `Proof/Framework/Lit.lean`), which
the registration files' `spSafe` checks evaluate.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Pbkdf2.Md.X86

/-- The functions `pbkdf2` calls for the hash function `M` of the instance
`I`, with the working space of `I`'s functions. -/
def fnsOf (I : Spec.Hmac.Instance) (M : Impl.Pbkdf2.Md.X86.Hash) : Fns where
  H := M.st
  W := I.scratch
  hiN := I.initScratchApi.name
  hiC := M.hmacInit
  hfN := I.finalizeScratchApi.name
  hfC := M.hmacFin
  itN := I.iterateApi.name
  itC := M.iterate

def md5F : Fns := VG.Proof.Pbkdf2.Whole.X86.fnsOf Spec.Hmac.md5I md5M
def sha384F : Fns := VG.Proof.Pbkdf2.Whole.X86.fnsOf Spec.Hmac.sha384I sha384M
def sha512F : Fns := VG.Proof.Pbkdf2.Whole.X86.fnsOf Spec.Hmac.sha512I sha512M'
def sha512_224F : Fns := VG.Proof.Pbkdf2.Whole.X86.fnsOf Spec.Hmac.sha512_224I sha512_224M
def sha512_256F : Fns := VG.Proof.Pbkdf2.Whole.X86.fnsOf Spec.Hmac.sha512_256I sha512_256M

materialize_code md5Pbkdf2 := md5F.pbkdf2
materialize_code sha384Pbkdf2 := sha384F.pbkdf2
materialize_code sha512Pbkdf2 := sha512F.pbkdf2
materialize_code sha512_224Pbkdf2 := sha512_224F.pbkdf2
materialize_code sha512_256Pbkdf2 := sha512_256F.pbkdf2

end VG.Proof.Pbkdf2.Whole.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances`. -/
section

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the instances

The generic proof (`CT.lean`) at each hash function of
`Proof/Pbkdf2/Md/X86/Hashes.lean`: the functions it calls are verified by
their own registration files, the taint checks are evaluated by the kernel,
and a state satisfies the shared contract (`pbkSat`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Pbkdf2.Stream.X86 (nosp_of md5OK sha384OK sha512OK sha512_224OK sha512_256OK)

/-! ## MD5 -/

theorem md5_checks : VG.Proof.Pbkdf2.Whole.X86.Checks VG.Proof.Pbkdf2.Whole.X86.md5F := by
  refine {
    pro := ⟨?_, ?_⟩
    cmp := ⟨?_, ?_⟩
    hk1 := ⟨?_, ?_⟩
    hk3 := ⟨?_, ?_⟩
    hk5 := ⟨?_, ?_⟩
    hk7 := ⟨?_, ?_⟩
    short := ⟨?_, ?_⟩
    su1 := ⟨?_, ?_⟩
    su3 := ⟨?_, ?_⟩
    su4 := ⟨?_, ?_⟩
    init := ⟨?_, ?_⟩
    b1 := ⟨?_, ?_⟩
    b2 := ⟨?_, ?_⟩
    b4 := ⟨?_, ?_⟩
    b6 := ⟨?_, ?_⟩
    b7 := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

def md5OKF : FnsOK VG.Proof.Pbkdf2.Whole.X86.md5F := by
  refine {
    hH := md5OK
    Wi := 48
    Wf := 48
    Wt := 48
    hi := .of_verified Proof.Pbkdf2.Md.X86.Instances.md5_init
    hf := .of_verified Proof.Pbkdf2.Md.X86.Instances.md5_finalize
    it := .of_verified Proof.Pbkdf2.Md.X86.Instances.md5_iterate
    hiSp := nosp_of ?_
    hfSp := nosp_of ?_
    itSp := nosp_of ?_
    hiSU := ?_
    hfSU := ?_
    itSU := ?_
    hWi := by decide
    hWf := by decide
    hWt := by decide
    hWH := by decide
    hW := by decide
    hDB := by decide
    hBS := by decide
    fits := by decide }
  taint_decide_all

theorem md5_sat : ∃ s, (Spec.Hmac.md5I.pbkdf2ScratchContract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using VG.Proof.Pbkdf2.Whole.X86.pbkSat 128

theorem md5 : Verified X86.target md5F.pbkdf2 (Spec.Hmac.md5I.pbkdf2ScratchContract X86.abi 76) :=
  VG.Proof.Pbkdf2.Whole.X86.verified VG.Proof.Pbkdf2.Whole.X86.md5OKF VG.Proof.Pbkdf2.Whole.X86.md5_checks rfl rfl VG.Proof.Pbkdf2.Whole.X86.md5_sat

/-! ## SHA-384 -/

theorem sha384_checks : VG.Proof.Pbkdf2.Whole.X86.Checks VG.Proof.Pbkdf2.Whole.X86.sha384F := by
  refine {
    pro := ⟨?_, ?_⟩
    cmp := ⟨?_, ?_⟩
    hk1 := ⟨?_, ?_⟩
    hk3 := ⟨?_, ?_⟩
    hk5 := ⟨?_, ?_⟩
    hk7 := ⟨?_, ?_⟩
    short := ⟨?_, ?_⟩
    su1 := ⟨?_, ?_⟩
    su3 := ⟨?_, ?_⟩
    su4 := ⟨?_, ?_⟩
    init := ⟨?_, ?_⟩
    b1 := ⟨?_, ?_⟩
    b2 := ⟨?_, ?_⟩
    b4 := ⟨?_, ?_⟩
    b6 := ⟨?_, ?_⟩
    b7 := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

def sha384OKF : FnsOK VG.Proof.Pbkdf2.Whole.X86.sha384F := by
  refine {
    hH := sha384OK
    Wi := 234
    Wf := 234
    Wt := 234
    hi := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha384_init
    hf := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha384_finalize
    it := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha384_iterate
    hiSp := nosp_of ?_
    hfSp := nosp_of ?_
    itSp := nosp_of ?_
    hiSU := ?_
    hfSU := ?_
    itSU := ?_
    hWi := by decide
    hWf := by decide
    hWt := by decide
    hWH := by decide
    hW := by decide
    hDB := by decide
    hBS := by decide
    fits := by decide }
  taint_decide_all

theorem sha384_sat : ∃ s, (Spec.Hmac.sha384I.pbkdf2ScratchContract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using VG.Proof.Pbkdf2.Whole.X86.pbkSat 426

theorem sha384 : Verified X86.target sha384F.pbkdf2 (Spec.Hmac.sha384I.pbkdf2ScratchContract X86.abi 76) :=
  VG.Proof.Pbkdf2.Whole.X86.verified VG.Proof.Pbkdf2.Whole.X86.sha384OKF VG.Proof.Pbkdf2.Whole.X86.sha384_checks rfl rfl VG.Proof.Pbkdf2.Whole.X86.sha384_sat

/-! ## SHA-512 -/

theorem sha512_checks : VG.Proof.Pbkdf2.Whole.X86.Checks VG.Proof.Pbkdf2.Whole.X86.sha512F := by
  refine {
    pro := ⟨?_, ?_⟩
    cmp := ⟨?_, ?_⟩
    hk1 := ⟨?_, ?_⟩
    hk3 := ⟨?_, ?_⟩
    hk5 := ⟨?_, ?_⟩
    hk7 := ⟨?_, ?_⟩
    short := ⟨?_, ?_⟩
    su1 := ⟨?_, ?_⟩
    su3 := ⟨?_, ?_⟩
    su4 := ⟨?_, ?_⟩
    init := ⟨?_, ?_⟩
    b1 := ⟨?_, ?_⟩
    b2 := ⟨?_, ?_⟩
    b4 := ⟨?_, ?_⟩
    b6 := ⟨?_, ?_⟩
    b7 := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

def sha512OKF : FnsOK VG.Proof.Pbkdf2.Whole.X86.sha512F := by
  refine {
    hH := sha512OK
    Wi := 234
    Wf := 234
    Wt := 234
    hi := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_init
    hf := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_finalize
    it := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_iterate
    hiSp := nosp_of ?_
    hfSp := nosp_of ?_
    itSp := nosp_of ?_
    hiSU := ?_
    hfSU := ?_
    itSU := ?_
    hWi := by decide
    hWf := by decide
    hWt := by decide
    hWH := by decide
    hW := by decide
    hDB := by decide
    hBS := by decide
    fits := by decide }
  taint_decide_all

theorem sha512_sat : ∃ s, (Spec.Hmac.sha512I.pbkdf2ScratchContract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using VG.Proof.Pbkdf2.Whole.X86.pbkSat 426

theorem sha512 : Verified X86.target sha512F.pbkdf2 (Spec.Hmac.sha512I.pbkdf2ScratchContract X86.abi 76) :=
  VG.Proof.Pbkdf2.Whole.X86.verified VG.Proof.Pbkdf2.Whole.X86.sha512OKF VG.Proof.Pbkdf2.Whole.X86.sha512_checks rfl rfl VG.Proof.Pbkdf2.Whole.X86.sha512_sat

/-! ## SHA-512/224 -/

theorem sha512_224_checks : VG.Proof.Pbkdf2.Whole.X86.Checks VG.Proof.Pbkdf2.Whole.X86.sha512_224F := by
  refine {
    pro := ⟨?_, ?_⟩
    cmp := ⟨?_, ?_⟩
    hk1 := ⟨?_, ?_⟩
    hk3 := ⟨?_, ?_⟩
    hk5 := ⟨?_, ?_⟩
    hk7 := ⟨?_, ?_⟩
    short := ⟨?_, ?_⟩
    su1 := ⟨?_, ?_⟩
    su3 := ⟨?_, ?_⟩
    su4 := ⟨?_, ?_⟩
    init := ⟨?_, ?_⟩
    b1 := ⟨?_, ?_⟩
    b2 := ⟨?_, ?_⟩
    b4 := ⟨?_, ?_⟩
    b6 := ⟨?_, ?_⟩
    b7 := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

def sha512_224OKF : FnsOK VG.Proof.Pbkdf2.Whole.X86.sha512_224F := by
  refine {
    hH := sha512_224OK
    Wi := 234
    Wf := 234
    Wt := 234
    hi := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_224_init
    hf := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_224_finalize
    it := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_224_iterate
    hiSp := nosp_of ?_
    hfSp := nosp_of ?_
    itSp := nosp_of ?_
    hiSU := ?_
    hfSU := ?_
    itSU := ?_
    hWi := by decide
    hWf := by decide
    hWt := by decide
    hWH := by decide
    hW := by decide
    hDB := by decide
    hBS := by decide
    fits := by decide }
  taint_decide_all

theorem sha512_224_sat : ∃ s, (Spec.Hmac.sha512_224I.pbkdf2ScratchContract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using VG.Proof.Pbkdf2.Whole.X86.pbkSat 426

theorem sha512_224 : Verified X86.target sha512_224F.pbkdf2 (Spec.Hmac.sha512_224I.pbkdf2ScratchContract X86.abi 76) :=
  VG.Proof.Pbkdf2.Whole.X86.verified VG.Proof.Pbkdf2.Whole.X86.sha512_224OKF VG.Proof.Pbkdf2.Whole.X86.sha512_224_checks rfl rfl VG.Proof.Pbkdf2.Whole.X86.sha512_224_sat

/-! ## SHA-512/256 -/

theorem sha512_256_checks : VG.Proof.Pbkdf2.Whole.X86.Checks VG.Proof.Pbkdf2.Whole.X86.sha512_256F := by
  refine {
    pro := ⟨?_, ?_⟩
    cmp := ⟨?_, ?_⟩
    hk1 := ⟨?_, ?_⟩
    hk3 := ⟨?_, ?_⟩
    hk5 := ⟨?_, ?_⟩
    hk7 := ⟨?_, ?_⟩
    short := ⟨?_, ?_⟩
    su1 := ⟨?_, ?_⟩
    su3 := ⟨?_, ?_⟩
    su4 := ⟨?_, ?_⟩
    init := ⟨?_, ?_⟩
    b1 := ⟨?_, ?_⟩
    b2 := ⟨?_, ?_⟩
    b4 := ⟨?_, ?_⟩
    b6 := ⟨?_, ?_⟩
    b7 := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

def sha512_256OKF : FnsOK VG.Proof.Pbkdf2.Whole.X86.sha512_256F := by
  refine {
    hH := sha512_256OK
    Wi := 234
    Wf := 234
    Wt := 234
    hi := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_256_init
    hf := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_256_finalize
    it := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_256_iterate
    hiSp := nosp_of ?_
    hfSp := nosp_of ?_
    itSp := nosp_of ?_
    hiSU := ?_
    hfSU := ?_
    itSU := ?_
    hWi := by decide
    hWf := by decide
    hWt := by decide
    hWH := by decide
    hW := by decide
    hDB := by decide
    hBS := by decide
    fits := by decide }
  taint_decide_all

theorem sha512_256_sat : ∃ s, (Spec.Hmac.sha512_256I.pbkdf2ScratchContract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using VG.Proof.Pbkdf2.Whole.X86.pbkSat 426

theorem sha512_256 : Verified X86.target sha512_256F.pbkdf2 (Spec.Hmac.sha512_256I.pbkdf2ScratchContract X86.abi 76) :=
  VG.Proof.Pbkdf2.Whole.X86.verified VG.Proof.Pbkdf2.Whole.X86.sha512_256OKF VG.Proof.Pbkdf2.Whole.X86.sha512_256_checks rfl rfl VG.Proof.Pbkdf2.Whole.X86.sha512_256_sat

end VG.Proof.Pbkdf2.Whole.X86

end
