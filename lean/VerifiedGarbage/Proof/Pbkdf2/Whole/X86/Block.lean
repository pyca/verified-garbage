module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Key
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Sha256.Stream

/-! ### `Pbkdf2.Whole.X86.Setup`, which only this module used -/

section

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: HMAC's states for the key, and the salt

HMAC's `init` makes the key's inner and outer states; the inner one is copied
and absorbs the salt (`setup_ok`), which gives the three states every block
starts from (`States`).
-/

@[expose] public section

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
  st0 : hF.hH.SH.Repr m (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad)
  st1 : hF.hH.SH.Repr m (A s₀ F.st1O) (xorPad (K0 hF s₀) opad)
  stS : hF.hH.SH.Repr m (A s₀ F.stSO) (xorPad (K0 hF s₀) ipad ++ saltB s₀)

/-- The representation is kept by what writes elsewhere. -/
theorem repr_keep (hH : HashOK F.H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, F.H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, F.H.S⟩) hd (by show F.H.S ≤ 2 ^ 64; have := hH.hSB; omega_arith) hi) hr

/-- The three states are kept by what writes elsewhere: after them in `scratch`. -/
theorem States.keep {hF : FnsOK F} {s₀ : State} (hz : Sizes F) {m m' : Mem} (h : States hF s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ F.st0O (3 * F.H.S)) r) :
    States hF s₀ m' := by
  have hl := layout (F := F); have he := end_le hz; have := hz.D
  have sub : ∀ o, F.st0O ≤ o → o + F.H.S ≤ F.st0O + 3 * F.H.S →
      Region.Sub (sR s₀ o F.H.S) (sR s₀ F.st0O (3 * F.H.S)) := fun o h₁ h₂ =>
    Offset.sub _ h₁ h₂
  refine ⟨repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega_arith) (by omega_arith))) h.st0,
    repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega_arith) (by omega_arith))) h.st1,
    repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega_arith) (by omega_arith))) h.stS⟩

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-- A copy of `n > 0` bytes within `scratch`, after the save area. -/
theorem copy_part_ok {s : State} (hk : KR F s₀ s) {a b n : Nat} (hn : 0 < n) (ha : a + n ≤ F.L8)
    (hb : b + n ≤ F.L8) (hb' : 8 * F.W + 16 ≤ b) (hab : a + n ≤ b ∨ b + n ≤ a) :
    WP isa (copy .ebp a .ebp b n) s fun t => KR F s₀ t ∧ (∀ r ∉ cclob, t.gpr r = s.gpr r) ∧
      t.mem = writeBytes s.mem (A s₀ b) (bytesAt s.mem (A s₀ a) n) := by
  have hL := L8_le hz; have := hp.nsc; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (copy_ok (src := .ebp) (dst := .ebp) (by decide) (by decide) hn (by omega_arith)
    (by rw [hk.ebp]; omega_arith) (by rw [hk.ebp]; omega_arith)
    (fun j hj => by
      rw [hk.ebp]
      exact ⟨scR s₀ F, List.mem_append_right _ (by rw [hk.wr]; exact sc_mem hp),
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun j hj => by
      rw [hk.ebp]
      exact ⟨scR s₀ F, by rw [hk.wr]; exact sc_mem hp,
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (by rw [hk.ebp]; exact part_disj hz hab ha hb)) fun t c => ?_
  rw [hk.ebp] at c
  have f : Frame [sR s₀ b n] s.mem t.mem := by
    rw [c.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  exact ⟨hk.write hz c.rd c.wr (fun r hr => c.other r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> decide))
    hb' hb f, c.other, c.mem⟩

omit hp hz in
/-- After such a copy, the bytes at `b` are those at `a`. -/
theorem copied_byte {m : Mem} {a b n : Nat} (hn : n ≤ 2 ^ 32) (i : Nat) (hi : i < n) :
    writeBytes m (A s₀ b) (bytesAt m (A s₀ a) n) (A s₀ b + BitVec.ofNat 64 i) = m (A s₀ a + BitVec.ofNat 64 i) := by
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_arith), bytesAt_getD' _ _ hi]

end

/-- After the key: where it is, and its `K₀`. -/
structure Keyed (hF : FnsOK F) (s₀ s : State) : Prop where
  kr : KR F s₀ s
  edx : s.gpr .edx = kp F s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 (kl F s₀)
  k0 : blockKey hF.hH.SH.H (bytesAt s.mem ((kp F s₀).setWidth 64) (kl F s₀)) = K0 hF s₀

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F) (hF : FnsOK F)
include hp hz hF

theorem keyed_ok {s : State} (hk : KR F s₀ s) : WP isa F.key s (Keyed hF s₀) :=
  WP.mono (key_ok hp hz hF.hH hk) fun _ ⟨k, d, c, b⟩ => ⟨k, d, c, b⟩

omit hp hz in
theorem su1_ok {s : State} (h : Keyed hF s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.st0O ++ VG.Impl.Pbkdf2.Stream.X86.scr .esi F.st1O)) s
      fun t => Keyed hF s₀ t ∧ t.gpr .edi = dO s₀ F.st0O ∧ t.gpr .esi = dO s₀ F.st1O := by
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have k₁ := h.kr.upd (by decide) u₁
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .esi F.st1O)]
  refine scr_ok k₁ fun s₂ u₂ => WP.block_nil ⟨⟨k₁.upd (by decide) u₂, ?_, ?_, ?_⟩, ?_, u₂.gpr⟩
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.edx]
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
  · rw [u₂.mem, u₁.mem]; exact h.k0
  · rw [u₂.other _ (by decide), u₁.gpr]

theorem su2_args {s : State} (h : Keyed hF s₀ s) (hdi : s.gpr .edi = dO s₀ F.st0O)
    (hsi : s.gpr .esi = dO s₀ F.st1O) :
    HiArgs hF.hH.SH hF.Wi s (dO s₀ F.st0O) (dO s₀ F.st1O) (kp F s₀) (scr s₀) (kl F s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWi; have hS := hF.hH.hS
  have e0 := dO_addr hp (o := F.st0O) (hz.st0O_lt)
  have e1 := dO_addr hp (o := F.st1O) (hz.st1O_lt)
  have hk := h.kr
  have kd : ∀ o n, o + n ≤ F.hkO → F.st0O ≤ o →
      Region.Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ (sR s₀ o n) := fun o n h₁ h₂ =>
    key_disj hp hz (part_sub (by omega_arith)) (part_disj hz (Or.inl h₁) (by omega_arith) (hz.hkO_D))
  have kls : Region.Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ (lowR s₀ (hF.Wi * 8)) :=
    key_disj hp hz (low_sub (by omega_arith)) (low_disj hz (by omega_arith) (hz.hkO_D))
  exact
    { edi := hdi
      esi := hsi
      edx := h.edx
      ecx := h.ecx
      ebp := hk.ebp
      klB := by rw [hF.hH.hB]; exact kl_le hp hz
      kl32 := by have := kl_le hp hz; have := hz.B; omega_arith
      sp := by rw [hk.esp]; exact hp.sp76
      cr := key_cov hp hz hk
      cw := by
        rw [hS, e0, e1]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact cov_part hp hk (hz.st0O_S)
          · exact cov_part hp hk (hz.st1O_S)
          · exact cov_low hp hk (by omega_arith)
      i_o := by rw [hS, e0, e1]; exact part_disj hz (Or.inl (by omega_arith)) (hz.st0O_S) (hz.st1O_S)
      i_k := by rw [hS, e0]; exact (kd _ _ (by omega_arith) (by omega_arith)).symm
      i_s := by rw [hS, e0]; exact (low_disj hz (by omega_arith) (hz.st0O_S)).symm
      o_k := by rw [hS, e1]; exact (kd _ _ (by omega_arith) (by omega_arith)).symm
      o_s := by rw [hS, e1]; exact (low_disj hz (by omega_arith) (hz.st1O_S)).symm
      k_s := kls
      b_i := by rw [hS, e0]; exact b76 hp hk (part_sub (hz.st0O_S))
      b_o := by rw [hS, e1]; exact b76 hp hk (part_sub (hz.st1O_S))
      b_k := key_stk hp hz hk
      b_s := b76 hp hk (low_sub (by omega_arith))
      ni := by rw [hS, dO_toNat hp (hz.st0O_lt)]; have := hp.nsc; omega_arith
      no := by rw [hS, dO_toNat hp (hz.st1O_lt)]; have := hp.nsc; omega_arith
      nk := key_toNat hp hz
      nsc := by have := hp.nsc; omega_arith }

theorem su2_ok {s : State} (h : Keyed hF s₀ s) (hdi : s.gpr .edi = dO s₀ F.st0O)
    (hsi : s.gpr .esi = dO s₀ F.st1O) :
    WP isa (.frame (.push hi5) (.call F.hiN F.hiC) (.pop .eax hi5.length)) s fun t => KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWi; have hS := hF.hH.hS
  have e0 := dO_addr hp (o := F.st0O) (hz.st0O_lt)
  have e1 := dO_addr hp (o := F.st1O) (hz.st1O_lt)
  refine hi_frame hF.hi hF.hiSp hF.hiSU (su2_args hp hz hF h hdi hsi) fun s' a r0 r1 => ⟨?_, ?_, ?_⟩
  · refine h.kr.call hp hz a fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [e0, hS], by omega_arith, by omega_arith⟩
    · exact .inr ⟨_, _, by rw [e1, hS], by omega_arith, by omega_arith⟩
    · exact .inl ⟨_, rfl, by omega_arith⟩
  · rw [h.k0, e0] at r0; exact r0
  · rw [h.k0, e1] at r1; exact r1

omit hF in
theorem K0_length (hF : FnsOK F) {s : State} (h : Keyed hF s₀ s) : (K0 hF s₀).length = F.H.B := by
  have := kl_le hp hz
  rw [← h.k0]
  simp only [blockKey, hF.hH.hB, bytesAt_length, show ¬ F.H.B < kl F s₀ by omega_arith, ↓reduceIte,
    List.length_append, List.length_replicate]
  omega_arith

/-- The key's inner state, copied for the salt. -/
theorem su3_ok {s : State} (hk : KR F s₀ s) (r0 : hF.hH.SH.Repr s.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad))
    (r1 : hF.hH.SH.Repr s.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad)) :
    WP isa (copy .ebp F.st0O .ebp F.stSO F.H.S) s fun t => KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.stSO) (xorPad (K0 hF s₀) ipad) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have hL := L8_le hz
  refine WP.mono (copy_part_ok hp hz hk hz.S.1 (hz.st0O_S) (hz.stSO_S) (by omega_arith) (Or.inl (by omega_arith)))
    fun t ⟨k, _, m⟩ => ?_
  have f : Frame [sR s₀ F.stSO F.H.S] s.mem t.mem := by
    rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨k, repr_keep hF.hH f (fun r hr => ?_) r0, repr_keep hF.hH f (fun r hr => ?_) r1, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega_arith)) (hz.st0O_S) (hz.stSO_S)
  · simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega_arith)) (hz.st1O_S) (hz.stSO_S)
  · refine hF.hH.repr _ _ _ _ _ (fun i hi => ?_) r0
    rw [m]; exact copied_byte (by omega_arith) i hi

omit hz hF in
/-- `update`'s arguments: the salt. -/
theorem su4_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stSO ++ ([.mov .eax (.imm 0),
      .mov .esi (.imm (BitVec.ofNat 32 F.H.B)), .mov .ecx (Fns.argM 3), .mov .edx (Fns.argM 2)] : List Instr))) s
      fun t => KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stSO ∧ t.gpr .esi = BitVec.ofNat 32 F.H.B ∧ t.gpr .eax = 0 ∧
        t.gpr .ecx = arg s₀ 3 ∧ t.gpr .edx = salt s₀ ∧ t.mem = s.mem := by
  refine scr_ok hk fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_movi fun s₃ u₃ => ?_
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
  have h₂ : (scR s₀ F).base.toNat + (scR s₀ F).len ≤ 2 ^ 32 := by
    show ((scr s₀).setWidth 64).toNat + F.L8 ≤ _; rw [toNat_setWidth64]; exact hp.nsc
  have h : sl s₀ + (F.W + F.H.S) * 8 ≤ 2 ^ 32 := Pbkdf2.Whole.len_add_le hp.sa_s h₁ h₂
  have := hz.B; have := hz.S; have := hz.BS
  omega_arith

theorem su5_args {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stSO)
    (hsi : s.gpr .esi = BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 3)
    (hdx : s.gpr .edx = salt s₀) :
    UpdArgs hF.hH s .esi .edi (dO s₀ F.stSO) (salt s₀) (scr s₀) (BitVec.ofNat 32 F.H.B) (sl s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stSO) (by omega_arith)
  exact
    { hst := hdi
      hlo := hsi
      eax := hax
      ecx := by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      hl := by decide
      hlen := (arg s₀ 3).isLt
      sp48 := by rw [hk.esp]; have := hp.sp76; omega_arith
      cd := cov_salt hp hk
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk (hz.stSO_S)
          · exact cov_low hp hk (by omega_arith)
      st_sc := by rw [ea]; exact (low_disj hz (k := hF.hH.Wb) (by omega_arith) (hz.stSO_S)).symm
      d_st := by rw [ea]; exact hp.sa_s.sub_right (part_sub (hz.stSO_S))
      d_sc := hp.sa_s.sub_right (low_sub (by omega_arith))
      b_st := by rw [ea]; exact b48 hp hk (part_sub (hz.stSO_S))
      b_d := hp.b_sa.sub_left (stk48_sub hp hk)
      b_sc := b48 hp hk (low_sub (by omega_arith))
      nst := by rw [dO_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith
      nd := hp.nsa
      nsc := by have := hp.nsc; omega_arith }

theorem su5_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stSO)
    (hsi : s.gpr .esi = BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 3)
    (hdx : s.gpr .edx = salt s₀) (hkl : (K0 hF s₀).length = F.H.B)
    (r0 : hF.hH.SH.Repr s.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad))
    (r1 : hF.hH.SH.Repr s.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad))
    (rS : hF.hH.SH.Repr s.mem (A s₀ F.stSO) (xorPad (K0 hF s₀) ipad)) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)) s
      fun t => KR F s₀ t ∧ States hF s₀ t.mem := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stSO) (by omega_arith)
  refine upd_frame hF.hH (su5_args hp hz hF hk hdi hsi hax hcx hdx) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega_arith, by omega_arith⟩
    · exact .inl ⟨_, rfl, by omega_arith⟩
  all_goals have f := a.frame
  all_goals rw [ea] at f
  · refine repr_keep hF.hH f (fun r hr => ?_) r0
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact part_disj hz (Or.inl (by omega_arith)) (hz.st0O_S) (hz.stSO_S)
    · exact low_disj hz (by omega_arith) (hz.st0O_S) |>.symm
    · exact (b48 hp hk (part_sub (hz.st0O_S))).symm
  · refine repr_keep hF.hH f (fun r hr => ?_) r1
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact part_disj hz (Or.inl (by omega_arith)) (hz.st1O_S) (hz.stSO_S)
    · exact low_disj hz (by omega_arith) (hz.st1O_S) |>.symm
    · exact (b48 hp hk (part_sub (hz.st1O_S))).symm
  · have := r (xorPad (K0 hF s₀) ipad) (by rw [ea]; exact rS) (by
      rw [xorPad_length, hkl, Pbkdf2.Stream.X86.zero_append_ofNat (by have := hz.B; omega_arith)])
    rw [ea, hk.saltBytes hp] at this
    exact this

theorem setup_ok {s : State} (h : Keyed hF s₀ s) :
    WP isa F.setup s fun t => KR F s₀ t ∧ States hF s₀ t.mem ∧ (K0 hF s₀).length = F.H.B := by
  have hkl := K0_length hp hz hF h
  unfold Fns.setup
  refine WP.seq (WP.mono (su1_ok hF h) fun s₁ ⟨k₁, d₁, i₁⟩ => ?_)
  refine WP.seq (WP.mono (su2_ok hp hz hF k₁ d₁ i₁) fun s₂ ⟨k₂, r0, r1⟩ => ?_)
  refine WP.seq (WP.mono (su3_ok hp hz hF k₂ r0 r1) fun s₃ ⟨k₃, r0, r1, rS⟩ => ?_)
  refine WP.seq (WP.mono (su4_ok hp k₃) fun s₄ ⟨k₄, d₄, i₄, a₄, c₄, x₄, m₄⟩ => ?_)
  exact WP.mono (su5_ok hp hz hF k₄ d₄ i₄ a₄ c₄ x₄ hkl (m₄ ▸ r0) (m₄ ▸ r1) (m₄ ▸ rS))
    fun t ⟨k, st⟩ => ⟨k, st, hkl⟩

end

end VG.Proof.Pbkdf2.Whole.X86

end

end


/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: a block of the output, up to `U₁`

After `k` blocks of the output (`Inv`), `out` holds the first `done k` bytes
of `T₁ ‖ … ‖ T_k`, `ebx` is `done k`, and `scratch` holds `INT (k + 1)`,
byte-reversed. A step copies the salted inner state into the working state,
absorbs `INT (k + 1)` into it (`update`) and computes `U₁` with HMAC's
`finalize`.
-/

@[expose] public section

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
abbrev prf (hF : FnsOK F) (s₀ : State) : List Byte → List Byte := hmacBlockKey hF.hH.SH.H (K0 hF s₀)

/-- `T₁ ‖ … ‖ T_k`, `T_i`, the number of blocks and the bytes written after `k` of them. -/
abbrev Gk (hF : FnsOK F) (s₀ : State) (k : Nat) : List Byte := Whole.G (prf hF s₀) (saltB s₀) (cc s₀) k
abbrev Tk (hF : FnsOK F) (s₀ : State) (i : Nat) : List Byte := Whole.Tb (prf hF s₀) (saltB s₀) (cc s₀) i
abbrev nbk (F : Fns) (s₀ : State) : Nat := Whole.nb F.H.D (ol s₀)
abbrev dn (F : Fns) (s₀ : State) (k : Nat) : Nat := Whole.done F.H.D (ol s₀) k

/-- After `k` blocks of the output. -/
structure Inv (hF : FnsOK F) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR F s₀ s
  st : States hF s₀ s.mem
  k0l : (K0 hF s₀).length = F.H.B
  ebx : s.gpr .ebx = BitVec.ofNat 32 (dn F s₀ k)
  intW : s.mem.readW (A s₀ F.intO) 32 = byteRev32 (BitVec.ofNat 32 (k + 1))
  glen : (Gk hF s₀ k).length = k * F.H.D
  outB : bytesAt s.mem ((out s₀).setWidth 64) (dn F s₀ k) = (Gk hF s₀ k).take (dn F s₀ k)

/-- The registers `Inv` fixes. -/
abbrev iregs : List Reg := [.esp, .ebp, .ebx]

/-- Where a step writes, before it copies `T` out: the working space, or
the parts of `scratch` from the working state up to `INT (i)`. -/
def Wks (F : Fns) (s₀ : State) (r : Region) : Prop :=
  (∃ k, r = lowR s₀ k ∧ k ≤ 8 * F.W) ∨ ∃ o n, r = sR s₀ o n ∧ F.stWO ≤ o ∧ o + n ≤ F.intO

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

omit hp in
theorem Wks.disj {r : Region} (h : Wks F s₀ r) :
    (svR F s₀).Disjoint r ∧ Region.Sub r (scR s₀ F) ∧ (sR s₀ F.st0O (3 * F.H.S)).Disjoint r ∧
      (sR s₀ F.intO 4).Disjoint r := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D
  rcases h with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
  · exact ⟨sv_low hz hk, low_sub (by omega_using [hl, he, hk]), (low_disj hz (by omega_using [hl, hk]) (hz.st0O_3S)).symm,
      (low_disj hz (by omega_using [hl, hk]) (end_le hz)).symm⟩
  · exact ⟨sv_disj hz (by omega_using [hl, h₁]) (by omega_using [h₂, he]), part_sub (by omega_using [he, h₂]),
      part_disj hz (Or.inl (by omega_using [hl, h₁])) (hz.st0O_3S) (by omega_using [he, h₂]), part_disj hz (Or.inr (by omega_using [h₂])) (end_le hz) (by omega_using [he, h₂])⟩

/-- `Inv` survives writes where a step writes, and to the stack below `esp`. -/
theorem Inv.keep {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ iregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, Wks F s₀ r ∨ r = stkR s₀) : Inv hF s₀ k s' := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D
  have hsb : (stkR s₀).Disjoint (scR s₀ F) := hp.b_s
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
    · exact (hsb.sub_right (part_sub (hz.st0O_3S))).symm
  · rw [← h.intW]
    refine hf.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases hw r hr with hw | rfl
    · exact (hw.disj hz).2.2.2
    · exact (hsb.sub_right (part_sub (end_le hz))).symm
  · rw [← h.outB]
    have osub : Region.Sub ⟨(out s₀).setWidth 64, dn F s₀ k⟩ (outR s₀) :=
      Region.sub_prefix (Nat.min_le_right _ _)
    refine bytes_keep hf (fun r hr => ?_) (by
      have h1 : dn F s₀ k ≤ ol s₀ := Nat.min_le_right _ _; have hp_no := hp.no; omega_using [hp_no, h1])
    rcases hw r hr with hw | rfl
    · exact (hp.o_s.sub_left osub).sub_right (hw.disj hz).2.1
    · exact hp.b_o.symm.sub_left osub

theorem Inv.upd {k : Nat} {s s' : State} (h : Inv hF s₀ k s) {d : Reg} (hd : d ∉ iregs) {v : BitVec 32}
    (u : Upd s s' d v) : Inv hF s₀ k s' :=
  h.keep hp hz u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp)

theorem Inv.same {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ iregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : Inv hF s₀ k s' :=
  h.keep hp hz hrd hwr hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- After a call that writes where a step writes. -/
theorem Inv.after {k : Nat} {s s' : State} (h : Inv hF s₀ k s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, Wks F s₀ r) : Inv hF s₀ k s' := by
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
theorem ea_scr {s : State} (hk : KR F s₀ s) {o : Nat} (ho : o < F.L8) :
    s.ea (at_ .ebp o) = A s₀ o := by
  rw [show s.ea (at_ .ebp o) = (dO s₀ o).setWidth 64 by
    show (s.gpr .ebp + BitVec.ofNat 32 o).setWidth 64 = _; rw [hk.ebp]]
  exact dO_addr hp ho

/-- `INT (1)`, no bytes written, and whether `out_len` is 0. -/
theorem loopInit_ok {s : State} (hk : KR F s₀ s) (hst : States hF s₀ s.mem) (hkl : (K0 hF s₀).length = F.H.B) :
    WP isa (.block F.loopInit) s fun t => Inv hF s₀ 0 t ∧ t.zf = some (decide (ol s₀ = 0)) := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D
  unfold Fns.loopInit
  refine wp_movi fun s₁ u₁ => wp_bswap fun s₂ u₂ => ?_
  refine wp_store (a := A s₀ F.intO) (ea_scr hp ((hk.upd (by decide) u₁).upd (by decide) u₂) (hz.intO_lt))
    (by rw [u₂.wr, u₁.wr]; exact in_sc hp hz hk.wr (end_le hz)) fun s₃ m₃ => ?_
  have f₃ : Frame [sR s₀ F.intO 4] s.mem s₃.mem := by
    rw [m₃.mem, u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₃ : KR F s₀ s₃ := hk.write hz (by rw [m₃.rd, u₂.rd, u₁.rd]) (by rw [m₃.wr, u₂.wr, u₁.wr])
    (fun r hr => by
      rw [m₃.gpr, u₂.other r (by simp only [List.mem_cons] at hr; rcases hr with rfl | rfl | h <;> simp_all),
        u₁.other r (by simp only [List.mem_cons] at hr; rcases hr with rfl | rfl | h <;> simp_all)])
    (by omega_using [hl]) (end_le hz) f₃
  refine wp_movi fun s₄ u₄ => wp_arg hp (k₃.upd (by decide) u₄) (by decide) fun s₅ u₅ => ?_
  refine wp_test fun s₆ f₆ z₆ => WP.block_nil ⟨⟨?_, ?_, hkl, ?_, ?_, by simp [Gk, Whole.G], ?_⟩, ?_⟩
  · exact ((k₃.upd (by decide) u₄).upd (by decide) u₅).same f₆.rd f₆.wr (fun r _ => by rw [f₆.gpr]) f₆.mem
  · rw [f₆.mem, u₅.mem, u₄.mem]
    exact hst.keep hz f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by omega_using [hl])) (hz.st0O_3S) (end_le hz)
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr]; simp [dn, Whole.done]
  · rw [f₆.mem, u₅.mem, u₄.mem, m₃.mem, Mem.readW_writeW_self32, u₂.gpr, u₁.gpr]; rfl
  · simp [dn, Whole.done, bytesAt]
  · rw [z₆, u₅.gpr, Pbkdf2.Stream.X86.test_z]

/-! ## A step: the working state, and `INT (i)` -/

/-- The salted inner state, copied into the working state. -/
theorem b1_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (copy .ebp F.stSO .ebp F.stWO F.H.S) s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D
  refine WP.mono (copy_part_ok hp hz h.kr hz.S.1 (hz.stSO_S) (hz.stWO_S) (by omega_using [hl]) (Or.inl (by omega_using [hl])))
    fun t ⟨kt, g, m⟩ => ⟨?_, ?_⟩
  · have f : Frame [sR s₀ F.stWO F.H.S] s.mem t.mem := by
      rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    exact h.keep hp hz (kt.rd.trans h.kr.rd.symm) (kt.wr.trans h.kr.wr.symm) (fun r hr => g r (by
      simp only [iregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (.inr ⟨_, _, rfl, Nat.le_refl _, by omega_using [hl]⟩)
  · refine hF.hH.repr _ _ _ _ _ (fun i hi => ?_) h.st.stS
    rw [m]; exact copied_byte (by omega_using [hz_S]) i hi

/-- `update`'s arguments: the working state, `B + salt_len`, `INT (i)`. -/
theorem b2_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.updArgs) s fun t => Inv hF s₀ k t ∧ t.gpr .edi = dO s₀ F.stWO ∧
      t.gpr .esi = arg s₀ 3 + BitVec.ofNat 32 F.H.B ∧ t.gpr .eax = 0 ∧ t.gpr .ecx = BitVec.ofNat 32 4 ∧
      t.gpr .edx = dO s₀ F.intO ∧ t.mem = s.mem := by
  simp only [Fns.updArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have i₁ := h.upd hp hz (by decide) u₁
  refine wp_arg hp i₁.kr (by decide) fun s₂ u₂ => wp_addi fun s₃ u₃ => wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => ?_
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

theorem b3_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (hdi : s.gpr .edi = dO s₀ F.stWO)
    (hsi : s.gpr .esi = arg s₀ 3 + BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = BitVec.ofNat 32 4)
    (hdx : s.gpr .edx = dO s₀ F.intO) :
    UpdArgs hF.hH s .esi .edi (dO s₀ F.stWO) (dO s₀ F.intO) (scr s₀) (arg s₀ 3 + BitVec.ofNat 32 F.H.B) 4 := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have := hF.hH.hWb
  have hk := h.kr
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  have ei := dO_addr hp (o := F.intO) (hz.intO_lt)
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
      sp48 := by rw [hk.esp]; have hp_sp76 := hp.sp76; omega_using [hp_sp76]
      cd := by
        rw [ei]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.intO) (n := 4) (end_le hz)
          exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk (hz.stWO_S)
          · exact cov_low hp hk (by omega_using [hl, he, hz_W, this])
      st_sc := by rw [ea]; exact (low_disj hz (k := hF.hH.Wb) (by omega_using [hl, hz_W, this]) (hz.stWO_S)).symm
      d_st := by rw [ei, ea]; exact part_disj hz (Or.inr (hz.stWO_S_intO)) (end_le hz) (hz.stWO_S)
      d_sc := by rw [ei]; exact (low_disj hz (k := hF.hH.Wb) (by omega_using [hl, hz_W, this]) (end_le hz)).symm
      b_st := by rw [ea]; exact b48 hp hk (part_sub (hz.stWO_S))
      b_d := by rw [ei]; exact b48 hp hk (part_sub (end_le hz))
      b_sc := b48 hp hk (low_sub (by omega_using [hl, he, hz_W, this]))
      nst := by rw [dO_toNat hp (hz.stWO_lt)]; have hp_nsc := hp.nsc; omega_using [hl, he, hp_nsc]
      nd := by rw [dO_toNat hp (hz.intO_lt)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he]
      nsc := by have hp_nsc := hp.nsc; omega_using [hl, he, hz_W, this, hp_nsc] }

/-- `update` with `INT (k + 1)`. -/
theorem b3_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) (hdi : s.gpr .edi = dO s₀ F.stWO)
    (hsi : s.gpr .esi = arg s₀ 3 + BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = BitVec.ofNat 32 4)
    (hdx : s.gpr .edx = dO s₀ F.intO)
    (hr : hF.hH.SH.Repr s.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀)) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)) s
      fun t => Inv hF s₀ k t ∧
        hF.hH.SH.Repr t.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  have ei := dO_addr hp (o := F.intO) (hz.intO_lt)
  have hsf := salt_fit hp hz
  refine upd_frame hF.hH (b3_args hp hz h hdi hsi hax hcx hdx) fun s' a r => ⟨h.after hp hz (After.of_hmac (by
    rw [h.kr.esp]; exact hp.sp76) a) fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], Nat.le_refl _, by omega_using [hl]⟩
    · exact .inl ⟨_, rfl, by omega_using [this, hz_W]⟩
  · have := r _ (by rw [ea]; exact hr) (by
      rw [List.length_append, xorPad_length, h.k0l, bytesAt_length,
        show arg s₀ 3 + BitVec.ofNat 32 F.H.B = BitVec.ofNat 32 (F.H.B + sl s₀) by
          rw [Nat.add_comm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        zero_append_ofNat (by omega_using [hsf])])
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
  omega_using []

/-- HMAC's `finalize`'s arguments. -/
theorem b4_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.finArgs) s fun t => Inv hF s₀ k t ∧ t.gpr .edx = dO s₀ F.stWO ∧
      t.gpr .esi = dO s₀ F.st1O ∧ t.gpr .eax = arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4) ∧ t.gpr .ecx = 0 ∧
      t.gpr .edi = dO s₀ F.uO ∧ t.mem = s.mem := by
  simp only [Fns.finArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have i₁ := h.upd hp hz (by decide) u₁
  refine scr_ok i₁.kr fun s₂ u₂ => ?_
  have i₂ := i₁.upd hp hz (by decide) u₂
  refine wp_arg hp i₂.kr (by decide) fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_movi fun s₅ u₅ => ?_
  have i₅ := ((i₂.upd hp hz (by decide) u₃).upd hp hz (by decide) u₄).upd hp hz (by decide) u₅
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.uO)]
  refine scr_ok i₅.kr fun s₆ u₆ => WP.block_nil ⟨i₅.upd hp hz (by decide) u₆, ?_, ?_, ?_, ?_, u₆.gpr, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr]
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b5_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (hdx : s.gpr .edx = dO s₀ F.stWO)
    (hsi : s.gpr .esi = dO s₀ F.st1O) (hax : s.gpr .eax = arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4))
    (hcx : s.gpr .ecx = 0) (hdi : s.gpr .edi = dO s₀ F.uO) :
    HfArgs hF.hH.SH hF.Wf s (dO s₀ F.stWO) (dO s₀ F.st1O) (arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4)) 0
      (dO s₀ F.uO) (scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have hF_hWf := hF.hWf; have hS := hF.hH.hS; have hD := hF.hH.hD
  have hk := h.kr
  have ew := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  have e1 := dO_addr hp (o := F.st1O) (hz.st1O_lt)
  have eu := dO_addr hp (o := F.uO) (hz.uO_lt)
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
          obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.st1O) (n := F.H.S) (hz.st1O_S)
          exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [hS, hD, ew, eu]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact cov_part hp hk (hz.stWO_S)
          · exact cov_part hp hk (hz.uO_D)
          · exact cov_low hp hk (by omega_using [hF_hWf, he, hl])
      i_u := by rw [hS, ew, e1]; exact part_disj hz (Or.inr (by omega_using [hl])) (hz.stWO_S) (hz.st1O_S)
      i_o := by rw [hS, hD, ew, eu]; exact part_disj hz (Or.inl (by omega_using [hl])) (hz.stWO_S) (hz.uO_D)
      i_s := by rw [hS, ew]; exact (low_disj hz (by omega_using [hl, hF_hWf]) (hz.stWO_S)).symm
      u_o := by rw [hS, hD, e1, eu]; exact part_disj hz (Or.inl (by omega_using [hl])) (hz.st1O_S) (hz.uO_D)
      u_s := by rw [hS, e1]; exact (low_disj hz (by omega_using [hF_hWf, hl]) (hz.st1O_S)).symm
      o_s := by rw [hD, eu]; exact (low_disj hz (by omega_using [hF_hWf, hl]) (hz.uO_D)).symm
      b_i := by rw [hS, ew]; exact b76 hp hk (part_sub (hz.stWO_S))
      b_u := by rw [hS, e1]; exact b76 hp hk (part_sub (hz.st1O_S))
      b_o := by rw [hD, eu]; exact b76 hp hk (part_sub (hz.uO_D))
      b_s := b76 hp hk (low_sub (by omega_using [hl, he, hF_hWf]))
      ni := by rw [hS, dO_toNat hp (hz.stWO_lt)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nu := by rw [hS, dO_toNat hp (hz.st1O_lt)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      no := by rw [hD, dO_toNat hp (hz.uO_lt)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nsc := by have hp_nsc := hp.nsc; omega_using [hp_nsc, hF_hWf, he, hl] }

/-- HMAC's `finalize`: `U₁ = PRF (salt ‖ INT (k + 1))`. -/
theorem b5_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) (hdx : s.gpr .edx = dO s₀ F.stWO)
    (hsi : s.gpr .esi = dO s₀ F.st1O) (hax : s.gpr .eax = arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4))
    (hcx : s.gpr .ecx = 0) (hdi : s.gpr .edi = dO s₀ F.uO)
    (hr : hF.hH.SH.Repr s.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.frame (.push hf6) (.call F.hfN F.hfC) (.pop .eax hf6.length)) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.uO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have hF_hWf := hF.hWf; have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have ew := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  have e1 := dO_addr hp (o := F.st1O) (hz.st1O_lt)
  have eu := dO_addr hp (o := F.uO) (hz.uO_lt)
  have hsf := salt_fit hp hz
  refine hf_frame (FnsOK.reprOK hF) (by rw [hS]; omega_using [hz_S]) hF.hf hF.hfSp hF.hfSU (b5_args hp hz h hdx hsi hax hcx hdi)
    fun s' a post => ⟨h.after hp hz a fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [ew, hS], Nat.le_refl _, by omega_using [hl]⟩
    · exact .inr ⟨_, _, by rw [eu, hD], by omega_using [hl], by omega_using [hl]⟩
    · exact .inl ⟨_, rfl, by omega_using [hF_hWf]⟩
  · have := post (K0 hF s₀) (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) (by rw [h.k0l, hB])
      (by rw [h.k0l, List.length_append, bytesAt_length]; simp only [Spec.Pbkdf2.int, List.length_cons,
        List.length_nil]; omega_using [hsf])
      (by rw [ew, ← List.append_assoc]; exact hr)
      (by
        rw [List.length_append, bytesAt_length, hB,
          show arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4) = BitVec.ofNat 32 (F.H.B + (sl s₀ + 4)) by
            rw [add_ofNat_eq _ (by have : sl s₀ = (arg s₀ 3).toNat := rfl; omega_using [this, hsf]),
              show (arg s₀ 3).toNat + (F.H.B + 4) = F.H.B + (sl s₀ + 4) by
                have : sl s₀ = (arg s₀ 3).toNat := rfl; omega_using [this]],
          zero_append_ofNat (by omega_using [hsf])]
        simp only [Spec.Pbkdf2.int, List.length_cons, List.length_nil])
      (by rw [e1]; exact h.st.st1)
    rwa [eu, hD] at this

end

end VG.Proof.Pbkdf2.Whole.X86
