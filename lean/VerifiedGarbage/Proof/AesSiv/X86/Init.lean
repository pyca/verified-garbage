import VerifiedGarbage.Proof.CmacAes.Stream.X86.Common
import VerifiedGarbage.Proof.AesSiv.X86.Contract
import VerifiedGarbage.Proof.AesSiv.Key
import VerifiedGarbage.Impl.AesSiv.X86

/-!
# AES-SIV on x86: `vg_aes_siv_init`'s code

Untrusted: everything here is checked by Lean. `initCore` saves the
registers in the scratch buffer (as streaming AES-CMAC's `init`, whose
pieces this reuses), expands `K1` into the context, derives its subkeys
after the schedule, expands `K2` after them and restores the registers: the
context is then that of the key (`Proof.AesSiv.keyRepr_of`). The code
between the calls is constant time by the taint analysis (from `esp` and the
stack arguments), and the calls by their own proofs (`ek_rel`, `sub_rel`),
their arguments pinned by `IMid₁`, `IMid₂` and `IMid₃`.
-/

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.Impl.AesSiv.X86
open VG.Impl.CmacAes.Stream.X86 (call4 save restore saved)
open VG.Proof.CmacAes.Stream.X86 (EArgs EPost SArgs SPost ek_call ek_rel sub_call sub_rel savedMem savedMem_frame
  saveMem_slot saved_bound saved_ne_eax save_wp restore_wp arg_sub args_below arg_keep arg_ofNat add_setWidth
  add_toNat arg_contains Pt Pt.refl Pt.agree below_eq)
open VG.Impl.CmacAes.X86 (argOp)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_addi wp_add wp_shr)
open VG.Proof.CmacAes.X86 (wp_arg)

variable (v : Proof.Aes.X86.Ctr32Impl)

section
variable (s₀ : State)

abbrev iKp : BitVec 32 := arg s₀ 0
abbrev iKL : Nat := (arg s₀ 1).toNat
abbrev iCt : BitVec 32 := arg s₀ 2
abbrev iSc : BitVec 32 := arg s₀ 3
abbrev iE : BitVec 32 := s₀.gpr .esp
abbrev ikR : Region := ⟨(iKp s₀).setWidth 64, iKL s₀⟩
abbrev ictR : Region := ⟨(iCt s₀).setWidth 64, 512⟩
abbrev iscR : Region := ⟨(iSc s₀).setWidth 64, 2560⟩
abbrev iaR : Region := ⟨argAddr s₀ 0, 16⟩

/-- Where the code writes: the context, the scratch buffer and the stack. -/
abbrev IBig : List Region := [ictR s₀, iscR s₀, below (iE s₀) 48]

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [ikR s₀, iaR s₀]
  wr : s₀.wr = [ictR s₀, iscR s₀]
  k_c : (ikR s₀).Disjoint (ictR s₀)
  k_s : (ikR s₀).Disjoint (iscR s₀)
  k_a : (ikR s₀).Disjoint (iaR s₀)
  c_s : (ictR s₀).Disjoint (iscR s₀)
  c_a : (ictR s₀).Disjoint (iaR s₀)
  s_a : (iscR s₀).Disjoint (iaR s₀)
  ret_k : (⟨(iE s₀).setWidth 64, 4⟩ : Region).Disjoint (ikR s₀)
  ret_c : (⟨(iE s₀).setWidth 64, 4⟩ : Region).Disjoint (ictR s₀)
  ret_s : (⟨(iE s₀).setWidth 64, 4⟩ : Region).Disjoint (iscR s₀)
  ret_a : (⟨(iE s₀).setWidth 64, 4⟩ : Region).Disjoint (iaR s₀)
  b_k' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (ikR s₀)
  b_c' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (ictR s₀)
  b_s' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (iscR s₀)
  b_a' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (iaR s₀)
  fK : (iKp s₀).toNat + iKL s₀ ≤ 2 ^ 32
  fC : (iCt s₀).toNat + 512 ≤ 2 ^ 32
  fS : (iSc s₀).toNat + 2560 ≤ 2 ^ 32
  esp48 : 48 ≤ (iE s₀).toNat
  espfit : (iE s₀).toNat + 20 ≤ 2 ^ 32
  klen : iKL s₀ = 32 ∨ iKL s₀ = 48 ∨ iKL s₀ = 64

theorem IPre.of {s₀ : State} (h : initX86.pre s₀) : IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, w⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, w⟩

namespace IPre
variable {s₀ : State} (hp : IPre s₀)
include hp

theorem b_k : (below (iE s₀) 48).Disjoint (ikR s₀) := by rw [below_eq hp.esp48]; exact hp.b_k'
theorem b_c : (below (iE s₀) 48).Disjoint (ictR s₀) := by rw [below_eq hp.esp48]; exact hp.b_c'
theorem b_s : (below (iE s₀) 48).Disjoint (iscR s₀) := by rw [below_eq hp.esp48]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.espfit; omega

theorem arg_in {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨iaR s₀, by simp [hp.rd, hp.wr], arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `IBig` changes. -/
theorem keep {m : Mem} (hf : Frame (IBig s₀) s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.c_a.symm.sub_left (arg_sub hp.fit hi)
    · exact hp.s_a.symm.sub_left (arg_sub hp.fit hi)
    · exact (args_below hp.fit (by decide) hp.esp48).symm.sub_left (arg_sub hp.fit hi)

theorem argsOut : ArgsOut 4 s₀ := by
  refine ⟨by have := hp.espfit; omega, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega) hp.ret_c hp.c_a.symm
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega) hp.ret_s hp.s_a.symm

end IPre

theorem IPre.savedMem_big {s₀ : State} (_hp : IPre s₀) : Frame (IBig s₀) s₀.mem (savedMem s₀ (iSc s₀)) :=
  (savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨iscR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Arithmetic -/

theorem shr_ofNat (x : BitVec 32) (k : Nat) : x >>> k = BitVec.ofNat 32 (x.toNat / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)]

theorem rounds32 {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 32 KL >>> 3 + 6 = BitVec.ofNat 32 (KL / 8 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

/-! ## Before the first call -/

theorem initPre_eq : initPre = .mov .eax (argOp 3) :: (save ++ ([.mov .eax (argOp 0), .mov .ecx (argOp 1),
    .shift .shr .ecx 1, .mov .edx (argOp 2), .mov .ebx (argOp 3)] : List Instr)) := rfl

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ s : State) : Prop where
  args : EArgs s (iKp s₀) (iCt s₀) (iSc s₀) (iKL s₀ / 2)
  esp : s.gpr .esp = iE s₀
  mem : s.mem = savedMem s₀ (iSc s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} (hp : IPre s₀) : WP isa (.block initPre) s₀ (IMid₁ s₀) := by
  have fS := hp.fS
  have fC := hp.fC
  have fK := hp.fK
  have e48 := hp.esp48
  have kl := hp.klen
  rw [initPre_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine save_wp (Sc := iSc s₀) u₁.gpr (by omega) (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  have hm₂ : s₂.mem = savedMem s₀ (iSc s₀) := by
    rw [m₂, u₁.mem, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = iE s₀ := by rw [g₂, u₁.other _ (by decide)]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr]
  have av : ∀ i < 4, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep hp.savedMem_big hi
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 0 (by decide))
    fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide)) (by rw [u₃.mem]; exact av 1 (by decide))
    fun s₄ u₄ => ?_
  refine wp_shr (by decide) fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem, u₃.mem]; exact av 2 (by decide)) fun s₆ u₆ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]; exact av 3 (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have esp₇ : s₇.gpr .esp = iE s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), esp₂]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂']
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂']
  have b20 : Region.Sub (below (iE s₀) 20) (below (iE s₀) 48) := below_sub (by decide) e48
  have hk : Region.Sub ⟨(iKp s₀).setWidth 64, iKL s₀ / 2⟩ (ikR s₀) := Region.sub_prefix (by omega)
  refine ⟨?_, esp₇, by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂], rd₇, wr₇⟩
  exact
  { eax := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr]
    ecx := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, shr_ofNat]
    edx := by rw [u₇.other _ (by decide), u₆.gpr]
    ebx := u₇.gpr
    klen := by omega
    esp := by rw [esp₇]; omega
    kw := (hp.k_c.sub_left hk).sub_right (Region.sub_prefix (by decide))
    ks := (hp.k_s.sub_left hk).sub_right (Region.sub_prefix (by decide))
    ws := (hp.c_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₇]; exact (hp.b_k.sub_left b20).sub_right hk
    bW := by rw [esp₇]; exact (hp.b_c.sub_left b20).sub_right (Region.sub_prefix (by decide))
    bS := by rw [esp₇]; exact (hp.b_s.sub_left b20).sub_right (Region.sub_prefix (by decide))
    fK := by omega
    fW := by omega
    fS := by omega
    reads := by
      rw [rd₇, wr₇, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ikR s₀, by simp, 0, by simp, by simp only [Nat.zero_add]; omega⟩
    writes := by
      rw [wr₇, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ictR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩ }

end VG.Proof.AesSiv.X86
