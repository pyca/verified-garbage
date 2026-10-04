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
  add_toNat arg_contains Pt Pt.refl Pt.agree below_eq ret_below)
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

/-! ## After a call -/

/-- What is known after each call. -/
structure IAft (s₀ s : State) : Prop where
  esp : s.gpr .esp = iE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (IBig s₀) s₀.mem s.mem

theorem IAft.pt {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s) : Pt 4 s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.keep h.frame hi⟩

theorem IMid₁.after {s₀ s s' : State} (hp : IPre s₀) (h : IMid₁ s₀ s)
    (h' : EPost s (iKp s₀) (iCt s₀) (iSc s₀) (iKL s₀ / 2) s') : IAft s₀ s' := by
  have fr := h'.frame
  rw [h.esp, h.mem] at fr
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.esp], by rw [h'.rd, h.rd], by rw [h'.wr, h.wr],
    hp.savedMem_big.trans (fr.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨ictR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨iscR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨below (iE s₀) 48, by simp, below_sub (by decide) hp.esp48⟩

/-! ## Between the first two calls -/

/-- What the code between the first two calls leaves. -/
structure IMid₂ (s₀ s : State) : Prop where
  args : SArgs s (iCt s₀) (iCt s₀ + BitVec.ofNat 32 240) (iSc s₀) (iKL s₀ / 8 + 6)
  aft : IAft s₀ s

theorem initMid₁_wp {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s) :
    WP isa (.block initMid₁) s fun s' => IMid₂ s₀ s' ∧ s'.mem = s.mem := by
  have fS := hp.fS
  have fC := hp.fC
  have e48 := hp.esp48
  have rw₀ : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have av : ∀ i < 4, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.keep h.frame hi
  refine wp_arg (s₀ := s₀) h.esp (by rw [rw₀]; exact hp.arg_in (by decide)) (av 2 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, rw₀]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact av 1 (by decide))
    fun s₂ u₂ => ?_
  refine wp_shr (by decide) fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_addi fun s₆ u₆ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, rw₀]
        exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact av 3 (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have esp₇ : s₇.gpr .esp = iE s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have kC : Region.Sub ⟨(iCt s₀ + BitVec.ofNat 32 240).setWidth 64, 32⟩ (ictR s₀) := by
    rw [add_setWidth (by omega)]; exact Offset.sub_base _ (by decide)
  have hR : iKL s₀ / 8 + 6 = 10 ∨ iKL s₀ / 8 + 6 = 12 ∨ iKL s₀ / 8 + 6 = 14 := by
    rcases hp.klen with h | h | h <;> rw [h] <;> decide
  refine ⟨⟨?_, ⟨esp₇, rd₇, wr₇, by rw [m₇]; exact h.frame⟩⟩, m₇⟩
  exact
  { eax := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    ecx := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr,
        arg_ofNat s₀ 1]
      exact rounds32 hp.klen
    edx := by
      rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]
    ebx := u₇.gpr
    rounds := hR
    esp := by rw [esp₇]; exact e48
    wk := by
      rw [add_setWidth (by omega)]; exact Offset.base_disjoint _ (by decide) (by omega)
    ws := (hp.c_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    ks := (hp.c_s.sub_left kC).sub_right (Region.sub_prefix (by decide))
    bW := by rw [esp₇]; exact hp.b_c.sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₇]; exact hp.b_c.sub_right kC
    bS := by rw [esp₇]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fW := by omega
    fK := by rw [add_toNat (by omega)]; omega
    fS := by omega
    reads := by
      rw [rd₇, wr₇, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ictR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₇, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ictR s₀, by simp, 240, add_setWidth (by omega), by simp⟩
      · exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩ }

theorem IMid₂.after {s₀ s s' : State} (hp : IPre s₀) (h : IMid₂ s₀ s)
    (h' : SPost s (iCt s₀) (iCt s₀ + BitVec.ofNat 32 240) (iSc s₀) (iKL s₀ / 8 + 6) s') : IAft s₀ s' := by
  have fr := h'.frame
  rw [h.aft.esp] at fr
  have fC := hp.fC
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.aft.esp], by rw [h'.rd, h.aft.rd],
    by rw [h'.wr, h.aft.wr], h.aft.frame.trans (fr.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨ictR s₀, by simp, ?_⟩
    rw [add_setWidth (by omega)]; exact Offset.sub_base _ (by decide)
  · exact ⟨iscR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨below (iE s₀) 48, by simp, fun _ h => h⟩

/-! ## Between the last two calls -/

/-- What the code between the last two calls leaves. -/
structure IMid₃ (s₀ s : State) : Prop where
  args : EArgs s (iKp s₀ + BitVec.ofNat 32 (iKL s₀ / 2)) (iCt s₀ + BitVec.ofNat 32 272) (iSc s₀) (iKL s₀ / 2)
  aft : IAft s₀ s

theorem initMid₂_wp {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s) :
    WP isa (.block initMid₂) s fun s' => IMid₃ s₀ s' ∧ s'.mem = s.mem := by
  have fS := hp.fS
  have fC := hp.fC
  have fK := hp.fK
  have e48 := hp.esp48
  have kl := hp.klen
  have rw₀ : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have av : ∀ i < 4, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.keep h.frame hi
  refine wp_arg (s₀ := s₀) h.esp (by rw [rw₀]; exact hp.arg_in (by decide)) (av 1 (by decide)) fun s₁ u₁ => ?_
  refine wp_shr (by decide) fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, rw₀]; exact hp.arg_in (by decide))
    (by rw [u₂.mem, u₁.mem]; exact av 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_add fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, rw₀]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact av 2 (by decide)) fun s₅ u₅ => ?_
  refine wp_addi fun s₆ u₆ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, rw₀]
        exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact av 3 (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have esp₇ : s₇.gpr .esp = iE s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have b20 : Region.Sub (below (iE s₀) 20) (below (iE s₀) 48) := below_sub (by decide) e48
  have aK : (iKp s₀ + BitVec.ofNat 32 (iKL s₀ / 2)).setWidth 64 =
      (iKp s₀).setWidth 64 + BitVec.ofNat 64 (iKL s₀ / 2) := add_setWidth (by omega)
  have aC : (iCt s₀ + BitVec.ofNat 32 272).setWidth 64 = (iCt s₀).setWidth 64 + BitVec.ofNat 64 272 :=
    add_setWidth (by omega)
  have hk : Region.Sub ⟨(iKp s₀ + BitVec.ofNat 32 (iKL s₀ / 2)).setWidth 64, iKL s₀ / 2⟩ (ikR s₀) := by
    rw [aK]; exact Offset.sub_base _ (by omega)
  have hc : Region.Sub ⟨(iCt s₀ + BitVec.ofNat 32 272).setWidth 64, 240⟩ (ictR s₀) := by
    rw [aC]; exact Offset.sub_base _ (by decide)
  refine ⟨⟨?_, ⟨esp₇, rd₇, wr₇, by rw [m₇]; exact h.frame⟩⟩, m₇⟩
  exact
  { eax := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr,
        u₃.other _ (by decide), u₂.gpr, u₁.gpr, shr_ofNat]
    ecx := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.gpr, shr_ofNat]
    edx := by rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr]
    ebx := u₇.gpr
    klen := by omega
    esp := by rw [esp₇]; omega
    kw := (hp.k_c.sub_left hk).sub_right hc
    ks := (hp.k_s.sub_left hk).sub_right (Region.sub_prefix (by decide))
    ws := (hp.c_s.sub_left hc).sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₇]; exact (hp.b_k.sub_left b20).sub_right hk
    bW := by rw [esp₇]; exact (hp.b_c.sub_left b20).sub_right hc
    bS := by rw [esp₇]; exact (hp.b_s.sub_left b20).sub_right (Region.sub_prefix (by decide))
    fK := by rw [add_toNat (by omega)]; omega
    fW := by rw [add_toNat (by omega)]; omega
    fS := by omega
    reads := by
      rw [rd₇, wr₇, hp.rd, hp.wr, aK]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨ikR s₀, by simp, iKL s₀ / 2, rfl, by simp only; omega⟩
    writes := by
      rw [wr₇, hp.wr, aC]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ictR s₀, by simp, 272, rfl, by simp⟩
      · exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩ }

theorem IMid₃.after {s₀ s s' : State} (hp : IPre s₀) (h : IMid₃ s₀ s)
    (h' : EPost s (iKp s₀ + BitVec.ofNat 32 (iKL s₀ / 2)) (iCt s₀ + BitVec.ofNat 32 272) (iSc s₀) (iKL s₀ / 2) s') :
    IAft s₀ s' := by
  have fr := h'.frame
  rw [h.aft.esp] at fr
  have fC := hp.fC
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.aft.esp], by rw [h'.rd, h.aft.rd],
    by rw [h'.wr, h.aft.wr], h.aft.frame.trans (fr.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨ictR s₀, by simp, ?_⟩
    rw [add_setWidth (by omega)]; exact Offset.sub_base _ (by decide)
  · exact ⟨iscR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨below (iE s₀) 48, by simp, below_sub (by decide) hp.esp48⟩

/-! ## The whole code -/

theorem initCore_eq : initCore v.expand v.callee v.suffix =
    .seq (.block initPre) (.seq (call4 v.expand.name v.expand.code) (.seq (.block initMid₁)
      (.seq (call4 ("vg_cmac_aes_subkeys" ++ v.suffix) (Impl.CmacAes.X86.subkeys v.callee))
        (.seq (.block initMid₂) (.seq (call4 v.expand.name v.expand.code) (.block (restore 3))))))) := rfl

theorem init_wp {s₀ : State} (h0 : initX86.pre s₀) :
    WP isa (initCore v.expand v.callee v.suffix) s₀ fun s' => abiPreserved s₀ s' ∧ initX86.post s₀ s' := by
  have hp := IPre.of h0
  have fS := hp.fS
  have fC := hp.fC
  have fK := hp.fK
  have kl := hp.klen
  have e48 := hp.esp48
  rw [initCore_eq]
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono ((ek_call v) h₁.args) fun s₂ h₂ => ?_)
  have a₂ := h₁.after hp h₂
  refine WP.seq (WP.mono (initMid₁_wp hp a₂) fun s₃ ⟨h₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono ((sub_call v) h₃.args) fun s₄ h₄ => ?_)
  have a₄ := h₃.after hp h₄
  refine WP.seq (WP.mono (initMid₂_wp hp a₄) fun s₅ ⟨h₅, m₅⟩ => ?_)
  refine WP.seq (WP.mono ((ek_call v) h₅.args) fun s₆ h₆ => ?_)
  have a₆ := h₅.after hp h₆
  have aC : ∀ d, d ≤ 272 → (iCt s₀ + BitVec.ofNat 32 d).setWidth 64 = (iCt s₀).setWidth 64 + BitVec.ofNat 64 d :=
    fun d hd => add_setWidth (by omega)
  have aK : (iKp s₀ + BitVec.ofNat 32 (iKL s₀ / 2)).setWidth 64 =
      (iKp s₀).setWidth 64 + BitVec.ofNat 64 (iKL s₀ / 2) := add_setWidth (by omega)
  have f₂ : Frame [⟨(iCt s₀).setWidth 64, 240⟩, ⟨(iSc s₀).setWidth 64, 512⟩, below (iE s₀) 48] s₁.mem s₂.mem := by
    have := h₂.frame
    rw [h₁.esp] at this
    refine this.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (iE s₀) 48, by simp, below_sub (by decide) e48⟩
  have f₄ : Frame [⟨(iCt s₀).setWidth 64 + BitVec.ofNat 64 240, 32⟩, ⟨(iSc s₀).setWidth 64, 2176⟩,
      below (iE s₀) 48] s₂.mem s₄.mem := by
    have := h₄.frame; rw [h₃.aft.esp, m₃, aC 240 (by decide)] at this; exact this
  have f₆ : Frame [⟨(iCt s₀).setWidth 64 + BitVec.ofNat 64 272, 240⟩, ⟨(iSc s₀).setWidth 64, 512⟩,
      below (iE s₀) 48] s₄.mem s₆.mem := by
    have := h₆.frame
    rw [h₅.aft.esp, m₅, aC 272 (by decide)] at this
    refine this.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (iE s₀) 48, by simp, below_sub (by decide) e48⟩
  -- The saved registers.
  have dSlot : ∀ d, 2176 ≤ d → d + 4 ≤ 2192 → ∀ r ∈ [⟨(iCt s₀).setWidth 64, 240⟩, ⟨(iSc s₀).setWidth 64, 512⟩,
      below (iE s₀) 48, ⟨(iCt s₀).setWidth 64 + BitVec.ofNat 64 240, 32⟩, ⟨(iSc s₀).setWidth 64, 2176⟩,
      ⟨(iCt s₀).setWidth 64 + BitVec.ofNat 64 272, 240⟩],
      (⟨(iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := fun d h₁ h₂ r hr => by
    have sub : Region.Sub ⟨(iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (iscR s₀) := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.c_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact hp.b_s.symm.sub_left sub
    · exact (hp.c_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact (hp.c_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
  have slots : ∀ r d, (r, d) ∈ saved →
      s₆.mem.readW ((iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    have hb := saved_bound _ hrd
    have c := Region.contains_self ((iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 4
    rw [f₆.readW c (fun q hq => dSlot d hb.1 hb.2 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with h | h | h <;> simp [h]))
        (by decide),
      f₄.readW c (fun q hq => dSlot d hb.1 hb.2 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with h | h | h <;> simp [h]))
        (by decide),
      f₂.readW c (fun q hq => dSlot d hb.1 hb.2 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with h | h | h <;> simp [h]))
        (by decide), h₁.mem]
    exact saveMem_slot _ _ _ hrd
  refine WP.mono (restore_wp (s₀ := s₀) (i := 3) (Sc := iSc s₀) a₆.esp
    (by rw [a₆.rd, a₆.wr]; exact hp.arg_in (by decide)) (hp.keep a₆.frame (by decide)) (by omega)
    (by
      rw [a₆.rd, a₆.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩)
    slots) fun s₇ ⟨hcs, m₇⟩ => ?_
  have F₇ : Frame (IBig s₀) s₀.mem s₇.mem := by rw [m₇]; exact a₆.frame
  refine ⟨⟨hcs, F₇.readW (r := ⟨(iE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_c
    · exact hp.ret_s
    · exact ret_below e48
  -- The key context.
  show Spec.Siv.KeyRepr s₇.mem ((iCt s₀).setWidth 64) (Spec.Aes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀))
  have hKL : ∀ {m : Mem}, Frame (IBig s₀) s₀.mem m → ∀ {d n : Nat}, d + n ≤ iKL s₀ →
      Spec.Aes.bytesAt m ((iKp s₀).setWidth 64 + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₀.mem ((iKp s₀).setWidth 64 + BitVec.ofNat 64 d) n := fun hf d n hd =>
    Proof.Cmac.bytesAt_frame hf (fun r hr => by
      have sub : Region.Sub ⟨(iKp s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ (ikR s₀) := Offset.sub_base _ hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.k_c.sub_left sub
      · exact hp.k_s.sub_left sub
      · exact hp.b_k.symm.sub_left sub) (by omega)
  have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  have hkey₁ : Spec.Aes.bytesAt s₁.mem ((iKp s₀).setWidth 64) (iKL s₀ / 2) =
      Spec.Aes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀ / 2) := by
    have := hKL (m := s₁.mem) (by rw [h₁.mem]; exact hp.savedMem_big) (d := 0) (n := iKL s₀ / 2) (by omega)
    rwa [k0] at this
  have hkey₅ : Spec.Aes.bytesAt s₅.mem ((iKp s₀).setWidth 64 + BitVec.ofNat 64 (iKL s₀ / 2)) (iKL s₀ / 2) =
      Spec.Aes.bytesAt s₀.mem ((iKp s₀).setWidth 64 + BitVec.ofNat 64 (iKL s₀ / 2)) (iKL s₀ / 2) := by
    rw [m₅]; exact hKL a₄.frame (by omega)
  have hR : Spec.Aes.rounds (iKL s₀ / 2 / 4) = iKL s₀ / 8 + 6 := by simp only [Spec.Aes.rounds]; omega
  have hRb : 16 * (iKL s₀ / 8 + 6 + 1) ≤ 240 := by omega
  have o₂ := h₂.out
  rw [hkey₁, hR] at o₂
  -- `K1`'s schedule, kept by the later calls.
  have sch₁ : Spec.Aes.bytesAt s₇.mem ((iCt s₀).setWidth 64) (16 * (iKL s₀ / 8 + 6 + 1)) =
      Spec.Aes.bytesAt s₂.mem ((iCt s₀).setWidth 64) (16 * (iKL s₀ / 8 + 6 + 1)) := by
    rw [m₇, Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.base_disjoint _ (by omega) (by omega)
        · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_c.sub_right (Region.sub_prefix (by omega))).symm) (by omega),
      Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.base_disjoint _ (by omega) (by omega)
        · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_c.sub_right (Region.sub_prefix (by omega))).symm) (by omega)]
  refine Proof.AesSiv.keyRepr_of kl (by rw [hR, sch₁, o₂]) ?_ ?_
  · -- The subkeys, kept by the last call.
    have e : Spec.Aes.bytesAt s₇.mem ((iCt s₀).setWidth 64 + BitVec.ofNat 64 240) 32 =
        Spec.Aes.bytesAt s₄.mem ((iCt s₀).setWidth 64 + BitVec.ofNat 64 240) 32 := by
      rw [m₇]
      exact Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact (hp.c_s.sub_left (Offset.sub_base _ (by decide))).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_c.sub_right (Offset.sub_base _ (by decide))).symm) (by decide)
    have o₄ := h₄.out
    rw [aC 240 (by decide), m₃, o₂] at o₄
    rw [e, o₄]
  · have o₆ := h₆.out
    rw [aC 272 (by decide), aK, hkey₅, hR] at o₆
    rw [hR, m₇, o₆]

/-! ## Constant time -/

theorem ek_after₁ {s₀ s : State} (hp : IPre s₀) (h : IMid₁ s₀ s) :
    WP isa (call4 v.expand.name v.expand.code) s (IAft s₀) :=
  WP.mono ((ek_call v) h.args) fun _ h' => h.after hp h'

theorem sub_after {s₀ s : State} (hp : IPre s₀) (h : IMid₂ s₀ s) :
    WP isa (call4 ("vg_cmac_aes_subkeys" ++ v.suffix) (Impl.CmacAes.X86.subkeys v.callee)) s (IAft s₀) :=
  WP.mono ((sub_call v) h.args) fun _ h' => h.after hp h'

theorem ek_after₂ {s₀ s : State} (hp : IPre s₀) (h : IMid₃ s₀ s) :
    WP isa (call4 v.expand.name v.expand.code) s (IAft s₀) :=
  WP.mono ((ek_call v) h.args) fun _ h' => h.after hp h'

theorem init_rel {s₀ s₀' : State} (h0 : initX86.pre s₀) (h0' : initX86.pre s₀') (hq : initX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (initCore v.expand v.callee v.suffix) fun _ _ => True := by
  have hp := IPre.of h0
  have hp' := IPre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have e0 : iKp s₀ = iKp s₀' := qa 0 (by decide)
  have e1 : iKL s₀ = iKL s₀' := by rw [iKL, iKL, qa 1 (by decide)]
  have e2 : iCt s₀ = iCt s₀' := qa 2 (by decide)
  have e3 : iSc s₀ = iSc s₀' := qa 3 (by decide)
  have ag : ∀ {a b : State}, Pt 4 s₀ a → Pt 4 s₀' b → VG.X86.Taint.Agree (argTaint [] (4 + 4 * 4)) a b :=
    fun h₁ h₂ => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ fun r hr => by simp at hr
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 4))
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _))
    (c := .block initPre) (by taint_decide)).wp (F₁ := IMid₁ s₀) (F₂ := IMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨initPre_wp hp, initPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have e := ((ek_rel v (E := iE s₀) (P := fun a b => IMid₁ s₀ a ∧ IMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e1, e2, e3]; exact h.2.args, h.1.esp, by rw [h.2.esp]; exact qE.symm⟩).wp
      (F₁ := IAft s₀) (F₂ := IAft s₀') fun _ _ h => ⟨(ek_after₁ v) hp h.1, (ek_after₁ v) hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have m := ((RelCT.taint (A := taint) (P := fun a b => IAft s₀ a ∧ IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block initMid₁) (by taint_decide)).wp
    (F₁ := fun s => IMid₂ s₀ s) (F₂ := fun s => IMid₂ s₀' s)
    fun _ _ h => ⟨WP.mono (initMid₁_wp hp h.1) fun _ h => h.1, WP.mono (initMid₁_wp hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have sk := ((sub_rel v (E := iE s₀) (P := fun a b => IMid₂ s₀ a ∧ IMid₂ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e1, e2, e3]; exact h.2.args, h.1.aft.esp, by rw [h.2.aft.esp]; exact qE.symm⟩).wp
      (F₁ := IAft s₀) (F₂ := IAft s₀') fun _ _ h => ⟨(sub_after v) hp h.1, (sub_after v) hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have m₂ := ((RelCT.taint (A := taint) (P := fun a b => IAft s₀ a ∧ IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block initMid₂) (by taint_decide)).wp
    (F₁ := fun s => IMid₃ s₀ s) (F₂ := fun s => IMid₃ s₀' s)
    fun _ _ h => ⟨WP.mono (initMid₂_wp hp h.1) fun _ h => h.1, WP.mono (initMid₂_wp hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have e' := ((ek_rel v (E := iE s₀) (P := fun a b => IMid₃ s₀ a ∧ IMid₃ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e1, e2, e3]; exact h.2.args, h.1.aft.esp, by rw [h.2.aft.esp]; exact qE.symm⟩).wp
      (F₁ := IAft s₀) (F₂ := IAft s₀') fun _ _ h => ⟨(ek_after₂ v) hp h.1, (ek_after₂ v) hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have p := RelCT.taint (A := taint) (P := fun a b => IAft s₀ a ∧ IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block (restore 3)) (by taint_decide)
  rw [initCore_eq]
  exact a.seq (e.seq (m.seq (sk.seq (m₂.seq (e'.seq p)))))

theorem init_ct : ConstantTime isa initX86.pre initX86.pub (initCore v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => ((init_rel v) h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesSiv.X86
