import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.ExpandMask
import VerifiedGarbage.Proof.Sha3.X86_64.X4.Bytes
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.ExpandMask4
import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.MlKem.X86_64.NttAvx2

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Base`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4`, the layout

Untrusted: everything here is checked by Lean. The contract the proofs are
written against (`em4K`), what holds between the pieces of the functions
(`Env`, relative to the entry state `σ`), and the prologue, as for
`vg_mlkem_sample_ntt4` (`Proof/MlKem/X86_64/S4Base.lean`).
-/

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Proof.MlKem.X86_64 (Keep WP.keep retR)
open VG.Proof.MlDsa.X86_64.Sample (gOf)
open VG.Spec.MlDsa (H PolyIs toRq bitUnpack bitlen seed66)
open VG.Spec.Sha3 (bytesAt)

/-- The output polynomial `k` of four at `a`. -/
abbrev poly4 (a : Addr) (k : Nat) : Addr := a + BitVec.ofNat 64 (1024 * k)

/-- `vg_mldsa_expand_mask_poly4(seeds = rdi, gamma1 = esi, a = rdx, scratch = rcx)`,
with 24 bytes of stack below `rsp`. -/
def em4K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 264⟩] ∧ s.wr = [⟨s.gpr .rdx, 4096⟩, ⟨s.gpr .rcx, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 264⟩ ⟨s.gpr .rdx, 4096⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 264⟩ ⟨s.gpr .rcx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 4096⟩ ⟨s.gpr .rcx, 8192⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 264⟩ ∧ (retR s).Disjoint ⟨s.gpr .rdx, 4096⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdi, 264⟩ ∧ (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdx, 4096⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (s.gpr .rdx).toNat + 4096 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64 ∧
    (gOf s = 2 ^ 17 ∨ gOf s = 2 ^ 19)
  post s s' := ∀ k < 4, PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Mask4.poly4 (s.gpr .rdx) k)
    (toRq (bitUnpack (H (seed66 s.mem (s.gpr .rdi) k) (32 * (1 + bitlen (gOf s - 1)))) (gOf s - 1) (gOf s)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32 ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

section
variable (σ : State)
abbrev sd : Addr := σ.gpr .rdi
abbrev aP : Addr := σ.gpr .rdx
abbrev scr : Addr := σ.gpr .rcx
/-- Seed `k`. -/
abbrev B (k : Nat) : List Byte := seed66 σ.mem (VG.Proof.MlDsa.X86_64.Mask4.sd σ) k
abbrev sdR : Region := ⟨VG.Proof.MlDsa.X86_64.Mask4.sd σ, 264⟩
abbrev aR : Region := ⟨VG.Proof.MlDsa.X86_64.Mask4.aP σ, 4096⟩
abbrev scrR : Region := ⟨VG.Proof.MlDsa.X86_64.Mask4.scr σ, 8192⟩
abbrev stkR : Region := below (σ.gpr .rsp) 24
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := VG.Proof.MlDsa.X86_64.Mask4.scr σ + BitVec.ofNat 64 off
end

/-- The precondition, by name. -/
structure Pre (σ : State) : Prop where
  rd : σ.rd = [VG.Proof.MlDsa.X86_64.Mask4.sdR σ]
  wr : σ.wr = [VG.Proof.MlDsa.X86_64.Mask4.aR σ, VG.Proof.MlDsa.X86_64.Mask4.scrR σ]
  sd_a : (VG.Proof.MlDsa.X86_64.Mask4.sdR σ).Disjoint (VG.Proof.MlDsa.X86_64.Mask4.aR σ)
  sd_scr : (VG.Proof.MlDsa.X86_64.Mask4.sdR σ).Disjoint (VG.Proof.MlDsa.X86_64.Mask4.scrR σ)
  a_scr : (VG.Proof.MlDsa.X86_64.Mask4.aR σ).Disjoint (VG.Proof.MlDsa.X86_64.Mask4.scrR σ)
  ret_sd : (retR σ).Disjoint (VG.Proof.MlDsa.X86_64.Mask4.sdR σ)
  ret_a : (retR σ).Disjoint (VG.Proof.MlDsa.X86_64.Mask4.aR σ)
  ret_scr : (retR σ).Disjoint (VG.Proof.MlDsa.X86_64.Mask4.scrR σ)
  stk_sd : (VG.Proof.MlDsa.X86_64.Mask4.stkR σ).Disjoint (VG.Proof.MlDsa.X86_64.Mask4.sdR σ)
  stk_a : (VG.Proof.MlDsa.X86_64.Mask4.stkR σ).Disjoint (VG.Proof.MlDsa.X86_64.Mask4.aR σ)
  stk_scr : (VG.Proof.MlDsa.X86_64.Mask4.stkR σ).Disjoint (VG.Proof.MlDsa.X86_64.Mask4.scrR σ)
  a_lt : (VG.Proof.MlDsa.X86_64.Mask4.aP σ).toNat + 4096 ≤ 2 ^ 64
  scr_lt : (VG.Proof.MlDsa.X86_64.Mask4.scr σ).toNat + 8192 ≤ 2 ^ 64
  gamma : gOf σ = 2 ^ 17 ∨ gOf σ = 2 ^ 19

theorem pre_of {σ : State} (h : em4K.pre σ) : VG.Proof.MlDsa.X86_64.Mask4.Pre σ :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- What holds between the pieces. -/
structure Env (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rbx : s.gpr .rbx = VG.Proof.MlDsa.X86_64.Mask4.scr σ
  r12 : s.gpr .r12 = VG.Proof.MlDsa.X86_64.Mask4.sd σ
  r13 : s.gpr .r13 = VG.Proof.MlDsa.X86_64.Mask4.aP σ
  r14 : s.gpr .r14 = σ.gpr .rsi
  rsp : s.gpr .rsp = σ.gpr .rsp
  r15 : s.gpr .r15 = σ.gpr .r15
  saved : ∀ i < 5, s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oSave + 8 * i)) 64 = σ.gpr (saved.getD i .rbx)
  frame : Frame [VG.Proof.MlDsa.X86_64.Mask4.aR σ, VG.Proof.MlDsa.X86_64.Mask4.scrR σ, VG.Proof.MlDsa.X86_64.Mask4.stkR σ] σ.mem s.mem

section
variable {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ)
include hp

omit hp in
theorem sub_scr {a n : Nat} (h : a + n ≤ 8192) : Region.Sub ⟨VG.Proof.MlDsa.X86_64.Mask4.at' σ a, n⟩ (VG.Proof.MlDsa.X86_64.Mask4.scrR σ) := Offset.sub_base _ h

omit hp in
theorem sub_poly {k : Nat} (hk : k < 4) : Region.Sub ⟨VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) k, 1024⟩ (VG.Proof.MlDsa.X86_64.Mask4.aR σ) :=
  Offset.sub_base _ (by omega)

theorem in_scr {s : State} (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 8192) : InRegions s.wr (VG.Proof.MlDsa.X86_64.Mask4.at' σ a) n := by
  rw [hw, hp.wr]; exact ⟨VG.Proof.MlDsa.X86_64.Mask4.scrR σ, by simp, Offset.contains_base _ h (by omega)⟩

theorem in_scr' {s : State} (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Mask4.at' σ a) n := by
  rw [hr, hw, hp.rd, hp.wr]; exact ⟨VG.Proof.MlDsa.X86_64.Mask4.scrR σ, by simp, Offset.contains_base _ h (by omega)⟩

theorem in_sd' {s : State} (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 264) :
    InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 a) n := by
  rw [hr, hw, hp.rd, hp.wr]; exact ⟨VG.Proof.MlDsa.X86_64.Mask4.sdR σ, by simp, Offset.contains_base _ h (by omega)⟩

/-- The seeds are not written. -/
theorem seeds_frame {m : Mem} (hf : Frame [VG.Proof.MlDsa.X86_64.Mask4.aR σ, VG.Proof.MlDsa.X86_64.Mask4.scrR σ, VG.Proof.MlDsa.X86_64.Mask4.stkR σ] σ.mem m) {a : Nat} (ha : a < 264) :
    m (VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 a) = σ.mem (VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 a) :=
  hf.bytes (R := VG.Proof.MlDsa.X86_64.Mask4.sdR σ) (by simpa using ⟨hp.sd_a, hp.sd_scr, hp.stk_sd.symm⟩) (by simp) ha

/-- Byte `a` of seed `k`. -/
theorem seed_byte {m : Mem} (hf : Frame [VG.Proof.MlDsa.X86_64.Mask4.aR σ, VG.Proof.MlDsa.X86_64.Mask4.scrR σ, VG.Proof.MlDsa.X86_64.Mask4.stkR σ] σ.mem m) {k a : Nat} (hk : k < 4) (ha : a < 66) :
    m (VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 (66 * k + a)) = (VG.Proof.MlDsa.X86_64.Mask4.B σ k).getD a 0 := by
  rw [VG.Proof.MlDsa.X86_64.Mask4.seeds_frame hp hf (by omega), VG.Proof.MlDsa.X86_64.Mask4.B, seed66, ← Offset.add_add]
  simp [bytesAt, ha]

end

/-! ## The prologue -/

/-- A read of 8 bytes at `scratch + d` after a write of 8 elsewhere. -/
theorem rd64_off {σ : State} {m : Mem} {d e : Nat} {v : BitVec 64} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) : (m.writeW (VG.Proof.MlDsa.X86_64.Mask4.at' σ e) v).readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ d) 64 = m.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ d) 64 :=
  readW_writeW_off m _ v (n := 8) (by omega) (by omega) h

theorem pro_eq : pro = [.store (VG.Impl.MlKem.X86_64.at_ .rcx 5088) .rbx, .store (VG.Impl.MlKem.X86_64.at_ .rcx 5096) .rbp,
    .store (VG.Impl.MlKem.X86_64.at_ .rcx 5104) .r12, .store (VG.Impl.MlKem.X86_64.at_ .rcx 5112) .r13,
    .store (VG.Impl.MlKem.X86_64.at_ .rcx 5120) .r14, .mov .rbx (.reg .rcx), .mov .r12 (.reg .rdi),
    .mov .r13 (.reg .rdx), .mov .r14 (.reg .rsi)] := rfl

theorem pro_ok {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) : WP isa (.block pro) σ (VG.Proof.MlDsa.X86_64.Mask4.Env σ) := by
  rw [VG.Proof.MlDsa.X86_64.Mask4.pro_eq]
  refine WP.mono (WP.keep [.rbx, .r12, .r13, .r14] (Q := fun s =>
      s.mem = ((((σ.mem.writeW (VG.Proof.MlDsa.X86_64.Mask4.at' σ 5088) (σ.gpr .rbx)).writeW (VG.Proof.MlDsa.X86_64.Mask4.at' σ 5096) (σ.gpr .rbp)).writeW (VG.Proof.MlDsa.X86_64.Mask4.at' σ 5104)
          (σ.gpr .r12)).writeW (VG.Proof.MlDsa.X86_64.Mask4.at' σ 5112) (σ.gpr .r13)).writeW (VG.Proof.MlDsa.X86_64.Mask4.at' σ 5120) (σ.gpr .r14) ∧
        s.gpr .rbx = VG.Proof.MlDsa.X86_64.Mask4.scr σ ∧ s.gpr .r12 = VG.Proof.MlDsa.X86_64.Mask4.sd σ ∧ s.gpr .r13 = VG.Proof.MlDsa.X86_64.Mask4.aP σ ∧ s.gpr .r14 = σ.gpr .rsi)
    (by xrun [VG.Proof.MlDsa.X86_64.Mask4.in_scr hp rfl (a := 5088) (n := 8) (by omega), VG.Proof.MlDsa.X86_64.Mask4.in_scr hp rfl (a := 5096) (n := 8) (by omega),
      VG.Proof.MlDsa.X86_64.Mask4.in_scr hp rfl (a := 5104) (n := 8) (by omega), VG.Proof.MlDsa.X86_64.Mask4.in_scr hp rfl (a := 5112) (n := 8) (by omega),
      VG.Proof.MlDsa.X86_64.Mask4.in_scr hp rfl (a := 5120) (n := 8) (by omega)])
    (by decide)) fun s1 ⟨⟨hm1, hbx, h12, h13, h14⟩, k1⟩ => ⟨k1.2.1, k1.2.2, hbx, h12, h13, h14,
      k1.gpr (by decide), k1.gpr (by decide), fun i hi => ?_, ?_⟩
  · rw [hm1]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := omega) only [oSave, Mem.readW_writeW_self64, VG.Proof.MlDsa.X86_64.Mask4.rd64_off, Nat.reduceMul, Nat.reduceAdd] <;> rfl
  · rw [hm1]
    have hin : ∀ a, a + 8 ≤ 8192 → (VG.Proof.MlDsa.X86_64.Mask4.scrR σ).Contains (VG.Proof.MlDsa.X86_64.Mask4.at' σ a) (64 / 8) := fun a ha =>
      Offset.contains_base _ (by omega) (by omega)
    exact ((((((Frame.refl _ _).writeW (by simp) _ (hin 5088 (by omega))).writeW (by simp) _
      (hin 5096 (by omega))).writeW (by simp) _ (hin 5104 (by omega))).writeW (by simp) _
      (hin 5112 (by omega))).writeW (by simp) _ (hin 5120 (by omega)))

end VG.Proof.MlDsa.X86_64.Mask4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Absorb`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4_avx2`, the round constants and the padded seeds

Untrusted: everything here is checked by Lean. After the prologue, the
table of the round constants (`rc_ok`), and the four states holding the
padded 66-byte seeds, byte by byte (`absorb_ok`), as for
`vg_mlkem_sample_ntt4_avx2` (`Proof/MlKem/X86_64/S4Absorb.lean`, whose
lemmas on the bytes of the states it uses).
-/

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Impl.MlKem.X86_64.Sample4 (zero4 oRc)
open VG.Proof.MlKem.X86_64
open VG.Proof.MlKem.X86_64.S4 (wb_in wb_out off4 bytes_write byte_setWidth)
open VG.Proof.Sha3.X86_64.X4 (q4 VUpd la ba Lanes4 wp_vmovq wp_vbcast wp_vst wp_vxor readW_write256 q4_ymm)
open VG.Proof.Sha3.X86_64 (wp_movi64)

/-- `Env` after writes below the saved registers. -/
theorem Env.write {σ s s' : State} (he : VG.Proof.MlDsa.X86_64.Mask4.Env σ s) {a n : Nat} (h : a + n ≤ oSave)
    (hf : Frame [⟨VG.Proof.MlDsa.X86_64.Mask4.at' σ a, n⟩] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp, .r15], s'.gpr r = s.gpr r) : VG.Proof.MlDsa.X86_64.Mask4.Env σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .r14 (by simp), he.r14], by rw [hg .rsp (by simp), he.rsp],
    by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using Offset.disjoint (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (d := oSave + 8 * i) (n := 8) (e := a) (k := n) (by simp only [oSave] at h ⊢; omega)
          (by simp only [oSave]; omega) (by simp only [oSave] at h; omega)) (by decide)]
    exact he.saved i hi
  · refine he.frame.trans (hf.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.MlDsa.X86_64.Mask4.scrR σ, by simp, Offset.sub_base _ (by simp only [oSave] at h; omega)⟩

/-! ## The round constants -/

/-- After the first `n` round constants. -/
structure RcInv (σ s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep [.rax] s₀ s
  frame : Frame [⟨VG.Proof.MlDsa.X86_64.Mask4.at' σ oRc, 768⟩] s₀.mem s.mem
  rc : ∀ r < n, ∀ k < 4, s.mem.readW (la (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (50 + r) k) 64 = Spec.Sha3.RC r

theorem rc_step {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {s₀ : State} (he : VG.Proof.MlDsa.X86_64.Mask4.Env σ s₀) {r : Nat} (hr : r < 24) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Mask4.RcInv σ s₀ r s) :
    WP isa (.block [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax),
      .vop (.vpbroadcastq .l256 .xmm0 .xmm0), Impl.Sha3.X86_64.X4.st .rbx (oRc / 32 + r) .xmm0]) s
      (VG.Proof.MlDsa.X86_64.Mask4.RcInv σ s₀ (r + 1)) := by
  have hbx : s.gpr .rbx = VG.Proof.MlDsa.X86_64.Mask4.scr σ := by rw [h.keep.gpr (by decide), he.rbx]
  refine wp_movi64 fun s₁ u₁ => wp_vmovq fun s₂ u₂ => wp_vbcast fun s₃ u₃ =>
    wp_vst (a := VG.Proof.MlDsa.X86_64.Mask4.at' σ (32 * (50 + r))) (by rw [VG.Proof.Sha3.X86_64.ea_at, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hbx]; rfl)
      (by rw [u₃.wr, u₂.wr, u₁.wr, h.keep.2.2, he.wr]; exact VG.Proof.MlDsa.X86_64.Mask4.in_scr hp rfl (by omega))
      fun s₄ g₄ _ m₄ r₄ w₄ => VG.Proof.Sha3.X86_64.wp_nil ?_
  have hv : ∀ k < 4, q4 s₃ .xmm0 k = Spec.Sha3.RC r := fun k hk => by
    rw [u₃.val k hk, u₂.val 0 (by decide), ite_eq_left rfl, u₁.gpr]
  have hm : s₄.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (32 * (50 + r))) (s₃.ymm .xmm0) := by rw [m₄, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨fun g hg => by rw [g₄, u₃.gpr, u₂.gpr, u₁.other g (by simpa using hg), h.keep.gpr hg],
      by rw [r₄, u₃.rd, u₂.rd, u₁.rd, h.keep.2.1], by rw [w₄, u₃.wr, u₂.wr, u₁.wr, h.keep.2.2]⟩, ?_,
    fun r' hr' k hk => ?_⟩
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by simp only [oRc]; omega)
      (by simp only [oRc]; omega) (by simp only [oRc]; omega))
  · rw [hm]
    by_cases e : r' = r
    · subst e
      rw [la, ← Offset.add_add, readW_write256 _ _ _ hk, q4_ymm _ _ hk, hv k hk]
    · have e := readW_writeW_off s.mem (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (s₃.ymm .xmm0) (d := 32 * (50 + r') + 8 * k)
        (e := 32 * (50 + r)) (n := 8) (by omega) (by omega) (by omega)
      exact e.trans (h.rc r' (by omega) k hk)

theorem rcTable_eq : Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) = (List.range 24).flatMap fun r =>
    [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax), .vop (.vpbroadcastq .l256 .xmm0 .xmm0),
      Impl.Sha3.X86_64.X4.st .rbx (oRc / 32 + r) .xmm0] := rfl

/-- The table of the round constants. -/
theorem rc_ok {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {s₀ : State} (he : VG.Proof.MlDsa.X86_64.Mask4.Env σ s₀) :
    WP isa (.block (Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32))) s₀ (VG.Proof.MlDsa.X86_64.Mask4.RcInv σ s₀ 24) := by
  rw [VG.Proof.MlDsa.X86_64.Mask4.rcTable_eq]
  exact wp_range_flatMap (M := isa) (VG.Proof.MlDsa.X86_64.Mask4.RcInv σ s₀) (fun r s hr h => VG.Proof.MlDsa.X86_64.Mask4.rc_step hp he hr h) 24 (Nat.le_refl _) s₀
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by omega)⟩


/-! ## The states, byte by byte -/

/-- The four states hold `F`. -/
def SB (σ : State) (m : Mem) (F : Nat → Nat → Byte) : Prop :=
  ∀ k < 4, ∀ q < 200, m (ba (VG.Proof.MlDsa.X86_64.Mask4.scr σ) k q) = F k q

/-- During the writes to the states, after the round constants (in `m₁`). -/
structure AI (σ : State) (m₁ : Mem) (s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Mask4.Env σ s
  frame : Frame [⟨VG.Proof.MlDsa.X86_64.Mask4.scr σ, 800⟩] m₁ s.mem

theorem AI.write {σ : State} {m₁ : Mem} {s s' : State} (h : VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s) {e n : Nat} (hn : e + n ≤ 800)
    (hm : ∃ v : BitVec (8 * n), s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Mask4.at' σ e) v) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r) : VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s' := by
  obtain ⟨v, hv⟩ := hm
  have hf : Frame [⟨VG.Proof.MlDsa.X86_64.Mask4.at' σ e, n⟩] s.mem s'.mem := by
    rw [hv]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
      rw [show 8 * n / 8 = n by omega]; exact Region.contains_self _ _)
  refine ⟨h.env.write (by simp only [oSave]; omega) hf hrd hwr fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    h.frame.trans (hf.sub fun r hr => ?_)⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ hn⟩

/-! ### Zeroing -/

/-- After zeroing the first `n` lanes of each state. -/
structure ZInv (σ : State) (m₁ : Mem) (n : Nat) (s : State) : Prop where
  ai : VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s
  x0 : ∀ k < 4, q4 s .xmm0 k = 0
  bytes : ∀ k < 4, ∀ q < 200, q / 8 < n → s.mem (ba (VG.Proof.MlDsa.X86_64.Mask4.scr σ) k q) = 0

theorem zero_step {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {m₁ : Mem} {i : Nat} (hi : i < 25) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.ZInv σ m₁ i s) :
    WP isa (.block [Impl.Sha3.X86_64.X4.st .rbx i .xmm0]) s (VG.Proof.MlDsa.X86_64.Mask4.ZInv σ m₁ (i + 1)) := by
  refine wp_vst (a := VG.Proof.MlDsa.X86_64.Mask4.at' σ (32 * i)) (by rw [VG.Proof.Sha3.X86_64.ea_at, h.ai.env.rbx])
    (by rw [h.ai.env.wr]; exact VG.Proof.MlDsa.X86_64.Mask4.in_scr hp rfl (by omega)) fun s' g' q' m' r' w' => VG.Proof.Sha3.X86_64.wp_nil ?_
  refine ⟨h.ai.write (e := 32 * i) (n := 32) (by omega) ⟨_, m'⟩ r' w' fun r _ => by rw [g'],
    fun k hk => by rw [q', h.x0 k hk], fun k hk q hq hn => ?_⟩
  rw [m']
  have hb := bytes_write (m := s.mem) (p := VG.Proof.MlDsa.X86_64.Mask4.scr σ) (F := fun k q => s.mem (ba (VG.Proof.MlDsa.X86_64.Mask4.scr σ) k q))
    (fun _ _ _ _ => rfl) (s.ymm .xmm0) (e := 32 * i) (by decide) (by omega) hk hq
  rw [hb]
  split
  · rename_i hc
    simp only [off4] at hc ⊢
    rw [show 8 * (32 * (q / 8) + 8 * k + q % 8 - 32 * i) = 64 * k + 8 * (q % 8) by omega, ← extract_extract (s.ymm .xmm0) (64 * k) 64 (8 * (q % 8)) 8 (by omega),
      q4_ymm _ _ hk, h.x0 k hk]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  · rename_i hc
    simp only [off4] at hc
    exact h.bytes k hk q hq (by omega)

theorem zero4_eq : zero4 = Impl.Sha3.X86_64.X4.vb .vpxor .xmm0 .xmm0 .xmm0 ::
    (List.range 25).flatMap fun i => [Impl.Sha3.X86_64.X4.st .rbx i .xmm0] := rfl

theorem zero_ok {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {m₁ : Mem} {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s) :
    WP isa (.block zero4) s (fun s' => VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s' ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s'.mem fun _ _ => 0) := by
  rw [VG.Proof.MlDsa.X86_64.Mask4.zero4_eq]
  refine wp_vxor fun s₁ u₁ => WP.mono (wp_range_flatMap (M := isa) (VG.Proof.MlDsa.X86_64.Mask4.ZInv σ m₁) (fun i s hi h => VG.Proof.MlDsa.X86_64.Mask4.zero_step hp hi h)
    25 (Nat.le_refl _) s₁ ⟨h.write (e := 0) (n := 0) (by omega) ⟨0, ?_⟩ u₁.rd u₁.wr fun r _ => by rw [u₁.gpr],
      fun k hk => by rw [u₁.val k hk, BitVec.xor_self]; rfl, fun _ _ _ _ h => absurd h (by omega)⟩)
    fun s' h' => ⟨h'.ai, fun k hk q hq => h'.bytes k hk q hq (by omega)⟩
  rw [u₁.mem]
  funext x
  simp [Mem.writeW, Mem.write]


/-! ### The seeds -/

/-- Byte `q` of seed `k` (0 past its end). -/
abbrev Bq (σ : State) (k q : Nat) : Byte := (VG.Proof.MlDsa.X86_64.Mask4.B σ k).getD q 0

/-- The states after the first `K` seeds, and the first `i` lanes of seed `K`. -/
def HF (σ : State) (K i : Nat) (k q : Nat) : Byte :=
  if (k < K ∧ q < 66) ∨ (k = K ∧ q < 8 * i) then VG.Proof.MlDsa.X86_64.Mask4.Bq σ k q else 0

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_movzx8 wp_store8 wp_mov32i wp_nil) in
theorem lane_step {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {m₁ : Mem} {K i : Nat} (hK : K < 4) (hi : i < 8) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s.mem (VG.Proof.MlDsa.X86_64.Mask4.HF σ K i)) :
    WP isa (.block [.mov .rax (.mem (at_ .r12 (66 * K + 8 * i))), .store (at_ .rbx (32 * i + 8 * K)) .rax]) s
      (fun s' => VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s' ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s'.mem (VG.Proof.MlDsa.X86_64.Mask4.HF σ K (i + 1))) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movm (a := VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 (66 * K + 8 * i)) (by rw [ea_at, ha.env.r12])
    (VG.Proof.MlDsa.X86_64.Mask4.in_sd' hp ha.env.rd ha.env.wr (by omega)) fun s₁ u₁ => wp_store (a := VG.Proof.MlDsa.X86_64.Mask4.at' σ (32 * i + 8 * K))
      (by rw [ea_at, u₁.other _ (by decide), ha.env.rbx]) (by rw [u₁.wr]; exact VG.Proof.MlDsa.X86_64.Mask4.in_scr hp ha.env.wr (by omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (32 * i + 8 * K)) (s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 (66 * K + 8 * i)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  refine ⟨ha.write (e := 32 * i + 8 * K) (n := 8) (by omega) ⟨_, hm⟩ (r₂.trans u₁.rd) (w₂.trans u₁.wr)
    fun r hr => by rw [g₂, u₁.other r hr], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by omega) hk hq]
  simp only [off4]
  by_cases hc : 32 * i + 8 * K ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 32 * i + 8 * K + 64 / 8
  · have hk' : k = K := by omega
    have hq' : q / 8 = i := by omega
    subst hk'
    rw [VG.Proof.MlKem.X86_64.ifp hc, VG.Proof.MlDsa.X86_64.Mask4.HF, VG.Proof.MlKem.X86_64.ifp (.inr ⟨rfl, by omega⟩),
      show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * i + 8 * k)) = 8 * (q % 8) by omega,
      byte_readW _ _ (by omega), Offset.add_add, show 66 * k + 8 * i + q % 8 = 66 * k + q by omega,
      VG.Proof.MlDsa.X86_64.Mask4.seed_byte hp ha.env.frame hK (by omega)]
  · rw [VG.Proof.MlKem.X86_64.ifn hc, VG.Proof.MlDsa.X86_64.Mask4.HF, VG.Proof.MlDsa.X86_64.Mask4.HF]
    by_cases hc' : (k < K ∧ q < 66) ∨ (k = K ∧ q < 8 * i)
    · rw [VG.Proof.MlKem.X86_64.ifp hc', VG.Proof.MlKem.X86_64.ifp (by omega)]
    · rw [VG.Proof.MlKem.X86_64.ifn hc', VG.Proof.MlKem.X86_64.ifn (by omega)]

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_movzx8 wp_store8 wp_mov32i wp_nil) in
/-- Byte `64 + j` of seed `K`. -/
theorem byte_step {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {m₁ : Mem} {K j : Nat} (hK : K < 4) (hj : j < 2) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s.mem fun k q => if (k < K ∧ q < 66) ∨ (k = K ∧ q < 64 + j) then VG.Proof.MlDsa.X86_64.Mask4.Bq σ k q else 0) :
    WP isa (.block [.movzx8 .rax (at_ .r12 (66 * K + (64 + j))), .store8 (at_ .rbx (256 + 8 * K + j)) .rax]) s
      (fun s' => VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s' ∧
        VG.Proof.MlDsa.X86_64.Mask4.SB σ s'.mem fun k q => if (k < K ∧ q < 66) ∨ (k = K ∧ q < 64 + (j + 1)) then VG.Proof.MlDsa.X86_64.Mask4.Bq σ k q else 0) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movzx8 (a := VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 (66 * K + (64 + j))) (by rw [ea_at, ha.env.r12])
    (VG.Proof.MlDsa.X86_64.Mask4.in_sd' hp ha.env.rd ha.env.wr (by omega)) fun s₁ u₁ => wp_store8 (a := VG.Proof.MlDsa.X86_64.Mask4.at' σ (256 + 8 * K + j))
      (by rw [ea_at, u₁.other _ (by decide), ha.env.rbx]) (by rw [u₁.wr]; exact VG.Proof.MlDsa.X86_64.Mask4.in_scr hp ha.env.wr (by omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (256 + 8 * K + j)) (s.mem (VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 (66 * K + (64 + j)))) := by
    rw [m₂, u₁.mem, u₁.gpr, byte_setWidth]
  refine ⟨ha.write (e := 256 + 8 * K + j) (n := 1) (by omega) ⟨_, hm⟩ (r₂.trans u₁.rd) (w₂.trans u₁.wr)
    fun r hr => by rw [g₂, u₁.other r hr], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by omega) hk hq]
  simp only [off4]
  by_cases hc : 256 + 8 * K + j ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 256 + 8 * K + j + 8 / 8
  · have hk' : k = K := by omega
    have hq' : q = 64 + j := by omega
    subst hk' hq'
    rw [VG.Proof.MlKem.X86_64.ifp hc, VG.Proof.MlKem.X86_64.ifp (.inr ⟨rfl, by omega⟩), show 8 * (32 * ((64 + j) / 8) + 8 * k + (64 + j) % 8 -
      (256 + 8 * k + j)) = 0 by omega, Proof.Sha3.extractLsb'_byte, VG.Proof.MlDsa.X86_64.Mask4.seed_byte hp ha.env.frame hK (by omega)]
  · rw [VG.Proof.MlKem.X86_64.ifn hc]
    by_cases hc' : (k < K ∧ q < 66) ∨ (k = K ∧ q < 64 + j)
    · rw [VG.Proof.MlKem.X86_64.ifp hc', VG.Proof.MlKem.X86_64.ifp (by omega)]
    · rw [VG.Proof.MlKem.X86_64.ifn hc', VG.Proof.MlKem.X86_64.ifn (by omega)]

theorem seedLanes_eq (K : Nat) : seedLanes K = (List.range 8).flatMap (fun i =>
    [.mov .rax (.mem (at_ .r12 (66 * K + 8 * i))), .store (at_ .rbx (32 * i + 8 * K)) .rax]) ++
    (([.movzx8 .rax (at_ .r12 (66 * K + (64 + 0))), .store8 (at_ .rbx (256 + 8 * K + 0)) .rax] : List Instr) ++
      ([.movzx8 .rax (at_ .r12 (66 * K + (64 + 1))), .store8 (at_ .rbx (256 + 8 * K + 1)) .rax] : List Instr)) := by
  simp only [seedLanes, Nat.add_zero]; rfl

/-- The states after the first `K` seeds. -/
def GF (σ : State) (K : Nat) (k q : Nat) : Byte := if k < K ∧ q < 66 then VG.Proof.MlDsa.X86_64.Mask4.Bq σ k q else 0

theorem seed_step {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {m₁ : Mem} {K : Nat} (hK : K < 4) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s.mem (VG.Proof.MlDsa.X86_64.Mask4.GF σ K)) :
    WP isa (.block (seedLanes K)) s (fun s' => VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s' ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s'.mem (VG.Proof.MlDsa.X86_64.Mask4.GF σ (K + 1))) := by
  rw [VG.Proof.MlDsa.X86_64.Mask4.seedLanes_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s => VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s.mem (VG.Proof.MlDsa.X86_64.Mask4.HF σ K i))
    (fun i s hi h => VG.Proof.MlDsa.X86_64.Mask4.lane_step hp hK hi h) 8 (Nat.le_refl _) s ⟨h.1, fun k hk q hq => ?_⟩) fun s₁ h₁ => ?_
  · rw [h.2 k hk q hq, VG.Proof.MlDsa.X86_64.Mask4.GF, VG.Proof.MlDsa.X86_64.Mask4.HF]
    by_cases hc : k < K ∧ q < 66
    · rw [VG.Proof.MlKem.X86_64.ifp hc, VG.Proof.MlKem.X86_64.ifp (.inl hc)]
    · rw [VG.Proof.MlKem.X86_64.ifn hc, VG.Proof.MlKem.X86_64.ifn (by omega)]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Mask4.byte_step hp (j := 0) hK (by decide) ⟨h₁.1, fun k hk q hq => ?_⟩) fun s₂ h₂ =>
    WP.mono (VG.Proof.MlDsa.X86_64.Mask4.byte_step hp (j := 1) hK (by decide) h₂) fun s₃ ⟨h₃, b₃⟩ => ⟨h₃, fun k hk q hq => ?_⟩
  · rw [h₁.2 k hk q hq, VG.Proof.MlDsa.X86_64.Mask4.HF]
  · rw [b₃ k hk q hq, VG.Proof.MlDsa.X86_64.Mask4.GF]
    dsimp only
    by_cases hc : (k < K ∧ q < 66) ∨ (k = K ∧ q < 64 + (1 + 1))
    · rw [VG.Proof.MlKem.X86_64.ifp hc]
      by_cases hc' : k < K + 1 ∧ q < 66
      · rw [VG.Proof.MlKem.X86_64.ifp hc']
      · rw [VG.Proof.MlKem.X86_64.ifn hc']; omega
    · rw [VG.Proof.MlKem.X86_64.ifn hc]
      by_cases hc' : k < K + 1 ∧ q < 66
      · omega
      · rw [VG.Proof.MlKem.X86_64.ifn hc']


/-! ### The padding -/

open VG.Proof.Sha3.X86_64 (wp_store8 wp_mov32i wp_nil) in
/-- The byte `c` (in `rax`) to byte `q₀` of state `K`. -/
theorem cbyte_step {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {m₁ : Mem} {F : Nat → Nat → Byte} {K q₀ : Nat} (hK : K < 4)
    (hq₀ : q₀ < 200) {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64) (h : VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s.mem F) :
    WP isa (.block [.store8 (at_ .rbx (32 * (q₀ / 8) + 8 * K + q₀ % 8)) .rax]) s
      (fun s' => VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s' ∧ s'.gpr .rax = s.gpr .rax ∧
        VG.Proof.MlDsa.X86_64.Mask4.SB σ s'.mem fun k q => if k = K ∧ q = q₀ then c else F k q) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_store8 (a := VG.Proof.MlDsa.X86_64.Mask4.at' σ (32 * (q₀ / 8) + 8 * K + q₀ % 8)) (by rw [ea_at, ha.env.rbx])
    (by exact VG.Proof.MlDsa.X86_64.Mask4.in_scr hp ha.env.wr (by omega)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (32 * (q₀ / 8) + 8 * K + q₀ % 8)) c := by
    rw [m₂, hax, byte_setWidth]
  refine ⟨ha.write (n := 1) (by omega) ⟨_, hm⟩ r₂ w₂ fun r _ => by rw [g₂], by rw [g₂], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by omega) hk hq]
  simp only [off4]
  by_cases hc : 32 * (q₀ / 8) + 8 * K + q₀ % 8 ≤ 32 * (q / 8) + 8 * k + q % 8 ∧
      32 * (q / 8) + 8 * k + q % 8 < 32 * (q₀ / 8) + 8 * K + q₀ % 8 + 8 / 8
  · have e : k = K ∧ q = q₀ := by omega
    rw [VG.Proof.MlKem.X86_64.ifp hc, VG.Proof.MlKem.X86_64.ifp e, show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * (q₀ / 8) + 8 * K + q₀ % 8)) = 0 by omega,
      Proof.Sha3.extractLsb'_byte]
  · rw [VG.Proof.MlKem.X86_64.ifn hc, VG.Proof.MlKem.X86_64.ifn (by omega)]

/-- The four states hold their padded seeds. -/
def PF (σ : State) (k q : Nat) : Byte :=
  if q < 66 then VG.Proof.MlDsa.X86_64.Mask4.Bq σ k q else if q = 66 then 0x1f else if q = 135 then 0x80 else 0

theorem sfx_eq : (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (256 + 8 * k + 2)) .rax]) =
    (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (32 * (66 / 8) + 8 * k + 66 % 8)) .rax]) := rfl

theorem last_eq : (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (512 + 8 * k + 7)) .rax]) =
    (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (32 * (135 / 8) + 8 * k + 135 % 8)) .rax]) := rfl

/-- The byte `c` to byte `q₀` of each state. -/
theorem cbytes_ok {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {m₁ : Mem} {F : Nat → Nat → Byte} {q₀ : Nat} (hq₀ : q₀ < 200)
    {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64) (h : VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s.mem F) :
    WP isa (.block ((List.range 4).flatMap fun k => [.store8 (at_ .rbx (32 * (q₀ / 8) + 8 * k + q₀ % 8)) .rax])) s
      (fun s' => VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s' ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s'.mem fun k q => if q = q₀ then c else F k q) := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s' => VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s' ∧ s'.gpr .rax = c.setWidth 64 ∧
      VG.Proof.MlDsa.X86_64.Mask4.SB σ s'.mem fun k q => if k < K ∧ q = q₀ then c else F k q)
    (fun K s' hK ⟨ha, hx, hb⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Mask4.cbyte_step hp hK hq₀ hx ⟨ha, hb⟩) fun s'' ⟨ha', hx', hb'⟩ =>
      ⟨ha', hx'.trans hx, fun k hk q hq => ?_⟩) 4 (Nat.le_refl _) s ⟨h.1, hax, fun k hk q hq => ?_⟩)
    fun s' ⟨ha, _, hb⟩ => ⟨ha, fun k hk q hq => ?_⟩
  · rw [hb' k hk q hq]
    dsimp only
    by_cases e : k = K ∧ q = q₀
    · rw [VG.Proof.MlKem.X86_64.ifp e, VG.Proof.MlKem.X86_64.ifp (by omega)]
    · rw [VG.Proof.MlKem.X86_64.ifn e]
      by_cases e' : k < K ∧ q = q₀
      · rw [VG.Proof.MlKem.X86_64.ifp e', VG.Proof.MlKem.X86_64.ifp (by omega)]
      · rw [VG.Proof.MlKem.X86_64.ifn e', VG.Proof.MlKem.X86_64.ifn (by omega)]
  · rw [h.2 k hk q hq]; dsimp only; rw [VG.Proof.MlKem.X86_64.ifn (by omega)]
  · rw [hb k hk q hq]
    dsimp only
    by_cases e : q = q₀
    · rw [VG.Proof.MlKem.X86_64.ifp e, VG.Proof.MlKem.X86_64.ifp ⟨hk, e⟩]
    · rw [VG.Proof.MlKem.X86_64.ifn e, VG.Proof.MlKem.X86_64.ifn (by omega)]

theorem absorb4_eq : absorb4 = zero4 ++ ((List.range 4).flatMap seedLanes ++
    (([.mov32 .rax (.imm 0x1f)] : List Instr) ++ ((List.range 4).flatMap (fun k =>
      [Instr.store8 (at_ .rbx (32 * (66 / 8) + 8 * k + 66 % 8)) .rax]) ++
    (([.mov32 .rax (.imm 0x80)] : List Instr) ++ (List.range 4).flatMap (fun k =>
      [Instr.store8 (at_ .rbx (32 * (135 / 8) + 8 * k + 135 % 8)) .rax]))))) := by
  simp only [absorb4, List.append_assoc, List.cons_append, List.nil_append]

open VG.Proof.Sha3.X86_64 (wp_mov32i) in
/-- The padded seeds in the four states. -/
theorem absorb_ok {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {m₁ : Mem} {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s) :
    WP isa (.block absorb4) s (fun s' => VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s' ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s'.mem (VG.Proof.MlDsa.X86_64.Mask4.PF σ)) := by
  rw [VG.Proof.MlDsa.X86_64.Mask4.absorb4_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Mask4.zero_ok hp h) fun s₁ ⟨h₁, z₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s.mem (VG.Proof.MlDsa.X86_64.Mask4.GF σ K))
    (fun K s hK h => VG.Proof.MlDsa.X86_64.Mask4.seed_step hp hK h) 4 (Nat.le_refl _) s₁ ⟨h₁, fun k hk q hq => ?_⟩) fun s₂ h₂ => ?_
  · rw [z₁ k hk q hq, VG.Proof.MlDsa.X86_64.Mask4.GF, VG.Proof.MlKem.X86_64.ifn (by omega)]
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₃ u₃ => VG.Proof.Sha3.X86_64.wp_nil
    (Q := fun s₃ => VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s₃ ∧ s₃.gpr .rax = (0x1f : Byte).setWidth 64 ∧ VG.Proof.MlDsa.X86_64.Mask4.SB σ s₃.mem (VG.Proof.MlDsa.X86_64.Mask4.GF σ 4))
    ⟨h₂.1.write (e := 0) (n := 0) (by omega) ⟨0, ?_⟩ u₃.rd u₃.wr fun r hr => u₃.other r hr, by rw [u₃.gpr]; rfl,
      by rw [u₃.mem]; exact h₂.2⟩) fun s₃ ⟨a₃, x₃, b₃⟩ => ?_
  · rw [u₃.mem]; funext x; simp [Mem.writeW, Mem.write]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Mask4.cbytes_ok hp (by decide) x₃ ⟨a₃, b₃⟩) fun s₄ ⟨a₄, b₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₅ u₅ => VG.Proof.Sha3.X86_64.wp_nil
    (Q := fun s₅ => VG.Proof.MlDsa.X86_64.Mask4.AI σ m₁ s₅ ∧ s₅.gpr .rax = (0x80 : Byte).setWidth 64 ∧
      VG.Proof.MlDsa.X86_64.Mask4.SB σ s₅.mem fun k q => if q = 66 then 0x1f else VG.Proof.MlDsa.X86_64.Mask4.GF σ 4 k q)
    ⟨a₄.write (e := 0) (n := 0) (by omega) ⟨0, ?_⟩ u₅.rd u₅.wr fun r hr => u₅.other r hr, by rw [u₅.gpr]; rfl,
      by rw [u₅.mem]; exact b₄⟩) fun s₅ ⟨a₅, x₅, b₅⟩ => ?_
  · rw [u₅.mem]; funext x; simp [Mem.writeW, Mem.write]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Mask4.cbytes_ok hp (by decide) x₅ ⟨a₅, b₅⟩) fun s₆ ⟨a₆, b₆⟩ => ⟨a₆, fun k hk q hq => ?_⟩
  rw [b₆ k hk q hq, VG.Proof.MlDsa.X86_64.Mask4.PF]
  dsimp only
  rw [VG.Proof.MlDsa.X86_64.Mask4.GF]
  by_cases e1 : q < 66
  · rw [VG.Proof.MlKem.X86_64.ifn (show ¬ q = 135 by omega), VG.Proof.MlKem.X86_64.ifn (show ¬ q = 66 by omega), VG.Proof.MlKem.X86_64.ifp (show k < 4 ∧ q < 66 from ⟨hk, e1⟩),
      VG.Proof.MlKem.X86_64.ifp e1]
  · rw [VG.Proof.MlKem.X86_64.ifn e1, VG.Proof.MlKem.X86_64.ifn (show ¬ (k < 4 ∧ q < 66) by omega)]
    by_cases e2 : q = 66
    · rw [VG.Proof.MlKem.X86_64.ifn (show ¬ q = 135 by omega), VG.Proof.MlKem.X86_64.ifp e2, VG.Proof.MlKem.X86_64.ifp e2]
    · rw [VG.Proof.MlKem.X86_64.ifn e2, VG.Proof.MlKem.X86_64.ifn e2]

end VG.Proof.MlDsa.X86_64.Mask4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Squeeze`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4_avx2`, squeezing

Untrusted: everything here is checked by Lean. The padded seeds are the
states that `Keccak-f` turns into the absorbed ones (`padded_A0`), and the
four states hold them after `absorb4` (`lanes_A0`). Each `squeeze4 n`
permutes the four states (`permute4_ok`) and copies the first 136 bytes of
each to its output, which then holds the first `136 (n + 1)` bytes of
SHAKE256 of the seed (`hByte`, `sq_ok`), as for `vg_mlkem_sample_ntt4_avx2`
(`Proof/MlKem/X86_64/S4Squeeze.lean`).
-/

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Impl.MlKem.X86_64.Sample4 (permArgs oBuf)
open VG.Proof.MlKem.X86_64
open VG.Proof.MlKem.X86_64.S4 (wb_in wb_out sx800 sx1600 sx2368)
open VG.Spec.Sha3 (keccakF RC)
open VG.Proof.Sha3 (byteOf Rep xorByte byteOf_xorByte byteOf_xorBytes absorb_pad iterF iterF_succ iterF_keccakF)
open VG.Proof.MlKem (padded shake256_eq)
open VG.Proof.Sha3 (squeeze_getElem length_squeeze)
open VG.Proof.Sha3.X86_64.X4 (la ba Lanes4 lanes4_of_bytes byte_of_lanes4 Pre4 permute4_ok)

/-! ## The padded seeds -/

/-- The state whose permutation is the absorbed padded seed. -/
def A0 (Bs : List Byte) : Spec.Sha3.State := xorByte (xorByte (Rep 136 Bs) 66 0x1f) 135 0x80

theorem padded_A0 {Bs : List Byte} (h : Bs.length = 66) :
    padded 136 Spec.Sha3.shakeSuffix Bs = keccakF (VG.Proof.MlDsa.X86_64.Mask4.A0 Bs) := by
  rw [padded, absorb_pad (by decide) (by decide), h]; rfl

theorem byteOf_A0 {Bs : List Byte} (h : Bs.length = 66) {q : Nat} (hq : q < 200) :
    byteOf (VG.Proof.MlDsa.X86_64.Mask4.A0 Bs) q = if q < 66 then Bs.getD q 0 else if q = 66 then 0x1f else if q = 135 then 0x80 else 0 := by
  have hz : byteOf Spec.Sha3.zero q = 0 := by
    simp only [byteOf, Spec.Sha3.zero, getElem!_pos (Vector.replicate 25 (0 : BitVec 64)) (q / 8) (by omega),
      Vector.getElem_replicate]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  have ha : Spec.Sha3.absorb 136 Bs = Spec.Sha3.zero := by simp [Spec.Sha3.absorb, h]
  have hr : byteOf (Rep 136 Bs) q = Bs.getD q 0 := by
    rw [Rep, ha, byteOf_xorBytes _ _ hq, hz, h, show 136 * (66 / 136) = 0 from rfl, List.drop_zero]
    exact BitVec.zero_xor
  have hd : ∀ q, 66 ≤ q → Bs.getD q 0 = 0 := fun q hq' => by
    rw [List.getD, List.getElem?_eq_none (by omega)]; rfl
  rw [VG.Proof.MlDsa.X86_64.Mask4.A0, byteOf_xorByte _ _ _ hq, byteOf_xorByte _ _ _ hq, hr]
  by_cases e1 : q < 66
  · rw [VG.Proof.MlKem.X86_64.ifn (show ¬ q = 135 by omega), VG.Proof.MlKem.X86_64.ifn (show ¬ q = 66 by omega), VG.Proof.MlKem.X86_64.ifp e1]
  · rw [VG.Proof.MlKem.X86_64.ifn e1, hd q (by omega)]
    by_cases e2 : q = 66
    · rw [VG.Proof.MlKem.X86_64.ifn (show ¬ q = 135 by omega), VG.Proof.MlKem.X86_64.ifp e2, VG.Proof.MlKem.X86_64.ifp e2]; exact BitVec.zero_xor
    · rw [VG.Proof.MlKem.X86_64.ifn e2, VG.Proof.MlKem.X86_64.ifn e2]
      by_cases e3 : q = 135
      · rw [VG.Proof.MlKem.X86_64.ifp e3, VG.Proof.MlKem.X86_64.ifp e3]; exact BitVec.zero_xor
      · rw [VG.Proof.MlKem.X86_64.ifn e3, VG.Proof.MlKem.X86_64.ifn e3]

theorem B_length (σ : State) (k : Nat) : (VG.Proof.MlDsa.X86_64.Mask4.B σ k).length = 66 := VG.Proof.Sha3.bytesAt_length _ _ _

/-- Byte `p` of SHAKE256 of `B`: byte `p mod 136` of the padded state after
`⌊p / 136⌋` more permutations. -/
def hByte (B : List Byte) (p : Nat) : Byte :=
  byteOf (iterF (p / 136) (padded 136 Spec.Sha3.shakeSuffix B)) (p % 136)

theorem H_getD (B : List Byte) {ℓ p : Nat} (hp : p < ℓ) : (Spec.MlDsa.H B ℓ).getD p 0 = VG.Proof.MlDsa.X86_64.Mask4.hByte B p := by
  have hl : (Spec.MlDsa.H B ℓ).length = ℓ := length_squeeze (by decide) (by decide) _ _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; exact hp), Option.getD_some]
  exact squeeze_getElem (by decide) (by decide) _ hp

/-- Byte `p` of SHAKE256 of `Bs`, from the states. -/
theorem hByte_A0 {Bs : List Byte} (h : Bs.length = 66) {n p : Nat} (hp : p < 136) :
    VG.Proof.MlDsa.X86_64.Mask4.hByte Bs (136 * n + p) = byteOf (iterF (n + 1) (VG.Proof.MlDsa.X86_64.Mask4.A0 Bs)) p := by
  rw [VG.Proof.MlDsa.X86_64.Mask4.hByte, show (136 * n + p) / 136 = n by omega, show (136 * n + p) % 136 = p by omega, VG.Proof.MlDsa.X86_64.Mask4.padded_A0 h,
    iterF_keccakF]

/-! ## `Env` after writes -/

/-- `Env` after writes below the saved registers. -/
theorem Env.low {σ s s' : State} (he : VG.Proof.MlDsa.X86_64.Mask4.Env σ s) {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨VG.Proof.MlDsa.X86_64.Mask4.scr σ, oSave⟩)
    (hf : Frame rs s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp, .r15], s'.gpr r = s.gpr r) : VG.Proof.MlDsa.X86_64.Mask4.Env σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .r14 (by simp), he.r14], by rw [hg .rsp (by simp), he.rsp],
    by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => ((Offset.base_disjoint (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (k := oSave)
        (e := oSave + 8 * i) (n := 8) (by omega) (by simp only [oSave]; omega)).symm).sub_right (hrs r hr))
      (by decide)]
    exact he.saved i hi
  · refine he.frame.trans (hf.sub fun r hr => ⟨VG.Proof.MlDsa.X86_64.Mask4.scrR σ, by simp, fun x hx => Offset.sub_base (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (d := 0)
      (n := oSave) (k := 8192) (by simp only [oSave]; omega) x (by rw [BitVec.add_zero]; exact hrs r hr x hx)⟩)

/-- `Env` after code that writes no memory and keeps its registers. -/
theorem Env.keep {σ s s' : State} (he : VG.Proof.MlDsa.X86_64.Mask4.Env σ s) (hm : s'.mem = s.mem) {rs : List Reg} (hk : Keep rs s s')
    (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp, .r15], r ∉ rs) : VG.Proof.MlDsa.X86_64.Mask4.Env σ s' :=
  Env.low he (rs := []) (by simp) (by rw [hm]; exact Frame.refl _ _) hk.2.1 hk.2.2 fun r hr => hk.gpr (hrs r hr)

/-! ## The squeezes -/

/-- After `n` squeezes. -/
structure SqInv (σ : State) (n : Nat) (s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Mask4.Env σ s
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (VG.Proof.MlDsa.X86_64.Mask4.scr σ) fun k => iterF n (VG.Proof.MlDsa.X86_64.Mask4.A0 (VG.Proof.MlDsa.X86_64.Mask4.B σ k))
  buf : ∀ k < 4, ∀ p < 136 * n, s.mem (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oBuf + 680 * k + p)) = VG.Proof.MlDsa.X86_64.Mask4.hByte (VG.Proof.MlDsa.X86_64.Mask4.B σ k) p

theorem lanes_A0 {σ : State} {m : Mem} (h : VG.Proof.MlDsa.X86_64.Mask4.SB σ m (VG.Proof.MlDsa.X86_64.Mask4.PF σ)) : Lanes4 m (VG.Proof.MlDsa.X86_64.Mask4.scr σ) fun k => iterF 0 (VG.Proof.MlDsa.X86_64.Mask4.A0 (VG.Proof.MlDsa.X86_64.Mask4.B σ k)) :=
  lanes4_of_bytes fun k hk q hq => by
    rw [h k hk q hq, show iterF 0 (VG.Proof.MlDsa.X86_64.Mask4.A0 (VG.Proof.MlDsa.X86_64.Mask4.B σ k)) = VG.Proof.MlDsa.X86_64.Mask4.A0 (VG.Proof.MlDsa.X86_64.Mask4.B σ k) from rfl, VG.Proof.MlDsa.X86_64.Mask4.byteOf_A0 (VG.Proof.MlDsa.X86_64.Mask4.B_length σ k) hq, VG.Proof.MlDsa.X86_64.Mask4.PF]



theorem la_tbl (σ : State) (r k : Nat) : la (VG.Proof.MlDsa.X86_64.Mask4.at' σ 1600) r k = la (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (50 + r) k := by
  rw [la, la, VG.Proof.MlDsa.X86_64.Mask4.at', Offset.add_add, show 1600 + (32 * r + 8 * k) = 32 * (50 + r) + 8 * k by omega]

theorem args_ok {σ s : State} (he : VG.Proof.MlDsa.X86_64.Mask4.Env σ s) :
    WP isa (.block permArgs) s fun s' => (s'.mem = s.mem ∧ s'.gpr .rdi = VG.Proof.MlDsa.X86_64.Mask4.scr σ ∧ s'.gpr .rsi = VG.Proof.MlDsa.X86_64.Mask4.at' σ 800 ∧
      s'.gpr .rdx = VG.Proof.MlDsa.X86_64.Mask4.at' σ 1600 ∧ s'.gpr .rcx = VG.Proof.MlDsa.X86_64.Mask4.at' σ 2368) ∧ Keep [.rdi, .rsi, .rdx, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold permArgs
  xrun [he.rbx, sx800, sx1600, sx2368]

/-- The permutation's precondition, in the scratch space. -/
theorem pre4 {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {s : State} (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr)
    (hrc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (50 + r) k) 64 = RC r) :
    Pre4 s (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (VG.Proof.MlDsa.X86_64.Mask4.at' σ 800) (VG.Proof.MlDsa.X86_64.Mask4.at' σ 1600) :=
  ⟨fun i _ => VG.Proof.MlDsa.X86_64.Mask4.in_scr hp hwr (a := 32 * i) (by omega),
    fun i _ => by rw [VG.Proof.MlDsa.X86_64.Mask4.at', Offset.add_add]; exact VG.Proof.MlDsa.X86_64.Mask4.in_scr hp hwr (by omega),
    fun r _ => by rw [VG.Proof.MlDsa.X86_64.Mask4.at', Offset.add_add]; exact VG.Proof.MlDsa.X86_64.Mask4.in_scr' hp hrd hwr (by omega),
    Offset.base_disjoint _ (by omega) (by omega),
    Offset.base_disjoint _ (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    fun r hr k hk => by rw [VG.Proof.MlDsa.X86_64.Mask4.la_tbl]; exact hrc r hr k hk⟩

/-- A buffer byte, read through a frame of the states. -/
theorem buf_frame {σ : State} {m m' : Mem} {rs : List Region}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨VG.Proof.MlDsa.X86_64.Mask4.at' σ oBuf, 2720⟩ r) (hf : Frame rs m m') {k p : Nat} (hk : k < 4)
    (hp' : p < 680) : m' (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oBuf + 680 * k + p)) = m (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oBuf + 680 * k + p)) := by
  have := hf.bytes (R := ⟨VG.Proof.MlDsa.X86_64.Mask4.at' σ oBuf, 2720⟩) hd (by simp only; omega) (i := 680 * k + p) (by simp only; omega)
  simpa only [VG.Proof.MlDsa.X86_64.Mask4.at', Offset.add_add, Nat.add_assoc] using this

/-- The permutation, after `n` squeezes. -/
theorem perm_ok {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {n : Nat} (hn : n < 5) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.SqInv σ n s)
    {rest : Prog isa} {Q : State → Prop} (kont : ∀ s', VG.Proof.MlDsa.X86_64.Mask4.Env σ s' ∧
      (∀ r < 24, ∀ k < 4, s'.mem.readW (la (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (50 + r) k) 64 = RC r) ∧
      Lanes4 s'.mem (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (fun k => iterF (n + 1) (VG.Proof.MlDsa.X86_64.Mask4.A0 (VG.Proof.MlDsa.X86_64.Mask4.B σ k))) ∧
      (∀ k < 4, ∀ p < 136 * n, s'.mem (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oBuf + 680 * k + p)) = VG.Proof.MlDsa.X86_64.Mask4.hByte (VG.Proof.MlDsa.X86_64.Mask4.B σ k) p) → WP isa rest s' Q) :
    WP isa (.seq (.block permArgs) (.seq Impl.Sha3.X86_64.X4.permute4 rest)) s Q := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.args_ok h.env) fun s₁ ⟨⟨hm, hdi, hsi, hdx, hcx⟩, k₁⟩ => ?_)
  have hrd : s₁.rd = σ.rd := k₁.2.1.trans h.env.rd
  have hwr : s₁.wr = σ.wr := k₁.2.2.trans h.env.wr
  refine WP.seq (WP.mono (permute4_ok (A := fun k => iterF n (VG.Proof.MlDsa.X86_64.Mask4.A0 (VG.Proof.MlDsa.X86_64.Mask4.B σ k))) (VG.Proof.MlDsa.X86_64.Mask4.pre4 hp hrd hwr (by rw [hm]; exact h.rc))
    hdi hsi hdx (by rw [hcx, VG.Proof.MlDsa.X86_64.Mask4.at', VG.Proof.MlDsa.X86_64.Mask4.at', Offset.add_add]) (by rw [hm]; exact h.lanes))
    fun s₂ ⟨hl, hf, hrd₂, hwr₂, _, hg⟩ => kont s₂ ?_)
  have hsub : ∀ r ∈ [(⟨VG.Proof.MlDsa.X86_64.Mask4.scr σ, 800⟩ : Region), ⟨VG.Proof.MlDsa.X86_64.Mask4.at' σ 800, 800⟩], Region.Sub r ⟨VG.Proof.MlDsa.X86_64.Mask4.scr σ, oSave⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by simp only [oSave]; omega)
    · exact Offset.sub_base _ (by simp only [oSave]; omega)
  refine ⟨Env.low (h.env.keep hm k₁ (by decide)) hsub hf hrd₂ hwr₂ fun r hr => hg r
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    fun r hr k hk => ?_, ?_, fun k hk p hp' => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using ⟨Offset.disjoint_base (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega) (by omega),
          Offset.disjoint (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (d := 32 * (50 + r) + 8 * k) (n := 8) (e := 800) (k := 800) (by omega) (by omega)
            (by omega)⟩) (by decide), hm]
    exact h.rc r hr k hk
  · intro i hi k hk
    rw [hl i hi k hk]
    rfl
  · rw [VG.Proof.MlDsa.X86_64.Mask4.buf_frame (by simpa using ⟨Offset.disjoint_base (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (k := 800) (d := oBuf) (n := 2720) (by simp only [oBuf]; omega)
                                    (by simp only [oBuf]; omega), Offset.disjoint (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (d := oBuf) (n := 2720) (e := 800) (k := 800)
                                      (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by omega)⟩) hf hk (by omega), hm]
    exact h.buf k hk p hp'


/-! ## Copying the output -/

/-- During the copy of block `n`: the first `I` lanes of state `K` copied,
and all of the states before it. -/
structure EXI (σ : State) (n K I : Nat) (s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Mask4.Env σ s
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (fun k => iterF (n + 1) (VG.Proof.MlDsa.X86_64.Mask4.A0 (VG.Proof.MlDsa.X86_64.Mask4.B σ k)))
  buf : ∀ k < 4, ∀ p < 680, (p < 136 * n ∨ (136 * n ≤ p ∧ p < 136 * n + 136 ∧ (k < K ∨ (k = K ∧ p < 136 * n + 8 * I)))) →
    s.mem (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oBuf + 680 * k + p)) = VG.Proof.MlDsa.X86_64.Mask4.hByte (VG.Proof.MlDsa.X86_64.Mask4.B σ k) p

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_nil) in
theorem ext_step {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {n K I : Nat} (hn : n < 5) (hK : K < 4) (hI : I < 17) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Mask4.EXI σ n K I s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))),
      .store (at_ .rbx (oBuf + 680 * K + 136 * n + 8 * I)) .rax]) s (VG.Proof.MlDsa.X86_64.Mask4.EXI σ n K (I + 1)) := by
  refine wp_movm (a := VG.Proof.MlDsa.X86_64.Mask4.at' σ (32 * I + 8 * K)) (by rw [ea_at, h.env.rbx])
    (VG.Proof.MlDsa.X86_64.Mask4.in_scr' hp h.env.rd h.env.wr (by omega)) fun s₁ u₁ => wp_store (a := VG.Proof.MlDsa.X86_64.Mask4.at' σ (oBuf + 680 * K + 136 * n + 8 * I))
      (by rw [ea_at, u₁.other _ (by decide), h.env.rbx]) (by rw [u₁.wr]; exact VG.Proof.MlDsa.X86_64.Mask4.in_scr hp h.env.wr (by simp only [oBuf]; omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oBuf + 680 * K + 136 * n + 8 * I)) (s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (32 * I + 8 * K)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  have hf : Frame [⟨VG.Proof.MlDsa.X86_64.Mask4.at' σ (oBuf + 680 * K + 136 * n + 8 * I), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨Env.low h.env (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base _ (by simp only [oBuf, oSave]; omega)) hf (r₂.trans u₁.rd) (w₂.trans u₁.wr)
      fun r hr => by
        rw [g₂, u₁.other r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)],
    fun r hr k hk => ?_, fun i hi k hk => ?_, fun k hk p hp' hc => ?_⟩
  · have e := readW_writeW_off s.mem (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (32 * I + 8 * K)) 64) (d := 32 * (50 + r) + 8 * k)
      (e := oBuf + 680 * K + 136 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · have e := readW_writeW_off s.mem (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (32 * I + 8 * K)) 64) (d := 32 * i + 8 * k)
      (e := oBuf + 680 * K + 136 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.lanes i hi k hk)
  · rw [hm]
    by_cases hw : k = K ∧ 136 * n + 8 * I ≤ p ∧ p < 136 * n + 8 * I + 8
    · obtain ⟨rfl, h₁, h₂⟩ := hw
      rw [wb_in _ _ _ (by omega) (by simp only [oBuf]; omega) (by decide),
        show 8 * (oBuf + 680 * k + p - (oBuf + 680 * k + 136 * n + 8 * I)) = 8 * (p - 136 * n - 8 * I) by omega,
        byte_readW _ _ (by omega), VG.Proof.MlDsa.X86_64.Mask4.at', Offset.add_add,
        show 32 * I + 8 * k + (p - 136 * n - 8 * I) = 32 * ((8 * I + (p - 136 * n - 8 * I)) / 8) + 8 * k +
          (8 * I + (p - 136 * n - 8 * I)) % 8 by omega,
        byte_of_lanes4 h.lanes hk (by omega), ← VG.Proof.MlDsa.X86_64.Mask4.hByte_A0 (VG.Proof.MlDsa.X86_64.Mask4.B_length σ k) (by omega),
        show 136 * n + (8 * I + (p - 136 * n - 8 * I)) = p by omega]
    · rw [wb_out _ _ _ (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by simp only [oBuf]; omega)]
      exact h.buf k hk p hp' (by omega)

theorem extract_eq (n : Nat) : VG.Impl.MlDsa.X86_64.Sample.Mask4.extract n = (List.range 4).flatMap fun K => (List.range 17).flatMap fun I =>
    [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))), .store (at_ .rbx (oBuf + 680 * K + 136 * n + 8 * I)) .rax] := rfl

/-- Block `n` of each state's output. -/
theorem extract_ok {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {n : Nat} (hn : n < 5) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.EXI σ n 0 0 s) :
    WP isa (.block (VG.Impl.MlDsa.X86_64.Sample.Mask4.extract n)) s (VG.Proof.MlDsa.X86_64.Mask4.SqInv σ (n + 1)) := by
  rw [VG.Proof.MlDsa.X86_64.Mask4.extract_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => VG.Proof.MlDsa.X86_64.Mask4.EXI σ n K 0 s) (fun K s hK h => ?_) 4 (Nat.le_refl _) s h)
    fun s' h' => ⟨h'.env, h'.rc, h'.lanes, fun k hk p hp' => h'.buf k hk p (by omega) (by omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun I s => VG.Proof.MlDsa.X86_64.Mask4.EXI σ n K I s) (fun I s hI h => VG.Proof.MlDsa.X86_64.Mask4.ext_step hp hn hK hI h)
    17 (Nat.le_refl _) s h) fun s' h' => ⟨h'.env, h'.rc, h'.lanes, fun k hk p hp' hc => h'.buf k hk p hp' (by omega)⟩

/-- `squeeze4 n`: after `n + 1` squeezes. -/
theorem sq_ok {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ) {n : Nat} (hn : n < 5) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.SqInv σ n s) :
    WP isa (squeeze4 n) s (VG.Proof.MlDsa.X86_64.Mask4.SqInv σ (n + 1)) := by
  unfold squeeze4
  exact VG.Proof.MlDsa.X86_64.Mask4.perm_ok hp hn h fun s' ⟨he, hrc, hl, hb⟩ =>
    VG.Proof.MlDsa.X86_64.Mask4.extract_ok hp hn ⟨he, hrc, hl, fun k hk p _ hc => hb k hk p (by omega)⟩

end VG.Proof.MlDsa.X86_64.Mask4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Top`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4_avx2`, correctness

Untrusted: everything here is checked by Lean. The pieces, in order: the
prologue, the round constants and the padded seeds (`M4Absorb.lean`), five
squeezes (`M4Squeeze.lean`), which leave the first 680 bytes of SHAKE256 of
each seed in its buffer, the branch on `γ₁`, the four unpackings, each the
loop of `vg_mldsa_expand_mask_poly` (`emBody_ok`) on the output of a seed
(`unpack_ok`), and the epilogue.
-/

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Impl.MlKem.X86_64.Sample4 (oRc oBuf)
open VG.Impl.MlDsa.X86_64.Sample (emBody)
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.X86_64.Sample (GPre emBody_ok emOk emV gOf)
open VG.Proof.MlDsa.Sample (emC emC_eq expandMask_getElem polyIs_of_coeffAt)
open VG.Spec.MlDsa (H coeffAt)
open VG.Proof.MlDsa.Sample (coeffAddr)
open VG.Proof.Sha3.X86_64.X4 (la)

/-- The first 640 bytes of SHAKE256 of seed `k`. -/
abbrev X (σ : State) (k : Nat) : List Byte := H (VG.Proof.MlDsa.X86_64.Mask4.B σ k) 640

/-- After the squeezes, and the unpackings of the first `K` seeds, `c` bits a coefficient. -/
structure UI (σ : State) (c K : Nat) (s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Mask4.Env σ s
  buf : ∀ k < 4, ∀ p < 680, s.mem (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oBuf + 680 * k + p)) = VG.Proof.MlDsa.X86_64.Mask4.hByte (VG.Proof.MlDsa.X86_64.Mask4.B σ k) p
  st : ∀ k < K, ∀ i < 256, coeffAt s.mem (VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) k) i = emV (VG.Proof.MlDsa.X86_64.Mask4.X σ k) c i

/-- During the unpacking of seed `K`: `g` groups of four. -/
structure EI (σ : State) (c K g : Nat) (s : State) : Prop where
  ui : VG.Proof.MlDsa.X86_64.Mask4.UI σ c K s
  rsi : s.gpr .rsi = VG.Proof.MlDsa.X86_64.Mask4.at' σ (oBuf + 680 * K) + BitVec.ofNat 64 (c / 2 * g)
  rdi : s.gpr .rdi = VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) K + BitVec.ofNat 64 (16 * g)
  cur : ∀ i < 4 * g, coeffAt s.mem (VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) K) i = emV (VG.Proof.MlDsa.X86_64.Mask4.X σ K) c i

section
variable {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ)
include hp

/-- The prologue, the round constants and the padded seeds. -/
theorem start_ok : WP isa (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4)) σ (VG.Proof.MlDsa.X86_64.Mask4.SqInv σ 0) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Mask4.pro_ok hp) fun s₁ h₁ => WP.mono (VG.Proof.MlDsa.X86_64.Mask4.rc_ok hp h₁) fun s₂ h₂ => ?_
  have he₂ : VG.Proof.MlDsa.X86_64.Mask4.Env σ s₂ := Env.low h₁ (rs := [⟨VG.Proof.MlDsa.X86_64.Mask4.at' σ oRc, 768⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [oRc, oSave]; omega))
    h₂.frame h₂.keep.2.1 h₂.keep.2.2 fun r hr => h₂.keep.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Mask4.absorb_ok hp (m₁ := s₂.mem) ⟨he₂, Frame.refl _ _⟩)
    fun s₃ ⟨a₃, b₃⟩ => ⟨a₃.env, fun r hr k hk => ?_, VG.Proof.MlDsa.X86_64.Mask4.lanes_A0 b₃, fun _ _ p hp' => absurd hp' (by omega)⟩
  rw [a₃.frame.readW (Region.contains_self _ _) (by
    simpa using Offset.disjoint_base (VG.Proof.MlDsa.X86_64.Mask4.scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega) (by omega))
    (by decide)]
  exact h₂.rc r hr k hk

/-- `Env` after writes to polynomial `K`. -/
theorem Env.poly {K : Nat} (hK : K < 4) {s s' : State} (he : VG.Proof.MlDsa.X86_64.Mask4.Env σ s)
    (hf : Frame [⟨VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) K, 1024⟩] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp, .r15], s'.gpr r = s.gpr r) : VG.Proof.MlDsa.X86_64.Mask4.Env σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .r14 (by simp), he.r14], by rw [hg .rsp (by simp), he.rsp],
    by rw [hg .r15 (by simp), he.r15], fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using ((hp.a_scr.sub_left (VG.Proof.MlDsa.X86_64.Mask4.sub_poly hK)).sub_right (VG.Proof.MlDsa.X86_64.Mask4.sub_scr (σ := σ) (a := oSave + 8 * i) (n := 8)
          (by simp only [oSave]; omega))).symm) (by decide)]
    exact he.saved i hi
  · exact he.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.MlDsa.X86_64.Mask4.aR σ, by simp, VG.Proof.MlDsa.X86_64.Mask4.sub_poly hK⟩)

/-- The facts a group of the unpacking of seed `K` needs. -/
theorem gpre {c K g : Nat} (hK : K < 4) (hg : g < 64) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.EI σ c K g s) :
    GPre c (VG.Proof.MlDsa.X86_64.Mask4.X σ K) (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oBuf + 680 * K)) (VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) K) g s := by
  refine ⟨h.rsi, h.rdi, hg, fun j hj => ?_, fun j hj => ?_, fun i hi => ?_, fun j hj hc => ?_⟩
  · rw [VG.Proof.MlDsa.X86_64.Mask4.at', Offset.add_add, ← VG.Proof.MlDsa.X86_64.Mask4.at', h.ui.buf K hK j (by omega)]; exact (VG.Proof.MlDsa.X86_64.Mask4.H_getD _ hj).symm
  · rw [VG.Proof.MlDsa.X86_64.Mask4.at', Offset.add_add, ← VG.Proof.MlDsa.X86_64.Mask4.at']
    exact VG.Proof.MlDsa.X86_64.Mask4.in_scr' hp h.ui.env.rd h.ui.env.wr (by simp only [oBuf]; omega)
  · rw [h.ui.env.wr, hp.wr]
    refine ⟨VG.Proof.MlDsa.X86_64.Mask4.aR σ, by simp, ?_⟩
    rw [VG.Proof.MlDsa.Sample.coeffAddr, VG.Proof.MlDsa.X86_64.Mask4.poly4, Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega)
  · rw [VG.Proof.MlDsa.X86_64.Mask4.at', Offset.add_add] at hc
    exact (hp.a_scr.sub_left (VG.Proof.MlDsa.X86_64.Mask4.sub_poly hK)) _ hc
      (Offset.contains_base _ (by simp only [oBuf]; omega) (by simp only [oBuf]; omega))

/-- An iteration of the unpacking of seed `K`. -/
theorem ei_step {c K g : Nat} (hc : emOk c) (hK : K < 4) (hg : g < 64) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.EI σ c K g s) :
    WP isa (.block (emBody c)) s fun s' => VG.Proof.MlDsa.X86_64.Mask4.EI σ c K (g + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  refine WP.mono (emBody_ok hc (VG.Proof.MlDsa.X86_64.Mask4.gpre hp hK hg h)) fun s' ⟨hk, hf, hst, hsame, hsi, hdi, hcx, hz⟩ => ?_
  refine ⟨⟨⟨Env.poly hp hK h.ui.env hf hk.2.1 hk.2.2 fun r hr => hk.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), fun k hk' p hp' => ?_, fun k hk' i hi => ?_⟩,
    hsi, hdi, fun i hi => ?_⟩, hcx, hz⟩
  · rw [VG.Proof.MlDsa.X86_64.Mask4.buf_frame (by simpa using ((hp.a_scr.sub_left (VG.Proof.MlDsa.X86_64.Mask4.sub_poly hK)).sub_right (VG.Proof.MlDsa.X86_64.Mask4.sub_scr (σ := σ) (a := oBuf)
                                    (n := 2720) (by simp only [oBuf]; omega))).symm) hf hk' hp']
    exact h.ui.buf k hk' p hp'
  · rw [show coeffAt s'.mem (VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) k) i = coeffAt s.mem (VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) k) i from
      hf.readW (VG.Proof.MlDsa.Sample.coeff_contains _ hi) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have hd := Offset.disjoint (VG.Proof.MlDsa.X86_64.Mask4.aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega)
          (by omega) (by omega)
        simpa [VG.Proof.MlDsa.X86_64.Mask4.poly4] using hd) (by decide)]
    exact h.ui.st k hk' i hi
  · by_cases hlo : i < 4 * g
    · rw [hsame i (by omega) (.inl hlo)]; exact h.cur i hlo
    · have := hst (i - 4 * g) (by omega)
      rwa [show 4 * g + (i - 4 * g) = i by omega] at this

/-- The unpacking of seed `K`. -/
theorem unpack_ok {c K : Nat} (hc : emOk c) (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.UI σ c K s) :
    WP isa (unpack c K) s (VG.Proof.MlDsa.X86_64.Mask4.UI σ c (K + 1)) := by
  unfold unpack
  refine WP.seq (WP.mono (WP.keep [.rsi, .rdi, .rcx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = VG.Proof.MlDsa.X86_64.Mask4.at' σ (oBuf + 680 * K) ∧ s'.gpr .rdi = VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) K ∧ s'.gpr .rcx = BitVec.ofNat 64 64)
    (by xrun [h.env.rbx, h.env.r13, VG.Proof.MlKem.X86_64.sx_ofNat (show oBuf + 680 * K < 2 ^ 31 by simp only [oBuf]; omega),
      VG.Proof.MlKem.X86_64.sx_ofNat (show 1024 * K < 2 ^ 31 by omega)]) (by rfl)) fun s1 ⟨⟨hm1, hsi1, hdi1, hcx1⟩, k1⟩ => ?_)
  have he1 : VG.Proof.MlDsa.X86_64.Mask4.Env σ s1 := Env.low h.env (rs := []) (by simp) (by rw [hm1]; exact Frame.refl _ _) k1.2.1 k1.2.2
    fun r hr => k1.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine wp_countdown (N := 64) (by decide) (by decide) (VG.Proof.MlDsa.X86_64.Mask4.EI σ c K) (fun g hg s hI _ =>
    WP.mono (VG.Proof.MlDsa.X86_64.Mask4.ei_step hp hc hK hg hI) fun s' ⟨hI', hc', hz⟩ => ⟨hI', hc', hz⟩) (fun s' hI =>
      ⟨hI.ui.env, hI.ui.buf, fun k hk i hi => ?_⟩)
    ⟨⟨he1, fun k hk p hp' => by rw [hm1]; exact h.buf k hk p hp', fun k hk i hi => by rw [hm1]; exact h.st k hk i hi⟩,
      by rw [hsi1]; simp, by rw [hdi1]; simp, fun i hi => absurd hi (by omega)⟩ hcx1
  by_cases e : k = K
  · subst e; exact hI.cur i (by omega)
  · exact hI.ui.st k (by omega) i hi

/-- The four unpackings. -/
theorem unpack4_ok {c : Nat} (hc : emOk c) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.UI σ c 0 s) : WP isa (unpack4 c) s (VG.Proof.MlDsa.X86_64.Mask4.UI σ c 4) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.unpack_ok hp hc (by decide) h) fun _ h₁ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.unpack_ok hp hc (by decide) h₁)
    fun _ h₂ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.unpack_ok hp hc (by decide) h₂) fun _ h₃ => VG.Proof.MlDsa.X86_64.Mask4.unpack_ok hp hc (by decide) h₃)))

omit hp in
theorem sx17 : BitVec.signExtend 64 (0x20000 : BitVec 32) = BitVec.ofNat 64 0x20000 := by decide

/-- The branch on `γ₁`, and the unpackings for it. -/
theorem sel_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.SqInv σ 5 s) {Q : State → Prop} (kont : ∀ s', VG.Proof.MlDsa.X86_64.Mask4.UI σ (emC (gOf σ)) 4 s' →
    WP isa (.block epi) s' Q) :
    WP isa (.seq (.block [.vop .vzeroupper, .alu32 .cmp .r14 (.imm 0x20000)])
      (.seq (.ite .e (unpack4 18) (unpack4 20)) (.block epi))) s Q := by
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = s.gpr .r14 ∧
      s'.zf = some (BitVec.setWidth 32 (s.gpr .r14) - 0x20000 == 0)) (by xrun; exact ⟨rfl, rfl, rfl⟩) (by decide))
    fun s1 ⟨⟨hm1, h14, hz1⟩, k1'⟩ => ?_)
  have k1 : Keep [] s s1 := ⟨fun r _ => by
    by_cases e : r = .r14
    · subst e; exact h14
    · exact k1'.gpr (by simp [e]), k1'.2⟩
  have hr14 : BitVec.setWidth 32 (s.gpr .r14) = BitVec.ofNat 32 (gOf σ) := by
    rw [h.env.r14, gOf, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hU : ∀ c, VG.Proof.MlDsa.X86_64.Mask4.UI σ c 0 s1 := fun c => ⟨Env.low h.env (rs := []) (by simp) (by rw [hm1]; exact Frame.refl _ _)
      k1.2.1 k1.2.2 fun r _ => k1.gpr (List.not_mem_nil),
    fun k hk p hp' => by rw [hm1]; exact h.buf k hk p (by omega), fun _ hk => absurd hk (by omega)⟩
  refine WP.seq (WP.mono (?_ : WP isa (.ite .e (unpack4 18) (unpack4 20)) s1 (VG.Proof.MlDsa.X86_64.Mask4.UI σ (emC (gOf σ)) 4)) kont)
  rcases hp.gamma with he | he
  · refine WP.ite true (by show s1.zf = _; rw [hz1, hr14, he]; rfl) (fun _ => ?_) (fun hb => absurd hb (by decide))
    rw [show emC (gOf σ) = 18 by rw [he]; rfl]; exact VG.Proof.MlDsa.X86_64.Mask4.unpack4_ok hp (.inl rfl) (hU 18)
  · refine WP.ite false (by show s1.zf = _; rw [hz1, hr14, he]; rfl) (fun hb => absurd hb (by decide)) (fun _ => ?_)
    rw [show emC (gOf σ) = 20 by rw [he]; rfl]; exact VG.Proof.MlDsa.X86_64.Mask4.unpack4_ok hp (.inr rfl) (hU 20)

omit hp in
theorem epi_eq : epi = [.mov .r14 (.mem (at_ .rbx 5120)), .mov .r13 (.mem (at_ .rbx 5112)),
    .mov .r12 (.mem (at_ .rbx 5104)), .mov .rbp (.mem (at_ .rbx 5096)), .mov .rbx (.mem (at_ .rbx 5088))] := rfl

/-- The postcondition, and the callee-saved registers restored. -/
theorem end_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.UI σ (emC (gOf σ)) 4 s) :
    WP isa (.block epi) s fun s' => em4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Mask4.scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    VG.Proof.MlDsa.X86_64.Mask4.in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega)
  rw [VG.Proof.MlDsa.X86_64.Mask4.epi_eq]
  refine WP.mono (WP.keep [.r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .r14 = s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  obtain ⟨_, _, hγ⟩ := emC_eq hp.gamma
  refine ⟨fun K hK => polyIs_of_coeffAt fun i hi => ?_, fun r hr => ?_, ?_⟩
  · rw [expandMask_getElem _ hp.gamma hi, hm, h.st K hK i (by omega)]
    simp only [emV]
    congr 3
    rw [← hγ]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega)⟩)
      (by decide)

end

theorem correct (σ : State) (hs : em4K.pre σ) :
    ∃ t s', Exec isa expandMask4Avx2 σ t s' ∧ abiPreserved σ s' ∧ em4K.post σ s' := by
  have hp := VG.Proof.MlDsa.X86_64.Mask4.pre_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.start_ok hp) fun _ h₀ =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.sq_ok hp (by decide) h₀) fun _ h₁ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.sq_ok hp (by decide) h₁) fun _ h₂ =>
      WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.sq_ok hp (by decide) h₂) fun _ h₃ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.sq_ok hp (by decide) h₃) fun _ h₄ =>
        WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.sq_ok hp (by decide) h₄) fun _ h₅ => VG.Proof.MlDsa.X86_64.Mask4.sel_ok hp h₅ fun _ hu => VG.Proof.MlDsa.X86_64.Mask4.end_ok hp hu))))))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Mask4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4CT`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4_avx2`, constant time

Untrusted: everything here is checked by Lean. Two runs whose pointers and
`γ₁` agree (the declared public data) leak the same. The taint analysis
proves each piece from the pointers (the prologue, the absorption and the
squeezes, from the arguments and then `rbx`; the unpackings, from `rbx`,
`r13` and `rsp`); the two runs take the same branch on `γ₁` (`cmp_ok`), as
their `γ₁` agree.
-/

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Impl.MlKem.X86_64.Sample4 (oRc)
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.X86_64.Sample (emOk gOf)
open VG.Proof.MlDsa.Sample (emC)

/-- Two runs related by `I`, from entry states that agree on what is public. -/
abbrev R (I : State → State → Prop) : State → State → Prop := Rel2 em4K.pre em4K.pub I

theorem env_rbx {σ₁ σ₂ s₁ s₂ : State} (hq : em4K.pub σ₁ σ₂) (e₁ : VG.Proof.MlDsa.X86_64.Mask4.Env σ₁ s₁) (e₂ : VG.Proof.MlDsa.X86_64.Mask4.Env σ₂ s₂) :
    s₁.gpr .rbx = s₂.gpr .rbx := by rw [e₁.rbx, e₂.rbx, VG.Proof.MlDsa.X86_64.Mask4.scr, VG.Proof.MlDsa.X86_64.Mask4.scr, hq.2.2.2.1]

theorem env_r13 {σ₁ σ₂ s₁ s₂ : State} (hq : em4K.pub σ₁ σ₂) (e₁ : VG.Proof.MlDsa.X86_64.Mask4.Env σ₁ s₁) (e₂ : VG.Proof.MlDsa.X86_64.Mask4.Env σ₂ s₂) :
    s₁.gpr .r13 = s₂.gpr .r13 := by rw [e₁.r13, e₂.r13, VG.Proof.MlDsa.X86_64.Mask4.aP, VG.Proof.MlDsa.X86_64.Mask4.aP, hq.2.2.1]

theorem env_rsp {σ₁ σ₂ s₁ s₂ : State} (hq : em4K.pub σ₁ σ₂) (e₁ : VG.Proof.MlDsa.X86_64.Mask4.Env σ₁ s₁) (e₂ : VG.Proof.MlDsa.X86_64.Mask4.Env σ₂ s₂) :
    s₁.gpr .rsp = s₂.gpr .rsp := by rw [e₁.rsp, e₂.rsp, hq.2.2.2.2]

/-- `squeeze4 n`, given its taint analysis. -/
theorem sq_ct (n : Nat) (hn : n < 5) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 n) hc).isSome = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Mask4.R fun σ s => VG.Proof.MlDsa.X86_64.Mask4.SqInv σ n s) (squeeze4 n) (VG.Proof.MlDsa.X86_64.Mask4.R fun σ s => VG.Proof.MlDsa.X86_64.Mask4.SqInv σ (n + 1) s) :=
  relInv (fun σ s hp h => VG.Proof.MlDsa.X86_64.Mask4.sq_ok (VG.Proof.MlDsa.X86_64.Mask4.pre_of hp) hn h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlDsa.X86_64.Mask4.env_rbx hq h₁.env h₂.env) c)

/-- The branch on `γ₁`'s comparison, and what it keeps. -/
theorem cmp_ok {σ : State} {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.SqInv σ 5 s) :
    WP isa (.block [.vop .vzeroupper, .alu32 .cmp .r14 (.imm 0x20000)]) s fun s' =>
      (∀ c, VG.Proof.MlDsa.X86_64.Mask4.UI σ c 0 s') ∧ s'.zf = some (BitVec.setWidth 32 (σ.gpr .rsi) - 0x20000 == 0) := by
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = s.gpr .r14 ∧
      s'.zf = some (BitVec.setWidth 32 (s.gpr .r14) - 0x20000 == 0)) (by xrun; exact ⟨rfl, rfl, rfl⟩) (by decide))
    fun s1 ⟨⟨hm1, h14, hz1⟩, k1'⟩ => ⟨fun c => ⟨Env.low h.env (rs := []) (by simp)
      (by rw [hm1]; exact Frame.refl _ _) k1'.2.1 k1'.2.2 fun r _ => by
        by_cases e : r = .r14
        · subst e; exact h14
        · exact k1'.gpr (by simp [e]),
      fun k hk p hp' => by rw [hm1]; exact h.buf k hk p (by omega), fun _ hk => absurd hk (by omega)⟩,
    by rw [hz1, h.env.r14]⟩

/-- The comparison of `γ₁`, as `γ₁ = 2¹⁷`. -/
theorem zf_gamma (σ : State) :
    (BitVec.setWidth 32 (σ.gpr .rsi) - 0x20000 == 0) = decide (gOf σ = 2 ^ 17) := by
  by_cases e : gOf σ = 2 ^ 17
  · rw [show BitVec.setWidth 32 (σ.gpr .rsi) = 0x20000 from BitVec.eq_of_toNat_eq (by rw [← gOf, e]; rfl),
      decide_eq_true e]
    rfl
  · rw [decide_eq_false e, beq_eq_false_iff_ne]
    intro h
    apply e
    rw [gOf, show BitVec.setWidth 32 (σ.gpr .rsi) = 0x20000 by
      rw [← BitVec.sub_add_cancel (BitVec.setWidth 32 (σ.gpr .rsi)) 0x20000, h]; rfl]
    rfl

/-- A piece that takes each run from `I` to `I'`, keeping a fact `C` of the entry states. -/
theorem relInvC {I I' : State → State → Prop} {C : State → Prop} {c : Prog isa}
    (hw : ∀ σ s, em4K.pre σ → I σ s → WP isa c s (I' σ)) (ht : RelCT isa (VG.Proof.MlDsa.X86_64.Mask4.R I) c fun _ _ => True) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Mask4.R fun σ s => I σ s ∧ C σ) c (VG.Proof.MlDsa.X86_64.Mask4.R fun σ s => I' σ s ∧ C σ) :=
  relInv (fun σ s hp hs => WP.mono (hw σ s hp hs.1) fun _ h => ⟨h, hs.2⟩)
    (RelCT.mono ht (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, i₁.1, i₂.1⟩) fun _ _ h => h)

/-- The unpackings for `c`, from states with the same pointers, keeping a fact `C` of the entry states. -/
theorem unpack4_ct {c : Nat} (hc : emOk c) {C : State → Prop} {hh : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13, .rsp]) (unpack4 c) hh).isSome = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Mask4.R fun σ s => VG.Proof.MlDsa.X86_64.Mask4.UI σ c 0 s ∧ C σ) (unpack4 c) (VG.Proof.MlDsa.X86_64.Mask4.R fun σ s => VG.Proof.MlDsa.X86_64.Mask4.UI σ c 4 s ∧ C σ) :=
  VG.Proof.MlDsa.X86_64.Mask4.relInvC (fun σ s hp h => VG.Proof.MlDsa.X86_64.Mask4.unpack4_ok (VG.Proof.MlDsa.X86_64.Mask4.pre_of hp) hc h)
    (taintRel [.rbx, .r13, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [VG.Proof.MlDsa.X86_64.Mask4.env_rbx hq h₁.env h₂.env, VG.Proof.MlDsa.X86_64.Mask4.env_r13 hq h₁.env h₂.env, VG.Proof.MlDsa.X86_64.Mask4.env_rsp hq h₁.env h₂.env]) ht)

theorem gOf_pub {σ₁ σ₂ : State} (hq : em4K.pub σ₁ σ₂) : gOf σ₁ = gOf σ₂ := by rw [gOf, gOf, hq.2.1]

/-- The branch on `γ₁`. -/
theorem sel_ct : RelCT isa (VG.Proof.MlDsa.X86_64.Mask4.R fun σ s => (∀ c, VG.Proof.MlDsa.X86_64.Mask4.UI σ c 0 s) ∧
      s.zf = some (BitVec.setWidth 32 (σ.gpr .rsi) - 0x20000 == 0))
    (.ite .e (unpack4 18) (unpack4 20)) (VG.Proof.MlDsa.X86_64.Mask4.R fun σ s => VG.Proof.MlDsa.X86_64.Mask4.UI σ (emC (gOf σ)) 4 s) := by
  refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
      show x.zf = y.zf; rw [h₁.2, h₂.2, hq.2.1]) ?_ ?_
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Mask4.unpack4_ct (C := fun σ => emC (gOf σ) = 18) (.inl rfl) (by taint_decide))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩ => ?_)
      fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨u₁, c₁⟩, ⟨u₂, c₂⟩⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, by show VG.Proof.MlDsa.X86_64.Mask4.UI σ₁ _ 4 x; rw [c₁]; exact u₁,
        by show VG.Proof.MlDsa.X86_64.Mask4.UI σ₂ _ 4 y; rw [c₂]; exact u₂⟩
    have hb' : x.zf = some true := hb
    rw [h₁.2, VG.Proof.MlDsa.X86_64.Mask4.zf_gamma, Option.some.injEq, decide_eq_true_iff] at hb'
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁.1 18, by rw [hb']; rfl⟩, ⟨h₂.1 18, by rw [← VG.Proof.MlDsa.X86_64.Mask4.gOf_pub hq, hb']; rfl⟩⟩
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Mask4.unpack4_ct (C := fun σ => emC (gOf σ) = 20) (.inr rfl) (by taint_decide))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩ => ?_)
      fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨u₁, c₁⟩, ⟨u₂, c₂⟩⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, by show VG.Proof.MlDsa.X86_64.Mask4.UI σ₁ _ 4 x; rw [c₁]; exact u₁,
        by show VG.Proof.MlDsa.X86_64.Mask4.UI σ₂ _ 4 y; rw [c₂]; exact u₂⟩
    have hb' : x.zf = some false := hb
    rw [h₁.2, VG.Proof.MlDsa.X86_64.Mask4.zf_gamma, Option.some.injEq, decide_eq_false_iff_not] at hb'
    have e₁ : gOf σ₁ = 2 ^ 19 := (VG.Proof.MlDsa.X86_64.Mask4.pre_of p₁).gamma.resolve_left hb'
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁.1 20, by rw [e₁]; rfl⟩, ⟨h₂.1 20, by rw [← VG.Proof.MlDsa.X86_64.Mask4.gOf_pub hq, e₁]; rfl⟩⟩

theorem ct : ConstantTime isa em4K.pre em4K.pub expandMask4Avx2 := by
  unfold expandMask4Avx2
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ s => VG.Proof.MlDsa.X86_64.Mask4.SqInv σ 0 s)
    (fun σ s hp h => by subst h; exact VG.Proof.MlDsa.X86_64.Mask4.start_ok (VG.Proof.MlDsa.X86_64.Mask4.pre_of hp))
    (taintRel [.rdi, .rdx, .rcx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]) (by taint_decide))) ?_)
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Mask4.sq_ct 0 (by decide) (by taint_decide)) (RelCT.seq (VG.Proof.MlDsa.X86_64.Mask4.sq_ct 1 (by decide) (by taint_decide))
    (RelCT.seq (VG.Proof.MlDsa.X86_64.Mask4.sq_ct 2 (by decide) (by taint_decide)) (RelCT.seq (VG.Proof.MlDsa.X86_64.Mask4.sq_ct 3 (by decide) (by taint_decide))
      (RelCT.seq (VG.Proof.MlDsa.X86_64.Mask4.sq_ct 4 (by decide) (by taint_decide)) ?_))))
  refine RelCT.seq (relInv (fun σ s _ h => VG.Proof.MlDsa.X86_64.Mask4.cmp_ok h) (taintRel [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
    (by taint_decide))) (RelCT.seq VG.Proof.MlDsa.X86_64.Mask4.sel_ct ?_)
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlDsa.X86_64.Mask4.env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlDsa.X86_64.Mask4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Scalar`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4`

Untrusted: everything here is checked by Lean. The baseline implementation
calls `vg_mldsa_expand_mask_poly` on each seed, between the prologue and the
epilogue of the one for AVX2: after the call on seed `K`, polynomial `K` is
`ExpandMask`'s for the seed (`PC`), as in `vg_mldsa_rej_ntt_poly4`
(`Rej4Scalar.lean`).
-/

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.X86_64.Sample (emK gOf expandMask_correct expandMask_ct)
open VG.Proof.MlDsa.Arith (polyIs_frame)
open VG.Spec.MlDsa (PolyIs H toRq bitUnpack bitlen seed66)
open VG.Spec.Sha3 (bytesAt)

theorem em_nosp : NoSp Impl.MlDsa.X86_64.Sample.expandMask := nosp_of (by decide +kernel)

theorem em_depth : Impl.MlDsa.X86_64.Sample.expandMask.depth = 2 := by decide +kernel

/-- `ExpandMask`'s polynomial for seed `k`. -/
abbrev P (σ : State) (k : Nat) : Spec.MlDsa.Poly :=
  toRq (bitUnpack (H (VG.Proof.MlDsa.X86_64.Mask4.B σ k) (32 * (1 + bitlen (gOf σ - 1)))) (gOf σ - 1) (gOf σ))

/-- Before the call on seed `K`. -/
structure PC (σ : State) (K : Nat) (s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Mask4.Env σ s
  polys : ∀ k < K, PolyIs s.mem (VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) k) (VG.Proof.MlDsa.X86_64.Mask4.P σ k)

/-- The regions of `vg_mldsa_expand_mask_poly`'s call for seed `K`. -/
abbrev cRd (σ : State) (K : Nat) : List Region := [⟨VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 (66 * K), 66⟩]
abbrev cWr (σ : State) (K : Nat) : List Region := [pR (VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) K), ⟨VG.Proof.MlDsa.X86_64.Mask4.at' σ oScalar, 2048⟩]

section
variable {σ : State} (hp : VG.Proof.MlDsa.X86_64.Mask4.Pre σ)
include hp

omit hp in
theorem c_sub {K : Nat} (hK : K < 4) : ∀ r ∈ VG.Proof.MlDsa.X86_64.Mask4.cWr σ K ++ [VG.Proof.MlDsa.X86_64.Mask4.stkR σ],
    (∃ R ∈ [VG.Proof.MlDsa.X86_64.Mask4.aR σ, VG.Proof.MlDsa.X86_64.Mask4.scrR σ, VG.Proof.MlDsa.X86_64.Mask4.stkR σ], Region.Sub r R) := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact ⟨VG.Proof.MlDsa.X86_64.Mask4.aR σ, by simp, VG.Proof.MlDsa.X86_64.Mask4.sub_poly hK⟩
  · exact ⟨VG.Proof.MlDsa.X86_64.Mask4.scrR σ, by simp, VG.Proof.MlDsa.X86_64.Mask4.sub_scr (by simp only [oScalar]; omega)⟩
  · exact ⟨VG.Proof.MlDsa.X86_64.Mask4.stkR σ, by simp, fun _ h => h⟩

/-- A region the call writes is apart from `⟨at' σ a, n⟩` in the scratch space below 6144. -/
theorem c_disj {K : Nat} (hK : K < 4) {a n : Nat} (h : a + n ≤ oScalar) :
    ∀ r ∈ VG.Proof.MlDsa.X86_64.Mask4.cWr σ K ++ [VG.Proof.MlDsa.X86_64.Mask4.stkR σ], Region.Disjoint ⟨VG.Proof.MlDsa.X86_64.Mask4.at' σ a, n⟩ r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact (hp.a_scr.symm.sub_left (VG.Proof.MlDsa.X86_64.Mask4.sub_scr (by simp only [oScalar] at h; omega))).sub_right (VG.Proof.MlDsa.X86_64.Mask4.sub_poly hK)
  · exact Offset.disjoint _ (.inl h) (by simp only [oScalar] at h; omega) (by simp only [oScalar]; omega)
  · exact (hp.stk_scr.sub_right (VG.Proof.MlDsa.X86_64.Mask4.sub_scr (by simp only [oScalar] at h; omega))).symm

theorem seed_bytes {K : Nat} (hK : K < 4) {m : Mem} (hf : Frame [VG.Proof.MlDsa.X86_64.Mask4.aR σ, VG.Proof.MlDsa.X86_64.Mask4.scrR σ, VG.Proof.MlDsa.X86_64.Mask4.stkR σ] σ.mem m) :
    bytesAt m (VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 (66 * K)) 66 = VG.Proof.MlDsa.X86_64.Mask4.B σ K := by
  rw [MlKem.bytesAt_frame hf (by simpa using ⟨hp.sd_a.sub_left (Offset.sub_base _ (by omega)),
    hp.sd_scr.sub_left (Offset.sub_base _ (by omega)), (hp.stk_sd.sub_right (Offset.sub_base _ (by omega))).symm⟩)
    (by decide)]
  rfl

theorem scr6144_lt : (VG.Proof.MlDsa.X86_64.Mask4.at' σ oScalar).toNat + 2048 ≤ 2 ^ 64 := by
  have := hp.scr_lt
  rw [VG.Proof.MlDsa.X86_64.Mask4.at', Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show oScalar < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (by simp only [oScalar]; omega)]
  simp only [oScalar]; omega

theorem regs {s : State} (he : VG.Proof.MlDsa.X86_64.Mask4.Env σ s) : s.rd ++ s.wr = [VG.Proof.MlDsa.X86_64.Mask4.sdR σ, VG.Proof.MlDsa.X86_64.Mask4.aR σ, VG.Proof.MlDsa.X86_64.Mask4.scrR σ] := by
  rw [he.rd, he.wr, hp.rd, hp.wr]; rfl

theorem cov {s : State} (he : VG.Proof.MlDsa.X86_64.Mask4.Env σ s) {K : Nat} (hK : K < 4) :
    Covers (VG.Proof.MlDsa.X86_64.Mask4.cRd σ K ++ VG.Proof.MlDsa.X86_64.Mask4.cWr σ K) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlDsa.X86_64.Mask4.cWr σ K) s.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · rw [VG.Proof.MlDsa.X86_64.Mask4.regs hp he]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.MlDsa.X86_64.Mask4.sdR σ, by simp, 66 * K, rfl, by simp only; omega⟩
    · exact ⟨VG.Proof.MlDsa.X86_64.Mask4.aR σ, by simp, 1024 * K, rfl, by simp only; omega⟩
    · exact ⟨VG.Proof.MlDsa.X86_64.Mask4.scrR σ, by simp, oScalar, rfl, by simp only [oScalar]; omega⟩
  · rw [he.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.MlDsa.X86_64.Mask4.aR σ, by simp, 1024 * K, rfl, by simp only; omega⟩
    · exact ⟨VG.Proof.MlDsa.X86_64.Mask4.scrR σ, by simp, oScalar, rfl, by simp only [oScalar]; omega⟩

/-- `PC` after the call. -/
theorem PC.call {K : Nat} (hK : K < 4) {s s' : State} (h : VG.Proof.MlDsa.X86_64.Mask4.PC σ K s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp, .r15], s'.gpr r = s.gpr r)
    (hf : Frame (VG.Proof.MlDsa.X86_64.Mask4.cWr σ K ++ [VG.Proof.MlDsa.X86_64.Mask4.stkR σ]) s.mem s'.mem) : VG.Proof.MlDsa.X86_64.Mask4.PC σ K s' := by
  refine ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, by rw [hg .rbx (by simp), h.env.rbx],
      by rw [hg .r12 (by simp), h.env.r12], by rw [hg .r13 (by simp), h.env.r13], by rw [hg .r14 (by simp), h.env.r14],
      by rw [hg .rsp (by simp), h.env.rsp], by rw [hg .r15 (by simp), h.env.r15], fun i hi => ?_,
      h.env.frame.trans (hf.sub (VG.Proof.MlDsa.X86_64.Mask4.c_sub (σ := σ) hK))⟩, fun k hk => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (VG.Proof.MlDsa.X86_64.Mask4.c_disj hp hK (by simp only [oSave, oScalar]; omega)) (by decide)]
    exact h.env.saved i hi
  · refine polyIs_frame hf (fun r hr => ?_) (h.polys k hk)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · have hd := Offset.disjoint (VG.Proof.MlDsa.X86_64.Mask4.aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega) (by omega)
        (by omega)
      simpa [VG.Proof.MlDsa.X86_64.Mask4.poly4] using hd
    · exact (hp.a_scr.sub_left (VG.Proof.MlDsa.X86_64.Mask4.sub_poly (by omega))).sub_right (VG.Proof.MlDsa.X86_64.Mask4.sub_scr (by simp only [oScalar]; omega))
    · exact (hp.stk_a.sub_right (VG.Proof.MlDsa.X86_64.Mask4.sub_poly (by omega))).symm

/-- The arguments of the call on seed `K`. -/
structure ArgI (σ : State) (K : Nat) (s : State) : Prop where
  pinv : VG.Proof.MlDsa.X86_64.Mask4.PC σ K s
  rdi : s.gpr .rdi = VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 (66 * K)
  rsi : s.gpr .rsi = σ.gpr .rsi
  rdx : s.gpr .rdx = VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) K
  rcx : s.gpr .rcx = VG.Proof.MlDsa.X86_64.Mask4.at' σ oScalar

omit hp in
theorem sx6144 : BitVec.signExtend 64 (BitVec.ofNat 32 oScalar) = BitVec.ofNat 64 6144 := by decide

omit hp in
theorem argsK_ok {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.PC σ K s) :
    WP isa (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (66 * K))), .mov .rsi (.reg .r14),
      .mov .rdx (.reg .r13), .alu .add .rdx (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rcx (.reg .rbx),
      .alu .add .rcx (.imm (BitVec.ofNat 32 oScalar))]) s (VG.Proof.MlDsa.X86_64.Mask4.ArgI σ K) :=
  WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 (66 * K) ∧ s'.gpr .rsi = σ.gpr .rsi ∧ s'.gpr .rdx = VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) K ∧
      s'.gpr .rcx = VG.Proof.MlDsa.X86_64.Mask4.at' σ oScalar)
    (by xrun [h.env.r12, h.env.r13, h.env.r14, h.env.rbx, VG.Proof.MlKem.X86_64.sx_ofNat (show 66 * K < 2 ^ 31 by omega),
      VG.Proof.MlKem.X86_64.sx_ofNat (show 1024 * K < 2 ^ 31 by omega), VG.Proof.MlDsa.X86_64.Mask4.sx6144]; rfl) (by rfl))
    fun _ ⟨⟨hm₂, hdi, hsi, hdx, hcx⟩, k₂⟩ => ⟨⟨h.env.keep hm₂ k₂ (by decide), by rw [hm₂]; exact h.polys⟩,
      hdi, hsi, hdx, hcx⟩

theorem argK_kS {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.ArgI σ K s) :
    (below (s.gpr .rsp) 24).Disjoint ⟨VG.Proof.MlDsa.X86_64.Mask4.sd σ + BitVec.ofNat 64 (66 * K), 66⟩ := by
  rw [h.pinv.env.rsp]; exact hp.stk_sd.sub_right (Offset.sub_base (VG.Proof.MlDsa.X86_64.Mask4.sd σ) (d := 66 * K) (n := 66) (by omega))

theorem argK_pre {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.ArgI σ K s) :
    emK.pre (s.callEntry.withRegions (VG.Proof.MlDsa.X86_64.Mask4.cRd σ K) (VG.Proof.MlDsa.X86_64.Mask4.cWr σ K)) := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := h.pinv.env.rsp
  have kS := VG.Proof.MlDsa.X86_64.Mask4.argK_kS hp hK h
  have kA : (below (s.gpr .rsp) 24).Disjoint (pR (VG.Proof.MlDsa.X86_64.Mask4.poly4 (VG.Proof.MlDsa.X86_64.Mask4.aP σ) K)) := by
    rw [hsp]; exact hp.stk_a.sub_right (VG.Proof.MlDsa.X86_64.Mask4.sub_poly (σ := σ) hK)
  have kZ : (below (s.gpr .rsp) 24).Disjoint ⟨VG.Proof.MlDsa.X86_64.Mask4.at' σ oScalar, 2048⟩ := by
    rw [hsp]; exact hp.stk_scr.sub_right (VG.Proof.MlDsa.X86_64.Mask4.sub_scr (σ := σ) (a := oScalar) (n := 2048) (by simp only [oScalar]; omega))
  simp only [emK, gOf, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s (by decide : Reg.rdi ≠ .rsp), ce_gpr' s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rdx ≠ .rsp), ce_gpr' s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx]
  exact ⟨trivial, trivial,
    (hp.sd_a.sub_left (Offset.sub_base _ (by omega))).sub_right (VG.Proof.MlDsa.X86_64.Mask4.sub_poly hK),
    (hp.sd_scr.sub_left (Offset.sub_base _ (by omega))).sub_right (VG.Proof.MlDsa.X86_64.Mask4.sub_scr (by simp only [oScalar]; omega)),
    (hp.a_scr.sub_left (VG.Proof.MlDsa.X86_64.Mask4.sub_poly hK)).sub_right (VG.Proof.MlDsa.X86_64.Mask4.sub_scr (by simp only [oScalar]; omega)),
    ret_disj24 s kS, ret_disj24 s kA, ret_disj24 s kZ, stk_disj24' s kS, stk_disj24' s kA, stk_disj24' s kZ,
    VG.Proof.MlDsa.X86_64.Mask4.scr6144_lt hp, hp.gamma⟩

theorem callK_ok {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.ArgI σ K s) :
    WP isa (.call "vg_mldsa_expand_mask_poly" Impl.MlDsa.X86_64.Sample.expandMask) s (VG.Proof.MlDsa.X86_64.Mask4.PC σ (K + 1)) := by
  have hcv := VG.Proof.MlDsa.X86_64.Mask4.cov hp h.pinv.env hK
  refine WP.call expandMask_correct VG.Proof.MlDsa.X86_64.Mask4.em_nosp (by rw [VG.Proof.MlDsa.X86_64.Mask4.em_depth]; decide) (VG.Proof.MlDsa.X86_64.Mask4.argK_pre hp hK h) hcv.1 hcv.2
    fun s₃ hrd hwr hcs hf _ ⟨s₃', hm₃, _, hpost⟩ => ?_
  rw [VG.Proof.MlDsa.X86_64.Mask4.em_depth, h.pinv.env.rsp] at hf
  have h₃ : VG.Proof.MlDsa.X86_64.Mask4.PC σ K s₃ := h.pinv.call hp hK hrd hwr (fun r hr => hcs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hf
  simp only [emK, gOf, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rsi ≠ .rsp), ce_gpr' s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hm₃,
    ce_bytesAt24 s (n := 66) (by decide) (VG.Proof.MlDsa.X86_64.Mask4.argK_kS hp hK h), VG.Proof.MlDsa.X86_64.Mask4.seed_bytes hp hK h.pinv.env.frame] at hpost
  refine ⟨h₃.env, fun k hk => ?_⟩
  by_cases e : k = K
  · subst e; exact hpost
  · exact h₃.polys k (by omega)

theorem callK_ok' {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.PC σ K s) : WP isa (VG.Impl.MlDsa.X86_64.Sample.Mask4.callK K) s (VG.Proof.MlDsa.X86_64.Mask4.PC σ (K + 1)) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.argsK_ok hK h) fun _ h₂ => VG.Proof.MlDsa.X86_64.Mask4.callK_ok hp hK h₂)

omit hp in
theorem epi_eq' : epi = [.mov .r14 (.mem (at_ .rbx 5120)), .mov .r13 (.mem (at_ .rbx 5112)),
    .mov .r12 (.mem (at_ .rbx 5104)), .mov .rbp (.mem (at_ .rbx 5096)), .mov .rbx (.mem (at_ .rbx 5088))] := rfl

/-- The postcondition, and the callee-saved registers restored. -/
theorem endS_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Mask4.PC σ 4 s) :
    WP isa (.block epi) s fun s' => em4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Mask4.scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    VG.Proof.MlDsa.X86_64.Mask4.in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega)
  rw [VG.Proof.MlDsa.X86_64.Mask4.epi_eq']
  refine WP.mono (WP.keep [.r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .r14 = s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (VG.Proof.MlDsa.X86_64.Mask4.at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨fun K hK => by rw [hm]; exact h.polys K hK, fun r hr => ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega)⟩)
      (by decide)

end

theorem correct_scalar (σ : State) (hs : em4K.pre σ) :
    ∃ t s', Exec isa expandMask4 σ t s' ∧ abiPreserved σ s' ∧ em4K.post σ s' := by
  have hp := VG.Proof.MlDsa.X86_64.Mask4.pre_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.pro_ok hp) fun _ h =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.callK_ok' hp (by decide) (⟨h, fun _ h' => absurd h' (by omega)⟩ : VG.Proof.MlDsa.X86_64.Mask4.PC σ 0 _)) fun _ p₁ =>
      WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.callK_ok' hp (by decide) p₁) fun _ p₂ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.callK_ok' hp (by decide) p₂)
        fun _ p₃ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Mask4.callK_ok' hp (by decide) p₃) fun _ p₄ => VG.Proof.MlDsa.X86_64.Mask4.endS_ok hp p₄)))))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Mask4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Verified`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4` and `vg_mldsa_expand_mask_poly4_avx2`, verified

Untrusted: everything here is checked by Lean. The baseline implementation
is constant time as the calls are (`expandMask_ct`, from their pointers and
`γ₁`), and the contract of the proofs (`em4K`) is the shared one of `Spec/`.
-/

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.X86_64.Sample (emK gOf expandMask_correct expandMask_ct)

/-- The call on seed `K`. -/
theorem call_ct {K : Nat} (hK : K < 4) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Mask4.R fun σ s => VG.Proof.MlDsa.X86_64.Mask4.ArgI σ K s) (.call "vg_mldsa_expand_mask_poly" Impl.MlDsa.X86_64.Sample.expandMask)
      (VG.Proof.MlDsa.X86_64.Mask4.R fun σ s => VG.Proof.MlDsa.X86_64.Mask4.PC σ (K + 1) s) :=
  relInv (fun σ s hp h => VG.Proof.MlDsa.X86_64.Mask4.callK_ok (VG.Proof.MlDsa.X86_64.Mask4.pre_of hp) hK h) (RelCT.callEx expandMask_correct expandMask_ct
    fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      have hsp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [h₁.pinv.env.rsp, h₂.pinv.env.rsp, hq.2.2.2.2]
      refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Mask4.argK_pre (VG.Proof.MlDsa.X86_64.Mask4.pre_of p₁) hK h₁, VG.Proof.MlDsa.X86_64.Mask4.argK_pre (VG.Proof.MlDsa.X86_64.Mask4.pre_of p₂) hK h₂, ?_,
        (VG.Proof.MlDsa.X86_64.Mask4.cov (VG.Proof.MlDsa.X86_64.Mask4.pre_of p₁) h₁.pinv.env hK).1, (VG.Proof.MlDsa.X86_64.Mask4.cov (VG.Proof.MlDsa.X86_64.Mask4.pre_of p₁) h₁.pinv.env hK).2,
        (VG.Proof.MlDsa.X86_64.Mask4.cov (VG.Proof.MlDsa.X86_64.Mask4.pre_of p₂) h₂.pinv.env hK).1, (VG.Proof.MlDsa.X86_64.Mask4.cov (VG.Proof.MlDsa.X86_64.Mask4.pre_of p₂) h₂.pinv.env hK).2, hsp⟩
      simp only [emK, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), h₁.rdi, h₂.rdi, h₁.rsi, h₂.rsi,
        h₁.rdx, h₂.rdx, h₁.rcx, h₂.rcx]
      simp only [VG.Proof.MlDsa.X86_64.Mask4.sd, VG.Proof.MlDsa.X86_64.Mask4.aP, VG.Proof.MlDsa.X86_64.Mask4.at', VG.Proof.MlDsa.X86_64.Mask4.scr, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hsp, and_self])

/-- The call on seed `K`, given the taint analysis of its arguments. -/
theorem callK_ct {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (66 * K))), .mov .rsi (.reg .r14),
        .mov .rdx (.reg .r13), .alu .add .rdx (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rcx (.reg .rbx),
        .alu .add .rcx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Mask4.R fun σ s => VG.Proof.MlDsa.X86_64.Mask4.PC σ K s) (VG.Impl.MlDsa.X86_64.Sample.Mask4.callK K) (VG.Proof.MlDsa.X86_64.Mask4.R fun σ s => VG.Proof.MlDsa.X86_64.Mask4.PC σ (K + 1) s) :=
  RelCT.seq (relInv (fun σ s _ h => VG.Proof.MlDsa.X86_64.Mask4.argsK_ok hK h) (taintRel [.r12, .r13, .rbx]
      (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.env.r12, h₂.env.r12, VG.Proof.MlDsa.X86_64.Mask4.sd, VG.Proof.MlDsa.X86_64.Mask4.sd, hq.1]
        · exact VG.Proof.MlDsa.X86_64.Mask4.env_r13 hq h₁.env h₂.env
        · exact VG.Proof.MlDsa.X86_64.Mask4.env_rbx hq h₁.env h₂.env) c))
    (VG.Proof.MlDsa.X86_64.Mask4.call_ct hK)

theorem ct_scalar : ConstantTime isa em4K.pre em4K.pub expandMask4 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ s => VG.Proof.MlDsa.X86_64.Mask4.PC σ 0 s)
    (fun σ s hp h => by
      subst h
      exact WP.mono (VG.Proof.MlDsa.X86_64.Mask4.pro_ok (VG.Proof.MlDsa.X86_64.Mask4.pre_of hp)) fun _ h => ⟨h, fun _ h => absurd h (by omega)⟩)
    (taintRel [.rdi, .rdx, .rcx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.2.1, hq.2.2.2.1]) (by taint_decide))) ?_)
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Mask4.callK_ct (K := 0) (by decide) (by taint_decide)) (RelCT.seq (VG.Proof.MlDsa.X86_64.Mask4.callK_ct (K := 1) (by decide)
    (by taint_decide)) (RelCT.seq (VG.Proof.MlDsa.X86_64.Mask4.callK_ct (K := 2) (by decide) (by taint_decide))
      (RelCT.seq (VG.Proof.MlDsa.X86_64.Mask4.callK_ct (K := 3) (by decide) (by taint_decide)) ?_)))
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlDsa.X86_64.Mask4.env_rbx hq h₁.env h₂.env) (by taint_decide)

/-- A state satisfying the precondition. -/
def em4Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x20000 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 264⟩]
  wr := [⟨0x2000, 4096⟩, ⟨0x4000, 8192⟩]

theorem em4_verified (c : Prog isa)
    (hc : ∀ σ, em4K.pre σ → ∃ t s', Exec isa c σ t s' ∧ abiPreserved σ s' ∧ em4K.post σ s')
    (ht : ConstantTime isa em4K.pre em4K.pub c) :
    Verified X86_64.target c (Spec.MlDsa.expandMask4Contract X86_64.abi 24) :=
  Verified.of_correct hc ht
    { pre := by sig_implies_pre [Spec.MlDsa.expandMask4Contract, Spec.MlDsa.expandMask4Sig, VG.Proof.MlDsa.X86_64.Mask4.em4K, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.expandMask4Contract, Spec.MlDsa.expandMask4Sig, VG.Proof.MlDsa.X86_64.Mask4.em4K, X86_64.abi, X86_64.argRegs]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.expandMask4Contract, Spec.MlDsa.expandMask4Sig, VG.Proof.MlDsa.X86_64.Mask4.em4K, X86_64.abi, X86_64.argRegs] at h
        obtain ⟨hsp, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp⟩
      sat := by sig_implies_sat [Spec.MlDsa.expandMask4Contract, Spec.MlDsa.expandMask4Sig, VG.Proof.MlDsa.X86_64.Mask4.em4K, X86_64.abi,
        X86_64.argRegs] [em4Sat] using VG.Proof.MlDsa.X86_64.Mask4.em4Sat }

theorem expandMask4Avx2_verified : Verified X86_64.target expandMask4Avx2
    (Spec.MlDsa.expandMask4Contract X86_64.abi 24) := VG.Proof.MlDsa.X86_64.Mask4.em4_verified _ VG.Proof.MlDsa.X86_64.Mask4.correct VG.Proof.MlDsa.X86_64.Mask4.ct

theorem expandMask4_verified : Verified X86_64.target expandMask4
    (Spec.MlDsa.expandMask4Contract X86_64.abi 24) := VG.Proof.MlDsa.X86_64.Mask4.em4_verified _ VG.Proof.MlDsa.X86_64.Mask4.correct_scalar VG.Proof.MlDsa.X86_64.Mask4.ct_scalar

end VG.Proof.MlDsa.X86_64.Mask4

end
