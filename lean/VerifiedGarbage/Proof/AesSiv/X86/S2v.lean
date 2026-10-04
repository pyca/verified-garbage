import VerifiedGarbage.Proof.AesSiv.X86.CmacOf

/-!
# AES-SIV on x86: S2V over the associated data

Untrusted: everything here is checked by Lean. After the entry, every piece
writes only parts of `W` (`wR`), the stack below `SP` and, from counter mode
on, the data (`ext`): the slots, our caller's registers saved in `W`, and
everything outside those keep their values (`Kept`). S2V starts with
`D = AES-CMAC(K1, <zero>)` (`start_ok`); then, for each component `S` a
descriptor at `A` lists (`compA`, `compL`), `D = dbl(D) ⊕ AES-CMAC(K1, S)`
(`adBody_ok`), until none is left (`s2vAds_ok`, with the invariant `AInv`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold length_bytesAt ofNat_sub32
  readW_writeW_off SavedAt savedR CT covers_left)

/-! ## The components of associated data -/

/-- The address of the `i`-th component, from its descriptor at `A + 8 i`. -/
abbrev compA (m : Mem) (A : BitVec 32) (i : Nat) : BitVec 32 := m.readW (w64 A + BitVec.ofNat 64 (8 * i)) 32

/-- The length of the `i`-th component. -/
abbrev compL (m : Mem) (A : BitVec 32) (i : Nat) : Nat := (m.readW (w64 A + BitVec.ofNat 64 (8 * i + 4)) 32).toNat

theorem listed_getElem (m : Mem) (A : BitVec 32) {N i : Nat} (hi : i < N) :
    (Sig.listed 32 m .u8 (w64 A) N)[i]'(by simp [Sig.listed, hi]) = ⟨w64 (compA m A i), compL m A i⟩ := by
  simp only [Sig.listed, List.getElem_map, List.getElem_range, Elem.size, Nat.mul_one, compA, compL,
    add_ofNat_assoc]
  rw [Nat.mul_comm i 8]

theorem comp_mem (m : Mem) (A : BitVec 32) {N i : Nat} (hi : i < N) :
    (⟨w64 (compA m A i), compL m A i⟩ : Region) ∈ Sig.listed 32 m .u8 (w64 A) N := by
  rw [← listed_getElem m A hi]; exact List.getElem_mem _

theorem components_take_succ (m : Mem) (A : BitVec 32) {N i : Nat} (hi : i < N) :
    (Spec.Siv.components 32 m (w64 A) N).take (i + 1) =
      (Spec.Siv.components 32 m (w64 A) N).take i ++ [bytesAt m (w64 (compA m A i)) (compL m A i)] := by
  have hl : i < (Spec.Siv.components 32 m (w64 A) N).length := by simp [Spec.Siv.components, Sig.listed, hi]
  rw [List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some]
  simp only [Spec.Siv.components, List.getElem_map, listed_getElem m A hi]

theorem components_take_all (m : Mem) (A : BitVec 32) (N : Nat) :
    (Spec.Siv.components 32 m (w64 A) N).take N = Spec.Siv.components 32 m (w64 A) N :=
  List.take_of_length_le (by simp [Spec.Siv.components, Sig.listed])

theorem s2vAcc_snoc (mac : List Byte → List Byte) (xs : List (List Byte)) (x : List Byte) :
    Spec.Siv.s2vAcc mac (xs ++ [x]) = Spec.Siv.s2vStep mac (Spec.Siv.s2vAcc mac xs) x := by
  simp [Spec.Siv.s2vAcc, List.foldl_append]

/-! ## What the pieces keep -/

/-- The parts of `W` the pieces write, and the stack below `SP`. -/
abbrev wR (W SP : BitVec 32) : List Region := [wA W, wB W, wV W, wS W, wC W, below SP 56]

/-- Since the entry from `s₀`: the environment, the slots and our caller's
registers in `W`, and the memory outside `W`, the stack below `SP` and the
regions `ext` as on entry. -/
structure Kept (s₀ : State) (C W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (ext : List Region)
    (s : State) : Prop where
  env : Env C W SP s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  slots : Slots W C R D n s.mem
  saved : SavedAt s.mem W s₀
  big : Frame ([⟨w64 W, 2576⟩, below SP 56] ++ ext) s₀.mem s.mem

/-- A piece that writes parts of `W` the pieces write, the stack below `SP`,
or the regions `ext` (apart from `W`) keeps `Kept`. -/
theorem Kept.step {s₀ : State} {C W SP : BitVec 32} {R : Nat} {D : BitVec 32} {n : Nat} {ext : List Region}
    (L : Lay C W SP) (hext : ∀ r ∈ ext, r.Disjoint ⟨w64 W, 2576⟩) {s s' : State}
    (h : Kept s₀ C W SP R D n ext s) (E : Env C W SP s') (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (∃ r' ∈ wR W SP, Region.Sub r r') ∨ ∃ r' ∈ ext, Region.Sub r r') :
    Kept s₀ C W SP R D n ext s' := by
  have kept : ∀ {d k : Nat}, (128 ≤ d ∧ d + k ≤ 144 ∨ 176 ≤ d ∧ d + k ≤ 184 ∨ 192 ≤ d ∧ d + k ≤ 200) →
      ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun {d k} hd r hr => by
    rcases hs r hr with ⟨r', hr', hsub⟩ | ⟨r', hr', hsub⟩
    · refine Region.Disjoint.sub_right ?_ hsub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa using Lay.w_w (W := W) (n := k) (d := 0) (k := 128) (.inr (by omega)) (by omega) (by decide)
      · exact Lay.w_w (by omega) (by omega) (by decide)
      · exact Lay.w_w (by omega) (by omega) (by decide)
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm
    · exact ((hext r' hr').sub_right (Lay.wSub (by omega))).symm.sub_right hsub
  have k : ∀ o, (128 ≤ o ∧ o + 4 ≤ 144 ∨ 176 ≤ o ∧ o + 4 ≤ 184 ∨ 192 ≤ o ∧ o + 4 ≤ 200) →
      slotv s'.mem W o = slotv s.mem W o := fun o ho =>
    hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (kept ho) (by decide)
  refine ⟨E, by rw [rd, h.rd], by rw [wr, h.wr], ⟨?_, ?_, ?_, ?_⟩, ?_, h.big.trans (hf.sub fun r hr => ?_)⟩
  · rw [k _ (by decide)]; exact h.slots.ctx
  · rw [k _ (by decide)]; exact h.slots.rounds
  · rw [k _ (by decide)]; exact h.slots.data
  · rw [k _ (by decide)]; exact h.slots.len
  · exact h.saved.frame hf fun r hr => kept (.inl ⟨Nat.le_refl _, Nat.le_refl _⟩) r hr
  · rcases hs r hr with ⟨r', hr', hsub⟩ | ⟨r', hr', hsub⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => Lay.wSub (W := w64 W) (d := 0) (n := 128) (by decide) _ (by simpa using hsub _ h)⟩
      · exact ⟨_, by simp, fun _ h => Lay.wSub (by decide) _ (hsub _ h)⟩
      · exact ⟨_, by simp, fun _ h => Lay.wSub (by decide) _ (hsub _ h)⟩
      · exact ⟨_, by simp, fun _ h => Lay.wSub (by decide) _ (hsub _ h)⟩
      · exact ⟨_, by simp, fun _ h => Lay.wSub (by decide) _ (hsub _ h)⟩
      · exact ⟨_, by simp, hsub⟩
    · exact ⟨r', List.mem_append_right _ hr', hsub⟩

/-- The bytes of a region apart from `W`, the stack below `SP` and `ext` are
as on entry. -/
theorem Kept.bytes {s₀ : State} {C W SP : BitVec 32} {R : Nat} {D : BitVec 32} {n : Nat} {ext : List Region}
    {s : State} (h : Kept s₀ C W SP R D n ext s) {p : Addr} {k : Nat}
    (hw : (⟨p, k⟩ : Region).Disjoint ⟨w64 W, 2576⟩) (hs : (below SP 56).Disjoint ⟨p, k⟩)
    (he : ∀ r ∈ ext, (⟨p, k⟩ : Region).Disjoint r) (hk : k ≤ 2 ^ 64) : bytesAt s.mem p k = bytesAt s₀.mem p k :=
  Proof.AesGcm.X86.bytesAt_frame h.big (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · exact hw
    · exact hs.symm
    · exact he r hr) hk

/-- The context's PRF, after code that writes apart from its 512 bytes. -/
theorem ctxMac_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : R ≤ 14) :
    Spec.Siv.ctxMac m' C R = Spec.Siv.ctxMac m C R := by
  have e : ∀ {d k : Nat}, d + k ≤ 512 → bytesAt m' (C + BitVec.ofNat 64 d) k = bytesAt m (C + BitVec.ofNat 64 d) k :=
    fun hk => Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub_base _ hk)) (by omega)
  have s0 := e (d := 0) (k := 16 * (R + 1)) (by omega)
  rw [BitVec.add_zero] at s0
  simp only [Spec.Siv.ctxMac, Spec.Siv.schedCiph, s0]
  rw [show (240 : Addr) = BitVec.ofNat 64 240 from rfl, show (256 : Addr) = BitVec.ofNat 64 256 from rfl,
    e (by decide), e (by decide)]

/-! ## S2V's first state -/

/-- What S2V of the associated data needs of the entry state `s₀`: the `N`
descriptors at `A` and the components they list, readable, apart from `W`
and the stack below `SP`. -/
structure AdCtx (s₀ : State) (C W SP A : BitVec 32) (R N : Nat) : Prop where
  lay : Lay C W SP
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  desc : Buf W SP s₀ A (8 * N)
  comps : ∀ i < N, Buf W SP s₀ (compA s₀.mem A i) (compL s₀.mem A i)
  N32 : N < 2 ^ 32

/-- The context's PRF while `Kept` holds. -/
theorem Kept.mac {s₀ : State} {C W SP : BitVec 32} {R : Nat} {D : BitVec 32} {n : Nat} {ext : List Region}
    {s : State} (L : Lay C W SP) (hR : R = 10 ∨ R = 12 ∨ R = 14) (h : Kept s₀ C W SP R D n ext s)
    (he : ∀ r ∈ ext, (⟨w64 C, 512⟩ : Region).Disjoint r) :
    Spec.Siv.ctxMac s.mem (w64 C) R = Spec.Siv.ctxMac s₀.mem (w64 C) R :=
  ctxMac_frame h.big (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · exact L.c_w
    · exact L.stk_c.symm
    · exact he r hr) (by omega)

theorem zero_eq : Spec.Siv.zero = Spec.Cmac.zeros 16 := rfl

/-- The CMAC of the zero block from the context's subkeys. -/
theorem ctxMac_zero (m : Mem) (C : Addr) (R : Nat) :
    Spec.Siv.ctxMac m C R Spec.Siv.zero = Spec.Cmac.aesWith R (bytesAt m C (16 * (R + 1)))
      (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (bytesAt m (C + BitVec.ofNat 64 240) 16)
        (bytesAt m (C + BitVec.ofNat 64 256) 16) (Spec.Cmac.zeros 16)) (Spec.Cmac.zeros 16)) := by
  have := Siv.cmacWith_split (Spec.Siv.schedCiph m C R) (bytesAt m (C + 240) 16) (bytesAt m (C + 256) 16)
    (msg := []) (last := Spec.Cmac.zeros 16) (by decide) (by decide) (.inl rfl)
  simp only [List.nil_append] at this
  rw [Spec.Siv.ctxMac, zero_eq, this, Proof.Cmac.xor_comm]
  rfl

/-- The registers and memory after the block before `start`'s call. -/
theorem startPre_ok {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {s : State} (E : Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) :
    ∃ s', runBlock isa (zero4 zOff ++ zero4 dOff ++ macArgs dOff ++
        ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm zOff), .mov .esi (imm 16)] : List Instr)) s = some s' ∧
      s'.mem = Cmac.zero4 (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 zOff)) (w64 W + BitVec.ofNat 64 dOff) ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 2560 ∧
      s'.gpr .ebx = W + BitVec.ofNat 32 16 ∧ s'.gpr .esi = BitVec.ofNat 32 16 ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have z₁ := zero4_fold s.mem W zOff
  have z₂ := zero4_fold (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 zOff)) W dOff
  simp only [Nat.reduceAdd, zOff, dOff] at z₁ z₂
  refine ⟨_, by crun [zero4, macArgs, E.ebp, L.aW, E.perm.wW, E.perm.wR, hc, hr], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · cmems [z₁, z₂]
  · cregs [hc]
  · cregs [hr]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs []
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `start`: `D = AES-CMAC(K1, <zero>)`, S2V's first state. -/
theorem start_ok (v : Ctr32Impl) {s₀ : State} {C W SP : BitVec 32} {R : Nat} {D : BitVec 32} {n : Nat}
    (L : Lay C W SP) (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State} (h : Kept s₀ C W SP R D n [] s) :
    WP isa (start v.callee v.suffix) s fun s' => Kept s₀ C W SP R D n [] s' ∧
      Frame (wR W SP) s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 dOff) 16 = Spec.Siv.s2vStart (Spec.Siv.ctxMac s₀.mem (w64 C) R) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  obtain ⟨s₁, run₁, m₁, ax₁, cx₁, dx₁, bx₁, si₁, di₁, bp₁, sp₁, rd₁, wr₁⟩ :=
    startPre_ok L h.env h.slots.ctx h.slots.rounds
  have E₁ : Env C W SP s₁ := ⟨bp₁, sp₁, h.env.perm.of_eq rd₁ wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have f₁ : Frame [⟨w64 W + BitVec.ofNat 64 zOff, 16⟩, ⟨w64 W + BitVec.ofNat 64 dOff, 16⟩] s.mem s₁.mem := by
    rw [m₁]
    exact ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans
      ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  refine WP.mono (finCall_ok v L E₁ hR (y := 2560) (.inr ⟨by decide, by decide⟩) (P := W + BitVec.ofNat 32 16)
    (l := 16) (Nat.le_refl _) (srcW L E₁.perm (t := 16) (k := 16) (by decide))
    (by rw [L.aW (o := 16) (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
    ax₁ cx₁ dx₁ bx₁ si₁ di₁) fun s₂ ⟨E₂, rd₂, wr₂, _, f₂, o₂⟩ => ?_
  have f₁₂ : Frame (wR W SP) s.mem s₂.mem := by
    refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨below SP 56, by simp, fun _ h => h⟩
  refine ⟨h.step L (by simp) E₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) f₁₂ fun r hr => .inl ⟨r, hr, fun _ h => h⟩,
    f₁₂, ?_⟩
  simp only [zOff, dOff] at m₁
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 2560, 16⟩] (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 16))
      s₁.mem := by rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
  have hz16 : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 16) 16 = Spec.Cmac.zeros 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)]
    exact Cmac.zero4_bytes _ _
  have hz : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 2560) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁]; exact Cmac.zero4_bytes _ _
  have hc₁ : Spec.Siv.ctxMac s₁.mem (w64 C) R = Spec.Siv.ctxMac s.mem (w64 C) R :=
    ctxMac_frame f₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact L.c_w.sub_right (Lay.wSub (by decide))) (by omega)
  simp only [dOff] at o₂ ⊢
  rw [o₂, Spec.Siv.s2vStart, ← h.mac L hR (by simp), ← hc₁, ctxMac_zero, L.aW (o := 16) (by decide), hz16, hz]

/-! ## `dbl` in place -/

/-- `dblAt o`: the block at `W + o` doubled in place; `ebp` is `W` again
after it. -/
theorem dblAt_wp {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {o : Nat}
    (ho : o + 16 ≤ 2576) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .ebp = W → s'.gpr .esp = SP →
      s'.mem = Proof.CmacAes.X86.dblMem s.mem (w64 W + BitVec.ofNat 64 o) 0 0 → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) :
    WP isa (.block (dblAt o ++ is)) s Q := by
  have hW := L.fw
  rw [dblAt, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨_, by crun [E.ebp], ?_⟩
  have aW : (W + BitVec.ofNat 32 o).setWidth 64 = w64 W + BitVec.ofNat 64 o := L.sW (by omega)
  refine Proof.CmacAes.X86.dbl_wp (K := W + BitVec.ofNat 32 o) (src := 0) (dst := 0) (by cregs [E.ebp])
    (by rw [L.nW (by omega)]; omega) (by rw [L.nW (by omega)]; omega)
    (by cmems []; rw [aW, BitVec.add_zero]; exact covers_left (E.perm.wC ho))
    (by cmems []; rw [aW, BitVec.add_zero]; exact E.perm.wC ho) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  rw [WP.block_append_iff]
  have bx₁ : s₁.gpr .ebx = W + BitVec.ofNat 32 o := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    cregs [E.ebp]
  have sp₁ : s₁.gpr .esp = SP := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    cregs [E.esp]
  refine WP.of_runBlock ⟨_, by crun [bx₁], k _ (by cregs [bx₁]; exact BitVec.add_sub_cancel _ _) (by cregs [sp₁])
    (by cmems [m₁, aW]) (by cmems [rd₁]) (by cmems [wr₁])⟩

/-! ## A step of S2V -/

theorem add32_assoc (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- After `dbl`: the CMAC state XORed into `D`, then the next descriptor and
one fewer left. -/
theorem adTail_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {a b : BitVec 32}
    (ha : slotv s.mem W adsO = a) (hb : slotv s.mem W leftO = b) :
    ∃ s', runBlock isa (([.mov .edx (.reg .ebp), .alu .add .edx (imm dOff)] : List Instr) ++ (xorInto stOff 0 ++
        ([.mov .eax (slot adsO), .alu .add .eax (imm 8), .store (at_ .ebp adsO) .eax,
          .mov .eax (slot leftO), .alu .sub .eax (imm 1), .store (at_ .ebp leftO) .eax] : List Instr))) s = some s' ∧
      s'.mem = ((Cmac.xor4Mem s.mem (w64 W + BitVec.ofNat 64 dOff) (w64 W + BitVec.ofNat 64 stOff)
        (w64 W + BitVec.ofNat 64 dOff)).writeW (w64 W + BitVec.ofNat 64 adsO) (a + BitVec.ofNat 32 8)).writeW
        (w64 W + BitVec.ofNat 64 leftO) (b - BitVec.ofNat 32 1) ∧
      s'.zf = some (b - BitVec.ofNat 32 1 == 0) ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [xorInto, E.ebp, L.aW, E.perm.wW, E.perm.wR, ha, hb, add32_assoc,
    Proof.AesGcm.X86.add_zero32], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [ha, hb, Cmac.xor4Mem, add_ofNat_assoc]
  · cmems [ha, hb]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `adStep`: `D = dbl(D) ⊕` the CMAC state, the next descriptor and one
fewer left. -/
theorem adStep_wp {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {A : BitVec 32} {N i : Nat}
    (hiN : i < N) (hN : N < 2 ^ 32) (hads : slotv s.mem W adsO = A + BitVec.ofNat 32 (8 * i))
    (hleft : slotv s.mem W leftO = BitVec.ofNat 32 (N - i)) :
    WP isa (.block adStep) s fun s' => Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 dOff, 16⟩, wV W] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 dOff) 16 =
        Spec.Cmac.xor (bytesAt s.mem (w64 W + BitVec.ofNat 64 stOff) 16)
          (Spec.Cmac.dbl 16 (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16)) ∧
      slotv s'.mem W adsO = A + BitVec.ofNat 32 (8 * (i + 1)) ∧
      slotv s'.mem W leftO = BitVec.ofNat 32 (N - (i + 1)) ∧ s'.zf = some (decide (i + 1 = N)) := by
  have e : adStep = dblAt dOff ++ (([.mov .edx (.reg .ebp), .alu .add .edx (imm dOff)] : List Instr) ++
      (xorInto stOff 0 ++ ([.mov .eax (slot adsO), .alu .add .eax (imm 8), .store (at_ .ebp adsO) .eax,
        .mov .eax (slot leftO), .alu .sub .eax (imm 1), .store (at_ .ebp leftO) .eax] : List Instr))) := by
    simp only [adStep, List.append_assoc]
  rw [e]
  refine dblAt_wp L E (o := dOff) (by decide) fun s₁ bp₁ sp₁ m₁ rd₁ wr₁ => ?_
  have E₁ : Env C W SP s₁ := ⟨bp₁, sp₁, E.perm.of_eq rd₁ wr₁⟩
  have fD : Frame [⟨w64 W + BitVec.ofNat 64 dOff, 16⟩] s.mem s₁.mem := by
    rw [m₁]
    have := Proof.CmacAes.X86.dblMem_frame s.mem (w64 W + BitVec.ofNat 64 dOff) 0 0
    rwa [BitVec.add_zero] at this
  have kD : ∀ o, o + 4 ≤ 2560 → slotv s₁.mem W o = slotv s.mem W o := fun o ho =>
    fD.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by simp only [dOff]; omega)) (by omega)
        (by decide)) (by decide)
  obtain ⟨s₂, run₂, m₂, zf₂, bp₂, sp₂, rd₂, wr₂⟩ := adTail_ok L E₁ (a := A + BitVec.ofNat 32 (8 * i))
    (b := BitVec.ofNat 32 (N - i)) (by rw [kD _ (by decide)]; exact hads) (by rw [kD _ (by decide)]; exact hleft)
  refine WP.of_runBlock ⟨s₂, run₂, ⟨bp₂, sp₂, E₁.perm.of_eq rd₂ wr₂⟩, by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, ?_,
    ?_, ?_, ?_⟩
  · -- What the step writes.
    have fX : Frame [⟨w64 W + BitVec.ofNat 64 dOff, 16⟩, wV W] s₁.mem s₂.mem := by
      rw [m₂]
      exact (((Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).writeW (r := wV W)
        (by simp) _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW (r := wV W) (by simp) _
        (Offset.contains _ (by decide) (by decide) (by decide))
    exact (fD.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans fX
  · -- `D`.
    have fC : Frame [wV W] (Cmac.xor4Mem s₁.mem (w64 W + BitVec.ofNat 64 dOff) (w64 W + BitVec.ofNat 64 stOff)
        (w64 W + BitVec.ofNat 64 dOff)) s₂.mem := by
      rw [m₂]
      exact ((Frame.refl _ _).writeW (r := wV W) (by simp) _
        (Offset.contains _ (by decide) (by decide) (by decide))).writeW (r := wV W) (by simp) _
        (Offset.contains _ (by decide) (by decide) (by decide))
    rw [Proof.AesGcm.X86.bytesAt_frame fC (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide),
      Cmac.xor4Mem_bytes _ (Cmac.Sep4.of_disjoint (Lay.w_w (.inr (by decide)) (by decide) (by decide)))
        (Cmac.Sep4.self _),
      Proof.AesGcm.X86.bytesAt_frame fD (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide), m₁]
    have := Proof.CmacAes.X86.dblMem_bytes s.mem (w64 W + BitVec.ofNat 64 dOff) 0 0
    rw [BitVec.add_zero] at this
    rw [this]
  · rw [m₂, slotv, readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, add32_assoc]
    congr 2
  · rw [m₂]
    exact (Mem.readW_writeW_self32 _ _ _).trans (Proof.AesGcm.X86.pred_count hiN hN)
  · rw [zf₂, Proof.AesGcm.X86.pred_beq hiN hN]

/-! ## The loop over the components -/

/-- The next descriptor's address and length into `W + strO` and
`W + slenO`. -/
theorem adNext_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {A : BitVec 32} {j : Nat}
    (hads : slotv s.mem W adsO = A + BitVec.ofNat 32 j) (hfit : A.toNat + j + 8 ≤ 2 ^ 32)
    (rD : Covers [⟨w64 A + BitVec.ofNat 64 j, 8⟩] (s.rd ++ s.wr))
    (dW : (⟨w64 A + BitVec.ofNat 64 j, 8⟩ : Region).Disjoint ⟨w64 W, 2576⟩) :
    ∃ s', runBlock isa adNext s = some s' ∧
      s'.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 strO) (s.mem.readW (w64 A + BitVec.ofNat 64 j) 32)).writeW
        (w64 W + BitVec.ofNat 64 slenO) (s.mem.readW (w64 A + BitVec.ofNat 64 (j + 4)) 32) ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have p0 : (A + BitVec.ofNat 32 j + BitVec.ofNat 32 0).setWidth 64 = w64 A + BitVec.ofNat 64 j := by
    rw [Proof.AesGcm.X86.add_zero32]; exact Buf.ptr (by omega)
  have p4 : (A + BitVec.ofNat 32 j + BitVec.ofNat 32 4).setWidth 64 = w64 A + BitVec.ofNat 64 (j + 4) := by
    rw [add32_assoc]; exact Buf.ptr (by omega)
  have i0 : InRegions (s.rd ++ s.wr) (w64 A + BitVec.ofNat 64 j) 4 := by
    have := Proof.AesGcm.X86.in_off (p := w64 A + BitVec.ofNat 64 j) rD (d := 0) (n := 4) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have i4 : InRegions (s.rd ++ s.wr) (w64 A + BitVec.ofNat 64 (j + 4)) 4 := by
    have := Proof.AesGcm.X86.in_off (p := w64 A + BitVec.ofNat 64 j) rD (d := 4) (n := 4) (by decide) (by decide)
    rwa [add_ofNat_assoc] at this
  have r4 : (s.mem.writeW (w64 W + BitVec.ofNat 64 strO) (s.mem.readW (w64 A + BitVec.ofNat 64 j) 32)).readW
      (w64 A + BitVec.ofNat 64 (j + 4)) 32 = s.mem.readW (w64 A + BitVec.ofNat 64 (j + 4)) 32 :=
    Cmac.readW_writeW_disj _ (((dW.sub_left (by
      rw [← add_ofNat_assoc]; exact Offset.sub_base _ (by decide))).sub_right (Lay.wSub (by decide))).symm)
  refine ⟨_, by crun [adNext, E.ebp, L.aW, E.perm.wW, E.perm.wR, hads, p0, p4, i0, i4], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hads, p0, p4, r4]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- Before the `i`-th component (and, for `i = N`, after the last): `D` is
S2V's state of the first `i`, with the next descriptor's address and how
many are left in their slots. -/
structure AInv (s₀ : State) (C W SP A : BitVec 32) (R N : Nat) (D : BitVec 32) (n i : Nat) (s : State) :
    Prop where
  kept : Kept s₀ C W SP R D n [] s
  le : i ≤ N
  ads : slotv s.mem W adsO = A + BitVec.ofNat 32 (8 * i)
  left : slotv s.mem W leftO = BitVec.ofNat 32 (N - i)
  acc : bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s₀.mem (w64 C) R) ((Spec.Siv.components 32 s₀.mem (w64 A) N).take i)

theorem sub_wS {W : BitVec 32} {d k : Nat} (h₁ : 200 ≤ d) (h₂ : d + k ≤ 256) :
    Region.Sub ⟨w64 W + BitVec.ofNat 64 d, k⟩ (wS W) := Offset.sub _ h₁ (by omega)

/-- The `i`-th descriptor read: what the component's CMAC starts from. -/
theorem adNext_wp {s₀ : State} {C W SP A : BitVec 32} {R N : Nat} {D : BitVec 32} {n i : Nat}
    (hA : AdCtx s₀ C W SP A R N) (hiN : i < N) {s : State} (h : AInv s₀ C W SP A R N D n i s) :
    WP isa (.block adNext) s fun s₁ => CmacPre C W SP R (compA s₀.mem A i) (compL s₀.mem A i) s₁ ∧
      Kept s₀ C W SP R D n [] s₁ ∧ Frame [⟨w64 W + BitVec.ofNat 64 strO, 8⟩] s.mem s₁.mem := by
  have L := hA.lay
  have K := h.kept
  have hRb : R ≤ 14 := by rcases hA.rounds with h | h | h <;> omega
  have hfA := hA.desc.wrap
  -- The descriptor, as on entry.
  have dW : (⟨w64 A + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint ⟨w64 W, 2576⟩ :=
    hA.desc.w.sub_left (Offset.sub_base _ (by omega))
  have dS : (below SP 56).Disjoint ⟨w64 A + BitVec.ofNat 64 (8 * i), 8⟩ :=
    hA.desc.stk.sub_right (Offset.sub_base _ (by omega))
  have rD : Covers [⟨w64 A + BitVec.ofNat 64 (8 * i), 8⟩] (s.rd ++ s.wr) := by
    rw [K.rd, K.wr]; exact Proof.AesGcm.X86.covers_off hA.desc.rd (by omega) (by have := hA.desc.lt; omega)
  have wd : ∀ {d : Nat}, d + 4 ≤ 8 → s.mem.readW (w64 A + BitVec.ofNat 64 (8 * i + d)) 32 =
      s₀.mem.readW (w64 A + BitVec.ofNat 64 (8 * i + d)) 32 := fun hd =>
    K.big.readW (r := ⟨w64 A + BitVec.ofNat 64 (8 * i), 8⟩)
      (by rw [← add_ofNat_assoc]; exact Offset.contains_base _ hd (by omega)) (fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dW
        · exact dS.symm) (by decide)
  have w0 := wd (d := 0) (by decide)
  have w4 := wd (d := 4) (by decide)
  rw [Nat.add_zero] at w0
  obtain ⟨s₁, run₁, m₁, bp₁, sp₁, rd₁, wr₁⟩ := adNext_ok L K.env h.ads (by omega) rD dW
  have E₁ : Env C W SP s₁ := ⟨bp₁, sp₁, K.env.perm.of_eq rd₁ wr₁⟩
  have f₁ : Frame [⟨w64 W + BitVec.ofNat 64 strO, 8⟩] s.mem s₁.mem := by
    rw [m₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 200) (n := 4) (e := 200) (k := 8) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 204) (n := 4) (e := 200) (k := 8) (by decide) (by decide) (by decide))
  have K₁ := K.step L (by simp) E₁ rd₁ wr₁ f₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨wS W, by simp, sub_wS (by decide) (by decide)⟩
  have hc₁ := hA.comps i hiN
  refine WP.of_runBlock ⟨s₁, run₁, ?_, K₁, f₁⟩
  exact
    ⟨E₁, K₁.slots.ctx, K₁.slots.rounds,
      by rw [m₁, slotv, readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, w0],
      by rw [m₁, slotv, Mem.readW_writeW_self32, w4]; exact (Proof.AesGcm.X86.ofNat_toNat32 _).symm,
      BitVec.isLt _, hc₁.of_eq K₁.rd K₁.wr⟩

/-- One component: its descriptor read (`adNext_wp`), its CMAC into the
working space (`cmacOf_ok`) and the step of S2V (`adStep_wp`). -/
theorem adBody_ok (v : Ctr32Impl) {s₀ : State} {C W SP A : BitVec 32} {R N : Nat} {D : BitVec 32} {n i : Nat}
    (hA : AdCtx s₀ C W SP A R N) (hiN : i < N) {s : State} (h : AInv s₀ C W SP A R N D n i s) :
    WP isa (.seq (.block adNext) (.seq (cmacOf v.callee v.suffix stOff) (.block adStep))) s
      fun s' => AInv s₀ C W SP A R N D n (i + 1) s' ∧ s'.zf = some (decide (i + 1 = N)) := by
  have L := hA.lay
  have hc₁ := hA.comps i hiN
  refine WP.seq (WP.mono (adNext_wp hA hiN h) fun s₁ ⟨P₁, K₁, f₁⟩ => ?_)
  refine WP.seq (WP.mono (cmacOf_ok v L hA.rounds P₁) fun s₂ M => ?_)
  have K₂ := K₁.step L (by simp) M.env M.rd M.wr M.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨wB W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact .inl ⟨wS W, by simp, sub_wS (by decide) (by decide)⟩
    · exact .inl ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact .inl ⟨below SP 56, by simp, fun _ h => h⟩
  -- The slots `adStep` reads.
  have kS : ∀ o, (176 ≤ o ∧ o + 4 ≤ 200) → slotv s₂.mem W o = slotv s.mem W o := fun o ho => by
    rw [cmacR_slot L M.frame (by omega) (by omega)]
    exact f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by simp only [strO]; omega)) (by omega)
        (by decide)) (by decide)
  refine WP.mono (adStep_wp L M.env hiN hA.N32 (by rw [kS _ (by decide)]; exact h.ads)
    (by rw [kS _ (by decide)]; exact h.left)) fun s₃ ⟨E₃, rd₃, wr₃, f₃, o₃, a₃, l₃, z₃⟩ => ⟨⟨?_, hiN, a₃, l₃, ?_⟩, z₃⟩
  · exact K₂.step L (by simp) E₃ rd₃ wr₃ f₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact .inl ⟨wV W, by simp, fun _ h => h⟩
  · -- `D = dbl(D) ⊕ AES-CMAC(K1, S)`.
    have hD₂ : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 dOff) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16 := by
      rw [Proof.AesGcm.X86.bytesAt_frame M.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact (L.stk_w' (by decide)).symm) (by decide),
        Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
          (by decide)]
    have hS : bytesAt s₁.mem (w64 (compA s₀.mem A i)) (compL s₀.mem A i) =
        bytesAt s₀.mem (w64 (compA s₀.mem A i)) (compL s₀.mem A i) :=
      K₁.bytes hc₁.w hc₁.stk (by simp) (by have := hc₁.lt; omega)
    rw [o₃, M.out, hD₂, h.acc, K₁.mac L hA.rounds (by simp), hS, components_take_succ _ _ hiN, s2vAcc_snoc,
      Spec.Siv.s2vStep, Siv.xor_eq, Proof.Cmac.xor_comm]
    rfl

theorem leftTest_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {N : Nat}
    (hN : N < 2 ^ 32) (hl : slotv s.mem W leftO = BitVec.ofNat 32 N) :
    ∃ s', runBlock isa [.mov .eax (slot leftO), .alu .test .eax (.reg .eax)] s = some s' ∧ s'.mem = s.mem ∧
      s'.zf = some (decide (N = 0)) ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hl], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cmems [hl]; rw [Proof.AesGcm.X86.and_self_beq32 hN]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals rfl

theorem AInv.keep {s₀ : State} {C W SP A : BitVec 32} {R N : Nat} {D : BitVec 32} {n i : Nat} {s s' : State}
    (L : Lay C W SP) (h : AInv s₀ C W SP A R N D n i s) (hm : s'.mem = s.mem) (hbp : s'.gpr .ebp = W)
    (hsp : s'.gpr .esp = SP) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AInv s₀ C W SP A R N D n i s' :=
  ⟨h.kept.step L (by simp) ⟨hbp, hsp, h.kept.env.perm.of_eq hrd hwr⟩ hrd hwr (rs := [])
    (by rw [hm]; exact Frame.refl _ _)
    (fun r hr => by simp at hr), h.le, by rw [hm]; exact h.ads, by rw [hm]; exact h.left, by rw [hm]; exact h.acc⟩

/-- `s2vAds`: S2V over every component. -/
theorem s2vAds_ok (v : Ctr32Impl) {s₀ : State} {C W SP A : BitVec 32} {R N : Nat} {D : BitVec 32} {n : Nat}
    (hA : AdCtx s₀ C W SP A R N) {s : State} (h : AInv s₀ C W SP A R N D n 0 s) :
    WP isa (s2vAds v.callee v.suffix) s (AInv s₀ C W SP A R N D n N) := by
  have L := hA.lay
  have l₀ := h.left
  rw [Nat.sub_zero] at l₀
  obtain ⟨s₁, run₁, m₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ := leftTest_ok L h.kept.env hA.N32 l₀
  have h₁ := h.keep L m₁ bp₁ sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (N = 0)) (eval_e zf₁) (fun hz => ?_) (fun hz => ?_)
  · have hN : N = 0 := of_decide_eq_true hz
    subst hN
    exact WP.block_nil h₁
  · have hN : N ≠ 0 := of_decide_eq_false hz
    refine WP.loop (fun (k : Nat) (t : State) => ∃ i, k = N - i ∧ i < N ∧ AInv s₀ C W SP A R N D n i t)
      (fun k t ⟨i, hk, hi, ht⟩ => ?_) (N - 0) s₁ ⟨0, rfl, by omega, h₁⟩
    refine WP.mono (adBody_ok v hA hi ht) fun t' ⟨ht', hz'⟩ => ?_
    by_cases he : i + 1 = N
    · left
      refine ⟨by rw [eval_ne hz']; simp [he], ?_⟩
      exact (congrArg (fun j => AInv s₀ C W SP A R N D n j t') he).mp ht'
    · right
      refine ⟨by rw [eval_ne hz']; simp [he], N - (i + 1), by omega, i + 1, rfl, by omega, ht'⟩

/-! ## Constant time -/

/-- `start` is constant time from the environment and the slots it reads. -/
theorem start_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (fun s => Env C W SP s ∧ slotv s.mem W ctxO = C ∧ slotv s.mem W roundsO = BitVec.ofNat 32 R)
      (start v.callee v.suffix) := by
  refine CT.block_seq [.ebp] (pin_ebp fun s h => h.1.ebp) (by taint_decide) (fun s hs => startPre_ok L hs.1 hs.2.1
    hs.2.2) ?_
  refine finCall_ct v L hR (y := 2560) (.inr ⟨by decide, by decide⟩) (P := W + BitVec.ofNat 32 16) (l := 16)
    (Nat.le_refl _) fun s₁ ⟨s, hs, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ => ?_
  have E₁ : Env C W SP s₁ := ⟨bp, sp, hs.1.perm.of_eq rd wr⟩
  exact ⟨E₁, srcW L E₁.perm (t := 16) (k := 16) (by decide),
    by rw [L.aW (o := 16) (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide), ax, cx, dx, bx, si,
    di⟩

theorem CT.of_empty {I : State → Prop} {c : Prog isa} (h : ∀ s, ¬ I s) : CT I c :=
  RelCT.of_false fun s₁ _ hp => h s₁ hp.1

/-- `AInv` from some entry state whose descriptors list the public
components `ca`, `cl`. -/
def ACT (C W SP A : BitVec 32) (R N : Nat) (ca : Nat → BitVec 32) (cl : Nat → Nat) (i : Nat) (s : State) : Prop :=
  ∃ s₀ D n, AdCtx s₀ C W SP A R N ∧ (∀ j < N, compA s₀.mem A j = ca j ∧ compL s₀.mem A j = cl j) ∧
    AInv s₀ C W SP A R N D n i s

/-- `adNext`, from the descriptor's address the slot holds. -/
theorem adNext_ct {C W SP A : BitVec 32} (L : Lay C W SP) {R N : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    {i : Nat} : CT (ACT C W SP A R N ca cl i) (.block adNext) := by
  have e : adNext = ([.mov .eax (slot adsO)] : List Instr) ++ [.mov .ecx (.mem (at_ .eax 0)),
      .store (at_ .ebp strO) .ecx, .mov .ecx (.mem (at_ .eax 4)), .store (at_ .ebp slenO) .ecx] := rfl
  rw [e]
  refine RelCT.block_append (CT.seq (J := fun s => s.gpr .ebp = W ∧ s.gpr .eax = A + BitVec.ofNat 32 (8 * i))
    (CT.taint [.ebp] (pin_ebp fun s ⟨_, _, _, _, _, h⟩ => h.kept.env.ebp) (by taint_decide))
    (fun s ⟨_, _, _, _, _, h⟩ => WP.of_runBlock ⟨_, by crun [h.kept.env.ebp, L.aW, h.kept.env.perm.wR],
      by cregs [h.kept.env.ebp], by cregs [h.ads]⟩)
    (CT.taint [.ebp, .eax] (pin2 fun _ h => h) (by taint_decide)))

theorem adBody_ct (v : Ctr32Impl) {C W SP A : BitVec 32} (L : Lay C W SP) {R N : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {ca : Nat → BitVec 32} {cl : Nat → Nat} {i : Nat} (hiN : i < N)
    (hcl : cl i < 2 ^ 32) :
    CT (ACT C W SP A R N ca cl i) (.seq (.block adNext) (.seq (cmacOf v.callee v.suffix stOff) (.block adStep))) := by
  refine CT.seq (J := CmacPre C W SP R (ca i) (cl i)) (adNext_ct L)
    (fun s ⟨s₀, D, n, hA, hc, h⟩ => WP.mono (adNext_wp hA hiN h) fun s₁ ⟨P₁, _⟩ => by
      rw [(hc i hiN).1, (hc i hiN).2] at P₁; exact P₁) ?_
  exact CT.seq (J := fun s => s.gpr .ebp = W) (cmacOf_ct v L hR hcl)
    (fun s hs => WP.mono (cmacOf_ok v L hR hs) fun s' M => M.env.ebp)
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))

/-- The loop over the components is constant time. -/
theorem s2vLoop_ct (v : Ctr32Impl) {C W SP A : BitVec 32} (L : Lay C W SP) {R N : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {ca : Nat → BitVec 32} {cl : Nat → Nat} (hcl : ∀ j < N, cl j < 2 ^ 32) (k : Nat) :
    CT (fun s => ∃ i, k = N - i ∧ i < N ∧ ACT C W SP A R N ca cl i s)
      (.loop (.seq (.block adNext) (.seq (cmacOf v.callee v.suffix stOff) (.block adStep))) .ne) := by
  refine CT.loopN (fun k s => ∃ i, k = N - i ∧ i < N ∧ ACT C W SP A R N ca cl i s) (fun k => ?_)
    (fun k s ⟨i, hk, hi, s₀, D, n, hA, hc, h⟩ => ?_) k
  · by_cases hk : 0 < k ∧ k ≤ N
    · exact (adBody_ct v L hR (A := A) (N := N) (ca := ca) (cl := cl) (i := N - k) (by omega) (hcl (N - k) (by omega))).mono fun s ⟨i, hk', hi, h⟩ => by
        rw [show N - k = i by omega]; exact h
    · exact CT.of_empty fun s ⟨i, hk', hi, _⟩ => hk ⟨by omega, by omega⟩
  · refine WP.mono (adBody_ok v hA hi h) fun s' ⟨h', hz⟩ => ⟨by omega, by rw [eval_ne hz]; simp; omega,
      fun hk1 => ⟨i + 1, by omega, by omega, s₀, D, n, hA, hc, h'⟩⟩

/-- `s2vAds` is constant time. -/
theorem s2vAds_ct (v : Ctr32Impl) {C W SP A : BitVec 32} (L : Lay C W SP) {R N : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hN : N < 2 ^ 32) {ca : Nat → BitVec 32} {cl : Nat → Nat}
    (hcl : ∀ j < N, cl j < 2 ^ 32) :
    CT (ACT C W SP A R N ca cl 0) (s2vAds v.callee v.suffix) := by
  refine CT.seq (J := fun s => ACT C W SP A R N ca cl 0 s ∧ s.zf = some (decide (N = 0)))
    (CT.taint [.ebp] (pin_ebp fun s ⟨_, _, _, _, _, h⟩ => h.kept.env.ebp) (by taint_decide))
    (fun s ⟨s₀, D, n, hA, hc, h⟩ => ?_) ?_
  · have l₀ := h.left
    rw [Nat.sub_zero] at l₀
    obtain ⟨s₁, run₁, m₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ := leftTest_ok L h.kept.env hN l₀
    exact WP.of_runBlock ⟨s₁, run₁, ⟨s₀, D, n, hA, hc, h.keep L m₁ bp₁ sp₁ rd₁ wr₁⟩, zf₁⟩
  refine CT.ite (decide (N = 0)) (fun s h => eval_e h.2) (fun _ => CT.nil) fun hz => ?_
  have hN0 : N ≠ 0 := of_decide_eq_false hz
  exact (s2vLoop_ct v L hR hcl N).mono fun s ⟨h, _⟩ => ⟨0, by omega, by omega, h⟩

end VG.Proof.AesSiv.X86
